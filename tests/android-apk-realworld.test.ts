import { afterEach, describe, expect, it } from "vitest";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  findApkSigningBlock,
  isApkSignatureEntry,
  protectZipOrApkBuffer,
  readZipEntries,
  UnsupportedApkProtectionError,
  writeZipArchive,
} from "../src/shields/formats/archive.js";
import { auditTarget } from "../src/engine/auditor.js";
import { protectTarget } from "../src/engine/protector.js";

const tempDirs: string[] = [];
afterEach(() => {
  for (const d of tempDirs.splice(0)) rmSync(d, { recursive: true, force: true });
});

function minimalDex(magicNumber = 0x12345678): Buffer {
  const dex = Buffer.alloc(112, 0);
  dex.write("dex\n035\0", 0, "ascii");
  dex.writeUInt32LE(112, 32);
  dex.writeUInt32LE(112, 36);
  dex.writeUInt32LE(magicNumber, 40);
  return dex;
}

function buildSignedApkWithSigningBlock(options: {
  readonly v1Signatures?: boolean;
  readonly v2SigningBlock?: boolean;
} = { v1Signatures: true, v2SigningBlock: true }): Buffer {
  const entries: { name: string; data: Buffer; storeOnly?: boolean }[] = [
    { name: "AndroidManifest.xml", data: Buffer.from("<manifest package='com.example.defense'/>") },
    { name: "classes.dex", data: minimalDex(0x11111111) },
    { name: "classes2.dex", data: minimalDex(0x22222222) },
    { name: "res/layout/activity_main.xml", data: Buffer.from("<LinearLayout/>") },
  ];

  if (options.v1Signatures) {
    entries.push(
      { name: "META-INF/MANIFEST.MF", data: Buffer.from("Manifest-Version: 1.0\r\nCreated-By: 1.0 (Android)\r\n") },
      { name: "META-INF/CERT.SF", data: Buffer.from("Signature-Version: 1.0\r\nSHA-256-Digest-Manifest: abc\r\n") },
      { name: "META-INF/CERT.RSA", data: Buffer.from("simulated-pkcs7-rsa-signature-block") },
    );
  }

  const baseZip = writeZipArchive(entries);
  if (!options.v2SigningBlock) {
    return baseZip;
  }

  // Insert APK Signing Block v2 immediately before Central Directory
  const eocdOffset = baseZip.length - 22;
  const cdStart = baseZip.readUInt32LE(eocdOffset + 16);
  const cdSize = baseZip.readUInt32LE(eocdOffset + 12);

  const v2Payload = Buffer.from("simulated-apk-signing-block-v2-signer-data");
  const pairLen = 4 + v2Payload.length;
  const blockSize = 8 + pairLen + 8 + 16;

  const sigBlock = Buffer.alloc(8 + blockSize);
  sigBlock.writeBigUInt64LE(BigInt(blockSize), 0);
  sigBlock.writeBigUInt64LE(BigInt(pairLen), 8);
  sigBlock.writeUInt32LE(0x7109871a, 16); // APK Signature Scheme v2 ID
  v2Payload.copy(sigBlock, 20);
  const secondSizeOffset = 20 + v2Payload.length;
  sigBlock.writeBigUInt64LE(BigInt(blockSize), secondSizeOffset);
  Buffer.from("APK Sig Block 42", "latin1").copy(sigBlock, secondSizeOffset + 8);

  const beforeCd = baseZip.subarray(0, cdStart);
  const cd = baseZip.subarray(cdStart, cdStart + cdSize);
  const eocd = Buffer.from(baseZip.subarray(eocdOffset));
  eocd.writeUInt32LE(cdStart + sigBlock.length, 16);

  return Buffer.concat([beforeCd, sigBlock, cd, eocd]);
}

describe("Real-world Android APK support", () => {
  it("recognizes Android APK signature scheme files", () => {
    expect(isApkSignatureEntry("META-INF/MANIFEST.MF")).toBe(false);
    expect(isApkSignatureEntry("META-INF/CERT.SF")).toBe(true);
    expect(isApkSignatureEntry("META-INF/CERT.RSA")).toBe(true);
    expect(isApkSignatureEntry("META-INF/KEY.DSA")).toBe(true);
    expect(isApkSignatureEntry("META-INF/RELEASE.EC")).toBe(true);
    expect(isApkSignatureEntry("META-INF/SIG-TEST")).toBe(true);

    expect(isApkSignatureEntry("classes.dex")).toBe(false);
    expect(isApkSignatureEntry("AndroidManifest.xml")).toBe(false);
    expect(isApkSignatureEntry("META-INF/androidx.core_core.version")).toBe(false);
  });

  it("detects APK Signing Block v2/v3 structure", () => {
    const signedApk = buildSignedApkWithSigningBlock({ v1Signatures: true, v2SigningBlock: true });
    const eocdOffset = signedApk.length - 22;
    const cdStart = signedApk.readUInt32LE(eocdOffset + 16);

    const block = findApkSigningBlock(signedApk, cdStart);
    expect(block).not.toBeNull();
    expect(block!.size).toBeGreaterThan(24);
    expect(block!.offset).toBeLessThan(cdStart);
  });

  it("fails closed with UnsupportedApkProtectionError on signed APK when stripSignatures is false", () => {
    const signedApk = buildSignedApkWithSigningBlock({ v1Signatures: true, v2SigningBlock: true });
    expect(() => protectZipOrApkBuffer(signedApk, { isApk: true })).toThrow(UnsupportedApkProtectionError);
  });

  it("hardens multidex and strips v1/v2 signatures when stripSignatures is true", () => {
    const signedApk = buildSignedApkWithSigningBlock({ v1Signatures: true, v2SigningBlock: true });
    const res = protectZipOrApkBuffer(signedApk, {
      isApk: true,
      stripSignatures: true,
      intensity: "balanced",
      seed: "realworld-apk",
    });

    expect(res.signaturesStripped).toBe(true);
    expect(res.membersHardened).toBe(2); // classes.dex and classes2.dex
    expect(res.canaryTokensEmbedded).toBeGreaterThan(0);
    expect(res.androidR8MappingBytes).toBeGreaterThan(100);
    expect(res.androidManifestDecoyBytes).toBeGreaterThan(100);

    const entries = readZipEntries(res.buffer, { allowApkStructures: true });
    expect(entries.some((e) => e.name === "META-INF/CERT.RSA")).toBe(false);
    expect(entries.some((e) => e.name === "META-INF/CERT.SF")).toBe(false);
    expect(entries.some((e) => e.name === "assets/bla-shield/bla-attestation-manifest.json")).toBe(true);
    expect(entries.some((e) => e.name === "lib/arm64-v8a/libbla_enclave_jni.so")).toBe(true);

    const dex1 = entries.find((e) => e.name === "classes.dex")!.data.toString("latin1");
    expect(dex1).toContain("BLA-DEX-SHIELD");
    const dex2 = entries.find((e) => e.name === "classes2.dex")!.data.toString("latin1");
    expect(dex2).toContain("BLA-DEX-SHIELD");
  });

  it("enforces 4-byte zipalign on stored entries when zipalign option is true", () => {
    const files = [
      { name: "stored_1.dat", data: Buffer.from("hello"), storeOnly: true },
      { name: "stored_2.dat", data: Buffer.from("world of android"), storeOnly: true },
      { name: "compressed.dat", data: Buffer.from("compressible data ".repeat(16)), storeOnly: false },
    ];
    const zip = writeZipArchive(files, { zipalign: true });

    const entries = readZipEntries(zip, { allowApkStructures: true });
    expect(entries).toHaveLength(3);

    // Verify local header offsets and 4-byte alignment
    let central = zip.readUInt32LE(zip.length - 6);
    const count = zip.readUInt16LE(zip.length - 12);
    for (let i = 0; i < count; i++) {
      const method = zip.readUInt16LE(central + 10);
      const nameLen = zip.readUInt16LE(central + 28);
      const extraLen = zip.readUInt16LE(central + 30);
      const commentLen = zip.readUInt16LE(central + 32);
      const localOffset = zip.readUInt32LE(central + 42);

      const localNameLen = zip.readUInt16LE(localOffset + 26);
      const localExtraLen = zip.readUInt16LE(localOffset + 28);
      const dataOffset = localOffset + 30 + localNameLen + localExtraLen;

      if (method === 0) {
        expect(dataOffset % 4).toBe(0);
      }
      central += 46 + nameLen + extraLen + commentLen;
    }
  });

  it("audits signed and unsigned APKs cleanly without throwing", () => {
    const dir = mkdtempSync(join(tmpdir(), "bla-apk-audit-"));
    tempDirs.push(dir);
    const apkPath = join(dir, "release-signed.apk");
    const signedApk = buildSignedApkWithSigningBlock({ v1Signatures: true, v2SigningBlock: true });
    writeFileSync(apkPath, signedApk);

    const report = auditTarget(apkPath);
    expect(report.detectedFormat).toBe("android-apk");
    expect(report.exposureScore).toBeGreaterThan(50);
    expect(report.protectionStatus).not.toBe("BLA_PROTECTED");
    expect(report.exposedItems.length).toBeGreaterThan(0);
  });

  it("protectTarget shields real APK files and outputs signable unsigned APK with stripSignatures: true", () => {
    const dir = mkdtempSync(join(tmpdir(), "bla-apk-protect-"));
    tempDirs.push(dir);
    const inApk = join(dir, "app-release.apk");
    const outApk = join(dir, "app-protected-unsigned.apk");
    const signedApk = buildSignedApkWithSigningBlock({ v1Signatures: true, v2SigningBlock: true });
    writeFileSync(inApk, signedApk);

    const res = protectTarget({
      inputPath: inApk,
      outputPath: outApk,
      stripSignatures: true,
      intensity: "maximum",
      seed: "target-apk-shield",
    });

    expect(res.detectedFormat).toBe("android-apk");
    expect(res.signaturesStripped).toBe(true);
    expect(res.afterAudit.protectionStatus).toBe("BLA_PROTECTED");
    expect(res.afterAudit.exposureScore).toBeLessThan(res.beforeAudit.exposureScore);
    expect(existsSync(outApk)).toBe(true);

    const outBytes = readFileSync(outApk);
    const outEntries = readZipEntries(outBytes, { allowApkStructures: true });
    expect(outEntries.some((e) => e.name.startsWith("assets/bla-shield/"))).toBe(true);
    expect(outEntries.some((e) => e.name === "META-INF/CERT.RSA")).toBe(false);
  });
});

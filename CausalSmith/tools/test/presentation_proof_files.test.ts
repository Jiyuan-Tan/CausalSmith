import { afterEach, describe, expect, it } from "vitest";
import { mkdtemp, mkdir, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { proofFileName, proofFilePath, proofObjId } from "../src/presentation/proof_files.js";

const dirs: string[] = [];
afterEach(async () => {
  await Promise.all(dirs.splice(0).map((dir) => rm(dir, { recursive: true, force: true })));
});

describe("portable proof file names", () => {
  it("spells the label colon as -- and inverts it", () => {
    expect(proofFileName("thm:convex-design")).toBe("thm--convex-design.tex");
    expect(proofObjId("thm--convex-design.tex")).toBe("thm:convex-design");
    expect(proofObjId("lem:legacy.tex")).toBe("lem:legacy");
    expect(proofObjId("_cache_keys.json")).toBeNull();
  });

  it("never produces a name Windows cannot check out", () => {
    for (const id of ["thm:a", "lem:x-y_z.1", "oeq:q"]) expect(proofFileName(id)).toMatch(/^[A-Za-z0-9._-]+\.tex$/);
    expect(() => proofFileName("thm:a b")).toThrow(/portable/);
    expect(() => proofFileName("thm:a--b")).toThrow(/--/);
  });

  it("prefers the encoded file and falls back to a legacy colon-named one", async () => {
    const outDir = await mkdtemp(join(tmpdir(), "proof-files-"));
    dirs.push(outDir);
    await mkdir(join(outDir, "proofs"));
    expect(proofFilePath(outDir, "thm:main")).toBe(join(outDir, "proofs", "thm--main.tex"));
    if (process.platform === "win32") return; // a colon-named file cannot exist there
    await writeFile(join(outDir, "proofs", "thm:main.tex"), "legacy\n");
    expect(proofFilePath(outDir, "thm:main")).toBe(join(outDir, "proofs", "thm:main.tex"));
    await writeFile(join(outDir, "proofs", "thm--main.tex"), "encoded\n");
    expect(proofFilePath(outDir, "thm:main")).toBe(join(outDir, "proofs", "thm--main.tex"));
  });
});

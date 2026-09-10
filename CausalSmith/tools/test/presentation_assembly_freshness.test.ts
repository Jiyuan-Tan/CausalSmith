import { afterEach, describe, expect, it } from "vitest";
import { mkdtemp, mkdir, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { assertP2AssemblyFresh, recordP2Assembly } from "../src/presentation/assembly_freshness.js";

const dirs: string[] = [];
afterEach(async () => {
  await Promise.all(dirs.splice(0).map((dir) => rm(dir, { recursive: true, force: true })));
});

async function fixture(): Promise<string> {
  const outDir = await mkdtemp(join(tmpdir(), "presentation-assembly-"));
  dirs.push(outDir);
  await mkdir(join(outDir, "sections"));
  await mkdir(join(outDir, "proofs"));
  await writeFile(join(outDir, "outline.md"), "# Title\n");
  await writeFile(join(outDir, "appendix_proofs.tex"), "Proof.\n");
  await writeFile(join(outDir, "sections", "01_body.tex"), "Body.\n");
  await writeFile(join(outDir, "proofs", "thm:main.tex"), "Proof.\n");
  return outDir;
}

describe("P2 assembly freshness", () => {
  it("accepts unchanged authored inputs", async () => {
    const outDir = await fixture();
    await recordP2Assembly(outDir);
    await expect(assertP2AssemblyFresh(outDir)).resolves.toBeUndefined();
  });

  it("blocks P4 after a cached section changes", async () => {
    const outDir = await fixture();
    await recordP2Assembly(outDir);
    await writeFile(join(outDir, "sections", "01_body.tex"), "Revised body.\n");
    await expect(assertP2AssemblyFresh(outDir)).rejects.toThrow(/changed after paper\.tex was assembled/);
  });

  it("blocks P4 after front_matter.tex changes, and joins it to the digest once it exists", async () => {
    const outDir = await fixture();
    await writeFile(join(outDir, "front_matter.tex"), "\\begin{abstract}A.\\end{abstract}\n");
    await recordP2Assembly(outDir);
    await expect(assertP2AssemblyFresh(outDir)).resolves.toBeUndefined();
    await writeFile(join(outDir, "front_matter.tex"), "\\begin{abstract}Revised.\\end{abstract}\n");
    await expect(assertP2AssemblyFresh(outDir)).rejects.toThrow(/changed after paper\.tex was assembled/);
  });

  it("honours a manifest recorded under the pre-front-matter formula until the next record", async () => {
    const outDir = await fixture();
    await recordP2Assembly(outDir); // no front matter → this IS the legacy formula's digest
    await writeFile(join(outDir, "front_matter.tex"), "\\begin{abstract}A.\\end{abstract}\n");
    // A bundle whose manifest predates the formula change must not read as stale on its own account,
    // and the match is consumed: the manifest is re-stamped so front matter is guarded from now on…
    await expect(assertP2AssemblyFresh(outDir)).resolves.toBeUndefined();
    await writeFile(join(outDir, "front_matter.tex"), "\\begin{abstract}Edited.\\end{abstract}\n");
    await expect(assertP2AssemblyFresh(outDir)).rejects.toThrow(/changed after paper\.tex was assembled/);
    // …and a real source edit still fails either way.
    await recordP2Assembly(outDir);
    await writeFile(join(outDir, "sections", "01_body.tex"), "Revised body.\n");
    await expect(assertP2AssemblyFresh(outDir)).rejects.toThrow(/changed after paper\.tex was assembled/);
  });

  it("requires a P2 baseline for legacy bundles", async () => {
    const outDir = await fixture();
    await expect(assertP2AssemblyFresh(outDir)).rejects.toThrow(/manifest is missing/);
  });
});

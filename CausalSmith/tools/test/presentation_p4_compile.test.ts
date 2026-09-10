import { afterEach, describe, expect, it, vi } from "vitest";
import { mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import type { StageIO } from "../src/presentation/pipeline.js";

const subprocess = vi.hoisted(() => vi.fn());
vi.mock("node:child_process", async (importOriginal) => ({
  ...await importOriginal<typeof import("node:child_process")>(),
  execFile: subprocess,
}));

import { stageP4 } from "../src/presentation/stages/p4_emit.js";
import { recordP2Assembly } from "../src/presentation/assembly_freshness.js";

const dirs: string[] = [];
afterEach(async () => {
  subprocess.mockReset();
  await Promise.all(dirs.splice(0).map((dir) => rm(dir, { recursive: true, force: true })));
});

async function fixture() {
  const outDir = await mkdtemp(join(tmpdir(), "p4-compile-"));
  dirs.push(outDir);
  for (const dir of ["sections", "proofs"]) await mkdir(join(outDir, dir));
  const paper = "\\documentclass{article}\n\\begin{document}\nA finite example.\n\\end{document}\n";
  for (const [name, body] of Object.entries({
    "paper.tex": paper,
    "appendix_proofs.tex": "",
    "front_matter.tex": "A finite example.",
    "formal_layer.json": JSON.stringify({ commit: null, blocks: [] }),
    "outline.md": "# Title\nExample\n# Sections\n",
    "references.bib": "",
    "equivalence_cache.json": "{}",
  })) await writeFile(join(outDir, name), body);
  await recordP2Assembly(outDir);
  const runCodex = vi.fn(async () => { throw new Error("unexpected paid dispatch"); });
  const io = {
    outDir,
    state: { notes: [] },
    ctx: { repoRoot: outDir, deps: { dryRun: false, runCodex } },
  } as unknown as StageIO;
  return { io, outDir, paper, runCodex };
}

describe("P4 mechanical compile recovery", () => {
  it("preserves authored input and returns a bounded diagnostic without a paid retry", async () => {
    const { io, outDir, paper, runCodex } = await fixture();
    subprocess.mockImplementation((_file, _args, _options, callback) => {
      callback(Object.assign(new Error("latexmk failed"), {
        stdout: "diagnostic prefix\n" + "x".repeat(6000),
        stderr: "Undefined control sequence: \\missingCommand",
      }));
    });
    const error = await stageP4(io).catch((err: Error) => err);
    expect(error).toBeInstanceOf(Error);
    expect((error as Error).message).toContain("mechanical recovery required (no model retry)");
    expect((error as Error).message).toContain("--from P2");
    expect((error as Error).message).toContain("Undefined control sequence");
    expect((error as Error).message).not.toContain("diagnostic prefix");
    expect((error as Error).message.length).toBeLessThan(2400);
    expect(subprocess).toHaveBeenCalledTimes(1);
    expect(subprocess.mock.calls[0][0]).toBe("latexmk");
    expect(runCodex).not.toHaveBeenCalled();
    expect(await readFile(join(outDir, "paper.tex"), "utf8")).toBe(paper);
    expect(await readFile(join(outDir, "front_matter.tex"), "utf8")).toBe("A finite example.");
  });

  it("continues to normal emission after successful compilation", async () => {
    const { io, runCodex } = await fixture();
    subprocess.mockImplementation((file, _args, _options, callback) => {
      callback(file === "latexmk" ? null : new Error("post-compile sentinel"), "");
    });
    await expect(stageP4(io)).rejects.toThrow("post-compile sentinel");
    expect(subprocess.mock.calls.map((call) => call[0])).toEqual(["latexmk", "git"]);
    expect(runCodex).not.toHaveBeenCalled();
  });
});

describe("P4 bibliography verification preserves publication metadata", () => {
  const bib = `@article{published,
  author = {Morgan, Alex},
  title = {Finite Sampling Bounds},
  journal = {Journal of Statistical Theory},
  year = {2024},
  volume = {19},
  pages = {101--120},
  eprint = {2101.12345}
}\n`;

  async function citedFixture(year: number, title = "Finite Sampling Bounds") {
    const f = await fixture();
    const paper = f.paper.replace("A finite example.", "A finite example \\cite{published}.");
    await writeFile(join(f.outDir, "paper.tex"), paper);
    await writeFile(join(f.outDir, "references.bib"), bib);
    await recordP2Assembly(f.outDir);
    f.io.ctx.deps.lookup = async () => ({
      title, authorFamily: "Morgan", author: "Morgan, Alex", year, authoritative: true,
    });
    subprocess.mockImplementation((file, _args, _options, callback) => {
      callback(file === "latexmk" ? null : new Error("post-compile sentinel"), "");
    });
    return f;
  }

  it("keeps the journal edition when its identifier resolves to an earlier preprint", async () => {
    const { io, outDir, runCodex } = await citedFixture(2021);
    await expect(stageP4(io)).rejects.toThrow("post-compile sentinel");
    expect(await readFile(join(outDir, "references.bib"), "utf8")).toBe(bib);
    expect(io.state.notes.some(n => n.includes("published kept with caveat"))).toBe(true);
    expect(subprocess.mock.calls.map(call => call[0])).toEqual(["latexmk", "git"]);
    expect(runCodex).not.toHaveBeenCalled();
  });

  it("continues without a caveat when the publication record agrees", async () => {
    const { io, outDir, runCodex } = await citedFixture(2024);
    await expect(stageP4(io)).rejects.toThrow("post-compile sentinel");
    expect(await readFile(join(outDir, "references.bib"), "utf8")).toBe(bib);
    expect(io.state.notes.some(n => n.includes("kept with caveat"))).toBe(false);
    expect(runCodex).not.toHaveBeenCalled();
  });

  it("keeps a hand-verified entry on its recorded authority without consulting a registry", async () => {
    const f = await citedFixture(1997, "Unrelated Infinite Limits");
    const handBib = bib.replace("  eprint = {2101.12345}\n", "  verifiedby = {ISBN 9780940600324, publisher catalogue}\n");
    await writeFile(join(f.outDir, "references.bib"), handBib);
    await recordP2Assembly(f.outDir);
    const lookup = vi.fn(f.io.ctx.deps.lookup!);
    f.io.ctx.deps.lookup = lookup;
    await expect(stageP4(f.io)).rejects.toThrow("post-compile sentinel");
    expect(lookup).not.toHaveBeenCalled();
    expect(await readFile(join(f.outDir, "references.bib"), "utf8")).toBe(handBib);
    expect(f.io.state.notes).toContain("P4: bib entry published kept with caveat: hand-verified (ISBN 9780940600324, publisher catalogue)");
    expect(f.runCodex).not.toHaveBeenCalled();
  });

  it("still stops before compilation or model calls for a different work", async () => {
    const { io, outDir, runCodex } = await citedFixture(2024, "Unrelated Infinite Limits");
    await expect(stageP4(io)).rejects.toThrow("failed re-verification: title does not match");
    await expect(stageP4(io)).rejects.toThrow("verifiedby = {<what confirmed it>}");
    expect(await readFile(join(outDir, "references.bib"), "utf8")).toBe(bib);
    expect(subprocess).not.toHaveBeenCalled();
    expect(runCodex).not.toHaveBeenCalled();
  });
});

import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, writeFile, readFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { stageP0 } from "../src/presentation/stages/p0_literature.js";
import { parseBib } from "../src/presentation/citations.js";
import type { StageIO } from "../src/presentation/pipeline.js";

/** P0 persists the raw pool and the brief before verification; a re-entry re-verifies only. */
const RAW = `@article{robins1994,
  title = {Estimation of Regression Coefficients When Some Regressors Are Not Always Observed},
  author = {Robins, James M. and Rotnitzky, Andrea and Zhao, Lue Ping},
  journal = {Journal of the American Statistical Association}, year = {1994},
  doi = {10.1080/01621459.1994.10476818}
}`;
let dir: string;
beforeEach(async () => { dir = await mkdtemp(join(tmpdir(), "p0reuse-")); });
afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

const io = (runCodex: StageIO["ctx"]["deps"]["runCodex"]): StageIO => ({
  outDir: dir,
  ctx: { repoRoot: dir, qid: "q", spec: "v1", deps: { runCodex, runClaude: async () => "", dryRun: false,
    lookup: async (e: { key: string }) => e.key === "robins1994"
      ? { title: "Estimation of regression coefficients when some regressors are not always observed", authorFamily: "Robins", year: 1994 }
      : null } },
  bank: { readme: {}, sourceBibliography: [], proposalTex: "A substantive proposal naming the anchor literature." },
  state: { notes: [] },
} as unknown as StageIO);

describe("P0 literature: persisted pool and brief are reused", () => {
  it("writes the raw pool and the brief before verification, then reuses both without a model call", async () => {
    let calls = 0;
    const first = io(async () => { calls++; return { stdout: "```bibtex\n" + RAW + "\n```\n```markdown\nBrief.\n```\n", stderr: "" }; });
    await stageP0(first);
    expect(calls).toBe(1);
    expect(await readFile(join(dir, "references_raw.bib"), "utf8")).toContain("robins1994");
    expect(await readFile(join(dir, "related_work_brief.md"), "utf8")).toBe("Brief.\n");
    expect(await readFile(join(dir, "references.bib"), "utf8")).toContain("robins1994");
    await rm(join(dir, "references.bib"));
    const second = io(async () => { throw new Error("the search must not be re-paid"); });
    await stageP0(second);
    expect(await readFile(join(dir, "references.bib"), "utf8")).toContain("robins1994");
    expect(second.state.notes.some((n) => n.includes("reused the persisted raw pool"))).toBe(true);
  });

  it("strips a model-written verifiedby mark, but honours one hand-added to the persisted pool", async () => {
    const marked = RAW.replace("  doi = ", "  verifiedby = {the model says so},\n  doi = ");
    const first = io(async () => ({ stdout: "```bibtex\n" + marked + "\n```\n```markdown\nBrief.\n```\n", stderr: "" }));
    await stageP0(first);
    const raw = await readFile(join(dir, "references_raw.bib"), "utf8");
    expect(raw).not.toContain("verifiedby");
    expect(raw).toContain("doi = ");
    // Every layout, and the entry stays parseable with all its other fields.
    const layouts = [
      `@misc{k, title = {T}, verifiedby = {ISBN 1}, year = {1995}}`,
      `@misc{k,\n  title = {T},\n  year = {1995},\n  verifiedby = {ISBN 1,\n  publisher {IMS} catalogue}\n}`,
      `@misc{k,\n  verifiedby = "ISBN 1",\n  title = {T}, year = {1995}\n}`,
    ];
    for (const layout of layouts) {
      await rm(join(dir, "references_raw.bib"));
      await rm(join(dir, "related_work_brief.md"));
      await stageP0(io(async () => ({ stdout: "```bibtex\n" + layout + "\n```\n```markdown\nBrief.\n```\n", stderr: "" }))).catch(() => undefined);
      const persisted = await readFile(join(dir, "references_raw.bib"), "utf8");
      expect(persisted).not.toContain("verifiedby");
      expect(parseBib(persisted).map((e) => [e.key, e.fields.title, e.fields.year])).toEqual([["k", "T", "1995"]]);
    }
    // The orchestrator confirms a work no registry indexes and marks the persisted pool by hand.
    await writeFile(join(dir, "references_raw.bib"), `@book{lindsay1995,
  author = {Lindsay, Bruce G.}, title = {Mixture Models}, year = {1995},
  verifiedby = {ISBN 9780940600324}
}\n`);
    await rm(join(dir, "references.bib"));
    const second = io(async () => { throw new Error("the search must not be re-paid"); });
    await stageP0(second);
    expect(await readFile(join(dir, "references.bib"), "utf8")).toContain("lindsay1995");
    expect(second.state.notes).toContain("P0: kept lindsay1995 with metadata caveat: hand-verified (ISBN 9780940600324)");
  });
});

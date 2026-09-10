import { describe, it, expect, afterAll } from "vitest";
import { rm, access, mkdtemp, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { tmpdir } from "node:os";
import { runPaperPipeline, type PaperDeps } from "../src/presentation/pipeline.js";
import { loadPaperState, savePaperState, freshPaperState } from "../src/presentation/state.js";
import { recordP2Assembly } from "../src/presentation/assembly_freshness.js";
import { acceptedBankEntry, causalSmithRoot, guardBankEntry } from "./helpers.js";

const stubDeps: PaperDeps = {
  runClaude: async () => "STUB",
  runCodex: async () => ({ stdout: "STUB", stderr: "" }),
  dryRun: true,
};

// Track whatever paper is currently banked (dry-run only loads the entry; every stage writes a stub).
const { qid: QID, spec: SPEC } = acceptedBankEntry();

describe("pipeline dry-run (integration)", () => {
  const root = causalSmithRoot();
  // NEVER the real presentationDir: a test run must not clobber live artifacts.
  const dirP = mkdtemp(join(tmpdir(), "causalsmith-dryrun-"));
  afterAll(async () => rm(await dirP, { recursive: true, force: true }));
  // Nor the real BANK entry: P1's statement audit, promotion and P5 persist into it, so a
  // stubbed run would write stub bodies into a tracked record. Snapshot now, restore after.
  afterAll(guardBankEntry(QID, SPEC));

  it("P0→P1 stops at outline checkpoint; resumes through draft to done", async () => {
    const dir = await dirP;
    const base = { repoRoot: root, qid: QID, spec: SPEC, deps: stubDeps, outDir: dir };
    const r1 = await runPaperPipeline(base);
    expect(r1.halt).toBe("checkpoint:outline");
    const s1 = await loadPaperState(dir, QID, SPEC);
    expect(s1!.stage_completed).toBe("P1");
    expect(s1!.checkpoint_pending).toBe("outline");

    const r2 = await runPaperPipeline({ ...base, resume: true });
    expect(r2.halt).toBe("checkpoint:draft");

    const r3 = await runPaperPipeline({ ...base, resume: true });
    expect(r3.halt).toBe("done");
    await access(join(dir, "p4.stub"));
    await access(join(dir, "p5.stub")); // P5 referee review runs as the terminal stage
    const s3 = await loadPaperState(dir, QID, SPEC);
    expect(s3!.stage_completed).toBe("P5");
  });

  it("refuses a flag-less re-run on a bundle with recorded state instead of restarting it", async () => {
    const dir = await dirP; // carries the state the first test left behind
    const before = await loadPaperState(dir, QID, SPEC);
    const live: PaperDeps = { ...stubDeps, dryRun: false, runCodex: async () => { throw new Error("no stage may run"); } };
    await expect(runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps: live, outDir: dir }))
      .rejects.toThrow(/already exists .*--resume/);
    expect(await loadPaperState(dir, QID, SPEC)).toEqual(before);
  });

  it("--stop-after halts without checkpoint", async () => {
    const dir = await mkdtemp(join(tmpdir(), "causalsmith-dryrun2-"));
    try {
      const r = await runPaperPipeline({
        repoRoot: root, qid: QID, spec: SPEC, deps: stubDeps, stopAfter: "P0", outDir: dir,
      });
      expect(r.halt).toBe("stopped:P0");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("--auto approves P1/P2 checkpoints and runs smoothly through P5", async () => {
    const dir = await mkdtemp(join(tmpdir(), "causalsmith-dryrun-auto-"));
    try {
      const r = await runPaperPipeline({
        repoRoot: root, qid: QID, spec: SPEC, deps: stubDeps, auto: true, outDir: dir,
      });
      expect(r.halt).toBe("done");
      await access(join(dir, "p1.stub"));
      await access(join(dir, "p2.stub"));
      await access(join(dir, "p5.stub"));
      const state = await loadPaperState(dir, QID, SPEC);
      expect(state!.stage_completed).toBe("P5");
      expect(state!.checkpoint_pending).toBeNull();
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("--auto still respects explicit --stop-after", async () => {
    const dir = await mkdtemp(join(tmpdir(), "causalsmith-dryrun-auto-stop-"));
    try {
      const r = await runPaperPipeline({
        repoRoot: root, qid: QID, spec: SPEC, deps: stubDeps, auto: true, stopAfter: "P1", outDir: dir,
      });
      expect(r.halt).toBe("stopped:P1");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("a review that is not a clean accept halts for hand revision after one referee call", async () => {
    const dir = await mkdtemp(join(tmpdir(), "causalsmith-p5-receipt-"));
    try {
      const { mkdir } = await import("node:fs/promises");
      for (const sub of ["sections", "proofs"]) await mkdir(join(dir, sub));
      for (const [name, body] of Object.entries({
        "paper.tex": "A submission.\n",
        "appendix_proofs.tex": "",
        "front_matter.tex": "A submission.",
        "formal_layer.json": '{"commit":null,"blocks":[]}\n',
        "lean_snippets.json": '{"commit":"","snippets":{}}\n',
        "outline.md": "# Title\nExample\n# Sections\n",
        "references.bib": "",
        "equivalence_cache.json": "{}",
      })) await writeFile(join(dir, name), body);
      await recordP2Assembly(dir); // sources and assembly agree, as after a completed P4
      const state = freshPaperState(QID, SPEC);
      state.stage_completed = "P4";
      await savePaperState(dir, state);
      let codexCalls = 0;
      const deps: PaperDeps = {
        ...stubDeps,
        dryRun: false,
        runCodex: async () => {
          codexCalls += 1;
          return {
            stdout: JSON.stringify({
              recommendation: "major_revision", score: 6.4, score_rationale: "r", summary: "s", strengths: [],
              findings: [{ finding_id: "x", severity: "major", kind: "prose", remedy: "rewrite", section: "Setup", issue: "i", fix: "f" }],
              questions_for_authors: [],
            }),
            stderr: "",
          };
        },
      };
      const r = await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps, from: "P5", auto: true, outDir: dir });
      expect(r.halt).toBe("p5:hand-revision");
      expect(codexCalls).toBe(1); // the referee only — nothing revises unattended
      const after = await loadPaperState(dir, QID, SPEC);
      expect(after!.notes.some((n) => n.includes("routed in p5_revision_routing.md for hand revision"))).toBe(true);
      await access(join(dir, "p5_revision_routing.md"));
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("a dry run scores once and ends without a revision loop", async () => {
    const dir = await mkdtemp(join(tmpdir(), "causalsmith-dryrun-p5-cap-"));
    try {
      const r = await runPaperPipeline({
        repoRoot: root, qid: QID, spec: SPEC, deps: stubDeps, auto: true, outDir: dir,
      });
      expect(r.halt).toBe("done");
      const state = await loadPaperState(dir, QID, SPEC);
      expect(state!.stage_completed).toBe("P5");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});

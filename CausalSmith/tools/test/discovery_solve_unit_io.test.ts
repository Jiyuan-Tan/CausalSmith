import { afterEach, describe, expect, it } from "vitest";
import { mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import {
  clearOrphanSolvePathLeases,
  readSolveUnitOutput,
  SolveUnitCarrierError,
} from "../src/discovery/solve/unit_io.js";
import { formalizationDir } from "../src/paths.js";
import type { PipelineContext } from "../src/types.js";

const roots: string[] = [];

afterEach(async () => {
  delete process.env.CAUSALSMITH_ALLOW_PARALLEL;
  await Promise.all(roots.splice(0).map((root) => rm(root, { recursive: true, force: true })));
});

describe("clearOrphanSolvePathLeases", () => {
  it("reclaims only this qid's stranded solve leases in parallel-qid mode", async () => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "solve-lease-"));
    roots.push(repoRoot);
    const ctx = {
      repoRoot,
      qid: "stat_orphan_reclaim",
      specialization: "v1",
    } as PipelineContext;
    const otherCtx = { ...ctx, qid: "stat_other_run" };
    const ownLock = path.join(formalizationDir(repoRoot, ctx.qid), "discovery", "solve_target.json.lease.lock");
    const otherLock = path.join(formalizationDir(repoRoot, otherCtx.qid), "discovery", "solve_target.json.lease.lock");
    await mkdir(ownLock, { recursive: true });
    await mkdir(otherLock, { recursive: true });
    await writeFile(path.join(ownLock, "owner-token"), "stranded\n");
    await writeFile(path.join(otherLock, "owner-token"), "live-other-qid\n");
    process.env.CAUSALSMITH_ALLOW_PARALLEL = "1";

    await clearOrphanSolvePathLeases(ctx);

    await expect(readFile(path.join(ownLock, "owner-token"), "utf8")).rejects.toMatchObject({ code: "ENOENT" });
    await expect(readFile(path.join(otherLock, "owner-token"), "utf8")).resolves.toBe("live-other-qid\n");
  });
});

describe("solve companion recovery diagnostics", () => {
  it("rejects inline long TeX fields and points to the required companion", async () => {
    const root = await mkdtemp(path.join(tmpdir(), "solve-companion-required-"));
    roots.push(root);
    const outPath = path.join(root, "solve_target.json");
    await writeFile(outPath, `${JSON.stringify({ proofs: [{ id: "thm:target", proof_tex: "Proof." }] })}\n`);

    await expect(readSolveUnitOutput(outPath, "target", { requireCompanionLongFields: true })).rejects.toThrow(
      /proofs\[0\]\.proof_tex[\s\S]*SOLVE_COMPANION_PATH|SOLVE_COMPANION_PATH[\s\S]*proofs\[0\]\.proof_tex/,
    );
  });

  it("rejects companion refs outside long TeX fields", async () => {
    const root = await mkdtemp(path.join(tmpdir(), "solve-companion-scope-"));
    roots.push(root);
    const outPath = path.join(root, "solve_target.json");
    const companionDir = path.join(root, "solve_tex");
    await mkdir(companionDir);
    await writeFile(outPath, `${JSON.stringify({ prose_updates: { tldr: { tex_ref: "tldr" } } })}\n`);
    await writeFile(path.join(companionDir, "solve_target.tex"), "%%% FIELD tldr\nprose\n");

    await expect(readSolveUnitOutput(outPath, "target", { requireCompanionLongFields: true })).rejects.toThrow(
      /prose_updates\.tldr \(tex_ref is malformed or not allowed here\)/,
    );
  });

  it("routes malformed unauthorized refs through carrier recovery", async () => {
    const root = await mkdtemp(path.join(tmpdir(), "solve-companion-malformed-"));
    roots.push(root);
    const outPath = path.join(root, "solve_target.json");
    await writeFile(outPath, `${JSON.stringify({
      prose_updates: { tldr: { tex_ref: "tldr", extra: "inline" } },
    })}\n`);

    await expect(readSolveUnitOutput(outPath, "target", { requireCompanionLongFields: true }))
      .rejects.toBeInstanceOf(SolveUnitCarrierError);
  });

  it("rejects valid and malformed refs used as array elements", async () => {
    const root = await mkdtemp(path.join(tmpdir(), "solve-companion-array-"));
    roots.push(root);
    const outPath = path.join(root, "solve_target.json");
    await writeFile(outPath, `${JSON.stringify({
      added_lemmas: [{ depends_on: [{ tex_ref: "dep" }] }],
      proposed_assumptions: [{ free_symbols: [{ tex_ref: "symbol", extra: "bad" }] }],
    })}\n`);

    await expect(readSolveUnitOutput(outPath, "target", { requireCompanionLongFields: true }))
      .rejects.toBeInstanceOf(SolveUnitCarrierError);
  });

  it("authorizes long TeX by schema position rather than matching nested key names", async () => {
    const root = await mkdtemp(path.join(tmpdir(), "solve-companion-schema-position-"));
    roots.push(root);
    const outPath = path.join(root, "solve_target.json");
    const companionDir = path.join(root, "solve_tex");
    await mkdir(companionDir);
    await writeFile(outPath, `${JSON.stringify({
      prose_updates: { sampling_model: { statement: { tex_ref: "rogue-prose" } } },
      proposed_core_edits: [{
        kind: "statement-replace",
        proposed: { proposed_statement_changes: [{ proposed: { tex_ref: "rogue-nested" } }] },
      }],
    })}\n`);
    await writeFile(
      path.join(companionDir, "solve_target.tex"),
      "%%% FIELD rogue-prose\nprose\n%%% FIELD rogue-nested\nnested\n",
    );

    await expect(readSolveUnitOutput(outPath, "target", { requireCompanionLongFields: true }))
      .rejects.toBeInstanceOf(SolveUnitCarrierError);
  });

  it("requires and resolves a statement replacement's nested partial result", async () => {
    const root = await mkdtemp(path.join(tmpdir(), "solve-companion-replacement-partial-"));
    roots.push(root);
    const outPath = path.join(root, "solve_target.json");
    const companionDir = path.join(root, "solve_tex");
    await mkdir(companionDir);
    const replacement = (partial_result: unknown) => ({
      proposed_core_edits: [{
        kind: "statement-replace",
        id: "thm:target",
        proposed: {
          id: "thm:target",
          kind: "theorem",
          statement: { tex_ref: "statement" },
          depends_on: [],
          status: "to-prove",
          obligation: { what_is_open: "step", obstruction: "gap", attempted: "route", partial_result },
        },
        reason: "correct scope",
        direction: "correct",
      }],
    });
    await writeFile(outPath, `${JSON.stringify(replacement("inline partial"))}\n`);
    await writeFile(
      path.join(companionDir, "solve_target.tex"),
      "%%% FIELD statement\nTarget statement.\n%%% FIELD partial\nCompanion partial.\n",
    );
    await expect(readSolveUnitOutput(outPath, "target", { requireCompanionLongFields: true }))
      .rejects.toBeInstanceOf(SolveUnitCarrierError);

    await writeFile(outPath, `${JSON.stringify(replacement({ tex_ref: "partial" }))}\n`);
    const parsed = await readSolveUnitOutput(outPath, "target", { requireCompanionLongFields: true });
    expect(parsed.proposed_core_edits[0]).toMatchObject({
      proposed: { statement: "Target statement.", obligation: { partial_result: "Companion partial." } },
    });
  });

  it("treats legacy statement and definition proposals as long TeX fields", async () => {
    const root = await mkdtemp(path.join(tmpdir(), "solve-companion-alias-"));
    roots.push(root);
    const outPath = path.join(root, "solve_target.json");
    await writeFile(outPath, `${JSON.stringify({
      proposed_statement_changes: [{ proposed: "claim" }],
      proposed_definition_changes: [{ proposed: "construction" }],
    })}\n`);

    await expect(readSolveUnitOutput(outPath, "target", { requireCompanionLongFields: true })).rejects.toThrow(
      /proposed_statement_changes\[0\]\.proposed \(expected tex_ref\)[\s\S]*proposed_definition_changes\[0\]\.proposed \(expected tex_ref\)/,
    );
  });

  it("gives raw-companion guidance with the ref and block-relative line", async () => {
    const root = await mkdtemp(path.join(tmpdir(), "solve-companion-diagnostic-"));
    roots.push(root);
    const outPath = path.join(root, "solve_target.json");
    const companionDir = path.join(root, "solve_tex");
    await mkdir(companionDir);
    await writeFile(outPath, `${JSON.stringify({ proofs: [{ proof_tex: { tex_ref: "proof-1" } }] })}\n`);
    await writeFile(
      path.join(companionDir, "solve_target.tex"),
      "%%% FIELD proof-1\nfirst line\n\\widehat\\tau + \f" + "rac12\n",
    );

    await expect(readSolveUnitOutput(outPath, "target")).rejects.toThrow(
      /raw companion blocks[\s\S]*not \\\\frac[\s\S]*preserving TeX syntax[\s\S]*\\\\ row terminators[\s\S]*tex_ref 'proof-1', block line 2: U\+000C/,
    );
  });
});

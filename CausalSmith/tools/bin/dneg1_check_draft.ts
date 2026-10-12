#!/usr/bin/env -S npx tsx
/**
 * Run the D-1.2 producer-boundary check on an authored proposal draft and print
 * the findings the pipeline gate would feed back — JSON parse + shape
 * canonicalization, run-identity stamp, proposal gate (G1–G7, GP1–GP3), schema, TeX
 * sealability and authored metadata, in that order (`auditAuthoredDraft`).
 * The author runs it once before printing its receipt; the pipeline still runs
 * the same check on hand-off, so this is a preview, not a bypass.
 *
 * The run is located from the draft path (nearest ancestor holding `state.json`).
 * Limitation: on the first cold-start of an upgrade run the pipeline takes the
 * cluster from the banked parent (held in memory, not in state.json), so this
 * check falls back to the qid-prefix cluster and may differ there.
 *
 * Usage (from CausalSmith/tools):
 *   npm run proposal:check -- --mode <cold-start|revise|pivot|kernel-replace|draft-rebuild> <draft path>
 *
 * Exit 0 when the draft passes, 1 when it has findings, 2 on usage errors.
 */
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import {
  auditAuthoredDraft,
  loadParentContract,
  type Neg1_2Mode,
} from "../src/discovery/stages/neg1_2_author.js";
import { clusterFor } from "../src/discovery/cluster_setup.js";
import { clusterFromLeanSubdir } from "../src/pipeline_support.js";
import { readArgs } from "../src/shared/cli_args.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import type { PipelineContext, StateJson } from "../src/types.js";

const MODES: readonly Neg1_2Mode[] = ["cold-start", "revise", "pivot", "kernel-replace", "draft-rebuild"];

function findRunDir(start: string): string | null {
  let cur = path.resolve(start);
  for (;;) {
    if (existsSync(path.join(cur, "state.json"))) return cur;
    const parent = path.dirname(cur);
    if (parent === cur) return null;
    cur = parent;
  }
}

async function main(): Promise<void> {
  const argv = process.argv.slice(2);
  const cli = readArgs(argv);
  const modeArg = cli.value("--mode");
  const draft = argv.filter((a, i) => !a.startsWith("--") && argv[i - 1] !== "--mode")[0];
  if (!draft || !modeArg || !(MODES as readonly string[]).includes(modeArg)) {
    console.error(`Usage: dneg1_check_draft.ts --mode <${MODES.join("|")}> <draft path>`);
    process.exitCode = 2;
    return;
  }
  const draftPath = path.resolve(draft);
  if (!existsSync(draftPath)) {
    console.error(`[WRITE] ${draftPath}: the draft file does not exist`);
    process.exitCode = 1;
    return;
  }
  const runDir = findRunDir(path.dirname(draftPath));
  if (!runDir) {
    console.error(`cannot locate the run: no state.json above ${draftPath}`);
    process.exitCode = 2;
    return;
  }
  const state = JSON.parse(readFileSync(path.join(runDir, "state.json"), "utf8")) as StateJson;
  if (!state.qid || !state.specialization) {
    console.error(`${path.join(runDir, "state.json")} does not record qid/specialization`);
    process.exitCode = 2;
    return;
  }
  const repoRoot = findCausalSmithRoot(runDir);
  const ctx: PipelineContext = { repoRoot, qid: state.qid, specialization: state.specialization, dryRun: true, resume: true };
  const upgradeFrom = state.pre_d0_intent?.upgrade_from ?? state.proposed_from?.upgrade_from;
  const parentContract = upgradeFrom ? await loadParentContract(repoRoot, upgradeFrom) : null;

  const audit = auditAuthoredDraft({
    rawText: readFileSync(draftPath, "utf8"),
    draftPath,
    mode: modeArg as Neg1_2Mode,
    identity: {
      qid: ctx.qid,
      specialization: ctx.specialization,
      expectedCluster: clusterFor(ctx, state) ?? clusterFromLeanSubdir(state.lean_subdir),
      upgradeFrom,
      parentContract,
    },
    inherited: {
      seed_list: state.proposed_from?.seed_list,
      seed_details: state.proposed_from?.seed_details,
    },
  });
  for (const warning of audit.warnings) console.error(warning);
  if (!audit.ok) {
    console.log(`REJECTED (${audit.kind}) — the pipeline gate would feed back:\n${audit.feedback}`);
    process.exitCode = 1;
    return;
  }
  if (audit.droppedKeys.length > 0) {
    console.log(`note: keys with no persistence home are dropped at hand-off: ${audit.droppedKeys.join(", ")}`);
  }
  console.log("PASS — the draft passes the producer-boundary check.");
}

main().catch((err) => {
  console.error(err instanceof Error ? err.message : String(err));
  process.exitCode = 2;
});

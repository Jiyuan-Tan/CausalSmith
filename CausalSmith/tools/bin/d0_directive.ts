#!/usr/bin/env -S npx tsx
/**
 * Orchestrator-only: inject a DIRECTIVE into the D0 escalation journal so the next
 * D0 solve round acts on it. A directive is free text plus, optionally, the
 * statement ids the round must dispatch (`--require-core-target`, repeatable; a
 * proved target is reopened for that round only). Without targets the whole
 * paper is dispatched.
 *
 * An EXACT mechanical edit is not a directive any more: edit core.json and run
 * `d0_vc.ts <qid> <spec> commit --note "…"`.
 *
 * Usage:
 *   npx tsx tools/bin/d0_directive.ts <qid> <spec> --directive "<direction / construction>"
 *   npx tsx tools/bin/d0_directive.ts <qid> <spec> --directive -        # read from stdin
 *   npx tsx tools/bin/d0_directive.ts <qid> <spec> --directive "…" --note "<short note>" --require-core-target thm:main
 *   npx tsx tools/bin/d0_directive.ts <qid> <spec> --directive "…" --provenance-only   # record, do not dispatch
 *
 * Capture artifacts (literal `null` lines from a mis-built `jq` pipe, a raw codex
 * event stream) are stripped or refused — see `src/shared/directive_text.ts`.
 * `--allow-dirty-capture` writes the text verbatim.
 */
import { readFileSync } from "node:fs";
import process from "node:process";
import type { PipelineContext } from "../src/types.js";
import { appendEscalationLog } from "../src/discovery/escalation_log.js";
import { sanitizeDirectiveForCli } from "../src/shared/directive_text.js";
import { loadState, saveState } from "../src/state.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";
import { withRunHeartbeat } from "../src/shared/run_heartbeat.js";

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const cli = readArgs(args);
  let directive = cli.value("--directive");
  const note = cli.value("--note");
  const requiredCoreTargets = cli.values("--require-core-target");
  const provenanceOnly = cli.bool("--provenance-only");
  const [qid, spec] = cli.positionals();
  if (!qid || !spec || directive === undefined) {
    console.error('Usage: d0_directive.ts <qid> <spec> --directive "<direction>" [--note "<note>"] [--require-core-target <id> ...] [--provenance-only]  (--directive - reads stdin)');
    process.exitCode = 1;
    return;
  }
  if (directive === "-") directive = readFileSync(0, "utf8").trim();
  const text = sanitizeDirectiveForCli(directive ?? "", args.includes("--allow-dirty-capture"));
  if (text === null) {
    process.exitCode = 1;
    return;
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  await withRunHeartbeat(repoRoot, qid, spec, async () => {
    const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: true };
    const state = await loadState(repoRoot, qid, spec);
    const round = state.flags.d0_loop_counters?.solve_rounds ?? 0;
    // Pin the pipeline BEFORE publishing the decision: a crash between the two costs
    // one harmless extra D0 pass; the reverse order could let a resume enter F1 over
    // an unaddressed directive.
    if (!provenanceOnly && state.stage_completed !== "-0.5") {
      state.stage_completed = "-0.5";
      await saveState(repoRoot, qid, spec, state);
    }
    await appendEscalationLog(ctx, {
      round,
      ...(note ? { note } : {}),
      directive: text,
      ...(requiredCoreTargets.length > 0 ? { required_core_targets: requiredCoreTargets } : {}),
      ...(provenanceOnly ? { provenance_only: true } : {}),
    });
    console.log(
      provenanceOnly
        ? `Recorded a provenance-only journal entry (round ${round}) for ${qid} / ${spec}; no re-solve is triggered.`
        : `Appended a D0 directive (round ${round}) for ${qid} / ${spec}` +
          (requiredCoreTargets.length > 0 ? ` targeting ${requiredCoreTargets.join(", ")}` : " (whole paper)") +
          ". --resume re-enters D0 and the next solve round renders it.",
    );
  });
}

main().catch((e) => {
  console.error(e);
  process.exitCode = 1;
});

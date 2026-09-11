#!/usr/bin/env node
/**
 * causalsmith present <qid> <spec> [--resume] [--auto] [--dry-run] [--stop-after P0..P5] [--from P0..P6] [--promote-again] [--refresh-frozen-bodies]
 *
 * Presentation pipeline: accepted bank entry → arXiv-grade paper bundle → P5
 * referee review. Normally halts at two user checkpoints (after P1: outline + bibliography;
 * after P2: first full draft); --auto approves both while preserving hard halts. The
 * final stage P5 sends the paper to a codex referee and writes p5_review.{json,md}.
 * Findings are routed in p5_revision_routing.md for the orchestrator's hand revision;
 * there is no automatic reviser pass.
 */
import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { runPaperPipeline, type PaperDeps } from "./pipeline.js";
import { PaperStage } from "./types.js";
import { presentationDir, ensureLogsDir } from "./paths.js";
import { findCausalSmithRoot } from "../shared/repo_root.js";
import { withAgentLogging } from "./agent_log.js";
import { runCodex } from "../shared/codex.js";
import { withRunHeartbeatAt } from "../shared/run_heartbeat.js";
import { runClaude } from "../workers/claude.js";
import { MODELS } from "../models.js";
import { withPresentationTokenUsage } from "./token_usage.js";
import { summarizeTokenUsage, writeTokenUsageSummary } from "../token_usage.js";

function usage(): never {
  console.error(
    "usage: causalsmith present <qid> <spec> [--resume] [--auto] [--dry-run] [--stop-after P0..P5] [--from P0..P6] [--promote-again] [--refresh-frozen-bodies]",
  );
  process.exit(2);
}

/** Run the presentation pipeline behind `causalsmith present`. */
export async function runPresentationCli(argv: string[]): Promise<void> {
  const positional: string[] = [];
  let resume = false;
  let auto = false;
  let dryRun = false;
  let stopAfter: string | undefined;
  let from: string | undefined;
  let refreshFrozenBodies = false;
  let promoteAgain = false;
  // Flags folded into file conventions or other flags; fail loudly with the replacement.
  const REMOVED: Record<string, string> = {
    "--reassemble": "--from P2 reassembles whenever front_matter.tex exists (delete it to draft afresh)",
    "--slides": "use --from P6",
    "--refresh-slides": "delete slides.md (and slides_cache.json) and run --from P6",
    "--revise": "read p5_revision_routing.md, which the pipeline writes with every review",
    "--refresh-statement-audit": "use --from P1 (only changed statements are re-judged)",
    "--max-p5-reviews": "every entry scores once and halts for hand revision; there is no automatic revision pass",
  };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--resume") resume = true;
    else if (a === "--auto") auto = true;
    else if (a === "--dry-run") dryRun = true;
    else if (a === "--refresh-frozen-bodies") refreshFrozenBodies = true;
    else if (a === "--promote-again") promoteAgain = true;
    else if (a in REMOVED) {
      console.error(`${a} was removed: ${REMOVED[a]}`);
      process.exit(2);
    }
    else if (a === "--stop-after") {
      const value = argv[++i];
      if (!value || value.startsWith("--")) usage();
      stopAfter = value;
    }
    else if (a === "--from") {
      const value = argv[++i];
      if (!value || value.startsWith("--")) usage();
      from = value;
    }
    else if (a.startsWith("--")) usage();
    else positional.push(a);
  }
  if (positional.length !== 2) usage();
  const [qid, spec] = positional;
  const parsedStop = stopAfter === undefined ? undefined : PaperStage.parse(stopAfter);
  const parsedFrom = from === undefined ? undefined : PaperStage.parse(from);
  if (parsedStop === "P6") {
    console.error("P6 (slides) is not part of the P0–P5 loop — run it with --from P6 after P5 settles");
    process.exit(2);
  }
  if (refreshFrozenBodies && parsedFrom !== "P1") {
    console.error("--refresh-frozen-bodies requires --from P1 (it releases the audit-frozen bodies before the layer is re-planned)");
    process.exit(2);
  }
  const repoRoot = findCausalSmithRoot(process.cwd());

  const baseDeps: PaperDeps = {
    codexModel: MODELS.codexPresentation,
    runClaude: (args) => runClaude(args),
    // Presentation authoring uses the dedicated 5.5 tier for literature breadth and
    // journal-style prose. Individual stages may override it (P5 review uses Sol).
    // Env: CAUSALEAN_MODEL_CODEX_PRESENT.
    runCodex: (args) => runCodex({ cwd: args.cwd, prompt: args.prompt, reasoningEffort: args.reasoningEffort, leanLsp: args.leanLsp, webSearch: args.webSearch, model: args.model ?? MODELS.codexPresentation, sandboxMode: args.sandboxMode, onUsage: args.onUsage, outputSchema: args.outputSchema }),
    dryRun,
  };
  // Per-run agent-call transcript (every codex/claude INPUT + OUTPUT), mirroring
  // causalsmith's `_agent_logs`. Created once at run start so the folder exists before
  // any stage dispatches; calls append across --resume / --from re-entries.
  const runLogsDir = ensureLogsDir(repoRoot, qid, spec);
  const logFile = join(runLogsDir, "agent_calls.log");
  const deps = withAgentLogging(baseDeps, logFile);

  // P6 — slides. Deliberately OUTSIDE runPaperPipeline: it is terminal and optional,
  // runs only once the paper is settled (P5 completed, nothing pending), and must
  // never join the P0–P5 revision loop's cache fan-out. One codex call; slides.md is
  // an authored source whose hand edits survive re-runs (see stages/p6_slides.ts).
  if (parsedFrom === "P6") {
    // `--auto` and `--resume` are accepted and inert here: P6's checkpoint is the orchestrator's
    // slides review, and P6 always continues from the settled paper.
    if (refreshFrozenBodies || promoteAgain || stopAfter) usage();
    const { loadBankEntry } = await import("./bank.js");
    const { loadPaperState, savePaperState } = await import("./state.js");
    const { stageP6 } = await import("./stages/p6_slides.js");
    const outDir = presentationDir(repoRoot, qid, spec);
    await withRunHeartbeatAt(runLogsDir, qid, spec, async () => {
      const state = await loadPaperState(outDir, qid, spec);
      if (!state) throw new Error("P6 requires an existing presentation run — run the paper pipeline first");
      // "P5 settled" = the referee has reviewed the CURRENT emitted paper and nothing is
      // mid-flight. A post-P5 `--from P4` re-emit legitimately leaves stage_completed=P4,
      // so the review file (P5 archives every pass) plus a P4/P5 boundary is the check —
      // not stage_completed === "P5" alone.
      const reviewed = await readFile(join(outDir, "p5_review.json"), "utf8").then(() => true, () => false);
      if (!reviewed || state.checkpoint_pending || !(state.stage_completed === "P4" || state.stage_completed === "P5")) {
        throw new Error(
          `P6 runs only after P5 is settled (stage_completed=${state.stage_completed}, ` +
            `checkpoint_pending=${state.checkpoint_pending ?? "none"}, p5_review.json ${reviewed ? "present" : "absent"}) — finish the paper first`,
        );
      }
      const bank = await loadBankEntry(repoRoot, qid, spec);
      await stageP6({
        ctx: { repoRoot, qid, spec, deps: withPresentationTokenUsage(deps, outDir, "P6"), outDir },
        state,
        bank,
        outDir,
      });
      await savePaperState(outDir, state);
      await surfaceTokenUsage(outDir);
      const note = state.notes.filter((n) => n.startsWith("P6:")).at(-1);
      console.log(`${note ?? "P6: done"}\nCHECKPOINT (slides): read ${outDir}/slides.md for CLARITY — hand-edit it directly; edits are preserved.`);
    });
    return;
  }

  // P0--P5 mutate one shared bundle.  A foreground terminal may report its
  // child complete before the child exits, so refuse a second invocation until
  // the first has released its durable heartbeat.
  const { halt } = await withRunHeartbeatAt(runLogsDir, qid, spec, () =>
    runPaperPipeline({ repoRoot, qid, spec, deps, resume, auto, stopAfter: parsedStop, from: parsedFrom,
      refreshFrozenBodies, promoteAgain }),
  );
  const outDir = presentationDir(repoRoot, qid, spec);
  await surfaceTokenUsage(outDir);
  if (halt === "checkpoint:outline") {
    console.log(`CHECKPOINT (outline): review ${outDir}/outline.md, formal_layer.tex and references.bib, then rerun with --resume.`);
  } else if (halt === "checkpoint:draft") {
    console.log(`CHECKPOINT (draft): review ${outDir}/paper.tex, then rerun with --resume.`);
  } else if (halt === "done") {
    await surfaceReview(outDir);
  } else if (halt === "p5:hand-revision") {
    console.log(`P5 SCORED: revise by hand from ${outDir}/p5_review.md and p5_revision_routing.md, then re-enter with --from P2 (or --from P1) to rescore.`);
  } else {
    console.log(`CausalSmith present halt: ${halt} (artifacts in ${outDir})`);
  }
}

/** Persist and print the exact cumulative model-call total known to the P pipeline. */
async function surfaceTokenUsage(outDir: string): Promise<void> {
  const summary = await summarizeTokenUsage(outDir);
  await writeTokenUsageSummary(outDir, summary);
  const missing = summary.pipeline_codex.calls_missing_usage + summary.pipeline_claude.calls_missing_usage;
  console.log(
    `Presentation pipeline tokens: ${summary.pipeline_tokens_consumed} ` +
      `(codex ${summary.pipeline_codex.total_tokens}, claude ${summary.pipeline_claude.total_tokens}` +
      `${missing > 0 ? `; ${missing} call(s) missing usage` : ""}).`,
  );
}

/** Print the P5 referee verdict so the orchestrator acts on it. */
async function surfaceReview(outDir: string): Promise<void> {
  const raw = await readFile(join(outDir, "p5_review.json"), "utf8").catch(() => null);
  if (raw === null) {
    console.log(`CausalSmith present halt: done (artifacts in ${outDir})`);
    return;
  }
  const r = JSON.parse(raw) as { recommendation: string; findings?: { severity: string }[] };
  const findings = r.findings ?? [];
  const majors = findings.filter((f) => f.severity === "major").length;
  if (r.recommendation === "accept" && findings.length === 0) {
    console.log(`P5 REVIEW: accept, no findings. Paper bundle ready in ${outDir}.`);
    return;
  }
  console.log(
    `P5 REVIEW: ${r.recommendation} — ${findings.length} findings (${majors} major). See ${outDir}/p5_review.md.\n` +
      `Holistic automatic revisions are exhausted; use p5_revision_routing.md to adjudicate the residual findings.`,
  );
}

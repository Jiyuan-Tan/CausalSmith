// D-1.1 (literature scout + gaps context) — first framework-ported stage.
// Shape: assembleContext → dispatchAgents → parseOutputs → decide (pure) → persist.
// The verdict logic is the pure `decideLitReviewOutcome`; I/O stays in the thin
// runner. See internal/plans/superpowers/specs/2026-07-20-dstage-framework-rewrite-design.md.

import { mkdir, readFile } from "node:fs/promises";
import { z } from "zod";
import { MODEL_PLAN } from "../../constants.js";
import type { PipelineContext, StageResult, StateJson } from "../../types.js";
import { artifactPaths, readPrompt, type StageDeps } from "../../pipeline_support.js";
import { dispatchAgent } from "../../framework/agent_dispatch.js";
import { normalizeRawModelJson } from "../core/latex_serialization.js";
import { gapsJsonPath } from "../../paths.js";
import { writeJsonAtomic } from "../../shared/json_atomic.js";

/** Pure verdict over the scout's parsed stdout JSON.
 *
 *  Contract (see the decision-table test):
 *  - a payload with NEITHER `n_open_problems` NOR `open_problems` is MALFORMED —
 *    a wrong-object parse (echoed template, narration) must not force a pivot
 *    that discards a healthy angle (the most expensive silent failure in the
 *    D phase);
 *  - a missing `status` keeps the historical default (completed — back-compat
 *    for outputs that omit the field); a PRESENT but unrecognized verdict halts
 *    as needs-pivot instead of silently advancing;
 *  - a completed harvest with fewer than 3 open problems becomes needs-pivot
 *    (the lit-review prompt requires thin completed payloads to halt). */
export type LitReviewDecision =
  | { kind: "completed"; nOpen: number }
  | { kind: "needs-pivot"; nOpen: number }
  | { kind: "malformed"; detail: string };

export function decideLitReviewOutcome(json: Record<string, unknown>): LitReviewDecision {
  const hasCount = typeof json.n_open_problems === "number" && Number.isFinite(json.n_open_problems);
  const hasList = Array.isArray(json.open_problems);
  if (!hasCount && !hasList) {
    return {
      kind: "malformed",
      detail: `payload carries NEITHER n_open_problems NOR open_problems (keys: ${
        Object.keys(json).slice(0, 12).join(", ") || "<none>"
      })`,
    };
  }
  const nOpen = hasCount
    ? Math.max(0, Math.floor(json.n_open_problems as number))
    : (json.open_problems as unknown[]).length;
  const status: "completed" | "needs-pivot" =
    typeof json.status !== "string" || json.status === "completed" ? "completed" : "needs-pivot";
  if (status === "completed" && nOpen < 3) return { kind: "needs-pivot", nOpen };
  return { kind: status, nOpen };
}

const nonEmptyString = z.string().trim().min(1);
const nonEmptyProvenanceString = z.string().refine((value) => value.trim().length > 0);
function boundedDisplayString(maxLength: number) {
  return z.preprocess(
    (value) => typeof value === "string" && value.length > maxLength
      ? value.slice(0, maxLength)
      : value,
    nonEmptyString.max(maxLength),
  );
}
const sourceRefSchema = z.discriminatedUnion("kind", [
  z.object({
    kind: z.literal("paper"),
    bibkey: nonEmptyString,
    claim: nonEmptyString,
    author: nonEmptyString,
    year: z.number().int(),
    venue: nonEmptyString,
    url_or_doi: nonEmptyString,
  }).strict(),
  z.object({
    kind: z.literal("prior_proposal"),
    path: nonEmptyString,
    qid: nonEmptyString,
    spec: nonEmptyString,
    where: nonEmptyString,
    excerpt: boundedDisplayString(120),
  }).strict(),
]);
const openProblemSchema = z.object({
  open_problem: nonEmptyString,
  source: z.enum(["web", "prior_proposal", "both"]),
  source_refs: z.array(sourceRefSchema).min(1),
  why_unsolved: nonEmptyString,
  what_a_resolution_would_look_like: nonEmptyString,
  cluster_hint: z.enum(["panel", "exactid", "partialid", "stat", "experimentation", "scm"]),
  exemplars: z.object({
    writing_exemplar: z.union([z.object({
      bibkey: nonEmptyString,
      arxiv_id_or_doi: nonEmptyString,
      why: nonEmptyString,
      motivation_arc: nonEmptyString,
    }).strict(), z.null()]),
    method_exemplars: z.array(z.object({
      bibkey: nonEmptyString,
      arxiv_id_or_doi: nonEmptyString,
      role: z.enum(["identification", "estimation_inference"]),
      technique: nonEmptyString,
      why_closest: nonEmptyString,
    }).strip()).nullable().transform((value) => value ?? []),
  }).strict(),
}).strict().superRefine((value, ctx) => {
  const kinds = new Set(value.source_refs.map((ref) => ref.kind));
  if (value.source === "web" && !kinds.has("paper")) {
    ctx.addIssue({ code: z.ZodIssueCode.custom, message: "web opportunity lacks a paper source" });
  }
  if (value.source === "prior_proposal" && !kinds.has("prior_proposal")) {
    ctx.addIssue({ code: z.ZodIssueCode.custom, message: "prior-proposal opportunity lacks a prior source" });
  }
  if (value.source === "both" && (!kinds.has("paper") || !kinds.has("prior_proposal"))) {
    ctx.addIssue({ code: z.ZodIssueCode.custom, message: "both-sourced opportunity lacks one source kind" });
  }
});
const scoutArtifactSchema = z.object({
  status: z.enum(["completed", "needs-pivot"]),
  gaps_path: nonEmptyString,
  topic: nonEmptyProvenanceString,
  n_open_problems: z.number().int().nonnegative(),
  by_source: z.object({
    web: z.number().int().nonnegative(),
    prior_proposal: z.number().int().nonnegative(),
    both: z.number().int().nonnegative(),
  }),
  open_problems: z.array(openProblemSchema),
  literature_map: z.string(),
  prior_proposal_map: z.string(),
  artifacts: z.array(nonEmptyString).min(1),
}).strict().superRefine((value, ctx) => {
  if (value.n_open_problems !== value.open_problems.length) {
    ctx.addIssue({ code: z.ZodIssueCode.custom, message: "n_open_problems disagrees with open_problems.length" });
  }
  const actualBySource = { web: 0, prior_proposal: 0, both: 0 };
  for (const problem of value.open_problems) actualBySource[problem.source] += 1;
  for (const source of ["web", "prior_proposal", "both"] as const) {
    if (value.by_source[source] !== actualBySource[source]) {
      ctx.addIssue({ code: z.ZodIssueCode.custom, message: `by_source.${source} disagrees with open_problems` });
    }
  }
  if ((value.status === "completed") !== (value.n_open_problems >= 3)) {
    ctx.addIssue({ code: z.ZodIssueCode.custom, message: "status disagrees with the three-opportunity threshold" });
  }
});

/** Bind the scout artifact to the orchestrator-owned topic.
 *
 * The topic is input provenance, not model-authored content.  Treating the
 * scout's lossy echo as authoritative made an otherwise valid harvest fail
 * whenever the model shortened a long topic. */
export function bindScoutTopic(
  json: Record<string, unknown>,
  expectedTopic: string,
): Record<string, unknown> {
  return { ...json, topic: expectedTopic };
}

/** Replace every filesystem/provenance field with orchestrator-owned values.
 *
 * The scout supplies research content only.  In particular, a path echoed by
 * the model is never inspected or used as a publication source. */
export function bindScoutProvenance(
  json: Record<string, unknown>,
  expectedTopic: string,
  gapsPath: string,
): Record<string, unknown> {
  return {
    ...json,
    topic: expectedTopic,
    gaps_path: gapsPath,
    artifacts: [gapsPath],
  };
}

export function parseStrictScoutStdout(
  stdout: string,
  expectedTopic: string,
  gapsPath: string,
):
  | { ok: true; json: z.infer<typeof scoutArtifactSchema> }
  | { ok: false; error: string } {
  const normalized = normalizeRawModelJson(stdout).trim();
  let raw: unknown;
  try {
    raw = JSON.parse(normalized);
  } catch (error) {
    return { ok: false, error: `no exact JSON object (${error instanceof Error ? error.message : String(error)})` };
  }
  if (raw === null || typeof raw !== "object" || Array.isArray(raw)) {
    return { ok: false, error: "stdout must be exactly one JSON object" };
  }
  const validated = scoutArtifactSchema.safeParse(
    bindScoutProvenance(raw as Record<string, unknown>, expectedTopic, gapsPath),
  );
  if (!validated.success) {
    return { ok: false, error: validated.error.issues[0]?.message ?? "schema mismatch" };
  }
  return { ok: true, json: validated.data };
}

function persistScoutDecision(args: {
  state: StateJson;
  gapsPath: string;
  decision: Exclude<LitReviewDecision, { kind: "malformed" }>;
  recovered: boolean;
}): StageResult {
  args.state.gaps = {
    gaps_path: args.gapsPath,
    n_open_problems: args.decision.nOpen,
    status: args.decision.kind,
  };

  const verb = args.recovered ? "recovered written artifact with" : "harvested";
  if (args.decision.kind === "needs-pivot") {
    return {
      stage: "-1.1",
      status: "checkpoint",
      advance: false,
      message:
        `Stage -1.1 needs-pivot — ${verb} ${args.decision.nOpen} open problem(s); topic anchor too generic; ` +
        "orchestrator must pivot the topic",
      artifacts: [args.gapsPath],
    };
  }

  return {
    stage: "-1.1",
    status: "completed",
    message: `Stage -1.1 ${verb} ${args.decision.nOpen} open problems at ${args.gapsPath}`,
    artifacts: [args.gapsPath],
  };
}

/**
 * Stage -1.1 literature scout: mine open problems from web search + prior
 * causalsmith proposals/reviewer JSONs and emit a structured `gaps.json` substrate
 * the Stage -1.2 proposer anchors its seeds to. Runs once per pipeline run; on
 * pivots/revises the gaps payload is reused (literature substrate is
 * angle-agnostic).
 *
 * Skipped silently when --propose is not set, mirroring the Stage -1.2 gate.
 * On `needs-pivot` (n_open_problems < 3) the handler returns a `checkpoint`
 * with `advance: false`, which HALTS the pipeline loop (see pipeline.ts — the
 * loop breaks on checkpoint). The run does NOT fall through to -1.2; the
 * operator must pivot the topic and re-run. Because of this, the proposer's
 * inline Step 0a fallback is reached only in the rare degraded case where
 * gaps.json was written + advanced but is missing/unreadable by the time -1.2
 * runs and no cached literature_map survives on state.proposed_from.
 */
export async function runStageNeg1_1(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<StageResult> {
  if (!args.ctx.proposeTopic) {
    return { stage: "-1.1", status: "skipped", message: "lit-review stage skipped (no --propose)" };
  }
  if (args.state.gaps && !args.state.pre_d0_intent?.scout_refresh) {
    // A `needs-pivot` harvest is NOT a completed lit review. `state.gaps` is written and
    // persisted BEFORE the checkpoint returns, and `pipeline.ts` selects the entry stage on
    // `state.gaps` being truthy — so without this guard a resume skips straight past this
    // stage and pays for a full D-1.2 author (40-min budget) plus a D-0.5 review on a topic
    // the scout had already declared too thin.
    if (args.state.gaps.status === "needs-pivot") {
      return {
        stage: "-1.1",
        status: "checkpoint",
        advance: false,
        message:
          `Stage -1.1 previously harvested only ${args.state.gaps.n_open_problems} open problem(s) and returned ` +
          `needs-pivot: the topic is too thin to author against. A resume must NOT proceed to D-1.2 on it. ` +
          `Pivot the topic under a NEW qid (the durable pre-D0 intent binds this qid to its topic), or if you ` +
          `disagree with the scout, re-enter with --resume --from-stage -1.1 to force a re-harvest.`,
      };
    }
    return {
      stage: "-1.1",
      status: "skipped",
      message: `lit-review already complete: ${args.state.gaps.n_open_problems} open problems at ${args.state.gaps.gaps_path}`,
    };
  }

  // ---- assembleContext ------------------------------------------------------
  const paths = artifactPaths(args.ctx, args.state);
  await mkdir(paths.formalizationDir, { recursive: true });
  const gapsPath = gapsJsonPath(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization);

  const litReviewPrompt = await readPrompt(args.ctx, "stage_neg1_1_lit_review.txt");
  const upgradeBlock = args.ctx.upgradeFrom
    ? [
        "",
        "=== UPGRADE CONTEXT ===",
        `parent_qid: ${args.ctx.upgradeFrom.parent_qid}`,
        `parent_spec: ${args.ctx.upgradeFrom.parent_spec}`,
        `parent_tier: ${args.ctx.upgradeFrom.parent_tier}`,
        `upgrade_axis: ${args.ctx.upgradeFrom.upgrade_axis}`,
        "The parent's bank entry README is the highest-priority Track-A source. Walk it first.",
        "=== END UPGRADE CONTEXT ===",
      ].join("\n")
    : "";

  const prompt = [
    litReviewPrompt,
    "",
    "=== ORCHESTRATOR-PROVIDED INPUTS ===",
    `Topic: ${args.ctx.proposeTopic ?? "(none)"}`,
    `qid: ${args.ctx.qid}`,
    `specialization: ${args.ctx.specialization}`,
    `gaps artifact path: ${gapsPath}`,
    upgradeBlock,
    "",
    "Artifact publication is orchestrator-owned for this stage. Do not write any file.",
    "Return the research payload only on stdout; topic, gaps_path, and artifacts are bound and published by TypeScript.",
    "Emit exactly one JSON object to stdout matching the schema in the prompt.",
  ]
    .filter((s) => s !== "")
    .join("\n");

  // ---- dispatchAgents -------------------------------------------------------
  const out = await dispatchAgent({
    ctx: args.ctx,
    deps: args.deps,
    stage: "-1.1",
    label: "D-1.1 lit-review",
    prompt,
    promptSources: [
      "prompts/D-1/stage_neg1_1_lit_review.txt",
      ...(upgradeBlock ? ["upgrade-context"] : []),
    ],
    model: MODEL_PLAN.stageNeg1_1_litReview.model,
    reasoningEffort: MODEL_PLAN.stageNeg1_1_litReview.effort,
    inactivityTimeoutMs: 40 * 60 * 1000,
  });

  // ---- parseOutputs ---------------------------------------------------------
  // The scout quotes estimands and rates from the literature, so its stdout is a
  // TeX-bearing model boundary: normalize the raw bytes (where an under-escaped
  // `\theta` is still distinguishable from tab + "heta") before the JSON funnel.
  const parsed = parseStrictScoutStdout(out.stdout, args.ctx.proposeTopic, gapsPath);
  if (!parsed.ok) {
    return {
      stage: "-1.1",
      status: "checkpoint",
      advance: false,
      message: `Stage -1.1 stdout is not a valid scout artifact (${parsed.error}); inspect codex logs before retrying`,
    };
  }

  // The model supplies content, not a path or a file.  Publish only the
  // schema-validated object whose provenance was deterministically rebound.
  await writeJsonAtomic(gapsPath, parsed.json);

  if (args.state.pre_d0_intent?.scout_refresh) {
    // A deliberate re-scout: the old proposal was drafted against the stale gaps,
    // so D-1.2 starts cold (the author overwrites the canonical core on promotion).
    delete args.state.proposed_from;
    args.state.pre_d0_intent.scout_refresh = false;
  }

  return persistScoutDecision({
    state: args.state,
    gapsPath,
    decision: { kind: parsed.json.status, nOpen: parsed.json.n_open_problems },
    recovered: false,
  });
}

/**
 * Build the GAPS CONTEXT block injected into the Stage -1.2 producer prompt.
 * Reads the gaps.json artifact produced by Stage -1.1 and renders it as a
 * load-bearing block: the proposer's seeds must anchor (F1) to either a paper
 * bibkey or a prior-proposal ref drawn from `open_problems[].source_refs`.
 *
 * If gaps.json is missing or unparseable, we fall back to the literature_map
 * cached on `state.proposed_from` (populated on the prior cold-start) so the
 * proposer still has *some* substrate. Empty string when neither source is
 * available — in that case the proposer prompt's legacy Step 0a kicks in.
 * (This tolerant read is a DESIGNED degradation with a visible fallback chain,
 * not an existsSync-fail-open: the caller renders an explicit fallback block.)
 */
export async function buildGapsContextBlock(args: {
  ctx: PipelineContext;
  state: StateJson;
  gapsPath: string;
}): Promise<string> {
  let raw: string | null = null;
  try {
    raw = await readFile(args.gapsPath, "utf8");
  } catch {
    raw = null;
  }
  if (raw && raw.length > 0) {
    return [
      "=== STAGE -1.1 GAPS CONTEXT (load-bearing for seed anchoring) ===",
      `Path: ${args.gapsPath}`,
      "This is the research-opportunity substrate harvested by Stage -1.1 (literature scout)",
      "from web search + prior causalsmith proposals/reviewers. Every seed in your Step",
      "0b ideation MUST anchor (F1) to either a paper bibkey from a `source_refs` entry",
      "with kind=paper, OR a prior-proposal ref from a `source_refs` entry with",
      "kind=prior_proposal. Rank opportunities by evidence, mathematical depth, novelty,",
      "feasibility, and consumer value — never by source or opportunity kind. The",
      "`literature_map` and `prior_proposal_map`",
      "fields below subsume your legacy Step 0a / Step 1a outputs — do NOT re-do them.",
      "",
      "Each opportunity also carries an `exemplars` block: a `writing_exemplar`",
      "(the paper whose intro + problem-formulation to imitate) and `method_exemplars`",
      "(the closest technique ancestors to adapt). These are NOT pre-digested — pull",
      "the actual paper up at the point of use, the way you keep a reference open on",
      "the desk: look up the method exemplar in Step 1b (while deepening / deriving),",
      "and the writing exemplar in Step 2 (while drafting §4 intro + §6 setup). When",
      "you anchor a seed to an open problem, inherit THAT problem's exemplars; record",
      "the ones you actually used in proposal §5 so Stage 0 inherits them.",
      "",
      "GAPS PAYLOAD (verbatim):",
      raw.trim(),
      "=== END STAGE -1.1 GAPS CONTEXT ===",
    ].join("\n");
  }
  const cachedLitMap = args.state.proposed_from?.literature_map;
  if (typeof cachedLitMap === "string" && cachedLitMap.length > 0) {
    return [
      "=== STAGE -1.1 GAPS CONTEXT (fallback: gaps.json missing, using cached literature_map) ===",
      "The gaps.json artifact could not be loaded. Falling back to the literature_map",
      "cached on state.proposed_from from the prior cold-start. Seeds must still anchor",
      "to a named paper, but the structured open-problem ledger is unavailable.",
      "",
      "CACHED LITERATURE_MAP:",
      cachedLitMap,
      "=== END STAGE -1.1 GAPS CONTEXT ===",
    ].join("\n");
  }
  return "";
}

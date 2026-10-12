// Discovery Stage 1 (F1) — the FORMALIZATION PLANNER.
//
// The D0 typed core (`<qid>_core.json`) is the machine-readable structural source
// of truth (symbols, atomic assumptions, class/construction definitions, statements,
// dep-DAG). F1 does not re-extract structure from the prose .tex: it authors the
// per-node formalization PLAN (`<qid>_<spec>_plan.json`) that maps every core node +
// ambient world to a Lean object, maximizing reuse of Causalean substrate. F2 then
// implements that plan.

import { existsSync } from "node:fs";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { MODEL_PLAN } from "../constants.js";
import type { ReviewResult } from "../judgment.js";
import type { PipelineContext, StageResult, StateJson } from "../types.js";
import {
  artifactPaths,
  baseBrief,
  clusterFromLeanSubdir,
  correctionBlock,
  parseStageOutput,
  recordGateNodes,
  readPrompt,
  readRequired,
  type StageDeps,
} from "../pipeline_support.js";
import { writeLeanLspMcpConfig } from "../workers/claude.js";
import { dispatchClaudeAgent } from "../framework/agent_dispatch.js";
import { buildGraphFromCorePlan } from "../graph/from_core.js";
import { renderBridgeNote } from "../graph/render_note.js";
import { graphPath, loadGraph, saveGraph } from "../graph/store.js";
import { mergeStage1RevisionGraph } from "../graph/revise_merge.js";
import { coreJsonPath } from "../discovery/stages/d0_core.js";
import { type Core } from "../discovery/core/schema.js";
import { parseTypedCore } from "../discovery/core/core_io.js";
import { runPlanGate } from "../formalization/plan/plan_gate.js";
import { PlanSchema, deriveFeasibility, resolveNodeCitation, type Plan } from "../formalization/plan/schema.js";
import { createRetrieval } from "../formalization/reuse_retrieval.js";
import { coreReuseCandidateBlock } from "../formalization/reuse_render.js";
import { laterStageEverRan } from "../shared/resume_mode.js";
import { parseJsonWithEscapeRepair, parseJsonWithEscapeRepairStatus } from "../shared/codex_json.js";
import { planCorePath } from "../paths.js";
import { appendPipelineLog } from "../log.js";
import { plannerCoreContextValue, restrictCoreContextValue } from "./core_context.js";
import { whatChangedBlock } from "./core_delta.js";
import { BEYOND_SCOPE_KEY, coreChangeSeeds, namedNodeIds, nodeReferenceIndex, reviseAffectedNodeIds, reviseLookupBlock } from "./revise_scope.js";

/** Copy D0.5's verified cited source-of-record into the F1 plan in place. */
export function copyVerifiedCitedSourcesToPlan(
  planObj: unknown,
  core: Core,
  opts: { trustedPlan?: unknown } = {},
): number {
  if (!planObj || typeof planObj !== "object") return 0;
  const pj = planObj as {
    nodes?: Record<string, { source?: unknown }>;
    citations?: Array<Record<string, unknown> & { id?: string; bibkey?: string; cite?: string; node?: string; used_by?: string[] }>;
  };
  const trusted = opts.trustedPlan && typeof opts.trustedPlan === "object"
    ? opts.trustedPlan as { nodes?: Record<string, { source?: unknown }> }
    : undefined;
  if (trusted && pj.citations) {
    const ids = new Set<string>();
    for (const citation of pj.citations) {
      if (!citation.id) continue;
      if (ids.has(citation.id)) throw new Error(`F2 plan contains duplicate citation id '${citation.id}'`);
      ids.add(citation.id);
    }
  }
  const sourceId = (source: unknown): string | undefined =>
    typeof source === "string" ? source
      : source && typeof source === "object" && "citation" in source && typeof source.citation === "string"
        ? source.citation
        : source && typeof source === "object" && "cite" in source && typeof source.cite === "string"
          ? source.cite
          : undefined;
  let copied = 0;
  type Work = {
    id: string;
    bibkey: string;
    authors?: string;
    year?: number;
    title?: string;
    arxiv?: string;
    doi?: string;
    url?: string;
  };
  const seen = new Map<string, { citation: Record<string, unknown>; work: Work }>();
  const mergeWork = (prior: Work, next: Work): Work => {
    for (const key of ["bibkey", "authors", "year", "title", "arxiv", "doi", "url"] as const) {
      const a = prior[key];
      const b = next[key];
      if (a !== undefined && b !== undefined && a !== b) {
        throw new Error(`F1 citation ${prior.id} has conflicting work metadata for '${key}'`);
      }
    }
    return { ...prior, ...Object.fromEntries(Object.entries(next).filter(([, value]) => value !== undefined)) } as Work;
  };
  for (const s of core.statements.filter((x) => x.status === "cited")) {
    if (!s.source) continue;
    const node = pj.nodes?.[s.id];
    if (!node) continue;
    const citeId = trusted ? sourceId(trusted.nodes?.[s.id]?.source) : sourceId(node.source);
    const keyed = pj.citations?.filter((c) => c.bibkey === s.source?.cite || c.cite === s.source?.cite) ?? [];
    let candidates = trusted
      ? pj.citations?.filter((c) => c.id === citeId) ?? []
      : keyed.length > 0 ? keyed : pj.citations?.filter((c) => c.id === citeId) ?? [];
    if (trusted && citeId && candidates.length === 0 && pj.citations) {
      const restored = { id: citeId };
      pj.citations.push(restored);
      candidates = [restored];
    }
    const owned = candidates.filter((c) => c.node === s.id || c.used_by?.includes(s.id));
    const matched = owned.length === 1 ? owned : candidates.filter((c) => c.id === citeId);
    const selected = matched.length === 1 ? matched : candidates.length === 1 ? candidates : [];
    const citation = selected.length === 1 ? selected[0] : undefined;
    if (!citation?.id) { delete node.source; continue; }
    const verbatim = s.source.verbatim_statement ?? s.proof_tex?.trim() ?? undefined;
    const bib = core.bibliography?.find((b) => b.key === s.source?.cite);
    const commaQuoted = bib?.citation?.match(/^(.+?) \((\d{4})(?:;[^)]*)?\),\s*(``.+?''.*)$/s);
    const citationText = bib?.citation?.match(/^(.+?) \((\d{4})(?:;[^)]*)?\)\.\s*(.+)$/s)
      ?? commaQuoted
      ?? bib?.citation?.match(/^(.+?)\. (\d{4})\.\s*(.+)$/s);
    // The bibliography entry is the work's record: a recognized format replaces the
    // planner's authors/title/year; any other text leaves the planner's values in place.
    const titleText = citationText?.[3]?.trim();
    const quotedTitle = titleText?.match(/^``(.+?)(?:,)?''(?:[.,]\s*|\s|$)/s)?.[1];
    const parsedTitle = (quotedTitle ?? titleText?.split(/\.\s/)[0].replace(/\.$/, ""))?.trim();
    const parsedAuthors = citationText?.[1]?.trim();
    const parsed = !!parsedAuthors && !!parsedTitle && !(commaQuoted && !quotedTitle);
    const work: Work = {
      id: citation.id,
      bibkey: s.source.cite,
      ...(parsed
        ? { authors: parsedAuthors, title: parsedTitle, year: Number(citationText![2]) }
        : {
            ...(typeof citation.authors === "string" ? { authors: citation.authors } : {}),
            ...(typeof citation.title === "string" ? { title: citation.title } : {}),
            ...(typeof citation.year === "number" ? { year: citation.year } : {}),
          }),
    };
    const arxiv = bib?.citation?.match(/arXiv:(\d{4}\.\d+(?:v\d+)?)/)?.[1];
    if (arxiv) work.arxiv = arxiv;
    if (s.source.arxiv) work.arxiv = s.source.arxiv;
    if (s.source.doi) work.doi = s.source.doi;
    if (s.source.url) work.url = s.source.url;
    const prior = seen.get(citation.id);
    const canonical = prior ? mergeWork(prior.work, work) : work;
    seen.set(citation.id, { citation: prior?.citation ?? citation, work: canonical });
    node.source = {
      citation: citation.id,
      locator: s.source.locator,
      ...(verbatim ? { verbatim_statement: verbatim } : {}),
      ...(s.source.attestation ? { attestation: s.source.attestation } : {}),
    };
    copied++;
  }
  if (pj.citations) {
    const retained = new Set<string>();
    pj.citations = pj.citations.filter((citation) => {
      if (!citation.id) return true;
      const canonical = seen.get(citation.id);
      if (canonical && canonical.citation !== citation) return false;
      if (retained.has(citation.id)) return false;
      retained.add(citation.id);
      if (canonical) {
        for (const key of Object.keys(citation)) delete citation[key];
        Object.assign(citation, canonical.work);
      } else {
        for (const key of ["locator", "verbatim_statement", "attestation", "node", "used_by", "cite"]) delete citation[key];
      }
      return true;
    });
  }
  return copied;
}

/** `text` without its indentation; unchanged when it is not plain JSON. */
function compactJson(text: string): string {
  try {
    return JSON.stringify(JSON.parse(text));
  } catch {
    return text;
  }
}

/** The planner's view of the core the plan on disk was written from, or null when none was
 *  recorded (a plan older than the record) or it is unreadable. */
async function readPlanCore(p: string): Promise<Record<string, unknown> | null> {
  if (!existsSync(p)) return null;
  try {
    const v = JSON.parse(await readFile(p, "utf8")) as Record<string, unknown>;
    return v && typeof v === "object" && Array.isArray(v.statements) ? v : null;
  } catch {
    return null;
  }
}

/** The plan on disk as a revise reads it: what the schema parses, or null (absent, unparseable). */
async function readPlanOnDisk(p: string): Promise<Plan | null> {
  if (!existsSync(p)) return null;
  try {
    const parsed = PlanSchema.safeParse(parseJsonWithEscapeRepair(await readFile(p, "utf8")));
    return parsed.success ? parsed.data : null;
  } catch {
    return null;
  }
}

/**
 * The seeds of an F1 revise (`reviseAffectedNodeIds` closes them): the nodes the correction or
 * the directive names, and the nodes that moved since the plan was written. Pure; exported
 * for tests.
 */
export function stage1ReviseSeeds(
  core: Core,
  args: {
    planCore: unknown | null;
    coreView: unknown;
    prior: ReviewResult | null;
    directive: string | null;
  },
): string[] {
  const texts: Array<string | undefined> = [args.directive ?? undefined];
  if (args.prior && args.prior.status !== "pass" && args.prior.status !== "accept") {
    for (const f of args.prior.perItemFindings) texts.push(f.label, f.one_line);
    texts.push(args.prior.verbatim_critique);
  }
  return [...new Set([...namedNodeIds(core, texts), ...(args.planCore ? coreChangeSeeds(args.planCore, args.coreView).nodes : [])])];
}

/** Locate the first bracket mismatch in a JSON text, ignoring brackets inside strings:
 * "opened `{` at line 128, closed by `]` at line 327". Null when the brackets balance (the
 * error is elsewhere — a bad escape, a stray comma). Exported for tests. */
export function describeJsonSyntaxError(text: string): string | null {
  const stack: Array<{ ch: string; line: number }> = [];
  let inString = false;
  let escaped = false;
  let line = 1;
  for (const ch of text) {
    if (ch === "\n") line += 1;
    if (inString) {
      if (escaped) escaped = false;
      else if (ch === "\\") escaped = true;
      else if (ch === '"') inString = false;
      continue;
    }
    if (ch === '"') inString = true;
    else if (ch === "{" || ch === "[") stack.push({ ch, line });
    else if (ch === "}" || ch === "]") {
      const open = stack.pop();
      if (!open) return `stray \`${ch}\` at line ${line}`;
      if ((open.ch === "{") !== (ch === "}")) {
        return `opened \`${open.ch}\` at line ${open.line}, closed by \`${ch}\` at line ${line}`;
      }
    }
  }
  if (stack.length > 0) return `unclosed \`${stack[stack.length - 1]!.ch}\` opened at line ${stack[stack.length - 1]!.line}`;
  return null;
}

export async function runStage1(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  priorReview?: ReviewResult | null;
  attempt?: number;
  /** Set on the ONE bounded re-dispatch after the planner wrote a plan.json that is not
   *  valid JSON: the parser's message plus a bracket diagnosis, for an in-place fix. */
  planSyntaxError?: string;
}): Promise<StageResult> {
  const paths = artifactPaths(args.ctx, args.state);
  const corePath = coreJsonPath(args.ctx);
  // The typed core is the structural input and is REQUIRED: D0 always emits it, so
  // absence is a fault (a plan authored from prose alone silently loses the
  // structural ground truth — the existsSync?degrade class from the D-stage hardening).
  const coreText = await readRequired(corePath, "F1 planning");
  let core: Core;
  try {
    core = parseTypedCore(coreText, `F1 planning: core.json at ${corePath}`);
  } catch (err) {
    throw new Error(
      `F1 planning: core.json at ${corePath} failed to parse/validate: ${err instanceof Error ? err.message : String(err)} (legacy pre-typed-core run? re-run discovery (D0) to regenerate core.json)`,
    );
  }

  // REVISE MODE (token-saver, drift-guard). F1 re-runs on two paths: the F1.5
  // boundary loop (carries `priorReview`) and an orchestrator re-entry with a
  // directive parked on `flags.f1_revise_directive` (`bin/f1_directive.ts`). In either
  // case the prior plan is on disk and only the flagged nodes need to change — point
  // the worker at it and Edit in place.
  const f1Directive = args.state.flags.f1_revise_directive ?? null;
  const hasLaterStageHistory = await laterStageEverRan(args.ctx, args.state, "1");
  const isRevise =
    args.priorReview?.status === "revise" ||
    !!f1Directive ||
    hasLaterStageHistory;
  const patching = isRevise && existsSync(paths.plan);
  // The core as a re-plan reads it: the slim view (no proof bodies or positioning prose) with the
  // cited bibliography entries. A first plan reads the whole core.
  const coreView = plannerCoreContextValue(core);
  let reviseBlock = "";
  /** The nodes a patch is about (`reviseAffectedNodeIds`), shown in full. */
  let affected = new Set<string>();
  let planOnDisk: Plan | null = null;
  if (patching) {
    // What moved since the plan was written. A plan with no record of its core, and a change
    // that names no node, get the whole view (`scoped` below).
    const planCore = await readPlanCore(planCorePath(args.ctx.repoRoot, args.ctx.qid));
    planOnDisk = await readPlanOnDisk(paths.plan);
    if (planCore) {
      affected = reviseAffectedNodeIds(
        core,
        planOnDisk,
        stage1ReviseSeeds(core, {
          planCore,
          coreView,
          prior: args.priorReview ?? null,
          directive: f1Directive,
        }),
      );
    }
    // With no record of the plan's core, the comparison is asked for only when nothing above
    // names the change instead.
    const named = (args.priorReview != null && args.priorReview.status !== "pass" && args.priorReview.status !== "accept")
      || !!f1Directive;
    reviseBlock = [
      planCore || !named ? whatChangedBlock(planCore, coreView) : "",
      await readPrompt(args.ctx, "stage1_head_revise.txt"),
      "",
      f1Directive
        ? `ORCHESTRATOR DIRECTIVE (the defect is in the FORMALIZATION PLAN. Fix the plan as directed):\n${f1Directive}\n`
        : "",
      `Prior plan to patch (Edit in place): ${paths.plan}`,
      "",
    ].filter(Boolean).join("\n");
  }
  const nodeCount = core.assumptions.length + core.definitions.length + core.statements.length;
  // A plan the schema does not parse gives no reference lines, and a change that reaches every
  // node is no scope: both read the whole view.
  const scoped = patching && planOnDisk != null && affected.size > 0 && affected.size < nodeCount;
  const coreBlock = !patching
    ? `Typed core JSON (the structural source of truth — map EVERY node; do NOT re-derive structure from prose):\n${compactJson(coreText)}`
    : !scoped
      ? `Typed core JSON (the structural source of truth; proof bodies and positioning prose omitted, the full file is at ${corePath}):\n${JSON.stringify(coreView)}`
      : [
          `Typed core — the ${affected.size} of ${nodeCount} nodes this revise affects, in full, with the symbols they use (settings, the bibliography, proof bodies and the remaining symbols are in the core file):\n${JSON.stringify(restrictCoreContextValue(coreView, affected))}`,
          "",
          reviseLookupBlock({
            index: nodeReferenceIndex(core, planOnDisk, affected),
            shown: affected.size,
            total: nodeCount,
            corePath,
            planPath: paths.plan,
            replyField: `\`${BEYOND_SCOPE_KEY}\``,
          }),
        ].join("\n");
  if (patching) {
    const scopeLine = scoped
      ? `F1 revise carries ${affected.size} of ${nodeCount} core nodes in full`
      : "F1 revise carries the whole core view (no record of the plan's core, an unreadable plan, or a change that names no node or reaches all)";
    console.warn(`[causalsmith] ${scopeLine}`);
    await appendPipelineLog(args.ctx, { stage: "1", status: "revise-scope", duration_ms: 0, message: scopeLine });
  }

  const cluster = clusterFromLeanSubdir(args.state.lean_subdir) ?? core.cluster ?? null;
  const reuseBlock = patching
    ? ""
    : coreReuseCandidateBlock(args.ctx.repoRoot, core, cluster, {
        // Semantic blend ON by default: pure-lexical ranking surfaced surface-token matches
        // over concept-correct declarations. Degrades to lexical-only if embeddings are stale.
        semantic: process.env.RETRIEVAL_SEMANTIC_PUSH !== "off",
      });

  const syntaxFixBlock = args.planSyntaxError
    ? [
        "=== PLAN FILE IS NOT VALID JSON — FIX IT IN PLACE ===",
        `Your previous plan at ${paths.plan} does not parse: ${args.planSyntaxError}`,
        "Repair the file with a minimal Edit (do not regenerate it), then validate before returning:",
        "  node -e 'JSON.parse(require(\"fs\").readFileSync(process.argv[1],\"utf8\"))' <plan path>",
        "",
      ].join("\n")
    : "";

  const prompt = [
    syntaxFixBlock,
    correctionBlock(args.priorReview ?? null, args.attempt ?? 1),
    "",
    reviseBlock,
    (await readPrompt(args.ctx, "stage1_template.txt")).replaceAll(
      "{{HEADER_CONTRACT}}",
      [
        "HEADER CONTRACT — Every generated Lean file begins, in order, with the optional copyright block, then `module`, contiguous imports written as `public import` (only a rare deliberate exception marked by a `-- private import` comment may use a private import), the `/-! ... -/` module docstring, and exactly one blanket section: `@[expose] public section` when the file defines a `def`, `abbrev`, `instance`, `structure`, `class`, or `inductive`, otherwise `public section`. Keep declarations bare: no per-declaration `public`, `private`, or `@[expose]`; helpers stay bare, and nothing is private unless it is truly file-local and never needed by a proof downstream. Run barrels and `Helpers.lean` are imports-only and use `public import` on every line.",
        "MODULE-SYSTEM CONSEQUENCES — A `module` file cannot import a legacy non-`module` file: every imported file must itself be a module file, and the scaffold must never add `import all`. A `def` whose body a downstream `rfl`, `decide`, or `unfold` needs must live in a file with `@[expose] public section`. A certificate evaluated by the kernel (`decide +kernel`) must not pass through well-founded recursion such as `Array.ofFn` or `termination_by`, because importers cannot see termination proofs; use a structural construction.",
      ].join("\n"),
    ),
    "",
    baseBrief(args.ctx, args.state),
    "",
    coreBlock,
    "",
    reuseBlock,
    "",
    patching
      ? `Patch the existing plan at ${paths.plan} per REVISE MODE above.`
      : `Write the formalization plan JSON to ${paths.plan}.`,
    "Return only the JSON object specified in the prompt's `=== OUTPUT JSON ===` block.",
  ].join("\n");

  const out = await dispatchClaudeAgent({
    ctx: args.ctx,
    deps: args.deps,
    stage: "1",
    label: "F1 plan author",
    promptSources: ["stage1_template.txt", ...(isRevise ? ["stage1_head_revise.txt"] : []), corePath],
    input: {
      prompt,
      model: MODEL_PLAN.stage1.model,
      cwd: args.ctx.repoRoot,
      mcpConfigPath: writeLeanLspMcpConfig(args.ctx.repoRoot),
      allowedTools: [
        "Read", "Write", "Edit", "Grep", "Glob",
        // Substrate survey for the per-node reuse decisions. The ranked library
        // search is the one shell command granted (cwd is the CausalSmith
        // package root); it replaces reading `doc/API.md` section by section.
        // A single command, no `&&`: permission rules match each `&&` segment.
        "Bash(npm --prefix tools run search:*)",
        "mcp__lean-lsp__lean_leansearch",
        "mcp__lean-lsp__lean_loogle",
        "mcp__lean-lsp__lean_local_search",
        "mcp__lean-lsp__lean_hover_info",
        "mcp__lean-lsp__lean_file_outline",
      ],
    },
  });
  const parsed = parseStageOutput(out);
  if (parsed.status === "parse_failed") {
    // AUDIT-A: fail closed on unparseable stage output; why: F1 must not advance on garbage.
    throw new Error("Stage 1: F1 worker output did not parse (parse_failed) - refusing to advance on unparseable output");
  }
  const p = parsed as Record<string, unknown>;
  // The mechanical affected set under-reached: say where, so the rule can be widened.
  const beyond = scoped && Array.isArray(p[BEYOND_SCOPE_KEY]) ? (p[BEYOND_SCOPE_KEY] as unknown[]).map(String) : [];
  if (beyond.length > 0) {
    const message = `F1 revise looked up ${beyond.length} node(s) beyond the affected set (${affected.size}): ${beyond.join(", ")}`;
    await appendPipelineLog(args.ctx, { stage: "1", status: "revise-scope", duration_ms: 0, message });
    console.warn(`[causalsmith] ${message}`);
  }

  // Read the just-written plan (if any) and run the deterministic gate as a
  // best-effort self-check — log violations. The F1.5 boundary enforces them as a
  // pre-review lint with producer retry (Phase 3); F1 never blocks on the gate.
  let planObj: unknown = null;
  if (existsSync(paths.plan)) {
    try {
      const parsedPlanText = parseJsonWithEscapeRepairStatus(await readFile(paths.plan, "utf8"));
      planObj = parsedPlanText.value;
      // PERSIST the repair. Repairing only in memory leaves an unparseable durable store
      // behind a gate that now passes, so every later reader must repeat the repair —
      // and F2's plan-derived directive builders do a bare `JSON.parse` and fail OPEN,
      // silently dropping the UNDELIVERED and gated-hyps blocks from the producer prompt.
      // Canonicalizing here keeps `plan.json` parseable for readers that do not repair.
      if (parsedPlanText.repaired) {
        await writeFile(paths.plan, JSON.stringify(planObj, null, 2), "utf8");
        console.warn(`[causalsmith] F1 repaired invalid string escapes in ${paths.plan} and rewrote it canonically.`);
      }
    } catch (err) {
      const reason = err instanceof Error ? err.message : String(err);
      console.warn(`[causalsmith] F1 wrote an unparseable plan at ${paths.plan}: ${reason}`);
      // A syntax slip is something the planner can fix in seconds; halting the run for it
      // is not. ONE bounded re-dispatch with the parser's message and a bracket diagnosis.
      if (!args.planSyntaxError) {
        const diagnosis = describeJsonSyntaxError(await readFile(paths.plan, "utf8"));
        console.warn(`[causalsmith] F1: re-dispatching once to repair the plan file (${diagnosis ?? "no bracket diagnosis"})`);
        return runStage1({
          ...args,
          attempt: (args.attempt ?? 1) + 1,
          planSyntaxError: `${reason}${diagnosis ? `; ${diagnosis}` : ""}`,
        });
      }
    }
  }
  // D0.5 has already source-matched every status:"cited" node. F1 must COPY
  // that verified source of record, not ask the planner to reconstruct theorem
  // text from prose. Apply it deterministically through the cited node's cite:
  // alias. Legacy cores may store the attested transcription in proof_tex.
  if (planObj && typeof planObj === "object") {
    const copied = copyVerifiedCitedSourcesToPlan(planObj, core);
    if (copied > 0) {
      await writeFile(paths.plan, JSON.stringify(planObj, null, 2), "utf8");
      console.warn(`[causalsmith] F1 copied ${copied} D0.5-verified cited source-of-record entr${copied === 1 ? "y" : "ies"} into the plan.`);
    }
  }
  if (planObj && typeof planObj === "object") {
    const rawPlan = planObj as Record<string, unknown>;
    const structuralPlan = PlanSchema.safeParse({ ...rawPlan, feasibility: undefined });
    if (structuralPlan.success) {
      const feasibility = deriveFeasibility(structuralPlan.data);
      if (rawPlan.feasibility !== feasibility) {
        rawPlan.feasibility = feasibility;
        await writeFile(paths.plan, JSON.stringify(planObj, null, 2), "utf8");
      }
    }
  }
  let derivedFeasibility: "formalizable-now" | "needs-new-infrastructure" | null = null;
  let planGateOk = true;
  const parsedPlan = planObj ? PlanSchema.safeParse(planObj) : null;
  if (planObj) {
    let knownDecls: Set<string> | undefined;
    try {
      const lib = createRetrieval(args.ctx.repoRoot).library;
      if (lib) knownDecls = new Set(lib.entries.map((e) => e.name));
    } catch {
      knownDecls = undefined;
    }
    if (!knownDecls) {
      console.warn(
        "[causalsmith] library index unavailable (doc/library_index.json missing/unreadable) — the P5 reuse-existence check is SKIPPED this pass; hallucinated reuse decls will surface only at compile. Run `lake build && lake exe library_index`.",
      );
    }
    const gate = runPlanGate(planObj, core, { knownDecls });
    planGateOk = gate.ok;
    if (!gate.ok) {
      console.warn(
        `[causalsmith] F1 plan_gate: ${gate.violations.length} violation(s)\n  ` +
          gate.violations.slice(0, 12).map((v) => `${v.code} @ ${v.where}: ${v.message}`).join("\n  "),
      );
    }
    if (parsedPlan?.success) derivedFeasibility = deriveFeasibility(parsedPlan.data);
  }
  // Judge cleanliness by the SAME gate run F1.5's prelint will apply (with knownDecls) — a
  // second knownDecls-less run here would clear the retry directives on a plan the boundary
  // is about to bounce for reuse-existence violations.
  const planGateClean =
    parsed.status === "completed" &&
    !!parsedPlan?.success &&
    planGateOk;
  // The core view this plan was written from: the next re-plan's WHAT CHANGED block diffs against
  // it. Only a completed pass records it — a blocked one left the plan on disk for the older core.
  if (parsed.status === "completed" && parsedPlan?.success) {
    const record = planCorePath(args.ctx.repoRoot, args.ctx.qid);
    await mkdir(path.dirname(record), { recursive: true });
    await writeFile(record, JSON.stringify(coreView), "utf8");
  }
  if (planGateClean) {
    // why: keep retry directives until F1 completed with a parsed, gate-clean plan.
    if (f1Directive) args.state.flags.f1_revise_directive = null;
  }

  // Emit the formalization graph from core + plan (the graph is the interchange the
  // F3/F4 proof loop refreshes off — without it the loop has no graph to refresh).
  // On revise, merge the structural delta into the existing graph. Later F stages
  // own its Lean links, proof state, review receipts, extracted edges, and auxiliary
  // nodes; rebuilding from an empty graph here would silently destroy all of them.
  // Best-effort: never blocks the stage. A failed revise merge leaves the existing
  // artifacts untouched rather than falling back to a destructive fresh write.
  try {
    // A malformed/partial revise must not replace valid downstream artifacts
    // with the builder's plan=null fallback.
    if (!parsedPlan?.success) throw new Error("plan is not schema-valid; preserving existing graph/note");
    const gp = graphPath(paths.formalizationDir, args.ctx.qid, args.ctx.specialization);
    const rebuilt = buildGraphFromCorePlan(core, args.ctx.specialization, parsedPlan.data);
    const g = isRevise && existsSync(gp)
      ? mergeStage1RevisionGraph(await loadGraph(gp), rebuilt)
      : rebuilt;
    await saveGraph(gp, g);
    // Bridge .md: the banked human record + causalsmith input + F5 premise-check
    // source, rendered deterministically from the graph (parseNoteBlocks-compatible).
    // The bridge is a canonical core+plan projection. Auxiliary proof-engineering
    // nodes belong in graph.json but must not leak into the paper-facing note.
    await mkdir(path.dirname(paths.md), { recursive: true });
    await writeFile(paths.md, renderBridgeNote(rebuilt), "utf8");
  } catch (err) {
    console.warn(`[graph] F1 core+plan emission skipped: ${err instanceof Error ? err.message : String(err)}`);
  }

  // Feasibility is DERIVED from the plan (Defer-tier nodes ⇒ needs-new-infrastructure);
  // fall back to a worker-reported verdict only when no plan was parsed (legacy path).
  const infra = p.infrastructure_needed;
  const feasibility =
    derivedFeasibility ?? (typeof p.feasibility_verdict === "string" ? p.feasibility_verdict : null);
  let infraItems: Array<Record<string, unknown>> = Array.isArray(infra) ? (infra as Array<Record<string, unknown>>) : [];
  // If the plan derives needs-new-infrastructure but the worker JSON listed no
  // items, synthesize the ledger items from the Defer-tier plan nodes.
  if (feasibility === "needs-new-infrastructure" && infraItems.length === 0 && parsedPlan?.success) {
    infraItems = Object.entries(parsedPlan.data.nodes)
      .filter(([, n]) => n.defer_tier)
      .map(([id, n]) => ({ id, kind: n.lean_kind, description: n.notes ?? "", effort: "medium" }));
  }
  const gateIds = new Set(
    parsedPlan?.success
      ? Object.entries(parsedPlan.data.nodes).filter(([, n]) => n.gate).map(([id]) => id)
      : [],
  );
  if (parsedPlan?.success && gateIds.size > 0) {
    try {
      const coreNl = new Map<string, string>();
      if (core) {
        for (const a of core.assumptions) coreNl.set(a.id, a.condition);
        for (const d of core.definitions) coreNl.set(d.id, d.construction);
        for (const s of core.statements) coreNl.set(s.id, s.statement);
      }
      const gateRows = Object.entries(parsedPlan.data.nodes)
        .filter(([, n]) => n.gate)
        .map(([id, n]) => {
          const matchingInfra = infraItems.find((it) =>
            String(it.id ?? "") === id ||
            String(it.id ?? "") === n.lean_name ||
            String(it.description ?? "").includes(id) ||
            String(it.description ?? "").includes(n.lean_name)
          );
          const cls = n.gate_class === "cited" ? ("cited" as const) : undefined;
          const cit = resolveNodeCitation(parsedPlan.data, n);
          const handle = cit?.arxiv ? `arXiv:${cit.arxiv}` : (cit?.doi ?? cit?.url);
          return {
            name: n.lean_name,
            statement: coreNl.get(id) ?? n.notes ?? id,
            classical_fact: cit
              ? `${cit.authors}${cit.year === undefined ? "" : ` (${cit.year})`} — ${cit.title}`
              : String(matchingInfra?.kind ?? "substrate-gate"),
            missing_infra: String(matchingInfra?.description ?? n.notes ?? "F1 substrate-gate plan node"),
            gate_class: cls,
            source: cls === "cited" && cit
              ? { cite_id: cit.id, locator: cit.locator, url: handle }
              : undefined,
          };
        });
      await recordGateNodes(args.ctx, gateRows);
    } catch (err) {
      console.warn(`[causalsmith] substrate-debt gate ledger write failed: ${err instanceof Error ? err.message : String(err)}`);
    }
  }
  // F1 does not halt for substrate: it has no frozen provenance for an uncited
  // external theorem, so build/citation classification belongs to F1.5.
  //
  // The plan audit (CKPT 1) is at F1.5: when F1 produced a usable plan it advances
  // straight into the F1.5 reuse-soundness review, so F1 + F1.5 halt together at ONE
  // consolidated CKPT 1. F1 halts on its own only when no usable plan was parsed
  // (blocked-infeasible / parse failure) — there is nothing for F1.5 to review.
  if (!parsedPlan?.success) {
    return {
      stage: "1",
      status: "checkpoint",
      message: parsed.message ?? "F1 produced no usable plan; inspect the artifact before resume.",
    };
  }
  return {
    stage: "1",
    status: "completed",
    message: parsed.message ?? "F1 plan authored; advancing to F1.5 reuse-soundness review (consolidated CKPT 1).",
  };
}

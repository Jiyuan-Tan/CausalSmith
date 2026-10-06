// Pure, testable core of the P1 executor→reviewer→router loop (the codex
// calls live in stages/p1_plan.ts; this module holds the logic they orchestrate).
// See doc/presentation/2026-06-17-causalsmith-graph-simplification-design.md §4.6.
import type { GraphNode } from "../graph/types.js";
import { envForNode, type EnvName } from "./graph_view.js";

/**
 * The deterministic mechanical frozen layer, rendered from already-topo-ordered
 * paper nodes (caller applies `topoOrder(renderedNodes(graph))`). Each env body is
 * the graph's `nl.statement`; the executor's touch-up replaces the WORDING in
 * place afterward (same obj_id). Titleless — the graph carries no title and the
 * env macro's `[title]` is optional; a title can be added by the render later.
 * Non-env kinds and all gates are skipped. A cited gate remains dependency metadata and is
 * disclosed by a generated footnote on each formally conditional consumer.
 */
export function renderMechanicalLayer(nodes: GraphNode[]): string {
  const out: string[] = [
    "% AUTO-GENERATED mechanical frozen layer — causalsmith P1 (graph render). Wording is touched up in place.",
  ];
  for (const n of nodes) {
    const env = envForNode(n);
    if (!env) continue;
    out.push(`\\begin{${env}}{${n.id}}`, n.nl.statement.trim(), `\\end{${env}}`, "");
  }
  return out.join("\n");
}

export type FixLocus = "wording-revise" | "synthesize-def" | "halt";

/** Findings the (codex) reviser can repair by re-rendering an env's wording.
 *  Gate names must match what the lints actually emit (`tex_anchors.ts`/`gates.ts`).
 *  `xref-missing` is advisory at the stage (it can over-fire on natural prose that
 *  names a dep instead of `\ref`-ing it); `xref-dangling` is enforced, and
 *  `xref-missing-assumption` (a statement-uses dep on an ASSUMPTION that the body never `\ref`s) is
 *  enforced too — an unreferenced hypothesis must be surfaced before the body freezes. */
const WORDING_GATES = new Set([
  "lean-identifier",
  "formalization-leak",
  "assumption-numbering",
  "xref-dangling",
  "xref-missing",
  "xref-missing-assumption",
  "faithfulness",
  // A bare "A1" in prose with no matching env is a render artifact: the reviser
  // should \ref the real assumption env, not invent a new one (all from-note
  // assumptions are already rendered as envs).
  "undefined-assumption",
  // Statement-presentation floor (`lintHypothesisPresentation`): a hypothesis-heavy theorem whose
  // conditions run together inline, or a `\ref`'d assumption restated inline. Both are repaired by
  // RE-RENDERING the env (itemize the hypotheses / drop the duplicated content) before the freeze —
  // exactly what that lint's docstring promises. Without these the router defaulted them to `halt`,
  // so P1 bailed on the first such finding instead of letting the reviser reformat.
  "hypothesis-not-itemized",
  "hypothesis-restated",
  // The Lean-fidelity judge's verdict: repair the body using the reported drift.
  "lean-drift",
]);
/**
 * Route a finding to its handler by gate name (the deterministic part of the
 * router — §4.6.0). The codex reviewer may also emit an explicit `fix_locus` on a
 * semantic finding; the caller prefers that when present and falls back here
 * (synthesis is requested only via an explicit `fix_locus`). Anything
 * unrecognized → `halt` (fail loud: unknown-objid, env-set-changed, bare-env,
 * not-frozen, …) rather than silently revising.
 */
export function routeFinding(gate: string): FixLocus {
  if (WORDING_GATES.has(gate)) return "wording-revise";
  return "halt";
}

// ---------------------------------------------------------------------------
// The executor → reviewer → router loop (control flow; model calls are injected
// as hooks so this is unit-testable with mocks). §4.6.1.
// ---------------------------------------------------------------------------

/** One paper env in flight. `statement` is the immutable graph nl.statement (the
 *  faithfulness anchor); `body` is its current rendered prose; `refSet` is the
 *  allowed `\ref` target ids (paper-env edge targets, from `refTargets`). */
export interface P1Env {
  id: string;
  env: EnvName;
  statement: string;
  body: string;
  refSet: string[];
  delivery?: { status: "undelivered"; role?: string; reason: string };
}

/** Ordering preferences and missing optional cross-references are advisory.
 *  Semantic `notation-reviewer` findings are deliberately NOT advisory: the presentation
 *  contract requires every named object to resolve before the P1 checkpoint can pass. */
const ADVISORY_GATES = new Set(["xref-missing", "notation-mutual-definition", "notation-home-is-result"]);

/** A reviewer/lint finding. `fixLocus` is the codex reviewer's explicit route when
 *  present; otherwise the router falls back to `routeFinding(gate)`. `symbol` names
 *  the orphan class/assumption for a `synthesize-def`. */
export interface P1Finding {
  gate: string;
  objId?: string;
  detail: string;
  fixLocus?: FixLocus;
  symbol?: string;
  usedIn?: string[];
}

/** Injected model/IO operations the loop orchestrates. */
export interface P1LoopHooks {
  /** (Re-)render envs to paper prose (codex). Round 0 passes the envs that need a body;
   *  later rounds pass only flagged envs with their prior body + defects. Returns id → new body. */
  render(
    reqs: { id: string; statement: string; refSet: string[]; priorBody?: string; defects?: string[]; delivery?: P1Env["delivery"] }[],
  ): Promise<Map<string, string>>;
  /** Review the assembled layer (codex notation + faithfulness) + deterministic floor lints. */
  review(layer: string, envs: P1Env[]): Promise<P1Finding[]>;
  /** Synthesize new definition envs for orphan symbols (codex+lean-lsp). `unresolved` lists the
   *  requested symbols the writer could not define faithfully: a later `synthesize-def` finding
   *  for such a symbol remains blocking instead of repeating the same request. */
  synthesize(symbols: string[], findings: P1Finding[]): Promise<{ envs: P1Env[]; unresolved: string[] }>;
  /** Assemble the layer tex from envs in PAPER order (the stage owns ordering; the loop's env
   *  list order carries no meaning). */
  assemble(envs: P1Env[]): string;
  /** Progress/persistence hook (optional): called after the round-0 render and
   *  after each review, so the stage can log and write the current layer to disk
   *  (observability — a slow/timed-out run still leaves the rendered output). */
  onRound?(info: { phase: "render0" | "review"; iter: number; envs: P1Env[]; findings?: P1Finding[] }): Promise<void> | void;
  maxIterations: number;
}

export interface P1LoopResult {
  envs: P1Env[];
  ok: boolean;
  /** On `ok:false`, the blocking findings (a halt, or unresolved after the cap). */
  unresolved: P1Finding[];
  /** Advisory findings (xref-missing) surfaced for the checkpoint, never blocking. */
  advisories: P1Finding[];
  iterations: number;
}

const locusOf = (f: P1Finding): FixLocus => f.fixLocus ?? routeFinding(f.gate);
export const isAdvisoryFinding = (f: P1Finding): boolean =>
  ADVISORY_GATES.has(f.gate) && f.fixLocus == null; // why: deterministic orphan notation opts into synthesis explicitly.

/** Reviewer findings occasionally name several missing symbols in one field.
 * Split only at visible math-fragment boundaries or top-level commas: commas
 * inside function arguments/subscripts remain part of one notation atom. */
export function atomicRequestedNotationSymbols(symbol: string): string[] {
  // Preserve the gaps between math fragments too: reviewers sometimes emit a
  // mixed form such as `m_1(h), \(m_2(h)\)`.  Selecting only the delimited
  // fragments silently dropped the bare atom.
  const raw = symbol.replace(/\$([^$]+)\$|\\\((.*?)\\\)|\\\[([\s\S]*?)\\\]/g,
    (_whole, dollar: string | undefined, inline: string | undefined, display: string | undefined) =>
      dollar ?? inline ?? display ?? "");
  const split = (raw: string): string[] => {
    const parts: string[] = [];
    let round = 0, square = 0, curly = 0, start = 0;
    const push = (end: number) => {
      const part = raw.slice(start, end).trim()
        .replace(/^(?:\\(?:[,;:!]|quad|qquad)\s*)+|(?:\s*\\(?:[,;:!]|quad|qquad))+$/g, "")
        .replace(/^[,;:]+|[,;:]+$/g, "").trim();
      if (part) parts.push(part);
    };
    for (let i = 0; i < raw.length; i++) {
      const c = raw[i];
      if (c === "(") round++; else if (c === ")") round--;
      else if (c === "[") square++; else if (c === "]") square--;
      else if (c === "{") curly++; else if (c === "}") curly--;
      else if (round === 0 && square === 0 && curly === 0) {
        if ((c === "," || c === ";") && raw[i - 1] !== "\\") {
          push(i); start = i + 1;
        } else {
          const connector = raw.slice(i).match(/^\s+and\s+|^(?:\\(?:[,;:!]|quad|qquad)\s*)+(?:and|\\text\{\s*and\s*\})(?:\s*\\(?:[,;:!]|quad|qquad))+/i)?.[0];
          if (!connector) continue;
          push(i);
          i += connector.length - 1;
          start = i + 1;
        }
      }
    }
    push(raw.length);
    return parts;
  };
  return [...new Set(split(raw.trim()))];
}

/**
 * Run the loop: render (round 0) → {review → route → handle} until the reviewer is clean, a
 * `halt` fires, or the iteration cap is hit. The `synthesize-def` handler adds authored envs;
 * `wording-revise` re-renders flagged envs with their defects; advisory gates are collected,
 * never blocking. Pure control flow — all model calls go through `h`.
 */
export interface P1LoopOptions {
  /** Ids to render in round 0 (default: every env). Envs whose bodies are already authored —
   *  synthesized definitions recovered from the cache — are passed through as they are. */
  renderIds?: string[];
}

export async function runP1Loop(initial: P1Env[], h: P1LoopHooks, opts: P1LoopOptions = {}): Promise<P1LoopResult> {
  let envs = initial.map((e) => ({ ...e }));
  const applyRender = (reqIds: string[], m: Map<string, string>) => {
    const requested = new Set(reqIds);
    const missing = reqIds.filter((id) => !m.has(id) || (m.get(id) ?? "").trim() === "");
    const extra = [...m.keys()].filter((id) => !requested.has(id));
    if (missing.length || extra.length) {
      throw new Error(`P1 render returned invalid id set — missing/empty: [${missing.join(", ")}], extra: [${extra.join(", ")}]`); // why: silently keeping old bodies publishes stale formal prose.
    }
    envs = envs.map((e) => (m.has(e.id) ? { ...e, body: m.get(e.id)! } : e));
  };
  // Round 0: render the envs that need a body.
  const round0 = new Set(opts.renderIds ?? envs.map((e) => e.id));
  const reqs0 = envs.filter((e) => round0.has(e.id)).map((e) => ({ id: e.id, statement: e.statement, refSet: e.refSet, delivery: e.delivery }));
  if (reqs0.length > 0) applyRender(reqs0.map((r) => r.id), await h.render(reqs0));
  await h.onRound?.({ phase: "render0", iter: 0, envs });

  let advisories: P1Finding[] = [];
  const addAdvisories = (fs: P1Finding[]) => {
    const seen = new Set(advisories.map((f) => `${f.gate}|${f.objId ?? ""}|${f.detail}`));
    for (const f of fs) {
      const key = `${f.gate}|${f.objId ?? ""}|${f.detail}`;
      if (!seen.has(key)) {
        advisories.push(f);
        seen.add(key);
      }
    }
  };
  // Symbols the synthesizer declined this run: a repeat request would only re-pay the same
  // refusal, so later findings for them remain blocking without another call.
  const unresolvable = new Set<string>();
  const declined = (f: P1Finding): P1Finding => {
    if (locusOf(f) !== "synthesize-def" || !f.symbol) return f;
    const atoms = atomicRequestedNotationSymbols(f.symbol);
    return atoms.length > 0 && atoms.every((a) => unresolvable.has(a))
      ? { gate: "notation-unresolved", objId: f.objId, symbol: f.symbol, detail: `${f.detail} (the definition writer could not define this symbol faithfully)` }
      : f;
  };
  let prevActionableFp = "";
  for (let iter = 1; iter <= h.maxIterations; iter++) {
    const findings = (await h.review(h.assemble(envs), envs)).map(declined);
    await h.onRound?.({ phase: "review", iter, envs, findings });
    addAdvisories(findings.filter(isAdvisoryFinding));
    const actionable = findings.filter((f) => !isAdvisoryFinding(f));
    if (actionable.length === 0) return { envs, ok: true, unresolved: [], advisories, iterations: iter };

    const halts = actionable.filter((f) => locusOf(f) === "halt");
    if (halts.length > 0) return { envs, ok: false, unresolved: halts, advisories, iterations: iter };

    // Fast-exit: if this round's actionable set is IDENTICAL to the previous round's
    // (same gates/loci/envs/symbols), the previous repair dispatch changed nothing the
    // reviewer cares about — an ordering or structural problem re-rendering cannot fix.
    // Halt loudly with the findings instead of burning the remaining iteration budget
    // re-paying identical render+review rounds (observed: two full 6-iteration burns).
    const actionableFp = actionable
      .map((f) => `${f.gate}|${locusOf(f)}|${f.objId ?? ""}|${f.symbol ?? ""}|${f.detail}`)
      .sort()
      .join(";");
    if (actionableFp === prevActionableFp) {
      return { envs, ok: false, unresolved: actionable, advisories, iterations: iter };
    }
    prevActionableFp = actionableFp;

    // synthesize-def → add the authored definition envs (the stage orders the layer).
    const symbols = [...new Set(actionable
      .filter((f) => locusOf(f) === "synthesize-def")
      .flatMap((f) => f.symbol ? atomicRequestedNotationSymbols(f.symbol) : []))];
    if (symbols.length > 0) {
      const made = await h.synthesize(symbols, actionable.filter((f) => locusOf(f) === "synthesize-def"));
      for (const sym of made.unresolved) unresolvable.add(sym);
      // A definition that already exists comes back re-rendered (it took on more symbols): its
      // body is replaced in place; new definitions are appended once.
      const madeById = new Map(made.envs.map((e) => [e.id, e] as const));
      envs = envs.map((e) => madeById.get(e.id) ?? e);
      const present = new Set(envs.map((e) => e.id));
      envs = [...envs, ...made.envs.filter((e) => !present.has(e.id) && (present.add(e.id), true))];
    }

    // wording-revise → re-render the flagged envs with their accumulated defects.
    const defectsById = new Map<string, string[]>();
    for (const f of actionable) {
      if (locusOf(f) === "wording-revise" && f.objId) {
        (defectsById.get(f.objId) ?? defectsById.set(f.objId, []).get(f.objId)!).push(f.detail);
      }
    }
    if (defectsById.size > 0) {
      const reqs = envs
        .filter((e) => defectsById.has(e.id))
        .map((e) => ({ id: e.id, statement: e.statement, refSet: e.refSet, priorBody: e.body, defects: defectsById.get(e.id)!, delivery: e.delivery }));
      applyRender(reqs.map((r) => r.id), await h.render(reqs));
    }
    // If a round only produced synth (no wording defects), the next iteration
    // re-reviews the enlarged layer — progress is guaranteed by the cap.
  }
  // Cap reached: re-review once to report what still blocks.
  const finalFindings = (await h.review(h.assemble(envs), envs)).map(declined);
  addAdvisories(finalFindings.filter(isAdvisoryFinding));
  const residual = finalFindings.filter((f) => !isAdvisoryFinding(f));
  return { envs, ok: residual.length === 0, unresolved: residual, advisories, iterations: h.maxIterations };
}

import { canonicalizeObjRefs, lintAnchors, lintEnvOrder, parseAnchoredEnvs, repairObjRefs, type LintProblem } from "./tex_anchors.js";
import { citedKeys, type BibEntry } from "./citations.js";
import { maskNonBoundaryPeriods, stripTexComments } from "../shared/tex_text.js";
import {
  normalizeRawModelJson,
  repairLatexStringsDeep,
} from "../discovery/core/latex_serialization.js";

/**
 * P3 gate logic, kept pure (model runners injected) so the revision loop and
 * each gate are unit-testable. Hard gates are pass/fail; the soft rubric only
 * drives bounded revision.
 */

export interface StatementCheck {
  obj_id: string;
  envBody: string;
  leanStatement: string;
  /** file/decl/line pointer so the auditor can read the surrounding Lean context. */
  leanPointer: string;
  /** A main result (theorem/lemma) — audited individually at high effort; definitions/assumptions
   *  are short structural comparisons, batched at medium. Keyed off the env KIND (not the obj_id
   *  prefix, which changed from `T-`/`L-` aliases to node ids like `thm:`/`lem:`). */
  isMainResult: boolean;
  /** Exact source-matched propositions erased from the journal-style hypothesis list. */
  citedDependencies?: string;
}

export interface GateRunners {
  overclaim(
    frontMatter: string,
    frozenEnvsTex: string,
  ): Promise<{ clean: boolean; flags?: { sentence: string; fix?: string }[] }>;
  /** Batched citation-support audit: verdicts keyed by `${key}|${sentence}`. The runner must
   *  attempt every pair (including singletons); a pair missing from the result is treated as
   *  `unverifiable` (advisory) by the caller, never silently supported. */
  citationSupportBatch(
    pairs: { sentence: string; entry: BibEntry }[],
  ): Promise<Map<string, { verdict: "supported" | "unsupported" | "unverifiable"; reason?: string }>>;
}

export interface HardGateInput {
  paperTex: string;
  /** Frozen-layer env ids in P1's settled order (`formal_layer.json` block order). */
  layerOrder: readonly string[];
  knownObjIds: Set<string>;
  frozenBodies: Map<string, string>; // obj_id → canonical frozen body
  frontMatter: string;
  frozenEnvsTex: string;
  bibEntries: BibEntry[];
}

/** Sentences of the paper that carry \cite commands, with their keys.
 * Boundaries are computed on a period-masked copy so `see, e.g. \citet{Foo}` /
 * `cf. \citet{Bar}` are not split right before the citation — that handed the
 * auditor a bare `\citep{…}` fragment with the supported claim cut off. */
export function citingSentences(tex: string): { sentence: string; keys: string[] }[] {
  const stripped = stripTexComments(tex)
    // structural commands glue unrelated text into one "sentence"
    .replace(/\\(?:section|subsection|paragraph|label)\*?\{[^}]*\}/g, "\n")
    .replace(/\\(?:begin|end)\{[^}]*\}/g, "\n");
  const masked = maskNonBoundaryPeriods(stripped); // 1:1 char replacement — offsets align
  const sentences: string[] = [];
  let start = 0;
  for (const m of masked.matchAll(/(?<=[.!?])\s+(?=[A-Z\\])/g)) {
    sentences.push(stripped.slice(start, m.index));
    start = m.index! + m[0].length;
  }
  sentences.push(stripped.slice(start));
  const out: { sentence: string; keys: string[] }[] = [];
  for (const sentence of sentences) {
    if (!/\\cite/.test(sentence)) continue;
    const keys = [...citedKeys(sentence)];
    if (keys.length > 0) out.push({ sentence: sentence.trim(), keys });
  }
  return out;
}

/** Concurrency-limited map: run `fn` over `items` with at most `limit` in flight, results in order. */
export async function mapLimit<T, R>(items: T[], limit: number, fn: (item: T, i: number) => Promise<R>): Promise<R[]> {
  const results = new Array<R>(items.length);
  let next = 0;
  const worker = async (): Promise<void> => {
    while (next < items.length) {
      const i = next++;
      try {
        results[i] = await fn(items[i], i);
      } catch (error) {
        next = items.length; // stop scheduling; let already-running jobs finish and persist
        throw error;
      }
    }
  };
  const settled = await Promise.allSettled(Array.from({ length: Math.min(limit, items.length) }, worker));
  const failed = settled.find((r) => r.status === "rejected");
  if (failed?.status === "rejected") throw failed.reason;
  return results;
}

export async function runHardGates(inp: HardGateInput, r: GateRunners): Promise<LintProblem[]> {
  const problems: LintProblem[] = [];
  problems.push(...lintAnchors(inp.paperTex, inp.knownObjIds, inp.frozenBodies));
  problems.push(...lintEnvOrder(inp.paperTex, inp.layerOrder));
  problems.push(...repairObjRefs(inp.paperTex, new Set(parseAnchoredEnvs(inp.paperTex).map((e) => e.obj_id))).problems); // why: P3 revisions must not defer dangling obj refs to P4.

  const pool = new Set(inp.bibEntries.map((e) => e.key));
  for (const k of citedKeys(inp.paperTex)) {
    if (!pool.has(k)) problems.push({ gate: "cite-pool", detail: `\\cite{${k}} not in the verified pool` });
  }

  const oc = await r.overclaim(inp.frontMatter, inp.frozenEnvsTex);
  if (!oc.clean) {
    for (const f of oc.flags ?? []) {
      // The auditor quotes the sentence with its `\cref{obj:…}` links and sometimes returns a
      // "fix" that only strips the `obj:` prefix (seen on 6 of 8 flags in one run): restoring the
      // prefix makes such a fix identical to the sentence, and a no-op flag is no finding.
      const fix = f.fix === undefined ? undefined : canonicalizeObjRefs(f.fix, inp.knownObjIds);
      if (fix !== undefined && fix.replace(/\s+/g, " ").trim() === f.sentence.replace(/\s+/g, " ").trim()) continue;
      problems.push({ gate: "overclaim", detail: `${f.sentence}${fix ? ` → ${fix}` : ""}` });
    }
    if ((oc.flags ?? []).length === 0) problems.push({ gate: "overclaim", detail: "flagged without detail" });
  }
  const byKey = new Map(inp.bibEntries.map((e) => [e.key, e]));
  const pairs: { sentence: string; entry: BibEntry }[] = [];
  for (const { sentence, keys } of citingSentences(inp.paperTex)) {
    for (const k of keys) {
      const entry = byKey.get(k);
      if (!entry) continue; // already a cite-pool problem
      pairs.push({ sentence, entry });
    }
  }
  // Citation support: one batched runner covers every pair. A pair the auditor returned no
  // verdict for stays advisory (`unverifiable`) so a parse failure can neither block nor
  // silently pass — and it is not cached, so a re-run retries it.
  const pre = await r.citationSupportBatch(pairs);
  const citeVerdicts = pairs.map(({ sentence, entry }) => ({
    sentence,
    entry,
    v: pre.get(`${entry.key}|${sentence}`) ??
      { verdict: "unverifiable" as const, reason: "auditor returned no verdict for this pair" },
  }));
  for (const { sentence, entry, v } of citeVerdicts) {
    const k = entry.key;
    if (v.verdict === "unsupported") {
      problems.push({ gate: "citation-support", detail: `${k}: ${v.reason ?? "unsupported"} — "${sentence.slice(0, 120)}"` });
    } else if (v.verdict === "unverifiable") {
      // advisory: evidence is silent, nothing contradicts — callers filter
      // this gate out of the hard pass/fail set and log it instead.
      problems.push({ gate: "citation-unverifiable", detail: `${k}: ${v.reason ?? ""} — "${sentence.slice(0, 120)}"` });
    }
  }
  return problems;
}

export interface RubricReview {
  scores: Record<string, number>;
  weaknesses: string[];
  /** Concrete, locatable, mechanically fixable reader-facing defects. Unlike `weaknesses`
   *  (judgment calls, weighed against the score threshold) these are ALWAYS repaired: a
   *  defect every reviewer flagged used to ship whenever the numeric score cleared the bar. */
  defects: string[];
}

/** Boundary validation for a model-emitted rubric review. Malformed JSON must be
 *  rejected here, not scored: a string score becomes NaN, so a garbage review would
 *  silently read as a passing (advisory) score and skip the revision pass. */
export function parseRubricReview(v: unknown): RubricReview | null {
  if (typeof v !== "object" || v === null) return null;
  const o = v as { scores?: unknown; weaknesses?: unknown; defects?: unknown };
  if (typeof o.scores !== "object" || o.scores === null) return null;
  const entries = Object.entries(o.scores as Record<string, unknown>);
  if (entries.length === 0 || !entries.every(([, s]) => typeof s === "number" && Number.isFinite(s))) return null;
  const weaknesses = o.weaknesses === undefined ? [] : o.weaknesses;
  if (!Array.isArray(weaknesses) || !weaknesses.every((w) => typeof w === "string")) return null;
  // `defects` is optional at the boundary so reviews cached before the field existed stay
  // valid (they simply carry none); a malformed value is still a rejected review.
  const defects = (o as { defects?: unknown }).defects === undefined ? [] : (o as { defects?: unknown }).defects;
  if (!Array.isArray(defects) || !defects.every((w) => typeof w === "string")) return null;
  return { scores: o.scores as Record<string, number>, weaknesses, defects };
}

const reviewMeans = (reviews: RubricReview[]): number[] =>
  reviews
    .map((r) => {
      const v = Object.values(r.scores);
      return v.reduce((a, b) => a + b, 0) / Math.max(1, v.length);
    })
    .sort((a, b) => a - b);

/** Pass statistic for a 2-reviewer ensemble: the harsher reviewer binds. */
export function minRubric(reviews: RubricReview[]): number {
  const means = reviewMeans(reviews);
  return means.length === 0 ? 0 : means[0];
}

/** Marks a synthetic gate problem that exists only to make `gateLoop` re-RUN the gate
 *  (e.g. the auditor replied with invalid JSON, nothing was cached). The paper is not
 *  defective, so the reviser must skip these — dispatching a revision at the sentence a
 *  sentinel happens to name pays a high-effort call to "fix" innocent prose. */
export const GATE_RERUN_SENTINEL = "[gate-rerun]";

/** Bounded gate-revise loop. `run` re-evaluates the gates; `revise` mutates the paper. */
export async function gateLoop(opts: {
  maxRounds: number;
  run: () => Promise<LintProblem[]>;
  revise: (problems: LintProblem[], round: number) => Promise<void>;
}): Promise<{ ok: boolean; rounds: number; problems: LintProblem[] }> {
  let problems = await opts.run();
  let round = 0;
  while (problems.length > 0 && round < opts.maxRounds) {
    round++;
    await opts.revise(problems, round);
    problems = await opts.run();
  }
  return { ok: problems.length === 0, rounds: round, problems };
}

// Model-authored JSON carrying TeX gets the same three-layer escape defense as
// the D-stage boundaries: `normalizeRawModelJson` repairs BOTH invalid escapes
// (`\(m\ge1\)`) and the silent collision class (`\to` decoding to a tab) on the
// raw bytes, where they are still distinguishable; the post-parse deep repair
// then restores control characters that arrived pre-encoded as valid `\u00XX`
// escapes. `repairUnknownJsonEscapes` stays as the legacy fallback.
const parseCandidate = (candidate: string): unknown => {
  const attempts = [
    () => JSON.parse(normalizeRawModelJson(candidate)),
    () => JSON.parse(candidate),
    () => JSON.parse(repairUnknownJsonEscapes(candidate)),
  ];
  for (const attempt of attempts) {
    try {
      const parsed = attempt();
      repairLatexStringsDeep(parsed);
      return parsed;
    } catch {
      /* try the next repair tier */
    }
  }
  return null;
};

/** Extracts the first parseable JSON object from model output.
 *
 *  CONVENTION for NEW dispatch sites: prefer a zod-validated boundary (the
 *  `components.ts` pattern — schema.safeParse, throw on mismatch, never degrade)
 *  over loose parsing. Every reply-boundary bug of 2026-08 (array-vs-object,
 *  cached unparseable verdicts, silently dropped reviewer replies) lived in a
 *  loose-parse call site; the existing sites are individually audited and stay,
 *  but new ones should start from the strict pattern. */
export function parseJsonLoose(text: string): unknown {
  const first = text.indexOf("{");
  const last = text.lastIndexOf("}");
  if (first >= 0 && last > first) {
    const whole = parseCandidate(text.slice(first, last + 1));
    if (whole !== null) return whole;
    let depth = 0;
    let start = -1;
    for (let i = first; i <= last; i++) {
      const c = text[i];
      if (c === "{") {
        if (depth === 0) start = i;
        depth++;
      } else if (c === "}") {
        depth--;
        if (depth === 0 && start >= 0) {
          const parsed = parseCandidate(text.slice(start, i + 1));
          if (parsed !== null) return parsed;
          start = -1;
        }
      }
    }
  }
  return null;
}

/**
 * Quote only genuinely unknown backslash escapes inside JSON strings.
 *
 * A regex cannot do this safely: in the valid JSON source `"\\\\(x\\\\)"`,
 * the second backslash is followed by `(` and looks invalid in isolation, but
 * it has already been consumed by the valid `\\\\` escape.  Scanning escape
 * pairs atomically preserves that source while repairing model output such as
 * `"\\(x\\)"` to `"\\\\(x\\\\)"`.
 */
export function repairUnknownJsonEscapes(candidate: string): string {
  let out = "";
  let inString = false;
  for (let i = 0; i < candidate.length; i++) {
    const c = candidate[i];
    if (!inString) {
      out += c;
      if (c === '"') inString = true;
      continue;
    }
    if (c === '"') {
      out += c;
      inString = false;
      continue;
    }
    if (c !== "\\") {
      out += c;
      continue;
    }
    const next = candidate[i + 1];
    if (next !== undefined && /["\\/bfnrtu]/.test(next)) {
      out += c + next;
      i += 1;
    } else {
      out += "\\\\";
    }
  }
  return out;
}

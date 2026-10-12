import { z } from "zod";
import { parseJsonWithEscapeRepair } from "./shared/codex_json.js";

/**
 * A disclosed external dependency: normally a named Lean hypothesis that ASSUMES
 * a true, standard mathematical fact the theorem ought eventually to prove, but
 * for `gate_class:"cited"` it may instead be a closed non-logical metadata carrier.
 * The proof-review loop's reviewers report it, also on a passing review, and it is
 * aggregated into the global `SUBSTRATE_DEBT.md` ledger so we know what
 * infrastructure to build.
 *
 * This is categorically distinct from a reject-class-A missing assumption: a
 * genuine gate must NOT weaken the claim, smuggle the conclusion, or make the
 * theorem vacuous — it is honest, trackable debt, not laundering.
 */
export interface SubstrateGate {
  /** Lean hypothesis identifier/binder, or cited metadata declaration name. */
  name: string;
  /** The assumed proposition or recorded metadata (informal or Lean rendering). */
  statement: string;
  /** The standard theorem this encodes (e.g. "Pinsker's inequality"). */
  classical_fact: string;
  /** The substrate layer whose absence forces the assumption. */
  missing_infra: string;
  /**
   * Discharge fate on the discharge-this-run axis (absent ⇒ "gated", back-compat):
   *  - "gated": WILL be discharged this run (parallelism gate); recorded in
   *    SUBSTRATE_DEBT.md until its proof lands. Verified by that proof.
   *  - "cited": NOT discharged this run — a logical assumption or closed metadata
   *    carrier matched against `source`; recorded in CITED_DEPENDENCIES.md.
   */
  gate_class?: "gated" | "cited";
  /** For `gate_class:"cited"`: the citation this carrier is matched against. */
  source?: { cite_id: string; locator: string; url?: string };
  /**
   * For `gate_class:"cited"`: the F2.5 source-match verdict.
   *  - `cited-verified`: Lean def matches the FETCHED source at the locator.
   *  - `cited-verified-attested`: matches the attested `verbatim_statement` (no fetch).
   *  - `cited-mismatch`: def does NOT match — HARD-BLOCKS banking.
   *  - `cited-underspecified`: carrier is not closed/self-contained — a logical
   *    condition is left abstract, or a metadata clause is missing/caller-supplied
   *    instead of fixed by the declaration — HARD-BLOCKS banking.
   *  - `cited-source-unverifiable`: neither fetch nor verbatim statement — invalid
   *    for new runs; migration-only carve-out (flag, do not block).
   */
  check_status?:
    | "cited-verified"
    | "cited-verified-attested"
    | "cited-mismatch"
    | "cited-underspecified"
    | "cited-source-unverifiable";
}

/** A review boundary's verdict. `accept` is a synonym of `pass`. */
export type ReviewResult =
  | { status: "pass"; notes?: string }
  | { status: "accept"; notes?: string; classification?: string }
  | {
      status: "revise" | "reject";
      classification: string;
      perItemFindings: Array<{
        label: string;
        verdict: string;
        one_line: string;
      }>;
      verbatim_critique: string;
      /**
       * D0.5.G only: which gap shape separates the delivered kernel from the
       * proposal's promise.
       *
       * - `kernel_substituted` — D0 derived a different (weaker) object than the
       *   proposal headlined.
       * - `assumption_omitted` — the headline object was derived only after
       *   dropping a load-bearing assumption.
       * - `direction_only` — the proposal promised an iff / equivalence frontier;
       *   D0 proved one direction.
       * - `constructive_object_missing` — the proposal promised an enumeration,
       *   algorithm, or explicit threshold; D0 proved existence only.
       * - `tier_genuinely_below` — the derived kernel matches the proposal and
       *   that kernel is honestly below the floor.
       *
       * `bin/bank_entry.ts` reads it from the review log to classify the
       * reusability of the run.
       */
      proposal_promise_gap?:
        | "kernel_substituted"
        | "assumption_omitted"
        | "direction_only"
        | "constructive_object_missing"
        | "tier_genuinely_below"
        | "proposal_drift";
    };

export const reviewResultSchema = z.union([
  z.object({
    status: z.union([z.literal("pass"), z.literal("accept")]),
    notes: z.string().optional(),
    classification: z.string().optional(),
  }).passthrough(),
  z.object({
    status: z.union([z.literal("revise"), z.literal("reject")]),
    classification: z.string(),
    perItemFindings: z.array(
      z.object({
        label: z.string(),
        verdict: z.string(),
        one_line: z.string(),
      }),
    ),
    verbatim_critique: z.string(),
    proposal_promise_gap: z
      .enum([
        "kernel_substituted",
        "assumption_omitted",
        "direction_only",
        "constructive_object_missing",
        "tier_genuinely_below",
        "proposal_drift",
      ])
      .optional(),
  }).passthrough(),
]) as unknown as z.ZodType<ReviewResult>;

export const stageOutputSchema = z
  .object({
    status: z.string().optional(),
    message: z.string().optional(),
    missing_items: z
      .array(
        z.object({
          kind: z.string(),
          name_suggestion: z.string(),
          purpose: z.string(),
          why_substantial: z.string(),
          nl_artifact_reference: z.string().optional(),
          suggested_location: z.string().optional(),
        }),
      )
      .optional(),
  })
  .passthrough();

/**
 * Extract the first valid JSON object from `text`.
 *
 * Walks brace depth (respecting strings + escapes) to find each candidate
 * balanced `{...}` slice, then attempts `JSON.parse` on it. Returns the first
 * slice that parses successfully. This handles three real-world layouts:
 *
 *   (a) Pure JSON output (the common case).
 *   (b) Prose-then-JSON ("Reading the .md confirms…\n{\"route\":...}").
 *   (c) Prose containing accidental balanced braces in code-spans
 *       (e.g. a backticked Lean set ``{Z=z_l}`` or a ``{x | P x}`` builder)
 *       FOLLOWED by the real JSON body. Without try-and-retry, the legacy
 *       extractor latched onto the first balanced pair from the prose and
 *       failed `JSON.parse` at position 1 (unquoted key), masking a perfectly
 *       valid JSON object further down. This was the recurring
 *       "model output did not contain a JSON object" /
 *       "Expected property name or '}' in JSON at position 1" failure.
 *
 * Falls back to a first-`{` / last-`}` slice only if no balanced parse
 * succeeds, which preserves behavior for outputs with stray closing braces.
 *
 * Every candidate slice is parsed through `parseJsonWithEscapeRepair`, so an
 * otherwise-complete payload is never lost to a raw LaTeX backslash — the class
 * that killed a completed D0.5.G verdict at round 60 ("Bad escaped character in
 * JSON at position 1273"). This funnel backs `parseAgentJson`, every D-stage stdout
 * boundary and every F-stage review/intervention payload, so wiring the repair here
 * rather than per call site is what stops the class from resurfacing at whichever
 * boundary next quotes inline math. See that helper for why the repair can make a
 * parse succeed but never succeed DIFFERENTLY.
 */
export function extractJsonObject(text: string): unknown {
  let firstParseError: unknown = null;

  const fences = Array.from(text.matchAll(/```([^\n`]*)\n?([\s\S]*?)```/g));
  const jsonFences = fences.filter((m) => m[1].trim().toLowerCase().startsWith("json"));
  const otherFences = fences.filter((m) => !m[1].trim().toLowerCase().startsWith("json"));
  // why: scan the raw text in DOCUMENT ORDER FIRST, so the FIRST valid JSON object wins — a real bare
  // object (e.g. `{"route":"stage_2"}`) must NOT be overridden by a later ```json example/diagnostic
  // the model appended. Accidental prose braces (`{x | P x}`) fail JSON.parse and are skipped, so the
  // real object further down is still found. Fenced contents are only a fallback when the document-order
  // scan finds nothing parseable (e.g. JSON that is only well-formed once the fence is stripped).
  const candidates = [text, ...jsonFences.map((m) => m[2]), ...otherFences.map((m) => m[2])];

  for (const candidate of candidates) {
    let cursor = 0;
    // Every top-level balanced object this candidate yields. Collected rather than
    // returned-on-first so that an ambiguous output (narration object + real payload)
    // is VISIBLE in the transcript instead of silently resolving to whichever came
    // first in document order.
    const parsed: unknown[] = [];
    // Try every balanced `{...}` starting at successive `{` positions; accept
    // the first one that JSON.parse can read. This survives prose with
    // accidentally balanced curly-brace runs before the real JSON.
    while (true) {
      const start = candidate.indexOf("{", cursor);
      if (start === -1) break;
      const balancedEnd = findBalancedObjectEnd(candidate, start);
      if (balancedEnd === -1) {
        // This object never closes — the output is TRUNCATED (a watchdog kill mid-write
        // is the usual cause). Every `{` after this point is therefore nested inside it,
        // so continuing the scan can only return a fragment of the payload we failed to
        // read: `{"a":1,"b":{"c":2}` used to yield `{"c":2}`. Stop scanning this
        // candidate so truncation surfaces as a parse failure instead of a plausible
        // wrong object.
        if (firstParseError === null) {
          firstParseError = new Error(
            `model output contains an unterminated JSON object at offset ${start} (truncated response)`,
          );
        }
        break;
      }
      const slice = candidate.slice(start, balancedEnd + 1);
      try {
        parsed.push(parseJsonWithEscapeRepair(slice));
        // Skip PAST this object, not one character into it.
        //
        // `cursor = start + 1` was the load-bearing defect: on a top-level parse
        // failure the walk re-entered the object it had just rejected and returned
        // one of its NESTED sub-objects. A payload with one bad LaTeX escape
        // (`"\sum"` is not a valid JSON escape) silently degraded to an inner
        // fragment like `{"cite_id":"C1"}` — which then validated, because
        // `stageOutputSchema` is all-optional plus passthrough. Advancing past the
        // object makes a failed payload stay failed.
        cursor = balancedEnd + 1;
      } catch (err) {
        if (firstParseError === null) firstParseError = err;
        cursor = balancedEnd + 1;
      }
    }
    if (parsed.length > 0) {
      if (parsed.length > 1) {
        // Behavior-preserving (first wins), but no longer silent. A model that
        // narrates before emitting — or echoes the prompt's own
        // `{"status":"completed",...}` example line — produces exactly this, and the
        // echoed template would otherwise be accepted as a genuine completion.
        console.error(
          `[extractJsonObject] AMBIGUOUS output: ${parsed.length} top-level JSON objects found; ` +
            `using the first. Keys per object: ` +
            parsed.map((o) => `{${Object.keys(o as object).slice(0, 6).join(",")}}`).join(" | "),
        );
      }
      return parsed[0];
    }
    // Legacy fallback: first `{` to last `}`. Rarely useful when balanced
    // parsing already failed, but kept for parity with the prior behavior on
    // malformed outputs that nonetheless contain a coarsely-recoverable body.
    const firstStart = candidate.indexOf("{");
    const lastEnd = candidate.lastIndexOf("}");
    if (firstStart !== -1 && lastEnd > firstStart) {
      try {
        return parseJsonWithEscapeRepair(candidate.slice(firstStart, lastEnd + 1));
      } catch (err) {
        if (firstParseError === null) firstParseError = err;
      }
    }
  }
  if (firstParseError) throw firstParseError;
  throw new Error("model output did not contain a JSON object");
}

function findBalancedObjectEnd(text: string, start: number): number {
  let depth = 0;
  let inString = false;
  let escape = false;
  for (let i = start; i < text.length; i++) {
    const ch = text[i];
    if (inString) {
      if (escape) {
        escape = false;
      } else if (ch === "\\") {
        escape = true;
      } else if (ch === '"') {
        inString = false;
      }
      continue;
    }
    if (ch === '"') {
      inString = true;
      continue;
    }
    if (ch === "{") {
      depth++;
    } else if (ch === "}") {
      depth--;
      if (depth === 0) return i;
    }
  }
  return -1;
}

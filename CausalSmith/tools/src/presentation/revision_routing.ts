// Orchestrator-owned routing from a P5 finding to either the holistic manuscript
// reviser or an explicit halt. The P5 referee remains pipeline-stage-independent.
import type { FindingKind, ReviewFinding, PriorReview } from "./revision_brief.js";

/** One unattended pass: it fixes sentence-level findings; what a referee repeats afterwards is
 * structural (frozen placement, definitions, literature comparison) and is revised by hand. */
export type RevisionAction =
  | { type: "revise" } // prose or structure the orchestrator rewrites by hand in the sources
  | { type: "escalate" } // the math/statement itself — out of causalsmith scope
  | { type: "decide" }; // orchestrator judgement (other, or a kind with no single stage)

/** kind → orchestrator action. Prose and structure rewrites are the orchestrator's hand work. */
export const KIND_ACTION: Record<FindingKind, RevisionAction> = {
  prose: { type: "revise" },
  structure: { type: "revise" },
  statement: { type: "escalate" },
  citation: { type: "decide" },
  other: { type: "decide" },
};

const norm = (s: string) => s.toLowerCase().replace(/[^a-z0-9]+/g, " ").trim();

/** A referee can identify a valid problem whose remedy is outside presentation
 * rewriting; it is escalated, never synthesized by a rewrite. */
export function requiresNewResearch(f: ReviewFinding): boolean {
  // The referee's structured `remedy` is authoritative when present: a `rewrite` finding whose
  // suggested fix merely mentions proving or simulating ("unless the authors add and prove …") is
  // still a rewrite. The keyword scan below is only the fallback for a finding with no remedy.
  if (f.remedy) return f.remedy !== "rewrite";
  const text = norm(`${f.issue} ${f.fix}`);
  return /\b(?:prove|new theorem|new lemma|derive a result|additional result|simulation|empirical exercise|experiment|implement|new data|collect data|literature search|find a citation|source formalization|change the lean|change the theorem)\b/.test(text);
}

/** A `statement` finding that concerns only an environment's TITLE — the display name, not the
 *  mathematics. A title is presentation: it names a result, it does not state it, and the
 *  statement audit keys on the BODY. So an overstating title ("Adaptive root-n minimaxity" over a
 *  theorem that is fixed-code and fixed-separation) is repairable in-run and must not be routed to
 *  the operator: user directive 2026-08-21, renames need no approval. Detected narrowly — the
 *  finding must talk about the name AND propose a rewrite — so a finding about the mathematics
 *  still escalates. */
export function isTitleOnlyFinding(f: ReviewFinding): boolean {
  if (f.remedy && f.remedy !== "rewrite") return false;
  const text = norm(`${f.issue} ${f.fix}`);
  const namesTheTitle = /\b(?:title|titled|heading|named|name of|shorthand|label)\b/.test(text);
  const aboutOverstatement = /\b(?:overstate|overstates|overstating|oversell|overclaim|overclaims|misleading|promises|suggests more|stronger than)\b/.test(text);
  return namesTheTitle && aboutOverstatement;
}

export function actionForFinding(f: ReviewFinding): RevisionAction {
  if (requiresNewResearch(f)) return { type: "escalate" };
  if (f.kind === "statement" && isTitleOnlyFinding(f)) return { type: "revise" };
  return KIND_ACTION[f.kind ?? "other"];
}

/** Stable enough to compare the same issue family across successive P5 wordings.
 * P5 supplies `finding_id` when possible; the normalized fallback keeps old runs usable. */
export function findingFingerprint(f: ReviewFinding): string {
  if (f.finding_id?.trim()) return norm(f.finding_id);
  const issue = norm(f.issue)
    .replace(/\b\d+(?:\.\d+)?\b/g, "#")
    .split(" ")
    .slice(0, 18)
    .join(" ");
  return `${f.kind ?? "other"}|${norm(f.section)}|${issue}`;
}

/** Only prose/structure rewrite findings are the orchestrator's to rewrite in the sources. Everything
 * else is persisted for adjudication instead of being silently weakened or citation-laundered. */
export function partitionFindings(findings: ReviewFinding[]): {
  repairable: ReviewFinding[];
  blocked: ReviewFinding[];
} {
  const repairable: ReviewFinding[] = [];
  const blocked: ReviewFinding[] = [];
  for (const finding of findings) {
    const action = actionForFinding(finding);
    (action.type === "revise" ? repairable : blocked).push(finding);
  }
  return { repairable, blocked };
}

/** A human-readable routing plan grouped by who acts: the orchestrator's hand revision of the
 *  sources, an escalation out of scope, or its own call. */
export function renderRoutingPlan(review: PriorReview): string {
  const byBucket = new Map<string, string[]>();
  const push = (k: string, s: string) => byBucket.set(k, [...(byBucket.get(k) ?? []), s]);
  for (const f of review.findings) {
    const a = actionForFinding(f);
    const remedy = f.remedy ? `·${f.remedy}` : "";
    const line = `[${f.severity}·${f.kind ?? "other"}${remedy}] (${f.section}) ${f.issue}`;
    if (a.type === "revise") push("fix by hand in the authored sources (prose/structure rewrite)", line);
    else if (a.type === "escalate") push("escalate — out of causalsmith scope (bank/causalsmith)", line);
    else push("your call — orchestrator decides", line);
  }
  const out: string[] = [`# Revision routing plan (${review.recommendation})`, ""];
  for (const [bucket, lines] of byBucket) {
    out.push(`## ${bucket}`, ...lines.map((l) => `- ${l}`), "");
  }
  out.push("→ revise by hand at the level that owns each finding; formal statements remain frozen; then rescore once");
  return out.join("\n") + "\n";
}

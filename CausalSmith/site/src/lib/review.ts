/**
 * The AI referee report (`p5_review.json`) as the SITE sees it.
 *
 * One rule shapes this whole module: the referee's `recommendation`
 * (accept / minor_revision / major_revision / reject) is NEVER shown to a
 * reader (user decision, 2026-09-20 — show the critique, not the verdict). It
 * is enforced structurally rather than by remembering not to print it: the
 * parser below is a WHITELIST, so `recommendation` is never read out of the
 * artifact and therefore cannot exist on any object a page can render.
 *
 * Everything is defensive. A bundle with no review, a truncated file, a round
 * history that is half-written — none of those may fail a build; they cost the
 * reader the panel and nothing else.
 */

export const SEVERITIES = ["major", "minor", "nit"] as const;
export type Severity = (typeof SEVERITIES)[number];

export interface Finding {
  severity: Severity;
  /** Where in the paper ("main results", "setup and assumptions"); may be absent. */
  section: string | null;
  issue: string;
  /** The referee's suggested fix — folded away under the finding. */
  fix: string | null;
}

/** One past referee pass. Scores are noisy, so every draw is kept and shown. */
export interface ReviewRound {
  /** 1-based, ascending; the last row is the current report. */
  round: number;
  score: number | null;
  findings: number;
  /** Only when the artifact recorded one — legacy rounds have no date. */
  date: string | null;
  current: boolean;
}

export interface Review {
  score: number | null;
  rationale: string | null;
  summary: string | null;
  strengths: string[];
  findings: Finding[];
  /** The MAJOR-severity findings — the landing/paper fold's "Main criticisms". */
  majors: Finding[];
  questions: string[];
  /** ISO date the referee ran; absent on every bundle emitted before P5 wrote it. */
  reviewedAt: string | null;
  /** sha256 of the `paper.tex` the referee read; absent on legacy files. */
  manuscriptSha256: string | null;
  counts: { major: number; minor: number; nit: number; total: number };
  history: ReviewRound[];
}

const isObj = (v: unknown): v is Record<string, unknown> =>
  typeof v === "object" && v !== null && !Array.isArray(v);

const str = (v: unknown): string | null => {
  const s = typeof v === "string" ? v.trim() : "";
  return s.length > 0 ? s : null;
};

const num = (v: unknown): number | null =>
  typeof v === "number" && Number.isFinite(v) ? v : null;

const strList = (v: unknown): string[] =>
  Array.isArray(v) ? v.map(str).filter((s): s is string => s !== null) : [];

/**
 * A REAL calendar date, or null.
 *
 * `2026-02-31` and `2026-99-99` both matched the old shape check and were then
 * printed at the reader and compared lexically to decide staleness (audit,
 * 2026-09-21). The UTC round-trip is what rejects them: a date that does not
 * survive `Date.UTC` is not a date.
 */
export const isoDate = (v: unknown): string | null => {
  const s = str(v);
  const m = s ? /^(\d{4})-(\d{2})-(\d{2})(?:[T ]|$)/.exec(s) : null;
  if (!m) return null;
  const [y, mo, d] = [Number(m[1]), Number(m[2]), Number(m[3])];
  const utc = new Date(Date.UTC(y, mo - 1, d));
  if (utc.getUTCFullYear() !== y || utc.getUTCMonth() !== mo - 1 || utc.getUTCDate() !== d) {
    return null;
  }
  return `${m[1]}-${m[2]}-${m[3]}`;
};

/** A sha256 digest, or null. Trimmed, lowercased, exactly 64 hex characters —
 *  a whitespace string was being treated as a real, mismatching hash. */
export const sha256 = (v: unknown): string | null => {
  const s = str(v)?.toLowerCase();
  return s && /^[0-9a-f]{64}$/.test(s) ? s : null;
};

/**
 * Normalizes a severity label. Today's corpus uses exactly major/minor/nit;
 * an unrecognized label becomes `minor` — the middle bucket, so a future
 * severity is neither dramatized into a headline criticism nor dismissed as a
 * nit by a site that does not yet know the word.
 */
function severityOf(v: unknown): Severity {
  const s = (str(v) ?? "").toLowerCase();
  if (s === "major" || s === "critical" || s === "blocker") return "major";
  if (s === "nit" || s === "nitpick" || s === "trivial") return "nit";
  return "minor";
}

function parseFindings(v: unknown): Finding[] {
  if (!Array.isArray(v)) return [];
  const out: Finding[] = [];
  for (const raw of v) {
    if (!isObj(raw)) continue;
    const issue = str(raw.issue);
    if (!issue) continue; // a finding with no text is nothing to show
    out.push({
      severity: severityOf(raw.severity),
      section: str(raw.section),
      issue,
      fix: str(raw.fix),
    });
  }
  return out;
}

/** A history round as read from `p5_review_history/round_NNN.json`. */
export interface RawRound {
  /** File order (0-based, as `round_000` … name it); rendered 1-based. */
  index: number;
  raw: unknown;
}

function parseHistory(rounds: RawRound[], current: { score: number | null; findings: number; date: string | null }): ReviewRound[] {
  const out: ReviewRound[] = [];
  for (const r of [...rounds].sort((a, b) => a.index - b.index)) {
    if (!isObj(r.raw)) continue;
    out.push({
      round: out.length + 1,
      score: num(r.raw.score),
      findings: Array.isArray(r.raw.findings) ? r.raw.findings.length : 0,
      date: isoDate(r.raw.reviewed_at),
      current: false,
    });
  }
  // The shipped report is the last round, not a separate thing: `round_000…N`
  // are the passes BEFORE it. A paper with no history file is a single round.
  out.push({ round: out.length + 1, ...current, current: true });
  return out;
}

/**
 * Parses `p5_review.json` (+ optional round history) into the render model.
 * Returns null when there is nothing worth showing — no summary, no findings,
 * no score — so callers can treat "has a review" as a single boolean.
 */
export function parseReview(raw: unknown, rounds: RawRound[] = []): Review | null {
  if (!isObj(raw)) return null;
  const findings = parseFindings(raw.findings);
  const summary = str(raw.summary);
  const score = num(raw.score);
  const strengths = strList(raw.strengths);
  if (summary === null && findings.length === 0 && score === null && strengths.length === 0) {
    return null;
  }
  const counts = {
    major: findings.filter((f) => f.severity === "major").length,
    minor: findings.filter((f) => f.severity === "minor").length,
    nit: findings.filter((f) => f.severity === "nit").length,
    total: findings.length,
  };
  const reviewedAt = isoDate(raw.reviewed_at);
  return {
    score,
    rationale: str(raw.score_rationale),
    summary,
    strengths,
    findings,
    majors: findings.filter((f) => f.severity === "major"),
    questions: strList(raw.questions_for_authors),
    reviewedAt,
    manuscriptSha256: sha256(raw.manuscript_sha256),
    counts,
    history: parseHistory(rounds, { score, findings: findings.length, date: reviewedAt }),
  };
}

// ── is this report still about the paper on screen? ──────────────────────
//
// Two sources of truth, in order of strength:
//
//   1. THE HASH. P5 records the sha256 of the `paper.tex` the referee read;
//      P4 records the sha256 of each version's `paper.tex`. Equal hashes mean
//      the report IS about this draft — a fact, not an inference. Different
//      hashes mean it is not.
//   2. THE DATES. `reviewed_at` before `revised` suggests drift. Weaker: a
//      same-day revision after the review looks fresh by date and is not.
//
// Neither may be assumed present. Every bundle shipped today has neither hash
// and no `reviewed_at`, and the backfill leaves `paper_sha256` null on the
// historical version entries — so the generic wording is the common case, not
// an edge case.

/** The paper's current `paper.tex` hash, if the bundle recorded one. */
export function latestPaperSha256(
  versions: { paper_sha256?: string | null }[] | null | undefined,
): string | null {
  if (!Array.isArray(versions) || versions.length === 0) return null;
  return sha256(versions[versions.length - 1]?.paper_sha256);
}

/** What the paper's current state says about this report. */
export interface PaperState {
  /** ISO date of the current version. Nullable in the contract. */
  revised?: string | null;
  /** sha256 of the current `paper.tex` — `latestPaperSha256(meta.versions)`. */
  paperSha256?: string | null;
}

export type Freshness =
  /** Hashes agree: the report is about exactly this draft. */
  | "fresh"
  /** Hashes disagree, or the revision postdates the review. */
  | "stale"
  /** No evidence either way. */
  | "unknown";

export function reviewFreshness(review: Review, paper: PaperState = {}): Freshness {
  // Both inputs are re-validated here, not trusted: a caller can hand us
  // anything meta.json happens to contain, and a lexical comparison against
  // "not-a-date" would answer confidently and wrongly.
  const mine = sha256(review.manuscriptSha256);
  const theirs = sha256(paper.paperSha256);
  if (mine && theirs) return mine === theirs ? "fresh" : "stale";
  const reviewed = isoDate(review.reviewedAt);
  const revised = isoDate(paper.revised);
  if (reviewed && revised) return reviewed < revised ? "stale" : "unknown";
  return "unknown";
}

/** Kept for readability at call sites that only want the warning condition. */
export function isStale(review: Review, paper: PaperState = {}): boolean {
  return reviewFreshness(review, paper) === "stale";
}

/**
 * The sentence under every score fold. It always says the report is one
 * automated referee; it warns about drift when there is drift to warn about,
 * says so plainly when the report is known to be about the current draft, and
 * admits it cannot tell when nothing in the bundle says either way.
 */
export function stalenessNote(
  review: Review,
  paper: PaperState = {},
  fmt: (d: string) => string = (d) => d,
): string {
  const disclaimer = "One automated referee’s estimate — not peer review.";
  // Re-validated, not trusted: a date the sentence prints must be a real one.
  const reviewed = isoDate(review.reviewedAt);
  const revised = isoDate(paper.revised);
  // "Referee report of", not "report on the draft of": the date belongs to
  // the REPORT, and the old phrasing read as if it dated the manuscript.
  const on = reviewed ? `Referee report of ${fmt(reviewed)}.` : null;
  switch (reviewFreshness(review, paper)) {
    case "fresh":
      return `${on ?? "Referee report on the current draft."} It was read against the current draft of the paper. ${disclaimer}`;
    case "stale": {
      // When the hashes decide, the DATES may still disagree with the verdict:
      // a report can carry a later date than the revision it predates, and
      // juxtaposing the two read as a contradiction (audit r4). So when the
      // hashes are what we know, say that, without the dates.
      if (sha256(review.manuscriptSha256) && sha256(paper.paperSha256)) {
        return `${on ? `${on} ` : ""}This report was written for an earlier draft; the ` +
          `paper has been revised since, so some findings may already be addressed. ` +
          `${disclaimer}`;
      }
      const since = revised
        ? `The paper was last revised ${fmt(revised)}, so some findings may already be addressed.`
        : "The paper has been revised since, so some findings may already be addressed.";
      return on ? `${on} ${since} ${disclaimer}` : `${since} ${disclaimer}`;
    }
    default:
      return on
        ? `${on} ${disclaimer}`
        : `The paper may have been revised since this report. ${disclaimer}`;
  }
}

import { describe, it, expect } from "vitest";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { formatDate } from "../src/lib/citation.js";
import {
  isStale,
  latestPaperSha256,
  parseReview,
  reviewFreshness,
  stalenessNote,
} from "../src/lib/review.js";

const FIXTURE = resolve(import.meta.dirname, "..", "fixtures", "demo_paper_v1");
const raw = JSON.parse(readFileSync(resolve(FIXTURE, "p5_review.json"), "utf8"));
const round0 = JSON.parse(
  readFileSync(resolve(FIXTURE, "p5_review_history", "round_000.json"), "utf8"),
);

describe("review parser", () => {
  it("reads the report the site shows", () => {
    const r = parseReview(raw)!;
    expect(r.score).toBe(6.4);
    expect(r.summary).toMatch(/demonstration upper bound/);
    expect(r.strengths).toHaveLength(3);
    expect(r.findings).toHaveLength(3);
    expect(r.questions).toHaveLength(2);
    expect(r.reviewedAt).toBe("2026-07-18");
    expect(r.manuscriptSha256).toMatch(/^[0-9a-f]{64}$/);
    expect(r.counts).toEqual({ major: 1, minor: 1, nit: 1, total: 3 });
    expect(r.majors.map((f) => f.section)).toEqual(["main results"]);
  });

  // The whole point of the module: the referee's verdict is not merely
  // unrendered, it is never read out of the artifact.
  it("never carries the recommendation into the render model", () => {
    const r = parseReview(raw, [{ index: 0, raw: round0 }])!;
    expect(raw.recommendation).toBe("major_revision"); // it IS in the artifact
    expect(round0.recommendation).toBe("reject");
    expect(JSON.stringify(r)).not.toMatch(/recommendation|major_revision|minor_revision|reject/);
  });

  it("tolerates a bundle with no report at all", () => {
    expect(parseReview(null)).toBeNull();
    expect(parseReview("not an object")).toBeNull();
    expect(parseReview({})).toBeNull();
    expect(parseReview({ recommendation: "accept" })).toBeNull(); // nothing to show
  });

  it("keeps whatever a half-written report does carry", () => {
    const r = parseReview({ score: 5, findings: "not a list", strengths: [1, null, "ok"] })!;
    expect(r.score).toBe(5);
    expect(r.findings).toEqual([]);
    expect(r.strengths).toEqual(["ok"]);
    expect(r.summary).toBeNull();
  });

  it("drops a finding with no text and normalizes an unknown severity to minor", () => {
    const r = parseReview({
      score: 1,
      findings: [
        { severity: "major", issue: "a" },
        { severity: "MAJOR", issue: "b" },
        { severity: "showstopper", issue: "c" },
        { severity: "nit", issue: "" },
        "junk",
      ],
    })!;
    expect(r.counts).toEqual({ major: 2, minor: 1, nit: 0, total: 3 });
  });

  it("has no reviewed_at on the legacy files that predate it", () => {
    const r = parseReview({ score: 7, summary: "s" })!;
    expect(r.reviewedAt).toBeNull();
    expect(r.manuscriptSha256).toBeNull();
  });
});

describe("round history", () => {
  it("numbers the rounds 1..N and makes the shipped report the last one", () => {
    const r = parseReview(raw, [
      { index: 1, raw: { score: 5.5, findings: [1, 2, 3] } },
      { index: 0, raw: round0 }, // deliberately out of order
    ])!;
    expect(r.history).toEqual([
      { round: 1, score: 4.1, findings: 2, date: "2026-06-30", current: false },
      { round: 2, score: 5.5, findings: 3, date: null, current: false },
      { round: 3, score: 6.4, findings: 3, date: "2026-07-18", current: true },
    ]);
  });

  it("is a single current round when the bundle kept no history", () => {
    const r = parseReview(raw)!;
    expect(r.history).toHaveLength(1);
    expect(r.history[0]).toMatchObject({ round: 1, current: true });
  });
});

describe("latestPaperSha256", () => {
  const HASH_A = "a".repeat(64);
  const HASH_B = "b".repeat(64);

  it("takes the last version's hash, and treats a null one as absent", () => {
    expect(latestPaperSha256([{ v: 1, paper_sha256: HASH_A }, { v: 2, paper_sha256: HASH_B }]))
      .toBe(HASH_B);
    // The backfill leaves every historical entry null — including, on a
    // not-yet-re-emitted bundle, the latest.
    expect(latestPaperSha256([{ v: 1, paper_sha256: null }])).toBeNull();
    // Not a digest, so not a comparison input: a whitespace or truncated value
    // used to be treated as a real, MISMATCHING hash (audit, 2026-09-21).
    for (const bad of ["  ", "aa", `${HASH_A}zz`, "Z".repeat(64)]) {
      expect(latestPaperSha256([{ v: 1, paper_sha256: bad }]), bad).toBeNull();
    }
    expect(latestPaperSha256([{ v: 1, paper_sha256: `  ${HASH_A.toUpperCase()}  ` }])).toBe(HASH_A);
    expect(latestPaperSha256([{ v: 1 }])).toBeNull();
    expect(latestPaperSha256([])).toBeNull();
    expect(latestPaperSha256(null)).toBeNull();
    expect(latestPaperSha256(undefined)).toBeNull();
  });
});

/**
 * Four cases, in the order the site trusts them: the hash decides when both
 * sides have one, the dates decide when they do not, and nothing decides when
 * the bundle carries neither — which is every bundle shipped today.
 */
// A report dated AFTER the revision it predates: the hash is what decides,
// and the sentence must not put the two dates side by side (audit r4).
describe("a report newer than the revision it predates", () => {
  it("never reads as a contradiction", () => {
    const r = parseReview({
      score: 5,
      summary: "s",
      reviewed_at: "2026-09-01",
      manuscript_sha256: "a".repeat(64),
    })!;
    const note = stalenessNote(r, { revised: "2026-06-01", paperSha256: "b".repeat(64) }, formatDate);
    expect(note).toContain("written for an earlier draft");
    expect(note).not.toContain("1 Jun 2026");
    expect(note).toContain("Referee report of 1 Sep 2026.");
  });
});

describe("date validation", () => {
  // "2026-02-31" matched the old shape check, was printed at the reader, and
  // was then compared lexically to decide staleness (audit, 2026-09-21).
  it("rejects a date that is not a real calendar day", () => {
    for (const bad of ["2026-02-31", "2026-99-99", "2026-13-01", "not-a-date", "2026-1-1", ""]) {
      expect(parseReview({ score: 1, summary: "s", reviewed_at: bad })!.reviewedAt, bad).toBeNull();
    }
  });

  it("accepts a real day, and a timestamp's day", () => {
    expect(parseReview({ score: 1, summary: "s", reviewed_at: "2026-02-28" })!.reviewedAt)
      .toBe("2026-02-28");
    expect(parseReview({ score: 1, summary: "s", reviewed_at: "2028-02-29" })!.reviewedAt)
      .toBe("2028-02-29"); // a leap day IS a day
    expect(parseReview({ score: 1, summary: "s", reviewed_at: "2026-07-18T09:00:00Z" })!.reviewedAt)
      .toBe("2026-07-18");
  });

  it("never lets a malformed date decide freshness", () => {
    const r = parseReview({ score: 1, summary: "s", reviewed_at: "2026-07-18" })!;
    for (const bad of ["not-a-date", "2026-02-31", "zzzz"]) {
      expect(reviewFreshness(r, { revised: bad }), bad).toBe("unknown");
      expect(stalenessNote(r, { revised: bad }, formatDate), bad).not.toContain(bad);
    }
  });
});

describe("staleness", () => {
  const r = parseReview(raw)!; // reviewed 2026-07-18, manuscript hash 0f1e…
  const MINE = r.manuscriptSha256!;
  const DISCLAIMER = "One automated referee’s estimate — not peer review.";

  it("1. hashes differ → stale, whatever the dates say", () => {
    const paper = { revised: "2026-06-01", paperSha256: "ff".repeat(32) };
    expect(reviewFreshness(r, paper)).toBe("stale");
    expect(isStale(r, paper)).toBe(true);
    // The dates disagree with the hash verdict here (the report is NEWER than
    // the revision), so the sentence states what is known and juxtaposes no
    // dates that would read as a contradiction (audit r4).
    expect(stalenessNote(r, paper, formatDate)).toBe(
      `Referee report of 18 Jul 2026. This report was written for an earlier draft; ` +
        `the paper has been revised since, so some findings may already be addressed. ` +
        `${DISCLAIMER}`,
    );
    expect(stalenessNote(r, paper, formatDate)).not.toContain("1 Jun 2026");
  });

  it("2. hashes match → fresh, and no “may have been revised” note", () => {
    const paper = { revised: "2026-08-27", paperSha256: MINE };
    expect(reviewFreshness(r, paper)).toBe("fresh");
    expect(isStale(r, paper)).toBe(false);
    const note = stalenessNote(r, paper, formatDate);
    expect(note).toBe(
      `Referee report of 18 Jul 2026. It was read against the current draft of the ` +
        `paper. ${DISCLAIMER}`,
    );
    expect(note).not.toContain("may have been revised");
    expect(note).not.toContain("may already be addressed");
  });

  it("3. a hash missing → fall back to the dates", () => {
    // Only the review has one (the bundle's versions were backfilled null).
    expect(reviewFreshness(r, { revised: "2026-08-27", paperSha256: null })).toBe("stale");
    // No hash on the paper side, so the DATES decide and may be shown.
    expect(stalenessNote(r, { revised: "2026-08-27", paperSha256: null }, formatDate)).toBe(
      `Referee report of 18 Jul 2026. The paper was last revised 27 Aug 2026, so some ` +
        `findings may already be addressed. ${DISCLAIMER}`,
    );
    // Only the paper has one.
    const noHash = parseReview({ ...raw, manuscript_sha256: undefined })!;
    const some = "c".repeat(64);
    expect(reviewFreshness(noHash, { revised: "2026-06-01", paperSha256: some })).toBe("unknown");
    expect(stalenessNote(noHash, { revised: "2026-06-01", paperSha256: some }, formatDate)).toBe(
      `Referee report of 18 Jul 2026. ${DISCLAIMER}`,
    );
  });

  // All 22 shipped reports are in this case today: no hash, no reviewed_at.
  it("4. no hash and no reviewed_at → the generic wording", () => {
    const legacy = parseReview({ score: 8, summary: "s" })!;
    for (const paper of [{}, { revised: "2026-08-27" }, { revised: null, paperSha256: null }]) {
      expect(reviewFreshness(legacy, paper)).toBe("unknown");
      expect(isStale(legacy, paper)).toBe(false);
      expect(stalenessNote(legacy, paper, formatDate)).toBe(
        `The paper may have been revised since this report. ${DISCLAIMER}`,
      );
    }
  });

  it("never assumes revised is present", () => {
    const paper = { revised: null, paperSha256: "ff".repeat(32) };
    expect(reviewFreshness(r, paper)).toBe("stale");
    expect(stalenessNote(r, paper, formatDate)).toBe(
      `Referee report of 18 Jul 2026. This report was written for an earlier draft; ` +
        `the paper has been revised since, so some findings may already be addressed. ` +
        `${DISCLAIMER}`,
    );
  });
});

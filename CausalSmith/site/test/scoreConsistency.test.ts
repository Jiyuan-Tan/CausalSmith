import { describe, expect, it } from "vitest";
import { existsSync } from "node:fs";
import { resolve } from "node:path";
import { loadBundles } from "../src/lib/bundles.js";

/**
 * One paper, one score.
 *
 * `meta.score` is a copy the pipeline takes out of `p5_review.json`, and the
 * two can drift. While the landing badge read the copy and the review page
 * read the report, a paper could publicly contradict itself — 7.0 on the
 * landing, 6.6 on its own report — and sort under a number it never showed
 * (audit, 2026-09-21).
 *
 * `Bundle.score` is now decided once, at load, by this rule. The corpus gate
 * also keeps the copied metadata aligned with the current review artifact.
 */

const PRESENTATION = resolve(import.meta.dirname, "..", "..", "doc", "presentation");

/**
 * A corpus sweep that finds no corpus proves nothing. Missing bundles are a
 * broken checkout, not a pass — opt out explicitly if you really mean it.
 */
function requireCorpus(found: number): void {
  if (found === 0 && process.env.SITE_ALLOW_NO_CORPUS !== "1") {
    throw new Error(
      "No bundles under doc/presentation: this sweep would pass vacuously. " +
        "Set SITE_ALLOW_NO_CORPUS=1 to allow it.",
    );
  }
}

// The REAL loader, not a reimplementation of the rule: a second copy would
// agree with itself while the site disagreed (audit r4).
const bundles = existsSync(PRESENTATION) ? await loadBundles([PRESENTATION]) : [];

describe("one score per paper", () => {
  it("covers the corpus", () => {
    requireCorpus(bundles.length);
    expect(bundles.length).toBeGreaterThanOrEqual(20);
  });

  it("resolves every paper to exactly one displayable number", () => {
    for (const b of bundles) {
      // What the loader decided IS what every page renders.
      if (typeof b.review?.score === "number") expect(b.score, b.id).toBe(b.review.score);
      else expect(b.score, b.id).toBe(b.meta.score ?? null);
      if (b.score !== null) expect(Number.isFinite(b.score), b.id).toBe(true);
    }
  });

  it("keeps the metadata copy aligned with the current report", () => {
    const drift = bundles
      .filter((b) => typeof b.review?.score === "number" && typeof b.meta.score === "number")
      .filter((b) => b.meta.score !== b.review!.score)
      .map((b) => `${b.id}: meta=${b.meta.score} review=${b.review!.score}`);
    expect(drift).toEqual([]);
  });
});

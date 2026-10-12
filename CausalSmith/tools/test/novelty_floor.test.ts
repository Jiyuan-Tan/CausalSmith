import { describe, expect, it } from "vitest";
import { meetsNoveltyFloor, normalizeReviewerTier, REVIEWER_TIER_RANK } from "../src/novelty.js";

describe("meetsNoveltyFloor", () => {
  it("enforces the flagship floor strictly (regression guard)", () => {
    expect(meetsNoveltyFloor("flagship", "flagship")).toBe(true);
    expect(meetsNoveltyFloor("field", "flagship")).toBe(false);
    expect(meetsNoveltyFloor("subfield", "flagship")).toBe(false);
    expect(meetsNoveltyFloor(undefined, "flagship")).toBe(false);
  });

  it("lets a field-tier proposal meet a field target", () => {
    expect(meetsNoveltyFloor("flagship", "field")).toBe(true);
    expect(meetsNoveltyFloor("field", "field")).toBe(true);
    expect(meetsNoveltyFloor("subfield", "field")).toBe(false);
    expect(meetsNoveltyFloor(undefined, "field")).toBe(false);
  });

  it("treats subfield as the floor for relative-to-literature", () => {
    expect(meetsNoveltyFloor("field", "relative-to-literature")).toBe(true);
    expect(meetsNoveltyFloor("subfield", "relative-to-literature")).toBe(true);
    expect(meetsNoveltyFloor("incremental", "relative-to-literature")).toBe(false);
    expect(meetsNoveltyFloor(undefined, "relative-to-literature")).toBe(false);
  });

  it("imposes no floor for relative-to-repo (any/missing tier passes)", () => {
    expect(meetsNoveltyFloor("incremental", "relative-to-repo")).toBe(true);
    expect(meetsNoveltyFloor("subfield", "relative-to-repo")).toBe(true);
    expect(meetsNoveltyFloor(undefined, "relative-to-repo")).toBe(true);
  });
});

describe("normalizeReviewerTier", () => {
  it("maps a legacy reviewer spelling onto the canonical ladder and ranks it the same", () => {
    expect(normalizeReviewerTier("letter")).toBe("subfield");
    expect(normalizeReviewerTier(" Not-Publishable ")).toBe("incremental");
    expect(normalizeReviewerTier("field")).toBe("field");
    expect(REVIEWER_TIER_RANK["letter"]).toBe(REVIEWER_TIER_RANK["subfield"]);
    expect(REVIEWER_TIER_RANK["not-publishable"]).toBe(REVIEWER_TIER_RANK["incremental"]);
  });
});

import { describe, expect, it } from "vitest";
import { parseLeanImport, publicSectionAt } from "../../src/shared/lean_syntax.js";

describe("publicSectionAt", () => {
  it("counts an unclosed blanket public section through EOF", () => {
    const source = "module\n@[expose] public section\nlemma published : True := by trivial\n";
    expect(publicSectionAt(source, source.indexOf("lemma"))).toBe(true);
  });

  it("stops at the matching end and ignores ordinary sections", () => {
    const source = [
      "public section",
      "lemma published : True := by trivial",
      "end",
      "section",
      "lemma hidden : True := by trivial",
    ].join("\n");
    expect(publicSectionAt(source, source.indexOf("published"))).toBe(true);
    expect(publicSectionAt(source, source.indexOf("hidden"))).toBe(false);
  });

  it.each(["public noncomputable section", "@[expose] public noncomputable section"])(
    "recognizes `%s` as a public frame",
    (section) => {
      const source = `module\n${section}\nlemma published : True := by trivial\n`;
      expect(publicSectionAt(source, source.indexOf("lemma"))).toBe(true);
    },
  );
});

describe("parseLeanImport", () => {
  it("accepts Unicode and every supported identifier punctuation character", () => {
    expect(parseLeanImport("public import CausalSmith.Mathlib.Δ₂_foo'«bar»!?")?.module)
      .toBe("CausalSmith.Mathlib.Δ₂_foo'«bar»!?");
  });
});

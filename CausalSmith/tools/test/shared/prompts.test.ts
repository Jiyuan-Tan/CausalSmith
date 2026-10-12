import { describe, expect, it } from "vitest";
import { renderTemplate } from "../../src/shared/prompts.js";

describe("renderTemplate", () => {
  it("substitutes {{var}} occurrences", () => {
    expect(renderTemplate("a {{x}} b {{y}} c", { x: "1", y: "2" })).toBe("a 1 b 2 c");
  });

  it("leaves unknown {{var}} placeholders intact", () => {
    expect(renderTemplate("hi {{name}} ({{unknown}})", { name: "Alice" })).toBe(
      "hi Alice ({{unknown}})",
    );
  });

  it("substitutes repeated placeholders", () => {
    expect(renderTemplate("{{n}} + {{n}} = 2*{{n}}", { n: "x" })).toBe("x + x = 2*x");
  });

  it("does not interpret regex specials in values", () => {
    // Naive `.replace(string, replacement)` treats $1 etc in `replacement` as
    // capture refs. We use the function form to avoid that — verify.
    expect(renderTemplate("v={{v}}", { v: "$1$&" })).toBe("v=$1$&");
  });

  it("returns the template unchanged when no placeholders", () => {
    expect(renderTemplate("nothing to substitute", {})).toBe("nothing to substitute");
  });
});

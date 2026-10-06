import { describe, it, expect } from "vitest";
import {
  assertSealableLatexPayload,
  repairSerializedLatex,
} from "../../src/discovery/core/latex_serialization.js";

describe("assertSealableLatexPayload", () => {
  it("accepts canonical balanced LaTeX payloads", () => {
    expect(() => assertSealableLatexPayload({
      kind: "definition-replace",
      id: "def:poly-class",
      construction: "The class \\(\\mathcal P_{T,\\beta}(C)=\\{Y:\\|Y\\|\\le B\\}\\).",
      reason: "repair delimiters",
    }, "test payload")).not.toThrow();
  });

  it("treats percent-encoded URL arguments as literal data", () => {
    for (const command of ["url", "nolinkurl", "path"]) {
      for (const argument of ["{https://example.org/Brand%20education.pdf}", "|https://example.org/Brand%20education.pdf|", "|https://example.org/Brand%20\neducation.pdf|"]) {
        expect(() => assertSealableLatexPayload({ citation: `\\${command}${argument}.` }, "URL replay")).not.toThrow();
      }
    }
  });

  it("scans nested brace-form URL arguments without changing their spelling", () => {
    for (const command of ["url", "nolinkurl", "path"]) {
      for (const argument of [String.raw`{https://example.org/{foo}/a%20b}`, String.raw`{https://example.org/\{foo\}/a%20b}`, "{https://example.org/\na%20b}"]) {
        expect(() => assertSealableLatexPayload({ citation: `\\${command}${argument}.` }, "nested URL")).not.toThrow();
      }
      expect(() => assertSealableLatexPayload({ citation: `\\${command}{https://example.org/{foo}/a%20b` }, "unclosed nested URL")).toThrow(/opaque TeX URL/);
    }
  });

  it("counts URL argument braces even after literal backslashes", () => {
    for (const command of ["url", "nolinkurl", "path"]) {
      for (const slashes of ["\\", "\\\\\\"]) {
        expect(() => assertSealableLatexPayload({ citation: `\\${command}{abc${slashes}}.` }, "URL backslash")).not.toThrow();
      }
    }
  });

  it("allows letter URL delimiters after a control-word boundary", () => {
    for (const command of ["url", "nolinkurl", "path"]) {
      expect(() => assertSealableLatexPayload({ citation: `\\${command} xabc%20x.` }, "letter URL delimiter")).not.toThrow();
    }
    expect(() => assertSealableLatexPayload({ citation: String.raw`\urlx{\(unclosed}` }, "different control word")).toThrow(/inline-math/);
  });

  it("rejects recognized URLs whose opaque argument has no closing delimiter", () => {
    for (const command of ["url", "nolinkurl", "path"]) {
      for (const opener of ["{", "|"]) {
        expect(() => assertSealableLatexPayload({ citation: `\\${command}${opener}https://example.org/a%20b` }, "unterminated URL")).toThrow(/opaque TeX URL/);
      }
    }
  });

  it("recognizes literal commands before interpreting percent as a comment", () => {
    for (const citation of [
      String.raw`\verb|% } \( literal| and \(x\).`,
      String.raw`\begin{verbatim}% } \( literal\end{verbatim} and \(x\).`,
    ]) {
      expect(() => assertSealableLatexPayload({ citation }, "literal replay")).not.toThrow();
    }
  });

  it("keeps comments outside literal commands and checks following TeX", () => {
    expect(() => assertSealableLatexPayload({ citation: "% \\url{unclosed\n\\(x\\)." }, "comment replay")).not.toThrow();
    expect(() => assertSealableLatexPayload({ citation: "\\url{https://example.org/a%20b} \\(unclosed" }, "URL trailing math")).toThrow(/inline-math/);
    expect(() => assertSealableLatexPayload({ citation: "\\url{https://example.org/a%20b" }, "incomplete URL")).toThrow(/opaque TeX URL/);
    expect(() => assertSealableLatexPayload({ citation: "\\\\% \\url{ignored\n\\(unclosed" }, "row break comment")).toThrow(/inline-math/);
  });

  it("accepts a legitimate row break directly before a parenthesis inside proved TeX", () => {
    expect(() => assertSealableLatexPayload({
      proof_tex: "\\begin{cases}a\\\\(b+1)&\\text{else}\\end{cases}",
    }, "test payload")).not.toThrow();
  });

  it("rejects a payload with an unclosed inline-math delimiter, naming the field", () => {
    expect(() => assertSealableLatexPayload({
      construction: "for all \\(x\\in\\mathcal X the map is linear.",
    }, "test payload")).toThrow(/construction.*inline-math|inline-math.*construction/s);
  });

  it("rejects a payload with an unclosed display-math delimiter", () => {
    expect(() => assertSealableLatexPayload({
      statement: "We have \\[\\int f\\,d\\mu = 0 and the rest is prose.",
    }, "test payload")).toThrow(/display-math/);
  });

  it("rejects a fully over-escaped payload (doubled delimiters, no canonical single backslash)", () => {
    expect(() => assertSealableLatexPayload({
      construction: "the set \\\\(\\\\{Y: \\\\|Y\\\\|\\\\le B\\\\}\\\\).",
    }, "test payload")).toThrow(/over-escaped/);
  });

  it("rejects a fully over-escaped display-math payload", () => {
    expect(() => assertSealableLatexPayload({
      construction: "the bound \\\\[\\\\|Y\\\\|\\\\le B\\\\] holds.",
    }, "test payload")).toThrow(/over-escaped/);
  });

  it("rejects a close delimiter appearing before any open", () => {
    expect(() => assertSealableLatexPayload({
      construction: "broken \\)x^2\\( tail",
    }, "test payload")).toThrow(/close.*before.*open|before any open/i);
  });

  it("canonicalizes a redundant terminal inline close after a balanced sentence", () => {
    const failedBundleField = "Define \\(\\Phi(a)=(V',E',\\pi'_0,s',y',m')\\).\\)";
    const repaired = repairSerializedLatex(failedBundleField);
    expect(repaired).toBe("Define \\(\\Phi(a)=(V',E',\\pi'_0,s',y',m')\\).");
    expect(repairSerializedLatex(repaired)).toBe(repaired);
    expect(() => assertSealableLatexPayload({ construction: repaired }, "failed bundle replay")).not.toThrow();
  });

  it("does not guess when an unmatched inline close is not a redundant sentence suffix", () => {
    const missingOpener = "The intended relation is x+y\\).";
    expect(repairSerializedLatex(missingOpener)).toBe(missingOpener);
  });

  it("does not consume paired backslashes from an odd terminal run", () => {
    for (const pairedPrefix of ["\\\\", "\\\\\\\\"]) {
      const value = `Define \\(x\\).${pairedPrefix}\\)`;
      expect(repairSerializedLatex(value)).toBe(value);
    }
  });

  it("does not repair a count-balanced but invalid nested inline span", () => {
    const nested = "Nested \\(outer \\(inner\\) tail\\).\\)";
    expect(repairSerializedLatex(nested)).toBe(nested);
    expect(() => assertSealableLatexPayload({ construction: nested }, "nested replay")).toThrow();
  });

  it("does not interpret delimiter examples inside comments or literal regions", () => {
    const comment = "% Preserve the literal example \\(x\\).\\)";
    const verbatim = "\\begin{verbatim}\\(x\\).\\)\\end{verbatim}";
    expect(repairSerializedLatex(comment)).toBe(comment);
    expect(repairSerializedLatex(verbatim)).toBe(verbatim);
    expect(() => assertSealableLatexPayload({ construction: comment }, "comment replay")).not.toThrow();
    expect(() => assertSealableLatexPayload({ construction: verbatim }, "verbatim replay")).not.toThrow();
  });

  it("rejects an unmatched math environment", () => {
    expect(() => assertSealableLatexPayload({
      statement: "We have \\begin{equation}\\tau = 0 and then prose continues.",
    }, "test payload")).toThrow(/environment/);
  });

  it("rejects crossed begin/end environments even when per-name counts balance", () => {
    expect(() => assertSealableLatexPayload({
      proof_tex: "\\begin{aligned}a\\begin{cases}b\\end{aligned}c\\end{cases}",
    }, "test payload")).toThrow(/environment/);
  });

  it("rejects an end-before-begin environment sequence with balanced counts", () => {
    expect(() => assertSealableLatexPayload({
      proof_tex: "x\\end{aligned}y\\begin{aligned}z",
    }, "test payload")).toThrow(/environment/);
  });

  it("accepts matched nested environments", () => {
    expect(() => assertSealableLatexPayload({
      proof_tex: "\\[\\begin{aligned}a &= b \\\\\n c &= d\\end{aligned}\\] and \\begin{cases}1\\\\2\\end{cases}",
    }, "test payload")).not.toThrow();
  });

  it("does not treat literal qquad prose, Unicode adjacency, metadata, or text commands as broken TeX", () => {
    expect(() => assertSealableLatexPayload({
      proof_tex: String.raw`The token qquad is discussed; \(αqquad + qquadβ + αqquadβ + \text{outer {qquad at C:/qquad/file}}\) are literal.`,
      reason: "The token qquad is discussed in /qquad documentation.",
    }, "test payload")).not.toThrow();
  });

  it("accepts CRLF line endings but still rejects a lone CR", () => {
    expect(() => assertSealableLatexPayload({
      verbatim_statement: "line one\r\nline two",
    }, "test payload")).not.toThrow();
    expect(() => assertSealableLatexPayload({
      proof_tex: "a\rho-smooth",
    }, "test payload")).toThrow(/U\+000D/);
  });

  it("rejects decoded control characters via the shared boundary check", () => {
    expect(() => assertSealableLatexPayload({
      construction: "a\theta-smooth class",
    }, "test payload")).toThrow(/control character/);
  });
});

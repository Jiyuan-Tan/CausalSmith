import { describe, expect, it } from "vitest";
import { compactSectionOutline, priorSectionContext, sectionContinuityExcerpt } from "../src/presentation/p2_section_context.js";
import { parseOutline } from "../src/presentation/stage_util.js";

describe("P2 section context", () => {
  it("keeps ordering and exact object IDs without duplicating full notation or section briefs", () => {
    const outline = parseOutline(`# Title\nPaper title\n# Notation\nFull notation secret\n# Sections\n## section: Setup\nDetailed prose brief\nobjs: def:law\nhome_objs: def:old\nbib: ref2026\n## section: Results\nobjs: thm:value\nbib: none`);
    const compact = compactSectionOutline(outline);
    expect(compact).toContain("Paper title");
    expect(compact.indexOf("Section: Setup")).toBeLessThan(compact.indexOf("Section: Results"));
    expect(compact).toContain("def:law");
    expect(compact).toContain("thm:value");
    for (const absent of ["Full notation secret", "Detailed prose brief", "home_objs", "def:old", "ref2026"]) expect(compact).not.toContain(absent);
  });

  it("preserves a complete link ledger and targeted paths without copying old prose or statements", () => {
    const context = priorSectionContext([
      { name: "Setup", objs: ["def:law"], path: "/bundle/sections/01_setup.tex", tex: String.raw`\section{Setup}
Old paragraph only in the original source. \leanref{sym:mu}{$\mu$}. \leanref{def:inline}{the inline definition}.
% \leanref{sym:commented}{$q$}
\begin{definitionv}{def:law}[Law]Secret long frozen body.\end{definitionv}` },
      { name: "Appendix A", objs: ["lem:bound"], path: "/bundle/sections/02_appendix_a.tex", tex: String.raw`\section{Appendix A}

\begin{lemmav}{lem:bound}[Bound]Another frozen body.\end{lemmav}

This establishes the bound for \leanref{sym:sigma}{$\sigma$}.` },
    ]);
    for (const expected of ["Setup", "Appendix A", "def:law", "lem:bound", "/bundle/sections/01_setup.tex", "/bundle/sections/02_appendix_a.tex", "def:inline, sym:mu, sym:sigma", "This establishes the bound"]) expect(context).toContain(expected);
    for (const absent of ["Old paragraph only", "Secret long frozen body", "Another frozen body", "sym:commented"]) expect(context).not.toContain(absent);
  });

  it("omits oversized paragraphs without cutting math and retains complete recent paragraphs", () => {
    const tex = `Earlier complete paragraph with $x+y$.\n\nOversized ${"x".repeat(2500)} $z$.\n\nFinal complete paragraph with \\(a+b\\).`;
    const excerpt = sectionContinuityExcerpt(tex);
    expect(excerpt).toBe("Earlier complete paragraph with $x+y$.\n\nFinal complete paragraph with \\(a+b\\).");
    expect(excerpt.length).toBeLessThanOrEqual(2000);
    expect(sectionContinuityExcerpt(tex, 45)).toBe("Final complete paragraph with \\(a+b\\).");
  });

  it("removes nested environments and complete displays without swallowing following prose", () => {
    const tex = String.raw`Before.

\begin{proof}Outer.\begin{proof}Inner.\end{proof}Outer end.\end{proof}

\[x = y

+ z\]

$$a = b$$

After with escaped \$ and \{braces\}.`;
    expect(sectionContinuityExcerpt(tex)).toBe(String.raw`Before.

After with escaped \$ and \{braces\}.`);
  });

  it("omits incomplete math/groups and an unfinished environment tail", () => {
    expect(sectionContinuityExcerpt(String.raw`Valid.

Bad $math.

Bad \(math.

Bad {group.

\begin{definitionv}{def:bad}Unfinished body.`)).toBe("Valid.");
    expect(priorSectionContext([])).toBe("(this is the first section; no prior links)");
  });
});

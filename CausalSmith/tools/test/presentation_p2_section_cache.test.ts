import { describe, it, expect } from "vitest";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  canonicalProofHelperContext, existingProofForP2, proofHelperContextFor, proofObjectCatalog, proofRenderCacheKey, sectionCacheKey, sectionRevisionBrief, frontMatterRevisionBrief,
} from "../src/presentation/stages/p2_draft.js";
import { parseAnchoredEnvs } from "../src/presentation/tex_anchors.js";

describe("sectionCacheKey (P2 content-keyed section cache)", () => {
  const base = () => sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "brief", "k1", "(no review)");

  it("is stable for identical inputs; re-keys when the objs are reordered (safe re-draft)", () => {
    expect(sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "brief", "k1", "(no review)")).toBe(base());
    expect(sectionCacheKey("02_main.tex", ["thm:b", "def:a"], "brief", "k1", "(no review)")).not.toBe(base());
  });
  it("changes when an env is added to / removed from the section (the restructure case)", () => {
    // def:a moved away → this section now has only thm:b → must re-draft.
    expect(sectionCacheKey("02_main.tex", ["thm:b"], "brief", "k1", "(no review)")).not.toBe(base());
  });
  it("changes when the brief, the cites, or the revision brief changes", () => {
    expect(sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "BRIEF2", "k1", "(no review)")).not.toBe(base());
    expect(sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "brief", "k2", "(no review)")).not.toBe(base());
    expect(sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "brief", "k1", "[major] fix wording")).not.toBe(base());
  });
  it("takes NO environment-body input: a re-rendered env swaps into cached prose without a re-draft", () => {
    // The signature itself is the contract — bodies are substituted mechanically at assembly
    // (normalizeFrozenEnvs), so they must not be able to invalidate authored prose.
    expect(sectionCacheKey.length).toBe(5);
  });
});

describe("proofRenderCacheKey", () => {
  const baseParts = () => ({
    modelKey: "model", objId: "thm:main", envTex: "THEOREM", leanPath: "/repo/Main.lean",
    leanDecl: "main", exactDecl: "theorem main : P := by trivial",
    helperContext: [{ obj_id: "lem:b", tex: "B" }, { obj_id: "lem:a", tex: "A" }],
    notation: "NOTATION", revisionBrief: "BRIEF", citedDependencies: "CITED",
    informalDerivation: "DERIVATION",
  });
  it("is invariant under helper presentation-order permutations", () => {
    const parts = baseParts();
    expect(proofRenderCacheKey({ ...parts, helperContext: [...parts.helperContext].reverse() }))
      .toBe(proofRenderCacheKey(parts));
  });
  it("changes for helper body or membership changes", () => {
    const parts = baseParts(), key = proofRenderCacheKey(parts);
    expect(proofRenderCacheKey({ ...parts, helperContext: [{ obj_id: "lem:b", tex: "B2" }, parts.helperContext[1]] })).not.toBe(key);
    expect(proofRenderCacheKey({ ...parts, helperContext: parts.helperContext.slice(1) })).not.toBe(key);
    expect(proofRenderCacheKey({ ...parts, helperContext: [{ obj_id: "lem:c", tex: "B" }, parts.helperContext[1]] })).not.toBe(key);
  });
  it("rejects duplicate helper identities instead of depending on their input order", () => {
    expect(() => canonicalProofHelperContext([{ obj_id: "lem:a", tex: "A" }, { obj_id: "lem:a", tex: "B" }]))
      .toThrow(/duplicate obj_id lem:a/);
  });
  it("changes only the affected theorem identity/body/brief/notation/Lean mapping inputs", () => {
    const parts = baseParts(), key = proofRenderCacheKey(parts);
    for (const changed of [
      { objId: "thm:other" }, { envTex: "THEOREM2" }, { revisionBrief: "BRIEF2" },
      { notation: "NOTATION2" }, { leanPath: "/repo/Other.lean" }, { leanDecl: "main2" },
      { exactDecl: "theorem main : Q := by trivial" }, { citedDependencies: "CITED2" },
      { informalDerivation: "DERIVATION2" },
    ]) expect(proofRenderCacheKey({ ...parts, ...changed })).not.toBe(key);
  });
});

describe("proofHelperContextFor", () => {
  const envs = parseAnchoredEnvs(String.raw`
\begin{theoremv}{thm:prior}[Prior theorem]
Prior theorem body.
\end{theoremv}
\begin{propositionv}{prop:target}[Target proposition]
Target proposition body.
\end{propositionv}
\begin{propositionv}{prop:other}[Other proposition]
Other proposition body.
\end{propositionv}`);
  const envText = new Map(envs.map((e) => [e.obj_id, String.raw`\begin{${e.env}}{${e.obj_id}}${e.title ? `[${e.title}]` : ""}
${e.body}
\end{${e.env}}`]));
  const graphWithDecl = (decl: string) => ({
    qid: "q", specialization: "v1", edges: [{ from: "prop:target", to: "thm:prior", kind: "proof-uses" }],
    nodes: envs.map((e) => ({
      id: e.obj_id, obj_id: e.obj_id, kind: e.env === "theoremv" ? "theorem" : "proposition",
      provenance: "from-note", nl: { statement: e.body, tex_anchor: "", frozen: true },
      lean: { decl_name: e.obj_id === "thm:prior" ? decl : e.obj_id.replace(":", "_"), file: "Basic.lean" },
      review: { status: "matched", passed_hash: null }, proof: { state: "complete", sorry_count: 0 },
    })),
  });

  it("includes recorded dependencies, excludes unrelated bodies, and preserves their catalogue identities", () => {
    const first = proofHelperContextFor(envs, envText, graphWithDecl("prior_v1") as never, "prop:target");
    expect(first.map((e) => e.obj_id)).toEqual(["thm:prior"]);
    const catalog = proofObjectCatalog(envs, graphWithDecl("prior_v1") as never, "prop:target");
    expect(catalog).toContain("prop:other | Other proposition | prop_other");
    expect(catalog).not.toContain("Other proposition body.");
    expect(catalog).not.toContain("prop:target");
    expect(first[0].tex).toContain("% realizes Lean declaration: prior_v1");
    const second = proofHelperContextFor(envs, envText, graphWithDecl("prior_v2") as never, "prop:target");
    expect(canonicalProofHelperContext(second)).not.toBe(canonicalProofHelperContext(first));
  });
  it("adds explicitly referenced helpers and their references without cycling or inventing targets", () => {
    const changed = envs.map(e => ({ ...e, body: e.obj_id === "prop:other"
      ? String.raw`Uses \cref{obj:thm:prior,obj:prop:other,obj:missing}.` : e.body }));
    const graph = { ...graphWithDecl("prior"), edges: [] };
    const selected = proofHelperContextFor(changed, envText, graph as never, "prop:target",
      String.raw`Repair cites \cref{obj:prop:other}. % \cref{obj:ignored}`);
    expect(selected.map(e => e.obj_id)).toEqual(["thm:prior", "prop:other"]);
  });
  it("invalidates renderer provenance when the fallback catalogue changes", () => {
    const parts = { modelKey: "m", objId: "x", envTex: "x", leanPath: "/a", leanDecl: "a",
      exactDecl: "a", helperContext: [], notation: "", revisionBrief: "", citedDependencies: "", informalDerivation: "" };
    expect(proofRenderCacheKey({ ...parts, objectCatalog: "lem:a | A | a" }))
      .not.toBe(proofRenderCacheKey({ ...parts, objectCatalog: "lem:a | A | renamed" }));
  });

});

describe("existing-proof audit candidate", () => {
  it("reuses authored work on a key miss and never calls it a cache hit", async () => {
    const dir = await mkdtemp(join(tmpdir(), "p2-existing-proof-"));
    const path = join(dir, "proof.tex");
    await writeFile(path, "existing proof\n");
    try {
      expect(await existingProofForP2(path, "old", "new")).toEqual({
        text: "existing proof\n", cacheHit: false,
      });
      expect(await existingProofForP2(path, "new", "new")).toEqual({
        text: "existing proof\n", cacheHit: true,
      });
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});

describe("sectionRevisionBrief", () => {
  it("carries the prior draft with the object delta so a changed section is revised, not rewritten", () => {
    const previous = "Hand-edited intro.\n\\begin{theoremv}{T-1}[A]x\\end{theoremv}\n\\begin{definitionv}{D-2}[B]y\\end{definitionv}\n";
    const brief = sectionRevisionBrief(previous, ["T-1", "D-3"]);
    expect(brief).toContain("Objects added to this section: D-3");
    expect(brief).toContain("Objects removed from this section: D-2");
    expect(brief).toContain("Hand-edited intro.");
    expect(brief.endsWith(previous.trim() + "\nEND OF PRIOR DRAFT")).toBe(true);
    const unchanged = sectionRevisionBrief(previous, ["T-1", "D-2"]);
    expect(unchanged).toContain("added to this section: (none)");
    expect(unchanged).toContain("removed from this section: (none)");
  });
});

describe("frontMatterRevisionBrief", () => {
  it("carries the prior front matter verbatim between the revise instruction and a closing line", () => {
    const prior = "\\begin{abstract}Hand-edited.\\end{abstract}\n\\section{Introduction}\\label{sec:intro}Intro.";
    const brief = frontMatterRevisionBrief(prior);
    expect(brief.startsWith("PRIOR DRAFT of the abstract and introduction")).toBe(true);
    expect(brief.endsWith(prior + "\nEND OF PRIOR DRAFT")).toBe(true);
  });
});

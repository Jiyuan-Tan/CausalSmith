import { describe, it, expect } from "vitest";
import { renderMechanicalLayer, routeFinding } from "../src/presentation/p1_loop.js";
import {
  presentedBody,
  routeNotationProblems,
  migrateSynthLedger,
  releaseLeanResolvableSynths,
  safelyFramesUndeliveredRemark,
  undeliveredRemarkBody,
} from "../src/presentation/stages/p1_plan.js";
import {
  paperOrder,
  insertSynths,
  repairDefinitionOrder,
  sectionObjs,
  rewriteOutlineObjs,
  outlineForPlanning,
} from "../src/presentation/p1_order.js";
import { parseOutline } from "../src/presentation/stage_util.js";
import { topoOrder, renderedNodes } from "../src/presentation/graph_view.js";
import { parseAnchoredEnvs, definitionOrderViolations, lintEnvOrder } from "../src/presentation/tex_anchors.js";
import type { FormalizationGraph, GraphNode, GraphEdge } from "../src/graph/types.js";

const node = (id: string, kind: GraphNode["kind"], stmt = `stmt ${id}`): GraphNode => ({
  id, kind, provenance: "from-note",
  nl: { statement: stmt, tex_anchor: "", frozen: true },
  lean: { decl_name: `${id}_decl`, file: "F.lean" },
  review: { status: "matched", passed_hash: null },
  proof: { state: "complete", sorry_count: 0 },
});
const edge = (from: string, to: string): GraphEdge => ({ kind: "statement-uses", from, to, source: "extracted" });
const graph = (nodes: GraphNode[], edges: GraphEdge[] = []): FormalizationGraph =>
  ({ qid: "q", specialization: "v1", nodes, edges });

describe("renderMechanicalLayer", () => {
  it("renders topo-ordered envs by kind, skips setups, body = nl.statement", () => {
    const g = graph(
      [node("a1", "assumption"), node("p7", "definition"), node("s1", "setup"), node("t1", "theorem")],
      [edge("a1", "p7"), edge("t1", "a1")],
    );
    const ordered = topoOrder(g, renderedNodes(g));
    const layer = renderMechanicalLayer(ordered);
    const envs = parseAnchoredEnvs(layer);
    // p7 before a1 (a1 uses p7); a1 before t1 (t1 uses a1); s1 skipped (setup)
    expect(envs.map((e) => e.obj_id)).toEqual(["p7", "a1", "t1"]);
    expect(envs[0].env).toBe("definitionv");
    expect(envs[2].env).toBe("theoremv");
    expect(envs[1].body).toContain("stmt a1");
    expect(layer).not.toContain("{s1}");
  });
});

const mkEnv = (id: string, body: string, env: P1Env["env"] = "definitionv"): P1Env =>
  ({ id, env, statement: body, body, refSet: [] });
const OUTLINE = parseOutline([
  "# Title", "**T.**", "# Notation", "| a | b | c |", "# Sections",
  "## section: Introduction", "brief", "objs: none", "bib: none",
  "## section: Setup", "brief", "objs: def:a, ass:b", "bib: none",
  "## section: Results", "brief", "objs: thm:c", "bib: none",
  "## section: Appendix: proofs", "brief", "objs: def:z", "bib: none",
].join("\n"));
const assembleTex = (envs: readonly P1Env[]) =>
  envs.map((e) => `\\begin{${e.env}}{${e.id}}\n${e.body}\n\\end{${e.env}}`).join("\n");
const depsOf = (...rows: [string, ...string[]][]) => new Map(rows.map(([user, ...homes]) => [user, new Set(homes)]));
const row = (symbol: string, home: string) => `\\(${symbol}\\) | \\(${symbol}\\) | meaning | ${home}`;
// The semantic order check as P1's repair reads it (the violations it would still have to fix).
const lintDefinitionOrder = (tex: string, notation: string) =>
  definitionOrderViolations(tex, notation).map((v) => ({
    gate: "notation-defined-after-use", objId: v.firstUse, detail: `${v.symbol} used in ${v.firstUse} before ${v.home}`,
  }));

describe("p1_order: paper order + synth insertion", () => {
  it("orders graph envs by the outline's sections and objs, ignoring synth ids in the outline", () => {
    const envs = [mkEnv("thm:c", "c"), mkEnv("def:z", "z"), mkEnv("ass:b", "b", "assumptionv"), mkEnv("def:a", "a"), mkEnv("def:unplaced", "u")];
    expect(paperOrder(OUTLINE, envs).map((e) => e.id)).toEqual(["def:a", "ass:b", "thm:c", "def:z", "def:unplaced"]);
  });
  it("inserts each synthesized definition immediately before its first user; no user → end of the setup, reported", () => {
    const graph = [mkEnv("d1", "Setup."), mkEnv("t1", String.raw`Uses \(\mathcal H^\beta\).`, "theoremv")];
    const synth = mkEnv("synth_1", String.raw`Defines \(\mathcal H^\beta\).`);
    const orphan = mkEnv("synth_2", String.raw`Defines \(Z\).`);
    const orphans = new Set<string>();
    const ordered = insertSynths(graph, [synth, orphan], new Map([["synth_1", [String.raw`\mathcal H^\beta`]], ["synth_2", ["Z"]]]), new Map(), orphans);
    // The orphan never leads the paper: it sits after the setup definition, before the first result.
    expect(ordered.map((e) => e.id).indexOf("synth_2")).toBeGreaterThan(ordered.map((e) => e.id).indexOf("d1"));
    expect(ordered.map((e) => e.id).indexOf("synth_2")).toBeLessThan(ordered.map((e) => e.id).indexOf("t1"));
    expect(ordered.map((e) => e.id).indexOf("synth_1")).toBe(ordered.map((e) => e.id).indexOf("t1") - 1);
    expect([...orphans]).toEqual(["synth_2"]);
  });
  it("places a consolidated synth before the earliest use among ALL its symbols, matching titles too", () => {
    const graph = [mkEnv("d1", "Setup."), mkEnv("l1", String.raw`Uses \(B_n\).`, "lemmav"), mkEnv("t1", String.raw`Uses \(A_n\).`, "theoremv")];
    const synth = mkEnv("synth_1", String.raw`Defines \(A_n\) and \(B_n\).`);
    const titles = new Map([["d1", String.raw`Setup for \(A_n\)`]]);
    expect(insertSynths(graph, [synth], new Map([["synth_1", ["A_n", "B_n"]]]), new Map()).map((e) => e.id)).toEqual(["d1", "synth_1", "l1", "t1"]);
    expect(insertSynths(graph, [synth], new Map([["synth_1", ["A_n", "B_n"]]]), titles).map((e) => e.id)).toEqual(["synth_1", "d1", "l1", "t1"]);
  });
  it("orders a synth that consumes another synth's symbol after its provider, without inventing a cycle from a labelled variant", () => {
    const graph = [mkEnv("thm:end", String.raw`Uses \(N_k\) and \(\mathcal A\).`, "theoremv")];
    const synthA = mkEnv("synth_1", String.raw`Define \(\mathcal A\) from \(\mathcal B\).`);
    const synthB = mkEnv("synth_2", String.raw`Define \(\mathcal B\).`);
    const synthN = mkEnv("synth_3", String.raw`Define \(N_k\) from \(M_j\).`);
    const synthM = mkEnv("synth_4", String.raw`Define \(M_j\) from the distinct count \(N_k^{(1)}\).`);
    const symbols = new Map([["synth_1", [String.raw`\mathcal A`]], ["synth_2", [String.raw`\mathcal B`]], ["synth_3", ["N_k"]], ["synth_4", ["M_j"]]]);
    expect(insertSynths(graph, [synthA, synthB, synthN, synthM], symbols, new Map()).map((e) => e.id))
      .toEqual(["synth_4", "synth_3", "synth_2", "synth_1", "thm:end"]);
  });
});

describe("p1_order: definition-order repair (P1 is the only judge of order; later stages assert it)", () => {
  it("does not infer graph prerequisites from local v, indexed ell, or a matrix A in a synth", () => {
    const setup = mkEnv("prop:setup", String.raw`For every \(u,v\), use the stacked array in \cref{obj:synth_1}.`, "propositionv");
    const synth = mkEnv("synth_1", String.raw`Stack a matrix \(A\).`);
    const estimator = mkEnv("def:estimator", String.raw`Evaluate at \(v\) on intervals with endpoints \(\ell_{j,x}\).`);
    const pilot = mkEnv("lem:pilot", String.raw`The bound sums \(\sum_{\ell=0}^h a_\ell\).`, "lemmav");
    const matrix = mkEnv("def:matrix", String.raw`Define the constraint matrix \(A\).`);
    setup.refSet = [estimator.id, pilot.id, matrix.id]; // Allowed citations are not dependencies.
    const envs = [synth, setup, estimator, pilot, matrix];
    expect(repairDefinitionOrder(envs, new Map(), new Map(), new Map()).envs).toEqual(envs);
    const explicit = repairDefinitionOrder(envs, depsOf([setup.id, estimator.id]), new Map(), new Map());
    expect(explicit.envs.map(e => e.id)).toEqual([synth.id, estimator.id, setup.id, pilot.id, matrix.id]);
  });
  it("uses comma-separated paper references but ignores comments, self references and missing targets", () => {
    const user = mkEnv("thm:user", String.raw`Use \Cref{obj:def:b, obj:def:a, obj:thm:user, obj:missing}.
% \cref{obj:def:commented}`, "theoremv");
    const a = mkEnv("def:a", "A.");
    const b = mkEnv("def:b", "B.");
    const commented = mkEnv("def:commented", "C.");
    const { envs, problems } = repairDefinitionOrder([user, a, b, commented], new Map(), new Map(), new Map());
    expect(envs.map(e => e.id)).toEqual([a.id, b.id, user.id, commented.id]);
    expect(problems).toEqual([]); // Missing references remain the separate xref lint's responsibility.
  });
  it("moves a definition home before its first user", () => {
    const envs = [mkEnv("thm:use", String.raw`Uses \(\mathcal A\).`, "theoremv"), mkEnv("def:a", String.raw`Define \(\mathcal A := \{1\}\).`)];
    const { envs: out, problems } = repairDefinitionOrder(envs, depsOf(["thm:use", "def:a"]), new Map(), new Map());
    expect(problems).toEqual([]);
    expect(out.map((e) => e.id)).toEqual(["def:a", "thm:use"]);
  });
  it("moves a synth AFTER the assumption that introduces a symbol it consumes, rather than moving the assumption", () => {
    const envs = [
      mkEnv("synth_1", String.raw`For the model \(\mathcal M\), define \(\mathfrak T\).`),
      mkEnv("ass:m", String.raw`Let \(\mathcal M\) denote the finite model.`, "assumptionv"),
      mkEnv("thm:t", String.raw`Uses \(\mathfrak T\).`, "theoremv"),
    ];
    const { envs: out, problems } = repairDefinitionOrder(envs, depsOf(["synth_1", "ass:m"]), new Map(), new Map([["synth_1", [String.raw`\mathfrak T`]]]));
    expect(problems).toEqual([]);
    expect(out.map((e) => e.id)).toEqual(["ass:m", "synth_1", "thm:t"]);
  });
  it("moves the assumption home earlier when the synth cannot move past its own user", () => {
    const envs = [
      mkEnv("synth_1", String.raw`For the model \(\mathcal M\), define \(\mathfrak T\).`),
      mkEnv("thm:t", String.raw`Uses \(\mathfrak T\).`, "theoremv"),
      mkEnv("ass:m", String.raw`Let \(\mathcal M\) denote the finite model.`, "assumptionv"),
    ];
    const { envs: out, problems } = repairDefinitionOrder(envs, depsOf(["synth_1", "ass:m"]), new Map(), new Map([["synth_1", [String.raw`\mathfrak T`]]]));
    expect(problems).toEqual([]);
    expect(out.map((e) => e.id)).toEqual(["ass:m", "synth_1", "thm:t"]);
  });
  it("never reorders around a theorem referenced by a definition; forward result citations are ordinary", () => {
    const envs = [mkEnv("def:x", String.raw`Uses \(\theta\).`), mkEnv("thm:id", String.raw`\[\theta = E[Y]\]`, "theoremv")];
    const { envs: out, problems } = repairDefinitionOrder(envs, depsOf(["def:x", "thm:id"]), new Map(), new Map());
    expect(out.map((e) => e.id)).toEqual(["def:x", "thm:id"]);
    expect(problems).toEqual([]);
  });
  it("uses the explicitly referenced provider rather than another environment mentioning the same symbol", () => {
    const envs = [
      mkEnv("def:setup", String.raw`Let \(b_0\) denote the target proxy law.`),
      mkEnv("def:fiber", String.raw`Uses \(b_0\).`),
      mkEnv("ass:sample", String.raw`Let \(b_0\) denote the target proxy law induced by sampling.`, "assumptionv"),
    ];
    const { envs: out, problems } = repairDefinitionOrder(envs, depsOf(["def:fiber", "def:setup"]), new Map(), new Map());
    expect(problems).toEqual([]);
    expect(out.map((e) => e.id)).toEqual(["def:setup", "def:fiber", "ass:sample"]);
  });
});

describe("p1_order: section assignment and outline rewrite", () => {
  it("recomputes seven stale section hoists before partitioning the recovered homes", () => {
    const main = ["def:kernel", "def:estimator", "def:embedding"];
    const upper = ["lem:extraction", "lem:convolution", "lem:pilot"];
    const lower = ["def:matching"];
    const homes = [["ass:setup"], main, upper, lower];
    const names = ["Setup", "Main results", "Appendix: Upper bound", "Appendix: Lower bound"];
    const envs = [...main, ...upper, ...lower, "ass:setup"].map(id =>
      mkEnv(id, "Standalone statement.", id.startsWith("lem:") ? "lemmav" : id.startsWith("ass:") ? "assumptionv" : "definitionv"));
    const saved = ["# Title", "T", "# Sections", ...names.flatMap((name, i) => [
      `## section: ${name}`, `objs: ${i === 0 ? envs.map(e => e.id).join(", ") : "none"}`,
      `home_objs: ${homes[i].join(", ")}`,
    ])].join("\n");
    const source = outlineForPlanning(saved);
    const outline = parseOutline(source);
    // Partitioning the old order reproduces the reported seven-object symptom.
    expect(sectionObjs(outline, envs).get("Setup")).toHaveLength(8);
    // P1 rebuilds the order from the recovered plan BEFORE calling the partitioner.
    const ordered = repairDefinitionOrder(insertSynths(paperOrder(outline, envs), [], new Map(), new Map()),
      new Map(), new Map(), new Map()).envs;
    const resolved = sectionObjs(outline, ordered);
    expect([...resolved.values()]).toEqual(homes);
    const persisted = rewriteOutlineObjs(source, resolved, new Map(names.map((name, i) => [name, homes[i]])));
    expect(parseOutline(persisted).sections.map(s => s.objs)).toEqual(homes);
    expect(parseOutline(outlineForPlanning(persisted)).sections.map(s => s.objs)).toEqual(homes);
  });
  it("a synth takes the section of the next graph env; a moved definition takes its user's section; a trailing synth joins its predecessor", () => {
    const ordered = [mkEnv("synth_1", "s1"), mkEnv("def:a", "a"), mkEnv("ass:b", "b", "assumptionv"), mkEnv("synth_2", "s2"), mkEnv("def:z", "z"), mkEnv("thm:c", "c", "theoremv"), mkEnv("synth_3", "s3")];
    const objs = sectionObjs(OUTLINE, ordered);
    expect(objs.get("Introduction")).toEqual([]);
    expect(objs.get("Setup")).toEqual(["synth_1", "def:a", "ass:b"]);
    expect(objs.get("Results")).toEqual(["synth_2", "def:z", "thm:c", "synth_3"]);
    expect(objs.get("Appendix: proofs")).toEqual([]);
  });
  it("returns hoisted definitions and assumptions to their planned homes when uses disappear across re-entries", () => {
    const md = ["# Title", "T", "# Notation", "# Sections",
      "## section: Setup", "setup brief", "objs: ass:setup", "bib: none",
      "## section: Results", "result brief", "objs: thm:main", "bib: none",
      "## section: Appendix", "analytic brief", "objs: def:a, ass:b", "bib: none"].join("\n");
    const notation = [row(String.raw`\mathcal A`, "def:a"), row(String.raw`\mathcal B`, "ass:b")].join("\n");
    const solve = (saved: string, setup: string) => {
      const source = outlineForPlanning(saved);
      const outline = parseOutline(source);
      const envs = [mkEnv("ass:setup", setup, "assumptionv"), mkEnv("thm:main", "Conclusion.", "theoremv"),
        mkEnv("def:a", String.raw`Define \(\mathcal A := \{1\}\).`),
        mkEnv("ass:b", String.raw`Define \(\mathcal B := \{2\}\).`, "assumptionv")];
      const repaired = repairDefinitionOrder(paperOrder(outline, envs), new Map(), new Map(), new Map());
      expect(repaired.problems).toEqual([]);
      return rewriteOutlineObjs(source, sectionObjs(outline, repaired.envs),
        new Map(outline.sections.map(s => [s.name, s.objs])));
    };
    const hoisted = solve(md, String.raw`Uses \cref{obj:def:a,obj:ass:b}.`);
    expect(parseOutline(hoisted).sections[0].objs).toEqual(["def:a", "ass:b", "ass:setup"]);
    expect(parseOutline(hoisted).sections[2].homeObjs).toEqual(["def:a", "ass:b"]);
    const partial = solve(hoisted, String.raw`Uses \cref{obj:ass:b}.`);
    expect(parseOutline(partial).sections[0].objs).toEqual(["ass:b", "ass:setup"]);
    expect(parseOutline(partial).sections[2].objs).toEqual(["def:a"]);
    const restored = solve(partial, "Setup.");
    expect(parseOutline(restored).sections.map(s => s.objs)).toEqual([["ass:setup"], ["thm:main"], ["def:a", "ass:b"]]);
    expect(solve(restored, "Setup.")).toBe(restored);
    expect(solve(restored, String.raw`Uses \cref{obj:def:a,obj:ass:b}.`)).toBe(hoisted);
    expect(parseOutline(restored).sections.map(s => s.brief)).toEqual(["setup brief", "result brief", "analytic brief"]);
    expect(outlineForPlanning(restored)).not.toContain("home_objs:");
  });
  it("honors explicit edits to planned homes and preserves legacy outlines without home metadata", () => {
    const md = "# Title\nT\n# Sections\n## section: Setup\nobjs: def:a, thm:x\nhome_objs: thm:x\n## section: Appendix\nobjs: none\nhome_objs: def:a\n";
    expect(parseOutline(outlineForPlanning(md)).sections.map(s => s.objs)).toEqual([["thm:x"], ["def:a"]]);
    const edited = md.replace("home_objs: thm:x", "home_objs: def:a, thm:x").replace("home_objs: def:a\n", "home_objs: none\n");
    expect(parseOutline(outlineForPlanning(edited)).sections.map(s => s.objs)).toEqual([["def:a", "thm:x"], []]);
    const legacy = "# Title\nT\n# Sections\n## section: Setup\nobjs: def:a, thm:x\n";
    expect(outlineForPlanning(legacy)).toBe(legacy);
  });
  it("rewrites every objs line from the assignment and preserves everything else byte-for-byte", () => {
    const md = ["# Title", "**T.**", "# Notation", "| a | b | c |", "# Sections",
      "## section: Introduction", "brief", "objs: none", "bib: k1",
      "## section: Setup", "brief line", "objs: def:a, ass:b", "bib: k2",
      "## section: Results", "brief", "bib: k3"].join("\n");
    const out = rewriteOutlineObjs(md, new Map([["Setup", ["synth_1", "def:a", "ass:b"]], ["Results", ["thm:c"]]]));
    const o = parseOutline(out);
    expect(o.sections.map((s) => s.objs)).toEqual([[], ["synth_1", "def:a", "ass:b"], ["thm:c"]]);
    expect(o.sections.map((s) => s.bib)).toEqual([["k1"], ["k2"], ["k3"]]);
    expect(out).toContain("brief line");
    expect(out.split("\n").filter((l) => l.startsWith("objs:"))).toHaveLength(3);
  });
});

describe("migrateSynthLedger (pre-v2 p1_cache.json)", () => {
  it("carries accepted ledger definitions into synthEnvs with their ids and drops the ledger", () => {
    const cache = {
      synth: {
        "\\mathcal E": { symbol: "\\mathcal E", accepted: true, id: "synth_3", title: "State spaces", body: "The spaces …" },
        "\\mathcal U": { symbol: "\\mathcal U", accepted: true, id: "synth_3", title: "State spaces", body: "The spaces …" },
        "K_n": { symbol: "K_n", accepted: false },
      },
      synthRetries: { K_n: 1 },
    } as { synth: Record<string, unknown>; synthEnvs?: Record<string, { symbols: string[]; title?: string; body: string }>; synthRetries?: unknown };
    migrateSynthLedger(cache);
    expect(cache.synthEnvs).toEqual({ synth_3: { symbols: ["\\mathcal E", "\\mathcal U"], title: "State spaces", body: "The spaces …" } });
    expect(cache.synth).toEqual({});
    expect("synthRetries" in cache).toBe(false);
  });
  it("leaves a v2 cache untouched", () => {
    const cache = { synth: { k: { groups: [], ids: [] } }, synthEnvs: { synth_1: { symbols: ["x"], body: "b" } } };
    migrateSynthLedger(cache);
    expect(cache.synth).toEqual({ k: { groups: [], ids: [] } });
  });
});

describe("releaseLeanResolvableSynths (Lean-first re-synthesis of cached prose definitions)", () => {
  it("drops presentation-only definitions whose symbols the Lean defines, and the calls that made them", () => {
    const cache = {
      synth: {
        k1: { groups: [], ids: ["synth_1", null] },
        k2: { groups: [], ids: ["synth_2"] },
      },
      synthEnvs: {
        synth_1: { symbols: ["\\operatorname{summaryRadius}"], body: "prose" },
        synth_2: { symbols: ["\\mathcal H"], body: "prose" },
        synth_3: { symbols: ["\\kappa"], body: "from Lean", lean: { decl: "JacksonTuning", file: "E.lean" } },
      },
    };
    const released = releaseLeanResolvableSynths(cache, (symbols) => symbols.includes("\\operatorname{summaryRadius}") || symbols.includes("\\kappa"));
    expect(released).toEqual(["synth_1"]);
    expect(Object.keys(cache.synthEnvs)).toEqual(["synth_2", "synth_3"]); // a linked definition is never released
    expect(Object.keys(cache.synth)).toEqual(["k2"]);
  });
});

describe("routeNotationProblems (order-blind: define it, or fix the use)", () => {
  const base = { knownIds: new Set(["thm:a", "def:b"]) };
  it("routes grouped symbols individually to existing providers or new definitions", () => {
    const result = routeNotationProblems([{ symbol: "a, b", case: "undefined", used_in: ["thm:x"], fix: "Give their meanings." }], {
      knownIds: new Set(["thm:x", "def:a"]), definitionFor: (symbol) => symbol === "a" ? "def:a" : undefined,
    });
    expect(result).toMatchObject([
      { symbol: "a", objId: "def:a", fixLocus: "wording-revise", usedIn: ["thm:x"] },
      { symbol: "b", fixLocus: "synthesize-def", usedIn: ["thm:x"] },
    ]);
    expect(result.every((f) => f.detail.includes("Give their meanings."))).toBe(true);
  });

  it("accepts environment ids in the paper's cited form (obj: prefix) as the layer's bare ids", () => {
    const out = routeNotationProblems([{ symbol: "D_z", case: "undefined", used_in: ["obj:thm:a", "thm:a"], fix: "Define it." }], base);
    expect(out).toMatchObject([{ symbol: "D_z", fixLocus: "synthesize-def", usedIn: ["thm:a"] }]);
  });

  it("routes undefined to synthesis", () => {
    const out = routeNotationProblems(
      [{ symbol: "\\mathcal H", case: "undefined", used_in: ["thm:a"], fix: "add a definition" }], base);
    expect(out).toMatchObject([{ gate: "notation-reviewer", fixLocus: "synthesize-def", symbol: "\\mathcal H" }]);
  });
  it("rejects an undefined symbol with no attributable using environment", () => {
    for (const kase of ["undefined", "no-anchor"] as const) {
      const out = routeNotationProblems([{ symbol: "w_k", case: kase, used_in: [], fix: "remove" }], base);
      expect(out).toMatchObject([{ gate: "notation-reviewer", symbol: "w_k", fixLocus: "halt" }]);
    }
  });
  it("halts loud on symbol-less problems and target-less wrong-refs instead of dropping them", () => {
    const out = routeNotationProblems(
      [{ case: "undefined", fix: "who knows" }, { symbol: "X", case: "wrong-ref", used_in: [] }], base);
    expect(out).toMatchObject([{ fixLocus: "halt" }, { fixLocus: "halt", symbol: "X" }]);
  });
  it("repairs every using environment, including a previously approved body", () => {
    const out = routeNotationProblems(
      [{ symbol: "\\mathcal H", case: "wrong-ref", used_in: ["thm:a", "def:b"] }], base);
    expect(out).toMatchObject([{ objId: "thm:a", fixLocus: "wording-revise" }, { objId: "def:b", fixLocus: "wording-revise" }]);
    const locked = routeNotationProblems(
      [{ symbol: "\\mathcal H", case: "mismatch", used_in: ["def:b"] }], base);
    expect(locked).toMatchObject([{ objId: "def:b", fixLocus: "wording-revise", symbol: "\\mathcal H" }]);
  });
  it("halts on an unrecognized case", () => {
    const out = routeNotationProblems([{ symbol: "X", case: "surprise" }], base);
    expect(out).toMatchObject([{ fixLocus: "halt", symbol: "X" }]);
  });
});

describe("undelivered presentation boundary", () => {
  it("uses a natural varied open-direction fallback rather than legalistic boilerplate", () => {
    const body = undeliveredRemarkBody("The exact atlas covers every real boundary branch", "the CAD substrate is secondary");
    expect(safelyFramesUndeliveredRemark(body)).toBe(true);
    expect(body).not.toContain("does not establish, prove, or deliver");
    expect(body).not.toContain("nevertheless");
    expect(body).not.toContain("Theorem");
  });

  it("keeps distinct safe agent paraphrases instead of replacing them with one template", () => {
    const a = "A natural next question is whether the exceptional locus admits a finite real stratification; resolving the boundary branches is left for future work.";
    const b = "It remains open whether every feasible fiber has the proposed atlas, and understanding the elimination boundary is a worthwhile direction for future research.";
    expect(undeliveredRemarkBody("claim A", "reason A", a)).toBe(a);
    expect(undeliveredRemarkBody("claim B", "reason B", b)).toBe(b);
  });

  it("rejects a disclaimer that later asserts the undelivered claim as a theorem", () => {
    const unsafe = "A natural open question is whether the atlas exists. Nevertheless, Theorem 7 proves that the atlas exists.";
    const framed = undeliveredRemarkBody("the atlas exists", "the boundary analysis is incomplete", unsafe);
    expect(framed).not.toBe(unsafe);
    expect(safelyFramesUndeliveredRemark(framed)).toBe(true);
  });

  it("rejects an open-question preface followed by an assertive reversal", () => {
    const unsafe = "It remains open whether the atlas exists. In fact, the atlas exists on every boundary branch.";
    expect(safelyFramesUndeliveredRemark(unsafe)).toBe(false);
  });

  it("final emission prefers the safe loop remark over a stale frozen theorem body", () => {
    expect(presentedBody("undelivered", "OLD THEOREM ASSERTION", "safe disclosed remark")).toBe("safe disclosed remark");
    expect(presentedBody("deliver", "validated theorem body", "new draft")).toBe("validated theorem body");
  });
});

describe("routeFinding (deterministic fix_locus)", () => {
  it("routes wording gates to the reviser", () => {
    for (const g of ["lean-identifier", "formalization-leak", "xref-dangling", "xref-missing", "xref-missing-assumption", "faithfulness", "objid-in-prose", "assumption-numbering", "bare-ref", "lean-drift"]) {
      expect(routeFinding(g)).toBe("wording-revise");
    }
  });
  it("routes the statement-presentation floor gates to the reviser (re-render, not halt)", () => {
    // Regression: `lintHypothesisPresentation` emits these and its docstring promises a RE-RENDER,
    // but they were absent from WORDING_GATES, so the router halted P1 on the first hypothesis-heavy
    // theorem instead of itemizing it. (Real incident: thm:margin-localization et al.)
    expect(routeFinding("hypothesis-not-itemized")).toBe("wording-revise");
    expect(routeFinding("hypothesis-restated")).toBe("wording-revise");
  });
  it("routes undefined-assumption to wording; synthesis needs an explicit reviewer fix_locus", () => {
    expect(routeFinding("undefined-assumption")).toBe("wording-revise");
    // The deterministic orphan-class gate was retired: no gate name routes to
    // synthesize-def by itself any more.
    expect(routeFinding("notation-undefined")).toBe("halt");
  });
  it("halts on structural / unrecognized gates", () => {
    for (const g of ["unknown-objid", "env-set-changed", "bare-env", "not-frozen", "mystery"]) {
      expect(routeFinding(g)).toBe("halt");
    }
  });
});

import { atomicRequestedNotationSymbols, runP1Loop, type P1Env, type P1Finding, type P1LoopHooks } from "../src/presentation/p1_loop.js";

const env = (id: string, refSet: string[] = []): P1Env =>
  ({ id, env: "theoremv", statement: `stmt ${id}`, body: `stmt ${id}`, refSet });

// Build hooks whose `review` returns a scripted finding list per call.
const hooks = (reviews: P1Finding[][], extra: Partial<P1LoopHooks> = {}): P1LoopHooks => {
  let call = 0;
  return {
    render: async (reqs) => new Map(reqs.map((r) => [r.id, `rendered ${r.id}${r.defects ? " (fixed)" : ""}`])),
    review: async () => reviews[Math.min(call++, reviews.length - 1)] ?? [],
    synthesize: async (syms) => ({ envs: syms.map((s) => env(`def_${s}`)), unresolved: [] }),
    assemble: (envs) => envs.map((e) => `\\begin{${e.env}}{${e.id}}\n${e.body}\n\\end{${e.env}}`).join("\n"),
    maxIterations: 4,
    ...extra,
  };
};

describe("runP1Loop (executor→reviewer→router control flow)", () => {
  it("renders only `renderIds` in round 0; an already-authored env keeps its body", async () => {
    const rendered: string[][] = [];
    const h = hooks([[]]);
    const render = h.render;
    h.render = async (reqs) => { rendered.push(reqs.map((r) => r.id)); return render(reqs); };
    const authored = { ...env("synth_1"), body: "AUTHORED DEFINITION" };
    const r = await runP1Loop([authored, env("t1")], h, { renderIds: ["t1"] });
    expect(r.ok).toBe(true);
    expect(rendered).toEqual([["t1"]]);
    expect(r.envs.find((e) => e.id === "synth_1")?.body).toBe("AUTHORED DEFINITION");
    expect(r.envs.find((e) => e.id === "t1")?.body).toBe("rendered t1");
  });

  it("a declined symbol stays blocking without repeating synthesis", async () => {
    const calls: string[][] = [];
    const r = await runP1Loop([env("t1")], hooks([
      [{ gate: "notation-reviewer", symbol: "X", fixLocus: "synthesize-def", detail: "X undefined" }],
      [{ gate: "notation-reviewer", symbol: "X", fixLocus: "synthesize-def", detail: "X undefined" }],
    ], { synthesize: async (symbols) => { calls.push(symbols); return { envs: [], unresolved: symbols }; } }));
    expect(calls).toEqual([["X"]]);
    expect(r.ok).toBe(false);
    expect(r.unresolved).toMatchObject([{ gate: "notation-unresolved", symbol: "X" }]);
  });

  it("renders all then exits clean when the reviewer is happy", async () => {
    const r = await runP1Loop([env("t1"), env("a1")], hooks([[]]));
    expect(r.ok).toBe(true);
    expect(r.iterations).toBe(1);
    expect(r.envs.find((e) => e.id === "t1")?.body).toBe("rendered t1");
  });

  it("routes a wording finding to a re-render, then converges", async () => {
    const r = await runP1Loop([env("a1")], hooks([
      [{ gate: "lean-identifier", objId: "a1", detail: "raw decl name" }],
      [],
    ]));
    expect(r.ok).toBe(true);
    expect(r.envs[0].body).toContain("(fixed)"); // re-rendered with defects
  });

  it("replaces a re-rendered existing definition in place instead of duplicating it", async () => {
    const r = await runP1Loop([env("t1"), { ...env("def_X"), body: "old" }], hooks([
      [{ gate: "notation-reviewer", symbol: "Y", fixLocus: "synthesize-def", detail: "Y undefined" }],
      [],
    ], { synthesize: async () => ({ envs: [{ ...env("def_X"), body: "X and Y" }], unresolved: [] }) }));
    expect(r.ok).toBe(true);
    expect(r.envs.map((e) => [e.id, e.body])).toEqual([["t1", "rendered t1"], ["def_X", "X and Y"]]);
  });

  it("adds synthesized definitions to the env set (the stage orders the layer)", async () => {
    const r = await runP1Loop([env("t1")], hooks([
      [{ gate: "notation-reviewer", symbol: "X", fixLocus: "synthesize-def", detail: "X undefined" }],
      [],
    ]));
    expect(r.ok).toBe(true);
    expect(r.envs.map((e) => e.id).sort()).toEqual(["def_X", "t1"]);
  });

  it("splits combined reviewer symbols into atomic synthesis requests", async () => {
    expect(atomicRequestedNotationSymbols(String.raw`\(m_1(h_n)\) and \(m_2(h_n)\)`))
      .toEqual([String.raw`m_1(h_n)`, String.raw`m_2(h_n)`]);
    expect(atomicRequestedNotationSymbols(String.raw`K(x,z), L(x)`))
      .toEqual([String.raw`K(x,z)`, String.raw`L(x)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(m_1(h_n),m_2(h_n)\) and \(m_3(h_n)\)`))
      .toEqual([String.raw`m_1(h_n)`, String.raw`m_2(h_n)`, String.raw`m_3(h_n)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(K(x,z),L(x)\), \(M(x)\)`))
      .toEqual([String.raw`K(x,z)`, String.raw`L(x)`, String.raw`M(x)`]);
    expect(atomicRequestedNotationSymbols(String.raw`m_1(h_n), \(m_2(h_n)\)`))
      .toEqual([String.raw`m_1(h_n)`, String.raw`m_2(h_n)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(m_1(h_n)\), m_2(h_n)`))
      .toEqual([String.raw`m_1(h_n)`, String.raw`m_2(h_n)`]);
    expect(atomicRequestedNotationSymbols(String.raw`K(x,z), \(L(x)\)`))
      .toEqual([String.raw`K(x,z)`, String.raw`L(x)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(m_1(h_n)\;,\;m_2(h_n)\)`))
      .toEqual([String.raw`m_1(h_n)`, String.raw`m_2(h_n)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(K\;(x,z),L(x)\)`))
      .toEqual([String.raw`K\;(x,z)`, String.raw`L(x)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(K\,(x,z),L(x)\)`))
      .toEqual([String.raw`K\,(x,z)`, String.raw`L(x)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(m_1(h)\,,\,m_2(h)\)`))
      .toEqual([String.raw`m_1(h)`, String.raw`m_2(h)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(m_1(h_n)\;\text{and}\;m_2(h_n)\)`))
      .toEqual([String.raw`m_1(h_n)`, String.raw`m_2(h_n)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(A\quad and\quad B\)`))
      .toEqual(["A", "B"]);
    expect(atomicRequestedNotationSymbols(String.raw`\(A\;and\;B\)`))
      .toEqual(["A", "B"]);
    expect(atomicRequestedNotationSymbols(String.raw`A; B`)).toEqual(["A", "B"]);
    expect(atomicRequestedNotationSymbols(String.raw`F_{A and B,C}, G(x)`))
      .toEqual([String.raw`F_{A and B,C}`, "G(x)"]);
    expect(atomicRequestedNotationSymbols(String.raw`K(A\quad and\quad B,z); L(x)`))
      .toEqual([String.raw`K(A\quad and\quad B,z)`, "L(x)"]);
    const calls: string[][] = [];
    const paired: P1Env = { id: "pair", env: "definitionv", statement: "pair",
      body: String.raw`\[m_1(h):=1,\quad m_2(h):=2\]`, refSet: [] };
    const r = await runP1Loop([env("t1")], hooks([
      [{ gate: "notation-reviewer", symbol: String.raw`\(m_1(h_n)\) and \(m_2(h_n)\)`, fixLocus: "synthesize-def", detail: "moments undefined" }],
      [],
    ], { synthesize: async (symbols) => { calls.push(symbols); return { envs: [paired], unresolved: [] }; } }));
    expect(calls).toEqual([[String.raw`m_1(h_n)`, String.raw`m_2(h_n)`]]);
    expect(r.ok).toBe(true);
    expect(r.envs.filter((e) => e.id === "pair")).toHaveLength(1);
  });

  it("persists separate atomic synthesis outputs through the next review round", async () => {
    const r = await runP1Loop([env("t1")], hooks([
      [
        { gate: "notation-reviewer", symbol: String.raw`m_1(h_n)`, fixLocus: "synthesize-def", detail: "first undefined" },
        { gate: "notation-reviewer", symbol: String.raw`m_2(h_n)`, fixLocus: "synthesize-def", detail: "second undefined" },
      ],
      [],
    ], { synthesize: async (symbols) => ({ envs: symbols.map((symbol, i) => ({
      id: `moment_${i}`, env: "definitionv", statement: symbol,
      body: `We define \\(${symbol}:=0\\).`, refSet: [],
    })), unresolved: [] }) }));
    expect(r.ok).toBe(true);
    expect(r.envs.map((e) => e.id).sort()).toEqual(["moment_0", "moment_1", "t1"]);
  });

  it("does not certify unresolved notation even when synthesis was already attempted", async () => {
    let synthCalled = false;
    const r = await runP1Loop([env("a1")], hooks([
      [{ gate: "notation-unresolved", symbol: "\\mathcal H", detail: "synthesis already attempted once" }],
    ], { synthesize: async () => { synthCalled = true; return { envs: [], unresolved: [] }; } }));
    expect(r.ok).toBe(false);
    expect(synthCalled).toBe(false);
    expect(r.unresolved.some((f) => f.gate === "notation-unresolved")).toBe(true);
  });

  it("halts on a structural finding", async () => {
    const r = await runP1Loop([env("a1")], hooks([
      [{ gate: "unknown-objid", objId: "a1", detail: "not in graph" }],
    ]));
    expect(r.ok).toBe(false);
    expect(r.unresolved[0].gate).toBe("unknown-objid");
  });

  it("treats xref-missing as advisory (non-blocking)", async () => {
    const r = await runP1Loop([env("a1", ["p7"])], hooks([
      [{ gate: "xref-missing", objId: "a1", detail: "missing p7" }],
    ]));
    expect(r.ok).toBe(true);
    expect(r.advisories[0].gate).toBe("xref-missing");
  });

  it("halts on unresolved semantic notation-reviewer findings", async () => {
    const r = await runP1Loop([env("a1")], hooks([
      [{ gate: "notation-reviewer", symbol: "\\operatorname{Cum}", detail: "named operator is undefined" }],
    ]));
    expect(r.ok).toBe(false);
    expect(r.unresolved[0].gate).toBe("notation-reviewer");
    expect(r.advisories.some((a) => a.gate === "notation-reviewer")).toBe(false);
  });

  it("ENFORCES xref-missing-assumption (blocks → re-renders, not advisory)", async () => {
    // round 0 flags the unreferenced assumption hypothesis; the re-render clears it on round 1.
    const r = await runP1Loop([env("thm:a", ["ass:foo"])], hooks([
      [{ gate: "xref-missing-assumption", objId: "thm:a", detail: "depends on ass:foo, never \\ref'd" }],
      [],
    ]));
    expect(r.ok).toBe(true);
    // it went through the actionable (re-render) path, NOT collected as a non-blocking advisory.
    expect(r.advisories.some((a) => a.gate === "xref-missing-assumption")).toBe(false);
  });

  it("fast-exits on a persistent identical finding instead of burning the iteration cap", async () => {
    const r = await runP1Loop([env("a1")], hooks([
      [{ gate: "lean-identifier", objId: "a1", detail: "persists" }],
    ]));
    expect(r.ok).toBe(false);
    // Round 1 flags it, the repair re-renders, round 2 sees the identical actionable
    // set and exits with the findings — re-paying rounds 3..cap cannot change anything.
    expect(r.iterations).toBe(2);
    expect(r.unresolved.map((f) => f.objId)).toEqual(["a1"]);
  });
});

// Mangled-word guard: the 2026-08-20 operator risk→u rename class.
import { lintClarity } from "../src/presentation/tex_anchors.js";
describe("lintClarity mangled-word guard", () => {
  const wrap = (body: string) =>
    `\\begin{theoremv}{thm:x}[T]\n${body}\n\\end{theoremv}`;
  it("flags a bare single-letter word in prose", () => {
    const hits = lintClarity(wrap("\\textbf{(ACE fixed-code u.)} If the law is nonempty, then \\(x\\ge0\\)."));
    expect(hits.some((p) => p.gate === "mangled-word" && p.detail.includes('"u"'))).toBe(true);
  });
  it("ignores articles, list markers, math, refs, and macros", () => {
    const hits = lintClarity(wrap(
      "A bound holds; I state it. (b) For a value \\(u\\) with $v>0$, see \\cref{obj:def:x}. The rate is 5\\% by \\emph{design}.",
    ));
    expect(hits.filter((p) => p.gate === "mangled-word")).toEqual([]);
  });
});

describe("audit follow-ups (P1 v2)", () => {
  it("an existential binder no longer counts as introducing a symbol for the order check", async () => {
    const tex = [
      String.raw`\begin{theoremv}{thm:exist}There exists a constant \(C_0\) such that the bound holds.\end{theoremv}`,
      String.raw`\begin{lemmav}{lem:use}The claim holds with the constant \(C_0\).\end{lemmav}`,
      String.raw`\begin{definitionv}{def:c}Define \(C_0 := 42\).\end{definitionv}`,
    ].join("\n");
    expect(lintDefinitionOrder(tex, String.raw`\(C_0\) | \(C_0\) | constant | def:c`)).toMatchObject([{ objId: "lem:use" }]);
  });
  it("introducesNotation accepts whole-atom and defining-LHS clauses and rejects RHS / sub-atom mentions", async () => {
    const { introducesNotation } = await import("../src/presentation/tex_anchors.js");
    expect(introducesNotation(String.raw`Let \(b\) denote the target proxy law.`, "b")).toBe(true);
    expect(introducesNotation(String.raw`We define \(A(x) := B(x)\).`, "A(x)")).toBe(true);
    expect(introducesNotation(String.raw`Denote the observed law by \(P_O\).`, "P_O")).toBe(true);
    expect(introducesNotation(String.raw`We define \(B(x):=A(x)\).`, "A(x)")).toBe(false);
    expect(introducesNotation(String.raw`Let \(x \in \mathcal X\) be a point.`, String.raw`\mathcal X`)).toBe(false);
    expect(introducesNotation(String.raw`Let \(\hat b\) denote the estimate.`, "b")).toBe(false);
    expect(introducesNotation(String.raw`Let \(T_\beta\) be the statistic.`, String.raw`\beta`)).toBe(false);
  });
  it("the loop never holds a synthesized env twice", async () => {
    const dup = env("synth_1");
    const r = await runP1Loop([env("t1")], hooks([
      [{ gate: "notation-reviewer", symbol: "X", fixLocus: "synthesize-def", detail: "X undefined" }],
      [{ gate: "notation-reviewer", symbol: "X", fixLocus: "synthesize-def", detail: "X still undefined (reworded)" }],
      [],
    ], { synthesize: async () => ({ envs: [dup], unresolved: [] }) }));
    expect(r.ok).toBe(true);
    expect(r.envs.filter((e) => e.id === "synth_1")).toHaveLength(1);
  });
  it("an explicit dependency cycle is reported as the concrete pair, not '(several)'", () => {
    const envs = [
      mkEnv("def:a", String.raw`Let \(\mathcal A\) denote the class built from \(\mathcal B\).`),
      mkEnv("def:b", String.raw`Let \(\mathcal B\) denote the class built from \(\mathcal A\).`),
    ];
    const notation = [row(String.raw`\mathcal A`, "def:a"), row(String.raw`\mathcal B`, "def:b")].join("\n");
    const { problems } = repairDefinitionOrder(envs, depsOf(["def:a", "def:b"], ["def:b", "def:a"]), new Map(), new Map());
    expect(problems).toHaveLength(1);
    expect(problems[0]).toMatchObject({ gate: "notation-mutual-definition" });
    expect(problems[0].detail).toMatch(/def:a ↔ def:b: cyclic prerequisites/);
  });
  it("a synth's family stem counts as a use (\\Gamma_{x,y}(M;p) requested, \\Gamma_{x,y}(M';q) used)", () => {
    const graph = [mkEnv("d1", "Setup."), mkEnv("t1", String.raw`Uses \(\Gamma_{x,y}(\mathcal M';q)\).`, "theoremv")];
    const synth = mkEnv("synth_1", String.raw`Define \(\Gamma_{x,y}(\mathcal M;p)\).`);
    const ordered = insertSynths(graph, [synth], new Map([["synth_1", [String.raw`\Gamma_{x,y}(\mathcal M;p)`]]]), new Map());
    expect(ordered.map((e) => e.id)).toEqual(["d1", "synth_1", "t1"]);
  });
  it("P2 re-sequences a section's envs into the outline order without touching prose", async () => {
    const { reorderAnchoredEnvs } = await import("../src/presentation/tex_anchors.js");
    const tex = [
      "Intro prose.",
      String.raw`\begin{theoremv}{thm:t}[T]Uses \(Q\).\end{theoremv}`,
      "Middle prose.",
      String.raw`\begin{definitionv}{def:q}Define \(Q\).\end{definitionv}`,
      "Tail prose.",
    ].join("\n");
    const out = reorderAnchoredEnvs(tex, ["def:q", "thm:t"]);
    expect(out.indexOf("{def:q}")).toBeLessThan(out.indexOf("{thm:t}"));
    expect(out).toContain("Intro prose.\n\\begin{definitionv}{def:q}");
    expect(out).toContain("Middle prose.\n\\begin{theoremv}{thm:t}[T]");
    expect(reorderAnchoredEnvs(out, ["def:q", "thm:t"])).toBe(out);
    expect(reorderAnchoredEnvs(tex, ["def:q"])).toBe(tex); // env sets differ → untouched
  });
});

describe("P2–P4 audit follow-ups touching the shared anchors", () => {
  it("a forward-reference clause ('let C be the constant of \\cref{…}') is not an introduction", async () => {
    const { introducesNotation } = await import("../src/presentation/tex_anchors.js");
    expect(introducesNotation(String.raw`Let \(C_0\) be the constant of \cref{obj:def:c}.`, "C_0")).toBe(false);
    expect(introducesNotation(String.raw`Let \(C_0\) be the constant defined below.`, "C_0")).toBe(true);
    const tex = [
      String.raw`\begin{theoremv}{thm:t}Let \(C_0\) be the constant of \cref{obj:def:c}. Then \(C_0 > 0\).\end{theoremv}`,
      String.raw`\begin{definitionv}{def:c}Define \(C_0 := 42\).\end{definitionv}`,
    ].join("\n");
    expect(lintDefinitionOrder(tex, String.raw`\(C_0\) | \(C_0\) | constant | def:c`)).toMatchObject([{ objId: "thm:t" }]);
  });
  it("a commented-out \\begin line is not an environment for the scanner", async () => {
    const { parseAnchoredEnvs, reorderAnchoredEnvs } = await import("../src/presentation/tex_anchors.js");
    const tex = [
      "% \\begin{theoremv}{thm:old}retired\\end{theoremv}",
      String.raw`\begin{theoremv}{thm:b}B.\end{theoremv}`,
      String.raw`\begin{theoremv}{thm:a}A.\end{theoremv}`,
    ].join("\n");
    expect(parseAnchoredEnvs(tex).map((e) => e.obj_id)).toEqual(["thm:b", "thm:a"]);
    const out = reorderAnchoredEnvs(tex, ["thm:a", "thm:b"]);
    expect(out.split("\n")).toEqual([
      "% \\begin{theoremv}{thm:old}retired\\end{theoremv}",
      String.raw`\begin{theoremv}{thm:a}A.\end{theoremv}`,
      String.raw`\begin{theoremv}{thm:b}B.\end{theoremv}`,
    ]);
  });
});

describe("comment masking in the env scanner (delta audit)", () => {
  it("skips a \\begin after an unescaped mid-line %, but not after an escaped \\%", async () => {
    const { parseAnchoredEnvs } = await import("../src/presentation/tex_anchors.js");
    const tex = [
      String.raw`prose % \begin{theoremv}{thm:dead}gone`,
      String.raw`\begin{theoremv}{thm:a}A.\end{theoremv}`,
      String.raw`50\% \begin{theoremv}{thm:b}B.\end{theoremv}`,
    ].join("\n");
    expect(parseAnchoredEnvs(tex).map((e) => e.obj_id)).toEqual(["thm:a", "thm:b"]);
  });
});

describe("mutual-introduction cycles (live-run follow-up)", () => {
  const notation = [row("Q_x", "def:kernel"), row("b_x", "def:estimator")].join("\n");
  const kernel = mkEnv("def:kernel", String.raw`Define the kernel \(Q_x := \sum_j b_x(j)\).`);
  const estimator = mkEnv("def:estimator", String.raw`Define the estimator \(b_x := Q_x / n\).`);
  it("the constraints of a mutual pair are contradictory and the violated one is reported by the check", () => {
    const tex = assembleTex([kernel, estimator]);
    expect(definitionOrderViolations(tex, notation)).toEqual([{ symbol: "b_x", home: "def:estimator", firstUse: "def:kernel" }]);
    expect(definitionOrderViolations(assembleTex([estimator, kernel]), notation)).toEqual([{ symbol: "Q_x", home: "def:kernel", firstUse: "def:estimator" }]);
  });
  it("an explicit dependency chain is resolved from any starting order", () => {
    const h = mkEnv("def:h", String.raw`Define \(\mathcal S := 1\).`);
    const u = mkEnv("def:u", String.raw`Define \(\mathcal T := \mathcal S + 1\).`);
    const x = mkEnv("def:x", String.raw`Define \(\mathcal X := \mathcal T + 1\).`);
    for (const table of [[row(String.raw`\mathcal S`, "def:h"), row(String.raw`\mathcal T`, "def:u")], [row(String.raw`\mathcal T`, "def:u"), row(String.raw`\mathcal S`, "def:h")]]) {
      for (const input of [[x, u, h], [u, x, h], [x, h, u]]) {
        const { envs: out, problems } = repairDefinitionOrder(input, depsOf(["def:u", "def:h"], ["def:x", "def:u"]), new Map(), new Map());
        expect(problems).toEqual([]);
        expect(out.map((e) => e.id)).toEqual(["def:h", "def:u", "def:x"]);
      }
    }
  });
  it("a one-directional violation inside a larger dependency web is repaired by a move, not tolerated", () => {
    // late uses nothing of user's; the web (kernel ↔ estimator, both used by user) must not glue
    // the pair into a "cycle" — reachability did, and 27 of 28 tolerated pairs on a live bundle
    // were of this kind.
    const late = mkEnv("def:late", String.raw`Define \(\mathcal L := Q_x + 1\).`);
    const user = mkEnv("def:user", String.raw`Define \(\mathcal U := \mathcal L + b_x\).`);
    const table = `${notation}\n${row(String.raw`\mathcal L`, "def:late")}\n${row(String.raw`\mathcal U`, "def:user")}`;
    const { envs: out, problems } = repairDefinitionOrder([kernel, estimator, user, late], depsOf(["def:kernel", "def:estimator"], ["def:estimator", "def:kernel"], ["def:user", "def:late", "def:estimator"], ["def:late", "def:kernel"]), new Map(), new Map());
    expect(out.map((e) => e.id)).toEqual(["def:kernel", "def:estimator", "def:late", "def:user"]);
    expect(problems.map((p) => p.gate)).toEqual(["notation-mutual-definition"]);
  });
  it("a result uses its exact declared provider even when another environment mentions the same symbol", () => {
    const i = mkEnv("lem:i", String.raw`Let \(\mathcal S\) denote the seed; then \(\mathcal T\) is bounded.`, "lemmav");
    const u = mkEnv("def:u", String.raw`Define \(\mathcal T := \mathcal S + 1\).`);
    const h = mkEnv("def:h", String.raw`Define \(\mathcal S := 1\).`);
    const table = [row(String.raw`\mathcal S`, "def:h"), row(String.raw`\mathcal T`, "def:u")].join("\n");
    const { envs: out, problems } = repairDefinitionOrder([i, u, h], depsOf(["lem:i", "def:u"], ["def:u", "def:h"]), new Map(), new Map());
    expect(problems).toEqual([]);
    expect(out.map((e) => e.id)).toEqual(["def:h", "def:u", "lem:i"]);
  });
  it("only the constraint that closes a cycle is left violated; a fixable violation on the same web is still fixed", () => {
    // kernel ↔ estimator is a genuine pair; `late` is needed by `kernel` and sits after it — fixable.
    const late = mkEnv("def:late", String.raw`Define \(\mathcal L := 1\).`);
    const kernelL = mkEnv("def:kernel", String.raw`Define the kernel \(Q_x := \mathcal L \sum_j b_x(j)\).`);
    const table = `${notation}\n${row(String.raw`\mathcal L`, "def:late")}`;
    const { envs: out, problems } = repairDefinitionOrder([kernelL, estimator, late], depsOf(["def:kernel", "def:estimator", "def:late"], ["def:estimator", "def:kernel"]), new Map(), new Map());
    expect(out.map((e) => e.id)).toEqual(["def:late", "def:kernel", "def:estimator"]);
    expect(problems.map((p) => p.gate)).toEqual(["notation-mutual-definition"]);
    expect(problems[0].detail).toMatch(/def:estimator used in def:kernel before def:estimator/);
  });
  it("a longer cycle leaves exactly one constraint violated, as an advisory, never a halt", () => {
    const a = mkEnv("def:a", String.raw`Define \(\mathcal A := \mathcal B + 1\).`);
    const b = mkEnv("def:b", String.raw`Define \(\mathcal B := \mathcal C + 1\).`);
    const c = mkEnv("def:c", String.raw`Define \(\mathcal C := \mathcal A + 1\).`);
    const table = [row(String.raw`\mathcal A`, "def:a"), row(String.raw`\mathcal B`, "def:b"), row(String.raw`\mathcal C`, "def:c")].join("\n");
    const { envs: out, problems } = repairDefinitionOrder([a, b, c], depsOf(["def:a", "def:b"], ["def:b", "def:c"], ["def:c", "def:a"]), new Map(), new Map());
    expect(out.map((e) => e.id)).toEqual(["def:a", "def:c", "def:b"]);
    expect(problems.map((p) => p.gate)).toEqual(["notation-mutual-definition"]);
    expect(definitionOrderViolations(assembleTex(out), table)).toHaveLength(1);
    expect(lintEnvOrder(assembleTex(out), out.map((e) => e.id))).toEqual([]);
  });
  it("P1 keeps the pair in place and reports it once as an advisory, not a halt", () => {
    const { envs: out, problems } = repairDefinitionOrder([kernel, estimator], depsOf(["def:kernel", "def:estimator"], ["def:estimator", "def:kernel"]), new Map(), new Map());
    expect(out.map((e) => e.id)).toEqual(["def:kernel", "def:estimator"]);
    expect(problems).toHaveLength(1);
    expect(problems[0]).toMatchObject({ gate: "notation-mutual-definition" });
    expect(problems[0].detail).toMatch(/def:estimator ↔ def:kernel/);
  });
  it("a genuine (acyclic) violation is still repaired next to a tolerated pair", () => {
    const late = mkEnv("def:late", String.raw`Define \(\mathcal L := 1\).`);
    const user = mkEnv("thm:u", String.raw`Uses \(\mathcal L\).`, "theoremv");
    const { envs: out, problems } = repairDefinitionOrder([kernel, estimator, user, late], depsOf(["def:kernel", "def:estimator"], ["def:estimator", "def:kernel"], ["thm:u", "def:late"]), new Map(), new Map());
    expect(out.map((e) => e.id)).toEqual(["def:kernel", "def:estimator", "def:late", "thm:u"]);
    expect(problems.map((p) => p.gate)).toEqual(["notation-mutual-definition"]);
  });
});

describe("result-env notation homes (live-run follow-up)", () => {
  it("a supporting lemma stays in its planned section despite a main-result dependency", () => {
    const envs = [
      mkEnv("prop:main", String.raw`For the bandwidth \(\eta\) the rate holds.`, "propositionv"),
      mkEnv("lem:conc", String.raw`Let \(\eta := n^{-1/3}\) denote the bandwidth. Then concentration holds.`, "lemmav"),
    ];
    const { envs: out, problems } = repairDefinitionOrder(envs, depsOf(["prop:main", "lem:conc"]), new Map(), new Map());
    expect(problems).toEqual([]);
    expect(out.map((e) => e.id)).toEqual(["prop:main", "lem:conc"]);
  });
  it("a forward reference to a theorem preserves planned result order", async () => {
    const envs = [
      mkEnv("ass:a", String.raw`Assume \(\theta > 0\).`, "assumptionv"),
      mkEnv("thm:id", String.raw`\[\theta = \mathbb E[Y]\]`, "theoremv"),
    ];
    const notation = row(String.raw`\theta`, "thm:id");
    const { envs: out, problems } = repairDefinitionOrder(envs, depsOf(["ass:a", "thm:id"]), new Map(), new Map());
    expect(out.map((e) => e.id)).toEqual(["ass:a", "thm:id"]);
    expect(problems).toEqual([]);
    expect(lintEnvOrder(assembleTex(out), out.map((e) => e.id))).toEqual([]);
  });
});

describe("lintEnvOrder (P3/P4 assert the P1 order instead of re-judging it)", () => {
  const layer = ["def:a", "def:b", "thm:t"];
  it("passes a paper whose frozen envs follow the layer order, ignoring envs outside the layer", () => {
    const tex = assembleTex([mkEnv("def:a", "A"), mkEnv("proof:t", "P", "remarkv"), mkEnv("def:b", "B"), mkEnv("thm:t", "T", "theoremv")]);
    expect(lintEnvOrder(tex, layer)).toEqual([]);
  });
  it("rejects an incomplete ordered subsequence and an empty paper", () => {
    const tex = assembleTex([mkEnv("def:a", "A"), mkEnv("thm:t", "T", "theoremv")]);
    expect(lintEnvOrder(tex, layer)).toMatchObject([{ gate: "frozen-layer-order", objId: "def:b" }]);
    expect(lintEnvOrder("", layer).map(p => p.objId)).toEqual(layer);
  });
  it("names the env that was moved ahead of an earlier one", () => {
    const tex = assembleTex([mkEnv("def:b", "B"), mkEnv("def:a", "A"), mkEnv("thm:t", "T", "theoremv")]);
    expect(lintEnvOrder(tex, layer)).toMatchObject([{ gate: "frozen-layer-order", objId: "def:a" }]);
  });
});


describe("P1 targeted semantic repairs", () => {
  it("translates implementation aliases in place and repairs an existing provider instead of duplicating it", () => {
    const opts = { knownIds: new Set(["thm:a", "synth_1"]), definitionFor: () => "synth_1" };
    expect(routeNotationProblems([{ symbol: "matrixAction", used_in: ["thm:a"], case: "rendering", fix: "Write matrix action." }], opts))
      .toMatchObject([{ objId: "thm:a", fixLocus: "wording-revise" }]);
    expect(routeNotationProblems([{ symbol: "H", used_in: ["thm:a"], case: "undefined", fix: "State the defining equality." }], opts))
      .toMatchObject([{ objId: "synth_1", fixLocus: "wording-revise" }]);
  });

  it("repairs only the challenged cached candidate and forwards synthesis evidence", async () => {
    const renders: string[][] = [];
    let synthesisEvidence: P1Finding[] = [];
    const finding: P1Finding = { gate: "notation-reviewer", symbol: "H", usedIn: ["t1"], fixLocus: "synthesize-def", detail: "Define H with its parameter domain." };
    const h = hooks([
      [{ gate: "notation-reviewer", objId: "t1", fixLocus: "wording-revise", detail: "Replace the implementation alias." }, finding], [],
    ], {
      render: async (rs) => { renders.push(rs.map((r) => r.id)); return new Map(rs.map((r) => [r.id, "REPAIRED"])); },
      synthesize: async (_symbols, evidence) => { synthesisEvidence = evidence; return { envs: [env("synth_1")], unresolved: [] }; },
    });
    const result = await runP1Loop([env("t1"), env("untouched")], h, { renderIds: [] });
    expect(result.ok).toBe(true);
    expect(renders).toEqual([["t1"]]);
    expect(result.envs.find((e) => e.id === "untouched")?.body).toBe(env("untouched").body);
    expect(synthesisEvidence).toEqual([finding]);
  });
});

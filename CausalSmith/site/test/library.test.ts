import { describe, expect, it, vi } from "vitest";
import { existsSync, mkdtempSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  loadLibrary,
  libraryRoot,
  statementHash,
  reviewStatus,
  declArea,
  declPagePath,
  isTier1,
  linkifyStatement,
  firstSentence,
  publicAxioms,
  buildModuleTree,
  displayModulePath,
  displayModuleSegment,
  sourceKind, isHiddenLibraryArea
} from "../src/lib/library.js";

function trackedLeanFiles(root: string): string[] {
  try {
    return execFileSync("git", ["ls-files", "Causalean/**/*.lean"], {
      cwd: root,
      encoding: "utf8",
    })
      .split(/\r?\n/)
      .filter((file) => file && existsSync(join(root, file)));
  } catch (err) {
    const out =
      err && typeof err === "object" && "stdout" in err && typeof err.stdout === "string"
        ? err.stdout
        : "";
    if (!out) throw err;
    return out.split(/\r?\n/).filter((file) => file && existsSync(join(root, file)));
  }
}

function fixtureRoot(opts: { badReviewDecl?: boolean; malformedSidecar?: boolean } = {}): string {
  const root = mkdtempSync(join(tmpdir(), "libsite-"));
  mkdirSync(join(root, "doc", "library_review"), { recursive: true });
  const entries = [
    {
      name: "Causalean.PO.Foo",
      kind: "def",
      module: "Causalean.PO.Basic",
      file: "Causalean/PO/Basic.lean",
      line: 10,
      statement: "ℕ →  ℕ",
      doc: "Adds one.\n\nNote.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      name: "Causalean.Graph.Bar",
      kind: "theorem",
      module: "Causalean.Graph.Basic",
      file: "Causalean/Graph/Basic.lean",
      line: 5,
      statement: "∀ n, Foo n = n + 1",
      doc: null,
      refs: ["Causalean.PO.Foo"],
      axioms: ["sorryAx"],
      usesSorry: true,
    },
    {
      // A structure field whose leaf name is a single letter. A bare `W` in
      // another statement is a bound variable, not a reference to this field.
      name: "Causalean.PO.System.W",
      kind: "def",
      module: "Causalean.PO.Basic",
      file: "Causalean/PO/Basic.lean",
      line: 20,
      statement: "ℝ",
      doc: null,
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      name: "Causalean.Substrate.Temp.helper",
      kind: "def",
      module: "Causalean.Substrate.Temp.Basic",
      file: "Causalean/Substrate/Temp/Basic.lean",
      line: 1,
      statement: "Nat",
      doc: "Temporary study-mode substrate helper.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      name: "Causalean.Tactic.Attr.causalDefsSimps",
      kind: "def",
      module: "Causalean.Tactic.Attr",
      file: "Causalean/Tactic/Attr.lean",
      line: 1,
      statement: "Lean.Name",
      doc: "Proof-automation simp-set registration.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
  ];
  writeFileSync(
    join(root, "doc", "library_index.json"),
    JSON.stringify({
      commit: "abc",
      toolchain: "t",
      entries,
      modules: {
        "Causalean.PO.Basic": "Core PO helpers.",
        "Causalean.Substrate.Temp.Basic": "Temporary study-mode substrate helpers.",
        "Causalean.Tactic.Attr": "Proof-automation attribute registration.",
      },
    }),
  );
  writeFileSync(
    join(root, "doc", "library_review", "PO.json"),
    JSON.stringify({
      // A non-array `reviews` is STRUCTURAL corruption (hard error); a dangling
      // decl name is mere DRIFT (warn-and-drop).
      headline_theorems: [],
      reviews: opts.malformedSidecar
        ? ({} as unknown[])
        : [
            {
              decl: opts.badReviewDecl ? "Causalean.PO.Nope" : "Causalean.PO.Foo",
              statement_hash: statementHash("ℕ → ℕ"),
              reviewed_at_commit: "abc",
              reviewer: "j",
            },
          ],
      flags: [],
    }),
  );
  return root;
}

describe("site library loader", () => {
  it("loads, areas, tiers, statuses", () => {
    const lib = loadLibrary(fixtureRoot());
    const foo = lib.entries.find((e) => e.name === "Causalean.PO.Foo")!;
    expect(declArea(foo)).toBe("PO");
    expect(isTier1(foo, lib.sidecars)).toBe(true);
    expect(reviewStatus(foo, lib.sidecars)).toBe("reviewed");
  });
  it("excludes study-mode substrate declarations and modules from the public Causalean page", () => {
    const lib = loadLibrary(fixtureRoot());
    expect(lib.entries.map((e) => e.name)).not.toContain("Causalean.Substrate.Temp.helper");
    expect(Object.keys(lib.modules)).not.toContain("Causalean.Substrate.Temp.Basic");
  });
  it("excludes proof-automation Tactic declarations and modules from the public Causalean page", () => {
    const lib = loadLibrary(fixtureRoot());
    expect(lib.entries.map((e) => e.name)).not.toContain("Causalean.Tactic.Attr.causalDefsSimps");
    expect(Object.keys(lib.modules)).not.toContain("Causalean.Tactic.Attr");
    expect(lib.entries.map(declArea)).not.toContain("Tactic");
  });
  it("renders the DiscreteID module segment as Discrete ID", () => {
    expect(displayModuleSegment("DiscreteID")).toBe("Discrete ID");
    expect(displayModulePath("ID.DiscreteID")).toBe("ID.Discrete ID");
  });
  it("adds discretionary hyphen breaks to long CamelCase module labels", () => {
    expect(displayModuleSegment("ResidualQuadratic")).toBe(
      "Residual\u00adQuadratic",
    );
    expect(displayModuleSegment("BoundedOutcomeEnvelope")).toBe(
      "Bounded\u00adOutcome\u00adEnvelope",
    );
  });
  it("published library areas have a table intro", () => {
    const lib = loadLibrary(libraryRoot());
    const areas = [...new Set(lib.entries.map(declArea))].sort();
    const missing = areas.filter((area) => !(lib.sidecars[area]?.intro ?? "").trim());
    expect(missing).toEqual([]);
  });
  it("published namespace pages have short descriptions", () => {
    const lib = loadLibrary(libraryRoot());
    const areas = [...new Set(lib.entries.map(declArea))].sort();
    const missing: string[] = [];
    const visit = (area: string, node: ReturnType<typeof buildModuleTree>[number]) => {
      if (node.children.length > 0) {
        const intro =
          lib.sidecars[area]?.namespace_intros?.[node.path] ??
          firstSentence(lib.modules[`Causalean.${area}.${node.path}`] ?? null);
        if (!(intro ?? "").trim()) missing.push(`${area}.${node.path}`);
      }
      node.children.forEach((child) => visit(area, child));
    };
    for (const area of areas) {
      const modules = [
        ...new Set(lib.entries.filter((entry) => declArea(entry) === area).map((entry) => entry.module)),
      ];
      buildModuleTree(area, modules).forEach((node) => visit(area, node));
    }
    expect(missing).toEqual([]);
  });
  it("published review sidecars do not contain stale decl references", () => {
    const root = libraryRoot();
    const lib = loadLibrary(root);
    const names = new Set(lib.entries.map((e) => e.name));
    const reviewDir = join(root, "doc", "library_review");
    const stale: string[] = [];
    const duplicateHeadlines: string[] = [];
    for (const file of readdirSync(reviewDir).filter((f) => f.endsWith(".json"))) {
      // Sidecars of areas hidden from the explorer describe declarations the page never loads.
      if (isHiddenLibraryArea(file.replace(/\.json$/, ""))) continue;
      const sidecar = JSON.parse(readFileSync(join(reviewDir, file), "utf8")) as {
        headline_theorems: string[];
        reviews: { decl: string }[];
        flags: { decl: string }[];
      };
      const seen = new Set<string>();
      for (const decl of sidecar.headline_theorems) {
        if (!names.has(decl)) stale.push(`${file}: headline ${decl}`);
        if (seen.has(decl)) duplicateHeadlines.push(`${file}: ${decl}`);
        seen.add(decl);
      }
      for (const review of sidecar.reviews) {
        if (!names.has(review.decl)) stale.push(`${file}: review ${review.decl}`);
      }
      for (const flag of sidecar.flags) {
        if (!names.has(flag.decl)) stale.push(`${file}: flag ${flag.decl}`);
      }
    }
    expect(stale).toEqual([]);
    expect(duplicateHeadlines).toEqual([]);
  });
  it("published page annotations resolve flagged internal wording", () => {
    const lib = loadLibrary(libraryRoot());
    const entries = new Map(lib.entries.map((entry) => [entry.name, entry]));
    const docsWithoutInternalLabels = [
      "Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.bridge_Dtilde_sq_eq_VD",
      "Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.bridge_VD_pos_iff_Dtilde_sq_pos",
      "Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.bridge_finite_residualized_eq_twfe",
      "Causalean.SCM.Examples.ContinuousBackdoor.cb_backdoor_identified",
      "Causalean.SCM.obsKernel_fixSet_W_rect_integral_eq",
    ];
    for (const name of docsWithoutInternalLabels) {
      const doc = entries.get(name)?.doc ?? "";
      expect(doc, name).not.toMatch(/\b(?:B\d+|G\d+|Helper\s+\d+)\b|reusability check/i);
    }
    for (const entry of lib.entries.filter((entry) => entry.file.startsWith("Causalean/SCM/Do/Rule2Kernel/"))) {
      expect(entry.doc ?? "", entry.name).not.toMatch(/\bHelper\s+\d+\b/);
    }

    const activeFlags = Object.values(lib.sidecars)
      .flatMap((sidecar) => sidecar.flags ?? [])
      .map((flag) => `${flag.decl}: ${flag.note}`);
    expect(
      activeFlags.filter((flag) =>
        /Bxx|Gxxx|reusability check|Helper 3|hdealine|not curated/i.test(flag),
      ),
    ).toEqual([]);
  });
  it("published pages with theorem declarations have a curated theorem card", () => {
    const lib = loadLibrary(libraryRoot());
    const pages = new Map<string, { theorems: number; curatedTheorems: number }>();
    for (const entry of lib.entries) {
      const page = declPagePath(entry, lib);
      const rec = pages.get(page) ?? { theorems: 0, curatedTheorems: 0 };
      if (["theorem", "lemma"].includes(entry.kind)) {
        rec.theorems += 1;
        if (isTier1(entry, lib.sidecars)) rec.curatedTheorems += 1;
      }
      pages.set(page, rec);
    }
    const pagesWithoutCuratedTheorem = [...pages]
      .filter(([, counts]) => counts.theorems > 0 && counts.curatedTheorems === 0)
      .map(([page]) => page)
      .sort();
    expect(pagesWithoutCuratedTheorem).toEqual([]);
  });
  it("published theorem modules have curated theorem anchors", () => {
    const lib = loadLibrary(libraryRoot());
    const modules = new Map<string, { theorems: number; curatedTheorems: number }>();
    for (const entry of lib.entries) {
      if (!["theorem", "lemma"].includes(entry.kind)) continue;
      const rec = modules.get(entry.module) ?? { theorems: 0, curatedTheorems: 0 };
      rec.theorems += 1;
      if (isTier1(entry, lib.sidecars)) rec.curatedTheorems += 1;
      modules.set(entry.module, rec);
    }
    const modulesWithoutCuratedTheorem = [...modules]
      .filter(([, counts]) => counts.theorems > 0 && counts.curatedTheorems === 0)
      .map(([module]) => module)
      .sort();
    expect(modulesWithoutCuratedTheorem).toEqual([]);
  });
  it("publishes the monotone counterfactual bound as an SCM example", () => {
    const lib = loadLibrary(libraryRoot());
    const staleEntries = lib.entries
      .filter(
        (entry) =>
          entry.name.startsWith("Causalean.SCM.ID.Flagship.") ||
          entry.module.startsWith("Causalean.SCM.ID.Flagship.") ||
          entry.file.startsWith("Causalean/SCM/ID/Flagship/"),
      )
      .map((entry) => entry.name)
      .sort();
    const staleSidecarKeys = Object.keys(lib.sidecars.SCM?.namespace_intros ?? {}).filter((path) =>
      path.startsWith("ID.Flagship"),
    );

    expect(staleEntries).toEqual([]);
    expect(staleSidecarKeys).toEqual([]);
    expect(
      lib.entries.some(
        (entry) =>
          entry.name ===
            "Causalean.SCM.Examples.MonotoneCounterfactualBound.monotoneCounterfactualBound" &&
          entry.module === "Causalean.SCM.Examples.MonotoneCounterfactualBound" &&
          entry.file === "Causalean/SCM/Examples/MonotoneCounterfactualBound.lean",
      ),
    ).toBe(true);
  });
  it("does not treat generated native_decide witnesses as public axioms", () => {
    const axioms = [
      "sorryAx",
      "Causalean.Estimation.MinimaxATE.Causal.wSWIGGraph._native.native_decide.ax_1",
      "Causalean.Foo.some_real_axiom",
    ];
    expect(publicAxioms(axioms)).toEqual(["Causalean.Foo.some_real_axiom"]);
  });
  it("published Causalean source files are represented in the library index", () => {
    const root = libraryRoot();
    const lib = loadLibrary(root);
    const leanFiles = trackedLeanFiles(root);
    const entryFiles = new Set(lib.entries.map((entry) => entry.file));
    const moduleFiles = new Set(
      Object.keys(lib.modules).map((module) => `${module.replace(/\./g, "/")}.lean`),
    );
    const missing = leanFiles
      .filter((file) => !isHiddenLibraryArea(file.split("/")[1] ?? ""))
      .filter((file) => !entryFiles.has(file) && !moduleFiles.has(file))
      .sort();

    expect(missing).toEqual([]);
  });
  it("published Stat file modules have short descriptions", () => {
    const lib = loadLibrary(libraryRoot());
    const area = "Stat";
    const modules = [
      ...new Set(lib.entries.filter((entry) => entry.file.startsWith("Causalean/Stat/")).map((entry) => entry.module)),
    ];
    const missing: string[] = [];
    const visit = (node: ReturnType<typeof buildModuleTree>[number]) => {
      const modDoc = node.module ? (lib.modules[node.module] ?? null) : null;
      const nsIntro = lib.sidecars[area]?.namespace_intros?.[node.path] ?? null;
      const brief = firstSentence(modDoc) ?? nsIntro;
      if (node.children.length === 0 && !(brief ?? "").trim()) {
        missing.push(node.module ?? `Causalean.${area}.${node.path}`);
      }
      node.children.forEach(visit);
    };
    buildModuleTree(area, modules).forEach(visit);
    expect(missing.sort()).toEqual([]);
  });
  it("drops a dangling review decl (drift) instead of throwing", () => {
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    try {
      const lib = loadLibrary(fixtureRoot({ badReviewDecl: true }));
      // Drift is tolerated: the stale review is filtered out, site still loads.
      expect(lib.sidecars.PO.reviews).toEqual([]);
      const foo = lib.entries.find((e) => e.name === "Causalean.PO.Foo")!;
      expect(reviewStatus(foo, lib.sidecars)).toBe("unreviewed");
      expect(warn).toHaveBeenCalledWith(expect.stringMatching(/unknown decl: Causalean\.PO\.Nope/));
    } finally {
      warn.mockRestore();
    }
  });
  it("throws on structural sidecar malformation (non-array field)", () => {
    expect(() => loadLibrary(fixtureRoot({ malformedSidecar: true }))).toThrow(/structural/);
  });
  it("linkifies known identifiers by longest match", () => {
    const lib = loadLibrary(fixtureRoot());
    const html = linkifyStatement("∀ n, Foo n = n + 1", lib, "/base");
    expect(html).toContain('href="/base/library/PO#Causalean.PO.Foo"');
    // the bare variable `n` must not be linked
    expect(html).not.toMatch(/<a[^>]*>n<\/a>/);
  });
  it("does not link a bare single-letter bound variable to a same-leaf field", () => {
    const lib = loadLibrary(fixtureRoot());
    const html = linkifyStatement("∀ W, 0 ≤ W", lib, "/base");
    // `W` collides with the field `Causalean.PO.System.W`; it must NOT link.
    expect(html).not.toMatch(/<a[^>]*>W<\/a>/);
    // …but the full name still resolves.
    const full = linkifyStatement("Causalean.PO.System.W", lib, "/base");
    expect(full).toContain('href="/base/library/PO#Causalean.PO.System.W"');
  });
  it("does not link a multi-name binder group member or its body recurrences", () => {
    const lib = loadLibrary(fixtureRoot());
    // `Foo` is a real decl, but here it is a BOUND variable: the first name in
    // the group `{Foo bar : Nat}` (so not immediately before the `:`) and reused
    // in the body. It must not link anywhere — mirrors the residualized regressor
    // `Dtilde` wrongly jumping to `GoodmanBacon.Dtilde`.
    const html = linkifyStatement("∀ {Foo bar : Nat}, bar = Foo", lib, "/base");
    expect(html).not.toMatch(/<a[^>]*>Foo<\/a>/);
    // a genuine reference (not bound here) still links.
    const ref = linkifyStatement("∀ n, Foo n = n", lib, "/base");
    expect(ref).toContain('href="/base/library/PO#Causalean.PO.Foo"');
  });
  it("sourceKind ignores a keyword-shaped word that only starts a docstring line", () => {
    // Regression: `id_sound_discrete`'s docstring reflows onto a line starting
    // "class. This is a *sound sufficient fragment*…" — sourceKind used to scan
    // raw `d.source` (docstring included) for the first line-initial keyword and
    // reported "class" for what is, on the declaration line itself, a theorem.
    const decl = {
      name: "Fixture.foo",
      kind: "theorem",
      module: "Fixture",
      file: "Fixture.lean",
      line: 1,
      statement: "",
      doc: null,
      refs: [],
      axioms: [],
      usesSorry: false,
      source: `/-- Identifies the query within the standard discrete positive model
class. This is a *sound sufficient fragment*, not the full algorithm. -/
theorem foo (x : Nat) : x = x := rfl`,
    };
    expect(sourceKind(decl)).toBe("theorem");
  });
});

// ── NL ↔ Lean crosslink gate ────────────────────────────────────────────────
// Hard gate on website regeneration (npm test runs before astro build, both
// internally and in the public mirror's site workflow): a docstring that
// carries crosslink markup must satisfy the convention IN FULL —
//   - every `(hyp:name)` resolves to a parameter/hypothesis/field row of the
//     structured statement (drift = a binder renamed after annotation);
//   - crosslinks live only in the first paragraph (the NL translation);
//   - `(goal)` / `(step:N)` only on theorems, definitions, instances and
//     inductives (a structure has no conclusion); a `(step:N)` names a clause
//     the page actually numbers;
//   - an annotated THEOREM is completely covered: every hyp-classified row
//     linked, and the conclusion linked via `(goal)`; an annotated DEFINITION
//     covers every explicit parameter and its defined object via `(goal)`;
//   - annotations only on statements the structurer can parse (otherwise the
//     underlines would render inert).
// Unannotated docstrings pass untouched — the gate tightens per migration wave.
describe("NL ↔ Lean crosslink gate", () => {
  it("every annotated docstring satisfies the crosslink convention", async () => {
    const { parseCrosslinks, nlOf } = await import("../src/lib/docmd.js");
    const { findProofStart, isBinderRow } = await import("../src/lib/leanStatement.js");
    const { buildDeclView, numberedTokens } = await import("../src/lib/leanDeclView.js");
    const { naturalLanguageDoc, stripLeadingDoc, sourceKind } = await import("../src/lib/library.js");
    const lib = loadLibrary(libraryRoot());
    const problems: string[] = [];
    for (const d of lib.entries) {
      const doc = naturalLanguageDoc(d);
      if (!doc || !/\]\((?:hyp:|goal\)|step:)/.test(doc)) continue;
      const paras = doc.trim().split(/\n\s*\n/);
      for (const p of paras.slice(1)) {
        if (parseCrosslinks(p).some((s) => s.links)) {
          problems.push(`${d.name}: crosslink markup outside the first paragraph`);
          break;
        }
      }
      const segs = parseCrosslinks(nlOf(doc) ?? "").filter((s) => s.links);
      if (segs.length === 0) continue;
      const all = [...new Set(segs.flatMap((s) => s.links!))];
      const names = all.filter((n) => !n.startsWith("⊢"));
      const steps = all.filter((n) => /^⊢\d+$/.test(n));
      const hasGoal = all.includes("⊢");
      const clauseBearing = d.kind === "theorem" || d.kind === "def" || d.kind === "instance" || d.kind === "inductive";
      if ((hasGoal || steps.length > 0) && !clauseBearing) {
        problems.push(`${d.name}: (goal)/(step:N) crosslink on a ${d.kind}`);
      }
      if (!d.source) {
        problems.push(`${d.name}: annotated but no authored source in the index`);
        continue;
      }
      let sig = stripLeadingDoc(d.source);
      const kind = sourceKind(d);
      if (d.kind === "theorem") {
        const proofStart = findProofStart(sig);
        if (proofStart >= 0) sig = sig.slice(0, proofStart);
      }
      const view = buildDeclView(sig, kind, d.params, d.result);
      if (!view) {
        // A source the index truncated at sourceSliceCap cannot structure —
        // the card falls back to plain (stripped) rendering, so annotations
        // are harmless there. Any OTHER unstructurable annotated statement
        // still fails: its annotations could never highlight anything.
        // An `alias` restates no signature of its own (its binders live on the
        // declaration it points at), so there is nothing to structure; its card
        // renders flat, where the markup is inert — the tools lint agrees.
        const isAlias = /^\s*(?:@\[[^\]]*\]\s*)*(?:protected\s+|private\s+)?alias\s/m.test(sig);
        if (!isAlias && !d.source.includes("… truncated")) {
          problems.push(`${d.name}: annotated but the statement does not structure into rows`);
        }
        continue;
      }
      const rows = [...view.rows, ...(view.fields ?? [])].filter(isBinderRow);
      const declared = new Set(
        rows.flatMap((r) => (r.dataNames ?? r.names).split(/\s+/).filter(Boolean)),
      );
      // Names past a sourceSliceCap truncation cannot be validated — they
      // render as inert spans, which is harmless (mirrors the lint).
      if (!d.source.includes("… truncated")) {
        for (const n of names) {
          if (!declared.has(n)) problems.push(`${d.name}: crosslink name '${n}' not in signature`);
        }
        const tokens = numberedTokens(view);
        for (const t of steps) {
          if (!tokens.has(t)) problems.push(`${d.name}: ${t.replace("⊢", "(step:")}) names a clause the page does not number`);
        }
      }
      const linked = new Set(names);
      // Coverage is judged on AUTHORED binders: rows lifted out of the goal /
      // body by the card builder (`origin: "lifted"`) are part of the clause
      // the `(goal)` link already covers.
      if (d.kind === "theorem") {
        for (const r of rows) {
          if (r.origin !== undefined) continue;
          const rNames = r.names.split(/\s+/).filter(Boolean);
          if (r.chip === "hyp" && !rNames.some((n) => linked.has(n))) {
            problems.push(`${d.name}: hypothesis '${r.names}' has no linked NL phrase`);
          }
        }
        if (!hasGoal) problems.push(`${d.name}: conclusion has no (goal) crosslink`);
      } else if (d.kind === "def" || d.kind === "instance" || d.kind === "inductive") {
        for (const r of view.rows.filter(isBinderRow)) {
          if (r.origin !== undefined || r.bracketKind !== "explicit" || !r.names) continue;
          const rNames = r.names.split(/\s+/).filter(Boolean);
          if (!rNames.some((n) => linked.has(n))) {
            problems.push(`${d.name}: parameter '${r.names}' has no linked NL phrase`);
          }
        }
        if (!hasGoal) problems.push(`${d.name}: defined object has no (goal) crosslink`);
      }
    }
    expect(problems, problems.join("\n")).toEqual([]);
  });

  // Wave-2 policy (2026-08-17): every HEADLINE theorem is annotated — at
  // minimum its conclusion carries a `(goal)` link (full coverage of the
  // annotation is enforced by the gate above). Exempt only statements the
  // structurer cannot parse (the card renders flat there, links would be
  // inert) and index-truncated sources.
  it("every headline theorem carries crosslink annotations", async () => {
    const { parseCrosslinks, nlOf } = await import("../src/lib/docmd.js");
    const { structureDeclSource, findProofStart } = await import("../src/lib/leanStatement.js");
    const { naturalLanguageDoc, stripLeadingDoc } = await import("../src/lib/library.js");
    const lib = loadLibrary(libraryRoot());
    const headline = new Set(
      Object.values(lib.sidecars).flatMap((s) => s.headline_theorems ?? []),
    );
    const problems: string[] = [];
    for (const d of lib.entries) {
      if (d.kind !== "theorem" || !headline.has(d.name)) continue;
      const doc = naturalLanguageDoc(d);
      if (doc && parseCrosslinks(nlOf(doc) ?? "").some((s) => s.links)) continue;
      if (!d.source || d.source.includes("… truncated")) continue;
      let sig = stripLeadingDoc(d.source);
      const proofStart = findProofStart(sig);
      if (proofStart >= 0) sig = sig.slice(0, proofStart);
      if (!structureDeclSource(sig, d.kind)) continue;
      problems.push(`${d.name} (${d.file}:${d.line}): headline theorem with no crosslinks`);
    }
    expect(problems, problems.join("\n")).toEqual([]);
  });
});

// Freshness guard for the gate above: it validates annotations THROUGH the
// derived index, so a stale index (docstrings edited without `lake build &&
// lake exe library_index`) would make it pass VACUOUSLY over pre-edit text
// (adversarial-audit finding F1, 2026-08-17). Line-based counting of source
// markers undercounts multi-marker lines, so only SOURCE ≫ INDEX fails.
describe("NL ↔ Lean crosslink gate freshness", () => {
  it("the index carries the crosslink markers present in the Lean sources", () => {
    const root = libraryRoot();
    const lib = loadLibrary(root);
    let srcCount = 0;
    for (const f of trackedLeanFiles(root)) {
      const text = readFileSync(join(root, f), "utf8");
      for (const line of text.split("\n")) if (line.includes("](hyp:")) srcCount++;
    }
    let idxCount = 0;
    for (const e of lib.entries) {
      if (e.name.startsWith("Causalean.") && e.doc) {
        idxCount += (e.doc.match(/\]\(hyp:/g) ?? []).length;
      }
    }
    expect(
      srcCount <= idxCount * 1.1 + 50,
      `sources carry ~${srcCount} marker lines but the index only ${idxCount} — regenerate: lake build && lake exe library_index`,
    ).toBe(true);
  });
});

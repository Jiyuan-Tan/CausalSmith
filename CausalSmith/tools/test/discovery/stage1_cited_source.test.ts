import { describe, expect, it } from "vitest";

import { copyVerifiedCitedSourcesToPlan } from "../../src/formalization/stage1.js";
import { PlanSchema, resolveNodeCitation } from "../../src/formalization/plan/schema.js";
import { runPlanGate } from "../../src/formalization/plan/plan_gate.js";
import type { Core } from "../../src/discovery/core/schema.js";

function coreWithSource(source: Record<string, unknown>, proof_tex?: string): Core {
  return {
    bibliography: [{ key: source.cite, citation: "A. Author (2026). Source theorem." }],
    statements: [{
      id: "lem:external",
      kind: "lemma",
      statement: "external theorem",
      depends_on: [],
      status: "cited",
      source,
      ...(proof_tex ? { proof_tex } : {}),
    }],
  } as unknown as Core;
}

describe("F1 cited source-of-record carry-forward", () => {
  it("rejects duplicate citation ids at schema and plan-gate ingress", () => {
    const duplicatePlan = {
      qid: "test",
      nodes: {},
      citations: [
        { id: "cite:duplicate", title: "First", authors: "A", year: 2020 },
        { id: "cite:duplicate", title: "Second", authors: "B", year: 2021 },
      ],
    };
    expect(PlanSchema.safeParse(duplicatePlan).success).toBe(false);
    const gate = runPlanGate(duplicatePlan, {
      qid: "test", symbols: [], assumptions: [], definitions: [], statements: [], target_estimand: "none",
    } as unknown as Core);
    expect(gate.ok).toBe(false);
    expect(gate.violations).toContainEqual(expect.objectContaining({ code: "schema", message: expect.stringContaining("duplicate citation id") }));
  });

  it("reads a string source through its citation's locator, and rejects one without a locator", () => {
    const core = {
      qid: "test", symbols: [], assumptions: [], definitions: [], target_estimand: "none",
      statements: [{
        id: "lem:cited", kind: "lemma", statement: "Cited result.", depends_on: [], status: "cited",
        source: { cite: "Paper2026", locator: "Theorem 1", carrier: "logical-claim", verbatim_statement: "Cited result." },
      }],
    } as unknown as Core;
    const stringPlan = (locator?: string) => ({
      qid: "test",
      nodes: {
        "lem:cited": {
          lean_kind: "assumption", lean_name: "Cited", disposition: "define-local",
          gate: true, gate_class: "cited", source: "cite:paper",
        },
      },
      citations: [{ id: "cite:paper", title: "Paper", authors: "A", year: 2026, ...(locator ? { locator } : {}) }],
      feasibility: "formalizable-now",
    });
    const withLocator = PlanSchema.parse(stringPlan("Theorem 1"));
    expect(resolveNodeCitation(withLocator, withLocator.nodes["lem:cited"])).toMatchObject({ id: "cite:paper", locator: "Theorem 1" });
    expect(runPlanGate(stringPlan("Theorem 1"), core).violations.filter((v) => v.message.includes("locator"))).toEqual([]);
    expect(runPlanGate(stringPlan(), core).violations).toContainEqual(expect.objectContaining({
      code: "P9", where: "lem:cited", message: expect.stringContaining("needs a locator"),
    }));
  });

  it("uses the verified core and bibliography when the planner writes an object source", () => {
    const plan = {
      nodes: { "lem:external": { source: { cite: "cite:external" } } },
      citations: [{ id: "cite:external", bibkey: "Paper2026", locator: "planner locator" }],
    };
    const core = coreWithSource({
      cite: "Paper2026", locator: "Corollary 1", verbatim_statement: "Verified theorem.",
    });
    core.bibliography = [{ key: "Paper2026", citation: "A. Author and B. Author (2026). Exact result: a theorem. arXiv:2601.12345." }];
    expect(copyVerifiedCitedSourcesToPlan(plan, core)).toBe(1);
    expect(plan.nodes["lem:external"].source).toEqual({
      citation: "cite:external", locator: "Corollary 1", verbatim_statement: "Verified theorem.",
    });
    expect(plan.citations[0]).toMatchObject({
      title: "Exact result: a theorem", authors: "A. Author and B. Author", year: 2026,
      bibkey: "Paper2026", arxiv: "2601.12345",
    });
    expect(plan.citations[0]).not.toHaveProperty("locator");
  });

  it("derives internal bank metadata from the source citation after replacing planner values", () => {
    const plan = {
      nodes: { "lem:external": { source: "cite:bank" } },
      citations: [{ id: "cite:bank", bibkey: "Bank2026", title: "planner title", authors: "planner authors", year: 1900 }],
    };
    const core = coreWithSource({ cite: "Bank2026", locator: "Theorem 1", verbatim_statement: "Exact lower bound." });
    core.bibliography = [{ key: "Bank2026", citation: "CausalSmith research bank (2026). Accepted lower-bound-only policy-regret exponent." }];
    copyVerifiedCitedSourcesToPlan(plan, core);
    expect(plan.citations[0]).toMatchObject({
      title: "Accepted lower-bound-only policy-regret exponent",
      authors: "CausalSmith research bank",
      year: 2026,
      bibkey: "Bank2026",
    });
  });

  it("derives period-year metadata and overwrites invented planner values", () => {
    const plan = {
      nodes: { "lem:external": { source: "cite:external" } },
      citations: [{ id: "cite:external", bibkey: "Paper1987", title: "Invented title", authors: "Invented author", year: 1900 }],
    };
    const core = coreWithSource({ cite: "Paper1987", locator: "Theorem 1" });
    core.bibliography = [{ key: "Paper1987", citation: "Nolan, Deborah, and David Pollard. 1987. U-Processes: Rates of Convergence. Annals of Statistics 15(2): 780--799." }];
    copyVerifiedCitedSourcesToPlan(plan, core);
    expect(plan.citations[0]).toMatchObject({
      title: "U-Processes: Rates of Convergence", authors: "Nolan, Deborah, and David Pollard", year: 1987,
    });
  });

  it("does not include the journal in a parenthetical-year title before arXiv metadata", () => {
    const plan = {
      nodes: { "lem:external": { source: "cite:external" } },
      citations: [{ id: "cite:external", bibkey: "Paper2026", title: "Invented title" }],
    };
    const core = coreWithSource({ cite: "Paper2026", locator: "Theorem 1" });
    core.bibliography = [{ key: "Paper2026", citation: "A. Author (2026). True Title. Journal Name. arXiv:2601.12345." }];
    copyVerifiedCitedSourcesToPlan(plan, core);
    expect(plan.citations[0]).toMatchObject({ title: "True Title", authors: "A. Author", year: 2026 });
  });

  it("extracts a TeX-quoted title before the venue in an existing cited-source format", () => {
    const plan = {
      nodes: { "lem:external": { source: "cite:external" } },
      citations: [{ id: "cite:external", bibkey: "Paper2023", title: "Invented title" }],
    };
    const core = coreWithSource({ cite: "Paper2023", locator: "Theorem 1" });
    core.bibliography = [{ key: "Paper2023", citation: "L. Wendong and colleagues (2023), ``Causal Component Analysis,'' Advances in Neural Information Processing Systems 36." }];
    copyVerifiedCitedSourcesToPlan(plan, core);
    expect(plan.citations[0]).toMatchObject({ title: "Causal Component Analysis", year: 2023 });
  });

  it("keeps the planner's work metadata when the bibliography entry matches no recognized format", () => {
    const plan = {
      nodes: { "lem:external": { source: "cite:external" } },
      citations: [{ id: "cite:external", bibkey: "Paper2023", title: "Planner title", authors: "Planner author", year: 2023 }],
    };
    const core = coreWithSource({ cite: "Paper2023", locator: "Theorem 1" });
    core.bibliography = [{ key: "Paper2023", citation: "Andreas Gerhardus and colleagues (2023), Projecting Infinite Time Series Graphs to Finite Marginal Graphs Using Number Theory, arXiv:2310.05526." }];
    expect(copyVerifiedCitedSourcesToPlan(plan, core)).toBe(1);
    expect(plan.citations[0]).toEqual({
      id: "cite:external", bibkey: "Paper2023", title: "Planner title", authors: "Planner author", year: 2023, arxiv: "2310.05526",
    });
    expect(plan.nodes["lem:external"].source).toEqual({ citation: "cite:external", locator: "Theorem 1" });
  });

  it("collapses duplicate citation ids to the repaired source record", () => {
    const plan = {
      nodes: { "lem:external": { source: "cite:external" } },
      citations: [
        { id: "cite:external", bibkey: "Paper2026", title: "invented" },
        { id: "cite:external", title: "wrong later record" },
      ],
    };
    const core = coreWithSource({ cite: "Paper2026", locator: "Theorem 1", verbatim_statement: "Exact theorem." });
    core.bibliography = [{ key: "Paper2026", citation: "A. Author (2026). True title. arXiv:2601.12345." }];
    copyVerifiedCitedSourcesToPlan(plan, core);
    expect(plan.citations).toHaveLength(1);
    expect(plan.citations[0]).toMatchObject({ title: "True title", bibkey: "Paper2026" });
  });

  it("fails closed when one citation id names different source works", () => {
    const core = coreWithSource({ cite: "Paper2026", locator: "Theorem 1", verbatim_statement: "Shared text." });
    core.statements.push({ ...core.statements[0], id: "lem:other", source: { cite: "Other2026", locator: "Theorem 1", verbatim_statement: "Shared text." } });
    core.bibliography!.push({ key: "Other2026", citation: "B. Author (2026). Other source theorem." });
    const plan = {
      nodes: { "lem:external": { source: "cite:shared" }, "lem:other": { source: "cite:shared" } },
      citations: [{ id: "cite:shared", locator: "Theorem 1" }],
    };
    expect(() => copyVerifiedCitedSourcesToPlan(plan, core)).toThrow(
      "citation cite:shared has conflicting work metadata for 'bibkey'",
    );
  });

  it("keeps distinct claim edges that cite the same canonical work", () => {
    const core = coreWithSource({ cite: "Paper2026", locator: "Theorem 1", verbatim_statement: "First claim." });
    core.statements.push({
      ...core.statements[0], id: "lem:other",
      source: { cite: "Paper2026", locator: "Corollary 4", verbatim_statement: "Second claim.", attestation: { by: "main", note: "checked page 9" } },
    });
    const plan = {
      qid: "test",
      nodes: {
        "lem:external": { lean_kind: "assumption", lean_name: "External", disposition: "define-local", source: "cite:shared" },
        "lem:other": { lean_kind: "assumption", lean_name: "Other", disposition: "define-local", source: "cite:shared" },
      },
      citations: [{ id: "cite:shared", bibkey: "Paper2026", title: "planner value" }],
    };
    expect(copyVerifiedCitedSourcesToPlan(plan, core)).toBe(2);
    expect(plan.citations).toHaveLength(1);
    expect(plan.citations[0]).toEqual({
      id: "cite:shared", bibkey: "Paper2026", authors: "A. Author", year: 2026, title: "Source theorem",
    });
    expect(plan.nodes["lem:external"].source).toEqual({
      citation: "cite:shared", locator: "Theorem 1", verbatim_statement: "First claim.",
    });
    expect(plan.nodes["lem:other"].source).toEqual({
      citation: "cite:shared", locator: "Corollary 4", verbatim_statement: "Second claim.",
      attestation: { by: "main", note: "checked page 9" },
    });
    const parsed = PlanSchema.parse(plan);
    expect(resolveNodeCitation(parsed, parsed.nodes["lem:other"])).toMatchObject({
      id: "cite:shared", title: "Source theorem", locator: "Corollary 4", verbatim_statement: "Second claim.",
    });
  });

  it("copies the D0.5-verified source instead of trusting planner prose", () => {
    const plan = {
      nodes: { "lem:external": { source: "cite:external" } },
      citations: [{
        id: "cite:external",
        locator: "wrong locator",
        verbatim_statement: "planner reconstruction",
      }],
    };
    const count = copyVerifiedCitedSourcesToPlan(plan, coreWithSource({
      cite: "Paper2026",
      locator: "Theorem 3.1",
      verbatim_statement: "Exact theorem with hypothesis H.",
      doi: "10.1/example",
      attestation: { by: "user", note: "page supplied by user" },
    }));
    expect(count).toBe(1);
    expect(plan.nodes["lem:external"].source).toMatchObject({
      citation: "cite:external",
      locator: "Theorem 3.1",
      verbatim_statement: "Exact theorem with hypothesis H.",
      attestation: { by: "user", note: "page supplied by user" },
    });
    expect(plan.citations[0]).toMatchObject({ doi: "10.1/example" });
  });

  it("migrates a legacy cited transcription from proof_tex", () => {
    const plan = {
      nodes: { "lem:external": { source: "cite:external" } },
      citations: [{ id: "cite:external" }],
    };
    copyVerifiedCitedSourcesToPlan(
      plan,
      coreWithSource({ cite: "Paper2026", locator: "Lemma 2" }, "Legacy exact transcription."),
    );
    expect(plan.nodes["lem:external"].source).toMatchObject({
      citation: "cite:external",
      locator: "Lemma 2",
      verbatim_statement: "Legacy exact transcription.",
    });
  });
});

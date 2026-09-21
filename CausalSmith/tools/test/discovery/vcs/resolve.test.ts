import { mkdtemp, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import type { Core } from "../../../src/discovery/core/schema.js";
import { SolveUnitOutputSchema } from "../../../src/discovery/solve/schemas.js";
import { commitOrThrow, headGraph } from "../../../src/discovery/vcs/commit.js";
import { checkGraph } from "../../../src/discovery/vcs/checks.js";
import { loadGraph } from "../../../src/discovery/vcs/graph.js";
import { blobId, contentKey, type NodeBlob } from "../../../src/discovery/vcs/node.js";
import { mergePr, openPr, readPr } from "../../../src/discovery/vcs/pr.js";
import { graphFromCore, normalizeGraph, renderCore } from "../../../src/discovery/vcs/render.js";
import { assertPreparedOeqResolutionPr, prepareOeqResolutionToExisting, resolveOeqToExisting } from "../../../src/discovery/vcs/resolve.js";
import { VcsStore } from "../../../src/discovery/vcs/store.js";
import { fixtureCore } from "./fixture.js";

describe("evidence-backed existing-theorem OEQ resolution", () => {
  let dir: string;
  let store: VcsStore;

  beforeEach(async () => {
    dir = await mkdtemp(path.join(os.tmpdir(), "vcs-resolve-"));
    store = new VcsStore(dir);
  });
  afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

  async function reviewedFixture(
    extraWitnessDependency?: string,
    witnessProof = "By thm:existing under the question context.",
    questionOnlyStatement = false,
    questionOnlyContext?: "assumption" | "definition",
    witnessStatement = "The rate is sharp.",
  ) {
    const core: Core = fixtureCore();
    core.statements.push({
      id: "thm:existing", kind: "theorem", statement: "The rate is sharp.",
      depends_on: ["ass:overlap"], free_symbols: [], status: "proved", proof_tex: "By ass:overlap.",
      justification: "j", gap: "g", consumer: "c",
    });
    core.statements.push({
      id: "thm:unrelated", kind: "theorem", statement: "An unrelated conclusion.",
      depends_on: ["ass:overlap"], free_symbols: [], status: "proved", proof_tex: "By ass:overlap.",
      justification: "j", gap: "g", consumer: "c",
    });
    core.statements.push({
      id: "oeq:sharp", kind: "openendedquestion", statement: "Is the rate sharp?",
      depends_on: ["ass:overlap"], free_symbols: [], status: "to-prove",
      justification: "j", gap: "g", consumer: "thm:main",
    });
    if (questionOnlyContext === "assumption") {
      core.assumptions.push({
        id: "ass:question-only", condition: "a question-only premise", free_symbols: [],
        novel: { flag: true, justification: "fixture" }, used_by: ["oeq:sharp"],
      });
      core.statements.find((s) => s.id === "oeq:sharp")!.depends_on!.push("ass:question-only");
    } else if (questionOnlyContext === "definition") {
      core.definitions.push({
        id: "def:question-only", name: "question-only object", construction: "$1$", free_symbols: [], inputs: [],
      });
      core.statements.find((s) => s.id === "oeq:sharp")!.depends_on!.push("def:question-only");
    }
    if (questionOnlyStatement) {
      core.statements.push({
        id: "lem:question-only", kind: "lemma", statement: "A question-specific intermediate result.",
        depends_on: ["ass:overlap"], free_symbols: [], status: "proved", proof_tex: "By ass:overlap.",
        justification: "j", gap: "g", consumer: "oeq:sharp",
      });
      core.statements.find((s) => s.id === "oeq:sharp")!.depends_on!.push("lem:question-only");
    }
    core.statements.find((s) => s.id === "thm:main")!.depends_on.push("oeq:sharp");
    core.symbols.push({ name: "rSharp", type: "rate", def: "the sharp rate", ref: "oeq:sharp" });
    if (extraWitnessDependency !== undefined) {
      core.assumptions.push({
        id: extraWitnessDependency, condition: "an unrelated extra condition", free_symbols: [],
        novel: { flag: true, justification: "fixture" }, used_by: [],
      });
    }
    const initial = await commitOrThrow({
      store, graph: graphFromCore(core), parents: [], author: "test", kind: "initial", message: "init", expectedHead: null,
    });
    const dependencies = ["oeq:sharp", "thm:existing"];
    if (extraWitnessDependency !== undefined) dependencies.push(extraWitnessDependency);
    if (questionOnlyStatement) dependencies.push("lem:question-only");
    if (questionOnlyContext !== undefined) dependencies.push(`${questionOnlyContext === "assumption" ? "ass" : "def"}:question-only`);
    const { pr } = await openPr({
      store, base: initial.id, round: 1,
      submissions: [{
        unit: "oeq:sharp", targets: ["oeq:sharp"],
        output: SolveUnitOutputSchema.parse({
          resolved_oeqs: [{
            source_id: "oeq:sharp",
            theorem: {
              id: "thm:wrapper", kind: "theorem", statement: witnessStatement,
              depends_on: dependencies, free_symbols: [], status: "proved",
              proof_tex: witnessProof,
            },
          }],
        }),
      }],
    });
    const merged = await mergePr({
      store, pr,
      verdict: { accept: "all", note: "the answer is correct", by: "adjudicator" },
    });
    expect(merged.ok).toBe(true);
    if (!merged.ok) throw new Error("fixture merge failed");
    const reviewed = await readPr(store, pr.id);
    const mergeCommit = await store.readCommit(merged.commit);
    const acceptedHeadId = mergeCommit.parents[1];
    const acceptedHeadCommit = await store.readCommit(acceptedHeadId);
    return {
      pr: reviewed,
      prBase: await loadGraph(store, pr.base),
      prHead: await loadGraph(store, pr.id),
      acceptedHead: await loadGraph(store, acceptedHeadId),
      current: (await headGraph(store)).graph,
      currentId: merged.commit,
      mergeCommit,
      acceptedHeadCommit,
    };
  }

  it("tombstones to the reviewed existing theorem and rewires consumers and symbols", async () => {
    const evidence = await reviewedFixture();
    const resolved = resolveOeqToExisting({
      ...evidence, sourceId: "oeq:sharp", theoremId: "thm:existing",
    });
    expect(resolved.nodes.get("oeq:sharp")).toMatchObject({
      body: { resolved_by: "thm:existing", proof_basis: { "thm:existing": expect.stringMatching(/^[a-f0-9]{64}$/) } },
    });
    expect(resolved.nodes.has("thm:wrapper")).toBe(false);
    expect(resolved.nodes.get("sym:rSharp")).toMatchObject({ body: { ref: "thm:existing" } });
    const rendered = renderCore(resolved);
    expect(rendered.statements.map((s) => s.id)).not.toContain("oeq:sharp");
    expect(rendered.statements.find((s) => s.id === "thm:main")?.depends_on).toContain("thm:existing");
    expect(rendered.statements.filter((s) => s.statement === "The rate is sharp.").map((s) => s.id)).toEqual(["thm:existing"]);
  });

  it("refuses an unrelated existing theorem", async () => {
    const evidence = await reviewedFixture();
    expect(() => resolveOeqToExisting({
      ...evidence, sourceId: "oeq:sharp", theoremId: "thm:unrelated",
    })).toThrow(/does not have the exact mathematical content of 'thm:unrelated'/);
  });

  it("requires the accepted witness and target to have identical mathematical content", async () => {
    const evidence = await reviewedFixture(
      undefined,
      "By thm:existing, a related but different conclusion follows.",
      false,
      undefined,
      "A related but different conclusion.",
    );
    expect(() => resolveOeqToExisting({
      ...evidence, sourceId: "oeq:sharp", theoremId: "thm:existing",
    })).toThrow(/does not have the exact mathematical content of 'thm:existing'/);
  });

  it("prepares an exact alias PR, accepts it normally, and finalizes by deduplication", async () => {
    const core: Core = fixtureCore();
    core.statements.push({
      id: "thm:existing", kind: "theorem", statement: "The rate is sharp.",
      depends_on: ["ass:overlap"], free_symbols: [], status: "proved", proof_tex: "By ass:overlap.",
      justification: "j", gap: "g", consumer: "c",
    });
    core.statements.push({
      id: "oeq:sharp", kind: "openendedquestion", statement: "Is the rate sharp?",
      depends_on: ["ass:overlap"], free_symbols: [], status: "to-prove",
      justification: "j", gap: "g", consumer: "thm:main",
    });
    core.symbols.push({ name: "rSharp", type: "rate", def: "the sharp rate", ref: "oeq:sharp" });
    const initial = await commitOrThrow({
      store, graph: graphFromCore(core), parents: [], author: "test", kind: "initial", message: "init", expectedHead: null,
    });
    const headBeforeCheck = await store.readRef("main");
    const prepared = prepareOeqResolutionToExisting(initial.graph, "oeq:sharp", "thm:existing");
    expect(await store.readRef("main")).toBe(headBeforeCheck); // `--check` calls only this pure preparation.
    expect(prepared.expectedApprovalIds).toEqual(expect.arrayContaining([prepared.witnessId, "sym:rSharp"]));
    const opened = await openPr({ store, base: initial.id, round: 0, submissions: [prepared.submission] });
    assertPreparedOeqResolutionPr(opened.pr, "oeq:sharp", prepared);
    expect(opened.pr.status).toBe("open");
    expect(opened.pr.approval.map((item) => item.id).sort()).toEqual(prepared.expectedApprovalIds);
    const merged = await mergePr({
      store, pr: opened.pr,
      verdict: { accept: "all", note: "exact alias answers the question", by: "adjudicator" },
    });
    expect(merged.ok).toBe(true);
    if (!merged.ok) throw new Error("fixture merge failed");
    const pr = await readPr(store, opened.pr.id);
    const mergeCommit = await store.readCommit(merged.commit);
    const acceptedHeadCommit = await store.readCommit(mergeCommit.parents[1]);
    const resolved = resolveOeqToExisting({
      current: merged.graph,
      currentId: merged.commit,
      prBase: await loadGraph(store, pr.base),
      prHead: await loadGraph(store, pr.id),
      acceptedHead: await loadGraph(store, acceptedHeadCommit.id),
      pr,
      mergeCommit,
      acceptedHeadCommit,
      sourceId: "oeq:sharp",
      theoremId: "thm:existing",
    });
    expect(resolved.nodes.get("oeq:sharp")).toMatchObject({ body: { resolved_by: "thm:existing" } });
    expect(resolved.nodes.has(prepared.witnessId)).toBe(false);
    expect(resolved.nodes.get("sym:rSharp")).toMatchObject({ body: { ref: "thm:existing" } });
  });

  it.each([
    ["TeX-wrapped definition", "definition"],
    ["plain assumption", "assumption"],
  ] as const)("prepare refuses a non-rewritable Q reference in a %s", (_label, kind) => {
    const core: Core = fixtureCore();
    core.statements.push({
      id: "thm:existing", kind: "theorem", statement: "The rate is sharp.",
      depends_on: [], free_symbols: [], status: "proved", proof_tex: "Immediate.",
      justification: "j", gap: "g", consumer: "c",
    });
    core.statements.push({
      id: "oeq:sharp", kind: "openendedquestion", statement: "Is the rate sharp?",
      depends_on: [], free_symbols: [], status: "to-prove", justification: "j", gap: "g", consumer: "c",
    });
    if (kind === "definition") {
      core.definitions[0].construction += " with \\mathrm{oeq{:}sharp}";
    } else {
      core.assumptions[0].condition += " and oeq:sharp";
    }
    expect(() => prepareOeqResolutionToExisting(
      graphFromCore(core), "oeq:sharp", "thm:existing",
    )).toThrow(new RegExp(`non-rewritable field of '${kind === "definition" ? "def:class" : "ass:overlap"}'.*oeq:sharp`));
  });

  it("prepare refuses an OEQ carrying partial proof state", () => {
    const core: Core = fixtureCore();
    core.statements.push({
      id: "thm:existing", kind: "theorem", statement: "The rate is sharp.",
      depends_on: [], free_symbols: [], status: "proved", proof_tex: "Immediate.",
      justification: "j", gap: "g", consumer: "c",
    });
    core.statements.push({
      id: "oeq:sharp", kind: "openendedquestion", statement: "Is the rate sharp?",
      depends_on: [], free_symbols: [], status: "to-prove", proof_tex: "A partial argument.",
      justification: "j", gap: "g", consumer: "c",
    });
    expect(() => prepareOeqResolutionToExisting(
      graphFromCore(core), "oeq:sharp", "thm:existing",
    )).toThrow(/not an ordinary to-prove open-ended question/);
  });

  it("refuses a target padded into dependencies and proof_basis but absent from proof text", async () => {
    const evidence = await reviewedFixture(undefined, "By ass:overlap under the question context.");
    expect(() => resolveOeqToExisting({
      ...evidence, sourceId: "oeq:sharp", theoremId: "thm:existing",
    })).toThrow(/does not cite 'thm:existing' in its proof/);
  });

  it("refuses a question-only lemma outside the target theorem closure", async () => {
    const evidence = await reviewedFixture(
      undefined,
      "By thm:existing together with lem:question-only.",
      true,
    );
    expect(() => resolveOeqToExisting({
      ...evidence, sourceId: "oeq:sharp", theoremId: "thm:existing",
    })).toThrow(/cites nodes outside 'thm:existing' closure: lem:question-only/);
  });

  it.each(["assumption", "definition"] as const)(
    "refuses a cited question-only %s outside the target theorem closure",
    async (kind) => {
      const id = `${kind === "assumption" ? "ass" : "def"}:question-only`;
      const evidence = await reviewedFixture(undefined, `By thm:existing together with ${id}.`, false, kind);
      expect(() => resolveOeqToExisting({
        ...evidence, sourceId: "oeq:sharp", theoremId: "thm:existing",
      })).toThrow(new RegExp(`cites nodes outside 'thm:existing' closure: ${id}`));
    },
  );

  it("refuses a witness that needs context outside the question and theorem", async () => {
    const evidence = await reviewedFixture("ass:extra");
    expect(() => resolveOeqToExisting({
      ...evidence, sourceId: "oeq:sharp", theoremId: "thm:existing",
    })).toThrow(/context outside.*ass:extra/);
  });

  it("refuses an open, unadjudicated evidence PR", async () => {
    const evidence = await reviewedFixture();
    const openEvidence = { ...evidence.pr, status: "open" as const, verdict: undefined };
    expect(() => resolveOeqToExisting({
      ...evidence, pr: openEvidence, sourceId: "oeq:sharp", theoremId: "thm:existing",
    })).toThrow(/did not positively adjudicate/);
  });

  it("refuses a mutable PR verdict that disagrees with the immutable merge", async () => {
    const evidence = await reviewedFixture();
    const tampered = {
      ...evidence.pr,
      verdict: { ...evidence.pr.verdict!, accepted: [...evidence.pr.verdict!.accepted, "thm:unrelated"] },
    };
    expect(() => resolveOeqToExisting({
      ...evidence, pr: tampered, sourceId: "oeq:sharp", theoremId: "thm:existing",
    })).toThrow(/immutable merge metadata disagrees/);
  });

  it("refuses a question changed after the reviewed resolution", async () => {
    const evidence = await reviewedFixture();
    const current = { tree: { ...evidence.current.tree }, nodes: new Map(evidence.current.nodes) };
    const source = current.nodes.get("oeq:sharp")! as Extract<NodeBlob, { node_type: "statement" }>;
    const changed: NodeBlob = { node_type: "statement", body: { ...source.body, consumer: "a different use" } };
    current.nodes.set("oeq:sharp", changed);
    current.tree["oeq:sharp"] = { ...current.tree["oeq:sharp"], blob: blobId(changed) };
    expect(() => resolveOeqToExisting({
      ...evidence, current, sourceId: "oeq:sharp", theoremId: "thm:existing",
    })).toThrow(/changed since the evidence PR/);
  });

  it("refuses a target whose proof is no longer current", async () => {
    const evidence = await reviewedFixture();
    const current = { tree: { ...evidence.current.tree }, nodes: new Map(evidence.current.nodes) };
    const theorem = current.nodes.get("thm:existing")! as Extract<NodeBlob, { node_type: "statement" }>;
    const { proof_basis: _basis, ...body } = theorem.body;
    const stale: NodeBlob = { node_type: "statement", body };
    current.nodes.set("thm:existing", stale);
    current.tree["thm:existing"] = { ...current.tree["thm:existing"], blob: blobId(stale) };
    expect(() => resolveOeqToExisting({
      ...evidence, current, sourceId: "oeq:sharp", theoremId: "thm:existing",
    })).toThrow(/not a proved theorem with a complete current basis/);
  });

  it("the resolution pin refuses a later target-content change", async () => {
    const evidence = await reviewedFixture();
    const resolved = resolveOeqToExisting({
      ...evidence, sourceId: "oeq:sharp", theoremId: "thm:existing",
    });
    const theorem = resolved.nodes.get("thm:existing")! as Extract<NodeBlob, { node_type: "statement" }>;
    const changed: NodeBlob = { node_type: "statement", body: { ...theorem.body, statement: "A changed claim." } };
    const changedGraph = { tree: { ...resolved.tree }, nodes: new Map(resolved.nodes) };
    changedGraph.nodes.set("thm:existing", changed);
    changedGraph.tree["thm:existing"] = { ...changedGraph.tree["thm:existing"], blob: blobId(changed) };
    const stillStale = normalizeGraph(changedGraph);
    expect(checkGraph(stillStale).violations).toContainEqual(expect.objectContaining({
      code: "V2", where: "oeq:sharp", message: expect.stringContaining("resolution basis does not pin"),
    }));
  });

  it("normalizes a legacy missing resolution pin and checks require it", async () => {
    const evidence = await reviewedFixture();
    const resolved = resolveOeqToExisting({
      ...evidence, sourceId: "oeq:sharp", theoremId: "thm:existing",
    });
    const legacy = { tree: { ...resolved.tree }, nodes: new Map(resolved.nodes) };
    const source = legacy.nodes.get("oeq:sharp")! as Extract<NodeBlob, { node_type: "statement" }>;
    const { proof_basis: _pin, ...body } = source.body;
    const unpinned: NodeBlob = { node_type: "statement", body };
    legacy.nodes.set("oeq:sharp", unpinned);
    legacy.tree["oeq:sharp"] = { ...legacy.tree["oeq:sharp"], blob: blobId(unpinned) };

    expect(checkGraph(legacy).violations).toContainEqual(expect.objectContaining({
      code: "V2", where: "oeq:sharp", message: expect.stringContaining("does not pin"),
    }));
    const migrated = normalizeGraph(legacy);
    const theorem = migrated.nodes.get("thm:existing")!;
    expect(migrated.nodes.get("oeq:sharp")).toMatchObject({
      body: { proof_basis: { "thm:existing": contentKey(theorem) } },
    });
    expect(checkGraph(migrated).ok).toBe(true);
    expect(normalizeGraph(migrated).tree).toEqual(migrated.tree);
  });

  it.each([
    ["definition construction", "def:class", "construction"],
    ["assumption condition", "ass:overlap", "condition"],
  ] as const)("refuses a wrapper reference in a non-rewritable %s", async (_label, nodeId, field) => {
    const evidence = await reviewedFixture();
    const current = { tree: { ...evidence.current.tree }, nodes: new Map(evidence.current.nodes) };
    const original = current.nodes.get(nodeId)!;
    const changed: NodeBlob = {
      ...original,
      body: { ...original.body, [field]: `${String((original.body as unknown as Record<string, unknown>)[field])} thm:wrapper` },
    } as NodeBlob;
    current.nodes.set(nodeId, changed);
    current.tree[nodeId] = { ...current.tree[nodeId], blob: blobId(changed) };
    expect(() => resolveOeqToExisting({
      ...evidence, current, sourceId: "oeq:sharp", theoremId: "thm:existing",
    })).toThrow(new RegExp(`non-rewritable field of '${nodeId}'.*thm:wrapper`));
  });

  it("refuses a TeX-wrapped wrapper reference in a non-rewritable field", async () => {
    const evidence = await reviewedFixture();
    const current = { tree: { ...evidence.current.tree }, nodes: new Map(evidence.current.nodes) };
    const original = current.nodes.get("def:class")! as Extract<NodeBlob, { node_type: "definition" }>;
    const changed: NodeBlob = {
      node_type: "definition",
      body: { ...original.body, construction: `${original.body.construction} \\mathrm{thm{:}wrapper}` },
    };
    current.nodes.set("def:class", changed);
    current.tree["def:class"] = { ...current.tree["def:class"], blob: blobId(changed) };
    expect(() => resolveOeqToExisting({
      ...evidence, current, sourceId: "oeq:sharp", theoremId: "thm:existing",
    })).toThrow(/non-rewritable field of 'def:class'.*thm:wrapper/);
  });
});

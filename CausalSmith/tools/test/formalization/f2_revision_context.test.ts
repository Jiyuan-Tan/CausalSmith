import { describe, expect, it } from "vitest";
import { CoreSchema } from "../../src/discovery/core/schema.js";
import {
  buildF2RevisionContext,
  F2_REVISION_TARGETS_HEADER,
  scaffoldCoverageGaps,
  revisionTargetsFromRedirect,
} from "../../src/formalization/f2_revision_context.js";
import { PlanSchema } from "../../src/formalization/plan/schema.js";

function fixture() {
  const core = CoreSchema.parse({
    qid: "local-context-test",
    symbols: [
      { name: "x", type: "real" },
      { name: "y", type: "real", refs: ["x"], ref: "def:derived" },
      { name: "z", type: "real" },
    ],
    assumptions: [
      {
        id: "ass:shared",
        condition: "x is positive",
        free_symbols: ["x"],
        standard: { name: "positivity", cite: "fixture" },
      },
      {
        id: "ass:unrelated",
        condition: "z is bounded",
        free_symbols: ["z"],
        standard: { name: "boundedness", cite: "fixture" },
      },
    ],
    definitions: [
      {
        id: "def:shared",
        name: "Shared",
        construction: "objects satisfying ass:shared",
        free_symbols: ["x"],
        by_member_properties: ["ass:shared"],
      },
      {
        id: "def:derived",
        name: "Derived",
        construction: "y computed from x",
        free_symbols: ["x", "y"],
        inputs: ["x"],
      },
    ],
    statements: [
      {
        id: "thm:target",
        kind: "theorem",
        statement: "target about x",
        free_symbols: ["x"],
        depends_on: ["def:shared"],
        route: "direct",
        status: "to-prove",
        proof_tex: "PROOF_SENTINEL",
        justification: "PROSE_SENTINEL",
      },
      {
        id: "lem:consumer",
        kind: "lemma",
        statement: "consumer of target",
        free_symbols: ["x"],
        depends_on: ["thm:target"],
        status: "to-prove",
      },
      {
        id: "lem:sibling",
        kind: "lemma",
        statement: "sibling using the same prerequisite",
        free_symbols: ["x"],
        depends_on: ["def:shared"],
        status: "to-prove",
      },
      {
        id: "lem:unrelated",
        kind: "lemma",
        statement: "unrelated z result",
        free_symbols: ["z"],
        depends_on: ["ass:unrelated"],
        status: "to-prove",
      },
    ],
    sampling_model: { observed: "x" },
    target_estimand: "x",
    bibliography: [],
  });
  const node = (lean_kind: string, lean_name: string, extra = {}) => ({
    lean_kind,
    lean_name,
    disposition: "define-local",
    reuse: null,
    modules: [],
    ...extra,
  });
  const plan = PlanSchema.parse({
    qid: core.qid,
    env: [
      { id: "S1", world: "x-world", binds_symbols: ["x"], binds_sampling_model: true, disposition: "define-local" },
      { id: "S2", world: "z-world", binds_symbols: ["z"], binds_sampling_model: false, disposition: "define-local" },
    ],
    nodes: {
      "ass:shared": node("assumption", "SharedAssumption"),
      "ass:unrelated": node("assumption", "UnrelatedAssumption"),
      "def:shared": node("structure", "Shared", { members: ["ass:shared"] }),
      "def:derived": node("def", "Derived"),
      "thm:target": node("theorem", "targetTheorem", { hyps: ["def:shared"] }),
      "lem:consumer": node("lemma", "consumerLemma", { hyps: ["thm:target"] }),
      "lem:sibling": node("lemma", "siblingLemma", { hyps: ["def:shared"] }),
      "lem:unrelated": node("lemma", "unrelatedLemma", { hyps: ["ass:unrelated"] }),
    },
    citations: [],
  });
  return { core, plan };
}

describe("F2 local revision context", () => {
  const shown = (packet: ReturnType<typeof buildF2RevisionContext>) =>
    Object.keys(packet!.plan.nodes as Record<string, unknown>);

  it("carries a flagged statement and the entries citing it, not its prerequisites or siblings", () => {
    const { core, plan } = fixture();
    const packet = buildF2RevisionContext(core, plan, ["thm:target"]);
    expect(shown(packet)).toEqual(["thm:target", "lem:consumer"]);
    expect(packet!.plan.env).toEqual([]);
    expect(packet!.core.symbols).toEqual([expect.objectContaining({ name: "x" })]);
    expect(JSON.stringify(packet!.core)).not.toContain("PROOF_SENTINEL");
    expect(JSON.stringify(packet!.core)).not.toContain("PROSE_SENTINEL");
  });

  it("carries the users of a flagged premise", () => {
    const { core, plan } = fixture();
    const packet = buildF2RevisionContext(core, plan, ["ass:shared"]);
    expect(shown(packet).sort()).toEqual(["ass:shared", "def:shared", "lem:consumer", "lem:sibling", "thm:target"]);
  });

  it("carries a flagged symbol's realizing cluster, not every declaration using the symbol", () => {
    const { core, plan } = fixture();
    const packet = buildF2RevisionContext(core, plan, ["sym:y"]);
    expect(shown(packet)).toEqual(["def:derived"]);
    expect(packet!.resolved_targets).toEqual(["sym:y"]);
    expect((packet!.core.symbols as Array<{ name: string }>).map((s) => s.name)).toEqual(["x", "y"]);
    const bound = buildF2RevisionContext(core, plan, ["sym:x"]);
    expect(shown(bound)).toEqual([]);
    expect(bound!.plan.env).toEqual([expect.objectContaining({ id: "S1" })]);
  });

  it("resolves a target that is no core node through the core nodes its id names", () => {
    const { core, plan } = fixture();
    const packet = buildF2RevisionContext(core, plan, ["ass:filler:3:lem:unrelated:7:h_gate"]);
    expect(packet!.resolved_targets).toEqual(["lem:unrelated"]);
    expect(shown(packet)).toEqual(["lem:unrelated"]);
    // An unresolvable target beside a resolvable one does not widen the packet.
    expect(shown(buildF2RevisionContext(core, plan, ["lem:unrelated", "aux_helper"]))).toEqual(["lem:unrelated"]);
  });

  it("carries a flagged S-block, the nodes the redirect names, and the users of an unbound symbol", () => {
    const { core, plan } = fixture();
    const block = buildF2RevisionContext(core, plan, ["S-2"], ["the Lean drops ass:unrelated"]);
    expect(block!.plan.env).toEqual([expect.objectContaining({ id: "S2" })]);
    expect(shown(block)).toEqual(["ass:unrelated"]);
    plan.env[1].binds_symbols = [];
    expect(shown(buildF2RevisionContext(core, plan, ["sym:z"])).sort()).toEqual(["ass:unrelated", "lem:unrelated"]);
  });

  it("keeps the whole context when no target resolves or the change reaches every node", () => {
    const { core, plan } = fixture();
    expect(buildF2RevisionContext(core, plan, ["aux_helper"])).toBeNull();
    expect(buildF2RevisionContext(core, plan, Object.keys(plan.nodes))).toBeNull();
  });

  it("recovers only the exact persisted dispatcher target block", () => {
    const redirect = `Fix the mismatch.\n\n${F2_REVISION_TARGETS_HEADER}\n- thm:target\n- sym:x`;
    expect(revisionTargetsFromRedirect(redirect)).toEqual(["thm:target", "sym:x"]);
    expect(revisionTargetsFromRedirect("Please edit thm:target")).toEqual([]);
  });

  it("lists the delivered nodes and S-blocks the scaffold does not cover", () => {
    const { plan } = fixture();
    const delivered = new Set(Object.keys(plan.nodes));
    const envs = new Set(plan.env.map((env) => env.id));
    expect(scaffoldCoverageGaps(plan, { nodes: delivered, envs })).toEqual([]);
    delivered.delete("lem:unrelated");
    expect(scaffoldCoverageGaps(plan, { nodes: delivered, envs })).toEqual(["lem:unrelated"]);
  });

  it("does not require a local scaffold tag for a library reuse node", () => {
    const { plan } = fixture();
    Object.assign(plan.nodes["lem:sibling"], {
      disposition: "reuse",
      reuse: "Library.siblingLemma",
      lean_name: "Library.siblingLemma",
    });
    const delivered = new Set(Object.keys(plan.nodes).filter((id) => id !== "lem:sibling"));
    const envs = new Set(plan.env.map((env) => env.id));
    expect(scaffoldCoverageGaps(plan, { nodes: delivered, envs })).toEqual([]);
  });
});

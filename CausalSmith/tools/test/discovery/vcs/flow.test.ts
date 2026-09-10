import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import type { PipelineContext, StateJson } from "../../../src/types.js";
import { CoreSchema, type Core } from "../../../src/discovery/core/schema.js";
import { coreJsonPath } from "../../../src/discovery/stages/d0_core.js";
import { protoCoreJsonPath } from "../../../src/discovery/stages/neg1_2_author.js";
import { workingPath, type WorkingState } from "../../../src/discovery/legacy_working.js";
import { commitGraph, coreMatchesGraph, headGraph, publishCore } from "../../../src/discovery/vcs/commit.js";
import { initStoreFromRun } from "../../../src/discovery/vcs/convert.js";
import { diffGraphs, loadGraph } from "../../../src/discovery/vcs/graph.js";
import { listPrs } from "../../../src/discovery/vcs/pr.js";
import { graphFromCore, renderCore } from "../../../src/discovery/vcs/render.js";
import { ensureStore } from "../../../src/discovery/vcs/round.js";
import { MAIN_REF, VcsStore } from "../../../src/discovery/vcs/store.js";
import { deriveStatus } from "../../../src/discovery/vcs/validity.js";
import { fixtureCore } from "./fixture.js";

// The orchestrator's whole interface: bring a run onto the store, edit core.json,
// commit, look at history, reset. Every mechanical fix is one of these; none of
// them rewinds anything. Plus the migration of what an old run had parked.

describe("vcs flow", () => {
  let repoRoot: string;
  let ctx: PipelineContext;
  const saveWorking = async (w: WorkingState): Promise<void> => {
    await mkdir(path.dirname(workingPath(ctx)), { recursive: true });
    await writeFile(workingPath(ctx), JSON.stringify(w), "utf8");
  };
  beforeEach(async () => {
    repoRoot = await mkdtemp(path.join(os.tmpdir(), "vcs-flow-"));
    ctx = { repoRoot, qid: "stat_vcs_fixture", specialization: "v1", dryRun: false, resume: false };
    const protoPath = protoCoreJsonPath(ctx);
    await mkdir(path.dirname(protoPath), { recursive: true });
    // A run with a frozen proto (all to-prove) and a working state carrying the proofs.
    const proto = fixtureCore();
    for (const s of proto.statements) if (s.status === "proved") { s.status = "to-prove"; delete s.proof_tex; }
    await writeFile(protoPath, JSON.stringify(proto), "utf8");
    await saveWorking({
      round: 3,
      store_format: 2,
      solved: {
        "lem:helper": { proof_tex: "By ass:overlap and the definition of def:class.", snapshot: { stmt: "", defs: {}, assumptions: {} } },
        "thm:main": { proof_tex: "Combine lem:helper with lem:cited.", snapshot: { stmt: "", defs: {}, assumptions: {} } },
      },
    });
  });
  afterEach(async () => { await rm(repoRoot, { recursive: true, force: true }); });

  const readCore = async (): Promise<Core> => CoreSchema.parse(JSON.parse(await readFile(coreJsonPath(ctx), "utf8")));
  const freshState = (): StateJson => ({ flags: {} } as unknown as StateJson);

  it("converts a run so main renders exactly what the old stores published, then edits commit without rewind", async () => {
    const { id: initial, origin } = await initStoreFromRun(ctx);
    expect(origin).toMatch(/round 3/);
    await publishCore(ctx);
    const core = await readCore();
    expect(core.statements.map((s) => s.status)).toEqual(["cited", "proved", "proved"]);
    await expect(initStoreFromRun(ctx)).rejects.toThrow(/already initialized/);

    // Mechanical fix 1: a bibliography row and an edge. No proof moves.
    core.bibliography.push({ key: "N2024", citation: "New (2024)" });
    core.statements[2].depends_on.push("lem:cited");
    await writeFile(coreJsonPath(ctx), JSON.stringify(core), "utf8");
    const store = VcsStore.at(ctx);
    const head1 = await headGraph(store);
    const edited1 = graphFromCore(await readCore(), head1.graph);
    const r1 = await commitGraph({ store, graph: edited1, parents: [head1.head], author: "orchestrator", kind: "direct", message: "bib + edge", expectedHead: head1.head });
    expect(r1.ok).toBe(true);
    await publishCore(ctx);
    expect((await readCore()).statements.map((s) => s.status)).toEqual(["cited", "proved", "proved"]);

    // Mechanical fix 2: a typo in a definition. The lemma and theorem resting on it reopen; nothing else is touched.
    const core2 = await readCore();
    core2.definitions[0].construction = "$\\{P : \\text{ass:overlap holds with margin}\\}$";
    await writeFile(coreJsonPath(ctx), JSON.stringify(core2), "utf8");
    const head2 = await headGraph(store);
    const r2 = await commitGraph({ store, graph: graphFromCore(await readCore(), head2.graph), parents: [head2.head], author: "orchestrator", kind: "direct", message: "def typo", expectedHead: head2.head });
    expect(r2.ok).toBe(true);
    if (!r2.ok) return;
    expect(deriveStatus(r2.graph, "lem:helper")).toBe("to-prove");
    expect(deriveStatus(r2.graph, "thm:main")).toBe("to-prove");
    expect(deriveStatus(r2.graph, "lem:cited")).toBe("cited");
    await publishCore(ctx);
    const published = await readCore();
    expect(published.statements[1].proof_tex).toBeDefined(); // prior progress kept as bytes
    expect(published.statements[1].status).toBe("to-prove");

    // History is complete and a reset is a new commit, never a deletion.
    const history = await store.history((await store.readRef(MAIN_REF))!);
    expect(history.map((c) => c.message)).toEqual(["def typo", "bib + edge", expect.stringMatching(/converted/)]);
    const back = await loadGraph(store, r1.ok ? r1.id : "");
    const r3 = await commitGraph({ store, graph: back, parents: [r2.id], author: "orchestrator", kind: "reset", message: "undo typo", expectedHead: r2.id });
    expect(r3.ok).toBe(true);
    await publishCore(ctx);
    expect((await readCore()).statements.map((s) => s.status)).toEqual(["cited", "proved", "proved"]);
    expect((await store.history((await store.readRef(MAIN_REF))!)).length).toBe(4);
    expect(store.hasCommit(initial)).toBe(true);
  });

  it("detects a working-copy edit even when graph normalization would erase it", () => {
    const graph = graphFromCore(fixtureCore());
    const working = renderCore(graph);
    const headline = working.statements.find((statement) => statement.id === "thm:main")!;
    headline.depends_on = headline.depends_on.filter((dependency) => dependency !== "lem:cited");

    expect(coreMatchesGraph(working, graph)).toBe(false);
    expect(diffGraphs(graph, graphFromCore(working, graph))).toMatchObject({ added: [], removed: [], changed: [], moved: [] });
  });

  it("refuses a commit that breaks the gate and leaves main and core.json untouched", async () => {
    await initStoreFromRun(ctx);
    await publishCore(ctx);
    const store = VcsStore.at(ctx);
    const before = await headGraph(store);
    const core = await readCore();
    core.statements[2].depends_on.push("lem:ghost");
    const result = await commitGraph({ store, graph: graphFromCore(core, before.graph), parents: [before.head], author: "orchestrator", kind: "direct", message: "bad", expectedHead: before.head });
    expect(result.ok).toBe(false);
    if (result.ok) return;
    expect(result.violations.map((v) => v.code)).toContain("V6");
    expect(await store.readRef(MAIN_REF)).toBe(before.head);
    expect(diffGraphs(before.graph, (await headGraph(store)).graph).changed).toEqual([]);
  });

  it("a stale expected head is refused so two writers cannot both advance", async () => {
    await initStoreFromRun(ctx);
    const store = VcsStore.at(ctx);
    const { head, graph } = await headGraph(store);
    const core = renderCore(graph);
    core.tldr = "first writer";
    const a = await commitGraph({ store, graph: graphFromCore(core, graph), parents: [head], author: "orchestrator", kind: "direct", message: "a", expectedHead: head });
    expect(a.ok).toBe(true);
    core.tldr = "second writer, same base";
    await expect(commitGraph({ store, graph: graphFromCore(core, graph), parents: [head], author: "orchestrator", kind: "direct", message: "b", expectedHead: head }))
      .rejects.toThrow(/moved under us/);
  });

  it("migration carries a parked bundle whose symbol deletion an untouched question still uses: the deletion is dropped, the rest lands, nothing is called merged", async () => {
    // The w3 incident (2026-09-06): the bundle deleted a symbol an untouched open question
    // declared, the gate reported the missing symbol ON THE QUESTION, and the whole bundle
    // was reverted and then reported as an empty successful merge.
    const protoPath = protoCoreJsonPath(ctx);
    const proto = JSON.parse(await readFile(protoPath, "utf8")) as Core;
    proto.symbols.push({ name: "I_n", type: "index set", def: "an index set" });
    proto.statements.push({ id: "oeq:untouched", kind: "openendedquestion", statement: "Does the bound hold uniformly?", depends_on: ["ass:overlap"], free_symbols: ["I_n"], status: "to-prove", justification: "j", gap: "g", consumer: "c" });
    await writeFile(protoPath, JSON.stringify(proto), "utf8");
    await saveWorking({
      round: 4, store_format: 2, solved: {},
      proposals: {
        statements: [], definitions: [], proofs: [],
        assumptions: [{ id: "ass:positive-sizes", condition: "every sample size is positive", reason: "needed", standard_or_novel: "novel: new", not_crux: "side condition", free_symbols: [] }],
        coreEdits: [
          { kind: "symbol-delete", name: "I_n", reason: "obsolete", direction: "delete-obsolete" },
          { kind: "bibliography-replace", key: "R1983", proposed: { key: "R1983", citation: "Rosenbaum and Rubin (1983), Biometrika" }, reason: "full citation", direction: "correct" },
        ],
      },
    });
    const store = await ensureStore(ctx, freshState());
    const marker = JSON.parse(await readFile(path.join(store.dir, "legacy_carried.json"), "utf8")) as { notes: string[]; pr_status: string };
    expect(marker.pr_status).toBe("open");
    expect(marker.notes.join("\n")).toMatch(/NOT merged automatically/);
    const [pr] = await listPrs(store, "open");
    expect(pr.dropped.map((d) => d.id)).toEqual(["sym:I_n"]);
    expect(pr.approval.map((a) => a.id)).toEqual(["ass:positive-sizes"]);
    expect(pr.summary.changed).toContain("bib:R1983");
    // Main is untouched until the adjudicator acts; the head keeps everything that survived.
    const head = await loadGraph(store, pr.id);
    expect(head.nodes.has("ass:positive-sizes")).toBe(true);
    expect(head.nodes.has("sym:I_n")).toBe(true);
    // A second entry does not carry again: any marker means done.
    await ensureStore(ctx, freshState());
    expect((await listPrs(store, "open")).length).toBe(1);
  });
});

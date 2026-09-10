// The versioned theorem graph: bringing an existing run onto the store.
//
// The initial commit is the run's assembled core (proto + working, rendered by
// the same `assembleCore` the old stage published through), so the first `main`
// renders byte-for-byte what `core.json` showed. Every statement the old stores
// published as `proved` gets a fresh basis against the converted graph — it is
// valid there by definition — and every resolved open question keeps a tombstone
// so its id stays addressable.
import { existsSync } from "node:fs";
import { assembleCore } from "../core/assemble.js";
import { readTypedCore } from "../core/core_io.js";
import { CoreSchema, type Core } from "../core/schema.js";
import { loadWorkingState } from "../legacy_working.js";
import { protoCoreJsonPath } from "../stages/neg1_2_author.js";
import { coreJsonPath } from "../stages/d0_core.js";
import type { PipelineContext } from "../../types.js";
import { commitGraph, commitOrThrow, headGraph, publishCore } from "./commit.js";
import { blobId as nodeBlobId } from "./node.js";
import { listPrs, mergePr, openPr } from "./pr.js";
import { SolveUnitOutputSchema } from "../solve/schemas.js";
import { writeJsonAtomic, writeTextAtomic } from "../../shared/json_atomic.js";
import { readFile } from "node:fs/promises";
import path from "node:path";
import type { StateJson } from "../../types.js";
import { proposalRevision } from "../proposal_revision.js";
import type { Graph } from "./graph.js";
import { blobId, type NodeBlob, type NodeId } from "./node.js";
import { nodesOfType } from "./graph.js";
import { graphFromCore, normalizeGraph } from "./render.js";
import { MAIN_REF, VcsStore } from "./store.js";

export interface ConversionSource {
  core: Core;
  /** Resolved question id → answer theorem id, with the question's frozen node. */
  tombstones: Array<{ id: NodeId; theorem: NodeId; node: Core["statements"][number] }>;
  origin: string;
}

/** Read the run's D0 artifacts. The published `core.json` (what every reviewer and
 *  F stage read) is the source of truth when present; otherwise the old stores are
 *  assembled through the same render they used to publish through. Resolved
 *  questions come from the working cursor either way. */
export async function conversionSourceFromRun(ctx: PipelineContext): Promise<ConversionSource> {
  const protoPath = protoCoreJsonPath(ctx);
  const corePath = coreJsonPath(ctx);
  const working = existsSync(protoPath) ? await loadWorkingStateTolerant(ctx) : null;
  const tombstones: ConversionSource["tombstones"] = [];
  if (working !== null && existsSync(protoPath)) {
    const proto = await readTypedCore(protoPath);
    for (const [id, resolution] of Object.entries(working.resolved_oeqs ?? {})) {
      const theorem = typeof resolution === "string" ? resolution : resolution.theorem_id;
      const node = proto.statements.find((s) => s.id === id);
      if (node !== undefined) tombstones.push({ id, theorem, node });
    }
  }
  if (existsSync(corePath)) {
    return { core: await readTypedCore(corePath), tombstones, origin: "core.json" + (working !== null ? ` (round ${working.round})` : "") };
  }
  if (!existsSync(protoPath)) throw new Error(`vcs: run has neither core.json nor proto_core.json (${ctx.qid})`);
  const proto = await readTypedCore(protoPath);
  if (working === null) return { core: proto, tombstones: [], origin: "proto_core.json" };
  return { core: CoreSchema.parse(assembleCore(proto, working)), tombstones, origin: `proto_core.json + d0_working.json (round ${working.round})` };
}

/** A corrupt legacy cursor is a note, not a wall: the run is converted from what can
 *  be read and the note lands in the migration marker. */
async function loadWorkingStateTolerant(ctx: PipelineContext): Promise<Awaited<ReturnType<typeof loadWorkingState>>> {
  try {
    return await loadWorkingState(ctx);
  } catch (err) {
    console.warn(`[D0] legacy working cursor unreadable; converting without it: ${err instanceof Error ? err.message : String(err)}`);
    return null;
  }
}

/** Build the graph a conversion source denotes (normalized, bases stamped). */
export function graphFromConversion(source: ConversionSource): Graph {
  const base = graphFromCore(source.core);
  if (source.tombstones.length === 0) return base;
  const nodes = new Map(base.nodes);
  const tree = { ...base.tree };
  let pos = Math.max(0, ...Object.values(tree).map((e) => e.pos)) + 1;
  for (const t of source.tombstones) {
    if (nodes.has(t.id) || !nodes.has(t.theorem)) continue;
    const { status: _s, proof_tex: _p, source: _src, ...body } = t.node;
    const blob: NodeBlob = { node_type: "statement", body: { ...body, resolved_by: t.theorem } };
    nodes.set(t.id, blob);
    tree[t.id] = { blob: blobId(blob), pos: pos++ };
  }
  return normalizeGraph({ tree, nodes });
}

/** Create the store for a run from its existing D0 artifacts. Refuses to overwrite. */
export async function initStoreFromRun(ctx: PipelineContext, source?: ConversionSource): Promise<{ id: string; origin: string }> {
  const store = VcsStore.at(ctx);
  if (store.exists()) throw new Error(`vcs: store already initialized at ${store.dir}`);
  const src = source ?? (await conversionSourceFromRun(ctx));
  const graph = graphFromConversion(src);
  const { id } = await commitOrThrow({
    store,
    graph,
    parents: [],
    author: "converter",
    kind: "initial",
    message: `converted from ${src.origin}`,
    expectedHead: null,
    meta: { origin: src.origin },
    // A published core that already fails a check still gets its store (otherwise
    // the run can never be resumed); the violations ride on the commit and `status`
    // shows them.
    recordViolations: true,
  });
  return { id, origin: src.origin };
}

// -- proposal revision -----------------------------------------------------------------

function proposalRevisionPath(store: VcsStore): string {
  return path.join(store.dir, "proposal_revision");
}

export async function storedProposalRevision(store: VcsStore): Promise<string | null> {
  const p = proposalRevisionPath(store);
  if (!existsSync(p)) return null;
  const value = (await readFile(p, "utf8")).trim();
  return value.length > 0 ? value : null;
}

export async function recordProposalRevision(store: VcsStore, revision: string | undefined): Promise<void> {
  if (revision !== undefined) await writeTextAtomic(proposalRevisionPath(store), `${revision}\n`);
}

/** A D-1.2 re-proposal (new angle/version accepted at D-0.5) replaces the paper: the
 *  new proto becomes main's tree. Proofs of the previous proposal are not carried —
 *  the claim catalogue changed — but stay in history. Returns the new head, or null
 *  when the store already tracks the state's revision. */
export async function reinitializeOnReproposal(ctx: PipelineContext, state: StateJson, store: VcsStore): Promise<string | null> {
  const current = proposalRevision(state);
  const stored = await storedProposalRevision(store);
  if (current === undefined) return null;
  if (stored === null) { await recordProposalRevision(store, current); return null; }
  if (stored === current) return null;
  const protoPath = protoCoreJsonPath(ctx);
  if (!existsSync(protoPath)) {
    console.warn(`[D0] proposal revision moved (${stored} → ${current}) but there is no proto_core.json to re-initialize from; main stays`);
    await recordProposalRevision(store, current);
    return null;
  }
  const { head } = await headGraph(store);
  const result = await commitGraph({
    store, graph: graphFromCore(await readTypedCore(protoPath)), parents: [head], author: "converter", kind: "reset",
    message: `re-proposed: ${stored} → ${current} (new D-1.2 proposal replaces the paper)`, expectedHead: head,
    meta: { proposal_revision: current, previous_revision: stored },
    recordViolations: true,
  });
  if (!result.ok) throw new Error(`vcs: the re-proposed proto could not be committed: ${result.violations.map((v) => `${v.code}@${v.where}: ${v.message}`).join("; ")}`);
  await recordProposalRevision(store, current);
  return result.id;
}

// -- legacy leftovers ---------------------------------------------------------------------

function legacyCarriedPath(store: VcsStore): string {
  return path.join(store.dir, "legacy_carried.json");
}

/** What the old cursor parked that a plain conversion does not render: sealed
 *  residual questions (stamped with an obligation so they are not re-paid) and a
 *  round's un-adjudicated proposals, together with the same-round payloads the old
 *  merge had quarantined (`withheld_content.json`), opened as ONE pull request on
 *  main. The PR is merged only when it needs no verdict and lost nothing; otherwise
 *  it stays open and `pr show` lists every item, drop and rejection. Idempotent
 *  through a marker (any earlier marker counts as done); the notes are for the log. */
export async function carryLegacyLeftovers(ctx: PipelineContext, store: VcsStore): Promise<string[]> {
  const marker = legacyCarriedPath(store);
  if (existsSync(marker)) return [];
  const notes: string[] = [];
  let prId: string | null = null;
  let prStatus: string | null = null;
  const working = existsSync(protoCoreJsonPath(ctx)) ? await loadWorkingStateTolerant(ctx) : null;
  // Whatever happens below, the marker is written: a carry that failed is reported
  // once, with the raw bundle kept beside the PR records, never retried on every entry.
  try {
    await carryOnce(ctx, store, working, notes, (id, status) => { prId = id; prStatus = status; });
  } catch (err) {
    notes.push(`LEGACY CARRY FAILED (not retried; the raw bundle is kept at ${legacyBundlePath(store)}): ${err instanceof Error ? err.message : String(err)}`);
  }
  await writeJsonAtomic(marker, { at: new Date().toISOString(), notes, pr_id: prId, pr_status: prStatus });
  return notes;
}

function legacyBundlePath(store: VcsStore): string {
  return path.join(store.dir, "prs", "legacy.inputs.json");
}

async function carryOnce(
  ctx: PipelineContext,
  store: VcsStore,
  working: Awaited<ReturnType<typeof loadWorkingState>>,
  notes: string[],
  record: (prId: string, status: "open" | "merged") => void,
): Promise<void> {
  if (working !== null) {
    const sealed = Object.keys(working.sealed_open_oeqs ?? {});
    if (sealed.length > 0) {
      const { head, graph } = await headGraph(store);
      const nodes = new Map(graph.nodes);
      const tree = { ...graph.tree };
      const stamped: string[] = [];
      for (const id of sealed) {
        const blob = nodes.get(id);
        if (blob?.node_type !== "statement" || blob.body.resolved_by !== undefined || blob.body.kind !== "openendedquestion" || blob.body.obligation !== undefined) continue;
        const next: NodeBlob = { node_type: "statement", body: { ...blob.body, obligation: {
          what_is_open: "the question itself (an acknowledged residual, sealed before the graph store)",
          obstruction: "left open by the orchestrator; not dispatched again unless a directive names it",
          attempted: "sealed",
        } } };
        nodes.set(id, next);
        tree[id] = { ...tree[id], blob: nodeBlobId(next) };
        stamped.push(id);
      }
      if (stamped.length > 0) {
        const result = await commitGraph({ store, graph: { tree, nodes }, parents: [head], author: "converter", kind: "direct", message: `carry ${stamped.length} sealed question(s): ${stamped.join(", ")}`, expectedHead: head });
        if (!result.ok) notes.push(`sealed questions NOT carried (stamping them fails a check): ${result.violations.map((v) => `${v.code}@${v.where}: ${v.message}`).join("; ")}`);
        else { await publishCore(ctx, store); notes.push(`sealed questions carried as obligations: ${stamped.join(", ")}`); }
      }
    }
    const p = working.proposals;
    const raw: Record<string, unknown[]> = {
      proofs: (p?.proofs ?? []).map((x) => ({ id: x.id, proof_tex: x.proof_tex })),
      proposed_statement_changes: p?.statements ?? [],
      proposed_definition_changes: p?.definitions ?? [],
      proposed_assumptions: p?.assumptions ?? [],
      proposed_core_edits: p?.coreEdits ?? [],
      added_lemmas: (p?.citationRevalidations ?? []) as unknown[],
      resolved_oeqs: [], open_obligations: [],
    };
    // Payloads the old merge quarantined in the same round (ownership collisions,
    // cross-unit conflicts). They are ordinary solver output here: the fold drops what
    // conflicts, the checks drop what dangles, the adjudicator sees the rest.
    const withheld = await legacyWithheldPayloads(ctx);
    for (const w of withheld) (raw[w.channel] ??= []).push(w.payload);
    if (withheld.length > 0) notes.push(`${withheld.length} withheld payload(s) folded into the legacy bundle`);
    const count = Object.values(raw).reduce((n, list) => n + list.length, 0);
    if (count > 0) {
      await writeJsonAtomic(legacyBundlePath(store), { round: working.round, bundle: raw });
      const parsed = SolveUnitOutputSchema.safeParse(raw);
      if (!parsed.success) throw new Error(`pending proposals NOT carried (unparseable): ${parsed.error.issues.slice(0, 3).map((i) => `${i.path.join(".")}: ${i.message}`).join("; ")}`);
      const head = (await store.readRef(MAIN_REF))!;
      const targets = new Set<string>([
        ...parsed.data.proofs.map((x) => x.id),
        ...parsed.data.resolved_oeqs.map((x) => x.source_id),
        ...parsed.data.open_obligations.map((x) => x.node_id),
        ...parsed.data.proposed_statement_changes.map((x) => x.id),
        ...parsed.data.added_lemmas.map((x) => x.id),
        ...parsed.data.proposed_core_edits.flatMap((e) => ("id" in e && typeof e.id === "string" ? [e.id] : [])),
      ]);
      const { pr } = await openPr({ store, base: head, round: working.round, submissions: [{ unit: "legacy-proposals", targets: [...targets], output: parsed.data }] });
      const rejected = pr.units.flatMap((u) => u.rejected);
      const lost = pr.dropped.length + rejected.length;
      if (lost > 0) {
        notes.push(`legacy bundle carried as PR ${pr.id.slice(0, 12)} with ${pr.dropped.length} dropped and ${rejected.length} rejected item(s) — ` +
          `NOT merged automatically; review it: d0_vc pr show ${pr.id.slice(0, 12)}`);
        record(pr.id, "open");
      } else if (pr.approval.length === 0) {
        const merged = await mergePr({ store, ctx, pr, verdict: { accept: "all", note: "legacy pending proposals (additive) carried at migration", by: "converter" } });
        if (!merged.ok) { record(pr.id, "open"); notes.push(`legacy bundle PR ${pr.id.slice(0, 12)} could not merge automatically (${merged.unresolved.map((u) => u.id).join(", ") || merged.violations.map((v) => `${v.code}@${v.where}`).join(", ")}); it stays open for the orchestrator`); }
        else { record(pr.id, "merged"); notes.push(`pending proposals carried and merged as ${merged.commit.slice(0, 12)} (+${pr.summary.added.length} −${pr.summary.removed.length} ~${pr.summary.changed.length})`); }
      } else {
        notes.push(`pending proposals carried as PR ${pr.id.slice(0, 12)} (${pr.approval.length} item(s) need a verdict: d0_vc pr show ${pr.id.slice(0, 12)})`);
        record(pr.id, "open");
      }
    }
  }
}

const WITHHELD_CHANNEL: Record<string, string> = {
  "core-edit": "proposed_core_edits", "statement-change": "proposed_statement_changes",
  "definition-change": "proposed_definition_changes", assumption: "proposed_assumptions",
  proof: "proofs", "added-lemma": "added_lemmas", "resolved-oeq": "resolved_oeqs",
  "open-obligation": "open_obligations",
};

/** The old merge's quarantined same-round payloads, when the file is present and
 *  readable. Anything malformed is skipped with a note rather than blocking the run. */
async function legacyWithheldPayloads(ctx: PipelineContext): Promise<Array<{ channel: string; payload: unknown }>> {
  const p = path.join(path.dirname(protoCoreJsonPath(ctx)), "withheld_content.json");
  if (!existsSync(p)) return [];
  let parsed: unknown;
  try {
    parsed = JSON.parse(await readFile(p, "utf8"));
  } catch {
    return [];
  }
  const list = (parsed as { withheld_payloads?: unknown }).withheld_payloads;
  if (!Array.isArray(list)) return [];
  const out: Array<{ channel: string; payload: unknown }> = [];
  for (const item of list) {
    const category = (item as { category?: unknown }).category;
    const payload = (item as { payload?: unknown }).payload;
    const channel = typeof category === "string" ? WITHHELD_CHANNEL[category] : undefined;
    if (channel !== undefined && payload !== undefined) out.push({ channel, payload });
  }
  return out;
}

// What a REVISE call carries. A re-plan (F1) and the review of a re-plan (F1.5) each change a
// handful of nodes of a core and a plan that are otherwise settled. A revise prompt carries its
// change block, the AFFECTED nodes in full (`reviseAffectedNodeIds`), one reference line for every
// other node (`nodeReferenceIndex`), and where to look up what the affected set missed
// (`reviseLookupBlock`). A first plan and a first review get everything.

import { existsSync } from "node:fs";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import type { Core } from "../discovery/core/schema.js";
import type { Plan } from "./plan/schema.js";
import { otherTopLevelChanges } from "./core_delta.js";

type Rec = Record<string, unknown>;
type PlanNodes = Pick<Plan, "nodes">;

/** A typed-core node id in free text (a reviewer's finding, a directive). */
const NODE_ID_RE = /\b(?:thm|lem|prop|oeq|conj|def|ass):[a-z0-9-]+/g;

/** The core node ids `texts` name (a correction, a directive, a finding's label), in order. Pure. */
export function namedNodeIds(core: Core, texts: ReadonlyArray<string | null | undefined>): string[] {
  const ids = new Set([...core.assumptions, ...core.definitions, ...core.statements].map((n) => n.id));
  const out = new Set<string>();
  for (const t of texts) {
    for (const m of (t ?? "").match(NODE_ID_RE) ?? []) {
      // `thm:foo-style` names `thm:foo`: drop trailing hyphenated words until an id matches.
      for (let id = m; id.includes(":"); id = id.slice(0, Math.max(id.lastIndexOf("-"), 0))) {
        if (ids.has(id)) { out.add(id); break; }
      }
    }
  }
  return [...out];
}

/**
 * The nodes a revise must have in full: the SEEDS — the nodes its change block names (a core
 * delta, a correction, a directive, a discharged gate) — and the USERS OF A CHANGED PREMISE,
 * closed transitively. When X is an assumption, a definition, or a statement the plan threads as
 * a hypothesis (its entry is a `gate` or has `lean_kind:"assumption"`), every statement with X in
 * its core `depends_on`, every class with X in `by_member_properties` and every construction with
 * X in `inputs` is affected. Whatever X is, every plan entry citing X in `hyps` or `members` is
 * affected. (So a changed atom reaches the classes bundling it, and through them the statements
 * taking those classes.)
 *
 * What the rule deliberately does NOT follow: from a changed ordinary statement to the statements
 * that USE it as a lemma (their plan entries and signatures do not cite it; their proofs are the
 * proof loop's to redo), and from a node to its unchanged prerequisites (the reference index
 * names those). It is a mechanical lower bound: a change whose effect travels by wording alone is
 * not seen, so every revise prompt keeps the agent's duty to trace further, by lookup. Ids that
 * are not core nodes are dropped. Pure.
 */
export function reviseAffectedNodeIds(core: Core, plan: PlanNodes | null, seeds: Iterable<string>): Set<string> {
  const statementIds = new Set(core.statements.map((s) => s.id));
  const nodeIds = new Set([...core.assumptions.map((a) => a.id), ...core.definitions.map((d) => d.id), ...statementIds]);
  const coreUsers = new Map<string, Set<string>>();
  const planUsers = new Map<string, Set<string>>();
  const link = (into: Map<string, Set<string>>, user: string, premise: string): void => {
    if (!nodeIds.has(user) || !nodeIds.has(premise)) return;
    if (!into.has(premise)) into.set(premise, new Set());
    into.get(premise)!.add(user);
  };
  for (const s of core.statements) for (const d of s.depends_on) link(coreUsers, s.id, d);
  for (const d of core.definitions) for (const m of [...(d.by_member_properties ?? []), ...(d.inputs ?? [])]) link(coreUsers, d.id, m);
  for (const [id, entry] of Object.entries(plan?.nodes ?? {})) {
    for (const h of [...(entry.hyps ?? []), ...(entry.members ?? [])]) link(planUsers, id, h);
  }
  const isPremise = (id: string): boolean => {
    if (!statementIds.has(id)) return true;
    const entry = plan?.nodes[id];
    return !!entry && (entry.gate === true || entry.lean_kind === "assumption");
  };
  const affected = new Set<string>();
  const queue = [...seeds].filter((id) => nodeIds.has(id));
  while (queue.length > 0) {
    const id = queue.pop()!;
    if (affected.has(id)) continue;
    affected.add(id);
    for (const u of planUsers.get(id) ?? []) queue.push(u);
    if (isPremise(id)) for (const u of coreUsers.get(id) ?? []) queue.push(u);
  }
  return affected;
}

/** Derived fields of a core record: a change in one alone moves nothing. */
const QUIET_CORE_FIELDS = ["used_by"];

const shape = (x: Rec, quiet: readonly string[]): string =>
  JSON.stringify(Object.fromEntries(Object.entries(x).filter(([k]) => !quiet.includes(k))));

const recs = (x: unknown): Rec[] => (Array.isArray(x) ? (x as Rec[]) : []);

/**
 * The seeds a changed core gives: every node of `cur` that `prev` lacks or records differently
 * (derived fields apart), and for a changed, added or removed SYMBOL — one naming a changed
 * definition (`ref`) counts as changed — that definition and every node that uses the symbol — it is in the node's `free_symbols`, or the node declares
 * none (an absent declaration may use any symbol). The symbols are returned in `symbols`. A
 * removed node has no record left; the statements that cited it changed with it. `prev`/`cur`
 * are cores or prompt views of cores (`formalizationCoreContextValue`). Pure.
 */
export function coreChangeSeeds(prev: unknown, cur: unknown): { nodes: string[]; symbols: string[] } {
  const p = (prev ?? {}) as Rec;
  const c = (cur ?? {}) as Rec;
  const nodes = new Set<string>();
  const curNodes = ["assumptions", "definitions", "statements"].flatMap((key) => recs(c[key]));
  for (const key of ["assumptions", "definitions", "statements"]) {
    const before = new Map(recs(p[key]).map((n) => [String(n.id), shape(n, QUIET_CORE_FIELDS)] as const));
    for (const n of recs(c[key])) if (before.get(String(n.id)) !== shape(n, QUIET_CORE_FIELDS)) nodes.add(String(n.id));
  }
  const before = new Map(recs(p.symbols).map((s) => [String(s.name), s] as const));
  const after = new Map(recs(c.symbols).map((s) => [String(s.name), s] as const));
  const symbols = [...new Set([...before.keys(), ...after.keys()])].filter((name) => {
    const a = before.get(name);
    const b = after.get(name);
    // A symbol naming a changed definition means something else now.
    return !a || !b || shape(a, []) !== shape(b, []) || (typeof b.ref === "string" && nodes.has(b.ref));
  });
  if (symbols.length > 0) {
    for (const name of symbols) {
      const ref = after.get(name)?.ref;
      if (typeof ref === "string") nodes.add(ref);
    }
    for (const n of curNodes) {
      const declared = Array.isArray(n.free_symbols) ? (n.free_symbols as unknown[]) : null;
      if (!declared || symbols.some((name) => declared.includes(name))) nodes.add(String(n.id));
    }
  }
  return { nodes: [...nodes], symbols };
}

/**
 * The plan entries of `cur` that `prev` lacks or records differently: node ids, S-block ids, and
 * `other` when something else of the plan moved (citations, feasibility, a top-level field, an
 * entry or S-block that is gone). Pure.
 */
export function planChangeSeeds(prev: unknown, cur: unknown): { nodes: string[]; envs: string[]; other: boolean } {
  const p = (prev ?? {}) as Rec;
  const c = (cur ?? {}) as Rec;
  const pn = (p.nodes ?? {}) as Record<string, Rec>;
  const cn = (c.nodes ?? {}) as Record<string, Rec>;
  const nodes = Object.entries(cn)
    .filter(([id, entry]) => !pn[id] || shape(pn[id]!, []) !== shape(entry, []))
    .map(([id]) => id);
  const pe = new Map(recs(p.env).map((e) => [String(e.id), shape(e, [])] as const));
  const ce = recs(c.env);
  const envs = ce.filter((e) => pe.get(String(e.id)) !== shape(e, [])).map((e) => String(e.id));
  const gone = Object.keys(pn).some((id) => !(id in cn)) || [...pe.keys()].some((id) => !ce.some((e) => String(e.id) === id));
  const rest = (x: Rec): string => shape(x, ["nodes", "env"]);
  return { nodes, envs, other: gone || rest(p) !== rest(c) };
}

/**
 * One line per core node NOT in `shown` — what a revise needs to REFER to a node it does not
 * carry: `<id> | <what it is> | <lean_kind> <lean_name> | <target_file>` (the plan columns are
 * absent for a node the plan does not map yet). Pure.
 */
export function nodeReferenceIndex(core: Core, plan: PlanNodes | null, shown: ReadonlySet<string>): string[] {
  const line = (id: string, what: string): string | null => {
    if (shown.has(id)) return null;
    const e = plan?.nodes[id];
    return [id, what, ...(e ? [`${e.lean_kind} ${e.lean_name}`, ...(e.target_file ? [e.target_file] : [])] : ["no plan entry"])].join(" | ");
  };
  return [
    ...core.assumptions.map((a) => line(a.id, "assumption")),
    ...core.definitions.map((d) => line(d.id, d.by_member_properties ? "class" : "construction")),
    ...core.statements.map((s) => line(s.id, s.kind)),
  ].filter((l): l is string => l !== null);
}

/** The reply marker under which an agent names what it looked up beyond the affected set. */
export const BEYOND_SCOPE_KEY = "looked_up_beyond_scope";

/**
 * The block every scoped revise prompt ends its context with: the reference index, where the
 * whole core and plan are, how to look a node up, and the duty to report having done so.
 * `replyField` says where in the reply the report goes. Pure.
 */
export function reviseLookupBlock(args: { index: string[]; shown: number; total: number; corePath: string; planPath: string; replyField: string }): string {
  return [
    `=== EVERY OTHER NODE (${args.total - args.shown} of ${args.total}; reference only) ===`,
    "Unchanged, and not shown in full: `<id> | <what it is> | <lean_kind> <lean_name> | <target_file>`.",
    ...args.index,
    "=== END EVERY OTHER NODE ===",
    "",
    "=== BEYOND THE AFFECTED SET ===",
    "The affected set above was computed mechanically (the nodes the change names and the users of a",
    "changed assumption, definition or threaded hypothesis). It can UNDER-REACH: a change that travels by",
    "meaning rather than by a cited id is not in it. Trace the change yourself, and when it reaches a node",
    "not shown in full, look that node up BY ID — search the file for the id and read only that record;",
    "never read either file whole:",
    `  typed core (READ-ONLY): ${args.corePath}`,
    `  plan: ${args.planPath}`,
    `Then SAY SO: list every node you had to look up in ${args.replyField} (an empty list when the set sufficed).`,
    "=== END BEYOND THE AFFECTED SET ===",
    "",
  ].join("\n");
}

/** The ids a reply reports under `BEYOND_SCOPE_KEY` (a JSON field, or the same word in prose
 *  followed by a list); empty when it reports none. Pure. */
export function beyondScopeReported(reply: string): string[] {
  const m = new RegExp(`${BEYOND_SCOPE_KEY}[\\\\"\`]*\\s*[:=]?\\s*\\[([^\\]]*)\\]`).exec(reply);
  if (!m) return [];
  return [...new Set(m[1]!.match(/[A-Za-z]+:[A-Za-z0-9_.-]+|S[0-9]+/g) ?? [])];
}

/** The plan (as written) and the core view (`formalizationCoreContextValue`) a stage last carried
 *  through — what F1.5 passed, what F2 scaffolded. The next revise diffs against it. */
export interface ReviseBasis {
  plan: unknown;
  core: unknown;
  /** F2 only: the persistent scaffold directive in force when the scaffold was made. */
  directive?: string | null;
}

/**
 * A change since `basis` that no node carries: a plan-level field or a removed entry, a top-level
 * field of the core, or the sampling model. A scoped revise or review then reads everything. Pure.
 */
export function movedBeyondNodes(basis: ReviseBasis, planRaw: unknown, coreView: unknown): boolean {
  const setting = (x: unknown): string => JSON.stringify((x as { sampling_model?: unknown } | null)?.sampling_model ?? null);
  return planChangeSeeds(basis.plan, planRaw).other
    || otherTopLevelChanges(basis.core, coreView).length > 0
    || setting(basis.core) !== setting(coreView);
}

export async function writeReviseBasis(file: string, basis: ReviseBasis): Promise<void> {
  await mkdir(path.dirname(file), { recursive: true });
  await writeFile(file, JSON.stringify(basis), "utf8");
}

/** The recorded basis, or null (a run older than the record, or an unreadable file: the stage
 *  then keeps its whole-context prompt). */
export async function readReviseBasis(file: string): Promise<ReviseBasis | null> {
  if (!existsSync(file)) return null;
  try {
    const b = JSON.parse(await readFile(file, "utf8")) as ReviseBasis;
    return b && typeof b === "object" && b.plan && b.core ? b : null;
  } catch {
    return null;
  }
}

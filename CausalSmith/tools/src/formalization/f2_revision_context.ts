import type { Core } from "../discovery/core/schema.js";
import { objIdToNodeId } from "../graph/from_note.js";
import { citationSourceId, type Plan } from "./plan/schema.js";
import { formalizationCoreContextValue, restrictCoreContextValue } from "./core_context.js";
import { namedNodeIds, reviseAffectedNodeIds } from "./revise_scope.js";

export const F2_REVISION_TARGETS_HEADER =
  "Declarations to edit (one obj_id per line, verbatim):";

/** Recover only the exact target block written by the proof-review dispatcher. */
export function revisionTargetsFromRedirect(redirect: string | null | undefined): string[] {
  if (!redirect) return [];
  const lines = redirect.split(/\r?\n/);
  const start = lines.lastIndexOf(F2_REVISION_TARGETS_HEADER);
  if (start < 0) return [];
  const targets: string[] = [];
  for (const line of lines.slice(start + 1)) {
    if (!line.startsWith("- ")) break;
    const target = line.slice(2).trim();
    if (target) targets.push(target);
  }
  return [...new Set(targets)];
}

export interface F2RevisionContext {
  requested_targets: string[];
  resolved_targets: string[];
  /** The core nodes carried in full. */
  shown_nodes: string[];
  plan: Record<string, unknown>;
  core: Record<string, unknown>;
  omitted_counts: {
    plan_nodes: number;
    env_entries: number;
    symbols: number;
    assumptions: number;
    definitions: number;
    statements: number;
    citations: number;
  };
}

/** Where the scaffold on disk does not cover the plan: delivered, locally defined nodes without
 *  an `@node` tag, undelivered nodes that still have one, S-blocks without an `@env` tag. A
 *  scoped revise carries each as a target, so none is left unscaffolded. */
export function scaffoldCoverageGaps(
  plan: Plan,
  tags: { nodes: Set<string>; envs: Set<string> },
): string[] {
  return [
    ...Object.entries(plan.nodes)
      .filter(([id, node]) =>
        node.delivery_status === "undelivered" ? tags.nodes.has(id) : node.disposition !== "reuse" && !tags.nodes.has(id))
      .map(([id]) => id),
    ...plan.env.filter((env) => !tags.envs.has(env.id)).map((env) => env.id),
  ];
}

function envTarget(target: string, envIds: Set<string>): string | null {
  if (envIds.has(target)) return target;
  const compact = target.replace(/-/g, "").toUpperCase();
  return envIds.has(compact) ? compact : null;
}

/**
 * What a targeted F2 revise carries in full. The prior scaffold is on disk and compiles, so the
 * scaffolder needs the records of the declarations it is asked to change, not of the paper:
 *
 * - the flagged nodes and the users of a changed premise (`reviseAffectedNodeIds`, the rule an F1
 *   re-plan uses), with their plan entries and the symbols they use;
 * - for a flagged symbol (`sym:<name>`): its record, the symbols it is defined from, the
 *   definition it names (`ref`) and the S-blocks binding it — the cluster that realizes its space
 *   (the nodes declaring it in `free_symbols` when it has neither);
 * - a flagged S-block, with the symbols it binds;
 * - the nodes `namedIn` (the redirect's text) names, without their users.
 *
 * A target that is no core node (a declaration a proof worker introduced) contributes the core
 * nodes its id names. Every other node is one reference line in the prompt, and the scaffolder
 * looks up what the set missed. Null — the caller keeps the whole plan and core — when no target
 * resolves or the set reaches every node.
 */
export function buildF2RevisionContext(
  core: Core,
  plan: Plan,
  requestedTargets: string[],
  namedIn: ReadonlyArray<string | null | undefined> = [],
): F2RevisionContext | null {
  const requested = [...new Set(requestedTargets.map((t) => t.trim()).filter(Boolean))];
  const nodeIds = new Set([...core.assumptions, ...core.definitions, ...core.statements].map((n) => n.id));
  const envIds = new Set(plan.env.map((entry) => entry.id));
  const symbolByName = new Map(core.symbols.map((symbol) => [symbol.name, symbol] as const));
  const leanNameToId = new Map(Object.entries(plan.nodes).map(([id, entry]) => [entry.lean_name, id] as const));

  const seeds = new Set<string>();
  const context = new Set<string>(namedNodeIds(core, namedIn));
  const shownSymbols = new Set<string>();
  const shownEnvs = new Set<string>();
  const resolved: string[] = [];
  for (const target of requested) {
    if (target.startsWith("sym:") && symbolByName.has(target.slice(4))) {
      const name = target.slice(4);
      shownSymbols.add(name);
      const ref = symbolByName.get(name)!.ref;
      const binding = plan.env.filter((env) => env.binds_symbols.includes(name));
      if (ref && nodeIds.has(ref)) context.add(ref);
      for (const env of binding) shownEnvs.add(env.id);
      if (!(ref && nodeIds.has(ref)) && binding.length === 0) {
        for (const node of [...core.assumptions, ...core.definitions, ...core.statements]) {
          if (node.free_symbols?.includes(name)) context.add(node.id);
        }
      }
      resolved.push(target);
      continue;
    }
    const env = envTarget(target, envIds);
    if (env) {
      shownEnvs.add(env);
      resolved.push(env);
      continue;
    }
    const direct = [target, objIdToNodeId(target), leanNameToId.get(target)].find((id) => id && nodeIds.has(id));
    const named = direct ? [direct] : namedNodeIds(core, [target]);
    for (const id of named) seeds.add(id);
    resolved.push(...named);
  }
  if (resolved.length === 0) return null;

  const shown = reviseAffectedNodeIds(core, plan, seeds);
  for (const id of context) shown.add(id);
  if (shown.size >= nodeIds.size) return null;

  for (const env of plan.env) if (shownEnvs.has(env.id)) for (const name of env.binds_symbols) shownSymbols.add(name);
  const view = formalizationCoreContextValue(core);
  const cut = restrictCoreContextValue(view, shown);
  for (const symbol of cut.symbols as Array<{ name: string }>) shownSymbols.add(symbol.name);
  for (let grew = true; grew; ) {
    grew = false;
    for (const name of [...shownSymbols]) {
      for (const ref of symbolByName.get(name)?.refs ?? []) {
        if (!shownSymbols.has(ref)) { shownSymbols.add(ref); grew = true; }
      }
    }
  }

  const selectedPlanNodes = Object.fromEntries(Object.entries(plan.nodes).filter(([id]) => shown.has(id)));
  const citedIds = new Set(
    Object.values(selectedPlanNodes).map((entry) => citationSourceId(entry.source)).filter((id): id is string => !!id),
  );
  const selectedCitations = plan.citations.filter((citation) => citedIds.has(citation.id));
  const count = (list: unknown): number => (Array.isArray(list) ? list.length : 0);
  return {
    requested_targets: requested,
    resolved_targets: [...new Set(resolved)],
    shown_nodes: [...shown],
    plan: {
      qid: plan.qid,
      ...(plan.specialization ? { specialization: plan.specialization } : {}),
      ...(plan.cluster ? { cluster: plan.cluster } : {}),
      ...(plan.lean_subdir ? { lean_subdir: plan.lean_subdir } : {}),
      env: plan.env.filter((entry) => shownEnvs.has(entry.id)),
      nodes: selectedPlanNodes,
      citations: selectedCitations,
      ...(plan.feasibility ? { feasibility: plan.feasibility } : {}),
    },
    core: {
      ...cut,
      symbols: core.symbols.filter((symbol) => shownSymbols.has(symbol.name)),
      ...(core.sampling_model ? { sampling_model: core.sampling_model } : {}),
      ...(core.estimand_functional ? { estimand_functional: core.estimand_functional } : {}),
      target_estimand: core.target_estimand,
    },
    omitted_counts: {
      plan_nodes: Object.keys(plan.nodes).length - Object.keys(selectedPlanNodes).length,
      env_entries: plan.env.length - shownEnvs.size,
      symbols: core.symbols.length - shownSymbols.size,
      assumptions: core.assumptions.length - count(cut.assumptions),
      definitions: core.definitions.length - count(cut.definitions),
      statements: core.statements.length - count(cut.statements),
      citations: plan.citations.length - selectedCitations.length,
    },
  };
}

/** One line per S-block a revise does not carry: `<id> | <world> | binds <symbols> | <reuse>`. */
export function envReferenceIndex(plan: Plan, shown: ReadonlySet<string>): string[] {
  return plan.env
    .filter((entry) => !shown.has(entry.id))
    .map((entry) => [entry.id, entry.world, `binds ${entry.binds_symbols.join(", ") || "no symbol"}`, entry.reuse ?? entry.disposition].join(" | "));
}

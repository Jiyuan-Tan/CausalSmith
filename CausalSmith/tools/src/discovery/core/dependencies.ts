import type { Core, CoreStatement } from "./schema.js";
import { extractNodeRefs } from "./node_ids.js";

/** Add every literal, existing node citation in a claim or proof to the statement's
 * direct dependencies. This must run after OEQ replacement because replacement
 * theorems are assembled after the first solver-output wiring pass. */
export function wireStatementProofDependencies(core: Core): void {
  const allNodeIds = new Set([
    ...core.assumptions.map((a) => a.id),
    ...core.definitions.map((d) => d.id),
    ...core.statements.map((s) => s.id),
  ]);
  const stmtIds = new Set(core.statements.map((s) => s.id));
  const openQuestionIds = new Set(core.statements.filter((s) => s.kind === "openendedquestion").map((s) => s.id));
  const depsById = new Map(core.statements.map((s) => [s.id, new Set(s.depends_on ?? [])] as const));
  /** Would adding `from → to` close a cycle? (i.e. is `from` already reachable from `to`?) */
  const wouldCycle = (from: string, to: string): boolean => {
    if (!stmtIds.has(to)) return false; // only statement→statement edges can cycle
    const seen = new Set<string>();
    const stack = [to];
    while (stack.length > 0) {
      const cur = stack.pop()!;
      if (cur === from) return true;
      if (seen.has(cur)) continue;
      seen.add(cur);
      for (const next of depsById.get(cur) ?? []) stack.push(next);
    }
    return false;
  };
  for (const statement of core.statements) {
    const dependencies = depsById.get(statement.id)!;
    for (const id of extractNodeRefs(`${statement.statement}\n${statement.proof_tex ?? ""}`)) {
      if (id === statement.id || !allNodeIds.has(id)) continue;
      // An open question named in prose is a workflow object, not evidence. Keep an
      // explicitly declared edge, but never infer one merely from a diagnostic mention.
      if (openQuestionIds.has(id) && !dependencies.has(id)) continue;
      // Prose citation is a WEAK signal — "the dual of lem:a" in lem:a's own counterpart
      // is a mention, not a dependency. Since this pass now matches case-insensitively
      // and includes `oeq:`, it discovers strictly more citations than before, and a
      // mutual pair of prose mentions would introduce a cycle that gate.ts reports as a
      // G4 violation on a core that previously passed. An inferred edge is never worth
      // breaking the graph over: skip it and leave the explicit `depends_on` authoritative.
      if (wouldCycle(statement.id, id)) continue;
      dependencies.add(id);
    }
    statement.depends_on = [...dependencies];
  }
}

/** Rebuild assumption reverse edges from the FINAL graph. Class definitions
 * declare membership structurally; constructed definitions may also cite an
 * assumption id literally in their formula (for example a target-law premise).
 * Both are direct definition consumers, alongside statement depends_on edges. */
export function rebuildAssumptionUsedBy(core: Core, carriedStatements: readonly CoreStatement[] = []): void {
  const directUsers = new Map(core.assumptions.map((a) => [a.id, new Set<string>()] as const));
  const frozenStatementIds = new Set(core.statements.map((statement) => statement.id));
  // Agent-added proved nodes live only in the incremental working cursor until the
  // final core is assembled.  Rebuilding from the frozen proto alone silently drops
  // their reverse edges after an unrelated statement deletion.  A frozen statement
  // remains authoritative for a same-id carried snapshot, which may be stale after a
  // claim edit and must not contribute old dependencies.
  const statements = [
    ...core.statements,
    ...carriedStatements.filter((statement) => !frozenStatementIds.has(statement.id)),
  ];
  for (const statement of statements) {
    for (const dependency of statement.depends_on ?? []) directUsers.get(dependency)?.add(statement.id);
  }
  for (const definition of core.definitions) {
    for (const dependency of definition.by_member_properties ?? []) directUsers.get(dependency)?.add(definition.id);
    for (const input of definition.inputs ?? []) {
      for (const cited of extractNodeRefs(input)) directUsers.get(cited)?.add(definition.id);
    }
    for (const cited of extractNodeRefs(definition.construction)) directUsers.get(cited)?.add(definition.id);
  }
  for (const assumption of core.assumptions) {
    const users = [...(directUsers.get(assumption.id) ?? [])].sort();
    if (users.length === 0) delete assumption.used_by;
    else assumption.used_by = users;
  }
}

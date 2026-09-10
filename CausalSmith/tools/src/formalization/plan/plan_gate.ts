// The F1 plan gate (CausalSmith/doc/research/F1_F2_PLAN_REDESIGN.md §7).
//
// Mechanical, no LLM. Runs on the plan right after F1 (self-check), as F1.5's
// pre-review lint, and after F2's sync-back. Enforces the one-to-one invariant —
// every core node maps to exactly one Lean object, no orphan Lean — plus kind/
// member/hyp consistency. A whole class of plan defects never reaches the
// reuse-soundness reviewer. The prose-faithfulness checks of the old F1.5
// (F/Q/N/L/P) are retired; H/U/X survive here as P2/P4/P7.
import type { Core } from "../../discovery/core/schema.js";
import { coreNodeIds } from "../../discovery/core/schema.js";
import { buildDagFromCore } from "../../discovery/core/dag.js";
import type { ExtractedDecl } from "../../graph/extractor.js";
import type { FormalizationGraph } from "../../graph/types.js";
import { PlanSchema, deriveFeasibility, type Plan } from "./schema.js";

export type PlanGateCode =
  | "schema"
  | "P1" // coverage
  | "P2" // member consistency
  | "P3" // kind consistency
  | "P4" // hyp closure
  | "P5" // reuse existence
  | "P6" // module resolution
  | "P7" // orphan Lean (emitted-tag correspondence)
  | "P8" // derived-feasibility consistency
  | "P9" // cited mapping (D0 status:"cited" ↔ gate_class:"cited"; source resolution)
  | "P10"; // undelivered guard (secondary theorem or cited node only; never load-bearing)

export interface PlanGateViolation {
  code: PlanGateCode;
  where: string;
  message: string;
}

export interface PlanGateResult {
  ok: boolean;
  violations: PlanGateViolation[];
}

export interface PlanGateOptions {
  /** Library-index decl names; when present, enables P5 (reuse existence). */
  knownDecls?: Set<string>;
  /** Importable module paths; when present, P6 requires membership (else format-only). */
  knownModules?: Set<string>;
  /** Tags parsed from emitted Lean (`-- @node` / `-- @env`); enables P7. F2 only. */
  leanTags?: { nodes: Set<string>; envs: Set<string> };
  /** All emitted Lean declaration names. Catches stale untagged declarations for an
   * undelivered plan node, which tag-only P7 cannot see. */
  leanDeclNames?: Set<string>;
  /** Formalization graph captured before F2. Enables the narrow P7 exemption for
   * exact, already-present agent-introduced helpers that intentionally have no plan node. */
  preF2Graph?: FormalizationGraph;
  /** Declarations extracted from the emitted Lean. Required with `preF2Graph` to
   * verify that an exempt helper is still linked to the same declaration. */
  annotatedDecls?: ExtractedDecl[];
  /** Declarations snapshotted from disk immediately before the F2 worker ran. A
   * plan-less helper is preserved only when its emitted declaration is byte-for-byte
   * identical at the extractor level; graph review hashes can be stale across parser
   * upgrades and therefore are not an adequate pre-image. */
  preF2AnnotatedDecls?: ExtractedDecl[];
  /** Final delivery audit only: permit a non-cited secondary omission after that
   * caller has required and will validate dual-model evidence receipts. */
  allowReviewedSecondaryUndelivered?: boolean;
}

const MODULE_RE = /^[A-Z][A-Za-z0-9_]*(\.[A-Za-z0-9_]+)*$/;

function isDirectCanonicalMetadataPayload(decl: ExtractedDecl | undefined): boolean {
  if (!decl?.sourceText) return false;
  const cut = decl.sourceText.indexOf(":=");
  if (cut < 0) return false;
  // The extractor bounds declarations at the next declaration/tag. For the final
  // declaration in a namespace, that can leave the namespace-closing `end ...`
  // attached to sourceText even though it is not part of the definition body.
  const body = decl.sourceText.slice(cut + 2).trim()
    .replace(/\n\s*end(?:\s+[A-Za-z0-9_.]+)?\s*$/, "")
    .trim();
  const leanString = `"(?:\\\\.|[^"\\\\])*"`;
  const items = `(?:${leanString}(?:\\s*,\\s*${leanString})*\\s*,?)?`;
  if (/\b_root_\.String\b/.test(decl.statement) && !/\b_root_\.(?:List|Array)\b/.test(decl.statement)) {
    return new RegExp(`^${leanString}$`, "s").test(body);
  }
  if (/\b_root_\.List\s+_root_\.String\b/.test(decl.statement)) {
    return new RegExp(`^\\[\\s*${items}\\s*\\]$`, "s").test(body);
  }
  if (/\b_root_\.Array\s+_root_\.String\b/.test(decl.statement)) {
    return new RegExp(`^#\\[\\s*${items}\\s*\\]$`, "s").test(body);
  }
  return false;
}

export function runPlanGate(planInput: unknown, core: Core, opts: PlanGateOptions = {}): PlanGateResult {
  const violations: PlanGateViolation[] = [];

  const parsed = PlanSchema.safeParse(planInput);
  if (!parsed.success) {
    for (const issue of parsed.error.issues) {
      violations.push({ code: "schema", where: issue.path.join(".") || "<root>", message: issue.message });
    }
    return { ok: false, violations };
  }
  const plan: Plan = parsed.data;
  const dag = buildDagFromCore(core);
  const nodeIds = coreNodeIds(core);
  const symbolNames = new Set(core.symbols.map((s) => s.name));
  const classIds = new Set([...dag.kindOf].filter(([, k]) => k === "definition-class").map(([id]) => id));
  const assumptionIds = new Set([...dag.kindOf].filter(([, k]) => k === "assumption").map(([id]) => id));
  const gateIds = new Set(Object.entries(plan.nodes).filter(([, n]) => n.gate).map(([id]) => id));

  // P1: coverage. nodes keys == core node ids; symbols all bound by some S-block.
  const planNodeKeys = new Set(Object.keys(plan.nodes));
  for (const id of nodeIds) {
    if (!planNodeKeys.has(id)) violations.push({ code: "P1", where: id, message: `core node has no plan entry` });
  }
  for (const id of planNodeKeys) {
    if (!nodeIds.has(id)) violations.push({ code: "P1", where: id, message: `plan node is not a core node id` });
  }
  const boundSymbols = new Set<string>();
  for (const e of plan.env) {
    for (const s of e.binds_symbols) {
      boundSymbols.add(s);
      if (!symbolNames.has(s)) violations.push({ code: "P1", where: e.id, message: `binds unknown symbol '${s}'` });
    }
  }
  for (const s of symbolNames) {
    if (!boundSymbols.has(s)) violations.push({ code: "P1", where: `symbol:${s}`, message: `symbol bound by no S-block` });
  }

  // P3: kind consistency (per node id whose plan entry exists).
  for (const [id, node] of Object.entries(plan.nodes)) {
    const kind = dag.kindOf.get(id);
    if (kind === undefined) continue; // already flagged by P1
    const coreStmt = kind === "statement" ? core.statements.find((s) => s.id === id) : undefined;
    const want =
      // A core assumption is normally `assumption`, but may be DISCHARGED to a proved
      // `lemma`/`theorem` (substrate-fact discharge) — allow all three for assumptions.
      kind === "assumption" ? ["assumption", "lemma", "theorem"]
      : kind === "definition-class" ? ["structure"]
      : kind === "definition-construction" ? ["def"]
      : coreStmt && node.gate
        ? node.gate_class === "cited"
          ? (coreStmt.source?.carrier ?? "logical-claim") === "bibliographic-metadata" ? ["def"] : ["assumption"]
          : ["assumption"]
      : coreStmt?.kind === "openendedquestion" ? ["def"] // solved OEQs are replaced by thm: nodes at D0; only unresolved OEQs can reach F1.
      : ["theorem", "lemma"]; // statement
    if (!want.includes(node.lean_kind)) {
      violations.push({ code: "P3", where: id, message: `lean_kind '${node.lean_kind}' invalid for core ${kind} (expected ${want.join("|")})` });
    }
  }

  // P2: member consistency. A class node's `members` must equal the core's
  // by_member_properties for that class; every member is an assumption id.
  for (const classId of classIds) {
    const node = plan.nodes[classId];
    if (!node) continue;
    const coreMembers = new Set(dag.classMembers.get(classId) ?? []);
    const planMembers = new Set(node.members ?? []);
    for (const m of coreMembers) {
      if (!planMembers.has(m)) violations.push({ code: "P2", where: classId, message: `plan omits core member '${m}'` });
    }
    for (const m of planMembers) {
      if (!coreMembers.has(m)) violations.push({ code: "P2", where: classId, message: `plan lists non-member '${m}'` });
      else if (!assumptionIds.has(m)) violations.push({ code: "P2", where: classId, message: `member '${m}' is not an assumption` });
    }
  }

  // P4: declared-hyp consistency. Only theorem/lemma consumers may carry hyps at all.
  // Each declared top-level hyp must be an assumption, class, or logical gate in
  // depends_on. Do not infer the converse from the dependency DAG: a core assumption
  // may occur under a quantified implication in the theorem conclusion, so requiring
  // every assumption dependency here as a top-level hyp changes a faithful statement.
  // F2.5 compares the emitted Lean statement with the frozen note and remains the
  // authoritative completeness check.
  for (const [id, candidate] of Object.entries(plan.nodes)) {
    if ((candidate.hyps?.length ?? 0) === 0) continue;
    if (candidate.lean_kind !== "theorem" && candidate.lean_kind !== "lemma") {
      violations.push({ code: "P4", where: id, message: `lean_kind '${candidate.lean_kind}' cannot carry hyps` });
    } else if (!core.statements.some((statement) => statement.id === id)) {
      violations.push({ code: "P4", where: id, message: `only a core statement mapped to theorem/lemma may carry hyps` });
    }
  }
  for (const s of core.statements) {
    const node = plan.nodes[s.id];
    if (!node) continue;
    const logicalCitedDeps = s.depends_on.filter((dep) => {
      const cited = core.statements.find((candidate) => candidate.id === dep && candidate.status === "cited");
      return !!cited && (cited.source?.carrier ?? "logical-claim") === "logical-claim";
    });
    if (node.lean_kind !== "theorem" && node.lean_kind !== "lemma") {
      for (const dep of logicalCitedDeps) {
        violations.push({ code: "P4", where: s.id, message: `logical cited dep '${dep}' requires a theorem/lemma consumer with an explicit hyp` });
      }
      continue;
    }
    const hyps = new Set(node.hyps ?? []);
    const depSet = new Set(s.depends_on);
    for (const h of hyps) {
      if (!depSet.has(h)) violations.push({ code: "P4", where: s.id, message: `hyp '${h}' is not in depends_on` });
      else if (!assumptionIds.has(h) && !classIds.has(h) && !gateIds.has(h)) {
        violations.push({ code: "P4", where: s.id, message: `hyp '${h}' is neither an assumption nor a class (cannot be a hypothesis)` });
      } else if (gateIds.has(h)) {
        const citedGate = core.statements.find((candidate) => candidate.id === h && candidate.status === "cited");
        if (citedGate && (citedGate.source?.carrier ?? "logical-claim") === "bibliographic-metadata") {
          violations.push({ code: "P4", where: s.id, message: `bibliographic metadata '${h}' cannot be a logical hyp` });
        }
      }
    }
    // A logical cited statement is a borrowed proposition and must surface explicitly
    // in every direct consumer. Bibliographic metadata is deliberately non-logical and
    // is never a theorem hypothesis even when the core uses it for comparative framing.
    for (const dep of logicalCitedDeps) {
      const citedPlanNode = plan.nodes[dep];
      if (citedPlanNode?.citation_discharged === true &&
          (citedPlanNode.lean_kind === "lemma" || citedPlanNode.lean_kind === "theorem")) continue;
      if (!hyps.has(dep)) {
        violations.push({ code: "P4", where: s.id, message: `logical cited dep '${dep}' must be an explicit hyp` });
      }
    }
  }

  // P5: reuse existence (optional — needs the library index).
  if (opts.knownDecls) {
    const checkReuse = (where: string, decl: string | null | undefined) => {
      if (decl && !opts.knownDecls!.has(decl)) violations.push({ code: "P5", where, message: `reuse decl '${decl}' not found in library index` });
    };
    for (const e of plan.env) checkReuse(e.id, e.disposition === "reuse" ? e.reuse : null);
    for (const [id, n] of Object.entries(plan.nodes)) checkReuse(id, n.disposition === "reuse" ? n.reuse : null);
  }

  // P6: module resolution. Format always; membership when knownModules supplied.
  const checkModules = (where: string, mods: string[]) => {
    for (const m of mods) {
      if (!MODULE_RE.test(m)) violations.push({ code: "P6", where, message: `module '${m}' is not a valid module path` });
      else if (opts.knownModules && !opts.knownModules.has(m)) violations.push({ code: "P6", where, message: `module '${m}' does not resolve` });
    }
  };
  for (const e of plan.env) checkModules(e.id, e.modules);
  for (const [id, n] of Object.entries(plan.nodes)) checkModules(id, n.modules);

  // P7: orphan Lean — emitted tags correspond exactly to plan keys (F2 only).
  if (opts.leanTags) {
    const envIds = new Set(plan.env.map((e) => e.id));
    const preF2Nodes = new Map(opts.preF2Graph?.nodes.map((node) => [node.id, node]) ?? []);
    const extractedByNode = new Map<string, ExtractedDecl[]>();
    for (const decl of opts.annotatedDecls ?? []) {
      const decls = extractedByNode.get(decl.nodeId) ?? [];
      decls.push(decl);
      extractedByNode.set(decl.nodeId, decls);
    }
    const preF2ExtractedByNode = new Map<string, ExtractedDecl[]>();
    for (const decl of opts.preF2AnnotatedDecls ?? []) {
      const decls = preF2ExtractedByNode.get(decl.nodeId) ?? [];
      decls.push(decl);
      preF2ExtractedByNode.set(decl.nodeId, decls);
    }
    const sameExtractedDecl = (a: ExtractedDecl, b: ExtractedDecl): boolean =>
      a.nodeId === b.nodeId &&
      a.declKind === b.declKind &&
      a.declName === b.declName &&
      a.namespace === b.namespace &&
      a.file === b.file &&
      a.statement === b.statement &&
      a.hasSorry === b.hasSorry;
    const isExactPreservedPreF2Helper = (id: string): boolean => {
      const node = preF2Nodes.get(id);
      const decls = extractedByNode.get(id) ?? [];
      const preF2Decls = preF2ExtractedByNode.get(id) ?? [];
      if (
        (node?.kind !== "lemma" && node?.kind !== "definition") ||
        node.provenance !== "agent-introduced" ||
        node.proof.state !== "complete" ||
        node.proof.sorry_count !== 0 ||
        node.review.status === "drift" ||
        node.lean.decl_name === null ||
        node.lean.file === null ||
        decls.length !== 1 ||
        preF2Decls.length !== 1
      ) return false;
      const decl = decls[0];
      const preF2Decl = preF2Decls[0];
      return !decl.hasSorry &&
        decl.declName === node.lean.decl_name &&
        decl.file === node.lean.file &&
        sameExtractedDecl(decl, preF2Decl);
    };
    for (const t of opts.leanTags.nodes) {
      if (!planNodeKeys.has(t) && !isExactPreservedPreF2Helper(t)) {
        violations.push({ code: "P7", where: t, message: `emitted Lean tags '@node ${t}' but no plan entry or exact completed pre-F2 helper` });
      }
    }
    for (const id of planNodeKeys) {
      const undelivered = plan.nodes[id]?.delivery_status === "undelivered";
      if (undelivered && opts.leanTags.nodes.has(id)) {
        violations.push({ code: "P7", where: id, message: `undelivered node must not emit an '@node' Lean declaration` });
      } else if (!undelivered && !opts.leanTags.nodes.has(id)) {
        violations.push({ code: "P7", where: id, message: `delivered plan node has no emitted '@node' tag` });
      }
    }
    if (opts.leanDeclNames) {
      const names = new Set<string>();
      for (const name of opts.leanDeclNames) {
        names.add(name);
        names.add(name.split(".").at(-1) ?? name);
      }
      for (const id of planNodeKeys) {
        const node = plan.nodes[id];
        if (node.delivery_status !== "undelivered") continue;
        const shortName = node.lean_name.split(".").at(-1) ?? node.lean_name;
        if (names.has(node.lean_name) || names.has(shortName)) {
          violations.push({ code: "P7", where: id, message: `undelivered node still has Lean declaration '${node.lean_name}' (tagged or untagged)` });
        }
      }
    }
    for (const t of opts.leanTags.envs) {
      if (!envIds.has(t)) violations.push({ code: "P7", where: t, message: `emitted Lean tags '@env ${t}' but no S-block` });
    }
    for (const id of envIds) {
      if (!opts.leanTags.envs.has(id)) violations.push({ code: "P7", where: id, message: `planned S-block has no emitted '@env' tag` });
    }
  }

  // P8: stored feasibility must match the derived value.
  if (plan.feasibility && plan.feasibility !== deriveFeasibility(plan)) {
    violations.push({ code: "P8", where: "<root>", message: `feasibility '${plan.feasibility}' disagrees with derived '${deriveFeasibility(plan)}'` });
  }
  // Paper-owned work cannot leave F1 as an assumed or omitted proof obligation.
  // Only an explicit external gate may use the substrate-build checkpoint; all
  // other delivered define-local nodes must proceed to F2–F4, however difficult.
  for (const [id, node] of Object.entries(plan.nodes)) {
    if (
      node.disposition === "define-local" &&
      node.defer_tier &&
      !node.gate
    ) {
      violations.push({
        code: "P8",
        where: id,
        message: "paper-owned proved/to-prove statement or support node cannot be defer_tier without an external gate; keep it in the F2–F4 proof scope",
      });
    }
  }
  for (const statement of core.statements) {
    const node = plan.nodes[statement.id];
    if (node?.gate && statement.status !== "cited") {
      violations.push({
        code: "P8",
        where: statement.id,
        message: `paper-owned core statement with status '${statement.status}' cannot be converted into a planner-authored external gate`,
      });
    }
  }
  for (const [id, node] of Object.entries(plan.nodes)) {
    if (node.gate && !core.statements.some((statement) => statement.id === id)) {
      violations.push({
        code: "P8",
        where: id,
        message: "gate:true is legal only for a core statement with frozen external provenance",
      });
    }
  }

  // P9: cited mapping. A D0 `status:"cited"` statement starts BORROWED (D0 chose not to
  // prove it). A mathematical cited claim is represented by a `gate_class:"cited"`
  // Prop assumption; a bibliographic scope/provenance record uses a source-reviewed non-Prop `def`
  // rather than a logical premise.
  // The supported discharge path may later replace that gate with an exact proved
  // lemma/theorem while retaining `source` as provenance. Do not force such a proved node
  // back into an assumption: gate.ts --discharge deliberately removes the gate keys and
  // reopens every consumer for F2.5/F4 review. Conversely, a non-gate `assumption` is not a
  // discharge and remains forbidden. Only the two discharge channels (bin/gate.ts --discharge
  // and the substrate-built application in stage1.ts) stamp `citation_discharged:true`, so a
  // fresh F1 plan cannot present the discharged shape. Every node `source` must resolve to citations[].
  const citationIds = new Set(plan.citations.map((c) => c.id));
  for (const s of core.statements) {
    const node = plan.nodes[s.id];
    if (!node) continue; // P1 already flagged
    if (s.status === "cited") {
      const frozenCarrier = s.source?.carrier ?? "logical-claim";
      const expectedDeferredKind = frozenCarrier === "bibliographic-metadata" ? "def" : "assumption";
      const deferredCitation =
        node.gate && node.gate_class === "cited" && node.lean_kind === expectedDeferredKind;
      const provedCitation =
        frozenCarrier === "logical-claim" &&
        !node.gate && node.gate_class === undefined && node.citation_discharged === true &&
        node.disposition !== "reuse" &&
        (node.lean_kind === "lemma" || node.lean_kind === "theorem");
      if (!deferredCitation && !provedCitation) {
        violations.push({
          code: "P9",
          where: s.id,
          message:
            `core status:"cited" with source.carrier=${frozenCarrier} must map to a gate_class:"cited" ` +
            `${expectedDeferredKind} or to its ` +
            `discharged lemma/theorem form stamped citation_discharged:true by gate.ts --discharge ` +
            `(got lean_kind=${node.lean_kind}, gate=${!!node.gate}, gate_class=${node.gate_class ?? "none"}, ` +
            `citation_discharged=${node.citation_discharged === true}) — re-laundering a citation`,
        });
      }
      // A `reuse` discharge points at a library decl and emits nothing locally.
      if (provedCitation && opts.annotatedDecls && node.disposition !== "reuse") {
        const decls = opts.annotatedDecls.filter((decl) => decl.nodeId === s.id);
        const expectedName = node.lean_name.split(".").at(-1) ?? node.lean_name;
        const exact = decls.length === 1 ? decls[0] : undefined;
        const exactName = exact && (node.lean_name.includes(".")
          ? exact.declName === node.lean_name
          : (exact.declName.split(".").at(-1) ?? exact.declName) === expectedName);
        const exactKind = exact && exact.declKind === node.lean_kind;
        if (!exact || !exactName || !exactKind || exact.hasSorry) {
          violations.push({
            code: "P9",
            where: s.id,
            message:
              `discharged citation must map to exactly one sorry-free emitted ${node.lean_kind} ` +
              `'${node.lean_name}' (found ${decls.length}${exact ? `; decl=${exact.declName}, kind=${exact.declKind}, sorry=${exact.hasSorry}` : ""})`,
          });
        }
      }
      if (deferredCitation && opts.annotatedDecls && node.disposition !== "reuse") {
        const decls = opts.annotatedDecls.filter((decl) => decl.nodeId === s.id);
        const expectedName = node.lean_name.split(".").at(-1) ?? node.lean_name;
        const exact = decls.length === 1 ? decls[0] : undefined;
        const exactName = exact && (node.lean_name.includes(".")
          ? exact.declName === node.lean_name
          : (exact.declName.split(".").at(-1) ?? exact.declName) === expectedName);
        const exactDef = exact?.declKind === "def";
        // Carrier checks are deliberately syntactic and closed-world. In particular, "anything
        // other than the token Prop" is not a metadata type: `Sort 0` and aliases can elaborate
        // to Prop. Metadata therefore uses only the canonical text payloads supported by F2.
        // `Sort 0` is Lean's unshadowable proposition universe syntax. A bare `Prop`
        // identifier can be shadowed by a namespace-local alias and is therefore rejected.
        const isSyntacticProp = !!exact && /:\s*\(*\s*Sort\s+0\s*\)*\s*(?:--[^\n]*)?$/.test(exact.statement.trim());
        const isCanonicalMetadata = !!exact &&
          /:\s*\(*\s*(?:_root_\.String|_root_\.List\s+_root_\.String|_root_\.Array\s+_root_\.String)\s*\)*\s*(?:--[^\n]*)?$/.test(exact.statement.trim());
        const exactCarrier = frozenCarrier === "logical-claim"
          ? isSyntacticProp
          : isCanonicalMetadata && isDirectCanonicalMetadataPayload(exact);
        if (!exact || !exactName || !exactDef || !exactCarrier || exact.hasSorry) {
          violations.push({
            code: "P9",
            where: s.id,
            message:
              `deferred cited ${frozenCarrier} carrier must match one sorry-free emitted def named '${expectedName}' ` +
              `with ${frozenCarrier === "logical-claim" ? "the unshadowable proposition carrier Sort 0" : "a direct literal root-qualified _root_.String/_root_.List _root_.String/_root_.Array _root_.String metadata"} payload ` +
              `(found ${decls.length === 0 ? "none" : decls.map((decl) => `${decl.declKind} ${decl.declName}: ${decl.statement}`).join("; ")})`,
          });
        }
      }
      if (!node.source) {
        violations.push({ code: "P9", where: s.id, message: `cited node must set 'source' to a cite: id` });
      }
    } else if (node.gate_class === "cited") {
      violations.push({ code: "P9", where: s.id, message: `plan marks gate_class:"cited" but core status is '${s.status}' — F1 must not invent a citation` });
    }
  }
  for (const [id, n] of Object.entries(plan.nodes)) {
    if (n.source && !citationIds.has(n.source)) {
      violations.push({ code: "P9", where: id, message: `node 'source' '${n.source}' does not resolve to a citations[] entry` });
    }
  }

  // P10: `undelivered` is a narrow, disclosed presentation status — never a way
  // to hide a headline or a proof dependency. At F1 it is legal only for a cited
  // node: the planner cannot independently certify its own theorem as secondary
  // before the downstream role audit. It must be a leaf with
  // respect to every delivered statement, because a delivered result cannot rely
  // on an object that has no Lean declaration.
  const undeliveredIds = new Set(
    Object.entries(plan.nodes)
      .filter(([, n]) => n.delivery_status === "undelivered")
      .map(([id]) => id),
  );
  for (const id of undeliveredIds) {
    const node = plan.nodes[id];
    const stmt = core.statements.find((s) => s.id === id);
    const cited = !!stmt && stmt.status === "cited" && node.gate && node.gate_class === "cited";
    const reviewedSecondary =
      opts.allowReviewedSecondaryUndelivered === true &&
      stmt?.kind === "theorem" &&
      node.lean_kind === "theorem" &&
      node.delivery_role === "secondary";
    if (!cited && !reviewedSecondary) {
      violations.push({
        code: "P10",
        where: id,
        message:
          `F1 may mark only a cited node undelivered; paper-owned secondary classification requires downstream independent review ` +
          `(got kind=${stmt?.kind ?? "non-statement"}, role=${node.delivery_role ?? "none"}, cited=${cited})`,
      });
    }
    if (!node.delivery_reason) {
      violations.push({ code: "P10", where: id, message: `undelivered node must disclose a nonempty delivery_reason` });
    }
  }
  const statementById = new Map(core.statements.map((s) => [s.id, s] as const));
  for (const s of core.statements) {
    if (undeliveredIds.has(s.id)) continue;
    const seen = new Set<string>();
    const stack = [...s.depends_on];
    while (stack.length > 0) {
      const dep = stack.pop()!;
      if (seen.has(dep)) continue;
      seen.add(dep);
      if (undeliveredIds.has(dep)) {
        violations.push({
          code: "P10",
          where: s.id,
          message: `delivered statement transitively depends on undelivered node '${dep}'`,
        });
        break;
      }
      stack.push(...(statementById.get(dep)?.depends_on ?? []));
    }
  }

  return { ok: violations.length === 0, violations };
}

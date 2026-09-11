// Solve-unit I/O: where a worker writes its output, how the pipeline reads it back
// (raw-byte normalization → JSON.parse → LaTeX repair → id heal → strict schema →
// companion resolution), path leases, and the weakly-connected-component grouping
// of open statements into units. Pure with respect to the graph store: nothing
// here knows what happens to an output once it validates.
import { existsSync } from "node:fs";
import { mkdir, open, readFile, readdir, rename, rm, writeFile } from "node:fs/promises";
import { randomUUID } from "node:crypto";
import path from "node:path";
import { artifactPath, formalizationDir } from "../../paths.js";
import type { PipelineContext } from "../../types.js";
import type { CoreStatement } from "../core/schema.js";
import { healStatementId } from "../core/node_ids.js";
import {
  assertNoDecodedControlChars,
  assertSealableLatexPayload,
  normalizeRawModelJson,
  repairLatexStringsDeep,
} from "../core/latex_serialization.js";
import { SolveUnitOutputSchema, type SolveUnitOutput } from "./schemas.js";
import { companionPathFor, sliceTexCompanion, resolveTexRefs } from "./tex_companion.js";

/** The persisted artifact is not a readable carrier (damaged JSON / TeX bytes)
 * even after the deterministic repairs: the model call itself failed and may be
 * repeated once. A schema/semantic contradiction in a readable carrier is
 * deliberately NOT this class — no mechanical rewrite may guess intent. */
export class SolveUnitCarrierError extends Error {}

function isCarrierDefect(err: unknown): boolean {
  if (err instanceof SyntaxError) return true;
  const message = err instanceof Error ? err.message : String(err);
  return /(?:Bad control character|LaTeX payload cannot be sealed|decoded JSON control character|under-escaped TeX|TeX companion|tex_ref|no tex_ref cites)/i.test(message);
}

export async function syncDirectory(dir: string): Promise<void> {
  const handle = await open(dir, "r");
  try {
    try {
      await handle.sync();
    } catch (err) {
      const code = (err as NodeJS.ErrnoException).code;
      if (code !== "EINVAL" && code !== "ENOTSUP" && code !== "EISDIR") throw err;
    }
  } finally {
    await handle.close();
  }
}

export function unitOutPath(ctx: PipelineContext, label: string): string {
  const slug = label.replace(/[^a-z0-9]+/gi, "_");
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", `solve_${slug}.json`, [`${ctx.qid}_solve_${slug}.json`]);
}

/** Round-scoped reuse receipts: a validated output bound to the exact prompt that
 * produced it, so a resume with a byte-identical prompt does not re-pay the model. */
export function solveReuseReceiptsDir(ctx: PipelineContext): string {
  return path.join(path.dirname(unitOutPath(ctx, "snapshot")), "solve_receipts");
}

export function repairSolveUnitLatexSerialization(value: unknown): void {
  repairLatexStringsDeep(value);
}

/** `prose_updates: {}` is an omission, not a prose write. */
export function normalizeEmptySolveUnitContainers(value: unknown): void {
  if (value === null || typeof value !== "object" || Array.isArray(value)) return;
  const body = value as Record<string, unknown>;
  const prose = body.prose_updates;
  if (prose !== null && typeof prose === "object" && !Array.isArray(prose) &&
      Object.keys(prose as Record<string, unknown>).length === 0) {
    delete body.prose_updates;
  }
}

export async function acquireSolvePathLease(outPath: string): Promise<{
  release: () => Promise<void>;
  assertOwned: () => Promise<void>;
}> {
  const lockDirectory = `${outPath}.lease.lock`;
  const ownerPath = path.join(lockDirectory, "owner-token");
  const ownerToken = randomUUID();
  try {
    await mkdir(lockDirectory);
  } catch (err) {
    if ((err as NodeJS.ErrnoException).code === "EEXIST") {
      throw Object.assign(new Error(`solve output path is already locked: ${outPath}`), { code: "ELOCKED" });
    }
    throw err;
  }
  await writeFile(ownerPath, `${ownerToken}\n`, { encoding: "utf8", flag: "wx" });
  const assertOwned = async (): Promise<void> => {
    try {
      if ((await readFile(ownerPath, "utf8")).trim() !== ownerToken) throw new Error("owner token changed");
    } catch (err) {
      throw new Error(`solve output lease ownership changed for ${outPath}: ${err instanceof Error ? err.message : String(err)}`);
    }
  };
  return {
    assertOwned,
    release: async () => {
      try {
        await assertOwned();
      } catch {
        return;
      }
      await rm(ownerPath, { force: true });
      await rm(lockDirectory, { recursive: true, force: true });
    },
  };
}

/** Called only from inside the acquired per-qid run heartbeat: the qid mutex proves
 * no normal pipeline owner remains, so a stranded lease can be reclaimed. */
export async function clearOrphanSolvePathLeases(ctx: PipelineContext): Promise<void> {
  const runDir = formalizationDir(ctx.repoRoot, ctx.qid);
  for (const dir of [path.join(runDir, "discovery"), runDir]) {
    let names: string[];
    try {
      names = await readdir(dir);
    } catch (err) {
      if ((err as NodeJS.ErrnoException).code === "ENOENT") continue;
      throw err;
    }
    for (const name of names) {
      if (/(^|_)solve_.*\.json\.lease\.lock$/.test(name)) await rm(path.join(dir, name), { recursive: true, force: true });
    }
  }
}

/** `direction` on a core edit is a function of `kind`; fill an omitted one. */
export function healCoreEditDirections(body: unknown): void {
  if (body === null || typeof body !== "object") return;
  const edits = (body as { proposed_core_edits?: unknown }).proposed_core_edits;
  if (!Array.isArray(edits)) return;
  for (const e of edits) {
    if (!e || typeof e !== "object") continue;
    const edit = e as { kind?: unknown; direction?: unknown };
    if (edit.direction !== undefined || typeof edit.kind !== "string") continue;
    edit.direction = edit.kind.endsWith("-delete") ? "delete-obsolete" : "correct";
  }
}

/** A D0 solve unit only owns `to-prove` statements.  A statement replacement may
 * change its mathematical payload, but proof promotion happens later when the PR
 * is applied; the model therefore has no authority over this status field. */
export function normalizeStatementReplacementStatuses(body: unknown): void {
  if (body === null || typeof body !== "object") return;
  const edits = (body as { proposed_core_edits?: unknown }).proposed_core_edits;
  if (!Array.isArray(edits)) return;
  for (const e of edits) {
    if (!e || typeof e !== "object") continue;
    const edit = e as { kind?: unknown; proposed?: unknown };
    if (edit.kind !== "statement-replace" || edit.proposed === null || typeof edit.proposed !== "object") continue;
    (edit.proposed as { status?: unknown }).status = "to-prove";
  }
}

/** Rewrite every emitted statement id into the schema's lowercase-kebab grammar,
 * including the edges, proofs, obligations, notes and edits that reference it. */
export function healSolveUnitIds(body: unknown): void {
  if (body === null || typeof body !== "object") return;
  const b = body as Record<string, unknown>;
  const rename = new Map<string, string>();
  const note = (id: unknown): void => {
    if (typeof id !== "string") return;
    const healed = healStatementId(id);
    if (healed !== null && healed !== id) rename.set(id, healed);
  };
  const stmts = [
    ...(Array.isArray(b.added_lemmas) ? b.added_lemmas : []),
    ...(Array.isArray(b.resolved_oeqs) ? b.resolved_oeqs.map((r) => (r as { theorem?: unknown }).theorem) : []),
  ];
  for (const st of stmts) if (st && typeof st === "object") note((st as { id?: unknown }).id);
  if (rename.size === 0) return;
  const swap = (id: unknown): unknown => (typeof id === "string" ? rename.get(id) ?? id : id);
  for (const st of stmts) {
    if (!st || typeof st !== "object") continue;
    const node = st as { id?: unknown; depends_on?: unknown };
    node.id = swap(node.id);
    if (Array.isArray(node.depends_on)) node.depends_on = node.depends_on.map(swap);
  }
  if (Array.isArray(b.proofs)) {
    for (const pr of b.proofs) if (pr && typeof pr === "object") (pr as { id?: unknown }).id = swap((pr as { id?: unknown }).id);
  }
  if (Array.isArray(b.open_obligations)) {
    for (const o of b.open_obligations) if (o && typeof o === "object") {
      (o as { node_id?: unknown }).node_id = swap((o as { node_id?: unknown }).node_id);
    }
  }
  const notes = (b.prose_updates as { statement_notes?: unknown } | undefined)?.statement_notes;
  if (Array.isArray(notes)) {
    for (const n of notes) if (n && typeof n === "object") (n as { id?: unknown }).id = swap((n as { id?: unknown }).id);
  }
  if (Array.isArray(b.proposed_core_edits)) {
    for (const e of b.proposed_core_edits) if (e && typeof e === "object") {
      const edit = e as {
        id?: unknown; replacement_id?: unknown;
        proposed?: { id?: unknown; depends_on?: unknown; ref?: unknown; by_member_properties?: unknown };
      };
      edit.id = swap(edit.id);
      edit.replacement_id = swap(edit.replacement_id);
      if (edit.proposed && typeof edit.proposed === "object") {
        edit.proposed.id = swap(edit.proposed.id);
        if (Array.isArray(edit.proposed.depends_on)) edit.proposed.depends_on = edit.proposed.depends_on.map(swap);
        edit.proposed.ref = swap(edit.proposed.ref);
        // NOT `refs`/`inputs`: those carry symbol names that may be spelled like a healed id.
        if (Array.isArray(edit.proposed.by_member_properties)) {
          edit.proposed.by_member_properties = edit.proposed.by_member_properties.map(swap);
        }
      }
    }
  }
  console.warn(
    `[D0-SOLVE] normalised ${rename.size} non-kebab emitted id(s) at the unit boundary: ` +
      `${[...rename].map(([a, c]) => `${a}->${c}`).join(", ")}`,
  );
}

export interface ReadSolveUnitOutputOptions {
  /** Commit the canonical unresolved JSON only after every check passes. */
  persistCanonical?: boolean;
  /** Fencing check supplied by live dispatch before destructive publication. */
  assertPersistenceLease?: () => Promise<void>;
  /** Exact companion generation accepted with the JSON. */
  onValidatedSnapshot?: (snapshot: { companionBlocks: Map<string, string>; companionRaw: string | null }) => void;
}

/** Solve-unit ingest. Parsing is pure unless the live dispatcher requests a canonical commit. */
export async function readSolveUnitOutput(
  outPath: string,
  label: string,
  options: ReadSolveUnitOutputOptions = {},
): Promise<SolveUnitOutput> {
  if (!existsSync(outPath)) throw new Error(`Stage 0-SOLVE unit ${label} completed without writing ${outPath}`);
  try {
    const raw = await readFile(outPath, "utf8");
    const companionPath = companionPathFor(outPath);
    const companionRawAtStart = existsSync(companionPath) ? await readFile(companionPath, "utf8") : null;
    const normalizedRaw = normalizeRawModelJson(raw);
    const body = JSON.parse(normalizedRaw);
    normalizeEmptySolveUnitContainers(body);
    repairSolveUnitLatexSerialization(body);
    assertNoDecodedControlChars(body, `Stage 0-SOLVE unit ${label} output`);
    healSolveUnitIds(body);
    healCoreEditDirections(body);
    normalizeStatementReplacementStatuses(body);
    const canonicalRaw = `${JSON.stringify(body, null, 2)}\n`;
    const validationBody = structuredClone(body);
    const companionBlocks = companionRawAtStart !== null
      ? sliceTexCompanion(companionRawAtStart, companionPath)
      : new Map<string, string>();
    {
      const used = resolveTexRefs(validationBody, companionBlocks, companionPath);
      const unused = [...companionBlocks.keys()].filter((ref) => !used.has(ref));
      if (unused.length > 0) {
        throw new Error(
          `TeX companion ${companionPath} has block(s) no tex_ref cites: ${unused.join(", ")} — ` +
            "either the JSON forgot a ref or a '%%% FIELD' look-alike line inside a block mis-sliced it",
        );
      }
    }
    healSolveUnitIds(validationBody);
    const parsed = SolveUnitOutputSchema.parse(validationBody);
    assertSealableLatexPayload(parsed, `Stage 0-SOLVE unit ${label} output`);

    if (options.persistCanonical === true && companionRawAtStart !== null) {
      await options.assertPersistenceLease?.();
      const companionHandle = await open(companionPath, "r");
      try {
        await companionHandle.sync();
      } finally {
        await companionHandle.close();
      }
      await syncDirectory(path.dirname(companionPath));
    }
    if (options.persistCanonical === true && canonicalRaw !== raw) {
      await options.assertPersistenceLease?.();
      if (await readFile(outPath, "utf8") !== raw) {
        throw new Error(`solve output generation changed during validation for ${outPath}; refusing to overwrite newer bytes`);
      }
      const staged = `${outPath}.canonical-${process.pid}-${randomUUID()}`;
      try {
        const handle = await open(staged, "wx");
        try {
          await handle.writeFile(canonicalRaw, "utf8");
          await handle.sync();
        } finally {
          await handle.close();
        }
        const beforeRenameRaw = await readFile(outPath, "utf8");
        const beforeRenameCompanion = existsSync(companionPath) ? await readFile(companionPath, "utf8") : null;
        if (beforeRenameRaw !== raw || beforeRenameCompanion !== companionRawAtStart) {
          throw new Error(`solve output generation changed before canonical commit for ${outPath}; refusing to persist a mixed JSON/companion generation`);
        }
        await options.assertPersistenceLease?.();
        await rename(staged, outPath);
        await syncDirectory(path.dirname(outPath));
      } finally {
        await rm(staged, { force: true });
      }
    }
    if (options.persistCanonical === true && canonicalRaw === raw) {
      await options.assertPersistenceLease?.();
      const acceptedHandle = await open(outPath, "r");
      try {
        await acceptedHandle.sync();
      } finally {
        await acceptedHandle.close();
      }
      await syncDirectory(path.dirname(outPath));
    }
    const finalRaw = await readFile(outPath, "utf8");
    const finalCompanion = existsSync(companionPath) ? await readFile(companionPath, "utf8") : null;
    const expectedRaw = options.persistCanonical === true && canonicalRaw !== raw ? canonicalRaw : raw;
    if (finalRaw !== expectedRaw || finalCompanion !== companionRawAtStart) {
      throw new Error(`solve output generation changed before validation returned for ${outPath}; refusing a mixed JSON/companion generation`);
    }
    if (options.persistCanonical === true) await options.assertPersistenceLease?.();
    options.onValidatedSnapshot?.({ companionBlocks: new Map(companionBlocks), companionRaw: companionRawAtStart });
    return parsed;
  } catch (err) {
    const message = `Stage 0-SOLVE unit ${label} wrote invalid solve JSON at ${outPath}: ${err instanceof Error ? err.message : String(err)}`;
    throw isCarrierDefect(err) ? new SolveUnitCarrierError(message, { cause: err }) : new Error(message, { cause: err });
  }
}

/** Partition to-prove statements into weakly-connected components of their mutual
 *  dependency graph. Only an edge between two TO-PROVE statements couples them. Each
 *  component becomes one solver unit, labelled by its lead headline. */
export function groupToProveByComponent(
  toProve: CoreStatement[],
): Array<{ targets: CoreStatement[]; label: string }> {
  const order = new Map(toProve.map((s, i) => [s.id, i]));
  const idSet = new Set(toProve.map((s) => s.id));
  const parent = new Map(toProve.map((s) => [s.id, s.id]));
  const find = (x: string): string => {
    let r = x;
    while (parent.get(r) !== r) r = parent.get(r)!;
    let c = x;
    while (parent.get(c) !== r) {
      const nxt = parent.get(c)!;
      parent.set(c, r);
      c = nxt;
    }
    return r;
  };
  const union = (a: string, b: string): void => { parent.set(find(a), find(b)); };
  for (const s of toProve) for (const d of s.depends_on ?? []) if (idSet.has(d)) union(s.id, d);
  const byRoot = new Map<string, CoreStatement[]>();
  for (const s of toProve) {
    const r = find(s.id);
    const bucket = byRoot.get(r) ?? [];
    bucket.push(s);
    byRoot.set(r, bucket);
  }
  const comps = [...byRoot.values()];
  for (const c of comps) c.sort((a, b) => order.get(a.id)! - order.get(b.id)!);
  comps.sort((a, b) => order.get(a[0].id)! - order.get(b[0].id)!);
  const HEADLINE_RANK: Record<string, number> = { theorem: 3, openendedquestion: 2, conjecture: 1 };
  return comps.map((targets) => {
    const lead = [...targets].sort((a, b) => {
      const byKind = (HEADLINE_RANK[b.kind] ?? 0) - (HEADLINE_RANK[a.kind] ?? 0);
      return byKind !== 0 ? byKind : a.id.localeCompare(b.id);
    })[0] ?? targets[0];
    return { targets, label: lead.id };
  });
}

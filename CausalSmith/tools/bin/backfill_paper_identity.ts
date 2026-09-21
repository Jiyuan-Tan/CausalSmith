#!/usr/bin/env -S npx tsx
/**
 * One-off backfill of citation identity into every shipped paper bundle.
 *
 * In plain words: the papers already on the site have no number, no version, and no
 * "last revised" date, so nobody can cite them. This fills those in, once, from what the
 * repository already knows — the bundle's own `created` date and the git history of its
 * `paper.tex` — and records the numbers in a tracked registry so they can never move again.
 *
 * Per the plan (`internal/plans/2026-09-20-cite-doi-ai-review.md`):
 *   * `wp_number` = `<SERIES>-<year of created>-<NNN>` (series from `paperSeriesPrefix()`),
 *     NNN a 1-based rank by (`created`, bundle id)
 *     within that year. Assigned ONCE, recorded in `doc/presentation/_wp_registry.json`, and
 *     re-read (never recomputed) on every later run.
 *   * `version`/`revised`/`versions` = v1 at `created`; plus v2 at the author date of the last
 *     commit that touched the bundle's `paper.tex`, when that is later than `created`.
 *   * `paper_sha256` is recorded on the LATEST versions entry only — the bytes of earlier
 *     rounds are not recoverable from a single git date, and a guess there would let a future
 *     emit mistake "unknown" for "unchanged".
 *
 * It FILLS, and only fills. A bundle that already has a `versions` history is left completely
 * alone — reported as "already has identity" and never touched. That is what makes a rerun safe:
 * once P4 owns a paper's version history, this script's plan is a stale snapshot of a state that
 * has moved on, and applying it would roll a v3 back to v2 or manufacture a v2 out of a git date
 * that only moved because of a date-pin commit. Filling is the one job it can still do correctly.
 *
 * `--dry-run` (the default) prints the table it would write; `--write` applies it.
 *
 * Usage: backfill_paper_identity.ts [--write] [--repo-root <CausalSmith package root>]
 */
import process from "node:process";
import { execFile } from "node:child_process";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { readFile, readdir } from "node:fs/promises";
import { join, resolve } from "node:path";
import { promisify } from "node:util";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { presentationRoot, wpRegistryPath } from "../src/presentation/paths.js";
import { PaperMeta } from "../src/presentation/types.js";
import { fileSha256 } from "../src/presentation/paper_stamp.js";
import { assertCalendarIsoDate, isoYear } from "../src/presentation/iso_date.js";
import { inPriorKeyOrder, updateBundleMeta } from "../src/presentation/meta_store.js";
import { isBundleEmitBusy, withBundleEmitLock } from "../src/presentation/emit_lock.js";
import {
  nextWpNumber, rankWpNumbers, readWpRegistry, validateClaimedWpNumber, withWpRegistryLock,
  writeWpRegistry, type WpRegistry,
} from "../src/presentation/wp_registry.js";
import { paperSeriesPrefix } from "../src/local_config.js";

const execFileP = promisify(execFile);

type Row = {
  id: string;
  created: string;
  texLast: string | null;
  wpNumber: string;
  version: number;
  revised: string;
  versions: Array<{ v: number; date: string; paper_sha256: string | null }>;
  changed: boolean;
};

/** Every directory under `doc/presentation/` that holds a `meta.json`. The directory also
 *  carries non-bundle entries (`_wp_registry.json`, and any future sidecar), so presence of the
 *  bundle contract — not the name — is the test. */
async function listBundles(root: string): Promise<string[]> {
  const entries = await readdir(root, { withFileTypes: true });
  const ids: string[] = [];
  for (const entry of entries) {
    if (!entry.isDirectory()) continue;
    const ok = await readFile(join(root, entry.name, "meta.json"), "utf8").then(() => true, () => false);
    if (ok) ids.push(entry.name);
  }
  return ids.sort();
}

/**
 * Author date (ISO, `YYYY-MM-DD`) of the last commit touching `relPath`, or null when the file
 * is untracked / has no history. `%ad` with `--date=short` is the AUTHOR date: the committer date
 * moves on a rebase or a cherry-pick, which would silently re-date a paper nobody revised.
 */
async function lastChangedIso(repoDir: string, relPath: string): Promise<string | null> {
  const { stdout } = await execFileP(
    "git",
    ["log", "-1", "--format=%ad", "--date=short", "--", relPath],
    { cwd: repoDir, maxBuffer: 4 * 1024 * 1024 },
  );
  const date = stdout.trim();
  return /^\d{4}-\d{2}-\d{2}$/.test(date) ? date : null;
}

function pad(value: string, width: number): string {
  return value.length >= width ? value : value + " ".repeat(width - value.length);
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const write = args.includes("--write");
  const rootFlag = args.indexOf("--repo-root");
  // Absolute: every repo-relative path below is derived by slicing the git top-level prefix off
  // these, which silently produces an empty pathspec for a relative root like `..`.
  const repoRoot = resolve(rootFlag >= 0 ? args[rootFlag + 1]! : findCausalSmithRoot());
  // The series, resolved and validated ONCE for the whole run and threaded from here.
  const prefix = paperSeriesPrefix();
  const bundlesDir = presentationRoot(repoRoot);
  // The git queries run against the enclosing checkout of the CausalSmith package, and the paths
  // they take are repo-relative — resolve both from git itself rather than assuming a layout.
  const gitTop = (await execFileP("git", ["rev-parse", "--show-toplevel"], { cwd: repoRoot })).stdout.trim();
  const relOf = (id: string) => `${join(bundlesDir, id, "paper.tex").slice(gitTop.length + 1).split("\\").join("/")}`;

  const ids = await listBundles(bundlesDir);
  if (ids.length === 0) throw new Error(`backfill: no bundles found under ${bundlesDir}`);

  const metas = new Map<string, Record<string, unknown>>();
  for (const id of ids) {
    metas.set(id, JSON.parse(await readFile(join(bundlesDir, id, "meta.json"), "utf8")) as Record<string, unknown>);
  }

  // ---------------------------------------------------------------------------
  // PHASE 1 — validate every bundle and derive every proposed row. NOTHING is written here.
  //
  // The registry is authoritative and an assignment in it is permanent, so it must not be
  // persisted until the whole input is known to be sound. Writing it first meant a bundle dated
  // 2026-02-31 could be given a ranked number, the run then throw on the bad date, and correcting
  // the date no longer be able to recompute the rank the series was supposed to have.
  type Derived = {
    id: string; created: string; texLast: string | null; version: number; revised: string;
    versions: Row["versions"];
    /** the bundle's own recorded number, validated verbatim against `prefix` and `created` */
    claimed: string | null;
    /** what phase 1 saw; phase 3 refuses to write over anything that has moved since */
    planned: { wp_number: unknown; version: unknown; revised: unknown; versions: unknown; sha: string };
  };
  const derived: Derived[] = [];
  const already: string[] = [];
  for (const id of ids) {
    const meta = metas.get(id)!;
    // Already has a history ⇒ P4 (or an earlier run of this script) owns it now. Nothing here can
    // improve on that, and everything here could damage it.
    if (Array.isArray(meta.versions) && meta.versions.length > 0) {
      already.push(id);
      continue;
    }
    const created = assertCalendarIsoDate(`${id}/meta.json created`, meta.created);
    const texLast = await lastChangedIso(gitTop, relOf(id));
    const sha = await fileSha256(join(bundlesDir, id, "paper.tex"));
    const versions: Row["versions"] = [{ v: 1, date: created, paper_sha256: null }];
    if (texLast !== null && texLast > created) versions.push({ v: 2, date: texLast, paper_sha256: null });
    const last = versions[versions.length - 1]!;
    last.paper_sha256 = sha;
    if (last.date < created) throw new Error(`backfill: ${id} would be revised (${last.date}) before created (${created})`);
    // The bundle's OWN recorded number, validated verbatim — same rules P4 applies, from the same
    // function. An earlier version hid this behind a placeholder here and then trimmed and adopted
    // the unvalidated original in phase 2, which is how a foreign-series or wrong-year number
    // could reach the authoritative registry.
    const claimed = validateClaimedWpNumber(id, created, meta.wp_number, prefix);
    PaperMeta.parse({ ...meta, wp_number: claimed, version: last.v, revised: last.date, versions });
    derived.push({
      id, created, texLast, version: last.v, revised: last.date, versions, claimed,
      planned: {
        wp_number: meta.wp_number, version: meta.version, revised: meta.revised, versions: meta.versions, sha,
      },
    });
  }

  // ---------------------------------------------------------------------------
  // PHASE 2 — the registry transaction: re-read, allocate, write, release. Under the registry
  // lock, because a P4 emit may be allocating a number for another bundle at the same instant;
  // an unlocked read-modify-write here would replace its entry with a snapshot that predates it.
  // The lock is held for a read and a write and nothing else.
  const allocate = (registry: WpRegistry): WpRegistry => {
    // Only claims phase 1 validated are adopted, and verbatim.
    for (const d of derived) {
      if (d.claimed !== null && registry[d.id] === undefined) registry[d.id] = d.claimed;
    }
    // A bundle this run leaves alone still owns its number; adopting it keeps the max+1 allocation
    // below from handing the same number to a bundle being filled.
    for (const id of already) {
      const owned = metas.get(id)!.wp_number;
      if (typeof owned === "string" && registry[id] === undefined) {
        registry[id] = validateClaimedWpNumber(id, String(metas.get(id)!.created), owned, prefix)!;
      }
    }
    const pending = derived.filter((d) => registry[d.id] === undefined)
      .sort((a, b) => (a.created < b.created ? -1 : a.created > b.created ? 1 : a.id < b.id ? -1 : 1));
    if (pending.length > 0) {
      if (Object.keys(registry).length === 0) {
        // The initial backfill: the whole series is ranked by (created, bundle id) within its year.
        Object.assign(registry, rankWpNumbers(pending.map(({ id, created }) => ({ id, created })), prefix));
      } else {
        // Stragglers joining an already-numbered series. Ranking them from 001 would collide with
        // numbers that are already published, so each takes max+1 for its year — exactly what P4
        // does for a new paper. Allocated in (created, id) order so the outcome is deterministic.
        for (const bundle of pending) registry[bundle.id] = nextWpNumber(registry, isoYear(bundle.created), prefix);
      }
    }
    const owners = new Map<string, string>();
    for (const [id, number] of Object.entries(registry)) {
      const prior = owners.get(number);
      if (prior !== undefined) throw new Error(`backfill: ${number} would be shared by ${prior} and ${id}`);
      owners.set(number, id);
    }
    return registry;
  };
  const serialise = (registry: WpRegistry) =>
    `${JSON.stringify(Object.fromEntries(Object.entries(registry).sort(([a], [b]) => (a < b ? -1 : 1))), null, 2)}\n`;

  let registry: WpRegistry;
  let registryBefore: string | null;
  if (write) {
    ({ registry, registryBefore } = await withWpRegistryLock(repoRoot, async () => {
      const before = await readFile(wpRegistryPath(repoRoot), "utf8").catch(() => null);
      const next = allocate(await readWpRegistry(repoRoot, prefix));
      if (serialise(next) !== before) await writeWpRegistry(repoRoot, next);
      return { registry: next, registryBefore: before };
    }));
  } else {
    // Dry run: read unlocked and report what WOULD be allocated. Nothing is committed, so a
    // concurrent allocation can only make this preview stale, never corrupt anything.
    registryBefore = await readFile(wpRegistryPath(repoRoot), "utf8").catch(() => null);
    registry = allocate(await readWpRegistry(repoRoot, prefix));
  }
  const registryText = serialise(registry);

  // ---------------------------------------------------------------------------
  // PHASE 3 — metadata, from the now-authoritative mapping. Each write goes through the shared
  // per-bundle writer, so it merges under that bundle's own lock and carries doi, score,
  // authorship and any unknown key. An interruption here is resumable: the numbers are already
  // committed, so a rerun simply finishes the files it did not reach.
  const rows: Row[] = [];
  const skipped: Array<{ id: string; why: string }> = [];
  /** Thrown from inside the metadata mutator to abandon a bundle without writing anything —
   *  `updateBundleMeta` writes only after the mutator returns, so throwing leaves the file
   *  untouched and still releases the lock. */
  class ChangedSincePlanning extends Error {}
  for (const d of derived) {
    const patch = { wp_number: registry[d.id]!, version: d.version, revised: d.revised, versions: d.versions };
    const before = await readFile(join(bundlesDir, d.id, "meta.json"), "utf8");
    const priorObj = JSON.parse(before) as Record<string, unknown>;
    const wouldBe = `${JSON.stringify(inPriorKeyOrder(priorObj, { ...priorObj, ...patch }), null, 2)}\n`;
    rows.push({ ...d, wpNumber: registry[d.id]!, changed: wouldBe !== before });
    if (!write || wouldBe === before) continue;
    // Phase 1 planned this patch minutes ago against a snapshot. `updateBundleMeta` re-reads the
    // file under the bundle's lock, so the object the mutator sees is current — and if a P4 emit
    // has bumped the version or re-pinned paper.tex in the meantime, applying the plan would
    // restore the OLDER identity, and the next identical emit would then bump again over nothing.
    // Refuse, say so, and exit non-zero; a rerun re-plans from the new state.
    //
    // BOTH halves of that check run inside the mutator, which is to say inside the bundle's lock.
    // Hashing paper.tex before acquiring the lock left a window: phase 3 could hash A, wait for
    // the lock while a concurrent emit re-pinned the file to B, and then record A as the current
    // version's hash. The read is synchronous precisely so nothing can interleave between the
    // hash and the write it authorises.
    try {
      // The bundle's EMIT lock wraps the hash-and-write transaction, so P4 cannot be rewriting
      // paper.tex while this decides what its hash is. Non-blocking: a backfill is a batch job
      // with no business queueing behind a multi-hour emit, and a bundle it skips is simply
      // picked up by the next run.
      await withBundleEmitLock(join(bundlesDir, d.id), async () => {
        await updateBundleMeta(join(bundlesDir, d.id), (m) => {
          const shaNow = createHash("sha256")
            .update(readFileSync(join(bundlesDir, d.id, "paper.tex")))
            .digest("hex");
          const same = shaNow === d.planned.sha &&
            JSON.stringify([m.wp_number, m.version, m.revised, m.versions]) ===
              JSON.stringify([d.planned.wp_number, d.planned.version, d.planned.revised, d.planned.versions]);
          if (!same) throw new ChangedSincePlanning();
          Object.assign(m, patch);
        });
      }, { wait: false });
    } catch (err) {
      if (err instanceof ChangedSincePlanning) skipped.push({ id: d.id, why: "identity or paper.tex changed since planning" });
      else if (isBundleEmitBusy(err)) skipped.push({ id: d.id, why: "an emit of this bundle is in progress" });
      else throw err;
      rows[rows.length - 1]!.changed = false;
    }
  }

  const w = Math.max(1, ...rows.map((r) => r.id.length), ...already.map((id) => id.length));
  console.log(`${pad("bundle", w)}  wp_number      created     paper.tex last  v  revised     write?`);
  for (const r of rows) {
    console.log(
      `${pad(r.id, w)}  ${r.wpNumber}  ${r.created}  ${pad(r.texLast ?? "(untracked)", 14)}  ${r.version}  ${r.revised}  ${r.changed ? "yes" : "unchanged"}`,
    );
  }
  for (const id of already) console.log(`${pad(id, w)}  (already has identity — untouched)`);
  console.log(
    `\n${ids.length} bundle(s): ${already.length} already have identity, ${rows.length} to fill ` +
      `(${rows.filter((r) => r.changed).length} meta.json to update); registry ` +
      `${registryText === registryBefore ? "unchanged" : "to update"} at ${wpRegistryPath(repoRoot)}.`,
  );
  console.log(write ? "WROTE the changes above." : "DRY RUN — nothing written. Rerun with --write to apply.");
  if (skipped.length > 0) {
    console.error(
      `\nSKIPPED ${skipped.length} bundle(s); nothing was written for them:\n` +
        skipped.map((s) => `  - ${s.id}: ${s.why}`).join("\n") +
        "\nRe-run the backfill once those bundles are idle; it re-plans against the current state.",
    );
    process.exitCode = 1;
  }
}

main().catch((error) => {
  console.error(error instanceof Error ? error.message : error);
  process.exitCode = 1;
});

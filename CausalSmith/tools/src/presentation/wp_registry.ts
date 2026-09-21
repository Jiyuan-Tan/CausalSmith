/**
 * Working-paper numbers (`<SERIES>-<year>-<NNN>`, e.g. `CSWP-2026-008`) and the tracked registry
 * that owns them.
 *
 * A citable series needs a number that never moves. Deriving it on the fly from a rank
 * over `created` would silently RENUMBER every later paper the moment a bundle is added,
 * removed, or backdated — and a number already printed on a PDF, in a DOI record, or in
 * someone's bibliography cannot be taken back. So the rank is computed ONCE (by the
 * backfill, over the bundles that existed then) and recorded in
 * `doc/presentation/_wp_registry.json`; from then on this module only ever READS an
 * existing assignment or appends `max+1` for the paper's `created` year. Nothing here
 * can renumber an existing entry.
 *
 * ONE CASE THIS CANNOT PREVENT. The locks serialise allocators sharing a filesystem, not ones
 * sharing a history: two git branches can each allocate the same next number to different papers,
 * and because the entries have different KEYS the registry merges without a conflict. The result
 * is two papers holding one citation, which is why `parseWpRegistry` rejects a duplicate number
 * loudly on the next read rather than letting it ship. There is no automatic repair — a number
 * may already have reached a PDF — so the rule is operational: emit new papers on one branch at a
 * time, and if the check does fire, decide by hand which paper keeps the number.
 */
import { mkdir, readFile, stat, writeFile } from "node:fs/promises";
import { join } from "node:path";
import lockfile from "proper-lockfile";
import { writeJsonAtomic } from "./json_io.js";
import { AsyncLocalStorage } from "node:async_hooks";
import { isHoldingBundleMetaLock } from "./meta_store.js";
import { presentationRoot, wpRegistryPath } from "./paths.js";

/**
 * `<SERIES>-<4-digit year>-<3-digit sequence>`; the sequence may grow past 999 without padding loss.
 *
 * The series is a REQUIRED parameter on every function in this module, never a default that
 * reaches for configuration. It is resolved once per operation, at the entry point (`stageP4`,
 * the backfill's `main`), and threaded down. That is the whole safety argument: an operation
 * cannot read the series twice and get two answers, so it cannot write `AAA-2026-001` into a
 * registry it is validating as `BBB`. Making the parameter required is what enforces it — a
 * defaulted one only asks nicely.
 */
export function wpNumberRe(prefix: string): RegExp {
  return new RegExp(`^${prefix}-(\\d{4})-(\\d{3,})$`);
}

/** bundle id (the `doc/presentation/<id>` directory name) → working-paper number. */
export type WpRegistry = Record<string, string>;

export function formatWpNumber(year: number, seq: number, prefix: string): string {
  if (!Number.isInteger(year) || year < 1000 || year > 9999) throw new Error(`invalid ${prefix} year ${year}`);
  if (!Number.isInteger(seq) || seq < 1) throw new Error(`invalid ${prefix} sequence ${seq}`);
  return `${prefix}-${year}-${String(seq).padStart(3, "0")}`;
}

/** `{year, seq}` of a number in the given series, or null (including for another series'). */
export function parseWpNumber(value: string, prefix: string): { year: number; seq: number } | null {
  const m = wpNumberRe(prefix).exec(value);
  return m ? { year: Number(m[1]), seq: Number(m[2]) } : null;
}

/** Year of an ISO `YYYY-MM-DD` date (string slice — never a `Date`, whose local-time
 *  parsing would move a 1 January paper into the previous year west of UTC). */
export function isoYear(iso: string): number {
  const m = /^(\d{4})-\d{2}-\d{2}$/.exec(iso);
  if (!m) throw new Error(`invalid ISO date "${iso}" (expected YYYY-MM-DD)`);
  return Number(m[1]);
}

/**
 * Validate a registry document: every value a well-formed number, no number used twice.
 * A duplicate would put two papers under one citation, so it fails loud rather than
 * being repaired by guesswork.
 */
export function parseWpRegistry(raw: string, path: string, prefix: string): WpRegistry {
  let value: unknown;
  try {
    value = JSON.parse(raw);
  } catch (err) {
    throw new Error(`${path}: not valid JSON (${(err as Error).message})`);
  }
  if (value === null || typeof value !== "object" || Array.isArray(value)) {
    throw new Error(`${path}: expected a { "<bundle id>": "${prefix}-…" } object`);
  }
  const registry: WpRegistry = {};
  const seen = new Map<string, string>();
  const pattern = wpNumberRe(prefix);
  for (const [id, number] of Object.entries(value as Record<string, unknown>)) {
    if (typeof number !== "string" || !pattern.test(number)) {
      // A number from ANOTHER series lands here. It is never renumbered into this one and never
      // mixed in: a registry belongs to exactly one series, and a fork that changes the prefix
      // starts from its own empty registry rather than inheriting somebody else's identifiers.
      const other = /^([A-Z][A-Z0-9]{1,9})-\d{4}-\d{3,}$/.exec(String(number))?.[1];
      throw new Error(
        `${path}: ${id} has a malformed working-paper number ${JSON.stringify(number)}` +
          (other && other !== prefix
            ? `: it belongs to series ${other}, but this checkout publishes ${prefix}. A registry holds one ` +
              "series only — point CAUSALSMITH_PAPER_SERIES_PREFIX at the right one, or start a separate registry."
            : ` (expected ${prefix}-<year>-<NNN>)`),
      );
    }
    const prior = seen.get(number);
    if (prior !== undefined) throw new Error(`${path}: ${number} is assigned to both ${prior} and ${id}`);
    seen.set(number, id);
    registry[id] = number;
  }
  return registry;
}

/** The registry as recorded, or `{}` when it does not exist yet. */
export async function readWpRegistry(repoRoot: string, prefix: string): Promise<WpRegistry> {
  const path = wpRegistryPath(repoRoot);
  const raw = await readFile(path, "utf8").catch((err: NodeJS.ErrnoException) => {
    if (err.code === "ENOENT") return null;
    throw err;
  });
  return raw === null ? {} : parseWpRegistry(raw, path, prefix);
}

/** Write the registry with its ids sorted, so a diff shows only the entry that was added.
 *  The bundles directory is created if absent: the registry can legitimately be the FIRST
 *  thing written into a fresh tree (a P4 emit whose outDir was made by the caller), and the
 *  presentation atomic writer does not mkdir its own destination. */
export async function writeWpRegistry(repoRoot: string, registry: WpRegistry): Promise<void> {
  const sorted = Object.fromEntries(
    Object.entries(registry).sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0)),
  );
  await mkdir(presentationRoot(repoRoot), { recursive: true });
  await writeJsonAtomic(wpRegistryPath(repoRoot), sorted);
}

/** The next free sequence for `year`: one past the highest already recorded (1 when none). */
export function nextWpNumber(registry: WpRegistry, year: number, prefix: string): string {
  let max = 0;
  for (const number of Object.values(registry)) {
    const parsed = parseWpNumber(number, prefix);
    if (parsed && parsed.year === year && parsed.seq > max) max = parsed.seq;
  }
  return formatWpNumber(year, max + 1, prefix);
}

/**
 * The initial assignment for a set of bundles: 1-based rank by (`created`, bundle id)
 * WITHIN each created year. Used only by the backfill's initial pass — once recorded,
 * `resolveWpNumber` never recomputes a rank.
 */
export function rankWpNumbers(
  bundles: Array<{ id: string; created: string }>,
  prefix: string,
): WpRegistry {
  const byYear = new Map<number, Array<{ id: string; created: string }>>();
  for (const bundle of bundles) {
    const year = isoYear(bundle.created);
    const members = byYear.get(year) ?? [];
    members.push(bundle);
    byYear.set(year, members);
  }
  const registry: WpRegistry = {};
  for (const [year, members] of byYear) {
    members
      .slice()
      .sort((a, b) => (a.created < b.created ? -1 : a.created > b.created ? 1 : a.id < b.id ? -1 : a.id > b.id ? 1 : 0))
      .forEach((bundle, i) => {
        registry[bundle.id] = formatWpNumber(year, i + 1, prefix);
      });
  }
  return registry;
}

/**
 * The lock guarding read-assign-write.
 *
 * It lives on the SHARED filesystem beside the registry it guards. An earlier version put it in
 * the host's `/tmp`, which synchronizes nothing: runs happen on several cluster nodes against one
 * checkout, so two nodes both read "highest is 022", both allocate 023 to different papers, and
 * the second atomic rename drops the first node's entry — after both PDFs have already been
 * stamped with the same number. A number that reached a PDF cannot be recalled, so this is the one place
 * in the package where a lock has to be correct across hosts.
 *
 * `proper-lockfile` acquires by `mkdir`, which is atomic on NFS, and creates `<target>.lock`
 * beside the sentinel. Both are gitignored (see the presentation byproducts block in the repo
 * `.gitignore`).
 *
 * LOCK ORDERING: emit lock, then registry, then a bundle's meta lock — never the reverse (see the
 * "Lock ordering" section in emit_lock.ts). Taking this lock from inside a meta lock is refused below
 * rather than left to deadlock two processes against each other on a shared filesystem, where
 * the symptom is a run that simply never returns. The critical section is a read and a write;
 * no caller may do slow work inside it.
 */
export const WP_REGISTRY_LOCK_FILE = ".wp_registry.lock";

function registryLockTarget(repoRoot: string): string {
  return join(presentationRoot(repoRoot), WP_REGISTRY_LOCK_FILE);
}

/** Run `action` holding the registry lock. Exported so a caller that must decide AND persist as
 *  one indivisible step (see `resolveWpNumber`) cannot be interleaved by another allocator. */
const holdingRegistryLock = new AsyncLocalStorage<{ active: boolean; compromised: unknown }>();

/** Whether the caller is inside a registry lock that is STILL HELD. Read by the emit lock, which
 *  is coarser and must never be taken from inside this one. */
export function isHoldingWpRegistryLock(): boolean {
  return holdingRegistryLock.getStore()?.active === true;
}

export async function withWpRegistryLock<T>(repoRoot: string, action: () => Promise<T>): Promise<T> {
  if (isHoldingBundleMetaLock()) {
    throw new Error(
      "lock order violation: the working-paper registry lock must be taken BEFORE a bundle's " +
        "meta.json lock, never inside it. Resolve the number first, release, then write metadata.",
    );
  }
  const target = registryLockTarget(repoRoot);
  await stat(target).catch(async () => {
    await mkdir(presentationRoot(repoRoot), { recursive: true });
    await writeFile(target, "working-paper registry lock sentinel\n", "utf8");
  });
  // Compromise is recorded rather than thrown from the refresh timer (which would be an uncaught
  // exception). Note what this does and does not undo: the allocation has ALREADY been persisted
  // by the time the check below runs, and then the error is thrown — the registry write is not
  // rolled back. That is deliberate and safe, because allocation is idempotent by bundle id: a
  // rerun reads the same entry back and returns the same number. The error's job is to stop the
  // caller TRUSTING an allocation made without exclusivity, not to unmake it.
  const token = { active: true, compromised: null as unknown };
  const release = await lockfile.lock(target, {
    stale: 60_000,
    retries: { retries: 30, factor: 1.4, minTimeout: 100, maxTimeout: 3_000 },
    realpath: false,
    onCompromised: (err) => { token.compromised = err; },
  });
  try {
    const result = await holdingRegistryLock.run(token, action);
    if (token.compromised != null) {
      throw new Error(
        `the working-paper registry lock was lost while allocating ` +
          `(${token.compromised instanceof Error ? token.compromised.message : String(token.compromised)}). ` +
          "Another allocator may have been running concurrently, so this allocation is not trusted. Re-run.",
      );
    }
    return result;
  } finally {
    try {
      await release();
    } catch (err) {
      if (token.compromised == null) throw err;
    } finally {
      token.active = false;
    }
  }
}

/**
 * Everything that can be decided about a CLAIMED `meta.wp_number` without consulting the registry:
 * whether it is absent, well formed, in this series, and filed under the right year.
 *
 * Shared by `resolveWpNumber` and the backfill so there is one definition of "acceptable claim"
 * rather than two that can drift. Ownership — is this number already somebody else's? — is
 * deliberately NOT here: that question can only be answered under the registry lock.
 *
 * Returns the claim VERBATIM (never trimmed: whitespace makes it malformed, not repairable), or
 * null when the field is genuinely absent. Only null and undefined count as absent; an empty
 * string, a number, an object are corrupt state, and reading them as "no number yet" would
 * allocate a second number to a paper that may already have published its first.
 */
export function validateClaimedWpNumber(
  bundleId: string,
  created: string,
  metaNumber: unknown,
  prefix: string,
): string | null {
  if (metaNumber === null || metaNumber === undefined) return null;
  if (typeof metaNumber !== "string" || !wpNumberRe(prefix).test(metaNumber)) {
    const other = /^([A-Z][A-Z0-9]{1,9})-\d{4}-\d{3,}$/.exec(String(metaNumber))?.[1];
    throw new Error(
      `${bundleId}/meta.json records a malformed working-paper number ${JSON.stringify(metaNumber)} ` +
        `(${typeof metaNumber})` +
        (other && other !== prefix
          ? `: it belongs to series ${other}, but this checkout publishes ${prefix}.`
          : `. Expected a ${prefix}-<year>-<NNN> string, or null to have one assigned.`),
    );
  }
  // The series year comes from `created`; a mismatch means either the date or the number is
  // wrong, and guessing which would permanently file the paper in the wrong year.
  const year = isoYear(created);
  const claimedYear = parseWpNumber(metaNumber, prefix)!.year;
  if (claimedYear !== year) {
    throw new Error(
      `${bundleId}/meta.json claims ${metaNumber} (series year ${claimedYear}) but its created date is ` +
        `${created} (year ${year}). Working-paper numbers are filed by created year — reconcile the ` +
        "date and the number by hand.",
    );
  }
  return metaNumber;
}

/**
 * The authoritative resolution of a bundle's number, for P4.
 *
 * THE REGISTRY WINS. An earlier version short-circuited on a non-empty `meta.wp_number` and never
 * consulted the registry at all, so a stale or hand-edited meta.json could stamp a number the
 * registry had given to a different paper — two papers, one citation, both already published.
 *
 * The rules, in order:
 *   * a present-but-malformed `meta.wp_number` fails the stage (it is not a number we can honour
 *     and it is not ours to silently discard);
 *   * registry has the bundle → that number wins; a disagreeing meta value fails the stage naming
 *     BOTH values, because only a human can say which one already reached a reader;
 *   * registry lacks the bundle but meta has a number → adopt it, unless another bundle already
 *     owns it, in which case fail naming both bundles;
 *   * neither → allocate `max+1` for the created year.
 *
 * The whole decision runs inside the registry lock, so the "is that number free?" check and the
 * write that takes it cannot be interleaved by a second allocator.
 */
export async function resolveWpNumber(
  repoRoot: string,
  bundleId: string,
  created: string,
  metaNumber: unknown,
  prefix: string,
): Promise<string> {
  const year = isoYear(created);
  const claimed = validateClaimedWpNumber(bundleId, created, metaNumber, prefix);
  return withWpRegistryLock(repoRoot, async () => {
    const registry = await readWpRegistry(repoRoot, prefix);
    const recorded = registry[bundleId];
    if (recorded !== undefined) {
      if (claimed !== null && claimed !== recorded) {
        throw new Error(
          `P4 blocked: ${bundleId} has working-paper number ${recorded} in ${wpRegistryPath(repoRoot)} but ` +
            `${claimed} in its meta.json. The registry is authoritative, but a number that has already been ` +
            "printed on a PDF or deposited cannot be changed silently — reconcile the two by hand.",
        );
      }
      return recorded;
    }
    if (claimed !== null) {
      const owner = Object.entries(registry).find(([id, number]) => number === claimed && id !== bundleId);
      if (owner) {
        throw new Error(
          `P4 blocked: ${bundleId}/meta.json claims ${claimed}, but the registry has already assigned that ` +
            `number to ${owner[0]}. Two papers cannot share a citation — resolve by hand.`,
        );
      }
      registry[bundleId] = claimed;
      await writeWpRegistry(repoRoot, registry);
      return claimed;
    }
    const assigned = nextWpNumber(registry, year, prefix);
    registry[bundleId] = assigned;
    await writeWpRegistry(repoRoot, registry);
    return assigned;
  });
}

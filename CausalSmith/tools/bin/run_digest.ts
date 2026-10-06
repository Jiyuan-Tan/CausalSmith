import { existsSync, readdirSync, readFileSync, statSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";

/**
 * Writes `run_digest.json` into every unfinished run banked under
 * `doc/research/_bank/{downgraded,failed}/<id>/`: the small reader-facing summary the site's
 * unfinished-runs page is built from, so the raw run folder need not ship with the repo.
 *
 * Every field is copied from the run's own files (state file, README frontmatter,
 * `discovery/proto_core.json`, `discovery/core.json`); nothing is inferred by a model.
 * `title`, `paper_type` and `stop_reason` are authored data, never computed here: each is the README
 * frontmatter value when filled in, else the site-side label map's, else the existing
 * digest's. `archive_url` points at the run's archive when the archive manifest lists it.
 *
 *   npx tsx bin/run_digest.ts            # write digests that are missing or out of date
 *   npx tsx bin/run_digest.ts --check    # write nothing; exit 1 if any digest is out of date
 */

const TOOLS = resolve(import.meta.dirname, "..");
const REPO = resolve(TOOLS, "..", "..");
const BANK = join(TOOLS, "..", "doc", "research", "_bank");
const BANK_REL = "CausalSmith/doc/research/_bank";
const TYPES_FILE = join(TOOLS, "..", "site", "src", "generated", "run_types.json");
const TITLES_FILE = join(TOOLS, "..", "site", "src", "generated", "run_titles.json");
const STOPS_FILE = join(TOOLS, "..", "site", "src", "generated", "run_stops.json");
const EXCLUDES_FILE = join(REPO, "internal", "export", "exclude.patterns");
const DIGEST = "run_digest.json";
/** Scrubbed raw records, one archive per run; the manifest lists the runs that have one. */
const ARCHIVE_MANIFEST = join(TOOLS, "..", "doc", "research", "run_archive_manifest.jsonl");
const ARCHIVE_BASE = "https://huggingface.co/datasets/jytan12/causalsmith-runs/resolve/main";

const CLUSTERS: Record<string, string> = {
  stat: "Stat",
  exp: "Experimentation",
  pid: "PartialID",
  eid: "ExactID",
  scm: "SCM",
  panel: "Panel",
};

function readJson(path: string): any {
  try {
    return JSON.parse(readFileSync(path, "utf8"));
  } catch {
    return null;
  }
}

/** Machine paths have no meaning to a reader and must not leave this machine: a token under a
 *  home directory, or any absolute path three or more folders deep. */
function scrub(s: string): string {
  return s
    .replace(/\s*\S*\/(home|Users)\/\S+/g, "")
    .replace(/(^|\s)\/[\w.-]+(\/[\w.-]+){2,}\S*/g, "$1")
    .trim();
}

function text(v: unknown): string | null {
  if (typeof v !== "string") return null;
  const s = scrub(v);
  return s === "" ? null : s;
}

/** One YAML scalar as written in a bank README: double-quoted (JSON escapes), single-quoted
 *  (`''` is a quote), or plain with an optional trailing ` # comment`. */
function yamlScalar(raw: string): string {
  const v = raw.trim();
  if (v.startsWith('"')) {
    const end = v.lastIndexOf('"');
    try {
      return String(JSON.parse(v.slice(0, end + 1)));
    } catch {
      return v.slice(1, end > 0 ? end : undefined);
    }
  }
  if (v.startsWith("'")) {
    const end = v.lastIndexOf("'");
    return v.slice(1, end > 0 ? end : undefined).replace(/''/g, "'");
  }
  return v.replace(/\s+#.*$/, "").trim();
}

/** The README frontmatter keys the digest carries: scalars, the `gap_reasons` list and the
 *  `proof_attempt_summary` block scalar. */
function frontmatter(readme: string): { scalars: Record<string, string>; gapReasons: string[]; summary: string | null } {
  const m = readme.match(/^---\n([\s\S]*?)\n---/);
  const scalars: Record<string, string> = {};
  const gapReasons: string[] = [];
  let summary: string | null = null;
  if (!m) return { scalars, gapReasons, summary };
  const lines = m[1].split("\n");
  for (let i = 0; i < lines.length; i++) {
    const kv = lines[i].match(/^([a-z_]+):\s*(.*)$/);
    if (!kv) continue;
    const [, key, raw] = kv;
    const block: string[] = [];
    while (i + 1 < lines.length && /^(\s|$)/.test(lines[i + 1])) block.push(lines[++i]);
    if (key === "gap_reasons") {
      for (const b of block) {
        const item = b.match(/^\s+-\s+(.*)$/);
        if (!item) continue;
        gapReasons.push(yamlScalar(item[1]));
      }
    } else if (key === "proof_attempt_summary") {
      summary = block.map((b) => b.trim()).join(" ").trim() || null;
    } else {
      scalars[key] = yamlScalar(raw);
    }
  }
  return { scalars, gapReasons, summary };
}

/** Runs whose Lean the public export withholds (unfinished proofs): they keep a digest, without
 *  a Lean link. The list exists only in the source repository; a published copy returns null and
 *  each digest keeps the flag it already has. */
function exportExcludes(): RegExp[] | null {
  if (!existsSync(EXCLUDES_FILE)) return null;
  return readFileSync(EXCLUDES_FILE, "utf8")
    .split("\n")
    .map((l) => l.trim())
    .filter((l) => l !== "" && !l.startsWith("#"))
    .map((l) => new RegExp(l));
}

/** An authored label: the first source that has it, in order of authority. A README scaffold
 *  placeholder (`TODO…`) counts as absent. */
function authored(...sources: unknown[]): string | null {
  for (const v of sources) {
    if (typeof v === "string" && v.trim() !== "" && !v.trim().startsWith("TODO")) return v.trim();
  }
  return null;
}

interface Labels {
  types: Record<string, string>;
  titles: Record<string, string>;
  /** Keyed `<tier>/<id>`: an id can sit in both tiers with different outcomes. */
  stops: Record<string, string>;
}

function archivedRuns(): Set<string> {
  const runs = new Set<string>();
  if (!existsSync(ARCHIVE_MANIFEST)) return runs;
  for (const line of readFileSync(ARCHIVE_MANIFEST, "utf8").split("\n")) {
    if (line.trim() === "") continue;
    const row = JSON.parse(line);
    runs.add(`${row.tier}/${row.id}`);
  }
  return runs;
}

function digestOf(tier: string, id: string, dir: string, labels: Labels, excludes: RegExp[] | null, archived: Set<string>): Record<string, unknown> | null {
  const files = readdirSync(dir);
  const stateFile = files.find((f) => f === "state.json") ?? files.find((f) => f.endsWith("_state.json"));
  const state = stateFile ? readJson(join(dir, stateFile)) : null;
  if (!state) return null;
  const readme = join(dir, "README.md");
  const fm = frontmatter(existsSync(readme) ? readFileSync(readme, "utf8") : "");
  const proto = readJson(join(dir, "discovery", "proto_core.json"));
  const core = readJson(join(dir, "discovery", "core.json"));
  const previous = readJson(join(dir, DIGEST)) ?? {};

  const statements: any[] = Array.isArray(core?.statements) ? core.statements : [];
  const count = (status: string) => statements.filter((s) => s?.status === status).length;
  const motifCounts = new Map<string, number>();
  for (const d of Array.isArray(proto?.seed_details) ? proto.seed_details : []) {
    for (const code of String(d?.motif ?? "").match(/M\d+/g) ?? []) {
      motifCounts.set(code, (motifCounts.get(code) ?? 0) + 1);
    }
  }
  // Occurrences of each motif code across the proposal's seeds, in first-seen order.
  const motifs = Object.fromEntries(motifCounts);
  const s = fm.scalars;
  const leanSubdir: string | null = typeof state.lean_subdir === "string" ? state.lean_subdir : null;
  const leanWithheld =
    excludes === null
      ? previous.lean_withheld === true
      : leanSubdir !== null && excludes.some((re) => re.test(`CausalSmith/${leanSubdir}/`));
  return {
    id,
    qid: state.qid ?? s.qid ?? id,
    title: authored(s.title, labels.titles[id], previous.title),
    tier,
    cluster: CLUSTERS[id.split("_")[0]] ?? "Other",
    banked_on: String(state.banked_on ?? s.banked_on ?? "").slice(0, 10) || null,
    stage_completed: state.stage_completed ?? null,
    has_derivation: existsSync(join(dir, "discovery", "writeup.tex")),
    has_core: core !== null,
    lean_subdir: leanSubdir !== null && !leanWithheld ? leanSubdir : null,
    lean_withheld: leanWithheld,
    banked_reason: text(state.banked_reason),
    novelty_target: s.novelty_target ?? null,
    banked_novelty_tier: state.banked_novelty_tier ?? s.banked_novelty_tier ?? null,
    tier_at_proposal: s.tier_at_proposal ?? null,
    tier_at_derivation: s.tier_at_derivation ?? null,
    reraise_status: s.reraise_status ?? null,
    gap_reasons: fm.gapReasons.map(scrub).filter((g) => g !== ""),
    proof_attempt_summary: authored(text(fm.summary)),
    tldr: text((core ?? proto)?.tldr),
    gap: text(proto?.project_justification?.gap),
    fill: text(proto?.project_justification?.fill),
    motifs,
    statements: { proved: count("proved"), open: count("to-prove"), cited: count("cited") },
    paper_type: authored(s.paper_type, labels.types[id], previous.paper_type),
    stop_reason: authored(s.stop_reason, labels.stops[`${tier}/${id}`], previous.stop_reason),
    archive_url: archived.has(`${tier}/${id}`) ? `${ARCHIVE_BASE}/${tier}/${id}.tar.zst` : null,
  };
}

function main(): void {
  const check = process.argv.includes("--check");
  const labels: Labels = { types: readJson(TYPES_FILE) ?? {}, titles: readJson(TITLES_FILE) ?? {},
    stops: readJson(STOPS_FILE) ?? {},
  };
  const excludes = exportExcludes();
  const archived = archivedRuns();
  let written = 0, current = 0, withheld = 0, noState = 0;
  const stale: string[] = [];
  for (const tier of ["downgraded", "failed"]) {
    const tierDir = join(BANK, tier);
    if (!existsSync(tierDir)) continue;
    for (const id of readdirSync(tierDir).sort()) {
      const dir = join(tierDir, id);
      if (id.startsWith("_") || !statSync(dir).isDirectory()) continue;
      const rel = `${BANK_REL}/${tier}/${id}/${DIGEST}`;
      const digest = digestOf(tier, id, dir, labels, excludes, archived);
      if (digest?.lean_withheld) withheld++;
      if (!digest) {
        noState++;
        continue;
      }
      const out = JSON.stringify(digest, null, 2) + "\n";
      const file = join(dir, DIGEST);
      if (existsSync(file) && readFileSync(file, "utf8") === out) {
        current++;
      } else if (check) {
        stale.push(rel);
      } else {
        writeFileSync(file, out);
        written++;
      }
    }
  }
  console.log(
    `run digests: ${check ? `${stale.length} out of date` : `${written} written`}, ${current} current, ` +
      `${withheld} with Lean withheld, ${noState} without a state file`,
  );
  if (check && stale.length > 0) {
    for (const p of stale.slice(0, 20)) console.log(`  ${p}`);
    process.exit(1);
  }
}

main();

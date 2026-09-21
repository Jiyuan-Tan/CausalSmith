#!/usr/bin/env -S npx tsx
/**
 * Deposit a CausalSmith working paper on Zenodo and record its DOI.
 *
 * The concept DOI is reserved BEFORE the PDF is compiled, so WP-B can stamp it onto
 * page 1 (plan decisions 5 and 6); `publish` then refuses a PDF that does not actually
 * print the DOI it is about to register under.
 *
 *   reserve <bundleDir>       open (or re-find) the draft; record the concept DOI
 *   release <bundleDir>       reserve, restamp page 1 with the DOI, verify, STOP before publish
 *   publish <bundleDir>       upload paper.pdf, set metadata, publish
 *   new-version <bundleDir>   open a draft for the next version, same concept DOI
 *   status <bundleDir>        what is recorded, and what Zenodo says
 *   abandon <bundleDir>       delete an unpublished draft and clear the fields
 *
 * SANDBOX IS THE DEFAULT, AND ITS RESULTS ARE QUARANTINED. Sandbox DOIs carry prefix
 * 10.5072, resolve to nothing, and would be indexed as the paper's real identifier if
 * they reached the site. So in sandbox mode the DOI is written to the bundle's
 * `zenodo.json` sidecar ONLY; `--write-meta` is required to put it in `meta.json`.
 *
 * PRODUCTION IS PERMANENT AND IS THE USER'S DECISION. It needs BOTH `--production` and
 * `--i-understand-this-is-permanent`, and no agent should ever run it: a published
 * record cannot be deleted and its DOI cannot be recalled.
 *
 * Usage:
 *   npx tsx tools/bin/zenodo_deposit.ts reserve <bundleDir> [flags]
 *   npx tsx tools/bin/zenodo_deposit.ts release <bundleDir> [--publish] [flags]
 *   npx tsx tools/bin/zenodo_deposit.ts publish <bundleDir> [--allow-unstamped] [flags]
 *   npx tsx tools/bin/zenodo_deposit.ts new-version <bundleDir> [--force] [flags]
 *   npx tsx tools/bin/zenodo_deposit.ts status|abandon <bundleDir> [flags]
 *
 * Flags: --production --i-understand-this-is-permanent --write-meta --dry-run
 *        --allow-unstamped --publish --force --site-base-url <url> --repo-url <url>
 *        --license <zenodo-id> --community <id> (repeatable) --title-prefix <s>
 */

import process from "node:process";
import { fileURLToPath } from "node:url";
import { realpathSync } from "node:fs";
import { resolve } from "node:path";
import { CliArgsError } from "../src/shared/cli_args.js";
import {
  PRODUCTION,
  SANDBOX,
  ZenodoClient,
  ZenodoError,
  type ZenodoEnvironment,
} from "../src/zenodo/client.js";
import { DEFAULT_LICENSE } from "../src/zenodo/metadata.js";
import { abandon, newVersion, publish, reserve, status, type DepositContext } from "../src/zenodo/deposit.js";
import { release } from "../src/zenodo/release.js";
import { paperSeriesPrefix } from "../src/local_config.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";

export const SUBCOMMANDS = ["reserve", "release", "publish", "new-version", "status", "abandon"] as const;
export type Subcommand = (typeof SUBCOMMANDS)[number];

const DEFAULT_SITE_BASE_URL = "https://causalsmith.org";
const DEFAULT_REPO_URL = "https://github.com/Jiyuan-Tan/CausalSmith";

function usage(): string {
  return [
    "Usage: zenodo_deposit.ts <reserve|release|publish|new-version|status|abandon> <bundleDir> [flags]",
    "",
    "  --production --i-understand-this-is-permanent   target zenodo.org (BOTH required)",
    "  --write-meta            allow writing doi/version_doi into the bundle's meta.json",
    "  --dry-run               print the requests (redacted); send nothing that mutates",
    "  --allow-unstamped       publish even if paper.pdf does not print the DOI",
    "  --publish               release: actually publish (default: stop after the preview)",
    "  --force                 new-version without a meta.version bump",
    "  --repair                status: reconcile local state against Zenodo and fix it",
    "  --discard-stamped-doi   abandon: discard a concept DOI the local PDF already prints",
    "  --confirm-no-remote-draft  reserve: create although an earlier reserve's outcome is unknown",
    `  --site-base-url <url>   default ${DEFAULT_SITE_BASE_URL}`,
    `  --repo-url <url>        default ${DEFAULT_REPO_URL}`,
    `  --license <id>          Zenodo licence id, default ${DEFAULT_LICENSE}`,
    "  --community <id>        Zenodo community (repeatable)",
    "  --title-prefix <s>      prefix the Zenodo title (sandbox defaults to '[TEST] ')",
  ].join("\n");
}

/**
 * Flags each subcommand accepts. Anything else is an error.
 *
 * WHY AN ALLOWLIST. The shared `cli_args` reader answers questions about argv; it does
 * not police it, so an unrecognised flag is simply never asked about and vanishes. For
 * a tool whose flags are the difference between a sandbox rehearsal and a permanent
 * public record, silence is the wrong default: `--productoin` used to run happily
 * against the sandbox and, with `--write-meta`, put a non-resolving DOI into a live
 * bundle. The shared reader is used by 40 other entry points, so the strictness lives
 * here rather than changing their behaviour.
 */
const GLOBAL_BOOLEANS = [
  "--production",
  "--i-understand-this-is-permanent",
  "--write-meta",
  "--no-write-meta",
  "--dry-run",
] as const;
const GLOBAL_VALUES = [
  "--site-base-url",
  "--repo-url",
  "--license",
  "--community",
  "--title-prefix",
] as const;

const SUBCOMMAND_FLAGS: Record<Subcommand, { booleans: string[]; values: string[] }> = {
  reserve: { booleans: ["--confirm-no-remote-draft"], values: [] },
  // `release` reserves, restamps and previews by default; --publish is the one thing that can
  // make it irreversible, and --allow-unstamped is what lets a sandbox rehearsal get that far
  // (a sandbox DOI is deliberately never stamped, so the stamp check cannot pass).
  release: { booleans: ["--publish", "--allow-unstamped"], values: [] },
  publish: { booleans: ["--allow-unstamped"], values: [] },
  "new-version": { booleans: ["--force"], values: [] },
  status: { booleans: ["--repair"], values: [] },
  abandon: { booleans: ["--discard-stamped-doi"], values: [] },
};

/** Repeatable value flags — several occurrences are legitimate. */
const REPEATABLE = new Set(["--community"]);

export interface ParsedArgs {
  readonly bundleDir: string;
  readonly booleans: ReadonlySet<string>;
  readonly values: ReadonlyMap<string, readonly string[]>;
}

/**
 * Parse argv strictly against `sub`'s schema and return the NORMALISED result.
 *
 * This is the only reader of argv. The previous version validated with one parser and
 * then read values with a second, generic one — and the two disagreed about
 * `--flag=value`: strict parsing accepted it, the generic reader did not recognise it,
 * and `--license=cc-zero` silently produced a CC-BY deposit. On production that is a
 * permanent licence on a permanent record. Two parsers for one argv is the bug; there
 * is now one, and it hands back exactly what the caller may use.
 *
 * `--flag=value` is rejected outright rather than supported, because supporting it
 * means every future reader has to handle both spellings and the next divergence is
 * only a refactor away.
 *
 * It also avoids a hazard in the shared reader's `positionals()`: that one treats the
 * token after ANY flag as the flag's value, so `reserve --dry-run /path` yields no
 * positionals at all. Knowing which flags are boolean removes the ambiguity.
 */
export function parseStrict(sub: Subcommand, argv: readonly string[]): ParsedArgs {
  const booleanNames = new Set<string>([...GLOBAL_BOOLEANS, ...SUBCOMMAND_FLAGS[sub].booleans]);
  const valueNames = new Set<string>([...GLOBAL_VALUES, ...SUBCOMMAND_FLAGS[sub].values]);
  const booleans = new Set<string>();
  const values = new Map<string, string[]>();
  const positionals: string[] = [];

  for (let i = 0; i < argv.length; i += 1) {
    const tok = argv[i];
    if (tok === "--") {
      positionals.push(...argv.slice(i + 1));
      break;
    }
    if (!tok.startsWith("--")) {
      positionals.push(tok);
      continue;
    }
    if (tok.includes("=")) {
      const name = tok.slice(0, tok.indexOf("="));
      throw new CliArgsError(
        `'${tok}' uses the --flag=value form, which this command does not accept. ` +
          `Write it as two arguments: ${name} <value>`,
      );
    }
    if (booleanNames.has(tok)) {
      if (booleans.has(tok)) throw new CliArgsError(`${tok} was given more than once.`);
      booleans.add(tok);
      continue;
    }
    if (valueNames.has(tok)) {
      const v = argv[i + 1];
      if (v === undefined) throw new CliArgsError(`${tok} requires a value but was given none.`);
      if (v.startsWith("--")) {
        throw new CliArgsError(
          `${tok} was followed by '${v}', which looks like another flag rather than a value.`,
        );
      }
      i += 1;
      const seen = values.get(tok);
      if (seen && !REPEATABLE.has(tok)) throw new CliArgsError(`${tok} was given more than once.`);
      if (seen) seen.push(v);
      else values.set(tok, [v]);
      continue;
    }
    const known = [...booleanNames, ...valueNames].sort();
    throw new CliArgsError(
      `Unknown flag '${tok}' for '${sub}'. This is refused rather than ignored: a mistyped ` +
        `flag must never silently change which Zenodo instance is used or what gets written. ` +
        `Accepted here: ${known.join(" ")}`,
    );
  }

  if (booleans.has("--write-meta") && booleans.has("--no-write-meta")) {
    throw new CliArgsError(
      "--write-meta and --no-write-meta contradict each other. Pass at most one: " +
        "--write-meta permits writing DOIs into meta.json, --no-write-meta forbids it " +
        "(including repairs).",
    );
  }
  if (positionals.length === 0) throw new CliArgsError(`${sub} needs a bundle directory.`);
  if (positionals.length > 1) {
    throw new CliArgsError(
      `${sub} takes exactly one bundle directory, but got ${positionals.length}: ` +
        `${positionals.join(" ")}`,
    );
  }
  return { bundleDir: positionals[0], booleans, values };
}

const one = (a: ParsedArgs, name: string): string | undefined => a.values.get(name)?.[0];
const all = (a: ParsedArgs, name: string): string[] => [...(a.values.get(name) ?? [])];

/** Pick the instance. Production takes two flags, not one: a single `--production`
 *  typo-adjacent to a sandbox run would mint a permanent DOI, and there is no undo. */
export function resolveEnvironment(args: ParsedArgs): ZenodoEnvironment {
  if (!args.booleans.has("--production")) return SANDBOX;
  if (!args.booleans.has("--i-understand-this-is-permanent")) {
    throw new Error(
      "--production also requires --i-understand-this-is-permanent. A published Zenodo record " +
        "cannot be deleted and its DOI cannot be recalled, so this is the user's decision to " +
        "make explicitly — not a default and not an agent's call.",
    );
  }
  return PRODUCTION;
}

async function main(): Promise<void> {
  const [sub, ...rest] = process.argv.slice(2);
  if (!sub || sub === "--help" || sub === "-h") {
    console.log(usage());
    return;
  }
  if (!(SUBCOMMANDS as readonly string[]).includes(sub)) {
    console.error(`Unknown subcommand '${sub}'.\n\n${usage()}`);
    process.exitCode = 1;
    return;
  }
  const subcommand = sub as Subcommand;
  const args = parseStrict(subcommand, rest);
  const bundleDir = args.bundleDir;

  const env = resolveEnvironment(args);
  const dryRun = args.booleans.has("--dry-run");
  const client = new ZenodoClient({
    env,
    dryRun,
    log: (line) => console.error(`  · ${line}`),
  });

  const titlePrefixFlag = one(args, "--title-prefix");
  const ctx: DepositContext = {
    bundleDir,
    client,
    // Production results belong in meta.json — that is the point of a production
    // deposit. Sandbox results do not, unless explicitly demanded.
    writeMeta: env.name === "production"
      ? !args.booleans.has("--no-write-meta")
      : args.booleans.has("--write-meta"),
    // An explicit prohibition, as distinct from the sandbox containment default: it
    // also blocks REPAIR of a DOI this tool previously wrote.
    metaWritesForbidden: args.booleans.has("--no-write-meta"),
    // `--dry-run` lives on the client, which is the only thing that can actually send
    // a request; a second copy on the context could disagree with it.
    allowUnstamped: args.booleans.has("--allow-unstamped"),
    siteBaseUrl: one(args, "--site-base-url") ?? DEFAULT_SITE_BASE_URL,
    repoUrl: one(args, "--repo-url") ?? DEFAULT_REPO_URL,
    license: one(args, "--license"),
    communities: all(args, "--community"),
    // A sandbox record is test data and should say so on its own landing page.
    titlePrefix: titlePrefixFlag ?? (env.name === "sandbox" ? "[TEST] " : undefined),
    log: (line) => console.log(line),
    warn: (line) => console.error(line),
    now: () => new Date(),
  };

  console.error(
    `zenodo_deposit ${sub}: environment=${env.name} (${env.apiBase})` +
      `${dryRun ? " [DRY RUN]" : ""} bundle=${bundleDir}`,
  );

  switch (subcommand) {
    case "reserve":
      await reserve(ctx, { confirmNoRemoteDraft: args.booleans.has("--confirm-no-remote-draft") });
      break;
    case "release":
      await release(ctx, {
        publish: args.booleans.has("--publish"),
        // Resolved ONCE, before anything is compiled or sent: one operation carries one series.
        repoRoot: findCausalSmithRoot(resolve(bundleDir)),
        seriesPrefix: paperSeriesPrefix(),
      });
      break;
    case "publish": await publish(ctx); break;
    case "new-version": await newVersion(ctx, { force: args.booleans.has("--force") }); break;
    case "status": await status(ctx, { repair: args.booleans.has("--repair") }); break;
    case "abandon":
      await abandon(ctx, { discardStampedDoi: args.booleans.has("--discard-stamped-doi") });
      break;
  }

  if (dryRun) {
    console.log("\n--- dry-run request transcript (redacted) ---");
    for (const line of client.requestLog) console.log(line);
  }
}

/**
 * Only run when executed as a program. Importing this module (the strict parser and the
 * environment gate are unit-tested directly) must not start a deposit.
 *
 * Both sides go through `realpathSync`. Comparing the raw paths makes the CLI a silent
 * exit-0 no-op whenever it is invoked through a symlink — a `bin/` shim, a
 * `node_modules/.bin` entry, a symlinked checkout — because `import.meta.url` resolves
 * to the real file while `process.argv[1]` keeps the link. "Did nothing and reported
 * success" is the worst possible failure for a deposit tool.
 */
const executedDirectly = (() => {
  const entry = process.argv[1];
  if (entry === undefined) return false;
  const real = (p: string): string => { try { return realpathSync(p); } catch { return p; } };
  return real(fileURLToPath(import.meta.url)) === real(entry);
})();

if (executedDirectly) main().catch((error) => {
  if (error instanceof ZenodoError) {
    console.error(`zenodo_deposit: ${error.message}`);
  } else if (error instanceof CliArgsError) {
    console.error(`zenodo_deposit: ${error.message}\n\n${usage()}`);
  } else {
    console.error(`zenodo_deposit: ${error instanceof Error ? error.message : String(error)}`);
  }
  process.exitCode = 1;
});

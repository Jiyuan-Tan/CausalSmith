// Single source of truth for machine-specific paths the pipeline needs.
//
// Edit ONE file — `tools/config/local.json` (gitignored; copy from
// `local.example.json`) — instead of hunting hardcoded paths across workers.
// Every value may also be overridden by an env var (env wins over the file),
// so CI / cluster runs can set env without editing the file.
//
// Fields:
//   gitBashPath      — Windows only: absolute path to git-bash `bash.exe`. The
//                      headless `claude` CLI refuses to run without it
//                      (CLAUDE_CODE_GIT_BASH_PATH). Leave null on Linux.
//   leanLspMcpBinary — `lean-lsp-mcp` server binary (PATH name or absolute).
//   leanProjectPath  — optional override for lean-lsp `--lean-project-path`;
//                      null ⇒ use the run's repoRoot (the lake project that
//                      transitively sees Causalean).
//   mcpTimeoutMs     — MCP_TIMEOUT for the (slow-cold-starting) lean-lsp server.
//   pythonPath       — interpreter for the Python retrieval scripts (the one with
//                      torch + sentence-transformers). null ⇒ probe the platform
//                      defaults; see `src/shared/python.ts` for the order. Set this
//                      on Windows, where `python3` is not a program name, or whenever
//                      the torch venv is not first on PATH.
//   codexSandbox     — local-tool sandbox for Codex workers. Keep the portable
//                      default `workspace-write`; set `danger-full-access` only
//                      when the machine is already externally confined and its
//                      Linux bubblewrap/user namespaces are unavailable.
//   paperSeriesPrefix — the working-paper SERIES this checkout publishes under, e.g. the
//                      default "CSWP" in `CSWP-2026-008`. A fork running its own series sets
//                      this (or CAUSALSMITH_PAPER_SERIES_PREFIX) and starts from its own empty
//                      registry; mixing two series in one registry is refused.
//   authMode / anthropicAuth / openaiAuth / *ApiKey / *ApiKeyFile / codexApiHome
//                    — who PAYS for the model calls: the operator's subscription
//                      logins (default) or an API key you supply. The fields are
//                      declared below; the precedence rules, the env overrides,
//                      and the reasons behind them live in `src/auth.ts`, which
//                      is the only module that interprets them.

import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

export interface LocalConfig {
  gitBashPath?: string;
  leanLspMcpBinary: string;
  leanProjectPath?: string;
  mcpTimeoutMs: number;
  /** Python 3 interpreter for the retrieval scripts; resolved in `src/shared/python.ts`. */
  pythonPath?: string;
  codexSandbox: "workspace-write" | "danger-full-access";
  /** Working-paper series prefix; see `paperSeriesPrefix()` below for resolution and validation. */
  paperSeriesPrefix?: string;
  /** Billing path for BOTH runners; per-provider fields below override it.
   *  Parsed and validated in `src/auth.ts`, not here, so that a bad value fails
   *  with an auth-specific message at the dispatch boundary. */
  authMode?: string;
  /** Billing path for the `claude` workers only. */
  anthropicAuth?: string;
  /** Billing path for the `codex` workers only. */
  openaiAuth?: string;
  anthropicApiKey?: string;
  /** Path to a file whose first non-empty line is the Anthropic key. */
  anthropicApiKeyFile?: string;
  openaiApiKey?: string;
  /** Path to a file whose first non-empty line is the OpenAI key. */
  openaiApiKeyFile?: string;
  /** CODEX_HOME used in codex api mode; kept separate from `~/.codex` so the
   *  subscription login is never evicted. Default `~/.codex-causalsmith-api`. */
  codexApiHome?: string;
  /** CLAUDE_CONFIG_DIR for the spawned `claude` workers, so the pipeline can run
   *  on a DIFFERENT Anthropic subscription than the operator's interactive login.
   *  Unset (the default) means the workers use `~/.claude` like everything else. */
  claudeConfigDir?: string;
}

const CONFIG_DIR = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  "..",
  "config",
);
const LOCAL_JSON = path.join(CONFIG_DIR, "local.json");

let cached: LocalConfig | null = null;
/**
 * Why the parse failure is remembered rather than only warned about.
 *
 * A malformed `local.json` degrades to env + defaults, which is the right call for a path or a
 * timeout — the run limps on and the warning is visible. It is the WRONG call for the paper
 * series prefix: a fork whose file says `AIWP7` would silently mint permanent CSWP identifiers
 * because of a syntax error somewhere else in the same file, and a published number cannot be
 * recalled. So the failure is recorded here and `paperSeriesPrefix()` refuses to guess.
 * Deliberately consulted by that one function only; every other key keeps its existing
 * fall-back-and-warn behaviour.
 */
let configParseError: string | null = null;

function parsePositiveIntegerConfig(name: string, value: unknown): number {
  const n = Number(String(value).trim());
  if (!Number.isFinite(n) || !Number.isInteger(n) || n <= 0) {
    // why: NaN timeout values propagate into MCP startup and hide config typos.
    throw new Error(`Invalid ${name}: ${String(value)} (expected a positive integer milliseconds value)`);
  }
  return n;
}

function parseCodexSandbox(value: unknown): LocalConfig["codexSandbox"] {
  const mode = String(value).trim();
  if (mode === "workspace-write" || mode === "danger-full-access") return mode;
  throw new Error(
    `Invalid codexSandbox: ${mode} (expected workspace-write or danger-full-access)`,
  );
}

/** The message from a failed `local.json` parse, or null (file absent or parsed cleanly).
 *  Populated by the first `localConfig()` call, which is memoised alongside the record itself. */
export function localConfigParseError(): string | null {
  localConfig();
  return configParseError;
}

/** The series every working-paper number in this checkout belongs to, absent other configuration. */
export const DEFAULT_PAPER_SERIES_PREFIX = "CSWP";

/** Letters and digits, starting with a letter, 2–10 characters — what reads as a series tag on a
 *  PDF and in a citation. Anything else is rejected: the prefix goes into permanent identifiers,
 *  so a typo would be published rather than corrected. */
export const PAPER_SERIES_PREFIX_RE = /^[A-Z][A-Z0-9]{1,9}$/;

export function assertPaperSeriesPrefix(value: unknown): string {
  if (typeof value !== "string" || !PAPER_SERIES_PREFIX_RE.test(value)) {
    throw new Error(
      `Invalid paperSeriesPrefix: ${JSON.stringify(value)} (expected 2-10 chars, uppercase letters and ` +
        `digits, starting with a letter — e.g. "${DEFAULT_PAPER_SERIES_PREFIX}"). Set it in ` +
        "tools/config/local.json or CAUSALSMITH_PAPER_SERIES_PREFIX.",
    );
  }
  return value;
}

/**
 * Decide the series from its three inputs. Pure, so the precedence and the fail-closed rule can
 * be tested without a config file on disk.
 *
 * Env beats file beats default, as everywhere else. The exception is `parseError`: when
 * `local.json` EXISTS but could not be read, the file's opinion is unknown rather than absent,
 * and defaulting would mint identifiers for the wrong series. An explicit env var still wins,
 * because that is an operator stating the answer rather than the code guessing it.
 */
export function resolveSeriesPrefix(
  envValue: string | undefined,
  fileValue: string | undefined,
  parseError: string | null,
): string {
  if (envValue !== undefined) return assertPaperSeriesPrefix(envValue);
  if (parseError !== null) {
    throw new Error(
      `Cannot determine the working-paper series: ${LOCAL_JSON} exists but could not be parsed ` +
        `(${parseError}). Working-paper numbers are permanent, so the series is never guessed — ` +
        "fix the file, or set CAUSALSMITH_PAPER_SERIES_PREFIX explicitly.",
    );
  }
  return assertPaperSeriesPrefix(fileValue ?? DEFAULT_PAPER_SERIES_PREFIX);
}

/**
 * The configured working-paper series prefix.
 *
 * Called exactly TWICE in the tree — at the top of `stageP4` and at the top of the backfill's
 * `main` — and the resulting string is then threaded as a required parameter through everything
 * that formats, parses, allocates or validates a number. That is why none of those functions
 * takes a default: one operation resolves the series once, so no mid-operation environment change
 * can make two halves of the same write disagree about which series they belong to, and the type
 * system makes a second lookup impossible rather than merely discouraged.
 */
export function paperSeriesPrefix(): string {
  return resolveSeriesPrefix(
    process.env.CAUSALSMITH_PAPER_SERIES_PREFIX,
    localConfig().paperSeriesPrefix,
    localConfigParseError(),
  );
}

export function localConfig(): LocalConfig {
  if (cached) return cached;
  let file: Partial<LocalConfig> = {};
  try {
    if (fs.existsSync(LOCAL_JSON)) {
      file = JSON.parse(fs.readFileSync(LOCAL_JSON, "utf8")) as Partial<LocalConfig>;
      if (Object.prototype.hasOwnProperty.call(file, ["module", "System"].join(""))) {
        console.warn('[local_config] ignoring obsolete "moduleSystem" key; the module system is always enabled.');
      }
    }
  } catch (err) {
    configParseError = err instanceof Error ? err.message : String(err);
    // Malformed local.json → fall back to env + defaults. Do NOT swallow
    // silently: a single-backslash Windows path (`E:\App\bash.exe`) is invalid
    // JSON, and a silent fallback strips `gitBashPath`, which makes every
    // headless `claude` worker fail on Windows with a misleading git-bash error.
    // Warn loudly so the real cause is visible. (Use forward slashes or `\\`.)
    console.warn(
      `[local_config] FAILED to parse ${LOCAL_JSON}: ${
        err instanceof Error ? err.message : String(err)
      }\n  -> falling back to env vars + defaults. gitBashPath/leanLspMcpBinary may be unset.` +
        `\n  -> Windows paths must use forward slashes or escaped backslashes (e.g. "E:/App/bash.exe").`,
    );
  }
  cached = {
    gitBashPath:
      process.env.CLAUDE_CODE_GIT_BASH_PATH ?? file.gitBashPath ?? undefined,
    leanLspMcpBinary:
      process.env.CAUSALSMITH_LEAN_LSP_MCP ?? file.leanLspMcpBinary ?? "lean-lsp-mcp",
    leanProjectPath:
      process.env.CAUSALSMITH_LEAN_PROJECT_PATH ?? file.leanProjectPath ?? undefined,
    // 10 min default: heavy concrete scaffolds (measure-theoretic estimator /
    // model-class defs) elaborate well past the old 2-min limit, so a reviewer's
    // lean-lsp vacuity probe on the active file times out even after a successful
    // pre-warm. Raised so probes on heavy-but-valid scaffolds can complete; the
    // F2.5 probe-unavailable downgrade is the backstop if they still don't.
    // Override via MCP_TIMEOUT env or local config file.
    mcpTimeoutMs: parsePositiveIntegerConfig(
      "MCP_TIMEOUT",
      process.env.MCP_TIMEOUT ?? file.mcpTimeoutMs ?? 600000,
    ),
    // Resolution (env > file > probed platform defaults) lives in shared/python.ts,
    // the only module that interprets it.
    pythonPath: file.pythonPath ?? undefined,
    codexSandbox: parseCodexSandbox(
      process.env.CAUSALSMITH_CODEX_SANDBOX ?? file.codexSandbox ?? "workspace-write",
    ),
    // Passed through VERBATIM and validated in `paperSeriesPrefix()`, the only reader, so the
    // prefix is checked at the point a number is minted rather than at unrelated CLI startup.
    paperSeriesPrefix: file.paperSeriesPrefix ?? undefined,
    // Auth fields pass through VERBATIM: `src/auth.ts` owns their precedence
    // (env beats file) and their validation, so duplicating either here would
    // give two places to disagree about which credential a run used.
    // `?? undefined` normalizes the example file's explicit `null` placeholders,
    // so consumers only ever see a string or absence.
    authMode: file.authMode ?? undefined,
    anthropicAuth: file.anthropicAuth ?? undefined,
    openaiAuth: file.openaiAuth ?? undefined,
    anthropicApiKey: file.anthropicApiKey ?? undefined,
    anthropicApiKeyFile: file.anthropicApiKeyFile ?? undefined,
    openaiApiKey: file.openaiApiKey ?? undefined,
    openaiApiKeyFile: file.openaiApiKeyFile ?? undefined,
    codexApiHome: file.codexApiHome ?? undefined,
    claudeConfigDir: file.claudeConfigDir ?? undefined,
  };
  return cached;
}

/**
 * The `bash` program every pipeline subprocess must spawn. On Windows a bare
 * `bash` resolves to WSL's `System32\bash.exe` (or nothing), not git-bash, so
 * the configured `gitBashPath` wins there; elsewhere it is PATH `bash`.
 */
export function bashBinary(): string {
  // Platform first: off Windows the config is never read, so an unrelated invalid
  // setting (e.g. MCP_TIMEOUT) cannot break a plain bash spawn.
  if (process.platform !== "win32") return "bash";
  return localConfig().gitBashPath || "bash";
}

/** Lean-lsp project root: the configured override, else the run's repoRoot. */
export function leanProjectPathFor(repoRoot: string): string {
  return localConfig().leanProjectPath || repoRoot;
}

/**
 * Inject worker-required env once at CLI startup so every spawned worker
 * inherits it: the `claude` CLI needs `CLAUDE_CODE_GIT_BASH_PATH` on Windows,
 * and lean-lsp wants a generous `MCP_TIMEOUT`. Idempotent; never overrides an
 * env var the caller already set.
 */
export function applyWorkerEnv(): void {
  const c = localConfig();
  if (c.gitBashPath && !process.env.CLAUDE_CODE_GIT_BASH_PATH) {
    process.env.CLAUDE_CODE_GIT_BASH_PATH = c.gitBashPath;
  }
  if (!process.env.MCP_TIMEOUT) {
    process.env.MCP_TIMEOUT = String(c.mcpTimeoutMs);
  }
}

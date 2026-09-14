// Machine-dependency checks shared by `npm run check:setup` and the presentation
// preflight. Probes spawn the program directly, without a shell, exactly as the
// pipeline does — so a program reachable only through a shell alias or a `.bat`
// shim reads as missing here and would fail in the pipeline too.
import { spawnSync, execFileSync } from "node:child_process";
import { existsSync } from "node:fs";
import { localConfig } from "../local_config.js";

/** Whether a program can be launched by name. */
export type ProgramProbe = (program: string) => boolean;

/** Reads one git config value normalized as a boolean ("true"/"false"), or null when unset. */
export type GitConfigReader = (key: string) => string | null;

/**
 * True when `program --version` launches and exits 0. Requiring a clean exit, not just
 * a launch, catches an install that starts but cannot work — e.g. MiKTeX's latexmk.exe
 * without Perl. A timeout counts as present: the program started and is only slow.
 */
export const probeProgram: ProgramProbe = (program) => {
  const r = spawnSync(program, ["--version"], { stdio: "ignore", timeout: 30_000 });
  if (r.error) return (r.error as NodeJS.ErrnoException).code === "ETIMEDOUT";
  return r.status === 0;
};

export const readGitBoolConfig: GitConfigReader = (key) => {
  try {
    const out = execFileSync("git", ["config", "--type=bool", "--get", key], {
      encoding: "utf8",
      stdio: ["ignore", "pipe", "ignore"],
    }).trim();
    return out || null;
  } catch {
    return null; // unset (git exits 1) or git itself unavailable
  }
};

const PRESENTATION_TOOLS = [
  {
    program: "pandoc",
    use: "P4 renders the paper body to HTML with it",
    install:
      "https://pandoc.org/installing.html — `apt install pandoc`, `brew install pandoc`, " +
      "or on Windows the installer / `winget install JohnMacFarlane.Pandoc`",
  },
  {
    program: "latexmk",
    use: "P4 compiles paper.tex to PDF with it",
    install:
      "a TeX distribution that ships latexmk — TeX Live (`apt install texlive-full latexmk`), " +
      "MacTeX, or TeX Live / MiKTeX on Windows (MiKTeX's latexmk also needs Perl)",
  },
] as const;

/** One actionable message per presentation program that cannot be launched. */
export function missingPresentationTools(probe: ProgramProbe = probeProgram): string[] {
  return PRESENTATION_TOOLS.filter((t) => !probe(t.program)).map(
    (t) => `\`${t.program}\` is missing or does not run (\`${t.program} --version\` failed; ${t.use}). Install: ${t.install}.`,
  );
}

/** Throw before any presentation stage runs when a required program is missing. */
export function assertPresentationTools(probe: ProgramProbe = probeProgram): void {
  const missing = missingPresentationTools(probe);
  if (missing.length === 0) return;
  throw new Error(
    "causalsmith present needs programs this machine does not have:\n" +
      missing.map((m) => `  - ${m}`).join("\n") +
      "\nInstall them, open a new shell so PATH picks them up, and rerun. " +
      "`npm run check:setup` (in CausalSmith/tools) re-checks.",
  );
}

/** Windows only: warn unless git's core.longpaths is enabled. */
export function longPathsWarning(
  platform: NodeJS.Platform = process.platform,
  read: GitConfigReader = readGitBoolConfig,
): string | null {
  if (platform !== "win32" || read("core.longpaths") === "true") return null;
  return (
    "git core.longpaths is not enabled; deep paths under .lake/ can exceed Windows' " +
    "260-character limit. Run `git config --global core.longpaths true`."
  );
}

/** Windows only: warn when the git-bash every bash spawn needs is unset or missing. */
export function gitBashWarning(
  platform: NodeJS.Platform,
  // Required, never defaulted: a default would also fire on an explicit `undefined`
  // and silently read this machine's real config.
  gitBashPath: string | undefined,
  pathExists: (p: string) => boolean = existsSync,
): string | null {
  if (platform !== "win32") return null;
  if (!gitBashPath) {
    return (
      "gitBashPath is not set; set it in CausalSmith/tools/config/local.json (forward slashes, " +
      "e.g. C:/Program Files/Git/bin/bash.exe) or CLAUDE_CODE_GIT_BASH_PATH."
    );
  }
  return pathExists(gitBashPath) ? null : `gitBashPath points at ${gitBashPath}, which does not exist.`;
}

export interface SetupCheckDeps {
  platform?: NodeJS.Platform;
  probe?: ProgramProbe;
  readGitConfig?: GitConfigReader;
  gitBashPath?: string;
  pathExists?: (p: string) => boolean;
}

/** Every machine-setup warning for this host; empty when nothing is wrong. */
export function setupWarnings(deps: SetupCheckDeps = {}): string[] {
  const platform = deps.platform ?? process.platform;
  const gitBashPath = "gitBashPath" in deps ? deps.gitBashPath : localConfig().gitBashPath;
  return [
    longPathsWarning(platform, deps.readGitConfig),
    gitBashWarning(platform, gitBashPath, deps.pathExists),
    ...missingPresentationTools(deps.probe),
  ].filter((w): w is string => w !== null);
}

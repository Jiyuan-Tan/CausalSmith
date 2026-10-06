// One-off bank migration: rewrite old bare-number stage ids in bank README prose
// (`stage 0.5`) to the `D-`/`F-` labels (`stage D0.5`), leaving code spans, fenced
// blocks and YAML front matter untouched.
//
// TypeScript rather than plain `.mjs` on purpose: the previous `.mjs` + hand-written
// `.d.mts` sidecar pair made module resolution ambiguous — on Windows the test's
// `import … from "./migrate_bank_stage_prose.mjs"` picked up the DECLARATION file and
// failed to parse it as JavaScript, taking the whole test file down at collection.
import { readdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";

export interface MigrationResult {
  content: string;
  substitutions: number;
}

export interface MigrationSummary {
  filesScanned: number;
  filesTouched: number;
  totalSubstitutions: number;
  changed: Array<{ file: string; substitutions: number }>;
}

const BANK_TIERS = ["downgraded", "failed", "accepted"];

const STAGE_MAP = new Map([
  ["-1.1", "D-1.1"],
  ["-1.2", "D-1.2"],
  ["-0.5", "D-0.5"],
  ["0.0", "D0.0"],
  ["0.k", "D0.k"],
  ["0.M", "D0.M"],
  ["0.5", "D0.5"],
  ["1.5", "F1.5"],
  ["2.5", "F2.5"],
  ["3.5", "F3.5"],
  ["4d", "F4.d"],
  ["-1", "D-1"],
  ["0", "D0"],
  ["1", "F1"],
  ["2", "F2"],
  ["3", "F3"],
  ["4", "F4"],
  ["5", "F5"],
]);

const stagePattern = /\b[Ss]tage\s+(4d|-1\.1|-1\.2|-0\.5|0\.0|0\.k|0\.M|0\.5|1\.5|2\.5|3\.5|-1|0|1|2|3|4|5)(?![\w-])/g;

function replaceStageLabels(text: string): MigrationResult {
  let substitutions = 0;
  const content = text.replace(stagePattern, (_match, stage: string) => {
    substitutions += 1;
    return STAGE_MAP.get(stage)!;
  });
  return { content, substitutions };
}

function migrateInlineProse(line: string): MigrationResult {
  let result = "";
  let substitutions = 0;
  let inInlineCode = false;

  for (const segment of line.split(/(`+)/)) {
    if (segment.startsWith("`")) {
      result += segment;
      if (segment.length % 2 === 1) {
        inInlineCode = !inInlineCode;
      }
      continue;
    }

    if (inInlineCode) {
      result += segment;
      continue;
    }

    const migrated = replaceStageLabels(segment);
    result += migrated.content;
    substitutions += migrated.substitutions;
  }

  return { content: result, substitutions };
}

export function migrateMarkdown(content: string): MigrationResult {
  const lines = content.match(/[^\n]*\n|[^\n]+/g) ?? [];
  const migratedLines: string[] = [];
  let substitutions = 0;
  let inYamlFrontMatter = lines[0]?.replace(/\r?\n$/, "") === "---";
  let inCodeFence = false;

  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index];
    const lineBody = line.replace(/\r?\n$/, "");
    const trimmed = lineBody.trimStart();

    if (inYamlFrontMatter) {
      migratedLines.push(line);
      if (index > 0 && lineBody.trim() === "---") {
        inYamlFrontMatter = false;
      }
      continue;
    }

    if (trimmed.startsWith("```")) {
      migratedLines.push(line);
      inCodeFence = !inCodeFence;
      continue;
    }

    if (inCodeFence) {
      migratedLines.push(line);
      continue;
    }

    const migrated = migrateInlineProse(line);
    migratedLines.push(migrated.content);
    substitutions += migrated.substitutions;
  }

  return { content: migratedLines.join(""), substitutions };
}

async function pathExists(dir: string): Promise<boolean> {
  try {
    await readdir(dir);
    return true;
  } catch (error) {
    if ((error as NodeJS.ErrnoException)?.code === "ENOENT") {
      return false;
    }
    throw error;
  }
}

async function collectReadmes(repoRoot: string): Promise<string[]> {
  const bankRoot = path.join(repoRoot, "CausalSmith", "doc", "research", "_bank");
  const files: string[] = [];

  for (const tier of BANK_TIERS) {
    const tierRoot = path.join(bankRoot, tier);
    if (!(await pathExists(tierRoot))) {
      continue;
    }

    const entries = await readdir(tierRoot, { withFileTypes: true });
    for (const entry of entries) {
      if (!entry.isDirectory()) {
        continue;
      }
      files.push(path.join(tierRoot, entry.name, "README.md"));
    }
  }

  return files.sort();
}

export async function runMigration(
  { repoRoot = process.cwd(), write = false }: { repoRoot?: string; write?: boolean } = {},
): Promise<MigrationSummary> {
  const files = await collectReadmes(repoRoot);
  const changed: Array<{ file: string; substitutions: number }> = [];
  let totalSubstitutions = 0;

  for (const file of files) {
    const before = await readFile(file, "utf8");
    const migrated = migrateMarkdown(before);
    if (migrated.substitutions === 0 || migrated.content === before) {
      continue;
    }

    totalSubstitutions += migrated.substitutions;
    changed.push({ file, substitutions: migrated.substitutions });

    if (write) {
      await writeFile(file, migrated.content);
    }
  }

  return {
    filesScanned: files.length,
    filesTouched: changed.length,
    totalSubstitutions,
    changed,
  };
}

function parseCliArgs(argv: string[]): { write: boolean } {
  if (argv.includes("--write") && argv.includes("--dry-run")) {
    throw new Error("Use either --dry-run or --write, not both.");
  }
  return { write: argv.includes("--write") };
}

async function main(): Promise<void> {
  const { write } = parseCliArgs(process.argv.slice(2));
  const summary = await runMigration({ write });
  const mode = write ? "write" : "dry-run";

  for (const change of summary.changed) {
    console.log(`${path.relative(process.cwd(), change.file)}: ${change.substitutions} substitutions`);
  }

  console.log(
    `[${mode}] scanned ${summary.filesScanned} README.md files; ` +
      `${summary.filesTouched} files touched; ${summary.totalSubstitutions} substitutions.`,
  );
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  main().catch((error: unknown) => {
    console.error(error instanceof Error ? error.message : String(error));
    process.exitCode = 1;
  });
}

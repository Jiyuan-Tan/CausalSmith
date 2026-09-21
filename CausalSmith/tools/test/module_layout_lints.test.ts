import { afterEach, describe, expect, it } from "vitest";
import { execFile } from "node:child_process";
import { mkdtemp, mkdir, readFile, readdir, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { promisify } from "node:util";

const exec = promisify(execFile);
const TOOLS = path.resolve(import.meta.dirname, "..");
const REPO = path.resolve(TOOLS, "..", "..");
const HEADERS = path.join(TOOLS, "bin", "lint_module_headers.ts");
const LAYOUT = path.join(TOOLS, "bin", "lint_library_layout.ts");
const temporary: string[] = [];

async function moduleFilesUnder(dir: string): Promise<string[]> {
  const out: string[] = [];
  for (const entry of await readdir(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) out.push(...await moduleFilesUnder(full));
    else if (entry.isFile() && entry.name.endsWith(".lean") && /^module\r?$/m.test(await readFile(full, "utf8"))) out.push(full);
  }
  return out;
}

async function tree(files: Record<string, string>): Promise<string> {
  const root = await mkdtemp(path.join(os.tmpdir(), "module-layout-lint-"));
  temporary.push(root);
  for (const [name, source] of Object.entries(files)) {
    const target = path.join(root, name);
    await mkdir(path.dirname(target), { recursive: true });
    await writeFile(target, source, "utf8");
  }
  return root;
}
async function run(script: string, args: string[], cwd = TOOLS) {
  return exec(process.execPath, ["--import", "tsx/esm", script, ...args], { cwd, env: process.env });
}
async function jsonFailure(script: string, args: string[]): Promise<unknown> {
  try { await run(script, args); throw new Error("expected lint failure"); }
  catch (error) { return JSON.parse((error as { stdout: string }).stdout); }
}
afterEach(async () => { await Promise.all(temporary.splice(0).map((dir) => rm(dir, { recursive: true, force: true }))); });

describe("lint_module_headers", () => {
  it("checks header, imports, blanket section placement, and exposure comment-aware", async () => {
    const root = await tree({
      "Causalean/Good.lean": "module\npublic import Mathlib.Data.Nat.Basic\n\n/-! Good. -/\n\n@[expose] public section\n-- def hidden : Nat := 0\ndef visible : Nat := 0\n",
      "Causalean/Bad.lean": "module\nimport Mathlib.Data.Nat.Basic\n/-! Bad. -/\npublic section\npublic section\ndef x : Nat := 0\n",
      "Causalean/Unexposed.lean": "module\npublic import Mathlib.Data.Nat.Basic\n/-! Unexposed. -/\npublic section\ndef x : Nat := 0\n",
      "Causalean/Private.lean": "module\n-- private import\nimport Mathlib.Tactic\n/-! Private imports. -/\n\npublic section\ntheorem x : True := trivial\n",
      "Causalean/Barrel.lean": "module\npublic import Mathlib.Data.Nat.Basic\n/-! Barrel with no declarations. -/\n",
      "Causalean/Theorems.lean": "module\npublic import Mathlib.Data.Nat.Basic\n/-! Theorems. -/\n@[expose] public section\ntheorem x : True := trivial\n",
      "Causalean/CommentImports.lean": "module\npublic import Mathlib.Data.Nat.Basic\n/-! Example only: import Fake.DocExample -/\npublic section\ntheorem x : True := trivial\n",
      "Causalean/Legacy.lean": "import Mathlib\ntheorem old : True := trivial\n",
    });
    const result = await jsonFailure(HEADERS, ["--paths", path.join(root, "Causalean"), "--strict", "--json"] as string[]) as { findings: { rule: string }[] };
    expect(result.findings.map((f) => f.rule)).toEqual(expect.arrayContaining([
      "missing-module-header", "non-public-import", "blanket-public-section", "expose-section",
    ]));
    expect(result.findings).toContainEqual(expect.objectContaining({ path: expect.stringContaining("Theorems.lean"), rule: "expose-section", severity: "warning" }));
    expect(result.findings.some((f) => String((f as { path?: string }).path).includes("Barrel.lean"))).toBe(false);
    expect(result.findings.some((f) => String((f as { path?: string }).path).includes("CommentImports.lean"))).toBe(false);
    const allowed = await run(HEADERS, ["--paths", path.join(root, "Causalean", "Legacy.lean"), "--json"]);
    expect(JSON.parse(allowed.stdout)).toMatchObject({ findings: [], legacyCount: 1 });
  });

  it("reports zero errors for every current module-system pilot", async () => {
    const moduleFiles = [
      ...await moduleFilesUnder(path.join(REPO, "Causalean")),
      ...await moduleFilesUnder(path.join(REPO, "CausalSmith", "CausalSmith")),
    ];
    expect(moduleFiles.length).toBeGreaterThan(0);
    const result = await run(HEADERS, ["--paths", ...moduleFiles, "--json"]);
    const parsed = JSON.parse(result.stdout) as { findings: { severity?: string }[] };
    expect(parsed.findings.filter((finding) => finding.severity !== "warning")).toEqual([]);
  }, 60_000);
});

describe("lint_library_layout", () => {
  it("finds every structural rule in a synthetic library and supports baselines", async () => {
    const oversized = Array.from({ length: 901 }, () => "-- line").join("\n");
    const root = await tree({
      "Causalean/Graph/Bad.lean": "import Causalean.Discovery.Topic\nimport CausalSmith.Secret\nnamespace Wrong.Name\n",
      "Causalean/Mathlib/Bad/Thing.lean": "import Causalean.Graph.DAG\nnamespace Causalean.Mathlib.Bad\n",
      "Causalean/Mathlib/Loose.lean": "namespace Causalean.Mathlib\n",
      "Causalean/AsymptoticLanConvolution/Big.lean": `${oversized}\nnamespace Causalean.AsymptoticLanConvolution\n`,
      "Causalean/PO.lean": "import Causalean.PO.ID.Exact.Result\n",
      "Causalean/PO/ID/Exact/Result.lean": "import Causalean.Graph.DAG\n",
      "Causalean/SCM.lean": "import Causalean.SCM.ID.Result\n",
      "Causalean/SCM/ID/Result.lean": "import Causalean.Graph.DAG\n",
      "Causalean/Graph/Legacy.lean": "import Causalean.Discovery.Topic\ndeprecated_module \"moved\" (since := \"2026-09-13\")\n",
      "Causalean/Stat/UsesLegacy.lean": "import Causalean.Experimentation.Legacy\n",
      "Causalean/Experimentation/Legacy.lean": "import Causalean.Stat.Replacement\ndeprecated_module \"moved\" (since := \"2026-09-13\")\n",
      "Causalean/ML/CausalApplication/App.lean": "import Causalean.Estimation.Core\nimport Causalean.Discovery.Topic\n",
      "Causalean/Stat/Identification/Check.lean": "import Causalean.Estimation.Core\n",
      "Causalean/Stat/FiniteDesign/Check.lean": "import Causalean.Estimation.Core\n",
      "Causalean/Stat/Weighted/Check.lean": "import Causalean.Estimation.Core\n",
      "Causalean/Stat/LinearModel/Check.lean": "import Causalean.Estimation.Core\n",
      "doc/library_index.json": JSON.stringify({ entries: [
        { name: "Causalean.Mathlib.Bad.headline", module: "Causalean.Mathlib.Bad", file: "Causalean/Mathlib/Bad/Thing.lean" },
        { name: "Causalean.Graph.Bad.one", module: "Causalean.Graph.Bad", file: "Causalean/Graph/Bad.lean" },
        { name: "Causalean.Graph.Bad.two", module: "Causalean.Graph.Bad", file: "Causalean/Graph/Bad.lean" },
        { name: "Causalean.Graph.Bad.three", module: "Causalean.Graph.Bad", file: "Causalean/Graph/Bad.lean" },
        { name: "Causalean.Graph.Bad.four", module: "Causalean.Graph.Bad", file: "Causalean/Graph/Bad.lean" },
        { name: "Causalean.Graph.Bad.five", module: "Causalean.Graph.Bad", file: "Causalean/Graph/Bad.lean" },
        { name: "Causalean.Graph.Bad.six", module: "Causalean.Graph.Bad", file: "Causalean/Graph/Bad.lean" },
      ] }),
      "doc/library_review/Graph.json": JSON.stringify({ headline_theorems: ["Causalean.Graph.Bad.one", "Causalean.Graph.Bad.two", "Causalean.Graph.Bad.three", "Causalean.Graph.Bad.four", "Causalean.Graph.Bad.five", "Causalean.Graph.Bad.six"], reviews: [], flags: [] }),
      "doc/library_review/Mathlib.json": JSON.stringify({ headline_theorems: ["Causalean.Mathlib.Bad.headline"], reviews: [], flags: [] }),
    });
    const result = await jsonFailure(LAYOUT, ["--root", root, "--json"]) as {
      findings: { rule: string; path: string; message: string }[]
    };
    for (const rule of ["LAYER", "RUN-NAME", "MATHLIB-PURITY", "SIZE", "HEADLINES", "NAMESPACE", "NO-CAUSALSMITH"])
      expect(result.findings.some((f) => f.rule === rule)).toBe(true);
    const layers = result.findings.filter((finding) => finding.rule === "LAYER");
    for (const exempt of ["PO.lean", "SCM.lean", "Graph/Legacy.lean", "Stat/UsesLegacy.lean"])
      expect(layers.some((finding) => finding.path.endsWith(exempt))).toBe(false);
    expect(layers.find((finding) => finding.path.endsWith("CausalApplication/App.lean"))?.message).toContain("(L8)");
    for (const directory of ["Identification", "FiniteDesign", "Weighted", "LinearModel"])
      expect(layers.find((finding) => finding.path.includes(`/Stat/${directory}/`))?.message).toContain("(L2)");
    const baseline = path.join(root, "baseline.json");
    const clean = await run(LAYOUT, ["--root", root, "--write-baseline", baseline, "--baseline", baseline, "--json"]);
    expect(JSON.parse(clean.stdout)).toMatchObject({ findings: [], suppressed: result.findings.length });
  });

  it("checks the namespace after a same-line module docstring closes", async () => {
    const root = await tree({
      "Causalean/Graph/Bad.lean": "module\n/-! docs -/\npublic section\nnamespace Wrong.Name\n",
    });
    const result = await jsonFailure(LAYOUT, ["--root", root, "--json"]) as { findings: { rule: string; path: string }[] };
    expect(result.findings).toContainEqual(expect.objectContaining({ rule: "NAMESPACE", path: "Causalean/Graph/Bad.lean" }));
  });

  it("uses the public-repository layout baseline by default", async () => {
    const result = await run(LAYOUT, ["--json"]);
    const parsed = JSON.parse(result.stdout) as { findings: unknown[]; suppressed: number };
    expect(parsed.findings).toEqual([]);
    expect(parsed.suppressed).toBeGreaterThan(0);
  }, 60_000);

  it("smoke-runs both lints on the repository in JSON mode", async () => {
    for (const [script, args] of [
      [HEADERS, ["--json", "--allow-legacy"]],
      [LAYOUT, ["--json"]],
    ] as const) {
      try {
        const result = await run(script, [...args]);
        expect(() => JSON.parse(result.stdout)).not.toThrow();
      } catch (error) {
        expect(() => JSON.parse((error as { stdout: string }).stdout)).not.toThrow();
      }
    }
  }, 60_000);
});

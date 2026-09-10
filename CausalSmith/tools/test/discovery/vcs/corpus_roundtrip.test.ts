import { existsSync, readFileSync } from "node:fs";
import { execSync } from "node:child_process";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { CoreSchema } from "../../../src/discovery/core/schema.js";
import { runStructuralGate } from "../../../src/discovery/core/gate.js";
import { rebuildAssumptionUsedBy, wireStatementProofDependencies } from "../../../src/discovery/core/dependencies.js";
import { repairCoreLatexSerialization } from "../../../src/discovery/core/latex_serialization.js";
import { stableJson } from "../../../src/shared/stable_json.js";
import { checkGraph } from "../../../src/discovery/vcs/checks.js";
import { graphFromCore, renderCore } from "../../../src/discovery/vcs/render.js";
import { proofValid } from "../../../src/discovery/vcs/validity.js";

// Every real core the repository holds must survive core → graph → core with no
// loss: same statuses (a proved node gets a fresh basis and is proved again), same
// edges, same prose, same layout. This is the migration contract: the first commit
// of a converted run renders exactly what the old stores published.

const researchRoot = path.resolve(process.cwd(), "..", "doc", "research");

function corpus(): string[] {
  if (!existsSync(researchRoot)) return [];
  return execSync(`find ${JSON.stringify(researchRoot)} -name core.json -path '*discovery*'`, { encoding: "utf8" })
    .trim().split("\n").filter((f) => f.length > 0);
}

describe("vcs corpus roundtrip", () => {
  const files = corpus();
  it.skipIf(files.length === 0)("renders every real core byte-for-byte after conversion", () => {
    let parsed = 0;
    let gatePassing = 0;
    const failures: string[] = [];
    for (const file of files) {
      let core;
      try { core = CoreSchema.parse(JSON.parse(readFileSync(file, "utf8"))); } catch { continue; }
      parsed++;
      const expected = structuredClone(core);
      repairCoreLatexSerialization(expected);
      wireStatementProofDependencies(expected);
      rebuildAssumptionUsedBy(expected);
      const graph = graphFromCore(core);
      const rendered = renderCore(graph);
      if (stableJson(rendered) !== stableJson(CoreSchema.parse(expected))) failures.push(`${file}: render differs`);
      for (const s of core.statements) {
        if (s.status === "proved" && !proofValid(graph, s.id)) failures.push(`${file}: ${s.id} lost its proof`);
      }
      if (runStructuralGate(core).ok) {
        gatePassing++;
        const check = checkGraph(graph);
        if (!check.ok) failures.push(`${file}: checkGraph ${check.violations.map((v) => `${v.code}@${v.where}`).join(",")}`);
      }
    }
    expect(failures).toEqual([]);
    expect(parsed).toBeGreaterThan(0);
    expect(gatePassing).toBeGreaterThan(0);
  }, 120_000);
});

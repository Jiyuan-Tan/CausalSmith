import { afterEach, describe, expect, it, vi } from "vitest";
import { mkdtemp, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";

async function renderProofFillerPrompt(): Promise<string> {
  vi.resetModules();
  const [{ runFiller }, { createEmptyGraph }] = await Promise.all([
    import("../../src/formalization/proof_filler.js"),
    import("../../src/graph/store.js"),
  ]);
  const repoRoot = await mkdtemp(join(tmpdir(), "module-prompt-rendering-"));
  let rendered = "";
  try {
    await runFiller({
      ctx: { repoRoot, qid: "q", specialization: "v1" },
      graph: createEmptyGraph("q", "v1"),
      leanDir: join(repoRoot, "CausalSmith", "Stat", "Q_Research"),
      promptPath: join(process.cwd(), "src/formalization/prompts/F4/proof_filler.txt"),
      deps: {
        runCodex: async (input) => {
          rendered = input.prompt;
          return { stdout: JSON.stringify({ summary: "no work" }), stderr: "" };
        },
      },
    });
  } finally {
    await rm(repoRoot, { recursive: true, force: true });
  }
  return rendered;
}

afterEach(() => {
  vi.resetModules();
});

describe("formalization prompt module header contract", () => {
  it("renders the module contract and consequences", async () => {
    const prompt = await renderProofFillerPrompt();
    expect(prompt).toContain("HEADER CONTRACT — Every generated Lean file");
    expect(prompt).toContain("`public import`");
    expect(prompt).toContain("`-- private import`");
    expect(prompt).toContain("`@[expose] public section`");
    expect(prompt).toContain("must never add `import all`");
    expect(prompt).toContain("`Array.ofFn`");
    expect(prompt).toContain("`termination_by`");
    expect(prompt).not.toContain("{{HEADER_CONTRACT}}");
  });
});

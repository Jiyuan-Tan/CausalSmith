import { execFileSync } from "node:child_process";
import { existsSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";

const repoRoot = path.resolve(process.cwd(), "../..");
const testScript = path.join(
  repoRoot,
  "internal/plans/module_system/scripts/test_move_tools.py",
);

describe("module move tools", () => {
  // The move tools are operator scripts that live outside the published tree, so a
  // checkout without them has nothing to test.
  it.skipIf(!existsSync(testScript))("passes the isolated Python integration suite", () => {
    const output = execFileSync("python3", [testScript], {
      cwd: repoRoot,
      encoding: "utf8",
      timeout: 30_000,
      stdio: ["ignore", "pipe", "pipe"],
    });
    expect(output).toBe("");
  });
});

import { afterEach, describe, expect, it } from "vitest";
import { mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { clearOrphanSolvePathLeases } from "../src/discovery/solve/unit_io.js";
import { formalizationDir } from "../src/paths.js";
import type { PipelineContext } from "../src/types.js";

const roots: string[] = [];

afterEach(async () => {
  delete process.env.CAUSALSMITH_ALLOW_PARALLEL;
  await Promise.all(roots.splice(0).map((root) => rm(root, { recursive: true, force: true })));
});

describe("clearOrphanSolvePathLeases", () => {
  it("reclaims only this qid's stranded solve leases in parallel-qid mode", async () => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "solve-lease-"));
    roots.push(repoRoot);
    const ctx = {
      repoRoot,
      qid: "stat_orphan_reclaim",
      specialization: "v1",
    } as PipelineContext;
    const otherCtx = { ...ctx, qid: "stat_other_run" };
    const ownLock = path.join(formalizationDir(repoRoot, ctx.qid), "discovery", "solve_target.json.lease.lock");
    const otherLock = path.join(formalizationDir(repoRoot, otherCtx.qid), "discovery", "solve_target.json.lease.lock");
    await mkdir(ownLock, { recursive: true });
    await mkdir(otherLock, { recursive: true });
    await writeFile(path.join(ownLock, "owner-token"), "stranded\n");
    await writeFile(path.join(otherLock, "owner-token"), "live-other-qid\n");
    process.env.CAUSALSMITH_ALLOW_PARALLEL = "1";

    await clearOrphanSolvePathLeases(ctx);

    await expect(readFile(path.join(ownLock, "owner-token"), "utf8")).rejects.toMatchObject({ code: "ENOENT" });
    await expect(readFile(path.join(otherLock, "owner-token"), "utf8")).resolves.toBe("live-other-qid\n");
  });
});

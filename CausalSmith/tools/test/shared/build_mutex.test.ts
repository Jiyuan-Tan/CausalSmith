// CausalSmith/tools/test/shared/build_mutex.test.ts
import { describe, it, expect } from "vitest";
import { mkdtemp, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { LockAcquireError, withFileLock, withPromotionLock } from "../../src/shared/build_mutex.js";

describe("withFileLock", () => {
  const impatient = { retries: 1, factor: 1, minTimeout: 5, maxTimeout: 5 };

  it("raises LockAcquireError only when the lock is held by someone else", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "filelock-"));
    try {
      const lockPath = path.join(root, "x.lock");
      let ranWhileHeld = false;
      await withFileLock(lockPath, impatient, async () => {
        await expect(withFileLock(lockPath, impatient, async () => { ranWhileHeld = true; }))
          .rejects.toBeInstanceOf(LockAcquireError);
      });
      expect(ranWhileHeld).toBe(false);
      // Released: the next caller gets it.
      expect(await withFileLock(lockPath, impatient, async () => "ok")).toBe("ok");
      // A lock that cannot be taken for any other reason is an ordinary error.
      const failure = await withFileLock(path.join(root, "missing-dir", "x.lock"), impatient, async () => "ran")
        .catch((err: unknown) => err);
      expect(failure).toBeInstanceOf(Error);
      expect(failure).not.toBeInstanceOf(LockAcquireError);
      // So is an error thrown by the guarded action itself.
      const boom = Object.assign(new Error("boom"), { code: "ELOCKED" });
      await expect(withFileLock(lockPath, impatient, async () => { throw boom; })).rejects.toBe(boom);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });
});

describe("withPromotionLock", () => {
  it("serializes concurrent promotions on the same Causalean root", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "promlock-"));
    try {
      let active = 0;
      let maxActive = 0;
      const task = () =>
        withPromotionLock(root, async () => {
          active += 1;
          maxActive = Math.max(maxActive, active);
          await new Promise((r) => setTimeout(r, 40));
          active -= 1;
        });
      await Promise.all([task(), task(), task()]);
      // The whole point of the promotion mutex: never two promotions at once.
      expect(maxActive).toBe(1);
      expect(active).toBe(0);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it("runs sequentially (each waiter gets the lock in turn, none errors out)", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "promlock-"));
    try {
      const order: number[] = [];
      await Promise.all(
        [0, 1, 2, 3].map((i) =>
          withPromotionLock(root, async () => {
            order.push(i);
            await new Promise((r) => setTimeout(r, 10));
          }),
        ),
      );
      // All four acquired the lock (none dropped on retry exhaustion).
      expect(order.sort()).toEqual([0, 1, 2, 3]);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });
});

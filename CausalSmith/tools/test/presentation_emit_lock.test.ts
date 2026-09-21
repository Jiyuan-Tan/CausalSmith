import { afterEach, describe, expect, it } from "vitest";
import { mkdtemp, readdir, rm, symlink } from "node:fs/promises";
import process from "node:process";
import { tmpdir } from "node:os";
import { join } from "node:path";

import {
  BundleEmitBusyError, EMIT_LOCK_FILE, assertBundleEmitLockHeld, bundleEmitLockCompromise,
  isBundleEmitBusy, isHoldingBundleEmitLock, withBundleEmitLock,
} from "../src/presentation/emit_lock.js";
import { withBundleMetaLock } from "../src/presentation/meta_store.js";
import { withWpRegistryLock } from "../src/presentation/wp_registry.js";

const dirs: string[] = [];
afterEach(async () => {
  await Promise.all(dirs.splice(0).map((dir) => rm(dir, { recursive: true, force: true })));
});

async function bundle(): Promise<string> {
  const dir = await mkdtemp(join(tmpdir(), "emit-lock-"));
  dirs.push(dir);
  return dir;
}

const NOWAIT = { wait: false } as const;

describe("per-bundle emit lock", () => {
  it("admits one holder and refuses a second that will not wait", async () => {
    const dir = await bundle();
    let inside = false;
    const held = withBundleEmitLock(dir, async () => {
      inside = true;
      await new Promise((r) => setTimeout(r, 400));
      return "done";
    }, NOWAIT);
    await new Promise((r) => setTimeout(r, 80));
    expect(inside).toBe(true);
    const refused = await withBundleEmitLock(dir, async () => "second", NOWAIT).catch((e: unknown) => e);
    expect(isBundleEmitBusy(refused)).toBe(true);
    expect(refused).toBeInstanceOf(BundleEmitBusyError);
    expect((refused as Error).message).toMatch(/another emit of this bundle is running/);
    expect(await held).toBe("done");
    // ...and once it is free the same acquisition succeeds
    expect(await withBundleEmitLock(dir, async () => "third", NOWAIT)).toBe("third");
  });

  it("makes a waiting emit queue behind the holder rather than fail", async () => {
    const dir = await bundle();
    const order: string[] = [];
    const first = withBundleEmitLock(dir, async () => {
      order.push("first-in");
      await new Promise((r) => setTimeout(r, 500));
      order.push("first-out");
    }, NOWAIT);
    await new Promise((r) => setTimeout(r, 80));
    const second = withBundleEmitLock(dir, async () => { order.push("second-in"); },
      { wait: true, retries: { retries: 30, factor: 1, minTimeout: 100, maxTimeout: 100 } });
    await Promise.all([first, second]);
    expect(order).toEqual(["first-in", "first-out", "second-in"]);
  });

  it("locks each bundle independently", async () => {
    const [a, b] = [await bundle(), await bundle()];
    const held = withBundleEmitLock(a, () => new Promise((r) => setTimeout(r, 300)), NOWAIT);
    await new Promise((r) => setTimeout(r, 60));
    expect(await withBundleEmitLock(b, async () => "b ran", NOWAIT)).toBe("b ran");
    await held;
  });

  it("releases the lock when the emit throws", async () => {
    const dir = await bundle();
    await expect(withBundleEmitLock(dir, async () => { throw new Error("emit blew up"); }, NOWAIT))
      .rejects.toThrow("emit blew up");
    expect(isHoldingBundleEmitLock(dir)).toBe(false);
    expect(await withBundleEmitLock(dir, async () => "recovered", NOWAIT)).toBe("recovered");
  });

  it("keeps refreshing a long-held lock so a contender cannot steal it as stale", async () => {
    const dir = await bundle();
    // Thresholds far shorter than production's: the lock is held well past `staleMs`, and the
    // periodic `update` is the only thing stopping a contender from "recovering" it. Without the
    // refresh this acquisition succeeds and two emitters rewrite paper.tex at once.
    const short = { staleMs: 2_000, updateMs: 300 };
    const held = withBundleEmitLock(dir, () => new Promise((r) => setTimeout(r, 4_500)), { ...short, wait: false });
    await new Promise((r) => setTimeout(r, 3_200)); // > staleMs
    const refused = await withBundleEmitLock(dir, async () => "stolen", { ...short, wait: false })
      .catch((e: unknown) => e);
    expect(isBundleEmitBusy(refused)).toBe(true);
    await held;
  }, 20_000);

  it("reports whether the caller is inside a held lock", async () => {
    const dir = await bundle();
    expect(isHoldingBundleEmitLock(dir)).toBe(false);
    await withBundleEmitLock(dir, async () => { expect(isHoldingBundleEmitLock(dir)).toBe(true); }, NOWAIT);
    expect(isHoldingBundleEmitLock(dir)).toBe(false);
  });

  // Holding A's lock says NOTHING about B. The answer used to be a bare "am I inside any emit
  // lock?", so a nested call for a different bundle read "already held", skipped its own
  // acquisition, and wrote to B with no exclusivity at all — while the checkpoint before that
  // write reported everything fine.
  it("answers per BUNDLE, not per call stack", async () => {
    const [a, b] = [await bundle(), await bundle()];
    await withBundleEmitLock(a, async () => {
      expect(isHoldingBundleEmitLock(a)).toBe(true);
      expect(isHoldingBundleEmitLock(b)).toBe(false);
      // ...and the same distinction at the write checkpoint.
      expect(() => assertBundleEmitLockHeld(a)).not.toThrow();
      expect(() => assertBundleEmitLockHeld(b)).toThrow(/DIFFERENT bundle/);
    }, NOWAIT);
  });

  it("sees through a symlinked bundle directory to the same lock", async () => {
    const dir = await bundle();
    const link = `${dir}-link`;
    await symlink(dir, link, "dir");
    await withBundleEmitLock(dir, async () => {
      expect(isHoldingBundleEmitLock(link)).toBe(true);
      expect(() => assertBundleEmitLockHeld(link)).not.toThrow();
    }, NOWAIT);
  });

  it("refuses the write checkpoint when NO lock is held at all", async () => {
    const dir = await bundle();
    // The checkpoint only looked at the compromise flag, so an unlocked caller sailed through —
    // the exact case it exists to catch, since never taking the lock and losing it leave the
    // writer equally exposed.
    expect(() => assertBundleEmitLockHeld(dir)).toThrow(/no emit lock is held for/);
    expect(() => assertBundleEmitLockHeld(dir)).toThrow(/withBundleEmitLock/);
  });

  it("leaves no lock debris behind", async () => {
    const dir = await bundle();
    await withBundleEmitLock(dir, async () => {}, NOWAIT);
    // the sentinel remains (it is gitignored); proper-lockfile's directory must not
    const entries = await readdir(dir);
    expect(entries).toContain(EMIT_LOCK_FILE);
    expect(entries).not.toContain(`${EMIT_LOCK_FILE}.lock`);
  });
});

describe("lock ordering: emit → registry → meta", () => {
  it("refuses the emit lock while the registry lock is held", async () => {
    const dir = await bundle();
    await expect(withWpRegistryLock(dir, () => withBundleEmitLock(dir, async () => "x", NOWAIT)))
      .rejects.toThrow(/lock order violation/);
  });

  it("refuses the emit lock while a bundle meta lock is held", async () => {
    const dir = await bundle();
    await expect(withBundleMetaLock(dir, () => withBundleEmitLock(dir, async () => "x", NOWAIT)))
      .rejects.toThrow(/lock order violation/);
  });

  it("allows the documented order, all three nested", async () => {
    const dir = await bundle();
    const seen = await withBundleEmitLock(dir, () =>
      withWpRegistryLock(dir, () =>
        withBundleMetaLock(dir, async () => "innermost")), NOWAIT);
    expect(seen).toBe("innermost");
  });
});

describe("a lock that gets compromised fails the operation, not the process", () => {
  it("surfaces a stolen emit lock as a controlled error naming the bundle", async () => {
    const dir = await bundle();
    let sawHealthyThenNot: [boolean, boolean] | null = null;
    const outcome = await withBundleEmitLock(dir, async () => {
      const healthy = bundleEmitLockCompromise() === null;
      // Somebody removes the mutex directory out from under us.
      await rm(join(dir, `${EMIT_LOCK_FILE}.lock`), { recursive: true, force: true });
      await new Promise((r) => setTimeout(r, 2_500)); // past the update interval
      sawHealthyThenNot = [healthy, bundleEmitLockCompromise() !== null];
      assertBundleEmitLockHeld(dir); // what P4 calls before its final writes
      return "should not get here";
    }, { wait: false, staleMs: 2_000, updateMs: 200 }).catch((e: unknown) => e);
    expect(sawHealthyThenNot).toEqual([true, true]);
    expect(outcome).toBeInstanceOf(Error);
    expect((outcome as Error).message).toMatch(/emit lock .* was lost/i);
    expect((outcome as Error).message).toContain(dir);
  }, 20_000);

  it("does not leave an uncaught exception behind when the lock is compromised", async () => {
    const dir = await bundle();
    const seen: unknown[] = [];
    const onUnhandled = (e: unknown) => seen.push(e);
    process.on("uncaughtException", onUnhandled);
    try {
      await withBundleEmitLock(dir, async () => {
        await rm(join(dir, `${EMIT_LOCK_FILE}.lock`), { recursive: true, force: true });
        await new Promise((r) => setTimeout(r, 2_500));
      }, { wait: false, staleMs: 2_000, updateMs: 1_000 }).catch(() => {});
      await new Promise((r) => setTimeout(r, 300));
    } finally {
      process.off("uncaughtException", onUnhandled);
    }
    expect(seen).toEqual([]);
  }, 20_000);

  it("names the lock path and the stale window when a bundle is busy", async () => {
    const dir = await bundle();
    const held = withBundleEmitLock(dir, () => new Promise((r) => setTimeout(r, 300)), { wait: false });
    await new Promise((r) => setTimeout(r, 60));
    const err = await withBundleEmitLock(dir, async () => "x", { wait: false }).catch((e: Error) => e);
    expect((err as Error).message).toContain(join(dir, EMIT_LOCK_FILE));
    expect((err as Error).message).toMatch(/30 minutes/);
    expect((err as Error).message).toMatch(/remove .* once you have confirmed no emit is running/);
    await held;
  });

  it("fails immediately on an acquisition error that waiting cannot fix", async () => {
    // A directory that does not exist and cannot be created: retrying for ten minutes is useless.
    const missing = join(await bundle(), "no", "such", "\0bad");
    const started = Date.now();
    await expect(withBundleEmitLock(missing, async () => "x", { wait: true })).rejects.toThrow();
    expect(Date.now() - started).toBeLessThan(5_000);
  });
});

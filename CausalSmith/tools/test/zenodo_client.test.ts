// The Zenodo client's load-bearing behaviours, none of which the happy path exercises:
// it must not leak the token, it must survive rate limiting WITHOUT ever replaying a
// non-idempotent request, it must never let a server-supplied link or a redirect move it
// between instances, and it must never turn an unusable 2xx body into a made-up record.
//
// The token rule is the one worth stating plainly. A personal access token grants
// permanent, irrevocable publishing rights on the user's account; a single copy in a
// CI log, a test snapshot, or a thrown error that gets pasted into an issue is a
// disclosure that cannot be walked back. So redaction is asserted at the boundary —
// on every thrown error and every logged line — rather than trusted to call sites.
//
// The retry rule comes from a measured surprise: the sandbox returns `Retry-After` on
// SUCCESSFUL responses too (it is "seconds left in the rate-limit window", not a
// backoff instruction). A client that honoured it unconditionally would sleep ~60s
// after every 2xx, so the header is read only on a retryable status, and that is
// pinned here.

import { describe, it, expect, beforeEach } from "vitest";
import {
  PRODUCTION,
  SANDBOX,
  ZenodoAmbiguousError,
  ZenodoClient,
  ZenodoError,
  isSandboxDoi,
  redactSecrets,
} from "../src/zenodo/client.js";
import { reserve } from "../src/zenodo/deposit.js";
import { readSidecar } from "../src/zenodo/bundle.js";
import { TEST_TOKEN, zenodoTestBed, type FakeCall, type FetchImpl } from "./zenodo_fixtures.js";

const TOKEN = TEST_TOKEN;

// The harness-level request record, for the tests below that hand-roll a `fetch`. Tests
// built on `client(...)` destructure their own `calls` and shadow this one.
const { h, fakeZenodo, ctxFor } = zenodoTestBed();
let calls: FakeCall[];
let dir: string;
beforeEach(() => {
  ({ calls, dir } = h);
});

interface Call {
  method: string;
  url: string;
  authorization: string | undefined;
  body: string | undefined;
}

interface Reply {
  status: number;
  body?: unknown;
  text?: string;
  headers?: Record<string, string>;
}

/** A fake `fetch` that replays `replies` in order and records every call. */
function fakeFetch(replies: Reply[]): {
  impl: (url: string, init?: RequestInit) => Promise<Response>;
  calls: Call[];
} {
  const calls: Call[] = [];
  let i = 0;
  const impl = async (url: string, init?: RequestInit): Promise<Response> => {
    const headers = (init?.headers ?? {}) as Record<string, string>;
    calls.push({
      method: init?.method ?? "GET",
      url,
      authorization: headers.Authorization,
      body: typeof init?.body === "string" ? init.body : undefined,
    });
    const reply = replies[Math.min(i, replies.length - 1)];
    i += 1;
    const text = reply.text ?? (reply.body === undefined ? "" : JSON.stringify(reply.body));
    return new Response(text, { status: reply.status, headers: reply.headers });
  };
  return { impl, calls };
}

function client(
  replies: Reply[],
  opts: { sleeps?: number[]; log?: string[]; env?: typeof SANDBOX } = {},
) {
  const { impl, calls } = fakeFetch(replies);
  const sleeps = opts.sleeps ?? [];
  const log = opts.log ?? [];
  const c = new ZenodoClient({
    env: opts.env ?? SANDBOX,
    tokenProvider: async () => TOKEN,
    fetchImpl: impl,
    sleep: async (ms) => void sleeps.push(ms),
    maxRetries: 3,
    backoffBaseMs: 100,
    log: (line) => log.push(line),
  });
  return { c, calls, sleeps, log };
}

describe("redactSecrets", () => {
  it("removes the literal token wherever it appears", () => {
    const out = redactSecrets(`failed with ${TOKEN} in the url`, TOKEN);
    expect(out).not.toContain(TOKEN);
    expect(out).toContain("<REDACTED>");
  });

  it("removes token-shaped material even when the literal is unknown", () => {
    const out = redactSecrets(`Authorization: Bearer ${TOKEN}; access_token=${TOKEN}&x=1`);
    expect(out).not.toContain(TOKEN);
    expect(out).toContain("access_token=<REDACTED>");
    expect(out).toContain("Bearer <REDACTED>");
  });

  it("leaves ordinary text alone", () => {
    expect(redactSecrets("concept DOI 10.5072/zenodo.606199", TOKEN))
      .toBe("concept DOI 10.5072/zenodo.606199");
  });
});

describe("DOI derivation", () => {
  it("composes the concept DOI from the environment prefix, not from prereserve_doi", () => {
    // The sandbox's prereserve_doi claims 10.5281 while it actually mints 10.5072.
    const { c } = client([{ status: 200, body: {} }]);
    expect(c.conceptDoi(606199)).toBe("10.5072/zenodo.606199");
    expect(c.versionDoi(606200)).toBe("10.5072/zenodo.606200");
  });

  it("uses the production prefix on the production instance", () => {
    const { c } = client([{ status: 200, body: {} }], { env: PRODUCTION });
    expect(c.conceptDoi(999)).toBe("10.5281/zenodo.999");
  });

  it("recognises a sandbox DOI so it can be kept out of meta.json", () => {
    expect(isSandboxDoi("10.5072/zenodo.606199")).toBe(true);
    expect(isSandboxDoi("10.5281/zenodo.606199")).toBe(false);
    expect(isSandboxDoi(null)).toBe(false);
  });
});

describe("token handling", () => {
  it("sends the token as a bearer header and never in the URL", async () => {
    const { c, calls } = client([{ status: 201, body: { id: 1, conceptrecid: 2, links: { bucket: "https://sandbox.zenodo.org/api/files/b" } } }]);
    await c.createDraft();
    expect(calls[0].authorization).toBe(`Bearer ${TOKEN}`);
    expect(calls[0].url).not.toContain(TOKEN);
  });

  it("keeps the token out of a thrown error, even when Zenodo echoes it back", async () => {
    const { c } = client([
      { status: 400, body: { message: `Bad request for access_token=${TOKEN}`, errors: [{ field: "metadata.title", messages: ["is required"] }] } },
    ]);
    const err = await c.createDraft().then(() => null, (e: unknown) => e);
    expect(err).toBeInstanceOf(ZenodoError);
    const zerr = err as ZenodoError;
    expect(zerr.status).toBe(400);
    expect(zerr.message).not.toContain(TOKEN);
    expect(JSON.stringify(zerr)).not.toContain(TOKEN);
    expect(zerr.message).toContain("metadata.title: is required");
  });

  it("keeps the token out of an error whose body is not JSON", async () => {
    const { c } = client([{ status: 502, text: `<html>proxy error ${TOKEN}</html>` }]);
    const err = await c
      .getDeposition(5)
      .then(() => null, (e: unknown) => (e instanceof Error ? e.message : String(e)));
    expect(String(err)).not.toContain(TOKEN);
  });

  it("keeps the token out of an error raised before any response", async () => {
    const boom = async (): Promise<Response> => {
      throw new Error(`socket hang up while sending Bearer ${TOKEN}`);
    };
    const c = new ZenodoClient({
      env: SANDBOX,
      tokenProvider: async () => TOKEN,
      fetchImpl: boom,
      sleep: async () => {},
      maxRetries: 0,
    });
    const msg = await c.getDeposition(1).then(() => "", (e: unknown) => (e as Error).message);
    expect(msg).not.toContain(TOKEN);
    expect(msg).toContain("<REDACTED>");
  });

  it("keeps the token out of the request log and the dry-run transcript", async () => {
    const log: string[] = [];
    // A GET, because a POST is never replayed, 429 included.
    const { c } = client([{ status: 429, headers: { "retry-after": "1" } }, { status: 200, body: { id: 7, conceptrecid: 6, links: {} } }], { log });
    await c.getDeposition(7);
    expect(log.length).toBeGreaterThan(0);
    expect(log.join("\n")).not.toContain(TOKEN);
    expect(c.requestLog.join("\n")).not.toContain(TOKEN);
  });
});

describe("retry and backoff", () => {
  it("honours Retry-After on a 429 for an idempotent request", async () => {
    const sleeps: number[] = [];
    const { c, calls } = client(
      [{ status: 429, headers: { "retry-after": "2" } }, { status: 200, body: { id: 1, conceptrecid: 2 } }],
      { sleeps },
    );
    expect((await c.getDeposition(1)).id).toBe(1);
    expect(calls).toHaveLength(2);
    expect(sleeps).toEqual([2000]);
  });

  it("does NOT sleep on a Retry-After returned with a successful response", async () => {
    // The sandbox sends `retry-after: 59` alongside 2xx; treating that as a backoff
    // instruction would stall every successful call for a minute.
    const sleeps: number[] = [];
    const { c } = client([{
      status: 201, headers: { "retry-after": "59" },
      body: { id: 1, conceptrecid: 2, links: { bucket: "https://sandbox.zenodo.org/api/files/b" } },
    }], { sleeps });
    await c.createDraft();
    expect(sleeps).toEqual([]);
  });

  it("backs off exponentially with jitter on 5xx (idempotent request)", async () => {
    const sleeps: number[] = [];
    const { c, calls } = client(
      [{ status: 500 }, { status: 503 }, { status: 200, body: { id: 3, conceptrecid: 2 } }],
      { sleeps },
    );
    await c.getDeposition(3);
    expect(calls).toHaveLength(3);
    expect(sleeps).toHaveLength(2);
    // base 100ms: ceilings are 100 and 200, with full jitter in [ceiling/2, ceiling].
    expect(sleeps[0]).toBeGreaterThanOrEqual(50);
    expect(sleeps[0]).toBeLessThanOrEqual(100);
    expect(sleeps[1]).toBeGreaterThanOrEqual(100);
    expect(sleeps[1]).toBeLessThanOrEqual(200);
  });

  it("gives up after maxRetries and surfaces the last status", async () => {
    const sleeps: number[] = [];
    const { c, calls } = client([{ status: 503, body: { message: "upstream down" } }], { sleeps });
    const err = await c.getDeposition(1).then(() => null, (e: unknown) => e as ZenodoError);
    expect(calls).toHaveLength(4); // 1 attempt + 3 retries
    expect(err?.status).toBe(503);
    expect(err?.zenodoMessage).toBe("upstream down");
  });

  it("does not retry a 4xx that is not 429", async () => {
    const { c, calls } = client([{ status: 403, body: { message: "forbidden" } }]);
    await c.publish(1).catch(() => {});
    expect(calls).toHaveLength(1);
  });

  it("caps a hostile Retry-After at maxSleepMs", async () => {
    const sleeps: number[] = [];
    const { impl } = fakeFetch([{ status: 429, headers: { "retry-after": "86400" } }, { status: 200, body: { id: 1 } }]);
    const c = new ZenodoClient({
      env: SANDBOX,
      tokenProvider: async () => TOKEN,
      fetchImpl: impl,
      sleep: async (ms) => void sleeps.push(ms),
      maxRetries: 2,
      maxSleepMs: 5_000,
    });
    await c.getDeposition(1);
    expect(sleeps).toEqual([5_000]);
  });

  it("retries a network-level failure on an idempotent request", async () => {
    const sleeps: number[] = [];
    let n = 0;
    const impl = async (): Promise<Response> => {
      n += 1;
      if (n === 1) throw new Error("ECONNRESET");
      return new Response(JSON.stringify({ id: 9, conceptrecid: 8 }), { status: 200 });
    };
    const c = new ZenodoClient({
      env: SANDBOX,
      tokenProvider: async () => TOKEN,
      fetchImpl: impl,
      sleep: async (ms) => void sleeps.push(ms),
      maxRetries: 2,
      backoffBaseMs: 10,
    });
    expect((await c.getDeposition(9)).id).toBe(9);
    expect(sleeps).toHaveLength(1);
  });
});

describe("instance containment", () => {
  it("refuses to follow a link that points at the other instance", async () => {
    const { c } = client([
      { status: 201, body: { id: 1, links: { latest_draft: "https://zenodo.org/api/deposit/depositions/999" } } },
    ]);
    const msg = await c.newVersion(1).then(() => "", (e: unknown) => (e as Error).message);
    expect(msg).toContain("Refusing to follow");
    expect(msg).toContain("https://zenodo.org");
  });

  it("fails loudly when newversion returns no latest_draft rather than guessing an id", async () => {
    const { c } = client([{ status: 201, body: { id: 1, links: {} } }]);
    const msg = await c.newVersion(1).then(() => "", (e: unknown) => (e as Error).message);
    expect(msg).toContain("no links.latest_draft");
  });
});

describe("operations", () => {
  it("treats a 404 as 'no such deposition' rather than an error", async () => {
    const { c } = client([{ status: 404, body: { message: "The persistent identifier does not exist." } }]);
    expect(await c.getDepositionOrNull(606202)).toBeNull();
  });

  it("uploads through the bucket API, which replaces an existing key in place", async () => {
    const { c, calls } = client([{ status: 201, body: { key: "paper.pdf", size: 4, checksum: "md5:x" } }]);
    const out = await c.uploadFile("https://sandbox.zenodo.org/api/files/abc", "paper.pdf", new Uint8Array([1, 2, 3, 4]));
    expect(calls[0].method).toBe("PUT");
    expect(calls[0].url).toBe("https://sandbox.zenodo.org/api/files/abc/paper.pdf");
    expect(out.key).toBe("paper.pdf");
  });

  it("follows links.latest_draft to the new draft on newVersion", async () => {
    const { c, calls } = client([
      { status: 201, body: { id: 1, links: { latest_draft: "https://sandbox.zenodo.org/api/deposit/depositions/606203" } } },
      { status: 200, body: { id: 606203, conceptrecid: 606199, conceptdoi: "10.5072/zenodo.606199", state: "unsubmitted" } },
    ]);
    const draft = await c.newVersion(606200);
    expect(draft.id).toBe(606203);
    expect(draft.conceptrecid).toBe(606199);
    expect(calls[1].method).toBe("GET");
  });

  it("sends nothing that mutates under dryRun, but still records the request", async () => {
    const { impl, calls } = fakeFetch([{ status: 201, body: { id: 1 } }]);
    const c = new ZenodoClient({ env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, dryRun: true });
    await c.createDraft();
    await c.publish(1);
    await c.deleteDraft(1);
    expect(calls).toHaveLength(0);
    expect(c.requestLog).toHaveLength(3);
    expect(c.requestLog[0]).toContain("POST https://sandbox.zenodo.org/api/deposit/depositions");
  });

  it("does NOT stub a malformed success outside dry-run", async () => {
    const { impl } = fakeFetch([{ status: 201, text: "not json" }]);
    const c = new ZenodoClient({ env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl });
    await expect(c.createDraft()).rejects.toThrow(/valid JSON/i);
  });
});

// Replaying a create, publish or new-version can duplicate a permanent record, so an
// ambiguous outcome is surfaced rather than retried. A 429 is no exception: it says a rate
// limiter refused the request, not WHICH layer refused it, and a proxy can rate-limit a call
// an upstream already performed.
describe("a non-idempotent POST is never replayed", () => {
  type Failure = "network" | 503 | 429;

  /** Fails the FIRST request as `failure` says and answers 201 from then on, so a replay
   *  would succeed — and be seen both as a resolved promise and as a second call. */
  function failingOnce(failure: Failure): FetchImpl {
    let n = 0;
    return async (url, init) => {
      calls.push({ method: init?.method ?? "GET", url });
      n += 1;
      if (n > 1) {
        return new Response(JSON.stringify({ id: 100, conceptrecid: 99, links: { bucket: "b" } }), { status: 201 });
      }
      if (failure === "network") throw new Error("ECONNRESET");
      return new Response(JSON.stringify({ message: "upstream" }), {
        status: failure, headers: failure === 429 ? { "retry-after": "1" } : undefined,
      });
    };
  }

  const clientOver = (fetchImpl: FetchImpl, maxRetries: number) => new ZenodoClient({
    env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl, sleep: async () => {}, maxRetries,
  });

  const post = {
    createDraft: (c: ZenodoClient) => c.createDraft(),
    publish: (c: ZenodoClient) => c.publish(1),
    newVersion: (c: ZenodoClient) => c.newVersion(1),
  };
  const cases = (["network", 503, 429] as const).flatMap((failure) =>
    (["createDraft", "publish", "newVersion"] as const).map((op) => ({ failure, op })));

  it.each(cases)("$op is sent exactly once after a $failure failure", async ({ failure, op }) => {
    const c = clientOver(failingOnce(failure), 4);
    await expect(post[op](c)).rejects.toBeInstanceOf(ZenodoAmbiguousError);
    expect(calls.filter((x) => x.method === "POST")).toHaveLength(1);
    expect(calls).toHaveLength(1);
  });

  it("tells the operator to re-run, since re-running reconciles", async () => {
    const msg = await clientOver(failingOnce(429), 4).createDraft().then(() => "", (e: Error) => e.message);
    expect(msg).toMatch(/re-run/i);
  });

  it("retries an idempotent GET after a 5xx", async () => {
    const c = clientOver(failingOnce(503), 3);
    await expect(c.getDeposition(100)).resolves.toBeTruthy();
    expect(calls.filter((x) => x.method === "GET")).toHaveLength(2);
  });

  it("retries an idempotent GET on 429", async () => {
    let n = 0;
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      calls.push({ method: init?.method ?? "GET", url });
      n += 1;
      if (n === 1) return new Response("{}", { status: 429, headers: { "retry-after": "1" } });
      return new Response(JSON.stringify({ id: 5, conceptrecid: 4, links: {} }), { status: 200 });
    };
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {}, maxRetries: 3,
    });
    expect((await c.getDeposition(5)).id).toBe(5);
    expect(calls).toHaveLength(2);
  });
});

describe("request timeouts", () => {
  it("treats a POST timeout as ambiguous and a GET timeout as retryable", async () => {
    const hang = async (_u: string, init?: RequestInit): Promise<Response> => {
      await new Promise((_r, reject) => {
        init?.signal?.addEventListener("abort", () => reject(new Error("The operation was aborted")));
      });
      throw new Error("unreachable");
    };
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: hang,
      sleep: async () => {}, maxRetries: 1, requestTimeoutMs: 20,
    });
    await expect(c.createDraft()).rejects.toThrow(/UNKNOWN outcome/);
    await expect(c.getDeposition(1)).rejects.toThrow(/timed out|aborted|before a response/i);
  }, 30_000);
});

// A redirect must not carry an authenticated request to the other instance.
describe("redirects", () => {
  it("does not follow a redirect to production", async () => {
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      calls.push({ method: init?.method ?? "GET", url });
      expect(init?.redirect).toBe("manual");
      return new Response(null, { status: 302, headers: { location: "https://zenodo.org/api/deposit/depositions/1" } });
    };
    const c = new ZenodoClient({ env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {} });
    await expect(c.getDeposition(1)).rejects.toThrow(/redirect|zenodo\.org/i);
    expect(calls).toHaveLength(1);
  });

  it("follows a same-origin redirect", async () => {
    let n = 0;
    const impl = async (url: string, init?: RequestInit): Promise<Response> => {
      calls.push({ method: init?.method ?? "GET", url });
      n += 1;
      if (n === 1) {
        return new Response(null, { status: 302, headers: { location: "https://sandbox.zenodo.org/api/deposit/depositions/2" } });
      }
      return new Response(JSON.stringify({ id: 2, conceptrecid: 1, links: {} }), { status: 200 });
    };
    const c = new ZenodoClient({ env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {} });
    expect((await c.getDeposition(1)).id).toBe(2);
    expect(calls).toHaveLength(2);
  });
});

describe("credentials never reach a log line or an error", () => {
  it("never logs a query string, even under an unrecognised parameter name", async () => {
    const log: string[] = [];
    const impl = async (): Promise<Response> =>
      new Response(JSON.stringify({ id: 1, conceptrecid: 2, links: {} }), { status: 200 });
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {}, log: (l) => log.push(l),
    });
    await c.getByUrl(`https://sandbox.zenodo.org/api/deposit/depositions/1?token=${TOKEN}&secret=${TOKEN}`);
    const all = [...log, ...c.requestLog].join("\n");
    expect(all).not.toContain(TOKEN);
    expect(all).not.toContain("token=");
    expect(all).not.toContain("?");
  });

  it("never logs URL userinfo", async () => {
    const log: string[] = [];
    const impl = async (): Promise<Response> =>
      new Response(JSON.stringify({ id: 1, conceptrecid: 2, links: {} }), { status: 200 });
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {}, log: (l) => log.push(l),
    });
    await c.getByUrl(`https://user:${TOKEN}@sandbox.zenodo.org/api/deposit/depositions/1`).catch(() => {});
    const all = [...log, ...c.requestLog].join("\n");
    expect(all).not.toContain(TOKEN);
    expect(all).not.toContain("@sandbox");
  });

  it("does not retain an unsanitised cause", async () => {
    const impl = async (): Promise<Response> => {
      const err = new Error("connect failed");
      (err as Error & { cause?: unknown }).cause = new Error(`Bearer ${TOKEN} at https://u:${TOKEN}@h/x`);
      throw err;
    };
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {}, maxRetries: 0,
    });
    const err = await c.createDraft().then(() => null, (e: unknown) => e);
    expect(JSON.stringify(err, Object.getOwnPropertyNames(err))).not.toContain(TOKEN);
    expect((err as { cause?: unknown }).cause).toBeUndefined();
  });

  it("sanitises a failure while reading the response body", async () => {
    const impl = async (): Promise<Response> => ({
      ok: true, status: 200,
      headers: new Headers(),
      text: async () => { throw new Error(`stream aborted: Bearer ${TOKEN}`); },
    } as unknown as Response);
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {}, maxRetries: 0,
    });
    const msg = await c.getDeposition(1).then(() => "", (e: Error) => e.message);
    expect(msg).not.toContain(TOKEN);
  });
});

describe("a 2xx with an unusable body is an error, never a stubbed record", () => {
  it.each([
    { what: "an empty body, instead of inventing record 0", body: "", pattern: /empty|body|malformed|invalid/i },
    { what: "JSON that lacks a numeric id", body: JSON.stringify({ conceptrecid: 9 }), pattern: /id/i },
    { what: "a draft with no conceptrecid, rather than deriving 10.5072/zenodo.0", body: JSON.stringify({ id: 5 }), pattern: /conceptrecid/i },
  ])("rejects a 201 carrying $what", async ({ body, pattern }) => {
    const impl = async (): Promise<Response> => new Response(body, { status: 201 });
    const c = new ZenodoClient({ env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {} });
    await expect(c.createDraft()).rejects.toThrow(pattern);
  });
});

describe("a repeated DELETE returns 404 and that is not an error", () => {
  it("deleteDraft reports alreadyGone rather than throwing", async () => {
    // Removing `allow404: true` from deleteDraft makes this throw ZenodoError 404.
    const { impl, drafts } = fakeZenodo();
    await reserve(ctxFor(impl));
    const id = (await readSidecar(dir)).sandbox!.draft!.deposition_id;
    const c = new ZenodoClient({
      env: SANDBOX, tokenProvider: async () => TOKEN, fetchImpl: impl, sleep: async () => {},
    });
    expect(await c.deleteDraft(id)).toEqual({ alreadyGone: false });
    expect(drafts.has(id)).toBe(false);
    expect(await c.deleteDraft(id)).toEqual({ alreadyGone: true });
  });
});

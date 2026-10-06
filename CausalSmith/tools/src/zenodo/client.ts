/** A small typed Zenodo deposition client.
 *
 * WHAT IT IS FOR. CausalSmith working papers need one citable DOI per paper that is
 * knowable BEFORE the PDF is compiled, because the DOI is stamped into page 1 of the
 * PDF (plan decision 5/6). Zenodo's "concept DOI" is that identifier: it addresses the
 * paper, not one version of it, and it never changes as versions are added.
 *
 * WHAT THE SANDBOX ACTUALLY DOES (probed 2026-09-20/21 against sandbox.zenodo.org —
 * every claim below is observed, not from the docs):
 *
 *  - `POST /deposit/depositions` with an empty body returns `conceptrecid` and
 *    `metadata.prereserve_doi = {doi, recid}`. It does NOT return `conceptdoi` or
 *    `doi`; those appear only once the deposition is published.
 *  - The eventual concept DOI IS `<prefix>/zenodo.<conceptrecid>` — predicted
 *    `10.5072/zenodo.606199` at draft time and the published record carried exactly
 *    that. So the concept DOI is knowable before the first publish.
 *  - **`prereserve_doi.doi` carries the WRONG PREFIX on the sandbox**: it came back as
 *    `10.5281/zenodo.606200` (the production prefix) while the record actually
 *    published under `10.5072/zenodo.606200`.
 *  - **`conceptrecid` is a STRING** in some responses and a number in others, so every
 *    record id goes through {@link toRecordId}.
 *  - `Retry-After` is returned on SUCCESSFUL (2xx) responses too — it is the seconds
 *    left in the rate-limit window, not a backoff instruction.
 *  - The default deposit listing does NOT include unpublished drafts (it returned only
 *    `state: "done"` rows). `?status=draft` does, and a quoted-phrase `q="<marker>"`
 *    matches text in `metadata.notes`. Both together are what {@link
 *    ZenodoClient.findDraftsByMarker} uses.
 *
 * THREE RULES THIS MODULE ENFORCES, each from a real failure mode:
 *
 *  1. **DOIs are composed locally, never copied from a response.** The prefix bug above
 *     means a response's `doi`/`conceptdoi` cannot be trusted; callers treat them as
 *     assertions to check, and {@link ZenodoClient.conceptDoi} is the only source.
 *  2. **A non-idempotent request is never blindly replayed.** A timeout or a 5xx on a
 *     `POST` does not prove Zenodo did nothing — replaying a draft creation mints a
 *     second concept DOI for the same paper. Those raise {@link ZenodoAmbiguousError}
 *     so the caller can reconcile against the server instead of guessing.
 *  3. **The token never reaches a log line.** URLs are logged as origin + path only,
 *     with no query string and no userinfo, because a credential can arrive in a
 *     server-supplied link under a parameter name we do not recognise.
 */

import { readFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";

/** Which Zenodo instance to talk to. */
export type ZenodoEnvironmentName = "sandbox" | "production";

export interface ZenodoEnvironment {
  readonly name: ZenodoEnvironmentName;
  /** API root, no trailing slash. */
  readonly apiBase: string;
  /** Web root, for building human-facing record URLs. */
  readonly webBase: string;
  /** DataCite prefix this instance mints under. Sandbox mints 10.5072 even though
   *  `prereserve_doi` claims 10.5281 — see the module docstring. */
  readonly doiPrefix: string;
  /** Path under `~/.zenodo/` holding this instance's personal access token. */
  readonly tokenFile: string;
}

export const SANDBOX: ZenodoEnvironment = {
  name: "sandbox",
  apiBase: "https://sandbox.zenodo.org/api",
  webBase: "https://sandbox.zenodo.org",
  doiPrefix: "10.5072",
  tokenFile: "sandbox_token",
};

export const PRODUCTION: ZenodoEnvironment = {
  name: "production",
  apiBase: "https://zenodo.org/api",
  webBase: "https://zenodo.org",
  doiPrefix: "10.5281",
  tokenFile: "token",
};

/** Sandbox is the default everywhere: a production deposit is permanent and is the
 *  user's decision, never a tool default. */
export const DEFAULT_ENVIRONMENT: ZenodoEnvironment = SANDBOX;

export function environmentByName(name: ZenodoEnvironmentName): ZenodoEnvironment {
  return name === "production" ? PRODUCTION : SANDBOX;
}

/** True for a DOI minted by the sandbox. Such a DOI resolves to nothing and must never
 *  reach a real bundle's `meta.json` or the live site. */
export function isSandboxDoi(doi: string | null | undefined): boolean {
  return typeof doi === "string" && doi.trim().startsWith(`${SANDBOX.doiPrefix}/`);
}

/** Coerce a Zenodo record id to a positive integer.
 *
 *  `conceptrecid` comes back as a string in some responses and a number in others, and
 *  every DOI this tool writes is built from one of these. A silent `Number(undefined)`
 *  would produce `NaN` and then the DOI `…/zenodo.NaN`; a silent `Number(null)` would
 *  produce the equally wrong `…/zenodo.0`. Returning null forces the caller to fail. */
export function toRecordId(value: unknown): number | null {
  if (typeof value === "number") return Number.isInteger(value) && value > 0 ? value : null;
  if (typeof value === "string" && /^\d+$/.test(value.trim())) {
    const n = Number(value.trim());
    return Number.isSafeInteger(n) && n > 0 ? n : null;
  }
  return null;
}

// ---------------------------------------------------------------------------
// Redaction
// ---------------------------------------------------------------------------

/** Patterns that match a credential even when we do not have the literal value to
 *  compare against — the safety net for anything this module did not construct
 *  itself (a Zenodo error body echoing the query string, a Node fetch cause chain). */
const SECRET_PATTERNS: readonly RegExp[] = [
  /(Bearer\s+)[A-Za-z0-9._~+/=-]{8,}/gi,
  /((?:access_token|api_key|apikey|token|secret|password|auth)=)[^&\s"'<>]+/gi,
  /("?(?:access_token|refresh_token|authorization|token|secret)"?\s*[:=]\s*"?)[A-Za-z0-9._~+/=-]{8,}/gi,
  // URL userinfo — `https://user:secret@host/…`
  /(https?:\/\/)[^/\s@]*@/gi,
];

/**
 * A one-line, fully sanitized description of a thrown value, walking the `cause` chain.
 *
 * `err.message` alone is not enough: Node's fetch wraps the real failure in a generic
 * `TypeError: fetch failed` whose `cause` holds the useful text — and, when the URL or
 * an auth header is echoed into it, the credential. Everything is flattened here and
 * passed through {@link redactSecrets}, and the original object is then dropped.
 */
export function describeThrown(err: unknown, literal?: string | null): string {
  const parts: string[] = [];
  let cur: unknown = err;
  for (let depth = 0; cur !== null && cur !== undefined && depth < 5; depth += 1) {
    parts.push(cur instanceof Error ? `${cur.name}: ${cur.message}` : String(cur));
    cur = cur instanceof Error ? (cur as Error & { cause?: unknown }).cause : undefined;
  }
  return redactSecrets(parts.join(" <- "), literal);
}

/** Remove anything credential-shaped from `value`. */
export function redactSecrets(value: string, literal?: string | null): string {
  let out = String(value);
  if (literal && literal.length >= 8) out = out.split(literal).join("<REDACTED>");
  for (const re of SECRET_PATTERNS) out = out.replace(re, "$1<REDACTED>");
  return out;
}

/**
 * The only form of a URL that is ever logged: scheme, host and path.
 *
 * Not a redaction of the query string — its OMISSION. A server-supplied link
 * (`links.latest_draft`, `links.bucket`) can carry a credential under any parameter
 * name, and a denylist of names we happen to know is exactly the kind of control that
 * fails silently the first time someone invents `?sig=`. Userinfo is dropped for the
 * same reason.
 */
export function logTarget(url: string): string {
  try {
    const u = new URL(url);
    return `${u.protocol}//${u.host}${u.pathname}`;
  } catch {
    return "<unparseable-url>";
  }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/** A Zenodo API failure whose outcome is KNOWN: the request was rejected and nothing
 *  happened server-side. Carries the HTTP status and Zenodo's own message, never the
 *  token. */
export class ZenodoError extends Error {
  readonly status: number;
  readonly zenodoMessage: string;
  readonly fieldErrors: readonly { field: string; message: string }[];
  readonly request: string;

  constructor(opts: {
    status: number;
    zenodoMessage: string;
    fieldErrors?: readonly { field: string; message: string }[];
    request: string;
  }) {
    const fields = (opts.fieldErrors ?? []).map((e) => `${e.field}: ${e.message}`).join("; ");
    super(
      `Zenodo ${opts.status} on ${opts.request}: ${opts.zenodoMessage}` + (fields ? ` [${fields}]` : ""),
    );
    this.name = "ZenodoError";
    this.status = opts.status;
    this.zenodoMessage = opts.zenodoMessage;
    this.fieldErrors = opts.fieldErrors ?? [];
    this.request = opts.request;
  }
}

/**
 * A non-idempotent request whose outcome is UNKNOWN.
 *
 * Raised when a POST hits a network error, a timeout, or a 5xx: the request may have
 * been fully applied before the failure. Retrying is the tempting thing and the wrong
 * thing — a replayed `POST /deposit/depositions` mints a SECOND concept DOI for a paper
 * that may already have a PDF stamped with the first. Callers must reconcile against
 * the server (see `ZenodoClient.findDraftsByMarker`) rather than guess.
 */
export class ZenodoAmbiguousError extends Error {
  readonly request: string;

  constructor(request: string, detail: string) {
    super(
      `Zenodo request ${request} failed with an UNKNOWN outcome (${detail}). It may or may ` +
        `not have been applied. It is NOT being retried automatically, because replaying a ` +
        `create/publish/new-version would duplicate a permanent record. RE-RUN THE SAME ` +
        `COMMAND: every command reconciles against Zenodo before it does anything, so a ` +
        `re-run will find and adopt whatever this request did or did not leave behind.`,
    );
    this.name = "ZenodoAmbiguousError";
    this.request = request;
    // No `cause`. An Error chain is serialized wholesale by loggers, test snapshots and
    // issue reports, and only the top-level `message` was ever sanitized — a fetch
    // failure whose cause carried the bearer token therefore leaked it through
    // `error.cause.message`. The sanitized detail above is all that survives.
  }
}

/**
 * A deliberate refusal: the client will not perform this request at all.
 *
 * Separate from every other error because of how it is handled. The origin check that
 * stops an authenticated request following a redirect to production used to throw a
 * plain `Error` from inside the send path, where the network-failure handler caught it
 * and — for an idempotent method — RETRIED it, four more times. A refusal is not a
 * transient failure; retrying one is at best noise and at worst repeated attempts to do
 * the forbidden thing.
 */
export class ZenodoRefusalError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "ZenodoRefusalError";
  }
}

/** A 2xx whose body is not the document the caller needs. Treated as a hard failure on
 *  a real mutation: fabricating a placeholder here is how `10.5072/zenodo.0` gets
 *  written into a bundle. */
export class ZenodoResponseError extends Error {
  readonly request: string;
  constructor(request: string, detail: string) {
    super(`Zenodo returned a success status on ${request} but ${detail}.`);
    this.name = "ZenodoResponseError";
    this.request = request;
  }
}

// ---------------------------------------------------------------------------
// Wire shapes
// ---------------------------------------------------------------------------

export interface DepositionFile {
  readonly id?: string;
  readonly filename?: string;
  readonly key?: string;
  readonly filesize?: number;
  readonly checksum?: string;
}

export interface DepositionLinks {
  readonly self?: string;
  readonly bucket?: string;
  readonly publish?: string;
  readonly newversion?: string;
  readonly latest_draft?: string;
  readonly html?: string;
  readonly record_html?: string;
  readonly latest_html?: string;
  readonly doi?: string;
  readonly parent_doi?: string;
  readonly [k: string]: string | undefined;
}

export interface Deposition {
  readonly id: number;
  readonly conceptrecid?: string | number;
  /** ASSERTION ONLY — never persisted. See rule 1 in the module docstring. */
  readonly conceptdoi?: string;
  /** ASSERTION ONLY — never persisted. */
  readonly doi?: string;
  readonly doi_url?: string;
  readonly state?: string;
  readonly submitted?: boolean;
  readonly title?: string;
  readonly metadata?: Record<string, unknown> & {
    prereserve_doi?: { doi?: string; recid?: number };
    notes?: string;
  };
  readonly links?: DepositionLinks;
  readonly files?: readonly DepositionFile[];
}

export interface UploadedFile {
  readonly key: string;
  readonly size: number;
  readonly checksum: string;
  readonly version_id?: string;
}

// ---------------------------------------------------------------------------
// Client
// ---------------------------------------------------------------------------

export type FetchLike = (input: string, init?: RequestInit) => Promise<Response>;

export interface ZenodoClientOptions {
  readonly env?: ZenodoEnvironment;
  /** Reads the token. Called once per HTTP request so the secret is never held for
   *  longer than a request needs it. Defaults to reading `~/.zenodo/<tokenFile>`. */
  readonly tokenProvider?: () => Promise<string>;
  readonly fetchImpl?: FetchLike;
  readonly sleep?: (ms: number) => Promise<void>;
  /** Attempts AFTER the first try, for IDEMPOTENT requests only. Default 4. */
  readonly maxRetries?: number;
  readonly backoffBaseMs?: number;
  readonly maxSleepMs?: number;
  /** Receives redacted, human-readable request lines. */
  readonly log?: (line: string) => void;
  /** When true, no mutating request is sent; each is logged instead. */
  readonly dryRun?: boolean;
  /** Redirect hops to follow (same-origin only). Default 3. */
  readonly maxRedirects?: number;
  /**
   * Abort any single request after this long. Default 120s.
   *
   * Without it a stalled connection holds the bundle's locks indefinitely and the
   * operator sees a command that never returns — the failure mode that looks least like
   * a failure. A timeout on a POST is an AMBIGUOUS outcome (the request may have been
   * applied before we stopped listening); on GET/PUT/DELETE it is simply retryable.
   */
  readonly requestTimeoutMs?: number;
  /** Uploads get longer: a paper PDF over a slow link is not a stall. Default 15min. */
  readonly uploadTimeoutMs?: number;
}

/** Read the personal access token for `env` from `~/.zenodo/`. */
export async function readTokenFromHome(env: ZenodoEnvironment): Promise<string> {
  const file = path.join(os.homedir(), ".zenodo", env.tokenFile);
  let raw: string;
  try {
    raw = await readFile(file, "utf8");
  } catch (err) {
    const code = (err as NodeJS.ErrnoException).code;
    throw new Error(
      `Cannot read the Zenodo ${env.name} token from ${file} (${code ?? "unreadable"}). ` +
        `Create it with your personal access token, mode 0600.`,
    );
  }
  const token = raw.trim();
  if (!token) throw new Error(`The Zenodo ${env.name} token file ${file} is empty.`);
  return token;
}

/** Statuses worth another attempt at all. */
const RETRYABLE_STATUSES = new Set([429, 500, 502, 503, 504]);

/**
 * Methods whose replay cannot create a second thing.
 *
 * `PUT` and `DELETE` are idempotent by definition, and the two this client uses are
 * genuinely so: a bucket `PUT` of the same key replaces it (verified on the sandbox),
 * and a second `DELETE` of a gone draft is a 404 the caller already tolerates. `POST`
 * is not on this list and never will be.
 */
const IDEMPOTENT_METHODS = new Set(["GET", "HEAD", "PUT", "DELETE", "OPTIONS"]);

interface RequestOptions {
  readonly method: string;
  readonly url: string;
  readonly json?: unknown;
  readonly body?: Uint8Array;
  readonly contentType?: string;
  readonly mutating: boolean;
  readonly allow404?: boolean;
}

/** Sent on every request; see the note where the headers are built. */
export const ZENODO_USER_AGENT = "CausalSmith-zenodo-deposit/1.0 (+https://causalsmith.org)";

export class ZenodoClient {
  readonly env: ZenodoEnvironment;
  private readonly tokenProvider: () => Promise<string>;
  private readonly fetchImpl: FetchLike;
  private readonly sleep: (ms: number) => Promise<void>;
  private readonly maxRetries: number;
  private readonly backoffBaseMs: number;
  private readonly maxSleepMs: number;
  private readonly logLine: (line: string) => void;
  private readonly maxRedirects: number;
  private readonly requestTimeoutMs: number;
  private readonly uploadTimeoutMs: number;
  readonly dryRun: boolean;
  /** Every request this client considered, logged as method + origin + path. */
  readonly requestLog: string[] = [];

  constructor(opts: ZenodoClientOptions = {}) {
    this.env = opts.env ?? DEFAULT_ENVIRONMENT;
    this.tokenProvider = opts.tokenProvider ?? (() => readTokenFromHome(this.env));
    this.fetchImpl = opts.fetchImpl ?? ((input, init) => fetch(input, init));
    this.sleep = opts.sleep ?? ((ms) => new Promise((r) => setTimeout(r, ms)));
    this.maxRetries = opts.maxRetries ?? 4;
    this.backoffBaseMs = opts.backoffBaseMs ?? 1000;
    this.maxSleepMs = opts.maxSleepMs ?? 60_000;
    this.logLine = opts.log ?? (() => {});
    this.dryRun = opts.dryRun ?? false;
    this.maxRedirects = opts.maxRedirects ?? 3;
    this.requestTimeoutMs = opts.requestTimeoutMs ?? 120_000;
    this.uploadTimeoutMs = opts.uploadTimeoutMs ?? 15 * 60_000;
  }

  /** The concept DOI a deposition with this `conceptrecid` publishes under. THE only
   *  source of a concept DOI in this codebase. */
  conceptDoi(conceptrecid: number): string {
    const id = toRecordId(conceptrecid);
    if (id === null) throw new Error(`Refusing to build a concept DOI from ${JSON.stringify(conceptrecid)}.`);
    return `${this.env.doiPrefix}/zenodo.${id}`;
  }

  /** The version DOI a deposition with this record id publishes under. */
  versionDoi(recid: number): string {
    const id = toRecordId(recid);
    if (id === null) throw new Error(`Refusing to build a version DOI from ${JSON.stringify(recid)}.`);
    return `${this.env.doiPrefix}/zenodo.${id}`;
  }

  recordUrl(recid: number): string {
    return `${this.env.webBase}/records/${recid}`;
  }

  // -- HTTP ---------------------------------------------------------------

  private resolve(url: string): string {
    if (/^https?:\/\//i.test(url)) return url;
    return `${this.env.apiBase}${url.startsWith("/") ? "" : "/"}${url}`;
  }

  /** Refuse a URL that points anywhere but the configured instance, or that carries
   *  userinfo (a credential smuggled into the authority component). */
  private assertSameOrigin(url: string, what: string): void {
    const expected = new URL(this.env.apiBase).origin;
    let u: URL;
    try {
      u = new URL(url);
    } catch {
      throw new ZenodoRefusalError(`Zenodo ${what} is not a valid URL.`);
    }
    if (u.username || u.password) {
      throw new ZenodoRefusalError(
        `Refusing a Zenodo ${what} that embeds credentials in the URL (${logTarget(url)}).`,
      );
    }
    if (u.origin !== expected) {
      throw new ZenodoRefusalError(
        `Refusing to follow a Zenodo ${what} to ${u.origin} while configured for ` +
          `${this.env.name} (${expected}). Cross-instance requests are never correct.`,
      );
    }
  }

  private retryAfterMs(res: Response, now: number): number | null {
    const raw = res.headers.get("retry-after");
    if (!raw) return null;
    const seconds = Number(raw.trim());
    if (Number.isFinite(seconds) && seconds >= 0) return Math.round(seconds * 1000);
    const at = Date.parse(raw);
    if (Number.isFinite(at)) return Math.max(0, at - now);
    return null;
  }

  private backoff(attempt: number, retryAfterMs: number | null): number {
    if (retryAfterMs !== null) return Math.min(retryAfterMs, this.maxSleepMs);
    const ceiling = Math.min(this.backoffBaseMs * 2 ** attempt, this.maxSleepMs);
    return Math.round(ceiling * (0.5 + Math.random() * 0.5));
  }

  /** One HTTP exchange, following only same-origin redirects. */
  /** Abort timers still armed for a response whose body has not been read yet. */
  private readonly pendingTimers = new Set<ReturnType<typeof setTimeout>>();

  private disarmTimers(): void {
    for (const t of this.pendingTimers) clearTimeout(t);
    this.pendingTimers.clear();
  }

  private async send(
    method: string,
    url: string,
    init: RequestInit,
    label: string,
    timeoutMs: number,
  ): Promise<{ res: Response; finalUrl: string }> {
    let current = url;
    for (let hop = 0; ; hop++) {
      const controller = new AbortController();
      const timer = setTimeout(() => controller.abort(new Error(`timed out after ${timeoutMs}ms`)), timeoutMs);
      // The timer is NOT cleared here. `fetch` resolves as soon as the headers arrive,
      // so disarming it at that point leaves the body read — which is where a stalled
      // connection actually hangs — with no timeout at all. It is cleared by the caller
      // once the body has been consumed.
      let res: Response;
      try {
        res = await this.fetchImpl(current, { ...init, redirect: "manual", signal: controller.signal });
      } catch (err) {
        clearTimeout(timer);
        throw err;
      }
      this.pendingTimers.add(timer);
      if (res.status < 300 || res.status >= 400) return { res, finalUrl: current };

      const location = res.headers.get("location");
      if (!location) {
        throw new ZenodoRefusalError(
          `Zenodo answered ${res.status} on ${label} with no Location header.`,
        );
      }
      const next = new URL(location, current).toString();
      // Validate BEFORE any further request: this is the whole point of redirect:"manual".
      this.assertSameOrigin(next, "redirect target");
      if (!IDEMPOTENT_METHODS.has(method)) {
        throw new ZenodoAmbiguousError(
          label,
          `it answered ${res.status} redirecting to ${logTarget(next)}; a redirected ` +
            `non-idempotent request cannot be replayed safely`,
        );
      }
      if (hop >= this.maxRedirects) {
        throw new ZenodoRefusalError(
          `Zenodo redirected more than ${this.maxRedirects} times on ${label}.`,
        );
      }
      current = next;
    }
  }

  private async request(opts: RequestOptions): Promise<{ status: number; json: unknown }> {
    const url = this.resolve(opts.url);
    this.assertSameOrigin(url, "request URL");
    const label = `${opts.method} ${logTarget(url)}`;
    const line = label +
      (opts.json !== undefined ? ` json=${redactSecrets(JSON.stringify(opts.json))}` : "") +
      (opts.body !== undefined ? ` body=<${opts.body.byteLength} bytes>` : "");
    this.requestLog.push(line);

    // Dry-run sends NOTHING — reads included. "It only does harmless GETs" is a
    // promise about today's code, and the value of --dry-run is that it is a promise
    // about the network.
    if (this.dryRun) {
      this.logLine(`[dry-run] would ${opts.mutating ? "send" : "query"}: ${line}`);
      return { status: 0, json: null };
    }
    this.logLine(line);

    const idempotent = IDEMPOTENT_METHODS.has(opts.method);

    for (let attempt = 0; ; attempt++) {
      const token = await this.tokenProvider();
      // Zenodo's production edge answers 403 ("unusual traffic") to Node's bare default
      // `User-Agent: node`; the sandbox does not, so only a production call ever shows it.
      // Identify the tool honestly instead — a descriptive agent with a contact URL.
      const headers: Record<string, string> = {
        Authorization: `Bearer ${token}`,
        "User-Agent": ZENODO_USER_AGENT,
      };
      if (opts.json !== undefined) headers["Content-Type"] = "application/json";
      else if (opts.contentType) headers["Content-Type"] = opts.contentType;

      let res: Response;
      let finalUrl: string;
      try {
        ({ res, finalUrl } = await this.send(
          opts.method,
          url,
          {
            method: opts.method,
            headers,
            body: opts.json !== undefined
              ? JSON.stringify(opts.json)
              : (opts.body as unknown as BodyInit | undefined),
          },
          label,
          opts.body !== undefined ? this.uploadTimeoutMs : this.requestTimeoutMs,
        ));
      } catch (err) {
        // A refusal and an ambiguous outcome are both final: neither is a transient
        // failure that another attempt could resolve.
        if (err instanceof ZenodoAmbiguousError || err instanceof ZenodoRefusalError) throw err;
        // A failure with no response. For an idempotent request, replaying cannot
        // create a second anything, so back off and retry. For a POST, the request may
        // already have been applied — stop and make the caller reconcile.
        const detail = describeThrown(err, token);
        if (!idempotent) throw new ZenodoAmbiguousError(label, detail);
        if (attempt >= this.maxRetries) {
          throw new Error(`Zenodo request ${label} failed before a response: ${detail}`);
        }
        await this.sleep(this.backoff(attempt, null));
        continue;
      }

      let text: string;
      try {
        text = await res.text();
      } catch (err) {
        // Reading the body can fail on its own — an aborted stream, or the request
        // timeout firing DURING the read, which is exactly the stall this timer is for.
        // That rejection used to escape the sanitizing path entirely.
        const detail = describeThrown(err, token);
        if (!idempotent) throw new ZenodoAmbiguousError(label, `response body unreadable: ${detail}`);
        if (attempt >= this.maxRetries) {
          throw new Error(`Zenodo response to ${label} could not be read: ${detail}`);
        }
        await this.sleep(this.backoff(attempt, null));
        continue;
      } finally {
        // Only now is the request genuinely over: `fetch` resolves at the headers, so
        // disarming the timer there would leave the body read untimed.
        this.disarmTimers();
      }
      if (res.ok || (opts.allow404 && res.status === 404)) {
        let json: unknown = null;
        if (text) {
          try {
            json = JSON.parse(text);
          } catch {
            json = undefined; // parsed-and-failed, distinct from "no body"
          }
        }
        return { status: res.status, json: json === undefined ? undefined : json };
      }

      if (RETRYABLE_STATUSES.has(res.status)) {
        // A non-idempotent request is NEVER replayed on any status, 429 included.
        // The earlier version argued that a rate limiter refuses a request without
        // performing it — true of Zenodo's own limiter, but the client does not know
        // it is talking to Zenodo's own limiter. Any proxy, gateway or CDN in front of
        // it can perform the upstream call and then return 429 of its own accord, and
        // a replayed create mints a second permanent DOI. Status codes are not
        // evidence about side effects.
        if (!idempotent) {
          throw new ZenodoAmbiguousError(label, `HTTP ${res.status}`);
        }
        if (attempt < this.maxRetries) {
          const hinted = this.retryAfterMs(res, Date.now());
          this.logLine(
            `Zenodo ${res.status} on ${label} — retry ${attempt + 1}/${this.maxRetries}` +
              (hinted !== null ? ` after Retry-After ${Math.round(hinted / 1000)}s` : ""),
          );
          await this.sleep(this.backoff(attempt, hinted));
          continue;
        }
      }

      throw this.toError(res.status, text, `${opts.method} ${logTarget(finalUrl)}`, token);
    }
  }

  private toError(status: number, text: string, request: string, token: string): ZenodoError {
    let zenodoMessage = redactSecrets(text.slice(0, 500) || "(empty response body)", token);
    let fieldErrors: { field: string; message: string }[] = [];
    try {
      const parsed = JSON.parse(text) as {
        message?: string;
        errors?: { field?: string; messages?: string[]; message?: string }[];
      };
      if (typeof parsed.message === "string") zenodoMessage = redactSecrets(parsed.message, token);
      if (Array.isArray(parsed.errors)) {
        fieldErrors = parsed.errors.map((e) => ({
          field: redactSecrets(String(e.field ?? "?"), token),
          message: redactSecrets(
            Array.isArray(e.messages) ? e.messages.join(", ") : String(e.message ?? ""),
            token,
          ),
        }));
      }
    } catch {
      // Non-JSON body (an HTML 502 from the proxy); the truncated text is the message.
    }
    return new ZenodoError({ status, zenodoMessage, fieldErrors, request });
  }

  // -- Response validation ------------------------------------------------

  /**
   * Turn a successful response body into a {@link Deposition}, or fail loudly.
   *
   * Everything downstream — the concept DOI, the sidecar, the stamp the PDF was
   * compiled with — is derived from `id` and `conceptrecid`. A body that is empty,
   * unparseable, or missing those fields used to become a placeholder `{id: 0}`, which
   * then produced the DOI `10.5072/zenodo.0` and recorded it as if it were real. There
   * is no safe default here; the only correct behaviour is to stop.
   */
  private asDeposition(
    json: unknown,
    request: string,
    need: { conceptrecid?: boolean; links?: boolean; bucket?: boolean } = {},
  ): Deposition {
    if (json === undefined) throw new ZenodoResponseError(request, "its body was not valid JSON");
    if (json === null) throw new ZenodoResponseError(request, "its body was empty");
    if (typeof json !== "object" || Array.isArray(json)) {
      throw new ZenodoResponseError(request, "its body was not a JSON object");
    }
    const dep = json as Record<string, unknown>;
    const id = toRecordId(dep.id);
    if (id === null) {
      throw new ZenodoResponseError(request, `it carried no usable numeric "id" (got ${JSON.stringify(dep.id)})`);
    }
    if (need.conceptrecid && toRecordId(dep.conceptrecid) === null) {
      throw new ZenodoResponseError(
        request,
        `it carried no usable numeric "conceptrecid" (got ${JSON.stringify(dep.conceptrecid)}), ` +
          `so the concept DOI cannot be derived`,
      );
    }
    if ((need.links || need.bucket) && (dep.links === null || typeof dep.links !== "object")) {
      throw new ZenodoResponseError(request, 'it carried no "links" object');
    }
    if (need.bucket && typeof (dep.links as DepositionLinks).bucket !== "string") {
      throw new ZenodoResponseError(request, 'it carried no "links.bucket" upload target');
    }
    return { ...(dep as unknown as Deposition), id };
  }

  // -- Operations ---------------------------------------------------------

  /** Create a draft. `metadata` SHOULD carry the bundle marker so a crashed run can
   *  find this draft again — see `deposit.ts`. */
  async createDraft(metadata?: Record<string, unknown>): Promise<Deposition> {
    const req = "POST /deposit/depositions";
    const { json } = await this.request({
      method: "POST",
      url: "/deposit/depositions",
      json: metadata ? { metadata } : {},
      mutating: true,
    });
    if (this.dryRun) return { id: 0, conceptrecid: 0, state: "dry-run", links: {}, files: [] };
    return this.asDeposition(json, req, { conceptrecid: true, bucket: true });
  }

  async getDeposition(id: number | string): Promise<Deposition> {
    const req = `GET /deposit/depositions/${id}`;
    if (this.dryRun) throw new Error(`Cannot read deposition ${id} under --dry-run (nothing is sent).`);
    const { json } = await this.request({ method: "GET", url: `/deposit/depositions/${id}`, mutating: false });
    return this.asDeposition(json, req);
  }

  /** Same as {@link getDeposition} but null instead of throwing on 404. */
  async getDepositionOrNull(id: number | string): Promise<Deposition | null> {
    const req = `GET /deposit/depositions/${id}`;
    const { status, json } = await this.request({
      method: "GET", url: `/deposit/depositions/${id}`, mutating: false, allow404: true,
    });
    if (this.dryRun) return null;
    return status === 404 ? null : this.asDeposition(json, req);
  }

  /**
   * As {@link getByUrl} but null on 404.
   *
   * `links.latest_draft` outlives the draft it names: after a revision draft is deleted
   * the published record still advertises the link, and following it hard-failed a
   * reconcile that had just correctly cleared that very draft.
   */
  async getByUrlOrNull(url: string): Promise<Deposition | null> {
    if (this.dryRun) return null;
    const { status, json } = await this.request({
      method: "GET", url, mutating: false, allow404: true,
    });
    return status === 404 ? null : this.asDeposition(json, `GET ${logTarget(this.resolve(url))}`);
  }

  /** GET an absolute link Zenodo handed us (e.g. `links.latest_draft`). */
  async getByUrl(url: string): Promise<Deposition> {
    if (this.dryRun) throw new Error(`Cannot follow ${logTarget(this.resolve(url))} under --dry-run.`);
    const { json } = await this.request({ method: "GET", url, mutating: false });
    return this.asDeposition(json, `GET ${logTarget(this.resolve(url))}`);
  }

  /**
   * Find this account's UNPUBLISHED drafts whose notes carry `marker`.
   *
   * This is the reconciliation primitive: after a create whose outcome is unknown, it
   * answers "did a draft for this bundle get made?" without creating anything.
   *
   * Probed shape: the plain listing omits drafts entirely (only `state: "done"` rows
   * came back), `?status=draft` includes them, and a QUOTED phrase `q="<marker>"`
   * matches `metadata.notes` while an unquoted one matches nothing. Both are sent, and
   * the marker is then re-checked locally — the server-side filter is an optimisation,
   * the local check is the correctness argument, so a change in Zenodo's search
   * semantics can cost recall but can never adopt the wrong draft.
   */
  async findDraftsByMarker(marker: string): Promise<Deposition[]> {
    const q = encodeURIComponent(`"${marker}"`);
    const req = "GET /deposit/depositions (draft search)";
    const { json } = await this.request({
      method: "GET",
      url: `/deposit/depositions?size=100&status=draft&q=${q}`,
      mutating: false,
    });
    if (this.dryRun) return [];
    // FAIL CLOSED. `return []` on an unexpected shape reads as "no orphan exists",
    // which is precisely the answer that makes `reserve` create a second deposit. If
    // Zenodo ever answers `{hits:{hits:[…]}}` — the InvenioRDM search shape — that must
    // stop the run, not license a duplicate concept DOI.
    if (!Array.isArray(json)) {
      throw new ZenodoResponseError(
        req,
        `the listing was not a JSON array (got ${json === null ? "null" : typeof json}). ` +
          `Refusing to read that as "no existing draft"`,
      );
    }
    const out: Deposition[] = [];
    for (const row of json) {
      if (row === null || typeof row !== "object" || Array.isArray(row)) {
        throw new ZenodoResponseError(req, "a listing row was not a deposition object");
      }
      const r = row as Record<string, unknown>;
      const id = toRecordId(r.id);
      if (id === null) throw new ZenodoResponseError(req, "a listing row had no usable numeric id");
      if (r.submitted !== false) continue;
      const notes = (r.metadata as { notes?: unknown } | undefined)?.notes;
      // EXACT LINE equality. Substring matching let bundle `foo` adopt a draft marked
      // for `foobar`; markers are now hashes, but the comparison is exact regardless.
      if (typeof notes !== "string") continue;
      if (!notes.split(/\r?\n/).some((line) => line.trim() === marker)) continue;
      if (toRecordId(r.conceptrecid) === null) {
        throw new ZenodoResponseError(req, `matching draft ${id} carried no usable conceptrecid`);
      }
      out.push({ ...(r as unknown as Deposition), id });
    }
    return out;
  }

  async updateMetadata(id: number | string, metadata: Record<string, unknown>): Promise<Deposition> {
    const req = `PUT /deposit/depositions/${id}`;
    const { json } = await this.request({
      method: "PUT", url: `/deposit/depositions/${id}`, json: { metadata }, mutating: true,
    });
    if (this.dryRun) return { id: Number(id), links: {}, files: [] };
    return this.asDeposition(json, req);
  }

  /**
   * Upload `bytes` as `filename`, replacing any existing file of that name.
   *
   * Uses the bucket API. Both upload APIs work on the current sandbox, but the bucket
   * one replaces in place: a second `PUT` of the same key returned 201 with a fresh
   * `version_id` and no prior delete, whereas the legacy endpoint 400s on a duplicate
   * filename. That matters for the new-version flow, where the draft INHERITS the
   * previous version's files under the same names.
   */
  async uploadFile(bucketUrl: string, filename: string, bytes: Uint8Array): Promise<UploadedFile> {
    if (!bucketUrl) {
      throw new Error("This deposition has no links.bucket, so its files cannot be uploaded.");
    }
    const url = `${bucketUrl.replace(/\/+$/, "")}/${encodeURIComponent(filename)}`;
    const req = `PUT ${logTarget(url)}`;
    const { json } = await this.request({
      method: "PUT", url, body: bytes, contentType: "application/octet-stream", mutating: true,
    });
    if (this.dryRun) return { key: filename, size: bytes.byteLength, checksum: "(dry-run)" };
    if (json === null || json === undefined || typeof json !== "object") {
      throw new ZenodoResponseError(req, "the upload response was not a JSON object");
    }
    const up = json as Record<string, unknown>;
    if (typeof up.key !== "string") {
      throw new ZenodoResponseError(req, 'the upload response carried no "key"');
    }
    return {
      key: up.key,
      size: typeof up.size === "number" ? up.size : bytes.byteLength,
      checksum: typeof up.checksum === "string" ? up.checksum : "",
      version_id: typeof up.version_id === "string" ? up.version_id : undefined,
    };
  }

  async deleteFile(id: number | string, fileId: string): Promise<void> {
    await this.request({ method: "DELETE", url: `/deposit/depositions/${id}/files/${fileId}`, mutating: true });
  }

  /** Publish. Irreversible on production. Returns the published deposition. */
  async publish(id: number | string): Promise<Deposition> {
    const req = `POST /deposit/depositions/${id}/actions/publish`;
    const { json } = await this.request({
      method: "POST", url: `/deposit/depositions/${id}/actions/publish`, mutating: true,
    });
    if (this.dryRun) return { id: Number(id), links: {}, files: [] };
    return this.asDeposition(json, req, { conceptrecid: true });
  }

  /**
   * Open a new version of a published record.
   *
   * The POST answers with the OLD deposition carrying `links.latest_draft`; the new
   * draft is a second fetch. Probed: the new draft keeps `conceptrecid`, gets a fresh
   * `prereserve_doi.recid`, has no `doi` until published, and INHERITS the previous
   * version's files.
   */
  async newVersion(id: number | string): Promise<Deposition> {
    const req = `POST /deposit/depositions/${id}/actions/newversion`;
    const { json } = await this.request({
      method: "POST", url: `/deposit/depositions/${id}/actions/newversion`, mutating: true,
    });
    if (this.dryRun) return { id: Number(id), links: {}, files: [] };
    const parent = this.asDeposition(json, req, { links: true });
    const latest = parent.links?.latest_draft;
    if (!latest) {
      throw new ZenodoResponseError(
        req,
        "it returned no links.latest_draft, so the new draft cannot be located — inspect the " +
          "deposition on the web UI before retrying, since a second newversion call may create " +
          "a second draft",
      );
    }
    this.assertSameOrigin(this.resolve(latest), "latest_draft link");
    const draft = await this.getByUrl(latest);
    if (toRecordId(draft.conceptrecid) === null) {
      throw new ZenodoResponseError(`GET ${logTarget(this.resolve(latest))}`, "the new draft carried no conceptrecid");
    }
    return draft;
  }

  /**
   * Delete an UNPUBLISHED draft. Probed: 204, and a subsequent GET is 404.
   *
   * A 404 is SUCCESS, not a failure. `DELETE` is idempotent and is retried on a network
   * error, so the ordinary "the delete landed, the response was lost" sequence ends with
   * the retry seeing 404 — and the caller treating that as an error left the local
   * bookkeeping unrepaired while the remote draft really was gone. Returns whether the
   * draft was still present, so a caller can say which happened.
   */
  async deleteDraft(id: number | string): Promise<{ alreadyGone: boolean }> {
    const { status } = await this.request({
      method: "DELETE", url: `/deposit/depositions/${id}`, mutating: true, allow404: true,
    });
    return { alreadyGone: status === 404 };
  }
}

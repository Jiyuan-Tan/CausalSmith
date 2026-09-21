/**
 * `release` — the whole chain from "this paper has no DOI" to "this paper is published", in one
 * command that stops before the irreversible step.
 *
 * ## The order, and why it is the only one that works
 *
 *   1. **reserve** (idempotent). Zenodo mints the concept DOI when the draft is created, so the
 *      identifier exists before anything is compiled against it. Re-running finds the same draft.
 *   2. **restamp with `--write`**. The DOI now in `meta.json` is rendered into `paper_stamp.tex`
 *      and `latexmk` puts it on page 1. This is the LaTeX-only path: no re-emit, no version bump,
 *      and the verification in `presentation/restamp.ts` proves nothing but page 1 moved.
 *   3. **verify the stamp** on PAGE 1, with the same reader `publish` uses.
 *   4. **stop**, and print exactly what would be sent — unless `--publish` is passed.
 *
 * ## `--dry-run`
 *
 * Writes nothing ANYWHERE: the restamp runs in its own preview mode, and the chain stops right
 * after it. Everything past that point reads the shipped `paper.pdf`, which a dry run has
 * deliberately not restamped, so a stamp check there would answer confidently about the old page 1.
 *
 * Doing this by hand is three commands with a compile in the middle, and the failure mode of
 * getting it wrong is a permanent public record whose page 1 prints a different DOI than the one
 * it is registered under. That is the whole reason this exists as one command.
 *
 * ## Sandbox
 *
 * A sandbox DOI has prefix `10.5072` and resolves to nothing, so `renderStampTex` deliberately
 * does NOT print it (see `PRODUCTION_DOI_RE`): page 1 falls back to the paper's site link. The
 * stamp check therefore CANNOT pass in sandbox mode, and `publish` would refuse. That is not a
 * bug to work around — it is the containment rule doing its job — so `release` says so plainly
 * and stops before publishing, unless `--allow-unstamped` says the operator understands.
 *
 * ## Locks
 *
 * Order is **emit → zenodo command → meta**, as everywhere else. `release` holds NONE of them
 * itself: `reserve`, `publish` and `restampBundle` each take the emit lock for their own
 * duration and release it. It has to be that way — the emit lock is not re-entrant, so a
 * `release` that held it around the three steps would deadlock against the first one that asked
 * for it. `restampBundle` still accepts an "already held" mode, and defaults to reading the async
 * context, so nesting stays safe if a future caller does hold it.
 */
import { readFile } from "node:fs/promises";
import { paperSeriesPrefix } from "../local_config.js";
import { restampBundle, type RestampOptions, type RestampResult } from "../presentation/restamp.js";
import { isProductionDoi } from "../presentation/paper_stamp.js";
import { bundleId, paperPdfPath, readBundleMeta } from "./bundle.js";
import { isSandboxDoi } from "./client.js";
import {
  metadataOptions, publish, reserve,
  type DepositContext, type PublishResult, type ReserveResult,
} from "./deposit.js";
import { buildZenodoMetadata } from "./metadata.js";
import { pdfPage1ContainsDoi } from "./pdf_text.js";

export interface ReleaseOptions {
  /** false (the default) stops after the preview. True is the only thing that can publish. */
  readonly publish?: boolean;
  /** the CausalSmith package root, for the working-paper registry */
  readonly repoRoot: string;
  /** the working-paper series, resolved ONCE by the caller; defaults to `paperSeriesPrefix()` */
  readonly seriesPrefix?: string;
  /** test seam: the restamp step */
  readonly restamp?: (dir: string, opts: RestampOptions) => Promise<RestampResult>;
}

export interface ReleaseResult {
  readonly reserved: ReserveResult;
  readonly restamped: RestampResult | null;
  readonly published: PublishResult | null;
  /** why it stopped before publishing, or null when it published (or was never asked to) */
  readonly stoppedBecause:
    | "not-asked" | "sandbox-doi-is-not-stamped" | "restamp-failed" | "unstamped-pdf" | "dry-run" | null;
}

/** One paper, from reservation to published record — stopping before the publish by default. */
export async function release(ctx: DepositContext, opts: ReleaseOptions): Promise<ReleaseResult> {
  const id = bundleId(ctx.bundleDir);
  const env = ctx.client.env.name;

  // 1. Reserve. Idempotent: a bundle that already holds a draft (or is already published) comes
  // back with the same concept DOI rather than a second one.
  const reserved = await reserve(ctx, {});
  const conceptDoi = reserved.record.concept_doi;
  if (!conceptDoi) {
    throw new Error(
      `release: no concept DOI for ${id} on ${env} after 'reserve'. Nothing was compiled or sent. ` +
        `Run 'status' to see what the ${env} instance holds for this bundle.`,
    );
  }
  ctx.log(`Concept DOI on ${env}: ${conceptDoi}${reserved.reused ? " (existing reservation)" : " (new)"}`);

  // The stamp is rendered from meta.doi, so a reservation the containment rule kept out of
  // meta.json cannot reach page 1. Say that BEFORE spending a minute on a compile that is
  // guaranteed not to carry it.
  const metaBefore = await readBundleMeta(ctx.bundleDir);
  if (metaBefore.doi !== conceptDoi) {
    ctx.warn(
      `meta.json holds doi=${JSON.stringify(metaBefore.doi ?? null)}, not ${conceptDoi}` +
        `${reserved.metaWritten ? "" : " (it was not written there — see the containment rule)"}. ` +
        `The stamp is rendered from meta.doi, so page 1 will not carry ${conceptDoi}.`,
    );
  }

  // 2. Restamp: recompile page 1 against the identity meta.json now holds. Takes the emit lock
  // itself; `reserve` has already released its own.
  //
  // `--dry-run` means NOTHING IS WRITTEN — not to Zenodo and not to the bundle. The restamp is
  // the one step in this chain that touches the working tree, so it runs in its own dry-run mode
  // (`write: false`), which compiles and verifies in a scratch copy and reports what it WOULD
  // replace. Passing `write: true` here made `--dry-run` rewrite paper.pdf, paper.tex and
  // meta.json of a real bundle — a permanent change made by the command whose whole promise is
  // that it makes none.
  const restampFn = opts.restamp ?? restampBundle;
  const restamped = await restampFn(ctx.bundleDir, {
    repoRoot: opts.repoRoot,
    seriesPrefix: opts.seriesPrefix ?? paperSeriesPrefix(),
    write: !ctx.client.dryRun,
  });
  ctx.log(
    `Restamp: ${restamped.verdict} — ${restamped.wpNumber ?? "(no number)"}` +
      `v${restamped.version ?? "?"}, ${restamped.pages ?? "?"} page(s). ${restamped.detail}`,
  );
  if (!restamped.ok) {
    return { reserved, restamped, published: null, stoppedBecause: "restamp-failed" };
  }

  // And stop here. Everything below reads the SHIPPED paper.pdf, which a dry run deliberately
  // left as it was — so the stamp check would report on the old page 1 and the preview would
  // describe a file no real run would send. A confident answer to the wrong question is worse
  // than no answer.
  if (ctx.client.dryRun) {
    ctx.log(
      `DRY RUN: nothing was written, to ${env} or to ${ctx.bundleDir}. The restamp above is a ` +
        `PREVIEW (${restamped.verdict}); ${paperPdfPath(ctx.bundleDir)} still carries the page 1 ` +
        `it shipped with, so the stamp check and the publish preview are skipped rather than run ` +
        `against a stale PDF. Re-run without --dry-run to stamp, then again with --publish.`,
    );
    return { reserved, restamped, published: null, stoppedBecause: "dry-run" };
  }

  // 3. The stamp check — the same reader `publish` uses, run here so the operator learns the
  // answer before being asked to authorise anything.
  const pdf = paperPdfPath(ctx.bundleDir);
  const check = await pdfPage1ContainsDoi(pdf, conceptDoi);
  const stamped = check.outcome === "present";
  ctx.log(
    stamped
      ? `Stamp check: ${conceptDoi} found on page 1 (via ${check.method}).`
      : `Stamp check: ${check.outcome === "absent"
          ? `${conceptDoi} is NOT on page 1 of ${pdf} (read via ${check.method})`
          : check.reason}.`,
  );

  // 4. The preview. Exactly what `publish` would send, built from the same function it builds it
  // from, so the preview cannot describe something other than the request.
  const meta = await readBundleMeta(ctx.bundleDir);
  const metadata = buildZenodoMetadata(meta, metadataOptions(ctx));
  const bytes = await readFile(pdf).catch(() => null);
  const draftId = reserved.record.draft?.deposition_id ?? null;
  ctx.log("");
  ctx.log(`WOULD PUBLISH on ${env} (${ctx.client.env.apiBase}):`);
  ctx.log(`  deposition   ${draftId ?? "(none open)"}`);
  ctx.log(`  concept DOI  ${conceptDoi}`);
  ctx.log(`  version DOI  ${draftId === null ? "(unknown until a draft is open)" : ctx.client.versionDoi(draftId)}`);
  ctx.log(`  file         ${pdf} (${bytes === null ? "MISSING" : `${bytes.byteLength} bytes`})`);
  ctx.log(`  page 1 DOI   ${stamped ? "present" : "NOT PRESENT"}`);
  ctx.log(`  metadata     ${JSON.stringify(metadata, null, 2).split("\n").join("\n               ")}`);
  ctx.log("");

  // A sandbox DOI is never stamped (see the module docstring), so the stamp check cannot pass and
  // `publish` would refuse. Stopping here with that stated is more useful than letting the
  // operator discover it from a refusal one command later.
  if (isSandboxDoi(conceptDoi) && !isProductionDoi(metaBefore.doi)) {
    if (!ctx.allowUnstamped) {
      ctx.warn(
        `STOPPING: ${conceptDoi} is a SANDBOX DOI. It resolves to nothing, so the stamp ` +
          `deliberately omits it and page 1 links to the paper's page instead — which means the ` +
          `stamp check cannot pass and 'publish' would refuse. This is the containment rule ` +
          `working, not a failure. Pass --allow-unstamped to rehearse the publish anyway, or ` +
          `--production --i-understand-this-is-permanent for the real thing.`,
      );
      return { reserved, restamped, published: null, stoppedBecause: "sandbox-doi-is-not-stamped" };
    }
    ctx.warn(`Continuing with an UNSTAMPED sandbox PDF because --allow-unstamped was passed.`);
  } else if (!stamped && !ctx.allowUnstamped) {
    ctx.warn(
      `STOPPING: page 1 of ${pdf} does not carry ${conceptDoi}, so 'publish' would refuse. ` +
        `Nothing was sent.`,
    );
    return { reserved, restamped, published: null, stoppedBecause: "unstamped-pdf" };
  }

  if (!opts.publish) {
    ctx.log("Stopping before publish. Re-run with --publish to send the above.");
    return { reserved, restamped, published: null, stoppedBecause: "not-asked" };
  }

  // 5. The irreversible step. `publish` re-reconciles, re-checks the stamp and takes the locks
  // again; nothing here is trusted to have stayed true.
  const published = await publish(ctx);
  return { reserved, restamped, published, stoppedBecause: null };
}

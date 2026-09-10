#!/usr/bin/env -S npx tsx
/**
 * Orchestrator-only: attest the source-of-record for a `cited` statement — its exact
 * verbatim statement, locator, and provenance (upstream primary source, or affirmed
 * original to the cited work). Writes one direct commit on the graph and re-renders
 * core.json. Never overwrites an existing verbatim statement.
 *
 * Usage: d0_attest_cited_source.ts <qid> <spec> --id <lem:id> --expect-locator <text>
 *          --verbatim <source-statement> --note <provenance>
 *          (--upstream <primary citation> [--upstream-locator <text>] [--upstream-cite <bibkey>] | --upstream-none)
 *          [--acknowledge-marker <text>]
 */
import process from "node:process";
import type { PipelineContext } from "../src/types.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";
import { resolveUpstreamDecision, detectUpstreamMarkers } from "../src/discovery/core/cited_provenance.js";
import { withRunHeartbeat } from "../src/shared/run_heartbeat.js";
import { assertNoUncommittedEdits, commitGraph, headGraph, publishCore } from "../src/discovery/vcs/commit.js";
import { nodesOfType, statementBlob } from "../src/discovery/vcs/graph.js";
import { blobId } from "../src/discovery/vcs/node.js";
import { formatViolations } from "../src/discovery/vcs/checks.js";
import { VcsStore } from "../src/discovery/vcs/store.js";

const USAGE =
  "Usage: d0_attest_cited_source.ts <qid> <spec> --id <lem:id> --expect-locator <text> " +
  "--verbatim <source-statement> --note <provenance> " +
  "(--upstream <primary citation> [--upstream-locator <text>] [--upstream-cite <bibkey>] | --upstream-none)";

async function main(): Promise<void> {
  const cli = readArgs(process.argv.slice(2));
  const [qid, spec] = cli.positionals();
  const id = cli.value("--id");
  const locator = cli.value("--expect-locator");
  const verbatim = cli.value("--verbatim");
  const note = cli.value("--note");
  if (!qid || !spec || !id || !locator || !verbatim?.trim() || !note?.trim()) throw new Error(USAGE);
  const repoRoot = findCausalSmithRoot(process.cwd());
  const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: true };
  await withRunHeartbeat(repoRoot, qid, spec, async () => {
    const store = VcsStore.at(ctx);
    await assertNoUncommittedEdits(ctx, store);
    const { head, graph } = await headGraph(store);
    const node = statementBlob(graph, id);
    if (node === undefined || node.body.resolved_by !== undefined) throw new Error(`${id} is not a live statement`);
    if (node.body.source === undefined) throw new Error(`${id} is not a cited statement (no source)`);
    if (node.body.source.locator !== locator) throw new Error(`${id} locator is ${JSON.stringify(node.body.source.locator)}, expected ${JSON.stringify(locator)}`);
    if (node.body.source.verbatim_statement) throw new Error(`${id} already has a verbatim source statement; refusing overwrite`);
    const suppliedVerbatim = verbatim.trim();
    const markers = detectUpstreamMarkers(suppliedVerbatim);
    const acknowledgeMarker = cli.value("--acknowledge-marker");
    if (markers.length > 0 && !acknowledgeMarker?.trim()) {
      throw new Error(`the verbatim text carries upstream-attribution marker(s) ${markers.join(", ")}; decide provenance and pass --acknowledge-marker`);
    }
    const requestedUpstream = resolveUpstreamDecision({
      upstream: cli.value("--upstream"),
      upstreamLocator: cli.value("--upstream-locator"),
      upstreamCite: cli.value("--upstream-cite"),
      upstreamNone: cli.bool("--upstream-none"),
      acknowledgeMarker,
      verbatim: suppliedVerbatim,
      bibkeys: new Set(nodesOfType(graph, "bib").map((b) => b.blob.body.key)),
    });
    const attestationNote = acknowledgeMarker?.trim() ? `${note.trim()} [marker acknowledged: ${acknowledgeMarker.trim()}]` : note.trim();
    const { verbatim_statement: _v, attestation: _a, upstream: _u, ...baseSource } = node.body.source;
    const source = {
      ...baseSource,
      verbatim_statement: suppliedVerbatim,
      ...(requestedUpstream ? { upstream: requestedUpstream } : {}),
      attestation: { by: "main" as const, note: attestationNote, at: new Date().toISOString() },
    };
    const next = { node_type: "statement" as const, body: { ...node.body, source } };
    const nodes = new Map(graph.nodes);
    nodes.set(id, next);
    const tree = { ...graph.tree, [id]: { ...graph.tree[id], blob: blobId(next) } };
    const result = await commitGraph({
      store, graph: { tree, nodes }, parents: [head], author: "orchestrator", kind: "direct",
      message: `attest cited source of ${id} (${locator})`, expectedHead: head,
    });
    if (!result.ok) throw new Error(`attestation refused:\n${formatViolations(result.violations)}`);
    await publishCore(ctx, store);
    console.log(JSON.stringify({
      id, locator, commit: result.id, verbatimLength: suppliedVerbatim.length, attestedBy: "main",
      upstream: requestedUpstream ?? "none (affirmed original to the cited work)",
    }, null, 2));
  });
}

main().catch((error: unknown) => {
  console.error(`d0_attest_cited_source: ${error instanceof Error ? error.message : String(error)}`);
  process.exitCode = 1;
});

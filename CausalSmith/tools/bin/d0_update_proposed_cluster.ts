#!/usr/bin/env -S npx tsx
/**
 * Orchestrator-only: correct a stale proposal cluster. The cluster lives in
 * `state.proposed_from.cluster` and in the graph's meta node; both move together
 * (one direct commit + one state write), guarded by `--expect-cluster`.
 *
 * Usage: d0_update_proposed_cluster.ts <qid> <spec> --expect-cluster <old> --cluster <new> [--check]
 */
import process from "node:process";
import type { PipelineContext } from "../src/types.js";
import { appendEntry } from "../src/decision_log.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";
import { withRunHeartbeat } from "../src/shared/run_heartbeat.js";
import { loadState, saveState } from "../src/state.js";
import { commitGraph, headGraph, publishCore } from "../src/discovery/vcs/commit.js";
import { META_ID, blobId, type NodeBlob } from "../src/discovery/vcs/node.js";
import { formatViolations } from "../src/discovery/vcs/checks.js";
import { VcsStore } from "../src/discovery/vcs/store.js";

const CLUSTERS = ["panel", "exactid", "partialid", "stat", "experimentation", "scm"] as const;
type Cluster = (typeof CLUSTERS)[number];

function parseCluster(value: string, flag: string): Cluster {
  if (!(CLUSTERS as readonly string[]).includes(value)) {
    throw new Error(`${flag} must be one of ${CLUSTERS.join(", ")}; got ${JSON.stringify(value)}`);
  }
  return value as Cluster;
}

async function main(): Promise<void> {
  const cli = readArgs(process.argv.slice(2));
  const [qid, spec] = cli.positionals();
  const expected = cli.value("--expect-cluster");
  const cluster = cli.value("--cluster");
  const check = cli.bool("--check");
  if (!qid || !spec || !expected?.trim() || !cluster?.trim()) {
    throw new Error("Usage: d0_update_proposed_cluster.ts <qid> <spec> --expect-cluster <old> --cluster <new> [--check]");
  }
  const expectedCluster = parseCluster(expected, "--expect-cluster");
  const nextCluster = parseCluster(cluster, "--cluster");
  if (expectedCluster === nextCluster) throw new Error("old and new clusters are identical");
  const repoRoot = findCausalSmithRoot(process.cwd());
  await withRunHeartbeat(repoRoot, qid, spec, async () => {
    const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: check, resume: true };
    const state = await loadState(repoRoot, qid, spec);
    if (!state.proposed_from) throw new Error("missing proposed_from state");
    const store = VcsStore.at(ctx);
    const { head, graph } = await headGraph(store);
    const meta = graph.nodes.get(META_ID);
    if (meta?.node_type !== "meta") throw new Error("graph has no meta node");
    const carriers = { state: state.proposed_from.cluster, core: meta.body.cluster };
    for (const [name, value] of Object.entries(carriers)) {
      if (value !== expectedCluster) throw new Error(`${name} cluster is ${JSON.stringify(value)}, expected ${JSON.stringify(expectedCluster)}`);
    }
    const receipt = { before: carriers, after: { state: nextCluster, core: nextCluster }, main: head };
    if (check) {
      console.log(JSON.stringify({ check: true, ...receipt }, null, 2));
      return;
    }
    const metaNext: NodeBlob = { node_type: "meta", body: { ...meta.body, cluster: nextCluster } };
    const nodes = new Map(graph.nodes);
    nodes.set(META_ID, metaNext);
    const tree = { ...graph.tree, [META_ID]: { ...graph.tree[META_ID], blob: blobId(metaNext) } };
    const result = await commitGraph({
      store, graph: { tree, nodes }, parents: [head], author: "orchestrator", kind: "direct",
      message: `cluster ${expectedCluster} -> ${nextCluster}`, expectedHead: head,
    });
    if (!result.ok) throw new Error(`cluster update refused:\n${formatViolations(result.violations)}`);
    state.proposed_from.cluster = nextCluster;
    await saveState(repoRoot, qid, spec, state);
    await publishCore(ctx, store);
    appendEntry(repoRoot, qid, {
      type: "command", from: "D", phase: "D", stage: "D0",
      round: state.flags.d0_loop_counters?.solve_rounds ?? 0,
      cmd: "update-proposed-cluster", target: nextCluster,
      note: `Guarded cluster synchronization ${expectedCluster} -> ${nextCluster} across state and the graph (commit ${result.id.slice(0, 12)}).`,
    }, spec);
    console.log(JSON.stringify({ ...receipt, commit: result.id }, null, 2));
  });
}

main().catch((error: unknown) => {
  console.error(`d0_update_proposed_cluster: ${error instanceof Error ? error.message : String(error)}`);
  process.exitCode = 1;
});

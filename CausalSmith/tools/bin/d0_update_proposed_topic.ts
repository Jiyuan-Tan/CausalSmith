#!/usr/bin/env -S npx tsx
/** Main-orchestrator writer for a stale proposal topic that remains injected into D0 prompts. */
import { readFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";
import { loadState, saveState } from "../src/state.js";
import { formalizationDir } from "../src/paths.js";
import { writeJsonAtomic } from "../src/shared/json_atomic.js";

function replaceAuditedTopic(
  value: unknown,
  expectedFragment: string,
  auditedTopic: string,
  label: string,
): string {
  if (value === auditedTopic) return auditedTopic;
  if (typeof value === "string" && value.includes(expectedFragment)) return auditedTopic;
  throw new Error(`${label} does not contain expected fragment ${JSON.stringify(expectedFragment)}`);
}

async function main(): Promise<void> {
  const cli = readArgs(process.argv.slice(2));
  const [qid, spec] = cli.positionals();
  const topic = cli.value("--topic");
  const expectContains = cli.value("--expect-contains");
  if (!qid || !spec || !topic?.trim() || !expectContains?.trim()) {
    throw new Error("Usage: d0_update_proposed_topic.ts <qid> <spec> --expect-contains <old-fragment> --topic <audited-topic>");
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const state = await loadState(repoRoot, qid, spec);
  const prior = state.proposed_from?.topic;
  if (!state.proposed_from) throw new Error("missing proposed_from state");

  const auditedTopic = topic.trim();
  const gapsPath = path.join(formalizationDir(repoRoot, qid), "discovery", "gaps.json");
  const gaps = JSON.parse(await readFile(gapsPath, "utf8")) as Record<string, unknown>;

  const beforeWithoutTopics = JSON.stringify({
    ...state,
    pre_d0_intent: state.pre_d0_intent && { ...state.pre_d0_intent, topic: undefined },
    proposed_from: { ...state.proposed_from, topic: undefined },
  });
  state.proposed_from.topic = replaceAuditedTopic(
    state.proposed_from.topic, expectContains, auditedTopic, "current proposed_from.topic",
  );
  if (state.pre_d0_intent) {
    state.pre_d0_intent.topic = replaceAuditedTopic(
      state.pre_d0_intent.topic, expectContains, auditedTopic, "current pre_d0_intent.topic",
    );
  }
  gaps.topic = replaceAuditedTopic(gaps.topic, expectContains, auditedTopic, "gaps.topic");
  const afterWithoutTopics = JSON.stringify({
    ...state,
    pre_d0_intent: state.pre_d0_intent && { ...state.pre_d0_intent, topic: undefined },
    proposed_from: { ...state.proposed_from, topic: undefined },
  });
  if (beforeWithoutTopics !== afterWithoutTopics) throw new Error("topic writer changed another state field; refusing save");

  // gaps.json first, state last: the command accepts either the old or the audited
  // value, so an interruption is repaired by reissuing the same invocation.
  await writeJsonAtomic(gapsPath, gaps);
  await saveState(repoRoot, qid, spec, state);
  console.log(JSON.stringify({ before: prior, after: state.proposed_from.topic }, null, 2));
}

main().catch((error: unknown) => {
  console.error(`d0_update_proposed_topic: ${error instanceof Error ? error.message : String(error)}`);
  process.exitCode = 1;
});

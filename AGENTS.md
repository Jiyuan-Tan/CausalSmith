# Codex Project Guide
Before making changes in this repository, read and follow `.claude/CLAUDE.md`.
Treat it as the project guide for proof style, documentation workflow, and
Lean-specific conventions.

Always verify before finishing work in this repository. For Lean changes, use
the Lean LSP/type checker as the default verification path, following
`.claude/CLAUDE.md`. This is a standing project instruction from the user and
counts as explicit permission to verify before reporting completion.

The `.claude` directory also contains project skills/workflows. In particular, for Lean theorem-proving tasks, inspect the relevant files under:

- `.claude/skills/lean4-theorem-proving/`

Use those skill files as local project guidance when they apply. If any
`.claude` instruction conflicts with higher-priority Codex system/developer
instructions, follow the higher-priority instruction and preserve the project intent as closely as possible.

When the inline prompt header identifies the caller as CausalSmith research (any `CausalSmith/tools/src/discovery/prompts/` or `CausalSmith/tools/src/formalization/prompts/` content), treat the inline prompt as authoritative. Do NOT load `.claude/skills/*/SKILL.md` or `.claude/agents/*.md` unless the inline prompt explicitly names that path. CLAUDE.md cues about conditional skills (e.g. `formalization-with-user`) do not apply inside autonomous CausalSmith research stages.

**Pipeline task prompts are self-contained.** A prompt whose first line is `=== PROMPT: <name> ===`
comes from a CausalSmith presentation stage (judges, writers, reviewers). For such a prompt: do NOT read `.claude/CLAUDE.md`, skills, or agent files — nothing
in them applies; do not run verification or builds beyond what the prompt itself asks; read Lean or
paper sources only where the prompt tells you to, and only the ranges it names. The prompt carries
every contract that governs the task.

## Where a CausalSmith research run lives (construct this path, never search for it)

    CausalSmith/doc/research/active/<qid>/           # live run
    CausalSmith/doc/research/_bank/<tier>/<qid>_<spec>/   # finished (tier: accepted|downgraded|failed)

The specialization (`v1`, `v2`, …) is a FIELD inside `state.json`, **not** a directory: there is no
`<qid>/v1/`. Inside a run dir: `state.json`, `pipeline.jsonl`, `discovery/`, `reviews/`, `orchestrator/`,
`logs/` (gitignored).

To resolve a run dir, use the known prefix — do not hunt:

    ls -d CausalSmith/doc/research/active/<qid>*/ 2>/dev/null

**Never run a recursive walk from `/`, `/soalnas`, `/sailhome`, `/scr` or `/tmp`, and always bound a
repo walk with `-maxdepth`.** The tree is on a shared network mount: an unbounded walk wedges in
uninterruptible disk wait, is orphaned when the calling tool times out, and then blocks every later
command from that agent. If a path does not resolve, re-read the qid and the prefix above rather than
widening the search.

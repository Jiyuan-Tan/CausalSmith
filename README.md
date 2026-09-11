# CausalSmith

**🌐 Website: [jiyuan-tan.github.io/CausalSmith](https://jiyuan-tan.github.io/CausalSmith/)** —
browse the Causalean library (every definition and theorem with a plain-English
translation) and the machine-verified working papers.

**📄 Paper: [CausalSmith: A Formally Grounded, Self-Improving Agentic Framework
for Automated Research in Causal
Inference](https://arxiv.org/abs/2607.22511)** — Tan & Syrgkanis,
arXiv:2607.22511. The paper describing this project.

CausalSmith lays foundations for **formalized, machine-checked causal inference**
and builds an **AI theorem pipeline** on top of it. The project is two
[Lean 4](https://leanprover.github.io/) packages with a one-way dependency — the
`Causalean` library, and the `CausalSmith` package that carries the pipeline and
shares the project's name:

- **`Causalean/`** — the foundational library. Built on
  [Mathlib](https://github.com/leanprover-community/mathlib4), it formalizes core
  objects and results of modern causal inference — structural causal models,
  do-calculus, potential outcomes, identification (backdoor, frontdoor, IV, DID,
  LATE, …), partial identification / bounds, panel and design-based inference,
  causal discovery, and semiparametric estimation theory — with full
  machine-checked proofs. Documented in [`doc/API.md`](doc/API.md).
- **`CausalSmith/`** — an umbrella package containing `CausalSmith research`, an
  LLM-driven pipeline that proposes and formally verifies new causal-inference
  theorems on top of Causalean. Causalean never imports CausalSmith.

> This repository is a periodically synced snapshot of an internal development
> repo: history arrives as squashed sync commits, and process/working material is
> not included. Issues are welcome; for substantial contributions please open an
> issue first so changes can be coordinated with the internal tree.

## Using the pipeline in three steps

The pipeline is operated *through* a coding agent: you install the two agent
CLIs once, and from then on you ask an agent to set the repository up and to run
the pipeline for you. You do not need to know Lean or the internals.

**1. Install Claude Code and Codex, and sign both in.**

```sh
npm install -g @anthropic-ai/claude-code   # Claude Code — then run `claude` once to sign in
npm install -g @openai/codex               # Codex        — then run `codex login`
```

Both are required: the pipeline drives Codex for discovery and proof work and
Claude for review and judging, and it spends those two logins by default (an
API key is an opt-in alternative — see [Model access](#model-access-for-the-pipeline)).

**2. Ask either agent to install CausalSmith.** Clone the repository, start
`claude` or `codex` inside it, and say:

> Set this repository up for the CausalSmith pipeline: follow the "Manual
> install" section of README.md and CausalSmith/doc/SETUP.md, then run the quick
> check in SETUP.md and tell me what you did.

The agent installs the Lean toolchain; downloads Mathlib's build cache and
Causalean's **prebuilt oleans** (a `.tar.zst` archive published as a release
asset on the `build-cache` tag, so the first build takes minutes rather than
hours); builds the library; installs the Node tooling; downloads the
**fine-tuned retrieval models** (about 2.3 GB, same release tag; they power the
semantic search tier the pipeline uses to find reusable lemmas); and writes the
machine-specific config. (Windows users: read the [platform notes](#platform-notes)
first.)

**3. Ask either agent to run the pipeline.** The workflow lives in the project
skill `.claude/skills/causalsmith/SKILL.md`; Claude Code exposes it as a slash
command, and Codex reads it on request.

| You want to… | In Claude Code | In Codex |
|---|---|---|
| Run the pipeline without bringing a topic | "Run the CausalSmith research pipeline and choose the topic yourself" | "Follow .claude/skills/causalsmith/SKILL.md: run the research pipeline and choose the topic yourself" |
| Get topic suggestions | `/causalsmith-topics <area>` | "Follow .claude/skills/causalsmith-topics/SKILL.md for `<area>`" |
| Discover, prove and bank a theorem | `/causalsmith research --propose "<topic>" <qid> v1 --auto` | "Follow .claude/skills/causalsmith/SKILL.md: run `causalsmith research --propose "<topic>" <qid> v1 --auto`" |
| Turn an accepted result into a paper | `/causalsmith present <qid> v1` | "Follow .claude/skills/causalsmith-present/SKILL.md for `<qid> v1`" |

**You do not have to supply a topic.** Asked to run the pipeline without one,
the agent first dispatches the topic-selection sub-skill, which searches the
literature and the bank of finished runs for an area with real headroom, then
names the run and launches it. Give it a topic and an id only when you want the
run pinned to an idea of your own.

`<qid>` is a short snake_case id you choose when you name a run yourself (see
[`CausalSmith/doc/qid-naming.md`](CausalSmith/doc/qid-naming.md)); `--auto` lets
the agent decide every checkpoint itself and stop only at the end. A finished run
lands in `CausalSmith/doc/research/_bank/accepted/<qid>_v1/` with its Lean proofs
under `CausalSmith/CausalSmith/`; the agent reports where. Everything the agent
follows is in [`CausalSmith/doc/USER_MANUAL.md`](CausalSmith/doc/USER_MANUAL.md)
if you want to drive it by hand.

## Manual install

This is what the agent does in step 2; you can also do it by hand.
Linux, macOS, and Windows are all supported. The commands below are for a POSIX
shell; on Windows run them from **Git Bash** (installed with Git for Windows) and
read the [platform notes](#platform-notes) first.

```sh
# 0. Clone (Windows: see the platform notes for the long-path setting)
git clone https://github.com/Jiyuan-Tan/CausalSmith.git && cd CausalSmith

# 1. Toolchain — elan reads lean-toolchain and installs the pinned Lean version
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh   # Linux/macOS; Windows: elan-init.exe (see below)

# 2. Build the library — both caches make this minutes instead of hours
lake exe cache get               # Mathlib's prebuilt oleans
scripts/fetch_build_cache.sh     # Causalean's prebuilt oleans (a GitHub release asset; needs curl, tar, zstd)
lake build                       # only what changed since the cached commit

# 3. Retrieval tooling — how you actually find things in a ~8000-declaration library
cd CausalSmith/tools && npm install
npm run search -- "backdoor adjustment"

# 4. Optional: the fine-tuned retrieval models (~2.3 GB, same release tag) for semantic search
cd ../.. && scripts/fetch_retrieval_models.sh   # needs curl, tar, zstd
cd CausalSmith/tools && npm run embed:library    # Python 3 + sentence-transformers; Linux/macOS only
npm run search -- --semantic "backdoor adjustment"
```

Both release assets live on the `build-cache` tag of this repository:
`causalean-build-<sha>.tar.zst` / `causalean-build-latest.tar.zst` (the prebuilt
oleans; `fetch_build_cache.sh` picks the exact commit when published, else the
latest and lets `lake` rebuild the delta) and `retrieval_model_ft.tar.zst` /
`retrieval_reranker_ft.tar.zst` (the model weights, unpacked into `doc/`).
Steps 2 and 4 need `zstd` (`apt install zstd`, `brew install zstd`, or the
[zstd releases](https://github.com/facebook/zstd/releases) on Windows).
Step 3 needs Node ≥ 20.20.2 and is worth doing before you read any Lean source:
the library is large, and `npm run search` is the intended entry point for
locating a definition, lemma, or module. Everything above needs only this clone —
no API keys, no sibling checkouts, no credentials; the only network access is to
Mathlib's cache and this repository's release assets. (Running the theorem-generation pipeline is
the one part that needs model access — see below.)

Then, depending on what you came for:

| You want to… | Start at |
|---|---|
| Find a specific definition or lemma | `npm run search -- "<concept>"` (see below) |
| Orient in an unfamiliar area | `npm run search -- --scope module "<area>"` |
| Browse a module's API | [`doc/API.md`](doc/API.md), section `## <n>. <path>` |
| Contribute a declaration | Write the docstring — see [Documentation](#documentation) |
| Run the theorem-generation pipeline | [Using the pipeline in three steps](#using-the-pipeline-in-three-steps) |

### Platform notes

- **Windows — clone.** Every tracked path is kept under 200 characters, so a plain
  `git clone` works from the usual locations (`C:\Users\<you>\...`). A deeply
  nested clone directory or the Lean build tree can still approach Windows'
  260-character limit, so enabling long paths once is recommended:
  `git config --global core.longpaths true` (or `git clone -c core.longpaths=true …`).
- **Windows — shell and tools.** Use Git Bash for the commands above. `curl` and
  `tar` ship with Git for Windows; put `zstd.exe` on `PATH` for the cache scripts.
  Install elan with `elan-init.exe` from the
  [elan releases](https://github.com/leanprover/elan/releases) (or let the VS Code
  Lean 4 extension install it); `lake` then works from Git Bash or PowerShell.
  `.gitattributes` keeps the shell scripts LF whatever `core.autocrlf` is set to.
- **macOS.** Everything works as on Linux; `brew install zstd` for the cache scripts.
  The default file system is case-insensitive, and the repository contains no
  paths that differ only by case.
- **Semantic retrieval** (the optional embedding tier and its Python daemons) is
  Linux/macOS only; the default lexical `npm run search` works everywhere. The
  pipeline's own Windows notes are in
  [`CausalSmith/doc/SETUP.md`](CausalSmith/doc/SETUP.md#windows).

### Model access for the pipeline

The library and the search tooling need no credentials. The `CausalSmith
research` pipeline does — it drives the `claude` and `codex` CLIs — and you
choose how those calls are paid for:

- **Subscription (default).** Sign the two CLIs in (`claude`, then `codex
  login`) and runs spend those logins. Nothing to configure.
- **API key.** Set `"authMode": "api"` in `CausalSmith/tools/config/local.json`
  (gitignored; copy `local.example.json`) and supply `anthropicApiKey` /
  `openaiApiKey` — inline, or as `anthropicApiKeyFile` / `openaiApiKeyFile`
  paths to files outside the repo. The `ANTHROPIC_API_KEY` / `OPENAI_API_KEY`
  environment variables override the file.

`anthropicAuth` and `openaiAuth` set the mode per provider, so running the
claude workers on an API key while codex stays on its subscription is a
supported mix. Selecting `api` without a key aborts the run rather than quietly
falling back to a subscription, and each run prints which path it resolved.
Full reference: [`CausalSmith/doc/SETUP.md`](CausalSmith/doc/SETUP.md).

## Finding things in the library

Causalean has ~8000 declarations, so grep is usually the wrong tool. The project
ships a ranked retrieval CLI over a docstring-derived index
(`doc/library_index.json`), which is the same engine the CausalSmith pipeline
uses to find reusable lemmas:

```sh
cd CausalSmith/tools

# Concept search (default) — lexical ranking over names, statements, docstrings
npm run search -- "weak overlap minimax rate"

# Type-pattern search, loogle-style
npm run search -- --type "Measure _ → ℝ≥0∞"

# Goal-directed: paste a Lean goal, get lemmas that could close it
npm run search -- --goal "∀ x, f x ≤ g x"

# Module-level orientation: "which file should I read?" rather than "which lemma?"
npm run search -- --scope module "design-based interference"
```

Useful flags: `--k N` (results, default 8), `--cluster panel|exactid|partialid|stat|experimentation|scm`
to restrict the search area, and `--semantic` to add an embedding tier on top of
lexical ranking. The embedding tier requires `npm run embed:library` (Python 3 +
`sentence-transformers`); `--scope module` switches it on automatically whenever
the embeddings are present and fresh, so that mode is slower on first use. The
fine-tuned encoder and reranker behind that tier are gitignored weight
directories: `scripts/fetch_retrieval_models.sh` downloads them (about 2.3 GB,
published as release assets) into `doc/`; without them the tooling falls back to
the off-the-shelf `BAAI/bge-large-en-v1.5` checkpoint.

Each hit shows the score, fully-qualified name, type signature, source file,
whether it is `tier-1` or carries a `⚠usesSorry` flag, and the docstring's
plain-English first paragraph — enough to decide whether to open the file.

If the CLI reports a missing or stale index, regenerate it:

```sh
lake build && lake exe library_index      # from the repository root
```

Two other retrieval surfaces:

- **Library explorer web app** — `CausalSmith/site/` (Astro) renders the same
  index as a browsable `/library` section with natural-language cards for
  headline theorems. `cd CausalSmith/site && npm install && npm run dev`.
- **`lean-lsp-mcp`** — if you work through an MCP-capable editor or agent, it
  gives in-file goal inspection and single-file declaration search, complementing
  the project-wide ranked search above.

## Repository layout

```
Causalean/            Foundational Lean library (the deliverable)
  Graph/              DAGs, d-separation (Bayes Ball), SWIG, c-components
  SCM/                Structural causal models, do-calculus, Markov properties;
                      ID/ (identifiability, do-calculus), PartialID/, Examples/
  PO/                 Potential outcomes: consistency, counterfactuals, laws;
                      ID/Exact/ (backdoor, frontdoor, ATE, DID, LATE, RDD, …),
                      ID/Partial/ (Manski, Balke–Pearl, Lee, Fréchet, random-set)
  Panel/              Panel-data substrate and estimand characterization
  Experimentation/    Design-based / randomization & anytime-valid inference
  Stat/, Estimation/  Semiparametric inference, concentration, DML/AIPW, minimax
  ML/                 Learning-theoretic foundations (ERM, risk, rates); uses FoML
  Discovery/          Causal discovery (invariant prediction)
  Mathlib/            Project-local Mathlib-style additions (promotion staging)
CausalSmith/          Theorem-generation pipeline (depends on Causalean)
  CausalSmith/        Generated + hand-written theorem outputs
  tools/              TypeScript pipeline (see CausalSmith/doc/SETUP.md)
  site/               Library-explorer web app (/library)
  doc/                Pipeline API, USER_MANUAL.md, SETUP.md; research/_bank/
                      holds the pipeline's banked runs
doc/                  Causalean docs: API.md, library_index.json
```

## Building

[`elan`](https://github.com/leanprover/elan) pins the Lean toolchain (see
[`lean-toolchain`](lean-toolchain)); with `elan` and `lake` installed the two
packages build independently:

```sh
lake exe cache get          # fetch Mathlib build cache (do this first — it saves hours)
scripts/fetch_build_cache.sh  # fetch Causalean's prebuilt oleans (release asset; lake rebuilds only the delta)
lake build                  # Causalean, the foundational library
lake -d CausalSmith build   # CausalSmith pipeline package (optional; depends on Causalean)
```

A full `lake build` is slow. When iterating, build a single module —
`lake build Causalean.PO.ID.Exact.Frontdoor` — or use `lean-lsp-mcp` for
incremental diagnostics without a build.

A fresh clone builds with no extra setup: the one non-Mathlib dependency,
`FoML` (Rademacher-complexity foundations, consumed by
`Causalean/Stat/Concentration/`, `Causalean/Estimation/`, `Causalean/ML/`), is a
vendored, MIT-licensed adaptation of
[`auto-res/lean-rademacher`](https://github.com/auto-res/lean-rademacher) carried
in-tree under [`third_party/lean-rademacher/`](third_party/lean-rademacher/) (see
its `UPSTREAM.md`). See [`CausalSmith/doc/SETUP.md`](CausalSmith/doc/SETUP.md) for
the pipeline's additional prerequisites.

## Documentation

- **[`doc/API.md`](doc/API.md)** — per-module API reference (derived from
  declaration docstrings).
- **[`CausalSmith/doc/USER_MANUAL.md`](CausalSmith/doc/USER_MANUAL.md)** — how to
  run the `CausalSmith research` pipeline.
- **[`CausalSmith/doc/SETUP.md`](CausalSmith/doc/SETUP.md)** — environment
  prerequisites for the pipeline.

Per-declaration documentation is **docstring-canonical**: each declaration's
plain-English description is authored once, in its Lean docstring, where the
first paragraph is a self-contained natural-language translation of the formal
statement written for a reader with no Lean background. Everything else —
`doc/API.md`'s per-declaration tables, `doc/library_index.json`, the search
embeddings, and the web explorer — is *derived* from those docstrings and
regenerated, never hand-edited.

So to document something, write its docstring; to describe a whole file, write
its `/-! -/` module docstring. After changing declarations or docstrings,
regenerate the derived views:

```sh
lake build && lake exe library_index                 # index (reads the .olean, so build first)
cd CausalSmith/tools && npm run doc:gen              # API.md generated tables
npm run embed:library && npm run lint:embeddings     # semantic search tier (optional)
```

Run `npm run doc:check` before committing to confirm `doc/API.md` is in sync; CI
(`.github/workflows/kb-lint.yml`) runs the knowledge-base and NL-crosslink lints.

## License

Licensed under the [Apache License 2.0](LICENSE). See [`NOTICE`](NOTICE) for
attribution and third-party dependencies.

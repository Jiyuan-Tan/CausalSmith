module
public import Causalean.Discovery
public import Causalean.Estimation
public import Causalean.Experimentation
public import Causalean.Graph
public import Causalean.ML
public import Causalean.Mathlib
public import Causalean.PO
public import Causalean.Panel
public import Causalean.SCM
public import Causalean.Stat
public import Causalean.Tactic

/-!
This top-level module gathers the Causalean library into one import, spanning
graphical causal models, potential outcomes, identification, partial
identification, panel regression algebra, statistics, estimation theory, the
design-based (randomization) inference substrate, and the standalone
machine-learning spine.
-/

public section

-- Structure-agnostic ATE optimality (Jin–Syrgkanis 2024): single roll-up entry point.
-- See `Estimation/MinimaxATE.lean` for the headline-theorem index.
-- CausalSmith research catalogue moved to the sibling package `CausalSmith/`. The umbrella
-- no longer imports any Q1_*/Q2_*/Q3_*/Q5_*/Q6_* theorem files; the Markov
-- ergodicity helper (Q1-coupled) and the Q1-coupled HomogeneousCollapse file
-- moved with them. Build the CausalSmith research catalogue via `lake -d CausalSmith build`
-- (sibling package; depends on this Causalean library). The Panel.Prompt
-- registry + `panelquestion_export` executable also moved with them â€” they
-- were pure CausalSmith pipeline infrastructure, not Causalean foundations.

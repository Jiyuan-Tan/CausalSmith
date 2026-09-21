/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Fixed Longitudinal Treatment Path: setup (general `n`)

General-`n` data layer for the sequential backdoor identification result
(`prop:po-dynamic-backdoor` from Basic Concepts.tex, subsection
`subsec:po-dynamic-regime`).

Design choices:
* Per-sequence exchangeability: hypotheses are quantified `∀ dbar : Fin n → δ`.
* Homogeneous treatment space `δ`; heterogeneous state types `γ : Fin n → Type`.
* Distinctness is kept as five separate hypotheses (not `Function.Injective`
  on a sum type) to make use sites clean.

Naming note: in the tex the intervention sequence is written `d̄`.  Lean's
lexer does not accept the grapheme cluster `d̄` as an identifier, so we use
`dbar` throughout.
-/

module
public import Causalean.PO.Assumptions.ConsistencyLemmas
public import Causalean.PO.Assumptions.IndepCF
public import Causalean.PO.Conditioning.CondExpTooling
public import Causalean.PO.Conditioning.Bundle
public import Causalean.Mathlib.Probability.Independence.Conditional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Independence.Conditional

/-! # Fixed Longitudinal Treatment Path Setup

This file provides the general finite-horizon potential-outcome setup for
prescribed longitudinal treatment paths. It defines stagewise states,
treatments, fixed-path interventions, sequential assumptions, and observable
adjusted functionals used by treatment-path identification theorems.

Each intervention is fixed by `dbar : Fin n → δ` before histories are observed.
No action can depend on an observed history, so this API does not represent
adaptive treatment policies despite the historical `DTR` directory name and
source-section label.

The setup allows heterogeneous state types across stages and a common treatment
value space across stages. The identification assumption bundle restricts that
treatment alphabet to a countable measurable space: its universal singleton
overlap condition cannot hold at a positive horizon for an uncountable alphabet.
Sequential exchangeability and overlap are stated for each treatment sequence
and stage.

The main public objects are `POLongitudinalPathSystem`, treatment-sequence regimes
`regimeUpTo` and `regime`, counterfactuals `Y_of` and `S_of`, history bundles,
the assumption bundle `Assumptions`, the backward-recursive regression
`innerReg`, and the estimands `treatmentPathMean` and `adjustedTreatmentPathMean`. -/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

/-- A fixed longitudinal treatment-path system packages [stage-indexed state
variables](hyp:S), [treatment nodes](hyp:D), and [a terminal outcome](hyp:Y). It records
[common treatment-space identifications](hyp:hDmeas),
[a real-valued outcome identification](hyp:hYreal),
[pairwise distinct state nodes](hyp:distinctSS),
[pairwise distinct treatment nodes](hyp:distinctDD),
[separation of states from treatments](hyp:distinctSD),
[separation of states from the outcome](hyp:distinctSY), and
[separation of treatments from the outcome](hyp:distinctDY).

Field guide:
* `S k` is the stage-`k` state or history-dependent covariate variable.
* `D k` is the stage-`k` treatment node in the ambient potential-outcome system.
* `Y` is the terminal outcome node.
* `hDmeas k` identifies the value space of treatment node `D k` with the common
  treatment alphabet `δ`.
* `hYreal` identifies the outcome value space with the real line.
* `distinctSS`, `distinctDD`, `distinctSD`, `distinctSY`, and `distinctDY` record
  that state, treatment, and outcome nodes are genuinely separate variables. -/
structure POLongitudinalPathSystem (P : POSystem) (n : ℕ) (δ : Type)
    (γ : Fin n → Type)
    [MeasurableSpace δ] [MeasurableSingletonClass δ]
    [∀ k, MeasurableSpace (γ k)] where
  /-- Stage-`k` state variable `Sₖ` (history-dependent covariates observed
  before the stage-`k` treatment is assigned), valued in the stage's type `γ k`. -/
  S : ∀ k : Fin n, POVar P (γ k)
  /-- Stage-`k` treatment node `Dₖ`, given as an index into the ambient system's
  variable set `P.V`. -/
  D : Fin n → P.V
  /-- The terminal outcome node `Y` (a variable of the ambient system). -/
  Y : P.V
  /-- Each treatment node `Dₖ` has value space measurably equivalent to the
  common treatment type `δ` (treatment alphabet is the same across stages). -/
  hDmeas : ∀ k : Fin n, P.X (D k) ≃ᵐ δ
  /-- The outcome node `Y` has value space measurably equivalent to `ℝ`. -/
  hYreal : P.X Y ≃ᵐ ℝ
  /-- The state nodes are distinct across stages (the map `k ↦ (S k).v` is
  injective). -/
  distinctSS : ∀ k l : Fin n, (S k).v = (S l).v → k = l
  /-- The treatment nodes are distinct across stages. -/
  distinctDD : Function.Injective D
  /-- No state node coincides with any treatment node. -/
  distinctSD : ∀ k l : Fin n, (S k).v ≠ D l
  /-- No state node coincides with the outcome node. -/
  distinctSY : ∀ k : Fin n, (S k).v ≠ Y
  /-- No treatment node coincides with the outcome node. -/
  distinctDY : ∀ k : Fin n, D k ≠ Y

namespace POLongitudinalPathSystem

variable {P : POSystem} {n : ℕ} {δ : Type} {γ : Fin n → Type}
variable [MeasurableSpace δ] [MeasurableSingletonClass δ]
variable [∀ k, MeasurableSpace (γ k)]

/-! ### POVar accessors -/

/-- [The treatment variable at a decision stage](goal) in [a longitudinal-path system](hyp:S)
[uses the selected stage](hyp:k) to [represent its treatment node on the common treatment
alphabet](step:1). -/
def dVar (S : POLongitudinalPathSystem P n δ γ) (k : Fin n) : POVar P δ :=
  ⟨S.D k, S.hDmeas k⟩

/-- [The terminal-outcome variable](goal) in [a longitudinal-path system](hyp:S)
[represents the terminal response on the real line](step:1). -/
def yVar (S : POLongitudinalPathSystem P n δ γ) : POVar P ℝ := ⟨S.Y, S.hYreal⟩

/-! ### Regimes -/

/-- [The intervention target path](goal) for [a longitudinal-path system](hyp:S) contains
[no treatment nodes at cutoff zero](step:1) and [at each positive cutoff adds the current
treatment node when that stage exists](step:2), so its targets are precisely the treatments
assigned before the cutoff.

It is defined independently of regimes so later regime construction can prove
the required disjointness facts. -/
def regimeTarget (S : POLongitudinalPathSystem P n δ γ) : ℕ → Finset P.V
  | 0 => ∅
  | k + 1 =>
      if h : k < n then insert (S.D ⟨k, h⟩) (S.regimeTarget k)
      else S.regimeTarget k

/-- [The regime target of a fixed-treatment-path system](hyp:S) [contains a variable
at a cutoff exactly when that variable is the treatment node of an earlier stage](goal),
so the recursive target set introduces no unintended interventions. -/
lemma regimeTarget_mem_iff (S : POLongitudinalPathSystem P n δ γ) :
    ∀ (k : ℕ) (_ : k ≤ n) (v : P.V),
      v ∈ S.regimeTarget k ↔ ∃ i : Fin n, i.val < k ∧ v = S.D i
  | 0, _, v => by
      simp [regimeTarget]
  | k + 1, h, v => by
      have hk : k < n := h
      simp only [regimeTarget, hk, ↓reduceDIte, Finset.mem_insert]
      constructor
      · rintro (rfl | hmem)
        · exact ⟨⟨k, hk⟩, Nat.lt_succ_self _, rfl⟩
        · rcases (S.regimeTarget_mem_iff k (Nat.le_of_lt hk) v).mp hmem with
            ⟨i, hi, rfl⟩
          exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
        · exact Or.inr ((S.regimeTarget_mem_iff k (Nat.le_of_lt hk) _).mpr
            ⟨i, hi', rfl⟩)
        · left
          have : (⟨k, hk⟩ : Fin n) = i := by
            apply Fin.ext; simp [hi']
          rw [this]

/-- [The certified partial regime](goal) for [a longitudinal-path system](hyp:S),
[a prescribed treatment path](hyp:dbar), and [a requested cutoff](hyp:k) [starts with the
empty intervention at cutoff zero](step:1) and [at each positive cutoff adds the current
treatment while certifying the resulting target set](step:2).

The pair `(regime, target-proof)` is built by recursion on `k`;
the target-proof at level `k` is needed to discharge the disjointness
hypothesis for `Regime.sqcup` at level `k+1`. -/
noncomputable def regimeUpToAux (S : POLongitudinalPathSystem P n δ γ) (dbar : Fin n → δ) :
    (k : ℕ) → k ≤ n →
      { r : Regime P.V P.X // r.target = S.regimeTarget k }
  | 0, _ => ⟨Regime.empty, by simp [regimeTarget, Regime.empty]⟩
  | k + 1, h =>
      have hk : k < n := h
      let rec_pair := S.regimeUpToAux dbar k (Nat.le_of_lt hk)
      let r_rec : Regime P.V P.X := rec_pair.1
      have hrec : r_rec.target = S.regimeTarget k := rec_pair.2
      let v := S.D ⟨k, hk⟩
      have hv_not : v ∉ r_rec.target := by
        rw [hrec]
        intro hmem
        rcases (S.regimeTarget_mem_iff k (Nat.le_of_lt hk) _).mp hmem with
          ⟨i, hi, heq⟩
        have hFin : (⟨k, hk⟩ : Fin n) = i := S.distinctDD heq
        have hval : (k : ℕ) = i.val := by
          have := congrArg Fin.val hFin
          simpa using this
        omega
      let r_new := Regime.sqcup
        (Regime.single v ((S.hDmeas ⟨k, hk⟩).symm (dbar ⟨k, hk⟩))) r_rec
        (Regime.single_disjoint_of_not_mem _ _ hv_not)
      ⟨r_new, by
        show r_new.target = S.regimeTarget (k + 1)
        simp only [r_new, Regime.sqcup_target, Regime.single_target,
                   regimeTarget, hk, ↓reduceDIte]
        rw [hrec]
        ext w
        simp [Finset.mem_insert, v]⟩
termination_by k _ => k

/-- [The partial treatment regime](goal) for [a longitudinal-path system](hyp:S) follows
[the prescribed treatment path](hyp:dbar) through [a selected cutoff](hyp:k), whose
[validity within the horizon](hyp:h) ensures that [exactly the earlier treatments are
intervened on](step:1). -/
noncomputable def regimeUpTo (S : POLongitudinalPathSystem P n δ γ) (dbar : Fin n → δ)
    (k : ℕ) (h : k ≤ n) : Regime P.V P.X :=
  (S.regimeUpToAux dbar k h).1

/-- For [a longitudinal-path system](hyp:S), [a prescribed treatment path](hyp:dbar),
[a cutoff](hyp:k), and [proof that it lies within the horizon](hyp:h),
[the partial regime's target equals the standalone target set](goal). -/
lemma regimeUpTo_target_eq (S : POLongitudinalPathSystem P n δ γ) (dbar : Fin n → δ)
    (k : ℕ) (h : k ≤ n) :
    (S.regimeUpTo dbar k h).target = S.regimeTarget k :=
  (S.regimeUpToAux dbar k h).2

/-- [The full treatment regime](goal) for [a longitudinal-path system](hyp:S)
[uses a prescribed treatment path](hyp:dbar) to
[fix every stage's treatment to its corresponding path value](step:1). -/
noncomputable def regime (S : POLongitudinalPathSystem P n δ γ) (dbar : Fin n → δ) :
    Regime P.V P.X :=
  S.regimeUpTo dbar n (le_refl n)

/-! ### Counterfactuals and factuals -/

/-- [The regime-specific terminal outcome](goal) in [a longitudinal-path system](hyp:S)
[uses a prescribed treatment path](hyp:dbar) to [record each unit's terminal response under
the full intervention following that path](step:1). -/
noncomputable def Y_of (S : POLongitudinalPathSystem P n δ γ) (dbar : Fin n → δ) :
    P.Ω → ℝ := S.yVar.cf (S.regime dbar)

/-- [The regime-specific state at a decision stage](goal) in
[a longitudinal-path system](hyp:S) uses [a prescribed treatment path](hyp:dbar) and
[the selected stage](hyp:k) to [record the state reached after intervening on all earlier
treatments along that path](step:1). -/
noncomputable def S_of (S : POLongitudinalPathSystem P n δ γ) (dbar : Fin n → δ)
    (k : Fin n) : P.Ω → γ k :=
  (S.S k).cf (S.regimeUpTo dbar k.val (Nat.le_of_lt k.isLt))

/-- [The factual treatment at a stage](goal) in [a longitudinal-path system](hyp:S)
[uses the selected stage](hyp:k) to [record each unit's observed treatment there](step:1). -/
noncomputable def factualD (S : POLongitudinalPathSystem P n δ γ) (k : Fin n) : P.Ω → δ :=
  (S.dVar k).factual

/-- [The factual terminal outcome](goal) in [a longitudinal-path system](hyp:S)
[records each unit's observed response at the end of follow-up](step:1). -/
noncomputable def factualY (S : POLongitudinalPathSystem P n δ γ) : P.Ω → ℝ :=
  S.yVar.factual

/-- [The factual state at a stage](goal) in [a longitudinal-path system](hyp:S)
[uses the selected stage](hyp:k) to [record each unit's observed state there](step:1). -/
noncomputable def factualS (S : POLongitudinalPathSystem P n δ γ) (k : Fin n) : P.Ω → γ k :=
  (S.S k).factual

/-- [The terminal outcome under a prescribed treatment path](hyp:S,dbar)
[is measurable](goal), so its mean and history-conditional expectations are defined. -/
@[fun_prop]
lemma measurable_Y_of (S : POLongitudinalPathSystem P n δ γ) (dbar : Fin n → δ) :
    Measurable (S.Y_of dbar) :=
  S.yVar.measurable_cf _
/-- [The state reached at a selected stage along a prescribed treatment path](hyp:S,dbar,k)
[is measurable](goal), so it can enter subsequent histories. -/
@[fun_prop]
lemma measurable_S_of (S : POLongitudinalPathSystem P n δ γ) (dbar : Fin n → δ)
    (k : Fin n) : Measurable (S.S_of dbar k) :=
  (S.S k).measurable_cf _
/-- [The observed treatment at a selected decision stage](hyp:S,k) [is measurable](goal),
making stagewise treatment events observable. -/
@[fun_prop]
lemma measurable_factualD (S : POLongitudinalPathSystem P n δ γ) (k : Fin n) :
    Measurable (S.factualD k) := (S.dVar k).measurable_factual
/-- [The observed terminal outcome in a longitudinal-path system](hyp:S)
[is measurable](goal), so its adjusted and unadjusted means are defined. -/
@[fun_prop]
lemma measurable_factualY (S : POLongitudinalPathSystem P n δ γ) :
    Measurable S.factualY := S.yVar.measurable_factual
/-- [The observed state at a selected decision stage](hyp:S,k) [is measurable](goal), so
the stagewise history is observable. -/
@[fun_prop]
lemma measurable_factualS (S : POLongitudinalPathSystem P n δ γ) (k : Fin n) :
    Measurable (S.factualS k) := (S.S k).measurable_factual

/-! ### Indicators -/

/-- [The joint treatment-path agreement process](goal) for
[a longitudinal-path system](hyp:S) and [a prescribed treatment path](hyp:dbar) equals
[one at cutoff zero](step:1) and [at each positive cutoff multiplies the prior value by
agreement with the current treatment when that stage exists](step:2).

Defined by recursion on the stage cutoff `k`.  For `k > n` the extra factors
are dropped — callers should only use this with `k ≤ n`. -/
noncomputable def indD (S : POLongitudinalPathSystem P n δ γ) (dbar : Fin n → δ) :
    ℕ → P.Ω → ℝ
  | 0 => fun _ => 1
  | k + 1 => fun ω =>
      if h : k < n then
        S.indD dbar k ω * (S.dVar ⟨k, h⟩).indicator (dbar ⟨k, h⟩) ω
      else
        S.indD dbar k ω

/-- [The indicator that observed treatment follows a prescribed path](hyp:S,dbar)
[is measurable at every cutoff](goal), allowing it to weight conditional expectations. -/
@[fun_prop]
lemma measurable_indD (S : POLongitudinalPathSystem P n δ γ) (dbar : Fin n → δ) :
    ∀ k : ℕ, Measurable (S.indD dbar k)
  | 0 => measurable_const
  | k + 1 => by
      unfold indD
      by_cases hk : k < n
      · simp only [hk, ↓reduceDIte]
        exact (S.measurable_indD dbar k).mul
          ((S.dVar ⟨k, hk⟩).measurable_indicator (dbar ⟨k, hk⟩)
            (measurableSet_singleton _))
      · simp only [hk, ↓reduceDIte]
        exact S.measurable_indD dbar k

/-! ### History bundles -/
/-- [The observed history available at a decision point](goal) in
[a longitudinal-path system](hyp:S) [uses the selected stage cutoff](hyp:k) to
[contain only the initial state at cutoff zero](step:1) and [recursively add each prior
treatment and the next state at a positive cutoff](step:2).

The history bundle at stage cutoff `k` stores the factual tuple newest first:
`(S k, D (k-1), S (k-1), ..., D 0, S 0)`. At `k = 0` it is the
singleton `(S 0,)`. The cutoff must satisfy `k < n` because the tuple includes `S k`. -/
noncomputable def historyBundle (S : POLongitudinalPathSystem P n δ γ) :
    (k : ℕ) → k < n → POCFBundle P
  | 0, h =>
      POCFBundle.cons (RegimedVar.ofFactual (S.S ⟨0, h⟩)) (POCFBundle.nil P)
  | k + 1, h =>
      POCFBundle.cons (RegimedVar.ofFactual (S.S ⟨k + 1, h⟩)) <|
      POCFBundle.cons
        (RegimedVar.ofFactual (S.dVar ⟨k, Nat.lt_of_succ_lt h⟩)) <|
      S.historyBundle k (Nat.lt_of_succ_lt h)

/-! ### Counterfactual bundle wrapper (for exchangeability) -/

/-- [The counterfactual outcome bundle](goal) for [a longitudinal-path system](hyp:S)
[uses a prescribed treatment path](hyp:dbar) to [package its terminal potential outcome as
the single target of sequential exchangeability](step:1). -/
noncomputable def cfYBundle (S : POLongitudinalPathSystem P n δ γ) (dbar : Fin n → δ) :
    POCFBundle P :=
  POCFBundle.cons (⟨S.yVar, S.regime dbar⟩ : RegimedVar P ℝ) (POCFBundle.nil P)

/-! ### Sequential backdoor assumptions -/

/-- Sequential backdoor identification for [a longitudinal-path system](hyp:S) requires
[potential-outcome consistency for the ambient
system](hyp:consistency); [per-sequence sequential
exchangeability, i.e. at each stage
the treatment is conditionally independent of the counterfactual terminal outcome
under the treatment sequence given the history observed up to that
stage](hyp:exch); [pointwise positivity of the stagewise propensity given the same
history, almost surely](hyp:overlap); and [integrability of the counterfactual
terminal outcome under every treatment sequence](hyp:integrable_Y) together with
[integrability of the factual terminal outcome](hyp:integrable_factualY).

Per-sequence exchangeability: for each `dbar : Fin n → δ` and each stage
`k : Fin n`, `D k ⟂ Y(dbar) | σ(historyBundle k)`.  Conditions on the full
σ-algebra of the history bundle (standard simplification of the
`{D̄_{k-1}=d̄_{k-1}}` qualifier).

Overlap is pointwise positivity:
`μ[1_{D k = dbar k} | σ(historyBundle k)] > 0` a.s. -/
structure Assumptions (S : POLongitudinalPathSystem P n δ γ)
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] : Prop where
  consistency : P.Consistency
  /-- Per-sequence sequential exchangeability. -/
  exch : ∀ (dbar : Fin n → δ) (k : Fin n),
    P.CondIndepCFBundle
      (RegimedVar.ofFactual (S.dVar k))
      (S.cfYBundle dbar)
      (S.historyBundle k.val k.isLt) P.μ
  /-- Pointwise (a.s.) positivity of stagewise propensities.

  Note the reach of this field: positivity is demanded for EVERY treatment sequence, so the
  conditional law of each stage's treatment must have an atom at every point of `δ`. A probability
  measure has at most countably many atoms, so at a positive horizon this is satisfiable only for
  a countable alphabet — a continuous treatment needs a density-based positivity condition
  (generalized propensity score) rather than this pointwise one. The restriction is stated here
  rather than imposed as a `Countable δ` field, which would add a proof obligation to every
  downstream result without changing what is provable. -/
  overlap : ∀ (dbar : Fin n → δ) (k : Fin n),
    ∀ᵐ ω ∂P.μ,
      0 < (S.historyBundle k.val k.isLt).condExpGiven
        ((S.dVar k).indicator (dbar k)) P.μ ω
  integrable_Y : ∀ dbar : Fin n → δ, Integrable (S.Y_of dbar) P.μ
  integrable_factualY : Integrable S.factualY P.μ

/-! ### Observable (adjusted) functionals -/
/-- [The backward adjusted-regression process](goal) for
[a longitudinal-path system](hyp:S) and [a prescribed treatment path](hyp:dbar) uses
[the final-history
conditional-expectation ratio when the horizon is positive, and zero otherwise](step:1), then
[the analogous recursively defined earlier-history ratio when the indicated stage exists, and
the preceding value otherwise](step:2).

Backward-recursive definition of the adjusted treatment-path functional.

We index by `j : ℕ` = "number of stages still to pull out", going from the
innermost stage (`j = 0`, uses `historyBundle (n-1)`) out to the outermost
(`j = n - 1`, uses `historyBundle 0`).

* `j = 0` (stage `n`):
      μ[Y · 1_{D_{<n}=dbar} | σ(historyBundle (n-1))]
      / μ[1_{D_{<n}=dbar} | σ(historyBundle (n-1))].
* `j = k + 1` (stage `n - k - 1`):
      μ[innerReg_k · 1_{D (n-k-1) = dbar (n-k-1)} | σ(historyBundle (n-k-2))]
      / μ[1_{D (n-k-1) = dbar (n-k-1)} | σ(historyBundle (n-k-2))].

For `n ≥ 2` the full recursion ends at `j = n - 1`, which conditions on
`historyBundle 0`; the final `adjustedTreatmentPathMean` integrates that over `P.μ`.

For `n = 0`, `innerReg` is the constant `0`. -/
noncomputable def innerReg (S : POLongitudinalPathSystem P n δ γ) (dbar : Fin n → δ) :
    ℕ → P.Ω → ℝ
  | 0 => fun ω =>
      if h : 0 < n then
        (S.historyBundle (n - 1) (Nat.sub_lt h Nat.one_pos)).condExpGiven
          (fun ω' => S.factualY ω' * S.indD dbar n ω') P.μ ω
        /
        (S.historyBundle (n - 1) (Nat.sub_lt h Nat.one_pos)).condExpGiven
          (S.indD dbar n) P.μ ω
      else 0
  | j + 1 => fun ω =>
      if h : j + 1 < n then
        let histIdx : ℕ := n - j - 2
        have hhist : histIdx < n := by
          change n - j - 2 < n; omega
        let stage : Fin n := ⟨histIdx, hhist⟩
        (S.historyBundle histIdx hhist).condExpGiven
          (fun ω' => S.innerReg dbar j ω' * (S.dVar stage).indicator (dbar stage) ω')
          P.μ ω
        /
        (S.historyBundle histIdx hhist).condExpGiven
          ((S.dVar stage).indicator (dbar stage)) P.μ ω
      else S.innerReg dbar j ω

/-- [The longitudinal-path mean outcome](goal) for [a longitudinal-path system](hyp:S)
[uses a prescribed treatment path](hyp:dbar) and [averages the terminal potential outcome
under that path over the target population](step:1). -/
noncomputable def treatmentPathMean (S : POLongitudinalPathSystem P n δ γ) (dbar : Fin n → δ) :
    ℝ := ∫ ω, S.Y_of dbar ω ∂P.μ

/-- [The observable adjusted longitudinal-path functional](goal) for
[a longitudinal-path system](hyp:S) and [a prescribed treatment path](hyp:dbar)
[integrates the outermost backward regression when a decision stage exists and returns zero
at a zero horizon](step:1).

Integrates the outermost
ratio `innerReg dbar (n - 1)` — which conditions on `historyBundle 0 = (S 0,)` —
against `P.μ`.  For `n = 0` this is `0`. -/
noncomputable def adjustedTreatmentPathMean
    (S : POLongitudinalPathSystem P n δ γ) (dbar : Fin n → δ) :
    ℝ :=
  if 0 < n then ∫ ω, S.innerReg dbar (n - 1) ω ∂P.μ else 0

end POLongitudinalPathSystem

end PO
end Causalean

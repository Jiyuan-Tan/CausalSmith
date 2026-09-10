/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased.DesignCore
import Causalean.Stat.Minimax.MinimaxValue
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Finite bounded squared-loss decision problems

This module defines the procedure, risk, Euclidean parameterization, and prior
simplex used by the finite squared-loss minimax theorem.  Procedures use the
existing `FiniteDesign` type and dependent bounded decision rules.
-/

open scoped BigOperators
open Set

namespace Causalean.Stat.Minimax.FiniteSquaredLoss

open Causalean.Experimentation.DesignBased

variable {Theta R : Type*} [Fintype Theta] [Fintype R]
variable {X : R → Type*} [∀ r, Fintype (X r)]

/-- A procedure consists of a finite randomized design and, for every selected
design and dependent observation, an action in the prescribed closed interval. -/
structure Procedure (X : R → Type*) [∀ r, Fintype (X r)] (l u : ℝ) where
  /-- The randomized finite design. -/
  design : FiniteDesign R
  /-- The bounded decision rule after observing the selected design's outcome. -/
  decision : ∀ r, X r → Set.Icc l u

/-- Given [state-specific observation likelihoods](hyp:P), [a real target for each state](hyp:tau),
[a bounded randomized procedure](hyp:q), and [a state](hyp:theta), [the statewise squared-loss risk](goal)
is the procedure-design-weighted sum of likelihood-weighted squared differences between the selected
action and that state's target. -/
def risk (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ)
    (q : Procedure X l u) (theta : Theta) : ℝ :=
  ∑ r, q.design.p r * ∑ x, P theta r x * ((q.decision r x : ℝ) - tau theta) ^ 2

/-- When the [likelihood coefficients](hyp:P) [are nonnegative](hyp:hP), every bounded finite
procedure has [nonnegative squared-loss risk in each state](goal). -/
theorem risk_nonneg (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ)
    (hP : ∀ theta r x, 0 ≤ P theta r x) (q : Procedure X l u) (theta : Theta) :
    0 ≤ risk P tau q theta := by
  -- Expand both finite sums and use nonnegativity of the design mass, `P`, and squares.
  unfold risk
  apply Finset.sum_nonneg
  intro r _
  apply mul_nonneg (q.design.p_nonneg r)
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (hP theta r x) (sq_nonneg _)

/-- A nonempty design space and [a nonempty action interval](hyp:hlu) have [a bounded
finite randomized procedure](goal), even when some observation spaces are empty. -/
theorem procedure_nonempty [Nonempty R] {l u : ℝ} (hlu : l ≤ u) :
    Nonempty (Procedure X l u) := by
  -- Put unit mass at one chosen design point and use the constant action `l`.
  classical
  let r₀ : R := Classical.choice inferInstance
  refine ⟨{
    design := {
      p := Pi.single r₀ 1
      p_nonneg := fun r ↦ by simp only [Pi.single_apply]; split_ifs <;> positivity
      p_sum := by simp }
    decision := fun _ _ ↦ ⟨l, le_rfl, hlu⟩ }⟩

/-- Given [a set of design indices](hyp:R) and [an observation space for each design
index](hyp:X), [the ambient coordinate space](goal) consists of one real design-weight vector and
one real action coordinate for every design-index and observation pair. -/
abbrev Ambient (R : Type*) (X : R → Type*) :=
  (R → ℝ) × (∀ r, X r → ℝ)

/-- Given [a family of finite observation spaces indexed by design](hyp:X), [a lower action bound](hyp:l),
and [an upper action bound](hyp:u), [the feasible procedure-coordinate set](goal) contains exactly
those ambient coordinates whose design weights form a probability distribution and whose action
coordinates all lie in the closed interval from the lower to the upper bound. -/
def procedureSet (X : R → Type*) (l u : ℝ) : Set (Ambient R X) :=
  {z | z.1 ∈ stdSimplex ℝ R ∧ ∀ r x, z.2 r x ∈ Set.Icc l u}

/-- Given [a bounded finite randomized procedure](hyp:q), [its ambient Euclidean coordinates](goal)
are its design probabilities together with its action at every design-index and observation pair. -/
def Procedure.toAmbient (q : Procedure X l u) : Ambient R X :=
  ⟨q.design.p, fun r x ↦ q.decision r x⟩

/-- The Euclidean coordinates of every bounded finite procedure [belong to the feasible
coordinate set](goal). -/
theorem Procedure.toAmbient_mem (q : Procedure X l u) :
    q.toAmbient ∈ procedureSet X l u := by
  -- The two obligations are exactly the proof fields of `FiniteDesign` and `Set.Icc`.
  exact ⟨⟨q.design.p_nonneg, q.design.p_sum⟩, fun r x ↦ (q.decision r x).property⟩

/-- Given [an ambient coordinate point](hyp:z) that [belongs to the feasible procedure-coordinate
set](hyp:hz), [the corresponding bounded finite procedure](goal) uses its design-weight coordinates
as design probabilities and its action coordinates as bounded decisions. -/
noncomputable def Procedure.ofAmbient {z : Ambient R X}
    (hz : z ∈ procedureSet X l u) : Procedure X l u where
  design :=
    { p := z.1
      p_nonneg := hz.1.1
      p_sum := hz.1.2 }
  decision := fun r x ↦ ⟨z.2 r x, hz.2 r x⟩

/-- Turning [a feasible coordinate point](hyp:hz) into a procedure and back [recovers that
coordinate point](goal). -/
@[simp] theorem Procedure.toAmbient_ofAmbient {z : Ambient R X}
    (hz : z ∈ procedureSet X l u) :
    (Procedure.ofAmbient hz).toAmbient = z := by
  rfl

/-- Given [state-specific observation likelihoods](hyp:P), [a real target for each state](hyp:tau),
[an ambient coordinate point](hyp:z), and [a state](hyp:theta), [the raw squared-loss risk](goal) is
the design-coordinate-weighted sum of likelihood-weighted squared differences between action coordinates
and that state's target. -/
def rawRisk (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ)
    (z : Ambient R X) (theta : Theta) : ℝ :=
  ∑ r, z.1 r * ∑ x, P theta r x * (z.2 r x - tau theta) ^ 2

/-- For given [likelihood coefficients](hyp:P), the ambient polynomial representation of a
procedure's risk [equals its public squared-loss risk](goal). -/
@[simp] theorem rawRisk_toAmbient
    (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ)
    (q : Procedure X l u) (theta : Theta) :
    rawRisk P tau q.toAmbient theta = risk P tau q theta := by
  rfl

/-- A nonempty design space and [a nonempty action interval](hyp:hlu) make [the feasible
Euclidean procedure set nonempty](goal). -/
theorem procedureSet_nonempty [Nonempty R] {l u : ℝ} (hlu : l ≤ u) :
    (procedureSet X l u).Nonempty := by
  -- Map the witness from `procedure_nonempty` through `Procedure.toAmbient`.
  let q := Classical.choice (procedure_nonempty (X := X) hlu)
  exact ⟨q.toAmbient, q.toAmbient_mem⟩

/-- [An action interval with ordered endpoints](hyp:hlu) makes [the feasible Euclidean
procedure set convex](goal). -/
theorem convex_procedureSet {l u : ℝ} (hlu : l ≤ u) :
    Convex ℝ (procedureSet X l u) := by
  -- Intersect the convex standard simplex with coordinatewise convex intervals.
  intro z hz w hw a b ha hb hab
  exact ⟨(convex_stdSimplex ℝ R) hz.1 hw.1 ha hb hab,
    fun r x ↦ (convex_Icc l u) (hz.2 r x) (hw.2 r x) ha hb hab⟩

/-- The feasible Euclidean procedure set [is compact](goal): it is the product of a finite
probability simplex and finitely many closed action intervals. -/
theorem isCompact_procedureSet (l u : ℝ) :
    IsCompact (procedureSet X l u) := by
  -- View the set as a closed subset of the product of the compact simplex and finite Icc cube.
  have hcube : IsCompact {f : ∀ r, X r → ℝ | ∀ r x, f r x ∈ Set.Icc l u} := by
    rw [show {f : ∀ r, X r → ℝ | ∀ r x, f r x ∈ Set.Icc l u} =
        Set.univ.pi (fun r ↦ Set.univ.pi (fun _ : X r ↦ Set.Icc l u)) by
      ext f
      constructor
      · intro hf
        rw [Set.mem_pi]
        intro r _
        rw [Set.mem_pi]
        intro x _
        exact hf r x
      · intro hf r x
        exact hf r (Set.mem_univ r) x (Set.mem_univ x)]
    exact isCompact_univ_pi (fun _ : R ↦
      isCompact_univ_pi (fun _ ↦ (isCompact_Icc : IsCompact (Set.Icc l u))))
  rw [show procedureSet X l u =
      stdSimplex ℝ R ×ˢ {f : ∀ r, X r → ℝ | ∀ r x, f r x ∈ Set.Icc l u} by
    ext z
    simp [procedureSet]]
  exact (isCompact_stdSimplex ℝ R).prod hcube

/-- For fixed [likelihood coefficients](hyp:P) and targets, the ambient squared-loss risk in any
state [varies continuously with the procedure coordinates](goal). -/
theorem continuous_rawRisk
    (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ) (theta : Theta) :
    Continuous (fun z : Ambient R X ↦ rawRisk P tau z theta) := by
  -- `fun_prop`/finite-sum continuity reduces this polynomial to coordinate projections.
  unfold rawRisk
  fun_prop

/-- Given [state-specific observation likelihoods](hyp:P), [a real target for each state](hyp:tau),
and [an ambient coordinate point](hyp:z), [the risk vector](goal) assigns to every state its raw
squared-loss risk at that coordinate point. -/
def riskVector (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ)
    (z : Ambient R X) : Theta → ℝ :=
  fun theta ↦ rawRisk P tau z theta

/-- For fixed [likelihood coefficients](hyp:P), the vector collecting each state's ambient
squared-loss risk [varies continuously with the procedure coordinates](goal). -/
theorem continuous_riskVector
    (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ) :
    Continuous (riskVector P tau : Ambient R X → Theta → ℝ) := by
  -- Use `continuous_pi` and `continuous_rawRisk` in each state coordinate.
  apply continuous_pi
  exact fun theta ↦ continuous_rawRisk P tau theta

/-- Under given [likelihood coefficients](hyp:P), the set of risk vectors attainable by feasible
finite procedures [is compact](goal). -/
theorem isCompact_riskVector_image
    (P : Theta → ∀ r, X r → ℝ) (tau : Theta → ℝ) (l u : ℝ) :
    IsCompact (riskVector P tau '' procedureSet X l u) := by
  -- Continuous image of `isCompact_procedureSet`.
  exact (isCompact_procedureSet (X := X) l u).image (continuous_riskVector P tau)

/-- Every finite randomized design has [a mass function in the standard probability
simplex](goal). -/
theorem finiteDesign_mem_stdSimplex (nu : FiniteDesign Theta) :
    nu.p ∈ stdSimplex ℝ Theta := by
  exact ⟨nu.p_nonneg, nu.p_sum⟩

/-- Given [a vector of weights over the finite state space](hyp:w) that [belongs to the standard
probability simplex](hyp:hw), [the corresponding finite design](goal) is the probability design whose
mass function is that vector. -/
def finiteDesignOfSimplex {w : Theta → ℝ} (hw : w ∈ stdSimplex ℝ Theta) :
    FiniteDesign Theta where
  p := w
  p_nonneg := hw.1
  p_sum := hw.2

/-- Given [a real-valued risk vector over states](hyp:z) and [a vector of prior weights](hyp:nu),
[the finite Bayes payoff](goal) is the sum over states of each prior weight times its risk-vector value. -/
def bayesPayoff (z nu : Theta → ℝ) : ℝ :=
  ∑ theta, nu theta * z theta

/-- Pairing a risk vector with a finite prior [equals that prior's existing finite-design
expectation](goal). -/
@[simp] theorem bayesPayoff_eq_E (z : Theta → ℝ) (nu : FiniteDesign Theta) :
    bayesPayoff z nu.p = nu.E z := by
  rfl

/-- The finite Bayes payoff [varies continuously with both the risk vector and the prior
weights](goal). -/
theorem continuous_bayesPayoff :
    Continuous (fun p : (Theta → ℝ) × (Theta → ℝ) ↦ bayesPayoff p.1 p.2) := by
  -- Finite sum of products of continuous coordinate projections.
  unfold bayesPayoff
  fun_prop

end Causalean.Stat.Minimax.FiniteSquaredLoss

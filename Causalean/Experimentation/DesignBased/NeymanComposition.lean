/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.FinitePopulationVariance
public import Causalean.Experimentation.TwoStageInterference.CompleteRandomization

/-!
# Composition lemmas for Neyman inference under complete randomization

This file connects the library's three representations of within-arm variation: ordinary sample
variance on a fixed-size subset, Boolean-assignment arm variances, and the finite-population
variance. Complementing the treated subset transports complete randomization to the control
design, so the existing sample-variance consistency theorem applies to either arm.
-/

@[expose] public section

open scoped BigOperators Topology
open Filter Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

open FinitePopulationMoments
open TwoStageInterference

private lemma FiniteDesign.ext_p {Ω : Type*} [Fintype Ω] {D E : FiniteDesign Ω}
    (h : D.p = E.p) : D = E := by
  cases D with
  | mk p hp hs =>
    cases E with
    | mk q hq hqs =>
      simp only [FiniteDesign.mk.injEq]
      exact h

/-- For [a finite population](hyp:U), [a feasible treated count](hyp:K,hK), the
[complement equivalence between size-`K` treated subsets and size-`N-K` control subsets](goal)
maps each treated set to precisely the units outside it. -/
def completeRandomizationComplementEquiv {U : Type*} [Fintype U] [DecidableEq U]
    (K : ℕ) (hK : K ≤ Fintype.card U) :
    {S : Finset U // S.card = K} ≃
      {S : Finset U // S.card = Fintype.card U - K} where
  toFun S := ⟨S.valᶜ, by simp [Finset.card_compl, S.property]⟩
  invFun S := ⟨S.valᶜ, by simp [Finset.card_compl, S.property, Nat.sub_sub_self hK]⟩
  left_inv S := by
    apply Subtype.ext
    exact compl_compl S.val
  right_inv S := by
    apply Subtype.ext
    exact compl_compl S.val

/-- For [a finite population](hyp:U) and [a feasible treated count](hyp:K,hK), [pushing complete
randomization forward through set complementation gives complete randomization of the
`N-K` controls](goal). -/
theorem completeRandomization_map_complement {U : Type*} [Fintype U] [DecidableEq U]
    (K : ℕ) (hK : K ≤ Fintype.card U) :
    (completeRandomization K hK).map (completeRandomizationComplementEquiv K hK) =
      completeRandomization (Fintype.card U - K) (Nat.sub_le _ _) := by
  apply FiniteDesign.ext_p
  funext T
  rw [FiniteDesign.map_p]
  simp only [completeRandomization]
  rw [show Fintype.card {S : Finset U // S.card = K} =
      Fintype.card {S : Finset U // S.card = Fintype.card U - K} by
        exact Fintype.card_congr (completeRandomizationComplementEquiv K hK)]
  simp_rw [← Equiv.eq_symm_apply]
  rw [Fintype.sum_ite_eq']

/-- For [a population of `n` indexed units](hyp:n) and [a feasible treated count](hyp:K,hK), the
[complement equivalence specialized to `Fin n`](goal) maps treated subsets to control subsets whose
cardinality is written definitionally as `n-K`. -/
def finCompleteRandomizationComplementEquiv {n : ℕ} (K : ℕ) (hK : K ≤ n) :
    {S : Finset (Fin n) // S.card = K} ≃ {S : Finset (Fin n) // S.card = n - K} where
  toFun S := ⟨S.valᶜ, by simp [Finset.card_compl, S.property]⟩
  invFun S := ⟨S.valᶜ, by simp [Finset.card_compl, S.property, Nat.sub_sub_self hK]⟩
  left_inv S := by
    apply Subtype.ext
    exact compl_compl S.val
  right_inv S := by
    apply Subtype.ext
    exact compl_compl S.val

/-- For [a population of `n` units](hyp:n) with [outcomes](hyp:a), [Neyman's treated-arm
finite-population variance equals the generic finite-population variance](goal). -/
lemma S1_eq_popVar {n : ℕ} (a : Fin n → ℝ) : S1 a = popVar a := by
  simp [S1, popVar, popMeanV, popMean]

/-- For [a population of `n` units](hyp:n), [a treated count](hyp:K), [treated outcomes](hyp:a),
and [a realized treated subset](hyp:S), [the Boolean treated-arm variance equals the ordinary
sample variance on that subset](goal). -/
lemma ShatTreated_crdToBoolOn_eq_sampleVariance {n : ℕ} (K : ℕ) (a : Fin n → ℝ)
    (S : {S : Finset (Fin n) // S.card = K}) :
    ShatTreated K a (crdToBoolOn K S) = sampleVariance K a S := by
  classical
  have hT : ∀ i, T i (crdToBoolOn K S) = if i ∈ S.val then 1 else 0 := by
    intro i
    change (if decide (i ∈ S.val) = true then (1 : ℝ) else 0) =
      if i ∈ S.val then 1 else 0
    by_cases hi : i ∈ S.val <;> simp [hi]
  have hmean : obsMeanTreated K a (crdToBoolOn K S) = sampleMean K a S := by
    unfold obsMeanTreated sampleMean
    apply congrArg (fun x : ℝ => x / (K : ℝ))
    apply Finset.sum_congr rfl
    intro i _
    rw [hT]
    by_cases hi : i ∈ S.val <;> simp [hi]
  unfold ShatTreated sampleVariance
  rw [hmean]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hT]
  by_cases hi : i ∈ S.val <;> simp [hi]

/-- For [a population of `n` units](hyp:n), [a feasible treated count](hyp:K,hK), [control
outcomes](hyp:b), and [a realized treated subset](hyp:S), [the Boolean control-arm variance equals
the ordinary sample variance on the complementary control subset](goal). -/
lemma ShatControl_crdToBoolOn_eq_sampleVariance {n : ℕ} (K : ℕ) (hK : K ≤ n)
    (b : Fin n → ℝ) (S : {S : Finset (Fin n) // S.card = K}) :
    ShatControl K b (crdToBoolOn K S) =
      sampleVariance (n - K) b (finCompleteRandomizationComplementEquiv K hK S) := by
  classical
  let C := finCompleteRandomizationComplementEquiv K hK S
  change ShatControl K b (crdToBoolOn K S) = sampleVariance (n - K) b C
  have hT : ∀ i, 1 - T i (crdToBoolOn K S) = if i ∈ C.val then 1 else 0 := by
    intro i
    change 1 - (if decide (i ∈ S.val) = true then (1 : ℝ) else 0) =
      if i ∈ S.valᶜ then 1 else 0
    by_cases hi : i ∈ S.val <;> simp [hi]
  have hmean : obsMeanControl K b (crdToBoolOn K S) = sampleMean (n - K) b C := by
    unfold obsMeanControl sampleMean
    rw [Nat.cast_sub hK]
    apply congrArg (fun x : ℝ => x / ((n : ℝ) - (K : ℝ)))
    apply Finset.sum_congr rfl
    intro i _
    rw [hT]
    by_cases hi : i ∈ C.val <;> simp [hi]
  unfold ShatControl sampleVariance
  rw [hmean, Nat.cast_sub hK]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hT]
  by_cases hi : i ∈ C.val <;> simp [hi]

/-- For [a population of `n` units](hyp:n), [a feasible treated count](hyp:K,hK), [treated and
control outcomes](hyp:a,b), and [a realized treated subset](hyp:S), [the feasible Neyman variance
estimator is the treated sample variance divided by `K` plus the complementary control sample
variance divided by `n-K`](goal). -/
lemma DifferenceInMeans.varianceEstimator_eq_sampleVariances {n : ℕ}
    (K : ℕ) (hK : K ≤ n) (a b : Fin n → ℝ)
    (S : {S : Finset (Fin n) // S.card = K}) :
    DifferenceInMeans.varianceEstimator K a b S =
      sampleVariance K a S / (K : ℝ) +
        sampleVariance (n - K) b (finCompleteRandomizationComplementEquiv K hK S) /
          ((n - K : ℕ) : ℝ) := by
  change varHat K a b (crdToBoolOn K S) = _
  unfold varHat
  rw [ShatTreated_crdToBoolOn_eq_sampleVariance,
    ShatControl_crdToBoolOn_eq_sampleVariance K hK, Nat.cast_sub hK]

/-- Along [finite populations](hyp:U) with [outcome vectors](hyp:y) and [feasible treated
counts](hyp:K,hK), suppose [every
control arm contains at least two units](hyp:hC2), [the control-arm sizes diverge](hyp:hCTop),
[the population variances converge](hyp:hvar), and [the largest squared centered outcome divided
by the control-arm size vanishes](hyp:hmax). Then [the ordinary sample variance on the complementary
control set converges in randomization probability to the finite-population variance](goal). -/
theorem control_sampleVariance_tendstoInProb
    {U : ℕ → Type*} [∀ k, Fintype (U k)] [∀ k, DecidableEq (U k)]
    [∀ k, Nonempty (U k)]
    (K : ℕ → ℕ) (hK : ∀ k, K k ≤ Fintype.card (U k))
    (hC2 : ∀ k, 2 ≤ Fintype.card (U k) - K k)
    (y : ∀ k, U k → ℝ) (v : ℝ)
    (hCTop : Tendsto (fun k => Fintype.card (U k) - K k) atTop atTop)
    (hvar : Tendsto (fun k => popVar (y k)) atTop (𝓝 v))
    (hmax : Tendsto (fun k =>
      popMaxSqDev (y k) / (Fintype.card (U k) - K k : ℕ)) atTop (𝓝 0)) :
    FiniteDesign.TendstoInProb
      (fun k => completeRandomization (K k) (hK k))
      (fun k S => sampleVariance (Fintype.card (U k) - K k) (y k)
        (completeRandomizationComplementEquiv (K k) (hK k) S))
      (fun k => popVar (y k)) := by
  have h := FinitePopulationMoments.SampleVarianceConsistency.sampleVariance_tendstoInProb
    (fun k => Fintype.card (U k) - K k) hC2 (fun k => Nat.sub_le _ _) y v
    hCTop hvar hmax
  intro ε hε
  have ht := h ε hε
  convert ht using 1
  funext k
  let A : {S : Finset (U k) // S.card = Fintype.card (U k) - K k} → Prop :=
    fun S => ε ≤
      |sampleVariance (Fintype.card (U k) - K k) (y k) S - popVar (y k)|
  change (completeRandomization (K k) (hK k)).Pr
      (fun S => A (completeRandomizationComplementEquiv (K k) (hK k) S)) =
    (completeRandomization (Fintype.card (U k) - K k) (Nat.sub_le _ _)).Pr A
  calc
    _ = ((completeRandomization (K k) (hK k)).map
        (completeRandomizationComplementEquiv (K k) (hK k))).Pr A :=
      (FiniteDesign.Pr_map _ _ _).symm
    _ = _ := by rw [completeRandomization_map_complement]

end DesignBased
end Experimentation
end Causalean

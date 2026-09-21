/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.Estimators.DifferenceInMeans
public import Causalean.Experimentation.TwoStageInterference.VarianceConservative

/-!
# Complete-randomization variance for the design-based difference in means

This adapter transports the two-stage interference variance identities to the paper-independent
design-based difference-in-means estimator. Keeping this transport above both source modules avoids
an import from the design-based estimator layer into the interference-specific layer.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased
namespace DifferenceInMeans

open TwoStageInterference

private lemma diffInMeans_eq_neg_tauHat {n K : ℕ} (Y1 Y0 : Fin n → ℝ)
    (hK : K ≤ n) (S : {S : Finset (Fin n) // S.card = K}) :
    diffInMeans K Y1 Y0 S = -tauHat K Y1 Y0 (crdToBoolOn K S) := by
  unfold diffInMeans treatedMean controlMean tauHat DesignBased.T crdToBoolOn FiniteDesign.ind
  have htreat : (∑ i, if i ∈ S.val then Y1 i else 0) =
      ∑ i, Y1 i * (if decide (i ∈ S.val) = true then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S.val <;> simp [hi]
  have hcontrol : (∑ i, if i ∈ S.val then 0 else Y0 i) =
      ∑ i, Y0 i * (1 - if decide (i ∈ S.val) = true then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S.val <;> simp [hi]
  rw [Fintype.card_fin, Nat.cast_sub hK, htreat, hcontrol]
  ring

private lemma Var_map_crd {n K : ℕ} (hK : K ≤ n) (X : (Fin n → Bool) → ℝ) :
    (crd K hK).Var X =
      (completeRandomization (V := Fin n) K (by simpa using hK)).Var
        (fun S => X (crdToBoolOn K S)) := by
  unfold crd crdOn FiniteDesign.Var
  rw [FiniteDesign.E_map, FiniteDesign.E_map]

/-- **Neyman's exact variance formula (Imbens--Rubin 2015, Theorem 6.2).** For [a population
size and treated count](hyp:n,K), with [a positive treated count](hyp:hK) and [at least one
remaining control](hyp:hKn), and [treated and control potential outcomes](hyp:Y1,Y0), [the
complete-randomization variance of the treated-minus-control difference in means equals
`S₁²/K + S₀²/(n-K) - Sτ²/n`](goal). -/
theorem Var_diffInMeans_eq_neyman {n K : ℕ} (hK : 0 < K) (hKn : K < n)
    (Y1 Y0 : Fin n → ℝ) :
    (completeRandomization (V := Fin n) K (by simpa using hKn.le)).Var
        (diffInMeans K Y1 Y0) =
      S1 Y1 / K + S0 Y0 / (n - K) - Stau Y1 Y0 / n := by
  have hfun : diffInMeans K Y1 Y0 =
      fun S => -tauHat K Y1 Y0 (crdToBoolOn K S) := by
    funext S
    exact diffInMeans_eq_neg_tauHat Y1 Y0 hKn.le S
  rw [hfun]
  have hneg : (completeRandomization (V := Fin n) K (by simpa using hKn.le)).Var
      (fun S => -tauHat K Y1 Y0 (crdToBoolOn K S)) =
      (completeRandomization (V := Fin n) K (by simpa using hKn.le)).Var
        (fun S => tauHat K Y1 Y0 (crdToBoolOn K S)) := by
    have heq : (fun S => -tauHat K Y1 Y0 (crdToBoolOn K S)) =
        fun S => (-1 : ℝ) * tauHat K Y1 Y0 (crdToBoolOn K S) := by
      funext S
      ring
    rw [heq, FiniteDesign.Var_const_mul]
    ring
  rw [hneg, ← Var_map_crd hKn.le]
  exact Var_tauHat_CRD K Y1 Y0 hK hKn

/-- **Conservativeness of Neyman's feasible variance estimator.** For [a population size and
treated count](hyp:n,K), if [at least two units are treated](hyp:hK2), [at least two remain in
control](hyp:hKn2), and [treated and control potential outcomes are fixed](hyp:Y1,Y0), then [the
expectation of the separate-arm sample-variance estimator is at least the exact randomization
variance of difference in means](goal). -/
theorem E_diffInMeansVarHat_conservative {n K : ℕ} (hK2 : 2 ≤ K) (hKn2 : K + 2 ≤ n)
    (Y1 Y0 : Fin n → ℝ) :
    (completeRandomization (V := Fin n) K (by
      simpa using le_trans (Nat.le_add_right K 2) hKn2)).Var
        (diffInMeans K Y1 Y0) ≤
      (completeRandomization (V := Fin n) K (by
        simpa using le_trans (Nat.le_add_right K 2) hKn2)).E
        (varianceEstimator K Y1 Y0) := by
  let hle : K ≤ n := le_trans (Nat.le_add_right K 2) hKn2
  have hfun : diffInMeans K Y1 Y0 =
      fun S => -tauHat K Y1 Y0 (crdToBoolOn K S) := by
    funext S
    exact diffInMeans_eq_neg_tauHat Y1 Y0 hle S
  rw [hfun]
  have hleFin : K ≤ Fintype.card (Fin n) := by simpa using hle
  have hneg : (completeRandomization (V := Fin n) K hleFin).Var
      (fun S => -tauHat K Y1 Y0 (crdToBoolOn K S)) =
      (completeRandomization (V := Fin n) K hleFin).Var
        (fun S => tauHat K Y1 Y0 (crdToBoolOn K S)) := by
    have heq : (fun S => -tauHat K Y1 Y0 (crdToBoolOn K S)) =
        fun S => (-1 : ℝ) * tauHat K Y1 Y0 (crdToBoolOn K S) := by
      funext S
      ring
    rw [heq, FiniteDesign.Var_const_mul]
    ring
  rw [hneg, ← Var_map_crd hle]
  change (crd K hle).Var (tauHat K Y1 Y0) ≤
    (completeRandomization (V := Fin n) K hleFin).E
      (fun S => varHat K Y1 Y0 (crdToBoolOn K S))
  rw [← FiniteDesign.E_map]
  exact E_varHat_conservative_CRD K Y1 Y0 hK2 hKn2

end DifferenceInMeans
end DesignBased
end Experimentation
end Causalean

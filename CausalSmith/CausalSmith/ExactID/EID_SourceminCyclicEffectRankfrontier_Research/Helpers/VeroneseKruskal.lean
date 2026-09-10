import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Helpers.CitedGates
import Causalean.Stat.Nonparametric.MomentProblems.FiniteMomentNearGaussianPerturbation.Main
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Fintype.Fin

/-!
# Veronese rank and near-Gaussian moment matching
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open MeasureTheory Set
open scoped BigOperators NNReal

noncomputable def veronesePower {p s : ℕ} (z : Vec p) : (Fin s → Fin p) → ℝ :=
  fun I => ∏ k, z (I k)

private lemma dual_apply_eq_sum {p : ℕ} (f : Module.Dual ℝ (Vec p)) (z : Vec p) :
    f z = ∑ q : Fin p, f (Pi.single q 1) * z q := by
  classical
  conv_lhs => rw [show z = ∑ q : Fin p, z q • Pi.single q 1 by
    ext i
    simp [Pi.single_apply]]
  rw [map_sum]
  simp [mul_comm]

private lemma tensor_contraction {p s : ℕ} (f : Fin s → Module.Dual ℝ (Vec p))
    (z : Vec p) :
    (∑ I : Fin s → Fin p, (∏ k, f k (Pi.single (I k) 1)) *
      veronesePower (s := s) z I) = ∏ k, f k z := by
  classical
  calc
    _ = ∑ I : Fin s → Fin p, ∏ k, (f k (Pi.single (I k) 1) * z (I k)) := by
      apply Fintype.sum_congr
      intro I
      simp only [veronesePower]
      rw [Finset.prod_mul_distrib]
    _ = ∏ k : Fin s, ∑ q : Fin p, f k (Pi.single q 1) * z q := by
      rw [Fintype.prod_sum]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro k _
      exact (dual_apply_eq_sum (f k) z).symm

private lemma projective_probe {p R : ℕ} (z : Fin R → Vec p)
    (hnz : ∀ j, z j ≠ 0)
    (hdir : ∀ j k, j ≠ k → ∀ t : ℝ, z j ≠ t • z k) :
    ∃ u v : Module.Dual ℝ (Vec p),
      (∀ j, u (z j) ≠ 0) ∧ Function.Injective (fun j => v (z j) / u (z j)) := by
  obtain ⟨u, hu⟩ := Module.exists_dual_forall_apply_ne_zero
    (K := ℝ) (M := Vec p) z hnz
  let w : {q : Fin R × Fin R // q.1 ≠ q.2} → Vec p := fun q =>
    u (z q.1.2) • z q.1.1 - u (z q.1.1) • z q.1.2
  have hw : ∀ q, w q ≠ 0 := by
    intro q hq
    apply hdir q.1.1 q.1.2 q.2 (u (z q.1.1) / u (z q.1.2))
    ext i
    have hi := congrFun (sub_eq_zero.mp hq) i
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    field_simp [hu q.1.2]
    linarith
  obtain ⟨v, hv⟩ := Module.exists_dual_forall_apply_ne_zero
    (K := ℝ) (M := Vec p) w hw
  refine ⟨u, v, hu, ?_⟩
  intro j k heq
  by_contra hjk
  have hcross : v (z j) * u (z k) = v (z k) * u (z j) := by
    exact (div_eq_div_iff (hu j) (hu k)).mp heq
  have hvzero : v (w ⟨(j, k), hjk⟩) = 0 := by
    simp only [w, map_sub, map_smul]
    dsimp
    linarith
  exact (hv ⟨(j, k), hjk⟩) hvzero

-- @node: lem:veronese-lagrange-rank
lemma veronese_kruskal_rank {p R s : ℕ} (z : Fin R → Vec p)
    (hR : 1 ≤ R) (hnz : ∀ j, z j ≠ 0)
    (hdir : ∀ j k, j ≠ k → ∀ t : ℝ, z j ≠ t • z k)
    (hs : R - 1 ≤ s) :
    ∀ S : Finset (Fin R), LinearIndependent ℝ
      (fun j : {j // j ∈ S} => veronesePower (s := s) (z j.1)) := by
  obtain ⟨u, v, hu, ht⟩ := projective_probe z hnz hdir
  have hall : LinearIndependent ℝ (fun j : Fin R => veronesePower (s := s) (z j)) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have heq (k : Fin R) :
        ∑ j : Fin R, (a j * u (z j) ^ s) * (v (z j) / u (z j)) ^ k.1 = 0 := by
      have hks : k.1 ≤ s := le_trans (Nat.le_pred_of_lt k.2) hs
      let fs : Fin s → Module.Dual ℝ (Vec p) := fun l => if l.1 < k.1 then v else u
      have hcontract := congrArg (fun T : (Fin s → Fin p) → ℝ =>
        ∑ I : Fin s → Fin p, (∏ l, fs l (Pi.single (I l) 1)) * T I) ha
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        mul_zero, Finset.sum_const_zero] at hcontract
      simp_rw [Finset.mul_sum] at hcontract
      rw [Finset.sum_comm] at hcontract
      have hfactor (j : Fin R) :
          (∑ I : Fin s → Fin p, (∏ l, fs l (Pi.single (I l) 1)) *
            (a j * veronesePower (s := s) (z j) I)) =
          a j * ∑ I : Fin s → Fin p, (∏ l, fs l (Pi.single (I l) 1)) *
            veronesePower (s := s) (z j) I := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro I _
        ring
      simp_rw [hfactor] at hcontract
      simp_rw [tensor_contraction] at hcontract
      have hprod (j : Fin R) :
          ∏ l : Fin s, fs l (z j) = v (z j) ^ k.1 * u (z j) ^ (s - k.1) := by
        simp only [fs]
        have hcardA : (Finset.univ.filter fun l : Fin s => l.val < k.val).card =
            k.val := by
          simpa [Nat.min_eq_right hks] using
            (Fin.card_filter_val_lt (n := s) (m := k.val))
        have hcardAc : (Finset.univ.filter fun l : Fin s => k.val ≤ l.val).card =
            s - k.val := by
          have hadd := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin s))) (p := fun l => l.val < k.val)
          simp only [Finset.card_univ, Fintype.card_fin] at hadd
          simp only [not_lt] at hadd
          omega
        have hfun : (fun l : Fin s => (if l.val < k.val then v else u) (z j)) =
            (fun l => if l.val < k.val then v (z j) else u (z j)) := by
          funext l
          split_ifs <;> rfl
        rw [hfun]
        rw [Finset.prod_ite]
        simp [hcardA, hcardAc]
      simp_rw [hprod] at hcontract
      convert hcontract using 1
      apply Finset.sum_congr rfl
      intro j _
      rw [div_pow]
      have hpow : u (z j) ^ s = u (z j) ^ (s - k.1) * u (z j) ^ k.1 := by
        rw [← pow_add, Nat.sub_add_cancel hks]
      rw [hpow]
      field_simp [hu j]
    have hz := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero ht heq
    intro j
    have := congrFun hz j
    simp only [Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ (hu j))
  intro S
  exact hall.comp Subtype.val Subtype.val_injective

noncomputable def totalVariationDistance {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) : ℝ :=
  sSup {d : ℝ | ∃ A : Set α, MeasurableSet A ∧
    d = |(P A).toReal - (Q A).toReal|}

-- @node: lem:finite-moment-near-gaussian-witness
lemma exists_nearGaussian_momentMatching_witness
    (CarlemanMomentDeterminacy_of_gate : CarlemanMomentDeterminacy)
    (K : ℕ) (hK : 3 ≤ K) (rho : ℝ) (hrho : 0 < rho) :
    ∃ F : Measure ℝ,
      IsProbabilityMeasure F ∧
      (∫ x, x ∂F) = 0 ∧
      ProbabilityTheory.variance id F = 1 ∧
      ¬ Causalean.Stat.MomentProblems.IsGaussianLaw F ∧
      MomentDeterminate F ∧
      totalVariationDistance F (ProbabilityTheory.gaussianReal 0 1) < rho ∧
      (∀ k, k ≤ K → rawMoment F k =
        rawMoment (ProbabilityTheory.gaussianReal 0 1) k) ∧
      (∀ k, k ≤ K → Causalean.Stat.MomentProblems.sourceCumulant F id k =
        Causalean.Stat.MomentProblems.sourceCumulant
          (ProbabilityTheory.gaussianReal 0 1) id k) := by
  obtain ⟨F, hprob, hmean, hvariance, hnongaussian, htv, hmoment,
      hallMoments, hcarleman, hcumulant⟩ :=
    Causalean.Stat.MomentProblems.exists_finiteMoment_near_gaussian_perturbation
      K rho hK hrho
  have hdeterminate : MomentDeterminate F :=
    CarlemanMomentDeterminacy_of_gate F hprob hallMoments (by
      simpa [Causalean.Stat.MomentProblems.hamburgerCarlemanSeries,
        Causalean.Stat.MomentProblems.rawMoment, rawMoment] using hcarleman)
  refine ⟨F, hprob, hmean, hvariance, hnongaussian, hdeterminate, ?_, ?_, hcumulant⟩
  · simpa [totalVariationDistance,
      Causalean.Stat.MomentProblems.totalVariationDistance] using htv
  · intro k hk
    simpa [rawMoment, Causalean.Stat.MomentProblems.rawMoment] using hmoment k hk

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

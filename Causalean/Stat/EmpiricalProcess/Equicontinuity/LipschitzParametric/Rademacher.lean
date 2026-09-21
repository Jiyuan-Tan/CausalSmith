/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Concentration.Covering.DudleyEntropy.EntropyBound
public import Causalean.Stat.Concentration.VC.Rademacher.Conditional
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.LipschitzParametric.Entropy

/-! # Conditional Rademacher bounds for Lipschitz parameter classes

This module applies conditional Dudley chaining to a finite-dimensional Lipschitz score
class, obtaining a samplewise bound in terms of the empirical envelope norm.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped BigOperators ENNReal

namespace Causalean.Stat

open Causalean.Stat.Concentration

/-- [The absolute Rademacher complexity is bounded by the sum of the positive
and negative signed complexities](goal) for [a function class](hyp:H) containing
[a pointwise-zero member](hyp:i₀,hzero), when the class is [uniformly bounded
on the sample](hyp:S,hM) by [a nonnegative bound](hyp:hM0). -/
lemma empiricalRademacherComplexity_le_signed_add_neg_of_zero_sample
    {X ι : Type*} [Nonempty ι]
    (H : ι → X → ℝ) (i₀ : ι) (hzero : ∀ x, H i₀ x = 0)
    {n : ℕ} (S : Fin n → X) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i k, |H i (S k)| ≤ M) :
    empiricalRademacherComplexity n H S ≤
      empiricalRademacherComplexity_without_abs n H S +
        empiricalRademacherComplexity_without_abs n (fun i x => -H i x) S := by
  classical
  unfold empiricalRademacherComplexity empiricalRademacherComplexity_without_abs
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ => ?_) (by positivity)
  let z : ι → ℝ := fun i =>
    (n : ℝ)⁻¹ * ∑ k : Fin n, (τ k : ℝ) * H i (S k)
  have hz0 : z i₀ = 0 := by simp [z, hzero]
  have hzabs : ∀ i, |z i| ≤ M := by
    intro i
    calc
      |z i| ≤ (n : ℝ)⁻¹ * ∑ k : Fin n, |H i (S k)| := by
        dsimp [z]
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
          congr 1
          ext k
          simp)
      _ ≤ (n : ℝ)⁻¹ * ∑ _k : Fin n, M := by
        gcongr with k
        exact hM i k
      _ ≤ M := by
        by_cases hn : n = 0
        · subst n
          simp [hM0]
        · simp [Nat.cast_ne_zero.mpr hn]
  have hbddAbs : BddAbove (Set.range fun i => |z i|) :=
    ⟨M, by rintro _ ⟨i, rfl⟩; exact hzabs i⟩
  have hbdd : BddAbove (Set.range z) :=
    ⟨M, by rintro _ ⟨i, rfl⟩; exact (le_abs_self _).trans (hzabs i)⟩
  have hbddNeg : BddAbove (Set.range fun i => -z i) :=
    ⟨M, by rintro _ ⟨i, rfl⟩; exact (neg_le_abs _).trans (hzabs i)⟩
  have hsup0 : 0 ≤ ⨆ i, z i := by rw [← hz0]; exact le_ciSup hbdd i₀
  have hsupNeg0 : 0 ≤ ⨆ i, -z i := by
    rw [← show -z i₀ = 0 by rw [hz0]; simp]
    exact le_ciSup hbddNeg i₀
  have hpoint : (⨆ i, |z i|) ≤ (⨆ i, z i) + (⨆ i, -z i) := by
    refine ciSup_le fun i => ?_
    by_cases hi : 0 ≤ z i
    · rw [abs_of_nonneg hi]
      linarith [le_ciSup hbdd i]
    · rw [abs_of_neg (lt_of_not_ge hi)]
      linarith [le_ciSup hbddNeg i]
  have hneg : (⨆ i, -z i) =
      ⨆ i, (n : ℝ)⁻¹ * ∑ k : Fin n, (τ k : ℝ) * (-H i (S k)) := by
    refine iSup_congr fun i => ?_
    calc
      -z i = (n : ℝ)⁻¹ * (-(∑ k : Fin n, (τ k : ℝ) * H i (S k))) := by
        simp only [z]
        ring
      _ = (n : ℝ)⁻¹ * ∑ k : Fin n, -((τ k : ℝ) * H i (S k)) := by
        rw [Finset.sum_neg_distrib]
      _ = (n : ℝ)⁻¹ * ∑ k : Fin n, (τ k : ℝ) * (-H i (S k)) := by
        congr 1
        refine Finset.sum_congr rfl fun k _ => by ring
  simpa [z, hneg] using hpoint

/-- [The signed empirical Rademacher complexity of a centered Lipschitz class
obeys the finite-dimensional chaining bound](goal) for [positive sample
size](hyp:hn) and [sample](hyp:S).  The [class](hyp:F) is [centered](hyp:hzero)
and has [Lipschitz control](hyp:hLip) by [a nonnegative envelope](hyp:L,hL) on
the ball with [center](hyp:θ₀) and [positive radius](hyp:hδ), whose
[empirical envelope norm is positive](hyp:ha). -/
lemma parametric_empiricalRademacher_without_abs_le
    {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {n : ℕ} (hn : 0 < n) (S : Fin n → X) (F : E → X → ℝ) (L : X → ℝ)
    (hL : ∀ x, 0 ≤ L x)
    (θ₀ : E) {δ : ℝ}
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ z,
      |F θ z - F η z| ≤ L z * ‖θ - η‖)
    (hzero : ∀ x, F θ₀ x = 0)
    (hδ : 0 < δ)
    (ha : 0 < Concentration.empiricalNorm S L) :
    empiricalRademacherComplexity_without_abs n
        (fun θ : Metric.closedBall θ₀ δ => F θ.1) S ≤
      48 * (Module.finrank ℝ E + 1) * δ *
        Concentration.empiricalNorm S L / Real.sqrt (n : ℝ) := by
  classical
  let FB : Metric.closedBall θ₀ δ → X → ℝ := fun θ => F θ.1
  let a := Concentration.empiricalNorm S L
  have hapos : 0 < a := by simpa [a] using ha
  let i₀ : Metric.closedBall θ₀ δ := ⟨θ₀, by simp [hδ.le]⟩
  letI : Nonempty (Metric.closedBall θ₀ δ) := ⟨i₀⟩
  have hnorm : ∀ θ : Metric.closedBall θ₀ δ,
      Concentration.empiricalNorm S (FB θ) ≤ δ * a := by
    intro θ
    apply empiricalNorm_le_mul S (FB θ) L δ hδ.le hL
    intro x
    have hb := hLip θ.1 θ.2 θ₀ (Metric.mem_closedBall_self hδ.le) x
    have hθ : ‖θ.1 - θ₀‖ ≤ δ := by
      have hp := θ.2
      rw [Metric.mem_closedBall, dist_eq_norm] at hp
      exact hp
    simpa [FB, hzero, mul_comm] using hb.trans (mul_le_mul_of_nonneg_left hθ (hL x))
  apply le_of_forall_pos_le_add
  intro ζ hζ
  let ε := min (δ * a / 2) (ζ / 4)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hδa : 0 < δ * a := mul_pos hδ hapos
  have hεR : ε ≤ δ * a := (min_le_left _ _).trans (by linarith)
  have hdudley := Concentration.dudley_entropy_integral_bound
    (F := FB) (c := 2 * (δ * a)) hε
    (parametric_empirical_totallyBounded S F L hL θ₀ δ hLip hδ.le)
    hn (fun θ => (hnorm θ).trans (by linarith [hδa]))
    (by
      have hm := min_le_left (δ * a / 2) (ζ / 4)
      change ε < (2 * (δ * a)) / 2
      rw [show (2 * (δ * a)) / 2 = δ * a by ring]
      exact lt_of_le_of_lt hm (by linarith))
  have hint := parametric_entropyIntegral_le S F L hL θ₀ hLip hδ hapos hε hεR
  have hεζ : 4 * ε ≤ ζ := by
    dsimp [ε]
    linarith [min_le_right (δ * a / 2) (ζ / 4)]
  calc
    empiricalRademacherComplexity_without_abs n FB S
        ≤ 4 * ε + 12 / Real.sqrt (n : ℝ) *
            (∫ x in ε..(δ * a),
              Real.sqrt (Real.log (Concentration.coveringNumber'
                (parametric_empirical_totallyBounded S F L hL θ₀ δ hLip hδ.le) x))) := by
          simpa [FB, a] using hdudley
    _ ≤ 4 * ε + 12 / Real.sqrt (n : ℝ) *
          (4 * (Module.finrank ℝ E + 1) * (δ * a)) := by
        gcongr
    _ ≤ 48 * (Module.finrank ℝ E + 1) * δ * a /
          Real.sqrt (n : ℝ) + ζ := by
        have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
        rw [div_eq_mul_inv, div_eq_mul_inv]
        nlinarith [hεζ, inv_pos.mpr hsqrt,
          show (0 : ℝ) ≤ Module.finrank ℝ E by positivity]

/-- [The absolute empirical Rademacher complexity of a centered Lipschitz
class is bounded by dimension times radius and empirical envelope norm](goal)
for [positive sample size](hyp:hn) and [sample](hyp:S).  The [class](hyp:F) is
[centered](hyp:hzero) and has [Lipschitz control](hyp:hLip) by [a nonnegative
envelope](hyp:L,hL) on the ball with [center](hyp:θ₀) and [positive
radius](hyp:hδ). -/
lemma parametric_empiricalRademacher_le
    {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {n : ℕ} (hn : 0 < n) (S : Fin n → X) (F : E → X → ℝ) (L : X → ℝ)
    (hL : ∀ x, 0 ≤ L x)
    (θ₀ : E) {δ : ℝ}
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ z,
      |F θ z - F η z| ≤ L z * ‖θ - η‖)
    (hzero : ∀ x, F θ₀ x = 0)
    (hδ : 0 < δ) :
    empiricalRademacherComplexity n
        (fun θ : Metric.closedBall θ₀ δ => F θ.1) S ≤
      96 * (Module.finrank ℝ E + 1) * δ *
        Concentration.empiricalNorm S L / Real.sqrt (n : ℝ) := by
  classical
  let FB : Metric.closedBall θ₀ δ → X → ℝ := fun θ => F θ.1
  let i₀ : Metric.closedBall θ₀ δ := ⟨θ₀, by simp [hδ.le]⟩
  letI : Nonempty (Metric.closedBall θ₀ δ) := ⟨i₀⟩
  let a := Concentration.empiricalNorm S L
  have ha : 0 ≤ a := by dsimp [a, Concentration.empiricalNorm]; positivity
  by_cases ha0 : a = 0
  · have hsampleZero : ∀ θ : Metric.closedBall θ₀ δ, ∀ k, FB θ (S k) = 0 := by
      intro θ k
      have hinside : (n : ℝ)⁻¹ * ∑ i : Fin n, L (S i) ^ 2 = 0 := by
        have hsqrt : Real.sqrt ((n : ℝ)⁻¹ * ∑ i : Fin n, L (S i) ^ 2) = 0 := by
          simpa [a, Concentration.empiricalNorm] using ha0
        exact (Real.sqrt_eq_zero (by positivity)).mp hsqrt
      have hsum : ∑ i : Fin n, L (S i) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hinside with hinv | hsum
        · exact False.elim (inv_ne_zero (by exact_mod_cast hn.ne') hinv)
        · exact hsum
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (L (S i)))).mp hsum k (by simp)
      have hLzero : L (S k) = 0 := sq_eq_zero_iff.mp hterm
      have hd := hLip θ.1 θ.2 θ₀ (Metric.mem_closedBall_self hδ.le) (S k)
      have : |F θ.1 (S k)| ≤ 0 := by simpa [hzero, hLzero] using hd
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
    have hcongr := Concentration.empiricalRademacherComplexity_congr_sample n FB
      (fun _ _ => 0) S (fun θ k => hsampleZero θ k)
    rw [hcongr]
    unfold empiricalRademacherComplexity
    simp [ha0, a]
  · have hapos : 0 < Concentration.empiricalNorm S L := by
      simpa [a] using lt_of_le_of_ne ha (Ne.symm ha0)
    have hM : ∀ θ : Metric.closedBall θ₀ δ, ∀ k,
        |FB θ (S k)| ≤ δ * ∑ i : Fin n, L (S i) := by
      intro θ k
      have hb := hLip θ.1 θ.2 θ₀ (Metric.mem_closedBall_self hδ.le) (S k)
      have hθ : ‖θ.1 - θ₀‖ ≤ δ := by
        have hp := θ.2
        rw [Metric.mem_closedBall, dist_eq_norm] at hp
        exact hp
      calc
        |FB θ (S k)| ≤ L (S k) * ‖θ.1 - θ₀‖ := by simpa [FB, hzero] using hb
        _ ≤ L (S k) * δ := mul_le_mul_of_nonneg_left hθ (hL _)
        _ ≤ δ * ∑ i : Fin n, L (S i) := by
          rw [mul_comm]
          gcongr
          exact Finset.single_le_sum (fun i _ => hL (S i)) (by simp)
    have habs := empiricalRademacherComplexity_le_signed_add_neg_of_zero_sample
      FB i₀ (by simp [FB, i₀, hzero]) S
      (mul_nonneg hδ.le (Finset.sum_nonneg fun i _ => hL (S i))) hM
    have hsigned := parametric_empiricalRademacher_without_abs_le
      hn S F L hL θ₀ hLip hzero hδ hapos
    have hLipNeg : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ z,
        |(-F θ z) - (-F η z)| ≤ L z * ‖θ - η‖ := by
      intro θ hθ η hη z
      rw [show (-F θ z) - (-F η z) = -(F θ z - F η z) by ring, abs_neg]
      exact hLip θ hθ η hη z
    have hsignedNeg := parametric_empiricalRademacher_without_abs_le
      hn S (fun θ x => -F θ x) L hL θ₀ hLipNeg (by simp [hzero]) hδ hapos
    calc
      empiricalRademacherComplexity n FB S
          ≤ empiricalRademacherComplexity_without_abs n FB S +
            empiricalRademacherComplexity_without_abs n (fun θ x => -FB θ x) S := habs
      _ ≤ 96 * (Module.finrank ℝ E + 1) * δ * a /
          Real.sqrt (n : ℝ) := by
        rw [show (96 : ℝ) = 48 + 48 by norm_num]
        simpa [FB, a, add_mul, add_div] using add_le_add hsigned hsignedNeg
      _ = 96 * (Module.finrank ℝ E + 1) * δ *
          Concentration.empiricalNorm S L / Real.sqrt (n : ℝ) := rfl


end Causalean.Stat

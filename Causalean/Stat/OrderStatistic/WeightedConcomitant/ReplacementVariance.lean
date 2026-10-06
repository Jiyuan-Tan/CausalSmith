module
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.ReplacementSensitivity

/-!
# Tensorized variance of rank-weighted concomitants

This module applies independent coordinate replacement to bound the variance
of a bounded rank-weighted concomitant by its squared cell weights.
-/

public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open ProbabilityTheory
open Causalean.Mathlib.Probability.PoissonAddOnePoincare
open scoped BigOperators

noncomputable section

/-- Under a continuous sorting-coordinate CDF, almost every original sample
and independent coordinate replacement have distinct coordinates and bounded
marks, so the pointwise rank replacement sensitivity applies. -/
theorem rankConcomitant_replacement_sensitivity_ae {N : ℕ}
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hcont : Continuous (fun t => ProbabilityTheory.cdf (μ.map Prod.fst) t))
    (hmark : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin N → ℝ) (ha : ∀ j, 0 ≤ a j) (hmono : Antitone a)
    (i : Fin N) :
    ∀ᵐ p : (Fin N → ℝ × ℝ) × (ℝ × ℝ)
      ∂(Measure.pi (fun _ : Fin N => μ)).prod μ,
      |rankConcomitant a p.1 -
        rankConcomitant a (coordinateReplace i p.1 p.2)| ≤
        a (rankPosition p.1 i) +
          a (rankPosition (coordinateReplace i p.1 p.2) i) := by
  -- Pull tie-free events back through the two product marginals, and use
  -- rankConcomitant_replacement_sensitivity on their intersection.
  let P : Measure (Fin N → ℝ × ℝ) := Measure.pi (fun _ : Fin N => μ)
  let R : Measure ((Fin N → ℝ × ℝ) × (ℝ × ℝ)) := P.prod μ
  let F : (Fin N → ℝ × ℝ) → (Fin N → ℝ) :=
    fun x k => ProbabilityTheory.cdf (μ.map Prod.fst) (x k).1
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro k
    exact hcont.measurable.comp (measurable_fst.comp (measurable_pi_apply k))
  have hcoord : ∀ᵐ x ∂P, Function.Injective (F x) := by
    have hu := iid_uniform_coordinates_injective_ae (N := N)
    rw [← cdf_transport_iid μ hcont] at hu
    exact ae_of_ae_map hF.aemeasurable hu
  have hinj : ∀ᵐ x ∂P, Function.Injective (fun k => (x k).1) := by
    filter_upwards [hcoord] with x hx j k hjk
    apply hx
    exact congrArg (fun t : ℝ => ProbabilityTheory.cdf (μ.map Prod.fst) t) hjk
  have hmarkP : ∀ᵐ x ∂P, ∀ j : Fin N, (x j).2 ∈ Set.Icc (0 : ℝ) 1 := by
    apply Filter.eventually_all.mpr
    intro j
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N => μ)
      (i := j)).eventually hmark
  have hfst : MeasurePreserving (Prod.fst : (Fin N → ℝ × ℝ) × (ℝ × ℝ) → _)
      R P := measurePreserving_fst
  have hsnd : MeasurePreserving (Prod.snd : (Fin N → ℝ × ℝ) × (ℝ × ℝ) → _)
      R μ := measurePreserving_snd
  have hreplace : MeasurePreserving
      (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) => coordinateReplace i p.1 p.2)
      R P := ⟨measurable_coordinateReplace_pair i, coordinateReplace_map_prod μ i⟩
  have hinj₁ : ∀ᵐ p ∂ R, Function.Injective (fun j => (p.1 j).1) := by
    exact ae_of_ae_map hfst.aemeasurable (by rw [hfst.map_eq]; exact hinj)
  have hinj₂ : ∀ᵐ p ∂ R,
      Function.Injective (fun j => ((coordinateReplace i p.1 p.2) j).1) := by
    exact ae_of_ae_map hreplace.aemeasurable
      (by rw [hreplace.map_eq]; exact hinj)
  have hm₁ : ∀ᵐ p ∂ R, ∀ j : Fin N, (p.1 j).2 ∈ Set.Icc (0 : ℝ) 1 := by
    exact ae_of_ae_map hfst.aemeasurable (by rw [hfst.map_eq]; exact hmarkP)
  have hm₂ : ∀ᵐ p ∂ R, p.2.2 ∈ Set.Icc (0 : ℝ) 1 := by
    exact ae_of_ae_map hsnd.aemeasurable (by rw [hsnd.map_eq]; exact hmark)
  filter_upwards [hinj₁, hinj₂, hm₁, hm₂] with p hp hp' hm hy
  exact rankConcomitant_replacement_sensitivity a ha hmono p.1 i p.2 hm hy hp hp'

/-- The squared change of a bounded rank concomitant after one independent
coordinate replacement is integrable under the sample–replacement product law. -/
theorem rankConcomitant_replacement_difference_sq_integrable {N : ℕ}
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hmark : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin N → ℝ) (i : Fin N) :
    Integrable
      (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) =>
        (rankConcomitant a p.1 -
          rankConcomitant a (coordinateReplace i p.1 p.2)) ^ 2)
      ((Measure.pi (fun _ : Fin N => μ)).prod μ) := by
  -- Pull square integrability of rankConcomitant along both projections;
  -- coordinateReplace_map_prod handles the resampled statistic.
  let P : Measure (Fin N → ℝ × ℝ) := Measure.pi (fun _ : Fin N => μ)
  let R : Measure ((Fin N → ℝ × ℝ) × (ℝ × ℝ)) := P.prod μ
  have hLp : MemLp (rankConcomitant a) 2 P := rankConcomitant_memLp_two μ hmark a
  have hfst : MeasurePreserving (Prod.fst : (Fin N → ℝ × ℝ) × (ℝ × ℝ) → _)
      R P := measurePreserving_fst
  have hreplace : MeasurePreserving
      (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) => coordinateReplace i p.1 p.2)
      R P := ⟨measurable_coordinateReplace_pair i, coordinateReplace_map_prod μ i⟩
  have h₁ : MemLp (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) =>
      rankConcomitant a p.1) 2 R := hLp.comp_measurePreserving hfst
  have h₂ : MemLp (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) =>
      rankConcomitant a (coordinateReplace i p.1 p.2)) 2 R :=
    hLp.comp_measurePreserving hreplace
  have hdiff : MemLp (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) =>
      rankConcomitant a p.1 - rankConcomitant a (coordinateReplace i p.1 p.2))
      2 R := h₁.sub h₂
  exact (memLp_two_iff_integrable_sq hdiff.aestronglyMeasurable).mp hdiff

/-- Under a continuous sorting-coordinate CDF, the square of a fixed
observation's rank weight is integrable for any finite real weight vector. -/
theorem rankPosition_weight_sq_integrable {N : ℕ}
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hcont : Continuous (fun t => ProbabilityTheory.cdf (μ.map Prod.fst) t))
    (a : Fin N → ℝ) (i : Fin N) :
    Integrable (fun x : Fin N → ℝ × ℝ => (a (rankPosition x i)) ^ 2)
      (Measure.pi (fun _ : Fin N => μ)) := by
  classical
  let P : Measure (Fin N → ℝ × ℝ) := Measure.pi (fun _ : Fin N => μ)
  let F : (Fin N → ℝ × ℝ) → (Fin N → ℝ) :=
    fun x k => ProbabilityTheory.cdf (μ.map Prod.fst) (x k).1
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro k
    exact hcont.measurable.comp (measurable_fst.comp (measurable_pi_apply k))
  have hcoord : ∀ᵐ x ∂P, Function.Injective (F x) := by
    have hu := iid_uniform_coordinates_injective_ae (N := N)
    rw [← cdf_transport_iid μ hcont] at hu
    exact ae_of_ae_map hF.aemeasurable hu
  have hinj : ∀ᵐ x ∂P, Function.Injective (fun k => (x k).1) := by
    filter_upwards [hcoord] with x hx j k hjk
    apply hx
    exact congrArg (fun t : ℝ => ProbabilityTheory.cdf (μ.map Prod.fst) t) hjk
  have hrank (j : Fin N) : NullMeasurableSet {x | rankPosition x i = j} P := by
    let E : Set (Fin N → ℝ × ℝ) :=
      {x | ((Finset.univ : Finset (Fin N)).filter
        (fun k => (x k).1 < (x i).1)).card = j.val}
    have hE : MeasurableSet E := by
      dsimp [E]
      apply measurableSet_eq_fun
      · simp_rw [Finset.card_filter]
        apply Finset.measurable_sum
        intro k _
        apply Measurable.ite
        · exact measurableSet_lt
            (measurable_fst.comp (measurable_pi_apply k))
            (measurable_fst.comp (measurable_pi_apply i))
        · exact measurable_const
        · exact measurable_const
      · exact measurable_const
    apply hE.nullMeasurableSet.congr
    filter_upwards [hinj] with x hx
    apply propext
    change (((Finset.univ : Finset (Fin N)).filter
      (fun k => (x k).1 < (x i).1)).card = j.val) ↔ rankPosition x i = j
    rw [← rankPosition_val_eq_card_lt x i hx]
    exact Fin.ext_iff.symm
  have hr : AEMeasurable (fun x : Fin N → ℝ × ℝ => rankPosition x i) P := by
    apply NullMeasurable.aemeasurable
    change @Measurable (NullMeasurableSpace (Fin N → ℝ × ℝ) P) (Fin N) _ _
      (fun x => rankPosition x i)
    apply measurable_to_countable'
    intro j
    exact hrank j
  have hstrong : AEStronglyMeasurable
      (fun x : Fin N → ℝ × ℝ => (a (rankPosition x i)) ^ 2) P :=
    ((measurable_of_countable (fun j : Fin N => (a j) ^ 2)).comp_aemeasurable
      hr).aestronglyMeasurable
  apply Integrable.of_bound hstrong (∑ j : Fin N, |(a j) ^ 2|)
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun j _ => abs_nonneg ((a j) ^ 2))
    (Finset.mem_univ (rankPosition x i))

/-- Independent replacement preserves the expected squared weight of
the replaced observation's rank. -/
theorem integral_replaced_rankPosition_weight_sq {N : ℕ}
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hcont : Continuous (fun t => ProbabilityTheory.cdf (μ.map Prod.fst) t))
    (a : Fin N → ℝ) (i : Fin N) :
    (∫ p : (Fin N → ℝ × ℝ) × (ℝ × ℝ),
      (a (rankPosition (coordinateReplace i p.1 p.2) i)) ^ 2
      ∂(Measure.pi (fun _ : Fin N => μ)).prod μ) =
      ∫ x, (a (rankPosition x i)) ^ 2
        ∂Measure.pi (fun _ : Fin N => μ) := by
  exact integral_coordinateReplace_prod μ i
    (fun x => (a (rankPosition x i)) ^ 2)
    (rankPosition_weight_sq_integrable μ hcont a i)

/-- Almost surely under the sample–replacement product law, the squared
change in a rank concomitant is at most twice the sum of the squared weights
at the removed and inserted ranks. -/
theorem rankConcomitant_replacement_sq_ae {N : ℕ}
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hcont : Continuous (fun t => ProbabilityTheory.cdf (μ.map Prod.fst) t))
    (hmark : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin N → ℝ) (ha : ∀ j, 0 ≤ a j) (hmono : Antitone a)
    (i : Fin N) :
    ∀ᵐ p : (Fin N → ℝ × ℝ) × (ℝ × ℝ)
      ∂(Measure.pi (fun _ : Fin N => μ)).prod μ,
      (rankConcomitant a p.1 -
        rankConcomitant a (coordinateReplace i p.1 p.2)) ^ 2 ≤
        2 * ((a (rankPosition p.1 i)) ^ 2 +
          (a (rankPosition (coordinateReplace i p.1 p.2) i)) ^ 2) := by
  filter_upwards [rankConcomitant_replacement_sensitivity_ae μ hcont hmark a ha hmono i]
    with p hp
  have h₁ := ha (rankPosition p.1 i)
  have h₂ := ha (rankPosition (coordinateReplace i p.1 p.2) i)
  have hprod : 0 ≤ |rankConcomitant a p.1 -
      rankConcomitant a (coordinateReplace i p.1 p.2)| *
      (a (rankPosition p.1 i) +
        a (rankPosition (coordinateReplace i p.1 p.2) i) -
        |rankConcomitant a p.1 -
          rankConcomitant a (coordinateReplace i p.1 p.2)|) :=
    mul_nonneg (abs_nonneg _) (sub_nonneg.mpr hp)
  have hprod' : 0 ≤ (a (rankPosition p.1 i) +
      a (rankPosition (coordinateReplace i p.1 p.2) i)) *
      (a (rankPosition p.1 i) +
        a (rankPosition (coordinateReplace i p.1 p.2) i) -
        |rankConcomitant a p.1 -
          rankConcomitant a (coordinateReplace i p.1 p.2)|) :=
    mul_nonneg (add_nonneg h₁ h₂) (sub_nonneg.mpr hp)
  nlinarith [sq_nonneg (a (rankPosition p.1 i) -
    a (rankPosition (coordinateReplace i p.1 p.2) i)),
    sq_abs (rankConcomitant a p.1 -
      rankConcomitant a (coordinateReplace i p.1 p.2))]

/-- For an iid marked sample with a continuous sorting-coordinate CDF and
unit-bounded marks, the mean squared change after resampling one observation
is at most four times the mean squared weight at its original rank. -/
theorem integral_replacement_sq_le_four_rank_weight_sq {N : ℕ}
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hcont : Continuous (fun t => ProbabilityTheory.cdf (μ.map Prod.fst) t))
    (hmark : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin N → ℝ) (ha : ∀ j, 0 ≤ a j) (hmono : Antitone a)
    (i : Fin N) :
    (∫ x, ∫ y,
      (rankConcomitant a x - rankConcomitant a (coordinateReplace i x y)) ^ 2 ∂μ
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      4 * ∫ x, (a (rankPosition x i)) ^ 2
        ∂Measure.pi (fun _ : Fin N => μ) := by
  -- On the full-measure tie-free event, replacement sensitivity gives
  -- (Z(x)-Z(x^i_y))² ≤ 2(a(rank_i x)²+a(rank_i x^i_y)²).
  -- The law of x^i_y under the product measure is again the iid law, so
  -- both weight-square integrals are equal.
  let P : Measure (Fin N → ℝ × ℝ) := Measure.pi (fun _ : Fin N => μ)
  let R : Measure ((Fin N → ℝ × ℝ) × (ℝ × ℝ)) := P.prod μ
  let w : (Fin N → ℝ × ℝ) → ℝ := fun x => (a (rankPosition x i)) ^ 2
  let w' : ((Fin N → ℝ × ℝ) × (ℝ × ℝ)) → ℝ :=
    fun p => (a (rankPosition (coordinateReplace i p.1 p.2) i)) ^ 2
  let d : ((Fin N → ℝ × ℝ) × (ℝ × ℝ)) → ℝ :=
    fun p => (rankConcomitant a p.1 -
      rankConcomitant a (coordinateReplace i p.1 p.2)) ^ 2
  have hw : Integrable w P := rankPosition_weight_sq_integrable μ hcont a i
  have hfst : MeasurePreserving (Prod.fst : ((Fin N → ℝ × ℝ) × (ℝ × ℝ)) → _) R P :=
    measurePreserving_fst
  have hwfst : Integrable (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) => w p.1) R :=
    hfst.integrable_comp_of_integrable hw
  have hreplace : MeasurePreserving
      (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) => coordinateReplace i p.1 p.2)
      R P := ⟨measurable_coordinateReplace_pair i, coordinateReplace_map_prod μ i⟩
  have hw' : Integrable w' R := hreplace.integrable_comp_of_integrable hw
  have hd : Integrable d R :=
    rankConcomitant_replacement_difference_sq_integrable μ hmark a i
  have hmono' : (∫ p : (Fin N → ℝ × ℝ) × (ℝ × ℝ), d p ∂(R)) ≤
      ∫ p : (Fin N → ℝ × ℝ) × (ℝ × ℝ), 2 * (w p.1 + w' p) ∂(R) := by
    apply integral_mono_ae hd
    · exact (hwfst.add hw').const_mul 2
    · exact rankConcomitant_replacement_sq_ae μ hcont hmark a ha hmono i
  have hleft : (∫ p : (Fin N → ℝ × ℝ) × (ℝ × ℝ), d p ∂(R)) = ∫ x, ∫ y,
      (rankConcomitant a x - rankConcomitant a (coordinateReplace i x y)) ^ 2
        ∂μ ∂(P) := integral_prod _ hd
  have hfirst : (∫ p : (Fin N → ℝ × ℝ) × (ℝ × ℝ), w p.1 ∂(R)) =
      ∫ x, w x ∂(P) := by
    rw [integral_prod _ hwfst]
    simp
  have hsecond : (∫ p : (Fin N → ℝ × ℝ) × (ℝ × ℝ), w' p ∂(R)) =
      ∫ x, w x ∂(P) := by
    exact integral_replaced_rankPosition_weight_sq μ hcont a i
  rw [← hleft]
  calc
    (∫ p : (Fin N → ℝ × ℝ) × (ℝ × ℝ), d p ∂(R)) ≤
        ∫ p : (Fin N → ℝ × ℝ) × (ℝ × ℝ), 2 * (w p.1 + w' p) ∂(R) := hmono'
    _ = 2 * ((∫ p : (Fin N → ℝ × ℝ) × (ℝ × ℝ), w p.1 ∂(R)) +
        ∫ p : (Fin N → ℝ × ℝ) × (ℝ × ℝ), w' p ∂(R)) := by
      rw [integral_const_mul, integral_add hwfst hw']
    _ = 4 * ∫ x, w x ∂(P) := by rw [hfirst, hsecond]; ring

/-- For an iid marked sample with continuous sorting-coordinate CDF and marks
 in `[0,1]`, the expected variance from resampling one coordinate is bounded
 by twice that coordinate's expected squared rank weight. -/
theorem integral_coordinateVariance_rankConcomitant_le {N : ℕ}
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hcont : Continuous (fun t => ProbabilityTheory.cdf (μ.map Prod.fst) t))
    (hmark : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin N → ℝ) (ha : ∀ j, 0 ≤ a j) (hmono : Antitone a)
    (i : Fin N) :
    (∫ x, variance (fun y => rankConcomitant a (coordinateReplace i x y)) μ
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      2 * ∫ x, (a (rankPosition x i)) ^ 2
        ∂Measure.pi (fun _ : Fin N => μ) := by
  -- Use the pairwise variance identity in the replacement coordinate, the
  -- sensitivity theorem on the full-measure tie-free/bounded-mark event, and
  -- symmetry of the original and resampled rank weights.
  rw [integral_coordinateVariance_eq_half_replacement_sq μ i
    (rankConcomitant a) (rankConcomitant_memLp_two μ hmark a)]
  have h := integral_replacement_sq_le_four_rank_weight_sq μ hcont hmark a ha hmono i
  nlinarith

/-- For an [iid marked law](hyp:μ) with [continuous sorting-coordinate CDF](hyp:hcont) and
 [unit-bounded marks](hyp:hmark), and [cell weights](hyp:a) that are [nonnegative and antitone](hyp:ha,hmono),
 [the concomitant variance is at most twice the squared-weight sum](goal). -/
theorem variance_rankConcomitant_le_twice_sum_sq {N : ℕ}
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hcont : Continuous (fun t => ProbabilityTheory.cdf (μ.map Prod.fst) t))
    (hmark : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin N → ℝ) (ha : ∀ j, 0 ≤ a j) (hmono : Antitone a) :
    variance (rankConcomitant a) (Measure.pi (fun _ : Fin N => μ)) ≤
      2 * ∑ j : Fin N, (a j) ^ 2 := by
  classical
  have hT := variance_pi_le_sum_integral_coordinateVariance
    (fun _ : Fin N => μ) (rankConcomitant a)
    (rankConcomitant_memLp_two μ hmark a)
  by_cases hN : 0 < N
  · calc
      variance (rankConcomitant a) (Measure.pi (fun _ : Fin N => μ)) ≤
          ∑ i : Fin N, ∫ x,
            variance (fun y => rankConcomitant a (coordinateReplace i x y)) μ
              ∂Measure.pi (fun _ : Fin N => μ) := hT
      _ ≤ ∑ i : Fin N, 2 * ∫ x, (a (rankPosition x i)) ^ 2
            ∂Measure.pi (fun _ : Fin N => μ) := by
              apply Finset.sum_le_sum
              intro i _
              exact integral_coordinateVariance_rankConcomitant_le
                μ hcont hmark a ha hmono i
      _ = 2 * ∑ j : Fin N, (a j) ^ 2 := by
        simp_rw [integral_rankPosition_weight_sq hN μ hcont a]
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
        field_simp
  · have h0 : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    simpa using hT


end
end Causalean.Stat.OrderStatistic.WeightedConcomitant

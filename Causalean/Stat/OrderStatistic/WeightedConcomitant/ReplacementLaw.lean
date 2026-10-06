module
public import Causalean.Mathlib.Probability.Poisson.Poincare.Tensorization

/-!
# Independent replacement under a finite product law

Replacing one coordinate of an iid tuple by an independent observation
preserves its product distribution. This measure statement isolates the
exchangeability step used by rank-statistic variance bounds.
-/

public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open ProbabilityTheory
open Causalean.Mathlib.Probability.PoissonAddOnePoincare

noncomputable section

/-- For a finite tuple and an independent replacement value, updating one
coordinate is a measurable map of the tuple and the value. -/
@[fun_prop] theorem measurable_coordinateReplace_pair {N : ℕ} {α : Type*}
    [MeasurableSpace α] (i : Fin N) :
    Measurable (fun p : (Fin N → α) × α =>
      coordinateReplace i p.1 p.2) := by
  classical
  apply measurable_pi_iff.mpr
  intro j
  by_cases h : j = i
  · subst j
    simpa [coordinateReplace] using
      (measurable_snd : Measurable (fun p : (Fin N → α) × α => p.2))
  · have hm : Measurable (fun p : (Fin N → α) × α => p.1 j) := by fun_prop
    simpa [coordinateReplace, h] using hm

/-- If a finite tuple has iid law `μ` and `y` is an independent draw from `μ`,
the tuple obtained by replacing coordinate `i` with `y` has the original iid law. -/
theorem coordinateReplace_map_prod {N : ℕ} {α : Type*}
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (i : Fin N) :
    Measure.map
      (fun p : (Fin N → α) × α => coordinateReplace i p.1 p.2)
      ((Measure.pi (fun _ : Fin N => μ)).prod μ) =
      Measure.pi (fun _ : Fin N => μ) := by
  classical
  apply (Measure.pi_eq (μ := fun _ : Fin N => μ) (fun s hs => ?_)).symm
  let t : Fin N → Set α := fun j => if j = i then Set.univ else s j
  have hpre :
      (fun p : (Fin N → α) × α => coordinateReplace i p.1 p.2) ⁻¹'
        (Set.univ.pi s) = (Set.univ.pi t) ×ˢ s i := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_prod, t, coordinateReplace]
    constructor
    · intro hp
      constructor
      · intro j
        by_cases h : j = i
        · simp [h]
        · simpa [h] using hp j
      · simpa using hp i
    · rintro ⟨hp, hi⟩ j
      by_cases h : j = i
      · simpa [h] using hi
      · simpa [h] using hp j
  rw [Measure.map_apply (measurable_coordinateReplace_pair i)
      (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod,
    Measure.pi_pi]
  dsimp [t]
  rw [show (∏ j : Fin N, μ (if j = i then Set.univ else s j)) =
      ∏ j ∈ Finset.univ.erase i, μ (s j) by
    rw [← Finset.prod_erase_mul (s := Finset.univ) (f := fun j =>
      μ (if j = i then Set.univ else s j)) (a := i) (by simp)]
    simp only [if_true, measure_univ, mul_one]
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [hji]]
  exact Finset.prod_erase_mul Finset.univ (fun j : Fin N => μ (s j)) (by simp)

/-- Integrating an integrable function of an iid tuple is unchanged when one
coordinate is replaced by an independent draw from the same law. -/
theorem integral_coordinateReplace_prod {N : ℕ} {α : Type*}
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (i : Fin N) (f : (Fin N → α) → ℝ)
    (hf : Integrable f (Measure.pi (fun _ : Fin N => μ))) :
    (∫ p : (Fin N → α) × α, f (coordinateReplace i p.1 p.2)
      ∂(Measure.pi (fun _ : Fin N => μ)).prod μ) =
      ∫ x, f x ∂Measure.pi (fun _ : Fin N => μ) := by
  have hfm : AEStronglyMeasurable f
      (Measure.map (fun p : (Fin N → α) × α => coordinateReplace i p.1 p.2)
        ((Measure.pi (fun _ : Fin N => μ)).prod μ)) := by
    rw [coordinateReplace_map_prod μ i]
    exact hf.aestronglyMeasurable
  rw [← integral_map (measurable_coordinateReplace_pair i).aemeasurable hfm,
    coordinateReplace_map_prod μ i]

/-- For a square-integrable statistic of an iid finite tuple, the expected
conditional variance at one coordinate is half the expected squared difference
between two independent replacements of that coordinate. -/
theorem integral_coordinateVariance_eq_half_double_replacement_sq
    {N : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (i : Fin N) (F : (Fin N → α) → ℝ)
    (hF : MemLp F 2 (Measure.pi (fun _ : Fin N => μ))) :
    (∫ x, variance (fun y => F (coordinateReplace i x y)) μ
      ∂Measure.pi (fun _ : Fin N => μ)) =
      (1 / 2 : ℝ) *
        ∫ x, ∫ y, ∫ z,
          (F (coordinateReplace i x y) - F (coordinateReplace i x z)) ^ 2 ∂μ ∂μ
          ∂Measure.pi (fun _ : Fin N => μ) := by
  -- Derive MemLp of the replacement section for almost every x from the
  -- product L² hypothesis. Apply variance_eq_half_integral_prod_sq_sub
  -- on those sections, then use Fubini for the triple square integral.
  let ν : Measure (Fin N → α) := Measure.pi (fun _ => μ)
  let H : (Fin N → α) × α → ℝ := fun p => F (coordinateReplace i p.1 p.2)
  have hmp : MeasurePreserving
      (fun p : (Fin N → α) × α => coordinateReplace i p.1 p.2)
      (ν.prod μ) ν := by
    refine ⟨measurable_coordinateReplace_pair i, ?_⟩
    exact coordinateReplace_map_prod μ i
  have hH : MemLp H 2 (ν.prod μ) := hF.comp_measurePreserving hmp
  have hslices : ∀ᵐ x ∂ν, MemLp (fun y => H (x, y)) 2 μ := by
    filter_upwards [hH.aestronglyMeasurable.prodMk_left,
      hH.integrable_sq.prod_right_ae] with x hxm hxi
    exact (memLp_two_iff_integrable_sq hxm).2 hxi
  change (∫ x, variance (fun y => H (x, y)) μ ∂ν) =
    (1 / 2 : ℝ) * ∫ x, ∫ y, ∫ z, (H (x, y) - H (x, z)) ^ 2 ∂μ ∂μ ∂ν
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hslices] with x hx
  rw [variance_eq_half_integral_prod_sq_sub μ (fun y => H (x, y)) hx]
  congr 1
  have hpair : Integrable (fun p : α × α =>
      (H (x, p.1) - H (x, p.2)) ^ 2) (μ.prod μ) :=
    ((hx.comp_fst μ).sub (hx.comp_snd μ)).integrable_sq
  exact integral_prod _ hpair

/-- For a square-integrable statistic of an iid finite tuple, averaging the
squared difference of two independent coordinate replacements equals averaging
the squared difference between the original tuple and one replacement. -/
theorem integral_double_replacement_sq_eq_replacement_sq
    {N : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (i : Fin N) (F : (Fin N → α) → ℝ)
    (hF : MemLp F 2 (Measure.pi (fun _ : Fin N => μ))) :
    (∫ x, ∫ y, ∫ z,
      (F (coordinateReplace i x y) - F (coordinateReplace i x z)) ^ 2 ∂μ ∂μ
        ∂Measure.pi (fun _ : Fin N => μ)) =
      ∫ x, ∫ y, (F x - F (coordinateReplace i x y)) ^ 2 ∂μ
        ∂Measure.pi (fun _ : Fin N => μ) := by
  -- Replacing the original tuple with the independent draw preserves its law.
  -- Lift that measure-preserving map across the other independent draw, then
  -- apply Fubini and collapse the two updates at the same coordinate.
  let ν : Measure (Fin N → α) := Measure.pi (fun _ => μ)
  let R : (Fin N → α) × α → (Fin N → α) :=
    fun p => coordinateReplace i p.1 p.2
  let G : (Fin N → α) × α → ℝ :=
    fun p => (F p.1 - F (coordinateReplace i p.1 p.2)) ^ 2
  have hR : MeasurePreserving R (ν.prod μ) ν := by
    refine ⟨measurable_coordinateReplace_pair i, ?_⟩
    exact coordinateReplace_map_prod μ i
  have hFR : MemLp (fun p : (Fin N → α) × α => F (R p)) 2 (ν.prod μ) :=
    hF.comp_measurePreserving hR
  have hG : Integrable G (ν.prod μ) := by
    exact ((hF.comp_fst μ).sub hFR).integrable_sq
  have hRR : MeasurePreserving (Prod.map R id)
      ((ν.prod μ).prod μ) (ν.prod μ) :=
    hR.prod (MeasurePreserving.id μ)
  have hGcomp : Integrable
      (fun p : ((Fin N → α) × α) × α => G (R p.1, p.2))
      ((ν.prod μ).prod μ) := by
    exact hRR.integrable_comp_of_integrable hG
  have hmap :
      (∫ p : ((Fin N → α) × α) × α, G (R p.1, p.2)
        ∂((ν.prod μ).prod μ)) = ∫ q, G q ∂(ν.prod μ) := by
    have hm : AEStronglyMeasurable G
        (Measure.map (Prod.map R id) ((ν.prod μ).prod μ)) := by
      rw [hRR.map_eq]
      exact hG.aestronglyMeasurable
    change (∫ p : ((Fin N → α) × α) × α, G ((Prod.map R id) p)
      ∂((ν.prod μ).prod μ)) = ∫ q, G q ∂(ν.prod μ)
    rw [← integral_map hRR.measurable.aemeasurable hm, hRR.map_eq]
  have hiter :
      (∫ x, ∫ z, ∫ y, G (R (x, z), y) ∂μ ∂μ ∂ν) =
        ∫ x, ∫ y, G (x, y) ∂μ ∂ν := by
    calc
      _ = ∫ p : (Fin N → α) × α, ∫ y, G (R p, y) ∂μ ∂(ν.prod μ) := by
        exact (integral_prod _ hGcomp.integral_prod_left).symm
      _ = ∫ p : ((Fin N → α) × α) × α, G (R p.1, p.2)
          ∂((ν.prod μ).prod μ) := by
        exact (integral_prod _ hGcomp).symm
      _ = ∫ q, G q ∂(ν.prod μ) := hmap
      _ = ∫ x, ∫ y, G (x, y) ∂μ ∂ν := integral_prod _ hG
  simpa only [G, R, coordinateReplace, Function.update_idem] using hiter

/-- An [iid sampling law](hyp:μ), [selected coordinate](hyp:i), and
[square-integrable statistic](hyp:F,hF) give [an expected replacement variance
equal to half its expected squared independent replacement change](goal). -/
theorem integral_coordinateVariance_eq_half_replacement_sq
    {N : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (i : Fin N) (F : (Fin N → α) → ℝ)
    (hF : MemLp F 2 (Measure.pi (fun _ : Fin N => μ))) :
    (∫ x, variance (fun y => F (coordinateReplace i x y)) μ
      ∂Measure.pi (fun _ : Fin N => μ)) =
      (1 / 2 : ℝ) *
        ∫ x, ∫ y, (F x - F (coordinateReplace i x y)) ^ 2 ∂μ
          ∂Measure.pi (fun _ : Fin N => μ) := by
  rw [integral_coordinateVariance_eq_half_double_replacement_sq μ i F hF,
    integral_double_replacement_sq_eq_replacement_sq μ i F hF]

end
end Causalean.Stat.OrderStatistic.WeightedConcomitant

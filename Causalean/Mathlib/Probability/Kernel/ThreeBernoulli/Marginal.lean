module
public import Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.Basic

/-!
# Base marginal and support transfer

Finite Boolean summation removes the three marks and recovers the original
base law. Full-mass measurable support sets then transfer to three marks.
-/

public section

open MeasureTheory

noncomputable section

namespace Causalean.Mathlib.Probability.Kernel.ThreeBernoulli

universe u

/-- [The base marginal in density coordinates equals `μ`](goal) when
[the three probabilities are measurable](hyp:he,hq₀,hq₁) and
[unit-interval valued](hyp:he01,hq₀01,hq₁01). -/
theorem densityLaw_base_marginal {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e q₀ q₁ : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (he01 : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    (hq₀01 : ∀ x, q₀ x ∈ Set.Icc (0 : ℝ) 1)
    (hq₁01 : ∀ x, q₁ x ∈ Set.Icc (0 : ℝ) 1) :
    (densityLaw μ e q₀ q₁).map (fun z : DensityCoord X => z.2.2) = μ := by
  -- Compare lintegrals against arbitrary measurable nonnegative test functions.
  -- Tonelli over the three Boolean counting measures leaves their total
  -- product mass, which is one by `tripleMass_sum`. The proof of
  -- `densityLaw_probability` already carries the measurable-density and
  -- `ofReal` finite-sum calculations needed here; the extra test function
  -- depends only on `x`, so it factors out after swapping the integrals.
  have hbit (p : X → ℝ) (hp : Measurable p)
      (b : DensityCoord X → Bool) (hb : Measurable b) :
      Measurable (fun z : DensityCoord X => bitMass (p z.2.2) (b z)) := by
    unfold bitMass
    apply Measurable.ite
    · exact hb (MeasurableSet.singleton true)
    · exact hp.comp (by fun_prop)
    · exact measurable_const.sub (hp.comp (by fun_prop))
  have hd : Measurable (density e q₀ q₁) := by
    unfold density tripleMass
    exact ENNReal.measurable_ofReal.comp
      (((hbit e he (fun z => z.1) (by fun_prop)).mul
        (hbit q₀ hq₀ (fun z => z.2.1.1) (by fun_prop))).mul
        (hbit q₁ hq₁ (fun z => z.2.1.2) (by fun_prop)))
  have hn (x : X) (a y₀ y₁ : Bool) :
      0 ≤ tripleMass (e x) (q₀ x) (q₁ x) a y₀ y₁ := by
    unfold tripleMass
    exact mul_nonneg (mul_nonneg (bitMass_nonneg _ (he01 x) _)
      (bitMass_nonneg _ (hq₀01 x) _)) (bitMass_nonneg _ (hq₁01 x) _)
  have hsum (x : X) :
      (∑ a : Bool, ∑ y₀ : Bool, ∑ y₁ : Bool,
        density e q₀ q₁ (a, ((y₀, y₁), x))) = 1 := by
    simp only [density]
    calc
      (∑ a : Bool, ∑ y₀ : Bool, ∑ y₁ : Bool,
          ENNReal.ofReal (tripleMass (e x) (q₀ x) (q₁ x) a y₀ y₁))
          = ∑ a : Bool, ∑ y₀ : Bool,
              ENNReal.ofReal (∑ y₁ : Bool, tripleMass (e x) (q₀ x) (q₁ x) a y₀ y₁) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro y₀ _
            exact (ENNReal.ofReal_sum_of_nonneg (fun y₁ _ => hn x a y₀ y₁)).symm
      _ = ∑ a : Bool, ENNReal.ofReal
            (∑ y₀ : Bool, ∑ y₁ : Bool, tripleMass (e x) (q₀ x) (q₁ x) a y₀ y₁) := by
          apply Finset.sum_congr rfl
          intro a _
          exact (ENNReal.ofReal_sum_of_nonneg (fun y₀ _ =>
            Finset.sum_nonneg fun y₁ _ => hn x a y₀ y₁)).symm
      _ = ENNReal.ofReal (∑ a : Bool, ∑ y₀ : Bool, ∑ y₁ : Bool,
            tripleMass (e x) (q₀ x) (q₁ x) a y₀ y₁) := by
          exact (ENNReal.ofReal_sum_of_nonneg (fun a _ =>
            Finset.sum_nonneg fun y₀ _ => Finset.sum_nonneg fun y₁ _ =>
              hn x a y₀ y₁)).symm
      _ = 1 := by rw [tripleMass_sum]; norm_num
  refine Measure.ext_of_lintegral μ (fun f hf => ?_)
  rw [lintegral_map hf (by fun_prop), densityLaw]
  rw [lintegral_withDensity_eq_lintegral_mul (reference μ) hd
    (show Measurable (fun z : DensityCoord X => f z.2.2) from hf.comp (by fun_prop))]
  change (∫⁻ z : DensityCoord X, density e q₀ q₁ z * f z.2.2 ∂reference μ) = _
  rw [reference, lintegral_prod_symm' _
    (show Measurable (fun z : DensityCoord X => density e q₀ q₁ z * f z.2.2) from
      hd.mul (hf.comp (by fun_prop)))]
  simp only [lintegral_count, tsum_fintype]
  rw [lintegral_prod_symm' _ (by fun_prop)]
  have hinner (x : X) :
      (∫⁻ z : Bool × Bool, ∑ a : Bool,
        (density e q₀ q₁ (a, (z, x)) * f x)
          ∂(Measure.count : Measure Bool).prod (Measure.count : Measure Bool)) =
        ∑ y₀ : Bool, ∑ y₁ : Bool, ∑ a : Bool,
          density e q₀ q₁ (a, ((y₀, y₁), x)) * f x := by
    rw [lintegral_prod _ (by exact (measurable_of_finite _).aemeasurable)]
    simp only [lintegral_count, tsum_fintype]
  calc
    _ = ∫⁻ x, (∑ y₀ : Bool, ∑ y₁ : Bool, ∑ a : Bool,
          density e q₀ q₁ (a, ((y₀, y₁), x)) * f x) ∂μ := by
        apply lintegral_congr
        intro x
        exact hinner x
    _ = ∫⁻ x, f x ∂μ := by
        apply lintegral_congr
        intro x
        simp_rw [← Finset.sum_mul]
        have hs : (∑ y₀ : Bool, ∑ y₁ : Bool, ∑ a : Bool,
            density e q₀ q₁ (a, ((y₀, y₁), x))) = 1 := by
          simp only [Fintype.sum_bool]
          have h := hsum x
          simp only [Fintype.sum_bool] at h
          convert h using 1; ac_rfl
        rw [hs, one_mul]

/-- [The base marginal of the public joint law equals `μ`](goal) for a
[probability base law `μ`](hyp:μ) when
[mark probabilities are measurable](hyp:he,hq₀,hq₁) and
[unit-interval valued](hyp:he01,hq₀01,hq₁01). -/
theorem jointLaw_base_marginal {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e q₀ q₁ : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (he01 : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    (hq₀01 : ∀ x, q₀ x ∈ Set.Icc (0 : ℝ) 1)
    (hq₁01 : ∀ x, q₁ x ∈ Set.Icc (0 : ℝ) 1) :
    (jointLaw μ e q₀ q₁).map (fun z : FullCoord X => z.1) = μ := by
  -- Compose the two measurable coordinate maps and apply
  -- `densityLaw_base_marginal`.
  unfold jointLaw
  rw [Measure.map_map (by fun_prop) (by unfold toFull; fun_prop)]
  change (densityLaw μ e q₀ q₁).map
    (fun z : DensityCoord X => z.2.2) = μ
  exact densityLaw_base_marginal μ e q₀ q₁ he hq₀ hq₁ he01 hq₀01 hq₁01

/-- [A measurable base support set of full `μ` mass also has full mass
under the joint law](goal), assuming [its measurability](hyp:hB),
[full base mass](hyp:hμB), [measurable marks](hyp:he,hq₀,hq₁), and
[unit-interval mark probabilities](hyp:he01,hq₀01,hq₁01). -/
theorem jointLaw_full_support {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e q₀ q₁ : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (he01 : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    (hq₀01 : ∀ x, q₀ x ∈ Set.Icc (0 : ℝ) 1)
    (hq₁01 : ∀ x, q₁ x ∈ Set.Icc (0 : ℝ) 1)
    (B : Set X) (hB : MeasurableSet B) (hμB : μ B = 1) :
    jointLaw μ e q₀ q₁ {z : FullCoord X | z.1 ∈ B} = 1 := by
  -- Evaluate `jointLaw_base_marginal` on `B` using `Measure.map_apply`.
  have hm := jointLaw_base_marginal μ e q₀ q₁
    he hq₀ hq₁ he01 hq₀01 hq₁01
  have h := congrArg (fun ν : Measure X => ν B) hm
  rw [Measure.map_apply (by fun_prop) hB] at h
  exact h.trans hμB

end Causalean.Mathlib.Probability.Kernel.ThreeBernoulli

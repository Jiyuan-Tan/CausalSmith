module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.CoordinateRegularity

/-! # Global Hölder modulus for calibrated supports

The roadmap's two-scale modulus argument turns a global Lipschitz bound and
an oscillation bound into the exact prescribed Hölder radius. It includes
exponent one and requires no derivative matching at cell endpoints.
-/
@[expose] public section
noncomputable section
open scoped ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Below unit scale, the linear modulus is bounded by every legal Hölder power;
above unit scale, the constant modulus is bounded by that power. [the documented result](goal) Under [the stated assumptions](hyp:hγ,hγ1). Under [the stated assumptions](hyp:hr). -/
-- @node: calibrated_two_scale_power
lemma calibrated_two_scale_power (r γ : ℝ) (hr : 0 ≤ r)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    min r 1 ≤ r ^ γ := by
  by_cases hsmall : r ≤ 1
  · rw [min_eq_left hsmall]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge' hr hsmall hγ.le hγ1
  · rw [min_eq_right (le_of_not_ge hsmall)]
    exact Real.one_le_rpow (le_of_not_ge hsmall) hγ.le

/-- A Lipschitz modulus at cell scale and a uniform oscillation modulus give an exponent-uniform Hölder bound after cancelling the rate-scaled amplitude. the documented result Under the stated assumptions. [The stated hypotheses](hyp:hk,hγ,hγ1,hlin,hamp) hold, and [the stated conclusion follows](goal). -/
-- @node: calibrated_holder_modulus
lemma calibrated_holder_modulus (f : Covariate → ℝ) (γ : ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlin : ∀ x z, |f x - f z| ≤ (k : ℝ) ^ (1-γ) * |(x : ℝ)-(z : ℝ)|)
    (hamp : ∀ x z, |f x - f z| ≤ 2 * (k : ℝ) ^ (-γ)) :
    holderSeminorm γ f ≤ 2 := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hknonneg := hkpos.le
  have hcancel : (k : ℝ) ^ (-γ) * (k : ℝ) ^ γ = 1 := by
    rw [← Real.rpow_add hkpos, neg_add_cancel, Real.rpow_zero]
  have hlinear : (k : ℝ) ^ (1-γ) = (k : ℝ) ^ (-γ) * (k : ℝ) := by
    calc
      (k : ℝ) ^ (1-γ) = (k : ℝ) ^ (-γ+1) := by congr 1; ring
      _ = (k : ℝ) ^ (-γ) * (k : ℝ) := by rw [Real.rpow_add hkpos, Real.rpow_one]
  have hmod : ∀ x z : Covariate,
      |f x-f z| ≤ 2 * |(x : ℝ)-(z : ℝ)| ^ γ := by
    intro x z
    let d : ℝ := |(x : ℝ)-(z : ℝ)|
    have hd : 0 ≤ d := abs_nonneg _
    have hscale : (k : ℝ) * d ≤ ((k : ℝ) * d) ^ γ ∨
        1 ≤ ((k : ℝ) * d) ^ γ := by
      by_cases hs : (k : ℝ) * d ≤ 1
      · left
        simpa [min_eq_left hs] using
          calibrated_two_scale_power ((k : ℝ)*d) γ (mul_nonneg hknonneg hd) hγ hγ1
      · right
        simpa [min_eq_right (le_of_not_ge hs)] using
          calibrated_two_scale_power ((k : ℝ)*d) γ (mul_nonneg hknonneg hd) hγ hγ1
    have hpow : (k : ℝ) ^ (-γ) * ((k : ℝ) * d) ^ γ = d ^ γ := by
      rw [Real.mul_rpow hknonneg hd, ← mul_assoc, hcancel, one_mul]
    rcases hscale with hs | hs
    · calc
        |f x-f z| ≤ (k : ℝ) ^ (1-γ) * d := hlin x z
        _ = (k : ℝ) ^ (-γ) * ((k : ℝ)*d) := by rw [hlinear]; ring
        _ ≤ (k : ℝ) ^ (-γ) * ((k : ℝ)*d) ^ γ :=
          mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hknonneg _)
        _ = d ^ γ := hpow
        _ ≤ 2 * d ^ γ := by nlinarith [Real.rpow_nonneg hd γ]
    · calc
        |f x-f z| ≤ 2 * (k : ℝ) ^ (-γ) := hamp x z
        _ ≤ 2 * (k : ℝ) ^ (-γ) * ((k : ℝ)*d) ^ γ :=
          le_mul_of_one_le_right (by positivity) hs
        _ = 2 * d ^ γ := by rw [mul_assoc, hpow]
  exact (holderSeminorm_le_of_pointwise γ 2 f hmod).trans (by norm_num)

/-- [Remaining construction obligations before applying the global modulus
argument: the five non-Hölder model properties and the two scale bounds for
each native logit. These are proof obligations, not additional model premises. -/
-- @node: CalibratedModelBounds
structure CalibratedModelBounds (α β : ℝ) (k : ℕ) (P : ObservedLaw) : Prop where
  uniform : UniformDesign P
  homogeneous : HomogeneousLogit P
  effect_envelope : EffectEnvelope P
  propensity_envelope : PropensityEnvelope P
  prognosis_envelope : PrognosisEnvelope P
  propensity_linear : ∀ x z, |propensityLogit P x-propensityLogit P z| ≤
    (k : ℝ) ^ (1-α) * |(x : ℝ)-(z : ℝ)|
  propensity_oscillation : ∀ x z, |propensityLogit P x-propensityLogit P z| ≤
    2 * (k : ℝ) ^ (-α)
  prognosis_linear : ∀ x z, |prognosisLogit P x-prognosisLogit P z| ≤
    (k : ℝ) ^ (1-β) * |(x : ℝ)-(z : ℝ)|
  prognosis_oscillation : ∀ x z, |prognosisLogit P x-prognosisLogit P z| ≤
    2 * (k : ℝ) ^ (-β)

/-- The two-scale native-logit bounds discharge both exact Hölder radii of
the paper model, uniformly over the public exponent domain. [the documented result](goal) Under [the stated assumptions](hyp:hab,hk,h). -/
-- @node: calibrated_model_of_bounds
lemma calibrated_model_of_bounds (α β : ℝ) (k : ℕ) (P : ObservedLaw)
    (hab : ExponentDomain α β) (hk : 1 ≤ k)
    (h : CalibratedModelBounds α β k P) : Model α β P := by
  refine ⟨h.uniform, h.homogeneous, h.effect_envelope, h.propensity_envelope,
    h.prognosis_envelope, ?_, ?_⟩
  · exact calibrated_holder_modulus _ α k hk (hab.1.trans hab.2.2.1) hab.2.2.2
      h.propensity_linear h.propensity_oscillation
  · exact calibrated_holder_modulus _ β k hk hab.1
      (hab.2.1.le.trans (by norm_num)) h.prognosis_linear h.prognosis_oscillation

end CausalSmith.Stat.LogoddsLowsmoothFrontier

module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.RiskBounds
public import Causalean.Stat.Minimax.ChiSquared

/-! # Information bounds for the lower experiments

A common independent randomizer preserves testing distance. Tensorization and
Cauchy–Schwarz convert a small row information budget into product separation.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory

/-- Appending the same independent probability law preserves total variation. -/
-- @node: lowerInformation_tv_prod_common
lemma lowerInformation_tv_prod_common {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ ν : Measure X) (ρ₀ : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ₀] :
    Causalean.Stat.tvDist (μ.prod ρ₀) (ν.prod ρ₀) = Causalean.Stat.tvDist μ ν := by
  apply le_antisymm
  · unfold Causalean.Stat.tvDist at ⊢
    refine ciSup_le fun A => ?_
    have hreal (ρ : Measure X) [IsProbabilityMeasure ρ] :
        (ρ.prod ρ₀).real A.1 = ∫ x, ρ₀.real (Prod.mk x ⁻¹' A.1) ∂ρ := by
      rw [measureReal_def, Measure.prod_apply A.2]
      symm
      exact integral_toReal (measurable_measure_prodMk_left A.2).aemeasurable
        (Filter.Eventually.of_forall fun x => measure_lt_top ρ₀ _)
    rw [hreal μ, hreal ν]
    simpa [Causalean.Stat.tvDist] using Causalean.Stat.tvDist_integral_range μ ν
      (fun x => ρ₀.real (Prod.mk x ⁻¹' A.1))
      ((measurable_measure_prodMk_left A.2).ennreal_toReal) 0 1 zero_le_one
      (fun x => ⟨measureReal_nonneg, by simpa using
        (measureReal_le_one : ρ₀.real (Prod.mk x ⁻¹' A.1) ≤ 1)⟩)
  · unfold Causalean.Stat.tvDist at ⊢
    refine ciSup_le fun A => ?_
    have h := Causalean.Stat.abs_measureReal_sub_le_tvDist
      (μ := μ.prod ρ₀) (ν := ν.prod ρ₀) (A.2.prod MeasurableSet.univ)
    simpa [measureReal_prod_prod, probReal_univ, Causalean.Stat.tvDist] using h

/-- The uniform randomizer leaves the observable sample testing distance unchanged. -/
-- @node: lowerInformation_experiment_tv
lemma lowerInformation_experiment_tv (P Q : RowLaw) (n : ℕ)
    (hP : WellFormed P) (hQ : WellFormed Q) :
    Causalean.Stat.tvDist (experiment P n) (experiment Q n) =
      Causalean.Stat.tvDist (sampleLaw P n) (sampleLaw Q n) := by
  haveI := sampleLaw_isProbability P n hP
  haveI := sampleLaw_isProbability Q n hQ
  haveI : IsProbabilityMeasure uniformRandomizer := by
    unfold uniformRandomizer
    constructor
    simp
  exact lowerInformation_tv_prod_common _ _ _

/-- Tensorization bounds product chi-square by the exponential row budget. -/
-- @node: lowerInformation_product_chi_bound
lemma lowerInformation_product_chi_bound {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν)
    (hint : Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1)^2) ν)
    (n : ℕ) (b : ℝ) (hb : (n:ℝ) * Causalean.Stat.chiSqDiv μ ν ≤ b) :
    Causalean.Stat.chiSqDiv (Measure.pi (fun _ : Fin n => μ))
      (Measure.pi (fun _ : Fin n => ν)) ≤ Real.exp b - 1 := by
  have he : (1 + Causalean.Stat.chiSqDiv μ ν)^n ≤ Real.exp b := by
    calc
      _ ≤ (Real.exp (Causalean.Stat.chiSqDiv μ ν))^n :=
        pow_le_pow_left₀ (by linarith [Causalean.Stat.chiSqDiv_nonneg (μ := μ) (ν := ν)])
          (by linarith [Real.add_one_le_exp (Causalean.Stat.chiSqDiv μ ν)]) n
      _ = Real.exp ((n:ℝ) * Causalean.Stat.chiSqDiv μ ν) := by
        rw [Real.exp_nat_mul]
      _ ≤ Real.exp b := Real.exp_le_exp.mpr hb
  rw [← Causalean.Stat.one_add_chiSqDiv_pi_iid_general μ ν hac hint n] at he
  linarith

/-- The public high-pair information budget makes the TV envelope strictly
less than one quarter, by the elementary exponential reciprocal bound. -/
-- @node: lowerInformation_small_tv_envelope
lemma lowerInformation_small_tv_envelope :
    (1/2:ℝ) * Real.sqrt (Real.exp (1/256) - 1) < 1/4 := by
  have he := Real.add_one_le_exp (-(1/256:ℝ))
  rw [Real.exp_neg] at he
  have hmul : (255/256:ℝ) * Real.exp (1/256) ≤ 1 := by
    apply (le_div_iff₀ (Real.exp_pos _)).mp
    rw [one_div]
    linarith
  have hbound : Real.exp (1/256) - 1 < (1/2:ℝ)^2 := by linarith
  have hs : Real.sqrt (Real.exp (1/256) - 1) < 1/2 :=
    (Real.sqrt_lt' (by norm_num)).2 hbound
  linarith

/-- A one-row chi-square budget of one 256th implies strict product-TV
separation, using the roadmap's tensorization and Cauchy–Schwarz steps. -/
-- @node: lowerInformation_product_tv_small
lemma lowerInformation_product_tv_small {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν)
    (hint : Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1)^2) ν)
    (n : ℕ) (hb : (n:ℝ) * Causalean.Stat.chiSqDiv μ ν ≤ 1/256) :
    Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => μ))
      (Measure.pi (fun _ : Fin n => ν)) < 1/4 := by
  have ht := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv
    (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => ν))
    (Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous
      μ ν hac n)
    (Causalean.Stat.pi_iid_integrable_sq_dev μ ν hac hint n)
  exact (ht.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (lowerInformation_product_chi_bound μ ν hac hint n (1/256) hb))
    (by norm_num))).trans_lt lowerInformation_small_tv_envelope

/-- A measurable treatment fraction in the unit interval has a two-point
loss floor of three eighths of the separation when testing TV is below one quarter. -/
-- @node: lowerInformation_block_loss_floor
lemma lowerInformation_block_loss_floor {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (d : X → ℝ) (hd : Measurable d) (hrange : ∀ x, d x ∈ Set.Icc (0:ℝ) 1)
    (K : ℝ) (hK : 0 ≤ K) (htv : Causalean.Stat.tvDist μ ν < 1/4) :
    (3/8:ℝ)*K ≤ max (K * (1 - ∫ x, d x ∂μ)) (K * ∫ x, d x ∂ν) := by
  have hgap := Causalean.Stat.tvDist_integral_range μ ν d hd 0 1
    zero_le_one (by simpa using hrange)
  have hdiff : (∫ x, d x ∂μ) - (∫ x, d x ∂ν) ≤
      Causalean.Stat.tvDist μ ν := by
    simpa only [mul_one] using (le_abs_self _).trans hgap
  have hsum : (3/4:ℝ)*K ≤ K * (1 - ∫ x, d x ∂μ) + K * ∫ x, d x ∂ν := by
    have h := mul_le_mul_of_nonneg_left
      (show (3/4:ℝ) ≤ 1 - ((∫ x, d x ∂μ) - ∫ x, d x ∂ν) by linarith) hK
    nlinarith
  have hp := le_max_left (K * (1 - ∫ x, d x ∂μ)) (K * ∫ x, d x ∂ν)
  have hn := le_max_right (K * (1 - ∫ x, d x ∂μ)) (K * ∫ x, d x ∂ν)
  linarith

/-- Nonnegative losses separated pointwise have the high-pair testing floor.
Clipping the second loss at the separation scale produces the bounded statistic
used by the total-variation comparison. -/
-- @node: lowerInformation_separated_loss_floor
lemma lowerInformation_separated_loss_floor {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g ν)
    (hgm : Measurable g) (hf0 : ∀ w, 0 ≤ f w) (hg0 : ∀ w, 0 ≤ g w)
    (K : ℝ) (hK : 0 < K) (hsep : ∀ w, K ≤ f w + g w)
    (htv : Causalean.Stat.tvDist μ ν < 1/4) :
    (3/8:ℝ)*K ≤ max (∫ w, f w ∂μ) (∫ w, g w ∂ν) := by
  let d : Ω → ℝ := fun w => min (g w / K) 1
  have hd : Measurable d := by
    fun_prop
  have hr : ∀ w, d w ∈ Set.Icc (0:ℝ) 1 := by
    intro w
    exact ⟨le_min (div_nonneg (hg0 w) hK.le) zero_le_one, min_le_right _ _⟩
  have hid (ρ : Measure Ω) [IsProbabilityMeasure ρ] : Integrable d ρ := by
    apply Integrable.of_bound hd.aestronglyMeasurable 1
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (hr w).1]
    exact (hr w).2
  have hp : K * (1 - ∫ w, d w ∂μ) ≤ ∫ w, f w ∂μ := by
    have hi : Integrable (fun w => K * (1 - d w)) μ :=
      ((integrable_const 1).sub (hid μ)).const_mul K
    have hb : ∀ w, K * (1 - d w) ≤ f w := by
      intro w
      by_cases h : g w / K ≤ 1
      · dsimp [d]
        rw [min_eq_left h]
        have he : K * (g w / K) = g w := by field_simp
        nlinarith [hsep w]
      · dsimp [d]
        rw [min_eq_right (le_of_not_ge h)]
        simpa using hf0 w
    have hb' := integral_mono hi hf hb
    simpa only [integral_const_mul, integral_sub (integrable_const 1) (hid μ),
      integral_const, probReal_univ, smul_eq_mul, one_mul] using hb'
  have hn : K * (∫ w, d w ∂ν) ≤ ∫ w, g w ∂ν := by
    have hi := (hid ν).const_mul K
    have hb : ∀ w, K * d w ≤ g w := by
      intro w
      calc
        K * d w ≤ K * (g w / K) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hK.le
        _ = g w := by field_simp
    simpa only [integral_const_mul] using integral_mono hi hg hb
  exact (lowerInformation_block_loss_floor μ ν d hd hr K hK.le htv).trans
    (max_le_max hp hn)

end CausalSmith.Stat.ScorethresholdOverlapRegret

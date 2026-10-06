module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.CosineRegularity
public import Causalean.Stat.Minimax.Mixture.Iid
/-! Exact iid likelihood-overlap expansion of the shared-sign mixture and its reduction
to a finite exponential average. All domination and integrability conditions are derived. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- Every observed causal law is a probability measure.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:P). -/
-- @node: observed_probability
lemma observed_probability (P : CausalLaw) : IsProbabilityMeasure (Pobs P) := by
  have hm : Measurable observe := by unfold observe X A Y; fun_prop
  exact Measure.isProbabilityMeasure_map hm.aemeasurable

/-- The finite sign weight is the reciprocal of the number of sign vectors. The result uses [the stated assumptions](hyp:hL) and establishes [the displayed conclusion](goal). -/
-- @node: sign_weight_eq_inv_card
lemma sign_weight_eq_inv_card (hL : ℝ) :
    ENNReal.ofReal ((2 : ℝ)^(-((activeSigns hL).card : ℤ))) =
      (Fintype.card (SignVector hL) : ℝ≥0∞)⁻¹ := by
  classical
  have hc : (Fintype.card (SignVector hL) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    _ = ENNReal.ofReal ((2 : ℝ)^(-((activeSigns hL).card : ℤ))) *
        ((Fintype.card (SignVector hL) : ℝ≥0∞) *
          (Fintype.card (SignVector hL) : ℝ≥0∞)⁻¹) := by
      rw [ENNReal.mul_inv_cancel hc (by simp), mul_one]
    _ = _ := by rw [← mul_assoc, sign_weight_normalization, one_mul]

/-- The dataset sign mixture is exactly the library's uniform finite iid mixture.  [the theorem's stated inputs and assumptions](hyp:n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: signMixture_eq_uniformMixture
lemma signMixture_eq_uniformMixture (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) :
    signMixture hL hhL n = Causalean.Stat.Minimax.Mixture.uniformMixture
      (fun lam : SignVector hL => Measure.pi
        (fun _ : Fin n => Pobs (cosineFamily hL hhL lam))) := by
  classical
  simp only [signMixture, sign_weight_eq_inv_card, dataLaw,
    Causalean.Stat.Minimax.Mixture.uniformMixture, Causalean.Stat.mixture,
    Finset.smul_sum]

/-- Finite domination bounds the real density under the reference measure.  [the theorem's stated inputs and assumptions](hyp:μ,ν,c,hc0,hct,hle), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:α). -/
-- @node: rnDeriv_toReal_le_of_domination
lemma rnDeriv_toReal_le_of_domination {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure ν] (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hct : c ≠ ∞) (hle : μ ≤ c • ν) :
    ∀ᵐ z ∂ν, (μ.rnDeriv ν z).toReal ≤ c.toReal := by
  letI : IsFiniteMeasure (c • ν) := Measure.smul_finite ν hct
  letI : IsFiniteMeasure μ := isFiniteMeasure_of_le (c • ν) hle
  have hsmall : μ.rnDeriv (c • ν) ≤ᵐ[ν] 1 :=
    (Measure.absolutelyContinuous_smul hc0).ae_le (Measure.rnDeriv_le_one_of_le hle)
  filter_upwards [hsmall, Measure.rnDeriv_smul_right_of_ne_top μ ν hc0 hct] with z hz hs
  rw [hs, Pi.smul_apply, smul_eq_mul] at hz
  apply ENNReal.toReal_mono hct
  calc
    _ = c * (c⁻¹ * μ.rnDeriv ν z) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hct, one_mul]
    _ ≤ c * 1 := mul_le_mul' le_rfl hz
    _ = c := mul_one _

/-- Products of the alternative one-record densities are integrable, with bound sixty-four.  [the theorem's stated inputs and assumptions](hyp:hhL,lam,lam'), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: cosineFamily_density_pair_integrable
lemma cosineFamily_density_pair_integrable (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (lam lam' : SignVector hL) :
    Integrable (fun z => ((Pobs (cosineFamily hL hhL lam)).rnDeriv (Pobs fairNull) z).toReal *
      ((Pobs (cosineFamily hL hhL lam')).rnDeriv (Pobs fairNull) z).toReal)
      (Pobs fairNull) := by
  letI := observed_probability fairNull
  have hb (l : SignVector hL) := rnDeriv_toReal_le_of_domination
    (Pobs (cosineFamily hL hhL l)) (Pobs fairNull) 8 (by norm_num) (by norm_num)
    (cosineFamily_observed_domination hL hhL l)
  apply Integrable.of_mem_Icc 0 64 (by fun_prop)
  filter_upwards [hb lam, hb lam'] with z hz hz'
  norm_num at hz hz'
  exact ⟨mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    (mul_le_mul hz hz' ENNReal.toReal_nonneg (by norm_num)).trans (by norm_num)⟩

/-- The one-record density overlap is the nonnegative likelihood inner product. -/
-- @node: signDensityOverlap
def signDensityOverlap (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam lam' : SignVector hL) : ℝ :=
  ∫ z, ((Pobs (cosineFamily hL hhL lam)).rnDeriv (Pobs fairNull) z).toReal *
    ((Pobs (cosineFamily hL hhL lam')).rnDeriv (Pobs fairNull) z).toReal ∂Pobs fairNull

/-- Each one-record density overlap is nonnegative.  [the theorem's stated inputs and assumptions](hyp:lam,lam'), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: signDensityOverlap_nonneg
lemma signDensityOverlap_nonneg (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam lam' : SignVector hL) : 0 ≤ signDensityOverlap hL hhL lam lam' := by
  exact integral_nonneg (fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

/-- One plus the dataset mixture divergence is exactly the uniform average of nth powers
of one-record overlaps; the iid product and finite-mixture identities come from Causalean.  [the theorem's stated inputs and assumptions](hyp:n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: signMixture_chiSq_overlap_identity
lemma signMixture_chiSq_overlap_identity (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) :
    1 + Causalean.Stat.chiSqDiv (signMixture hL hhL n) (dataLaw n fairNull) =
      (∑ lam : SignVector hL, ∑ lam' : SignVector hL,
        (signDensityOverlap hL hhL lam lam')^n) /
          (Fintype.card (SignVector hL) : ℝ)^2 := by
  letI (P : CausalLaw) := observed_probability P
  rw [signMixture_eq_uniformMixture]
  exact Causalean.Stat.Minimax.Mixture.one_add_chiSqDiv_uniformMixture_iid
    (fun lam : SignVector hL => Pobs (cosineFamily hL hhL lam)) (Pobs fairNull)
    (fun lam => Measure.absolutelyContinuous_of_le_smul
      (cosineFamily_observed_domination hL hhL lam))
    (cosineFamily_density_pair_integrable hL hhL) n

/-- Nonnegative likelihood overlaps raised to n are dominated by the exponential of
the centered overlap times n, as used in the fixed-sample roadmap.  [the theorem's stated inputs and assumptions](hyp:n,lam,lam'), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: signDensityOverlap_pow_le_exp
lemma signDensityOverlap_pow_le_exp (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (lam lam' : SignVector hL) :
    (signDensityOverlap hL hhL lam lam')^n ≤
      Real.exp ((n : ℝ)*(signDensityOverlap hL hhL lam lam'-1)) := by
  have hb : signDensityOverlap hL hhL lam lam' ≤
      Real.exp (signDensityOverlap hL hhL lam lam'-1) := by
    simpa using Real.add_one_le_exp (signDensityOverlap hL hhL lam lam'-1)
  calc
    _ ≤ (Real.exp (signDensityOverlap hL hhL lam lam'-1))^n :=
      pow_le_pow_left₀ (signDensityOverlap_nonneg hL hhL lam lam') hb n
    _ = _ := by rw [← Real.exp_nat_mul]

/-- The exact iid mixture identity reduces its divergence bound to a finite exponential
average, without any additional integrability or absolute-continuity assumptions.  [the theorem's stated inputs and assumptions](hyp:n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: signMixture_chiSq_le_exp_average
lemma signMixture_chiSq_le_exp_average (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) :
    1 + Causalean.Stat.chiSqDiv (signMixture hL hhL n) (dataLaw n fairNull) ≤
      (∑ lam : SignVector hL, ∑ lam' : SignVector hL,
        Real.exp ((n : ℝ)*(signDensityOverlap hL hhL lam lam'-1))) /
          (Fintype.card (SignVector hL) : ℝ)^2 := by
  rw [signMixture_chiSq_overlap_identity]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact Finset.sum_le_sum (fun lam _ => Finset.sum_le_sum
    (fun lam' _ => signDensityOverlap_pow_le_exp hL hhL n lam lam'))

/-- The centered conditional likelihood inner product in the paper's Fourier expansion. -/
-- @node: signOverlapIntegrand
def signOverlapIntegrand (hL : ℝ) (lam lam' : SignVector hL) (x : Covariate) : ℝ :=
  separation hL * (1 + (separation hL*bump hL x-1)^2) *
    perturbation hL lam x * perturbation hL lam' x +
  (separation hL)^2 * (bump hL x-(perturbation hL lam x)^2) *
    (bump hL x-(perturbation hL lam' x)^2)

/-- Orthogonality of the four fair marks leaves exactly the two terms of the
centered overlap integrand, pointwise in the covariate.  [the theorem's stated inputs and assumptions](hyp:hhL,lam,lam',x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: conditionalLikelihood_pair_inner_product
lemma conditionalLikelihood_pair_inner_product (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (lam lam' : SignVector hL) (x : Covariate) :
    (∑ av : Bool, ∑ yv : Bool,
      conditionalLikelihood hL lam x av yv * conditionalLikelihood hL lam' x av yv) / 4 =
        1 + signOverlapIntegrand hL lam lam' x := by
  have ht : 0 ≤ separation hL := (separation_le_sqrt hL hhL).1
  simp_rw [conditionalLikelihood_fourier hL hhL]
  simp only [Fintype.sum_bool, bit, if_true, Bool.false_eq_true, if_false]
  dsimp [signOverlapIntegrand]
  ring_nf
  rw [Real.sq_sqrt ht]
  ring

/-- The centered overlap integrand is Borel measurable in the covariate. The result uses [the stated assumptions](hyp:hL) and establishes [the displayed conclusion](goal). -/
-- @node: measurable_signOverlapIntegrand
@[fun_prop] lemma measurable_signOverlapIntegrand (hL : ℝ)
    (lam lam' : SignVector hL) : Measurable (signOverlapIntegrand hL lam lam') := by
  unfold signOverlapIntegrand
  fun_prop

/-- The finite sign second moment is exactly the number of signs times the bump,
including macro endpoints and lattice boundaries.  [the theorem's stated inputs and assumptions](hyp:x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: perturbation_sign_square_sum_exact
lemma perturbation_sign_square_sum_exact (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (x : Covariate) :
    (∑ lam : SignVector hL, (perturbation hL lam x)^2) =
      (Fintype.card (SignVector hL) : ℝ)*bump hL x := by
  rw [perturbation_sign_square_sum, weighted_frame_square_partition hL hhL]

/-- Averaging the centered integrand over the first sign vector gives zero for every
fixed second sign vector and every covariate, exactly as required by the mgf step.  [the theorem's stated inputs and assumptions](hyp:lam',x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: signOverlapIntegrand_sign_sum
lemma signOverlapIntegrand_sign_sum (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam' : SignVector hL) (x : Covariate) :
    (∑ lam : SignVector hL, signOverlapIntegrand hL lam lam' x) = 0 := by
  classical
  simp only [signOverlapIntegrand, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_sub_distrib, perturbation_sign_sum,
    perturbation_sign_square_sum_exact hL hhL, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

/-- The actual sign probability law gives the centered integrand mean zero pointwise.  [the theorem's stated inputs and assumptions](hyp:lam',x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: signOverlapIntegrand_sign_mean
lemma signOverlapIntegrand_sign_mean (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam' : SignVector hL) (x : Covariate) :
    (∫ lam, signOverlapIntegrand hL lam lam' x ∂signLaw hL) = 0 := by
  rw [integral_signLaw, signOverlapIntegrand_sign_sum hL hhL, mul_zero]

/-- The fair observed null integrates four equally weighted mark cells at each covariate.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:f,hf). -/
-- @node: fairNull_lintegral_marks
lemma fairNull_lintegral_marks (f : O → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂Pobs fairNull) =
      ∫⁻ x : Covariate, ∑ av : Bool, ∑ yv : Bool, (1 / 4 : ℝ≥0∞)*f (x,av,yv) := by
  have hm : Measurable observe := by unfold observe X A Y; fun_prop
  change (∫⁻ z, f z ∂(binaryLaw (fun _ => 1/2) (fun _ => 1/2)
    (fun _ => 1/2)).map observe) = _
  rw [lintegral_map hf hm, binaryLaw_lintegral (fun _ => 1/2) (fun _ => 1/2) (fun _ => 1/2) measurable_const
    measurable_const measurable_const (fun z => f (observe z)) (hf.comp hm)]
  apply lintegral_congr
  intro x
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Function.comp_apply,
    observe, X, A, Y, bernoulliMass, Bool.false_eq_true, if_false, if_true]
  norm_num [ENNReal.ofReal_div_of_pos]
  have hc : (8 : ℝ≥0∞)⁻¹ * 2 = 4⁻¹ := by
    rw [show (8 : ℝ≥0∞) = 4*2 by norm_num, ENNReal.mul_inv, mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one] <;> norm_num
  ring_nf
  simp only [mul_right_comm _ _ (2 : ℝ≥0∞), hc]
  ring

/-- The actual conditional likelihood is measurable on the full observed record space. The result uses [the stated assumptions](hyp:hL) and establishes [the displayed conclusion](goal). -/
-- @node: measurable_conditionalLikelihood_record
@[fun_prop] lemma measurable_conditionalLikelihood_record (hL : ℝ) (lam : SignVector hL) :
    Measurable (fun z : O => conditionalLikelihood hL lam z.1 z.2.1 z.2.2) := by
  have ha : MeasurableSet {z : O | z.2.1 = true} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hy : MeasurableSet {z : O | z.2.2 = true} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have he : Measurable (fun z : O => altE hL lam z.1) := by fun_prop
  have h0 : Measurable (fun z : O => altMu0 hL lam z.1) := by fun_prop
  have h1 : Measurable (fun z : O => altMu1 hL lam z.1) := by fun_prop
  classical
  have hm : Measurable (fun z : O => if z.2.1 then altMu1 hL lam z.1 else altMu0 hL lam z.1) := h1.ite ha h0
  exact (measurable_const.mul (he.ite ha (measurable_const.sub he))).mul
    (hm.ite hy (measurable_const.sub hm))

/-- Every actual conditional mark likelihood is nonnegative for legal macro radii.  [the theorem's stated inputs and assumptions](hyp:lam,x,av,yv), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: conditionalLikelihood_nonneg
lemma conditionalLikelihood_nonneg (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam : SignVector hL) (x : Covariate) (av yv : Bool) :
    0 ≤ conditionalLikelihood hL lam x av yv := by
  unfold conditionalLikelihood
  apply mul_nonneg (mul_nonneg (by norm_num)
    (bernoulliMass_nonneg (alt_parameters_range hL hhL lam x).1 av))
  cases av
  · exact bernoulliMass_nonneg (alt_parameters_range hL hhL lam x).2.1 yv
  · exact bernoulliMass_nonneg (alt_parameters_range hL hhL lam x).2.2 yv

/-- The conditional four-cell likelihood is the actual observed density relative to the fair null.  [the theorem's stated inputs and assumptions](hyp:lam), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: cosineFamily_observed_withDensity
lemma cosineFamily_observed_withDensity (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam : SignVector hL) :
    Pobs (cosineFamily hL hhL lam) = (Pobs fairNull).withDensity
      (fun z => ENNReal.ofReal (conditionalLikelihood hL lam z.1 z.2.1 z.2.2)) := by
  classical
  ext s hs
  rw [cosineFamily, binaryCausalLaw_observed_apply _ _ _
    (measurable_altE hL lam) (measurable_altMu0 hL lam) (measurable_altMu1 hL lam)
    (alt_parameters_range hL hhL lam) s hs, withDensity_apply _ hs,
    ← lintegral_indicator hs]
  rw [fairNull_lintegral_marks _
    (((measurable_conditionalLikelihood_record hL lam).ennreal_ofReal).indicator hs)]
  apply lintegral_congr
  intro x
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro av hav
  apply Finset.sum_congr rfl
  intro yv hyv
  by_cases hx : (x,av,yv) ∈ s
  · simp only [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    rw [conditionalLikelihood, mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [ENNReal.ofReal_ofNat, ← mul_assoc]
    norm_num
    rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  · simp [Set.indicator_of_notMem hx]

/-- The real observed density is the stated likelihood almost everywhere under the null.  [the theorem's stated inputs and assumptions](hyp:lam), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: cosineFamily_rnDeriv_toReal_likelihood
lemma cosineFamily_rnDeriv_toReal_likelihood (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam : SignVector hL) :
    (fun z => ((Pobs (cosineFamily hL hhL lam)).rnDeriv (Pobs fairNull) z).toReal)
      =ᵐ[Pobs fairNull] (fun z => conditionalLikelihood hL lam z.1 z.2.1 z.2.2) := by
  letI := observed_probability fairNull
  rw [cosineFamily_observed_withDensity]
  filter_upwards [Measure.rnDeriv_withDensity (Pobs fairNull)
    (measurable_conditionalLikelihood_record hL lam).ennreal_ofReal] with z hz
  rw [hz, ENNReal.toReal_ofReal (conditionalLikelihood_nonneg hL hhL lam z.1 z.2.1 z.2.2)]

/-- Nonnegative real functions under the fair null integrate their four-cell average.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:f,hf,hf0). -/
-- @node: fairNull_integral_marks
lemma fairNull_integral_marks (f : O → ℝ) (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z) :
    (∫ z, f z ∂Pobs fairNull) =
      ∫ x : Covariate, (∑ av : Bool, ∑ yv : Bool, f (x,av,yv)) / 4 := by
  have hm : Measurable (fun x : Covariate => (∑ av : Bool, ∑ yv : Bool, f (x,av,yv)) / 4) := by
    apply Measurable.div_const
    apply Finset.measurable_fun_sum
    intro av hav
    apply Finset.measurable_fun_sum
    intro yv hyv
    exact hf.comp (by fun_prop)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable,
    fairNull_lintegral_marks _ hf.ennreal_ofReal]
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun x => div_nonneg
      (Finset.sum_nonneg (fun av _ => Finset.sum_nonneg (fun yv _ => hf0 (x,av,yv))))
      (by norm_num))) hm.aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4), ENNReal.ofReal_ofNat]
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun av _ => Finset.sum_nonneg (fun yv _ => hf0 (x,av,yv)))]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun yv _ => hf0 (x,_,yv))]
  simp only [div_eq_mul_inv, Finset.sum_mul, one_mul, mul_comm]
  simp only [Finset.mul_sum]

/-- Each actual conditional likelihood is at most four, since a Bernoulli cell mass
is a product of two probabilities at most one.  [the theorem's stated inputs and assumptions](hyp:lam,x,av,yv), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: conditionalLikelihood_le_four
lemma conditionalLikelihood_le_four (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam : SignVector hL) (x : Covariate) (av yv : Bool) :
    conditionalLikelihood hL lam x av yv ≤ 4 := by
  have hb (p : ℝ) (hp : p ∈ Icc 0 1) (b : Bool) : bernoulliMass p b ≤ 1 := by
    cases b <;> simp only [bernoulliMass, Bool.false_eq_true, if_false, if_true] <;>
      linarith [hp.1, hp.2]
  have hm : (if av then altMu1 hL lam x else altMu0 hL lam x) ∈ Icc 0 1 := by
    cases av
    · exact (alt_parameters_range hL hhL lam x).2.1
    · exact (alt_parameters_range hL hhL lam x).2.2
  have hprod := mul_le_one₀ (hb _ (alt_parameters_range hL hhL lam x).1 av)
    (bernoulliMass_nonneg hm yv) (hb _ hm yv)
  unfold conditionalLikelihood
  rw [mul_assoc]
  linarith

/-- The centered Fourier overlap integrand lies between minus one and fifteen.  [the theorem's stated inputs and assumptions](hyp:lam,lam',x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: signOverlapIntegrand_range
lemma signOverlapIntegrand_range (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam lam' : SignVector hL) (x : Covariate) :
    signOverlapIntegrand hL lam lam' x ∈ Icc (-1) 15 := by
  have hp (av yv : Bool) :
      0 ≤ conditionalLikelihood hL lam x av yv * conditionalLikelihood hL lam' x av yv ∧
      conditionalLikelihood hL lam x av yv * conditionalLikelihood hL lam' x av yv ≤ 16 := by
    exact ⟨mul_nonneg (conditionalLikelihood_nonneg hL hhL lam x av yv)
      (conditionalLikelihood_nonneg hL hhL lam' x av yv),
      (mul_le_mul (conditionalLikelihood_le_four hL hhL lam x av yv)
        (conditionalLikelihood_le_four hL hhL lam' x av yv)
        (conditionalLikelihood_nonneg hL hhL lam' x av yv) (by norm_num)).trans
          (by norm_num)⟩
  have hl := Finset.sum_nonneg (s := Finset.univ)
    (fun av _ => Finset.sum_nonneg (s := Finset.univ) (fun yv _ => (hp av yv).1))
  have hu := Finset.sum_le_sum (s := Finset.univ)
    (fun av _ => Finset.sum_le_sum (s := Finset.univ) (fun yv _ => (hp av yv).2))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul] at hu
  have hu' : (∑ av : Bool, ∑ yv : Bool,
      conditionalLikelihood hL lam x av yv * conditionalLikelihood hL lam' x av yv) ≤ 64 :=
    hu.trans (by norm_num)
  have he := conditionalLikelihood_pair_inner_product hL hhL lam lam' x
  constructor <;> linarith [hu']

/-- The covariate overlap integral is integrable by its measurable bounded construction. The result uses [the stated assumptions](hyp:hL,hhL) and establishes [the displayed conclusion](goal). -/
-- @node: integrable_signOverlapIntegrand
@[fun_prop] lemma integrable_signOverlapIntegrand (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam lam' : SignVector hL) : Integrable (signOverlapIntegrand hL lam lam') := by
  exact Integrable.of_mem_Icc (-1) 15 (by fun_prop)
    (ae_of_all _ (signOverlapIntegrand_range hL hhL lam lam'))

/-- The paper's centered likelihood inner product integrates the Fourier overlap terms. -/
-- @node: signOverlap
def signOverlap (hL : ℝ) (lam lam' : SignVector hL) : ℝ :=
  ∫ x : Covariate, signOverlapIntegrand hL lam lam' x

/-- The observed density overlap equals one plus the explicit Fourier covariate integral.  [the theorem's stated inputs and assumptions](hyp:lam,lam'), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: signDensityOverlap_eq_one_add_signOverlap
lemma signDensityOverlap_eq_one_add_signOverlap (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam lam' : SignVector hL) :
    signDensityOverlap hL hhL lam lam' = 1 + signOverlap hL lam lam' := by
  unfold signDensityOverlap
  have he : (fun z =>
      ((Pobs (cosineFamily hL hhL lam)).rnDeriv (Pobs fairNull) z).toReal *
      ((Pobs (cosineFamily hL hhL lam')).rnDeriv (Pobs fairNull) z).toReal) =ᵐ[Pobs fairNull]
      (fun z => conditionalLikelihood hL lam z.1 z.2.1 z.2.2 *
        conditionalLikelihood hL lam' z.1 z.2.1 z.2.2) := by
    filter_upwards [cosineFamily_rnDeriv_toReal_likelihood hL hhL lam,
      cosineFamily_rnDeriv_toReal_likelihood hL hhL lam'] with z hz hz'
    rw [hz, hz']
  rw [integral_congr_ae he]
  rw [fairNull_integral_marks _ (by fun_prop)
    (fun z => mul_nonneg (conditionalLikelihood_nonneg hL hhL lam z.1 z.2.1 z.2.2)
      (conditionalLikelihood_nonneg hL hhL lam' z.1 z.2.1 z.2.2))]
  simp_rw [conditionalLikelihood_pair_inner_product hL hhL]
  rw [integral_add (integrable_const 1) (integrable_signOverlapIntegrand hL hhL lam lam')]
  simp [signOverlap]

/-- Finite averaging commutes with the bounded covariate integrals; the centered overlap
has sum zero in its first sign vector for every fixed second vector.  [the theorem's stated inputs and assumptions](hyp:lam'), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: signOverlap_sign_sum
lemma signOverlap_sign_sum (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam' : SignVector hL) : (∑ lam : SignVector hL, signOverlap hL lam lam') = 0 := by
  classical
  unfold signOverlap
  rw [← integral_finsetSum _ (fun lam _ => integrable_signOverlapIntegrand hL hhL lam lam')]
  simp_rw [signOverlapIntegrand_sign_sum hL hhL lam']
  simp

/-- The centered likelihood overlap has expectation zero under the actual sign law.  [the theorem's stated inputs and assumptions](hyp:lam'), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: signOverlap_sign_mean
lemma signOverlap_sign_mean (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam' : SignVector hL) : (∫ lam, signOverlap hL lam lam' ∂signLaw hL) = 0 := by
  rw [integral_signLaw, signOverlap_sign_sum hL hhL, mul_zero]

/-- The exact fixed-sample chi-square identity uses the paper's centered Fourier overlap.  [the theorem's stated inputs and assumptions](hyp:n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: signMixture_chiSq_fourier_identity
lemma signMixture_chiSq_fourier_identity (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) :
    1 + Causalean.Stat.chiSqDiv (signMixture hL hhL n) (dataLaw n fairNull) =
      (∑ lam : SignVector hL, ∑ lam' : SignVector hL,
        (1 + signOverlap hL lam lam')^n) /
          (Fintype.card (SignVector hL) : ℝ)^2 := by
  rw [signMixture_chiSq_overlap_identity]
  simp_rw [signDensityOverlap_eq_one_add_signOverlap hL hhL]

/-- The dataset divergence is bounded by the uniform exponential average of the explicit
centered Fourier overlap; only the bounded-differences estimate remains to be assembled.  [the theorem's stated inputs and assumptions](hyp:hhL,n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: signMixture_chiSq_le_fourier_exp_average
lemma signMixture_chiSq_le_fourier_exp_average (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ) :
    1 + Causalean.Stat.chiSqDiv (signMixture hL hhL n) (dataLaw n fairNull) ≤
      (∑ lam : SignVector hL, ∑ lam' : SignVector hL,
        Real.exp ((n : ℝ)*signOverlap hL lam lam')) /
          (Fintype.card (SignVector hL) : ℝ)^2 := by
  have hb := signMixture_chiSq_le_exp_average hL hhL n
  simpa only [signDensityOverlap_eq_one_add_signOverlap hL hhL,
    add_sub_cancel_left] using hb

end CausalSmith.Stat.PrivateCateRoughdesign

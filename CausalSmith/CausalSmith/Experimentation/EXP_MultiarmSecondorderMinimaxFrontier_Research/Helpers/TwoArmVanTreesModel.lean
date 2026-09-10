import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmSmoothModel

/-!
Regularized likelihood identities for the smooth two-arm van Trees model.

The clamp only controls the likelihood outside the ambient parameter interval;
inside `(-1,1)` the model and its derivative are exactly the Bernoulli product
likelihood used by the paper.
-/

open scoped BigOperators
open Finset Set MeasureTheory

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

open Causalean.Stat.Limit.ObservationDependentVanTrees

-- @node: twoArmRegularBernoulliLikelihood
/-- The Bernoulli product likelihood with its scalar parameter clamped to `[-1,1]`. -/
noncomputable def twoArmRegularBernoulliLikelihood {n : ℕ} (θ : ℝ)
    (s : Unit n → Bool) : ℝ :=
  twoArmBernoulliLikelihood (twoArmClampedParameter 2 θ) s

-- @node: twoArmRegularBernoulliLikelihood_eq
/-- [the parameter lies in the stated interior interval](hyp:hθ), [In the regular Bernoulli region the clamped likelihood is the ordinary product likelihood.](goal) -/
lemma twoArmRegularBernoulliLikelihood_eq {n : ℕ} {θ : ℝ} (hθ : |θ| ≤ 1)
    (s : Unit n → Bool) :
    twoArmRegularBernoulliLikelihood θ s = twoArmBernoulliLikelihood θ s := by
  rw [twoArmRegularBernoulliLikelihood,
    twoArmClampedParameter_eq (by simpa using hθ)]

-- @node: twoArmRegularBernoulliLikelihood_nonneg
/-- [The regularized product likelihood is nonnegative for every real parameter.](goal) -/
lemma twoArmRegularBernoulliLikelihood_nonneg {n : ℕ} (θ : ℝ)
    (s : Unit n → Bool) : 0 ≤ twoArmRegularBernoulliLikelihood θ s := by
  rw [twoArmRegularBernoulliLikelihood]
  exact twoArmBernoulliLikelihood_nonneg (by
    simpa using twoArmClampedParameter_abs_le (a := (2 : ℝ))
      (θ := θ) (by norm_num)) s

-- @node: twoArmRegularBernoulliLikelihood_sum
/-- [the parameter lies in the stated interior interval](hyp:hθ), [In the regular region the finite likelihood masses sum to one.](goal) -/
lemma twoArmRegularBernoulliLikelihood_sum {n : ℕ} {θ : ℝ} (hθ : |θ| ≤ 1) :
    ∑ s : Unit n → Bool, twoArmRegularBernoulliLikelihood θ s = 1 := by
  simp_rw [twoArmRegularBernoulliLikelihood_eq hθ]
  exact twoArmBernoulliLikelihood_sum hθ

-- @node: twoArmRegularBernoulliLikelihood_integral_eq_one
/-- [the parameter lies in the stated interior interval](hyp:hθ), [In the regular region the likelihood has unit mass under counting measure.](goal) -/
lemma twoArmRegularBernoulliLikelihood_integral_eq_one {n : ℕ} {θ : ℝ}
    (hθ : |θ| ≤ 1) :
    ∫ s : Unit n → Bool, twoArmRegularBernoulliLikelihood θ s ∂Measure.count = 1 := by
  exact finite_likelihood_normalization (twoArmRegularBernoulliLikelihood_sum hθ)

-- @node: twoArmRegularBernoulliLikelihood_integrable_count
/-- [Every section of the finite regularized likelihood is counting-measure integrable.](goal) -/
lemma twoArmRegularBernoulliLikelihood_integrable_count {n : ℕ} (θ : ℝ) :
    Integrable (twoArmRegularBernoulliLikelihood (n := n) θ) Measure.count := by
  rw [integrable_count_iff]
  apply summable_of_hasFiniteSupport
  exact Set.toFinite _

-- @node: twoArmBernoulliLikelihoodDeriv_integrable_count
/-- [Every section of the displayed finite likelihood derivative is counting-measure integrable.](goal) -/
lemma twoArmBernoulliLikelihoodDeriv_integrable_count {n : ℕ} (θ : ℝ) :
    Integrable (twoArmBernoulliLikelihoodDeriv (n := n) θ) Measure.count := by
  rw [integrable_count_iff]
  apply summable_of_hasFiniteSupport
  exact Set.toFinite _

-- @node: twoArmRegularBernoulliLikelihood_hasDerivAt
/-- [the parameter lies in the stated interior interval](hyp:hθ), [Inside `(-1,1)`, the displayed product-rule field differentiates the regularized likelihood.](goal) -/
lemma twoArmRegularBernoulliLikelihood_hasDerivAt {n : ℕ} {θ : ℝ}
    (hθ : |θ| < 1) (s : Unit n → Bool) :
    HasDerivAt (fun t => twoArmRegularBernoulliLikelihood t s)
      (twoArmBernoulliLikelihoodDeriv θ s) θ := by
  have heq : (fun t => twoArmRegularBernoulliLikelihood t s) =ᶠ[nhds θ]
      fun t => twoArmBernoulliLikelihood t s := by
    filter_upwards [Ioo_mem_nhds (by rw [abs_lt] at hθ; exact hθ.1)
      (by rw [abs_lt] at hθ; exact hθ.2)] with t ht
    exact twoArmRegularBernoulliLikelihood_eq ((abs_lt).2 ht).le s
  exact (twoArmBernoulliLikelihood_hasDerivAt θ s).congr_of_eventuallyEq heq

-- @node: twoArmRegularBernoulliLikelihood_pos
/-- [the parameter lies in the stated interior interval](hyp:hθ), [Every score vector has positive regularized likelihood in the open Bernoulli region.](goal) -/
lemma twoArmRegularBernoulliLikelihood_pos {n : ℕ} {θ : ℝ}
    (hθ : |θ| < 1) (s : Unit n → Bool) :
    0 < twoArmRegularBernoulliLikelihood θ s := by
  rw [twoArmRegularBernoulliLikelihood_eq hθ.le]
  exact twoArmBernoulliLikelihood_pos hθ s

-- @node: twoArmRegularBernoulliLikelihoodDeriv_sum_eq_zero
/-- [the parameter lies in the stated interior interval](hyp:hθ), [The displayed derivative masses are centered in the open Bernoulli region.](goal) -/
lemma twoArmRegularBernoulliLikelihoodDeriv_sum_eq_zero {n : ℕ} {θ : ℝ}
    (hθ : |θ| < 1) :
    ∑ s : Unit n → Bool, twoArmBernoulliLikelihoodDeriv θ s = 0 := by
  apply finite_derivative_centering
  · exact fun s => twoArmRegularBernoulliLikelihood_hasDerivAt hθ s
  · filter_upwards [Ioo_mem_nhds (by rw [abs_lt] at hθ; exact hθ.1)
      (by rw [abs_lt] at hθ; exact hθ.2)] with t ht
    exact twoArmRegularBernoulliLikelihood_sum ((abs_lt).2 ht).le

-- @node: twoArmRegularBernoulliLikelihoodDeriv_integral_eq_zero
/-- [the parameter lies in the stated interior interval](hyp:hθ), [The counting integral of the displayed derivative vanishes in the regular region.](goal) -/
lemma twoArmRegularBernoulliLikelihoodDeriv_integral_eq_zero {n : ℕ} {θ : ℝ}
    (hθ : |θ| < 1) :
    ∫ s : Unit n → Bool, twoArmBernoulliLikelihoodDeriv θ s ∂Measure.count = 0 := by
  rw [integral_count, twoArmRegularBernoulliLikelihoodDeriv_sum_eq_zero hθ]

-- @node: twoArmRegularBernoulliIntegral_hasDerivAt
/-- [the parameter lies in the stated interior interval](hyp:hθ), [Differentiation passes through the finite counting integral in the regular region.](goal) -/
lemma twoArmRegularBernoulliIntegral_hasDerivAt {n : ℕ} {θ : ℝ}
    (hθ : |θ| < 1) :
    HasDerivAt
      (fun t => ∫ s : Unit n → Bool, twoArmRegularBernoulliLikelihood t s ∂Measure.count)
      (∫ s : Unit n → Bool, twoArmBernoulliLikelihoodDeriv θ s ∂Measure.count) θ := by
  simp_rw [integral_count]
  exact hasDerivAt_finite_likelihood_sum
    (fun s => twoArmRegularBernoulliLikelihood_hasDerivAt hθ s)

-- @node: twoArmRegularBernoulliLikelihood_absolutelyContinuous
/-- [Every regularized Bernoulli likelihood section is absolutely continuous on the ambient parameter interval used by the smooth prior.](goal) -/
lemma twoArmRegularBernoulliLikelihood_absolutelyContinuous {n : ℕ}
    (s : Unit n → Bool) :
    AbsolutelyContinuousOnInterval
      (fun θ => twoArmRegularBernoulliLikelihood θ s) (-1 / 2) (1 / 2) := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  apply (show ContDiff ℝ 1 (fun θ => twoArmBernoulliLikelihood θ s) by
    unfold twoArmBernoulliLikelihood
    induction (Finset.univ : Finset (Unit n)) using Finset.induction_on with
    | empty => simp; fun_prop
    | @insert i t hi iht =>
      have hfactor : ContDiff ℝ 1
          (fun θ : ℝ => if s i then (1 + θ) / 2 else (1 - θ) / 2) := by
        cases h : s i <;> simp [h] <;> fun_prop
      simpa only [Finset.prod_insert hi] using hfactor.mul iht).contDiffOn.congr
  intro θ hθ
  rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hθ
  exact twoArmRegularBernoulliLikelihood_eq (by
    rw [abs_le]
    constructor <;> nlinarith [hθ.1, hθ.2]) s

-- @node: twoArmPosteriorTarget_absolutelyContinuous
/-- [The observation-dependent posterior target is absolutely continuous on the same ambient interval, which stays uniformly away from its poles.](goal) -/
lemma twoArmPosteriorTarget_absolutelyContinuous {n : ℕ} (a : ℝ)
    (s : Unit n → Bool) :
    AbsolutelyContinuousOnInterval
      (fun θ => twoArmPosteriorTarget a θ s) (-1 / 2) (1 / 2) := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  unfold twoArmPosteriorTarget twoArmPosteriorWeight
  apply ContDiffOn.add (by fun_prop)
  apply ContDiffOn.mul
  · apply ContDiffOn.div (by fun_prop) (by fun_prop)
    intro θ hθ
    rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hθ
    rcases hθ with ⟨hlo, hhi⟩
    nlinarith [sq_nonneg (θ - 1), sq_nonneg (θ + 1)]
  · fun_prop

-- @node: finiteCountProduct_integrable_of_sections
/-- [every finite-coordinate section satisfies the stated regularity condition](hyp:hf), [A real field on an interval times a finite discrete carrier is integrable when each of its finitely many interval sections is integrable.](goal) -/
lemma finiteCountProduct_integrable_of_sections
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {ell u : ℝ} {f : ℝ × X → ℝ}
    (hf : ∀ x, Integrable (fun θ => f (θ, x))
      (volume.restrict (Icc ell u))) :
    Integrable f ((volume.restrict (Icc ell u)).prod Measure.count) := by
  classical
  have hmeas : AEStronglyMeasurable f
      ((volume.restrict (Icc ell u)).prod Measure.count) := by
    have hterm (x : X) : AEStronglyMeasurable
        (fun z : ℝ × X => (if z.2 = x then 1 else 0) * f (z.1, x))
        ((volume.restrict (Icc ell u)).prod Measure.count) := by
      apply AEStronglyMeasurable.mul
      · exact (show Measurable
          (fun z : ℝ × X => if z.2 = x then (1 : ℝ) else 0) by
          apply Measurable.ite
          · exact (measurableSet_singleton x).preimage measurable_snd
          · exact measurable_const
          · exact measurable_const).aestronglyMeasurable
      · exact (hf x).aestronglyMeasurable.comp_fst
    have hsum := Finset.aestronglyMeasurable_sum (Finset.univ : Finset X)
      (fun x _hx => hterm x)
    have hsum' : AEStronglyMeasurable
        (fun z : ℝ × X => ∑ x, (if z.2 = x then 1 else 0) * f (z.1, x))
        ((volume.restrict (Icc ell u)).prod Measure.count) := by
      apply hsum.congr
      filter_upwards with z
      exact Fintype.sum_apply z _
    convert hsum' using 1
    funext z
    simp
  rw [integrable_prod_iff' hmeas]
  constructor
  · filter_upwards with x
    exact hf x
  · rw [integrable_count_iff]
    apply summable_of_hasFiniteSupport
    exact Set.toFinite _

-- @node: finiteCountProduct_integrable_of_continuousSections
/-- [every finite-coordinate section satisfies the stated regularity condition](hyp:hf), [Sectionwise continuity on a compact interval implies integrability over that interval times any finite discrete carrier.](goal) -/
lemma finiteCountProduct_integrable_of_continuousSections
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {ell u : ℝ} {f : ℝ × X → ℝ}
    (hf : ∀ x, ContinuousOn (fun θ => f (θ, x)) (Icc ell u)) :
    Integrable f ((volume.restrict (Icc ell u)).prod Measure.count) := by
  apply finiteCountProduct_integrable_of_sections
  exact fun x => (hf x).integrableOn_Icc

-- @node: twoArmRegularBernoulliLikelihood_hasDerivAt_ae
/-- [The regularized product likelihood has the advertised derivative almost everywhere on the ambient parameter/counting product measure.](goal) -/
lemma twoArmRegularBernoulliLikelihood_hasDerivAt_ae {n : ℕ} :
    ∀ᵐ z ∂((Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
      (-1 / 2) (1 / 2)).prod (Measure.count : Measure (Unit n → Bool))),
      HasDerivAt (fun t => twoArmRegularBernoulliLikelihood t z.2)
        (twoArmBernoulliLikelihoodDeriv z.1 z.2) z.1 := by
  have hmemθ : ∀ᵐ (θ : ℝ) ∂Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
      (-1 / 2) (1 / 2), θ ∈ Set.Icc (-1 / 2) (1 / 2) := by
    unfold Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
    exact ae_restrict_mem measurableSet_Icc
  have hmem := (Measure.quasiMeasurePreserving_fst
    (μ := Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
      (-1 / 2) (1 / 2))
    (ν := (Measure.count : Measure (Unit n → Bool)))).tendsto_ae.eventually hmemθ
  filter_upwards [hmem] with z hz
  apply twoArmRegularBernoulliLikelihood_hasDerivAt
  rw [abs_lt]
  constructor <;> nlinarith [hz.1, hz.2]

-- @node: twoArmPosteriorTarget_hasDerivAt_ae
/-- [The supplied posterior-target derivative is valid almost everywhere on the ambient parameter/counting product measure.](goal) -/
lemma twoArmPosteriorTarget_hasDerivAt_ae {n : ℕ} (a : ℝ) :
    ∀ᵐ z ∂((Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
      (-1 / 2) (1 / 2)).prod (Measure.count : Measure (Unit n → Bool))),
      HasDerivAt (fun t => twoArmPosteriorTarget a t z.2)
        (twoArmPosteriorTargetDeriv a z.1 z.2) z.1 := by
  have hmemθ : ∀ᵐ (θ : ℝ) ∂Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
      (-1 / 2) (1 / 2), θ ∈ Set.Icc (-1 / 2) (1 / 2) := by
    unfold Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
    exact ae_restrict_mem measurableSet_Icc
  have hmem := (Measure.quasiMeasurePreserving_fst
    (μ := Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
      (-1 / 2) (1 / 2))
    (ν := (Measure.count : Measure (Unit n → Bool)))).tendsto_ae.eventually hmemθ
  filter_upwards [hmem] with z hz
  unfold twoArmPosteriorTargetDeriv
  apply twoArmPosteriorTarget_hasDerivAt
  nlinarith [hz.1, hz.2]

-- @node: twoArmRegularBernoulliLikelihood_continuousOn
/-- [Each regularized Bernoulli likelihood section is continuous on the ambient parameter interval.](goal) -/
lemma twoArmRegularBernoulliLikelihood_continuousOn {n : ℕ}
    (s : Unit n → Bool) :
    ContinuousOn (fun θ => twoArmRegularBernoulliLikelihood θ s)
      (Icc (-1 / 2) (1 / 2)) := by
  have h := (twoArmRegularBernoulliLikelihood_absolutelyContinuous s).continuousOn
  rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at h
  exact h

-- @node: twoArmPosteriorTargetDeriv_continuousOn
/-- [The displayed posterior-target derivative is continuous on the ambient interval, which stays away from both poles.](goal) -/
lemma twoArmPosteriorTargetDeriv_continuousOn {n : ℕ} (a : ℝ)
    (s : Unit n → Bool) :
    ContinuousOn (fun θ => twoArmPosteriorTargetDeriv a θ s)
      (Icc (-1 / 2) (1 / 2)) := by
  unfold twoArmPosteriorTargetDeriv twoArmPosteriorWeight twoArmScoreAverage
  apply ContinuousOn.add
  · apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro θ hθ
    rcases hθ with ⟨hlo, hhi⟩
    nlinarith [sq_nonneg (θ - 1), sq_nonneg (θ + 1)]
  · apply ContinuousOn.mul
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro θ hθ
      rcases hθ with ⟨hlo, hhi⟩
      nlinarith [sq_nonneg (θ - 1), sq_nonneg (θ + 1)]
    · fun_prop

-- @node: twoArmSensitivityField_integrable
/-- [the parameter lies in the stated interval](hyp:ha), [The smooth-prior sensitivity field is integrable over the ambient parameter interval and finite score carrier.](goal) -/
lemma twoArmSensitivityField_integrable {n : ℕ} (a : ℝ) (ha : 0 < a) :
    Integrable
      (sensitivityField (smoothPrior 0 (a / 2))
        twoArmRegularBernoulliLikelihood (twoArmPosteriorTargetDeriv a))
      ((parameterMeasure (-1 / 2) (1 / 2)).prod
        (Measure.count : Measure (Unit n → Bool))) := by
  apply finiteCountProduct_integrable_of_continuousSections
  intro s
  unfold sensitivityField jointDensity
  convert (twoArmPosteriorTargetDeriv_continuousOn a s).mul
    ((smoothPrior_contDiff (by positivity : 0 < a / 2)).continuous.continuousOn.mul
      (twoArmRegularBernoulliLikelihood_continuousOn s)) using 1
  ext θ
  rfl

-- @node: twoArmErrorSqField_integrable
/-- [the parameter lies in the stated interval](hyp:ha), [Every finite estimator gives an integrable smooth-prior squared-error field for the observation-dependent posterior target.](goal) -/
lemma twoArmErrorSqField_integrable {n : ℕ} (a : ℝ) (ha : 0 < a)
    (T : (Unit n → Bool) → ℝ) :
    Integrable
      (errorSqField (smoothPrior 0 (a / 2))
        twoArmRegularBernoulliLikelihood (twoArmPosteriorTarget a) T)
      ((parameterMeasure (-1 / 2) (1 / 2)).prod
        (Measure.count : Measure (Unit n → Bool))) := by
  apply finiteCountProduct_integrable_of_continuousSections
  intro s
  have hg := (twoArmPosteriorTarget_absolutelyContinuous a s).continuousOn
  rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hg
  have he : ContinuousOn (fun θ => (T s - twoArmPosteriorTarget a θ s) ^ 2)
      (Icc (-1 / 2) (1 / 2)) := by fun_prop
  unfold errorSqField jointDensity
  convert he.mul
    ((smoothPrior_contDiff (by positivity : 0 < a / 2)).continuous.continuousOn.mul
      (twoArmRegularBernoulliLikelihood_continuousOn s)) using 1
  ext θ
  rfl

-- @node: twoArmRegularLikelihoodScore_continuousOn
/-- [On the ambient parameter interval, every guarded likelihood-score section is continuous because every Bernoulli product mass is strictly positive.](goal) -/
lemma twoArmRegularLikelihoodScore_continuousOn {n : ℕ}
    (s : Unit n → Bool) :
    ContinuousOn
      (fun θ => likelihoodScore twoArmRegularBernoulliLikelihood
        twoArmBernoulliLikelihoodDeriv θ s) (Icc (-1 / 2) (1 / 2)) := by
  have hp : ContinuousOn
      (fun θ => twoArmRegularBernoulliLikelihood (n := n) θ s)
      (Icc (-1 / 2) (1 / 2)) :=
    twoArmRegularBernoulliLikelihood_continuousOn s
  have hdp : ContinuousOn
      (fun θ => twoArmBernoulliLikelihoodDeriv (n := n) θ s)
      (Icc (-1 / 2) (1 / 2)) := by
    unfold twoArmBernoulliLikelihoodDeriv
    apply Continuous.continuousOn
    apply continuous_finsetSum Finset.univ
    intro i _hi
    apply Continuous.mul
    · apply continuous_finsetProd (Finset.univ.erase i)
      intro j _hj
      split <;> fun_prop
    · split <;> fun_prop
  refine (hdp.div hp ?_).congr ?_
  · intro θ hθ hzero
    exact (twoArmRegularBernoulliLikelihood_pos (by
      rw [abs_lt]
      constructor <;> nlinarith [hθ.1, hθ.2]) s).ne' hzero
  · intro θ hθ
    unfold likelihoodScore
    change (if 0 < twoArmRegularBernoulliLikelihood θ s then
      twoArmBernoulliLikelihoodDeriv θ s /
        twoArmRegularBernoulliLikelihood θ s else 0) = _
    rw [if_pos (twoArmRegularBernoulliLikelihood_pos (by
      rw [abs_lt]
      constructor <;> nlinarith [hθ.1, hθ.2]) s)]
    rfl

-- @node: twoArmFisherScoreField_integrable
/-- [the parameter lies in the stated interval](hyp:ha), [The smooth-prior weighted likelihood-score square is integrable on the ambient parameter interval times the finite score carrier.](goal) -/
lemma twoArmFisherScoreField_integrable {n : ℕ} (a : ℝ) (ha : 0 < a) :
    Integrable
      (fun z : ℝ × (Unit n → Bool) =>
        smoothPrior 0 (a / 2) z.1 * twoArmRegularBernoulliLikelihood z.1 z.2 *
          (likelihoodScore twoArmRegularBernoulliLikelihood
            twoArmBernoulliLikelihoodDeriv z.1 z.2) ^ 2)
      ((parameterMeasure (-1 / 2) (1 / 2)).prod Measure.count) := by
  apply finiteCountProduct_integrable_of_continuousSections
  intro s
  apply ContinuousOn.mul
  · exact (smoothPrior_contDiff (by positivity : 0 < a / 2)).continuous.continuousOn.mul
      (twoArmRegularBernoulliLikelihood_continuousOn s)
  · exact (twoArmRegularLikelihoodScore_continuousOn s).pow 2

-- @node: twoArmPriorScoreField_integrable_section
/-- [the parameter lies in the stated interval](hyp:ha), [Each finite score section of the lifted smooth-prior score square is integrable on the ambient parameter interval.](goal) -/
lemma twoArmPriorScoreField_integrable_section {n : ℕ} (a : ℝ) (ha : 0 < a)
    (s : Unit n → Bool) :
    Integrable
      (fun θ : ℝ =>
        smoothPrior 0 (a / 2) θ * twoArmRegularBernoulliLikelihood θ s *
          (priorScore (smoothPrior 0 (a / 2))
            (smoothPriorDeriv 0 (a / 2)) θ) ^ 2)
      (parameterMeasure (-1 / 2) (1 / 2)) := by
  have hbase : Integrable
      (fun θ => smoothPrior 0 (a / 2) θ *
        (priorScore (smoothPrior 0 (a / 2))
          (smoothPriorDeriv 0 (a / 2)) θ) ^ 2)
      (parameterMeasure (-1 / 2) (1 / 2)) :=
    smoothPrior_scoreSq_integrable (by positivity : 0 < a / 2)
  have hpSm : AEStronglyMeasurable
      (fun θ => twoArmRegularBernoulliLikelihood θ s)
      (parameterMeasure (-1 / 2) (1 / 2)) := by
    exact (twoArmRegularBernoulliLikelihood_continuousOn s).aestronglyMeasurable
      measurableSet_Icc
  have hpBound : ∀ᵐ θ ∂parameterMeasure (-1 / 2) (1 / 2),
      ‖twoArmRegularBernoulliLikelihood θ s‖ ≤ 1 := by
    have hmem : ∀ᵐ θ ∂parameterMeasure (-1 / 2) (1 / 2),
        θ ∈ Set.Icc (-1 / 2) (1 / 2) := by
      unfold parameterMeasure
      exact ae_restrict_mem measurableSet_Icc
    filter_upwards [hmem] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg
      (twoArmRegularBernoulliLikelihood_nonneg θ s)]
    have hsum := twoArmRegularBernoulliLikelihood_sum (n := n) (θ := θ) (by
      rw [abs_le]
      constructor <;> nlinarith [hθ.1, hθ.2])
    rw [← hsum]
    exact Finset.single_le_sum
      (fun x _ => twoArmRegularBernoulliLikelihood_nonneg θ x)
      (Finset.mem_univ s)
  change Integrable
    (fun θ => smoothPrior 0 (a / 2) θ * twoArmRegularBernoulliLikelihood θ s *
      priorScore (smoothPrior 0 (a / 2)) (smoothPriorDeriv 0 (a / 2)) θ ^ 2)
    (parameterMeasure (-1 / 2) (1 / 2))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hbase.bdd_mul hpSm hpBound

-- @node: twoArmPriorScoreField_integrable
/-- [the parameter lies in the stated interval](hyp:ha), [The smooth-prior weighted prior-score square is integrable after lifting to the finite Bernoulli score carrier.](goal) -/
lemma twoArmPriorScoreField_integrable {n : ℕ} (a : ℝ) (ha : 0 < a) :
    Integrable
      (fun z : ℝ × (Unit n → Bool) =>
        smoothPrior 0 (a / 2) z.1 * twoArmRegularBernoulliLikelihood z.1 z.2 *
          (priorScore (smoothPrior 0 (a / 2))
            (smoothPriorDeriv 0 (a / 2)) z.1) ^ 2)
      ((parameterMeasure (-1 / 2) (1 / 2)).prod Measure.count) := by
  apply finiteCountProduct_integrable_of_sections
  exact twoArmPriorScoreField_integrable_section a ha

-- @node: twoArmScoreCrossField_integrable
/-- [the parameter lies in the stated interval](hyp:ha), [The smooth-prior weighted cross product of the prior and likelihood scores is integrable on the parameter--score product space.](goal) -/
lemma twoArmScoreCrossField_integrable {n : ℕ} (a : ℝ) (ha : 0 < a) :
    Integrable
      (fun z : ℝ × (Unit n → Bool) =>
        smoothPrior 0 (a / 2) z.1 * twoArmRegularBernoulliLikelihood z.1 z.2 *
          (priorScore (smoothPrior 0 (a / 2))
              (smoothPriorDeriv 0 (a / 2)) z.1 *
            likelihoodScore twoArmRegularBernoulliLikelihood
              twoArmBernoulliLikelihoodDeriv z.1 z.2))
      ((parameterMeasure (-1 / 2) (1 / 2)).prod Measure.count) := by
  apply finiteCountProduct_integrable_of_sections
  intro s
  have hp := twoArmPriorScoreField_integrable_section (n := n) a ha s
  have hf : Integrable
      (fun θ => smoothPrior 0 (a / 2) θ * twoArmRegularBernoulliLikelihood θ s *
        likelihoodScore twoArmRegularBernoulliLikelihood
          twoArmBernoulliLikelihoodDeriv θ s ^ 2)
      (parameterMeasure (-1 / 2) (1 / 2)) := by
    apply (ContinuousOn.mul
      ((smoothPrior_contDiff (by positivity : 0 < a / 2)).continuous.continuousOn.mul
        (twoArmRegularBernoulliLikelihood_continuousOn s))
      ((twoArmRegularLikelihoodScore_continuousOn s).pow 2)).integrableOn_Icc
  apply (hp.add hf).mono'
  · have hw : Measurable (smoothPrior 0 (a / 2)) :=
      (smoothPrior_contDiff (by positivity : 0 < a / 2)).continuous.measurable
    have hdw : Measurable (smoothPriorDeriv 0 (a / 2)) := by
      unfold smoothPriorDeriv
      apply Measurable.ite
      · exact measurableSet_lt (by fun_prop) measurable_const
      · fun_prop
      · fun_prop
    have hps : Measurable
        (priorScore (smoothPrior 0 (a / 2)) (smoothPriorDeriv 0 (a / 2))) := by
      unfold priorScore
      apply Measurable.ite
      · exact measurableSet_lt measurable_const hw
      · exact hdw.div hw
      · exact measurable_const
    have hpSm : AEStronglyMeasurable
        (fun θ => twoArmRegularBernoulliLikelihood θ s)
        (parameterMeasure (-1 / 2) (1 / 2)) :=
      (twoArmRegularBernoulliLikelihood_continuousOn s).aestronglyMeasurable
        measurableSet_Icc
    have hlikeSm : AEStronglyMeasurable
        (fun θ => likelihoodScore twoArmRegularBernoulliLikelihood
          twoArmBernoulliLikelihoodDeriv θ s)
        (parameterMeasure (-1 / 2) (1 / 2)) :=
      (twoArmRegularLikelihoodScore_continuousOn s).aestronglyMeasurable
        measurableSet_Icc
    convert (((hw.aestronglyMeasurable.mul hpSm).mul hps.aestronglyMeasurable).mul
      hlikeSm) using 1
    ext θ
    simp only [Pi.mul_apply]
    ring
  · filter_upwards with θ
    change ‖smoothPrior 0 (a / 2) θ * twoArmRegularBernoulliLikelihood θ s *
        (priorScore (smoothPrior 0 (a / 2)) (smoothPriorDeriv 0 (a / 2)) θ *
          likelihoodScore twoArmRegularBernoulliLikelihood
            twoArmBernoulliLikelihoodDeriv θ s)‖ ≤ _
    have hw : 0 ≤ smoothPrior 0 (a / 2) θ :=
      smoothPrior_nonneg (by positivity) θ
    have hp0 : 0 ≤ twoArmRegularBernoulliLikelihood θ s :=
      twoArmRegularBernoulliLikelihood_nonneg θ s
    rw [Real.norm_eq_abs]
    change abs (smoothPrior 0 (a / 2) θ * twoArmRegularBernoulliLikelihood θ s *
          (priorScore (smoothPrior 0 (a / 2))
              (smoothPriorDeriv 0 (a / 2)) θ *
            likelihoodScore twoArmRegularBernoulliLikelihood
              twoArmBernoulliLikelihoodDeriv θ s)) ≤
      smoothPrior 0 (a / 2) θ * twoArmRegularBernoulliLikelihood θ s *
          priorScore (smoothPrior 0 (a / 2))
            (smoothPriorDeriv 0 (a / 2)) θ ^ 2 +
        smoothPrior 0 (a / 2) θ * twoArmRegularBernoulliLikelihood θ s *
          likelihoodScore twoArmRegularBernoulliLikelihood
            twoArmBernoulliLikelihoodDeriv θ s ^ 2
    calc
      abs (smoothPrior 0 (a / 2) θ * twoArmRegularBernoulliLikelihood θ s *
          (priorScore (smoothPrior 0 (a / 2))
              (smoothPriorDeriv 0 (a / 2)) θ *
            likelihoodScore twoArmRegularBernoulliLikelihood
              twoArmBernoulliLikelihoodDeriv θ s)) ≤
          smoothPrior 0 (a / 2) θ * twoArmRegularBernoulliLikelihood θ s *
            (priorScore (smoothPrior 0 (a / 2))
                (smoothPriorDeriv 0 (a / 2)) θ ^ 2 +
              likelihoodScore twoArmRegularBernoulliLikelihood
                twoArmBernoulliLikelihoodDeriv θ s ^ 2) := by
            rw [abs_mul, abs_of_nonneg (mul_nonneg hw hp0)]
            exact mul_le_mul_of_nonneg_left (by
              rw [abs_mul]
              nlinarith [sq_nonneg
                (|priorScore (smoothPrior 0 (a / 2))
                    (smoothPriorDeriv 0 (a / 2)) θ| -
                  |likelihoodScore twoArmRegularBernoulliLikelihood
                    twoArmBernoulliLikelihoodDeriv θ s|),
                sq_abs (priorScore (smoothPrior 0 (a / 2))
                  (smoothPriorDeriv 0 (a / 2)) θ),
                sq_abs (likelihoodScore twoArmRegularBernoulliLikelihood
                  twoArmBernoulliLikelihoodDeriv θ s)]) (mul_nonneg hw hp0)
      _ = smoothPrior 0 (a / 2) θ * twoArmRegularBernoulliLikelihood θ s *
            priorScore (smoothPrior 0 (a / 2))
              (smoothPriorDeriv 0 (a / 2)) θ ^ 2 +
          smoothPrior 0 (a / 2) θ * twoArmRegularBernoulliLikelihood θ s *
            likelihoodScore twoArmRegularBernoulliLikelihood
              twoArmBernoulliLikelihoodDeriv θ s ^ 2 := by ring

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

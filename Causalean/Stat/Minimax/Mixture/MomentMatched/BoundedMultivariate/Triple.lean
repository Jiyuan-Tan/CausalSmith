module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.Scalar

/-!
# Bounded triple priors

A scalar pair is reweighted by `a/x`, with the remaining mass at zero.
The positive branch uses `p=bx`, `π=(1+qa/x)/2`, and
`μ=1/(2π)=x/(x+qa)`; the zero branch uses `(0,1/2,1)`.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

/-- [The parameter triple](goal) stores arrival mass, propensity, and conditional success probability in that order. -/
abbrev MarkedParam := ℝ × ℝ × ℝ

/-- Three [monomial degrees](hyp:i,j,k) and [a parameter triple](hyp:t) determine [the mixed monomial](goal) by [multiplying the three corresponding powers](step:1). -/
def mixedMonomial (i j k : ℕ) (t : MarkedParam) : ℝ :=
  t.1 ^ i * (t.1 * t.2.1) ^ j * (t.1 * t.2.1 * t.2.2) ^ k

/-- A [parameter triple](hyp:t) determines [the target functional](goal) by [multiplying arrival mass and conditional success probability](step:1). -/
def targetFunctional (t : MarkedParam) : ℝ := t.1 * t.2.2

/-- A [matching degree](hyp:K), [arrival-mass bound and overlap margin](hyp:b,ε), and [target gap](hyp:gap) specify a bounded marked prior pair with finite probability support, matched mixed moments, and separated mean success mass. -/
structure TriplePriors (K : ℕ) (b ε gap : ℝ) where
  positive_degree : 1 ≤ K
  ν₀ : Measure MarkedParam
  ν₁ : Measure MarkedParam
  probability₀ : IsProbabilityMeasure ν₀
  probability₁ : IsProbabilityMeasure ν₁
  finite₀ : ∃ s : Finset MarkedParam, ν₀ (s : Set MarkedParam) = 1
  finite₁ : ∃ s : Finset MarkedParam, ν₁ (s : Set MarkedParam) = 1
  supported₀ : ν₀ {t | 0 ≤ t.1 ∧ t.1 ≤ b ∧ ε ≤ t.2.1 ∧
    t.2.1 ≤ 1 - ε ∧ 0 ≤ t.2.2 ∧ t.2.2 ≤ 1} = 1
  supported₁ : ν₁ {t | 0 ≤ t.1 ∧ t.1 ≤ b ∧ ε ≤ t.2.1 ∧
    t.2.1 ≤ 1 - ε ∧ 0 ≤ t.2.2 ∧ t.2.2 ≤ 1} = 1
  mixed_match : ∀ i j k : ℕ, i + j + k ≤ 3 * K →
    (∫ t, mixedMonomial i j k t ∂ν₀) =
      ∫ t, mixedMonomial i j k t ∂ν₁
  mean_p_match : (∫ t, t.1 ∂ν₀) = ∫ t, t.1 ∂ν₁
  target_gap : gap ≤
    |(∫ t, targetFunctional t ∂ν₀) -
      ∫ t, targetFunctional t ∂ν₁|

/-- A [rescaling factor, scalar scale, and inverse coefficient](hyp:b,a,q) together with [a scalar atom](hyp:x) determine [the marked parameter triple](goal) by [using the stated positive-atom formula and a fixed zero atom](step:1). -/
noncomputable def scalarToTriple (b a q : ℝ) (x : ℝ) : MarkedParam :=
  if x = 0 then (0, 1 / 2, 1)
  else (b * x, (1 + q * a / x) / 2, x / (x + q * a))

/-- A [scalar scale](hyp:a) and [scalar prior](hyp:ω) determine [the reweighted scalar measure](goal) by [adding a zero atom to the density tilted by the scale-to-atom ratio](step:1). -/
noncomputable def reweightedScalar (a : ℝ) (ω : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - ∫ x, a / x ∂ω) • Measure.dirac 0 +
    ω.withDensity (fun x => ENNReal.ofReal (a / x))

/-- A [rescaling factor, scalar scale, and inverse coefficient](hyp:b,a,q) and [scalar prior](hyp:ω) determine [the triple prior](goal) by [mapping its reweighted scalar measure through the triple transformation](step:1). -/
noncomputable def triplePrior (b a q : ℝ) (ω : Measure ℝ) :
    Measure MarkedParam :=
  (reweightedScalar a ω).map (scalarToTriple b a q)

/- On the scalar support, 0 ≤ a/x ≤ 1. Thus the density has mass
  ∫ a/x and the added atom has its complementary mass. Finite support is
  preserved by weighting, adjoining zero, and mapping. -/

/-- A [positive scale](hyp:ha₀) no larger than one [in its support endpoint](hyp:ha₁), [probability prior](hyp:ω), [finite support certificate](hyp:hfinite), and [interval support certificate](hyp:hsupport) give [a reweighted finite probability prior supported at zero and on the original interval](goal). -/
theorem reweightedScalar_probability_finite_supported
    {a : ℝ} (ha₀ : 0 < a) (ha₁ : a ≤ 1) (ω : Measure ℝ)
    [IsProbabilityMeasure ω]
    (hfinite : ∃ s : Finset ℝ, ω (s : Set ℝ) = 1)
    (hsupport : ω (Set.Icc a 1) = 1) :
    IsProbabilityMeasure (reweightedScalar a ω) ∧
      (∃ s : Finset ℝ, (reweightedScalar a ω) (s : Set ℝ) = 1) ∧
      (reweightedScalar a ω) ({0} ∪ Set.Icc a 1) = 1 := by
  let f : ℝ → ℝ := fun x => a / x
  have hmeas : Measurable f := by fun_prop
  have hae : ∀ᵐ x ∂ω, x ∈ Set.Icc a 1 := by
    apply ae_iff.mpr
    exact (prob_compl_eq_zero_iff measurableSet_Icc).2 hsupport
  have hbounds : ∀ᵐ x ∂ω, 0 ≤ f x ∧ f x ≤ 1 := by
    filter_upwards [hae] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha₀ hx.1
    constructor
    · exact div_nonneg (le_of_lt ha₀) (le_of_lt hxpos)
    · exact (div_le_one hxpos).2 hx.1
  have hfint : Integrable f ω := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards [hbounds] with x hx
    simpa [abs_of_nonneg hx.1] using hx.2
  have hmean₀ : 0 ≤ ∫ x, f x ∂ω := integral_nonneg_of_ae (hbounds.mono fun x hx => hx.1)
  have hmean₁ : (∫ x, f x ∂ω) ≤ 1 := by
    calc
      (∫ x, f x ∂ω) ≤ ∫ _x, (1 : ℝ) ∂ω :=
        integral_mono_ae hfint (integrable_const 1) (hbounds.mono fun x hx => hx.2)
      _ = 1 := by simp
  have hmass : (ω.withDensity (fun x => ENNReal.ofReal (f x))) Set.univ =
      ENNReal.ofReal (∫ x, f x ∂ω) := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hfint (hbounds.mono fun x hx => hx.1)).symm
  have hprob : IsProbabilityMeasure (reweightedScalar a ω) := by
    apply IsProbabilityMeasure.mk
    have hsum : ENNReal.ofReal (1 - ∫ x, f x ∂ω) +
        (ω.withDensity (fun x => ENNReal.ofReal (f x))) Set.univ = 1 := by
      rw [hmass, ← ENNReal.ofReal_add (by linarith : 0 ≤ 1 - ∫ x, f x ∂ω) hmean₀]
      norm_num
    simpa [reweightedScalar, f] using hsum
  letI : IsProbabilityMeasure (reweightedScalar a ω) := hprob
  have hzero {s : Set ℝ} (hs : MeasurableSet s) (hω : ω s = 1) (h0 : (0 : ℝ) ∈ s) :
      (reweightedScalar a ω) s = 1 := by
    apply (prob_compl_eq_zero_iff hs).1
    have hωc : ω sᶜ = 0 := (prob_compl_eq_zero_iff hs).2 hω
    have hdens : (ω.withDensity (fun x => ENNReal.ofReal (f x))) sᶜ = 0 :=
      (withDensity_absolutelyContinuous ω (fun x => ENNReal.ofReal (f x))) hωc
    change ENNReal.ofReal (1 - ∫ x, f x ∂ω) • (Measure.dirac 0) sᶜ +
      (ω.withDensity (fun x => ENNReal.ofReal (f x))) sᶜ = 0
    simp [hdens, h0]
  refine ⟨hprob, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hfinite
    refine ⟨insert 0 s, hzero (Finset.measurableSet _) ?_ (by simp)⟩
    exact le_antisymm prob_le_one (hs ▸ measure_mono (by simp))
  · apply hzero (MeasurableSet.union (by simp) measurableSet_Icc) ?_ (by simp)
    exact le_antisymm prob_le_one (hsupport ▸ measure_mono Set.subset_union_right)

/- For positive total degree the zero atom contributes zero. On the
  positive branch, pπμ=bx/2 and pπ=b(x+qa)/2. Multiplication by the
  density a/x gives the displayed integrand, including exponent -1. -/

/-- With a [positive reweighting scale](hyp:a,ha), [rescaling factor](hyp:b),
[nonnegative inverse coefficient](hyp:q,hq), [probability prior supported on
its positive interval](hyp:ω,hsupport), and [three degrees with positive total
degree](hyp:i,j,k,hdegree), [the transported mixed moment has the stated
scalar-integral formula](goal). -/
theorem integral_mixedMonomial_triplePrior
    {a b q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) (ω : Measure ℝ)
    [IsProbabilityMeasure ω] (hsupport : ω (Set.Icc a 1) = 1)
    (i j k : ℕ) (hdegree : 0 < i + j + k) :
    (∫ t, mixedMonomial i j k t ∂triplePrior b a q ω) =
      ∫ x, a * b ^ (i + j + k) / (2 : ℝ) ^ (j + k) *
        x ^ (i + k) / x * (x + q * a) ^ j ∂ω := by
  let d : ℝ → ENNReal := fun x => ENNReal.ofReal (a / x)
  let G : ℝ → ℝ := fun x => mixedMonomial i j k (scalarToTriple b a q x)
  let R : ℝ → ℝ := fun x =>
    a * b ^ (i + j + k) / (2 : ℝ) ^ (j + k) *
      x ^ (i + k) / x * (x + q * a) ^ j
  have hae : ∀ᵐ x ∂ω, x ∈ Set.Icc a 1 := by
    apply ae_iff.mpr
    exact (prob_compl_eq_zero_iff measurableSet_Icc).2 hsupport
  have hd : Measurable d := by fun_prop
  have hdtop : ∀ᵐ x ∂ω, d x < ⊤ := by simp [d]
  have hmap : Measurable (scalarToTriple b a q) := by
    unfold scalarToTriple
    apply Measurable.ite (measurableSet_singleton 0)
    · fun_prop
    · fun_prop
  have hG : Measurable G := by
    exact (show Measurable (mixedMonomial i j k) by
      unfold mixedMonomial
      fun_prop).comp hmap
  have hRcont : ContinuousOn R (Set.Icc a 1) := by
    dsimp [R]
    apply ContinuousOn.mul
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro x hx
      exact ne_of_gt (lt_of_lt_of_le ha hx.1)
    · fun_prop
  have hRint : Integrable R ω := by
    have h : IntegrableOn R (Set.Icc a 1) ω :=
      hRcont.integrableOn_compact isCompact_Icc
    have hsets : (Set.univ : Set ℝ) =ᵐ[ω] Set.Icc a 1 := by
      filter_upwards [hae] with x hx
      exact propext (iff_of_true trivial hx)
    simpa using h.congr_set_ae hsets
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc a 1) :
      (d x).toReal * G x = R x := by
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hden : x + q * a ≠ 0 := by positivity
    have hadiv : 0 ≤ a / x := div_nonneg (le_of_lt ha) (le_of_lt hxpos)
    have hpπ : b * x * ((1 + q * a / x) / 2) = b * (x + q * a) / 2 := by
      field_simp
    have hpπμ : b * x * ((1 + q * a / x) / 2) * (x / (x + q * a)) =
        b * x / 2 := by
      rw [hpπ]
      field_simp
    simp only [d, G, R, scalarToTriple, if_neg hxne, mixedMonomial,
      ENNReal.toReal_ofReal hadiv]
    rw [hpπμ, hpπ]
    simp only [mul_pow, div_pow, pow_add]
    field_simp
  have hweight : Integrable (fun x => (d x).toReal * G x) ω :=
    hRint.congr (hae.mono fun x hx => (hpoint x hx).symm)
  have hdens : Integrable G (ω.withDensity d) := by
    exact (integrable_withDensity_iff_integrable_smul' hd hdtop).2
      (by simpa only [smul_eq_mul] using hweight)
  have hdirac : Integrable G (Measure.dirac 0) := integrable_dirac (by simp)
  calc
    (∫ t, mixedMonomial i j k t ∂triplePrior b a q ω) =
        ∫ x, G x ∂reweightedScalar a ω := by
          exact integral_map hmap.aemeasurable (by
            unfold mixedMonomial
            fun_prop)
    _ = ∫ x, G x ∂ω.withDensity d := by
      rw [reweightedScalar, integral_add_measure
        (hdirac.smul_measure ENNReal.ofReal_ne_top) hdens,
        integral_smul_measure, integral_dirac]
      have hz : G 0 = 0 := by
        simp [G, scalarToTriple, mixedMonomial]
        omega
      simp [hz]
    _ = ∫ x, (d x).toReal * G x ∂ω := by
      rw [integral_withDensity_eq_integral_toReal_smul hd hdtop]
      simp only [smul_eq_mul]
    _ = ∫ x, R x ∂ω := integral_congr_ae (hae.mono fun x hx => hpoint x hx)
    _ = _ := rfl

/-- A [positive scalar scale](hyp:ha), [nonnegative inverse coefficient](hyp:hq), [probability prior](hyp:ω), and [its interval support](hyp:hsupport) give [the target mean of the triple prior as the stated scaled scalar rational-target mean](goal). -/
theorem integral_targetFunctional_triplePrior
    {a b q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) (ω : Measure ℝ)
    [IsProbabilityMeasure ω] (hsupport : ω (Set.Icc a 1) = 1) :
    (∫ t, targetFunctional t ∂triplePrior b a q ω) =
      a * b * ∫ x, x / (x + q * a) ∂ω := by
  let d : ℝ → ENNReal := fun x => ENNReal.ofReal (a / x)
  let G : ℝ → ℝ := fun x => targetFunctional (scalarToTriple b a q x)
  let R : ℝ → ℝ := fun x => x / (x + q * a)
  have hae : ∀ᵐ x ∂ω, x ∈ Set.Icc a 1 := by
    apply ae_iff.mpr
    exact (prob_compl_eq_zero_iff measurableSet_Icc).2 hsupport
  have hd : Measurable d := by fun_prop
  have hdtop : ∀ᵐ x ∂ω, d x < ⊤ := by simp [d]
  have hmap : Measurable (scalarToTriple b a q) := by
    unfold scalarToTriple
    apply Measurable.ite (measurableSet_singleton 0)
    · fun_prop
    · fun_prop
  have hG : Measurable G := by
    exact (show Measurable targetFunctional by
      unfold targetFunctional
      fun_prop).comp hmap
  have hRcont : ContinuousOn R (Set.Icc a 1) := by
    dsimp [R]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hqa : 0 ≤ q * a := mul_nonneg hq (le_of_lt ha)
    positivity
  have hRint : Integrable R ω := by
    have h : IntegrableOn R (Set.Icc a 1) ω :=
      hRcont.integrableOn_compact isCompact_Icc
    have hsets : (Set.univ : Set ℝ) =ᵐ[ω] Set.Icc a 1 := by
      filter_upwards [hae] with x hx
      exact propext (iff_of_true trivial hx)
    simpa using h.congr_set_ae hsets
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc a 1) :
      (d x).toReal * G x = a * b * R x := by
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hden : x + q * a ≠ 0 := by positivity
    have hadiv : 0 ≤ a / x := div_nonneg (le_of_lt ha) (le_of_lt hxpos)
    simp only [d, G, R, scalarToTriple, if_neg hxne, targetFunctional,
      ENNReal.toReal_ofReal hadiv]
    field_simp
  have hweight : Integrable (fun x => (d x).toReal * G x) ω := by
    have h := hRint.const_mul (a * b)
    exact h.congr (hae.mono fun x hx => (hpoint x hx).symm)
  have hdens : Integrable G (ω.withDensity d) := by
    exact (integrable_withDensity_iff_integrable_smul' hd hdtop).2
      (by simpa only [smul_eq_mul] using hweight)
  have hdirac : Integrable G (Measure.dirac 0) :=
    integrable_dirac (by simp)
  have hsum : Integrable G (reweightedScalar a ω) := by
    unfold reweightedScalar
    exact (hdirac.smul_measure ENNReal.ofReal_ne_top).add_measure hdens
  calc
    (∫ t, targetFunctional t ∂triplePrior b a q ω) =
        ∫ x, G x ∂reweightedScalar a ω := by
          exact integral_map hmap.aemeasurable (by
            unfold targetFunctional
            fun_prop)
    _ = ∫ x, G x ∂ω.withDensity d := by
      rw [reweightedScalar, integral_add_measure
        (hdirac.smul_measure ENNReal.ofReal_ne_top) hdens,
        integral_smul_measure, integral_dirac]
      simp [G, targetFunctional, scalarToTriple]
    _ = ∫ x, (d x).toReal * G x ∂ω := by
      rw [integral_withDensity_eq_integral_toReal_smul hd hdtop]
      simp only [smul_eq_mul]
    _ = ∫ x, a * b * R x ∂ω :=
      integral_congr_ae (hae.mono fun x hx => hpoint x hx)
    _ = a * b * ∫ x, R x ∂ω := by rw [integral_const_mul]
    _ = _ := rfl

end Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

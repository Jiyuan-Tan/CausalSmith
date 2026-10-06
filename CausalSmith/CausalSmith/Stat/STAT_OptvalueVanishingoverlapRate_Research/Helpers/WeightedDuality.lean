module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.WeightedApproximation
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Alternation
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Weighted dual comparison and common-atom normalization

Roadmap equation (2): moment matching and the mean-one normalization bound
the constrained prior separation by four times the best weighted error.
Equations (6)--(7): adding the same atom to the two Jordan parts produces
probability priors of mean one without changing their moment or functional
differences. The weighted dual witness for the reverse comparison remains
to be built.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory


-- @node: commonAtom_location
/-- Weighted normalization places the common atom between one half and two. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:ht,hu,hnorm), the [stated conclusion](goal) holds. -/
lemma commonAtom_location (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hnorm : t + u = 1 / 2) :
    t ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ (1 - u) / (1 - t) ∧
      (1 - u) / (1 - t) ≤ 2 := by
  have htupper : t ≤ 1 / 2 := by linarith
  have hden : 0 < 1 - t := by linarith
  refine ⟨htupper, (le_div_iff₀ hden).2 ?_, (div_le_iff₀ hden).2 ?_⟩ <;> linarith


-- @node: integrable_of_supported_Icc
/-- A continuous function on the supporting interval is integrable; no extra moment-integrability assumption is needed for the compactly supported witness. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hsupp,hf), the [stated conclusion](goal) holds. -/
lemma integrable_of_supported_Icc (μ : Measure ℝ) [IsFiniteMeasure μ]
    (M : ℝ) (hsupp : μ (Set.Icc 0 M)ᶜ = 0) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 M)) : Integrable f μ := by
  have hrestrict : μ.restrict (Set.Icc 0 M) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by exact mem_ae_iff.mpr hsupp)
  have hi := hf.integrableOn_compact (μ := μ) isCompact_Icc
  simpa only [IntegrableOn, hrestrict] using hi


-- @node: commonAtom_probability
/-- Filling the missing mass by a Dirac atom yields a probability measure. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:ht), the [stated conclusion](goal) holds. -/
lemma commonAtom_probability (μ : Measure ℝ) [IsFiniteMeasure μ]
    (ht : (μ Set.univ).toReal ≤ 1) (z₀ : ℝ) :
    IsProbabilityMeasure
      (μ + ENNReal.ofReal (1 - (μ Set.univ).toReal) • Measure.dirac z₀) := by
  constructor
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ z₀), smul_eq_mul, mul_one]
  conv_lhs => lhs; rw [← ENNReal.ofReal_toReal (measure_ne_top μ Set.univ)]
  rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg (sub_nonneg.mpr ht)]
  simp


-- @node: commonAtom_support
/-- Adding the common atom preserves support when its location is in the interval. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hsupp,hz₀), the [stated conclusion](goal) holds. -/
lemma commonAtom_support (μ : Measure ℝ) (M t z₀ : ℝ)
    (hsupp : μ (Set.Icc 0 M)ᶜ = 0) (hz₀ : z₀ ∈ Set.Icc 0 M) :
    (μ + ENNReal.ofReal (1 - t) • Measure.dirac z₀) (Set.Icc 0 M)ᶜ = 0 := by
  simp [Measure.add_apply, Measure.smul_apply, hsupp, hz₀]


-- @node: commonAtom_integral
/-- The integral under a completed measure is the old integral plus the atom's contribution. This applies to moments and to the weighted objective. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:ht,hf), the [stated conclusion](goal) holds. -/
lemma commonAtom_integral (μ : Measure ℝ) (t z₀ : ℝ) (ht : t ≤ 1)
    (f : ℝ → ℝ) (hf : Integrable f μ) :
    (∫ z, f z ∂(μ + ENNReal.ofReal (1 - t) • Measure.dirac z₀)) =
      (∫ z, f z ∂μ) + (1 - t) * f z₀ := by
  have hi : Integrable f (ENNReal.ofReal (1 - t) • Measure.dirac z₀) :=
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  rw [integral_add_measure hf hi, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ht)]
  rfl


-- @node: commonAtomCompletion_constrained
/-- Two supported Jordan parts of a weighted-normalized moment annihilator complete to feasible priors, with the exact common-atom construction (6)--(7). All moment integrability follows from compact support. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hK,hM,hdom,hsuppp,hsuppm,hmass,hmom,hnorm), the [stated conclusion](goal) holds. -/
lemma commonAtomCompletion_constrained (K : ℕ) (M : ℝ) (hK : 1 ≤ K)
    (hM : 2 ≤ M) (σp σm : Measure ℝ) (hdom : CommonAtomDomain σp σm)
    (hsuppp : σp (Set.Icc 0 M)ᶜ = 0) (hsuppm : σm (Set.Icc 0 M)ᶜ = 0)
    (hmass : σp Set.univ = σm Set.univ)
    (hmom : ∀ j : ℕ, j ≤ K → (∫ z, z ^ j ∂σp) = (∫ z, z ^ j ∂σm))
    (hnorm : (σp Set.univ).toReal + (∫ z, z ∂σp) = 1 / 2) :
    ∃ p : ConstrainedPriorPair K M,
      commonAtomCompletion σp σm hdom = (p.ν₀, p.ν₁) := by
  let : IsFiniteMeasure σp := hdom.1
  let : IsFiniteMeasure σm := hdom.2.1
  let t := (σp Set.univ).toReal
  let u := ∫ z, z ∂σp
  let z₀ := (1 - u) / (1 - t)
  have hu : 0 ≤ u := integral_nonneg_of_ae
    (by filter_upwards [show ∀ᵐ z ∂σp, z ∈ Set.Icc 0 M from
      by exact mem_ae_iff.mpr hsuppp] with z hz; exact hz.1)
  have hloc := commonAtom_location t u ENNReal.toReal_nonneg hu hnorm
  have ht : t ≤ 1 := by linarith [hloc.1]
  have hz₀ : z₀ ∈ Set.Icc 0 M := ⟨by linarith [hloc.2.1],
    le_trans hloc.2.2 hM⟩
  have hm : (σm Set.univ).toReal = t := by dsimp [t]; rw [hmass]
  have hmeanm : (∫ z, z ∂σm) = u := by
    simpa only [pow_one] using (hmom 1 hK).symm
  have hmean : u + (1 - t) * z₀ = 1 := by
    have hden : 1 - t ≠ 0 := by linarith [hloc.1]
    dsimp [z₀]
    field_simp
    ring
  refine ⟨{
    ν₀ := σm + ENNReal.ofReal (1 - t) • Measure.dirac z₀
    ν₁ := σp + ENNReal.ofReal (1 - t) • Measure.dirac z₀
    prob₀ := ?_
    prob₁ := commonAtom_probability σp ht z₀
    supp₀ := commonAtom_support σm M t z₀ hsuppm hz₀
    supp₁ := commonAtom_support σp M t z₀ hsuppp hz₀
    mean₀ := ?_
    mean₁ := ?_
    moments := ?_ }, rfl⟩
  · simpa only [hm] using commonAtom_probability σm (by rw [hm]; exact ht) z₀
  · rw [commonAtom_integral σm t z₀ ht _ hdom.2.2.2.1, hmeanm]
    exact hmean
  · rw [commonAtom_integral σp t z₀ ht _ hdom.2.2.1]
    exact hmean
  · intro j hj
    have hp := integrable_of_supported_Icc σp M hsuppp (fun z => z ^ j)
      (by fun_prop)
    have hm' := integrable_of_supported_Icc σm M hsuppm (fun z => z ^ j)
      (by fun_prop)
    rw [commonAtom_integral σm t z₀ ht _ hm', commonAtom_integral σp t z₀ ht _ hp,
      hmom j hj]


-- @node: commonAtomCompletion_gap
/-- The identical added atom cancels from every integrable functional gap. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hdom,ht,hp,hm), the [stated conclusion](goal) holds. -/
lemma commonAtomCompletion_gap (σp σm : Measure ℝ) (hdom : CommonAtomDomain σp σm)
    (ht : (σp Set.univ).toReal ≤ 1) (f : ℝ → ℝ)
    (hp : Integrable f σp) (hm : Integrable f σm) :
    (∫ z, f z ∂(commonAtomCompletion σp σm hdom).2) -
      (∫ z, f z ∂(commonAtomCompletion σp σm hdom).1) =
      (∫ z, f z ∂σp) - (∫ z, f z ∂σm) := by
  dsimp [commonAtomCompletion]
  rw [commonAtom_integral σp _ _ ht f hp, commonAtom_integral σm _ _ ht f hm]
  ring

/-- Compact support makes the weighted objective integrable, so the common-atom completion preserves its gap without any additional regularity hypothesis. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hdom,hsuppp,hsuppm,ht), the [stated conclusion](goal) holds. -/
lemma commonAtomCompletion_phiEps_gap (σp σm : Measure ℝ)
    (hdom : CommonAtomDomain σp σm) (M ε : ℝ)
    (hsuppp : σp (Set.Icc 0 M)ᶜ = 0) (hsuppm : σm (Set.Icc 0 M)ᶜ = 0)
    (ht : (σp Set.univ).toReal ≤ 1) :
    (∫ z, phiEpsFormula ε z ∂(commonAtomCompletion σp σm hdom).2) -
      (∫ z, phiEpsFormula ε z ∂(commonAtomCompletion σp σm hdom).1) =
      (∫ z, phiEpsFormula ε z ∂σp) - (∫ z, phiEpsFormula ε z ∂σm) := by
  let : IsFiniteMeasure σp := hdom.1
  let : IsFiniteMeasure σm := hdom.2.1
  have hc : ContinuousOn (phiEpsFormula ε) (Set.Icc 0 M) := by
    unfold phiEpsFormula
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro z hz
      linarith [hz.1]
  exact commonAtomCompletion_gap σp σm hdom ht (phiEpsFormula ε)
    (integrable_of_supported_Icc σp M hsuppp _ hc)
    (integrable_of_supported_Icc σm M hsuppm _ hc)


-- @node: constrainedPriorPair_polynomial_integrals
/-- Matching monomial moments matches every polynomial of the permitted degree. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp), the [stated conclusion](goal) holds. -/
lemma constrainedPriorPair_polynomial_integrals {K : ℕ} {M : ℝ}
    (P : ConstrainedPriorPair K M) (p : Polynomial ℝ) (hp : p.natDegree ≤ K) :
    (∫ z, p.eval z ∂P.ν₀) = (∫ z, p.eval z ∂P.ν₁) := by
  let := P.prob₀
  let := P.prob₁
  have hpoly : (fun z => p.eval z) =
      (fun z => ∑ j ∈ Finset.range (K + 1), p.coeff j * z ^ j) := by
    funext z
    exact Polynomial.eval_eq_sum_range' (by omega) z
  have hi (μ : Measure ℝ) [IsFiniteMeasure μ]
      (hs : μ (Set.Icc 0 M)ᶜ = 0) (j : ℕ) :
      Integrable (fun z => p.coeff j * z ^ j) μ :=
    integrable_of_supported_Icc μ M hs _ (by fun_prop)
  rw [hpoly, integral_finsetSum _ (fun j _ => hi P.ν₀ P.supp₀ j),
    integral_finsetSum _ (fun j _ => hi P.ν₁ P.supp₁ j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, integral_const_mul, P.moments j (by
    have := Finset.mem_range.mp hj
    omega)]

/-- Compactness bounds each polynomial's weighted residual, and its supremum controls the residual pointwise on the supporting interval. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
lemma weightedPolynomial_error_bound (M ε : ℝ) (hM : 0 ≤ M)
    (p : Polynomial ℝ) :
    let e := sSup ((fun z : ℝ => |phiEpsFormula ε z - p.eval z| / (1 + z)) '' Set.Icc 0 M)
    0 ≤ e ∧ ∀ z ∈ Set.Icc 0 M, |phiEpsFormula ε z - p.eval z| ≤ e * (1 + z) := by
  dsimp only
  have hc : ContinuousOn (fun z : ℝ =>
      |phiEpsFormula ε z - p.eval z| / (1 + z)) (Set.Icc 0 M) := by
    unfold phiEpsFormula
    apply ContinuousOn.div
    · apply ContinuousOn.abs
      apply ContinuousOn.sub
      · apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro z hz; linarith [hz.1]
      · fun_prop
    · fun_prop
    · intro z hz; linarith [hz.1]
  have hb := isCompact_Icc.bddAbove_image hc
  have hz0 : (0 : ℝ) ∈ Set.Icc 0 M := ⟨le_rfl, hM⟩
  refine ⟨le_trans (by positivity)
    (le_csSup hb (Set.mem_image_of_mem _ hz0)), ?_⟩
  intro z hz
  exact (div_le_iff₀ (by linarith [hz.1])).mp
    (le_csSup hb (Set.mem_image_of_mem _ hz))

/-- Mean-one probability priors integrate the residual envelope to twice its weighted error; moment matching therefore bounds their gap by four times it (roadmap equation (2), before taking the infimum). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM,hp), the [stated conclusion](goal) holds. -/
lemma constrainedPriorPair_gap_le_polynomial_error {K : ℕ} {M : ℝ}
    (P : ConstrainedPriorPair K M) (ε : ℝ) (hM : 0 ≤ M)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ K) :
    |(∫ z, phiEpsFormula ε z ∂P.ν₁) - (∫ z, phiEpsFormula ε z ∂P.ν₀)| ≤
      4 * sSup ((fun z : ℝ => |phiEpsFormula ε z - p.eval z| / (1 + z)) '' Set.Icc 0 M) := by
  let := P.prob₀
  let := P.prob₁
  let e := sSup ((fun z : ℝ => |phiEpsFormula ε z - p.eval z| / (1 + z)) '' Set.Icc 0 M)
  have hb := weightedPolynomial_error_bound M ε hM p
  have hc : ContinuousOn (phiEpsFormula ε) (Set.Icc 0 M) := by
    unfold phiEpsFormula
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro z hz; linarith [hz.1]
  have hi (μ : Measure ℝ) [IsProbabilityMeasure μ]
      (hs : μ (Set.Icc 0 M)ᶜ = 0) :
      Integrable (phiEpsFormula ε) μ ∧ Integrable (fun z => p.eval z) μ :=
    ⟨integrable_of_supported_Icc μ M hs _ hc,
      integrable_of_supported_Icc μ M hs _ (by fun_prop)⟩
  have hres (μ : Measure ℝ) [IsProbabilityMeasure μ]
      (hs : μ (Set.Icc 0 M)ᶜ = 0) (hmean : (∫ z, z ∂μ) = 1) :
      |∫ z, phiEpsFormula ε z - p.eval z ∂μ| ≤ 2 * e := by
    have hid := integrable_of_supported_Icc μ M hs (fun z => z) (by fun_prop)
    have hw : Integrable (fun z : ℝ => e * (1 + z)) μ :=
      (integrable_const 1 |>.add hid).const_mul e
    calc
      |∫ z, phiEpsFormula ε z - p.eval z ∂μ| ≤
          ∫ z, |phiEpsFormula ε z - p.eval z| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ z, e * (1 + z) ∂μ := integral_mono_ae
        ((hi μ hs).1.sub (hi μ hs).2).abs hw (by
          filter_upwards [show ∀ᵐ z ∂μ, z ∈ Set.Icc 0 M from
            mem_ae_iff.mpr hs] with z hz
          exact hb.2 z hz)
      _ = 2 * e := by
        rw [integral_const_mul, integral_add (integrable_const 1) hid, hmean]
        simp
        ring
  have heq : (∫ z, phiEpsFormula ε z ∂P.ν₁) - (∫ z, phiEpsFormula ε z ∂P.ν₀) =
      (∫ z, phiEpsFormula ε z - p.eval z ∂P.ν₁) -
        (∫ z, phiEpsFormula ε z - p.eval z ∂P.ν₀) := by
    rw [integral_sub (hi P.ν₁ P.supp₁).1 (hi P.ν₁ P.supp₁).2,
      integral_sub (hi P.ν₀ P.supp₀).1 (hi P.ν₀ P.supp₀).2,
      constrainedPriorPair_polynomial_integrals P p hp]
    ring
  rw [heq]
  have ha := abs_sub_le (∫ z, phiEpsFormula ε z - p.eval z ∂P.ν₁)
    0 (∫ z, phiEpsFormula ε z - p.eval z ∂P.ν₀)
  simp only [sub_zero, zero_sub, abs_neg] at ha
  have h0 := hres P.ν₀ P.supp₀ P.mean₀
  have h1 := hres P.ν₁ P.supp₁ P.mean₁
  change _ ≤ 4 * e
  linarith


-- @node: constrainedPriorPair_nonempty
/-- The identical Dirac priors at one make the feasible set nonempty. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
lemma constrainedPriorPair_nonempty (K : ℕ) (M : ℝ) (hM : 1 ≤ M) :
    Nonempty (ConstrainedPriorPair K M) := by
  refine ⟨{
    ν₀ := Measure.dirac 1
    ν₁ := Measure.dirac 1
    prob₀ := inferInstance
    prob₁ := inferInstance
    supp₀ := ?_
    supp₁ := ?_
    mean₀ := ?_
    mean₁ := ?_
    moments := fun _ _ => rfl }⟩ <;> simp [hM]

/-- Taking the polynomial infimum and the feasible-prior supremum proves the upper half of the weighted dual comparison (roadmap equations (2) and (8)). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
lemma constrainedPriorSeparation_le_four_weightedApproxError
    (K : ℕ) (M ε : ℝ) (hM : 1 ≤ M) :
    constrainedPriorSeparationFormula K M ε ≤ 4 * weightedApproxError K M ε := by
  have hnonempty : Nonempty (ConstrainedPriorPair K M) :=
    constrainedPriorPair_nonempty K M hM
  unfold constrainedPriorSeparationFormula
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨P, rfl⟩
  have hne : {e : ℝ | ∃ p : Polynomial ℝ, p.natDegree ≤ K ∧
      e = sSup ((fun z : ℝ => |phiEpsFormula ε z - p.eval z| / (1 + z)) ''
        Set.Icc 0 M)}.Nonempty := by
    refine ⟨_, 0, ?_, rfl⟩
    simp
  have hle : |(∫ z, phiEpsFormula ε z ∂P.ν₁) - (∫ z, phiEpsFormula ε z ∂P.ν₀)| / 4 ≤
      weightedApproxError K M ε := by
    apply le_csInf hne
    rintro e ⟨p, hp, rfl⟩
    have hbound := constrainedPriorPair_gap_le_polynomial_error P ε
      (by linarith) p hp
    linarith
  linarith

end CausalSmith.Stat.OptvalueVanishingoverlapRate

module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.Occupancy
/-! Actual conditional design laws and cross-treatment pair moments. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- The actual design distribution conditioned on a public cell. -/
-- @node: conditionalDesignLaw
noncomputable def conditionalDesignLaw (h : ℝ) (k : ℕ) (P : CausalLaw)
    (j : Fin k) : Measure Covariate :=
  ((PX P) (cell h k j))⁻¹ • (PX P).restrict (cell h k j)

/-- Every admissible public cell has a normalized conditional design law.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: conditionalDesignLaw_probability
lemma conditionalDesignLaw_probability (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) (j : Fin k) :
    IsProbabilityMeasure (conditionalDesignLaw h k P j) := by
  let : IsProbabilityMeasure (PX P) := Measure.isProbabilityMeasure_map measurable_X.aemeasurable
  have hp : 0 < cellMass h k P j := lt_of_lt_of_le
    (half_pos (cell_endpoint_bounds k h hk hh j).2.2.2)
    (cellMass_density_bounds k h hk hh P hP j).1
  have hz : (PX P) (cell h k j) ≠ 0 := by
    intro hz
    simp [cellMass, measureReal_def, hz] at hp
  refine ⟨?_⟩
  simp only [conditionalDesignLaw, Measure.smul_apply,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hz (measure_ne_top _ _)

/-- Conditional design integrals retain the actual within-cell density.  [the theorem's stated inputs and assumptions](hyp:f), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,h,P,j). -/
-- @node: conditionalDesignLaw_integral
lemma conditionalDesignLaw_integral (k : ℕ) (h : ℝ) (P : CausalLaw) (j : Fin k)
    (f : Covariate → ℝ) :
    (∫ x, f x ∂conditionalDesignLaw h k P j) =
      (∫ x in cell h k j, f x ∂PX P) / cellMass h k P j := by
  rw [conditionalDesignLaw, integral_smul_measure, ENNReal.toReal_inv]
  simp only [cellMass, measureReal_def, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Two independent conditional covariates belong to their conditioning cell almost surely.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: conditionalDesignLaw_pair_mem
lemma conditionalDesignLaw_pair_mem (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) (j : Fin k) :
    ∀ᵐ z ∂(conditionalDesignLaw h k P j).prod (conditionalDesignLaw h k P j),
      z.1 ∈ cell h k j ∧ z.2 ∈ cell h k j := by
  let μ := conditionalDesignLaw h k P j
  let : IsProbabilityMeasure μ := conditionalDesignLaw_probability k h hk hh P hP j
  have hm : ∀ᵐ x ∂μ, x ∈ cell h k j :=
    Measure.ae_smul_measure (ae_restrict_mem (measurableSet_cell h k j)) _
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_cell h k j).preimage measurable_fst |>.inter
      ((measurableSet_cell h k j).preimage measurable_snd))).mpr
  filter_upwards [hm] with x hx
  filter_upwards [hm] with y hy
  exact ⟨hx, hy⟩

/-- Cross-treatment numerator at two selected covariates. -/
-- @node: designPairNumerator
def designPairNumerator (P : CausalLaw) (z : Covariate × Covariate) : ℝ :=
  P.e z.1 * (1 - P.e z.2) * (P.mu1 z.1 - P.mu0 z.2) +
    P.e z.2 * (1 - P.e z.1) * (P.mu1 z.2 - P.mu0 z.1)

/-- Cross-treatment probability at two selected covariates. -/
-- @node: designPairDenominator
def designPairDenominator (P : CausalLaw) (z : Covariate × Covariate) : ℝ :=
  P.e z.1 * (1 - P.e z.2) + P.e z.2 * (1 - P.e z.1)

/-- The propensity, arm means, and arm-response regressions are integrable under any finite
covariate measure, because the complete model gives everywhere binary-mean bounds.  [the theorem's stated inputs and assumptions](hyp:μ), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:P,hP). -/
-- @node: design_regressions_integrable
lemma design_regressions_integrable (P : CausalLaw) (hP : CompleteModel P)
    (μ : Measure Covariate) [IsFiniteMeasure μ] :
    Integrable P.e μ ∧ Integrable (fun x => 1 - P.e x) μ ∧
    Integrable (fun x => P.e x * P.mu1 x) μ ∧
    Integrable (fun x => (1 - P.e x) * P.mu0 x) μ := by
  have hme := P.e_measurable
  have hmm0 := P.mu0_measurable
  have hmm1 := P.mu1_measurable
  have he : ∀ x, P.e x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    constructor <;> linarith [(hP.overlap x).1, (hP.overlap x).2]
  have hm0 (x) : P.mu0 x ∈ Set.Icc (0 : ℝ) 1 := arm_mean_mem_Icc P hP false x
  have hm1 (x) : P.mu1 x ∈ Set.Icc (0 : ℝ) 1 := arm_mean_mem_Icc P hP true x
  have hi : Integrable P.e μ := Integrable.of_mem_Icc 0 1 (by fun_prop) (ae_of_all _ he)
  refine ⟨hi, (integrable_const _).sub hi, ?_, ?_⟩
  · apply Integrable.of_mem_Icc 0 1 (by fun_prop)
    exact ae_of_all _ (fun x => ⟨mul_nonneg (he x).1 (hm1 x).1,
      mul_le_one₀ (he x).2 (hm1 x).1 (hm1 x).2⟩)
  · apply Integrable.of_mem_Icc 0 1 (by fun_prop)
    exact ae_of_all _ (fun x => ⟨mul_nonneg (by linarith [(he x).2]) (hm0 x).1,
      mul_le_one₀ (by linarith [(he x).1]) (hm0 x).1 (hm0 x).2⟩)

/-- Factorization of independent design pairs gives the exact numerator formula.  [the theorem's stated inputs and assumptions](hyp:μ), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:P,hP). -/
-- @node: design_pair_numerator_moment
lemma design_pair_numerator_moment (P : CausalLaw) (hP : CompleteModel P)
    (μ : Measure Covariate) [IsProbabilityMeasure μ] :
    Integrable (designPairNumerator P) (μ.prod μ) ∧
    (∫ z, designPairNumerator P z ∂μ.prod μ) =
      2 * ((∫ x, P.e x * P.mu1 x ∂μ) - (∫ x, P.e x ∂μ) *
        ((∫ x, (1 - P.e x) * P.mu0 x ∂μ) + (∫ x, P.e x * P.mu1 x ∂μ))) := by
  obtain ⟨he, hc, ht, hu⟩ := design_regressions_integrable P hP μ
  have hfun : designPairNumerator P = (fun z =>
      (P.e z.1 * P.mu1 z.1) * (1 - P.e z.2) -
      P.e z.1 * ((1 - P.e z.2) * P.mu0 z.2) +
      (1 - P.e z.1) * (P.e z.2 * P.mu1 z.2) -
      ((1 - P.e z.1) * P.mu0 z.1) * P.e z.2) := by
    funext z
    unfold designPairNumerator
    ring
  rw [hfun]
  dsimp only
  refine ⟨((ht.mul_prod hc).sub (he.mul_prod hu)).add (hc.mul_prod ht) |>.sub
    (hu.mul_prod he), ?_⟩
  have hsub := integral_sub (((ht.mul_prod hc).sub (he.mul_prod hu)).add (hc.mul_prod ht))
    (hu.mul_prod he)
  have hadd := integral_add ((ht.mul_prod hc).sub (he.mul_prod hu)) (hc.mul_prod ht)
  have hsub' := integral_sub (ht.mul_prod hc) (he.mul_prod hu)
  simp only [Pi.add_apply, Pi.sub_apply] at hsub hadd hsub'
  rw [hsub, hadd, hsub',
    integral_prod_mul (fun x => P.e x * P.mu1 x) (fun x => 1 - P.e x),
    integral_prod_mul P.e (fun x => (1 - P.e x) * P.mu0 x),
    integral_prod_mul (fun x => 1 - P.e x) (fun x => P.e x * P.mu1 x),
    integral_prod_mul (fun x => (1 - P.e x) * P.mu0 x) P.e]
  rw [integral_sub (integrable_const _) he]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- Factorization of independent design pairs gives the exact denominator formula.  [the theorem's stated inputs and assumptions](hyp:μ), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:P,hP). -/
-- @node: design_pair_denominator_moment
lemma design_pair_denominator_moment (P : CausalLaw) (hP : CompleteModel P)
    (μ : Measure Covariate) [IsProbabilityMeasure μ] :
    Integrable (designPairDenominator P) (μ.prod μ) ∧
    (∫ z, designPairDenominator P z ∂μ.prod μ) =
      2 * (∫ x, P.e x ∂μ) * (1 - ∫ x, P.e x ∂μ) := by
  obtain ⟨he, hc, _, _⟩ := design_regressions_integrable P hP μ
  have hfun : designPairDenominator P =
      (fun z => P.e z.1 * (1 - P.e z.2) + (1 - P.e z.1) * P.e z.2) := by
    funext z
    unfold designPairDenominator
    ring
  rw [hfun]
  dsimp only
  refine ⟨(he.mul_prod hc).add (hc.mul_prod he), ?_⟩
  rw [integral_add (he.mul_prod hc) (hc.mul_prod he)]
  rw [integral_prod_mul P.e (fun x => 1 - P.e x),
    integral_prod_mul (fun x => 1 - P.e x) P.e]
  rw [integral_sub (integrable_const _) he]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- Integration of the pointwise causal certificate preserves the density-weighted cell bias.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: conditional_design_pair_bias
lemma conditional_design_pair_bias (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) (j : Fin k) :
    |(∫ z, designPairNumerator P z
        ∂(conditionalDesignLaw h k P j).prod (conditionalDesignLaw h k P j)) -
      theta P * (∫ z, designPairDenominator P z
        ∂(conditionalDesignLaw h k P j).prod (conditionalDesignLaw h k P j))| ≤
      bias h k * (∫ z, designPairDenominator P z
        ∂(conditionalDesignLaw h k P j).prod (conditionalDesignLaw h k P j)) := by
  let μ := conditionalDesignLaw h k P j
  let : IsProbabilityMeasure μ := conditionalDesignLaw_probability k h hk hh P hP j
  have hN := (design_pair_numerator_moment P hP μ).1
  have hD := (design_pair_denominator_moment P hP μ).1
  have hb : ∀ᵐ z ∂μ.prod μ,
      |designPairNumerator P z - theta P * designPairDenominator P z| ≤
        bias h k * designPairDenominator P z := by
    filter_upwards [conditionalDesignLaw_pair_mem k h hk hh P hP j] with z hz
    exact (cell_cross_treatment_certificate k h hk hh P hP j z.1 z.2 hz.1 hz.2).2
  calc
    _ = |∫ z, designPairNumerator P z - theta P * designPairDenominator P z
        ∂μ.prod μ| := by rw [integral_sub hN (hD.const_mul _), integral_const_mul]
    _ ≤ ∫ z, |designPairNumerator P z - theta P * designPairDenominator P z|
        ∂μ.prod μ := abs_integral_le_integral_abs
    _ ≤ ∫ z, bias h k * designPairDenominator P z ∂μ.prod μ :=
      integral_mono_ae (hN.sub (hD.const_mul _)).abs (hD.const_mul _) hb
    _ = _ := integral_const_mul _ _
end CausalSmith.Stat.PrivateCateRoughdesign

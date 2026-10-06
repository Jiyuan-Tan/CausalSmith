module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerHellinger
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! Identification of the rare-mark likelihood with the original conditional mark law. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
variable (κ : Params) (n : ℕ)

/-- The six reference atom weights times the likelihood are the original treatment/outcome weights. -/
-- @node: lower_density_atom_weights
lemma lower_density_atom_weights (hκ : κ.Valid) (hn : 2 ≤ n)
    (ε : Bool) (v : Signs κ n) (x : unitInterval) (z : Bool) :
    let p := if z then lowerP0 else 1-lowerP0
    let e := if z then lowerPropensity κ n v x else 1-lowerPropensity κ n v x
    p*(lowerRare κ n/2)*lowerDensity κ n (lowerA κ n) (sign ε*lowerB κ n) v x (z,lowerAmplitude κ n) =
      e*(lowerRare κ n/2+lowerMean κ n ε v z x/(2*lowerAmplitude κ n)) ∧
    p*(lowerRare κ n/2)*lowerDensity κ n (lowerA κ n) (sign ε*lowerB κ n) v x (z,-lowerAmplitude κ n) =
      e*(lowerRare κ n/2-lowerMean κ n ε v z x/(2*lowerAmplitude κ n)) ∧
    p*(1-lowerRare κ n)*lowerDensity κ n (lowerA κ n) (sign ε*lowerB κ n) v x (z,0) =
      e*(1-lowerRare κ n) := by
  have hBpos := (lower_rare_scale κ n hκ hn).1
  have hB := hBpos.ne'
  have hr : lowerRare κ n ≠ 0 := by
    apply ne_of_gt
    unfold lowerRare
    positivity
  cases z <;>
    simp only [Bool.false_eq_true, ↓reduceIte, lowerDensity, markU, markV,
      lowerMean, lowerPropensity, lowerP0] <;>
    constructor
  all_goals
    try constructor
    all_goals field_simp
    all_goals ring

/-- The constructed conditional record marks are exactly a tilt of the common six-atom reference. -/
-- @node: lower_recordMeasure_withDensity
lemma lower_recordMeasure_withDensity (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (ε : Bool) (v : Signs κ n) (x : unitInterval) :
    recordMeasure (lowerPropensity κ n v) (lowerOutcomeKernel κ n ε v) x =
      (referenceMarks κ n).withDensity
        (fun z => ENNReal.ofReal (lowerDensity κ n (lowerA κ n) (sign ε*lowerB κ n) v x z)) := by
  have hd : κ.Valid ∧ boundary κ ≤ 1 ∧ 2 ≤ n := ⟨hκ,hb,hn⟩
  have hBpos := (lower_rare_scale κ n hκ hn).1
  have hr : 0 ≤ lowerRare κ n := by unfold lowerRare; positivity
  have hp := (lower_law_versions κ n hd ε v).1 x
  have hw (z) := lower_atom_weights_nonneg κ n hκ hn ε v z x
  have hc (z) := lower_density_atom_weights κ n hκ hn ε v x z
  have hcoef (z : Bool) :
      let p := if z then lowerP0 else 1-lowerP0
      let e := if z then lowerPropensity κ n v x else 1-lowerPropensity κ n v x
      ENNReal.ofReal e * ENNReal.ofReal (lowerRare κ n/2+lowerMean κ n ε v z x/(2*lowerAmplitude κ n)) =
        ENNReal.ofReal p * ENNReal.ofReal (lowerRare κ n/2) *
          ENNReal.ofReal (lowerDensity κ n (lowerA κ n) (sign ε*lowerB κ n) v x (z,lowerAmplitude κ n)) ∧
      ENNReal.ofReal e * ENNReal.ofReal (lowerRare κ n/2-lowerMean κ n ε v z x/(2*lowerAmplitude κ n)) =
        ENNReal.ofReal p * ENNReal.ofReal (lowerRare κ n/2) *
          ENNReal.ofReal (lowerDensity κ n (lowerA κ n) (sign ε*lowerB κ n) v x (z,-lowerAmplitude κ n)) ∧
      ENNReal.ofReal e * ENNReal.ofReal (1-lowerRare κ n) =
        ENNReal.ofReal p * ENNReal.ofReal (1-lowerRare κ n) *
          ENNReal.ofReal (lowerDensity κ n (lowerA κ n) (sign ε*lowerB κ n) v x (z,0)) := by
    dsimp only
    have hp0 : 0 ≤ (if z then lowerP0 else 1-lowerP0) := by cases z <;> norm_num [lowerP0]
    have he0 : 0 ≤ (if z then lowerPropensity κ n v x else 1-lowerPropensity κ n v x) := by
      cases z
      · exact sub_nonneg.mpr hp.2
      · exact hp.1
    simp only [← ENNReal.ofReal_mul hp0,
      ← ENNReal.ofReal_mul (mul_nonneg hp0 (div_nonneg hr (by norm_num : (0 : ℝ) ≤ 2))),
      ← ENNReal.ofReal_mul (mul_nonneg hp0 (sub_nonneg.mpr (lower_rare_scale κ n hκ hn).2.1)),
      ← ENNReal.ofReal_mul he0]
    rw [← (hc z).1, ← (hc z).2.1, ← (hc z).2.2]
    exact ⟨rfl,rfl,rfl⟩
  unfold recordMeasure lowerOutcomeKernel
  simp only [Kernel.coe_mk]
  simp only [lowerOutcomeMeasure, referenceMarks,
    Measure.prod_add, Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.dirac_prod_dirac, smul_add, smul_smul,
    withDensity_add_measure, withDensity_smul_measure, dirac_withDensity]
  have ht := hcoef true
  have hf := hcoef false
  simp only [Bool.false_eq_true, ↓reduceIte] at ht hf
  rw [ht.1, ht.2.1, ht.2.2,
    hf.1, hf.2.1, hf.2.2]
  simp only [mul_comm, mul_left_comm, mul_assoc]
  abel

/-- The one-record law has the displayed likelihood against uniform covariates and reference marks. -/
-- @node: lower_prior_law_withDensity
lemma lower_prior_law_withDensity (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (ε : Bool) (v : Signs κ n) :
    (lowerPriorLaw κ n ε v).P =
      (design.prod (referenceMarks κ n)).withDensity
        (fun o => ENNReal.ofReal (lowerDensity κ n (lowerA κ n) (sign ε*lowerB κ n) v o.1 o.2)) := by
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hd : κ.Valid ∧ boundary κ ≤ 1 ∧ 2 ≤ n := ⟨hκ,hb,hn⟩
  letI := recordKernel_markov (lowerPropensity κ n v) (measurable_lowerPropensity κ n v)
    (lower_law_versions κ n hd ε v).1 (lowerOutcomeKernel κ n ε v)
    (lower_law_versions κ n hd ε v).2.1
  have hm : Measurable (fun o : O => ENNReal.ofReal
      (lowerDensity κ n (lowerA κ n) (sign ε*lowerB κ n) v o.1 o.2)) := by
    have hU : Measurable markU := measurable_of_countable _
    unfold lowerDensity markV lowerField lowerSquare lowerCutoff
    fun_prop
  rw [lowerPriorLaw, dif_pos hd]
  change (design ⊗ₘ recordKernel (lowerPropensity κ n v)
    (measurable_lowerPropensity κ n v) (lowerOutcomeKernel κ n ε v)) = _
  ext s hs
  rw [Measure.compProd_apply hs, withDensity_apply _ hs,
    ← lintegral_indicator hs, lintegral_prod _ (hm.indicator hs).aemeasurable]
  apply lintegral_congr
  intro x
  change recordMeasure (lowerPropensity κ n v) (lowerOutcomeKernel κ n ε v) x
    (Prod.mk x ⁻¹' s) = _
  rw [lower_recordMeasure_withDensity κ n hκ hb hn ε v x,
    withDensity_apply _ (measurable_prodMk_left hs),
    ← lintegral_indicator (measurable_prodMk_left hs)]
  apply lintegral_congr
  intro z
  by_cases hz : (x,z) ∈ s <;> simp [hz]

/-- Original one-record likelihoods are nonnegative on the common reference support. -/
-- @node: lower_prior_density_nonneg_ae
lemma lower_prior_density_nonneg_ae (hκ : κ.Valid) (hn : 2 ≤ n)
    (ε : Bool) (v : Signs κ n) :
    ∀ᵐ o ∂design.prod (referenceMarks κ n),
      0 ≤ lowerDensity κ n (lowerA κ n) (sign ε*lowerB κ n) v o.1 o.2 := by
  have ha := (lower_scale_small κ n hκ hn).2.1
  have hβ := (lower_scale_small κ n hκ hn).2.2
  have ht : |sign ε*lowerB κ n| ≤ lowerB κ n := by
    cases ε <;> simp [sign, abs_of_pos hβ.1]
  have hmark := reference_markV_scaled_bound κ n hκ hn (sign ε*lowerB κ n) ht
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  have hmeas : MeasurableSet {o : O | 0 ≤ lowerDensity κ n (lowerA κ n) (sign ε*lowerB κ n) v o.1 o.2} := by
    apply measurableSet_le measurable_const
    have hU : Measurable markU := measurable_of_countable _
    unfold lowerDensity markV lowerField lowerSquare lowerCutoff
    fun_prop
  apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
  filter_upwards [] with x
  filter_upwards [hmark] with z hz
  exact (by norm_num : (0 : ℝ) ≤ 1/2).trans
    (lower_density_half_le κ n (by omega) (lowerA κ n) (sign ε*lowerB κ n)
      (by simpa [abs_of_pos ha.1] using ha.2) v x z hz)

/-- Exact singleton cancellation identifies both original one-record mixtures with the common reference. -/
-- @node: lower_singleton_mixture_reference
lemma lower_singleton_mixture_reference (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (ε : Bool) :
    (Fintype.card (Signs κ n) : ℝ≥0∞)⁻¹ • ∑ v : Signs κ n, (lowerPriorLaw κ n ε v).P =
      design.prod (referenceMarks κ n) := by
  let μ := design.prod (referenceMarks κ n)
  let f := fun (v : Signs κ n) (o : O) =>
    ENNReal.ofReal (lowerDensity κ n (lowerA κ n) (sign ε*lowerB κ n) v o.1 o.2)
  have hm (v) : Measurable (f v) := by
    dsimp [f]
    have hU : Measurable markU := measurable_of_countable _
    unfold lowerDensity markV lowerField lowerSquare lowerCutoff
    fun_prop
  simp_rw [lower_prior_law_withDensity κ n hκ hb hn ε]
  change (Fintype.card (Signs κ n) : ℝ≥0∞)⁻¹ • ∑ v, μ.withDensity (f v) = μ
  rw [← Measure.sum_fintype, ← withDensity_tsum hm, ← withDensity_smul _ (by fun_prop)]
  have heq : (fun o => (Fintype.card (Signs κ n) : ℝ≥0∞)⁻¹ * ∑' v, f v o) =ᵐ[μ] fun _ => 1 := by
    have hnn := ae_all_iff.mpr (lower_prior_density_nonneg_ae κ n hκ hn ε)
    filter_upwards [hnn] with o ho
    rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun v _ => ho v)]
    have hcard : (Fintype.card (Signs κ n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have ha := (lower_scale_small κ n hκ hn).2.1
    have hβ := (lower_scale_small κ n hκ hn).2.2
    have ht : |sign ε*lowerB κ n| ≤ lowerB κ n := by
      cases ε <;> simp [sign, abs_of_pos hβ.1]
    have hc := singleton_cancellation κ n hκ hb hn (lowerA κ n) (sign ε*lowerB κ n)
      (by simpa [abs_of_pos ha.1] using le_rfl : |lowerA κ n| ≤ lowerA κ n) ht o.1 o.2
    have hsum : ∑ v : Signs κ n,
        lowerDensity κ n (lowerA κ n) (sign ε*lowerB κ n) v o.1 o.2 = Fintype.card (Signs κ n) := by
      field_simp at hc
      exact hc
    rw [hsum]
    simp only [ENNReal.ofReal_natCast]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero (α := Signs κ n)) (by simp)
  have heq' : ((Fintype.card (Signs κ n) : ℝ≥0∞)⁻¹ • ∑' v, f v) =ᵐ[μ] (fun _ => 1) := by
    filter_upwards [heq] with o ho
    simpa only [Pi.smul_apply, smul_eq_mul, ENNReal.tsum_apply] using ho
  rw [withDensity_congr_ae heq']
  exact withDensity_one

/-- The two original one-record sign mixtures coincide exactly, including frame transitions. -/
-- @node: lower_singleton_mixtures_equal
lemma lower_singleton_mixtures_equal (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n) :
    (Fintype.card (Signs κ n) : ℝ≥0∞)⁻¹ • ∑ v : Signs κ n, (lowerPriorLaw κ n true v).P =
    (Fintype.card (Signs κ n) : ℝ≥0∞)⁻¹ • ∑ v : Signs κ n, (lowerPriorLaw κ n false v).P := by
  rw [lower_singleton_mixture_reference κ n hκ hb hn true,
    lower_singleton_mixture_reference κ n hκ hb hn false]

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

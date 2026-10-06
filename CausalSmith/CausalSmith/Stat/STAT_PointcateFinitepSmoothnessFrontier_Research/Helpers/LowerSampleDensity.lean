module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerDensityIdentification
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerTensorization
public import Mathlib.MeasureTheory.Integral.Pi

/-! Product-density identification for the original rare-mark sample experiment. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- Independent coordinates with nonnegative integrable likelihoods have their product likelihood. -/
-- @node: finite_product_withDensity
lemma finite_product_withDensity {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : ι → Measure Ω) [∀ i, SigmaFinite (μ i)] (f : ι → Ω → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (hn : ∀ i x, 0 ≤ f i x)
    [∀ i, IsProbabilityMeasure ((μ i).withDensity (fun x => ENNReal.ofReal (f i x)))] :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hn i))]
    apply Finset.prod_congr rfl
    intro i _
    rw [withDensity_apply _ (hs i),
      ← ofReal_integral_eq_lintegral_ofReal (hf i).integrableOn]
    exact Filter.Eventually.of_forall (hn i)
  · exact (Integrable.fintype_prod hf).integrableOn
  · exact Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hn i (x i)))

variable (κ : Params) (n : ℕ)

/-- The nonnegative representative of the original one-record likelihood. -/
-- @node: lowerRecordLikelihood
def lowerRecordLikelihood (ε : Bool) (v : Signs κ n) (o : O) : ℝ :=
  max 0 (lowerDensity κ n (lowerA κ n) (sign ε*lowerB κ n) v o.1 o.2)

/-- The finite-prior sample likelihood against the product reference experiment. -/
-- @node: lowerSampleLikelihood
def lowerSampleLikelihood (ε : Bool) (o : Dataset n) : ℝ :=
  (Fintype.card (Signs κ n) : ℝ)⁻¹ * ∑ v : Signs κ n,
    ∏ i, lowerRecordLikelihood κ n ε v (o i)

/-- Clipping the likelihood below zero does not change its original weighted law. -/
-- @node: lower_record_likelihood_identification
lemma lower_record_likelihood_identification (hκ : κ.Valid) (hb : boundary κ ≤ 1)
    (hn : 2 ≤ n) (ε : Bool) (v : Signs κ n) :
    (lowerPriorLaw κ n ε v).P = (design.prod (referenceMarks κ n)).withDensity
      (fun o => ENNReal.ofReal (lowerRecordLikelihood κ n ε v o)) := by
  rw [lower_prior_law_withDensity κ n hκ hb hn ε v]
  congr 1
  funext o
  simp [lowerRecordLikelihood]

/-- The clipped record likelihood is Borel. -/
-- @node: measurable_lowerRecordLikelihood
@[fun_prop] lemma measurable_lowerRecordLikelihood (ε : Bool) (v : Signs κ n) :
    Measurable (lowerRecordLikelihood κ n ε v) := by
  unfold lowerRecordLikelihood lowerDensity lowerField lowerSquare lowerCutoff markV
  fun_prop

/-- The reference support bounds every original likelihood uniformly in its covariate. -/
-- @node: integrable_lowerRecordLikelihood
lemma integrable_lowerRecordLikelihood (hκ : κ.Valid) (hn : 2 ≤ n)
    (ε : Bool) (v : Signs κ n) :
    Integrable (lowerRecordLikelihood κ n ε v) (design.prod (referenceMarks κ n)) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  have ht : |sign ε*lowerB κ n| ≤ lowerB κ n := by
    cases ε <;> simp [sign, abs_of_pos (lower_scale_small κ n hκ hn).2.2.1]
  have hz := reference_markV_scaled_bound κ n hκ hn (sign ε*lowerB κ n) ht
  have hz' : ∀ᵐ o ∂design.prod (referenceMarks κ n),
      |(sign ε*lowerB κ n)*markV κ n o.2.2| ≤ 1/4 :=
    (measurePreserving_snd (μ := design) (ν := referenceMarks κ n)).quasiMeasurePreserving.ae hz
  apply (integrable_const (3/2 : ℝ)).mono'
    (measurable_lowerRecordLikelihood κ n ε v).aestronglyMeasurable
  filter_upwards [hz'] with o ho
  have hA : |lowerA κ n| ≤ 1/1024 := by
    rw [abs_of_pos (lower_scale_small κ n hκ hn).2.1.1]
    exact (lower_scale_small κ n hκ hn).2.1.2
  have hd := (lower_density_derivative_ledger κ n (by omega) (lowerA κ n)
    (sign ε*lowerB κ n) hA v o.1 o.2 ho).1
  change |max 0 (lowerDensity κ n (lowerA κ n) (sign ε*lowerB κ n) v o.1 o.2)| ≤ _
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le (by norm_num) ((le_abs_self _).trans hd)

/-- The clipped sample likelihood is nonnegative everywhere. -/
-- @node: lowerSampleLikelihood_nonneg
lemma lowerSampleLikelihood_nonneg (ε : Bool) (o : Dataset n) :
    0 ≤ lowerSampleLikelihood κ n ε o := by
  unfold lowerSampleLikelihood
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun v _ => Finset.prod_nonneg
    (fun i _ => le_max_left 0 _))

/-- Finite sign averaging preserves integrability of independent record likelihoods. -/
-- @node: integrable_lowerSampleLikelihood
lemma integrable_lowerSampleLikelihood (hκ : κ.Valid) (hn : 2 ≤ n) (ε : Bool) :
    Integrable (lowerSampleLikelihood κ n ε)
      (Measure.pi (fun _ : Fin n => design.prod (referenceMarks κ n))) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro v _
  exact Integrable.fintype_prod (fun _ => integrable_lowerRecordLikelihood κ n hκ hn ε v)

/-- The original iid sample law is the product of its record likelihoods. -/
-- @node: lower_prior_sample_withDensity
lemma lower_prior_sample_withDensity (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (ε : Bool) (v : Signs κ n) :
    Measure.pi (fun _ : Fin n => (lowerPriorLaw κ n ε v).P) =
      (Measure.pi (fun _ : Fin n => design.prod (referenceMarks κ n))).withDensity
        (fun o => ENNReal.ofReal (∏ i, lowerRecordLikelihood κ n ε v (o i))) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  letI : IsProbabilityMeasure ((design.prod (referenceMarks κ n)).withDensity
      (fun o => ENNReal.ofReal (lowerRecordLikelihood κ n ε v o))) := by
    rw [← lower_record_likelihood_identification κ n hκ hb hn ε v]
    infer_instance
  simp_rw [lower_record_likelihood_identification κ n hκ hb hn ε v]
  exact finite_product_withDensity _ _
    (fun _ => integrable_lowerRecordLikelihood κ n hκ hn ε v)
    (fun _ _ => le_max_left _ _)

/-- Averaging product likelihoods identifies the original finite-prior sample law. -/
-- @node: lower_mixture_withDensity
lemma lower_mixture_withDensity (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (ε : Bool) :
    lowerMixture κ n ε =
      (Measure.pi (fun _ : Fin n => design.prod (referenceMarks κ n))).withDensity
        (fun o => ENNReal.ofReal (lowerSampleLikelihood κ n ε o)) := by
  let μ := Measure.pi (fun _ : Fin n => design.prod (referenceMarks κ n))
  let f := fun (v : Signs κ n) (o : Dataset n) =>
    ENNReal.ofReal (∏ i, lowerRecordLikelihood κ n ε v (o i))
  have hm (v) : Measurable (f v) := by dsimp [f]; fun_prop
  unfold lowerMixture
  simp_rw [lower_prior_sample_withDensity κ n hκ hb hn ε]
  change (Fintype.card (Signs κ n) : ℝ≥0∞)⁻¹ • ∑ v, μ.withDensity (f v) = _
  rw [← Measure.sum_fintype, ← withDensity_tsum hm, ← withDensity_smul _ (by fun_prop)]
  congr 1
  funext o
  simp only [lowerSampleLikelihood, ENNReal.tsum_apply, tsum_fintype, Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_mul (by positivity)]
  have hn0 (v : Signs κ n) : 0 ≤ ∏ i, lowerRecordLikelihood κ n ε v (o i) :=
    Finset.prod_nonneg (fun i _ => le_max_left _ _)
  rw [ENNReal.ofReal_sum_of_nonneg (fun v _ => hn0 v)]
  simp [f]

/-- Original record probability normalization also normalizes its real likelihood. -/
-- @node: lower_record_likelihood_integral_one
lemma lower_record_likelihood_integral_one (hκ : κ.Valid) (hb : boundary κ ≤ 1)
    (hn : 2 ≤ n) (ε : Bool) (v : Signs κ n) :
    (∫ o, lowerRecordLikelihood κ n ε v o ∂design.prod (referenceMarks κ n)) = 1 := by
  have h : ENNReal.ofReal (∫ o, lowerRecordLikelihood κ n ε v o
      ∂design.prod (referenceMarks κ n)) = 1 := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_lowerRecordLikelihood κ n hκ hn ε v)
      (Filter.Eventually.of_forall (fun _ => le_max_left _ _))]
    have he := congrArg (fun μ : Measure O => μ univ)
      (lower_record_likelihood_identification κ n hκ hb hn ε v)
    simpa [withDensity_apply] using he.symm
  have hn0 : 0 ≤ ∫ o, lowerRecordLikelihood κ n ε v o ∂design.prod (referenceMarks κ n) :=
    integral_nonneg (fun _ => le_max_left _ _)
  simpa [ENNReal.toReal_ofReal hn0] using congrArg ENNReal.toReal h

/-- The original finite-prior sample likelihood integrates to one. -/
-- @node: lower_sample_likelihood_integral_one
lemma lower_sample_likelihood_integral_one (hκ : κ.Valid) (hb : boundary κ ≤ 1)
    (hn : 2 ≤ n) (ε : Bool) :
    (∫ o, lowerSampleLikelihood κ n ε o
      ∂Measure.pi (fun _ : Fin n => design.prod (referenceMarks κ n))) = 1 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  unfold lowerSampleLikelihood
  rw [integral_const_mul, integral_finsetSum _ (fun v _ =>
    Integrable.fintype_prod (fun _ => integrable_lowerRecordLikelihood κ n hκ hn ε v))]
  simp_rw [integral_fintype_prod_eq_prod,
    lower_record_likelihood_integral_one κ n hκ hb hn ε]
  simp

/-- On reference marks, clipping leaves the conditional mixture density unchanged. -/
-- @node: lower_sample_likelihood_conditional
lemma lower_sample_likelihood_conditional (hκ : κ.Valid) (hn : 2 ≤ n)
    (ε : Bool) (x : Fin n → unitInterval) :
    (fun z => lowerSampleLikelihood κ n ε (fun i => (x i,z i))) =ᵐ[
      Measure.pi (fun _ : Fin n => referenceMarks κ n)]
      componentDensity κ n n x (lowerA κ n) (sign ε*lowerB κ n) := by
  letI : IsProbabilityMeasure (referenceMarks κ n) := reference_marks_probability κ n hκ hn
  have ht : |sign ε*lowerB κ n| ≤ lowerB κ n := by
    cases ε <;> simp [sign, abs_of_pos (lower_scale_small κ n hκ hn).2.2.1]
  have hz (i : Fin n) : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => referenceMarks κ n),
      |(sign ε*lowerB κ n)*markV κ n (z i).2| ≤ 1/4 :=
    (measurePreserving_eval (fun _ : Fin n => referenceMarks κ n) i).quasiMeasurePreserving.ae
      (reference_markV_scaled_bound κ n hκ hn (sign ε*lowerB κ n) ht)
  filter_upwards [ae_all_iff.mpr hz] with z hz
  unfold lowerSampleLikelihood componentDensity
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.prod_congr rfl
  intro i _
  unfold lowerRecordLikelihood
  exact max_eq_right ((by norm_num : (0 : ℝ) ≤ 1/2).trans
    (lower_density_half_le κ n (by omega) _ _
      (by simpa [abs_of_pos (lower_scale_small κ n hκ hn).2.1.1] using
        (lower_scale_small κ n hκ hn).2.1.2) v (x i) (z i) (hz i)))

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

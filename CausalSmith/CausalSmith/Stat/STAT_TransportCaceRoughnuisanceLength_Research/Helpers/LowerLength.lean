module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CellMoments
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Identification
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Length

/-! # Coverage averaging and continuum length for the lower experiment

Componentwise honesty passes to the finite sign mixture, and total variation
then transfers it to the center. Integrating inclusion probabilities gives
the lower length bound without requiring connected confidence sets.
-/

public section

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The three sampling conditions and the marginal probability laws make the data law a probability.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP), [the stated conclusion holds](goal). -/
-- @node: dataLaw_isProbabilityMeasure_of_model
lemma dataLaw_isProbabilityMeasure_of_model (c_f C_f L : ℝ) (P : TransportLaw)
    (n : ℕ) (hP : ModelClass c_f C_f L P n) : IsProbabilityMeasure (dataLaw P n n) := by
  let := sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let := targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
  infer_instance

/-- Expected restricted lengths are nonnegative, even before regularity is imposed.  Under [the displayed assumptions and inputs](hyp:P,n,C), [the stated conclusion holds](goal). -/
-- @node: expectedLength_nonneg
lemma expectedLength_nonneg (P : TransportLaw) (n : ℕ) (C : TwoSample n n → Set ℝ) :
    0 ≤ expectedLength P n n C := by
  exact integral_nonneg (fun _ => ENNReal.toReal_nonneg)

/-- A probability expectation of restricted length cannot exceed the length two of the parameter space.  Under [the displayed assumptions and inputs](hyp:P,n,C), [the stated conclusion holds](goal). -/
-- @node: expectedLength_le_two
lemma expectedLength_le_two (P : TransportLaw) (n : ℕ)
    [IsProbabilityMeasure (dataLaw P n n)] (C : TwoSample n n → Set ℝ) :
    expectedLength P n n C ≤ 2 := by
  have hb (ω : TwoSample n n) : restrictedLength (C ω) ≤ 2 := by
    unfold restrictedLength Causalean.Stat.restrictedSetVolume
    have h := ENNReal.toReal_mono (show volume parameterSpace ≠ ⊤ by
      simp [parameterSpace, Real.volume_Icc])
      (measure_mono (inter_subset_right : C ω ∩ parameterSpace ⊆ parameterSpace))
    norm_num [parameterSpace, Real.volume_Icc] at h ⊢
    exact h
  by_cases hi : Integrable (fun ω => restrictedLength (C ω)) (dataLaw P n n)
  · exact (integral_mono hi (integrable_const (2 : ℝ)) hb).trans_eq (by simp)
  · rw [expectedLength, integral_undef hi]
    norm_num

/-- The definition's power-of-two normalization is the cardinality normalization of a uniform mixture.  Under [the displayed assumptions and inputs](hyp:a,n,cStar), [the stated conclusion holds](goal). -/
-- @node: lowerMixture_eq_uniform_data
lemma lowerMixture_eq_uniform_data (a : ℝ) (n : ℕ) (cStar τ : ℝ) :
    lowerMixture a n cStar τ = Causalean.Stat.Minimax.Mixture.uniformMixture
      (fun sgn : Fin (lowerCells n) → Bool => dataLaw (legalIVComponent a n cStar τ sgn) n n) := by
  simp [lowerMixture, Causalean.Stat.Minimax.Mixture.uniformMixture,
    Causalean.Stat.mixture, Finset.smul_sum, Fintype.card_fun]

/-- Averaging preserves a common lower coverage bound over a finite nonempty family.  Under [the displayed assumptions and inputs](hyp:Ω,S,Q,E,p,hcover), [the stated conclusion holds](goal). -/
-- @node: uniform_data_mixture_coverage
lemma uniform_data_mixture_coverage {Ω S : Type*} [MeasurableSpace Ω]
    [Fintype S] [Nonempty S] (Q : S → Measure Ω)
    [∀ s, IsProbabilityMeasure (Q s)] (E : Set Ω) (p : ℝ)
    (hcover : ∀ s, p ≤ (Q s E).toReal) :
    p ≤ (Causalean.Stat.Minimax.Mixture.uniformMixture Q E).toReal := by
  classical
  let w : ℝ≥0∞ := (Fintype.card S : ℝ≥0∞)⁻¹
  have hw : w ≠ ⊤ := by simp [w, Fintype.card_ne_zero]
  have hsum : (∑ _s : S, w.toReal) = 1 := by
    simp [w, ENNReal.toReal_inv, nsmul_eq_mul, Fintype.card_ne_zero]
  rw [Causalean.Stat.Minimax.Mixture.uniformMixture, Causalean.Stat.mixture_apply,
    ENNReal.toReal_sum (fun s _ => ENNReal.mul_ne_top hw (measure_ne_top (Q s) E))]
  simp only [ENNReal.toReal_mul]
  calc
    p = ∑ _s : S, w.toReal * p := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun s _ =>
      mul_le_mul_of_nonneg_left (hcover s) ENNReal.toReal_nonneg)

/-- The finite-size fallback parameter interval is an honest connected confidence set.  Under [the displayed assumptions and inputs](hyp:α,c_f,C_f,L,hα,n), [the stated conclusion holds](goal). -/
-- @node: parameterSpace_honest
lemma parameterSpace_honest (α c_f C_f L : ℝ) (hα : 0 < α ∧ α < 1) (n : ℕ) :
    (fun _ : TwoSample n n => parameterSpace) ∈ HonestIntervals α c_f C_f L n := by
  refine ⟨hα.1, hα.2, (fun _ => ⟨Subset.rfl, ordConnected_Icc⟩),
    measurableSet_Icc.preimage measurable_snd, ?_⟩
  intro P hP
  let := dataLaw_isProbabilityMeasure_of_model c_f C_f L P n hP
  have hid := transported_cace_identification c_f C_f L P n
    hP.sourceBounds.1 hP.sourceBounds.2.1 hP.sourceHolder.1 hP
  have hθ := hid.2.2.2.2.2.2
  simp only [hθ, ofPred_true, measure_univ, ENNReal.toReal_one]
  linarith [hα.1]

/-- The floor chosen by the mixture implements the exact capped inverse-strength rate.  Under [the displayed assumptions and inputs](hyp:a,n,ha,hn), [the stated conclusion holds](goal). -/
-- @node: actualStrength_rate_identity
lemma actualStrength_rate_identity (a : ℝ) (n : ℕ) (ha : 0 < a) (hn : 0 < n) :
    (n : ℝ) ^ (-(1 / 3 : ℝ)) / actualStrength a n =
      min 1 ((n : ℝ) ^ (-(1 / 3 : ℝ)) / a) := by
  have hr : 0 < (n : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  unfold actualStrength
  by_cases h : a ≤ (n : ℝ) ^ (-(1 / 3 : ℝ))
  · rw [max_eq_right h, div_self hr.ne', min_eq_left ((le_div_iff₀ ha).2 (by simpa using h))]
  · have h' := le_of_not_ge h
    rw [max_eq_left h', min_eq_right ((div_le_one ha).2 h')]

/-- Integrating a uniform inclusion bound over a symmetric subinterval gives its length times coverage.  Under [the displayed assumptions and inputs](hyp:P,n,C,hgraph,r,p,hr,hr1,hcover), [the stated conclusion holds](goal). -/
-- @node: expectedLength_lower_of_inclusion
lemma expectedLength_lower_of_inclusion (P : TransportLaw) (n : ℕ)
    [IsProbabilityMeasure (dataLaw P n n)] (C : TwoSample n n → Set ℝ)
    (hgraph : MeasurableSet {p : TwoSample n n × ℝ | p.2 ∈ C p.1})
    (r p : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hcover : ∀ t ∈ Icc (-r) r, p ≤ (dataLaw P n n {ω | t ∈ C ω}).toReal) :
    2 * r * p ≤ expectedLength P n n C := by
  let f := fun t => (dataLaw P n n {ω | t ∈ C ω}).toReal
  have hf : Measurable f := (measurable_measure_prodMk_right hgraph).ennreal_toReal
  have hreg : volume parameterSpace ≠ ⊤ := by simp [parameterSpace, Real.volume_Icc]
  have hsub : Icc (-r) r ⊆ parameterSpace := by
    intro t ht
    change -1 ≤ t ∧ t ≤ 1
    constructor <;> linarith [ht.1, ht.2]
  have hfin : volume (Icc (-r) r) ≠ ⊤ := by simp [Real.volume_Icc]
  have hint : IntegrableOn f parameterSpace := by
    let := isFiniteMeasure_restrict.mpr hreg
    apply Integrable.of_bound hf.aestronglyMeasurable.restrict 1
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact measureReal_le_one
  rw [expectedLength_eq_integral_inclusion P n n C hgraph]
  calc
    2 * r * p = ∫ _t in Icc (-r) r, p := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, Measure.real, Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ r - -r)]
      ring
    _ ≤ ∫ t in Icc (-r) r, f t :=
      setIntegral_mono_on (integrableOn_const hfin) (hint.mono_set hsub)
        measurableSet_Icc hcover
    _ ≤ ∫ t in parameterSpace, f t := setIntegral_mono_set hint
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      (Filter.Eventually.of_forall hsub)

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

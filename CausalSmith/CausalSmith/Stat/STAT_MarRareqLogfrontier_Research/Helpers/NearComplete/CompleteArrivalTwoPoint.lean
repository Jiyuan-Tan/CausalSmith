module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Identification
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.CompleteArrivalTesting
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.CompleteArrivalFamily
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import Causalean.Mathlib.Probability.IidMeanVariance
public import Causalean.Stat.Minimax.ChiSquaredFinite
public import Causalean.Stat.Minimax.MarkovKernelTransport

/-! Complete-arrival frontier for the finite randomized experiment. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:n,d), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_ht_estimator_regular (n d : ℕ) :
    Measurable (completeArrivalHTEstimator n d) ∧
      ∀ s, completeArrivalHTEstimator n d s ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · exact measurable_of_finite _
  · intro s
    unfold completeArrivalHTEstimator clip
    constructor
    · exact le_max_left _ _
    · exact (max_le_iff.mpr ⟨by norm_num, min_le_left _ _⟩)

/-- Given [the specified inputs and assumptions](hyp:u,v,hv), [the stated mathematical conclusion holds](goal). -/
lemma clip_sq_error_le (u v : ℝ) (hv : v ∈ Set.Icc (-1 : ℝ) 1) :
    (clip u - v) ^ 2 ≤ (u - v) ^ 2 := by
  rcases hv with ⟨hvlo, hvhi⟩
  unfold clip
  rcases le_total u 1 with hu | hu
  · rw [min_eq_right hu]
    rcases le_total (-1 : ℝ) u with hlu | hlu
    · rw [max_eq_right hlu]
    · rw [max_eq_left hlu]
      nlinarith
  · rw [min_eq_left hu]
    rw [max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
    nlinarith

/-- Given [the specified inputs and assumptions](hyp:d,P), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_score_variance_le {d : ℕ} (P : FullLaw d) :
    ProbabilityTheory.variance
      (fun o : ObsRecord d =>
        2 * armSign o.A * (if o.RY then (1 : ℝ) else 0)) (P.1.map obs) ≤ 4 := by
  let μ := P.1.map obs
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable obs P.1)
  have hbound : ∀ᵐ o ∂μ,
      2 * armSign o.A * (if o.RY then (1 : ℝ) else 0) ∈ Set.Icc (-2) 2 := by
    filter_upwards [] with o
    cases hA : o.A <;> cases hRY : o.RY <;>
      simp [armSign]
  have hmeas : AEMeasurable
      (fun o : ObsRecord d =>
        2 * armSign o.A * (if o.RY then (1 : ℝ) else 0)) μ := by
    fun_prop
  have h := ProbabilityTheory.variance_le_sq_of_bounded hbound hmeas
  norm_num at h ⊢
  exact h

/-- Given [the specified inputs and assumptions](hyp:n,d,P,hP,j), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_no_absent_cell {n d : ℕ} (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d 1 P) (j : Cell d) :
    P.1.real {r | inCell r j ∧ r.R = false} = 0 := by
  letI : IsProbabilityMeasure P.1 := P.2
  have hbound : arrivedCell P j ≤ cellProb P j :=
    measureReal_mono (by intro r hr; exact hr.1)
  have heq : arrivedCell P j = cellProb P j := by
    by_cases hp : 0 < cellProb P j
    · exact le_antisymm hbound (by simpa using hP.arrival j hp)
    · have hz : cellProb P j = 0 :=
        le_antisymm (le_of_not_gt hp) measureReal_nonneg
      exact (le_antisymm (hbound.trans_eq hz) measureReal_nonneg).trans hz.symm
  have hdiff : {r : FullRecord d | inCell r j ∧ r.R = false} =
      {r | inCell r j} \ {r | inCell r j ∧ r.R = true} := by
    ext r
    cases r.R <;> simp <;> tauto
  rw [hdiff, measureReal_sdiff (by intro r hr; exact hr.1) (by simp)]
  exact sub_eq_zero.mpr heq.symm

/-- Given [the specified inputs and assumptions](hyp:n,d,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_almost_sure {n d : ℕ} (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d 1 P) :
    ∀ᵐ r : FullRecord d ∂P.1, r.R = true := by
  letI : IsProbabilityMeasure P.1 := P.2
  have hzero : P.1.real {r : FullRecord d | r.R = false} = 0 := by
    let μ := P.1.restrict {r : FullRecord d | r.R = false}
    have hsum := sum_measureReal_preimage_singleton (μ := μ)
      (Finset.univ : Finset (Cell d))
      (f := fun r : FullRecord d => (r.A, r.X, r.S)) (by intro; simp)
    have hcell (j : Cell d) :
        μ.real ((fun r : FullRecord d => (r.A, r.X, r.S)) ⁻¹' {j}) = 0 := by
      have hs : ((fun r : FullRecord d => (r.A, r.X, r.S)) ⁻¹' {j}) ∩
          {r : FullRecord d | r.R = false} =
          {r | inCell r j ∧ r.R = false} := by
        ext r
        rcases j with ⟨a, x, s⟩
        simp [inCell, Prod.mk.injEq, and_assoc, and_left_comm, and_comm]
      change (P.1.restrict {r : FullRecord d | r.R = false}).real
        ((fun r : FullRecord d => (r.A, r.X, r.S)) ⁻¹' {j}) = 0
      rw [measureReal_def, Measure.restrict_apply (by simp)]
      rw [hs]
      exact congrArg ENNReal.toReal (by
        exact (measureReal_eq_zero_iff (by simp)).mp
          (complete_arrival_no_absent_cell P hP j))
    simp_rw [hcell] at hsum
    simpa [μ, measureReal_def, Measure.restrict_apply] using hsum.symm
  have hzero' : P.1 {r : FullRecord d | r.R = false} = 0 := by
    exact (measureReal_eq_zero_iff (by simp)).mp hzero
  exact (ae_iff).2 (by simpa using hzero')

/-- Given [the specified inputs and assumptions](hyp:n,d,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_score_mean {n d : ℕ} (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d 1 P) :
    (∫ o : ObsRecord d,
      2 * armSign o.A * (if o.R && o.RY then (1 : ℝ) else 0) ∂(P.1.map obs)) = ate P := by
  letI : IsProbabilityMeasure P.1 := P.2
  have hmap :
      (∫ o : ObsRecord d,
        2 * armSign o.A * (if o.R && o.RY then (1 : ℝ) else 0) ∂(P.1.map obs)) =
      ∫ r : FullRecord d,
        2 * armSign r.A * (if r.R && r.Y then (1 : ℝ) else 0) ∂P.1 := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp [obs, Bool.and_assoc]
  rw [hmap]
  have hae := complete_arrival_almost_sure P hP
  have hreplace :
      (∫ r : FullRecord d,
        2 * armSign r.A * (if r.R && r.Y then (1 : ℝ) else 0) ∂P.1) =
      ∫ r : FullRecord d,
        2 * armSign r.A * (if r.Y then (1 : ℝ) else 0) ∂P.1 := by
    apply integral_congr_ae
    filter_upwards [hae] with r hr
    simp [hr]
  rw [hreplace]
  let E (a : Bool) : Set (FullRecord d) := {r | r.A = a ∧ r.Y = true}
  have hpoint :
      (fun r : FullRecord d => 2 * armSign r.A * (if r.Y then (1 : ℝ) else 0)) =
      (E true).indicator (fun _ => (2 : ℝ)) -
        (E false).indicator (fun _ => (2 : ℝ)) := by
    funext r
    cases hA : r.A <;> cases hY : r.Y <;>
      simp [E, armSign, Set.indicator, hA, hY]
  rw [hpoint]
  have hmeas (a : Bool) : MeasurableSet (E a) := by simp [E]
  change (∫ r : FullRecord d,
    (E true).indicator (fun _ => (2 : ℝ)) r -
      (E false).indicator (fun _ => (2 : ℝ)) r ∂P.1) = ate P
  rw [integral_sub ((integrable_const (2 : ℝ)).indicator (hmeas true))
    ((integrable_const (2 : ℝ)).indicator (hmeas false))]
  rw [integral_indicator_const (2 : ℝ) (hmeas true),
    integral_indicator_const (2 : ℝ) (hmeas false)]
  rw [ate_eq_potentialOutcomeMass P]
  have ht := randomized_armOutcomeMass P hP.randomized hP.balanced true
  have hf := randomized_armOutcomeMass P hP.randomized hP.balanced false
  simp only [E] at *
  simp only [ite_true, Bool.false_eq_true, ite_false] at ht hf
  linear_combination ht - hf

/-- Given [the specified inputs and assumptions](hyp:d,P), [the stated mathematical conclusion holds](goal). -/
lemma ate_mem_unit_interval {d : ℕ} (P : FullLaw d) :
    ate P ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ate_eq_potentialOutcomeMass]
  have h₀ : (0 : ℝ) ≤ P.1.real {r | r.Y0 = true} := measureReal_nonneg
  have h₁ : (0 : ℝ) ≤ P.1.real {r | r.Y1 = true} := measureReal_nonneg
  have h₀' : P.1.real {r | r.Y0 = true} ≤ 1 := by
    letI : IsProbabilityMeasure P.1 := P.2
    exact measureReal_le_one
  have h₁' : P.1.real {r | r.Y1 = true} ≤ 1 := by
    letI : IsProbabilityMeasure P.1 := P.2
    exact measureReal_le_one
  constructor <;> linarith

/-- Given [the specified inputs and assumptions](hyp:n,d,T,P), [the stated mathematical conclusion holds](goal). -/
lemma unrestricted_squaredRisk_bounds {n d : ℕ} (T : Estimator n d)
    (P : FullLaw d) : 0 ≤ squaredRisk T P ∧ squaredRisk T P ≤ 4 := by
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsMarkovKernel T.toBoundedKernel.1 := T.toBoundedKernel.2.1
  have hATE := ate_mem_unit_interval P
  rw [Set.mem_Icc] at hATE
  have hinner_nonneg (s : Fin n → ObsRecord d) :
      0 ≤ ∫ t, (t - ate P) ^ 2 ∂(T.toBoundedKernel.1 s) := by
    exact integral_nonneg (fun t => sq_nonneg _)
  have hinner_le (s : Fin n → ObsRecord d) :
      (∫ t, (t - ate P) ^ 2 ∂(T.toBoundedKernel.1 s)) ≤ 4 := by
    haveI : IsProbabilityMeasure (T.toBoundedKernel.1 s) := inferInstance
    have hs : ∀ᵐ t ∂(T.toBoundedKernel.1 s), t ∈ Set.Icc (-1 : ℝ) 1 :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (T.toBoundedKernel.2.2 s)
    have hb : ∀ᵐ t ∂(T.toBoundedKernel.1 s), (t - ate P) ^ 2 ≤ 4 := by
      filter_upwards [hs] with t ht
      rw [Set.mem_Icc] at ht
      nlinarith [sq_nonneg (t - ate P + 2), sq_nonneg (t - ate P - 2)]
    simpa using (integral_mono_of_nonneg (μ := T.toBoundedKernel.1 s)
      (Filter.Eventually.of_forall (fun t => sq_nonneg (t - ate P)))
      (integrable_const 4) hb)
  haveI : IsProbabilityMeasure (sampleLaw n P) := by
    unfold sampleLaw
    letI : IsProbabilityMeasure (P.1.map obs) :=
      Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable obs P.1)
    infer_instance
  constructor
  · exact integral_nonneg hinner_nonneg
  · simpa [squaredRisk] using (integral_mono_of_nonneg (μ := sampleLaw n P)
      (Filter.Eventually.of_forall hinner_nonneg) (integrable_const 4)
      (Filter.Eventually.of_forall hinner_le))

/-- Given [the specified inputs and assumptions](hyp:n,d,q,c,P₀,P₁,hP₀,hP₁,htwo), [the stated mathematical conclusion holds](goal). -/
lemma unrestricted_minimax_lower_of_two_point {n d : ℕ} {q c : ℝ}
    (P₀ P₁ : FullLaw d)
    (hP₀ : UnrestrictedArrivalModelClass n d q P₀)
    (hP₁ : UnrestrictedArrivalModelClass n d q P₁)
    (htwo : ∀ T : Estimator n d,
      c ≤ max (squaredRisk T P₀) (squaredRisk T P₁)) :
    c ≤ unrestrictedMinimaxRisk n d q := by
  let T₀ : Estimator n d :=
    Estimator.ofMap (fun _ => 0) ⟨measurable_const, by intro s; norm_num⟩
  letI : Nonempty (Estimator n d) := ⟨T₀⟩
  let θ₀ : {P : FullLaw d // UnrestrictedArrivalModelClass n d q P} := ⟨P₀, hP₀⟩
  let θ₁ : {P : FullLaw d // UnrestrictedArrivalModelClass n d q P} := ⟨P₁, hP₁⟩
  unfold unrestrictedMinimaxRisk
  apply Causalean.Stat.le_minimaxValue_of_two_point θ₀ θ₁
  · intro T
    refine ⟨4, ?_⟩
    rintro r ⟨θ, rfl⟩
    exact (unrestricted_squaredRisk_bounds T θ.1).2
  · intro T
    exact htwo T

/-- Given [the specified inputs and assumptions](hyp:n,d,hn,P₀,P₁,hac,hchi), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_chisq_testing_floor {n d : ℕ} (hn : 1 ≤ n)
    (P₀ P₁ : FullLaw d)
    (hac : (P₁.1.map obs) ≪ (P₀.1.map obs))
    (hchi : Causalean.Stat.chiSqDiv (P₁.1.map obs) (P₀.1.map obs) ≤
      (1 / 8 : ℝ) / n) :
    ∀ A : Set (Fin n → ObsRecord d), MeasurableSet A →
      (sampleLaw n P₁).real Aᶜ + (sampleLaw n P₀).real A ≥ 1 / 2 := by
  letI : IsProbabilityMeasure P₀.1 := P₀.2
  letI : IsProbabilityMeasure P₁.1 := P₁.2
  letI : IsProbabilityMeasure (P₀.1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (P₁.1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  simpa only [sampleLaw] using
    complete_arrival_product_testing_half n hn
      (P₁.1.map obs) (P₀.1.map obs) hac (Integrable.of_finite) hchi

/-- Given [the specified inputs and assumptions](hyp:n,d,T,P), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_kernel_mean_risk_le {n d : ℕ} (T : Estimator n d)
    (P : FullLaw d) :
    deterministicRisk (Causalean.Stat.kernelMean T.toBoundedKernel.1 clip) P ≤
      squaredRisk T P := by
  letI : IsMarkovKernel T.toBoundedKernel.1 := T.toBoundedKernel.2.1
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsProbabilityMeasure (P.1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (sampleLaw n P) := by
    unfold sampleLaw
    infer_instance
  have hclip_meas : Measurable clip := by
    unfold clip
    fun_prop
  have hclip_bound : Causalean.Stat.UniformlyBounded clip := by
    refine ⟨1, by norm_num, ?_⟩
    intro t
    rw [abs_le]
    simp [clip]
  have hclip_abs (t : ℝ) : |clip t| ≤ 1 := by
    rw [abs_le]
    constructor <;> simp [clip]
  let f := Causalean.Stat.kernelMean T.toBoundedKernel.1 clip
  have hf : Measurable f := Causalean.Stat.measurable_kernelMean T.toBoundedKernel.1 hclip_meas
  have hpoint (s : Fin n → ObsRecord d) :
      (f s - ate P) ^ 2 ≤ ∫ t, (t - ate P) ^ 2 ∂(T.toBoundedKernel.1 s) := by
    calc
      _ ≤ ∫ t, (clip t - ate P) ^ 2 ∂(T.toBoundedKernel.1 s) :=
        Causalean.Stat.sqLoss_kernelMean_le T.toBoundedKernel.1 hclip_meas
          hclip_bound (ate P) s
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [(mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (T.toBoundedKernel.2.2 s)]
          with t ht
        simp [clip, ht.1, ht.2]
  have hfbound : ∀ s, f s ∈ Icc (-1 : ℝ) 1 := by
    intro s
    rw [Set.mem_Icc, ← abs_le]
    exact Causalean.Stat.abs_kernelMean_le T.toBoundedKernel.1 (M := 1)
      hclip_abs s
  have hmeas : Measurable (fun s ↦ ∫ t, (t - ate P) ^ 2 ∂(T.toBoundedKernel.1 s)) := by
    exact ((measurable_id.sub measurable_const).pow_const 2).stronglyMeasurable
      |>.integral_kernel.measurable
  have hbound (s : Fin n → ObsRecord d) :
      |(∫ t, (t - ate P) ^ 2 ∂(T.toBoundedKernel.1 s))| ≤ 4 := by
    have hATE := ate_mem_unit_interval P
    have hs : ∀ᵐ t ∂(T.toBoundedKernel.1 s), t ∈ Icc (-1 : ℝ) 1 :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (T.toBoundedKernel.2.2 s)
    have hle : ∀ᵐ t ∂(T.toBoundedKernel.1 s), (t - ate P) ^ 2 ≤ 4 := by
      filter_upwards [hs] with t ht
      rw [Set.mem_Icc] at ht hATE
      nlinarith [sq_nonneg (t - ate P + 2), sq_nonneg (t - ate P - 2)]
    have hnon : 0 ≤ ∫ t, (t - ate P) ^ 2 ∂(T.toBoundedKernel.1 s) :=
      integral_nonneg (fun _ ↦ sq_nonneg _)
    rw [abs_of_nonneg hnon]
    simpa using integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t ↦ sq_nonneg _)
      (integrable_const 4) hle
  unfold deterministicRisk squaredRisk
  exact integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
    (Integrable.of_bound hmeas.aestronglyMeasurable 4
      (Filter.Eventually.of_forall fun s ↦ by
        simpa [Real.norm_eq_abs] using hbound s))
    (Filter.Eventually.of_forall hpoint)

/-- Given [the specified inputs and assumptions](hyp:n,d,P₀,P₁,δ,c,hδ,hc,hgap,hfloor), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_two_point_decision_reduction {n d : ℕ}
    (P₀ P₁ : FullLaw d) (δ c : ℝ) (hδ : 0 < δ) (hc : 0 ≤ c)
    (hgap : ate P₁ = ate P₀ + δ)
    (hfloor : ∀ A : Set (Fin n → ObsRecord d), MeasurableSet A →
      (sampleLaw n P₁).real Aᶜ + (sampleLaw n P₀).real A ≥ c) :
    ∀ T : Estimator n d,
      c * δ ^ 2 / 8 ≤ max (squaredRisk T P₀) (squaredRisk T P₁) := by
  intro T
  let f := Causalean.Stat.kernelMean T.toBoundedKernel.1 clip
  let E₀ : Set (Fin n → ObsRecord d) := {s | δ / 2 ≤ |f s - ate P₀|}
  let E₁ : Set (Fin n → ObsRecord d) := {s | δ / 2 ≤ |f s - ate P₁|}
  let A : Set (Fin n → ObsRecord d) :=
    {s | |f s - ate P₁| ≤ |f s - ate P₀|}
  letI : IsMarkovKernel T.toBoundedKernel.1 := T.toBoundedKernel.2.1
  letI : IsProbabilityMeasure P₀.1 := P₀.2
  letI : IsProbabilityMeasure P₁.1 := P₁.2
  letI : IsProbabilityMeasure (P₀.1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (P₁.1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (sampleLaw n P₀) := by
    unfold sampleLaw
    infer_instance
  letI : IsProbabilityMeasure (sampleLaw n P₁) := by
    unfold sampleLaw
    infer_instance
  have hf : Measurable f := Causalean.Stat.measurable_kernelMean T.toBoundedKernel.1 (by
    unfold clip
    fun_prop)
  have hA : MeasurableSet A := by
    exact measurableSet_le
      (continuous_abs.measurable.comp (hf.sub measurable_const))
      (continuous_abs.measurable.comp (hf.sub measurable_const))
  have htri (s : Fin n → ObsRecord d) :
      δ ≤ |f s - ate P₀| + |f s - ate P₁| := by
    have ht := abs_sub_le (ate P₁) (f s) (ate P₀)
    have hdiff : |ate P₁ - ate P₀| = δ := by
      rw [hgap]
      simpa using abs_of_pos hδ
    calc
      δ = |ate P₁ - ate P₀| := hdiff.symm
      _ ≤ _ := by simpa [abs_sub_comm, add_comm] using ht
  have hA_E₀ : A ⊆ E₀ := by
    intro s hs
    simp only [A, E₀, Set.mem_setOf_eq] at hs ⊢
    linarith [htri s]
  have hAc_E₁ : Aᶜ ⊆ E₁ := by
    intro s hs
    simp only [A, E₁, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hs ⊢
    linarith [htri s]
  have htest : c ≤ (sampleLaw n P₁).real E₁ +
      (sampleLaw n P₀).real E₀ := by
    calc
      c ≤ (sampleLaw n P₁).real Aᶜ +
          (sampleLaw n P₀).real A := hfloor A hA
      _ ≤ _ := add_le_add
        (measureReal_mono hAc_E₁ (by finiteness))
        (measureReal_mono hA_E₀ (by finiteness))
  have hbound (P : FullLaw d) : ∀ s, f s ∈ Icc (-1 : ℝ) 1 := by
    intro s
    rw [Set.mem_Icc, ← abs_le]
    exact Causalean.Stat.abs_kernelMean_le T.toBoundedKernel.1 (M := 1)
      (fun t => by rw [abs_le]; constructor <;> simp [clip]) s
  have hint₀ : Integrable (fun s ↦ (f s - ate P₀) ^ 2) (sampleLaw n P₀) :=
    Causalean.Stat.mse_integrable_of_estimator_bound _ f hf (by norm_num)
      (hbound P₀)
  have hint₁ : Integrable (fun s ↦ (f s - ate P₁) ^ 2) (sampleLaw n P₁) :=
    Causalean.Stat.mse_integrable_of_estimator_bound _ f hf (by norm_num)
      (hbound P₁)
  have hmse₀ : (δ / 2) ^ 2 * (sampleLaw n P₀).real E₀ ≤
      deterministicRisk f P₀ := by
    unfold deterministicRisk E₀
    have hset : {s | (δ / 2) ^ 2 ≤ (f s - ate P₀) ^ 2} =
        {s | δ / 2 ≤ |f s - ate P₀|} := by
      ext s
      simp only [Set.mem_setOf_eq]
      rw [sq_le_sq, abs_of_nonneg (show (0 : ℝ) ≤ δ / 2 by positivity)]
    rw [← hset]
    exact mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun s ↦ sq_nonneg _) hint₀ _
  have hmse₁ : (δ / 2) ^ 2 * (sampleLaw n P₁).real E₁ ≤
      deterministicRisk f P₁ := by
    unfold deterministicRisk E₁
    have hset : {s | (δ / 2) ^ 2 ≤ (f s - ate P₁) ^ 2} =
        {s | δ / 2 ≤ |f s - ate P₁|} := by
      ext s
      simp only [Set.mem_setOf_eq]
      rw [sq_le_sq, abs_of_nonneg (show (0 : ℝ) ≤ δ / 2 by positivity)]
    rw [← hset]
    exact mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun s ↦ sq_nonneg _) hint₁ _
  have hmax : c / 2 ≤ max ((sampleLaw n P₀).real E₀)
      ((sampleLaw n P₁).real E₁) := by
    nlinarith [le_max_left ((sampleLaw n P₀).real E₀)
      ((sampleLaw n P₁).real E₁),
      le_max_right ((sampleLaw n P₀).real E₀)
        ((sampleLaw n P₁).real E₁)]
  calc
    c * δ ^ 2 / 8 ≤ (δ / 2) ^ 2 *
        max ((sampleLaw n P₀).real E₀) ((sampleLaw n P₁).real E₁) := by
      nlinarith [sq_nonneg δ]
    _ = max ((δ / 2) ^ 2 * (sampleLaw n P₀).real E₀)
          ((δ / 2) ^ 2 * (sampleLaw n P₁).real E₁) := by
      by_cases hle : (sampleLaw n P₀).real E₀ ≤
          (sampleLaw n P₁).real E₁
      · rw [max_eq_right hle, max_eq_right]
        exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
      · have hge := le_of_not_ge hle
        rw [max_eq_left hge, max_eq_left]
        exact mul_le_mul_of_nonneg_left hge (sq_nonneg _)
    _ ≤ max (deterministicRisk f P₀) (deterministicRisk f P₁) :=
      max_le_max hmse₀ hmse₁
    _ ≤ max (squaredRisk T P₀) (squaredRisk T P₁) :=
      max_le_max (complete_arrival_kernel_mean_risk_le T P₀)
        (complete_arrival_kernel_mean_risk_le T P₁)

/-- Given [the specified inputs and assumptions](hyp:n,d,hn,P₀,P₁,hP₀,hP₁,δ,hδ,hgap,hδsq,hac,hchi), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_two_point_minimax_floor {n d : ℕ} (hn : 1 ≤ n)
    (P₀ P₁ : FullLaw d)
    (hP₀ : UnrestrictedArrivalModelClass n d 1 P₀)
    (hP₁ : UnrestrictedArrivalModelClass n d 1 P₁)
    (δ : ℝ) (hδ : 0 < δ) (hgap : ate P₁ = ate P₀ + δ)
    (hδsq : δ ^ 2 = 1 / (16 * (n : ℝ)))
    (hac : (P₁.1.map obs) ≪ (P₀.1.map obs))
    (hchi : Causalean.Stat.chiSqDiv (P₁.1.map obs) (P₀.1.map obs) ≤
      (1 / 8 : ℝ) / n) :
    1 / (256 * (n : ℝ)) ≤ unrestrictedMinimaxRisk n d 1 := by
  apply unrestricted_minimax_lower_of_two_point P₀ P₁ hP₀ hP₁
  intro T
  have hfloor := complete_arrival_chisq_testing_floor hn P₀ P₁ hac hchi
  have hrisk := complete_arrival_two_point_decision_reduction P₀ P₁ δ (1 / 2)
    hδ (by norm_num) hgap hfloor T
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hn)
  rw [hδsq] at hrisk
  convert hrisk using 1 <;> ring

/-- Uniformly over sample size and alphabet size, [the complete-arrival minimax and estimator risks have the displayed parametric bounds](goal). -/
theorem complete_arrival_frontier_direct :
    ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d →
      1 / (256 * (n : ℝ)) ≤ unrestrictedMinimaxRisk n d 1 ∧
      unrestrictedMinimaxRisk n d 1 ≤
        Causalean.Stat.worstCaseRiskReal
          (fun (_ : Unit) (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d 1 P}) =>
            deterministicRisk (completeArrivalHTEstimator n d) P.1) () ∧
      Causalean.Stat.worstCaseRiskReal
          (fun (_ : Unit) (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d 1 P}) =>
            deterministicRisk (completeArrivalHTEstimator n d) P.1) () ≤
        4 / (n : ℝ) := by
  intro n d hn hd
  constructor
  · let x : Fin d := ⟨0, hd⟩
    let δ : ℝ := 1 / (4 * Real.sqrt n)
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.lt_of_lt_of_le (by omega : 0 < 1) hn)
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hn1
    have hδle : δ ≤ 1 / 4 := by
      dsimp [δ]
      rw [div_le_iff₀ (by positivity : 0 < 4 * Real.sqrt (n : ℝ))]
      nlinarith
    have hu₀ : (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 := by norm_num
    have hu₁ : (0 : ℝ) ≤ 1 / 2 + δ ∧ (1 / 2 + δ : ℝ) ≤ 1 := by
      constructor <;> linarith
    let P₀ := completeFamilyLaw x (1 / 2) hu₀
    let P₁ := completeFamilyLaw x (1 / 2 + δ) hu₁
    have hgap : ate P₁ = ate P₀ + δ := by
      simp [P₀, P₁, completeFamilyLaw_ate]
    have hδsq : δ ^ 2 = 1 / (16 * (n : ℝ)) := by
      dsimp [δ]
      calc
        (1 / (4 * Real.sqrt (n : ℝ))) ^ 2 =
            1 / (16 * (Real.sqrt (n : ℝ)) ^ 2) := by ring
        _ = 1 / (16 * (n : ℝ)) := by rw [Real.sq_sqrt (le_of_lt hnR)]
    have hP₀ : UnrestrictedArrivalModelClass n d 1 P₀ := by
      apply completeFamilyLaw_in_unrestricted_class_of_randomized hn hd x (1 / 2) hu₀
      exact completeFamilyLaw_randomized x (1 / 2) hu₀
    have hP₁ : UnrestrictedArrivalModelClass n d 1 P₁ := by
      apply completeFamilyLaw_in_unrestricted_class_of_randomized hn hd x (1 / 2 + δ) hu₁
      exact completeFamilyLaw_randomized x (1 / 2 + δ) hu₁
    have hac : (P₁.1.map obs) ≪ (P₀.1.map obs) := by
      simpa [P₀, P₁] using completeFamilyLaw_obs_ac x (1 / 2 + δ) hu₁
    have hchi : Causalean.Stat.chiSqDiv (P₁.1.map obs) (P₀.1.map obs) ≤
        (1 / 8 : ℝ) / n := by
      have heq : Causalean.Stat.chiSqDiv (P₁.1.map obs) (P₀.1.map obs) =
          2 * δ ^ 2 := by
        simpa [P₀, P₁] using
          completeFamilyLaw_obs_chi x (1 / 2 + δ) hu₁
      rw [heq, hδsq]
      apply le_of_eq
      field_simp [hnR.ne']
      ring
    exact complete_arrival_two_point_minimax_floor hn P₀ P₁ hP₀ hP₁ δ
      hδ hgap hδsq hac hchi
  constructor
  · let f := completeArrivalHTEstimator n d
    have hEstimator := complete_arrival_ht_estimator_regular n d
    let T : Estimator n d :=
      Estimator.ofMap f hEstimator
    have hrisk : ∀ (T : Estimator n d)
        (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d 1 P}),
        0 ≤ squaredRisk T P.1 := by
      intro T P
      exact integral_nonneg (fun s => integral_nonneg (fun y => sq_nonneg _))
    have hval : unrestrictedMinimaxRisk n d 1 ≤
        Causalean.Stat.worstCaseRiskReal
          (fun (_ : Unit) (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d 1 P}) =>
            squaredRisk T P.1) () := by
      exact Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg hrisk T
    have heq :
        (fun (_ : Unit) (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d 1 P}) =>
          squaredRisk T P.1) =
        (fun (_ : Unit) P => deterministicRisk f P.1) := by
      funext _ P
      simp [squaredRisk, deterministicRisk, T, Estimator.ofMap, Kernel.deterministic_apply]
    rw [heq] at hval
    exact hval
  · unfold Causalean.Stat.worstCaseRiskReal
    by_cases hne : Nonempty
        {P : FullLaw d // UnrestrictedArrivalModelClass n d 1 P}
    · letI := hne
      apply ciSup_le
      intro P
      let μ := P.1.1.map obs
      let ξ : ObsRecord d → ℝ := fun o =>
        2 * armSign o.A * (if o.R && o.RY then (1 : ℝ) else 0)
      letI : IsProbabilityMeasure P.1.1 := P.1.2
      letI : IsProbabilityMeasure μ :=
        Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable obs P.1.1)
      letI : IsProbabilityMeasure (sampleLaw n P.1) := by
        unfold sampleLaw
        infer_instance
      have htarget : ate P.1 ∈ Set.Icc (-1 : ℝ) 1 :=
        ate_mem_unit_interval P.1
      have hbound : ∀ᵐ o ∂μ, ξ o ∈ Set.Icc (-2 : ℝ) 2 := by
        filter_upwards [] with o
        cases hA : o.A <;> cases hR : o.R <;> cases hRY : o.RY <;>
          simp [ξ, armSign, hA, hR, hRY]
      have hLp : MemLp ξ 2 μ :=
        memLp_of_bounded hbound (by fun_prop) 2
      have hsquare : (∫ o, (ξ o) ^ 2 ∂μ) ≤ 4 := by
        have hint : Integrable (fun o => (ξ o) ^ 2) μ := hLp.integrable_sq
        have h := integral_mono hint (integrable_const (4 : ℝ))
        simpa using h (fun o => by
          cases hA : o.A <;> cases hR : o.R <;> cases hRY : o.RY <;>
            norm_num [ξ, armSign, hA, hR, hRY])
      have hmean : (∫ o, ξ o ∂μ) = ate P.1 :=
        complete_arrival_score_mean P.1 P.2
      have hiid := Causalean.Mathlib.Probability.iid_mean_sq_le
        μ hn ξ hLp
      have hsumLp : MemLp
          (fun s : Fin n → ObsRecord d => ∑ i : Fin n, ξ (s i)) 2
          (sampleLaw n P.1) := by
        simpa [sampleLaw, μ] using
          (memLp_finset_sum Finset.univ (fun i _ =>
            hLp.comp_measurePreserving
              (measurePreserving_eval (fun _ : Fin n => μ) i)))
      have hdevInt : Integrable
          (fun s : Fin n → ObsRecord d =>
            ((n : ℝ)⁻¹ * ∑ i : Fin n, ξ (s i) - ate P.1) ^ 2)
          (sampleLaw n P.1) :=
        ((hsumLp.const_mul _).sub (memLp_const _)).integrable_sq
      have hpoint (s : Fin n → ObsRecord d) :
          (completeArrivalHTEstimator n d s - ate P.1) ^ 2 ≤
          ((n : ℝ)⁻¹ * ∑ i : Fin n, ξ (s i) - ate P.1) ^ 2 := by
        have hraw : (2 / (n : ℝ)) * ∑ i : Fin n,
            armSign (s i).A *
              (if (s i).R && (s i).RY then (1 : ℝ) else 0) =
            (n : ℝ)⁻¹ * ∑ i : Fin n, ξ (s i) := by
          simp only [ξ]
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          ring
        unfold completeArrivalHTEstimator
        rw [hraw]
        exact clip_sq_error_le _ _ htarget
      have hrisk : deterministicRisk (completeArrivalHTEstimator n d) P.1 ≤
          (∫ s, ((n : ℝ)⁻¹ * ∑ i : Fin n, ξ (s i) - ate P.1) ^ 2
            ∂(sampleLaw n P.1)) := by
        unfold deterministicRisk
        exact integral_mono_of_nonneg (ae_of_all _ (fun s => sq_nonneg _)) hdevInt
          (ae_of_all _ hpoint)
      calc
        deterministicRisk (completeArrivalHTEstimator n d) P.1 ≤ _ := hrisk
        _ ≤ (∫ o, (ξ o) ^ 2 ∂μ) / (n : ℝ) := by
          simpa [sampleLaw, μ, hmean] using hiid
        _ ≤ 4 / (n : ℝ) := by
          exact div_le_div_of_nonneg_right hsquare (by positivity)
    · haveI : IsEmpty {P : FullLaw d // UnrestrictedArrivalModelClass n d 1 P} :=
        not_nonempty_iff.mp hne
      simp
      positivity

end CausalSmith.Stat.MarRareqLogfrontier

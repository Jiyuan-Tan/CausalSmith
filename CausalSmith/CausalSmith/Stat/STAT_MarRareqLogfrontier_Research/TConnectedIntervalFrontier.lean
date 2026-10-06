module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.IntervalNeighborhood
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.IntervalConcentration
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.IntervalRegimes
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationCalibration
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TFullExperimentLower
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TMixedCountUpper
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TUnrestrictedCompleteArrivalFrontier

/-! TConnectedIntervalFrontier for the finite rare-arrival experiment. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: riskEnvelopeEndpoints_length_le
/-- Given [the specified inputs and assumptions](hyp:n,d,q,α,s), [the stated mathematical conclusion holds](goal). -/
lemma riskEnvelopeEndpoints_length_le (n d : ℕ) (q α : ℝ)
    (s : Fin n → ObsRecord d) :
    (riskEnvelopeEndpoints n d q α s).2 -
      (riskEnvelopeEndpoints n d q α s).1 ≤
        2 * Real.sqrt (riskEnvelope n d q / α) := by
  unfold riskEnvelopeEndpoints
  have hlo := le_max_right (-1 : ℝ)
    (mixedCountEstimator n d q s - Real.sqrt (riskEnvelope n d q / α))
  have hhi := min_le_right (1 : ℝ)
    (mixedCountEstimator n d q s + Real.sqrt (riskEnvelope n d q / α))
  linarith

-- @node: riskEnvelopeInterval_contains_of_error_le
/-- Given [the specified inputs and assumptions](hyp:n,d,q,α,P,s,herror), [the stated mathematical conclusion holds](goal). -/
lemma riskEnvelopeInterval_contains_of_error_le (n d : ℕ) (q α : ℝ)
    (P : FullLaw d) (s : Fin n → ObsRecord d)
    (herror : |mixedCountEstimator n d q s - ate P| ≤
      Real.sqrt (riskEnvelope n d q / α)) :
    ate P ∈ riskEnvelopeInterval n d q α s := by
  have htarget := ate_mem_unit_interval P
  rcases abs_le.mp herror with ⟨hlo, hhi⟩
  simp only [riskEnvelopeInterval, riskEnvelopeEndpoints, Set.mem_Icc] at *
  constructor
  · exact max_le htarget.1 (by linarith)
  · exact le_min htarget.2 (by linarith)

-- @node: riskEnvelopeInterval_contains_of_sq_error_le
/-- Given [the specified inputs and assumptions](hyp:n,d,q,α,P,s,hratio,herror), [the stated mathematical conclusion holds](goal). -/
lemma riskEnvelopeInterval_contains_of_sq_error_le (n d : ℕ) (q α : ℝ)
    (P : FullLaw d) (s : Fin n → ObsRecord d)
    (hratio : 0 ≤ riskEnvelope n d q / α)
    (herror : (mixedCountEstimator n d q s - ate P) ^ 2 ≤
      riskEnvelope n d q / α) :
    ate P ∈ riskEnvelopeInterval n d q α s := by
  apply riskEnvelopeInterval_contains_of_error_le
  have hsqrt : (Real.sqrt (riskEnvelope n d q / α)) ^ 2 =
      riskEnvelope n d q / α := Real.sq_sqrt hratio
  have hnonneg := Real.sqrt_nonneg (riskEnvelope n d q / α)
  nlinarith [abs_nonneg (mixedCountEstimator n d q s - ate P),
    sq_abs (mixedCountEstimator n d q s - ate P)]

-- @node: riskEnvelopeInterval_coverage_of_positive_envelope
/-- Given [the specified inputs and assumptions](hyp:n,d,q,α,P,hα,henv,hrisk), [the stated mathematical conclusion holds](goal). -/
lemma riskEnvelopeInterval_coverage_of_positive_envelope (n d : ℕ) (q α : ℝ)
    (P : FullLaw d) (hα : 0 < α) (henv : 0 < riskEnvelope n d q)
    (hrisk : deterministicRisk (mixedCountEstimator n d q) P ≤
      riskEnvelope n d q) :
    1 - α ≤ (sampleLaw n P).real
      {s | ate P ∈ riskEnvelopeInterval n d q α s} := by
  let μ := sampleLaw n P
  let f : (Fin n → ObsRecord d) → ℝ :=
    fun s => (mixedCountEstimator n d q s - ate P) ^ 2
  let t := riskEnvelope n d q / α
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, sampleLaw]
    letI : IsProbabilityMeasure (P.1.map obs) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    infer_instance
  have ht : 0 < t := div_pos henv hα
  have hmarkov : t * μ.real {s | t ≤ f s} ≤ riskEnvelope n d q := by
    calc
      t * μ.real {s | t ≤ f s} ≤ ∫ s, f s ∂μ :=
        mul_meas_ge_le_integral_of_nonneg
          (Filter.Eventually.of_forall fun s => sq_nonneg _) Integrable.of_finite t
      _ ≤ riskEnvelope n d q := hrisk
  let good : Set (Fin n → ObsRecord d) :=
    {s | ate P ∈ riskEnvelopeInterval n d q α s}
  have hsubset : goodᶜ ⊆ {s | t ≤ f s} := by
    intro s hnotgood
    by_contra hlt
    have hsq : f s ≤ t := le_of_lt (lt_of_not_ge hlt)
    have hmem := riskEnvelopeInterval_contains_of_sq_error_le n d q α P s
      (le_of_lt ht) (by simpa [f, t] using hsq)
    exact hnotgood hmem
  have hbad : μ.real goodᶜ ≤ α := by
    have hmono := measureReal_mono (μ := μ) hsubset (measure_ne_top μ _)
    have hmul := mul_le_mul_of_nonneg_left hmono (le_of_lt ht)
    have hαne : α ≠ 0 := ne_of_gt hα
    have henvne : riskEnvelope n d q ≠ 0 := ne_of_gt henv
    dsimp [t] at hmul hmarkov
    have hprod : (riskEnvelope n d q / α) * α = riskEnvelope n d q := by
      field_simp
    nlinarith
  have hgood : MeasurableSet good := by
    classical
    have heq : ((fun s : Fin n → ObsRecord d => decide (s ∈ good)) ⁻¹' {true}) =
        good := by
      ext s
      simp
    rw [← heq]
    exact (measurable_of_finite
      (fun s : Fin n → ObsRecord d => decide (s ∈ good)))
      (measurableSet_singleton true)
  have htotal : μ.real goodᶜ = 1 - μ.real good := by
    simpa using (measureReal_compl (μ := μ) hgood)
  dsimp [μ, good] at *
  linarith

-- @node: riskEnvelopeInterval_coverage
/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hα,hrisk), [the stated mathematical conclusion holds](goal). -/
lemma riskEnvelopeInterval_coverage (n d : ℕ) (q α : ℝ)
    (P : FullLaw d) (hα : 0 < α)
    (hrisk : deterministicRisk (mixedCountEstimator n d q) P ≤
      riskEnvelope n d q) :
    1 - α ≤ (sampleLaw n P).real
      {s | ate P ∈ riskEnvelopeInterval n d q α s} := by
  have henv_nonneg : 0 ≤ riskEnvelope n d q := by
    have hrisk_nonneg : 0 ≤ deterministicRisk (mixedCountEstimator n d q) P := by
      unfold deterministicRisk
      exact integral_nonneg (fun s => sq_nonneg _)
    exact hrisk_nonneg.trans hrisk
  rcases eq_or_lt_of_le henv_nonneg with hzero | hpos
  · let μ := sampleLaw n P
    let f : (Fin n → ObsRecord d) → ℝ :=
      fun s => (mixedCountEstimator n d q s - ate P) ^ 2
    letI : IsProbabilityMeasure P.1 := P.2
    letI : IsProbabilityMeasure μ := by
      dsimp [μ, sampleLaw]
      letI : IsProbabilityMeasure (P.1.map obs) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      infer_instance
    have hzero_integral : (∫ s, f s ∂μ) = 0 := by
      have hle : (∫ s, f s ∂μ) ≤ 0 := by
        simpa [deterministicRisk, μ, f, ← hzero] using hrisk
      exact le_antisymm hle (integral_nonneg (fun s => sq_nonneg _))
    have hae : ∀ᵐ s ∂μ, f s = 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun s => sq_nonneg (mixedCountEstimator n d q s - ate P))
        Integrable.of_finite).mp hzero_integral
    let good : Set (Fin n → ObsRecord d) :=
      {s | ate P ∈ riskEnvelopeInterval n d q α s}
    have hgood : MeasurableSet good := by
      classical
      have heq : ((fun s : Fin n → ObsRecord d => decide (s ∈ good)) ⁻¹' {true}) =
          good := by
        ext s
        simp
      rw [← heq]
      exact (measurable_of_finite
        (fun s : Fin n → ObsRecord d => decide (s ∈ good)))
        (measurableSet_singleton true)
    have hgoodae : ∀ᵐ s ∂μ, s ∈ good := by
      filter_upwards [hae] with s hs
      apply riskEnvelopeInterval_contains_of_sq_error_le n d q α P s
      · simp [← hzero]
      · simpa [f, ← hzero] using le_of_eq hs
    have hprob : μ good = 1 := (mem_ae_iff_prob_eq_one hgood).mp hgoodae
    have hreal : μ.real good = 1 := by
      simp [measureReal_def, hprob]
    change 1 - α ≤ μ.real good
    rw [hreal]
    linarith
  · exact riskEnvelopeInterval_coverage_of_positive_envelope n d q α P hα hpos hrisk

-- @node: riskEnvelopeEndpoints_risk_le
/-- Given [the specified inputs and assumptions](hyp:n,d,q,α,P), [the stated mathematical conclusion holds](goal). -/
lemma riskEnvelopeEndpoints_risk_le (n d : ℕ) (q α : ℝ)
    (P : FullLaw d) :
    deterministicIntervalRisk (riskEnvelopeEndpoints n d q α) P ≤
      2 * Real.sqrt (riskEnvelope n d q / α) := by
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsProbabilityMeasure (sampleLaw n P) := by
    unfold sampleLaw
    letI : IsProbabilityMeasure (P.1.map obs) :=
      Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable obs P.1)
    infer_instance
  unfold deterministicIntervalRisk
  have hint : Integrable
      (fun s : Fin n → ObsRecord d =>
        (riskEnvelopeEndpoints n d q α s).2 -
          (riskEnvelopeEndpoints n d q α s).1) (sampleLaw n P) :=
    Integrable.of_finite
  have h := integral_mono hint (integrable_const _)
    (fun s => riskEnvelopeEndpoints_length_le n d q α s)
  simpa using h

-- @node: riskEnvelope_interval_upper
/-- Given [the specified inputs and assumptions](hyp:α,hα), [the stated mathematical conclusion holds](goal). -/
lemma riskEnvelope_interval_upper (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ) (q : ℝ) (P : FullLaw d),
        RareArrivalModelClass n d q P →
          deterministicIntervalRisk (riskEnvelopeEndpoints n d q α) P ≤
            C * Real.sqrt (frontierRate n d q) := by
  obtain ⟨C₀, hC₀, hupper⟩ := mixed_count_upper
  refine ⟨2 * Real.sqrt (C₀ / α), by positivity, ?_⟩
  intro n d q P hP
  have henv : riskEnvelope n d q ≤ C₀ * frontierRate n d q :=
    (hupper n d q P hP).2.1
  calc
    deterministicIntervalRisk (riskEnvelopeEndpoints n d q α) P ≤
        2 * Real.sqrt (riskEnvelope n d q / α) :=
      riskEnvelopeEndpoints_risk_le n d q α P
    _ ≤ 2 * Real.sqrt (C₀ * frontierRate n d q / α) := by
      gcongr
    _ = 2 * Real.sqrt (C₀ / α) * Real.sqrt (frontierRate n d q) := by
      rw [show C₀ * frontierRate n d q / α =
        (C₀ / α) * frontierRate n d q by ring]
      rw [Real.sqrt_mul (by positivity : 0 ≤ C₀ / α)]
      ring

-- @node: riskEnvelope_interval_worst_upper
/-- Given [the specified inputs and assumptions](hyp:α,hα), [the stated mathematical conclusion holds](goal). -/
lemma riskEnvelope_interval_worst_upper (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d → 0 < q →
        Causalean.Stat.worstCaseRiskReal
          (fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
            deterministicIntervalRisk (riskEnvelopeEndpoints n d q α) P.1) () ≤
          C * Real.sqrt (frontierRate n d q) := by
  obtain ⟨C, hC, hbound⟩ := riskEnvelope_interval_upper α hα
  refine ⟨C, hC, ?_⟩
  intro n d q hn hd hq
  unfold Causalean.Stat.worstCaseRiskReal
  by_cases hne : Nonempty {P : FullLaw d // RareArrivalModelClass n d q P}
  · letI := hne
    exact ciSup_le (fun P => hbound n d q P.1 P.2)
  · haveI : IsEmpty {P : FullLaw d // RareArrivalModelClass n d q P} :=
      not_nonempty_iff.mp hne
    simp
    have hN : 0 < effectiveSize n q := by
      unfold effectiveSize
      positivity
    have hrate : 0 ≤ frontierRate n d q := by
      unfold frontierRate
      exact le_min (by norm_num) (by positivity)
    positivity

-- @node: riskEnvelope_connectedInterval
/-- For [the specified inputs and assumptions](hyp:n,d,q,α,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def riskEnvelope_connectedInterval (n d : ℕ) (q α : ℝ)
    (s : Fin n → ObsRecord d) : ConnectedInterval := by
  let e := riskEnvelopeEndpoints n d q α s
  have hc := (mixed_count_estimator_regular n d q).2 s
  have hr : 0 ≤ Real.sqrt (riskEnvelope n d q / α) := Real.sqrt_nonneg _
  have hlo : -1 ≤ e.1 := by
    dsimp [e, riskEnvelopeEndpoints]
    exact le_max_left _ _
  have hhi : e.2 ≤ 1 := by
    dsimp [e, riskEnvelopeEndpoints]
    exact min_le_left _ _
  have horder : e.1 ≤ e.2 := by
    dsimp [e, riskEnvelopeEndpoints]
    apply le_min
    · exact max_le (by norm_num) (by linarith [hc.2])
    · exact max_le (by linarith [hc.1]) (by linarith)
  exact ⟨(e.1, e.2), hlo, horder, hhi⟩

-- @node: riskEnvelope_connectedInterval_contains
/-- Given [the specified inputs and assumptions](hyp:n,d,q,α,t,s), [the stated mathematical conclusion holds](goal). -/
lemma riskEnvelope_connectedInterval_contains (n d : ℕ) (q α t : ℝ)
    (s : Fin n → ObsRecord d) :
    intervalContains (riskEnvelope_connectedInterval n d q α s) t ↔
      t ∈ riskEnvelopeInterval n d q α s := by
  simp [intervalContains, riskEnvelopeInterval, riskEnvelope_connectedInterval]

-- @node: riskEnvelope_connectedInterval_length
/-- Given [the specified inputs and assumptions](hyp:n,d,q,α,s), [the stated mathematical conclusion holds](goal). -/
lemma riskEnvelope_connectedInterval_length (n d : ℕ) (q α : ℝ)
    (s : Fin n → ObsRecord d) :
    (riskEnvelope_connectedInterval n d q α s).hi -
      (riskEnvelope_connectedInterval n d q α s).lo =
        (riskEnvelopeEndpoints n d q α s).2 -
          (riskEnvelopeEndpoints n d q α s).1 := rfl

/-- Given [the specified inputs and assumptions](hyp:n,d,q,α,hα), [the stated mathematical conclusion holds](goal). -/
lemma riskEnvelope_honestInterval (n d : ℕ) (q α : ℝ) (hα : 0 < α) :
    HonestInterval n d q α
      ⟨Kernel.deterministic (riskEnvelope_connectedInterval n d q α)
        (measurable_of_finite _), inferInstance⟩ := by
  intro P hP
  obtain ⟨C, hC, hupper⟩ := mixed_count_upper
  have hrisk := hupper n d q P hP
  have hcoverage := riskEnvelopeInterval_coverage n d q α P hα hrisk.1
  let f := riskEnvelope_connectedInterval n d q α
  let μ := sampleLaw n P
  let good : Set (Fin n → ObsRecord d) :=
    {s | ate P ∈ riskEnvelopeInterval n d q α s}
  have hgood : MeasurableSet good := by
    exact MeasurableSet.of_discrete
  have heq (s : Fin n → ObsRecord d) :
      (Kernel.deterministic f (measurable_of_finite _) s).real
          {I | intervalContains I (ate P)} =
        good.indicator (fun _ => (1 : ℝ)) s := by
    have hset : MeasurableSet
        {I : ConnectedInterval | intervalContains I (ate P)} := by
      unfold intervalContains
      have hlo : Measurable (fun I : ConnectedInterval => I.lo) :=
        measurable_connectedInterval_lo
      have hhi : Measurable (fun I : ConnectedInterval => I.hi) :=
        measurable_connectedInterval_hi
      have hleft : Measurable (fun I : ConnectedInterval => I.closedLeft) :=
        measurable_const
      have hright : Measurable (fun I : ConnectedInterval => I.closedRight) :=
        measurable_const
      have hseteq :
          {I : ConnectedInterval |
            (if I.closedLeft = true then I.lo ≤ ate P else I.lo < ate P) ∧
              (if I.closedRight = true then ate P ≤ I.hi else ate P < I.hi)} =
          (({I | I.closedLeft = true} ∩ {I | I.lo ≤ ate P}) ∪
              ({I | I.closedLeft = false} ∩ {I | I.lo < ate P})) ∩
            (({I | I.closedRight = true} ∩ {I | ate P ≤ I.hi}) ∪
              ({I | I.closedRight = false} ∩ {I | ate P < I.hi})) := by
        ext I
        by_cases hl : I.closedLeft = true <;>
          by_cases hr : I.closedRight = true <;> simp [hl, hr]
      rw [hseteq]
      measurability
    rw [Kernel.deterministic_apply, Measure.real, Measure.dirac_apply' _ hset]
    by_cases hmem : ate P ∈ riskEnvelopeInterval n d q α s <;>
      simp [good, f, Set.indicator, riskEnvelope_connectedInterval_contains, hmem]
  change 1 - α ≤ ∫ s,
    (Kernel.deterministic f (measurable_of_finite _) s).real
      {I | intervalContains I (ate P)} ∂μ
  simp_rw [heq]
  rw [integral_indicator_const _ hgood]
  simpa [μ, good] using hcoverage

-- @node: intervalLengthRisk_le_riskEnvelope_worst
/-- Given [the specified inputs and assumptions](hyp:n,d,q,α,hα), [the stated mathematical conclusion holds](goal). -/
lemma intervalLengthRisk_le_riskEnvelope_worst (n d : ℕ) (q α : ℝ)
    (hα : 0 < α) :
    intervalLengthRisk n d q α ≤
      Causalean.Stat.worstCaseRiskReal
        (fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
          deterministicIntervalRisk (riskEnvelopeEndpoints n d q α) P.1) () := by
  let f := riskEnvelope_connectedInterval n d q α
  let T : IntervalProcedure n d :=
    IntervalProcedure.ofMap f (measurable_of_finite _)
  let H : {T : IntervalProcedure n d // HonestInterval n d q α T} :=
    ⟨T, riskEnvelope_honestInterval n d q α hα⟩
  have hrisk : ∀ (T : {T : IntervalProcedure n d // HonestInterval n d q α T})
      (P : {P : FullLaw d // RareArrivalModelClass n d q P}),
      0 ≤ intervalRisk T.1 P.1 := by
    intro T P
    exact integral_nonneg (fun s => integral_nonneg (fun I => sub_nonneg.mpr I.ordered))
  have hval := Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg hrisk H
  change intervalLengthRisk n d q α ≤
    Causalean.Stat.worstCaseRiskReal
      (fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
        intervalRisk H.1 P.1) () at hval
  have heq :
      (fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
        intervalRisk H.1 P.1) =
      (fun (_ : Unit) P =>
        deterministicIntervalRisk (riskEnvelopeEndpoints n d q α) P.1) := by
    funext _ P
    unfold intervalRisk deterministicIntervalRisk
    congr 1
    funext s
    change (∫ I : ConnectedInterval, I.hi - I.lo ∂(Kernel.deterministic f
      (measurable_of_finite _) s)) =
        (riskEnvelopeEndpoints n d q α s).2 -
          (riskEnvelopeEndpoints n d q α s).1
    have hlo : Measurable (fun I : ConnectedInterval => I.lo) :=
      measurable_connectedInterval_lo
    have hhi : Measurable (fun I : ConnectedInterval => I.hi) :=
      measurable_connectedInterval_hi
    have hmeas : StronglyMeasurable
        (fun I : ConnectedInterval => I.hi - I.lo) :=
      (hhi.sub hlo).stronglyMeasurable
    rw [Kernel.deterministic_apply, integral_dirac' _ _ hmeas]
    exact riskEnvelope_connectedInterval_length n d q α s
  rw [heq] at hval
  exact hval

/-- Given [the specified inputs and assumptions](hyp:I,s,θ,δ,w,hδ,hw,hmeet), [the stated mathematical conclusion holds](goal). -/
-- @node: connectedInterval_grid_neighborhood_length
lemma connectedInterval_grid_neighborhood_length (I : ConnectedInterval)
    (s : Finset ℕ) (θ δ w : ℝ) (hδ : 0 ≤ δ) (hw : 0 ≤ w)
    (hmeet : ∀ i ∈ s, ∃ x : ℝ,
      I.lo ≤ x ∧ x ≤ I.hi ∧ |x - (θ + (i : ℝ) * δ)| ≤ w) :
    ((s.card : ℝ) - 1) * δ - 2 * w ≤ I.hi - I.lo := by
  classical
  obtain hs | hs := s.eq_empty_or_nonempty
  · subst s
    simp only [Finset.card_empty, Nat.cast_zero]
    have hlen := I.ordered
    nlinarith
  · have hsub : s ⊆ Finset.Icc (s.min' hs) (s.max' hs) := by
      intro i hi
      exact Finset.mem_Icc.mpr ⟨s.min'_le i hi, s.le_max' i hi⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hminmax := s.min'_le_max' hs
    have hspan : s.card + s.min' hs ≤ s.max' hs + 1 := by omega
    have hspanR : (s.card : ℝ) - 1 ≤
        (s.max' hs : ℝ) - (s.min' hs : ℝ) := by
      exact_mod_cast (show (s.card : ℤ) - 1 ≤
        (s.max' hs : ℤ) - (s.min' hs : ℤ) by omega)
    obtain ⟨x, hxlo, hxhi, hx⟩ := hmeet (s.min' hs) (s.min'_mem hs)
    obtain ⟨y, hylo, hyhi, hy⟩ := hmeet (s.max' hs) (s.max'_mem hs)
    have hx' := (abs_le.mp hx).2
    have hy' := (abs_le.mp hy).1
    have hmul := mul_le_mul_of_nonneg_right hspanR hδ
    nlinarith

/-- Given [the specified inputs and assumptions](hyp:ν,s,θ,δ,w,hδ,hw,hcount,hmeet), [the stated mathematical conclusion holds](goal). -/
-- @node: connectedInterval_expected_grid_neighborhood_length
lemma connectedInterval_expected_grid_neighborhood_length
    (ν : Measure ConnectedInterval) [IsProbabilityMeasure ν]
    (s : ConnectedInterval → Finset ℕ) (θ δ w : ℝ)
    (hδ : 0 ≤ δ) (hw : 0 ≤ w)
    (hcount : Integrable (fun I => (s I).card : ConnectedInterval → ℝ) ν)
    (hmeet : ∀ I i, i ∈ s I → ∃ x : ℝ,
      I.lo ≤ x ∧ x ≤ I.hi ∧ |x - (θ + (i : ℝ) * δ)| ≤ w) :
    ((∫ I, ((s I).card : ℝ) ∂ν) - 1) * δ - 2 * w ≤
      ∫ I, I.hi - I.lo ∂ν := by
  have hmeas : Measurable (fun I : ConnectedInterval => I.hi - I.lo) := by
    fun_prop
  have hlen : Integrable (fun I : ConnectedInterval => I.hi - I.lo) ν :=
    Integrable.of_bound hmeas.aestronglyMeasurable 2
      (Filter.Eventually.of_forall (fun I => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr I.ordered)]
        linarith [I.lower, I.upper]))
  have hleft : Integrable (fun I =>
      (((s I).card : ℝ) - 1) * δ - 2 * w) ν :=
    ((hcount.sub (integrable_const 1)).mul_const δ).sub (integrable_const (2 * w))
  have hbound := integral_mono hleft hlen (fun I =>
    connectedInterval_grid_neighborhood_length I (s I) θ δ w hδ hw (hmeet I))
  have heq : (∫ I, (((s I).card : ℝ) - 1) * δ - 2 * w ∂ν) =
      ((∫ I, ((s I).card : ℝ) ∂ν) - 1) * δ - 2 * w := by
    integral_linearity
    simp
  rw [heq] at hbound
  exact hbound

-- @node: frontier_min_sum_le_twice_max
/-- Given [the specified inputs and assumptions](hyp:a,b), [the stated mathematical conclusion holds](goal). -/
lemma frontier_min_sum_le_twice_max (a b : ℝ) :
    min 1 (a + b) ≤ 2 * max (min 1 a) (min 1 b) := by
  by_cases ha1 : a ≤ 1
  · by_cases hb1 : b ≤ 1
    · simp only [min_eq_right ha1, min_eq_right hb1]
      by_cases hab : a ≤ b
      · rw [max_eq_right hab]
        exact (min_le_right _ _).trans (by linarith)
      · rw [max_eq_left (le_of_not_ge hab)]
        exact (min_le_right _ _).trans (by linarith)
    · have hb1' : 1 ≤ b := le_of_not_ge hb1
      rw [min_eq_left hb1', max_eq_right (by simpa [min_eq_right ha1] using ha1)]
      exact le_trans (min_le_left _ _) (by norm_num)
  · have ha1' : 1 ≤ a := le_of_not_ge ha1
    rw [min_eq_left ha1']
    exact le_trans (min_le_left _ _) (by
      have hmax : 1 ≤ max (1 : ℝ) (min 1 b) := le_max_left _ _
      linarith)

-- @node: frontierRate_le_two_lower_scales
/-- Given [the specified inputs and assumptions](hyp:n,d,q), [the stated mathematical conclusion holds](goal). -/
lemma frontierRate_le_two_lower_scales (n d : ℕ) (q : ℝ) :
    frontierRate n d q ≤ 2 * max
      (min 1 (effectiveSize n q)⁻¹)
      (min 1 (((d : ℝ) / (effectiveSize n q * logScale n q)) ^ 2)) := by
  unfold frontierRate
  exact frontier_min_sum_le_twice_max _ _

/-- Given [the specified inputs and assumptions](hyp:x), [the stated mathematical conclusion holds](goal). -/
-- @node: frontier_sqrt_min_one
lemma frontier_sqrt_min_one (x : ℝ) :
    Real.sqrt (min 1 x) = min 1 (Real.sqrt x) := by
  by_cases hx : x ≤ 1
  · rw [min_eq_right hx, min_eq_right (Real.sqrt_le_one.mpr hx)]
  · have hx' : 1 ≤ x := le_of_not_ge hx
    have hs : 1 ≤ Real.sqrt x := by
      simpa using Real.sqrt_le_sqrt hx'
    rw [min_eq_left hx', min_eq_left hs, Real.sqrt_one]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,c,L,hc,hparam,hmany,hN), [the stated mathematical conclusion holds](goal). -/
-- @node: frontier_interval_lower_of_two_scales
lemma frontier_interval_lower_of_two_scales (n d : ℕ) (q c L : ℝ)
    (hc : 0 ≤ c)
    (hparam : c * Real.sqrt (min 1 (effectiveSize n q)⁻¹) ≤ L)
    (hmany : c * Real.sqrt
      (min 1 (((d : ℝ) / (effectiveSize n q * logScale n q)) ^ 2)) ≤ L)
    (hN : 0 ≤ effectiveSize n q) :
    (c / 2) * Real.sqrt (frontierRate n d q) ≤ L := by
  let A := min 1 (effectiveSize n q)⁻¹
  let B := min 1 (((d : ℝ) / (effectiveSize n q * logScale n q)) ^ 2)
  have hA : 0 ≤ A := le_min (by norm_num) (inv_nonneg.mpr hN)
  have hmax : 0 ≤ max A B := hA.trans (le_max_left _ _)
  have hboth : c * Real.sqrt (max A B) ≤ L := by
    rcases le_total A B with h | h
    · simpa [max_eq_right h, B] using hmany
    · simpa [max_eq_left h, A] using hparam
  have hrate := frontierRate_le_two_lower_scales n d q
  have hs : Real.sqrt (frontierRate n d q) ≤ 2 * Real.sqrt (max A B) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hsq := Real.sq_sqrt hmax
    change frontierRate n d q ≤ 2 * max A B at hrate
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hs hc
  linarith

-- @node: thm:connected-interval-frontier
/-- At every admissible miscoverage level, [connected randomized intervals attain matching frontier bounds](goal). -/
theorem connected_interval_frontier :
    ∀ α : ℝ, 0 < α → α < 1 → -- @realizes \(\alpha\)(miscoverage level)
      -- @realizes \(\underline c_\alpha\)(positive interval lower constant)
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ -- @realizes \(\overline C_\alpha\)(interval upper constant)
        ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d → 0 < q → q ≤ 1 →
          RareArrivalSlice n q →
            c * Real.sqrt (frontierRate n d q) ≤ intervalLengthRisk n d q α ∧
            intervalLengthRisk n d q α ≤
              Causalean.Stat.worstCaseRiskReal
                (fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
                  deterministicIntervalRisk (riskEnvelopeEndpoints n d q α) P.1) () ∧
            Causalean.Stat.worstCaseRiskReal
                (fun (_ : Unit) (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
                  deterministicIntervalRisk (riskEnvelopeEndpoints n d q α) P.1) () ≤
                C * Real.sqrt (frontierRate n d q) ∧
            (∀ P : FullLaw d, RareArrivalModelClass n d q P →
              1 - α ≤ (sampleLaw n P).real
                {s | ate P ∈ riskEnvelopeInterval n d q α s}) := by
  intro α hα hα1
  obtain ⟨C, hC, hUpper⟩ := riskEnvelope_interval_worst_upper α hα
  obtain ⟨c₀, hc₀, hLower⟩ :
      ∃ c₀ : ℝ, 0 < c₀ ∧
        ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d → 0 < q → q ≤ 1 →
          RareArrivalSlice n q →
            c₀ * Real.sqrt (frontierRate n d q) ≤ intervalLengthRisk n d q α := by
    obtain ⟨c₁, hc₁, hMany⟩ :
        ∃ c₁ : ℝ, 0 < c₁ ∧
          ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d → 0 < q → q ≤ 1 →
            RareArrivalSlice n q →
              c₁ * Real.sqrt (min 1
                (((d : ℝ) / (effectiveSize n q * logScale n q)) ^ 2)) ≤
                  intervalLengthRisk n d q α := by
      let η := Real.exp (-32)
      obtain ⟨T, D, cAct, hT, hD, hcAct, hActivated⟩ :
          ∃ (T : ℝ) (D : ℕ) (cAct : ℝ), 1 ≤ T ∧ 1 ≤ D ∧ 0 < cAct ∧
            ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d → 0 < q → q ≤ 1 →
              RareArrivalSlice n q → T ≤ effectiveSize n q →
                (D : ℝ) ≤ (2 * rareMass η n q)⁻¹ ∧
                (D ≤ rareCount η n d q →
                  cAct * min 1 ((d : ℝ) /
                    (effectiveSize n q * logScale n q)) ≤ intervalLengthRisk n d q α) := by
        exact interval_activated_large_regime α hα.le hα1
      let cP := 3 * (1 - α) ^ 2 / 512
      have hcP : 0 < cP := by dsimp [cP]; positivity
      refine ⟨min cAct (min (cP * min 1 (Real.sqrt T)⁻¹) (cP / D)),
        by positivity, ?_⟩
      intro n d q hn hd hq hq1 hslice
      have hN : 0 < effectiveSize n q := by unfold effectiveSize; positivity
      have hell : 1 ≤ logScale n q := by
        unfold logScale
        have h := Real.log_le_log (Real.exp_pos (1 : ℝ))
          (show Real.exp 1 ≤ Real.exp 1 + effectiveSize n q by linarith)
        simpa using h
      obtain ⟨M, grid, hM, hinj, hgrid, -, hfloor⟩ :=
        oneCell_interval_minimax_floor q α hn hd hq hq1 hslice hα hα1
      rw [interval_many_scale_sqrt n d q hN (by linarith)]
      apply interval_many_scale_of_large_regime η T cP cAct D hT hD hcP hcAct
        n d q (intervalLengthRisk n d q α) hd hN hell hfloor
      · intro hNT
        exact (hActivated n d q hn hd hq hq1 hslice hNT).1
      · intro hNT hJ
        exact (hActivated n d q hn hd hq hq1 hslice hNT).2 hJ
    let cParam := 3 * (1 - α) ^ 2 / 512
    have hcParam : 0 < cParam := by dsimp [cParam]; positivity
    refine ⟨min cParam c₁ / 2, by positivity, ?_⟩
    intro n d q hn hd hq hq1 hslice
    obtain ⟨M, grid, hM, hinj, hgrid, -, hfloor⟩ :=
      oneCell_interval_minimax_floor q α hn hd hq hq1 hslice hα hα1
    apply frontier_interval_lower_of_two_scales n d q (min cParam c₁) _
      (le_of_lt (lt_min hcParam hc₁))
    · rw [frontier_sqrt_min_one, Real.sqrt_inv]
      exact (mul_le_mul_of_nonneg_right (min_le_left cParam c₁)
        (le_min (by norm_num) (by positivity))).trans hfloor
    · exact (mul_le_mul_of_nonneg_right (min_le_right cParam c₁)
        (Real.sqrt_nonneg _)).trans (hMany n d q hn hd hq hq1 hslice)
    · unfold effectiveSize
      positivity
  refine ⟨min c₀ C, C, lt_min hc₀ hC, min_le_right _ _, ?_⟩
  intro n d q hn hd hq hq1 hslice
  refine ⟨?_, intervalLengthRisk_le_riskEnvelope_worst n d q α hα,
    hUpper n d q hn hd hq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (min_le_left c₀ C)
      (Real.sqrt_nonneg _)).trans (hLower n d q hn hd hq hq1 hslice)
  · intro P hP
    obtain ⟨C', hC', hMixed⟩ := mixed_count_upper
    have hrisk := hMixed n d q P hP
    exact riskEnvelopeInterval_coverage n d q α P hα hrisk.1

end CausalSmith.Stat.MarRareqLogfrontier

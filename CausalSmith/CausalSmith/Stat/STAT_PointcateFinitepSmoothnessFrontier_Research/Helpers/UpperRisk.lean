module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.RatioRisk

/-! Finite-moment point-CATE frontier: Helpers/UpperRisk. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- Every denominator in the public bias ledger is positive on the public domain. -/
-- @node: cPub_positive
lemma cPub_positive (κ : Params) (hκ : κ.Valid) : 0 < cPub κ := by
  have hp := phase_algebra κ hκ
  have hA : 0 < constantA κ := hp.2.2.2.2.1
  have hE : 0 < constantE κ := hp.2.2.2.2.2.1
  have hb : 0 < cBias κ := by
    unfold cBias
    positivity
  have hn : 0 ≤ cNoise κ := by
    unfold cNoise
    positivity
  unfold cPub
  positivity

/-- A center in the target range and a nonnegative radius give a nonempty closed interval,
whose length is bounded by both the target diameter and twice the radius. -/
-- @node: closedInterval_radius_certificate
lemma closedInterval_radius_certificate (t r : ℝ) (ht : t ∈ Icc (-1/2) (1/2))
    (hr : 0 ≤ r) :
    (closedInterval (max (-1/2) (t-r)) (min (1/2) (t+r))).length ≤ min 1 (2*r) ∧
    ∃ c : Endpoints,
      closedInterval (max (-1/2) (t-r)) (min (1/2) (t+r)) = .inr c ∧
      c.1.2.2.1 = true ∧ c.1.2.2.2 = true := by
  have hlo : max (-1/2 : ℝ) (t-r) ≤ t := max_le ht.1 (by linarith)
  have hhi : t ≤ min (1/2 : ℝ) (t+r) := le_min ht.2 (by linarith)
  have hv : (-1/2 : ℝ) ≤ max (-1/2) (t-r) ∧
      max (-1/2) (t-r) ≤ min (1/2) (t+r) ∧ min (1/2) (t+r) ≤ 1/2 :=
    ⟨le_max_left _ _, hlo.trans hhi, min_le_left _ _⟩
  simp only [closedInterval, dif_pos hv, IntervalCode.length, Causalean.Stat.intervalLength]
  constructor
  · apply max_le
    · exact le_min (by norm_num) (by linarith)
    · apply le_min
      · have h1 := le_max_left (-1/2 : ℝ) (t-r)
        have h2 := min_le_left (1/2 : ℝ) (t+r)
        linarith
      · have h1 := le_max_right (-1/2 : ℝ) (t-r)
        have h2 := min_le_right (1/2 : ℝ) (t+r)
        linarith
  · exact ⟨⟨(max (-1/2) (t-r), min (1/2) (t+r), true, true), hv⟩, rfl, rfl, rfl⟩

/-- The explicit reported intervals have ordered closed endpoints and the advertised
finite-sample length, including when the radius covers the entire target range. -/
-- @node: upperInterval_certificate
lemma upperInterval_certificate (κ : Params) (hκ : κ.Valid) (n : ℕ)
    (z : Dataset n × unitInterval × Unit) :
    (upperInterval κ n z).length ≤ min 1 (20*cPub κ*rate κ n) ∧
    ∃ c : Endpoints, upperInterval κ n z = .inr c ∧
      c.1.2.2.1 = true ∧ c.1.2.2.2 = true := by
  have hc := cPub_positive κ hκ
  have hrate : 0 ≤ rate κ n := by unfold rate; positivity
  have hr : upperRadius κ n = 10*cPub κ*rate κ n := by
    unfold upperRadius
    exact max_eq_right (by positivity)
  have h := closedInterval_radius_certificate (upperEstimator κ n z) (upperRadius κ n)
    ((upperEstimator_total κ n).2 z) (le_max_left _ _)
  change (upperInterval κ n z).length ≤ min 1 (2*upperRadius κ n) ∧ _ at h
  have hlen := h.1
  rw [hr, show 2*(10*cPub κ*rate κ n) = 20*cPub κ*rate κ n by ring] at hlen
  exact ⟨hlen, h.2⟩

/-- The Markov argument can use the error event directly: every target in range within
the public radius belongs to the actual clipped, closed reported interval. -/
-- @node: upperInterval_covers_of_error
lemma upperInterval_covers_of_error (κ : Params) (n : ℕ)
    (z : Dataset n × unitInterval × Unit) (θ : ℝ) (hθ : θ ∈ Icc (-1/2) (1/2))
    (herr : |upperEstimator κ n z - θ| ≤ upperRadius κ n) :
    θ ∈ (upperInterval κ n z).toSet := by
  have ht := (upperEstimator_total κ n).2 z
  have hr : 0 ≤ upperRadius κ n := le_max_left _ _
  have hlo : max (-1/2 : ℝ) (upperEstimator κ n z-upperRadius κ n) ≤ upperEstimator κ n z :=
    max_le ht.1 (by linarith)
  have hhi : upperEstimator κ n z ≤ min (1/2 : ℝ) (upperEstimator κ n z+upperRadius κ n) :=
    le_min ht.2 (by linarith)
  have hv : (-1/2 : ℝ) ≤ max (-1/2) (upperEstimator κ n z-upperRadius κ n) ∧
      max (-1/2) (upperEstimator κ n z-upperRadius κ n) ≤
        min (1/2) (upperEstimator κ n z+upperRadius κ n) ∧
      min (1/2) (upperEstimator κ n z+upperRadius κ n) ≤ 1/2 :=
    ⟨le_max_left _ _, hlo.trans hhi, min_le_left _ _⟩
  simp only [upperInterval, closedInterval, dif_pos hv, IntervalCode.toSet,
    ↓reduceIte, mem_Icc]
  have he := abs_le.mp herr
  exact ⟨max_le hθ.1 (by linarith), le_min hθ.2 (by linarith)⟩

/-- A bounded original-record decision has integrable absolute target error. -/
-- @node: upperEstimator_error_integrable
lemma upperEstimator_error_integrable (κ : Params) (n : ℕ)
    (μ : Measure (Experiment n)) [IsProbabilityMeasure μ] (θ : ℝ)
    (hθ : θ ∈ Icc (-1/2) (1/2)) :
    Integrable (fun z => |upperEstimator κ n (z.1, z.2, ()) - θ|) μ := by
  have hm : Measurable (fun z : Experiment n =>
      |upperEstimator κ n (z.1, z.2, ()) - θ|) := by
    have ht := (upperEstimator_total κ n).1
    fun_prop
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  have ht := (upperEstimator_total κ n).2 (z.1, z.2, ())
  rw [Real.norm_eq_abs, abs_abs]
  exact abs_le.mpr ⟨by linarith [ht.1, hθ.2], by linarith [ht.2, hθ.1]⟩

/-- Markov's inequality makes the public clipped interval honest once its absolute-risk
ledger is established; boundedness supplies integrability without a new model premise. -/
-- @node: upperInterval_coverage_of_risk
lemma upperInterval_coverage_of_risk (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n)
    (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw)
    (law : ObservedLaw) (hm : InModel κ law)
    (hrisk : decisionRisk n expLaw (fun _ => ()) (upperDecision κ n) law ≤
      cPub κ * rate κ n) :
    9/10 ≤ coverage n expLaw (fun _ => ()) (upperIntervalDecision κ n) law := by
  let μ := expLaw n law.P
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hμ : μ = (Measure.pi (fun _ : Fin n => law.P)).prod design :=
    hiid n hn law.P inferInstance
  let : IsProbabilityMeasure μ := by
    rw [hμ]
    infer_instance
  let err : Experiment n → ℝ := fun z => |upperEstimator κ n (z.1, z.2, ()) - law.theta|
  have hθ : law.theta ∈ Icc (-1/2) (1/2) := by
    simpa only [ObservedLaw.theta, mem_Icc, neg_div] using abs_le.mp (hm.effectRange xstar)
  have he : Integrable err μ := upperEstimator_error_integrable κ n μ law.theta hθ
  have hc := cPub_positive κ hκ
  have hrate : 0 < rate κ n := by
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    unfold rate
    positivity
  have hr : upperRadius κ n = 10 * (cPub κ * rate κ n) := by
    unfold upperRadius
    rw [max_eq_right (by positivity)]
    ring
  have hrpos : 0 < upperRadius κ n := by rw [hr]; positivity
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := err)
    (Filter.Eventually.of_forall (fun z => abs_nonneg
      (upperEstimator κ n (z.1, z.2, ()) - law.theta))) he (upperRadius κ n)
  have hbad : μ.real {z | upperRadius κ n < err z} ≤ (1/10 : ℝ) := by
    have hsub : μ.real {z | upperRadius κ n < err z} ≤
        μ.real {z | upperRadius κ n ≤ err z} :=
      measureReal_mono (μ := μ)
        (fun z (hz : upperRadius κ n < err z) => le_of_lt hz) (measure_ne_top μ _)
    have hnonneg : 0 ≤ μ.real {z | upperRadius κ n < err z} := measureReal_nonneg
    have hmul := (mul_le_mul_of_nonneg_left hsub hrpos.le).trans hmarkov
    change (∫ z, err z ∂μ) ≤ cPub κ * rate κ n at hrisk
    rw [hr] at hmul
    rw [hr]
    have hp := mul_pos hc hrate
    nlinarith only [hmul.trans hrisk, hp]
  have hgood : MeasurableSet {z | err z ≤ upperRadius κ n} := by
    have ht := (upperEstimator_total κ n).1
    apply measurableSet_le _ measurable_const
    dsimp [err]
    fun_prop
  have hcompl := measureReal_compl (μ := μ) hgood
  have hgoodprob : (9/10 : ℝ) ≤ μ.real {z | err z ≤ upperRadius κ n} := by
    have heq : {z | err z ≤ upperRadius κ n}ᶜ = {z | upperRadius κ n < err z} := by
      ext z
      simp
    rw [heq, probReal_univ] at hcompl
    linarith only [hcompl, hbad]
  apply hgoodprob.trans
  change μ.real {z | err z ≤ upperRadius κ n} ≤
    μ.real {z | law.theta ∈ (upperInterval κ n (z.1, z.2, ())).toSet}
  apply measureReal_mono (μ := μ) _ (measure_ne_top μ _)
  intro z hz
  exact upperInterval_covers_of_error κ n (z.1, z.2, ()) law.theta hθ hz

/-- The safeguard, final range projection and Markov radius certify one honest original procedure. -/
-- @node: upper_risk
lemma upper_risk (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n)
    (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw) :
  0 < cPub κ ∧
  (∀ law, InModel κ law → decisionRisk n expLaw (fun _ => ()) (upperDecision κ n) law ≤ cPub κ*rate κ n) ∧
  (∀ law, InModel κ law → 9/10 ≤ coverage n expLaw (fun _ => ()) (upperIntervalDecision κ n) law) ∧
  (∀ z, (upperInterval κ n z).length ≤ min 1 (20*cPub κ*rate κ n) ∧
    ∃ c : Endpoints, upperInterval κ n z = .inr c ∧ c.1.2.2.1 = true ∧ c.1.2.2.2 = true) := by
  suffices hstat :
      (∀ law, InModel κ law → decisionRisk n expLaw (fun _ => ()) (upperDecision κ n) law ≤ cPub κ*rate κ n) ∧
      (∀ law, InModel κ law → 9/10 ≤ coverage n expLaw (fun _ => ()) (upperIntervalDecision κ n) law) by
    exact ⟨cPub_positive κ hκ, hstat.1, hstat.2, upperInterval_certificate κ hκ n⟩
  -- Assemble the bias/noise ledgers through the safeguard, then apply Markov.
  have hrisk : ∀ law, InModel κ law →
      decisionRisk n expLaw (fun _ => ()) (upperDecision κ n) law ≤ cPub κ*rate κ n := by
    intro law hm
    let μ := Measure.pi (fun _ : Fin n => law.P)
    let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
    let : IsProbabilityMeasure design := by unfold design; infer_instance
    let N₀ := localNumerator law (upperH κ n) (upperJ κ n)
    let D₀ := localDenominator law (upperH κ n) (upperJ κ n)
    let m := ∫ o, numeratorHat κ n o ∂μ
    have hθ : law.theta ∈ Icc (-1/2) (1/2) := by
      simpa only [ObservedLaw.theta, mem_Icc, neg_div] using abs_le.mp (hm.effectRange xstar)
    have htune := upper_tuning κ hκ n hn
    have hD : 3/16 ≤ D₀ :=
      (local_covariance_bias κ hκ law hm _ htune.1 (upperJ κ n)).1
    have hInt := upper_statistics_integrable κ n μ
    have hN := (hInt.1.sub (integrable_const m)).abs
    have hDen := (hInt.2.sub (integrable_const D₀)).abs
    let B := |m-N₀| + |N₀-law.theta*D₀|
    have hpoint (o : Dataset n) :
        |upperEstimator κ n (o, 0, ()) - law.theta| ≤
          (32/3 : ℝ) * (|numeratorHat κ n o-m| + B + |denominatorHat κ n o-D₀|) := by
      have h := safeguarded_ratio_error (numeratorHat κ n o) (denominatorHat κ n o)
        N₀ D₀ law.theta hD hθ
      have hn := abs_add_le (numeratorHat κ n o-m) (m-N₀)
      rw [sub_add_sub_cancel] at hn
      change |upperEstimator κ n (o, 0, ()) - law.theta| ≤ _ at h
      dsimp [B]
      linarith
    have he : Integrable (fun o : Dataset n =>
        |upperEstimator κ n (o, 0, ()) - law.theta|) μ := by
      have hm' : Measurable (fun o : Dataset n =>
          |upperEstimator κ n (o, 0, ()) - law.theta|) := by
        have ht := (upperEstimator_total κ n).1
        fun_prop
      apply (integrable_const (1 : ℝ)).mono' hm'.aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro o
      rw [Real.norm_eq_abs, abs_abs]
      have ht := (upperEstimator_total κ n).2 (o, 0, ())
      exact abs_le.mpr ⟨by linarith [ht.1, hθ.2], by linarith [ht.2, hθ.1]⟩
    have hmajor := ((hN.add (integrable_const B)).add hDen).const_mul (32/3 : ℝ)
    have hib := integral_mono he hmajor hpoint
    dsimp only [Pi.add_apply, Pi.sub_apply] at hib hN hDen
    have hNB : Integrable (fun o => |numeratorHat κ n o-m| + B) μ :=
      hN.add (integrable_const B)
    have hsum : (∫ o, (32/3 : ℝ) *
        (|numeratorHat κ n o-m| + B + |denominatorHat κ n o-D₀|) ∂μ) =
        (32/3 : ℝ) * ((∫ o, |numeratorHat κ n o-m| ∂μ) + B +
          (∫ o, |denominatorHat κ n o-D₀| ∂μ)) := by
      integral_linearity
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [hsum] at hib
    have hvar := upper_variance κ hκ n hn law hm
    have hbias := (upper_bias κ hκ n hn law hm).2.2
    change B ≤ cBias κ*rate κ n at hbias
    change (∫ o, |numeratorHat κ n o-m| ∂μ) ≤ cNoise κ*rate κ n ∧
      (∫ o, |denominatorHat κ n o-D₀| ∂μ) ≤ 20*rate κ n at hvar
    have hr : 0 ≤ rate κ n := by unfold rate; positivity
    have hc : 0 ≤ cBias κ+cNoise κ+20 := by
      have hp := cPub_positive κ hκ
      unfold cPub at hp
      linarith
    have hrisk : (∫ o, |upperEstimator κ n (o, 0, ()) - law.theta| ∂μ) ≤
        cPub κ*rate κ n := by
      unfold cPub
      nlinarith [mul_nonneg hc hr]
    change (∫ z, |upperEstimator κ n (z.1, z.2, ()) - law.theta| ∂expLaw n law.P) ≤ _
    rw [hiid n hn law.P inferInstance]
    change (∫ z, |upperEstimator κ n (z.1, z.2, ()) - law.theta| ∂μ.prod design) ≤ _
    have hseed : (fun z : Experiment n => |upperEstimator κ n (z.1, z.2, ()) - law.theta|) =
        (fun z => |upperEstimator κ n (z.1, 0, ()) - law.theta|) := by
      funext z
      rfl
    rw [hseed, integral_fun_fst (μ := μ) (ν := design)
      (fun o : Dataset n => |upperEstimator κ n (o, 0, ()) - law.theta|)]
    simpa only [probReal_univ, one_smul] using hrisk
  exact ⟨hrisk, fun law hm => upperInterval_coverage_of_risk κ hκ n hn expLaw hiid
    law hm (hrisk law hm)⟩

/-- Existence of the full public construction, witnessed by the explicit two-block procedure and its ledgers. -/
-- @node: upper_handle_exists
lemma upper_handle_exists (κ : Params) : ∃ program : UpperProgram, UpperProgramCertificate κ program := by
  refine ⟨(cPub κ, fun n => (upperDecision κ n, upperRadius κ n, upperIntervalDecision κ n)), ?_⟩
  intro hκ
  have hiid : IIDSampling jointLaw := by
    intro n hn P hP
    rfl
  have hc := (upper_risk κ hκ 2 (by omega) jointLaw hiid).1
  refine ⟨hc, ?_⟩
  intro n hn
  have hr := upper_risk κ hκ n hn jointLaw hiid
  have ht := upper_tuning κ hκ n hn
  have hrate : 0 ≤ rate κ n := by
    unfold rate
    positivity
  have hrad : upperRadius κ n = 10*cPub κ*rate κ n := by
    unfold upperRadius
    exact max_eq_right (by positivity)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold upperRadius
    exact le_max_left _ _
  · rw [hrad]
    ring_nf
    exact le_rfl
  · refine ⟨treatmentBlock n, outcomeBlock n, ?_, ?_, ?_, ?_,
      upperH κ n, ht.1.1, ht.1.2, upperJ κ n, upperT κ n, ht.2.2.2.2.2.1,
      3/32, by norm_num, ?_⟩
    · refine ⟨⟨0, by omega⟩, ?_⟩
      simp only [treatmentBlock, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · refine ⟨⟨n/2, by omega⟩, ?_⟩
      simp [outcomeBlock]
    · apply Finset.disjoint_left.mpr
      intro i hiT hiY
      simp only [treatmentBlock, outcomeBlock, Finset.mem_filter,
        Finset.mem_univ, true_and] at hiT hiY
      omega
    · ext i
      simp only [Finset.mem_union, treatmentBlock, outcomeBlock, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact iff_true_intro (lt_or_ge i.val (n/2))
    · intro z
      rfl
  · intro z
    rfl
  · intro law hlaw
    exact ⟨hr.2.1 law hlaw, hr.2.2.1 law hlaw⟩
  · intro z
    rw [hrad]
    have hz := (hr.2.2.2 z).1
    change (upperInterval κ n z).length ≤ min 1 (2*(10*cPub κ*rate κ n))
    rw [show 2*(10*cPub κ*rate κ n) = 20*cPub κ*rate κ n by ring]
    exact hz

-- @node: def:upper-handle
/-- Select a public two-block programme supplied by upper_handle_exists, retaining its full certificate.
The concrete half-split procedure above is an auxiliary proof witness, rather than a uniquely specified choice. -/
def upperHandle (κ : Params) : {program : UpperProgram // UpperProgramCertificate κ program} :=
  ⟨Classical.choose (upper_handle_exists κ), Classical.choose_spec (upper_handle_exists κ)⟩ -- @realizes upperHandle(certified public two-block programme)

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

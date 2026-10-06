module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Decision
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.Upper
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.PairedTV

/-!
# Helpers/TVModel

Finite original-record private value frontiers: Helpers/TVModel.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


variable {n d : ℕ}
-- @env: S5
variable (M : Set (Measure (PairedSymbol d))) -- @realizes \mathcal M(paired family or simplex)
-- @node: def:tv-private-decision-values
/-- Fix [the protocol-class label](hyp:C), [the probability law M](hyp:M), [the sample size](hyp:n), and [the privacy budget](hyp:eps). [Paired-input pure-local minimax squared-error value, with canonical iid sampling](goal). -/
def tvMinimaxRisk (C : ProtocolClassLabel) (M : Set (Measure (PairedSymbol d)))
    (n : ℕ) (eps : ℝ) : ℝ≥0∞ :=
  riskValue (n := n) M tvFromUniform canonicalDecisionLaw C eps
  -- @realizes \mathfrak R^{\mathrm{TV}}(minimax TV MSE) @realizes \mathfrak K(paired input class)
/-- Fix [the protocol-class label](hyp:C), [the probability law M](hyp:M), [the sample size](hyp:n), and [the privacy budget](hyp:eps). [Globally honest TV interval value on the specified model, interval range [0,1]](goal). -/
def tvHonestLength (C : ProtocolClassLabel) (M : Set (Measure (PairedSymbol d)))
    (n : ℕ) (eps : ℝ) : ℝ≥0∞ :=
  lengthValue (n := n) M tvFromUniform canonicalDecisionLaw C eps 0 1
  -- @realizes \mathfrak H^{\mathrm{TV}}(minimax honest TV length)
/-- Fix [the sample size and the dimension](hyp:n,d) and [the privacy budget and the public seed and the stated h condition and the constant C0](hyp:eps,r,h,C0). [Paired finite sign-vector protocol and attaining transcript-only decisions in [0,1/4]](goal). -/
def TvAttainment (n d : ℕ) (eps r h C0 : ℝ) : Prop :=
  ∃ K : LocalProtocol n (PairedSymbol d), NoninteractiveClass K eps ∧
    (∀ i : Fin n, Nonempty (K.Message i ≃ (Fin d → Bool))) ∧
    ∃ (T : Estimator K) (J : IntervalDecision K 0 (1/4)), TranscriptOnly K T ∧
      ∀ p ∈ pairedFamily d,
        squaredRisk (canonicalDecisionLaw K p) T (tvFromUniform p) ≤ ENNReal.ofReal (C0*r) ∧
        (0.90 : ℝ) ≤ coverage (canonicalDecisionLaw K p) J (tvFromUniform p) ∧
        expectedLength (canonicalDecisionLaw K p) J ≤ ENNReal.ofReal (C0*h)

/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the participant index](hyp:i). [Paired-input signed-vector channel, with constant unused releases](goal). -/
def tvFrontierKernel (n d : ℕ) (eps : ℝ) (i : Fin n) :
    Kernel (PairedSymbol d) (Fin d → Bool) :=
  ⟨fun v => atomLaw (fun z =>
    if i.val < 2*(frontierDesign n d eps).resources.m then
      (2 : ℝ)^(-(d : ℤ)) * (1 + privacyDelta eps * signVal v.2 * signVal (z v.1))
    else if z = (fun _ => false) then 1 else 0), measurable_of_countable _⟩
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the participant index](hyp:i). [Paired participant stage ignoring seed and histories](goal). -/
def tvFrontierStageKernel (n d : ℕ) (eps : ℝ) (i : Fin n) :
    Kernel ((PairedSymbol d × Fin 1) ×
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.History
        (fun _ : Fin n => Fin d → Bool) i.val (Nat.le_of_lt i.isLt)) (Fin d → Bool) :=
  (tvFrontierKernel n d eps i).comap (fun w => w.1.1) (measurable_fst.comp measurable_fst)
/-- [Markov certificate of the concrete paired participant channel](goal). -/
-- @node: tvFrontierStage_markov
lemma tvFrontierStage_markov (n d : ℕ) (eps : ℝ) (i : Fin n) :
    IsMarkovKernel (tvFrontierStageKernel n d eps i) := by
  classical
  have hk : IsMarkovKernel (tvFrontierKernel n d eps i) := by
    constructor
    intro v
    constructor
    change atomLaw _ Set.univ = 1
    by_cases h : i.val < 2*(frontierDesign n d eps).resources.m
    · let o : ObsRecord d := (v.1, true, v.2)
      change atomLaw (fun z => if i.val < 2*(frontierDesign n d eps).resources.m then
        _ else _) Set.univ = 1
      simp only [h, ↓reduceIte]
      have ho := (vectorKernel_markov d eps).isProbabilityMeasure o |>.measure_univ
      change atomLaw (vectorMass eps o) Set.univ = 1 at ho
      have hm : vectorMass eps o = (fun z => (2 : ℝ)^(-(d : ℤ)) *
          (1 + privacyDelta eps * signVal v.2 * signVal (z v.1))) := by
        funext z
        simp [vectorMass, o, obsSign, signVal]
      rw [hm] at ho
      exact ho
    · simp [h, atomLaw, Measure.finsetSum_apply, Measure.smul_apply,
        Measure.dirac_apply_of_mem, apply_ite ENNReal.ofReal]
  letI := hk
  unfold tvFrontierStageKernel
  infer_instance
/-- Fix [the sample size and the dimension](hyp:n,d) and [the privacy budget](hyp:eps). [Resource-selected finite sign-vector NI protocol for the paired model](goal). -/
def tvFrontierProtocol (n d : ℕ) (eps : ℝ) : LocalProtocol n (PairedSymbol d) where
  Seed := Fin 1
  seedMeasurable := inferInstance
  seedStandard := inferInstance
  seedLaw := Measure.dirac 0
  seedProbability := inferInstance
  Message := fun _ => Fin d → Bool
  messageMeasurable := fun _ => inferInstance
  messageStandard := fun _ => inferInstance
  kernels := tvFrontierStageKernel n d eps
  markov := tvFrontierStage_markov n d eps
/-- Assume [a nonnegative privacy budget](hyp:heps) and [the set hE](hyp:hE). [Active paired rows are signed-vector rows after a deterministic record embedding; unused participants release the same constant for every input](goal). -/
-- @node: tvFrontierKernel_privacy
lemma tvFrontierKernel_privacy (n d : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (i : Fin n) (v v' : PairedSymbol d) (E : Set (Fin d → Bool))
    (hE : MeasurableSet E) :
    tvFrontierKernel n d eps i v E ≤
      ENNReal.ofReal (Real.exp eps) * tvFrontierKernel n d eps i v' E := by
  classical
  by_cases hi : i.val < 2*(frontierDesign n d eps).resources.m
  · have hmass (u : PairedSymbol d) :
        vectorMass eps (u.1, true, u.2) =
          (fun z => (2 : ℝ)^(-(d : ℤ)) *
            (1 + privacyDelta eps * signVal u.2 * signVal (z u.1))) := by
      funext z
      simp [vectorMass, obsSign, signVal]
    simpa only [tvFrontierKernel, Kernel.coe_mk, hi, ↓reduceIte,
      vectorKernel, hmass] using
      vectorKernel_privacy eps heps (v.1, true, v.2) (v'.1, true, v'.2) E hE
  · have he : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp eps) := by
      simpa only [ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr heps)
    change atomLaw _ E ≤ ENNReal.ofReal (Real.exp eps) * atomLaw _ E
    simp only [hi, ↓reduceIte]
    exact le_mul_of_one_le_left' he

/-- Assume [a nonnegative privacy budget](hyp:heps). [The resource-selected paired sign-vector protocol is noninteractive and pure private at every history, including constant unused releases](goal). -/
-- @node: tvFrontierProtocol_noninteractive
lemma tvFrontierProtocol_noninteractive (n d : ℕ) (eps : ℝ) (heps : 0 ≤ eps) :
    NoninteractiveClass (tvFrontierProtocol n d eps) eps := by
  constructor
  · intro i v v' eta r E hE
    exact tvFrontierKernel_privacy n d eps heps i v v' E hE
  · intro i v eta eta' r
    rfl

/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the protocol transcript](hyp:z). [Embed paired vector messages in the common private polynomial computation](goal). -/
def tvToNormTranscript (n d : ℕ) (eps : ℝ)
    (z : ProtocolTranscript (tvFrontierProtocol n d eps)) :
    ProtocolTranscript (frontierProtocol n d eps) :=
  fun i =>
    let m0 := (frontierDesign n d eps).resources.m0
    if i.val < m0 then (false,fun _ => false)
    else if h : i.val - m0 < n then (false,z ⟨i.val-m0,h⟩)
    else (false,fun _ => false)
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the protocol decision](hyp:w). [Explicit projected TV polynomial decision, using no baseline block](goal). -/
def tvFrontierEstimate (n d : ℕ) (eps : ℝ)
    (w : DecisionSpace (tvFrontierProtocol n d eps)) : ℝ :=
  if n = 2 then 1/8 else
    max 0 (min (1/4) (frontierNormEstimate n d eps (tvToNormTranscript n d eps w.1)/2))
/-- [Borel measurability of the concrete paired polynomial decision](goal). -/
-- @node: tvFrontierEstimate_measurable
lemma tvFrontierEstimate_measurable (n d : ℕ) (eps : ℝ) :
    Measurable (tvFrontierEstimate n d eps) := by
  classical
  letI : Countable (ProtocolTranscript (tvFrontierProtocol n d eps)) := by
    change Countable (Fin n → Fin d → Bool)
    infer_instance
  letI : MeasurableSingletonClass (ProtocolTranscript (tvFrontierProtocol n d eps)) := by
    change MeasurableSingletonClass (Fin n → Fin d → Bool)
    infer_instance
  let f : ProtocolTranscript (tvFrontierProtocol n d eps) → ℝ :=
    fun z => tvFrontierEstimate n d eps (z, (0 : Fin 1), 0)
  have hf : Measurable f := measurable_of_countable f
  exact hf.comp measurable_fst
/-- Fix [the sample size and the dimension](hyp:n,d) and [the privacy budget](hyp:eps). [The measurable transcript-only paired estimator](goal). -/
def tvFrontierEstimator (n d : ℕ) (eps : ℝ) : Estimator (tvFrontierProtocol n d eps) :=
  ⟨tvFrontierEstimate n d eps, tvFrontierEstimate_measurable n d eps⟩
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget and the constant C0](hyp:eps,C0), and [the protocol decision](hyp:w). [Lower endpoint in the sharper paired interval range](goal). -/
def tvFrontierLo (n d : ℕ) (eps C0 : ℝ)
    (w : DecisionSpace (tvFrontierProtocol n d eps)) : ℝ :=
  max 0 (tvFrontierEstimate n d eps w - Real.sqrt (10*C0*rateR .NI n d eps))
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget and the constant C0](hyp:eps,C0), and [the protocol decision](hyp:w). [Upper endpoint in the sharper paired interval range](goal). -/
def tvFrontierHi (n d : ℕ) (eps C0 : ℝ)
    (w : DecisionSpace (tvFrontierProtocol n d eps)) : ℝ :=
  min (1/4) (tvFrontierEstimate n d eps w + Real.sqrt (10*C0*rateR .NI n d eps))
/-- [Regularity, order and range certificate for the concrete paired interval](goal). -/
-- @node: tvFrontier_interval_certificate
lemma tvFrontier_interval_certificate (n d : ℕ) (eps C0 : ℝ) :
    Measurable (tvFrontierLo n d eps C0) ∧ Measurable (tvFrontierHi n d eps C0) ∧
    (∀ w, tvFrontierLo n d eps C0 w ≤ tvFrontierHi n d eps C0 w) ∧
    (∀ w, tvFrontierLo n d eps C0 w ∈ Set.Icc (0 : ℝ) (1/4)) ∧
    (∀ w, tvFrontierHi n d eps C0 w ∈ Set.Icc (0 : ℝ) (1/4)) := by
  have hm := tvFrontierEstimate_measurable n d eps
  have hrad : 0 ≤ Real.sqrt (10*C0*rateR .NI n d eps) := by positivity
  have hrange : ∀ w, tvFrontierEstimate n d eps w ∈ Set.Icc (0 : ℝ) (1/4 : ℝ) := by
    intro w
    dsimp [tvFrontierEstimate]
    split_ifs
    · norm_num
    · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change Measurable (fun w =>
      max 0 (tvFrontierEstimate n d eps w - Real.sqrt (10*C0*rateR .NI n d eps)))
    fun_prop
  · change Measurable (fun w =>
      min (1/4) (tvFrontierEstimate n d eps w + Real.sqrt (10*C0*rateR .NI n d eps)))
    fun_prop
  · intro w
    have hw := hrange w
    dsimp [tvFrontierLo, tvFrontierHi]
    apply max_le
    · apply le_min
      · norm_num
      · linarith [hw.1]
    · apply le_min
      · linarith [hw.2]
      · linarith
  · intro w
    have hw := hrange w
    change (0 : ℝ) ≤
      max (0 : ℝ) (tvFrontierEstimate n d eps w - Real.sqrt (10*C0*rateR .NI n d eps)) ∧ _
    exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith [hw.2])⟩
  · intro w
    have hw := hrange w
    change (0 : ℝ) ≤
      min (1/4 : ℝ) (tvFrontierEstimate n d eps w + Real.sqrt (10*C0*rateR .NI n d eps)) ∧ _
    exact ⟨le_min (by norm_num) (by linarith [hw.1]), min_le_left _ _⟩
/-- Fix [the sample size and the dimension](hyp:n,d) and [the privacy budget and the constant C0](hyp:eps,C0). [Actual paired globally honest closed connected interval](goal). -/
def tvFrontierInterval (n d : ℕ) (eps C0 : ℝ) :
    IntervalDecision (tvFrontierProtocol n d eps) 0 (1/4) :=
  { lo := tvFrontierLo n d eps C0, hi := tvFrontierHi n d eps C0,
    measurable_lo := (tvFrontier_interval_certificate n d eps C0).1,
    measurable_hi := (tvFrontier_interval_certificate n d eps C0).2.1,
    ordered := (tvFrontier_interval_certificate n d eps C0).2.2.1,
    range_lo := (tvFrontier_interval_certificate n d eps C0).2.2.2.1,
    range_hi := (tvFrontier_interval_certificate n d eps C0).2.2.2.2 }
/-- Fix [the sample size and the dimension](hyp:n,d) and [the privacy budget and the constant C0](hyp:eps,C0). [Concrete attainment by the resource-selected sign-vector polynomial decisions](goal). -/
def ConcreteTvAttainment (n d : ℕ) (eps C0 : ℝ) : Prop :=
  NoninteractiveClass (tvFrontierProtocol n d eps) eps ∧
    ∀ p ∈ pairedFamily d,
      squaredRisk (canonicalDecisionLaw (tvFrontierProtocol n d eps) p)
        (tvFrontierEstimator n d eps) (tvFromUniform p) ≤ ENNReal.ofReal (C0*rateR .NI n d eps) ∧
      (0.90 : ℝ) ≤ coverage (canonicalDecisionLaw (tvFrontierProtocol n d eps) p)
        (tvFrontierInterval n d eps C0) (tvFromUniform p) ∧
      expectedLength (canonicalDecisionLaw (tvFrontierProtocol n d eps) p)
        (tvFrontierInterval n d eps C0) ≤ ENNReal.ofReal (C0*rateH .NI n d eps)


/-- Assume [the stated hv condition](hyp:hv). [The two-participant fallback has squared error at most one sixty-fourth throughout the paired target range](goal). -/
-- @node: tvFrontierEstimator_two_risk
lemma tvFrontierEstimator_two_risk (d : ℕ) (eps : ℝ)
    (L : Measure (DecisionSpace (tvFrontierProtocol 2 d eps))) [IsProbabilityMeasure L]
    (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) (1/4)) :
    squaredRisk L (tvFrontierEstimator 2 d eps) v ≤ ENNReal.ofReal (1/64 : ℝ) := by
  have hpoint : ∀ w : DecisionSpace (tvFrontierProtocol 2 d eps),
      ((tvFrontierEstimator 2 d eps).1 w - v)^2 ≤ (1/64 : ℝ) := by
    intro w
    change (tvFrontierEstimate 2 d eps w - v)^2 ≤ _
    simp only [tvFrontierEstimate, ↓reduceIte]
    nlinarith [hv.1, hv.2, mul_nonneg hv.1 (sub_nonneg.mpr hv.2)]
  unfold squaredRisk
  calc
    _ ≤ ∫⁻ _w, ENNReal.ofReal (1/64 : ℝ) ∂L :=
      lintegral_mono (fun w => ENNReal.ofReal_le_ofReal (hpoint w))
    _ = _ := by simp

/-- [Clipping the paired interval to its target range can only shorten it](goal). -/
-- @node: tvFrontierInterval_length_le
lemma tvFrontierInterval_length_le (n d : ℕ) (eps C0 : ℝ)
    (w : DecisionSpace (tvFrontierProtocol n d eps)) :
    Causalean.Stat.intervalLength ((tvFrontierInterval n d eps C0).lo w)
      ((tvFrontierInterval n d eps C0).hi w) ≤
      2 * Real.sqrt (10*C0*rateR .NI n d eps) := by
  have hr := Real.sqrt_nonneg (10*C0*rateR .NI n d eps)
  change max 0 (min (1/4) (tvFrontierEstimate n d eps w +
    Real.sqrt (10*C0*rateR .NI n d eps)) - max 0 (tvFrontierEstimate n d eps w -
    Real.sqrt (10*C0*rateR .NI n d eps))) ≤ _
  apply max_le
  · positivity
  · have hu := min_le_right (1/4 : ℝ) (tvFrontierEstimate n d eps w +
      Real.sqrt (10*C0*rateR .NI n d eps))
    have hl := le_max_right (0 : ℝ) (tvFrontierEstimate n d eps w -
      Real.sqrt (10*C0*rateR .NI n d eps))
    linarith

/-- Assume [the stated c0 condition](hyp:hC0). [Integrating the deterministic paired length bound yields the square-root rate](goal). -/
-- @node: tvFrontierInterval_expectedLength_le
lemma tvFrontierInterval_expectedLength_le (n d : ℕ) (eps C0 : ℝ) (hC0 : 0 ≤ C0)
    (L : Measure (DecisionSpace (tvFrontierProtocol n d eps))) [IsProbabilityMeasure L] :
    expectedLength L (tvFrontierInterval n d eps C0) ≤
      ENNReal.ofReal (Real.sqrt (40*C0) * rateH .NI n d eps) := by
  have hs : 2 * Real.sqrt (10*C0) = Real.sqrt (40*C0) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.sqrt_mul (by norm_num)]
    congr 1
    ring
  have heq : 2 * Real.sqrt (10*C0*rateR .NI n d eps) =
      Real.sqrt (40*C0) * rateH .NI n d eps := by
    rw [Real.sqrt_mul (by positivity), ← mul_assoc, hs]
    rfl
  unfold expectedLength
  calc
    _ ≤ ∫⁻ _w, ENNReal.ofReal (2 * Real.sqrt (10*C0*rateR .NI n d eps)) ∂L :=
      lintegral_mono (fun w => ENNReal.ofReal_le_ofReal
        (tvFrontierInterval_length_le n d eps C0 w))
    _ = _ := by simp [heq]

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated c0 condition](hyp:hC0), [the stated hv condition](hyp:hv), and [the estimator hRisk](hyp:hRisk). [Markov's inequality converts the finite MSE bound into ninety-percent coverage](goal). -/
-- @node: tvFrontierInterval_coverage_of_risk
lemma tvFrontierInterval_coverage_of_risk (n d : ℕ) (eps : ℝ) (hAllowed : Allowed n d eps)
    (C0 : ℝ) (hC0 : 0 < C0)
    (L : Measure (DecisionSpace (tvFrontierProtocol n d eps))) [IsProbabilityMeasure L]
    (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) (1/4))
    (hRisk : squaredRisk L (tvFrontierEstimator n d eps) v ≤
      ENNReal.ofReal (C0 * rateR .NI n d eps)) :
    (0.90 : ℝ) ≤ coverage L (tvFrontierInterval n d eps C0) v := by
  let q := Real.sqrt (10*C0*rateR .NI n d eps)
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
  have ht : 0 < (n : ℝ) * eps^2 := mul_pos hn (sq_pos_of_pos hAllowed.2.2.1)
  have hrho : 0 < rho (n*eps^2) d :=
    (lt_min (by norm_num) (one_div_pos.mpr ht)).trans_le
      (rho_elementary_comparisons n d eps hAllowed).1
  have hq : 0 < q := Real.sqrt_pos.mpr (by dsimp [rateR]; positivity)
  have hq2 : q^2 = (10*C0) * rho (n*eps^2) d :=
    Real.sq_sqrt (by positivity)
  let f := fun w : DecisionSpace (tvFrontierProtocol n d eps) =>
    ENNReal.ofReal ((tvFrontierEstimate n d eps w - v)^2)
  have hf : Measurable f := by
    dsimp [f]
    have hm := tvFrontierEstimate_measurable n d eps
    fun_prop
  have hm := mul_meas_ge_le_lintegral (μ := L) hf (ENNReal.ofReal (q^2))
  have hm' : ENNReal.ofReal (q^2) * L {w | ENNReal.ofReal (q^2) ≤ f w} ≤
      ENNReal.ofReal (C0 * rateR .NI n d eps) := hm.trans hRisk
  have hmR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm'
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg q),
    ENNReal.toReal_ofReal (by dsimp [rateR]; positivity)] at hmR
  change q^2 * L.real {w | ENNReal.ofReal (q^2) ≤ f w} ≤ _ at hmR
  let E := Causalean.Stat.coverageEvent (tvFrontierInterval n d eps C0).lo
    (tvFrontierInterval n d eps C0).hi v
  have hE : MeasurableSet E := Causalean.Stat.measurableSet_coverageEvent
    (tvFrontierInterval n d eps C0).measurable_lo (tvFrontierInterval n d eps C0).measurable_hi
  have hsub : Eᶜ ⊆ {w | ENNReal.ofReal (q^2) ≤ f w} := by
    intro w hw
    have herr : q < |tvFrontierEstimate n d eps w - v| := by
      by_contra hh
      have ha := abs_le.mp (le_of_not_gt hh)
      apply hw
      change max 0 (tvFrontierEstimate n d eps w - q) ≤ v ∧
        v ≤ min (1/4) (tvFrontierEstimate n d eps w + q)
      exact ⟨max_le hv.1 (by linarith [ha.2]), le_min hv.2 (by linarith [ha.1])⟩
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_abs (tvFrontierEstimate n d eps w - v)]
  have hmono := measureReal_mono (μ := L) hsub
  have hbad : L.real Eᶜ ≤ (1/10 : ℝ) := by
    have hmR' : q^2 * L.real {w | ENNReal.ofReal (q^2) ≤ f w} ≤ q^2/10 := by
      dsimp [rateR] at hmR
      calc
        _ ≤ C0 * rho (n*eps^2) d := hmR
        _ = q^2/10 := by rw [hq2]; ring
    have hpos : 0 < q^2 := sq_pos_of_pos hq
    nlinarith
  rw [measureReal_compl hE, probReal_univ] at hbad
  change (0.90 : ℝ) ≤ L.real E
  linarith


end CausalSmith.Stat.LdpOptvalueUniformFrontier

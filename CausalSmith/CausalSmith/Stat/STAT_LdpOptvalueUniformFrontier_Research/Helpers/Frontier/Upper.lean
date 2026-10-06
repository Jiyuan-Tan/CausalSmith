module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Calibration.Hybrid
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Decision
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.DecisionSampling
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.RateAlgebra

/-!
# Helpers/Frontier/Upper

Finite original-record private value frontiers: Helpers/Frontier/Upper.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


variable {n d : ℕ} {eps : ℝ}
/-- [Explicit fallback and polynomial branches of the attaining construction](goal). -/
inductive FrontierBranch where
  | constant | absMean | hybrid | fallbackQuarter | globalPoly
  deriving DecidableEq
/-- [Equality of the explicit frontier-construction branches is decidable](goal). -/
add_decl_doc instDecidableEqFrontierBranch
/-- [Resource-selected design including converse amplitude and matching degree](goal). -/
structure FrontierDesign where
  m : ℕ
  m0 : ℕ
  branch : FrontierBranch
  degree : ℕ
  threshold : ℝ
  radius : ℝ
  converseAmp : ℝ
  converseDegree : ℕ

/-- Fix [the sample size and the dimension](hyp:n,d) and [the privacy budget](hyp:eps). [Fixed public-resource choices: the first applicable branch is used, with the constants and rounding rules of the frozen construction. In the n=2 branch the block and polynomial entries are unused by the constant estimator](goal). -/
def frontierResources (n d : ℕ) (eps : ℝ) : FrontierDesign :=
  let m := n/3
  let m0 := n - 2*m
  let L := logDim d
  let t := n*eps^2
  let sigma2 := sigmaSquared d m eps
  let H := Real.log (Real.exp 1 + sigma2*L)
  let z := (d : ℝ)^2 * L / t
  let w := Real.log (Real.exp 1 + z)
  let dense := (d : ℝ)^2 * L ≤ t
  { m := m, m0 := m0,
    branch := if n = 2 then .constant else
      if L < 4096 then .absMean else if dense then .hybrid else
      if L/(1024*H) < 4 then .fallbackQuarter else .globalPoly,
    degree := if dense then 2*⌊L/2048⌋₊ else 2*⌊L/(2048*H)⌋₊,
    threshold := 4*Real.sqrt sigma2*Real.sqrt L,
    radius := if dense then 8*Real.sqrt sigma2*Real.sqrt L else 1/2,
    converseAmp := if z ≤ 1 then (1/100 : ℝ)*Real.sqrt z else 1/100,
    converseDegree := if z ≤ 1 then 2*⌈16*L⌉₊+1 else 2*⌈16*L/w⌉₊+1 }
/-- Fix [the dimension](hyp:d). [Combined binary/vector message alphabet](goal). -/
abbrev FrontierMessage (d : ℕ) := Bool × (Fin d → Bool)
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), [the participant index](hyp:i), [the observed participant record](hyp:o), and [the parameter z](hyp:z). [Original-input participant-specific finite atom channel](goal). -/
def frontierMass (n d : ℕ) (eps : ℝ) (i : Fin n) (o : ObsRecord d)
    (z : FrontierMessage d) : ℝ :=
  if n = 2 then
    if z = (false,fun _ => false) then 1 else 0
  else if i.val < (frontierResources n d eps).m0 then
    (1+privacyDelta eps*signVal o.2.2*signVal z.1)/2 *
      (if z.2 = (fun _ => false) then 1 else 0)
  else vectorMass eps o z.2 * (if z.1 = false then 1 else 0)
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the participant index](hyp:i). [Finite participant channel ignoring histories](goal). -/
def frontierKernel (n d : ℕ) (eps : ℝ) (i : Fin n) :
    Kernel (ObsRecord d) (FrontierMessage d) :=
  ⟨fun o => atomLaw (frontierMass n d eps i o), measurable_of_countable _⟩
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the participant index](hyp:i). [Participant stage with ignored histories](goal). -/
def frontierStageKernel (n d : ℕ) (eps : ℝ) (i : Fin n) :
    Kernel ((ObsRecord d × Fin 1) ×
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.History
        (fun _ : Fin n => FrontierMessage d) i.val (Nat.le_of_lt i.isLt)) (FrontierMessage d) :=
  (frontierKernel n d eps i).comap (fun w => w.1.1) (measurable_fst.comp measurable_fst)
/-- [Binary randomized-response masses are nonnegative](goal). -/
-- @node: binaryOutcomeMass_nonneg
lemma binaryOutcomeMass_nonneg (eps : ℝ) (y z : Bool) :
    0 ≤ (1 + privacyDelta eps * signVal y * signVal z)/2 := by
  have hlo := (abs_lt.mp (Real.abs_tanh_lt_one (eps/2))).1
  have hhi := (abs_lt.mp (Real.abs_tanh_lt_one (eps/2))).2
  unfold privacyDelta signVal
  cases y <;> cases z <;> norm_num <;> linarith

/-- [The two binary response probabilities sum to one](goal). -/
-- @node: binaryOutcomeMass_sum
lemma binaryOutcomeMass_sum (eps : ℝ) (y : Bool) :
    ∑ z : Bool, (1 + privacyDelta eps * signVal y * signVal z)/2 = 1 := by
  simp only [Fintype.sum_bool, signVal, Bool.false_eq_true, ↓reduceIte]
  ring

/-- [The binary outcome channel is a probability kernel](goal). -/
-- @node: binaryOutcomeKernel_markov
lemma binaryOutcomeKernel_markov (d : ℕ) (eps : ℝ) :
    IsMarkovKernel (binaryOutcomeKernel d eps) := by
  constructor
  intro o
  constructor
  change atomLaw _ Set.univ = 1
  simp only [atomLaw, Measure.finsetSum_apply, MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply_of_mem, Set.mem_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => binaryOutcomeMass_nonneg eps o.2.2 z),
    binaryOutcomeMass_sum]
  simp


/-- [Stage Markov certificate](goal). -/
-- @node: frontierStage_markov
lemma frontierStage_markov (n d : ℕ) (eps : ℝ) (i : Fin n) :
    IsMarkovKernel (frontierStageKernel n d eps i) := by
  classical
  have hm : ∀ o z, 0 ≤ frontierMass n d eps i o z := by
    intro o z
    unfold frontierMass
    split
    · split <;> positivity
    · split
      · exact mul_nonneg (binaryOutcomeMass_nonneg eps o.2.2 z.1) (by split <;> positivity)
      · exact mul_nonneg (vectorMass_nonneg eps o z.2) (by split <;> positivity)
  have hs : ∀ o, ∑ z, frontierMass n d eps i o z = 1 := by
    intro o
    unfold frontierMass
    by_cases hn : n = 2
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      by_cases hi : i.val < (frontierResources n d eps).m0
      · simp only [hi, ↓reduceIte]
        rw [Fintype.sum_prod_type]
        simp only [← Finset.mul_sum]
        simpa [Fintype.sum_bool] using binaryOutcomeMass_sum eps o.2.2
      · simp only [hi, ↓reduceIte]
        rw [Fintype.sum_prod_type]
        simp [vectorMass_sum]
  have hk : IsMarkovKernel (frontierKernel n d eps i) := by
    constructor
    intro o
    constructor
    change atomLaw _ Set.univ = 1
    simp only [atomLaw, Measure.finsetSum_apply, MeasurableSet.univ,
      Measure.smul_apply, Measure.dirac_apply_of_mem, Set.mem_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hm o z), hs]
    simp
  letI := hk
  unfold frontierStageKernel
  infer_instance
/-- Fix [the sample size and the dimension](hyp:n,d) and [the privacy budget](hyp:eps). [Explicit noninteractive original-record attaining protocol](goal). -/
def frontierProtocol (n d : ℕ) (eps : ℝ) : LocalProtocol n (ObsRecord d) where
  Seed := Fin 1
  seedMeasurable := inferInstance
  seedStandard := inferInstance
  seedLaw := Measure.dirac 0
  seedProbability := inferInstance
  Message := fun _ => FrontierMessage d
  messageMeasurable := fun _ => inferInstance
  messageStandard := fun _ => inferInstance
  kernels := frontierStageKernel n d eps
  markov := frontierStage_markov n d eps
/-- Fix [the protocol transcript](hyp:z) and [the participant index](hyp:i). [Safe extraction from a finite transcript, returning a fixed unused message past the horizon](goal). -/
def messageAt (z : ProtocolTranscript (frontierProtocol n d eps)) (i : ℕ) : FrontierMessage d :=
  if hi : i < n then z ⟨i,hi⟩ else (false,fun _ => false)
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), [the natural-number parameter offset](hyp:offset), and [the protocol transcript](hyp:z). [Scaled vector block extracted from a transcript](goal). -/
def frontierBlock (n d : ℕ) (eps : ℝ) (offset : ℕ)
    (z : ProtocolTranscript (frontierProtocol n d eps)) : Fin (n/3) → Fin d → Bool :=
  fun i => (messageAt z (offset+i.val)).2
/-- Fix [the privacy budget and the amplitude](hyp:eps,a), [the natural-number parameter D](hyp:D), [the coordinate index](hyp:j), and [the function z](hyp:z). [Finite polynomial computation using the prescribed elementary-symmetric recursion](goal). -/
def frontierPolynomialEstimate {m : ℕ} (eps a : ℝ) (D : ℕ) (j : Fin d)
    (z : Fin m → Fin d → Bool) : ℝ :=
  ∑ v ∈ Finset.range (D+1), (chebyshevAbsPoly D).coeff v *
    a^((1 : ℤ) - (v : ℤ)) * ((Nat.choose m v : ℝ)⁻¹ *
      elementaryMoment (fun i => if hi : i < m then scaledMessages eps z ⟨i,hi⟩ j else 0) m v)
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the protocol transcript](hyp:z). [Raw norm estimate from the chosen pilot/evaluation branch](goal). -/
def frontierNormEstimate (n d : ℕ) (eps : ℝ)
    (z : ProtocolTranscript (frontierProtocol n d eps)) : ℝ :=
  let design := frontierResources n d eps
  let pilot := frontierBlock n d eps design.m0 z
  let eval := frontierBlock n d eps (design.m0+design.m) z
  match design.branch with
  | .constant => 0
  | .fallbackQuarter => 1/4
  | .absMean => (d : ℝ)⁻¹ * ∑ j, |scaledColumnMean eps j eval|
  | .globalPoly => (d : ℝ)⁻¹ * ∑ j,
      frontierPolynomialEstimate eps design.radius design.degree j eval
  | .hybrid => (d : ℝ)⁻¹ * ∑ j,
      let M := scaledColumnMean eps j pilot
      if |M| ≤ design.threshold then
        frontierPolynomialEstimate eps design.radius design.degree j eval
      else (if 0 < M then 1 else if M < 0 then -1 else 0) * scaledColumnMean eps j eval
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the protocol transcript](hyp:z). [Fresh-person randomized-response estimate of the baseline](goal). -/
def frontierBaselineEstimate (n d : ℕ) (eps : ℝ)
    (z : ProtocolTranscript (frontierProtocol n d eps)) : ℝ :=
  let m0 := (frontierResources n d eps).m0
  1/2 + ((m0 : ℝ)⁻¹ * ∑ i ∈ Finset.range m0, signVal (messageAt z i).1)/(2*privacyDelta eps)
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the protocol decision](hyp:w). [Projected causal estimator using only private messages](goal). -/
def frontierEstimate (n d : ℕ) (eps : ℝ)
    (w : DecisionSpace (frontierProtocol n d eps)) : ℝ :=
  if n = 2 then 1/2 else
    max (1/4) (min (3/4) (frontierBaselineEstimate n d eps w.1 + frontierNormEstimate n d eps
      w.1/2))
/-- [Measurability of the concrete finite transcript estimate](goal). -/
-- @node: frontierEstimate_measurable
lemma frontierEstimate_measurable (n d : ℕ) (eps : ℝ) :
    Measurable (frontierEstimate n d eps) := by
  classical
  letI : Countable (ProtocolTranscript (frontierProtocol n d eps)) := by
    change Countable (Fin n → FrontierMessage d)
    infer_instance
  letI : MeasurableSingletonClass (ProtocolTranscript (frontierProtocol n d eps)) := by
    change MeasurableSingletonClass (Fin n → FrontierMessage d)
    infer_instance
  let f : ProtocolTranscript (frontierProtocol n d eps) → ℝ :=
    fun z => frontierEstimate n d eps (z, (0 : Fin 1), 0)
  have hf : Measurable f := measurable_of_countable f
  exact hf.comp measurable_fst
/-- Fix [the sample size and the dimension](hyp:n,d) and [the privacy budget](hyp:eps). [Attaining Borel estimator packaged without any unproved definitional payload](goal). -/
def frontierEstimator (n d : ℕ) (eps : ℝ) : Estimator (frontierProtocol n d eps) :=
  ⟨frontierEstimate n d eps, frontierEstimate_measurable n d eps⟩
/-- Fix [the sample size and the dimension](hyp:n,d) and [the privacy budget](hyp:eps). [The fixed honesty radius prescribed for every branch, including n=2](goal). -/
def frontierHonestyRadius (n d : ℕ) (eps : ℝ) : ℝ :=
  Real.sqrt ((10 : ℝ)^17 * rho (n * eps^2) d)
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the protocol decision](hyp:w). [Lower endpoint with the prescribed fixed honesty radius](goal). -/
def frontierLo (n d : ℕ) (eps : ℝ) (w : DecisionSpace (frontierProtocol n d eps)) : ℝ :=
  max (1/4) (frontierEstimate n d eps w - frontierHonestyRadius n d eps)
/-- Fix [the sample size and the dimension](hyp:n,d), [the privacy budget](hyp:eps), and [the protocol decision](hyp:w). [Upper endpoint of the concrete connected interval](goal). -/
def frontierHi (n d : ℕ) (eps : ℝ) (w : DecisionSpace (frontierProtocol n d eps)) : ℝ :=
  min (3/4) (frontierEstimate n d eps w + frontierHonestyRadius n d eps)
/-- [Endpoint regularity and range certificate for the actual interval](goal). -/
-- @node: frontier_interval_certificate
lemma frontier_interval_certificate (n d : ℕ) (eps : ℝ) :
    Measurable (frontierLo n d eps) ∧ Measurable (frontierHi n d eps) ∧
    (∀ w, frontierLo n d eps w ≤ frontierHi n d eps w) ∧
    (∀ w, frontierLo n d eps w ∈ Set.Icc (1/4 : ℝ) (3/4)) ∧
    (∀ w, frontierHi n d eps w ∈ Set.Icc (1/4 : ℝ) (3/4)) := by
  have hm := frontierEstimate_measurable n d eps
  have hrad : 0 ≤ frontierHonestyRadius n d eps := Real.sqrt_nonneg _
  have hrange : ∀ w, frontierEstimate n d eps w ∈ Set.Icc (1/4 : ℝ) (3/4 : ℝ) := by
    intro w
    dsimp [frontierEstimate]
    split_ifs
    · norm_num
    · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change Measurable (fun w =>
      max (1/4) (frontierEstimate n d eps w - frontierHonestyRadius n d eps))
    fun_prop
  · change Measurable (fun w =>
      min (3/4) (frontierEstimate n d eps w + frontierHonestyRadius n d eps))
    fun_prop
  · intro w
    have hw := hrange w
    dsimp [frontierLo, frontierHi]
    apply max_le
    · apply le_min
      · norm_num
      · linarith [hw.1]
    · apply le_min
      · linarith [hw.2]
      · linarith
  · intro w
    have hw := hrange w
    change (1/4 : ℝ) ≤
      max (1/4 : ℝ) (frontierEstimate n d eps w - frontierHonestyRadius n d eps) ∧ _
    exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith [hw.2])⟩
  · intro w
    have hw := hrange w
    change (1/4 : ℝ) ≤
      min (3/4 : ℝ) (frontierEstimate n d eps w + frontierHonestyRadius n d eps) ∧ _
    exact ⟨le_min (by norm_num) (by linarith [hw.1]), min_le_left _ _⟩
/-- Fix [the sample size and the dimension](hyp:n,d) and [the privacy budget](hyp:eps). [The resource-selected closed connected interval](goal). -/
def frontierInterval (n d : ℕ) (eps : ℝ) : IntervalDecision (frontierProtocol n d eps) (1/4)
  (3/4) :=
  { lo := frontierLo n d eps, hi := frontierHi n d eps,
    measurable_lo := (frontier_interval_certificate n d eps).1,
    measurable_hi := (frontier_interval_certificate n d eps).2.1,
    ordered := (frontier_interval_certificate n d eps).2.2.1,
    range_lo := (frontier_interval_certificate n d eps).2.2.2.1,
    range_hi := (frontier_interval_certificate n d eps).2.2.2.2 }

/-- Fix [the sample size and the dimension](hyp:n,d). [Data of the fixed constructive and converse handle. Kernel normalization, Borel decisions and interval range are typing obligations; privacy, moment identities, risk and global honesty are proved later rather than defining membership. The prior maps are applied to the symmetric moment-duality measures at degree k-1](goal). -/
structure FrontierConstruction (n d : ℕ) where
  resources : FrontierDesign
  protocol : LocalProtocol n (ObsRecord d)
  estimator : Estimator protocol
  interval : IntervalDecision protocol (1/4) (3/4)
  scaledPrior : Measure ℝ → Measure ℝ
  productPrior : Measure ℝ → Measure (Fin d → ℝ)
  causalLaw : (Fin d → ℝ) → Measure (FullRecord d)

-- @node: def:frontier-handle
/-- Fix [the sample size and the dimension](hyp:n,d) and [the privacy budget](hyp:eps). [The fixed original-input construction for the public tuple (n,d,ε): singleton seed, binary baseline and two disjoint sign-vector blocks, transcript-only clipped estimate, fixed-radius connected interval, and scaled coordinate product priors. Selection is deterministic in public resources, by the ordered branches of frontierResources; there is no optimization over designs. Admissibility, calibration, risk and coverage are subsequent construction obligations, not assumed performance fields of this mathematical object](goal). -/
def frontierDesign (n d : ℕ) (eps : ℝ) : FrontierConstruction n d :=
  let resources := frontierResources n d eps
  let scaled := fun xi : Measure ℝ => xi.map (fun u => resources.converseAmp * u)
  { resources := resources,
    protocol := frontierProtocol n d eps,
    estimator := frontierEstimator n d eps,
    interval := frontierInterval n d eps,
    scaledPrior := scaled,
    productPrior := fun xi => Measure.pi (fun _ : Fin d => scaled xi),
    causalLaw := symmetricLaw }
  -- @realizes \mathscr H(fixed protocol, decisions, resource choices and converse prior maps)
/-- Assume [a nonnegative privacy budget](hyp:heps). [The binary outcome response obeys the same extreme-sign ratio as the vector release](goal). -/
-- @node: binaryOutcomeMass_privacy
lemma binaryOutcomeMass_privacy (eps : ℝ) (heps : 0 ≤ eps) (y y' z : Bool) :
    (1 + privacyDelta eps * signVal y * signVal z)/2 ≤
      Real.exp eps * ((1 + privacyDelta eps * signVal y' * signVal z)/2) := by
  have hd := (privacyDelta_bounds eps heps).1
  have hs : ∀ b : Bool, -privacyDelta eps ≤ privacyDelta eps * signVal b * signVal z ∧
      privacyDelta eps * signVal b * signVal z ≤ privacyDelta eps := by
    intro b
    cases b <;> cases z <;> norm_num [signVal] <;> linarith
  have hh : 1 + privacyDelta eps * signVal y * signVal z ≤
      Real.exp eps * (1 + privacyDelta eps * signVal y' * signVal z) := by
    calc
      _ ≤ 1 + privacyDelta eps := by linarith [(hs y).2]
      _ = Real.exp eps * (1 - privacyDelta eps) := privacyDelta_odds_identity eps
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [(hs y').1]) (Real.exp_pos eps).le
  linarith

/-- Assume [a nonnegative privacy budget](hyp:heps). [Each branch of the combined finite message channel satisfies the atomwise privacy bound](goal). -/
-- @node: frontierMass_privacy
lemma frontierMass_privacy (n d : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (i : Fin n) (o o' : ObsRecord d) (z : FrontierMessage d) :
    frontierMass n d eps i o z ≤ Real.exp eps * frontierMass n d eps i o' z := by
  have he : 1 ≤ Real.exp eps := Real.one_le_exp_iff.mpr heps
  unfold frontierMass
  by_cases hn : n = 2
  · simp only [hn, ↓reduceIte]
    split_ifs <;> simpa using he
  · simp only [hn, ↓reduceIte]
    by_cases hi : i.val < (frontierResources n d eps).m0
    · simp only [hi, ↓reduceIte]
      split_ifs
      · simpa using binaryOutcomeMass_privacy eps heps o.2.2 o'.2.2 z.1
      · simp
    · simp only [hi, ↓reduceIte]
      split_ifs
      · simpa using vectorMass_privacy eps heps o o' z.2
      · simp

/-- Assume [a nonnegative privacy budget](hyp:heps). [Summing the finite atom inequalities proves privacy for every message event](goal). -/
-- @node: frontierKernel_privacy
lemma frontierKernel_privacy (n d : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (i : Fin n) (o o' : ObsRecord d) (E : Set (FrontierMessage d)) :
    frontierKernel n d eps i o E ≤
      ENNReal.ofReal (Real.exp eps) * frontierKernel n d eps i o' E := by
  classical
  change (atomLaw (frontierMass n d eps i o)) E ≤
    ENNReal.ofReal (Real.exp eps) * (atomLaw (frontierMass n d eps i o')) E
  simp only [atomLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos eps).le]
  simpa only [mul_comm] using
    mul_le_mul_right (ENNReal.ofReal_le_ofReal (frontierMass_privacy n d eps heps i o o' z))
      ((Measure.dirac z) E)

/-- Assume [a nonnegative privacy budget](hyp:heps). [The entire resource-selected original-input procedure is noninteractive and pure private](goal). -/
-- @node: frontierProtocol_noninteractive
lemma frontierProtocol_noninteractive (n d : ℕ) (eps : ℝ) (heps : 0 ≤ eps) :
    NoninteractiveClass (frontierProtocol n d eps) eps := by
  constructor
  · intro i o o' eta r E _
    exact frontierKernel_privacy n d eps heps i o o' E
  · intro i o eta eta' r
    rfl

/-- [Clipping the endpoints can only shorten the fixed-radius interval](goal). -/
-- @node: frontierInterval_length_le
lemma frontierInterval_length_le (n d : ℕ) (eps : ℝ)
    (w : DecisionSpace (frontierProtocol n d eps)) :
    Causalean.Stat.intervalLength ((frontierInterval n d eps).lo w)
      ((frontierInterval n d eps).hi w) ≤ 2 * frontierHonestyRadius n d eps := by
  have hr := Real.sqrt_nonneg ((10 : ℝ)^17 * rho (n * eps^2) d)
  change max 0 (min (3/4) (frontierEstimate n d eps w + frontierHonestyRadius n d eps) -
    max (1/4) (frontierEstimate n d eps w - frontierHonestyRadius n d eps)) ≤ _
  apply max_le
  · exact mul_nonneg (by norm_num) hr
  · have hu := min_le_right (3/4 : ℝ) (frontierEstimate n d eps w + frontierHonestyRadius n d eps)
    have hl := le_max_right (1/4 : ℝ) (frontierEstimate n d eps w - frontierHonestyRadius n d eps)
    linarith

/-- [Integrating the deterministic length bound requires only that the decision law be a probability](goal). -/
-- @node: frontierInterval_expectedLength_le
lemma frontierInterval_expectedLength_le (n d : ℕ) (eps : ℝ)
    (L : Measure (DecisionSpace (frontierProtocol n d eps))) [IsProbabilityMeasure L] :
    expectedLength L (frontierInterval n d eps) ≤
      ENNReal.ofReal (2 * frontierHonestyRadius n d eps) := by
  unfold expectedLength
  calc
    _ ≤ ∫⁻ _w, ENNReal.ofReal (2 * frontierHonestyRadius n d eps) ∂L :=
      lintegral_mono (fun w => ENNReal.ofReal_le_ofReal (frontierInterval_length_le n d eps w))
    _ = _ := by simp

/-- [The interval radius has exactly the prescribed square-root rate, for all resource tuples](goal). -/
-- @node: frontierInterval_rate_length
lemma frontierInterval_rate_length (n d : ℕ) (eps : ℝ)
    (L : Measure (DecisionSpace (frontierProtocol n d eps))) [IsProbabilityMeasure L] :
    expectedLength L (frontierInterval n d eps) ≤
      ENNReal.ofReal (Real.sqrt (40 * (10 : ℝ)^16) * rateH .NI n d eps) := by
  have hs : 2 * Real.sqrt ((10 : ℝ)^17) = Real.sqrt (40 * (10 : ℝ)^16) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_mul (by norm_num)]
    congr 1
    norm_num
  have heq : 2 * frontierHonestyRadius n d eps =
      Real.sqrt (40 * (10 : ℝ)^16) * rateH .NI n d eps := by
    dsimp [frontierHonestyRadius, rateH, rateR]
    rw [Real.sqrt_mul (by positivity), ← mul_assoc, hs]
  rw [← heq]
  exact frontierInterval_expectedLength_le n d eps L

/-- Assume [the causal-model conditions for the data law](hyp:hP) and [positive dimension](hyp:hd). [The causal target lies in the interval's fixed output domain](goal). -/
-- @node: causal_value_range
lemma causal_value_range (P : Measure (FullRecord d)) (hP : CausalModel P) (hd : 0 < d) :
    value P ∈ Set.Icc (1/4 : ℝ) (3/4) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcell : ∀ j : Fin d, max (armMean P false j) (armMean P true j) ∈
      Set.Icc (1/4 : ℝ) (3/4) := by
    intro j
    exact ⟨(hP.interior false j).1.trans (le_max_left _ _),
      max_le (hP.interior false j).2 (hP.interior true j).2⟩
  have hlo : ∑ _j : Fin d, (1/4 : ℝ) ≤ ∑ j, max (armMean P false j) (armMean P true j) :=
    Finset.sum_le_sum (fun j _ => (hcell j).1)
  have hhi : ∑ j : Fin d, max (armMean P false j) (armMean P true j) ≤ ∑ _j : Fin d, (3/4 : ℝ) :=
    Finset.sum_le_sum (fun j _ => (hcell j).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlo hhi
  change (1/4 : ℝ) ≤ (d : ℝ)⁻¹ * _ ∧ (d : ℝ)⁻¹ * _ ≤ (3/4 : ℝ)
  constructor
  · calc
      (1/4 : ℝ) = (d : ℝ)⁻¹ * ((d : ℝ) * (1/4)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (inv_nonneg.mpr hdR.le)
  · calc
      _ ≤ (d : ℝ)⁻¹ * ((d : ℝ) * (3/4)) := mul_le_mul_of_nonneg_left hhi (inv_nonneg.mpr hdR.le)
      _ = (3/4 : ℝ) := by field_simp

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hv condition](hyp:hv), and [the estimator hRisk](hyp:hRisk). [Markov's inequality converts the finite MSE bound into ninety-percent coverage](goal). -/
-- @node: frontierInterval_coverage_of_risk
lemma frontierInterval_coverage_of_risk (n d : ℕ) (eps : ℝ) (hAllowed : Allowed n d eps)
    (L : Measure (DecisionSpace (frontierProtocol n d eps))) [IsProbabilityMeasure L]
    (v : ℝ) (hv : v ∈ Set.Icc (1/4 : ℝ) (3/4))
    (hRisk : squaredRisk L (frontierEstimator n d eps) v ≤
      ENNReal.ofReal ((10 : ℝ)^16 * rateR .NI n d eps)) :
    (0.90 : ℝ) ≤ coverage L (frontierInterval n d eps) v := by
  let q := frontierHonestyRadius n d eps
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
  have ht : 0 < (n : ℝ) * eps^2 := mul_pos hn (sq_pos_of_pos hAllowed.2.2.1)
  have hrho : 0 < rho (n*eps^2) d :=
    (lt_min (by norm_num) (one_div_pos.mpr ht)).trans_le
      (rho_elementary_comparisons n d eps hAllowed).1
  have hq : 0 < q := Real.sqrt_pos.mpr (mul_pos (by positivity) hrho)
  have hq2 : q^2 = (10 : ℝ)^17 * rho (n*eps^2) d :=
    Real.sq_sqrt (mul_nonneg (by positivity) hrho.le)
  let f := fun w : DecisionSpace (frontierProtocol n d eps) =>
    ENNReal.ofReal ((frontierEstimate n d eps w - v)^2)
  have hf : Measurable f := by
    dsimp [f]
    have hm := frontierEstimate_measurable n d eps
    fun_prop
  have hm := mul_meas_ge_le_lintegral (μ := L) hf (ENNReal.ofReal (q^2))
  have hm' : ENNReal.ofReal (q^2) * L {w | ENNReal.ofReal (q^2) ≤ f w} ≤
      ENNReal.ofReal ((10 : ℝ)^16 * rateR .NI n d eps) := hm.trans hRisk
  have hmR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm'
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg q),
    ENNReal.toReal_ofReal (by dsimp [rateR]; positivity)] at hmR
  change q^2 * L.real {w | ENNReal.ofReal (q^2) ≤ f w} ≤ _ at hmR
  let E := Causalean.Stat.coverageEvent (frontierInterval n d eps).lo
    (frontierInterval n d eps).hi v
  have hE : MeasurableSet E := Causalean.Stat.measurableSet_coverageEvent
    (frontierInterval n d eps).measurable_lo (frontierInterval n d eps).measurable_hi
  have hsub : Eᶜ ⊆ {w | ENNReal.ofReal (q^2) ≤ f w} := by
    intro w hw
    have herr : q < |frontierEstimate n d eps w - v| := by
      by_contra hh
      have ha := abs_le.mp (le_of_not_gt hh)
      apply hw
      change max (1/4) (frontierEstimate n d eps w - q) ≤ v ∧
        v ≤ min (3/4) (frontierEstimate n d eps w + q)
      exact ⟨max_le hv.1 (by linarith [ha.2]), le_min hv.2 (by linarith [ha.1])⟩
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_abs (frontierEstimate n d eps w - v)]
  have hmono := measureReal_mono (μ := L) hsub
  have hbad : L.real Eᶜ ≤ (1/10 : ℝ) := by
    have hmR' : q^2 * L.real {w | ENNReal.ofReal (q^2) ≤ f w} ≤ q^2/10 := by
      dsimp [rateR] at hmR
      calc
        _ ≤ (10 : ℝ)^16 * rho (n*eps^2) d := hmR
        _ = q^2/10 := by rw [hq2]; ring
    have hpos : 0 < q^2 := sq_pos_of_pos hq
    nlinarith
  rw [measureReal_compl hE, probReal_univ] at hbad
  change (0.90 : ℝ) ≤ L.real E
  linarith



end CausalSmith.Stat.LdpOptvalueUniformFrontier

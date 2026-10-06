module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Procedures
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotBridge
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotSelectorBridge
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TFiveOutputUpperBound
public import Causalean.Stat.SampleSplit.FiniteCategoryPilot

/-! # Private pilot and affine main-sample estimator

Four-category randomized response estimates the input probabilities. A
measurable saddle selector chooses the main staircase channel and influence
values from that pilot, with the pilot discarded from the final average. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

-- @env: S5
variable (m : ℕ → ℕ)

/-- the [pilot output](goal) is the mathematical object specified below. -/
abbrev PilotOutput := Fin 4 ⊕ Fin 14

/-- the [pilot output family](goal) is the mathematical object specified below. -/
abbrev pilotOutputFamily : OutputFamily := fun _ _ => PilotOutput

/-- [The measurable-space instance for pilot outputs](goal) is determined by [the displayed parameters](hyp:n,i). -/
instance : ∀ n i, MeasurableSpace (pilotOutputFamily n i) :=
  fun _ _ => inferInstanceAs (MeasurableSpace PilotOutput)

-- @node: instMeasurableSingletonClassPilotOutput
/-- the [inst measurable singleton class pilot output](goal) is the mathematical object specified below. -/
instance instMeasurableSingletonClassPilotOutput : MeasurableSingletonClass PilotOutput := by
  refine ⟨fun x => ?_⟩
  cases x with
  | inl a => simpa only [Set.image_singleton] using (measurableSet_singleton a).inl_image
  | inr b => simpa only [Set.image_singleton] using (measurableSet_singleton b).inr_image

/-- [The measurable-singleton instance for pilot outputs](goal) is determined by [the displayed parameters](hyp:n,i). -/
instance : ∀ n i, MeasurableSingletonClass (pilotOutputFamily n i) :=
  fun _ _ => inferInstanceAs (MeasurableSingletonClass PilotOutput)

/-- [The countability instance for private pilot histories](goal) is determined by [the displayed parameters](hyp:n,i). -/
instance (n : ℕ) (i : Fin n) :
    Countable (PrivateHistory (Z := pilotOutputFamily n) i) := inferInstance

-- @node: instMeasurableSingletonClassPilotHistory
/-- For [the supplied quantities and conditions](hyp:n,i), the [inst measurable singleton class pilot history](goal) is the mathematical object specified below. -/
instance instMeasurableSingletonClassPilotHistory (n : ℕ) (i : Fin n) :
    MeasurableSingletonClass (PrivateHistory (Z := pilotOutputFamily n) i) := by
  infer_instance

/-- For the supplied quantities and conditions, the rr pilot probability is the mathematical object specified below. [The rr Pilot Probability](goal) is determined by [the displayed parameters](hyp:ε,j,k). -/
def rrPilotProbability (ε : ℝ) (j k : Fin 4) : ℝ :=
  (if j = k then Real.exp ε else 1) / (Real.exp ε + 3)

-- @node: rrPilotProbability_ldp
/-- Under the supplied quantities and conditions, the rr pilot probability ldp assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε), [the rr Pilot Probability ldp](goal).

Under the stated assumptions, the rr Pilot Probability ldp. -/
lemma rrPilotProbability_ldp (ε : ℝ) (hε : 0 < ε)
    (j j' k : Fin 4) :
    rrPilotProbability ε j k ≤ Real.exp ε * rrPilotProbability ε j' k := by
  have he : 1 ≤ Real.exp ε := (Real.one_le_exp_iff).2 (le_of_lt hε)
  have hd : 0 < Real.exp ε + 3 := by positivity
  unfold rrPilotProbability
  rw [← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right hd).2
  split_ifs <;> nlinarith [sq_nonneg (Real.exp ε - 1)]

/-- the rr pilot kernel is the mathematical object specified below. [The rr Pilot Kernel](goal) is determined by [the displayed parameters](hyp:ε). -/
def rrPilotKernel (ε : ℝ) : Kernel (Fin 4) (Fin 4) :=
  Kernel.ofFunOfCountable fun j =>
    Measure.count.withDensity
      (fun k : Fin 4 => ENNReal.ofReal (rrPilotProbability ε j k))

-- @node: rrPilotKernel_markov
/-- [the rr pilot kernel markov assertion](goal) holds. -/
lemma rrPilotKernel_markov (ε : ℝ) : IsMarkovKernel (rrPilotKernel ε) := by
  constructor
  intro j
  constructor
  have he : 0 < Real.exp ε := Real.exp_pos ε
  have hd : Real.exp ε + 3 ≠ 0 := by positivity
  have hsum : (∑ k : Fin 4, rrPilotProbability ε j k) = 1 := by
    fin_cases j <;> simp +decide [rrPilotProbability, Fin.sum_univ_succ] <;>
      field_simp <;> ring
  rw [← ENNReal.ofReal_one, ← hsum]
  change (Measure.count.withDensity
      (fun k : Fin 4 => ENNReal.ofReal (rrPilotProbability ε j k))) Set.univ = _
  simp only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_count]
  rw [tsum_fintype, ENNReal.ofReal_sum_of_nonneg]
  intro k hk
  unfold rrPilotProbability
  split_ifs <;> positivity

-- @node: rrPilotKernel_private
/-- Under the supplied quantities and conditions, the rr pilot kernel private assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε), [the rr Pilot Kernel private](goal).

Under the stated assumptions, the rr Pilot Kernel private. -/
lemma rrPilotKernel_private (ε : ℝ) (hε : 0 < ε)
    (A : Set (Fin 4)) (j j' : Fin 4) :
    rrPilotKernel ε j A ≤ ENNReal.ofReal (Real.exp ε) * rrPilotKernel ε j' A := by
  let r := ENNReal.ofReal (Real.exp ε)
  have hr : r ≠ ∞ := ENNReal.ofReal_ne_top
  have hm : Measure.count.withDensity
      (fun k : Fin 4 => ENNReal.ofReal (rrPilotProbability ε j k)) ≤
      r • Measure.count.withDensity
        (fun k : Fin 4 => ENNReal.ofReal (rrPilotProbability ε j' k)) := by
    rw [← withDensity_smul' r _ hr]
    apply withDensity_mono
    filter_upwards [] with k
    dsimp [r]
    rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos ε))]
    exact ENNReal.ofReal_le_ofReal (rrPilotProbability_ldp ε hε j j' k)
  exact hm A

/-- For the supplied quantities and conditions, the clip interior is the mathematical object specified below. [The clip Interior](goal) is determined by [the displayed parameters](hyp:δ,x). -/
def clipInterior (δ x : ℝ) : ℝ :=
  max δ (min (1 - δ) x)

/-- For [the supplied quantities and conditions](hyp:m), the [pilot frequency](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:z,k), these specify the stated inputs. -/
def pilotFrequency {n : ℕ} (m : ℕ → ℕ)
    (z : Transcript (pilotOutputFamily n)) (k : Fin 4) : ℝ :=
  (m n : ℝ)⁻¹ * ∑ i : Fin n,
    if i.val < m n ∧ z i = Sum.inl k then (1 : ℝ) else 0

/-- For the supplied quantities and conditions, the pilot theta is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The pilot Theta](goal) is determined by [the displayed parameters](hyp:p,ε,m,z). -/
def pilotTheta (p ε : ℝ) (m : ℕ → ℕ) {n : ℕ}
    (z : Transcript (pilotOutputFamily n)) : TrialParameter :=
  let δ := (m n + 2 : ℝ)⁻¹
  let invFreq (k : Fin 4) :=
    ((Real.exp ε + 3) * pilotFrequency m z k - 1) /
      (Real.exp ε - 1)
  fun a =>
    if a = 0 then clipInterior δ (invFreq 1 / controlProb p)
    else clipInterior δ (invFreq 3 / p)
  -- @realizes \widetilde\theta(inverted clipped randomized-response pilot)

/-- For [the supplied quantities and conditions](hyp:m), the [pilot history frequency](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:i,h,k), these specify the stated inputs. -/
def pilotHistoryFrequency {n : ℕ} (m : ℕ → ℕ)
    (i : Fin n) (h : PrivateHistory (Z := pilotOutputFamily n) i)
    (k : Fin 4) : ℝ :=
  (m n : ℝ)⁻¹ * ∑ j : {j : Fin n // j < i},
    if j.1.val < m n ∧ h j = Sum.inl k then (1 : ℝ) else 0

/-- For the supplied quantities and conditions, the pilot history theta is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The pilot History Theta](goal) is determined by [the displayed parameters](hyp:p,ε,m,i,h). -/
def pilotHistoryTheta (p ε : ℝ) (m : ℕ → ℕ) {n : ℕ}
    (i : Fin n) (h : PrivateHistory (Z := pilotOutputFamily n) i) :
    TrialParameter :=
  let δ := (m n + 2 : ℝ)⁻¹
  let invFreq (k : Fin 4) :=
    ((Real.exp ε + 3) * pilotHistoryFrequency m i h k - 1) /
      (Real.exp ε - 1)
  fun a =>
    if a = 0 then clipInterior δ (invFreq 1 / controlProb p)
    else clipInterior δ (invFreq 3 / p)

-- @node: clipInterior_interior
/-- Under the supplied quantities and conditions, the clip interior interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hδ,hhalf), [the clip Interior interior](goal).

Under the stated assumptions, the clip Interior interior. -/
lemma clipInterior_interior (δ x : ℝ) (hδ : 0 < δ)
    (hhalf : δ ≤ 1 / 2) : 0 < clipInterior δ x ∧ clipInterior δ x < 1 := by
  unfold clipInterior
  constructor
  · exact lt_of_lt_of_le hδ (le_max_left _ _)
  · have hbound : max δ (min (1 - δ) x) ≤ 1 - δ :=
      max_le (by linarith) (min_le_left _ _)
    linarith

-- @node: pilotHistoryTheta_interior
/-- Under [the supplied quantities and conditions](hyp:p,m), [the pilot history theta interior assertion](goal) holds. For [the displayed quantities and conditions](hyp:i,h), these specify the stated inputs. -/
lemma pilotHistoryTheta_interior (p ε : ℝ) (m : ℕ → ℕ) {n : ℕ}
    (i : Fin n) (h : PrivateHistory (Z := pilotOutputFamily n) i) :
    InteriorMeans (pilotHistoryTheta p ε m i h) := by
  have hδ : 0 < ((m n + 2 : ℝ)⁻¹) := by positivity
  have hhalf : ((m n + 2 : ℝ)⁻¹) ≤ 1 / 2 := by
    rw [one_div]
    have hden : (2 : ℝ) ≤ m n + 2 := by
      exact_mod_cast Nat.le_add_left 2 (m n)
    simpa [one_div] using one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 2) hden
  have h0 := clipInterior_interior ((m n + 2 : ℝ)⁻¹)
    (((Real.exp ε + 3) * pilotHistoryFrequency m i h 1 - 1) /
      (Real.exp ε - 1) / controlProb p) hδ hhalf
  have h1 := clipInterior_interior ((m n + 2 : ℝ)⁻¹)
    (((Real.exp ε + 3) * pilotHistoryFrequency m i h 3 - 1) /
      (Real.exp ε - 1) / p) hδ hhalf
  simpa [InteriorMeans, pilotHistoryTheta] using
    And.intro h0.1 (And.intro h0.2 (And.intro h1.1 h1.2))

/-- For the supplied quantities and conditions, the saddle selection is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The Saddle Selection](goal) is determined by [the displayed parameters](hyp:p,ε,select). -/
def SaddleSelection (p ε : ℝ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ) : Prop :=
  Measurable select ∧
  ∀ θ, InteriorMeans θ →
    staircaseFeasible ε (select θ).1 ∧
    (∀ u, informationObjective θ p ε (select θ).1 (select θ).2.1 ≤
      informationObjective θ p ε (select θ).1 u) ∧
    Jstar θ p ε = (select θ).2.2 ∧
    (select θ).2.2 =
      informationObjective θ p ε (select θ).1 (select θ).2.1

/-- For the supplied quantities and conditions, the strong saddle selection is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The Strong Saddle Selection](goal) is determined by [the displayed parameters](hyp:p,ε,select). -/
def StrongSaddleSelection (p ε : ℝ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ) : Prop :=
  SaddleSelection p ε select ∧
  ∀ θ, InteriorMeans θ → ∀ β, staircaseFeasible ε β →
    informationObjective θ p ε β (select θ).2.1 ≤
      informationObjective θ p ε (select θ).1 (select θ).2.1

-- keep: proves nonvacuity of the universal measurable strong-saddle selector interface
/-- Under the supplied quantities and conditions, the exists measurable strong saddle selector assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hε), [the exists measurable strong saddle selector](goal).

Under the stated assumptions, the exists measurable strong saddle selector. -/
lemma exists_measurable_strong_saddle_selector (p ε : ℝ)
    (hp : InteriorAssignment p) (hε : 0 < ε) :
    ∃ select : TrialParameter → StaircaseWeight × ℝ × ℝ,
      StrongSaddleSelection p ε select := by
  obtain ⟨select, hm, hs⟩ :=
    exists_measurable_saddle_selector_bridge_strong p ε hp hε
  refine ⟨select, ⟨⟨hm, ?_⟩, ?_⟩⟩
  · intro θ hθ
    have h := hs θ hθ
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · intro θ hθ
    exact (hs θ hθ).2.2.2.2

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under the supplied quantities and conditions, the exists measurable saddle selector assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hε), [the exists measurable saddle selector](goal).

Under the stated assumptions, the exists measurable saddle selector. -/
lemma exists_measurable_saddle_selector (p ε : ℝ)
    (hp : InteriorAssignment p) (hε : 0 < ε) :
    ∃ select : TrialParameter → StaircaseWeight × ℝ × ℝ,
      SaddleSelection p ε select := by
  exact exists_measurable_saddle_selector_bridge p ε hp hε

/-- For the supplied quantities and conditions, the phi tilde is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The phi Tilde](goal) is determined by [the displayed parameters](hyp:θ,p,ε,select,s). -/
def phiTilde (θ : TrialParameter) (p ε : ℝ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    (s : Fin 14) : ℝ :=
  projectedGradient p ε s (select θ).2.1 /
    ((select θ).2.2 * patternMass θ p ε s)
  -- @realizes \widetilde\phi(S)(selected affine correction)

/-- For the supplied quantities and conditions, the phi output is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The phi Output](goal) is determined by [the displayed parameters](hyp:θ,p,ε,select,z). -/
def phiOutput (θ : TrialParameter) (p ε : ℝ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    (z : PilotOutput) : ℝ :=
  match z with
  | Sum.inl _ => 0
  | Sum.inr s => phiTilde θ p ε select s -- @realizes S_i(main-sample pattern release)

/-- For the supplied quantities and conditions, the tau star is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The tau Star](goal) is determined by [the displayed parameters](hyp:p,ε,m,select,z). -/
def tauStar (p ε : ℝ) (m : ℕ → ℕ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    {n : ℕ} (z : Transcript (pilotOutputFamily n)) : ℝ :=
  let θtilde := pilotTheta p ε m z
  let N := n - m n
  contrast θtilde +
    (N : ℝ)⁻¹ * ∑ i : Fin n,
      if m n ≤ i.val then phiOutput θtilde p ε select (z i) else 0
  -- @realizes \widehat\tau^*(pilot contrast plus main correction)

/-- For the supplied quantities and conditions, the vhat star is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The Vhat Star](goal) is determined by [the displayed parameters](hyp:p,ε,m,select,z). -/
def VhatStar (p ε : ℝ) (m : ℕ → ℕ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    {n : ℕ} (z : Transcript (pilotOutputFamily n)) : ℝ :=
  let θtilde := pilotTheta p ε m z
  let N := n - m n
  let mean := (N : ℝ)⁻¹ * ∑ i : Fin n,
    if m n ≤ i.val then phiOutput θtilde p ε select (z i) else 0
  (N : ℝ)⁻¹ * ∑ i : Fin n,
    if m n ≤ i.val then
      (phiOutput θtilde p ε select (z i) - mean) ^ 2
    else 0
  -- @realizes \widehat V^*(main-sample influence variance)

/-- For the supplied quantities and conditions, the pilot protocol is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The pilot Protocol](goal) is determined by [the displayed parameters](hyp:p,ε,m,select,n). -/
def pilotProtocol (p ε : ℝ) (m : ℕ → ℕ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    (n : ℕ) : SequentialKernel (Z := pilotOutputFamily n) :=
  fun i => Kernel.ofFunOfCountable fun xh =>
    if i.val < m n then
      (rrPilotKernel ε xh.1).map Sum.inl
    else
      ((staircaseChannel ε
        (select (pilotHistoryTheta p ε m i xh.2)).1) xh.1).map Sum.inr

/-- Under the supplied quantities and conditions, the pilot protocol private assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε), [the pilot Protocol private](goal).

Under the stated assumptions, the pilot Protocol private. -/
lemma pilotProtocol_private (p ε : ℝ) (m : ℕ → ℕ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) (n : ℕ) :
    SequentialLDP (Z := pilotOutputFamily n) ε
      (pilotProtocol p ε m select n) := by
  constructor
  · intro i
    constructor
    intro xh
    change IsProbabilityMeasure
      (if i.val < m n then (rrPilotKernel ε xh.1).map Sum.inl
       else (staircaseChannel ε
        (select (pilotHistoryTheta p ε m i xh.2)).1 xh.1).map Sum.inr)
    split_ifs with hi
    · haveI : IsMarkovKernel (rrPilotKernel ε) := rrPilotKernel_markov ε
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    · have hsel := hselect.1.2
          (pilotHistoryTheta p ε m i xh.2)
          (pilotHistoryTheta_interior p ε m i xh.2)
      haveI : IsMarkovKernel (staircaseChannel ε
          (select (pilotHistoryTheta p ε m i xh.2)).1) :=
        staircaseChannel_markov ε _ hsel.1
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  · intro i A hA x x' h
    change (if i.val < m n then (rrPilotKernel ε x).map Sum.inl
      else (staircaseChannel ε
        (select (pilotHistoryTheta p ε m i h)).1 x).map Sum.inr) A ≤
      ENNReal.ofReal (Real.exp ε) *
        (if i.val < m n then (rrPilotKernel ε x').map Sum.inl
        else (staircaseChannel ε
          (select (pilotHistoryTheta p ε m i h)).1 x').map Sum.inr) A
    split_ifs with hi
    · rw [Measure.map_apply (by fun_prop) hA,
          Measure.map_apply (by fun_prop) hA]
      exact rrPilotKernel_private ε hε _ x x'
    · rw [Measure.map_apply (by fun_prop) hA,
          Measure.map_apply (by fun_prop) hA]
      have hsel := hselect.1.2
          (pilotHistoryTheta p ε m i h)
          (pilotHistoryTheta_interior p ε m i h)
      exact staircaseChannel_private ε hε _ hsel.1 _ x x'

-- @node: tauStar_measurable
/-- Under [the supplied quantities and conditions](hyp:p,m), [the tau star measurable assertion](goal) holds. For [the displayed quantities and conditions](hyp:select,n), these specify the stated inputs. -/
lemma tauStar_measurable (p ε : ℝ) (m : ℕ → ℕ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ) (n : ℕ) :
    Measurable (tauStar p ε m select (n := n)) := by
  exact measurable_of_finite _

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under the supplied quantities and conditions, the exists pilot transcript assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε), [the exists pilot transcript](goal).

Under the stated assumptions, the exists pilot transcript. -/
lemma exists_pilot_transcript (p ε : ℝ) (m : ℕ → ℕ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) (n : ℕ) :
    ∃ R : (Fin n → Fin 4) → Measure (Transcript (pilotOutputFamily n)),
      TranscriptFactorizes
        (pilotProtocol p ε m select n) R := by
  exact exists_transcript_factorization
    (pilotProtocol p ε m select n)
    (pilotProtocol_private p ε m select hselect hp hε n).1

-- @node: def:pilot-estimator
/-- For the supplied quantities and conditions, the pilot estimator is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The pilot Estimator](goal) is determined by [the displayed parameters](hyp:p,ε,m,select,hselect,hp,hε). -/
def pilotEstimator (p ε : ℝ) (m : ℕ → ℕ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) :
    ProcedureSequence pilotOutputFamily ε where
  channel n := pilotProtocol p ε m select n
  transcript n := finiteSequenceTranscript
    (pilotProtocol p ε m select n)
  factorizes n := finiteSequenceTranscript_factorizes
    (pilotProtocol p ε m select n)
    (pilotProtocol_private p ε m select hselect hp hε n).1
  privacy n := pilotProtocol_private p ε m select hselect hp hε n
  estimate n := tauStar p ε m select (n := n)
  estimate_measurable n := tauStar_measurable p ε m select n

end CausalSmith.Stat.LdpAteEfficiencySurface

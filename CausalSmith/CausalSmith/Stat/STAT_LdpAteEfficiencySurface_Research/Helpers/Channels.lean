module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.Kernel.Basic

/-! # Stationary private channels and their information

Radon–Nikodym densities are taken against the finite sum of the four channel
rows, so no countable-generation condition is imposed on the output space. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Z : Type*} [MeasurableSpace Z]

/-- the stationary ldp is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The Stationary LDP](goal) is determined by [the displayed parameters](hyp:ε,Q). -/
def StationaryLDP (ε : ℝ) (Q : Kernel (Fin 4) Z) : Prop :=
  IsMarkovKernel Q ∧
  ∀ A, MeasurableSet A → ∀ x x',
    Q x A ≤ ENNReal.ofReal (Real.exp ε) * Q x' A
  -- @realizes Q(arbitrary-output stationary private channel)

/-- the [dominating measure](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
def dominatingMeasure (Q : Kernel (Fin 4) Z) : Measure Z :=
  ∑ j : Fin 4, Q j

/-- For [the supplied quantities and conditions](hyp:j), the [channel density](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
def channelDensity (Q : Kernel (Fin 4) Z) (j : Fin 4) : Z → ℝ :=
  fun z => (Q j |>.rnDeriv (dominatingMeasure Q) z).toReal

/-- For [the supplied quantities and conditions](hyp:p,j,k), the [input derivative](goal) is the mathematical object specified below. -/
def inputDerivative (p : ℝ) (j : Fin 4) (k : Fin 2) : ℝ :=
  if k = 0 then
    if j = 0 then -controlProb p else if j = 1 then controlProb p else 0
  else
    if j = 2 then -p else if j = 3 then p else 0

/-- For the supplied quantities and conditions, the channel output density is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The channel Output Density](goal) is determined by [the displayed parameters](hyp:θ,p,Q,z). -/
def channelOutputDensity (θ : TrialParameter) (p : ℝ)
    (Q : Kernel (Fin 4) Z) (z : Z) : ℝ :=
  ∑ j : Fin 4, piTheta θ p j * channelDensity Q j z

/-- For [the supplied quantities and conditions](hyp:p), the [channel derivative density](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:Q,k,z), these specify the stated inputs. -/
def channelDerivativeDensity (p : ℝ) (Q : Kernel (Fin 4) Z)
    (k : Fin 2) (z : Z) : ℝ :=
  ∑ j : Fin 4, inputDerivative p j k * channelDensity Q j z

/-- For the supplied quantities and conditions, the channel fisher info is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The channel Fisher Info](goal) is determined by [the displayed parameters](hyp:θ,p,Q). -/
def channelFisherInfo (θ : TrialParameter) (p : ℝ)
    (Q : Kernel (Fin 4) Z) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => ∫ z, (channelDerivativeDensity p Q a z *
    channelDerivativeDensity p Q b z) / channelOutputDensity θ p Q z
      ∂dominatingMeasure Q
  -- @realizes I_\theta(Q)(RN-density Fisher matrix)

/-- For the supplied quantities and conditions, the output law is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The output Law](goal) is determined by [the displayed parameters](hyp:θ,p,Q). -/
def outputLaw (θ : TrialParameter) (p : ℝ) (Q : Kernel (Fin 4) Z) : Measure Z :=
  ∑ j : Fin 4, ENNReal.ofReal (piTheta θ p j) • Q j

open Classical in
/-- For the supplied quantities and conditions, the output cardinality is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The output Cardinality](goal) is determined by [the displayed parameters](hyp:θ,p,Q). -/
def outputCardinality (θ : TrialParameter) (p : ℝ)
    (Q : Kernel (Fin 4) Z) : ℕ∞ :=
  if h : Finite Z then
    letI := h
    Set.encard {z : Z | outputLaw θ p Q {z} ≠ 0}
  else ⊤
  -- @realizes \kappa(Q)(positive-mass symbols for finite outputs; infinity otherwise)

/-- the staircase channel is the mathematical object specified below. [The staircase Channel](goal) is determined by [the displayed parameters](hyp:ε,α). -/
def staircaseChannel (ε : ℝ) (α : StaircaseWeight) : Kernel (Fin 4) (Fin 14) :=
  Kernel.ofFunOfCountable fun j =>
    Measure.count.withDensity
      (fun s : Fin 14 => ENNReal.ofReal (α s * patternRay ε s j))
  -- @realizes Q_\alpha(pattern release law)

private def staircaseRowMass (ε : ℝ) (α : StaircaseWeight)
    (j : Fin 4) (s : Fin 14) : ℝ≥0∞ :=
  ENNReal.ofReal (α s * patternRay ε s j)

private def staircaseTotalMass (ε : ℝ) (α : StaircaseWeight)
    (s : Fin 14) : ℝ≥0∞ :=
  ∑ j : Fin 4, staircaseRowMass ε α j s

private lemma staircaseChannel_eq_withDensity (ε : ℝ) (α : StaircaseWeight)
    (j : Fin 4) :
    staircaseChannel ε α j =
      Measure.count.withDensity (staircaseRowMass ε α j) := by
  rfl

private lemma dominatingMeasure_staircaseChannel (ε : ℝ) (α : StaircaseWeight) :
    dominatingMeasure (staircaseChannel ε α) =
      Measure.count.withDensity (staircaseTotalMass ε α) := by
  apply Measure.ext_of_singleton
  intro s
  unfold dominatingMeasure
  change (∑ j : Fin 4, staircaseChannel ε α j {s}) = _
  rw [withDensity_apply _ (measurableSet_singleton s)]
  simp only [lintegral_singleton]
  simp
  apply Finset.sum_congr rfl
  intro j hj
  rw [staircaseChannel_eq_withDensity,
    withDensity_apply _ (measurableSet_singleton s)]
  simp [staircaseTotalMass, staircaseRowMass]

private lemma channelDensity_staircase_raw_ae (ε : ℝ) (α : StaircaseWeight)
    (j : Fin 4) :
    channelDensity (staircaseChannel ε α) j =ᵐ[
      dominatingMeasure (staircaseChannel ε α)]
      fun s => (staircaseRowMass ε α j s /
        staircaseTotalMass ε α s).toReal := by
  let _ : SigmaFinite (staircaseChannel ε α j) := by
    rw [staircaseChannel_eq_withDensity]
    exact SigmaFinite.withDensity_of_ne_top' (by
      intro s
      simp [staircaseRowMass])
  let _ : SigmaFinite (dominatingMeasure (staircaseChannel ε α)) := by
    rw [dominatingMeasure_staircaseChannel]
    exact SigmaFinite.withDensity_of_ne_top' (by
      intro s
      simp [staircaseTotalMass, staircaseRowMass])
  have hdom : dominatingMeasure (staircaseChannel ε α) ≪ Measure.count := by
    rw [dominatingMeasure_staircaseChannel]
    exact withDensity_absolutelyContinuous _ _
  have hrow : staircaseChannel ε α j ≪ Measure.count := by
    rw [staircaseChannel_eq_withDensity]
    exact withDensity_absolutelyContinuous _ _
  have hquot := Measure.rnDeriv_eq_div hrow hdom
  have hrowdensity :
      (staircaseChannel ε α j).rnDeriv Measure.count =ᵐ[
        dominatingMeasure (staircaseChannel ε α)] staircaseRowMass ε α j :=
    hdom (by
      rw [staircaseChannel_eq_withDensity]
      exact Measure.rnDeriv_withDensity _ (measurable_of_finite _))
  have htotaldensity :
      (dominatingMeasure (staircaseChannel ε α)).rnDeriv Measure.count =ᵐ[
        dominatingMeasure (staircaseChannel ε α)] staircaseTotalMass ε α :=
    hdom (by
      rw [dominatingMeasure_staircaseChannel]
      exact Measure.rnDeriv_withDensity _ (measurable_of_finite _))
  filter_upwards [hquot, hrowdensity, htotaldensity] with s hq hr ht
  unfold channelDensity
  rw [hq, hr, ht]

/-- the channel density staircase ae assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε,hα), [the channel Density staircase ae](goal).

Under the stated assumptions, the channel Density staircase ae. -/
lemma channelDensity_staircase_ae (ε : ℝ) (α : StaircaseWeight)
    (hε : 0 ≤ ε) (hα : ∀ s, 0 ≤ α s) (j : Fin 4) :
    channelDensity (staircaseChannel ε α) j =ᵐ[
      dominatingMeasure (staircaseChannel ε α)]
      fun s => if α s = 0 then 0 else
        patternRay ε s j / ∑ i : Fin 4, patternRay ε s i := by
  filter_upwards [channelDensity_staircase_raw_ae ε α j] with s hs
  rw [hs]
  have hray (i : Fin 4) : 0 ≤ patternRay ε s i := by
    unfold patternRay privacyIncrement privacyRatio
    cases patternContains s i <;> simp <;> positivity
  have htotal : staircaseTotalMass ε α s =
      ENNReal.ofReal (α s * ∑ i : Fin 4, patternRay ε s i) := by
    unfold staircaseTotalMass staircaseRowMass
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [Finset.mul_sum]
    · intro i hi
      exact mul_nonneg (hα s) (hray i)
  rw [htotal]
  unfold staircaseRowMass
  by_cases ha : α s = 0
  · simp [ha]
  · have ha_pos : 0 < α s := lt_of_le_of_ne (hα s) (Ne.symm ha)
    have hR_pos : 0 < ∑ i : Fin 4, patternRay ε s i := by
      have hone : 0 < patternRay ε s (0 : Fin 4) := lt_of_lt_of_le zero_lt_one (by
        unfold patternRay
        split_ifs <;> simp [privacyIncrement, privacyRatio,
          (Real.one_le_exp_iff).2 hε])
      exact lt_of_lt_of_le hone (Finset.single_le_sum (fun i hi => hray i)
        (Finset.mem_univ 0))
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (mul_nonneg ha_pos.le (hray j)),
      ENNReal.toReal_ofReal (mul_nonneg ha_pos.le hR_pos.le)]
    simp [ha]
    field_simp

/-- the dominating measure staircase singleton real assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε,hα), [the dominating Measure staircase singleton real](goal).

Under the stated assumptions, the dominating Measure staircase singleton real. -/
lemma dominatingMeasure_staircase_singleton_real (ε : ℝ)
    (α : StaircaseWeight) (hε : 0 ≤ ε) (hα : ∀ s, 0 ≤ α s)
    (s : Fin 14) :
    (dominatingMeasure (staircaseChannel ε α)).real {s} =
      α s * ∑ j : Fin 4, patternRay ε s j := by
  rw [dominatingMeasure_staircaseChannel]
  change ((Measure.count.withDensity (staircaseTotalMass ε α)) {s}).toReal = _
  rw [withDensity_apply _ (measurableSet_singleton s)]
  simp only [lintegral_singleton]
  have hray (j : Fin 4) : 0 ≤ patternRay ε s j := by
    unfold patternRay privacyIncrement privacyRatio
    cases patternContains s j <;> simp <;> positivity
  have htotal : staircaseTotalMass ε α s =
      ENNReal.ofReal (α s * ∑ j : Fin 4, patternRay ε s j) := by
    unfold staircaseTotalMass staircaseRowMass
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [Finset.mul_sum]
    · intro j hj
      exact mul_nonneg (hα s) (hray j)
  have hRnonneg : 0 ≤ ∑ j : Fin 4, patternRay ε s j :=
    Finset.sum_nonneg fun j hj => hray j
  rw [htotal]
  simp [ENNReal.toReal_ofReal (mul_nonneg (hα s) hRnonneg)]

-- @node: patternRay_ldp
/-- Under the supplied quantities and conditions, the pattern ray ldp assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε), [the pattern Ray ldp](goal).

Under the stated assumptions, the pattern Ray ldp. -/
lemma patternRay_ldp (ε : ℝ) (hε : 0 < ε)
    (s : Fin 14) (j j' : Fin 4) :
    patternRay ε s j ≤ Real.exp ε * patternRay ε s j' := by
  have he : 1 ≤ Real.exp ε := (Real.one_le_exp_iff).2 (le_of_lt hε)
  cases h : patternContains s j <;> cases h' : patternContains s j' <;>
    simp [patternRay, privacyIncrement, privacyRatio, h, h'] <;>
    nlinarith [sq_nonneg (Real.exp ε - 1)]

-- @node: staircaseChannel_markov
/-- the staircase channel markov assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hα), [the staircase Channel markov](goal).

Under the stated assumptions, the staircase Channel markov. -/
lemma staircaseChannel_markov (ε : ℝ) (α : StaircaseWeight)
    (hα : staircaseFeasible ε α) : IsMarkovKernel (staircaseChannel ε α) := by
  constructor
  intro j
  constructor
  have hsum : (∑ s : Fin 14, α s * patternRay ε s j) = 1 := hα.2 j
  rw [← ENNReal.ofReal_one, ← hsum]
  change (Measure.count.withDensity
      (fun s : Fin 14 => ENNReal.ofReal (α s * patternRay ε s j))) Set.univ = _
  simp only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_count]
  rw [tsum_fintype, ENNReal.ofReal_sum_of_nonneg]
  intro s hs
  apply mul_nonneg (hα.1 s)
  unfold patternRay privacyIncrement privacyRatio
  cases patternContains s j <;> simp <;> positivity

-- @node: staircaseChannel_private
/-- Under the supplied quantities and conditions, the staircase channel private assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε,hα), [the staircase Channel private](goal).

Under the stated assumptions, the staircase Channel private. -/
lemma staircaseChannel_private (ε : ℝ) (hε : 0 < ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α)
    (A : Set (Fin 14)) (j j' : Fin 4) :
    staircaseChannel ε α j A ≤
      ENNReal.ofReal (Real.exp ε) * staircaseChannel ε α j' A := by
  let r := ENNReal.ofReal (Real.exp ε)
  have hr : r ≠ ∞ := ENNReal.ofReal_ne_top
  have hm : Measure.count.withDensity
      (fun s : Fin 14 => ENNReal.ofReal (α s * patternRay ε s j)) ≤
      r • Measure.count.withDensity
        (fun s : Fin 14 => ENNReal.ofReal (α s * patternRay ε s j')) := by
    rw [← withDensity_smul' r _ hr]
    apply withDensity_mono
    filter_upwards [] with s
    dsimp [r]
    rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos ε))]
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left (patternRay_ldp ε hε s j j') (hα.1 s)
    nlinarith
  exact hm A

/-- Under the supplied quantities and conditions, the staircase channel stationary ldp assertion holds. Under [the stated assumptions](hyp:hε,hα), [the staircase Channel stationary LDP](goal).

Under the stated assumptions, the staircase Channel stationary LDP. -/
lemma staircaseChannel_stationaryLDP (ε : ℝ) (hε : 0 < ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) :
    StationaryLDP ε (staircaseChannel ε α) := by
  exact ⟨staircaseChannel_markov ε α hα,
    fun A _ j j' => staircaseChannel_private ε hε α hα A j j'⟩

end CausalSmith.Stat.LdpAteEfficiencySurface

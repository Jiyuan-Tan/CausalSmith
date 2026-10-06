module
public import Causalean.Stat.Sample
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Distributions.TwoValued
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Binary trial and finite staircase program

This file fixes the four input symbols of a randomized binary trial and gives the
fourteen ray staircase program for its private information surface. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

/-- the [private alphabet](goal) is the mathematical object specified below. -/
abbrev PrivateAlphabet := Fin 4 -- @realizes \mathcal X(ordered four-point input)
/-- Coordinates of the fourteen nonconstant rays used in the finite program. [The stated result](goal) follows. -/
abbrev StaircasePattern := Fin 14

/-- The declared pattern carrier is the full power set, including the empty and full sets. [The stated result](goal) follows. -/
abbrev StaircaseSubset := Finset PrivateAlphabet
  -- @realizes \mathcal S(all subsets of the four-point alphabet)

/-- the [staircase pattern space](goal) is the mathematical object specified below. -/
def staircasePatternSpace : Finset StaircaseSubset :=
  (Finset.univ : Finset PrivateAlphabet).powerset
  -- @realizes \mathcal S(full power set, including empty and full subsets)

-- keep: exact full-power-set realization certificate
/-- [the staircase pattern space eq univ assertion](goal) holds. -/
lemma staircasePatternSpace_eq_univ : staircasePatternSpace = Finset.univ := by
  ext s
  simp [staircasePatternSpace]

-- keep: exact full-power-set realization certificate
/-- [the staircase pattern space card assertion](goal) holds. -/
lemma staircasePatternSpace_card : staircasePatternSpace.card = 16 := by
  simp [staircasePatternSpace]

-- keep: exact full-power-set realization certificate
/-- [the staircase pattern space contains constants assertion](goal) holds. -/
lemma staircasePatternSpace_contains_constants :
    (∅ : StaircaseSubset) ∈ staircasePatternSpace ∧
      (Finset.univ : StaircaseSubset) ∈ staircasePatternSpace := by
  simp [staircasePatternSpace]
/-- the trial parameter is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The Trial Parameter](goal) is the displayed object. -/
abbrev TrialParameter := Fin 2 → ℝ -- @realizes \theta(real pair; closed square via MeanRange)
/-- the staircase weight is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The Staircase Weight](goal) is the displayed object. -/
abbrev StaircaseWeight := StaircasePattern → ℝ -- @realizes \alpha(fourteen pattern weights)

/-- the [contrast](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:θ), these specify the stated inputs. -/
def contrast (θ : TrialParameter) : ℝ := θ 1 - θ 0 -- @realizes \tau(mu1 - mu0)

/-- the [contrast vector](goal) is the mathematical object specified below. -/
def contrastVector : TrialParameter := fun k => if k = 0 then -1 else 1 -- @realizes c((-1,1))

/-- For [the supplied quantities and conditions](hyp:p), the [control prob](goal) is the mathematical object specified below. -/
def controlProb (p : ℝ) : ℝ := 1 - p -- @realizes q(1-p)

/-- For [the supplied quantities and conditions](hyp:p), the [pi theta](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:θ), these specify the stated inputs. -/
def piTheta (θ : TrialParameter) (p : ℝ) : PrivateAlphabet → ℝ -- @realizes \pi_\theta(four masses)
  | ⟨0, _⟩ => controlProb p * (1 - θ 0)
  | ⟨1, _⟩ => controlProb p * θ 0
  | ⟨2, _⟩ => p * (1 - θ 1)
  | _ => p * θ 1

/-- For [the supplied quantities and conditions](hyp:p), the [input law](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:θ), these specify the stated inputs. -/
def inputLaw (θ : TrialParameter) (p : ℝ) : Measure PrivateAlphabet :=
  Measure.count.withDensity (fun j => ENNReal.ofReal (piTheta θ p j))
  -- @realizes P_\theta(law on four-point alphabet)

-- @realizes \ell_\theta(x_j)(Bernoulli score)
-- keep: reusable public score primitive for later channel and mechanism comparisons
/-- the [input score](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:θ), these specify the stated inputs. -/
def inputScore (θ : TrialParameter) : PrivateAlphabet → TrialParameter
  | ⟨0, _⟩ => fun k => if k = 0 then -(1 - θ 0)⁻¹ else 0
  | ⟨1, _⟩ => fun k => if k = 0 then (θ 0)⁻¹ else 0
  | ⟨2, _⟩ => fun k => if k = 1 then -(1 - θ 1)⁻¹ else 0
  | _ => fun k => if k = 1 then (θ 1)⁻¹ else 0

/-- For [the supplied quantities and conditions](hyp:W,Y,i), the [private record](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:ω), these specify the stated inputs. -/
def privateRecord (W Y : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) : PrivateAlphabet :=
  if W i ω = 0 then
    if Y i ω = 0 then 0 else 1
  else if Y i ω = 0 then 2 else 3
  -- @realizes X_i(ordered treatment-outcome pair)

-- @env: S1
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (Y0 Y1 W Y : ℕ → Ω → ℝ)
  (p : ℝ) -- @realizes p(real carrier; closed range via AssignmentRange)
  (θ : TrialParameter)

/-- For [the supplied quantities and conditions](hyp:Y0,Y1), the [arm mean parameter](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:μ), these specify the stated inputs. -/
def armMeanParameter (μ : Measure Ω) (Y0 Y1 : ℕ → Ω → ℝ) :
    TrialParameter :=
  fun k => if k = 0 then ∫ ω, Y0 0 ω ∂μ else ∫ ω, Y1 0 ω ∂μ
  -- @realizes \mu_0(E[Y0]); @realizes \mu_1(E[Y1]);
  -- @realizes \theta(pair of potential-outcome means; range via MeanRange)

-- @node: ass:iid-subjects
/-- the iid subjects is the mathematical object specified below. [The Iid Subjects](goal) is determined by [the displayed parameters](hyp:μ,Y0,Y1,W). -/
def IidSubjects : Prop :=
  iIndepFun (fun i ω => (Y0 i ω, Y1 i ω, W i ω)) μ ∧
  ∀ i, IdentDistrib
    (fun ω => (Y0 0 ω, Y1 0 ω, W 0 ω))
    (fun ω => (Y0 i ω, Y1 i ω, W i ω)) μ μ

-- @node: ass:random-assignment
/-- the random assignment is the mathematical object specified below. [The Random Assignment](goal) is determined by [the displayed parameters](hyp:μ,Y0,Y1,W). -/
def RandomAssignment : Prop :=
  ∀ i, IndepFun (W i) (fun ω => (Y0 i ω, Y1 i ω)) μ

-- @node: ass:known-assignment
/-- the known assignment is the mathematical object specified below. [The Known Assignment](goal) is determined by [the displayed parameters](hyp:μ,W,p). -/
def KnownAssignment : Prop :=
  ∀ i, (∀ᵐ ω ∂μ, W i ω ∈ ({0, 1} : Set ℝ)) ∧
    μ {ω | W i ω = 1} = ENNReal.ofReal p
    -- @realizes W_i(binary assignment with probability p)

-- @node: ass:consistency
/-- the outcome consistency is the mathematical object specified below. [The Outcome Consistency](goal) is determined by [the displayed parameters](hyp:Y0,Y1,W,Y). -/
def OutcomeConsistency : Prop :=
  ∀ i ω, Y i ω = W i ω * Y1 i ω + (1 - W i ω) * Y0 i ω
  -- @realizes Y_i(consistency equation)

-- @node: ass:binary-outcomes
/-- the binary outcomes is the mathematical object specified below. [The Binary Outcomes](goal) is determined by [the displayed parameters](hyp:μ,Y0,Y1). -/
def BinaryOutcomes : Prop :=
  ∀ i, ∀ᵐ ω ∂μ, Y0 i ω ∈ ({0, 1} : Set ℝ) ∧ Y1 i ω ∈ ({0, 1} : Set ℝ)
  -- @realizes Y_i(0)(binary); @realizes Y_i(1)(binary)

-- @node: ass:interior-assignment
/-- the interior assignment is the mathematical object specified below. [The Interior Assignment](goal) is determined by [the displayed parameters](hyp:p). -/
def InteriorAssignment : Prop := 0 < p ∧ p < 1

-- @node: ass:interior-means
/-- the interior means is the mathematical object specified below. [The Interior Means](goal) is determined by [the displayed parameters](hyp:θ). -/
def InteriorMeans : Prop :=
  0 < θ 0 ∧ θ 0 < 1 ∧ 0 < θ 1 ∧ θ 1 < 1

-- @node: def:assignment-range
/-- For [the supplied quantities and conditions](hyp:p), the [assignment range](goal) is the mathematical object specified below. -/
def AssignmentRange (p : ℝ) : Prop := 0 ≤ p ∧ p ≤ 1
  -- @realizes p(closed assignment-probability range [0,1])

-- @node: def:mean-range
/-- the [mean range](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:θ), these specify the stated inputs. -/
def MeanRange (θ : TrialParameter) : Prop :=
  0 ≤ θ 0 ∧ θ 0 ≤ 1 ∧ 0 ≤ θ 1 ∧ θ 1 ≤ 1
  -- @realizes \mu_0(closed range [0,1]); @realizes \mu_1(closed range [0,1]);
  -- @realizes \theta(closed square [0,1]^2)

/-- the [contrast range](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:τ), these specify the stated inputs. -/
def ContrastRange (τ : ℝ) : Prop := -1 ≤ τ ∧ τ ≤ 1
  -- @realizes \tau(closed contrast range [-1,1])

-- @node: def:control-range
/-- For [the supplied quantities and conditions](hyp:p), the [control range](goal) is the mathematical object specified below. -/
def ControlRange (p : ℝ) : Prop := 0 ≤ controlProb p ∧ controlProb p ≤ 1
  -- @realizes q(closed control-assignment range [0,1])

-- @node: interior_assignment_implies_range
/-- Under [the supplied quantities and conditions](hyp:hp), [the assignment range assertion](goal) holds. -/
lemma InteriorAssignment.assignmentRange (hp : InteriorAssignment p) :
    AssignmentRange p := ⟨hp.1.le, hp.2.le⟩

-- @node: interior_means_implies_range
/-- Under the supplied quantities and conditions, the mean range assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ), [the mean Range](goal).

Under the stated assumptions, the mean Range. -/
lemma InteriorMeans.meanRange (hθ : InteriorMeans θ) : MeanRange θ :=
  ⟨hθ.1.le, hθ.2.1.le, hθ.2.2.1.le, hθ.2.2.2.le⟩

/-- Under the supplied quantities and conditions, the contrast range assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ), [the contrast Range](goal).

Under the stated assumptions, the contrast Range. -/
lemma MeanRange.contrastRange (hθ : MeanRange θ) : ContrastRange (contrast θ) := by
  unfold MeanRange at hθ
  unfold ContrastRange contrast
  constructor <;> linarith [hθ.1, hθ.2.1, hθ.2.2.1, hθ.2.2.2]

-- @node: assignment_range_implies_control_range
/-- Under [the supplied quantities and conditions](hyp:hp), [the control range assertion](goal) holds. -/
lemma AssignmentRange.controlRange (hp : AssignmentRange p) : ControlRange p := by
  unfold AssignmentRange at hp
  unfold ControlRange controlProb
  constructor <;> linarith [hp.1, hp.2]

/-- the positive sample size is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The Positive Sample Size](goal) is the displayed object. -/
abbrev PositiveSampleSize := {n : ℕ // 0 < n}
  -- @realizes n(positive sample-size index)

/-- The public binary-trial model is the family of IID laws of the observed treatment-outcome record. Its `n`th member is the `n`-fold product of the four-point law at `(θ,p)`. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. For the displayed quantities and conditions, these specify the stated inputs. [The Binary Trial Model](goal) is determined by [the displayed parameters](hyp:θ,p,_hθ,_hp,n). -/
-- @node: def:binary-trial-model
def BinaryTrialModel (θ : TrialParameter) (p : ℝ)
    (_hθ : InteriorMeans θ) (_hp : InteriorAssignment p) (n : PositiveSampleSize) :
    Measure (Fin n.val → PrivateAlphabet) :=
  Measure.pi fun _ => inputLaw θ p

/-- A latent representation of the public binary-trial model by potential outcomes, assignment, and the observed outcome. [The Latent Binary Trial Representation](goal) is determined by [the displayed parameters](hyp:μ,Y0,Y1,W,Y,p,θ). -/
structure LatentBinaryTrialRepresentation : Prop where
  measurable : ∀ i, Measurable (fun ω => (Y0 i ω, Y1 i ω, W i ω))
  iid : IidSubjects μ Y0 Y1 W
  randomized : RandomAssignment μ Y0 Y1 W
  assigned : KnownAssignment μ W p
  consistent : OutcomeConsistency Y0 Y1 W Y
  binary : BinaryOutcomes μ Y0 Y1
  assignmentInterior : InteriorAssignment p
  meansInterior : InteriorMeans θ
  parameterLaw : θ = armMeanParameter μ Y0 Y1

-- @node: binary_event_probs
/-- Under [the supplied quantities and conditions](hyp:X), [the binary event probs assertion](goal) holds. For [the displayed quantities and conditions](hyp:hXmeas,hX), these specify the stated inputs. -/
lemma binary_event_probs [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hXmeas : AEMeasurable X μ)
    (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    μ.real {ω | X ω = 1} = ∫ ω, X ω ∂μ ∧
    μ.real {ω | X ω = 0} = 1 - ∫ ω, X ω ∂μ := by
  constructor
  · exact (integral_of_ae_eq_zero_or_one hXmeas hX).symm
  · rw [← integral_one_sub_of_ae_eq_zero_or_one hXmeas hX]
    have hXint : Integrable X μ :=
      Integrable.of_mem_Icc (0 : ℝ) 1 hXmeas (by
        filter_upwards [hX] with ω hω
        rcases hω with hω | hω <;> simp [hω])
    rw [integral_sub (integrable_const 1) hXint]
    simp

-- @node: recordLaw_eq_piTheta
/-- Under [the supplied quantities and conditions](hyp:hmodel), [the record law eq pi theta assertion](goal) holds. For [the displayed quantities and conditions](hyp:i), these specify the stated inputs. -/
lemma recordLaw_eq_piTheta (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ)
    (i : ℕ) :
    μ.map (privateRecord W Y i) = inputLaw θ p := by
  letI : IsProbabilityMeasure μ := hmodel.iid.1.isProbabilityMeasure
  have hY0dist : IdentDistrib (Y0 0) (Y0 i) μ μ := by
    convert (hmodel.iid.2 i).comp (by fun_prop :
      Measurable (fun x : ℝ × ℝ × ℝ => x.1)) using 1 <;> rfl
  have hY1dist : IdentDistrib (Y1 0) (Y1 i) μ μ := by
    convert (hmodel.iid.2 i).comp (by fun_prop :
      Measurable (fun x : ℝ × ℝ × ℝ => x.2.1)) using 1 <;> rfl
  have hWdist : IdentDistrib (W 0) (W i) μ μ := by
    convert (hmodel.iid.2 i).comp (by fun_prop :
      Measurable (fun x : ℝ × ℝ × ℝ => x.2.2)) using 1 <;> rfl
  have hmean0 : ∫ ω, Y0 i ω ∂μ = θ 0 := by
    rw [← hY0dist.integral_eq, hmodel.parameterLaw]
    rfl
  have hmean1 : ∫ ω, Y1 i ω ∂μ = θ 1 := by
    rw [← hY1dist.integral_eq, hmodel.parameterLaw]
    rfl
  have hbinary0 : ∀ᵐ ω ∂μ, Y0 i ω = 0 ∨ Y0 i ω = 1 := by
    filter_upwards [(hmodel.binary i)] with ω hω
    simpa using hω.1
  have hbinary1 : ∀ᵐ ω ∂μ, Y1 i ω = 0 ∨ Y1 i ω = 1 := by
    filter_upwards [(hmodel.binary i)] with ω hω
    simpa using hω.2
  have hbinaryW : ∀ᵐ ω ∂μ, W i ω = 0 ∨ W i ω = 1 := by
    filter_upwards [(hmodel.assigned i).1] with ω hω
    simpa using hω
  have hy0 := binary_event_probs μ (Y0 i) hY0dist.aemeasurable_snd hbinary0
  have hy1 := binary_event_probs μ (Y1 i) hY1dist.aemeasurable_snd hbinary1
  have hw := binary_event_probs μ (W i) hWdist.aemeasurable_snd hbinaryW
  have hm0 : Measurable (Y0 i) := (hmodel.measurable i).fst
  have hm1 : Measurable (Y1 i) := (hmodel.measurable i).snd.fst
  have hmw : Measurable (W i) := (hmodel.measurable i).snd.snd
  have hmy : Measurable (Y i) := by
    have hf : Measurable (fun ω => W i ω * Y1 i ω +
        (1 - W i ω) * Y0 i ω) := by fun_prop
    convert hf using 1
    funext ω
    exact hmodel.consistent i ω
  have hmr : Measurable (privateRecord W Y i) := by
    unfold privateRecord
    apply Measurable.ite (hmw (measurableSet_singleton 0))
    · exact Measurable.ite (hmy (measurableSet_singleton 0))
        measurable_const measurable_const
    · exact Measurable.ite (hmy (measurableSet_singleton 0))
        measurable_const measurable_const
  have hmassY0one : μ {ω | Y0 i ω = 1} = ENNReal.ofReal (θ 0) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    change ENNReal.ofReal (μ.real {ω | Y0 i ω = 1}) = _
    rw [hy0.1, hmean0]
  have hmassY0zero : μ {ω | Y0 i ω = 0} = ENNReal.ofReal (1 - θ 0) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    change ENNReal.ofReal (μ.real {ω | Y0 i ω = 0}) = _
    rw [hy0.2, hmean0]
  have hmassY1one : μ {ω | Y1 i ω = 1} = ENNReal.ofReal (θ 1) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    change ENNReal.ofReal (μ.real {ω | Y1 i ω = 1}) = _
    rw [hy1.1, hmean1]
  have hmassY1zero : μ {ω | Y1 i ω = 0} = ENNReal.ofReal (1 - θ 1) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    change ENNReal.ofReal (μ.real {ω | Y1 i ω = 0}) = _
    rw [hy1.2, hmean1]
  have hmassWone : μ {ω | W i ω = 1} = ENNReal.ofReal p := (hmodel.assigned i).2
  have hmeanW : ∫ ω, W i ω ∂μ = p := by
    rw [← hw.1]
    change (μ {ω | W i ω = 1}).toReal = p
    rw [hmassWone]
    exact ENNReal.toReal_ofReal hmodel.assignmentInterior.1.le
  have hmassWzero : μ {ω | W i ω = 0} = ENNReal.ofReal (controlProb p) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    change ENNReal.ofReal (μ.real {ω | W i ω = 0}) = _
    rw [hw.2, hmeanW]
    rfl
  have hprod0 (a b : ℝ) :
      μ {ω | W i ω = a ∧ Y0 i ω = b} =
        μ {ω | W i ω = a} * μ {ω | Y0 i ω = b} := by
    have h := (hmodel.randomized i).measure_inter_preimage_eq_mul
      ({a} : Set ℝ) ({x : ℝ × ℝ | x.1 = b})
      (measurableSet_singleton a)
      (measurable_fst (measurableSet_singleton b))
    change μ {ω | W i ω = a ∧ Y0 i ω = b} =
      μ {ω | W i ω = a} * μ {ω | Y0 i ω = b} at h
    exact h
  have hprod1 (a b : ℝ) :
      μ {ω | W i ω = a ∧ Y1 i ω = b} =
        μ {ω | W i ω = a} * μ {ω | Y1 i ω = b} := by
    have h := (hmodel.randomized i).measure_inter_preimage_eq_mul
      ({a} : Set ℝ) ({x : ℝ × ℝ | x.2 = b})
      (measurableSet_singleton a)
      (measurable_snd (measurableSet_singleton b))
    change μ {ω | W i ω = a ∧ Y1 i ω = b} =
      μ {ω | W i ω = a} * μ {ω | Y1 i ω = b} at h
    exact h
  have hrec (ω : Ω) (hwω : W i ω = 0 ∨ W i ω = 1) :
      privateRecord W Y i ω =
        if W i ω = 0 then
          (if Y0 i ω = 0 then (0 : Fin 4) else 1)
        else if Y1 i ω = 0 then 2 else 3 := by
    unfold privateRecord
    rw [hmodel.consistent i ω]
    rcases hwω with h0 | h1
    · simp [h0]
    · simp [h1]
  have hatom0 : μ ((privateRecord W Y i) ⁻¹' {0}) =
      μ {ω | W i ω = 0 ∧ Y0 i ω = 0} := by
    apply measure_congr
    filter_upwards [hbinaryW] with ω hwω
    change (privateRecord W Y i ω = 0) = (W i ω = 0 ∧ Y0 i ω = 0)
    apply propext
    rw [hrec ω hwω]
    by_cases h0 : W i ω = 0
    · simp [h0]
    · simp [h0]
      split_ifs <;> decide
  have hatom1 : μ ((privateRecord W Y i) ⁻¹' {1}) =
      μ {ω | W i ω = 0 ∧ Y0 i ω = 1} := by
    apply measure_congr
    filter_upwards [hbinaryW, hbinary0, hbinary1] with ω hwω hy0ω hy1ω
    change (privateRecord W Y i ω = 1) = (W i ω = 0 ∧ Y0 i ω = 1)
    apply propext
    rw [hrec ω hwω]
    rcases hwω with h0 | h1
    · rcases hy0ω with h | h <;> simp [h0, h]
    · rcases hy1ω with h | h <;> simp [h1, h]
  have hatom2 : μ ((privateRecord W Y i) ⁻¹' {2}) =
      μ {ω | W i ω = 1 ∧ Y1 i ω = 0} := by
    apply measure_congr
    filter_upwards [hbinaryW, hbinary0, hbinary1] with ω hwω hy0ω hy1ω
    change (privateRecord W Y i ω = 2) = (W i ω = 1 ∧ Y1 i ω = 0)
    apply propext
    rw [hrec ω hwω]
    rcases hwω with h0 | h1
    · rcases hy0ω with h | h <;> simp [h0, h]
    · rcases hy1ω with h | h <;> simp [h1, h]
  have hatom3 : μ ((privateRecord W Y i) ⁻¹' {3}) =
      μ {ω | W i ω = 1 ∧ Y1 i ω = 1} := by
    apply measure_congr
    filter_upwards [hbinaryW, hbinary0, hbinary1] with ω hwω hy0ω hy1ω
    change (privateRecord W Y i ω = 3) = (W i ω = 1 ∧ Y1 i ω = 1)
    apply propext
    rw [hrec ω hwω]
    rcases hwω with h0 | h1
    · rcases hy0ω with h | h <;> simp [h0, h]
    · rcases hy1ω with h | h <;> simp [h1, h]
  have hinput (j : Fin 4) :
      inputLaw θ p {j} = ENNReal.ofReal (piTheta θ p j) := by
    unfold inputLaw
    rw [withDensity_apply _ (measurableSet_singleton j), lintegral_singleton]
    simp
  apply Measure.ext_of_singleton
  intro j
  fin_cases j
  · change (μ.map (privateRecord W Y i)) {0} = inputLaw θ p {0}
    rw [Measure.map_apply hmr (measurableSet_singleton 0), hatom0,
      hprod0, hmassWzero, hmassY0zero, hinput 0]
    change ENNReal.ofReal (controlProb p) * ENNReal.ofReal (1 - θ 0) =
      ENNReal.ofReal (controlProb p * (1 - θ 0))
    exact (ENNReal.ofReal_mul (le_of_lt (by
      dsimp [controlProb]
      exact sub_pos.mpr hmodel.assignmentInterior.2))).symm
  · change (μ.map (privateRecord W Y i)) {1} = inputLaw θ p {1}
    rw [Measure.map_apply hmr (measurableSet_singleton 1), hatom1,
      hprod0, hmassWzero, hmassY0one, hinput 1]
    change ENNReal.ofReal (controlProb p) * ENNReal.ofReal (θ 0) =
      ENNReal.ofReal (controlProb p * θ 0)
    exact (ENNReal.ofReal_mul (le_of_lt (by
      dsimp [controlProb]
      exact sub_pos.mpr hmodel.assignmentInterior.2))).symm
  · change (μ.map (privateRecord W Y i)) {2} = inputLaw θ p {2}
    rw [Measure.map_apply hmr (measurableSet_singleton 2), hatom2,
      hprod1, hmassWone, hmassY1zero, hinput 2]
    change ENNReal.ofReal p * ENNReal.ofReal (1 - θ 1) =
      ENNReal.ofReal (p * (1 - θ 1))
    exact (ENNReal.ofReal_mul hmodel.assignmentInterior.1.le).symm
  · change (μ.map (privateRecord W Y i)) {3} = inputLaw θ p {3}
    rw [Measure.map_apply hmr (measurableSet_singleton 3), hatom3,
      hprod1, hmassWone, hmassY1one, hinput 3]
    change ENNReal.ofReal p * ENNReal.ofReal (θ 1) =
      ENNReal.ofReal (p * θ 1)
    exact (ENNReal.ofReal_mul hmodel.assignmentInterior.1.le).symm

/-- A latent representation realizes every finite prefix of the public
observed-law model. For [the displayed inputs and conditions](hyp:hmodel), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:n), these specify the stated inputs. -/
lemma latentRepresentation_prefixLaw
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ)
    (n : PositiveSampleSize) :
    μ.map (fun ω => fun i : Fin n.val => privateRecord W Y i ω) =
      BinaryTrialModel θ p hmodel.meansInterior hmodel.assignmentInterior n := by
  have hmeas (i : Fin n.val) : Measurable (privateRecord W Y i) := by
    have hm := hmodel.measurable i.val
    have hmw : Measurable (W i) := hm.snd.snd
    have hmy : Measurable (Y i) := by
      have hf : Measurable (fun ω => W i ω * Y1 i ω +
          (1 - W i ω) * Y0 i ω) := by
        exact hmw.mul hm.snd.fst |>.add ((measurable_const.sub hmw).mul hm.fst)
      convert hf using 1
      funext ω
      exact hmodel.consistent i ω
    unfold privateRecord
    exact Measurable.ite (hmw (measurableSet_singleton 0))
      (Measurable.ite (hmy (measurableSet_singleton 0)) measurable_const measurable_const)
      (Measurable.ite (hmy (measurableSet_singleton 0)) measurable_const measurable_const)
  let g : (Fin n.val) → (ℝ × ℝ × ℝ) → PrivateAlphabet := fun _ x =>
    if x.2.2 = 0 then (if x.1 = 0 then 0 else 1)
    else if x.2.1 = 0 then 2 else 3
  have hg (i : Fin n.val) : Measurable (g i) := by
    unfold g
    apply Measurable.ite (measurable_snd.snd (measurableSet_singleton 0))
    · exact Measurable.ite (measurable_fst (measurableSet_singleton 0))
        measurable_const measurable_const
    · exact Measurable.ite (measurable_snd.fst (measurableSet_singleton 0))
        measurable_const measurable_const
  have hindTriple : iIndepFun
      (fun i : Fin n.val => fun ω => (Y0 i ω, Y1 i ω, W i ω)) μ :=
    hmodel.iid.1.precomp Fin.val_injective
  have hindG := hindTriple.comp g hg
  have hcomp (i : Fin n.val) :
      g i ∘ (fun ω => (Y0 i ω, Y1 i ω, W i ω)) =ᵐ[μ]
        privateRecord W Y i := by
    filter_upwards [(hmodel.assigned i).1] with ω hw
    have hw' : W i ω = 0 ∨ W i ω = 1 := by simpa using hw
    simp only [Function.comp_apply, g, privateRecord]
    rw [hmodel.consistent i ω]
    rcases hw' with hw | hw <;> simp [hw]
  have hind : iIndepFun (fun i : Fin n.val => privateRecord W Y i) μ := by
    apply hindG.congr
    exact hcomp
  rw [hind.map_fun_eq_pi_map (fun i => (hmeas i).aemeasurable)]
  unfold BinaryTrialModel
  congr 1
  funext i
  exact recordLaw_eq_piTheta μ Y0 Y1 W Y p θ hmodel i

private def canonicalBit (b : Bool) : ℝ := if b then 1 else 0

private def canonicalBernoulli (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) : Measure Bool :=
  bernoulliMeasure true false ⟨x, hx⟩

private def canonicalSubjectLaw (θ : TrialParameter) (p : ℝ)
    (hθ : InteriorMeans θ) (hp : InteriorAssignment p) :
    Measure ((Bool × Bool) × Bool) :=
  ((canonicalBernoulli (θ 0) ⟨hθ.1.le, hθ.2.1.le⟩).prod
    (canonicalBernoulli (θ 1) ⟨hθ.2.2.1.le, hθ.2.2.2.le⟩)).prod
    (canonicalBernoulli p ⟨hp.1.le, hp.2.le⟩)

private def canonicalY0 (i : ℕ) (ω : ℕ → ((Bool × Bool) × Bool)) : ℝ :=
  canonicalBit (ω i).1.1

private def canonicalY1 (i : ℕ) (ω : ℕ → ((Bool × Bool) × Bool)) : ℝ :=
  canonicalBit (ω i).1.2

private def canonicalW (i : ℕ) (ω : ℕ → ((Bool × Bool) × Bool)) : ℝ :=
  canonicalBit (ω i).2

private def canonicalY (i : ℕ) (ω : ℕ → ((Bool × Bool) × Bool)) : ℝ :=
  canonicalW i ω * canonicalY1 i ω + (1 - canonicalW i ω) * canonicalY0 i ω

private lemma canonicalLatentRepresentation (θ : TrialParameter) (p : ℝ)
    (hθ : InteriorMeans θ) (hp : InteriorAssignment p) :
    let ν := canonicalSubjectLaw θ p hθ hp
    let μ := Measure.infinitePi (fun _ : ℕ => ν)
    LatentBinaryTrialRepresentation μ canonicalY0 canonicalY1 canonicalW canonicalY p θ := by
  dsimp only
  let ν := canonicalSubjectLaw θ p hθ hp
  let μ := Measure.infinitePi (fun _ : ℕ => ν)
  have h0prob : IsProbabilityMeasure
      (canonicalBernoulli (θ 0) ⟨hθ.1.le, hθ.2.1.le⟩) := by
    dsimp [canonicalBernoulli]
    infer_instance
  letI := h0prob
  have h1prob : IsProbabilityMeasure
      (canonicalBernoulli (θ 1) ⟨hθ.2.2.1.le, hθ.2.2.2.le⟩) := by
    dsimp [canonicalBernoulli]
    infer_instance
  letI := h1prob
  have hwprob : IsProbabilityMeasure
      (canonicalBernoulli p ⟨hp.1.le, hp.2.le⟩) := by
    dsimp [canonicalBernoulli]
    infer_instance
  letI := hwprob
  have hpairprob : IsProbabilityMeasure
      ((canonicalBernoulli (θ 0) ⟨hθ.1.le, hθ.2.1.le⟩).prod
        (canonicalBernoulli (θ 1) ⟨hθ.2.2.1.le, hθ.2.2.2.le⟩)) := by
    infer_instance
  letI := hpairprob
  have hν : IsProbabilityMeasure ν := by
    dsimp [ν, canonicalSubjectLaw, canonicalBernoulli]
    infer_instance
  letI : IsProbabilityMeasure ν := hν
  letI : ∀ _ : ℕ, IsProbabilityMeasure ν := fun _ => hν
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have heval (i : ℕ) : μ.map (fun ω => ω i) = ν := by
    simp [μ, Measure.infinitePi_map_eval]
  have hmapTriple (i : ℕ) :
      μ.map (fun ω => (canonicalY0 i ω, canonicalY1 i ω, canonicalW i ω)) =
        ν.map (fun x => (canonicalBit x.1.1, canonicalBit x.1.2, canonicalBit x.2)) := by
    rw [show (fun ω => (canonicalY0 i ω, canonicalY1 i ω, canonicalW i ω)) =
        (fun x => (canonicalBit x.1.1, canonicalBit x.1.2, canonicalBit x.2)) ∘
          (fun ω => ω i) by rfl]
    exact (Measure.map_map (μ := μ) (by fun_prop) (by fun_prop)).symm.trans
      (congrArg (Measure.map fun x =>
        (canonicalBit x.1.1, canonicalBit x.1.2, canonicalBit x.2)) (heval i))
  have hmapW (i : ℕ) : μ.map (canonicalW i) =
      ν.map (fun x => canonicalBit x.2) := by
    rw [show canonicalW i = (fun x => canonicalBit x.2) ∘ (fun ω => ω i) by rfl]
    exact (Measure.map_map (μ := μ) (by fun_prop) (by fun_prop)).symm.trans
      (congrArg (Measure.map fun x => canonicalBit x.2) (heval i))
  have hmapPair (i : ℕ) : μ.map (fun ω => (canonicalY0 i ω, canonicalY1 i ω)) =
      ν.map (fun x => (canonicalBit x.1.1, canonicalBit x.1.2)) := by
    rw [show (fun ω => (canonicalY0 i ω, canonicalY1 i ω)) =
        (fun x => (canonicalBit x.1.1, canonicalBit x.1.2)) ∘ (fun ω => ω i) by rfl]
    exact (Measure.map_map (μ := μ) (by fun_prop) (by fun_prop)).symm.trans
      (congrArg (Measure.map fun x => (canonicalBit x.1.1, canonicalBit x.1.2)) (heval i))
  have hmapJoint (i : ℕ) :
      μ.map (fun ω => (canonicalW i ω, canonicalY0 i ω, canonicalY1 i ω)) =
        ν.map (fun x => (canonicalBit x.2, canonicalBit x.1.1, canonicalBit x.1.2)) := by
    rw [show (fun ω => (canonicalW i ω, canonicalY0 i ω, canonicalY1 i ω)) =
        (fun x => (canonicalBit x.2, canonicalBit x.1.1, canonicalBit x.1.2)) ∘
          (fun ω => ω i) by rfl]
    exact (Measure.map_map (μ := μ) (by fun_prop) (by fun_prop)).symm.trans
      (congrArg (Measure.map fun x =>
        (canonicalBit x.2, canonicalBit x.1.1, canonicalBit x.1.2)) (heval i))
  have hcoord : iIndepFun
      (fun i : ℕ => fun ω : ℕ → ((Bool × Bool) × Bool) => ω i) μ := by
    dsimp [μ]
    exact iIndepFun_infinitePi (X := fun _ x => x) (by fun_prop)
  have htripleMeas (i : ℕ) : Measurable
      (fun ω : ℕ → ((Bool × Bool) × Bool) =>
        (canonicalY0 i ω, canonicalY1 i ω, canonicalW i ω)) := by
    simp only [canonicalY0, canonicalY1, canonicalW]
    fun_prop
  refine
    { measurable := htripleMeas
      iid := ?_
      randomized := ?_
      assigned := ?_
      consistent := ?_
      binary := ?_
      assignmentInterior := hp
      meansInterior := hθ
      parameterLaw := ?_ }
  · constructor
    · have h := hcoord.comp
          (fun _ x => (canonicalBit x.1.1, canonicalBit x.1.2, canonicalBit x.2))
          (by intro i; fun_prop)
      simpa [Function.comp_def, canonicalY0, canonicalY1, canonicalW] using h
    · intro i
      refine ⟨(htripleMeas 0).aemeasurable, (htripleMeas i).aemeasurable, ?_⟩
      exact (hmapTriple 0).trans (hmapTriple i).symm
  · intro i
    have hindν : IndepFun
        (fun x : (Bool × Bool) × Bool => canonicalBit x.2)
        (fun x : (Bool × Bool) × Bool =>
          (canonicalBit x.1.1, canonicalBit x.1.2)) ν := by
      have hpair : IsProbabilityMeasure
          ((canonicalBernoulli (θ 0) ⟨hθ.1.le, hθ.2.1.le⟩).prod
            (canonicalBernoulli (θ 1) ⟨hθ.2.2.1.le, hθ.2.2.2.le⟩)) := by
        dsimp [canonicalBernoulli]
        infer_instance
      letI := hpair
      have hwprob : IsProbabilityMeasure
          (canonicalBernoulli p ⟨hp.1.le, hp.2.le⟩) := by
        dsimp [canonicalBernoulli]
        infer_instance
      letI := hwprob
      have hbase := (indepFun_prod (μ :=
          (canonicalBernoulli (θ 0) ⟨hθ.1.le, hθ.2.1.le⟩).prod
            (canonicalBernoulli (θ 1) ⟨hθ.2.2.1.le, hθ.2.2.2.le⟩))
          (ν := canonicalBernoulli p ⟨hp.1.le, hp.2.le⟩)
          (X := fun x : Bool × Bool => (canonicalBit x.1, canonicalBit x.2))
          (Y := fun x : Bool => canonicalBit x)
          (by fun_prop) (by fun_prop)).symm
      simpa [ν, canonicalSubjectLaw, Function.comp_def] using hbase
    rw [indepFun_iff_map_prod_eq_prod_map_map
      (htripleMeas i).snd.snd.aemeasurable
      (Measurable.prodMk (htripleMeas i).fst (htripleMeas i).snd.fst).aemeasurable]
    rw [hmapJoint i, hmapW i, hmapPair i]
    exact hindν.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)
  · intro i
    constructor
    · filter_upwards with ω
      simp [canonicalW, canonicalBit]
    · change μ ((canonicalW i) ⁻¹' {1}) = ENNReal.ofReal p
      rw [← Measure.map_apply (by
          exact (htripleMeas i).snd.snd)
        (measurableSet_singleton 1), hmapW i]
      rw [show (fun x : (Bool × Bool) × Bool => canonicalBit x.2) =
          canonicalBit ∘ Prod.snd by rfl,
        ← Measure.map_map (by fun_prop) (by fun_prop)]
      simp [ν, canonicalSubjectLaw, canonicalBernoulli, canonicalBit,
        ProbabilityTheory.bernoulliMeasure_apply]
      rw [← ENNReal.ofNNReal_toNNReal p]
      congr 1
      apply NNReal.eq
      simp [unitInterval.coe_toNNReal, Real.coe_toNNReal p hp.1.le]
  · intro i ω
    rfl
  · intro i
    filter_upwards with ω
    simp [canonicalY0, canonicalY1, canonicalBit]
  · funext k
    fin_cases k
    · change θ 0 = ∫ ω, canonicalY0 0 ω ∂μ
      symm
      calc
        ∫ ω, canonicalY0 0 ω ∂μ =
            ∫ x, canonicalBit x.1.1 ∂μ.map (fun ω => ω 0) := by
              rw [integral_map (measurable_pi_apply 0).aemeasurable (by fun_prop)]
              rfl
        _ = ∫ x, canonicalBit x.1.1 ∂ν := by rw [heval 0]
        _ = θ 0 := by
          dsimp [ν, canonicalSubjectLaw]
          rw [integral_prod _ Integrable.of_finite]
          simp
          rw [integral_prod _ Integrable.of_finite]
          simp [canonicalBernoulli, ProbabilityTheory.integral_bernoulliMeasure,
            canonicalBit]
    · change θ 1 = ∫ ω, canonicalY1 0 ω ∂μ
      symm
      calc
        ∫ ω, canonicalY1 0 ω ∂μ =
            ∫ x, canonicalBit x.1.2 ∂μ.map (fun ω => ω 0) := by
              rw [integral_map (measurable_pi_apply 0).aemeasurable (by fun_prop)]
              rfl
        _ = ∫ x, canonicalBit x.1.2 ∂ν := by rw [heval 0]
        _ = θ 1 := by
          dsimp [ν, canonicalSubjectLaw]
          rw [integral_prod _ Integrable.of_finite]
          simp
          rw [integral_prod _ Integrable.of_finite]
          simp [canonicalBernoulli, ProbabilityTheory.integral_bernoulliMeasure,
            canonicalBit]

-- keep: public observed-law/latent-representation characterization required by the research contract
/-- A family belongs to the public observed-law model exactly when some latent binary-trial representation realizes all of its finite-prefix laws. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the binary Trial Model iff latent Representation](goal).

Under the stated assumptions, the binary Trial Model iff latent Representation. -/
theorem binaryTrialModel_iff_latentRepresentation
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (P : (n : PositiveSampleSize) → Measure (Fin n.val → PrivateAlphabet)) :
    P = BinaryTrialModel θ p hθ hp ↔
      ∃ (Ω : Type) (mΩ : MeasurableSpace Ω),
        letI := mΩ
        ∃ (μ : Measure Ω) (Y0 Y1 W Y : ℕ → Ω → ℝ),
          LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ ∧
          ∀ n, μ.map (fun ω => fun i : Fin n.val => privateRecord W Y i ω) = P n := by
  constructor
  · rintro rfl
    let ν := canonicalSubjectLaw θ p hθ hp
    let μ := Measure.infinitePi (fun _ : ℕ => ν)
    have hrep : LatentBinaryTrialRepresentation μ canonicalY0 canonicalY1
        canonicalW canonicalY p θ := canonicalLatentRepresentation θ p hθ hp
    exact ⟨ℕ → ((Bool × Bool) × Bool), inferInstance, μ,
      canonicalY0, canonicalY1, canonicalW, canonicalY, hrep,
      latentRepresentation_prefixLaw μ canonicalY0 canonicalY1 canonicalW canonicalY
        p θ hrep⟩
  · rintro ⟨Ω, mΩ, hrep⟩
    letI := mΩ
    rcases hrep with ⟨μ, Y0, Y1, W, Y, hmodel, hP⟩
    funext n
    rw [← hP n]
    exact latentRepresentation_prefixLaw μ Y0 Y1 W Y p θ hmodel n

-- @env: S3
variable (ε : ℝ) (α : StaircaseWeight)

-- Algebraic extensions used by the existing finite-program calculations.
/-- the [privacy ratio](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:ε), these specify the stated inputs. -/
def privacyRatio (ε : ℝ) : ℝ := Real.exp ε
/-- the [privacy increment](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:ε), these specify the stated inputs. -/
def privacyIncrement (ε : ℝ) : ℝ := privacyRatio ε - 1

/-- The paper's likelihood-ratio parameter is evaluated only at a positive privacy budget. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The admissible Privacy Ratio](goal) is determined by [the displayed parameters](hyp:ε,_hε). -/
def admissiblePrivacyRatio (ε : ℝ) (_hε : 0 < ε) : ℝ :=
  privacyRatio ε -- @realizes r(exp ε with ε>0)

/-- The paper's staircase increment is evaluated only at a positive privacy budget. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The admissible Privacy Increment](goal) is determined by [the displayed parameters](hyp:ε,_hε). -/
def admissiblePrivacyIncrement (ε : ℝ) (_hε : 0 < ε) : ℝ :=
  privacyIncrement ε -- @realizes d(exp ε - 1 with ε>0)

/-- Under the supplied quantities and conditions, the admissible privacy ratio gt one assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε), [the admissible Privacy Ratio gt one](goal).

Under the stated assumptions, the admissible Privacy Ratio gt one. -/
lemma admissiblePrivacyRatio_gt_one (ε : ℝ) (hε : 0 < ε) :
    1 < admissiblePrivacyRatio ε hε := by
  exact Real.one_lt_exp_iff.mpr hε

/-- Under the supplied quantities and conditions, the admissible privacy increment pos assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε), [the admissible Privacy Increment pos](goal).

Under the stated assumptions, the admissible Privacy Increment pos. -/
lemma admissiblePrivacyIncrement_pos (ε : ℝ) (hε : 0 < ε) :
    0 < admissiblePrivacyIncrement ε hε := by
  exact sub_pos.mpr (admissiblePrivacyRatio_gt_one ε hε)

-- keep: reverse-coverage certificate for the exact r symbol space
/-- Under [the supplied quantities and conditions](hyp:r,hr), [the admissible privacy ratio covers assertion](goal) holds. -/
lemma admissiblePrivacyRatio_covers (r : ℝ) (hr : 1 < r) :
    ∃ (ε : ℝ) (hε : 0 < ε), admissiblePrivacyRatio ε hε = r := by
  exact ⟨Real.log r, Real.log_pos hr, Real.exp_log (by linarith)⟩

-- keep: reverse-coverage certificate for the exact d symbol space
/-- Under [the supplied quantities and conditions](hyp:d,hd), [the admissible privacy increment covers assertion](goal) holds. -/
lemma admissiblePrivacyIncrement_covers (d : ℝ) (hd : 0 < d) :
    ∃ (ε : ℝ) (hε : 0 < ε), admissiblePrivacyIncrement ε hε = d := by
  refine ⟨Real.log (d + 1), Real.log_pos (by linarith), ?_⟩
  simp [admissiblePrivacyIncrement, privacyIncrement, privacyRatio,
    Real.exp_log (show 0 < d + 1 by linarith)]

/-- For [the supplied quantities and conditions](hyp:s,j), the [pattern contains](goal) is the mathematical object specified below. -/
def patternContains (s : Fin 14) (j : Fin 4) : Bool :=
  Nat.testBit (s.val + 1) j.val
  -- @realizes S_j(four-bit support)

/-- The fixed enumeration embeds the fourteen nonconstant masks into the full power set. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:s), these specify the stated inputs. -/
-- keep: bridge from the fourteen nonconstant program coordinates into the declared full power set
def staircasePatternSubset (s : StaircasePattern) : StaircaseSubset :=
  Finset.univ.filter (fun j => patternContains s j = true)

/-- For [the supplied quantities and conditions](hyp:s,j), the [pattern ray](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:ε), these specify the stated inputs. -/
def patternRay (ε : ℝ) (s : Fin 14) (j : Fin 4) : ℝ :=
  1 + privacyIncrement ε * if patternContains s j then 1 else 0
  -- @realizes b_S(1+d indicator)

/-- For [the supplied quantities and conditions](hyp:p,s), the [pattern mass](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:θ,ε), these specify the stated inputs. -/
def patternMass (θ : TrialParameter) (p ε : ℝ) (s : Fin 14) : ℝ :=
  ∑ j : Fin 4, piTheta θ p j * patternRay ε s j

/-- The paper's mass factor is computed on the declared probability-parameter domains. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. For the displayed quantities and conditions, these specify the stated inputs. [The admissible Pattern Mass](goal) is determined by [the displayed parameters](hyp:θ,p,ε,_hθ,_hp,_hε,s). -/
def admissiblePatternMass (θ : TrialParameter) (p ε : ℝ)
    (_hθ : MeanRange θ) (_hp : AssignmentRange p) (_hε : 0 < ε)
    (s : StaircasePattern) : ℝ :=
  patternMass θ p ε s
  -- @realizes h_S(\theta)(pi transpose b, with theta in [0,1]^2, p in [0,1], epsilon>0)

-- keep: positivity certificate for the declared h_S parameter domain
/-- Under the supplied quantities and conditions, the admissible pattern mass pos assertion holds. For the displayed quantities and conditions, these specify the stated inputs. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ,hp,hε), [the admissible Pattern Mass pos](goal).

Under the stated assumptions, the admissible Pattern Mass pos. -/
lemma admissiblePatternMass_pos (θ : TrialParameter) (p ε : ℝ)
    (hθ : MeanRange θ) (hp : AssignmentRange p) (hε : 0 < ε)
    (s : StaircasePattern) : 0 < admissiblePatternMass θ p ε hθ hp hε s := by
  have hπ (j : Fin 4) : 0 ≤ piTheta θ p j := by
    rcases hp with ⟨hp0, hp1⟩
    rcases hθ with ⟨h00, h01, h10, h11⟩
    fin_cases j <;> simp only [piTheta, controlProb] <;>
      apply mul_nonneg <;> linarith
  have hr (j : Fin 4) : 1 ≤ patternRay ε s j := by
    have hd := (admissiblePrivacyIncrement_pos ε hε).le
    change 0 ≤ privacyIncrement ε at hd
    unfold patternRay
    split_ifs <;> simp_all
  have hsum : (∑ j : Fin 4, piTheta θ p j) = 1 := by
    rw [Fin.sum_univ_four]
    change controlProb p * (1 - θ 0) + controlProb p * θ 0 +
      p * (1 - θ 1) + p * θ 1 = 1
    dsimp [controlProb]
    ring
  have hbound : 1 ≤ patternMass θ p ε s := by
    rw [← hsum]
    unfold patternMass
    exact Finset.sum_le_sum fun j _ => by
      simpa using mul_le_mul_of_nonneg_left (hr j) (hπ j)
  exact lt_of_lt_of_le (by norm_num) hbound

/-- For [the supplied quantities and conditions](hyp:p,s), the [pattern gradient](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:ε), these specify the stated inputs. -/
def patternGradient (p ε : ℝ) (s : Fin 14) : TrialParameter :=
  fun k =>
    if k = 0 then privacyIncrement ε * controlProb p *
      ((if patternContains s 1 then 1 else 0) -
       (if patternContains s 0 then 1 else 0))
    else privacyIncrement ε * p *
      ((if patternContains s 3 then 1 else 0) -
       (if patternContains s 2 then 1 else 0))
  -- @realizes g_S(derivative vector)

/-- For [the supplied quantities and conditions](hyp:j), the [staircase matrix](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:ε,α), these specify the stated inputs. -/
def staircaseMatrix (ε : ℝ) (α : StaircaseWeight) (j : Fin 4) : ℝ :=
  ∑ s : Fin 14, α s * patternRay ε s j
  -- @realizes B(four by fourteen ray matrix)

/-- the [staircase feasible](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:ε,α), these specify the stated inputs. -/
def staircaseFeasible (ε : ℝ) (α : StaircaseWeight) : Prop :=
  (∀ s, 0 ≤ α s) ∧ ∀ j, staircaseMatrix ε α j = 1
  -- @realizes \mathcal A_\varepsilon(nonnegative normalized weights)

/-- For [the supplied quantities and conditions](hyp:t), the [direction](goal) is the mathematical object specified below. -/
def direction (t : ℝ) : TrialParameter := fun k => if k = 0 then t else t + 1
  -- @realizes v(t)(unit contrast direction)

/-- For [the supplied quantities and conditions](hyp:p,s,t), the [projected gradient](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:ε), these specify the stated inputs. -/
def projectedGradient (p ε : ℝ) (s : Fin 14) (t : ℝ) : ℝ :=
  ∑ k : Fin 2, patternGradient p ε s k * direction t k

/-- For [the supplied quantities and conditions](hyp:p,s,t), the [pattern information](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:θ,ε), these specify the stated inputs. -/
def patternInformation (θ : TrialParameter) (p ε : ℝ) (s : Fin 14) (t : ℝ) : ℝ :=
  (projectedGradient p ε s t) ^ 2 / patternMass θ p ε s
  -- @realizes f_S(t)(directional contribution)

/-- For [the supplied quantities and conditions](hyp:p), the [information matrix](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:θ,ε,α), these specify the stated inputs. -/
def informationMatrix (θ : TrialParameter) (p ε : ℝ) (α : StaircaseWeight) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => ∑ s : Fin 14,
    α s * patternGradient p ε s a * patternGradient p ε s b /
      patternMass θ p ε s
  -- @realizes I_\theta(\alpha)(Fisher matrix)

-- keep: reusable public score primitive for later channel and mechanism comparisons
/-- For [the supplied quantities and conditions](hyp:p,s), the [output score](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:θ,ε), these specify the stated inputs. -/
def outputScore (θ : TrialParameter) (p ε : ℝ) (s : Fin 14) : TrialParameter :=
  fun k => patternGradient p ε s k / patternMass θ p ε s
  -- @realizes s_S^{\mathrm{out}}(\theta)(gradient over mass)

/-- For [the supplied quantities and conditions](hyp:p,s,t), the [projected score](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:θ,ε), these specify the stated inputs. -/
def projectedScore (θ : TrialParameter) (p ε : ℝ) (s : Fin 14) (t : ℝ) : ℝ :=
  projectedGradient p ε s t / patternMass θ p ε s
  -- @realizes \rho_S(\theta,t)(projected output score)

/-- For [the supplied quantities and conditions](hyp:p), the [information objective](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:t), these specify the stated inputs. For [the displayed quantities and conditions](hyp:θ,ε,α), these specify the stated inputs. -/
def informationObjective (θ : TrialParameter) (p ε : ℝ)
    (α : StaircaseWeight) (t : ℝ) : ℝ :=
  ∑ s : Fin 14, α s * patternInformation θ p ε s t
  -- @realizes F_\theta(\alpha,t)(directional information)

-- @node: def:staircase-saddle
/-- [The optimized Fisher-information value](goal) is determined by [the displayed parameters](hyp:θ,p,ε). -/
noncomputable def Jstar (θ : TrialParameter) (p ε : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ α : StaircaseWeight,
    staircaseFeasible ε α ∧
    z = sInf {y : ℝ | ∃ t : ℝ, y = informationObjective θ p ε α t}}
  -- @realizes J^*(\theta,p,\varepsilon)(max-min information)

/-- [The reciprocal optimized contrast variance](goal) is determined by [the displayed parameters](hyp:θ,p,ε). -/
noncomputable def Vstar (θ : TrialParameter) (p ε : ℝ) : ℝ :=
  (Jstar θ p ε)⁻¹
  -- @realizes V^*(\theta,p,\varepsilon)(reciprocal information)

-- @env: S2
variable {n : ℕ} {Z : Fin n → Type*} [∀ i, MeasurableSpace (Z i)]

/-- For the supplied quantities and conditions, the private history is the mathematical object specified below. [The Private History](goal) is determined by [the displayed parameters](hyp:i). -/
abbrev PrivateHistory (i : Fin n) := (j : {j : Fin n // j < i}) → Z j.1
  -- @realizes H_{i-1}(earlier release tuple)

/-- the [sequential kernel](goal) is the mathematical object specified below. -/
abbrev SequentialKernel := ∀ i : Fin n,
  Kernel (Fin 4 × PrivateHistory (Z := Z) i) (Z i)
  -- @realizes Q_i(history-dependent kernel)

-- @node: ass:fixed-privacy
/-- For [the supplied quantities and conditions](hyp:epsSeq), the [fixed privacy](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:ε), these specify the stated inputs. -/
def FixedPrivacy (epsSeq : ℕ → ℝ) (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ k, epsSeq k = ε
  -- @realizes \varepsilon(fixed positive budget)

-- @node: ass:sequential-ldp
/-- For [the supplied quantities and conditions](hyp:Z), the [sequential ldp](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. For [the displayed quantities and conditions](hyp:ε), these specify the stated inputs. -/
def SequentialLDP (ε : ℝ) (Q : SequentialKernel (Z := Z)) : Prop :=
  (∀ i, IsMarkovKernel (Q i)) ∧
  ∀ i A, MeasurableSet A →
    ∀ x x' h, Q i (x, h) A ≤ ENNReal.ofReal (Real.exp ε) * Q i (x', h) A
  -- @realizes \mathfrak Q^{\mathrm{seq}}_{n,\varepsilon}(LDP at every history)

-- @node: def:sequential-channels
/-- For [the supplied quantities and conditions](hyp:epsSeq), this sequential channels packages the stated mathematical data. For [the displayed quantities and conditions](hyp:Q), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:ε), these specify the stated inputs. -/
structure SequentialChannels (epsSeq : ℕ → ℝ) (ε : ℝ)
    (Q : SequentialKernel (Z := Z)) : Prop where
  fixed : FixedPrivacy epsSeq ε
  ldp : SequentialLDP (Z := Z) (epsSeq n) Q

-- @node: ass:pilot-diverges
/-- For [the supplied quantities and conditions](hyp:m), the [pilot diverges](goal) is the mathematical object specified below. -/
def PilotDiverges (m : ℕ → ℕ) : Prop :=
  Tendsto m atTop atTop -- @realizes m_n(diverging pilot)

-- @node: ass:pilot-sublinear
/-- For [the supplied quantities and conditions](hyp:m), the [pilot sublinear](goal) is the mathematical object specified below. -/
def PilotSublinear (m : ℕ → ℕ) : Prop :=
  Tendsto (fun k => (m k : ℝ) / k) atTop (nhds 0) ∧
  ∀ k ≥ 2, 1 ≤ m k ∧ m k < k
  -- @realizes m_n(sublinear pilot in 1,...,n-1)

end CausalSmith.Stat.LdpAteEfficiencySurface

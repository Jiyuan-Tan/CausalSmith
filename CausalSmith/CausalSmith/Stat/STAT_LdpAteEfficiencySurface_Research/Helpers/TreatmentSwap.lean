module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TFiveOutputUpperBound
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.CenteredR5Certificate

/-! # Treatment-arm swap symmetry for centered staircase designs -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Transpose the two-by-two treatment/outcome membership table of a staircase ray. For [the displayed inputs and conditions](hyp:s), [the stated result](goal) follows. -/
def swapTreatmentPattern (s : Fin 14) : Fin 14 :=
  Fin.ofNat 14 (((s.val + 1) % 4 * 4 + (s.val + 1) / 4) - 1)

/-- the [swapped support](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:K), these specify the stated inputs. -/
def swappedSupport (K : Finset (Fin 14)) : Finset (Fin 14) :=
  K.image swapTreatmentPattern

/-- Exchange the two treatment arms in the four-point input alphabet. [The stated result](goal) follows. -/
def swapTreatmentInput : Fin 4 → Fin 4
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | _ => 1

/-- the swap treatment weight is the mathematical object specified below. [The swap Treatment Weight](goal) is determined by [the displayed parameters](hyp:α). -/
def swapTreatmentWeight (α : StaircaseWeight) : StaircaseWeight :=
  fun s => α (swapTreatmentPattern s)

/-- [the swap treatment pattern involutive assertion](goal) holds. -/
lemma swapTreatmentPattern_involutive : Function.Involutive swapTreatmentPattern := by
  intro s
  fin_cases s <;> rfl

/-- [the swap treatment input involutive assertion](goal) holds. -/
lemma swapTreatmentInput_involutive : Function.Involutive swapTreatmentInput := by
  intro j
  fin_cases j <;> rfl

/-- Under [the supplied quantities and conditions](hyp:j), [the swap treatment input val assertion](goal) holds. -/
lemma swapTreatmentInput_val (j : Fin 4) :
    (swapTreatmentInput j).val = (j.val + 2) % 4 := by
  fin_cases j <;> decide

/-- the [swap treatment pattern equiv](goal) is the mathematical object specified below. -/
def swapTreatmentPatternEquiv : Fin 14 ≃ Fin 14 where
  toFun := swapTreatmentPattern
  invFun := swapTreatmentPattern
  left_inv := swapTreatmentPattern_involutive
  right_inv := swapTreatmentPattern_involutive

/-- the [swap treatment input equiv](goal) is the mathematical object specified below. -/
def swapTreatmentInputEquiv : Fin 4 ≃ Fin 4 where
  toFun := swapTreatmentInput
  invFun := swapTreatmentInput
  left_inv := swapTreatmentInput_involutive
  right_inv := swapTreatmentInput_involutive

/-- Under [the supplied quantities and conditions](hyp:s,j), [the pattern ray swap treatment assertion](goal) holds. -/
lemma patternRay_swapTreatment (ε : ℝ) (s : Fin 14) (j : Fin 4) :
    patternRay ε (swapTreatmentPattern s) (swapTreatmentInput j) = patternRay ε s j := by
  fin_cases s <;> fin_cases j <;>
    simp [swapTreatmentPattern, swapTreatmentInput, patternRay, patternContains,
      Nat.testBit]

/-- [the swap treatment weight involutive assertion](goal) holds. -/
lemma swapTreatmentWeight_involutive : Function.Involutive swapTreatmentWeight := by
  intro α
  funext s
  simp [swapTreatmentWeight, swapTreatmentPattern_involutive s]

/-- Under [the supplied quantities and conditions](hyp:j), [the staircase matrix swap treatment assertion](goal) holds. -/
lemma staircaseMatrix_swapTreatment (ε : ℝ) (α : StaircaseWeight) (j : Fin 4) :
    staircaseMatrix ε (swapTreatmentWeight α) j =
      staircaseMatrix ε α (swapTreatmentInput j) := by
  unfold staircaseMatrix swapTreatmentWeight
  rw [← swapTreatmentPatternEquiv.sum_comp
    (fun s => α s * patternRay ε s (swapTreatmentInput j))]
  apply Finset.sum_congr rfl
  intro s _
  change α (swapTreatmentPattern s) * patternRay ε s j =
    α (swapTreatmentPattern s) *
      patternRay ε (swapTreatmentPattern s) (swapTreatmentInput j)
  rw [patternRay_swapTreatment]

/-- [the staircase feasible swap treatment assertion](goal) holds. -/
lemma staircaseFeasible_swapTreatment (ε : ℝ) (α : StaircaseWeight) :
    staircaseFeasible ε (swapTreatmentWeight α) ↔ staircaseFeasible ε α := by
  constructor <;> intro h
  · constructor
    · intro s
      have := h.1 (swapTreatmentPattern s)
      simpa [swapTreatmentWeight, swapTreatmentPattern_involutive s] using this
    · intro j
      have hm := h.2 (swapTreatmentInput j)
      rw [staircaseMatrix_swapTreatment, swapTreatmentInput_involutive j] at hm
      exact hm
  · constructor
    · intro s
      exact h.1 (swapTreatmentPattern s)
    · intro j
      rw [staircaseMatrix_swapTreatment]
      exact h.2 (swapTreatmentInput j)

/-- [the staircase support swap treatment assertion](goal) holds. -/
lemma staircaseSupport_swapTreatment (α : StaircaseWeight) :
    staircaseSupport (swapTreatmentWeight α) = swappedSupport (staircaseSupport α) := by
  ext s
  simp only [staircaseSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    swappedSupport, Finset.mem_image]
  constructor
  · intro hs
    refine ⟨swapTreatmentPattern s, ?_, swapTreatmentPattern_involutive s⟩
    simpa [swapTreatmentWeight, swapTreatmentPattern_involutive s] using hs
  · rintro ⟨u, hu, rfl⟩
    simpa [swapTreatmentWeight, swapTreatmentPattern_involutive u] using hu

/-- Under [the supplied quantities and conditions](hyp:p,j), [the centered pi theta swap treatment assertion](goal) holds. -/
lemma centered_piTheta_swapTreatment (p : ℝ) (j : Fin 4) :
    piTheta (fun _ => (1 / 2 : ℝ)) p (swapTreatmentInput j) =
      piTheta (fun _ => (1 / 2 : ℝ)) (1 - p) j := by
  rw [centered_piTheta, centered_piTheta]
  rw [swapTreatmentInput_val]
  fin_cases j <;> norm_num <;> ring

/-- Under [the supplied quantities and conditions](hyp:p,s), [the centered pattern mass swap treatment assertion](goal) holds. -/
lemma centered_patternMass_swapTreatment (p ε : ℝ) (s : Fin 14) :
    patternMass (fun _ => (1 / 2 : ℝ)) p ε (swapTreatmentPattern s) =
      patternMass (fun _ => (1 / 2 : ℝ)) (1 - p) ε s := by
  unfold patternMass
  rw [← swapTreatmentInputEquiv.sum_comp
    (fun j => piTheta (fun _ => (1 / 2 : ℝ)) p j *
      patternRay ε (swapTreatmentPattern s) j)]
  apply Finset.sum_congr rfl
  intro j _
  change piTheta (fun _ => (1 / 2 : ℝ)) p (swapTreatmentInput j) *
      patternRay ε (swapTreatmentPattern s) (swapTreatmentInput j) = _
  rw [centered_piTheta_swapTreatment, patternRay_swapTreatment]

/-- Under [the supplied quantities and conditions](hyp:p,s), [the pattern gradient swap treatment assertion](goal) holds. -/
lemma patternGradient_swapTreatment (p ε : ℝ) (s : Fin 14) :
    patternGradient p ε (swapTreatmentPattern s) 0 =
        patternGradient (1 - p) ε s 1 ∧
      patternGradient p ε (swapTreatmentPattern s) 1 =
        patternGradient (1 - p) ε s 0 := by
  fin_cases s <;>
    simp [patternGradient, swapTreatmentPattern, patternContains, Nat.testBit,
      controlProb] <;> ring

/-- Under [the supplied quantities and conditions](hyp:p,t,s), [the projected gradient swap treatment assertion](goal) holds. -/
lemma projectedGradient_swapTreatment (p ε t : ℝ) (s : Fin 14) :
    projectedGradient p ε (swapTreatmentPattern s) t =
      -projectedGradient (1 - p) ε s (-1 - t) := by
  obtain ⟨h0, h1⟩ := patternGradient_swapTreatment p ε s
  simp [projectedGradient, direction, Fin.sum_univ_two, h0, h1]
  ring

/-- Under [the supplied quantities and conditions](hyp:p,t,s), [the centered pattern information swap treatment assertion](goal) holds. -/
lemma centered_patternInformation_swapTreatment (p ε t : ℝ) (s : Fin 14) :
    patternInformation (fun _ => (1 / 2 : ℝ)) p ε
        (swapTreatmentPattern s) t =
      patternInformation (fun _ => (1 / 2 : ℝ)) (1 - p) ε s (-1 - t) := by
  rw [patternInformation, patternInformation, centered_patternMass_swapTreatment,
    projectedGradient_swapTreatment]
  ring

/-- Under [the supplied quantities and conditions](hyp:p,t), [the centered information objective swap treatment assertion](goal) holds. -/
lemma centered_informationObjective_swapTreatment
    (p ε t : ℝ) (α : StaircaseWeight) :
    informationObjective (fun _ => (1 / 2 : ℝ)) p ε
        (swapTreatmentWeight α) t =
      informationObjective (fun _ => (1 / 2 : ℝ)) (1 - p) ε α (-1 - t) := by
  unfold informationObjective swapTreatmentWeight
  rw [← swapTreatmentPatternEquiv.sum_comp
    (fun s => α s * patternInformation
      (fun _ => (1 / 2 : ℝ)) (1 - p) ε s (-1 - t))]
  apply Finset.sum_congr rfl
  intro s _
  change α (swapTreatmentPattern s) *
      patternInformation (fun _ => (1 / 2 : ℝ)) p ε s t =
    α (swapTreatmentPattern s) *
      patternInformation (fun _ => (1 / 2 : ℝ)) (1 - p) ε
        (swapTreatmentPattern s) (-1 - t)
  rw [← centered_patternInformation_swapTreatment p ε t
    (swapTreatmentPattern s), swapTreatmentPattern_involutive]

/-- Under [the supplied quantities and conditions](hyp:p), [the centered profile set swap treatment assertion](goal) holds. -/
lemma centered_profileSet_swapTreatment (p ε : ℝ) (α : StaircaseWeight) :
    {u : ℝ | ∃ t : ℝ, u = informationObjective
      (fun _ => (1 / 2 : ℝ)) p ε (swapTreatmentWeight α) t} =
    {u : ℝ | ∃ t : ℝ, u = informationObjective
      (fun _ => (1 / 2 : ℝ)) (1 - p) ε α t} := by
  ext u
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨-1 - t, centered_informationObjective_swapTreatment p ε t α⟩
  · rintro ⟨t, rfl⟩
    refine ⟨-1 - t, ?_⟩
    rw [centered_informationObjective_swapTreatment]
    congr 2
    ring

/-- Under [the supplied quantities and conditions](hyp:p), [the centered jstar swap treatment assertion](goal) holds. -/
lemma centered_Jstar_swapTreatment (p ε : ℝ) :
    Jstar (fun _ => (1 / 2 : ℝ)) p ε =
      Jstar (fun _ => (1 / 2 : ℝ)) (1 - p) ε := by
  unfold Jstar
  congr 1
  ext z
  constructor
  · rintro ⟨α, hα, rfl⟩
    refine ⟨swapTreatmentWeight α,
      (staircaseFeasible_swapTreatment ε α).2 hα, ?_⟩
    have hs := congrArg sInf
      (centered_profileSet_swapTreatment (1 - p) ε α)
    convert hs.symm using 1 <;> ring
  · rintro ⟨α, hα, rfl⟩
    refine ⟨swapTreatmentWeight α,
      (staircaseFeasible_swapTreatment ε α).2 hα, ?_⟩
    exact (congrArg sInf
      (centered_profileSet_swapTreatment p ε α)).symm

/-- Under [the supplied quantities and conditions](hyp:p), [the centered vstar swap treatment assertion](goal) holds. -/
lemma centered_Vstar_swapTreatment (p ε : ℝ) :
    Vstar (fun _ => (1 / 2 : ℝ)) p ε =
      Vstar (fun _ => (1 / 2 : ℝ)) (1 - p) ε := by
  rw [Vstar, Vstar, centered_Jstar_swapTreatment]

variable {Z : Type*} [MeasurableSpace Z]

/-- the [swap treatment channel](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
def swapTreatmentChannel (Q : Kernel (Fin 4) Z) : Kernel (Fin 4) Z :=
  Q.comap swapTreatmentInput (measurable_of_finite _)

/-- Under [the supplied quantities and conditions](hyp:j), [the swap treatment channel apply assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
lemma swapTreatmentChannel_apply (Q : Kernel (Fin 4) Z) (j : Fin 4) :
    swapTreatmentChannel Q j = Q (swapTreatmentInput j) := rfl

/-- [the stationary ldp swap treatment assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,hQ), these specify the stated inputs. -/
lemma stationaryLDP_swapTreatment (ε : ℝ) (Q : Kernel (Fin 4) Z)
    (hQ : StationaryLDP ε Q) : StationaryLDP ε (swapTreatmentChannel Q) := by
  refine ⟨⟨fun j => hQ.1.isProbabilityMeasure (swapTreatmentInput j)⟩, ?_⟩
  intro A hA j k
  exact hQ.2 A hA (swapTreatmentInput j) (swapTreatmentInput k)

/-- [the dominating measure swap treatment assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
lemma dominatingMeasure_swapTreatment (Q : Kernel (Fin 4) Z) :
    dominatingMeasure (swapTreatmentChannel Q) = dominatingMeasure Q := by
  unfold dominatingMeasure
  rw [← swapTreatmentInputEquiv.sum_comp (fun j => Q j)]
  rfl

/-- Under [the supplied quantities and conditions](hyp:j), [the channel density swap treatment assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
lemma channelDensity_swapTreatment (Q : Kernel (Fin 4) Z) (j : Fin 4) :
    channelDensity (swapTreatmentChannel Q) j =
      channelDensity Q (swapTreatmentInput j) := by
  funext z
  simp only [channelDensity, swapTreatmentChannel_apply,
    dominatingMeasure_swapTreatment]

/-- Under [the supplied quantities and conditions](hyp:p), [the centered channel output density swap treatment assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,z), these specify the stated inputs. -/
lemma centered_channelOutputDensity_swapTreatment (p : ℝ)
    (Q : Kernel (Fin 4) Z) (z : Z) :
    channelOutputDensity (fun _ => (1 / 2 : ℝ)) (1 - p)
        (swapTreatmentChannel Q) z =
      channelOutputDensity (fun _ => (1 / 2 : ℝ)) p Q z := by
  unfold channelOutputDensity
  rw [← swapTreatmentInputEquiv.sum_comp
    (fun j => piTheta (fun _ => (1 / 2 : ℝ)) p j * channelDensity Q j z)]
  apply Finset.sum_congr rfl
  intro j _
  rw [channelDensity_swapTreatment]
  change piTheta (fun _ => (1 / 2 : ℝ)) (1 - p) j *
      channelDensity Q (swapTreatmentInput j) z = _
  rw [← centered_piTheta_swapTreatment]
  rfl

/-- Under [the supplied quantities and conditions](hyp:p), [the centered channel output density swap treatment inv two assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,z), these specify the stated inputs. -/
lemma centered_channelOutputDensity_swapTreatment_invTwo (p : ℝ)
    (Q : Kernel (Fin 4) Z) (z : Z) :
    channelOutputDensity (fun _ => (2 : ℝ)⁻¹) (1 - p)
        (swapTreatmentChannel Q) z =
      channelOutputDensity (fun _ => (2 : ℝ)⁻¹) p Q z := by
  convert centered_channelOutputDensity_swapTreatment p Q z <;> norm_num

/-- Under [the supplied quantities and conditions](hyp:p,j), [the input derivative swap treatment assertion](goal) holds. -/
lemma inputDerivative_swapTreatment (p : ℝ) (j : Fin 4) :
    inputDerivative (1 - p) j 0 = inputDerivative p (swapTreatmentInput j) 1 ∧
      inputDerivative (1 - p) j 1 = inputDerivative p (swapTreatmentInput j) 0 := by
  fin_cases j <;> simp [inputDerivative, swapTreatmentInput, controlProb] <;> ring

/-- Under [the supplied quantities and conditions](hyp:p), [the channel derivative density swap treatment assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,z), these specify the stated inputs. -/
lemma channelDerivativeDensity_swapTreatment (p : ℝ) (Q : Kernel (Fin 4) Z)
    (z : Z) :
    channelDerivativeDensity (1 - p) (swapTreatmentChannel Q) 0 z =
        channelDerivativeDensity p Q 1 z ∧
      channelDerivativeDensity (1 - p) (swapTreatmentChannel Q) 1 z =
        channelDerivativeDensity p Q 0 z := by
  constructor
  · unfold channelDerivativeDensity
    rw [← swapTreatmentInputEquiv.sum_comp
      (fun j => inputDerivative p j 1 * channelDensity Q j z)]
    apply Finset.sum_congr rfl
    intro j _
    rw [channelDensity_swapTreatment]
    change inputDerivative (1 - p) j 0 *
      channelDensity Q (swapTreatmentInput j) z =
        inputDerivative p (swapTreatmentInput j) 1 *
          channelDensity Q (swapTreatmentInput j) z
    rw [(inputDerivative_swapTreatment p j).1]
  · unfold channelDerivativeDensity
    rw [← swapTreatmentInputEquiv.sum_comp
      (fun j => inputDerivative p j 0 * channelDensity Q j z)]
    apply Finset.sum_congr rfl
    intro j _
    rw [channelDensity_swapTreatment]
    change inputDerivative (1 - p) j 1 *
      channelDensity Q (swapTreatmentInput j) z =
        inputDerivative p (swapTreatmentInput j) 0 *
          channelDensity Q (swapTreatmentInput j) z
    rw [(inputDerivative_swapTreatment p j).2]

/-- For [the supplied quantities and conditions](hyp:k), the [swap treatment parameter](goal) is the mathematical object specified below. -/
def swapTreatmentParameter (k : Fin 2) : Fin 2 := if k = 0 then 1 else 0

/-- the [swap treatment matrix](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:I), these specify the stated inputs. -/
def swapTreatmentMatrix (I : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => I (swapTreatmentParameter a) (swapTreatmentParameter b)

/-- Under [the supplied quantities and conditions](hyp:p), [the channel derivative density swap treatment zero assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
lemma channelDerivativeDensity_swapTreatment_zero (p : ℝ) (Q : Kernel (Fin 4) Z) :
    channelDerivativeDensity (1 - p) (swapTreatmentChannel Q) 0 =
      channelDerivativeDensity p Q 1 := by
  funext z
  exact (channelDerivativeDensity_swapTreatment p Q z).1

/-- Under [the supplied quantities and conditions](hyp:p), [the channel derivative density swap treatment one assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
lemma channelDerivativeDensity_swapTreatment_one (p : ℝ) (Q : Kernel (Fin 4) Z) :
    channelDerivativeDensity (1 - p) (swapTreatmentChannel Q) 1 =
      channelDerivativeDensity p Q 0 := by
  funext z
  exact (channelDerivativeDensity_swapTreatment p Q z).2

/-- Under [the supplied quantities and conditions](hyp:p), [the channel fisher info swap treatment assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
lemma channelFisherInfo_swapTreatment (p : ℝ) (Q : Kernel (Fin 4) Z) :
    channelFisherInfo (fun _ => (1 / 2 : ℝ)) (1 - p)
        (swapTreatmentChannel Q) =
      swapTreatmentMatrix
        (channelFisherInfo (fun _ => (1 / 2 : ℝ)) p Q) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [channelFisherInfo, swapTreatmentMatrix, swapTreatmentParameter,
      dominatingMeasure_swapTreatment,
      channelDerivativeDensity_swapTreatment_zero,
      channelDerivativeDensity_swapTreatment_one] <;>
    apply MeasureTheory.integral_congr_ae <;>
    filter_upwards with z <;>
    rw [centered_channelOutputDensity_swapTreatment_invTwo]

/-- Under [the supplied quantities and conditions](hyp:p), [the centered output law swap treatment assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
lemma centered_outputLaw_swapTreatment (p : ℝ) (Q : Kernel (Fin 4) Z) :
    outputLaw (fun _ => (1 / 2 : ℝ)) (1 - p) (swapTreatmentChannel Q) =
      outputLaw (fun _ => (1 / 2 : ℝ)) p Q := by
  unfold outputLaw
  rw [← swapTreatmentInputEquiv.sum_comp
    (fun j => ENNReal.ofReal (piTheta (fun _ => (1 / 2 : ℝ)) p j) • Q j)]
  apply Finset.sum_congr rfl
  intro j _
  change ENNReal.ofReal (piTheta (fun _ => (1 / 2 : ℝ)) (1 - p) j) •
      Q (swapTreatmentInput j) = _
  rw [← centered_piTheta_swapTreatment]
  rfl

/-- Under [the supplied quantities and conditions](hyp:p), [the centered output cardinality swap treatment assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q), these specify the stated inputs. -/
lemma centered_outputCardinality_swapTreatment (p : ℝ) (Q : Kernel (Fin 4) Z) :
    outputCardinality (fun _ => (1 / 2 : ℝ)) (1 - p)
        (swapTreatmentChannel Q) =
      outputCardinality (fun _ => (1 / 2 : ℝ)) p Q := by
  classical
  unfold outputCardinality
  split <;> simp_all only [centered_outputLaw_swapTreatment]

/-- For [the supplied quantities and conditions](hyp:v), the [reflect treatment parameter](goal) is the mathematical object specified below. -/
def reflectTreatmentParameter (v : TrialParameter) : TrialParameter :=
  fun k => -v (swapTreatmentParameter k)

-- keep: reusable treatment-symmetry API for companion mechanism results
/-- [the reflect treatment parameter involutive assertion](goal) holds. -/
lemma reflectTreatmentParameter_involutive :
    Function.Involutive reflectTreatmentParameter := by
  intro v
  funext k
  fin_cases k <;> simp [reflectTreatmentParameter, swapTreatmentParameter]

/-- [the swap treatment matrix mul vec assertion](goal) holds. For [the displayed quantities and conditions](hyp:I,v,k), these specify the stated inputs. -/
lemma swapTreatmentMatrix_mulVec (I : Matrix (Fin 2) (Fin 2) ℝ)
    (v : TrialParameter) (k : Fin 2) :
    (swapTreatmentMatrix I).mulVec (reflectTreatmentParameter v) k =
      -(I.mulVec v (swapTreatmentParameter k)) := by
  fin_cases k <;>
    simp [swapTreatmentMatrix, reflectTreatmentParameter, swapTreatmentParameter,
      Matrix.mulVec, Fin.sum_univ_two] <;> ring

/-- Under [the supplied quantities and conditions](hyp:k), [the neg contrast vector swap assertion](goal) holds. -/
lemma neg_contrastVector_swap (k : Fin 2) :
    -contrastVector (swapTreatmentParameter k) = contrastVector k := by
  fin_cases k <;> simp [contrastVector, swapTreatmentParameter]

/-- [the contrast in range swap treatment assertion](goal) holds. For [the displayed quantities and conditions](hyp:I), these specify the stated inputs. -/
lemma contrastInRange_swapTreatment (I : Matrix (Fin 2) (Fin 2) ℝ) :
    contrastInRange (swapTreatmentMatrix I) ↔ contrastInRange I := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨reflectTreatmentParameter v, ?_⟩
    funext k
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    fin_cases k <;>
      simp [swapTreatmentMatrix, reflectTreatmentParameter, swapTreatmentParameter,
        Matrix.mulVec, Fin.sum_univ_two, contrastVector] at h0 h1 ⊢ <;> linarith
  · rintro ⟨v, hv⟩
    refine ⟨reflectTreatmentParameter v, ?_⟩
    funext k
    rw [swapTreatmentMatrix_mulVec, hv, neg_contrastVector_swap]

/-- Under [the supplied quantities and conditions](hyp:v), [the contrast pairing reflect assertion](goal) holds. -/
lemma contrastPairing_reflect (v : TrialParameter) :
    ∑ k : Fin 2, contrastVector k * reflectTreatmentParameter v k =
      ∑ k : Fin 2, contrastVector k * v k := by
  simp [contrastVector, reflectTreatmentParameter, swapTreatmentParameter,
    Fin.sum_univ_two]

/-- [the contrast solution values swap treatment assertion](goal) holds. For [the displayed quantities and conditions](hyp:I), these specify the stated inputs. -/
lemma contrastSolutionValues_swapTreatment (I : Matrix (Fin 2) (Fin 2) ℝ) :
    {u : ℝ | ∃ v : TrialParameter,
      (swapTreatmentMatrix I).mulVec v = contrastVector ∧
      u = ∑ k : Fin 2, contrastVector k * v k} =
    {u : ℝ | ∃ v : TrialParameter, I.mulVec v = contrastVector ∧
      u = ∑ k : Fin 2, contrastVector k * v k} := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨reflectTreatmentParameter v, ?_, contrastPairing_reflect v |>.symm⟩
    funext k
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    fin_cases k <;>
      simp [swapTreatmentMatrix, reflectTreatmentParameter, swapTreatmentParameter,
        Matrix.mulVec, Fin.sum_univ_two, contrastVector] at h0 h1 ⊢ <;> linarith
  · rintro ⟨v, hv, rfl⟩
    refine ⟨reflectTreatmentParameter v, ?_, contrastPairing_reflect v |>.symm⟩
    funext k
    rw [swapTreatmentMatrix_mulVec, hv, neg_contrastVector_swap]

/-- [the contrast variance swap treatment assertion](goal) holds. For [the displayed quantities and conditions](hyp:I), these specify the stated inputs. -/
lemma contrastVariance_swapTreatment (I : Matrix (Fin 2) (Fin 2) ℝ) :
    contrastVariance (swapTreatmentMatrix I) = contrastVariance I := by
  classical
  unfold contrastVariance
  by_cases h : contrastInRange I
  · have hs : contrastInRange (swapTreatmentMatrix I) :=
      (contrastInRange_swapTreatment I).2 h
    rw [if_pos h, if_pos hs, contrastSolutionValues_swapTreatment]
  · have hs : ¬ contrastInRange (swapTreatmentMatrix I) := by
      simpa [contrastInRange_swapTreatment I] using h
    rw [if_neg h, if_neg hs]

end CausalSmith.Stat.LdpAteEfficiencySurface

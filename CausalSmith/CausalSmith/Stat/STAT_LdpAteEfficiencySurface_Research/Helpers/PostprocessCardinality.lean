module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Refinement
public import Causalean.Mathlib.MeasureTheory.FiniteAtomicMeasure

/-! # Output cardinality under a singular postprocessing refinement

Positive active staircase rays whose postprocessing laws are pairwise mutually
singular require distinct positive-mass output atoms.  The argument works for
arbitrary measurable structures on a finite output type and returns the
definitional infinite bound for nonfinite output types.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory

-- @node: postprocess_row_ac_input
/-- [the postprocess row ac input assertion](goal) holds. For [the displayed quantities and conditions](hyp:K,hK,Q,hfactor,s,hs), these specify the stated inputs. -/
lemma postprocess_row_ac_input
    {Z : Type*} [MeasurableSpace Z]
    (ε : ℝ) (α : StaircaseWeight) (K : Kernel (Fin 14) Z)
    (hK : IsMarkovKernel K) (Q : Kernel (Fin 4) Z)
    (hfactor : Q = K.comp (staircaseChannel ε α))
    (s : Fin 14) (hs : 0 < α s) : K s ≪ Q 0 := by
  letI : IsMarkovKernel K := hK
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hQA
  rw [hfactor, Kernel.comp_apply' _ _ _ hA, lintegral_fintype] at hQA
  have hsum : ∑ u : Fin 14,
      K u A * (staircaseChannel ε α) 0 {u} = 0 := hQA
  have hterm : K s A * (staircaseChannel ε α) 0 {s} = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ zero_le)).mp hsum s
      (Finset.mem_univ s)
  have hT : (staircaseChannel ε α) 0 {s} ≠ 0 := by
    change (Measure.count.withDensity (fun u : Fin 14 ↦
      ENNReal.ofReal (α u * patternRay ε u 0))) {s} ≠ 0
    simp [withDensity_apply _ (measurableSet_singleton s)]
    have hr : 0 < patternRay ε s 0 := by
      simp only [patternRay, privacyIncrement, privacyRatio]
      split <;> simp_all <;> positivity
    exact mul_pos hs hr
  exact (mul_eq_zero.mp hterm).resolve_right hT

-- @node: input_zero_ac_outputLaw
/-- [the input zero ac output law assertion](goal) holds. For [the displayed quantities and conditions](hyp:p,Q,hpi), these specify the stated inputs. -/
lemma input_zero_ac_outputLaw
    {Z : Type*} [MeasurableSpace Z]
    (θ : TrialParameter) (p : ℝ) (Q : Kernel (Fin 4) Z)
    (hpi : 0 < piTheta θ p 0) : Q 0 ≪ outputLaw θ p Q := by
  apply Measure.AbsolutelyContinuous.mk
  intro A _ hout
  have hsum : ∑ j : Fin 4,
      ENNReal.ofReal (piTheta θ p j) * Q j A = 0 := by
    simpa only [outputLaw, Measure.coe_finsetSum, Measure.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hout
  have hterm : ENNReal.ofReal (piTheta θ p 0) * Q 0 A = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ zero_le)).mp hsum 0
      (Finset.mem_univ 0)
  have hcoef : ENNReal.ofReal (piTheta θ p 0) ≠ 0 := by simp [hpi]
  exact (mul_eq_zero.mp hterm).resolve_left hcoef

-- @node: active_card_le_outputCardinality_of_pairwise_singular
/-- the active card le output cardinality of pairwise singular assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hpos,hK,hfactor,hsing), [the active card le output Cardinality of pairwise singular](goal).

Under the stated assumptions, the active card le output Cardinality of pairwise singular. -/
lemma active_card_le_outputCardinality_of_pairwise_singular
    {Z : Type*} [MeasurableSpace Z]
    (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (A : Finset (Fin 14)) (α : StaircaseWeight)
    (hpos : ∀ s ∈ A, 0 < α s)
    (K : Kernel (Fin 14) Z) (hK : IsMarkovKernel K)
    (Q : Kernel (Fin 4) Z)
    (hfactor : Q = K.comp (staircaseChannel ε α))
    (hsing : ∀ s ∈ A, ∀ u ∈ A, s ≠ u → K s ⟂ₘ K u) :
    (A.card : ℕ∞) ≤ outputCardinality θ p Q := by
  have hpi : 0 < piTheta θ p 0 := by
    rcases hp with ⟨hp0, hp1⟩
    rcases hθ with ⟨h00, h01, h10, h11⟩
    simp only [piTheta, controlProb]
    exact mul_pos (by linarith) (by linarith)
  have hac (s : Fin 14) (hs : s ∈ A) : K s ≪ outputLaw θ p Q :=
    (postprocess_row_ac_input ε α K hK Q hfactor s (hpos s hs)).trans
      (input_zero_ac_outputLaw θ p Q hpi)
  unfold outputCardinality
  split_ifs with hfinite
  · letI := hfinite
    letI : IsMarkovKernel K := hK
    exact Causalean.Mathlib.MeasureTheory.pairwise_singular_card_le_positive_atoms
      A (fun s ↦ K s)
      (outputLaw θ p Q) hac hsing
  · exact le_top

end CausalSmith.Stat.LdpAteEfficiencySurface

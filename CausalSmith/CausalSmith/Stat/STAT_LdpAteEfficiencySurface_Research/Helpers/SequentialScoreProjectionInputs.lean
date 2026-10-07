module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialBayesOrdering
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialSuccessor

/-! # Paper inputs for measurable-statistic score projection -/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- A full transcript mixture derivative vanishes wherever its positive-weight
finite-mixture density vanishes. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,theta,v,p,n,hp,htheta,z,hz), these specify the stated inputs. -/
lemma transcriptMixtureRealDerivative_eq_zero_of_density_eq_zero
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (theta v : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (htheta : InteriorMeans theta)
    (z : Transcript (Z n))
    (hz : transcriptMixtureRealDensity P theta p n z = 0) :
    transcriptMixtureRealDerivative P theta v p n z = 0 := by
  have hterms : ∀ x : Fin n → Fin 4,
      inputPathProbability theta p x * transcriptComponentRealDensity P n x z = 0 := by
    have hnonneg : ∀ x ∈ (Finset.univ : Finset (Fin n → Fin 4)),
        0 ≤ inputPathProbability theta p x * transcriptComponentRealDensity P n x z := by
      intro x hx
      exact mul_nonneg (inputPathProbability_pos_of_interior theta p hp htheta x).le
        ENNReal.toReal_nonneg
    exact fun x => (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz x (Finset.mem_univ x)
  unfold transcriptMixtureRealDerivative
  apply Finset.sum_eq_zero
  intro x hx
  have hcomponent : transcriptComponentRealDensity P n x z = 0 := by
    have hprob := inputPathProbability_pos_of_interior theta p hp htheta x
    exact (mul_eq_zero.mp (hterms x)).resolve_left (ne_of_gt hprob)
  rw [hcomponent, mul_zero]

/-- The raw quotient defining the full transcript score agrees with the guarded
zero convention used by score projection. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,theta,v,p,n,hp,htheta,z), these specify the stated inputs. -/
lemma conditionalTranscriptDirectionalScore_eq_guarded
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (theta v : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (htheta : InteriorMeans theta)
    (z : Transcript (Z n)) :
    conditionalTranscriptDirectionalScore P theta v p n z =
      if 0 < transcriptMixtureRealDensity P theta p n z then
        transcriptMixtureRealDerivative P theta v p n z /
          transcriptMixtureRealDensity P theta p n z
      else 0 := by
  unfold conditionalTranscriptDirectionalScore
  split_ifs with hpos
  · rfl
  · have hnonneg := transcriptMixtureRealDensity_nonneg P theta p n hp htheta z
    have hz : transcriptMixtureRealDensity P theta p n z = 0 :=
      le_antisymm (le_of_not_gt hpos) hnonneg
    rw [hz, transcriptMixtureRealDerivative_eq_zero_of_density_eq_zero
      P theta v p n hp htheta z hz, zero_div]

/-- Prefix finite-mixture densities are nonnegative under interior parameters. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,theta,p,n,k,hk,hp,htheta,h), these specify the stated inputs. -/
lemma transcriptPrefixMixtureRealDensity_nonneg
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (theta : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n)
    (hp : InteriorAssignment p) (htheta : InteriorMeans theta)
    (h : History (Z n) k hk) :
    0 ≤ transcriptPrefixMixtureRealDensity P theta p n k hk h := by
  unfold transcriptPrefixMixtureRealDensity
  exact Finset.sum_nonneg fun x _ => mul_nonneg
    (inputPathProbability_pos_of_interior theta p hp htheta x).le ENNReal.toReal_nonneg

/-- A prefix mixture derivative vanishes wherever its positive-weight
finite-mixture density vanishes. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,theta,v,p,n,k,hk,hp,htheta,h,hz), these specify the stated inputs. -/
lemma transcriptPrefixMixtureRealDerivative_eq_zero_of_density_eq_zero
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (theta v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n)
    (hp : InteriorAssignment p) (htheta : InteriorMeans theta)
    (h : History (Z n) k hk)
    (hz : transcriptPrefixMixtureRealDensity P theta p n k hk h = 0) :
    transcriptPrefixMixtureRealDerivative P theta v p n k hk h = 0 := by
  have hterms : ∀ x : Fin n → Fin 4,
      inputPathProbability theta p x *
        transcriptPrefixComponentRealDensity P n k hk x h = 0 := by
    have hnonneg : ∀ x ∈ (Finset.univ : Finset (Fin n → Fin 4)),
        0 ≤ inputPathProbability theta p x *
          transcriptPrefixComponentRealDensity P n k hk x h := by
      intro x hx
      exact mul_nonneg (inputPathProbability_pos_of_interior theta p hp htheta x).le
        ENNReal.toReal_nonneg
    exact fun x => (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz x (Finset.mem_univ x)
  unfold transcriptPrefixMixtureRealDerivative
  apply Finset.sum_eq_zero
  intro x hx
  have hcomponent : transcriptPrefixComponentRealDensity P n k hk x h = 0 := by
    have hprob := inputPathProbability_pos_of_interior theta p hp htheta x
    exact (mul_eq_zero.mp (hterms x)).resolve_left (ne_of_gt hprob)
  rw [hcomponent, mul_zero]

/-- The raw quotient defining a prefix score agrees with the guarded zero
convention used by score projection. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,theta,v,p,n,k,hk,hp,htheta,h), these specify the stated inputs. -/
lemma conditionalTranscriptPrefixDirectionalScore_eq_guarded
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (theta v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n)
    (hp : InteriorAssignment p) (htheta : InteriorMeans theta)
    (h : History (Z n) k hk) :
    conditionalTranscriptPrefixDirectionalScore P theta v p n k hk h =
      if 0 < transcriptPrefixMixtureRealDensity P theta p n k hk h then
        transcriptPrefixMixtureRealDerivative P theta v p n k hk h /
          transcriptPrefixMixtureRealDensity P theta p n k hk h
      else 0 := by
  unfold conditionalTranscriptPrefixDirectionalScore
  split_ifs with hpos
  · rfl
  · have hnonneg := transcriptPrefixMixtureRealDensity_nonneg
      P theta p n k hk hp htheta h
    have hz : transcriptPrefixMixtureRealDensity P theta p n k hk h = 0 :=
      le_antisymm (le_of_not_gt hpos) hnonneg
    rw [hz, transcriptPrefixMixtureRealDerivative_eq_zero_of_density_eq_zero
      P theta v p n k hk hp htheta h hz, zero_div]

end CausalSmith.Stat.LdpAteEfficiencySurface

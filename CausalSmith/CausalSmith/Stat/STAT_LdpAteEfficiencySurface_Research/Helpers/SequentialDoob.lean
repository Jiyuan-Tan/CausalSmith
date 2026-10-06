module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialGlobalScore
public import Causalean.Stat.DoobInformation

/-! # Doob decomposition of the sequential transcript score

This file equips a full released transcript with its coordinate-prefix filtration and
instantiates the generic finite-horizon Doob information decomposition for the paper's
global finite-mixture score.  Identifying the conditional expectations with the explicit
prefix scores is kept separate until the score-projection substrate is available.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Kernel.FiniteSequence
open scoped BigOperators

/-- The prefix filtration on a length-`n` transcript is generated at time `k` by the
coordinates whose indices are strictly below `k`. [The stated result](goal) follows. -/
def transcriptPrefixFiltration {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)] :
    Filtration ℕ (inferInstance : MeasurableSpace (Transcript Z)) where
  seq k := ⨆ i : Fin n, ⨆ _h : i.val < k,
    MeasurableSpace.comap (fun z : Transcript Z ↦ z i) inferInstance
  mono' i j hij := by
    apply iSup₂_le
    intro a ha
    exact le_iSup_of_le a (le_iSup_of_le (lt_of_lt_of_le ha hij) le_rfl)
  le' k := by
    apply iSup₂_le
    intro i hi
    exact (measurable_pi_apply i).comap_le

/-- [the transcript prefix filtration zero assertion](goal) holds. -/
lemma transcriptPrefixFiltration_zero {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)] :
    transcriptPrefixFiltration (Z := Z) 0 = ⊥ := by
  apply le_antisymm
  · change (⨆ i : Fin n, ⨆ _h : i.val < 0,
      MeasurableSpace.comap (fun z : Transcript Z ↦ z i) inferInstance) ≤ ⊥
    apply iSup₂_le
    intro i hi
    exact (Nat.not_lt_zero _ hi).elim
  · exact bot_le

/-- [the transcript prefix filtration terminal assertion](goal) holds. -/
lemma transcriptPrefixFiltration_terminal {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)] :
    transcriptPrefixFiltration (Z := Z) n =
      (inferInstance : MeasurableSpace (Transcript Z)) := by
  apply le_antisymm (Filtration.le _ _)
  change (⨆ i : Fin n,
      MeasurableSpace.comap (fun z : Transcript Z ↦ z i) inferInstance) ≤
    (⨆ i : Fin n, ⨆ _h : i.val < n,
      MeasurableSpace.comap (fun z : Transcript Z ↦ z i) inferInstance)
  apply iSup_le
  intro i
  exact le_iSup_of_le i (le_iSup_of_le i.isLt le_rfl)

/-- The coordinate-prefix filtration agrees with the sigma-algebra pulled back by the
explicit prefix map.  This is the bridge needed to apply measurable-statistic score
projection to the Doob increments. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:hk), these specify the stated inputs. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma transcriptPrefixFiltration_eq_comap {n k : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)] (hk : k ≤ n) :
    transcriptPrefixFiltration (Z := Z) k =
      MeasurableSpace.comap (transcriptPrefix (Z := Z) hk)
        (inferInstance : MeasurableSpace (History Z k hk)) := by
  apply le_antisymm
  · apply iSup₂_le
    intro i hi
    let j : Fin k := ⟨i.val, hi⟩
    have hij : Fin.castLE hk j = i := Fin.ext (by rfl)
    rw [← hij]
    have hj : Measurable (fun h : History Z k hk ↦ h j) := measurable_pi_apply j
    change MeasurableSpace.comap
        (fun z : Transcript Z ↦ (transcriptPrefix (Z := Z) hk z) j) inferInstance ≤
      MeasurableSpace.comap (transcriptPrefix (Z := Z) hk) inferInstance
    rw [show (fun z : Transcript Z ↦ (transcriptPrefix (Z := Z) hk z) j) =
      (fun h : History Z k hk ↦ h j) ∘ transcriptPrefix (Z := Z) hk by rfl]
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (g := transcriptPrefix (Z := Z) hk) hj.comap_le
  · rw [show (inferInstance : MeasurableSpace (History Z k hk)) =
        ⨆ j : Fin k, MeasurableSpace.comap (fun h : History Z k hk ↦ h j) inferInstance by
          rfl]
    rw [MeasurableSpace.comap_iSup]
    apply iSup_le
    intro j
    rw [MeasurableSpace.comap_comp]
    exact le_iSup_of_le (Fin.castLE hk j) (le_iSup_of_le j.isLt le_rfl)

/-- At the terminal time, conditioning the global transcript score on the prefix filtration returns the score itself. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the cond Exp global Score terminal](goal).

Under the stated assumptions, the cond Exp global Score terminal. -/
lemma condExp_globalScore_terminal {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    (transcriptLaw P θ p n)[conditionalTranscriptDirectionalScore P θ v p n |
        transcriptPrefixFiltration (Z := Z n) n] =ᵐ[transcriptLaw P θ p n]
      conditionalTranscriptDirectionalScore P θ v p n := by
  letI : IsProbabilityMeasure (transcriptLaw P θ p n) :=
    transcriptLaw_isProbability P θ p hp hθ n
  rw [transcriptPrefixFiltration_terminal]
  exact Filter.Eventually.of_forall (fun z ↦ congrFun (condExp_of_stronglyMeasurable le_rfl
    (measurable_conditionalTranscriptDirectionalScore P θ v p n).stronglyMeasurable
    (conditionalTranscriptDirectionalScore_integrable P θ v p n hp hθ)) z)

/-- At time zero, conditioning the centered global transcript score on the prefix filtration is zero. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the cond Exp global Score initial](goal).

Under the stated assumptions, the cond Exp global Score initial. -/
lemma condExp_globalScore_initial {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    (transcriptLaw P θ p n)[conditionalTranscriptDirectionalScore P θ v p n |
        transcriptPrefixFiltration (Z := Z n) 0] =ᵐ[transcriptLaw P θ p n]
      (0 : Transcript (Z n) → ℝ) := by
  letI : IsProbabilityMeasure (transcriptLaw P θ p n) :=
    transcriptLaw_isProbability P θ p hp hθ n
  rw [transcriptPrefixFiltration_zero, condExp_bot]
  rw [integral_conditionalTranscriptDirectionalScore_eq_zero P θ v p n hp hθ]
  rfl

/-- The paper's global transcript Fisher information is the sum of the squared Doob prefix increments. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the global Score fisher eq doob sum](goal).

Under the stated assumptions, the global Score fisher eq doob sum. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma globalScore_fisher_eq_doob_sum {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    (∫ z, conditionalTranscriptDirectionalScore P θ v p n z ^ 2
        ∂transcriptLaw P θ p n) =
      ∑ k ∈ Finset.range n, ∫ z,
        Causalean.Stat.DoobInformation.increment
          (transcriptLaw P θ p n) (transcriptPrefixFiltration (Z := Z n))
          (conditionalTranscriptDirectionalScore P θ v p n) k z ^ 2
        ∂transcriptLaw P θ p n := by
  letI : IsProbabilityMeasure (transcriptLaw P θ p n) :=
    transcriptLaw_isProbability P θ p hp hθ n
  exact Causalean.Stat.DoobInformation.fisher_eq_sum
    (transcriptPrefixFiltration (Z := Z n))
    (conditionalTranscriptDirectionalScore P θ v p n)
    (conditionalTranscriptDirectionalScore_memLp_two P θ v p n hp hθ) n
    (condExp_globalScore_terminal P θ v p n hp hθ)
    (condExp_globalScore_initial P θ v p n hp hθ)

/-- Every prefix increment of the global transcript score is square-integrable. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the global Score doob Increment mem Lp two](goal).

Under the stated assumptions, the global Score doob Increment mem Lp two. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma globalScore_doobIncrement_memLp_two {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n k : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    MemLp (Causalean.Stat.DoobInformation.increment
      (transcriptLaw P θ p n) (transcriptPrefixFiltration (Z := Z n))
      (conditionalTranscriptDirectionalScore P θ v p n) k) 2
      (transcriptLaw P θ p n) := by
  letI : IsProbabilityMeasure (transcriptLaw P θ p n) :=
    transcriptLaw_isProbability P θ p hp hθ n
  exact Causalean.Stat.DoobInformation.increment_memLp
    (transcriptPrefixFiltration (Z := Z n))
    (conditionalTranscriptDirectionalScore P θ v p n)
    (conditionalTranscriptDirectionalScore_memLp_two P θ v p n hp hθ) k

/-- Every prefix increment of the global transcript score has conditional mean zero given the preceding prefix sigma-algebra. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the cond Exp global Score doob Increment zero](goal).

Under the stated assumptions, the cond Exp global Score doob Increment zero. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma condExp_globalScore_doobIncrement_zero {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n k : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    (transcriptLaw P θ p n)[
        Causalean.Stat.DoobInformation.increment
          (transcriptLaw P θ p n) (transcriptPrefixFiltration (Z := Z n))
          (conditionalTranscriptDirectionalScore P θ v p n) k |
        transcriptPrefixFiltration (Z := Z n) k] =ᵐ[transcriptLaw P θ p n]
      (0 : Transcript (Z n) → ℝ) := by
  letI : IsProbabilityMeasure (transcriptLaw P θ p n) :=
    transcriptLaw_isProbability P θ p hp hθ n
  exact Causalean.Stat.DoobInformation.increment_condExp_zero
    (transcriptPrefixFiltration (Z := Z n))
    (conditionalTranscriptDirectionalScore P θ v p n)
    (conditionalTranscriptDirectionalScore_memLp_two P θ v p n hp hθ) k

/-- The finite sum of the prefix increments recovers the centered global transcript score almost everywhere. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the global Score eq sum doob Increment](goal).

Under the stated assumptions, the global Score eq sum doob Increment. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma globalScore_eq_sum_doobIncrement {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    (fun z ↦ ∑ k ∈ Finset.range n,
      Causalean.Stat.DoobInformation.increment
        (transcriptLaw P θ p n) (transcriptPrefixFiltration (Z := Z n))
        (conditionalTranscriptDirectionalScore P θ v p n) k z) =ᵐ[
          transcriptLaw P θ p n]
      conditionalTranscriptDirectionalScore P θ v p n := by
  letI : IsProbabilityMeasure (transcriptLaw P θ p n) :=
    transcriptLaw_isProbability P θ p hp hθ n
  filter_upwards [Causalean.Stat.DoobInformation.increment_sum
      (transcriptPrefixFiltration (Z := Z n))
      (conditionalTranscriptDirectionalScore P θ v p n)
      (conditionalTranscriptDirectionalScore_memLp_two P θ v p n hp hθ) n,
    condExp_globalScore_terminal P θ v p n hp hθ,
    condExp_globalScore_initial P θ v p n hp hθ] with z hsum hterminal hinitial
  rw [hsum, hterminal, hinitial]
  simp

/-- Distinct prefix increments of the global transcript score are orthogonal. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hij), [the global Score doob Increment orthogonal](goal).

Under the stated assumptions, the global Score doob Increment orthogonal. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma globalScore_doobIncrement_orthogonal {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    {i j : ℕ} (hij : i ≠ j) :
    ∫ z,
      Causalean.Stat.DoobInformation.increment
          (transcriptLaw P θ p n) (transcriptPrefixFiltration (Z := Z n))
          (conditionalTranscriptDirectionalScore P θ v p n) i z *
        Causalean.Stat.DoobInformation.increment
          (transcriptLaw P θ p n) (transcriptPrefixFiltration (Z := Z n))
          (conditionalTranscriptDirectionalScore P θ v p n) j z
      ∂transcriptLaw P θ p n = 0 := by
  letI : IsProbabilityMeasure (transcriptLaw P θ p n) :=
    transcriptLaw_isProbability P θ p hp hθ n
  exact Causalean.Stat.DoobInformation.increment_orthogonal
    (transcriptPrefixFiltration (Z := Z n))
    (conditionalTranscriptDirectionalScore P θ v p n)
    (conditionalTranscriptDirectionalScore_memLp_two P θ v p n hp hθ) hij

end CausalSmith.Stat.LdpAteEfficiencySurface

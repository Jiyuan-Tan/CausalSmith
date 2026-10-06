module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialScore
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotPrefix
public import Causalean.Stat.Minimax.SequentialScore

/-! # Observed kernels for finite IID latent inputs -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- Average one private release row over the fresh IID four-cell input. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The observed Stage Measure](goal) is determined by [the displayed parameters](hyp:P,θ,p,n,i). -/
def observedStageMeasure {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (n : ℕ) (i : Fin n) :
    PrivateHistory (Z := Z n) i → Measure (Z n i) := fun h =>
  ∑ j : Fin 4, ENNReal.ofReal (piTheta θ p j) • P.channel n i (j, h)

/-- [the measurable observed stage measure assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,p,n,i), these specify the stated inputs. -/
lemma measurable_observedStageMeasure {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (n : ℕ) (i : Fin n) :
    Measurable (observedStageMeasure P θ p n i) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  simp only [observedStageMeasure, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  exact Finset.measurable_fun_sum _ fun j _ =>
    measurable_const.mul ((P.channel n i).measurable_coe hA |>.comp
      (measurable_const.prodMk measurable_id))

/-- The observed next-output kernel. The unit coordinate matches the generic finite-horizon score API; the history is the released history only. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The observed Stage Kernel](goal) is determined by [the displayed parameters](hyp:P,θ,p,n,i). -/
def observedStageKernel {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (n : ℕ) (i : Fin n) :
    Kernel (Unit × History (Z n) i.val (Nat.le_of_lt i.isLt)) (Z n i) :=
  (⟨observedStageMeasure P θ p n i,
    measurable_observedStageMeasure P θ p n i⟩ :
      Kernel (PrivateHistory (Z := Z n) i) (Z n i)).comap
        (fun uh => fsHistoryToPrivate i uh.2)
        ((measurable_fsHistoryToPrivate i).comp measurable_snd)

/-- [the observed stage kernel apply assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,p,n,i,uh), these specify the stated inputs. -/
lemma observedStageKernel_apply {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (n : ℕ) (i : Fin n)
    (uh : Unit × History (Z n) i.val (Nat.le_of_lt i.isLt)) :
    observedStageKernel P θ p n i uh =
      ∑ j : Fin 4, ENNReal.ofReal (piTheta θ p j) •
        P.channel n i (j, fsHistoryToPrivate i uh.2) := by
  rfl

/-- the observed stage kernel is markov assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the observed Stage Kernel is Markov](goal).

Under the stated assumptions, the observed Stage Kernel is Markov. -/
lemma observedStageKernel_isMarkov {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n : ℕ) (i : Fin n) :
    IsMarkovKernel (observedStageKernel P θ p n i) := by
  refine ⟨fun uh => ⟨?_⟩⟩
  rw [observedStageKernel_apply]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  have hmarkov := (P.privacy n).1 i
  letI : IsMarkovKernel (P.channel n i) := hmarkov
  simp only [measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [piTheta_sum_eq_one]
    norm_num
  · intro j _
    exact (piTheta_pos_interior θ p hp hθ j).le

/-- Parameterize the observed release kernels along a local affine path. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The observed Kernel Family](goal) is determined by [the displayed parameters](hyp:P,θ,v,p,n,u). -/
def observedKernelFamily {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n : ℕ) (u : ℝ) : KernelFamily Unit (Z n) := fun i =>
  observedStageKernel P (parameterPath θ v u) p n i

-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
/-- [the observed kernel family is markov assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,hp,n,u,hu,i), these specify the stated inputs. -/
lemma observedKernelFamily_isMarkov {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (n : ℕ) (u : ℝ)
    (hu : InteriorMeans (parameterPath θ v u)) (i : Fin n) :
    IsMarkovKernel (observedKernelFamily P θ v p n u i) :=
  observedStageKernel_isMarkov P _ p hp hu n i

end CausalSmith.Stat.LdpAteEfficiencySurface

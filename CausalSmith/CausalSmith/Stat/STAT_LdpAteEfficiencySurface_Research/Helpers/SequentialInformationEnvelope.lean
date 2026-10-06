module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAdaptiveContinuity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialJointChannel

/-! # Local sequential information envelope

This file identifies the least-favorable contrast direction and proves local
continuity of its stationary staircase information envelope.  The resulting
sequential criterion is uniform over arbitrary scalar sequences staying in a
fixed compact interval.
-/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open Filter MeasureTheory Set
open scoped Topology BigOperators
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- The selected least-favorable direction has unit contrast. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the contrast selected Direction](goal).

Under the stated assumptions, the contrast selected Direction. -/
lemma contrast_selectedDirection (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    contrast (direction (selectedDirection θ p ε hp hθ hε)) = 1 := by
  simp [contrast, direction]

/-- At the base parameter, the selected direction attains the stationary staircase envelope value `Jstar`. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the upper Envelope selected Direction](goal).

Under the stated assumptions, the upper Envelope selected Direction. -/
lemma upperEnvelope_selectedDirection (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    upperEnvelope θ p ε (selectedDirection θ p ε hp hθ hε) =
      Jstar θ p ε :=
  Classical.choose_spec (exists_selectedDirection θ p ε hp hθ hε)

/-- Every history-conditioned sequential channel has directional Fisher information at most the stationary envelope in the selected direction. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hη,hθ,hε), [the sequential Joint Channel fisher selected Direction le upper Envelope](goal).

Under the stated assumptions, the sequential Joint Channel fisher selected Direction le upper Envelope. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma sequentialJointChannel_fisher_selectedDirection_le_upperEnvelope
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n : ℕ) (i : Fin n)
    (μ : Measure (History (Z n) i.val (Nat.le_of_lt i.isLt)))
    [IsProbabilityMeasure μ] (η θ : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hη : InteriorMeans η)
    (hθ : InteriorMeans θ) (hε : 0 < ε) :
    informationQuadratic
        (channelFisherInfo η p (sequentialJointChannel P n i μ))
        (direction (selectedDirection θ p ε hp hθ hε)) ≤
      upperEnvelope η p ε (selectedDirection θ p ε hp hθ hε) := by
  exact sequentialJointChannel_fisher_le_upperEnvelope
    P n i μ η p (selectedDirection θ p ε hp hθ hε) hp hη hε

set_option maxHeartbeats 800000 in
-- Elaborating compact-supremum continuity expands the finite staircase objective.
/-- At fixed direction, the staircase upper envelope is continuous on the interior trial-parameter space. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hε), [the continuous upper Envelope interior](goal).

Under the stated assumptions, the continuous upper Envelope interior. -/
lemma continuous_upperEnvelope_interior (p ε t : ℝ)
    (hp : InteriorAssignment p) (hε : 0 ≤ ε) :
    Continuous (fun θ : {η : TrialParameter // InteriorMeans η} =>
      upperEnvelope θ.1 p ε t) := by
  let Θ := {η : TrialParameter // InteriorMeans η}
  have hmass (s : Fin 14) : Continuous (fun θ : Θ =>
      patternMass θ.1 p ε s) := by
    unfold patternMass
    apply continuous_finsetSum
    intro j _
    apply Continuous.mul
    · fin_cases j <;> simp only [piTheta]
      · exact continuous_const.mul
          (continuous_const.sub ((continuous_apply 0).comp continuous_subtype_val))
      · exact continuous_const.mul
          ((continuous_apply 0).comp continuous_subtype_val)
      · exact continuous_const.mul
          (continuous_const.sub ((continuous_apply 1).comp continuous_subtype_val))
      · exact continuous_const.mul
          ((continuous_apply 1).comp continuous_subtype_val)
    · exact continuous_const
  have hobj : Continuous (fun z : Θ × StaircaseWeight =>
      informationObjective z.1.1 p ε z.2 t) := by
    unfold informationObjective patternInformation
    apply continuous_finsetSum
    intro s _
    apply Continuous.mul
    · exact (continuous_apply s).comp continuous_snd
    · apply Continuous.div continuous_const
        ((hmass s).comp continuous_fst)
      intro z
      exact ne_of_gt (patternMass_pos_interior z.1.1 p ε hp
        z.1.2 hε s)
  have hc := (staircaseFeasible_compact ε hε).continuous_sSup
    (f := fun (θ : Θ) (α : StaircaseWeight) =>
      informationObjective θ.1 p ε α t) hobj
  simpa [upperEnvelope, Set.image, eq_comm] using hc

/-- Any interior parameter sequence converging to the base point has its selected-direction envelope converge to `Jstar` at that point. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hη,hηθ), [the tendsto upper Envelope selected Direction of tendsto](goal).

Under the stated assumptions, the tendsto upper Envelope selected Direction of tendsto. -/
lemma tendsto_upperEnvelope_selectedDirection_of_tendsto
    (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (η : ℕ → TrialParameter) (hη : ∀ n, InteriorMeans (η n))
    (hηθ : Tendsto η atTop (nhds θ)) :
    Tendsto (fun n => upperEnvelope (η n) p ε
      (selectedDirection θ p ε hp hθ hε)) atTop
      (nhds (Jstar θ p ε)) := by
  let Θ := {x : TrialParameter // InteriorMeans x}
  let θsub : Θ := ⟨θ, hθ⟩
  let ηsub : ℕ → Θ := fun n => ⟨η n, hη n⟩
  have hlift : Tendsto ηsub atTop (nhds θsub) := by
    rw [tendsto_subtype_rng]
    exact hηθ
  have hc := (continuous_upperEnvelope_interior p ε
    (selectedDirection θ p ε hp hθ hε) hp hε.le).continuousAt
      (x := θsub)
  have ht := Filter.Tendsto.comp hc hlift
  have heq : (fun x : Θ => upperEnvelope x.1 p ε
      (selectedDirection θ p ε hp hθ hε)) ∘ ηsub =
      fun n => upperEnvelope (η n) p ε
        (selectedDirection θ p ε hp hθ hε) := by
    funext n
    rfl
  rw [heq] at ht
  simpa only [θsub,
    upperEnvelope_selectedDirection θ p ε hp hθ hε] using ht

/-- Uniform sequential form: along any scalar sequence contained in a fixed compact interval, the inverse-root-sample local envelope in the selected direction converges to the base `Jstar`. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,_hR,ha,hinterior), [the tendsto upper Envelope compact Scaled selected Direction](goal).

Under the stated assumptions, the tendsto upper Envelope compact Scaled selected Direction. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma tendsto_upperEnvelope_compactScaled_selectedDirection
    (θ : TrialParameter) (p ε R : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (_hR : 0 ≤ R) (a : ℕ → ℝ) (ha : ∀ n, a n ∈ Icc (-R) R)
    (hinterior : ∀ n, InteriorMeans
      (parameterPath θ (direction (selectedDirection θ p ε hp hθ hε))
        (a n / Real.sqrt n))) :
    Tendsto (fun n => upperEnvelope
      (parameterPath θ (direction (selectedDirection θ p ε hp hθ hε))
        (a n / Real.sqrt n)) p ε
      (selectedDirection θ p ε hp hθ hε)) atTop
      (nhds (Jstar θ p ε)) := by
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have habounded : ∀ᶠ n : ℕ in atTop, |a n| ≤ R :=
    Filter.Eventually.of_forall fun n => abs_le.2 (ha n)
  have hscalar : Tendsto (fun n => a n / Real.sqrt n) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv] using
      bdd_le_mul_tendsto_zero' R habounded hinv
  have hpath : Tendsto (fun n =>
      parameterPath θ (direction (selectedDirection θ p ε hp hθ hε))
        (a n / Real.sqrt n)) atTop (nhds θ) := by
    rw [tendsto_pi_nhds]
    intro k
    simpa [parameterPath] using
      tendsto_const_nhds.add
        (hscalar.mul tendsto_const_nhds)
  exact tendsto_upperEnvelope_selectedDirection_of_tendsto
    θ p ε hp hθ hε _ hinterior hpath

end CausalSmith.Stat.LdpAteEfficiencySurface

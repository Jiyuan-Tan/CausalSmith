module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Basic
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

set_option linter.style.longLine false

/-!
# Finite witness encoding: core definitions

Foundational finite-symbol trajectory definitions, separated from their
chronological factorization proofs so that the latter can reuse the finite
path marginalization library without an import cycle.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- The finite counterpart of the two-block full trajectory. -/
abbrev FiniteTrajectory (T nX nH nR : Nat) :=
  (Fin (T + 1) → JointState nX nH) × (Fin T → Bool × Fin nR)

/-- The finite observed-symbol path. -/
abbrev FiniteObsView (T nX nR : Nat) := Fin T → (Fin nX × Bool × Fin nR)

/-- For [the specified a input](hyp:A), [the specified w input](hyp:w), [the pmf of real weight](goal) is defined by the displayed finite-model construction. -/
noncomputable def pmfOfRealWeight {A : Type*} [Fintype A] [Nonempty A]
    (w : A → ℝ) : PMF A :=
  if hsum : ∑' a, ENNReal.ofReal (w a) = 0 then
    PMF.pure (Classical.choice inferInstance)
  else
    PMF.normalize (fun a ↦ ENNReal.ofReal (w a)) hsum (by simp)

/-- For [the specified kernel input](hyp:kernel), [the specified init input](hyp:init), [the specified b input](hyp:b), [the specified tau input](hyp:tau), [the finite path weight](goal) is defined by the displayed finite-model construction. -/
noncomputable def finitePathWeight {T nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (init : PMF (JointState nX nH)) (b : Fin nX → PMF Bool)
    (tau : FiniteTrajectory T nX nH nR) : ℝ :=
  (init (tau.1 0)).toReal *
    ∏ t : Fin T,
      (b (tau.1 t.castSucc).1 (tau.2 t).1).toReal *
        (kernel (tau.1 t.castSucc) (tau.2 t).1
          ((tau.2 t).2, tau.1 t.succ)).toReal

/-- For [the specified kernel input](hyp:kernel), [the specified init input](hyp:init), [the specified b input](hyp:b), [the finite path pmf](goal) is defined by the displayed finite-model construction. -/
noncomputable def finitePathPMF {T nX nH nR : Nat}
    [NeZero nX] [NeZero nH] [NeZero nR]
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (init : PMF (JointState nX nH)) (b : Fin nX → PMF Bool) :
    PMF (FiniteTrajectory T nX nH nR) :=
  pmfOfRealWeight (finitePathWeight kernel init b)

/-- [the finite reward model data record](goal) packages the displayed data together with its stated size certificate. -/
structure FiniteRewardModel (T nX nH nR : Nat) where
  kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH)
  rew : Fin nR → ℝ
  rew_mem : ∀ r, rew r ∈ Set.Icc (-1 : ℝ) 1
  init : PMF (JointState nX nH)
  b : Fin nX → PMF Bool
  e : Fin nX → PMF Bool
  law : PMF (FiniteTrajectory T nX nH nR)
  law_generated : ∀ tau,
    law tau = init (tau.1 0) *
      ∏ t : Fin T,
        b (tau.1 t.castSucc).1 (tau.2 t).1 *
          kernel (tau.1 t.castSucc) (tau.2 t).1 ((tau.2 t).2, tau.1 t.succ)

/-- For [the specified tau input](hyp:tau), [the fin obs proj](goal) is defined by the displayed finite-model construction. -/
def finObsProj {T nX nH nR : Nat} (tau : FiniteTrajectory T nX nH nR) :
    FiniteObsView T nX nR :=
  fun t ↦ ((tau.1 t.castSucc).1, (tau.2 t).1, (tau.2 t).2)

/-- For [the specified f input](hyp:F), [the obs pmf](goal) is defined by the displayed finite-model construction. -/
noncomputable def FiniteRewardModel.obsPMF {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) : PMF (FiniteObsView T nX nR) :=
  F.law.map finObsProj

/-- For [the specified rew input](hyp:rew), [the specified tau input](hyp:tau), [the decode traj](goal) is defined by the displayed finite-model construction. -/
def decodeTraj {T nX nH nR : Nat} (rew : Fin nR → ℝ)
    (tau : FiniteTrajectory T nX nH nR) : FullTrajectory T nX nH :=
  (tau.1, fun t ↦ ((tau.2 t).1, rew (tau.2 t).2))

/-- For [the specified f input](hyp:F), [the embed](goal) is defined by the displayed finite-model construction. -/
noncomputable def embed {T nX nH nR : Nat} (F : FiniteRewardModel T nX nH nR) :
    RawPomdpExperiment T nX nH where
  K s a := (F.kernel s a).map (fun p ↦ (F.rew p.1, p.2)) |>.toMeasure
  b x a := (F.b x a).toReal
  e x a := (F.e x a).toReal
  init s := (F.init s).toReal
  law := (F.law.map (decodeTraj F.rew)).toMeasure
  law_isProbability := by infer_instance

/-- For [the specified f input](hyp:F), [the specified p input](hyp:p), [the finite policy kernel](goal) is defined by the displayed finite-model construction. -/
noncomputable def finitePolicyKernel {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (p : Fin nX → PMF Bool)
    (s s' : JointState nX nH) : ℝ :=
  ∑ a : Bool, (p s.1 a).toReal *
    (∑ r : Fin nR, F.kernel s a (r, s')).toReal

/-- For [the specified f input](hyp:F), [the finite target value](goal) is defined by the displayed finite-model construction. -/
noncomputable def finiteTargetValue {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) : ℝ :=
  ∑ s, stationaryLaw (finitePolicyKernel F F.e) s *
    ∑ a : Bool, (F.e s.1 a).toReal *
      ∑ p : Fin nR × JointState nX nH, (F.kernel s a p).toReal * F.rew p.1

end CausalSmith.Stat.PomdpLatentOverlapMinimax

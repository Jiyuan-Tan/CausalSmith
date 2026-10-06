module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.CellTV
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.Product

/-!
Tensorization of the actual affine core/filler predictive measures. Independent
rare cells obey the joint Taylor budget, and a common reservoir law adds no distance.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open Causalean.Stat.Minimax.MomentMatchedMixture

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,n,m,d), The independent rare-cell product has total variation below one sixty-fourth.  This gives [the stated result](goal).-/
-- @node: affineCellPoissonPredictive_product_tv_small
lemma affineCellPoissonPredictive_product_tv_small (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    let t := affineTuning n m d eps
    Causalean.Stat.tvDist
      (Measure.pi fun _ : Fin t.Kstar => affineCellPoissonPredictive sigma t.u t.w true)
      (Measure.pi fun _ : Fin t.Kstar => affineCellPoissonPredictive sigma t.u t.w false) <
      1 / 64 := by
  intro t
  exact (tvDist_pi_iid_le t.Kstar _ _).trans_lt
    (affineCellPoissonPredictive_joint_tv_small n m d eps hn hd heps heps' sigma)

/-- [Under the stated inputs and conditions](hyp:R,rho,eps,hn,hd,heps,heps',sigma,n,m,d), Adding any common independent reservoir factor preserves the joint distance budget.  This gives [the stated result](goal).-/
-- @node: affineCellPoissonPredictive_reservoir_tv_small
lemma affineCellPoissonPredictive_reservoir_tv_small {R : Type*} [MeasurableSpace R]
    (rho : Measure R) [IsProbabilityMeasure rho]
    (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    let t := affineTuning n m d eps
    Causalean.Stat.tvDist
      ((Measure.pi fun _ : Fin t.Kstar =>
        affineCellPoissonPredictive sigma t.u t.w true).prod rho)
      ((Measure.pi fun _ : Fin t.Kstar =>
        affineCellPoissonPredictive sigma t.u t.w false).prod rho) < 1 / 64 := by
  intro t
  have h := tvDist_prod_le_add
    (Measure.pi fun _ : Fin t.Kstar => affineCellPoissonPredictive sigma t.u t.w true)
    (Measure.pi fun _ : Fin t.Kstar => affineCellPoissonPredictive sigma t.u t.w false)
    rho rho
  have hself : Causalean.Stat.tvDist rho rho = 0 := by
    simp [Causalean.Stat.tvDist]
  rw [hself, add_zero] at h
  exact h.trans_lt
    (affineCellPoissonPredictive_product_tv_small n m d eps hn hd heps heps' sigma)

end CausalSmith.Stat.AnnotationRarearmFrontier

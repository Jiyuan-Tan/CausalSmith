module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Basic
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.KnownMarginalLimit

/-! Convergence to the exact-known-treatment-marginal experiment. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open Filter Topology
open Causalean.Stat.Minimax.FiniteSideInformation

-- @node: thm:known-marginal-limit
/-- For fixed labeled size and alphabet, the minimax risk converges to the risk
with the exact treatment-covariate table supplied.  [the stated conditions](hyp:heps,heps2,hn,hd) [the stated conclusion](goal). -/
theorem known_marginal_limit {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2)
    (n d : Nat) (hn : 1 ≤ n) (hd : 2 ≤ d) :
    Tendsto (fun m => minimaxRisk n m d eps) atTop
      (nhds (knownMarginalRisk n d eps)) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (lt_of_lt_of_le (by omega) hd)
  letI : Nonempty (Set.Icc eps (1 - eps)) := ⟨⟨eps, le_rfl, by linarith⟩⟩
  letI : Nonempty (KnownMarginalParam d eps) := inferInstance
  let p := fun theta : KnownMarginalParam d eps ↦
    knownMarginalLabelProb (n := n) theta heps.le
  let q := knownMarginalAuxProb (d := d) (eps := eps)
  let hq := fun theta : KnownMarginalParam d eps ↦
    knownMarginalAuxProb_simplex theta heps.le
  let tau := knownMarginalTarget (d := d) (eps := eps)
  have hgeneric := knownMarginalGeneric_tendsto heps heps2 n d hd
  have hmeasurable : measurableExactTableMinimaxValue p q tau (-1) 1 =
      exactSideMinimaxValue p q hq tau (-1) 1 := by
    apply measurableExactTableMinimaxValue_eq_of_tendsto
      p q tau
      (fun theta ↦ knownMarginalLabelProb_simplex theta heps.le)
      hq (by norm_num) knownMarginalTarget_mem
    exact hgeneric
  have hlimit : knownMarginalRisk n d eps =
      exactSideMinimaxValue p q hq tau (-1) 1 :=
    (knownMarginalRisk_eq_measurableValue heps heps2 n d hd).trans hmeasurable
  have hseq : (fun m ↦ minimaxRisk n m d eps) =
      (fun m ↦ empiricalSideMinimaxValue p q hq tau (-1) 1 m) := by
    funext m
    exact minimaxRisk_eq_empiricalValue heps heps2 n m d hd
  rw [hseq, hlimit]
  exact hgeneric

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

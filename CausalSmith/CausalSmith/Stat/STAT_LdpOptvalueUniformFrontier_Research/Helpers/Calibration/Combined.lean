module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Calibration.HybridBasics

/-!
# Combining the pilot and evaluation rows

The independent two-block experiment is a split iid vector block. Hybrid
statistics depend only on their own columns in this combined experiment.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {m d : ℕ}

/-- Fix [the function z](hyp:z). [Split a combined vector block into its pilot and evaluation halves](goal). -/
-- @node: splitHybridRows
def splitHybridRows (z : Fin (m+m) → Fin d → Bool) :
    (Fin m → Fin d → Bool) × (Fin m → Fin d → Bool) :=
  (fun i => z (Fin.castAdd m i), fun i => z (Fin.natAdd m i))

/-- [Splitting iid rows gives exactly the independent pilot/evaluation law](goal). -/
-- @node: splitHybridRows_measurePreserving
lemma splitHybridRows_measurePreserving (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (eps : ℝ) :
    MeasurePreserving (splitHybridRows (m := m) (d := d))
      (vectorBlockLaw P eps (m+m)) (hybridLaw P eps m) := by
  letI := vectorMessageLaw_probability P eps
  have hr := measurePreserving_piCongrLeft
    (fun _ : Fin m ⊕ Fin m => vectorMessageLaw P eps)
    (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m+m)).symm
  have hs := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin m ⊕ Fin m => vectorMessageLaw P eps)
  convert hs.comp hr using 1
  · funext z
    simp [splitHybridRows, Function.comp_def, MeasurableEquiv.sumPiEquivProdPi,
      MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft]
  · rfl
  · rfl

/-- [Hybrid means can be evaluated in the combined-row experiment](goal). -/
-- @node: hybridMean_eq_combined_blockMean
lemma hybridMean_eq_combined_blockMean (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (eps : ℝ)
    (f : ((Fin m → Fin d → Bool) × (Fin m → Fin d → Bool)) → ℝ) :
    hybridMean P eps f = blockMean P eps (fun z => f (splitHybridRows z)) := by
  unfold hybridMean blockMean
  rw [← (splitHybridRows_measurePreserving P eps).map_eq]
  exact integral_map (by fun_prop) (by fun_prop)

/-- [Hybrid variances can be evaluated in the combined-row experiment](goal). -/
-- @node: hybridVar_eq_combined_blockVar
lemma hybridVar_eq_combined_blockVar (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (eps : ℝ)
    (f : ((Fin m → Fin d → Bool) × (Fin m → Fin d → Bool)) → ℝ) :
    hybridVar P eps f = blockVar P eps (fun z => f (splitHybridRows z)) := by
  unfold hybridVar blockVar
  rw [← hybridMean_eq_combined_blockMean]
  exact hybridMean_eq_combined_blockMean P eps _

/-- Fix [the privacy budget](hyp:eps), [the natural-number parameter D](hyp:D), [the coordinate index](hyp:j), and [the function w](hyp:w). [The hybrid rule applied to a single combined scaled column](goal). -/
-- @node: combinedHybridStatistic
def combinedHybridStatistic (eps : ℝ) (D : ℕ) (j : Fin d)
    (w : Fin (m+m) → ℝ) : ℝ :=
  let T := 4 * Real.sqrt (sigmaSquared d m eps) * Real.sqrt (logDim d)
  let pilot := (m : ℝ)⁻¹ * ∑ i : Fin m, w (Fin.castAdd m i)
  let evaluation := (m : ℝ)⁻¹ * ∑ i : Fin m, w (Fin.natAdd m i)
  let poly := ∑ v ∈ Finset.range (D+1), (chebyshevAbsPoly D).coeff v *
    (2*T)^((1 : ℤ) - (v : ℤ)) *
      privateMoment (fun i : Fin m => fun _ : Fin d => w (Fin.natAdd m i)) v j
  if |pilot| ≤ T then poly
  else (if 0 < pilot then 1 else if pilot < 0 then -1 else 0) * evaluation

/-- [Each split hybrid statistic is an own-column statistic of the combined block](goal). -/
-- @node: hybridColumn_eq_combined_columnStatistic
lemma hybridColumn_eq_combined_columnStatistic (eps : ℝ) (D : ℕ) (j : Fin d)
    (z : Fin (m+m) → Fin d → Bool) :
    hybridColumn eps D j (splitHybridRows z) =
      columnStatistic eps (combinedHybridStatistic (m := m) eps D) j z := by
  rfl

/-- [The combined hybrid rule is measurable on real scaled columns](goal). -/
-- @node: combinedHybridStatistic_measurable
@[fun_prop]
lemma combinedHybridStatistic_measurable (eps : ℝ) (D : ℕ) (j : Fin d) :
    Measurable (combinedHybridStatistic (m := m) eps D j) := by
  unfold combinedHybridStatistic privateMoment
  dsimp only
  apply Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop)
  apply Measurable.mul _ (by fun_prop)
  apply Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop)
  exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop))
    (by fun_prop) (by fun_prop)

end CausalSmith.Stat.LdpOptvalueUniformFrontier

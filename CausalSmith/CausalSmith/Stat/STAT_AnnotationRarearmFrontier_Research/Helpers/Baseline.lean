module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Estimator

/-!
Deterministic inverse-count baseline with independent two-pool prefix averaging.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[The baseline prefix statistic clips the treated-minus-control inverse-count sum](goal).
-/
noncomputable def baselinePrefixStatistic {n m d : Nat} (r g : Nat) (s : Sample n m d) : Real :=
  let h := n / 2
  let u : Real := h / 8
  let Z := fun a j => labeledBlockCount s.1 0 r j a true
  let K := fun a j => pooledArmCount s h (n - h) 0 g j a
  let H := fun a j => (Z a j : Real) / u *
    (1 + (K (!a) j : Real) / ((K a j : Real) + 1))
  max (-1) (min 1 (∑ j : Fin d, (H true j - H false j)))
-- @node: def:baseline
/--
[The inverse-count baseline averages valid two-pool prefixes and outputs zero on overflow or
small sample sizes](goal).
-/
noncomputable def baselineEstimator (n m d : Nat) : Sample n m d → Real :=
  fun s => if n < 6 then 0 else
    let h := n / 2
    let g := n - h + m
    let u : Real := h / 8
    let t : Real := g / 8
    ∑ r ∈ Finset.range (h + 1), ∑ v ∈ Finset.range (g + 1),
      Real.exp (-u - t) * (u ^ r / (r.factorial : Real)) *
        (t ^ v / (v.factorial : Real)) * baselinePrefixStatistic r v s
  -- @realizes T^{\mathrm B}(total clipped inverse-count prefix average)
/--
[The baseline is measurable on the original finite sample arrays](goal).
-/
@[fun_prop]
-- @node: baselineEstimator_measurable
lemma baselineEstimator_measurable (n m d : Nat) : Measurable (baselineEstimator n m d) := by
  fun_prop
/--
[The total baseline takes values between minus one and one](goal).
-/
-- @node: baselineEstimator_mem_Icc
lemma baselineEstimator_mem_Icc (n m d : Nat) (s : Sample n m d) :
    baselineEstimator n m d s ∈ Set.Icc (-1) 1 := by
  classical
  by_cases hsmall : n < 6
  · simp [baselineEstimator, hsmall]
  · rw [baselineEstimator, if_neg hsmall]
    let h := n / 2
    let g := n - h + m
    let u : Real := h / 8
    let t : Real := g / 8
    have hu : 0 ≤ u := by dsimp [u]; positivity
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hclip (r v : Nat) : baselinePrefixStatistic r v s ∈ Set.Icc (-1) 1 := by
      constructor
      · exact le_max_left _ _
      · exact max_le (by norm_num) (min_le_left _ _)
    have havg := finitePoissonAverage_mem_Icc u hu h _ (fun r =>
      finitePoissonAverage_mem_Icc t ht g _ (hclip r))
    convert havg using 1
    simp only [u, t, g, h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro v _
    rw [sub_eq_add_neg, Real.exp_add]
    ring

end CausalSmith.Stat.AnnotationRarearmFrontier

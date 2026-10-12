module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.MatchingFamily
public import Mathlib.Algebra.BigOperators.Field

/-!
# Full-graph Bayes weights and the planted graph marginal

Cold scaffold: definitions are complete; proof obligations are reserved for Stage 3.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

/-- The one-bit likelihood ratio, including the declared single-point and zero-r conventions. -/
def edgeRatio (q r : ℝ) (h : Bool) : ℝ :=
  if r = 0 then 0 else if r = 1 ∧ q = 1 then 1 else if h then q/r else (1-q)/(1-r)
-- @realizes W(q/r on a positive bit and (1-q)/(1-r) on a negative bit, with endpoint conventions)
/-- The corresponding one-bit second moment. -/
def kappa (q r : ℝ) : ℝ :=
  if r = 0 then 0 else if r = 1 ∧ q = 1 then 1 else q^2/r + (1-q)^2/(1-r)
-- @realizes kappa(two-branch second moment, one at q=r=1 and zero at r=0)
/-- The likelihood of every labeled off-diagonal report coordinate under a matching. -/
def graphLikelihood (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ)
    (H : Acq (Fin n)) (M : Matching m) : ℝ :=
  ∏ e : OffDiag (Fin n), if matchingEdge n m hfit M e.1.1 e.1.2 then
    (if H e then q else 1-q) else (if H e then r else 1-r)
/-- The unnormalized posterior combines prior mass with full-graph likelihood. -/
def posteriorWeight (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ)
    (H : Acq (Fin n)) (M : Matching m) : ℝ :=
  matchingPriorMass m M * graphLikelihood n m hfit q r H M
/-- The total finite Bayes construction, falling back to the prior only at zero total weight. -/
-- @node: def:matching-posterior
def matchingPosterior (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ)
    (H : Acq (Fin n)) (M : Matching m) : ℝ :=
  if (∑ M' : Matching m, posteriorWeight n m hfit q r H M') = 0 then matchingPriorMass m M
  else posteriorWeight n m hfit q r H M / ∑ M' : Matching m, posteriorWeight n m hfit q r H M'
-- @realizes PiH(total posterior on all legal matchings, using the entire graph H)
/-- [The empty matching supplies a unit term to the prior partition sum.](goal) -/
-- @node: matchingPartition_pos
lemma matchingPartition_pos (m : ℕ) : 0 < matchingPartition m := by
  let empty : Matching m := ⟨fun _ => none, by simp⟩
  have hw (M : Matching m) : 0 ≤ matchingWeight m M := by
    unfold matchingWeight activity
    positivity
  have hempty : matchingWeight m empty = 1 := by
    simp [matchingWeight, Matching.size, Matching.edges, empty]
  have hle := Finset.single_le_sum (fun M _ => hw M) (Finset.mem_univ empty)
  rw [hempty] at hle
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hle

/-- [Each normalized prior weight is nonnegative.](goal) -/
-- @node: matchingPriorMass_nonneg
lemma matchingPriorMass_nonneg (m : ℕ) (M : Matching m) :
    0 ≤ matchingPriorMass m M := by
  apply div_nonneg _ (matchingPartition_pos m).le
  unfold matchingWeight activity
  positivity

/-- [Normalizing by the positive partition sum gives unit total mass.](goal) -/
-- @node: matchingPriorMass_sum_one
lemma matchingPriorMass_sum_one (m : ℕ) :
    (∑ M : Matching m, matchingPriorMass m M) = 1 := by
  simp only [matchingPriorMass, ← Finset.sum_div]
  exact div_self (ne_of_gt (matchingPartition_pos m))

/-- Given [the stated assumptions](hyp:hfit,hqr), [Every full-graph likelihood is a product of nonnegative bit probabilities.](goal) -/
-- @node: graphLikelihood_nonneg
lemma graphLikelihood_nonneg (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ)
    (hqr : ChannelDomain q r) (H : Acq (Fin n)) (M : Matching m) :
    0 ≤ graphLikelihood n m hfit q r H M := by
  have hq : 0 ≤ q := le_trans hqr.1 hqr.2.1
  have hr : r ≤ 1 := le_trans hqr.2.1 hqr.2.2
  unfold graphLikelihood
  apply Finset.prod_nonneg
  intro e _
  split_ifs <;> linarith [hqr.1, hqr.2.2]

/-- Given [the stated assumptions](hyp:hfit,hqr), [The prior mass times the graph likelihood is nonnegative.](goal) -/
-- @node: posteriorWeight_nonneg
lemma posteriorWeight_nonneg (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ)
    (hqr : ChannelDomain q r) (H : Acq (Fin n)) (M : Matching m) :
    0 ≤ posteriorWeight n m hfit q r H M := by
  exact mul_nonneg (matchingPriorMass_nonneg m M)
    (graphLikelihood_nonneg n m hfit q r hqr H M)

/-- Given [the stated assumptions](hyp:hfit,hqr), [Nonnegative channel probabilities give nonnegative posterior masses.](goal) -/
-- @node: matchingPosterior_nonneg
lemma matchingPosterior_nonneg (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ)
    (hqr : ChannelDomain q r) (H : Acq (Fin n)) (M : Matching m) :
    0 ≤ matchingPosterior n m hfit q r H M := by
  unfold matchingPosterior
  split_ifs
  · exact matchingPriorMass_nonneg m M
  · exact div_nonneg (posteriorWeight_nonneg n m hfit q r hqr H M)
      (Finset.sum_nonneg (fun M _ => posteriorWeight_nonneg n m hfit q r hqr H M))
-- @realizes PiH(nonnegative posterior masses)
/-- Given [the stated assumptions](hyp:hfit,hqr), [The total posterior mass is one.](goal) -/
-- @node: matchingPosterior_sum_one
lemma matchingPosterior_sum_one (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ)
    (hqr : ChannelDomain q r) (H : Acq (Fin n)) :
    (∑ M : Matching m, matchingPosterior n m hfit q r H M) = 1 := by
  unfold matchingPosterior
  split_ifs with h
  · exact matchingPriorMass_sum_one m
  · rw [← Finset.sum_div]
    exact div_self h
-- @realizes PiH(normalized total posterior mass)
/-- The actual acquired-graph marginal under the dilute planted matching prior. -/
def plantedGraphLaw (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ) : Measure (Acq (Fin n)) :=
  (matchingPrior m).bind (fun M => acquisitionLaw (matchingGraphSchedule n m hfit M) q r)

/-- Given [the stated assumptions](hyp:hqr,h), [The declared endpoint extension remains a nonnegative likelihood ratio on admissible channels.](goal) -/
-- @node: edgeRatio_nonneg
lemma edgeRatio_nonneg (q r : ℝ) (hqr : ChannelDomain q r) (h : Bool) :
    0 ≤ edgeRatio q r h := by
  have hq : 0 ≤ q := le_trans hqr.1 hqr.2.1
  have hr : r ≤ 1 := le_trans hqr.2.1 hqr.2.2
  unfold edgeRatio
  split_ifs
  · exact le_rfl
  · norm_num
  · exact div_nonneg hq hqr.1
  · exact div_nonneg (sub_nonneg.mpr hqr.2.2) (sub_nonneg.mpr hr)
-- @realizes W(nonnegative ratio on the entire admitted channel including endpoints)
/-- Given [the stated assumptions](hyp:hqr), [The one-bit second moment is nonnegative.](goal) -/
-- @node: kappa_nonneg
lemma kappa_nonneg (q r : ℝ) (hqr : ChannelDomain q r) : 0 ≤ kappa q r := by
  have hr : r ≤ 1 := le_trans hqr.2.1 hqr.2.2
  unfold kappa
  split_ifs
  · exact le_rfl
  · norm_num
  · exact add_nonneg (div_nonneg (sq_nonneg q) hqr.1)
      (div_nonneg (sq_nonneg (1-q)) (sub_nonneg.mpr hr))
-- @realizes kappa(nonnegative finite real second moment)

/-- Given [the stated assumptions](hyp:hr,hrq,hq), [A positive admissible channel has likelihood-ratio second moment at least one,
including the single-point channel.](goal) -/
-- @node: kappa_ge_one_of_positive
lemma kappa_ge_one_of_positive (q r : ℝ) (hr : 0 < r) (hrq : r ≤ q)
    (hq : q ≤ 1) : 1 ≤ kappa q r := by
  have hr1 : r ≤ 1 := hrq.trans hq
  by_cases hendpoint : r = 1
  · have hq1 : q = 1 := le_antisymm hq (hendpoint ▸ hrq)
    simp [kappa, hendpoint, hq1]
  · have hrlt : r < 1 := lt_of_le_of_ne hr1 hendpoint
    have hid : q^2/r + (1-q)^2/(1-r) = 1 + (q-r)^2/(r*(1-r)) := by
      field_simp
      ring
    rw [kappa, if_neg (ne_of_gt hr), if_neg (by simp [hendpoint]), hid]
    exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (by positivity))

end CausalSmith.Experimentation.NoisygraphTtePrecision

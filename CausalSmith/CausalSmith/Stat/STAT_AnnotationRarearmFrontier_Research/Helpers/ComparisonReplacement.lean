module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.EmpiricalTableAdjustment
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.FiniteLaw

/-!
Proof-only replacement of a population marginal while retaining its binary outcome
regressions. This realizes the comparison law in the benchmark-recovery roadmap.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- [Under the stated inputs and conditions](hyp:d,P,j,a,y), Binary conditional outcome weights are nonnegative, including null original arms.  This gives [the stated result](goal).-/
-- @node: comparisonOutcomeWeight_nonneg
lemma comparisonOutcomeWeight_nonneg {d : Nat} (P : DiscreteLaw d)
    (j : Fin d) (a y : Bool) : 0 ≤ bernoulliMass (outcomeMean P a j) y := by
  have h := outcomeMean_mem_Icc P a j
  cases y <;> simp only [bernoulliMass, Bool.false_eq_true, if_false, if_true] <;>
    linarith [h.1, h.2]

/-- [Under the stated inputs and conditions](hyp:d,P,j,a), The two conditional outcome weights sum to one.  This gives [the stated result](goal).-/
-- @node: comparisonOutcomeWeight_sum
lemma comparisonOutcomeWeight_sum {d : Nat} (P : DiscreteLaw d)
    (j : Fin d) (a : Bool) : ∑ y : Bool, bernoulliMass (outcomeMean P a j) y = 1 := by
  simp [bernoulliMass]

/-- [Under the stated inputs and conditions](hyp:d,P,j,a,y), Every original atom factors into its arm mass and its conditional outcome weight.  This gives [the stated result](goal).-/
-- @node: comparison_jointMass_factor
lemma comparison_jointMass_factor {d : Nat} (P : DiscreteLaw d)
    (j : Fin d) (a y : Bool) :
    jointMass P j a y = armMass P j a * bernoulliMass (outcomeMean P a j) y := by
  have hs := armMass_nonneg P j a
  have hq := jointMass_nonneg P j a true
  have hf := jointMass_nonneg P j a false
  have hsum : armMass P j a = jointMass P j a true + jointMass P j a false := by
    simp [armMass]
  by_cases hz : armMass P j a = 0
  · have ht : jointMass P j a true = 0 := by linarith
    have hc : jointMass P j a false = 0 := by linarith
    cases y <;> simp [hz, ht, hc]
  · have hprod : armMass P j a * outcomeMean P a j = jointMass P j a true := by
      unfold outcomeMean markedMass
      field_simp
    cases y <;> simp only [bernoulliMass, Bool.false_eq_true, if_false, if_true]
    · nlinarith
    · exact hprod.symm

/-- Attach the original outcome regressions to an arbitrary supplied table, with a
population fallback on ambient inputs that cannot be normalized. -/
-- @node: comparisonReplacementLaw
noncomputable def comparisonReplacementLaw {d : Nat} (P : DiscreteLaw d)
    (v : AuxTable d) : DiscreteLaw d :=
  ⟨normalizedPMF (fun z => v (z.1, z.2.1) *
    bernoulliMass (outcomeMean P z.2.1 z.1) z.2.2) P.pmf⟩

/-- [Under the stated inputs and conditions](hyp:d,P,v,hv,hs,j,a,y), A nonnegative probability table gives exactly the specified replacement atoms.  This gives [the stated result](goal).-/
-- @node: comparisonReplacementLaw_jointMass
lemma comparisonReplacementLaw_jointMass {d : Nat} (P : DiscreteLaw d)
    (v : AuxTable d) (hv : ∀ z, 0 ≤ v z) (hs : ∑ z, v z = 1)
    (j : Fin d) (a y : Bool) :
    jointMass (comparisonReplacementLaw P v) j a y =
      v (j, a) * bernoulliMass (outcomeMean P a j) y := by
  apply normalizedPMF_toReal
  · intro z
    exact mul_nonneg (hv _) (comparisonOutcomeWeight_nonneg P _ _ _)
  · simpa only [Fintype.sum_prod_type, ← Finset.mul_sum,
      comparisonOutcomeWeight_sum, mul_one] using hs

/-- [Under the stated inputs and conditions](hyp:d,P,v,hv,hs,j,a), The arm masses of the replacement law are the supplied table entries.  This gives [the stated result](goal).-/
-- @node: comparisonReplacementLaw_armMass
lemma comparisonReplacementLaw_armMass {d : Nat} (P : DiscreteLaw d)
    (v : AuxTable d) (hv : ∀ z, 0 ≤ v z) (hs : ∑ z, v z = 1)
    (j : Fin d) (a : Bool) : armMass (comparisonReplacementLaw P v) j a = v (j, a) := by
  simp only [armMass, comparisonReplacementLaw_jointMass P v hv hs,
    ← Finset.mul_sum, comparisonOutcomeWeight_sum, mul_one]

/-- [Under the stated inputs and conditions](hyp:d,P,v,hv,hs), The auxiliary table is exactly the requested replacement marginal.  This gives [the stated result](goal).-/
-- @node: comparisonReplacementLaw_auxTable
lemma comparisonReplacementLaw_auxTable {d : Nat} (P : DiscreteLaw d)
    (v : AuxTable d) (hv : ∀ z, 0 ≤ v z) (hs : ∑ z, v z = 1) :
    auxTable (comparisonReplacementLaw P v) = v := by
  funext z
  exact (auxMarginal_toReal_armMass _ z.1 z.2).trans
    (comparisonReplacementLaw_armMass P v hv hs z.1 z.2)

/-- [Under the stated inputs and conditions](hyp:d,P,v,hv,hs,j), Covariate masses sum the supplied arm entries.  This gives [the stated result](goal).-/
-- @node: comparisonReplacementLaw_cellMass
lemma comparisonReplacementLaw_cellMass {d : Nat} (P : DiscreteLaw d)
    (v : AuxTable d) (hv : ∀ z, 0 ≤ v z) (hs : ∑ z, v z = 1)
    (j : Fin d) : cellMass (comparisonReplacementLaw P v) j = v (j, true) + v (j, false) := by
  change (∑ a : Bool, armMass (comparisonReplacementLaw P v) j a) = _
  simp only [comparisonReplacementLaw_armMass P v hv hs, Fintype.sum_bool]

/-- [Under the stated inputs and conditions](hyp:d,P,v,eps,hv,hs,hlegal), A legal replacement marginal gives a law in the same overlap model.  This gives [the stated result](goal).-/
-- @node: comparisonReplacementLaw_model
lemma comparisonReplacementLaw_model {d : Nat} (P : DiscreteLaw d)
    (v : AuxTable d) (eps : Real) (hv : ∀ z, 0 ≤ v z) (hs : ∑ z, v z = 1)
    (hlegal : ∀ j, eps * (v (j, false) + v (j, true)) ≤ v (j, true) ∧
      v (j, true) ≤ (1 - eps) * (v (j, false) + v (j, true))) :
    ModelClass d eps (comparisonReplacementLaw P v) := by
  constructor
  intro j hp
  have hz : cellMass (comparisonReplacementLaw P v) j ≠ 0 := ne_of_gt hp
  unfold propensity
  rw [if_neg hz]
  simp only [comparisonReplacementLaw_armMass P v hv hs,
    comparisonReplacementLaw_cellMass P v hv hs] at hp ⊢
  constructor
  · exact (le_div_iff₀ hp).mpr (by simpa only [add_comm] using (hlegal j).1)
  · exact (div_le_iff₀ hp).mpr (by simpa only [add_comm] using (hlegal j).2)

/-- [Under the stated inputs and conditions](hyp:d,P,v,hv,hs,j,a,ha), In every positive replacement arm the conditional mean is inherited, even if the
original arm was null (its inherited mean is then zero).  This gives [the stated result](goal).-/
-- @node: comparisonReplacementLaw_outcomeMean
lemma comparisonReplacementLaw_outcomeMean {d : Nat} (P : DiscreteLaw d)
    (v : AuxTable d) (hv : ∀ z, 0 ≤ v z) (hs : ∑ z, v z = 1)
    (j : Fin d) (a : Bool) (ha : v (j, a) ≠ 0) :
    outcomeMean (comparisonReplacementLaw P v) a j = outcomeMean P a j := by
  simp only [outcomeMean, markedMass, comparisonReplacementLaw_jointMass P v hv hs,
    comparisonReplacementLaw_armMass P v hv hs, bernoulliMass, if_true]
  exact mul_div_cancel_left₀ _ ha

/-- [Under the stated inputs and conditions](hyp:d,P,v,hv,hs), Retaining the binary conditional weights preserves the complete-table L¹ distance.  This gives [the stated result](goal).-/
-- @node: comparisonReplacementLaw_l1
lemma comparisonReplacementLaw_l1 {d : Nat} (P : DiscreteLaw d)
    (v : AuxTable d) (hv : ∀ z, 0 ≤ v z) (hs : ∑ z, v z = 1) :
    (∑ z : Obs d, |jointMass P z.1 z.2.1 z.2.2 -
      jointMass (comparisonReplacementLaw P v) z.1 z.2.1 z.2.2|) =
      ∑ z : AuxObs d, |auxTable P z - v z| := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  simp only [comparisonReplacementLaw_jointMass P v hv hs, comparison_jointMass_factor P,
    ← sub_mul, abs_mul, abs_of_nonneg (comparisonOutcomeWeight_nonneg P j a _),
    ← Finset.mul_sum, comparisonOutcomeWeight_sum, mul_one, auxTable,
    auxMarginal_toReal_armMass]

/-- [Under the stated inputs and conditions](hyp:d,P,v,eps,heps,hv,hs,hlegal,j,a), In a legal occupied replacement cell, both inherited arm means are unchanged.  This gives [the stated result](goal).-/
-- @node: comparisonReplacementLaw_weighted_mean
lemma comparisonReplacementLaw_weighted_mean {d : Nat} (P : DiscreteLaw d)
    (v : AuxTable d) (eps : Real) (heps : 0 < eps)
    (hv : ∀ z, 0 ≤ v z) (hs : ∑ z, v z = 1)
    (hlegal : ∀ j, eps * (v (j, false) + v (j, true)) ≤ v (j, true) ∧
      v (j, true) ≤ (1 - eps) * (v (j, false) + v (j, true)))
    (j : Fin d) (a : Bool) :
    cellMass (comparisonReplacementLaw P v) j *
      outcomeMean (comparisonReplacementLaw P v) a j =
    cellMass (comparisonReplacementLaw P v) j * outcomeMean P a j := by
  by_cases hz : cellMass (comparisonReplacementLaw P v) j = 0
  · simp only [hz, zero_mul]
  · have hp : 0 < cellMass (comparisonReplacementLaw P v) j :=
      lt_of_le_of_ne (cellMass_nonneg _ _) (Ne.symm hz)
    have hmodel := comparisonReplacementLaw_model P v eps hv hs hlegal
    have ha := (mul_pos heps hp).trans_le
      (armMass_ge_overlap_cellMass _ eps hmodel j a)
    rw [comparisonReplacementLaw_armMass P v hv hs] at ha
    rw [comparisonReplacementLaw_outcomeMean P v hv hs j a (ne_of_gt ha)]

/-- [Under the stated inputs and conditions](hyp:d,P,v,eps,heps,hv,hs,hlegal), The replacement target is the original regression contrast under the new cell weights.  This gives [the stated result](goal).-/
-- @node: comparisonReplacementLaw_target
lemma comparisonReplacementLaw_target {d : Nat} (P : DiscreteLaw d)
    (v : AuxTable d) (eps : Real) (heps : 0 < eps)
    (hv : ∀ z, 0 ≤ v z) (hs : ∑ z, v z = 1)
    (hlegal : ∀ j, eps * (v (j, false) + v (j, true)) ≤ v (j, true) ∧
      v (j, true) ≤ (1 - eps) * (v (j, false) + v (j, true))) :
    ateFunctional (comparisonReplacementLaw P v) =
      ∑ j, (v (j, true) + v (j, false)) *
        (outcomeMean P true j - outcomeMean P false j) := by
  unfold ateFunctional
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_sub, comparisonReplacementLaw_weighted_mean P v eps heps hv hs hlegal,
    comparisonReplacementLaw_weighted_mean P v eps heps hv hs hlegal,
    ← mul_sub, comparisonReplacementLaw_cellMass P v hv hs]

/-- [Under the stated inputs and conditions](hyp:d,P,v,eps,heps,hv,hs,hlegal), Moving a legal marginal changes the target by at most the marginal L¹ distance.  This gives [the stated result](goal).-/
-- @node: comparisonReplacementLaw_target_error
lemma comparisonReplacementLaw_target_error {d : Nat} (P : DiscreteLaw d)
    (v : AuxTable d) (eps : Real) (heps : 0 < eps)
    (hv : ∀ z, 0 ≤ v z) (hs : ∑ z, v z = 1)
    (hlegal : ∀ j, eps * (v (j, false) + v (j, true)) ≤ v (j, true) ∧
      v (j, true) ≤ (1 - eps) * (v (j, false) + v (j, true))) :
    |ateFunctional P - ateFunctional (comparisonReplacementLaw P v)| ≤
      ∑ z : AuxObs d, |auxTable P z - v z| := by
  have hcell (j : Fin d) : cellMass P j =
      auxTable P (j, true) + auxTable P (j, false) := by
    simp only [auxTable, auxMarginal_toReal_armMass, cellMass, armMass, Fintype.sum_bool]
  have hcontrast (j : Fin d) : |outcomeMean P true j - outcomeMean P false j| ≤ 1 := by
    have ht := outcomeMean_mem_Icc P true j
    have hc := outcomeMean_mem_Icc P false j
    exact abs_le.mpr ⟨by linarith [ht.1, hc.2], by linarith [ht.2, hc.1]⟩
  rw [comparisonReplacementLaw_target P v eps heps hv hs hlegal]
  unfold ateFunctional
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin d, |cellMass P j * (outcomeMean P true j - outcomeMean P false j) -
        (v (j, true) + v (j, false)) *
          (outcomeMean P true j - outcomeMean P false j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin d, (|auxTable P (j, true) - v (j, true)| +
        |auxTable P (j, false) - v (j, false)|) := by
      apply Finset.sum_le_sum
      intro j _
      rw [← sub_mul, abs_mul]
      calc
        _ ≤ |cellMass P j - (v (j, true) + v (j, false))| * 1 :=
          mul_le_mul_of_nonneg_left (hcontrast j) (abs_nonneg _)
        _ = |(auxTable P (j, true) - v (j, true)) +
            (auxTable P (j, false) - v (j, false))| := by
          rw [mul_one, hcell]; congr 1; ring
        _ ≤ _ := abs_add_le _ _
    _ = _ := by simp only [Fintype.sum_prod_type, Fintype.sum_bool]

end CausalSmith.Stat.AnnotationRarearmFrontier

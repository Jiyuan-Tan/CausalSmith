module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Basic

/-!
Finite normalization with a total fallback outside the public parameter domain.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[Normalize finite nonnegative masses; a supplied PMF handles illegal total inputs](goal).
-/
noncomputable def normalizedPMF {alpha : Type} [Fintype alpha]
    (mass : alpha → Real) (fallback : PMF alpha) : PMF alpha :=
  let f := fun z => ENNReal.ofReal (mass z)
  if h : (∑' z, f z) ≠ 0 ∧ (∑' z, f z) ≠ ⊤ then PMF.normalize f h.1 h.2 else fallback
/--
[For a success probability](hyp:r) and [a binary outcome](hyp:b), [the Bernoulli atom mass](goal) is the success probability for a success and its complement for a failure.
-/
noncomputable def bernoulliMass (r : Real) (b : Bool) : Real := if b then r else 1 - r

/-- [Under the stated inputs and conditions](hyp:alpha,mass,fallback,hnonneg,hsum,z), Normalizing an already normalized nonnegative table preserves every atom.  This gives [the stated result](goal).-/
-- @node: normalizedPMF_toReal
lemma normalizedPMF_toReal {alpha : Type} [Fintype alpha]
    (mass : alpha → Real) (fallback : PMF alpha)
    (hnonneg : ∀ z, 0 ≤ mass z) (hsum : ∑ z, mass z = 1) (z : alpha) :
    (normalizedPMF mass fallback z).toReal = mass z := by
  have htotal : (∑' z, ENNReal.ofReal (mass z)) = 1 := by
    rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun z _ => hnonneg z),
      hsum, ENNReal.ofReal_one]
  simp only [normalizedPMF, htotal, ne_eq, one_ne_zero, ENNReal.one_ne_top,
    not_false_eq_true, and_self, dite_true, PMF.normalize_apply, inv_one, mul_one]
  exact ENNReal.toReal_ofReal (hnonneg z)

end CausalSmith.Stat.AnnotationRarearmFrontier

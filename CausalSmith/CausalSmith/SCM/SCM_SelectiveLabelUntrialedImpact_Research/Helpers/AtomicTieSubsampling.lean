import Mathlib.Data.Real.Basic

/-!
# Atomic-tie subsampling support

This file isolates the global-sign argument used at the zero atom in the
atomic-tie subsampling proof.  It is independent of the eventual finite-fan,
conditional-quantile, and probability-space encodings.
-/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

/-- The joint endpoint limit statistic `H(g) = max {D_L(g), -D_U(g)}`. -/
def endpointLimitStatistic {V : Type*} (DLower DUpper : V → ℝ) (g : V) : ℝ :=
  max (DLower g) (-DUpper g)

/-- The centered subsampling statistic
`K_a(g) = max {D_L(g) - D_L(a), D_U(a) - D_U(g)}`. -/
def centeredEndpointStatistic {V : Type*} (DLower DUpper : V → ℝ) (a g : V) : ℝ :=
  max (DLower g - DLower a) (DUpper a - DUpper g)

/-- If the centering direction is at the zero atom, then a negative centered
subsampling statistic forces the uncentered endpoint statistic to be negative.
This is the global-sign implication used in equation (21) of the core proof;
it requires neither a selected fan cone nor uniqueness of an endpoint slope. -/
theorem atomic_tie_global_sign
    {V : Type*} (DLower DUpper : V → ℝ) (a g : V)
    (ha : endpointLimitStatistic DLower DUpper a = 0)
    (hg : centeredEndpointStatistic DLower DUpper a g < 0) :
    endpointLimitStatistic DLower DUpper g < 0 := by
  have haLower : DLower a ≤ 0 := by
    calc
      DLower a ≤ max (DLower a) (-DUpper a) := le_max_left _ _
      _ = 0 := ha
  have haUpper : 0 ≤ DUpper a := by
    apply neg_nonpos.mp
    calc
      -DUpper a ≤ max (DLower a) (-DUpper a) := le_max_right _ _
      _ = 0 := ha
  have hgParts :
      DLower g - DLower a < 0 ∧ DUpper a - DUpper g < 0 := by
    exact max_lt_iff.mp hg
  have hgLower : DLower g < 0 :=
    lt_of_lt_of_le (sub_neg.mp hgParts.1) haLower
  have hgUpperPos : 0 < DUpper g :=
    lt_of_le_of_lt haUpper (sub_neg.mp hgParts.2)
  have hgUpper : -DUpper g < 0 := neg_neg_of_pos hgUpperPos
  exact max_lt hgLower hgUpper

end CausalSmith.SCM.SelectiveLabelUntrialedImpact

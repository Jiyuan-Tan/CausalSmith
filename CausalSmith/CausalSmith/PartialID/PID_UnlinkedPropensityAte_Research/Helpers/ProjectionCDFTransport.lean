module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Finite-mass CDF normalization bounds

This file isolates the algebraic normalization step needed when comparing
finite measures of unequal positive mass.  It is independent of the particular
projection statistic: after each submeasure is normalized to a probability
measure, multiplying the normalized CDF discrepancy by the smaller mass costs
at most the raw CDF discrepancy plus the mass discrepancy.
-/

public section

open MeasureTheory Set

namespace CausalSmith.PartialID.UnlinkedPropensityAte

end CausalSmith.PartialID.UnlinkedPropensityAte

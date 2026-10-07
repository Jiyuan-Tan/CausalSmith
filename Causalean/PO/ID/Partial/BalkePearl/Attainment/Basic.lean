/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.PO.ID.Partial.BalkePearl.ClosedForm

/-! # Observed cell probabilities form a distribution per instrument value

In the binary Balke–Pearl instrumental-variable model, the observed data are the eight cell
probabilities p(y, d | z) of outcome y and treatment d given instrument value z. This file proves
that these cells are nonnegative and that, under the Balke–Pearl base assumptions, the four cells
at each instrument value sum to one. Both facts are read off the realized latent response-type
table and are the arithmetic inputs for checking that explicit latent tables are feasible.

## Main results

* `POBalkePearlSystem.cellProb_nonneg` — every observed cell probability is nonnegative.
* `POBalkePearlSystem.sum_cellProb_eq_one` — for each instrument value, the four
  outcome–treatment cell probabilities sum to one (under the base assumptions).
-/

public section

namespace Causalean
namespace PO

open MeasureTheory

namespace POBalkePearlSystem

variable {P : POSystem} (S : POBalkePearlSystem P)

/-! ### Validity of the observed cell probabilities -/

/-- Observed cell probabilities are nonnegative. -/
lemma cellProb_nonneg (y d z : Bool) : 0 ≤ S.cellProb y d z :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- Under [the Balke-Pearl IV base assumptions](hyp:hA), [for every instrument value `z`,
the four observed outcome-treatment cell probabilities sum to one](goal). -/
lemma sum_cellProb_eq_one (hA : S.BaseAssumptions) (z : Bool) :
    ∑ y : Bool, ∑ d : Bool, S.cellProb y d z = 1 := by
  have h : ∀ y d, S.cellProb y d z = _ := fun y d => S.cellProb_eq_sum_latent hA y d z
  have hs := S.latentProb_sum_eq_one
  simp only [Fintype.sum_bool] at hs
  simp only [Fintype.sum_bool, h]
  cases z <;>
    simp only [dArm, yArm, Fintype.sum_bool] <;>
    norm_num <;>
    linarith [hs]

end POBalkePearlSystem

end PO
end Causalean

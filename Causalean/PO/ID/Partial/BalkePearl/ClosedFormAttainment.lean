/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.PO.ID.Partial.BalkePearl.Attainment.Lower
public import Causalean.PO.ID.Partial.BalkePearl.Attainment.Upper
public import Causalean.PO.ID.Partial.BalkePearl.IntervalForm

/-! # Attainment of the Balke–Pearl closed-form endpoints

The Balke–Pearl closed-form bounds on the average treatment effect with a binary instrument,
treatment and outcome are exact: the largest of the eight lower expressions equals the infimum,
and the smallest of the eight upper expressions equals the supremum, of the linear-program
objective over all latent response-type tables compatible with the observed cell probabilities.
The proof combines validity of the closed form (every feasible table has objective between the
two endpoints) with explicit feasible tables attaining each endpoint. This is a statement about
the linear program; that every feasible table comes from an actual potential-outcome model is
the separate sharpness theorem `balkePearl_sharp`.

## Main results

* `csInf_BPIdentifiedInterval_eq_bpLower` — the infimum of the identified set is `bpLower`.
* `csSup_BPIdentifiedInterval_eq_bpUpper` — the supremum of the identified set is `bpUpper`.
* `bpLower_bpUpper_eq_csInf_csSup` — both equalities together, under the base assumptions.
-/

public section

namespace Causalean
namespace PO

open MeasureTheory

namespace POBalkePearlSystem

variable {P : POSystem} (S : POBalkePearlSystem P)

/-! ### The lower endpoint is attained -/

/-- **The closed-form lower endpoint is exactly the LP minimum.** Under [the Balke-Pearl
IV base assumptions](hyp:hA), [the infimum of the Balke-Pearl identified interval equals
the closed-form lower bound `bpLower`](goal). -/
theorem csInf_BPIdentifiedInterval_eq_bpLower (hA : S.BaseAssumptions) :
    sInf (S.BPIdentifiedInterval hA) = S.bpLower := by
  refine le_antisymm ?_ ?_
  · exact csInf_le (S.bddBelow_BPIdentifiedInterval hA) (S.bpLower_mem_BPIdentifiedInterval hA)
  · refine le_csInf ⟨_, S.bpLower_mem_BPIdentifiedInterval hA⟩ ?_
    rintro b ⟨x, rfl⟩
    exact S.bpLower_le_BPObjective hA x.2

/-! ### The upper endpoint is attained -/

/-- **The closed-form upper endpoint is exactly the LP maximum.** Under [the Balke-Pearl
IV base assumptions](hyp:hA), [the supremum of the Balke-Pearl identified interval equals
the closed-form upper bound `bpUpper`](goal). -/
theorem csSup_BPIdentifiedInterval_eq_bpUpper (hA : S.BaseAssumptions) :
    sSup (S.BPIdentifiedInterval hA) = S.bpUpper := by
  refine le_antisymm ?_ ?_
  · refine csSup_le ⟨_, S.bpUpper_mem_BPIdentifiedInterval hA⟩ ?_
    rintro b ⟨x, rfl⟩
    exact S.BPObjective_le_bpUpper hA x.2
  · exact le_csSup (S.bddAbove_BPIdentifiedInterval hA) (S.bpUpper_mem_BPIdentifiedInterval hA)

/-! ### Sharpness of the closed form -/

/-- **The Balke-Pearl closed form is sharp.** Under [the Balke-Pearl IV base
assumptions](hyp:hA), [the interval `[bpLower, bpUpper]`, computed from the observed cell
probabilities alone, has both endpoints attained by observationally-equivalent latent
tables — equivalently, `bpLower` is the infimum and `bpUpper` is the supremum of the
Balke-Pearl identified interval](goal). So no smaller interval contains every average
treatment effect compatible with the data: the bound cannot be improved without further
assumptions. -/
theorem bpLower_bpUpper_eq_csInf_csSup (hA : S.BaseAssumptions) :
    S.bpLower = sInf (S.BPIdentifiedInterval hA) ∧
      S.bpUpper = sSup (S.BPIdentifiedInterval hA) :=
  ⟨(S.csInf_BPIdentifiedInterval_eq_bpLower hA).symm,
   (S.csSup_BPIdentifiedInterval_eq_bpUpper hA).symm⟩

end POBalkePearlSystem

end PO
end Causalean

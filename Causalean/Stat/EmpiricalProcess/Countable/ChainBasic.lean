module
public import Causalean.Stat.EmpiricalProcess.Countable.Basic

/-!
# Weighted chain sums and restricted energy

Common notation for finite signed weighted set sums, their real suprema,
and squared-weight energy in a containing set. These definitions carry no
maximal inequality and impose no cardinality restriction on the set family.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- [The chain supremum](goal) of [a family of sets](hyp:B) on [a
sample](hyp:x) with [real sample weights w](hyp:w) and [a sign vector
σ](hyp:σ) is [the supremum over the family of the absolute value of
Σ_j σ_j w_j taken over the observations lying in the set](step:1).

The weights may have either sign.
-/
def chainSignSup {Ω ι : Type*} (B : ι → Set Ω) {n : ℕ}
    (x : Fin n → Ω) (w : Fin n → ℝ) (σ : Fin n → Bool) : ℝ := by
  classical
  exact ⨆ i, |∑ j, if x j ∈ B i then (if σ j then (1 : ℝ) else -1) * w j else 0|

/-- [The chain energy](goal) of [a set U](hyp:U) on [a sample](hyp:x) with
[real sample weights w](hyp:w) is [the sum of the squared weights w_j over
the observations lying in U](step:1). -/
def chainEnergy {Ω : Type*} (U : Set Ω) {n : ℕ}
    (x : Fin n → Ω) (w : Fin n → ℝ) : ℝ := by
  classical
  exact ∑ j, if x j ∈ U then w j ^ 2 else 0

end Causalean.Stat.EmpiricalProcess.Countable

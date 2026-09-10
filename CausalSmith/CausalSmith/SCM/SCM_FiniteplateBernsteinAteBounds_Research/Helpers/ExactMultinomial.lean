import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.MomentGeometry
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Causalean.PO.ID.Partial.Inference.Basic

/-! # Exact finite multinomial inversion -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

open scoped BigOperators ENNReal

-- @env: S3
variable (m n : ℕ) (α : ℝ)

/-- The nominal confidence error probability lies strictly between zero and one. -/
def ValidConfidenceLevel (α : ℝ) : Prop :=
  0 < α ∧ α < 1 -- @realizes alpha(alpha in the open unit interval)

/-- The finite set of bounded aggregate count vectors summing to `n`. -/
def aggregateFinset (m n : ℕ) : Finset (CountIndex m → Fin (n + 1)) :=
  Finset.univ.filter (fun z => ∑ c, (z c).val = n)

/-- Aggregate count sample space. -/
abbrev AggregateSpace (m n : ℕ) := {z // z ∈ aggregateFinset m n}
  -- @realizes H_n(aggregate counts summing to n)

lemma aggregateSpace_nonempty (m n : ℕ) : Nonempty (AggregateSpace m n) := by
  sorry

noncomputable instance (m n : ℕ) : Nonempty (AggregateSpace m n) :=
  aggregateSpace_nonempty m n

/-- Natural count in one aggregate cell. -/
def aggregateCount {m n : ℕ} (z : AggregateSpace m n) (c : CountIndex m) : ℕ :=
  (z.1 c).val

/-- Empirical count-law vector `z/n`. -/
noncomputable def empiricalCountLaw {m n : ℕ}
    (z : AggregateSpace m n) (c : CountIndex m) : ℝ :=
  (aggregateCount z c : ℝ) / n
  -- @realizes hat_b(empirical aggregate count law)

/-- The exact multinomial probability mass function. -/
noncomputable def multinomialPmf {m : ℕ} (n : ℕ)
    (bprime : CountIndex m → ℝ) (z : AggregateSpace m n) : ℝ :=
  (n.factorial : ℝ) / (∏ c, ((aggregateCount z c).factorial : ℝ)) *
    ∏ c, (bprime c) ^ aggregateCount z c
  -- @realizes b_prime(candidate simplex-valued count law)

/-- Extended-real multinomial likelihood-ratio deviance. -/
noncomputable def deviance {m : ℕ} (n : ℕ)
    (z : AggregateSpace m n) (bprime : CountIndex m → ℝ) : EReal :=
  if ∃ c, 0 < aggregateCount z c ∧ bprime c = 0 then ⊤
  else ((2 * ∑ c with 0 < aggregateCount z c,
    (aggregateCount z c : ℝ) *
      Real.log ((aggregateCount z c : ℝ) / ((n : ℝ) * bprime c))) : ℝ)
  -- @realizes T_n(tie-comparable extended deviance with +infinity zero-cell branch)

/-- Exact tie-inclusive upper-tail probability. -/
noncomputable def exactPValue {m : ℕ} (n : ℕ)
    (bprime : CountIndex m → ℝ) (z : AggregateSpace m n) : ℝ :=
  ∑ w : AggregateSpace m n with deviance n z bprime ≤ deviance n w bprime,
    multinomialPmf n bprime w
  -- @realizes P_n(exact upper tail including every deviance tie)

/-- The nonrandomized exact likelihood-inversion region. -/
-- @node: def:exact-multinomial-region
noncomputable def exactMultinomialRegion {m : ℕ} (n : ℕ) (α : ℝ)
    (zobs : AggregateSpace m n) : Set (CountIndex m → ℝ) :=
  {bprime | ValidConfidenceLevel α ∧
    bprime ∈ stdSimplex ℝ (CountIndex m) ∧
    α < exactPValue n bprime zobs}
  -- @realizes z_obs(observed aggregate count vector)
  -- @realizes alpha(range threaded through ValidConfidenceLevel)
  -- @realizes R_n_alpha(nonrandomized inversion P_n>alpha)

/-- The union of all sharp intervals over count laws retained by the exact test. -/
-- @node: def:whole-set-confidence
noncomputable def wholeSetConfidenceSet (m n : ℕ) (ε α : ℝ)
    (zobs : AggregateSpace m n) : Set ℝ :=
  {t | ∃ bprime,
    bprime ∈ exactMultinomialRegion n α zobs ∩ bernsteinMomentBody m ε ∧
      t ∈ Set.Icc (lowerEndpoint m ε bprime) (upperEndpoint m ε bprime)}
  -- @realizes C_n_alpha(union of sharp intervals over retained feasible count laws)

end CausalSmith.SCM.FiniteplateBernsteinAteBounds

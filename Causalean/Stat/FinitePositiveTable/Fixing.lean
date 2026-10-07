module
public import Causalean.Stat.FinitePositiveTable.Marginals

/-!
# Coordinate fixing and sequential expansions

This module defines graph-independent coordinate fixing for positive finite tables and records
its one-step and sequential conditional-factor expansions.
-/

@[expose] public section

open Finset
open scoped BigOperators

noncomputable section

namespace Causalean.Stat.FinitePositiveTable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {r : V → ℕ}

/-- The [kernel](hyp:q), [coordinate](hyp:v), and [conditioning set](hyp:C) determine [the
kernel after fixing that coordinate](goal) [by dividing each profile's mass by the kernel's
conditional mass of that profile's value at the coordinate given its values on the conditioning
set](step:1). The division follows the real-number convention that division by zero gives zero,
so the result is the intended quotient only when the conditional mass is nonzero, as it is for a
strictly positive kernel. -/
def fixKernelCoordinate (q : Kernel r) (v : V) (C : Finset V) : Kernel r :=
  fun x ↦ q x / kernelConditionalMass q v C x (x v)

/-- The [positive table](hyp:p), [coordinate](hyp:v), and [conditioning set](hyp:C) determine
[the fixed kernel](goal) [as the fixed mass kernel](step:1). -/
def fixCoordinate (p : PositiveTable r) (v : V) (C : Finset V) : Kernel r :=
  fixKernelCoordinate p.mass v C

/-- The [coordinate type](hyp:V) determines one algebraic fixing step, consisting of the
coordinate to remove and the coordinates used for conditioning. -/
structure FixingStep (V : Type u) where
  /-- The coordinate removed from the random kernel. -/
  coordinate : V
  /-- The coordinates conditioned on when the coordinate is fixed. -/
  conditioning : Finset V

/-- The [list of fixing steps](hyp:steps) satisfies [algebraic validity](goal) when [its fixed
coordinates are distinct](step:1) and [no step conditions on its own coordinate](step:2). -/
def FixingSequenceValid (steps : List (FixingStep V)) : Prop :=
  (steps.map (fun s ↦ s.coordinate)).Nodup ∧
    ∀ s ∈ steps, s.coordinate ∉ s.conditioning

/-- The [kernel](hyp:q) and a list of fixing steps determine [the sequentially fixed
kernel](goal): [an empty list leaves the kernel unchanged](step:1), and [a nonempty list fixes
its head before continuing with its tail](step:2). -/
def fixKernelSequence (q : Kernel r) : List (FixingStep V) → Kernel r
  | [] => q
  | s :: ss => fixKernelSequence (fixKernelCoordinate q s.coordinate s.conditioning) ss

/-- The [positive table](hyp:p) and [list of fixing steps](hyp:steps) determine [the
sequentially fixed kernel](goal) [as the sequentially fixed mass kernel](step:1). -/
def fixSequence (p : PositiveTable r) (steps : List (FixingStep V)) : Kernel r :=
  fixKernelSequence p.mass steps

/-- The [kernel](hyp:q) and a list of fixing steps determine [the product of the
successive conditional factors](goal), evaluated at a profile: [an empty list has product
one](step:1), and [a nonempty list multiplies the kernel's conditional mass for its first step by
the product for the remaining steps computed from the kernel after that first step has been
fixed](step:2). -/
def fixingConditionalProduct (q : Kernel r) : List (FixingStep V) → ProfileSpace r → ℝ
  | [], _ => 1
  | s :: ss, x =>
      kernelConditionalMass q s.coordinate s.conditioning x (x s.coordinate) *
        fixingConditionalProduct
          (fixKernelCoordinate q s.coordinate s.conditioning) ss x

/-- For [a kernel](hyp:q), [a coordinate and conditioning set](hyp:v,C), and [a profile](hyp:x),
[one fixing step has its defining pointwise quotient form](goal). -/
theorem fixKernelCoordinate_apply (q : Kernel r) (v : V) (C : Finset V)
    (x : ProfileSpace r) :
    fixKernelCoordinate q v C x =
      q x / kernelConditionalMass q v C x (x v) := by
  rfl

/-- For [a pointwise strictly positive kernel](hyp:q,hq), [a coordinate and conditioning
set](hyp:v,C), and [a profile](hyp:x), [one fixing step equals the original mass times the
conditioning marginal divided by the joint marginal](goal). -/
theorem fixKernelCoordinate_eq_mul_marginal_div {q : Kernel r}
    (hq : q.IsStrictlyPositive) (v : V) (C : Finset V) (x : ProfileSpace r) :
    fixKernelCoordinate q v C x =
      q x * kernelMarginalMass q C x /
        kernelMarginalMass q (insert v C) x := by
  unfold fixKernelCoordinate kernelConditionalMass
  rw [Function.update_eq_self]
  have hJoint : kernelMarginalMass q (insert v C) x ≠ 0 :=
    (kernelMarginalMass_pos hq (insert v C) x).ne'
  by_cases hzero : kernelMarginalMass q (insert v C) x = 0
  · exact (hJoint hzero).elim
  · exact div_div_eq_mul_div _ _ _

/-- For [a positive table](hyp:p), [a coordinate and conditioning set](hyp:v,C), and [a
profile](hyp:x), [one fixing step has the corresponding table marginal-ratio expansion](goal). -/
theorem fixCoordinate_eq_mul_marginal_div (p : PositiveTable r)
    (v : V) (C : Finset V) (x : ProfileSpace r) :
    fixCoordinate p v C x =
      p.mass x * marginalMass p C x / marginalMass p (insert v C) x := by
  exact fixKernelCoordinate_eq_mul_marginal_div p.mass_pos v C x

/-- For [a pointwise strictly positive kernel](hyp:q,hq), [a coordinate](hyp:v), and [a
conditioning set](hyp:C), [fixing preserves pointwise strict positivity](goal). -/
theorem fixKernelCoordinate_pos {q : Kernel r} (hq : q.IsStrictlyPositive)
    (v : V) (C : Finset V) :
    (fixKernelCoordinate q v C).IsStrictlyPositive := by
  intro x
  exact div_pos (hq x) (kernelConditionalMass_pos hq v C x (x v))

/-- For [a pointwise strictly positive kernel](hyp:q,hq) and [a list of fixing steps](hyp:steps),
[sequential fixing preserves pointwise strict positivity](goal). -/
theorem fixKernelSequence_pos {q : Kernel r} (hq : q.IsStrictlyPositive)
    (steps : List (FixingStep V)) :
    (fixKernelSequence q steps).IsStrictlyPositive := by
  induction steps generalizing q with
  | nil => exact hq
  | cons s ss ih =>
      exact ih (fixKernelCoordinate_pos hq s.coordinate s.conditioning)

/-- For [a positive table](hyp:p), [a list of fixing steps](hyp:steps), and [a profile](hyp:x),
[the sequentially fixed kernel is nonnegative](goal). -/
theorem fixSequence_nonneg (p : PositiveTable r) (steps : List (FixingStep V))
    (x : ProfileSpace r) : 0 ≤ fixSequence p steps x := by
  exact (fixKernelSequence_pos p.mass_pos steps x).le

/-- For [a pointwise strictly positive kernel](hyp:q,hq), [a list of fixing steps](hyp:steps),
and [a profile](hyp:x), [the product of successive conditional factors is strictly positive](goal). -/
theorem fixingConditionalProduct_pos {q : Kernel r} (hq : q.IsStrictlyPositive)
    (steps : List (FixingStep V)) (x : ProfileSpace r) :
    0 < fixingConditionalProduct q steps x := by
  induction steps generalizing q with
  | nil => simp [fixingConditionalProduct]
  | cons s ss ih =>
      exact mul_pos
        (kernelConditionalMass_pos hq s.coordinate s.conditioning x (x s.coordinate))
        (ih (fixKernelCoordinate_pos hq s.coordinate s.conditioning))

/-- For [a pointwise strictly positive kernel](hyp:q,hq), [an algebraically valid list of fixing
steps](hyp:steps,hvalid), and [a profile](hyp:x), [sequential fixing equals the original mass
divided by the product of its successive conditional factors](goal). -/
theorem fixKernelSequence_eq_div_conditionalProduct {q : Kernel r}
    (hq : q.IsStrictlyPositive) (steps : List (FixingStep V))
    (hvalid : FixingSequenceValid steps) (x : ProfileSpace r) :
    fixKernelSequence q steps x = q x / fixingConditionalProduct q steps x := by
  induction steps generalizing q with
  | nil => simp [fixKernelSequence, fixingConditionalProduct]
  | cons s ss ih =>
      rw [fixKernelSequence, ih
        (fixKernelCoordinate_pos hq s.coordinate s.conditioning)]
      · simp only [fixKernelCoordinate_apply, fixingConditionalProduct, div_div]
      · exact ⟨hvalid.1.tail, fun t ht ↦ hvalid.2 t (List.mem_cons_of_mem s ht)⟩

/-- For [a positive table](hyp:p), [an algebraically valid list of fixing steps](hyp:steps,hvalid),
and [a profile](hyp:x), [the sequentially fixed kernel at that profile equals the table's mass
there divided by the product of the successive conditional factors, each computed from the
kernel obtained after the earlier fixing steps](goal). -/
theorem fixSequence_eq_div_conditionalProduct (p : PositiveTable r)
    (steps : List (FixingStep V)) (hvalid : FixingSequenceValid steps)
    (x : ProfileSpace r) :
    fixSequence p steps x = p.mass x / fixingConditionalProduct p.mass steps x := by
  exact fixKernelSequence_eq_div_conditionalProduct p.mass_pos steps hvalid x

/-- For [a kernel](hyp:q), [a first fixing step](hyp:s), [the
remaining fixing steps](hyp:ss), and [a profile](hyp:x), [the first conditional-product factor
is the ratio of its joint and conditioning marginals](goal). -/
theorem fixingConditionalProduct_cons_eq_marginal_ratio {q : Kernel r}
    (s : FixingStep V) (ss : List (FixingStep V))
    (x : ProfileSpace r) :
    fixingConditionalProduct q (s :: ss) x =
      (kernelMarginalMass q (insert s.coordinate s.conditioning) x /
        kernelMarginalMass q s.conditioning x) *
      fixingConditionalProduct
        (fixKernelCoordinate q s.coordinate s.conditioning) ss x := by
  simp only [fixingConditionalProduct, kernelConditionalMass, Function.update_eq_self]

end Causalean.Stat.FinitePositiveTable

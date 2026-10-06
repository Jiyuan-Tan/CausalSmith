module
public import Causalean.Mathlib.Probability.Independence.Conditional.JoinedBlockProduct

/-!
# Shifted scores on joined training and evaluation blocks

A shifted held-out score is represented as a measurable score on the union of
the training coordinates and its held-out block. This representation connects
shifted products to joined-view conditional factorization.
-/

@[expose] public section

open MeasureTheory
open Causalean.Mathlib.Probability.Independence

namespace Causalean.Mathlib.Probability.Independence.Conditional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- [The training block](hyp:B0), [one evaluation block](hyp:B1), [a held-out
score](hyp:f), and [a training-block shift](hyp:a) define [the shifted score on their
joined coordinate view](goal), [by subtracting the training shift from the held-out
score](step:1). -/
noncomputable def shiftedJoinedScore (B0 B1 : Finset ι)
    (f : ((i : {i // i ∈ B1}) → Ω i.val) → ℝ)
    (a : ((i : {i // i ∈ B0}) → Ω i.val) → ℝ) :
    ((i : {i // i ∈ B0 ∪ B1}) → Ω i.val) → ℝ :=
  fun y =>
    f (fun i => y ⟨i.val, Finset.mem_union.mpr (Or.inr i.property)⟩) -
    a (fun i => y ⟨i.val, Finset.mem_union.mpr (Or.inl i.property)⟩)

/-- [The training block and evaluation block](hyp:B0,B1), [a held-out score](hyp:f),
[a training-block shift](hyp:a), and [a full product point](hyp:x) imply that [evaluating
the joined shifted score equals the held-out score minus its training shift](goal). -/
theorem shiftedJoinedScore_comp_proj (B0 B1 : Finset ι)
    (f : ((i : {i // i ∈ B1}) → Ω i.val) → ℝ)
    (a : ((i : {i // i ∈ B0}) → Ω i.val) → ℝ)
    (x : ∀ i, Ω i) :
    shiftedJoinedScore B0 B1 f a (finsetCoordProj (B0 ∪ B1) x) =
      f (finsetCoordProj B1 x) - a (finsetCoordProj B0 x) := rfl

/-- [The training block and evaluation block](hyp:B0,B1), [a held-out score](hyp:f),
[a training-block shift](hyp:a), and [measurability of both functions](hyp:hf,ha) imply
that [the joined shifted score is measurable](goal). -/
@[fun_prop] theorem measurable_shiftedJoinedScore (B0 B1 : Finset ι)
    (f : ((i : {i // i ∈ B1}) → Ω i.val) → ℝ)
    (a : ((i : {i // i ∈ B0}) → Ω i.val) → ℝ)
    (hf : Measurable f) (ha : Measurable a) :
    Measurable (shiftedJoinedScore B0 B1 f a) := by
  unfold shiftedJoinedScore
  apply Measurable.sub
  · exact hf.comp (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))
  · exact ha.comp (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))

end Causalean.Mathlib.Probability.Independence.Conditional

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-! # Measurability of transport along an equality of indices

Moving a value between the fibres of an indexed family along a proof that the two indices are
equal does not disturb measurability, and neither does transporting the codomain index of a
measurable function. Both facts are immediate once the index equality is substituted away, but
they are needed wherever an indexed family is re-indexed, so they are stated once here.
-/

public section

namespace Causalean.Mathlib.MeasureTheory

/-- For [an equality between two indices of a measurable family](hyp:hab), [transporting a value
from the fibre over the first index to the fibre over the second is measurable](goal). -/
@[fun_prop]
theorem measurable_cast_family {I : Type*} {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] {a b : I} (hab : a = b) :
    Measurable (cast (congrArg X hab) : X a → X b) := by
  subst hab
  exact measurable_id

/-- For [an equality between two indices of a measurable family](hyp:h) and [a measurable
function into the fibre over the first index](hyp:f,hf), [transporting that function's codomain
to the fibre over the second index leaves it measurable](goal). -/
@[fun_prop]
theorem measurable_family_cast {I γ : Type*} {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] [MeasurableSpace γ]
    {v w : I} (h : v = w) {f : γ → X v} (hf : Measurable f) :
    Measurable (fun x => (h ▸ f x : X w)) := by
  subst h
  exact hf

end Causalean.Mathlib.MeasureTheory

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Potential outcomes under an exposure mapping

Each assignment `z ∈ Ω` induces a fixed *randomization potential outcome* `yr i z` for
unit `i`; these are fixed features of the finite population, not random.  Aronow & Samii's
**Condition 1 (properly specified exposure mapping)** says interference acts only through
the exposure: if `expo i z = expo i z'` then `yr i z = yr i z'`.  Equivalently, the
randomization potential outcome factors through the exposure, `yr i z = y i (expo i z)`
for exposure-indexed potential outcomes `y : ι → Δ → ℝ`.

We take that factored form as primitive: `Yobs y f θ i z = y i (expo f θ i z)` is unit
`i`'s observed outcome under assignment `z`.  **Condition 2 (consistency)** then holds as a
lemma: `Yobs i z = ∑_d 1(expo i = d) · y i d`.
-/

import Causalean.Experimentation.DesignBased.Exposure

/-! # Potential outcomes under exposure mappings

This file represents a unit's outcome under an assignment by evaluating its potential outcome at
the exposure induced by that assignment. It supplies the properly specified exposure condition and
the observed-outcome construction used by the design-based interference results. -/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {Ω : Type*} [Fintype Ω]
variable {ι Θ Δ : Type*} [DecidableEq Δ]

/-- For [potential outcomes indexed by unit and exposure level](hyp:y), [randomization potential
outcomes indexed by unit and assignment](hyp:yr), [an assignment-to-exposure mapping](hyp:f), and
[unit-level attributes used by that mapping](hyp:θ), [the properly specified exposure condition](goal)
states that, for every unit and every assignment, the randomization potential outcome equals the
potential outcome at the exposure induced for that unit by the assignment. -/
def ProperlySpecified (y : ι → Δ → ℝ) (yr : ι → Ω → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ) : Prop :=
  ∀ i z, yr i z = y i (expo f θ i z)

/-- For [potential outcomes indexed by unit and exposure level](hyp:y), [an assignment-to-exposure
mapping](hyp:f), [unit-level attributes used by that mapping](hyp:θ), [a unit](hyp:i), and [an
assignment](hyp:z), [the observed outcome](goal) is that unit's potential outcome at the exposure
induced by the assignment. -/
def Yobs (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (z : Ω) : ℝ :=
  y i (expo f θ i z)

variable [Fintype Δ]

omit [Fintype Ω] in
/-- **Condition 2 (consistency).** [The observed outcome of unit `i` under assignment `z` equals
the sum, over every exposure level, of the exposure indicator times the exposure-indexed
potential outcome](goal). -/
lemma Yobs_eq_sum (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (z : Ω) :
    Yobs y f θ i z = ∑ d, expoInd f θ i d z * y i d := by
  unfold Yobs expoInd FiniteDesign.ind
  rw [Finset.sum_eq_single (expo f θ i z)
      (fun d _ hd => by rw [if_neg (fun h => hd h.symm), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
  simp

omit [Fintype Ω] [Fintype Δ] in
/-- On the event `expo i = d`, the observed outcome agrees with the potential outcome
`y i d`; hence `1(expo i = d)·Yobs i = 1(expo i = d)·y i d`. -/
lemma expoInd_mul_Yobs (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (d : Δ) (z : Ω) :
    expoInd f θ i d z * Yobs y f θ i z = expoInd f θ i d z * y i d := by
  unfold expoInd FiniteDesign.ind Yobs
  by_cases h : expo f θ i z = d <;> simp [h]

omit [Fintype Ω] [Fintype Δ] in
/-- Squared on-event substitution: `1(expo i = d)·(Yobs i)² = 1(expo i = d)·(y i d)²`. -/
lemma expoInd_mul_Yobs_sq (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (d : Δ) (z : Ω) :
    expoInd f θ i d z * (Yobs y f θ i z) ^ 2 = expoInd f θ i d z * (y i d) ^ 2 := by
  unfold expoInd FiniteDesign.ind Yobs
  by_cases h : expo f θ i z = d <;> simp [h]

omit [Fintype Ω] [Fintype Δ] in
/-- On the event `expo i = di`, multiplying the observed outcome for unit `i` by any real
quantity leaves it valid to replace that outcome by potential outcome `y i di`. -/
lemma expoInd₂_mul_Yobs (y : ι → Δ → ℝ) (f : Ω → Θ → Δ) (θ : ι → Θ) (i : ι) (di : Δ)
    (q : Ω → ℝ) (z : Ω) :
    expoInd f θ i di z * q z * Yobs y f θ i z = expoInd f θ i di z * q z * y i di := by
  unfold expoInd FiniteDesign.ind Yobs
  by_cases h : expo f θ i z = di <;> simp [h]

end DesignBased
end Experimentation
end Causalean

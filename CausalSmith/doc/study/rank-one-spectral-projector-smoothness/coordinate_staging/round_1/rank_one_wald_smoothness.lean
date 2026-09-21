import Causalean.Mathlib.Analysis.RankOneGramPseudoinverse
import Causalean.Mathlib.Analysis.LocallyBoundedDerivative

/-!
# Smoothness of the induced rank-one Wald functional

This module composes the algebraic rank-one pseudoinverse with a target direction and an outcome direction.  Its regularity condition is solely a positive isolated upper root of the left Gram matrix and makes no continuity assumption about an eigenvector selector.
-/

open Matrix
open scoped Matrix.Norms.Elementwise

namespace Causalean.Mathlib.Analysis

variable {E : Type*} [Fintype E]

/-- Given [a finite outcome-coordinate type](hyp:E), [an input to the rank-one Wald functional](goal) consists of a real two-row matrix, an outcome direction, and a two-dimensional target direction. -/
abbrev WaldInput (E : Type*) :=
  Matrix (Fin 2) E ℝ × ((E → ℝ) × (Fin 2 → ℝ))

/-- [The regularity region](goal) contains [rank-one Wald inputs](hyp:E) whose left Gram matrix has distinct roots and a strictly positive upper root. -/
def waldRegularSet : Set (WaldInput E) :=
  {x | leftGram x.1 ∈ strictGapSet ∧ 0 < lambda₁ (leftGram x.1)}

/-- Given [a rank-one Wald input](hyp:x), [the choice-free algebraic Wald functional](goal) applies the algebraic rank-one pseudoinverse to the target direction and pairs the result with the outcome direction. -/
noncomputable def algebraicWaldFunctional (x : WaldInput E) : ℝ :=
  dotProduct x.2.1 ((algebraicRankOnePseudoInverse x.1).mulVec x.2.2)

private theorem continuous_leftGram_fst :
    Continuous (fun x : WaldInput E => leftGram x.1) := by
  unfold leftGram
  fun_prop

/-- [The regularity region of the algebraic rank-one Wald functional is open](goal). -/
theorem isOpen_waldRegularSet : IsOpen (waldRegularSet (E := E)) := by
  rw [show waldRegularSet (E := E) =
      (fun x : WaldInput E => leftGram x.1) ⁻¹' strictGapSet ∩
        {x | 0 < lambda₁ (leftGram x.1)} by rfl]
  apply (isOpen_strictGapSet.preimage continuous_leftGram_fst).inter
  have hlambda : Continuous (fun x : WaldInput E => lambda₁ (leftGram x.1)) := by
    unfold lambda₁ rootDiscriminant leftGram
    fun_prop
  exact isOpen_lt continuous_const hlambda

/-- Given [a rank-one Wald input](hyp:x) in [the regularity region](hyp:hx), [the algebraic Wald functional varies continuously differentiably near that input](goal). -/
theorem contDiffAt_algebraicWaldFunctional {x : WaldInput E}
    (hx : x ∈ waldRegularSet (E := E)) :
    ContDiffAt ℝ 1 (algebraicWaldFunctional (E := E)) x := by
  have hpinv : ContDiffAt ℝ 1
      (fun y : WaldInput E => algebraicRankOnePseudoInverse y.1) x :=
    (contDiffAt_algebraicRankOnePseudoInverse hx.1 hx.2).comp x (by fun_prop)
  have hmulVec : ContDiffAt ℝ 1
      (fun y : WaldInput E => (algebraicRankOnePseudoInverse y.1).mulVec y.2.2) x := by
    apply contDiffAt_pi'
    intro i
    simp only [Matrix.mulVec]
    apply ContDiffAt.sum
    intro j _
    exact ((contDiffAt_pi.mp (contDiffAt_pi.mp hpinv i) j).mul (by fun_prop))
  unfold algebraicWaldFunctional dotProduct
  apply ContDiffAt.sum
  intro i _
  exact (by fun_prop : ContDiffAt ℝ 1 (fun y : WaldInput E => y.2.1 i) x).mul
    (contDiffAt_pi.mp hmulVec i)

/-- [The algebraic Wald functional is continuously differentiable throughout its regularity region](goal). -/
theorem contDiffOn_algebraicWaldFunctional :
    ContDiffOn ℝ 1 (algebraicWaldFunctional (E := E)) (waldRegularSet (E := E)) := by
  intro x hx
  exact (contDiffAt_algebraicWaldFunctional hx).contDiffWithinAt

/-- Given [a rank-one Wald input](hyp:x) in [the regularity region](hyp:hx), [the algebraic Wald functional has a bounded Fréchet derivative on some neighborhood of that input](goal). -/
theorem algebraicWaldFunctional_hasLocallyBoundedFDerivAt {x : WaldInput E}
    (hx : x ∈ waldRegularSet (E := E)) :
    HasLocallyBoundedFDerivAt (algebraicWaldFunctional (E := E)) x := by
  exact ContDiffAt.hasLocallyBoundedFDerivAt (contDiffAt_algebraicWaldFunctional hx)

end Causalean.Mathlib.Analysis

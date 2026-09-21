/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.CondIndep.PositiveDensityIntersection.Basic

/-!
# Marginal laws of a three-block product density

This module fixes the canonical three-block coordinates and isolates the Tonelli calculations
identifying every marginal law used by the conditional-independence bridge.  In particular, it
records the laws of the conditioning block, each random block paired with the conditioning block,
and the fully reordered triple.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.CondIndep.PositiveDensityIntersection

universe uA uB uC

/-- The canonical sample space for two random blocks and one conditioning block. -/
abbrev ThreeBlock (A : Type uA) (B : Type uB) (C : Type uC) := A × (B × C)

/-- The first random coordinate of a canonical three-block sample. -/
def firstThreeCoord {A : Type uA} {B : Type uB} {C : Type uC} :
    ThreeBlock A B C → A := fun q ↦ q.1

/-- The second random coordinate of a canonical three-block sample. -/
def secondThreeCoord {A : Type uA} {B : Type uB} {C : Type uC} :
    ThreeBlock A B C → B := fun q ↦ q.2.1

/-- The conditioning coordinate of a canonical three-block sample. -/
def thirdThreeCoord {A : Type uA} {B : Type uB} {C : Type uC} :
    ThreeBlock A B C → C := fun q ↦ q.2.2

section MeasurableCoordinates

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

/-- The first coordinate map on the three-block product is measurable. -/
@[fun_prop] theorem measurable_firstThreeCoord :
    Measurable (@firstThreeCoord A B C) := measurable_fst

/-- The second coordinate map on the three-block product is measurable. -/
@[fun_prop] theorem measurable_secondThreeCoord :
    Measurable (@secondThreeCoord A B C) := measurable_fst.comp measurable_snd

/-- The conditioning-coordinate map on the three-block product is measurable. -/
@[fun_prop] theorem measurable_thirdThreeCoord :
    Measurable (@thirdThreeCoord A B C) := measurable_snd.comp measurable_snd

end MeasurableCoordinates

/-- Three coordinate reference measures determine the right-associated product reference measure
on the canonical three-block sample space. -/
def threeBlockReference {A : Type uA} {B : Type uB} {C : Type uC}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (muA : Measure A) (muB : Measure B) (muC : Measure C) :
    Measure (ThreeBlock A B C) := muA.prod (muB.prod muC)

section DensityObjects

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

/-- Integrating a three-block density over the second random block gives its
first-and-conditioning marginal density. -/
def densityFirstConditioning (muB : Measure B) (d : ThreeBlock A B C → ℝ≥0∞) :
    A × C → ℝ≥0∞ := fun ac ↦ ∫⁻ b, d (ac.1, (b, ac.2)) ∂muB

/-- Integrating a three-block density over the first random block gives its
second-and-conditioning marginal density. -/
def densitySecondConditioning (muA : Measure A) (d : ThreeBlock A B C → ℝ≥0∞) :
    B × C → ℝ≥0∞ := fun bc ↦ ∫⁻ a, d (a, (bc.1, bc.2)) ∂muA

/-- Integrating a three-block density over both random blocks gives its conditioning marginal
density. -/
def densityConditioning (muA : Measure A) (muB : Measure B)
    (d : ThreeBlock A B C → ℝ≥0∞) : C → ℝ≥0∞ :=
  fun c ↦ ∫⁻ a, ∫⁻ b, d (a, (b, c)) ∂muB ∂muA

/-- A three-block density factors given its third block when it is almost everywhere the product
of measurable terms depending on `(A,C)` and `(B,C)`. -/
def ThreeBlockFactors (muA : Measure A) (muB : Measure B) (muC : Measure C)
    (d : ThreeBlock A B C → ℝ≥0∞) : Prop :=
  ∃ a : A × C → ℝ≥0∞, ∃ b : B × C → ℝ≥0∞,
    Measurable a ∧ Measurable b ∧
      d =ᵐ[threeBlockReference muA muB muC]
        (fun q ↦ a (q.1, q.2.2) * b (q.2.1, q.2.2))

/-- The conditional-density identity says that the joint density times the conditioning marginal
equals the product of the two random-block-with-conditioning marginal densities almost
everywhere. -/
def ThreeBlockDensityIdentity (muA : Measure A) (muB : Measure B) (muC : Measure C)
    (d : ThreeBlock A B C → ℝ≥0∞) : Prop :=
  ∀ᵐ q ∂threeBlockReference muA muB muC,
    d q * densityConditioning muA muB d q.2.2 =
      densityFirstConditioning muB d (q.1, q.2.2) *
        densitySecondConditioning muA d (q.2.1, q.2.2)

end DensityObjects

section MarginalLaws

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
variable (muA : Measure A) (muB : Measure B) (muC : Measure C)
variable [SigmaFinite muA] [SigmaFinite muB] [SigmaFinite muC]
variable {d : ThreeBlock A B C → ℝ≥0∞}

/-- For [three reference measures](hyp:muA,muB,muC) and [a measurable three-block density](hyp:hd),
[pushing the density-weighted law to the conditioning coordinate gives its marginal density-weighted
reference measure](goal). -/
theorem map_thirdThreeCoord_withDensity (hd : Measurable d) :
    ((threeBlockReference muA muB muC).withDensity d).map
        (@thirdThreeCoord A B C) =
      muC.withDensity (densityConditioning muA muB d) := by
  /- Prove equality on measurable sets, expand `map` and `withDensity`, then commute the
  `C` integral past the `A` and `B` integrals by Tonelli. -/
  have hdc : Measurable (densityConditioning muA muB d) := by
    unfold densityConditioning
    fun_prop
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [lintegral_map hf measurable_thirdThreeCoord,
    lintegral_withDensity_eq_lintegral_mul _ hd (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hdc hf]
  change (∫⁻ q : A × (B × C), d q * f q.2.2 ∂muA.prod (muB.prod muC)) =
    ∫⁻ c, (∫⁻ a, ∫⁻ b, d (a, (b, c)) ∂muB ∂muA) * f c ∂muC
  rw [lintegral_prod _ (by fun_prop)]
  have hBC (a : A) :
      (∫⁻ b, ∫⁻ c, d (a, (b, c)) * f c ∂muC ∂muB) =
        ∫⁻ c, ∫⁻ b, d (a, (b, c)) * f c ∂muB ∂muC := by
    exact lintegral_lintegral_swap (by fun_prop)
  calc
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ c, d (a, (b, c)) * f c ∂muC ∂muB ∂muA := by
      apply lintegral_congr
      intro a
      rw [lintegral_prod _ (by fun_prop)]
    _ = ∫⁻ a, ∫⁻ c, ∫⁻ b, d (a, (b, c)) * f c ∂muB ∂muC ∂muA := by
      apply lintegral_congr
      exact hBC
    _ = ∫⁻ c, ∫⁻ a, ∫⁻ b, d (a, (b, c)) * f c ∂muB ∂muA ∂muC := by
      exact lintegral_lintegral_swap (by fun_prop)
    _ = _ := by
      apply lintegral_congr
      intro c
      calc
        _ = ∫⁻ a, (∫⁻ b, d (a, (b, c)) ∂muB) * f c ∂muA := by
          apply lintegral_congr
          intro a
          rw [lintegral_mul_const (f c) (by fun_prop)]
        _ = _ := lintegral_mul_const (f c) (by fun_prop)

/-- Pushing a measurable three-block product density to the first and conditioning coordinates
gives their product reference measure weighted by the first-conditioning marginal density. -/
theorem map_firstThird_withDensity (hd : Measurable d) :
    ((threeBlockReference muA muB muC).withDensity d).map
        (fun q ↦ (firstThreeCoord q, thirdThreeCoord q)) =
      (muA.prod muC).withDensity (densityFirstConditioning muB d) := by
  /- Prove equality on measurable sets and use Tonelli to integrate out `B`; the only coordinate
  permutation is between the `B` and `C` integrations. -/
  have hdAC : Measurable (densityFirstConditioning muB d) := by
    unfold densityFirstConditioning
    fun_prop
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [lintegral_map hf (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hd (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hdAC hf]
  change (∫⁻ q : A × (B × C), d q * f (q.1, q.2.2) ∂muA.prod (muB.prod muC)) =
    ∫⁻ ac : A × C, (∫⁻ b, d (ac.1, (b, ac.2)) ∂muB) * f ac ∂muA.prod muC
  rw [lintegral_prod _ (by fun_prop)]
  calc
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ c, d (a, (b, c)) * f (a, c) ∂muC ∂muB ∂muA := by
      apply lintegral_congr
      intro a
      rw [lintegral_prod _ (by fun_prop)]
    _ = ∫⁻ a, ∫⁻ c, ∫⁻ b, d (a, (b, c)) * f (a, c) ∂muB ∂muC ∂muA := by
      apply lintegral_congr
      intro a
      exact lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ a, ∫⁻ c, (∫⁻ b, d (a, (b, c)) ∂muB) * f (a, c) ∂muC ∂muA := by
      apply lintegral_congr
      intro a
      apply lintegral_congr
      intro c
      rw [lintegral_mul_const (f (a, c)) (by fun_prop)]
    _ = _ := by
      rw [lintegral_prod _ (by fun_prop)]

/-- Pushing a measurable three-block product density to the second and conditioning coordinates
gives their product reference measure weighted by the second-conditioning marginal density. -/
theorem map_secondThird_withDensity (hd : Measurable d) :
    ((threeBlockReference muA muB muC).withDensity d).map
        (fun q ↦ (secondThreeCoord q, thirdThreeCoord q)) =
      (muB.prod muC).withDensity (densitySecondConditioning muA d) := by
  /- Prove equality on measurable sets and use Tonelli to integrate out `A`. -/
  have hdBC : Measurable (densitySecondConditioning muA d) := by
    unfold densitySecondConditioning
    fun_prop
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [lintegral_map hf (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hd (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hdBC hf]
  change (∫⁻ q : A × (B × C), d q * f (q.2.1, q.2.2) ∂muA.prod (muB.prod muC)) =
    ∫⁻ bc : B × C, (∫⁻ a, d (a, (bc.1, bc.2)) ∂muA) * f bc ∂muB.prod muC
  rw [lintegral_prod_symm _ (by fun_prop),
    lintegral_prod _ (by fun_prop)]
  calc
    _ = ∫⁻ b, ∫⁻ c, (∫⁻ a, d (a, (b, c)) ∂muA) * f (b, c) ∂muC ∂muB := by
      apply lintegral_congr
      intro b
      apply lintegral_congr
      intro c
      rw [lintegral_mul_const (f (b, c)) (by fun_prop)]
    _ = _ := by
      rw [lintegral_prod _ (by fun_prop)]

/-- Reordering a measurable three-block product density as conditioning-first preserves the law
and transports its density by the same coordinate permutation. -/
theorem map_thirdFirstSecond_withDensity (hd : Measurable d) :
    ((threeBlockReference muA muB muC).withDensity d).map
        (fun q ↦ (thirdThreeCoord q, (firstThreeCoord q, secondThreeCoord q))) =
      (muC.prod (muA.prod muB)).withDensity
        (fun q ↦ d (q.2.1, (q.2.2, q.1))) := by
  /- Prove equality on measurable rectangles, or use successive measurable-equivalence maps and
  product associativity/commutativity. -/
  let e : ThreeBlock A B C ≃ᵐ C × (A × B) :=
    MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm
  have he : MeasurePreserving e (threeBlockReference muA muB muC)
      (muC.prod (muA.prod muB)) := by
    refine ⟨e.measurable, ?_⟩
    change Measure.map e (muA.prod (muB.prod muC)) = muC.prod (muA.prod muB)
    calc
      Measure.map e (muA.prod (muB.prod muC)) =
          Measure.map Prod.swap
            (Measure.map MeasurableEquiv.prodAssoc.symm (muA.prod (muB.prod muC))) := by
        rw [Measure.map_map measurable_swap MeasurableEquiv.prodAssoc.symm.measurable]
        rfl
      _ = muC.prod (muA.prod muB) := by
        rw [← Measure.prodAssoc_prod, MeasurableEquiv.map_symm_map, Measure.prod_swap]
  change Measure.map e ((threeBlockReference muA muB muC).withDensity d) = _
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [lintegral_map hf e.measurable,
    lintegral_withDensity_eq_lintegral_mul _ hd (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf,
    ← he.lintegral_comp (by fun_prop)]
  rfl

end MarginalLaws

end Causalean.Mathlib.CondIndep.PositiveDensityIntersection

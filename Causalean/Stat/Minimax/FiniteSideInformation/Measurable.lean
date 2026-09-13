/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Minimax.FiniteSideInformation.Comparison
import Causalean.Stat.Minimax.FiniteSideInformation.SimplexSpecialization
import Causalean.Experimentation.DesignBased.ProductMeasure
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.TietzeExtension

/-!
# Measurable finite-side-information minimax bridge

This module connects finite-sample side-information procedures with globally
measurable bounded procedures on ambient probability-coordinate tables.  It
proves polynomial continuity of conditional averaging, clipped measurable
extension from the finite simplex, finite-product integral identities, and the
minimax comparison that is stable under surjective reparameterization.
-/

open scoped BigOperators ENNReal
open Set Filter Topology MeasureTheory

namespace Causalean.Stat.Minimax.FiniteSideInformation

open Causalean.Stat
open Causalean.Experimentation.DesignBased

variable {X C : Type*} [Fintype X] [Fintype C]

/-- Given a [side-sample size](hyp:m), an [empirical procedure](hyp:d), and a
[label](hyp:x), the [conditional-average polynomial](goal) is the finite sum of
action-weighted sample monomials. -/
noncomputable def conditionalAveragePolynomial (m : ℕ)
    (d : EmpiricalSideProcedure X C m l u) (x : X) : MvPolynomial C ℝ :=
  ∑ z : Fin m → C, MvPolynomial.C (d x z : ℝ) * ∏ i, MvPolynomial.X (z i)

/-- For a [side-sample size](hyp:m), [empirical procedure](hyp:d), [label](hyp:x),
and [real coordinate table](hyp:w), [evaluating the conditional-average polynomial
gives the corresponding product-weighted finite sum](goal). -/
theorem eval_conditionalAveragePolynomial (m : ℕ)
    (d : EmpiricalSideProcedure X C m l u) (x : X) (w : C → ℝ) :
    MvPolynomial.eval w (conditionalAveragePolynomial m d x) =
      ∑ z : Fin m → C, (∏ i, w (z i)) * (d x z : ℝ) := by
  simp [conditionalAveragePolynomial, mul_comm]

/-- Given [action bounds](hyp:l,u), a [side-sample size](hyp:m), an
[empirical procedure](hyp:d), and a [label](hyp:x), the [conditional-average
procedure varies continuously with the finite side-law vector](goal). -/
theorem continuous_conditionalAverageProcedure (l u : ℝ) (m : ℕ)
    (d : EmpiricalSideProcedure X C m l u) (x : X) :
    Continuous (conditionalAverageProcedure l u m d x) := by
  unfold conditionalAverageProcedure
  apply Continuous.subtype_mk
  apply continuous_finsetSum
  intro z _
  have hc : Continuous (fun _ : FinitePmf C ↦ (d x z : ℝ)) := continuous_const
  exact (continuous_productProbability C z).mul hc

/-- Given [action bounds](hyp:l,u), a [side-sample size](hyp:m), an
[empirical procedure](hyp:d), and a [label](hyp:x), the [conditional-average
procedure is Borel measurable in the finite side-law vector](goal). -/
theorem measurable_conditionalAverageProcedure (l u : ℝ) (m : ℕ)
    (d : EmpiricalSideProcedure X C m l u) (x : X) :
    Measurable (conditionalAverageProcedure l u m d x) := by
  exact (continuous_conditionalAverageProcedure l u m d x).measurable

section Extension

variable [Nonempty C] {l u : ℝ}

/-- Given a [label alphabet](hyp:X), a [side alphabet](hyp:C), and [action
bounds](hyp:l,u), an [ambient exact-table procedure](goal) is the function assigning a
bounded action to each label and arbitrary real side-coordinate table. -/
abbrev AmbientExactSideProcedure (X C : Type*) (l u : ℝ) :=
  X → (C → ℝ) → Set.Icc l u

/-- Given an [ambient exact-table procedure](hyp:d), the [continuity property](goal)
requires every fixed-label section to vary continuously with its real coordinate table. -/
def IsContinuousAmbientExactSideProcedure
    (d : AmbientExactSideProcedure X C l u) : Prop :=
  ∀ x, Continuous (d x)

/-- Given an [ambient exact-table procedure](hyp:d), the [measurability property](goal)
requires every fixed-label section to be Borel measurable in its real coordinate table. -/
def IsMeasurableAmbientExactSideProcedure
    (d : AmbientExactSideProcedure X C l u) : Prop :=
  ∀ x, Measurable (d x)

/-- Given [ordered action bounds](hyp:hlu), an [interval-valued simplex rule](hyp:f),
and [its continuity](hyp:hf), a [continuous interval-valued ambient extension agreeing
on the simplex](goal) exists. -/
theorem exists_continuous_clippedExtension (hlu : l ≤ u)
    (f : FinitePmf C → Set.Icc l u) (hf : Continuous f) :
    ∃ g : (C → ℝ) → Set.Icc l u, Continuous g ∧ ∀ w : FinitePmf C, g w.1 = f w := by
  let fb : BoundedContinuousFunction (FinitePmf C) ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun w ↦ (f w : ℝ), hf.subtype_val⟩
  have hfb : ∀ w, fb w ∈ Set.Icc l u := by
    intro w
    exact (f w).2
  have he : Topology.IsClosedEmbedding ((↑) : FinitePmf C → C → ℝ) :=
    Topology.IsClosedEmbedding.subtypeVal (isClosed_stdSimplex ℝ C)
  rcases BoundedContinuousFunction.exists_extension_forall_mem_Icc_of_isClosedEmbedding
      fb hfb hlu he with ⟨g, hg, hgf⟩
  let g' : (C → ℝ) → Set.Icc l u := fun w ↦ ⟨g w, hg w⟩
  refine ⟨g', g.continuous.subtype_mk _, ?_⟩
  intro w
  apply Subtype.ext
  exact congrFun hgf w

/-- Given [ordered action bounds](hyp:hlu), an [exact-side procedure](hyp:d), and
[continuous label sections](hyp:hd), an [ambient procedure with continuous sections
that agrees on simplex tables](goal) exists. -/
theorem exists_continuous_ambientExactSideProcedure (hlu : l ≤ u)
    (d : ExactSideProcedure X C l u) (hd : ∀ x, Continuous (d x)) :
    ∃ g : AmbientExactSideProcedure X C l u,
      IsContinuousAmbientExactSideProcedure g ∧
        ∀ x (w : FinitePmf C), g x w.1 = d x w := by
  choose g hg_cont hg_eq using fun x ↦
    exists_continuous_clippedExtension hlu (d x) (hd x)
  exact ⟨g, hg_cont, hg_eq⟩

/-- Given [ordered action bounds](hyp:hlu), an [exact-side procedure](hyp:d), and
[continuous label sections](hyp:hd), a [Borel-measurable ambient procedure that
agrees on simplex tables](goal) exists. -/
theorem exists_measurable_clippedAmbientExactSideProcedure (hlu : l ≤ u)
    (d : ExactSideProcedure X C l u) (hd : ∀ x, Continuous (d x)) :
    ∃ g : AmbientExactSideProcedure X C l u,
      IsMeasurableAmbientExactSideProcedure g ∧
        ∀ x (w : FinitePmf C), g x w.1 = d x w := by
  rcases exists_continuous_ambientExactSideProcedure hlu d hd with ⟨g, hg, hgeq⟩
  exact ⟨g, fun x ↦ (hg x).measurable, hgeq⟩

end Extension

/-- Given a [finite probability vector](hyp:w), the [corresponding finite randomization
design](goal) is the design with exactly those atom probabilities. -/
def finitePmfDesign (w : FinitePmf C) : FiniteDesign C where
  p := w.1
  p_nonneg := w.nonneg
  p_sum := w.sum_eq_one

/-- Given a [finite probability vector](hyp:w), the [finite-PMF measure](goal) is the
atomic probability measure with those atom masses. -/
noncomputable def finitePmfMeasure [MeasurableSpace C] [MeasurableSingletonClass C]
    (w : FinitePmf C) : Measure C :=
  (finitePmfDesign w).toMeasure

/-- Given a [finite probability vector](hyp:w) and a [real-valued function](hyp:f),
[integration against its atomic measure equals the probability-weighted finite sum](goal). -/
theorem integral_finitePmfMeasure_eq_sum [MeasurableSpace C] [MeasurableSingletonClass C]
    (w : FinitePmf C) (f : C → ℝ) :
    ∫ c, f c ∂finitePmfMeasure w = ∑ c, w.1 c * f c := by
  simpa [finitePmfMeasure, FiniteDesign.E, finitePmfDesign] using
    (FiniteDesign.integral_toMeasure (finitePmfDesign w) f)

/-- Given a [finite probability vector](hyp:w) and [sample size](hyp:m), [the finite
product of its atomic measures equals the product-design measure](goal). -/
theorem pi_finitePmfMeasure_eq_productDesignMeasure [MeasurableSpace C]
    [MeasurableSingletonClass C] (w : FinitePmf C) (m : ℕ) :
    Measure.pi (fun _ : Fin m ↦ finitePmfMeasure w) =
      (prodDesign (fun _ : Fin m ↦ finitePmfDesign w)).toMeasure := by
  simpa [finitePmfMeasure] using
    (prodDesign_toMeasure_eq_pi (fun _ : Fin m ↦ finitePmfDesign w)).symm

/-- Given a [finite probability vector](hyp:w), [sample size](hyp:m), and [real-valued
sample function](hyp:f), [integration against the iid product measure equals the exact
product-probability sum](goal). -/
theorem integral_pi_finitePmfMeasure_eq_sum_productProbability [MeasurableSpace C]
    [MeasurableSingletonClass C] (w : FinitePmf C) (m : ℕ) (f : (Fin m → C) → ℝ) :
    ∫ z, f z ∂Measure.pi (fun _ : Fin m ↦ finitePmfMeasure w) =
      ∑ z : Fin m → C, productProbability C w z * f z := by
  rw [pi_finitePmfMeasure_eq_productDesignMeasure]
  rw [FiniteDesign.integral_toMeasure]
  rfl

variable {Theta : Type*}
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace C] [MeasurableSingletonClass C]

/-- Given [label probabilities](hyp:p), [side probabilities](hyp:q), [simplex validity](hyp:hp,hq),
a [target](hyp:tau), an [exact-side procedure](hyp:d), and a [parameter](hyp:theta), the
[exact-side finite-sum risk equals its finite-measure integral representation](goal). -/
theorem exactSideRisk_eq_integral (p : Theta → X → ℝ) (q : Theta → C → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C) (tau : Theta → ℝ)
    (d : ExactSideProcedure X C l u) (theta : Theta) :
    exactSideRisk p q hq tau d theta =
      ∫ x, (((d x (sidePmf q hq theta) : Set.Icc l u) : ℝ) - tau theta) ^ 2
        ∂finitePmfMeasure (sidePmf p hp theta) := by
  rw [integral_finitePmfMeasure_eq_sum]
  rfl

/-- Given [label probabilities](hyp:p), [side probabilities](hyp:q), [simplex validity](hyp:hp,hq),
a [target](hyp:tau), [sample size](hyp:m), an [empirical procedure](hyp:d), and a
[parameter](hyp:theta), the [empirical finite-sum risk equals its iterated product-measure
integral representation](goal). -/
theorem empiricalSideRisk_eq_integral (p : Theta → X → ℝ)
    (q : Theta → C → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C) (tau : Theta → ℝ) (m : ℕ)
    (d : EmpiricalSideProcedure X C m l u) (theta : Theta) :
    empiricalSideRisk p q hq tau m d theta =
      ∫ x, ∫ z,
        ((d x z : ℝ) - tau theta) ^ 2
          ∂Measure.pi (fun _ : Fin m ↦ finitePmfMeasure (sidePmf q hq theta))
        ∂finitePmfMeasure (sidePmf p hp theta) := by
  rw [integral_finitePmfMeasure_eq_sum]
  simp_rw [integral_pi_finitePmfMeasure_eq_sum_productProbability]
  rfl

variable {Theta X C : Type*} [Fintype X] [Fintype C] [Nonempty C]

/-- Given a [label alphabet](hyp:X), a [finite side alphabet](hyp:C), and [action
bounds](hyp:l,u), a [measurable ambient exact-table procedure](goal) is an ambient bounded
rule equipped with Borel measurability of every label section. -/
abbrev MeasurableAmbientExactSideProcedure (X C : Type*) [Fintype C] (l u : ℝ) :=
  {d : AmbientExactSideProcedure X C l u // IsMeasurableAmbientExactSideProcedure d}

/-- Given [label probabilities](hyp:p), [side-coordinate probabilities](hyp:q), a
[target](hyp:tau), a [measurable ambient procedure](hyp:d), and a [parameter](hyp:theta),
the [measurable exact-table risk](goal) is the label-probability-weighted squared loss after
evaluating the procedure at that parameter's raw side-coordinate table. -/
def measurableExactTableRisk (p : Theta → X → ℝ) (q : Theta → C → ℝ)
    (tau : Theta → ℝ) (d : MeasurableAmbientExactSideProcedure X C l u)
    (theta : Theta) : ℝ :=
  ∑ x, p theta x * ((d.1 x (q theta) : ℝ) - tau theta) ^ 2

/-- Given [label probabilities](hyp:p), [side-coordinate probabilities](hyp:q), a
[target](hyp:tau), and [action bounds](hyp:l,u), the [measurable exact-table minimax
value](goal) is the infimum of worst-case squared risks over globally Borel-measurable
bounded ambient procedures. -/
noncomputable def measurableExactTableMinimaxValue (p : Theta → X → ℝ)
    (q : Theta → C → ℝ) (tau : Theta → ℝ) (l u : ℝ) : ℝ :=
  minimaxValue (measurableExactTableRisk p q tau :
    MeasurableAmbientExactSideProcedure X C l u → Theta → ℝ)

/-- Given a [risk](hyp:risk), a [fixed procedure](hyp:e), a [parameter map](hyp:phi), and
[surjectivity of that map](hyp:hphi), [reindexing leaves the worst-case risk unchanged](goal). -/
theorem worstCaseRisk_comp_surjective {E A B : Type*} (risk : E → B → ℝ) (e : E)
    (phi : A → B) (hphi : Function.Surjective phi) :
    worstCaseRisk (fun e a ↦ risk e (phi a)) e = worstCaseRisk risk e := by
  rw [worstCaseRisk, iSup]
  congr 1
  ext r
  simp only [Set.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨phi a, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := hphi b
    exact ⟨a, rfl⟩

/-- Given a [risk](hyp:risk), a [parameter map](hyp:phi), and [surjectivity of that map](hyp:hphi),
[reindexing leaves the minimax value unchanged](goal). -/
theorem minimaxValue_comp_surjective {E A B : Type*} (risk : E → B → ℝ)
    (phi : A → B) (hphi : Function.Surjective phi) :
    minimaxValue (fun e a ↦ risk e (phi a)) = minimaxValue risk := by
  unfold minimaxValue
  congr 1
  funext e
  exact worstCaseRisk_comp_surjective risk e phi hphi

/-- Given a [parameter map](hyp:phi), [its continuity](hyp:hphi), a [real coordinate family](hyp:f),
and [continuity of every coordinate](hyp:hf), the [pulled-back coordinate family is continuous](goal). -/
theorem continuous_coordinateFamily_comp {A B I : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (phi : A → B) (hphi : Continuous phi) (f : B → I → ℝ)
    (hf : ∀ i, Continuous (fun b ↦ f b i)) :
    ∀ i, Continuous (fun a ↦ f (phi a) i) := by
  intro i
  exact (hf i).comp hphi

/-- Given [label probabilities](hyp:p), [side-coordinate probabilities](hyp:q), a [target](hyp:tau),
[action bounds](hyp:l,u), a [surjective parameter map](hyp:phi,hphi), [pulling all model
coordinates back leaves the measurable exact-table minimax value unchanged](goal). -/
theorem measurableExactTableMinimaxValue_comp_surjective {A B : Type*}
    (p : B → X → ℝ) (q : B → C → ℝ) (tau : B → ℝ) (l u : ℝ)
    (phi : A → B) (hphi : Function.Surjective phi) :
    measurableExactTableMinimaxValue (fun a ↦ p (phi a)) (fun a ↦ q (phi a))
        (fun a ↦ tau (phi a)) l u =
      measurableExactTableMinimaxValue p q tau l u := by
  unfold measurableExactTableMinimaxValue
  exact minimaxValue_comp_surjective (measurableExactTableRisk p q tau) phi hphi

/-- Given [label probabilities](hyp:p), [side-coordinate probabilities](hyp:q), [simplex validity](hyp:hq),
a [target](hyp:tau), [action bounds](hyp:l,u), and a [surjective parameter map](hyp:phi,hphi),
[pulling all model coordinates back leaves the exact-side minimax value unchanged](goal). -/
theorem exactSideMinimaxValue_comp_surjective {A B : Type*}
    (p : B → X → ℝ) (q : B → C → ℝ)
    (hq : ∀ b, q b ∈ stdSimplex ℝ C) (tau : B → ℝ) (l u : ℝ)
    (phi : A → B) (hphi : Function.Surjective phi) :
    exactSideMinimaxValue (fun a ↦ p (phi a)) (fun a ↦ q (phi a))
        (fun a ↦ hq (phi a)) (fun a ↦ tau (phi a)) l u =
      exactSideMinimaxValue p q hq tau l u := by
  unfold exactSideMinimaxValue
  exact minimaxValue_comp_surjective (exactSideRisk p q hq tau) phi hphi

/-- Given [label probabilities](hyp:p), [side-coordinate probabilities](hyp:q), [simplex validity](hyp:hq),
a [target](hyp:tau), [action bounds](hyp:l,u), a [sample size](hyp:m), and a [surjective
parameter map](hyp:phi,hphi), [pulling all model coordinates back leaves the empirical-side
minimax value unchanged](goal). -/
theorem empiricalSideMinimaxValue_comp_surjective {A B : Type*}
    (p : B → X → ℝ) (q : B → C → ℝ)
    (hq : ∀ b, q b ∈ stdSimplex ℝ C) (tau : B → ℝ) (l u : ℝ) (m : ℕ)
    (phi : A → B) (hphi : Function.Surjective phi) :
    empiricalSideMinimaxValue (fun a ↦ p (phi a)) (fun a ↦ q (phi a))
        (fun a ↦ hq (phi a)) (fun a ↦ tau (phi a)) l u m =
      empiricalSideMinimaxValue p q hq tau l u m := by
  unfold empiricalSideMinimaxValue
  exact minimaxValue_comp_surjective (empiricalSideRisk p q hq tau m) phi hphi

/-- Given [simplex-valid label and side probabilities](hyp:hp,hq), a [target](hyp:tau),
[ordered action bounds](hyp:hlu), and [target containment in those bounds](hyp:htau), the
[unrestricted exact-side minimax value is at most the measurable ambient exact-table value](goal). -/
theorem exactSideMinimaxValue_le_measurableExactTableMinimaxValue [Nonempty Theta]
    (p : Theta → X → ℝ) (q : Theta → C → ℝ) (tau : Theta → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (hlu : l ≤ u) (htau : ∀ theta, tau theta ∈ Set.Icc l u) :
    exactSideMinimaxValue p q hq tau l u ≤
      measurableExactTableMinimaxValue p q tau l u := by
  letI : Nonempty (MeasurableAmbientExactSideProcedure X C l u) :=
    ⟨⟨fun _ _ ↦ ⟨l, le_rfl, hlu⟩, fun _ ↦ measurable_const⟩⟩
  have hexact_nonneg (d : ExactSideProcedure X C l u) (theta : Theta) :
      0 ≤ exactSideRisk p q hq tau d theta := by
    unfold exactSideRisk
    exact Finset.sum_nonneg fun x _ ↦
      mul_nonneg ((hp theta).1 x) (sq_nonneg _)
  unfold exactSideMinimaxValue measurableExactTableMinimaxValue
  refine minimaxValue_le_minimaxValue
    (bddBelow_range_worstCaseRisk hexact_nonneg) ?_
  intro d
  refine ⟨fun x w ↦ d.1 x w.1, ?_⟩
  rfl

/-- Given [simplex-valid label and side probabilities](hyp:hp,hq), a [target](hyp:tau),
[ordered action bounds](hyp:hlu), [target containment in those bounds](hyp:htau), and a
[sample size](hyp:m), the [measurable ambient exact-table minimax value is at most the
empirical-side minimax value](goal). -/
theorem measurableExactTableMinimaxValue_le_empiricalSideMinimaxValue [Nonempty Theta]
    (p : Theta → X → ℝ) (q : Theta → C → ℝ) (tau : Theta → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (hlu : l ≤ u) (htau : ∀ theta, tau theta ∈ Set.Icc l u) (m : ℕ) :
    measurableExactTableMinimaxValue p q tau l u ≤
      empiricalSideMinimaxValue p q hq tau l u m := by
  letI : Nonempty (EmpiricalSideProcedure X C m l u) :=
    ⟨fun _ _ ↦ ⟨l, le_rfl, hlu⟩⟩
  have htable_nonneg
      (d : MeasurableAmbientExactSideProcedure X C l u) (theta : Theta) :
      0 ≤ measurableExactTableRisk p q tau d theta := by
    unfold measurableExactTableRisk
    exact Finset.sum_nonneg fun x _ ↦
      mul_nonneg ((hp theta).1 x) (sq_nonneg _)
  unfold measurableExactTableMinimaxValue empiricalSideMinimaxValue
  refine minimaxValue_le_minimaxValue
    (bddBelow_range_worstCaseRisk htable_nonneg) ?_
  intro d
  rcases exists_measurable_clippedAmbientExactSideProcedure hlu
      (conditionalAverageProcedure l u m d)
      (continuous_conditionalAverageProcedure l u m d) with ⟨g, hg, hgeq⟩
  refine ⟨⟨g, hg⟩, ?_⟩
  apply worstCaseRisk_le
  intro theta
  calc
    measurableExactTableRisk p q tau ⟨g, hg⟩ theta =
        exactSideRisk p q hq tau (conditionalAverageProcedure l u m d) theta := by
      unfold measurableExactTableRisk exactSideRisk
      congr 1
      funext x
      simpa only [sidePmf] using congrArg
        (fun a : Set.Icc l u ↦ p theta x * ((a : ℝ) - tau theta) ^ 2)
        (hgeq x (sidePmf q hq theta))
    _ ≤ empiricalSideRisk p q hq tau m d theta :=
      exactSideRisk_conditionalAverage_le p q tau hp hq hlu m d theta
    _ ≤ worstCaseRisk (empiricalSideRisk p q hq tau m) d := by
      apply le_worstCaseRisk
      refine ⟨(u - l) ^ 2, ?_⟩
      rintro _ ⟨theta', rfl⟩
      exact empiricalSideRisk_le p q hp hq tau hlu htau m d theta'

/-- Given [simplex-valid label and side probabilities](hyp:hp,hq), a [target](hyp:tau),
[ordered action bounds](hyp:hlu), and [target containment in those bounds](hyp:htau), the
[measurable exact-table minimax value lies between the exact-side value and every empirical-side
value](goal). -/
theorem measurableExactTableMinimax_squeeze [Nonempty Theta]
    (p : Theta → X → ℝ) (q : Theta → C → ℝ) (tau : Theta → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (hlu : l ≤ u) (htau : ∀ theta, tau theta ∈ Set.Icc l u) :
    exactSideMinimaxValue p q hq tau l u ≤
        measurableExactTableMinimaxValue p q tau l u ∧
      ∀ m, measurableExactTableMinimaxValue p q tau l u ≤
        empiricalSideMinimaxValue p q hq tau l u m := by
  exact ⟨exactSideMinimaxValue_le_measurableExactTableMinimaxValue
      p q tau hp hq hlu htau,
    fun m ↦ measurableExactTableMinimaxValue_le_empiricalSideMinimaxValue
      p q tau hp hq hlu htau m⟩

/-- Given a [continuous parameter map](hyp:phi,hcont), [its surjectivity](hyp:hsurj),
[model coordinates and target](hyp:p,q,tau), [simplex validity](hyp:hp,hq), [ordered action
bounds](hyp:hlu), and [target containment](hyp:htau), the [measurable exact-table value on the
source parameterization is squeezed between the target exact-side value and every target
empirical-side value](goal). -/
theorem measurableExactTableMinimax_squeeze_continuousSurjection
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [CompactSpace A] [CompactSpace B] [Nonempty A] [Nonempty B]
    (phi : A → B) (hcont : Continuous phi) (hsurj : Function.Surjective phi)
    (p : B → X → ℝ) (q : B → C → ℝ) (tau : B → ℝ)
    (hp : ∀ b, p b ∈ stdSimplex ℝ X) (hq : ∀ b, q b ∈ stdSimplex ℝ C)
    (hlu : l ≤ u) (htau : ∀ b, tau b ∈ Set.Icc l u) :
    exactSideMinimaxValue p q hq tau l u ≤
        measurableExactTableMinimaxValue (fun a ↦ p (phi a)) (fun a ↦ q (phi a))
          (fun a ↦ tau (phi a)) l u ∧
      ∀ m, measurableExactTableMinimaxValue (fun a ↦ p (phi a)) (fun a ↦ q (phi a))
          (fun a ↦ tau (phi a)) l u ≤
        empiricalSideMinimaxValue p q hq tau l u m := by
  have _hcont : Continuous phi := hcont
  rw [measurableExactTableMinimaxValue_comp_surjective p q tau l u phi hsurj]
  exact measurableExactTableMinimax_squeeze p q tau hp hq hlu htau

/-- Given [simplex-valid label and side probabilities](hyp:hp,hq), a [target](hyp:tau),
[ordered action bounds](hyp:hlu), [target containment](hyp:htau), and [convergence of the
empirical-side minimax values to the exact-side value](hyp:hconv), the [measurable exact-table
minimax value equals that common limit](goal). -/
theorem measurableExactTableMinimaxValue_eq_of_tendsto [Nonempty Theta]
    (p : Theta → X → ℝ) (q : Theta → C → ℝ) (tau : Theta → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (hlu : l ≤ u) (htau : ∀ theta, tau theta ∈ Set.Icc l u)
    (hconv : Tendsto (fun m : ℕ ↦ empiricalSideMinimaxValue p q hq tau l u m) atTop
      (nhds (exactSideMinimaxValue p q hq tau l u))) :
    measurableExactTableMinimaxValue p q tau l u =
      exactSideMinimaxValue p q hq tau l u := by
  apply le_antisymm
  · apply ge_of_tendsto hconv
    exact Filter.Eventually.of_forall fun m ↦
      measurableExactTableMinimaxValue_le_empiricalSideMinimaxValue
        p q tau hp hq hlu htau m
  · exact exactSideMinimaxValue_le_measurableExactTableMinimaxValue
      p q tau hp hq hlu htau

end Causalean.Stat.Minimax.FiniteSideInformation

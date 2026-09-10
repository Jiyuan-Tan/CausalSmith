/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Fixed-order U-statistics

This file defines fixed-order U-statistics for kernels on `m` sample points.  The
sample statistic averages the kernel over ordered injective tuples from the first
`n` observations, so for symmetric kernels it is the standard U-statistic
normalization.  It also defines the population mean, the first Hoeffding
projection, and the higher-order residual left after subtracting the mean and
all first projections.
-/

import Causalean.Stat.UStatistic.Basic
import Causalean.Tactic.IntegralLinearity
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Fixed-order U-statistics

This module defines fixed-order U-statistics over ordered injective tuples.  The
core objects are `injectiveTuples`, `injectiveTupleCount`, `uStatisticOrder`,
`uMeanOrder`, the coordinatewise first projections `uProjOrderAt` and
`uProjOrder`, and the residual kernel `uDegenOrder`.

The main structural results are the falling-factorial tuple counts
`injectiveTuples_card_eq_descFactorial` and
`injectiveTupleCount_eq_descFactorial`, the pointwise Hoeffding decomposition
`hoeffding_decomp_order`, centering and integrability lemmas for the first-order
influence function, and `uDegenOrder_integral_tail_eq_zero`, which proves
coordinatewise first-order degeneracy of the residual under the stated
finite-product/Fubini hypotheses.  The order-2 compatibility layer is supplied
by `pairKernel`, `sum_injectiveTuples_two_eq_offDiag`, and
`uStatisticOrder_two_eq_uStatistic`.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-! ## Ordered injective tuples -/

/-- For [a tuple length](hyp:m) and [a number of available sample positions](hyp:n), [the collection of ordered injective tuples](goal) consists of all ordered selections of the specified length whose entries are distinct positions among the first specified number of observations. -/
noncomputable def injectiveTuples (m n : ℕ) : Finset (Fin m → Fin n) := by
  classical
  exact Finset.univ.filter Function.Injective

/-- For [a tuple length](hyp:m) and [a number of available sample positions](hyp:n), [the ordered injective-tuple count](goal) is the real-valued number of ordered selections of that length with distinct entries among the first specified number of observations. -/
noncomputable def injectiveTupleCount (m n : ℕ) : ℝ :=
  ((injectiveTuples m n).card : ℝ)

/-- For [a domain size](hyp:m) and [a codomain size](hyp:n), [the equivalence between injective maps and embeddings](goal) identifies every injective map from an $m$-element index set to an $n$-element index set with the corresponding embedding, and conversely. -/
noncomputable def injectiveSubtypeEquivEmbedding (m n : ℕ) :
    {t : Fin m → Fin n // Function.Injective t} ≃ (Fin m ↪ Fin n) where
  toFun t := ⟨t.1, t.2⟩
  invFun f := ⟨f, f.2⟩
  left_inv t := by cases t; rfl
  right_inv f := by cases f; rfl

/-- The ordered injective tuple count is the falling factorial `n (n-1) ...`. -/
theorem injectiveTuples_card_eq_descFactorial (m n : ℕ) :
    (injectiveTuples m n).card = n.descFactorial m := by
  classical
  have hsub : Fintype.card {t : Fin m → Fin n // Function.Injective t} =
      (injectiveTuples m n).card := by
    unfold injectiveTuples
    exact Fintype.card_of_subtype _ (by intro t; simp)
  rw [← hsub]
  rw [Fintype.card_congr (injectiveSubtypeEquivEmbedding m n)]
  simp [Fintype.card_embedding_eq]

/-- The real-valued ordered injective tuple count is the falling factorial. -/
theorem injectiveTupleCount_eq_descFactorial (m n : ℕ) :
    injectiveTupleCount m n = (n.descFactorial m : ℝ) := by
  rw [injectiveTupleCount, injectiveTuples_card_eq_descFactorial]

/-! ## Basic order-`m` objects -/

/-- Given [an independent and identically distributed sample on a measurable sample space, with a specified sample-space measure and observation-space measure](hyp:Ω,X,μ,P,S), [an order-$m$ real-valued kernel](hyp:m,h), and [a sample size](hyp:n), [the fixed-order U-statistic](goal) maps each sample outcome to the average of the kernel over all ordered $m$-tuples of distinct observations among its first $n$ observations. -/
noncomputable def uStatisticOrder (S : IIDSample Ω X μ P) {m : ℕ}
    (h : (Fin m → X) → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (injectiveTupleCount m n)⁻¹ *
    ∑ t ∈ injectiveTuples m n, h (fun j => S.Z (t j : ℕ) ω)

/-- Given [a measurable observation space and an order-$m$ real-valued kernel on it](hyp:X,m,h) and [a measure on that space](hyp:P), [the population mean of the kernel](goal) is its integral under the $m$-fold product of that measure. -/
noncomputable def uMeanOrder {m : ℕ} (h : (Fin m → X) → ℝ) (P : Measure X) : ℝ :=
  ∫ z, h z ∂(Measure.pi fun _ : Fin m => P)

/-- Given [an order $m$](hyp:m), [a distinguished coordinate](hyp:j), [a value in the observation space](hyp:X,x), and [values for every remaining coordinate](hyp:tail), [the completed coordinate tuple](goal) assigns the given value to the distinguished coordinate and the supplied remaining values to all other coordinates. -/
def insertCoord {m : ℕ} (j : Fin m) (x : X) (tail : ({k : Fin m // k ≠ j}) → X) :
    Fin m → X :=
  fun k => if hkj : k = j then x else tail ⟨k, hkj⟩

/-- Given [an order-$m$ real-valued kernel](hyp:X,m,h), [a distinguished coordinate](hyp:j), and [a measure on the observation space](hyp:P), [the coordinate-specific first Hoeffding projection](goal) maps a proposed value at that coordinate to the kernel integrated over the product measure for all other coordinates, minus the kernel's population mean.

The distinguished coordinate is supplied explicitly; for symmetric kernels all choices agree. -/
noncomputable def uProjOrderAt {m : ℕ} (j : Fin m) (h : (Fin m → X) → ℝ)
    (P : Measure X) : X → ℝ :=
  fun x =>
    (∫ tail : ({k : Fin m // k ≠ j}) → X,
        h (insertCoord j x tail) ∂(Measure.pi fun _ : {k : Fin m // k ≠ j} => P))
      - uMeanOrder h P

/-- Given [a positive order $m$](hyp:m), [an order-$m$ real-valued kernel](hyp:X,h), and [a measure on the observation space](hyp:P), [the first Hoeffding projection](goal) is the coordinate-specific first projection obtained by treating the first coordinate as distinguished. -/
noncomputable def uProjOrder {m : ℕ} [NeZero m] (h : (Fin m → X) → ℝ)
    (P : Measure X) : X → ℝ :=
  uProjOrderAt (⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩ : Fin m) h P

/-- Given [a positive order $m$](hyp:m), [an order-$m$ real-valued kernel](hyp:X,h), and [a measure on the observation space](hyp:P), [the higher-order residual kernel](goal) maps each $m$-tuple to the original kernel value minus its population mean and minus the sum of all coordinate-specific first Hoeffding projections at that tuple. -/
noncomputable def uDegenOrder {m : ℕ} [NeZero m] (h : (Fin m → X) → ℝ)
    (P : Measure X) : (Fin m → X) → ℝ :=
  fun z => h z - uMeanOrder h P - ∑ j : Fin m, uProjOrderAt j h P (z j)

/-- For [an order-`m` kernel `h`](hyp:m,h), [population law `P`](hyp:P), and [an `m`-tuple of
points `z`](hyp:z), [the kernel value decomposes as the population mean plus the sum of the `m`
coordinatewise first Hoeffding projections plus the degenerate higher-order residual kernel
evaluated at `z`](goal). -/
theorem hoeffding_decomp_order {m : ℕ} [NeZero m] (h : (Fin m → X) → ℝ)
    (P : Measure X) (z : Fin m → X) :
    h z = uMeanOrder h P + (∑ j : Fin m, uProjOrderAt j h P (z j)) +
      uDegenOrder h P z := by
  simp only [uDegenOrder]
  ring

/-! ## First-projection facts -/

/-- The coordinatewise first projection is integrable whenever the corresponding
slice-averaged kernel is integrable. -/
@[fun_prop]
theorem uProjOrderAt_integrable [IsFiniteMeasure P] {m : ℕ} (j : Fin m)
    {h : (Fin m → X) → ℝ}
    (hint : Integrable
      (fun x => ∫ tail : ({k : Fin m // k ≠ j}) → X,
        h (insertCoord j x tail) ∂(Measure.pi fun _ : {k : Fin m // k ≠ j} => P)) P) :
    Integrable (uProjOrderAt j h P) P := by
  unfold uProjOrderAt
  exact hint.sub (integrable_const _)

/-- The coordinatewise first projection integrates to zero once the
slice-averaged representation of the population mean is available.  The
additional equality is the standard finite-product/Fubini identity for the
chosen coordinate. -/
theorem uProjOrderAt_integral_eq_zero [IsProbabilityMeasure P] {m : ℕ}
    (j : Fin m) {h : (Fin m → X) → ℝ}
    (hint : Integrable
      (fun x => ∫ tail : ({k : Fin m // k ≠ j}) → X,
        h (insertCoord j x tail) ∂(Measure.pi fun _ : {k : Fin m // k ≠ j} => P)) P)
    (hmean :
      ∫ x, (∫ tail : ({k : Fin m // k ≠ j}) → X,
        h (insertCoord j x tail) ∂(Measure.pi fun _ : {k : Fin m // k ≠ j} => P)) ∂P
        = uMeanOrder h P) :
    ∫ x, uProjOrderAt j h P x ∂P = 0 := by
  unfold uProjOrderAt
  integral_linearity
  rw [integral_const, probReal_univ, one_smul, hmean]
  ring

/-- The summed first-order influence function is integrable if every
coordinatewise first projection is integrable. -/
@[fun_prop]
theorem uInfluenceOrder_integrable {m : ℕ}
    {h : (Fin m → X) → ℝ}
    (hint : ∀ j : Fin m, Integrable (uProjOrderAt j h P) P) :
    Integrable (fun x => ∑ j : Fin m, uProjOrderAt j h P x) P := by
  exact integrable_finset_sum _ (fun j _ => hint j)

/-- The summed first-order influence function is centered if every
coordinatewise first projection is centered. -/
theorem uInfluenceOrder_integral_eq_zero {m : ℕ} {h : (Fin m → X) → ℝ}
    (hint : ∀ j : Fin m, Integrable (uProjOrderAt j h P) P)
    (hzero : ∀ j : Fin m, ∫ x, uProjOrderAt j h P x ∂P = 0) :
    ∫ x, (∑ j : Fin m, uProjOrderAt j h P x) ∂P = 0 := by
  integral_linearity
  simp [hzero]

/-- Integrating a function of one coordinate under a finite product law recovers
the one-dimensional integral. -/
theorem integral_pi_eval_eq [IsProbabilityMeasure P] {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ι) {f : X → E} (hf : Integrable f P) :
    ∫ z : ι → X, f (z i) ∂(Measure.pi fun _ : ι => P)
      = ∫ x, f x ∂P := by
  have hmp := measurePreserving_eval (fun _ : ι => P) i
  have hsm : AEStronglyMeasurable f
      (Measure.map (Function.eval i) (Measure.pi fun _ : ι => P)) := by
    rw [hmp.map_eq]
    exact hf.aestronglyMeasurable
  have hmap := integral_map hmp.aemeasurable hsm
  rw [hmp.map_eq] at hmap
  exact hmap.symm

/-- The first-order Hoeffding residual has zero conditional mean in each
coordinate after integrating over all other coordinates, provided the usual
finite-product/Fubini identities and slice integrability assumptions hold. -/
theorem uDegenOrder_integral_tail_eq_zero [IsProbabilityMeasure P] {m : ℕ}
    [NeZero m] {h : (Fin m → X) → ℝ}
    (hslice_int : ∀ j : Fin m, Integrable
      (fun x => ∫ tail : ({k : Fin m // k ≠ j}) → X,
        h (insertCoord j x tail) ∂(Measure.pi fun _ : {k : Fin m // k ≠ j} => P)) P)
    (hmean : ∀ j : Fin m,
      ∫ x, (∫ tail : ({k : Fin m // k ≠ j}) → X,
        h (insertCoord j x tail) ∂(Measure.pi fun _ : {k : Fin m // k ≠ j} => P)) ∂P
        = uMeanOrder h P)
    (hrow : ∀ (j : Fin m) (x : X),
      Integrable (fun tail : ({k : Fin m // k ≠ j}) → X =>
        h (insertCoord j x tail))
        (Measure.pi fun _ : {k : Fin m // k ≠ j} => P))
    (j : Fin m) (x : X) :
    ∫ tail : ({k : Fin m // k ≠ j}) → X,
        uDegenOrder h P (insertCoord j x tail)
      ∂(Measure.pi fun _ : {k : Fin m // k ≠ j} => P) = 0 := by
  classical
  let ν : Measure (({k : Fin m // k ≠ j}) → X) :=
    Measure.pi fun _ : {k : Fin m // k ≠ j} => P
  have hproj_int : ∀ l : Fin m, Integrable (uProjOrderAt l h P) P :=
    fun l => uProjOrderAt_integrable l (hslice_int l)
  have hproj_zero : ∀ l : Fin m, ∫ y, uProjOrderAt l h P y ∂P = 0 :=
    fun l => uProjOrderAt_integral_eq_zero l (hslice_int l) (hmean l)
  have hterm_int : ∀ l : Fin m, Integrable
      (fun tail : ({k : Fin m // k ≠ j}) → X =>
        uProjOrderAt l h P ((insertCoord j x tail) l)) ν := by
    intro l
    by_cases hlj : l = j
    · subst l
      simp [ν, insertCoord]
    · have hcomp : Integrable
        (fun tail : ({k : Fin m // k ≠ j}) → X =>
          uProjOrderAt l h P (tail ⟨l, hlj⟩)) ν := by
        change Integrable
          (fun tail : ({k : Fin m // k ≠ j}) → X =>
            uProjOrderAt l h P (tail ⟨l, hlj⟩))
          (Measure.pi fun _ : {k : Fin m // k ≠ j} => P)
        have := integral_pi_eval_eq (P := P) (i := (⟨l, hlj⟩ : {k : Fin m // k ≠ j}))
          (f := uProjOrderAt l h P) (hproj_int l)
        -- The integral identity above also supplies the needed map-law; use
        -- `Integrable.comp_measurePreserving` for the actual integrability.
        have hmp := measurePreserving_eval
          (fun _ : {k : Fin m // k ≠ j} => P) (⟨l, hlj⟩ : {k : Fin m // k ≠ j})
        simpa [Function.comp_def] using
          hmp.integrable_comp_of_integrable (hproj_int l)
      simpa [insertCoord, hlj, ν] using hcomp
  have hsum_int : Integrable
      (fun tail : ({k : Fin m // k ≠ j}) → X =>
        ∑ l : Fin m, uProjOrderAt l h P ((insertCoord j x tail) l)) ν :=
    integrable_finset_sum _ (fun l _ => hterm_int l)
  have hconst_int : Integrable
      (fun _ : ({k : Fin m // k ≠ j}) → X => uMeanOrder h P) ν :=
    integrable_const _
  have hleft_int : Integrable
      (fun tail : ({k : Fin m // k ≠ j}) → X =>
        h (insertCoord j x tail) - uMeanOrder h P) ν :=
    (hrow j x).sub hconst_int
  have hkey :
      ∫ tail : ({k : Fin m // k ≠ j}) → X,
          uDegenOrder h P (insertCoord j x tail) ∂ν
        =
      (∫ tail : ({k : Fin m // k ≠ j}) → X,
          h (insertCoord j x tail) ∂ν)
        - uMeanOrder h P
        - ∑ l : Fin m,
            ∫ tail : ({k : Fin m // k ≠ j}) → X,
              uProjOrderAt l h P ((insertCoord j x tail) l) ∂ν := by
    rw [show (fun tail : ({k : Fin m // k ≠ j}) → X =>
          uDegenOrder h P (insertCoord j x tail))
        =
        (fun tail => (h (insertCoord j x tail) - uMeanOrder h P)
          - ∑ l : Fin m, uProjOrderAt l h P ((insertCoord j x tail) l)) from by
          funext tail
          simp only [uDegenOrder]]
    have hrow_int := hrow j x
    integral_linearity
    simp only [integral_const, probReal_univ, one_smul]
  have hsum_eval :
      (∑ l : Fin m,
            ∫ tail : ({k : Fin m // k ≠ j}) → X,
              uProjOrderAt l h P ((insertCoord j x tail) l) ∂ν)
        = uProjOrderAt j h P x := by
    rw [Finset.sum_eq_single j]
    · simp [ν, insertCoord]
    · intro l _ hlj
      have hmp := measurePreserving_eval
        (fun _ : {k : Fin m // k ≠ j} => P) (⟨l, hlj⟩ : {k : Fin m // k ≠ j})
      have hsm : AEStronglyMeasurable (uProjOrderAt l h P)
          (Measure.map (Function.eval (⟨l, hlj⟩ : {k : Fin m // k ≠ j})) ν) := by
        change AEStronglyMeasurable (uProjOrderAt l h P)
          (Measure.map (Function.eval (⟨l, hlj⟩ : {k : Fin m // k ≠ j}))
            (Measure.pi fun _ : {k : Fin m // k ≠ j} => P))
        rw [hmp.map_eq]
        exact (hproj_int l).aestronglyMeasurable
      have hmap := integral_map hmp.aemeasurable hsm
      change (∫ (a : X), uProjOrderAt l h P a
            ∂Measure.map (Function.eval (⟨l, hlj⟩ : {k : Fin m // k ≠ j}))
              (Measure.pi fun _ : {k : Fin m // k ≠ j} => P))
          =
          ∫ (a : ({k : Fin m // k ≠ j}) → X),
            uProjOrderAt l h P
              (Function.eval (⟨l, hlj⟩ : {k : Fin m // k ≠ j}) a)
            ∂Measure.pi fun _ : {k : Fin m // k ≠ j} => P at hmap
      rw [hmp.map_eq] at hmap
      rw [show (fun tail : ({k : Fin m // k ≠ j}) → X =>
            uProjOrderAt l h P ((insertCoord j x tail) l))
          = fun tail => uProjOrderAt l h P (tail ⟨l, hlj⟩) by
            funext tail
            simp [insertCoord, hlj]]
      rw [← hmap, hproj_zero l]
    · intro hjnot
      exact False.elim (hjnot (Finset.mem_univ j))
  rw [hkey, hsum_eval]
  unfold uProjOrderAt
  ring

/-! ## Order-2 compatibility -/

/-- Given [an observation space](hyp:X) and [a real-valued binary kernel](hyp:h), [the corresponding two-coordinate kernel](goal) maps an ordered pair to the binary kernel evaluated at its first and second entries. -/
def pairKernel (h : X → X → ℝ) : (Fin 2 → X) → ℝ :=
  fun z => h (z 0) (z 1)

/-- Ordered injective `Fin 2` tuples are the same data as off-diagonal ordered
pairs. -/
theorem sum_injectiveTuples_two_eq_offDiag (S : IIDSample Ω X μ P)
    (h : X → X → ℝ) (n : ℕ) (ω : Ω) :
    ∑ t ∈ injectiveTuples 2 n, pairKernel h (fun j => S.Z (t j : ℕ) ω)
      = ∑ p ∈ (Finset.range n).offDiag, h (S.Z p.1 ω) (S.Z p.2 ω) := by
  classical
  refine Finset.sum_bij'
    (fun t _ => ((t 0 : ℕ), (t 1 : ℕ)))
    (fun p _ => Fin.cases ⟨p.1, by
        exact (Finset.mem_range.mp (Finset.mem_offDiag.mp ‹p ∈ (Finset.range n).offDiag›).1)⟩
      (fun _ : Fin 1 => ⟨p.2, by
        exact (Finset.mem_range.mp (Finset.mem_offDiag.mp ‹p ∈ (Finset.range n).offDiag›).2.1)⟩))
    ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_offDiag]
    have htinj : Function.Injective t := (Finset.mem_filter.mp ht).2
    refine ⟨Finset.mem_range.mpr (t 0).isLt, Finset.mem_range.mpr (t 1).isLt, ?_⟩
    intro h01
    have : (0 : Fin 2) = 1 := htinj (Fin.ext h01)
    norm_num at this
  · intro p hp
    rw [injectiveTuples, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact False.elim ((Finset.mem_offDiag.mp hp).2.2 (congrArg Fin.val hab))
    · exact False.elim ((Finset.mem_offDiag.mp hp).2.2 (congrArg Fin.val hab.symm))
    · rfl
  · intro t ht
    funext j
    fin_cases j <;> rfl
  · intro p hp
    exact Prod.ext rfl rfl
  · intro t ht
    rfl

/-- The order-2 fixed-order statistic agrees with the existing ordered
off-diagonal U-statistic for the corresponding pair kernel. -/
theorem uStatisticOrder_two_eq_uStatistic (S : IIDSample Ω X μ P)
    (h : X → X → ℝ) (n : ℕ) :
    uStatisticOrder S (pairKernel h) n = uStatistic S h n := by
  funext ω
  simp only [uStatisticOrder, uStatistic, injectiveTupleCount]
  rw [sum_injectiveTuples_two_eq_offDiag S h n ω]
  congr 1
  have hcard : (injectiveTuples 2 n).card = (Finset.range n).offDiag.card :=
    Finset.card_bij
    (fun t _ => ((t 0 : ℕ), (t 1 : ℕ)))
    (by
      intro t ht
      rw [Finset.mem_offDiag]
      have htinj : Function.Injective t := (Finset.mem_filter.mp ht).2
      refine ⟨Finset.mem_range.mpr (t 0).isLt, Finset.mem_range.mpr (t 1).isLt, ?_⟩
      intro h01
      have : (0 : Fin 2) = 1 := htinj (Fin.ext h01)
      norm_num at this)
    (by
      intro t₁ ht₁ t₂ ht₂ hpair
      funext j
      fin_cases j
      · exact Fin.ext (congrArg Prod.fst hpair)
      · exact Fin.ext (congrArg Prod.snd hpair))
    (by
      intro p hp
      refine ⟨Fin.cases ⟨p.1, Finset.mem_range.mp (Finset.mem_offDiag.mp hp).1⟩
          (fun _ : Fin 1 => ⟨p.2, Finset.mem_range.mp (Finset.mem_offDiag.mp hp).2.1⟩), ?_, ?_⟩
      · rw [injectiveTuples, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro a b hab
        fin_cases a <;> fin_cases b
        · rfl
        · exact False.elim ((Finset.mem_offDiag.mp hp).2.2 (congrArg Fin.val hab))
        · exact False.elim ((Finset.mem_offDiag.mp hp).2.2
            (congrArg Fin.val hab.symm))
        · rfl
      · exact Prod.ext rfl rfl)
  have hoff : ((Finset.range n).offDiag.card : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Finset.offDiag_card, Finset.card_range]
    have hle : n ≤ n * n := by
      by_cases hn0 : n = 0
      · subst n
        simp
      · exact Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hn0)
    rw [Nat.cast_sub hle, Nat.cast_mul]
    ring
  rw [show ((injectiveTuples 2 n).card : ℝ) = (n : ℝ) * ((n : ℝ) - 1) by
    rw [hcard, hoff]]

end Causalean.Stat
namespace Causalean.Stat

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-! ## Normalized finite-coordinate statistics -/

/-- For [a finite coordinate family](hyp:ι) and [a sample size](hyp:n), [the collection of injective sample assignments](goal) consists of all assignments sending distinct coordinates to distinct positions among the first $n$ observations. -/
noncomputable def finiteInjectiveTuples (ι : Type*) [Fintype ι] (n : ℕ) :
    Finset (ι → Fin n) := by
  classical
  exact Finset.univ.filter Function.Injective

/-- For [a finite coordinate family](hyp:ι) and [sample size `n`](hyp:n), [the
number of injective sample assignments is the falling factorial of `n` with
length equal to the number of coordinates](goal). -/
theorem finiteInjectiveTuples_card (ι : Type*) [Fintype ι] (n : ℕ) :
    (finiteInjectiveTuples ι n).card = n.descFactorial (Fintype.card ι) := by
  classical
  have hsub : Fintype.card {t : ι → Fin n // Function.Injective t} =
      (finiteInjectiveTuples ι n).card := by
    unfold finiteInjectiveTuples
    exact Fintype.card_of_subtype _ (by intro t; simp)
  let e : {t : ι → Fin n // Function.Injective t} ≃ (ι ↪ Fin n) :=
    { toFun := fun t => ⟨t.1, t.2⟩
      invFun := fun f => ⟨f, f.2⟩
      left_inv := fun t => by cases t; rfl
      right_inv := fun f => by cases f; rfl }
  rw [← hsub, Fintype.card_congr e]
  simp [Fintype.card_embedding_eq]

/-- Given [an independent and identically distributed sample on a measurable sample space, with a specified sample-space measure and observation-space measure](hyp:Ω,X,μ,P,S), [a finite coordinate family](hyp:ι), [a real-valued kernel indexed by that family](hyp:k), and [a sample size](hyp:n), [the normalized finite-kernel statistic](goal) maps each sample outcome to the average kernel value over every injective assignment of the coordinate family to the first $n$ sample positions. -/
noncomputable def normalizedFiniteKernelStatistic (S : Causalean.Stat.IIDSample Ω X μ P)
    {ι : Type*} [Fintype ι] (k : (ι → X) → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ((n.descFactorial (Fintype.card ι) : ℝ)⁻¹) *
    ∑ t ∈ finiteInjectiveTuples ι n, k (fun i => S.Z (t i : ℕ) ω)

/-- Given [an observation space](hyp:X), [an order](hyp:r), and [one real-valued function of an observation for each coordinate](hyp:f), [the ordered-product kernel](goal) maps an ordered $r$-tuple to the product of its coordinate-specific function values. -/
def orderedProductKernel {r : ℕ} (f : Fin r → X → ℝ) : (Fin r → X) → ℝ :=
  fun z => ∏ i, f i (z i)

/-- Given [an independent and identically distributed sample on a measurable sample space, with a specified sample-space measure and observation-space measure](hyp:Ω,X,μ,P,S), [an order](hyp:r), [one real-valued function of an observation for each coordinate](hyp:f), and [a sample size](hyp:n), [the normalized ordered-product statistic](goal) maps each sample outcome to the average, over all injective ordered $r$-tuples from its first $n$ observations, of the product of the corresponding coordinate-specific function values. -/
noncomputable def normalizedOrderedProductStatistic
    (S : Causalean.Stat.IIDSample Ω X μ P) {r : ℕ}
    (f : Fin r → X → ℝ) (n : ℕ) : Ω → ℝ :=
  normalizedFiniteKernelStatistic S (orderedProductKernel f) n

/-- For [an i.i.d. sample](hyp:S), [an order-`r` kernel](hyp:k), and [sample size
`n`](hyp:n), [the normalized finite-kernel statistic agrees with the existing
fixed-order U-statistic](goal). -/
theorem normalizedFiniteKernelStatistic_fin_eq_uStatisticOrder
    (S : Causalean.Stat.IIDSample Ω X μ P) {r : ℕ}
    (k : (Fin r → X) → ℝ) (n : ℕ) :
    normalizedFiniteKernelStatistic S k n =
      Causalean.Stat.uStatisticOrder S k n := by
  classical
  have htuples : finiteInjectiveTuples (Fin r) n =
      Causalean.Stat.injectiveTuples r n := by
    ext t
    simp [finiteInjectiveTuples, Causalean.Stat.injectiveTuples]
  unfold normalizedFiniteKernelStatistic Causalean.Stat.uStatisticOrder
  rw [Causalean.Stat.injectiveTupleCount_eq_descFactorial]
  rw [htuples]
  simp

/-- For [an i.i.d. sample](hyp:S), [a family of order-`r` coordinate functions](hyp:f),
and [sample size `n`](hyp:n), [the normalized ordered-product statistic is the
existing fixed-order U-statistic applied to their product kernel](goal). -/
theorem normalizedOrderedProductStatistic_eq_uStatisticOrder
    (S : Causalean.Stat.IIDSample Ω X μ P) {r : ℕ}
    (f : Fin r → X → ℝ) (n : ℕ) :
    normalizedOrderedProductStatistic S f n =
      Causalean.Stat.uStatisticOrder S (orderedProductKernel f) n := by
  exact normalizedFiniteKernelStatistic_fin_eq_uStatisticOrder S
    (orderedProductKernel f) n

end Causalean.Stat

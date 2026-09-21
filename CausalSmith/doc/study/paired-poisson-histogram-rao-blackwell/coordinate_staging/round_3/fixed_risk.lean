/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.PairingLaw
import Causalean.Stat.Minimax.ChiSquaredFinite
import Mathlib.Algebra.Order.Chebyshev

/-!
# Fixed-total risk contraction for two histogram fibres

This module proves the finite Jensen inequality for independent histogram
fibres and its integrated squared-risk consequence for two independent samples
whose fixed totals may differ.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

private def finiteProductWeight {m : ℕ} {Z : Type*}
    (p : Z → ℝ) (z : Fin m → Z) : ℝ :=
  ∏ i, p (z i)

private lemma finiteProductWeight_eq_histogramProduct
    {m : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (p : Z → ℝ) (z : Fin m → Z) :
    finiteProductWeight p z =
      ∏ a, p a ^ finiteSampleHistogram z a := by
  unfold finiteProductWeight finiteSampleHistogram
  rw [← Fintype.prod_fiberwise' z p]
  congr 1
  funext a
  simp

private lemma finiteProductWeight_eq_of_histogram_eq
    {m : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (p : Z → ℝ) {z z' : Fin m → Z}
    (h : finiteSampleHistogram z = finiteSampleHistogram z') :
    finiteProductWeight p z = finiteProductWeight p z' := by
  rw [finiteProductWeight_eq_histogramProduct,
    finiteProductWeight_eq_histogramProduct, h]

private lemma sum_pair_partition
    {A B C D M : Type*} [Fintype A] [Fintype B]
    [DecidableEq C] [DecidableEq D] [AddCommMonoid M]
    (g : A → C) (h : B → D) (f : A → B → M) :
    (∑ x : A, ∑ y : B, f x y) =
      ∑ c ∈ Finset.univ.image g, ∑ d ∈ Finset.univ.image h,
        ∑ x ∈ (Finset.univ : Finset A) with g x = c,
          ∑ y ∈ (Finset.univ : Finset B) with h y = d, f x y := by
  classical
  let H := (Finset.univ.image g).product (Finset.univ.image h)
  have hs := Finset.sum_fiberwise_eq_sum_filter
    (Finset.univ : Finset (A × B)) H (fun z ↦ (g z.1, h z.2))
    (fun z ↦ f z.1 z.2)
  have hs' :
      (∑ j ∈ H, ∑ i ∈ (Finset.univ : Finset (A × B)) with
        (g i.1, h i.2) = j, f i.1 i.2) = ∑ x : A, ∑ y : B, f x y := by
    simpa [H, Fintype.sum_prod_type] using hs
  rw [← hs']
  dsimp [H]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Fintype.sum_prod_type, Finset.sum_filter, Prod.mk.injEq]
  apply Fintype.sum_congr
  intro x
  by_cases hx : g x = c
  · simp [hx]
  · simp [hx]

private lemma sum_pair_subtype
    {A B M : Type*} [Fintype A] [Fintype B] [AddCommMonoid M]
    (p : A → Prop) (q : B → Prop) [DecidablePred p] [DecidablePred q]
    (f : A → B → M) :
    (∑ x ∈ (Finset.univ : Finset A) with p x,
      ∑ y ∈ (Finset.univ : Finset B) with q y, f x y) =
      ∑ x : {x // p x}, ∑ y : {y // q y}, f x.1 y.1 := by
  rw [Finset.sum_subtype (p := p)
    (Finset.univ.filter p) (by simp) (fun x ↦
      ∑ y ∈ (Finset.univ : Finset B) with q y, f x y)]
  apply Fintype.sum_congr
  intro x
  exact Finset.sum_subtype (p := q)
    (Finset.univ.filter q) (by simp) (f x.1)

/-- Given [a paired-sample estimator](hyp:est), [a real target](hyp:theta),
[two finite count histograms](hyp:cX,cY), and [certificates that both totals contain the
requested sample length](hyp:hX,hY), [the squared loss of the independent two-fibre
average is at most the uniform average squared loss over both ordering fibres](goal). -/
theorem pairedHistogramAverage_sq_sub_le
    {n : ℕ} {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (est : (Fin n → X × Y) → ℝ) (theta : ℝ)
    (cX : X → ℕ) (cY : Y → ℕ)
    (hX : n ≤ histogramTotal cX) (hY : n ≤ histogramTotal cY) :
    (pairedHistogramAverage est cX cY hX hY - theta) ^ 2 ≤
      (∑ x : HistogramFiber cX, ∑ y : HistogramFiber cY,
        (est (pairRetainedArrays (retainedHistogramPrefix hX x)
          (retainedHistogramPrefix hY y)) - theta) ^ 2) /
      (Fintype.card (HistogramFiber cX) * Fintype.card (HistogramFiber cY)) := by
  classical
  letI : Nonempty (HistogramFiber cX) := histogramFiber_nonempty cX
  letI : Nonempty (HistogramFiber cY) := histogramFiber_nonempty cY
  have hcard :
      ((Fintype.card (HistogramFiber cX) *
        Fintype.card (HistogramFiber cY) : ℕ) : ℝ) ≠ 0 := by
    positivity
  rw [pairedHistogramAverage]
  have hrewrite :
      (∑ x : HistogramFiber cX, ∑ y : HistogramFiber cY,
          est (pairRetainedArrays (retainedHistogramPrefix hX x)
            (retainedHistogramPrefix hY y))) /
            (Fintype.card (HistogramFiber cX) *
              Fintype.card (HistogramFiber cY)) - theta =
        (∑ z : HistogramFiber cX × HistogramFiber cY,
          (est (pairRetainedArrays (retainedHistogramPrefix hX z.1)
            (retainedHistogramPrefix hY z.2)) - theta)) /
            Fintype.card (HistogramFiber cX × HistogramFiber cY) := by
    rw [Fintype.sum_prod_type, Fintype.card_prod]
    simp only [Prod.fst, Prod.snd]
    simp_rw [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    simp only [Nat.cast_mul]
    field_simp [hcard]
  rw [hrewrite]
  simpa [Fintype.sum_prod_type, Fintype.card_prod] using
    (sum_div_card_sq_le_sum_sq_div_card
      (s := Finset.univ)
      (f := fun z : HistogramFiber cX × HistogramFiber cY =>
        est (pairRetainedArrays (retainedHistogramPrefix hX z.1)
          (retainedHistogramPrefix hY z.2)) - theta))

private lemma pairedHistogramFiber_weighted_average_sq_le
    {n : ℕ} {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (p : X → ℝ) (q : Y → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (est : (Fin n → X × Y) → ℝ) (theta : ℝ)
    (cX : X → ℕ) (cY : Y → ℕ)
    (hX : n ≤ histogramTotal cX) (hY : n ≤ histogramTotal cY) :
    (∑ x : HistogramFiber cX, ∑ y : HistogramFiber cY,
      finiteProductWeight p x.1 * finiteProductWeight q y.1 *
        (pairedHistogramAverage est cX cY hX hY - theta) ^ 2) ≤
      ∑ x : HistogramFiber cX, ∑ y : HistogramFiber cY,
        finiteProductWeight p x.1 * finiteProductWeight q y.1 *
          (est (pairRetainedArrays (retainedHistogramPrefix hX x)
            (retainedHistogramPrefix hY y)) - theta) ^ 2 := by
  classical
  letI : Nonempty (HistogramFiber cX) := histogramFiber_nonempty cX
  letI : Nonempty (HistogramFiber cY) := histogramFiber_nonempty cY
  let x0 : HistogramFiber cX := Classical.arbitrary _
  let y0 : HistogramFiber cY := Classical.arbitrary _
  let w := finiteProductWeight p x0.1 * finiteProductWeight q y0.1
  have hwX (x : HistogramFiber cX) : finiteProductWeight p x.1 =
      finiteProductWeight p x0.1 :=
    finiteProductWeight_eq_of_histogram_eq p (x.2.trans x0.2.symm)
  have hwY (y : HistogramFiber cY) : finiteProductWeight q y.1 =
      finiteProductWeight q y0.1 :=
    finiteProductWeight_eq_of_histogram_eq q (y.2.trans y0.2.symm)
  have hw0 : 0 ≤ w := by
    apply mul_nonneg
    · exact Finset.prod_nonneg fun i _ ↦ hp (x0.1 i)
    · exact Finset.prod_nonneg fun i _ ↦ hq (y0.1 i)
  have hc :
      (0 : ℝ) < Fintype.card (HistogramFiber cX) *
        Fintype.card (HistogramFiber cY) := by
    positivity
  have hJ := pairedHistogramAverage_sq_sub_le est theta cX cY hX hY
  have hscaled :
      (Fintype.card (HistogramFiber cX) *
          Fintype.card (HistogramFiber cY) : ℝ) *
          (pairedHistogramAverage est cX cY hX hY - theta) ^ 2 ≤
        ∑ x : HistogramFiber cX, ∑ y : HistogramFiber cY,
          (est (pairRetainedArrays (retainedHistogramPrefix hX x)
            (retainedHistogramPrefix hY y)) - theta) ^ 2 := by
    exact (by simpa [Nat.cast_mul, mul_comm] using (le_div_iff₀ hc).mp hJ)
  have hmul := mul_le_mul_of_nonneg_left hscaled hw0
  simp_rw [hwX, hwY]
  simp_rw [← Finset.mul_sum]
  simpa [x0, y0, w, Finset.sum_const, nsmul_eq_mul, Nat.cast_mul,
    mul_assoc, mul_left_comm, mul_comm] using hmul

private lemma fixedHistogramPair_weighted_average_sq_le
    {n NX NY : ℕ} {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (p : X → ℝ) (q : Y → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (est : (Fin n → X × Y) → ℝ) (theta : ℝ)
    (cX : X → ℕ) (cY : Y → ℕ)
    (htX : histogramTotal cX = NX) (htY : histogramTotal cY = NY)
    (hX : n ≤ NX) (hY : n ≤ NY) :
    (∑ x : {x : Fin NX → X // finiteSampleHistogram x = cX},
      ∑ y : {y : Fin NY → Y // finiteSampleHistogram y = cY},
        finiteProductWeight p x.1 * finiteProductWeight q y.1 *
          (pairedHistogramAverage est cX cY
            (hX.trans_eq htX.symm) (hY.trans_eq htY.symm) - theta) ^ 2) ≤
      ∑ x : {x : Fin NX → X // finiteSampleHistogram x = cX},
        ∑ y : {y : Fin NY → Y // finiteSampleHistogram y = cY},
          finiteProductWeight p x.1 * finiteProductWeight q y.1 *
            (est (pairRetainedArrays
              (fun i ↦ x.1 (Fin.castLE hX i))
              (fun i ↦ y.1 (Fin.castLE hY i))) - theta) ^ 2 := by
  subst NX
  subst NY
  have hle := pairedHistogramFiber_weighted_average_sq_le
    p q hp hq est theta cX cY hX hY
  let FX : Fintype {x : Fin (histogramTotal cX) → X //
      finiteSampleHistogram x = cX} := Subtype.fintype _
  let FY : Fintype {y : Fin (histogramTotal cY) → Y //
      finiteSampleHistogram y = cY} := Subtype.fintype _
  have huX :
      @Finset.univ _ (histogramFiberFintype cX) = @Finset.univ _ FX := by
    ext x
    exact iff_of_true
      (@Finset.mem_univ _ (histogramFiberFintype cX) x)
      (@Finset.mem_univ _ FX x)
  have huY :
      @Finset.univ _ (histogramFiberFintype cY) = @Finset.univ _ FY := by
    ext y
    exact iff_of_true
      (@Finset.mem_univ _ (histogramFiberFintype cY) y)
      (@Finset.mem_univ _ FY y)
  rw [huX, huY] at hle
  exact hle

private lemma pairedHistogramAverage_weighted_risk_le
    {n NX NY : ℕ} {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (p : X → ℝ) (q : Y → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (est : (Fin n → X × Y) → ℝ) (theta : ℝ)
    (hX : n ≤ NX) (hY : n ≤ NY) :
    (∑ zX : Fin NX → X, ∑ zY : Fin NY → Y,
      finiteProductWeight p zX * finiteProductWeight q zY *
        (pairedHistogramAverage est
          (finiteSampleHistogram zX) (finiteSampleHistogram zY)
          (by simpa only [histogramTotal_finiteSampleHistogram] using hX)
          (by simpa only [histogramTotal_finiteSampleHistogram] using hY) - theta) ^ 2) ≤
      ∑ zX : Fin NX → X, ∑ zY : Fin NY → Y,
        finiteProductWeight p zX * finiteProductWeight q zY *
          (est (pairRetainedArrays
            (fun i ↦ zX (Fin.castLE hX i))
            (fun i ↦ zY (Fin.castLE hY i))) - theta) ^ 2 := by
  classical
  conv_lhs =>
    rw [sum_pair_partition
      (g := fun zX : Fin NX → X ↦ finiteSampleHistogram zX)
      (h := fun zY : Fin NY → Y ↦ finiteSampleHistogram zY)]
  conv_rhs =>
    rw [sum_pair_partition
      (g := fun zX : Fin NX → X ↦ finiteSampleHistogram zX)
      (h := fun zY : Fin NY → Y ↦ finiteSampleHistogram zY)]
  apply Finset.sum_le_sum
  intro cX hcX
  apply Finset.sum_le_sum
  intro cY hcY
  obtain ⟨zX0, _, hzX0⟩ := Finset.mem_image.mp hcX
  obtain ⟨zY0, _, hzY0⟩ := Finset.mem_image.mp hcY
  subst cX
  subst cY
  have hle := fixedHistogramPair_weighted_average_sq_le
    p q hp hq est theta (finiteSampleHistogram zX0)
      (finiteSampleHistogram zY0)
      (histogramTotal_finiteSampleHistogram zX0)
      (histogramTotal_finiteSampleHistogram zY0) hX hY
  conv_lhs =>
    rw [sum_pair_subtype
      (p := fun zX : Fin NX → X ↦
        finiteSampleHistogram zX = finiteSampleHistogram zX0)
      (q := fun zY : Fin NY → Y ↦
        finiteSampleHistogram zY = finiteSampleHistogram zY0)]
  conv_rhs =>
    rw [sum_pair_subtype
      (p := fun zX : Fin NX → X ↦
        finiteSampleHistogram zX = finiteSampleHistogram zX0)
      (q := fun zY : Fin NY → Y ↦
        finiteSampleHistogram zY = finiteSampleHistogram zY0)]
  have hxhist (x : {zX : Fin NX → X //
      finiteSampleHistogram zX = finiteSampleHistogram zX0}) :
      finiteSampleHistogram x.1 = finiteSampleHistogram zX0 := x.2
  have hyhist (y : {zY : Fin NY → Y //
      finiteSampleHistogram zY = finiteSampleHistogram zY0}) :
      finiteSampleHistogram y.1 = finiteSampleHistogram zY0 := y.2
  simp_rw [hxhist, hyhist]
  simpa [HistogramFiber, histogramTotal_finiteSampleHistogram,
    retainedHistogramPrefix] using hle

private lemma map_retainedPrefix_pi
    {n N : ℕ} {Z : Type*} [MeasurableSpace Z]
    (R : Measure Z) [IsProbabilityMeasure R] (h : n ≤ N) :
    Measure.map (fun z : Fin N → Z ↦ fun i ↦ z (Fin.castLE h i))
      (Measure.pi (fun _ : Fin N ↦ R)) =
      Measure.pi (fun _ : Fin n ↦ R) := by
  have hN : Measurable (fun z : ℕ → Z ↦ fun i : Fin N ↦ z i) :=
    measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i : ℕ)
  have hp : Measurable (fun z : Fin N → Z ↦
      fun i : Fin n ↦ z (Fin.castLE h i)) := by
    fun_prop
  rw [← Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.iidStreamLaw_map_finPrefix
      R N, Measure.map_map hp hN]
  change Measure.map (fun z : ℕ → Z ↦ fun i : Fin n ↦ z i)
      (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.iidStreamLaw R) = _
  exact Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.iidStreamLaw_map_finPrefix R n

private lemma map_pairedRetainedPrefixes_prod_pi
    {n NX NY : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (hX : n ≤ NX) (hY : n ≤ NY) :
    Measure.map
      (fun z : (Fin NX → X) × (Fin NY → Y) ↦
        pairRetainedArrays
          (fun i ↦ z.1 (Fin.castLE hX i))
          (fun i ↦ z.2 (Fin.castLE hY i)))
      ((Measure.pi (fun _ : Fin NX ↦ P)).prod
        (Measure.pi (fun _ : Fin NY ↦ Q))) =
      Measure.pi (fun _ : Fin n ↦ P.prod Q) := by
  let prefixX : (Fin NX → X) → (Fin n → X) :=
    fun z i ↦ z (Fin.castLE hX i)
  let prefixY : (Fin NY → Y) → (Fin n → Y) :=
    fun z i ↦ z (Fin.castLE hY i)
  have hprefixX : Measurable prefixX := by fun_prop
  have hprefixY : Measurable prefixY := by fun_prop
  have hpair : Measurable (fun z : (Fin n → X) × (Fin n → Y) ↦
      pairRetainedArrays z.1 z.2) := measurable_pairRetainedArrays
  calc
    _ = Measure.map (fun z : (Fin n → X) × (Fin n → Y) ↦
          pairRetainedArrays z.1 z.2)
        (Measure.map (Prod.map prefixX prefixY)
          ((Measure.pi (fun _ : Fin NX ↦ P)).prod
            (Measure.pi (fun _ : Fin NY ↦ Q)))) := by
      rw [Measure.map_map hpair (hprefixX.prodMap hprefixY)]
      rfl
    _ = Measure.map (fun z : (Fin n → X) × (Fin n → Y) ↦
          pairRetainedArrays z.1 z.2)
        ((Measure.pi (fun _ : Fin n ↦ P)).prod
          (Measure.pi (fun _ : Fin n ↦ Q))) := by
      rw [← Measure.map_prod_map _ _ hprefixX hprefixY,
        map_retainedPrefix_pi P hX, map_retainedPrefix_pi Q hY]
    _ = _ := map_pairRetainedArrays_prod_pi P Q

/-- Given [two finite-alphabet probability laws](hyp:P,Q), [a paired-sample
estimator](hyp:est), [a real target](hyp:theta), and [certificates that both fixed totals
contain the requested sample length](hyp:hX,hY), [independent histogram averaging followed
by coordinatewise pairing has no greater squared risk than the paired iid experiment](goal). -/
theorem pairedHistogramAverage_productRisk_le
    {n NX NY : ℕ} {X Y : Type*}
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y] [DecidableEq Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (est : (Fin n → X × Y) → ℝ) (theta : ℝ)
    (hX : n ≤ NX) (hY : n ≤ NY) :
    (∫ z : (Fin NX → X) × (Fin NY → Y),
        (pairedHistogramAverage est
          (finiteSampleHistogram z.1) (finiteSampleHistogram z.2)
          (by simpa only [histogramTotal_finiteSampleHistogram] using hX)
          (by simpa only [histogramTotal_finiteSampleHistogram] using hY) - theta) ^ 2
      ∂((Measure.pi (fun _ : Fin NX => P)).prod
        (Measure.pi (fun _ : Fin NY => Q)))) ≤
      ∫ z : Fin n → X × Y, (est z - theta) ^ 2
      ∂Measure.pi (fun _ : Fin n => P.prod Q) := by
  let μ := (Measure.pi (fun _ : Fin NX ↦ P)).prod
    (Measure.pi (fun _ : Fin NY ↦ Q))
  let prefixPair :=
    fun z : (Fin NX → X) × (Fin NY → Y) ↦
      pairRetainedArrays
        (fun i ↦ z.1 (Fin.castLE hX i))
        (fun i ↦ z.2 (Fin.castLE hY i))
  have hfinite := pairedHistogramAverage_weighted_risk_le
    (p := fun a : X ↦ P.real {a}) (q := fun b : Y ↦ Q.real {b})
    (fun _ ↦ measureReal_nonneg) (fun _ ↦ measureReal_nonneg)
    est theta hX hY
  have hweighted :
      (∫ z : (Fin NX → X) × (Fin NY → Y),
        (pairedHistogramAverage est
          (finiteSampleHistogram z.1) (finiteSampleHistogram z.2)
          (by simpa only [histogramTotal_finiteSampleHistogram] using hX)
          (by simpa only [histogramTotal_finiteSampleHistogram] using hY) - theta) ^ 2
        ∂μ) ≤
      ∫ z : (Fin NX → X) × (Fin NY → Y),
        (est (prefixPair z) - theta) ^ 2 ∂μ := by
    rw [integral_fintype Integrable.of_finite,
      integral_fintype Integrable.of_finite]
    simp_rw [Fintype.sum_prod_type]
    simp_rw [show ∀ (x : Fin NX → X) (y : Fin NY → Y),
        μ.real {(x, y)} =
          (Measure.pi (fun _ : Fin NX ↦ P)).real {x} *
            (Measure.pi (fun _ : Fin NY ↦ Q)).real {y} by
      intro x y
      rw [show ({(x, y)} : Set ((Fin NX → X) × (Fin NY → Y))) =
          {x} ×ˢ {y} by ext z; simp]
      simp only [μ, measureReal_def, Measure.prod_prod]
      exact ENNReal.toReal_mul]
    simp_rw [Causalean.Stat.pi_real_singleton]
    simpa [finiteProductWeight, prefixPair, smul_eq_mul, mul_assoc] using hfinite
  change (∫ z, _ ∂μ) ≤ _
  calc
    _ ≤ ∫ z : (Fin NX → X) × (Fin NY → Y),
        (est (prefixPair z) - theta) ^ 2 ∂μ := hweighted
    _ = _ := by
      rw [← map_pairedRetainedPrefixes_prod_pi P Q hX hY]
      have hm : AEMeasurable prefixPair μ := by fun_prop
      have hf : AEStronglyMeasurable (fun z : Fin n → X × Y ↦
          (est z - theta) ^ 2) (Measure.map prefixPair μ) :=
        (measurable_of_countable _).aestronglyMeasurable
      simpa [prefixPair] using (integral_map hm hf).symm

end Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

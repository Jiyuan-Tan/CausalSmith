module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Coordinates
public import Mathlib.Data.Finset.CastCard
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Second moment of a bilinear sum on fixed iid arrays

Two independently sampled finite arrays have a bilinear square whose four
terms are indexed by the two possible equality decisions in each stream.
-/

public section

open MeasureTheory

namespace Causalean.Mathlib.Probability.Poisson.PairSecondMoment

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Given [two probability laws](hyp:P,Q), [a real kernel](hyp:K), [two fixed
array lengths](hyp:m,n), [a measurable kernel](hyp:hK), and [an integrable
kernel square](hyp:hK2), [the squared bilinear array sum is integrable](goal). -/
theorem integrable_fixedCount_pairSum_sq
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (K : X → Y → ℝ) (m n : ℕ)
    (hK : Measurable (Function.uncurry K))
    (hK2 : Integrable (fun p : X × Y => K p.1 p.2 ^ 2) (P.prod Q)) :
    Integrable
      (fun p : (Fin m → X) × (Fin n → Y) =>
        (∑ i : Fin m, ∑ j : Fin n, K (p.1 i) (p.2 j)) ^ 2)
      ((Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q)) := by
  classical
  let μ := (Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q)
  have hprod (i k : Fin m) (j l : Fin n) :=
    integrable_fixedCount_kernelProduct P Q K m n hK hK2 i k j l
  change Integrable (fun p => (∑ i, ∑ j, K (p.1 i) (p.2 j)) ^ 2) μ
  simp_rw [bilinearSum_sq_eq_coincidence]
  refine Integrable.add (Integrable.add (Integrable.add ?_ ?_) ?_) ?_
  · apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact hprod i i j j
  · apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro l _
    exact hprod i i j l
  · apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro k _
    exact hprod i k j j
  · apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro k _
    apply integrable_finsetSum
    intro l _
    exact hprod i k j l

/-- Given [two probability laws](hyp:P,Q), [a measurable real kernel](hyp:K,hK),
[an integrable kernel square](hyp:hK2), and [two fixed array lengths](hyp:m,n),
[the expected sum of squared kernel values is the length product times the
one-pair squared-kernel integral](goal). -/
theorem integral_fixedCount_sum_kernel_sq
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (K : X → Y → ℝ) (m n : ℕ)
    (hK : Measurable (Function.uncurry K))
    (hK2 : Integrable (fun p : X × Y => K p.1 p.2 ^ 2) (P.prod Q)) :
    (∫ p : (Fin m → X) × (Fin n → Y),
      (∑ i : Fin m, ∑ j : Fin n, K (p.1 i) (p.2 j) ^ 2)
      ∂((Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q))) =
      (m : ℝ) * (n : ℝ) *
        (∫ x, ∫ y, K x y ^ 2 ∂Q ∂P) := by
  classical
  let μ := (Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q)
  have hterm (i : Fin m) (j : Fin n) :
      Integrable (fun p : (Fin m → X) × (Fin n → Y) =>
        K (p.1 i) (p.2 j) ^ 2) μ := by
    simpa only [pow_two] using
      (integrable_fixedCount_kernelProduct P Q K m n hK hK2 i i j j)
  have hinner (i : Fin m) :
      Integrable (fun p : (Fin m → X) × (Fin n → Y) =>
        ∑ j : Fin n, K (p.1 i) (p.2 j) ^ 2) μ :=
    integrable_finsetSum Finset.univ (by intro j _; exact hterm i j)
  calc
    (∫ p, ∑ i : Fin m, ∑ j : Fin n, K (p.1 i) (p.2 j) ^ 2 ∂μ) =
        ∑ i : Fin m, ∫ p, ∑ j : Fin n, K (p.1 i) (p.2 j) ^ 2 ∂μ :=
      integral_finsetSum Finset.univ (by intro i _; exact hinner i)
    _ = ∑ i : Fin m, ∑ j : Fin n,
        ∫ p, K (p.1 i) (p.2 j) ^ 2 ∂μ := by
      congr 1
      ext i
      exact integral_finsetSum Finset.univ (by intro j _; exact hterm i j)
    _ = _ := by
      simp_rw [show ∀ (i : Fin m) (j : Fin n),
          (∫ p, K (p.1 i) (p.2 j) ^ 2 ∂μ) =
            (∫ x, ∫ y, K x y ^ 2 ∂Q ∂P) from by
          intro i j
          simpa only [pow_two] using
            integral_fixedCount_both_equal P Q K m n hK hK2 i j]
      simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- Given [two probability laws](hyp:P,Q), [a measurable real kernel](hyp:K,hK),
[an integrable kernel square](hyp:hK2), and [two fixed array lengths](hyp:m,n),
[the expected squared bilinear sum over two independent iid arrays is the sum of four
terms: `m·n` times the mean squared kernel; `m·n(n-1)` times the mean product of two
kernel values sharing the left point with independent right points; `m(m-1)·n` times the
mean product sharing the right point with independent left points; and `m(m-1)·n(n-1)`
times the mean product at four independent points](goal). -/
theorem integral_fixedCount_pairSum_sq
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (K : X → Y → ℝ) (m n : ℕ)
    (hK : Measurable (Function.uncurry K))
    (hK2 : Integrable (fun p : X × Y => K p.1 p.2 ^ 2) (P.prod Q)) :
    (∫ p : (Fin m → X) × (Fin n → Y),
      (∑ i : Fin m, ∑ j : Fin n, K (p.1 i) (p.2 j)) ^ 2
      ∂((Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q))) =
      (m : ℝ) * (n : ℝ) *
        (∫ x, ∫ y, K x y * K x y ∂Q ∂P) +
      (m : ℝ) * ((n : ℝ) * ((n : ℝ) - 1)) *
        (∫ x, ∫ y, ∫ y', K x y * K x y' ∂Q ∂Q ∂P) +
      ((m : ℝ) * ((m : ℝ) - 1)) * (n : ℝ) *
        (∫ x, ∫ x', ∫ y, K x y * K x' y ∂Q ∂P ∂P) +
      ((m : ℝ) * ((m : ℝ) - 1)) * ((n : ℝ) * ((n : ℝ) - 1)) *
        (∫ x, ∫ x', ∫ y, ∫ y', K x y * K x' y' ∂Q ∂Q ∂P ∂P) := by
  classical
  let μ := (Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin n => Q)
  have hprod (i k : Fin m) (j l : Fin n) :=
    integrable_fixedCount_kernelProduct P Q K m n hK hK2 i k j l
  change (∫ p, (∑ i, ∑ j, K (p.1 i) (p.2 j)) ^ 2 ∂μ) = _
  rw [integral_bilinearSum_sq_eq_coincidence μ
    (fun i j p => K (p.1 i) (p.2 j)) (fun i j k l => hprod i k j l)]
  dsimp only [μ]
  simp_rw [integral_fixedCount_both_equal P Q K m n hK hK2]
  have hB : (∑ i : Fin m, ∑ j : Fin n, ∑ l ∈ Finset.univ.erase j,
      ∫ p, K (p.1 i) (p.2 j) * K (p.1 i) (p.2 l) ∂μ) =
      ∑ i : Fin m, ∑ j : Fin n, ∑ l ∈ Finset.univ.erase j,
        ∫ x, ∫ y, ∫ y', K x y * K x y' ∂Q ∂Q ∂P := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro l hl
    exact integral_fixedCount_shared_left P Q K m n hK hK2 i j l
      ((Finset.mem_erase.mp hl).1.symm)
  have hC : (∑ i : Fin m, ∑ j : Fin n, ∑ k ∈ Finset.univ.erase i,
      ∫ p, K (p.1 i) (p.2 j) * K (p.1 k) (p.2 j) ∂μ) =
      ∑ i : Fin m, ∑ j : Fin n, ∑ k ∈ Finset.univ.erase i,
        ∫ x, ∫ x', ∫ y, K x y * K x' y ∂Q ∂P ∂P := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k hk
    exact integral_fixedCount_shared_right P Q K m n hK hK2 i k j
      ((Finset.mem_erase.mp hk).1.symm)
  have hD : (∑ i : Fin m, ∑ j : Fin n, ∑ k ∈ Finset.univ.erase i,
      ∑ l ∈ Finset.univ.erase j,
        ∫ p, K (p.1 i) (p.2 j) * K (p.1 k) (p.2 l) ∂μ) =
      ∑ i : Fin m, ∑ j : Fin n, ∑ k ∈ Finset.univ.erase i,
      ∑ l ∈ Finset.univ.erase j,
        ∫ x, ∫ x', ∫ y, ∫ y', K x y * K x' y' ∂Q ∂Q ∂P ∂P := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k hk
    apply Finset.sum_congr rfl; intro l hl
    exact integral_fixedCount_both_distinct P Q K m n hK hK2 i k j l
      ((Finset.mem_erase.mp hk).1.symm) ((Finset.mem_erase.mp hl).1.symm)
  rw [hB, hC, hD]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  simp only [Finset.cast_card_erase_of_mem (Finset.mem_univ _)]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  ring

end Causalean.Mathlib.Probability.Poisson.PairSecondMoment

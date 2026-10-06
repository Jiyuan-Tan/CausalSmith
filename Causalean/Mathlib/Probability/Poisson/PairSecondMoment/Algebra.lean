module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Coincidence expansion for bilinear finite sums

This file isolates the finite combinatorial expansion behind second moments of
bilinear statistics of two independent Poisson streams.  The four terms
correspond to coincidence in both stream indices, only the second index, only
the first index, and neither index.
-/

public section

open MeasureTheory

namespace Causalean.Mathlib.Probability.Poisson.PairSecondMoment

/-- Given [a finite real array](hyp:K), [its squared bilinear sum is the sum
of its four index-coincidence classes](goal). -/
theorem bilinearSum_sq_eq_coincidence
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (K : ι → κ → ℝ) :
    (∑ i, ∑ j, K i j) ^ 2 =
      (∑ i, ∑ j, K i j * K i j) +
      (∑ i, ∑ j, ∑ l ∈ (Finset.univ.erase j), K i j * K i l) +
      (∑ i, ∑ j, ∑ k ∈ (Finset.univ.erase i), K i j * K k j) +
      (∑ i, ∑ j, ∑ k ∈ (Finset.univ.erase i),
        ∑ l ∈ (Finset.univ.erase j), K i j * K k l) := by
  classical
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.add_sum_erase Finset.univ (fun k =>
    ∑ l, K i j * K k l) (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase Finset.univ (fun l =>
    K i j * K i l) (Finset.mem_univ j)]
  simp_rw [← Finset.add_sum_erase Finset.univ (fun l =>
    K i j * K _ l) (Finset.mem_univ j)]
  rw [Finset.sum_add_distrib]
  ring

/-- Given [a measure](hyp:μ), [a finite array of real summands](hyp:K), and
[integrable products of every two summands](hyp:hK), [the integral of its
squared bilinear sum is the four-class coincidence expansion](goal). -/
theorem integral_bilinearSum_sq_eq_coincidence
    {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (μ : Measure Ω) (K : ι → κ → Ω → ℝ)
    (hK : ∀ i j k l, Integrable (fun ω => K i j ω * K k l ω) μ) :
    ∫ ω, (∑ i, ∑ j, K i j ω) ^ 2 ∂μ =
      (∑ i, ∑ j, ∫ ω, K i j ω * K i j ω ∂μ) +
      (∑ i, ∑ j, ∑ l ∈ (Finset.univ.erase j),
        ∫ ω, K i j ω * K i l ω ∂μ) +
      (∑ i, ∑ j, ∑ k ∈ (Finset.univ.erase i),
        ∫ ω, K i j ω * K k j ω ∂μ) +
      (∑ i, ∑ j, ∑ k ∈ (Finset.univ.erase i),
        ∑ l ∈ (Finset.univ.erase j),
          ∫ ω, K i j ω * K k l ω ∂μ) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    bilinearSum_sq_eq_coincidence (fun i j => K i j ω))]
  let A := fun ω => ∑ i, ∑ j, K i j ω * K i j ω
  let B := fun ω => ∑ i, ∑ j, ∑ l ∈ (Finset.univ.erase j),
    K i j ω * K i l ω
  let C := fun ω => ∑ i, ∑ j, ∑ k ∈ (Finset.univ.erase i),
    K i j ω * K k j ω
  let D := fun ω => ∑ i, ∑ j, ∑ k ∈ (Finset.univ.erase i),
    ∑ l ∈ (Finset.univ.erase j), K i j ω * K k l ω
  have hA : Integrable A μ := by
    dsimp only [A]
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact hK i j i j
  have hB : Integrable B μ := by
    dsimp only [B]
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro l _
    exact hK i j i l
  have hC : Integrable C μ := by
    dsimp only [C]
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro k _
    exact hK i j k j
  have hD : Integrable D μ := by
    dsimp only [D]
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro k _
    apply integrable_finsetSum
    intro l _
    exact hK i j k l
  change ∫ ω, ((A ω + B ω) + C ω) + D ω ∂μ = _
  have hAB := integral_add hA hB
  have hABC := integral_add (hA.add hB) hC
  have hABCD := integral_add ((hA.add hB).add hC) hD
  have hAB' : (∫ ω, (A + B) ω ∂μ) =
      (∫ ω, A ω ∂μ) + (∫ ω, B ω ∂μ) := by
    simpa only [Pi.add_apply] using hAB
  have hABC' : (∫ ω, (A + B + C) ω ∂μ) =
      (∫ ω, (A + B) ω ∂μ) + (∫ ω, C ω ∂μ) := by
    simpa only [Pi.add_apply] using hABC
  have eA : (∫ ω, A ω ∂μ) =
      ∑ i, ∑ j, ∫ ω, K i j ω * K i j ω ∂μ := by
    dsimp only [A]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hK i j i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ => hK i j i j)]
  have eB : (∫ ω, B ω ∂μ) =
      ∑ i, ∑ j, ∑ l ∈ (Finset.univ.erase j),
        ∫ ω, K i j ω * K i l ω ∂μ := by
    dsimp only [B]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum (Finset.univ.erase j) (fun l _ => hK i j i l)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum (Finset.univ.erase j) (fun l _ => hK i j i l))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum (Finset.univ.erase j) (fun l _ => hK i j i l)]
  have eC : (∫ ω, C ω ∂μ) =
      ∑ i, ∑ j, ∑ k ∈ (Finset.univ.erase i),
        ∫ ω, K i j ω * K k j ω ∂μ := by
    dsimp only [C]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum (Finset.univ.erase i) (fun k _ => hK i j k j)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum (Finset.univ.erase i) (fun k _ => hK i j k j))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum (Finset.univ.erase i) (fun k _ => hK i j k j)]
  have eD : (∫ ω, D ω ∂μ) =
      ∑ i, ∑ j, ∑ k ∈ (Finset.univ.erase i),
        ∑ l ∈ (Finset.univ.erase j),
          ∫ ω, K i j ω * K k l ω ∂μ := by
    dsimp only [D]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum (Finset.univ.erase i) (fun k _ =>
          integrable_finsetSum (Finset.univ.erase j) (fun l _ => hK i j k l))))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum (Finset.univ.erase i) (fun k _ =>
        integrable_finsetSum (Finset.univ.erase j) (fun l _ => hK i j k l)))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum (Finset.univ.erase i) (fun k _ =>
      integrable_finsetSum (Finset.univ.erase j) (fun l _ => hK i j k l))]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_finsetSum (Finset.univ.erase j) (fun l _ => hK i j k l)]
  calc
    _ = (∫ ω, (A + B + C) ω ∂μ) + (∫ ω, D ω ∂μ) := by
      simpa only [Pi.add_apply] using hABCD
    _ = ((∫ ω, (A + B) ω ∂μ) + (∫ ω, C ω ∂μ)) +
        (∫ ω, D ω ∂μ) := by rw [hABC']
    _ = (((∫ ω, A ω ∂μ) + (∫ ω, B ω ∂μ)) +
        (∫ ω, C ω ∂μ)) + (∫ ω, D ω ∂μ) := by rw [hAB']
    _ = _ := by rw [eA, eB, eC, eD]

end Causalean.Mathlib.Probability.Poisson.PairSecondMoment

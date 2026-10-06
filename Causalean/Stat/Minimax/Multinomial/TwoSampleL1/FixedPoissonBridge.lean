module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic
public import Causalean.Stat.Minimax.Mixture
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.Definitions
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.FinitePoissonPrefix
public import Causalean.Stat.Minimax.TotalVariation

/-!
# Fixed-sample comparison with finite Poisson samples

A Poisson sample with a common count law and mean larger than the target
sample size can be truncated to a fixed prefix. The only discrepancy is the
event that the Poisson count is too small. This comparison is uniform over
finite parameter priors and keeps the ordered iid experiment intact.
-/

public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- Given [fixed sample, alphabet, and mixture sizes with a nonempty alphabet and Poisson mean](hyp:n,k,m,hk,lam), [two normalized mixture weights](hyp:w₀,w₁,hw₀,hw₁), and [two collections of multinomial vectors](hyp:R₀,R₁), [the fixed-sample predictive distance is bounded by the Poisson predictive distance plus the common short-count loss](goal). -/
theorem fixedSampleMixture_tv_le_finitePoisson
    (n k m : ℕ) (hk : 0 < k) (lam : ℝ≥0)
    (w₀ w₁ : Fin m → ℝ≥0∞)
    (hw₀ : ∑ i, w₀ i = 1) (hw₁ : ∑ i, w₁ i = 1)
    (R₀ R₁ : Fin m → ProbabilitySimplex k) :
    Causalean.Stat.tvDist
      (Causalean.Stat.mixture w₀ (fun i => simplexSampleLaw (R₀ i) n))
      (Causalean.Stat.mixture w₁ (fun i => simplexSampleLaw (R₁ i) n)) ≤
    Causalean.Stat.tvDist
      (Causalean.Stat.mixture w₀ (fun i =>
        Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
          (simplexPMF (R₀ i)).toMeasure lam))
      (Causalean.Stat.mixture w₁ (fun i =>
        Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
          (simplexPMF (R₁ i)).toMeasure lam)) +
      2 * (poissonMeasure lam (Set.Iio n)).toReal := by
  let x₀ : Fin k := ⟨0, hk⟩
  let f := finitePoissonPrefix x₀ n
  let q := poissonMeasure lam (Set.Ici n)
  let p := poissonMeasure lam (Set.Iio n)
  let δ : Measure (Fin n → Fin k) := Measure.dirac (fun _ => x₀)
  let Q (w : Fin m → ℝ≥0∞) (R : Fin m → ProbabilitySimplex k) :=
    Causalean.Stat.mixture w (fun i =>
      Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
        (simplexPMF (R i)).toMeasure lam)
  have hqp : q + p = 1 := by
    change (poissonMeasure lam) (Set.Ici n) +
      (poissonMeasure lam) (Set.Iio n) = 1
    rw [show Set.Iio n = (Set.Ici n)ᶜ by ext i; simp]
    rw [measure_add_measure_compl (by measurability), measure_univ]
  have hmap (w : Fin m → ℝ≥0∞) (hw : ∑ i, w i = 1)
      (R : Fin m → ProbabilitySimplex k) :
      Measure.map f (Q w R) =
        q • Causalean.Stat.mixture w (fun i => simplexSampleLaw (R i) n) +
          p • δ := by
    change Measure.map f (∑ i, w i •
        Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
          (simplexPMF (R i)).toMeasure lam) = _
    rw [Measure.map_finset_sum' (measurable_finitePoissonPrefix x₀ n).aemeasurable]
    simp_rw [Measure.map_smul, finitePoissonSampleLaw_map_prefix]
    simp_rw [smul_add, smul_smul]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Causalean.Stat.mixture, Finset.smul_sum]
      congr 1
      ext i
      simp [q, simplexSampleLaw, smul_smul, mul_comm]
    · rw [← Finset.sum_smul, ← Finset.sum_mul, hw, one_mul]
  have hprobP (w : Fin m → ℝ≥0∞) (hw : ∑ i, w i = 1)
      (R : Fin m → ProbabilitySimplex k) :
      IsProbabilityMeasure
        (Causalean.Stat.mixture w (fun i => simplexSampleLaw (R i) n)) :=
    Causalean.Stat.mixture_isProbabilityMeasure w hw _
  have hprobQ (w : Fin m → ℝ≥0∞) (hw : ∑ i, w i = 1)
      (R : Fin m → ProbabilitySimplex k) : IsProbabilityMeasure (Q w R) := by
    dsimp [Q]
    exact Causalean.Stat.mixture_isProbabilityMeasure w hw _
  let μ₀ := Causalean.Stat.mixture w₀ (fun i => simplexSampleLaw (R₀ i) n)
  let μ₁ := Causalean.Stat.mixture w₁ (fun i => simplexSampleLaw (R₁ i) n)
  let ρ₀ := Q w₀ R₀
  let ρ₁ := Q w₁ R₁
  letI : IsProbabilityMeasure μ₀ := hprobP w₀ hw₀ R₀
  letI : IsProbabilityMeasure μ₁ := hprobP w₁ hw₁ R₁
  letI : IsProbabilityMeasure ρ₀ := hprobQ w₀ hw₀ R₀
  letI : IsProbabilityMeasure ρ₁ := hprobQ w₁ hw₁ R₁
  letI : IsProbabilityMeasure (Measure.map f ρ₀) :=
    Measure.isProbabilityMeasure_map (measurable_finitePoissonPrefix x₀ n).aemeasurable
  letI : IsProbabilityMeasure (Measure.map f ρ₁) :=
    Measure.isProbabilityMeasure_map (measurable_finitePoissonPrefix x₀ n).aemeasurable
  have hmap₀ : Measure.map f ρ₀ = q • μ₀ + p • δ := hmap w₀ hw₀ R₀
  have hmap₁ : Measure.map f ρ₁ = q • μ₁ + p • δ := hmap w₁ hw₁ R₁
  have hqfin : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (le_of_le_of_eq (le_add_right le_rfl) hqp)
  have hpfin : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (le_of_le_of_eq (le_add_left le_rfl) hqp)
  have hqpReal : q.toReal + p.toReal = 1 := by
    rw [← ENNReal.toReal_add hqfin hpfin, hqp]
    rfl
  have hcontract : Causalean.Stat.tvDist (Measure.map f ρ₀) (Measure.map f ρ₁) ≤
      Causalean.Stat.tvDist ρ₀ ρ₁ := by
    unfold Causalean.Stat.tvDist
    apply ciSup_le
    rintro ⟨A, hA⟩
    rw [map_measureReal_apply_of_aemeasurable
        (measurable_finitePoissonPrefix x₀ n).aemeasurable hA,
      map_measureReal_apply_of_aemeasurable
        (measurable_finitePoissonPrefix x₀ n).aemeasurable hA]
    exact le_ciSup Causalean.Stat.bddAbove_tvDist_range
      ⟨f ⁻¹' A, hA.preimage (measurable_finitePoissonPrefix x₀ n)⟩
  calc
    Causalean.Stat.tvDist μ₀ μ₁ ≤
        Causalean.Stat.tvDist (Measure.map f ρ₀) (Measure.map f ρ₁) +
          2 * p.toReal := by
      unfold Causalean.Stat.tvDist
      apply ciSup_le
      rintro ⟨A, hA⟩
      have hmass₀ : (Measure.map f ρ₀).real A =
          q.toReal * μ₀.real A + p.toReal * δ.real A := by
        rw [hmap₀, measureReal_add_apply
          (by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_ne_top hqfin (measure_ne_top μ₀ A))
          (by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_ne_top hpfin (measure_ne_top δ A))]
        simp
      have hmass₁ : (Measure.map f ρ₁).real A =
          q.toReal * μ₁.real A + p.toReal * δ.real A := by
        rw [hmap₁, measureReal_add_apply
          (by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_ne_top hqfin (measure_ne_top μ₁ A))
          (by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_ne_top hpfin (measure_ne_top δ A))]
        simp
      have hgap : |μ₀.real A - μ₁.real A| ≤ 1 :=
        Causalean.Stat.abs_measureReal_sub_le_one A
      have hqnonneg : 0 ≤ q.toReal := ENNReal.toReal_nonneg
      have hpnonneg : 0 ≤ p.toReal := ENNReal.toReal_nonneg
      have habs : |(Measure.map f ρ₀).real A - (Measure.map f ρ₁).real A| =
          q.toReal * |μ₀.real A - μ₁.real A| := by
        rw [hmass₀, hmass₁]
        have heq : q.toReal * μ₀.real A + p.toReal * δ.real A -
            (q.toReal * μ₁.real A + p.toReal * δ.real A) =
            q.toReal * (μ₀.real A - μ₁.real A) := by ring
        rw [heq, abs_mul, abs_of_nonneg hqnonneg]
      have htv : q.toReal * |μ₀.real A - μ₁.real A| ≤
          ⨆ A : {A : Set (Fin n → Fin k) // MeasurableSet A},
            |(Measure.map f ρ₀).real A.1 - (Measure.map f ρ₁).real A.1| := by
        rw [← habs]
        exact le_ciSup Causalean.Stat.bddAbove_tvDist_range ⟨A, hA⟩
      have hpbound := mul_le_mul_of_nonneg_left hgap hpnonneg
      nlinarith
    _ ≤ Causalean.Stat.tvDist ρ₀ ρ₁ + 2 * p.toReal := by gcongr

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1

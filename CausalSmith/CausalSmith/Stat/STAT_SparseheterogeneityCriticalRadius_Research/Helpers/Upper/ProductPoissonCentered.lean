module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.HeavyMissingMoment

/-! Exact centered second moment of the total count under a product-Poisson law. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Causalean.Mathlib.Probability.Poisson
open Causalean.Mathlib.Probability.Poisson.PairSecondMoment

/-- The centered second moment of two independent Poisson counts equals the
sum of their rates. -/
lemma productPoisson_total_center_sq_integral (a b : ℝ≥0) :
    (∫ N0 : ℕ, ∫ N1 : ℕ,
        (((N0 + N1 : ℕ) : ℝ) - ((a : ℝ) + (b : ℝ))) ^ 2
        ∂poissonMeasure b ∂poissonMeasure a) =
      (a : ℝ) + (b : ℝ) := by
  have hinner (N0 : ℕ) :
      (∫ N1 : ℕ,
          (((N0 + N1 : ℕ) : ℝ) - ((a : ℝ) + (b : ℝ))) ^ 2
          ∂poissonMeasure b) =
        (b : ℝ) + ((N0 : ℝ) - (a : ℝ)) ^ 2 := by
    let μ : Measure ℕ := poissonMeasure b
    let c : ℝ := (N0 : ℝ) - (a : ℝ) - (b : ℝ)
    let f0 : ℕ → ℝ := fun N1 => (N1 : ℝ) ^ 2
    let f1 : ℕ → ℝ := fun N1 => 2 * c * (N1 : ℝ)
    let f2 : ℕ → ℝ := fun _ => c ^ 2
    have hcount : Integrable (fun N1 : ℕ => (N1 : ℝ)) μ :=
      (poisson_natCast_memLp_two b).integrable (by norm_num)
    have hsq : Integrable f0 μ := by
      simpa only [f0] using integrable_poisson_count_sq b
    have hlin : Integrable f1 μ := by
      dsimp only [f1]
      exact hcount.const_mul _
    have hconst : Integrable f2 μ := by
      exact integrable_const _
    have hfun :
        (fun N1 : ℕ =>
          (((N0 + N1 : ℕ) : ℝ) - ((a : ℝ) + (b : ℝ))) ^ 2) =
          fun N1 => (f0 N1 + f1 N1) + f2 N1 := by
      funext N1
      simp only [f0, f1, f2, c, Nat.cast_add]
      ring
    have hsum :
        (∫ N1, (f0 N1 + f1 N1) + f2 N1 ∂μ) =
          ((∫ N1, f0 N1 ∂μ) + ∫ N1, f1 N1 ∂μ) +
            ∫ N1, f2 N1 ∂μ := by
      calc
        _ = (∫ N1, f0 N1 + f1 N1 ∂μ) + ∫ N1, f2 N1 ∂μ :=
          integral_add (hsq.add hlin) hconst
        _ = _ := by rw [integral_add hsq hlin]
    have hv0 : (∫ N1, f0 N1 ∂μ) = (b : ℝ) ^ 2 + (b : ℝ) := by
      simpa only [f0, μ] using poisson_count_second_moment b
    have hv1 : (∫ N1, f1 N1 ∂μ) = 2 * c * (b : ℝ) := by
      rw [show (∫ N1, f1 N1 ∂μ) =
          2 * c * ∫ N1 : ℕ, (N1 : ℝ) ∂μ by
        simp [f1, integral_const_mul]]
      rw [show (∫ N1 : ℕ, (N1 : ℝ) ∂μ) = (b : ℝ) by
        simpa only [μ] using poisson_count_first_moment b]
    have hv2 : (∫ N1, f2 N1 ∂μ) = c ^ 2 := by
      simp [f2, μ]
    rw [hfun, hsum, hv0, hv1, hv2]
    dsimp only [c]
    ring
  simp_rw [hinner]
  let μ : Measure ℕ := poissonMeasure a
  let f0 : ℕ → ℝ := fun _ => (b : ℝ)
  let f1 : ℕ → ℝ := fun N0 => (N0 : ℝ) ^ 2
  let f2 : ℕ → ℝ := fun N0 =>
    (-2 * (a : ℝ)) * (N0 : ℝ) + (a : ℝ) ^ 2
  have hcount : Integrable (fun N0 : ℕ => (N0 : ℝ)) μ :=
    (poisson_natCast_memLp_two a).integrable (by norm_num)
  have hi0 : Integrable f0 μ := integrable_const _
  have hi1 : Integrable f1 μ := by
    simpa only [f1] using integrable_poisson_count_sq a
  have hi2 : Integrable f2 μ := by
    dsimp only [f2]
    exact (hcount.const_mul _).add (integrable_const _)
  have hfun :
      (fun N0 : ℕ => (b : ℝ) + ((N0 : ℝ) - (a : ℝ)) ^ 2) =
        fun N0 => (f0 N0 + f1 N0) + f2 N0 := by
    funext N0
    simp only [f0, f1, f2]
    ring
  have hsum :
      (∫ N0 : ℕ, (f0 N0 + f1 N0) + f2 N0 ∂μ) =
        ((∫ N0, f0 N0 ∂μ) + ∫ N0, f1 N0 ∂μ) +
          ∫ N0, f2 N0 ∂μ := by
    calc
      _ = (∫ N0, f0 N0 + f1 N0 ∂μ) + ∫ N0, f2 N0 ∂μ :=
        integral_add (hi0.add hi1) hi2
      _ = _ := by rw [integral_add hi0 hi1]
  have hv0 : (∫ N0, f0 N0 ∂μ) = (b : ℝ) := by simp [f0, μ]
  have hv1 : (∫ N0, f1 N0 ∂μ) = (a : ℝ) ^ 2 + (a : ℝ) := by
    simpa only [f1, μ] using poisson_count_second_moment a
  have hv2 : (∫ N0, f2 N0 ∂μ) =
      (-2 * (a : ℝ)) * (a : ℝ) + (a : ℝ) ^ 2 := by
    rw [show (∫ N0, f2 N0 ∂μ) =
        (-2 * (a : ℝ)) * ∫ N0 : ℕ, (N0 : ℝ) ∂μ +
          (a : ℝ) ^ 2 by
      dsimp only [f2]
      rw [integral_add (hcount.const_mul _) (integrable_const _),
        integral_const_mul]
      simp [μ]]
    rw [show (∫ N0 : ℕ, (N0 : ℝ) ∂μ) = (a : ℝ) by
      simpa only [μ] using poisson_count_first_moment a]
  rw [hfun, hsum, hv0, hv1, hv2]
  ring

lemma productPoisson_total_center_sq_integrable_inner (a b : ℝ≥0) (N0 : ℕ) :
    Integrable (fun N1 : ℕ =>
      (((N0 + N1 : ℕ) : ℝ) - ((a : ℝ) + (b : ℝ))) ^ 2)
      (poissonMeasure b) := by
  rw [show (fun N1 : ℕ =>
      (((N0 + N1 : ℕ) : ℝ) - ((a : ℝ) + (b : ℝ))) ^ 2) =
      fun (N1 : ℕ) => (N1 : ℝ) ^ 2 +
        (2 * ((N0 : ℝ) - (a : ℝ) - (b : ℝ))) * (N1 : ℝ) +
        ((N0 : ℝ) - (a : ℝ) - (b : ℝ)) ^ 2 by
    funext N1
    norm_num only [Nat.cast_add]
    ring]
  exact ((integrable_poisson_count_sq b).add
    ((poisson_natCast_memLp_two b).integrable (by norm_num) |>.const_mul _)).add
    (integrable_const _)

lemma productPoisson_total_center_sq_integrable_outer (a b : ℝ≥0) :
    Integrable (fun N0 : ℕ => ∫ N1 : ℕ,
      (((N0 + N1 : ℕ) : ℝ) - ((a : ℝ) + (b : ℝ))) ^ 2
      ∂poissonMeasure b) (poissonMeasure a) := by
  let g : ℕ → ℝ := fun N0 =>
    2 * ((b : ℝ) ^ 2 + b) +
      2 * ((N0 : ℝ) - (a : ℝ) - (b : ℝ)) ^ 2
  have hcenter : Integrable
      (fun N0 : ℕ => ((N0 : ℝ) - (a : ℝ) - (b : ℝ)) ^ 2)
      (poissonMeasure a) := by
    rw [show (fun N0 : ℕ => ((N0 : ℝ) - (a : ℝ) - (b : ℝ)) ^ 2) =
        fun (N0 : ℕ) => (N0 : ℝ) ^ 2 +
          (-2 * ((a : ℝ) + (b : ℝ))) * (N0 : ℝ) +
          ((a : ℝ) + (b : ℝ)) ^ 2 by funext N0; ring]
    exact ((integrable_poisson_count_sq a).add
      ((poisson_natCast_memLp_two a).integrable (by norm_num) |>.const_mul _)).add
      (integrable_const _)
  have hg : Integrable g (poissonMeasure a) :=
    (integrable_const _).add (hcenter.const_mul 2)
  apply hg.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards with N0
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
  calc
    _ ≤ ∫ N1 : ℕ,
        (2 * (N1 : ℝ) ^ 2 +
          2 * ((N0 : ℝ) - (a : ℝ) - (b : ℝ)) ^ 2)
        ∂poissonMeasure b := by
      apply integral_mono (productPoisson_total_center_sq_integrable_inner a b N0)
        ((integrable_poisson_count_sq b).const_mul 2 |>.add (integrable_const _))
      intro N1
      change ((((N0 + N1 : ℕ) : ℝ) - ((a : ℝ) + (b : ℝ))) ^ 2) ≤
        2 * (N1 : ℝ) ^ 2 +
          2 * ((N0 : ℝ) - (a : ℝ) - (b : ℝ)) ^ 2
      norm_num only [Nat.cast_add]
      nlinarith [sq_nonneg ((N1 : ℝ) -
        ((N0 : ℝ) - (a : ℝ) - (b : ℝ)))]
    _ = g N0 := by
      dsimp only [g]
      rw [integral_add ((integrable_poisson_count_sq b).const_mul 2)
        (integrable_const _), integral_const_mul, poisson_count_second_moment]
      simp

/-- The guarded centered total count is controlled by Poisson fluctuation and
the exact missing-arm square. -/
lemma guardedTotalCount_center_sq_integral_le (a b : ℝ≥0) :
    (∫ N0 : ℕ, ∫ N1 : ℕ,
      (guardedTotalCount N0 N1 - ((a : ℝ) + (b : ℝ))) ^ 2
      ∂poissonMeasure b ∂poissonMeasure a) ≤
      2 * ((a : ℝ) + (b : ℝ)) +
        2 * (Real.exp (-(a : ℝ)) * ((b : ℝ) ^ 2 + b) +
          Real.exp (-(b : ℝ)) * ((a : ℝ) ^ 2 + a)) := by
  let s : ℝ := (a : ℝ) + (b : ℝ)
  have hinner (N0 : ℕ) :
      (∫ N1 : ℕ, (guardedTotalCount N0 N1 - s) ^ 2 ∂poissonMeasure b) ≤
        ∫ N1 : ℕ,
          2 * (((N0 + N1 : ℕ) : ℝ) - s) ^ 2 +
            2 * missingCountSquareEnvelope N0 N1 ∂poissonMeasure b := by
    apply integral_mono (guardedTotalCount_center_sq_integrable_inner b N0 s)
      ((productPoisson_total_center_sq_integrable_inner a b N0).const_mul 2 |>.add
        ((missingCountSquareEnvelope_integrable_inner b N0).const_mul 2))
    exact fun N1 => guardedTotalCount_center_sq_le N0 N1 s
  have hrhs : Integrable (fun N0 : ℕ =>
      ∫ N1 : ℕ,
        2 * (((N0 + N1 : ℕ) : ℝ) - s) ^ 2 +
          2 * missingCountSquareEnvelope N0 N1 ∂poissonMeasure b)
      (poissonMeasure a) := by
    dsimp only [s]
    simp_rw [integral_add
      ((productPoisson_total_center_sq_integrable_inner a b _).const_mul 2)
      ((missingCountSquareEnvelope_integrable_inner b _).const_mul 2),
      integral_const_mul]
    exact (productPoisson_total_center_sq_integrable_outer a b).const_mul 2 |>.add
      ((missingCountSquareEnvelope_integrable_outer a b).const_mul 2)
  calc
    _ ≤ ∫ N0 : ℕ, ∫ N1 : ℕ,
        2 * (((N0 + N1 : ℕ) : ℝ) - s) ^ 2 +
          2 * missingCountSquareEnvelope N0 N1
        ∂poissonMeasure b ∂poissonMeasure a := by
      apply integral_mono
        (guardedTotalCount_center_sq_integrable_outer a b s) hrhs hinner
    _ = 2 * (∫ N0 : ℕ, ∫ N1 : ℕ,
          (((N0 + N1 : ℕ) : ℝ) - s) ^ 2
          ∂poissonMeasure b ∂poissonMeasure a) +
        2 * (∫ N0 : ℕ, ∫ N1 : ℕ,
          missingCountSquareEnvelope N0 N1
          ∂poissonMeasure b ∂poissonMeasure a) := by
      dsimp only [s]
      simp_rw [integral_add
        ((productPoisson_total_center_sq_integrable_inner a b _).const_mul 2)
        ((missingCountSquareEnvelope_integrable_inner b _).const_mul 2),
        integral_const_mul]
      rw [integral_add
        ((productPoisson_total_center_sq_integrable_outer a b).const_mul 2)
        ((missingCountSquareEnvelope_integrable_outer a b).const_mul 2),
        integral_const_mul, integral_const_mul]
    _ = _ := by
      dsimp only [s]
      rw [productPoisson_total_center_sq_integral,
        missingCountSquareEnvelope_integral]

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

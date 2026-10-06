module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.Moments
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Product
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.ScalarPoissonLikelihood
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Data.Nat.Choose.Multinomial

/-! Likelihood Gram identities for the four-count marked-Poisson experiment. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Nat

/-- Four-variable multinomial mass identity underlying the reciprocal
factorial count in (67). -/
lemma finFour_sum_multinomial (r : ℕ) :
    (∑ alpha ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) r,
      Nat.multinomial Finset.univ alpha) = 4 ^ r := by
  have h := Finset.sum_pow_eq_sum_piAntidiag
    (R := ℕ) (Finset.univ : Finset (Fin 4)) (fun _ => 1) r
  simpa using h.symm

/-- The reciprocal-factorial mass of four-part multi-indices of total degree
`r` is `4^r / r!`.  This is the combinatorial identity in equation (67). -/
lemma finFour_sum_reciprocal_factorial (r : ℕ) :
    (∑ alpha ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) r,
      (1 : ℝ) / ∏ s, ((alpha s).factorial : ℝ)) =
      (4 : ℝ) ^ r / r.factorial := by
  have hpoint (alpha : Fin 4 → ℕ)
      (halpha : alpha ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) r) :
      (1 : ℝ) / ∏ s, ((alpha s).factorial : ℝ) =
        (Nat.multinomial Finset.univ alpha : ℝ) / r.factorial := by
    have hsum : ∑ s, alpha s = r := by
      exact (Finset.mem_piAntidiag.mp halpha).1
    have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin 4)) alpha
    have hspecR :
        (∏ s, ((alpha s).factorial : ℝ)) *
            (Nat.multinomial Finset.univ alpha : ℝ) = (r.factorial : ℝ) := by
      exact_mod_cast hspec.trans (congrArg Nat.factorial hsum)
    have hprod : (∏ s, ((alpha s).factorial : ℝ)) ≠ 0 := by positivity
    have hfact : (r.factorial : ℝ) ≠ 0 := by positivity
    apply (div_eq_div_iff hprod hfact).2
    simpa [mul_comm] using hspecR.symm
  rw [Finset.sum_congr rfl hpoint]
  rw [← Finset.sum_div]
  norm_cast
  rw [finFour_sum_multinomial]

/-- The elementary polynomial-to-exponential comparison used to dominate the
quadratic factor in the Taylor tail. -/
lemma nat_sq_le_four_pow (r : ℕ) : r ^ 2 ≤ 4 ^ r := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      cases r with
      | zero => norm_num
      | succ r =>
          calc
            (r + 2) ^ 2 ≤ (2 * (r + 1)) ^ 2 :=
              Nat.pow_le_pow_left (by omega) 2
            _ = 4 * (r + 1) ^ 2 := by ring
            _ ≤ 4 * 4 ^ (r + 1) := Nat.mul_le_mul_left 4 ih
            _ = 4 ^ (r + 2) := by rw [pow_succ]; ring

/-- Under the explicit small-intensity calibration `Lambda ≤ 2⁻¹²`, each
quadratically weighted factorial-tail term is bounded by a geometric term
with ratio `2⁻⁸`. -/
lemma quadratic_factorial_term_le_geometric (Lambda : ℝ) (r : ℕ)
    (hLambda : 0 ≤ Lambda) (hsmall : Lambda ≤ (1 : ℝ) / 4096) :
    (r : ℝ) ^ 2 * (4 * Lambda) ^ r / r.factorial ≤
      ((1 : ℝ) / 256) ^ r := by
  have hfac : (1 : ℝ) ≤ r.factorial := by
    norm_cast
    exact Nat.factorial_pos r
  have hsquare : (r : ℝ) ^ 2 ≤ (4 : ℝ) ^ r := by
    exact_mod_cast nat_sq_le_four_pow r
  calc
    (r : ℝ) ^ 2 * (4 * Lambda) ^ r / r.factorial ≤
        (r : ℝ) ^ 2 * (4 * Lambda) ^ r :=
      div_le_self (mul_nonneg (sq_nonneg _) (pow_nonneg (by positivity) _)) hfac
    _ ≤ (4 : ℝ) ^ r * (4 * Lambda) ^ r := by
      gcongr
    _ = (16 * Lambda) ^ r := by rw [← mul_pow]; congr 1 <;> ring
    _ ≤ ((1 : ℝ) / 256) ^ r := by
      apply pow_le_pow_left₀ (by positivity)
      linarith

/-- Ratio-calibrated version of the factorial-term bound.  It uses the
Stirling lower bound and applies when `Lambda / r ≤ 2⁻¹² / 3`, which is the
condition available after starting the roadmap tail beyond degree `3J`. -/
lemma quadratic_factorial_term_le_geometric_of_ratio (Lambda : ℝ) (r : ℕ)
    (hr : 1 ≤ r) (hLambda : 0 ≤ Lambda)
    (hsmall : Lambda ≤ (r : ℝ) / 12288) :
    (r : ℝ) ^ 2 * (4 * Lambda) ^ r / r.factorial ≤
      ((1 : ℝ) / 256) ^ r := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hsqrt : (1 : ℝ) ≤ √(2 * Real.pi * r) := by
    rw [Real.one_le_sqrt]
    calc
      (1 : ℝ) ≤ 2 * 3 * 1 := by norm_num
      _ ≤ 2 * Real.pi * r := by
        gcongr
        · exact Real.pi_gt_three.le
        exact_mod_cast hr
  have hstirling : ((r : ℝ) / Real.exp 1) ^ r ≤ (r.factorial : ℝ) := by
    calc
      ((r : ℝ) / Real.exp 1) ^ r ≤
          √(2 * Real.pi * r) * ((r : ℝ) / Real.exp 1) ^ r := by
        exact le_mul_of_one_le_left (pow_nonneg (by positivity) _) hsqrt
      _ ≤ (r.factorial : ℝ) := Stirling.le_factorial_stirling r
  have hpow : (4 * Lambda) ^ r / (r.factorial : ℝ) ≤
      (3 * (4 * Lambda) / r) ^ r := by
    calc
      (4 * Lambda) ^ r / (r.factorial : ℝ) ≤
          (4 * Lambda) ^ r / (((r : ℝ) / Real.exp 1) ^ r) :=
        div_le_div_of_nonneg_left (pow_nonneg (by positivity) _)
          (pow_pos (by positivity) _) hstirling
      _ = (Real.exp 1 * (4 * Lambda) / r) ^ r := by
        rw [← div_pow]
        congr 1
        field_simp [ne_of_gt hrpos]
      _ ≤ (3 * (4 * Lambda) / r) ^ r := by
        apply pow_le_pow_left₀ (by positivity)
        apply div_le_div_of_nonneg_right _ hrpos.le
        exact mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (by positivity)
  have hratio : 3 * (4 * Lambda) / (r : ℝ) ≤ (1 : ℝ) / 1024 := by
    apply (div_le_iff₀ hrpos).2
    nlinarith
  calc
    (r : ℝ) ^ 2 * (4 * Lambda) ^ r / r.factorial =
        (r : ℝ) ^ 2 * ((4 * Lambda) ^ r / r.factorial) := by ring
    _ ≤ (r : ℝ) ^ 2 * (3 * (4 * Lambda) / r) ^ r := by
      gcongr
    _ ≤ (4 : ℝ) ^ r * ((1 : ℝ) / 1024) ^ r := by
      exact mul_le_mul (by exact_mod_cast nat_sq_le_four_pow r)
        (pow_le_pow_left₀ (by positivity) hratio r) (pow_nonneg (by positivity) _)
        (by positivity)
    _ = ((1 : ℝ) / 256) ^ r := by rw [← mul_pow]; congr 1 <;> norm_num

/-- Exact sum of the geometric majorant after discarding degrees through
`J`. -/
lemma tsum_geometric_256_shift (J : ℕ) :
    (∑' k : ℕ, ((1 : ℝ) / 256) ^ (J + 1 + k)) =
      ((1 : ℝ) / 256) ^ (J + 1) * (256 / 255 : ℝ) := by
  have hfun : (fun k : ℕ => ((1 : ℝ) / 256) ^ (J + 1 + k)) =
      fun k => ((1 : ℝ) / 256) ^ (J + 1) * ((1 : ℝ) / 256) ^ k := by
    funext k
    rw [show J + 1 + k = (J + 1) + k by omega, pow_add]
  rw [hfun]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (by norm_num)]
  norm_num

/-- The shifted quadratic factorial tail is geometrically small.  The left
side enumerates precisely the degrees `r > J`; the right side is already on
the `2⁻⁸J` scale used by the converse calibration. -/
lemma quadratic_factorial_tail_le (Lambda : ℝ) (J : ℕ)
    (hLambda : 0 ≤ Lambda) (hsmall : Lambda ≤ (1 : ℝ) / 4096) :
    (∑' k : ℕ,
      ((J + 1 + k : ℕ) : ℝ) ^ 2 * (4 * Lambda) ^ (J + 1 + k) /
        (J + 1 + k).factorial) ≤
      2 * ((1 : ℝ) / 256) ^ (J + 1) := by
  let f : ℕ → ℝ := fun k =>
    ((J + 1 + k : ℕ) : ℝ) ^ 2 * (4 * Lambda) ^ (J + 1 + k) /
      (J + 1 + k).factorial
  let g : ℕ → ℝ := fun k => ((1 : ℝ) / 256) ^ (J + 1 + k)
  have hf_nonneg : ∀ k, 0 ≤ f k := by
    intro k
    exact div_nonneg
      (mul_nonneg (sq_nonneg _) (pow_nonneg (by positivity) _)) (by positivity)
  have hfg : ∀ k, f k ≤ g k := by
    intro k
    exact quadratic_factorial_term_le_geometric Lambda (J + 1 + k)
      hLambda hsmall
  have hg : Summable g := by
    change Summable (fun k : ℕ => ((1 : ℝ) / 256) ^ (J + 1 + k))
    simpa only [show ∀ k : ℕ, J + 1 + k = (J + 1) + k by omega, pow_add] using
      (summable_geometric_of_lt_one (r := (1 : ℝ) / 256)
        (by positivity) (by norm_num)).mul_left (((1 : ℝ) / 256) ^ (J + 1))
  have hf : Summable f := Summable.of_nonneg_of_le hf_nonneg hfg hg
  change (∑' k, f k) ≤ _
  calc
    (∑' k, f k) ≤ ∑' k, g k := hf.tsum_le_tsum hfg hg
    _ = ((1 : ℝ) / 256) ^ (J + 1) * (256 / 255 : ℝ) :=
      tsum_geometric_256_shift J
    _ ≤ 2 * ((1 : ℝ) / 256) ^ (J + 1) := by
      rw [mul_comm 2]
      exact mul_le_mul_of_nonneg_left (by norm_num) (pow_nonneg (by positivity) _)

/-- A simpler consequence of `quadratic_factorial_tail_le`, exposing exactly
the `2⁻⁸J` decay factor. -/
lemma quadratic_factorial_tail_le_pow (Lambda : ℝ) (J : ℕ)
    (hLambda : 0 ≤ Lambda) (hsmall : Lambda ≤ (1 : ℝ) / 4096) :
    (∑' k : ℕ,
      ((J + 1 + k : ℕ) : ℝ) ^ 2 * (4 * Lambda) ^ (J + 1 + k) /
        (J + 1 + k).factorial) ≤
      ((1 : ℝ) / 256) ^ J := by
  calc
    _ ≤ 2 * ((1 : ℝ) / 256) ^ (J + 1) :=
      quadratic_factorial_tail_le Lambda J hLambda hsmall
    _ ≤ ((1 : ℝ) / 256) ^ J := by
      rw [pow_succ]
      calc
        2 * (((1 : ℝ) / 256) ^ J * (1 / 256)) =
            (1 / 128 : ℝ) * ((1 / 256 : ℝ) ^ J) := by ring
        _ ≤ 1 * ((1 / 256 : ℝ) ^ J) :=
          mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg (by positivity) _)
        _ = _ := one_mul _

/-- With the roadmap calibration `Lambda ≤ J / 4096`, the factorial series
strictly above degree `3J` is bounded by `2⁻²⁴J`. -/
lemma quadratic_factorial_tail_three_mul_le_pow (Lambda : ℝ) (J : ℕ)
    (hLambda : 0 ≤ Lambda) (hsmall : Lambda ≤ (J : ℝ) / 4096) :
    (∑' k : ℕ,
      ((3 * J + 1 + k : ℕ) : ℝ) ^ 2 * (4 * Lambda) ^ (3 * J + 1 + k) /
        (3 * J + 1 + k).factorial) ≤
      ((1 : ℝ) / 256) ^ (3 * J) := by
  let f : ℕ → ℝ := fun k =>
    ((3 * J + 1 + k : ℕ) : ℝ) ^ 2 * (4 * Lambda) ^ (3 * J + 1 + k) /
      (3 * J + 1 + k).factorial
  let g : ℕ → ℝ := fun k => ((1 : ℝ) / 256) ^ (3 * J + 1 + k)
  have hf_nonneg : ∀ k, 0 ≤ f k := by
    intro k
    exact div_nonneg
      (mul_nonneg (sq_nonneg _) (pow_nonneg (by positivity) _)) (by positivity)
  have hfg : ∀ k, f k ≤ g k := by
    intro k
    apply quadratic_factorial_term_le_geometric_of_ratio Lambda (3 * J + 1 + k)
    · omega
    · exact hLambda
    · have hcast : (3 : ℝ) * J ≤ (3 * J + 1 + k : ℕ) := by
        norm_cast
        omega
      nlinarith
  have hg : Summable g := by
    change Summable (fun k : ℕ => ((1 : ℝ) / 256) ^ (3 * J + 1 + k))
    simpa only [show ∀ k : ℕ, 3 * J + 1 + k = (3 * J + 1) + k by omega,
      pow_add] using
      (summable_geometric_of_lt_one (r := (1 : ℝ) / 256)
        (by positivity) (by norm_num)).mul_left (((1 : ℝ) / 256) ^ (3 * J + 1))
  have hf : Summable f := Summable.of_nonneg_of_le hf_nonneg hfg hg
  change (∑' k, f k) ≤ _
  calc
    (∑' k, f k) ≤ ∑' k, g k := hf.tsum_le_tsum hfg hg
    _ = ((1 : ℝ) / 256) ^ (3 * J + 1) * (256 / 255 : ℝ) :=
      tsum_geometric_256_shift (3 * J)
    _ ≤ 2 * ((1 : ℝ) / 256) ^ (3 * J + 1) := by
      rw [mul_comm 2]
      exact mul_le_mul_of_nonneg_left (by norm_num) (pow_nonneg (by positivity) _)
    _ ≤ ((1 : ℝ) / 256) ^ (3 * J) := by
      rw [pow_succ]
      calc
        2 * (((1 : ℝ) / 256) ^ (3 * J) * (1 / 256)) =
            (1 / 128 : ℝ) * ((1 / 256 : ℝ) ^ (3 * J)) := by ring
        _ ≤ 1 * ((1 / 256 : ℝ) ^ (3 * J)) :=
          mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg (by positivity) _)
        _ = _ := one_mul _

/-- Equation (67) in the calibration used by the roadmap: after multiplying
the Taylor tail by `J rho² / 16`, it is bounded by
`rho² J³ 16⁻J`. -/
lemma signedScore_chiSquare_tail_three_mul_le (rho Lambda : ℝ) (J : ℕ)
    (hJ : 1 ≤ J) (hLambda : 0 ≤ Lambda)
    (hsmall : Lambda ≤ (J : ℝ) / 4096) :
    ((J : ℝ) * rho ^ 2 / 16) *
        (∑' k : ℕ,
          ((3 * J + 1 + k : ℕ) : ℝ) ^ 2 * (4 * Lambda) ^ (3 * J + 1 + k) /
            (3 * J + 1 + k).factorial) ≤
      rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J := by
  have hcoef : 0 ≤ (J : ℝ) * rho ^ 2 / 16 := by positivity
  have hbase : ((1 : ℝ) / 256) ^ (3 * J) ≤ ((1 : ℝ) / 16) ^ J := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    norm_num
  have hJreal : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJscale : (J : ℝ) / 16 ≤ (J : ℝ) ^ 3 := by
    calc
      (J : ℝ) / 16 ≤ J := by nlinarith
      _ = J * 1 := by ring
      _ ≤ J * J ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [sq_nonneg ((J : ℝ) - 1)]
      _ = J ^ 3 := by ring
  calc
    ((J : ℝ) * rho ^ 2 / 16) *
        (∑' k : ℕ,
          ((3 * J + 1 + k : ℕ) : ℝ) ^ 2 * (4 * Lambda) ^ (3 * J + 1 + k) /
            (3 * J + 1 + k).factorial) ≤
        ((J : ℝ) * rho ^ 2 / 16) * ((1 : ℝ) / 256) ^ (3 * J) :=
      mul_le_mul_of_nonneg_left
        (quadratic_factorial_tail_three_mul_le_pow Lambda J hLambda hsmall) hcoef
    _ ≤ ((J : ℝ) * rho ^ 2 / 16) * ((1 : ℝ) / 16) ^ J :=
      mul_le_mul_of_nonneg_left hbase hcoef
    _ = (rho ^ 2 * ((J : ℝ) / 16)) * ((1 : ℝ) / 16) ^ J := by ring
    _ ≤ (rho ^ 2 * (J : ℝ) ^ 3) * ((1 : ℝ) / 16) ^ J := by
      gcongr
    _ = rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J := rfl

/-- The analytic tail in the signed-score chi-square calculation, including
the radius and polynomial prefactors, is bounded by `C rho² J³ 2⁻⁸J`.
This form is ready for the product-TV calibration after the probabilistic
Gram expansion supplies its nonnegative constant `C`. -/
-- keep: standalone analytic tail bound for auditing the converse calibration
lemma signedScore_chiSquare_tail_le (C rho Lambda : ℝ) (J : ℕ)
    (hC : 0 ≤ C) (hLambda : 0 ≤ Lambda)
    (hsmall : Lambda ≤ (1 : ℝ) / 4096) :
    C * rho ^ 2 * (J : ℝ) ^ 3 *
        (∑' k : ℕ,
          ((J + 1 + k : ℕ) : ℝ) ^ 2 * (4 * Lambda) ^ (J + 1 + k) /
            (J + 1 + k).factorial) ≤
      C * rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 256) ^ J := by
  apply mul_le_mul_of_nonneg_left
  · exact quadratic_factorial_tail_le_pow Lambda J hLambda hsmall
  · positivity

/-- Four marked Poisson counts, grouped into two pairs so product integrals can
be reduced to four scalar Poisson moment-generating functions. -/
abbrev SignedScoreCounts := (ℕ × ℕ) × (ℕ × ℕ)

/-- A one-count Poisson likelihood ratio relative to a positive reference
intensity. -/
@[no_expose]
noncomputable def poissonReferenceLikelihood (Lambda v : ℝ) (z : ℕ) : ℝ :=
  Real.exp (Lambda - v) * (v / Lambda) ^ z

/-- A nonnegative-rate Poisson law has the displayed likelihood density with
respect to a positive reference Poisson law. -/
lemma poissonMeasure_eq_withDensity_reference (Lambda v : ℝ)
    (hLambda : 0 < Lambda) (hv : 0 ≤ v) :
    poissonMeasure (Real.toNNReal v) =
      (poissonMeasure (Real.toNNReal Lambda)).withDensity
        (fun z => ENNReal.ofReal (poissonReferenceLikelihood Lambda v z)) := by
  apply Measure.ext_of_singleton
  intro z
  rw [withDensity_apply _ (MeasurableSet.singleton z), lintegral_singleton]
  simp only [poissonMeasure_singleton, poissonReferenceLikelihood,
    Real.coe_toNNReal _ hv, Real.coe_toNNReal _ hLambda.le]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show Real.exp (-v) = Real.exp (-Lambda) * Real.exp (Lambda - v) by
    rw [← Real.exp_add]
    congr 1
    ring]
  rw [div_pow]
  field_simp

/-- The four independent reference counts, each with mean `Lambda`. -/
@[no_expose]
noncomputable def signedScoreReferenceLaw (Lambda : ℝ) : Measure SignedScoreCounts :=
  let Q := poissonMeasure (Real.toNNReal Lambda)
  (Q.prod Q).prod (Q.prod Q)

/-- The common four-count reference law is a probability measure for every
real reference parameter.  Negative inputs are truncated by `Real.toNNReal`
in each Poisson coordinate. -/
instance signedScoreReferenceLaw_isProbabilityMeasure (Lambda : ℝ) :
    IsProbabilityMeasure (signedScoreReferenceLaw Lambda) := by
  unfold signedScoreReferenceLaw
  infer_instance

/-- The four-count law at a specified nonnegative intensity vector. -/
@[no_expose]
noncomputable def signedScorePoissonLaw (v : Fin 4 → ℝ) :
    Measure SignedScoreCounts :=
  let Q := fun s => poissonMeasure (Real.toNNReal (v s))
  ((Q 0).prod (Q 1)).prod ((Q 2).prod (Q 3))

/-- Singleton probabilities of the nested four-count representation factor
coordinatewise. -/
lemma signedScorePoissonLaw_singleton_expanded (v : Fin 4 → ℝ)
    (z : SignedScoreCounts) :
    signedScorePoissonLaw v {z} =
      poissonMeasure (Real.toNNReal (v 0)) {z.1.1} *
      poissonMeasure (Real.toNNReal (v 1)) {z.1.2} *
      poissonMeasure (Real.toNNReal (v 2)) {z.2.1} *
      poissonMeasure (Real.toNNReal (v 3)) {z.2.2} := by
  rcases z with ⟨⟨z0, z1⟩, ⟨z2, z3⟩⟩
  unfold signedScorePoissonLaw
  rw [show ({((z0, z1), (z2, z3))} : Set SignedScoreCounts) =
      ({(z0, z1)} : Set (ℕ × ℕ)) ×ˢ ({(z2, z3)} : Set (ℕ × ℕ)) by
        ext x
        simp, Measure.prod_prod]
  rw [show ({(z0, z1)} : Set (ℕ × ℕ)) =
      ({z0} : Set ℕ) ×ˢ ({z1} : Set ℕ) by ext x; simp,
    show ({(z2, z3)} : Set (ℕ × ℕ)) =
      ({z2} : Set ℕ) ×ˢ ({z3} : Set ℕ) by ext x; simp,
    Measure.prod_prod, Measure.prod_prod]
  ring

/-- Every four-coordinate signed-score Poisson law is a probability measure. -/
lemma signedScorePoissonLaw_isProbabilityMeasure (v : Fin 4 → ℝ) :
    IsProbabilityMeasure (signedScorePoissonLaw v) := by
  unfold signedScorePoissonLaw
  infer_instance

/-- Prior predictive four-count law for a distribution of intensity vectors. -/
@[no_expose]
noncomputable def signedScoreMixtureLaw (pi : Measure (Fin 4 → ℝ)) :
    Measure SignedScoreCounts :=
  pi.bind signedScorePoissonLaw

lemma signedScoreMixtureLaw_eq_bind (pi : Measure (Fin 4 → ℝ)) :
    signedScoreMixtureLaw pi = pi.bind signedScorePoissonLaw := by
  rfl

/-- Binding a probability prior through the measurable signed-score Poisson
kernel produces a probability predictive law. -/
lemma signedScoreMixtureLaw_isProbabilityMeasure (pi : Measure (Fin 4 → ℝ))
    [IsProbabilityMeasure pi] (hkernel : AEMeasurable signedScorePoissonLaw pi) :
    IsProbabilityMeasure (signedScoreMixtureLaw pi) := by
  unfold signedScoreMixtureLaw
  apply isProbabilityMeasure_bind hkernel
  filter_upwards [] with v
  exact signedScorePoissonLaw_isProbabilityMeasure v

/-- Product likelihood ratio for a four-vector of marked intensities. -/
@[no_expose]
noncomputable def signedScoreLikelihood (Lambda : ℝ) (v : Fin 4 → ℝ)
    (z : SignedScoreCounts) : ℝ :=
  poissonReferenceLikelihood Lambda (v 0) z.1.1 *
  poissonReferenceLikelihood Lambda (v 1) z.1.2 *
  poissonReferenceLikelihood Lambda (v 2) z.2.1 *
  poissonReferenceLikelihood Lambda (v 3) z.2.2

/-- The candidate density of a four-count prior predictive law relative to the
common reference experiment. -/
@[no_expose]
noncomputable def signedScoreMixtureLikelihood (Lambda : ℝ)
    (pi : Measure (Fin 4 → ℝ)) (z : SignedScoreCounts) : ℝ :=
  ∫ v, signedScoreLikelihood Lambda v z ∂pi

/-- For fixed counts, the four-count likelihood varies continuously with the
intensity vector. -/
@[fun_prop] lemma signedScoreLikelihood_continuous_intensity (Lambda : ℝ)
    (z : SignedScoreCounts) :
    Continuous (fun v => signedScoreLikelihood Lambda v z) := by
  unfold signedScoreLikelihood poissonReferenceLikelihood
  fun_prop

/-- For fixed counts, the four-count likelihood is measurable in the
intensity vector. -/
@[fun_prop] lemma signedScoreLikelihood_measurable_intensity (Lambda : ℝ)
    (z : SignedScoreCounts) :
    Measurable (fun v => signedScoreLikelihood Lambda v z) :=
  (signedScoreLikelihood_continuous_intensity Lambda z).measurable

/-- For fixed counts, the four-count likelihood is strongly measurable in the
intensity vector.  This is the regularity required by `integral_map`. -/
@[fun_prop] lemma signedScoreLikelihood_stronglyMeasurable_intensity (Lambda : ℝ)
    (z : SignedScoreCounts) :
    StronglyMeasurable (fun v => signedScoreLikelihood Lambda v z) :=
  (signedScoreLikelihood_measurable_intensity Lambda z).stronglyMeasurable

/-- For a fixed intensity vector, the likelihood is measurable as a function
of the four discrete counts. -/
@[fun_prop] lemma signedScoreLikelihood_measurable_count (Lambda : ℝ)
    (v : Fin 4 → ℝ) : Measurable (signedScoreLikelihood Lambda v) := by
  exact measurable_of_countable _

/-- For a fixed intensity vector, the likelihood is strongly measurable as a
function of the four discrete counts. -/
@[fun_prop] lemma signedScoreLikelihood_stronglyMeasurable_count (Lambda : ℝ)
    (v : Fin 4 → ℝ) : StronglyMeasurable (signedScoreLikelihood Lambda v) :=
  (signedScoreLikelihood_measurable_count Lambda v).stronglyMeasurable

/-- The likelihood is jointly strongly measurable in its intensity vector
and count argument. -/
@[fun_prop] lemma signedScoreLikelihood_joint_stronglyMeasurable (Lambda : ℝ) :
    StronglyMeasurable
      (fun p : (Fin 4 → ℝ) × SignedScoreCounts =>
        signedScoreLikelihood Lambda p.1 p.2) := by
  exact stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun z => signedScoreLikelihood_continuous_intensity Lambda z)
    (fun v => signedScoreLikelihood_stronglyMeasurable_count Lambda v)

/-- The likelihood is jointly measurable in its intensity vector and count
argument. -/
@[fun_prop] lemma signedScoreLikelihood_joint_measurable (Lambda : ℝ) :
    Measurable
      (fun p : (Fin 4 → ℝ) × SignedScoreCounts =>
        signedScoreLikelihood Lambda p.1 p.2) :=
  (signedScoreLikelihood_joint_stronglyMeasurable Lambda).measurable

/-- At the common reference intensity, the likelihood ratio is identically
one. -/
lemma signedScoreLikelihood_reference (Lambda : ℝ) (hLambda : 0 < Lambda)
    (z : SignedScoreCounts) :
    signedScoreLikelihood Lambda (fun _ => Lambda) z = 1 := by
  simp [signedScoreLikelihood, poissonReferenceLikelihood, hLambda.ne']

/-- Unfolding the prior-predictive likelihood exposes its integral over the
intensity prior. -/
lemma signedScoreMixtureLikelihood_eq_integral (Lambda : ℝ)
    (pi : Measure (Fin 4 → ℝ)) (z : SignedScoreCounts) :
    signedScoreMixtureLikelihood Lambda pi z =
      ∫ v, signedScoreLikelihood Lambda v z ∂pi :=
  signedScoreMixtureLikelihood.eq_1 Lambda pi z

/-- A mapped intensity prior can be integrated by pulling the likelihood back
along the intensity map. -/
-- keep: reusable change-of-variables identity for signed-score mixture likelihoods
lemma signedScoreMixtureLikelihood_map (Lambda : ℝ) {alpha : Type*}
    [MeasurableSpace alpha] (f : alpha → Fin 4 → ℝ) (mu : Measure alpha)
    (hf : Measurable f) (z : SignedScoreCounts) :
    signedScoreMixtureLikelihood Lambda (Measure.map f mu) z =
      ∫ x, signedScoreLikelihood Lambda (f x) z ∂mu := by
  rw [signedScoreMixtureLikelihood_eq_integral,
    integral_map_of_stronglyMeasurable hf
      (signedScoreLikelihood_stronglyMeasurable_intensity Lambda z)]

/-- The prior-predictive likelihood is measurable in the discrete count
argument. -/
@[fun_prop] lemma signedScoreMixtureLikelihood_measurable (Lambda : ℝ)
    (pi : Measure (Fin 4 → ℝ)) :
    Measurable (signedScoreMixtureLikelihood Lambda pi) := by
  exact measurable_of_countable _

/-- The prior-predictive likelihood is strongly measurable in the discrete
count argument. -/
@[fun_prop] lemma signedScoreMixtureLikelihood_stronglyMeasurable (Lambda : ℝ)
    (pi : Measure (Fin 4 → ℝ)) :
    StronglyMeasurable (signedScoreMixtureLikelihood Lambda pi) :=
  (signedScoreMixtureLikelihood_measurable Lambda pi).stronglyMeasurable

lemma signedScoreLikelihood_nonneg (Lambda : ℝ) (v : Fin 4 → ℝ)
    (z : SignedScoreCounts) (hLambda : 0 < Lambda) (hv : ∀ s, 0 ≤ v s) :
    0 ≤ signedScoreLikelihood Lambda v z := by
  simp only [signedScoreLikelihood, poissonReferenceLikelihood]
  have hfactor (s : Fin 4) (k : ℕ) :
      0 ≤ Real.exp (Lambda - v s) * (v s / Lambda) ^ k :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg (div_nonneg (hv s) hLambda.le) _)
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (hfactor 0 z.1.1) (hfactor 1 z.1.2))
      (hfactor 2 z.2.1))
    (hfactor 3 z.2.2)

/-- A prior supported on nonnegative intensity vectors has a nonnegative
prior-predictive likelihood. -/
lemma signedScoreMixtureLikelihood_nonneg (Lambda : ℝ)
    (pi : Measure (Fin 4 → ℝ)) (z : SignedScoreCounts)
    (hLambda : 0 < Lambda) (hsupport : ∀ᵐ v ∂pi, ∀ s, 0 ≤ v s) :
    0 ≤ signedScoreMixtureLikelihood Lambda pi z := by
  rw [signedScoreMixtureLikelihood_eq_integral]
  apply integral_nonneg_of_ae
  filter_upwards [hsupport] with v hv
  exact signedScoreLikelihood_nonneg Lambda v z hLambda hv

/-- The four-count likelihood is the density of the vector Poisson law with
respect to the common positive reference law. -/
lemma signedScorePoissonLaw_eq_withDensity (Lambda : ℝ) (v : Fin 4 → ℝ)
    (hLambda : 0 < Lambda) (hv : ∀ s, 0 ≤ v s) :
    signedScorePoissonLaw v =
      (signedScoreReferenceLaw Lambda).withDensity
        (fun z => ENNReal.ofReal (signedScoreLikelihood Lambda v z)) := by
  unfold signedScorePoissonLaw signedScoreReferenceLaw
  simp only
  rw [poissonMeasure_eq_withDensity_reference Lambda (v 0) hLambda (hv 0),
    poissonMeasure_eq_withDensity_reference Lambda (v 1) hLambda (hv 1),
    poissonMeasure_eq_withDensity_reference Lambda (v 2) hLambda (hv 2),
    poissonMeasure_eq_withDensity_reference Lambda (v 3) hLambda (hv 3)]
  rw [MeasureTheory.prod_withDensity (measurable_of_countable _)
      (measurable_of_countable _),
    MeasureTheory.prod_withDensity (measurable_of_countable _)
      (measurable_of_countable _),
    MeasureTheory.prod_withDensity (measurable_of_countable _)
      (measurable_of_countable _)]
  congr 1
  funext z
  have hnonneg (s : Fin 4) (k : ℕ) :
      0 ≤ poissonReferenceLikelihood Lambda (v s) k := by
    unfold poissonReferenceLikelihood
    exact mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (div_nonneg (hv s) hLambda.le) _)
  simp only [signedScoreLikelihood]
  conv_rhs =>
    congr
    rw [show
      poissonReferenceLikelihood Lambda (v 0) z.1.1 *
          poissonReferenceLikelihood Lambda (v 1) z.1.2 *
          poissonReferenceLikelihood Lambda (v 2) z.2.1 *
          poissonReferenceLikelihood Lambda (v 3) z.2.2 =
        (poissonReferenceLikelihood Lambda (v 0) z.1.1 *
          poissonReferenceLikelihood Lambda (v 1) z.1.2) *
        (poissonReferenceLikelihood Lambda (v 2) z.2.1 *
          poissonReferenceLikelihood Lambda (v 3) z.2.2) by ring]
  rw [ENNReal.ofReal_mul (mul_nonneg (hnonneg 0 z.1.1) (hnonneg 1 z.1.2)),
    ENNReal.ofReal_mul (hnonneg 0 z.1.1),
    ENNReal.ofReal_mul (hnonneg 2 z.2.1)]

/-- Interchanging the prior integral with the common reference density gives
the prior-predictive likelihood.  The integrability assumption is exactly what
is needed to turn the nonnegative `lintegral` into the displayed real
integral; bounded-support priors used in the converse satisfy it. -/
lemma signedScoreMixtureLaw_eq_withDensity (Lambda : ℝ)
    (pi : Measure (Fin 4 → ℝ)) (hLambda : 0 < Lambda)
    (hkernel : AEMeasurable signedScorePoissonLaw pi)
    (hsupport : ∀ᵐ v ∂pi, ∀ s, 0 ≤ v s)
    (hint : ∀ z, Integrable (fun v => signedScoreLikelihood Lambda v z) pi) :
    signedScoreMixtureLaw pi =
      (signedScoreReferenceLaw Lambda).withDensity
        (fun z => ENNReal.ofReal (signedScoreMixtureLikelihood Lambda pi z)) := by
  letI : IsProbabilityMeasure (signedScoreReferenceLaw Lambda) := by
    unfold signedScoreReferenceLaw
    infer_instance
  apply Measure.ext_of_singleton
  intro z
  rw [signedScoreMixtureLaw, Measure.bind_apply (MeasurableSet.singleton z) hkernel,
    withDensity_apply _ (MeasurableSet.singleton z), lintegral_singleton]
  have hpoint : ∀ᵐ v ∂pi,
      signedScorePoissonLaw v {z} =
        ENNReal.ofReal (signedScoreLikelihood Lambda v z) *
          signedScoreReferenceLaw Lambda {z} := by
    filter_upwards [hsupport] with v hv
    rw [signedScorePoissonLaw_eq_withDensity Lambda v hLambda hv,
      withDensity_apply _ (MeasurableSet.singleton z), lintegral_singleton]
  rw [lintegral_congr_ae hpoint]
  rw [lintegral_mul_const' _ _ (measure_ne_top _ _)]
  rw [← ofReal_integral_eq_lintegral_ofReal (hint z)]
  · rfl
  · filter_upwards [hsupport] with v hv
    exact signedScoreLikelihood_nonneg Lambda v z hLambda hv

/-- The scalar Poisson likelihood inner product.  This is the one-coordinate
factor in roadmap equation (64). -/
lemma poissonReferenceLikelihood_inner (Lambda v w : ℝ) (hLambda : 0 < Lambda) :
    (∫ z : ℕ, poissonReferenceLikelihood Lambda v z *
        poissonReferenceLikelihood Lambda w z ∂poissonMeasure (Real.toNNReal Lambda)) =
      Real.exp ((v - Lambda) * (w - Lambda) / Lambda) := by
  have hcast : ((Real.toNNReal Lambda : NNReal) : ℝ) = Lambda :=
    Real.coe_toNNReal Lambda hLambda.le
  rw [show (fun z : ℕ => poissonReferenceLikelihood Lambda v z *
      poissonReferenceLikelihood Lambda w z) = fun z =>
        (Real.exp (Lambda - v) * Real.exp (Lambda - w)) *
          ((v / Lambda) * (w / Lambda)) ^ z by
    funext z
    simp only [poissonReferenceLikelihood, mul_pow]
    ring]
  rw [integral_const_mul,
    Causalean.Stat.Minimax.Multinomial.TwoSampleL1.poisson_power_mgf,
    hcast, ← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- The exact four-count likelihood Gram formula in roadmap equation (64). -/
lemma signedScoreLikelihood_inner (Lambda : ℝ) (v w : Fin 4 → ℝ)
    (hLambda : 0 < Lambda) :
    (∫ z, signedScoreLikelihood Lambda v z * signedScoreLikelihood Lambda w z
        ∂signedScoreReferenceLaw Lambda) =
      Real.exp (∑ s : Fin 4, (v s - Lambda) * (w s - Lambda) / Lambda) := by
  let Q := poissonMeasure (Real.toNNReal Lambda)
  let f01 : ℕ × ℕ → ℝ := fun z =>
    (poissonReferenceLikelihood Lambda (v 0) z.1 *
      poissonReferenceLikelihood Lambda (w 0) z.1) *
    (poissonReferenceLikelihood Lambda (v 1) z.2 *
      poissonReferenceLikelihood Lambda (w 1) z.2)
  let f23 : ℕ × ℕ → ℝ := fun z =>
    (poissonReferenceLikelihood Lambda (v 2) z.1 *
      poissonReferenceLikelihood Lambda (w 2) z.1) *
    (poissonReferenceLikelihood Lambda (v 3) z.2 *
      poissonReferenceLikelihood Lambda (w 3) z.2)
  have hfactor (z : SignedScoreCounts) :
      signedScoreLikelihood Lambda v z * signedScoreLikelihood Lambda w z =
        f01 z.1 * f23 z.2 := by
    simp only [signedScoreLikelihood, f01, f23]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hfactor)]
  simp only [signedScoreReferenceLaw]
  have h01 : (∫ z, f01 z ∂Q.prod Q) =
      Real.exp ((v 0 - Lambda) * (w 0 - Lambda) / Lambda) *
        Real.exp ((v 1 - Lambda) * (w 1 - Lambda) / Lambda) := by
    rw [show (∫ z, f01 z ∂Q.prod Q) =
        (∫ z, poissonReferenceLikelihood Lambda (v 0) z *
          poissonReferenceLikelihood Lambda (w 0) z ∂Q) *
        ∫ z, poissonReferenceLikelihood Lambda (v 1) z *
          poissonReferenceLikelihood Lambda (w 1) z ∂Q by
      simpa only [f01] using
        (MeasureTheory.integral_prod_mul (μ := Q) (ν := Q)
          (fun z => poissonReferenceLikelihood Lambda (v 0) z *
            poissonReferenceLikelihood Lambda (w 0) z)
          (fun z => poissonReferenceLikelihood Lambda (v 1) z *
            poissonReferenceLikelihood Lambda (w 1) z))]
    rw [
      poissonReferenceLikelihood_inner Lambda (v 0) (w 0) hLambda,
      poissonReferenceLikelihood_inner Lambda (v 1) (w 1) hLambda]
  have h23 : (∫ z, f23 z ∂Q.prod Q) =
      Real.exp ((v 2 - Lambda) * (w 2 - Lambda) / Lambda) *
        Real.exp ((v 3 - Lambda) * (w 3 - Lambda) / Lambda) := by
    rw [show (∫ z, f23 z ∂Q.prod Q) =
        (∫ z, poissonReferenceLikelihood Lambda (v 2) z *
          poissonReferenceLikelihood Lambda (w 2) z ∂Q) *
        ∫ z, poissonReferenceLikelihood Lambda (v 3) z *
          poissonReferenceLikelihood Lambda (w 3) z ∂Q by
      simpa only [f23] using
        (MeasureTheory.integral_prod_mul (μ := Q) (ν := Q)
          (fun z => poissonReferenceLikelihood Lambda (v 2) z *
            poissonReferenceLikelihood Lambda (w 2) z)
          (fun z => poissonReferenceLikelihood Lambda (v 3) z *
            poissonReferenceLikelihood Lambda (w 3) z))]
    rw [
      poissonReferenceLikelihood_inner Lambda (v 2) (w 2) hLambda,
      poissonReferenceLikelihood_inner Lambda (v 3) (w 3) hLambda]
  rw [MeasureTheory.integral_prod_mul f01 f23]
  rw [h01, h23,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Fin.sum_univ_four]
  ring

/-- Fubini converts the inner product of two prior-predictive likelihoods into
the product-prior exponential Gram integral. -/
lemma signedScoreMixtureLikelihood_inner_prod (Lambda : ℝ)
    (pi0 pi1 : Measure (Fin 4 → ℝ)) [SFinite pi0] [SFinite pi1]
    (hLambda : 0 < Lambda)
    (hjoint : Integrable (fun p : ((Fin 4 → ℝ) × (Fin 4 → ℝ)) × SignedScoreCounts =>
      signedScoreLikelihood Lambda p.1.1 p.2 *
        signedScoreLikelihood Lambda p.1.2 p.2)
      ((pi0.prod pi1).prod (signedScoreReferenceLaw Lambda))) :
    (∫ z, signedScoreMixtureLikelihood Lambda pi0 z *
        signedScoreMixtureLikelihood Lambda pi1 z
        ∂signedScoreReferenceLaw Lambda) =
      ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
        Real.exp (∑ s : Fin 4,
          (p.1 s - Lambda) * (p.2 s - Lambda) / Lambda) ∂pi0.prod pi1 := by
  let F : ((Fin 4 → ℝ) × (Fin 4 → ℝ)) × SignedScoreCounts → ℝ := fun p =>
    signedScoreLikelihood Lambda p.1.1 p.2 *
      signedScoreLikelihood Lambda p.1.2 p.2
  let G : (Fin 4 → ℝ) × (Fin 4 → ℝ) → ℝ := fun p =>
    Real.exp (∑ s : Fin 4,
      (p.1 s - Lambda) * (p.2 s - Lambda) / Lambda)
  have hinner : ∀ p, (∫ z, F (p, z) ∂signedScoreReferenceLaw Lambda) = G p := by
    intro p
    exact signedScoreLikelihood_inner Lambda p.1 p.2 hLambda
  calc
    (∫ z, signedScoreMixtureLikelihood Lambda pi0 z *
        signedScoreMixtureLikelihood Lambda pi1 z
        ∂signedScoreReferenceLaw Lambda) =
        ∫ z, ∫ p, F (p, z) ∂pi0.prod pi1
          ∂signedScoreReferenceLaw Lambda := by
      apply integral_congr_ae
      filter_upwards [] with z
      simpa only [signedScoreMixtureLikelihood, F] using
        (MeasureTheory.integral_prod_mul
          (μ := pi0) (ν := pi1)
          (fun v => signedScoreLikelihood Lambda v z)
          (fun w => signedScoreLikelihood Lambda w z)).symm
    _ = ∫ p, ∫ z, F (p, z) ∂signedScoreReferenceLaw Lambda
          ∂pi0.prod pi1 := (integral_integral_swap hjoint).symm
    _ = ∫ p, G p ∂pi0.prod pi1 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hinner
    _ = ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
        Real.exp (∑ s : Fin 4,
          (p.1 s - Lambda) * (p.2 s - Lambda) / Lambda) ∂pi0.prod pi1 := rfl

/-- Iterated form of the product-prior Gram identity, equation (65). -/
-- keep: paper equation (65) endpoint exposing the iterated Gram identity
lemma signedScoreMixtureLikelihood_inner (Lambda : ℝ)
    (pi0 pi1 : Measure (Fin 4 → ℝ)) [SFinite pi0] [SFinite pi1]
    (hLambda : 0 < Lambda)
    (hjoint : Integrable (fun p : ((Fin 4 → ℝ) × (Fin 4 → ℝ)) × SignedScoreCounts =>
      signedScoreLikelihood Lambda p.1.1 p.2 *
        signedScoreLikelihood Lambda p.1.2 p.2)
      ((pi0.prod pi1).prod (signedScoreReferenceLaw Lambda)))
    (hgram : Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
        Real.exp (∑ s : Fin 4,
          (p.1 s - Lambda) * (p.2 s - Lambda) / Lambda))
          (pi0.prod pi1)) :
    (∫ z, signedScoreMixtureLikelihood Lambda pi0 z *
        signedScoreMixtureLikelihood Lambda pi1 z
        ∂signedScoreReferenceLaw Lambda) =
      ∫ v, ∫ w,
        Real.exp (∑ s : Fin 4,
          (v s - Lambda) * (w s - Lambda) / Lambda) ∂pi1 ∂pi0 := by
  rw [signedScoreMixtureLikelihood_inner_prod Lambda pi0 pi1 hLambda hjoint]
  symm
  exact integral_integral hgram

/-- Centered multivariate monomials occurring in the Taylor expansion of the
exponential Gram kernel. -/
@[no_expose]
noncomputable def signedScoreCenteredMonomial (Lambda : ℝ)
    (alpha : Fin 4 → ℕ) (v : Fin 4 → ℝ) : ℝ :=
  ∏ s, (v s - Lambda) ^ alpha s

/-- Unfolding a centered multi-index monomial exposes its raw finite product.
This equation bridges the opaque public definition to product-form moment
hypotheses. -/
lemma signedScoreCenteredMonomial_eq_prod (Lambda : ℝ) (alpha : Fin 4 → ℕ)
    (v : Fin 4 → ℝ) :
    signedScoreCenteredMonomial Lambda alpha v =
      ∏ s, (v s - Lambda) ^ alpha s :=
  signedScoreCenteredMonomial.eq_1 Lambda alpha v

/-- A finite multivariate polynomial in the centered intensity vector. -/
@[no_expose]
noncomputable def signedScoreFinitePolynomial (Lambda : ℝ)
    (A : Finset (Fin 4 → ℕ)) (c : (Fin 4 → ℕ) → ℝ)
    (v : Fin 4 → ℝ) : ℝ :=
  ∑ alpha ∈ A, c alpha * signedScoreCenteredMonomial Lambda alpha v

/-- Moment cancellation extends term by term to every finite Taylor
polynomial whose multi-indices have total degree at most `J`.  This packages
the exact low-degree cancellation step between equations (65) and (66). -/
-- keep: reusable finite-polynomial consequence of multivariate moment matching
lemma signedScoreFinitePolynomial_integral_eq_of_moments_eq
    (Lambda : ℝ) (J : ℕ) (pi0 pi1 : Measure (Fin 4 → ℝ))
    (A : Finset (Fin 4 → ℕ)) (c : (Fin 4 → ℕ) → ℝ)
    (hdegree : ∀ alpha ∈ A, (∑ s, alpha s) ≤ J)
    (hmom : ∀ alpha, (∑ s, alpha s) ≤ J →
      (∫ v, signedScoreCenteredMonomial Lambda alpha v ∂pi0) =
        ∫ v, signedScoreCenteredMonomial Lambda alpha v ∂pi1)
    (hint0 : ∀ alpha ∈ A,
      Integrable (signedScoreCenteredMonomial Lambda alpha) pi0)
    (hint1 : ∀ alpha ∈ A,
      Integrable (signedScoreCenteredMonomial Lambda alpha) pi1) :
    (∫ v, signedScoreFinitePolynomial Lambda A c v ∂pi0) =
      ∫ v, signedScoreFinitePolynomial Lambda A c v ∂pi1 := by
  simp only [signedScoreFinitePolynomial]
  rw [integral_finset_sum A (fun alpha halpha =>
      (hint0 alpha halpha).const_mul (c alpha)),
    integral_finset_sum A (fun alpha halpha =>
      (hint1 alpha halpha).const_mul (c alpha))]
  apply Finset.sum_congr rfl
  intro alpha halpha
  rw [integral_const_mul, integral_const_mul,
    hmom alpha (hdegree alpha halpha)]

/-- A pointwise coupling bound transfers directly to the corresponding
expectation difference under a probability coupling. -/
lemma abs_integral_sub_integral_le_of_ae_coupling
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] (f g : Omega → ℝ) (B : ℝ)
    (hf : Integrable f mu) (hg : Integrable g mu)
    (hfg : ∀ᵐ omega ∂mu, |f omega - g omega| ≤ B) :
    |(∫ omega, f omega ∂mu) - ∫ omega, g omega ∂mu| ≤ B := by
  rw [← integral_sub hf hg]
  calc
    |∫ omega, f omega - g omega ∂mu| ≤
        ∫ omega, |f omega - g omega| ∂mu := abs_integral_le_integral_abs
    _ ≤ ∫ _omega, B ∂mu := integral_mono_ae (hf.sub hg).abs
      (integrable_const B) hfg
    _ = B := by simp

/-- A single centered-intensity power changes by at most its degree times the
coordinate displacement and the ambient intensity scale.  This is the scalar
telescoping factor used in roadmap equation (66). -/
lemma abs_pow_sub_pow_le_radius {x y Lambda rho : ℝ} (k : ℕ)
    (hLambda : 0 ≤ Lambda) (hrho : 0 ≤ rho)
    (hx : |x| ≤ Lambda) (hy : |y| ≤ Lambda)
    (hxy : |x - y| ≤ rho * Lambda) :
    |x ^ k - y ^ k| ≤ (k : ℝ) * rho * Lambda ^ k := by
  cases k with
  | zero => simp
  | succ k =>
      have hmax : max |x| |y| ≤ Lambda := max_le hx hy
      calc
        |x ^ (k + 1) - y ^ (k + 1)| ≤
            |x - y| * (k + 1 : ℕ) * max |x| |y| ^ k :=
          by simpa using (abs_pow_sub_pow_le x y (k + 1))
        _ ≤ (rho * Lambda) * (k + 1 : ℕ) * Lambda ^ k := by
          gcongr
        _ = ((k + 1 : ℕ) : ℝ) * rho * Lambda ^ (k + 1) := by
          rw [pow_succ]
          ring

/-- Four-coordinate telescoping of a centered multi-index monomial. -/
lemma signedScoreCenteredMonomial_sub_eq_telescoping (Lambda : ℝ)
    (alpha : Fin 4 → ℕ) (x y : Fin 4 → ℝ) :
    signedScoreCenteredMonomial Lambda alpha x -
        signedScoreCenteredMonomial Lambda alpha y =
      (((x 0 - Lambda) ^ alpha 0 - (y 0 - Lambda) ^ alpha 0) *
          (x 1 - Lambda) ^ alpha 1 * (x 2 - Lambda) ^ alpha 2 *
          (x 3 - Lambda) ^ alpha 3) +
      ((y 0 - Lambda) ^ alpha 0 *
          ((x 1 - Lambda) ^ alpha 1 - (y 1 - Lambda) ^ alpha 1) *
          (x 2 - Lambda) ^ alpha 2 * (x 3 - Lambda) ^ alpha 3) +
      ((y 0 - Lambda) ^ alpha 0 * (y 1 - Lambda) ^ alpha 1 *
          ((x 2 - Lambda) ^ alpha 2 - (y 2 - Lambda) ^ alpha 2) *
          (x 3 - Lambda) ^ alpha 3) +
      ((y 0 - Lambda) ^ alpha 0 * (y 1 - Lambda) ^ alpha 1 *
          (y 2 - Lambda) ^ alpha 2 *
          ((x 3 - Lambda) ^ alpha 3 - (y 3 - Lambda) ^ alpha 3)) := by
  simp only [signedScoreCenteredMonomial, Fin.prod_univ_four]
  ring

/-- Radius-sensitive multi-index bound used in equation (66). -/
lemma abs_signedScoreCenteredMonomial_sub_le_radius
    (Lambda rho : ℝ) (alpha : Fin 4 → ℕ) (x y : Fin 4 → ℝ)
    (hLambda : 0 ≤ Lambda) (hrho : 0 ≤ rho)
    (hx : ∀ s, |x s| ≤ Lambda) (hy : ∀ s, |y s| ≤ Lambda)
    (hxy : ∀ s, |x s - y s| ≤ rho * Lambda) :
    |signedScoreCenteredMonomial 0 alpha x -
        signedScoreCenteredMonomial 0 alpha y| ≤
      ((∑ s, alpha s : ℕ) : ℝ) * rho * Lambda ^ (∑ s, alpha s) := by
  have hxp (s : Fin 4) : |x s ^ alpha s| ≤ Lambda ^ alpha s := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hx s) _
  have hyp (s : Fin 4) : |y s ^ alpha s| ≤ Lambda ^ alpha s := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hy s) _
  have hd (s : Fin 4) :
      |x s ^ alpha s - y s ^ alpha s| ≤
        (alpha s : ℝ) * rho * Lambda ^ alpha s :=
    abs_pow_sub_pow_le_radius (alpha s) hLambda hrho (hx s) (hy s) (hxy s)
  rw [signedScoreCenteredMonomial_sub_eq_telescoping]
  simp only [sub_zero]
  calc
    _ ≤ |(x 0 ^ alpha 0 - y 0 ^ alpha 0) * x 1 ^ alpha 1 *
          x 2 ^ alpha 2 * x 3 ^ alpha 3| +
        |y 0 ^ alpha 0 * (x 1 ^ alpha 1 - y 1 ^ alpha 1) *
          x 2 ^ alpha 2 * x 3 ^ alpha 3| +
        |y 0 ^ alpha 0 * y 1 ^ alpha 1 *
          (x 2 ^ alpha 2 - y 2 ^ alpha 2) * x 3 ^ alpha 3| +
        |y 0 ^ alpha 0 * y 1 ^ alpha 1 * y 2 ^ alpha 2 *
          (x 3 ^ alpha 3 - y 3 ^ alpha 3)| := by
      calc
        _ ≤ |(x 0 ^ alpha 0 - y 0 ^ alpha 0) * x 1 ^ alpha 1 *
              x 2 ^ alpha 2 * x 3 ^ alpha 3 +
            y 0 ^ alpha 0 * (x 1 ^ alpha 1 - y 1 ^ alpha 1) *
              x 2 ^ alpha 2 * x 3 ^ alpha 3 +
            y 0 ^ alpha 0 * y 1 ^ alpha 1 *
              (x 2 ^ alpha 2 - y 2 ^ alpha 2) * x 3 ^ alpha 3| +
            |y 0 ^ alpha 0 * y 1 ^ alpha 1 * y 2 ^ alpha 2 *
              (x 3 ^ alpha 3 - y 3 ^ alpha 3)| := abs_add_le _ _
        _ ≤ (|(x 0 ^ alpha 0 - y 0 ^ alpha 0) * x 1 ^ alpha 1 *
              x 2 ^ alpha 2 * x 3 ^ alpha 3| +
            |y 0 ^ alpha 0 * (x 1 ^ alpha 1 - y 1 ^ alpha 1) *
              x 2 ^ alpha 2 * x 3 ^ alpha 3| +
            |y 0 ^ alpha 0 * y 1 ^ alpha 1 *
              (x 2 ^ alpha 2 - y 2 ^ alpha 2) * x 3 ^ alpha 3|) + _ := by
          gcongr
          exact (abs_add_three _ _ _)
        _ = _ := by ring
    _ ≤ (alpha 0 : ℝ) * rho * Lambda ^ alpha 0 * Lambda ^ alpha 1 *
          Lambda ^ alpha 2 * Lambda ^ alpha 3 +
        Lambda ^ alpha 0 * ((alpha 1 : ℝ) * rho * Lambda ^ alpha 1) *
          Lambda ^ alpha 2 * Lambda ^ alpha 3 +
        Lambda ^ alpha 0 * Lambda ^ alpha 1 *
          ((alpha 2 : ℝ) * rho * Lambda ^ alpha 2) * Lambda ^ alpha 3 +
        Lambda ^ alpha 0 * Lambda ^ alpha 1 * Lambda ^ alpha 2 *
          ((alpha 3 : ℝ) * rho * Lambda ^ alpha 3) := by
      simp only [abs_mul]
      gcongr
      all_goals first | exact hd _ | exact hxp _ | exact hyp _
    _ = _ := by
      rw [Fin.sum_univ_four]
      push_cast
      simp only [pow_add]
      ring

/-- Coupled expectation version of the radius-sensitive multi-index bound,
matching the moment difference estimate in roadmap equation (66). -/
-- keep: paper equation (66) radius-sensitive moment-difference bound
lemma abs_signedScoreCenteredMonomial_integral_sub_le_radius
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Lambda rho : ℝ) (alpha : Fin 4 → ℕ)
    (X Y : Omega → Fin 4 → ℝ)
    (hLambda : 0 ≤ Lambda) (hrho : 0 ≤ rho)
    (hX : ∀ᵐ omega ∂mu, ∀ s, |X omega s| ≤ Lambda)
    (hY : ∀ᵐ omega ∂mu, ∀ s, |Y omega s| ≤ Lambda)
    (hXY : ∀ᵐ omega ∂mu, ∀ s,
      |X omega s - Y omega s| ≤ rho * Lambda)
    (hintX : Integrable (fun omega =>
      signedScoreCenteredMonomial 0 alpha (X omega)) mu)
    (hintY : Integrable (fun omega =>
      signedScoreCenteredMonomial 0 alpha (Y omega)) mu) :
    |(∫ omega, signedScoreCenteredMonomial 0 alpha (X omega) ∂mu) -
        ∫ omega, signedScoreCenteredMonomial 0 alpha (Y omega) ∂mu| ≤
      ((∑ s, alpha s : ℕ) : ℝ) * rho * Lambda ^ (∑ s, alpha s) := by
  apply abs_integral_sub_integral_le_of_ae_coupling mu _ _ _ hintX hintY
  filter_upwards [hX, hY, hXY] with omega hx hy hxy
  exact abs_signedScoreCenteredMonomial_sub_le_radius
    Lambda rho alpha (X omega) (Y omega) hLambda hrho hx hy hxy

/-- The independent product of the one-cell signed-score prior-predictive law. -/
@[no_expose]
noncomputable def signedScoreProductMixtureLaw (d : ℕ)
    (pi : Measure (Fin 4 → ℝ)) : Measure (Fin d → SignedScoreCounts) :=
  Measure.pi fun _ : Fin d => signedScoreMixtureLaw pi

lemma signedScoreProductMixtureLaw_eq_pi (d : ℕ)
    (pi : Measure (Fin 4 → ℝ)) :
    signedScoreProductMixtureLaw d pi =
      Measure.pi fun _ : Fin d => signedScoreMixtureLaw pi := by
  rfl

/-- General-space chi-square tensorization followed by `1 + x ≤ exp x`.
This is the product step in roadmap equation (68), before inserting the
one-cell signed-score estimate. -/
lemma signedScoreProductMixture_one_add_chiSq_le_exp
    (d : ℕ) (pi0 pi1 : Measure (Fin 4 → ℝ))
    [IsProbabilityMeasure (signedScoreMixtureLaw pi0)]
    [IsProbabilityMeasure (signedScoreMixtureLaw pi1)]
    (hac : signedScoreMixtureLaw pi0 ≪ signedScoreMixtureLaw pi1)
    (hint : Integrable (fun z =>
      (((signedScoreMixtureLaw pi0).rnDeriv (signedScoreMixtureLaw pi1) z).toReal - 1) ^ 2)
      (signedScoreMixtureLaw pi1))
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hchi : Causalean.Stat.chiSqDiv (signedScoreMixtureLaw pi0)
      (signedScoreMixtureLaw pi1) ≤ delta) :
    1 + Causalean.Stat.chiSqDiv
        (signedScoreProductMixtureLaw d pi0)
        (signedScoreProductMixtureLaw d pi1) ≤
      Real.exp ((d : ℝ) * delta) := by
  rw [signedScoreProductMixtureLaw, signedScoreProductMixtureLaw,
    Causalean.Stat.one_add_chiSqDiv_pi_iid_general
      (signedScoreMixtureLaw pi0) (signedScoreMixtureLaw pi1) hac hint]
  calc
    (1 + Causalean.Stat.chiSqDiv (signedScoreMixtureLaw pi0)
        (signedScoreMixtureLaw pi1)) ^ d ≤ (1 + delta) ^ d := by
      apply pow_le_pow_left₀
      · linarith [Causalean.Stat.chiSqDiv_nonneg
          (μ := signedScoreMixtureLaw pi0) (ν := signedScoreMixtureLaw pi1)]
      · linarith
    _ ≤ (Real.exp delta) ^ d := by
      apply pow_le_pow_left₀
      · linarith
      · simpa [add_comm] using Real.add_one_le_exp delta
    _ = Real.exp ((d : ℝ) * delta) := by
      rw [← Real.exp_nat_mul]

/-- Inserting the one-cell tail estimate and a final numerical calibration
gives the strict `1.01` product chi-square bound in roadmap equation (68). -/
lemma signedScoreProductMixture_one_add_chiSq_lt_101_div_100
    (d J : ℕ) (pi0 pi1 : Measure (Fin 4 → ℝ)) (C rho : ℝ)
    [IsProbabilityMeasure (signedScoreMixtureLaw pi0)]
    [IsProbabilityMeasure (signedScoreMixtureLaw pi1)]
    (hac : signedScoreMixtureLaw pi0 ≪ signedScoreMixtureLaw pi1)
    (hint : Integrable (fun z =>
      (((signedScoreMixtureLaw pi0).rnDeriv (signedScoreMixtureLaw pi1) z).toReal - 1) ^ 2)
      (signedScoreMixtureLaw pi1))
    (hcell : Causalean.Stat.chiSqDiv (signedScoreMixtureLaw pi0)
      (signedScoreMixtureLaw pi1) ≤
        C * rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J)
    (hcal : (d : ℝ) *
      (C * rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J) <
        Real.log ((101 : ℝ) / 100)) :
    1 + Causalean.Stat.chiSqDiv
        (signedScoreProductMixtureLaw d pi0)
        (signedScoreProductMixtureLaw d pi1) < (101 : ℝ) / 100 := by
  have hdelta : 0 ≤
      C * rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J :=
    (Causalean.Stat.chiSqDiv_nonneg
      (μ := signedScoreMixtureLaw pi0)
      (ν := signedScoreMixtureLaw pi1)).trans hcell
  calc
    1 + Causalean.Stat.chiSqDiv
        (signedScoreProductMixtureLaw d pi0)
        (signedScoreProductMixtureLaw d pi1) ≤
      Real.exp ((d : ℝ) *
        (C * rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J)) :=
      signedScoreProductMixture_one_add_chiSq_le_exp d pi0 pi1 hac hint _ hdelta hcell
    _ < Real.exp (Real.log ((101 : ℝ) / 100)) := Real.exp_lt_exp.mpr hcal
    _ = (101 : ℝ) / 100 := Real.exp_log (by norm_num)

/-- The rational budget `1/200` lies strictly below the logarithmic budget
corresponding to the `1.01` threshold. -/
lemma one_div_200_lt_log_101_div_100 :
    (1 : ℝ) / 200 < Real.log ((101 : ℝ) / 100) := by
  have h := Real.lt_log_one_add_of_pos (x := (1 : ℝ) / 100) (by norm_num)
  norm_num at h
  exact (by norm_num : (1 : ℝ) / 200 < 2 / 201).trans h

/-- A rational version of the final calibration: it suffices to make the
tensorized exponent at most `1/200`. -/
-- keep: audit endpoint translating the tensor budget into the advertised chi-square constant
lemma signedScoreProductMixture_one_add_chiSq_lt_101_div_100_of_budget
    (d J : ℕ) (pi0 pi1 : Measure (Fin 4 → ℝ)) (C rho : ℝ)
    [IsProbabilityMeasure (signedScoreMixtureLaw pi0)]
    [IsProbabilityMeasure (signedScoreMixtureLaw pi1)]
    (hac : signedScoreMixtureLaw pi0 ≪ signedScoreMixtureLaw pi1)
    (hint : Integrable (fun z =>
      (((signedScoreMixtureLaw pi0).rnDeriv (signedScoreMixtureLaw pi1) z).toReal - 1) ^ 2)
      (signedScoreMixtureLaw pi1))
    (hcell : Causalean.Stat.chiSqDiv (signedScoreMixtureLaw pi0)
      (signedScoreMixtureLaw pi1) ≤
        C * rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J)
    (hbudget : (d : ℝ) *
      (C * rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J) ≤ 1 / 200) :
    1 + Causalean.Stat.chiSqDiv
        (signedScoreProductMixtureLaw d pi0)
        (signedScoreProductMixtureLaw d pi1) < (101 : ℝ) / 100 := by
  apply signedScoreProductMixture_one_add_chiSq_lt_101_div_100
    d J pi0 pi1 C rho hac hint hcell
  exact hbudget.trans_lt one_div_200_lt_log_101_div_100

/-- The calibrated product chi-square bound implies the product total
variation bound used immediately after roadmap equation (68). -/
lemma signedScoreProductMixture_tv_lt_one_quarter
    (d J : ℕ) (pi0 pi1 : Measure (Fin 4 → ℝ)) (C rho : ℝ)
    [IsProbabilityMeasure (signedScoreMixtureLaw pi0)]
    [IsProbabilityMeasure (signedScoreMixtureLaw pi1)]
    (hac : signedScoreMixtureLaw pi0 ≪ signedScoreMixtureLaw pi1)
    (hint : Integrable (fun z =>
      (((signedScoreMixtureLaw pi0).rnDeriv (signedScoreMixtureLaw pi1) z).toReal - 1) ^ 2)
      (signedScoreMixtureLaw pi1))
    (hcell : Causalean.Stat.chiSqDiv (signedScoreMixtureLaw pi0)
      (signedScoreMixtureLaw pi1) ≤
        C * rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J)
    (hcal : (d : ℝ) *
      (C * rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J) <
        Real.log ((101 : ℝ) / 100)) :
    Causalean.Stat.tvDist
        (signedScoreProductMixtureLaw d pi0)
        (signedScoreProductMixtureLaw d pi1) < 1 / 4 := by
  let mu := signedScoreMixtureLaw pi0
  let nu := signedScoreMixtureLaw pi1
  letI : IsProbabilityMeasure (signedScoreProductMixtureLaw d pi0) := by
    unfold signedScoreProductMixtureLaw
    infer_instance
  letI : IsProbabilityMeasure (signedScoreProductMixtureLaw d pi1) := by
    unfold signedScoreProductMixtureLaw
    infer_instance
  have hacProd : signedScoreProductMixtureLaw d pi0 ≪
      signedScoreProductMixtureLaw d pi1 := by
    unfold signedScoreProductMixtureLaw
    exact Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous
      mu nu hac d
  have hintProd : Integrable (fun z =>
      (((signedScoreProductMixtureLaw d pi0).rnDeriv
        (signedScoreProductMixtureLaw d pi1) z).toReal - 1) ^ 2)
      (signedScoreProductMixtureLaw d pi1) := by
    exact Causalean.Stat.pi_iid_integrable_sq_dev mu nu hac hint d
  have hproduct := signedScoreProductMixture_one_add_chiSq_lt_101_div_100
    d J pi0 pi1 C rho hac hint hcell hcal
  have hchi : Causalean.Stat.chiSqDiv
      (signedScoreProductMixtureLaw d pi0)
      (signedScoreProductMixtureLaw d pi1) < (1 : ℝ) / 100 := by
    linarith
  have htv := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv
    (signedScoreProductMixtureLaw d pi0)
    (signedScoreProductMixtureLaw d pi1) hacProd hintProd
  calc
    Causalean.Stat.tvDist
        (signedScoreProductMixtureLaw d pi0)
        (signedScoreProductMixtureLaw d pi1) ≤
      (1 / 2 : ℝ) * Real.sqrt (Causalean.Stat.chiSqDiv
        (signedScoreProductMixtureLaw d pi0)
        (signedScoreProductMixtureLaw d pi1)) := htv
    _ < (1 / 2 : ℝ) * Real.sqrt ((1 : ℝ) / 100) := by
      apply mul_lt_mul_of_pos_left _ (by norm_num)
      exact Real.sqrt_lt_sqrt
        (Causalean.Stat.chiSqDiv_nonneg
          (μ := signedScoreProductMixtureLaw d pi0)
          (ν := signedScoreProductMixtureLaw d pi1)) hchi
    _ < 1 / 4 := by
      rw [show (1 : ℝ) / 100 = (1 / 10 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq_eq_abs]
      norm_num

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

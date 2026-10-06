module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Kernel_Part2
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Jackson moments sufficient for constant five

Reuse Causalean's unit-mass order-four kernel and exact mass. The existing public
64/K² bound loses too much when translated to rank. Instead the sine chord bound
gives the raw weighted estimate, whose normalization is at most 3π²/(2K²).
We retain the convenient weaker bound (2π/K)². Jensen at exponent γ/2 then
gives the unit-coordinate γ-moment at most (2/K)^γ. For K=(k+1)/2, the
rank factor is at most 4^γ ≤ 4 ≤ 5, including k=1.

Reference for conventions: Cambridge Part III Approximation Theory, Lecture 9
(2005), Definitions 9.3 and 9.5, Lemma 9.6, Theorem 9.8:
https://www.damtp.cam.ac.uk/user/na/PartIIIat/b09.pdf . The source supplies the
classical construction, not the explicit constant claimed here. All numerical
bounds below remain formal proof obligations.
-/

public section

open MeasureTheory
open scoped ENNReal
open Causalean.Mathlib.Analysis.JacksonApproximation
namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

/-- On the [principal period](hyp:ht), at a [positive kernel order](hyp:hK),
[the raw squared-angle weighted kernel is bounded by π² times the squared
Chebyshev sine quotient](goal).

Use `Real.mul_abs_le_abs_sin` on t/2 to get t² ≤ π² sin²(t/2), then
cancel two powers of the denominator and bound sin²(Kt/2) by one. At zero
denominator, the chord bound implies t=0. The corresponding helper in
Kernel_Part2 is private, so this public reusable statement needs its own proof.
-/
theorem weighted_jraw_le_chebyshev {K : ℕ} (hK : 0 < K) {t : ℝ}
    (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    t ^ 2 * jraw K t ≤ Real.pi ^ 2 *
      (Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval (Real.cos (t / 2)) ^ 2 := by
  have hhalf : |t / 2| ≤ Real.pi / 2 := by
    rw [abs_div]
    norm_num
    exact div_le_div_of_nonneg_right (abs_le.mpr ht) (by norm_num)
  have hchord := Real.mul_abs_le_abs_sin hhalf
  have habs : |t| ≤ Real.pi * |Real.sin (t / 2)| := by
    have hpi := Real.pi_pos
    rw [abs_div] at hchord
    norm_num at hchord
    field_simp at hchord
    nlinarith
  have ht2 : t ^ 2 ≤ Real.pi ^ 2 * Real.sin (t / 2) ^ 2 := by
    have hs := mul_self_le_mul_self (abs_nonneg t) habs
    simpa [← pow_two, mul_pow, sq_abs] using hs
  let u := (Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval (Real.cos (t / 2))
  have hu : u * Real.sin (t / 2) = Real.sin ((K : ℝ) * t / 2) := by
    have hc : (((K - 1 : ℕ) : ℤ) : ℝ) + 1 = (K : ℝ) := by
      exact_mod_cast (show K - 1 + 1 = K by omega)
    have hu := Polynomial.Chebyshev.U_real_cos (t / 2) ((K - 1 : ℕ) : ℤ)
    rw [hc] at hu
    simpa [u, mul_div_assoc] using hu
  have hs2 : Real.sin ((K : ℝ) * t / 2) ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_sin ((K : ℝ) * t / 2),
      Real.sin_le_one ((K : ℝ) * t / 2)]
  have hbase : t ^ 2 * u ^ 2 ≤ Real.pi ^ 2 := by
    calc
      _ ≤ (Real.pi ^ 2 * Real.sin (t / 2) ^ 2) * u ^ 2 :=
        mul_le_mul_of_nonneg_right ht2 (sq_nonneg u)
      _ = Real.pi ^ 2 * Real.sin ((K : ℝ) * t / 2) ^ 2 := by
        rw [← hu]; ring
      _ ≤ Real.pi ^ 2 := by nlinarith [sq_nonneg Real.pi]
  rw [jraw_eq_chebyshev K hK t]
  change t ^ 2 * u ^ 4 ≤ Real.pi ^ 2 * u ^ 2
  calc
    _ = (t ^ 2 * u ^ 2) * u ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbase (sq_nonneg u)

/-- At a [positive order](hyp:hK), [the squared Chebyshev sine quotient has
period integral 2π times that order](goal).

Expand with `cheb_U_sq_eval`; the nonconstant cosine integrals vanish by
`integral_cos_nat`. Both facts already exist publicly in Kernel_Part1.
-/
theorem integral_chebyshev_sq {K : ℕ} (hK : 0 < K) :
    (∫ t in Set.Icc (-Real.pi) Real.pi,
      (Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval (Real.cos (t / 2)) ^ 2) =
      2 * Real.pi * (K : ℝ) := by
  have hfun : (fun t : ℝ =>
      (Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval
        (Real.cos (t / 2)) ^ 2) = fun t =>
      (K : ℝ) + 2 * ∑ j ∈ Finset.range (K - 1),
        ((K - 1 : ℕ) - j : ℝ) * Real.cos (((j + 1 : ℕ) : ℝ) * t) := by
    funext t
    rw [cheb_U_sq_eval (K - 1) t]
    congr 2
    norm_cast
    omega
  rw [hfun]
  have hiConst : IntegrableOn (fun _t : ℝ => (K : ℝ))
      (Set.Icc (-Real.pi) Real.pi) :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have hiSum : IntegrableOn (fun t : ℝ =>
      2 * ∑ j ∈ Finset.range (K - 1),
        ((K - 1 : ℕ) - j : ℝ) * Real.cos (((j + 1 : ℕ) : ℝ) * t))
      (Set.Icc (-Real.pi) Real.pi) := by
    exact (show Continuous (fun t : ℝ =>
      2 * ∑ j ∈ Finset.range (K - 1),
        ((K - 1 : ℕ) - j : ℝ) * Real.cos (((j + 1 : ℕ) : ℝ) * t)) by
          fun_prop).continuousOn.integrableOn_compact isCompact_Icc
  rw [MeasureTheory.integral_add hiConst hiSum, MeasureTheory.integral_const_mul]
  have hsum : (∫ t in Set.Icc (-Real.pi) Real.pi,
      ∑ j ∈ Finset.range (K - 1),
        ((K - 1 : ℕ) - j : ℝ) * Real.cos (((j + 1 : ℕ) : ℝ) * t)) = 0 := by
    calc
      _ = ∑ j ∈ Finset.range (K - 1), ∫ t in Set.Icc (-Real.pi) Real.pi,
          ((K - 1 : ℕ) - j : ℝ) * Real.cos (((j + 1 : ℕ) : ℝ) * t) :=
        MeasureTheory.integral_finsetSum (Finset.range (K - 1)) (by
          intro j hj
          exact (show Continuous (fun t : ℝ =>
            ((K - 1 : ℕ) - j : ℝ) *
              Real.cos (((j + 1 : ℕ) : ℝ) * t)) by fun_prop).continuousOn
                |>.integrableOn_compact isCompact_Icc)
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [MeasureTheory.integral_const_mul, integral_cos_nat (j + 1) (by omega)]
        ring
  rw [hsum]
  rw [integral_const_Icc]
  ring

/-- At a [positive kernel order](hyp:hK), [the Jackson squared-angle moment
is at most the square of 2π divided by the order](goal).

Integrate `weighted_jraw_le_chebyshev`, use `integral_chebyshev_sq`, and
divide by `jrawMass_lower`. This leaves room in the final constant without
requiring a sharp kernel moment or a numerical approximation to π.
-/
theorem jackson_second_moment_scaled {K : ℕ} (hK : 0 < K) :
    (∫ t in Set.Icc (-Real.pi) Real.pi, t ^ 2 * jackson K t) ≤
      (2 * Real.pi / (K : ℝ)) ^ 2 := by
  have hiLeft : IntegrableOn (fun t => t ^ 2 * jraw K t)
      (Set.Icc (-Real.pi) Real.pi) :=
    (show Continuous (fun t => t ^ 2 * jraw K t) by fun_prop).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hiRight : IntegrableOn (fun t => Real.pi ^ 2 *
      (Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval
        (Real.cos (t / 2)) ^ 2) (Set.Icc (-Real.pi) Real.pi) :=
    (show Continuous (fun t => Real.pi ^ 2 *
      (Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval
        (Real.cos (t / 2)) ^ 2) by fun_prop).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hraw : (∫ t in Set.Icc (-Real.pi) Real.pi, t ^ 2 * jraw K t) ≤
      2 * Real.pi ^ 3 * (K : ℝ) := by
    calc
      _ ≤ ∫ t in Set.Icc (-Real.pi) Real.pi, Real.pi ^ 2 *
          (Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval
            (Real.cos (t / 2)) ^ 2 :=
        setIntegral_mono_on hiLeft hiRight measurableSet_Icc
          (fun t ht => weighted_jraw_le_chebyshev hK ht)
      _ = _ := by
        rw [integral_const_mul, integral_chebyshev_sq hK]
        ring
  have hmass := jrawMass_lower K hK
  have hmasspos := jrawMass_pos K hK
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  rw [show (fun t => t ^ 2 * jackson K t) =
      (fun t => (t ^ 2 * jraw K t) / jrawMass K) by
        funext t; simp only [jackson]; ring, integral_div]
  apply (div_le_iff₀ hmasspos).2
  calc
    _ ≤ 2 * Real.pi ^ 3 * (K : ℝ) := hraw
    _ ≤ (2 * Real.pi / (K : ℝ)) ^ 2 *
        ((4 * Real.pi / 3) * (K : ℝ) ^ 3) := by
      field_simp
      nlinarith [Real.pi_pos]
    _ ≤ (2 * Real.pi / (K : ℝ)) ^ 2 * jrawMass K :=
      mul_le_mul_of_nonneg_left hmass (sq_nonneg _)

/-- A [positive order](hyp:hK) and an [exponent between zero and one](hyp:hγ,hγ1)
give [a Jackson Hölder moment in unit coordinates at most (2/K)^γ](goal).

Equip the principal period with density `jackson K`; positivity and unit mass
come from Kernel_Part2. Jensen for the concave power γ/2 of (t/π)² reduces
this to `jackson_second_moment_scaled`. Prove the density/norm bridges explicitly.
-/
theorem jackson_holder_moment {K : ℕ} {γ : ℝ}
    (hK : 0 < K) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (∫ t in Set.Icc (-Real.pi) Real.pi, (|t| / Real.pi) ^ γ * jackson K t) ≤
      (2 / (K : ℝ)) ^ γ := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (-Real.pi) Real.pi)
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (jackson K t)
  let ν : Measure ℝ := μ.withDensity w
  have hw : Measurable w := (measurable_jackson K).ennreal_ofReal
  have hwtop : ∀ᵐ t ∂μ, w t < ∞ := Filter.Eventually.of_forall
    (fun t => ENNReal.ofReal_lt_top)
  have hnonneg : ∀ t, 0 ≤ jackson K t := jackson_nonneg K hK
  have hbridge (f : ℝ → ℝ) : (∫ t, f t ∂ν) =
      ∫ t in Set.Icc (-Real.pi) Real.pi, f t * jackson K t := by
    rw [integral_withDensity_eq_integral_toReal_smul hw hwtop]
    simp only [w, ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul, mul_comm]
    rfl
  have hν : ν Set.univ = 1 := by
    change μ.withDensity w Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    change (∫⁻ t, ENNReal.ofReal (jackson K t) ∂μ) = 1
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_jackson K)
      (Filter.Eventually.of_forall hnonneg), jackson_integral_eq_one K hK]
    norm_num
  let : IsProbabilityMeasure ν := ⟨hν⟩
  let f : ℝ → ℝ := fun t => (|t| / Real.pi) ^ 2
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hp : 0 < γ / 2 := by linarith
  have hpow : Continuous (fun t => f t ^ (γ / 2)) :=
    hf.rpow_const (fun t => Or.inr hp.le)
  have hfi : Integrable f ν := by
    apply (integrable_withDensity_iff_integrable_smul' hw hwtop).2
    simpa only [w, ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul, μ,
      IntegrableOn] using
      (show Continuous (fun t => jackson K t * f t) by fun_prop).continuousOn
        |>.integrableOn_compact isCompact_Icc
  have hgi : Integrable ((fun x : ℝ => x ^ (γ / 2)) ∘ f) ν := by
    apply (integrable_withDensity_iff_integrable_smul' hw hwtop).2
    simpa only [w, ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul,
      Function.comp_def, μ, IntegrableOn] using
      (show Continuous (fun t => jackson K t * f t ^ (γ / 2)) by fun_prop).continuousOn
        |>.integrableOn_compact isCompact_Icc
  have hj := (Real.concaveOn_rpow hp.le (by linarith : γ / 2 ≤ 1)).le_map_integral
    (Real.continuous_rpow_const hp.le).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun t => sq_nonneg (|t| / Real.pi))) hfi hgi
  have hmoment : (∫ t, f t ∂ν) ≤ (2 / (K : ℝ)) ^ 2 := by
    rw [hbridge]
    have heq : (fun t => f t * jackson K t) =
        (fun t => (t ^ 2 * jackson K t) / Real.pi ^ 2) := by
      funext t
      dsimp [f]
      rw [div_pow, sq_abs]
      ring
    rw [heq, integral_div]
    apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).2
    convert jackson_second_moment_scaled hK using 1 <;> first | rfl | ring
  have hpower (x : ℝ) (hx : 0 ≤ x) : (x ^ 2) ^ (γ / 2) = x ^ γ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    congr 1
    ring
  calc
    _ = ∫ t, f t ^ (γ / 2) ∂ν := by
      rw [hbridge]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [f]
        rw [hpower _ (div_nonneg (abs_nonneg t) Real.pi_pos.le)])
    _ ≤ (∫ t, f t ∂ν) ^ (γ / 2) := hj
    _ ≤ ((2 / (K : ℝ)) ^ 2) ^ (γ / 2) :=
      Real.rpow_le_rpow (integral_nonneg (fun t => sq_nonneg _)) hmoment hp.le
    _ = _ := hpower _ (by positivity)

/-- For a [positive rank](hyp:hk), its matched Jackson order is
[positive and has degree strictly below rank](goal). -/
theorem matchedOrder_bounds {k : ℕ} (hk : 1 ≤ k) :
    0 < (k + 1) / 2 ∧ 2 * ((k + 1) / 2 - 1) < k := by
  omega

/-- For a [positive rank](hyp:hk) and an [exponent between zero and one](hyp:hγ,hγ1),
[the matched-order moment bound is at most five times rank to minus that exponent](goal).

Show k ≤ 2*((k+1)/2), hence 2/K ≤ 4/k. Then use 4^γ ≤ 4 ≤ 5.
This arithmetic includes rank one and does not introduce an asymptotic threshold.
-/
theorem matchedOrder_constant_five {k : ℕ} {γ : ℝ}
    (hk : 1 ≤ k) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (2 / (((k + 1) / 2 : ℕ) : ℝ)) ^ γ ≤ 5 * (k : ℝ) ^ (-γ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hKR : (0 : ℝ) < ((k + 1) / 2 : ℕ) := by
    exact_mod_cast (matchedOrder_bounds hk).1
  have hrank : (k : ℝ) ≤ 2 * (((k + 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : k ≤ 2 * ((k + 1) / 2))
  have hratio : 2 / (((k + 1) / 2 : ℕ) : ℝ) ≤ 4 / (k : ℝ) := by
    apply (div_le_div_iff₀ hKR hkR).2
    linarith
  have hfour : (4 : ℝ) ^ γ ≤ 4 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hγ1
  calc
    _ ≤ (4 / (k : ℝ)) ^ γ := Real.rpow_le_rpow (by positivity) hratio hγ.le
    _ = (4 : ℝ) ^ γ * (k : ℝ) ^ (-γ) := by
      rw [Real.div_rpow (by norm_num) hkR.le, Real.rpow_neg hkR.le, div_eq_mul_inv]
    _ ≤ 5 * (k : ℝ) ^ (-γ) :=
      mul_le_mul_of_nonneg_right (hfour.trans (by norm_num))
        (Real.rpow_nonneg hkR.le _)

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection


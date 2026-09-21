module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Szego
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.NormNum.Parity
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Kernel_Part1

/-!
# Normalization and moment bounds for the order-four Jackson kernel

Building on `Kernel_Part1`, this module computes the raw kernel's exact mass, proves that the
normalized kernel has unit integral at positive order, derives explicit first- and second-moment
bounds, and bounds its trigonometric degree.
-/

public section

namespace Causalean.Mathlib.Analysis.JacksonApproximation

open MeasureTheory Real
open scoped BigOperators
/-- For [integer order K](hyp:K) that is [strictly positive](hyp:hK), [the raw Jackson mass equals
two π thirds times K times two K squared plus one](goal).
-/
theorem jrawMass_eq (K : ℕ) (hK : 0 < K) :
    jrawMass K = (2 * Real.pi / 3) * (K : ℝ) * (2 * (K : ℝ) ^ 2 + 1) := by
  have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hK))]
    norm_num
  have hfun : jraw K = fun t =>
      ((K : ℝ) + ∑ j ∈ Finset.range (K - 1),
        (2 * (((K - 1 : ℕ) : ℝ) - (j : ℝ))) *
          Real.cos (((j + 1 : ℕ) : ℝ) * t)) ^ 2 := by
    funext t
    rw [jraw_eq_chebyshev K hK t]
    rw [show
      (Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval (Real.cos (t / 2)) ^ 4 =
        ((Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval
          (Real.cos (t / 2)) ^ 2) ^ 2 by ring]
    congr 1
    rw [cheb_U_sq_eval (K - 1) t]
    have hsucc : K - 1 + 1 = K := by omega
    rw [hcast]
    rw [Finset.mul_sum]
    have hlead : (K : ℝ) - 1 + 1 = (K : ℝ) := by ring
    rw [hlead]
    apply congrArg ((K : ℝ) + ·)
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [jrawMass, hfun, integral_sq_cos_sum]
  have hsum := sum_range_sub_sq (K - 1)
  have hcoeff :
      (∑ j ∈ Finset.range (K - 1),
          (2 * (((K - 1 : ℕ) : ℝ) - (j : ℝ))) ^ 2) =
        4 * (((K - 1 : ℕ) : ℝ) * ((K - 1 : ℕ) + 1) *
          (2 * (K - 1 : ℕ) + 1) / 6) := by
    calc
      (∑ j ∈ Finset.range (K - 1),
          (2 * (((K - 1 : ℕ) : ℝ) - (j : ℝ))) ^ 2) =
          4 * ∑ j ∈ Finset.range (K - 1),
            (((K - 1 : ℕ) : ℝ) - (j : ℝ)) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [hsum]
  rw [hcoeff, hcast]
  push_cast
  ring

/-- For [integer order K](hyp:K) that is [strictly positive](hyp:hK), [the raw Jackson mass is at
least four π thirds times K cubed](goal).
-/
theorem jrawMass_lower (K : ℕ) (hK : 0 < K) :
    (4 * Real.pi / 3) * (K : ℝ) ^ 3 ≤ jrawMass K := by
  rw [jrawMass_eq K hK]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  nlinarith [sq_nonneg ((K : ℝ) - 1)]

/-- For [integer order K](hyp:K) that is [strictly positive](hyp:hK), [the raw Jackson mass is at
most two π times K cubed](goal).
-/
theorem jrawMass_upper (K : ℕ) (hK : 0 < K) :
    jrawMass K ≤ 2 * Real.pi * (K : ℝ) ^ 3 := by
  rw [jrawMass_eq K hK]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hsquare : 2 * (K : ℝ) ^ 2 + 1 ≤ 3 * (K : ℝ) ^ 2 := by nlinarith
  calc
    (2 * Real.pi / 3) * (K : ℝ) * (2 * (K : ℝ) ^ 2 + 1) ≤
        (2 * Real.pi / 3) * (K : ℝ) * (3 * (K : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = 2 * Real.pi * (K : ℝ) ^ 3 := by ring

/-- For [integer order K](hyp:K) that is [strictly positive](hyp:hK), [the raw Jackson mass is
strictly positive](goal).
-/
theorem jrawMass_pos (K : ℕ) (hK : 0 < K) : 0 < jrawMass K := by
  have hl := jrawMass_lower K hK
  have hpi : 0 < Real.pi := Real.pi_pos
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  exact lt_of_lt_of_le (by positivity) hl

/-- For [integer order K](hyp:K), [the normalized Jackson kernel is continuous on the real
line](goal).
-/
@[fun_prop]
theorem continuous_jackson (K : ℕ) : Continuous (jackson K) := by
  unfold jackson
  fun_prop

/-- For [integer order K](hyp:K), [the normalized Jackson kernel is Borel measurable](goal).
-/
@[measurability, fun_prop]
theorem measurable_jackson (K : ℕ) : Measurable (jackson K) := by
  exact (continuous_jackson K).measurable

/-- For [integer order K](hyp:K), [the normalized Jackson kernel is integrable over the standard
period](goal).
-/
theorem integrableOn_jackson (K : ℕ) :
    IntegrableOn (jackson K) (Set.Icc (-Real.pi) Real.pi) := by
  exact (continuous_jackson K).continuousOn.integrableOn_compact isCompact_Icc

/-- At [integer order K](hyp:K) that is [strictly positive](hyp:hK) and [real argument t](hyp:t),
[the normalized Jackson kernel is nonnegative](goal).
-/
theorem jackson_nonneg (K : ℕ) (hK : 0 < K) (t : ℝ) : 0 ≤ jackson K t := by
  exact div_nonneg (jraw_nonneg K t) (jrawMass_pos K hK).le

/-- For [integer order K](hyp:K), [the normalized Jackson kernel is symmetric about zero](goal).
-/
theorem jackson_even (K : ℕ) : Function.Even (jackson K) := by
  intro t
  simp only [jackson, jraw_even K t]

/-- For [integer order K](hyp:K) that is [strictly positive](hyp:hK), [the normalized Jackson
kernel has unit mass over the standard period](goal).
-/
theorem jackson_integral_eq_one (K : ℕ) (hK : 0 < K) :
    (∫ t in Set.Icc (-Real.pi) Real.pi, jackson K t) = 1 := by
  rw [show jackson K = fun t => jraw K t / jrawMass K by rfl,
    MeasureTheory.integral_div, ← jrawMass]
  exact div_self (jrawMass_pos K hK).ne'

private lemma sq_le_pi_sq_mul_sin_sq {t : ℝ}
    (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    t ^ 2 ≤ Real.pi ^ 2 * Real.sin (t / 2) ^ 2 := by
  have habst : |t| ≤ Real.pi := by
    rw [abs_le]
    exact ht
  have hhalf : |t / 2| ≤ Real.pi / 2 := by
    rw [abs_div]
    norm_num
    exact div_le_div_of_nonneg_right habst (by norm_num)
  have hs := Real.mul_abs_le_abs_sin hhalf
  have hpi := Real.pi_pos
  have habs : |t| ≤ Real.pi * |Real.sin (t / 2)| := by
    calc
      |t| = Real.pi * (2 / Real.pi * |t / 2|) := by
        rw [abs_div]
        field_simp
        <;> ring
      _ ≤ Real.pi * |Real.sin (t / 2)| :=
        mul_le_mul_of_nonneg_left hs hpi.le
  have hsquare := mul_self_le_mul_self (abs_nonneg t) habs
  calc
    t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    _ ≤ (Real.pi * |Real.sin (t / 2)|) ^ 2 := by
      simpa [pow_two] using hsquare
    _ = Real.pi ^ 2 * Real.sin (t / 2) ^ 2 := by
      rw [mul_pow, sq_abs]

private lemma weighted_jraw_le (K : ℕ) (hK : 0 < K) {t : ℝ}
    (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    t ^ 2 * jraw K t ≤ Real.pi ^ 2 *
      (Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval
        (Real.cos (t / 2)) ^ 2 := by
  have ht2 := sq_le_pi_sq_mul_sin_sq ht
  by_cases hs : Real.sin (t / 2) = 0
  · have ht0 : t = 0 := by
      rw [hs, zero_pow] at ht2
      · nlinarith [sq_nonneg t]
      · norm_num
    subst t
    simp
    positivity
  · let u := (Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval
        (Real.cos (t / 2))
    let s := Real.sin ((K : ℝ) * t / 2)
    let d := Real.sin (t / 2)
    have hu : u = s / d := by
      apply (eq_div_iff hs).2
      dsimp [u, s, d]
      have hcheb := Polynomial.Chebyshev.U_real_cos (t / 2) ((K - 1 : ℕ) : ℤ)
      have harg : (((((K - 1 : ℕ) : ℤ) : ℝ) + 1) * (t / 2)) =
          (K : ℝ) * t / 2 := by
        have hc : (((((K - 1 : ℕ) : ℤ) : ℝ) + 1)) = (K : ℝ) := by
          exact_mod_cast (show K - 1 + 1 = K by omega)
        rw [hc]
        ring
      exact hcheb.trans (congrArg Real.sin harg)
    have hs2 : s ^ 2 ≤ 1 := by
      dsimp [s]
      nlinarith [Real.neg_one_le_sin ((K : ℝ) * t / 2),
        Real.sin_le_one ((K : ℝ) * t / 2)]
    have hdpos : 0 < d ^ 2 := by
      exact sq_pos_of_ne_zero hs
    have hbase : t ^ 2 * (s / d) ^ 2 ≤ Real.pi ^ 2 * s ^ 2 := by
      rw [div_pow]
      calc
        t ^ 2 * (s ^ 2 / d ^ 2) = (t ^ 2 * s ^ 2) / d ^ 2 := by ring
        _ ≤ Real.pi ^ 2 * s ^ 2 := by
          apply (div_le_iff₀ hdpos).2
          have hmul := mul_le_mul_of_nonneg_right ht2 (sq_nonneg s)
          dsimp [d] at hmul ⊢
          nlinarith
    rw [jraw_eq_of_sin_ne_zero K hs, ← hu]
    calc
      t ^ 2 * u ^ 4 = (t ^ 2 * (s / d) ^ 2) * (s / d) ^ 2 := by
        rw [hu]
        ring
      _ ≤ (Real.pi ^ 2 * s ^ 2) * (s / d) ^ 2 :=
        mul_le_mul_of_nonneg_right hbase (sq_nonneg (s / d))
      _ ≤ Real.pi ^ 2 * (s / d) ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (by simpa using mul_le_mul_of_nonneg_left hs2 (sq_nonneg Real.pi))
          (sq_nonneg (s / d))
      _ = Real.pi ^ 2 * u ^ 2 := by rw [hu]

private lemma integral_cheb_U_sq (K : ℕ) (hK : 0 < K) :
    (∫ t in Set.Icc (-Real.pi) Real.pi,
      (Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval
        (Real.cos (t / 2)) ^ 2) = 2 * Real.pi * (K : ℝ) := by
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

private lemma jackson_second_moment_aux (K : ℕ) (hK : 0 < K) :
    (∫ t in Set.Icc (-Real.pi) Real.pi, t ^ 2 * jackson K t) ≤
      24 / (K : ℝ) ^ 2 := by
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
      (∫ t in Set.Icc (-Real.pi) Real.pi, t ^ 2 * jraw K t) ≤
          ∫ t in Set.Icc (-Real.pi) Real.pi, Real.pi ^ 2 *
            (Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval
              (Real.cos (t / 2)) ^ 2 := by
        exact MeasureTheory.setIntegral_mono_on hiLeft hiRight measurableSet_Icc (fun t ht =>
          weighted_jraw_le K hK ht)
      _ = 2 * Real.pi ^ 3 * (K : ℝ) := by
        rw [MeasureTheory.integral_const_mul, integral_cheb_U_sq K hK]
        ring
  have hmass := jrawMass_lower K hK
  have hmasspos := jrawMass_pos K hK
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_le_four]
  rw [show (fun t => t ^ 2 * jackson K t) =
      fun t => (t ^ 2 * jraw K t) / jrawMass K by
        funext t; simp [jackson]; ring,
    MeasureTheory.integral_div]
  apply (div_le_iff₀ hmasspos).2
  calc
    (∫ t in Set.Icc (-Real.pi) Real.pi, t ^ 2 * jraw K t) ≤
        2 * Real.pi ^ 3 * (K : ℝ) := hraw
    _ ≤ (24 / (K : ℝ) ^ 2) *
        ((4 * Real.pi / 3) * (K : ℝ) ^ 3) := by
      field_simp
      nlinarith [Real.pi_pos, hpi2]
    _ ≤ (24 / (K : ℝ) ^ 2) * jrawMass K := by
      exact mul_le_mul_of_nonneg_left hmass (by positivity)

/-- For [integer order K](hyp:K) that is [strictly positive](hyp:hK), [the normalized absolute
first moment is at most thirty-two divided by K](goal).
-/
theorem jackson_first_moment (K : ℕ) (hK : 0 < K) :
    (∫ t in Set.Icc (-Real.pi) Real.pi, |t| * jackson K t) ≤ 32 / (K : ℝ) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hpoint (t : ℝ) : |t| ≤ (K : ℝ) / 4 * t ^ 2 + 1 / (K : ℝ) := by
    have hs := sq_nonneg ((K : ℝ) * |t| - 2)
    have ht2 : |t| ^ 2 = t ^ 2 := sq_abs t
    field_simp
    nlinarith
  have hiLeft : IntegrableOn (fun t => |t| * jackson K t)
      (Set.Icc (-Real.pi) Real.pi) :=
    (show Continuous (fun t => |t| * jackson K t) by fun_prop).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hiRight : IntegrableOn (fun t =>
      ((K : ℝ) / 4 * t ^ 2 + 1 / (K : ℝ)) * jackson K t)
      (Set.Icc (-Real.pi) Real.pi) :=
    (show Continuous (fun t =>
      ((K : ℝ) / 4 * t ^ 2 + 1 / (K : ℝ)) * jackson K t) by fun_prop).continuousOn
      |>.integrableOn_compact isCompact_Icc
  calc
    (∫ t in Set.Icc (-Real.pi) Real.pi, |t| * jackson K t) ≤
        ∫ t in Set.Icc (-Real.pi) Real.pi,
          ((K : ℝ) / 4 * t ^ 2 + 1 / (K : ℝ)) * jackson K t := by
      exact MeasureTheory.setIntegral_mono_on hiLeft hiRight measurableSet_Icc (fun t ht =>
        mul_le_mul_of_nonneg_right (hpoint t) (jackson_nonneg K hK t))
    _ = (K : ℝ) / 4 *
          (∫ t in Set.Icc (-Real.pi) Real.pi, t ^ 2 * jackson K t) +
        (1 / (K : ℝ)) *
          (∫ t in Set.Icc (-Real.pi) Real.pi, jackson K t) := by
      have hi₁ : IntegrableOn (fun t => (K : ℝ) / 4 * (t ^ 2 * jackson K t))
          (Set.Icc (-Real.pi) Real.pi) :=
        (show Continuous (fun t => (K : ℝ) / 4 * (t ^ 2 * jackson K t)) by
          fun_prop).continuousOn.integrableOn_compact isCompact_Icc
      have hi₂ : IntegrableOn (fun t => (1 / (K : ℝ)) * jackson K t)
          (Set.Icc (-Real.pi) Real.pi) :=
        (show Continuous (fun t => (1 / (K : ℝ)) * jackson K t) by
          fun_prop).continuousOn.integrableOn_compact isCompact_Icc
      rw [show (fun t => ((K : ℝ) / 4 * t ^ 2 + 1 / (K : ℝ)) * jackson K t) =
          fun t => (K : ℝ) / 4 * (t ^ 2 * jackson K t) +
            (1 / (K : ℝ)) * jackson K t by funext t; ring]
      rw [MeasureTheory.integral_add hi₁ hi₂,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ (K : ℝ) / 4 * (24 / (K : ℝ) ^ 2) +
        (1 / (K : ℝ)) * 1 := by
      gcongr
      · exact jackson_second_moment_aux K hK
      · exact (jackson_integral_eq_one K hK).le
    _ ≤ 32 / (K : ℝ) := by
      field_simp
      nlinarith

/-- For [integer order K](hyp:K) that is [strictly positive](hyp:hK), [the normalized second
moment is at most sixty-four divided by K squared](goal).
-/
theorem jackson_second_moment (K : ℕ) (hK : 0 < K) :
    (∫ t in Set.Icc (-Real.pi) Real.pi, t ^ 2 * jackson K t) ≤
      64 / (K : ℝ) ^ 2 := by
  refine (jackson_second_moment_aux K hK).trans ?_
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  field_simp
  nlinarith

/-- For [integer order K](hyp:K) that is [strictly positive](hyp:hK), [the raw Jackson kernel is a
real trigonometric polynomial with frequency at most twice the predecessor of K](goal).
-/
theorem jraw_isTrigPolyLE (K : ℕ) (hK : 0 < K) :
    Causalean.Mathlib.Analysis.BernsteinSzegoTrig.IsTrigPolyLE (2 * (K - 1)) (jraw K) := by
  let U : Polynomial ℝ := Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)
  let p : Polynomial ℝ := U ^ 4
  have hpneg : ∀ x : ℝ, p.eval (-x) = p.eval x := by
    intro x
    simp only [p, Polynomial.eval_pow, U]
    rw [Polynomial.Chebyshev.U_eval_neg]
    rw [mul_pow]
    have hsign :
        (((((K - 1 : ℕ) : ℤ)).negOnePow : ℤ) : ℝ) ^ 4 = 1 := by
      have habs :
          |(((((K - 1 : ℕ) : ℤ)).negOnePow : ℤ) : ℝ)| = 1 := by
        norm_cast
        exact Int.abs_negOnePow _
      calc
        (((((K - 1 : ℕ) : ℤ)).negOnePow : ℤ) : ℝ) ^ 4 =
            |(((((K - 1 : ℕ) : ℤ)).negOnePow : ℤ) : ℝ) ^ 4| := by
          rw [abs_of_nonneg (by positivity)]
        _ = |(((((K - 1 : ℕ) : ℤ)).negOnePow : ℤ) : ℝ)| ^ 4 := by
          exact abs_pow _ _
        _ = 1 := by rw [habs]; norm_num
    rw [hsign, one_mul]
  obtain ⟨q, hqdeg, hpq⟩ := exists_comp_sq_of_eval_neg_eq p hpneg
  let A : Polynomial ℝ := Polynomial.C (1 / 2 : ℝ) * (Polynomial.X + 1)
  let R : Polynomial ℝ := q.comp A
  have hAdeg : A.natDegree ≤ 1 := by
    dsimp [A]
    compute_degree
  have hpdeg : p.natDegree = 4 * (K - 1) := by
    dsimp [p, U]
    rw [Polynomial.natDegree_pow, Polynomial.Chebyshev.natDegree_U_natCast]
  have hRdeg : R.natDegree ≤ 2 * (K - 1) := by
    calc
      R.natDegree ≤ q.natDegree * A.natDegree := Polynomial.natDegree_comp_le
      _ ≤ q.natDegree * 1 := Nat.mul_le_mul_left _ hAdeg
      _ = q.natDegree := Nat.mul_one _
      _ ≤ p.natDegree / 2 := hqdeg
      _ = 2 * (K - 1) := by rw [hpdeg]; omega
  apply (Causalean.Mathlib.Analysis.BernsteinSzegoTrig.cosComp_isTrigPolyLE
    R (2 * (K - 1)) hRdeg).congr
  intro t
  rw [jraw_eq_chebyshev K hK t]
  have hhalf : Real.cos (t / 2) ^ 2 = (Real.cos t + 1) / 2 := by
    have hcos := Real.cos_two_mul (t / 2)
    rw [show 2 * (t / 2) = t by ring] at hcos
    nlinarith
  calc
    (Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval (Real.cos (t / 2)) ^ 4 =
        p.eval (Real.cos (t / 2)) := by simp [p, U]
    _ = q.eval (Real.cos (t / 2) ^ 2) := by
      rw [hpq, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
    _ = q.eval ((Real.cos t + 1) / 2) := by rw [hhalf]
    _ = R.eval (Real.cos t) := by
      simp [R, A, Polynomial.eval_comp]
      congr 1
      ring

/-- For [integer order K](hyp:K) that is [strictly positive](hyp:hK), [the normalized Jackson
kernel is a real trigonometric polynomial with frequency at most twice the predecessor of
K](goal).
-/
theorem jackson_isTrigPolyLE (K : ℕ) (hK : 0 < K) :
    Causalean.Mathlib.Analysis.BernsteinSzegoTrig.IsTrigPolyLE
      (2 * (K - 1)) (jackson K) := by
  apply (Causalean.Mathlib.Analysis.BernsteinSzegoTrig.IsTrigPolyLE.const_mul
    (jrawMass K)⁻¹ (jraw_isTrigPolyLE K hK)).congr
  intro t
  simp [jackson, div_eq_mul_inv, mul_comm]

end Causalean.Mathlib.Analysis.JacksonApproximation

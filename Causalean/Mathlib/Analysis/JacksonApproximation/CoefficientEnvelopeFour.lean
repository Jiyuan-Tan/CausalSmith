import Causalean.Mathlib.Analysis.JacksonApproximation.TensorExtraction
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# A four-dimensional coefficient envelope for Jackson approximation

This module bounds the coefficient one-norm of the four-variable polynomial extracted from a
uniformly bounded tensor Jackson convolution, while retaining coordinate and total-degree control.
-/

namespace Causalean.Mathlib.Analysis.JacksonApproximation

open MeasureTheory Real
open scoped BigOperators

/-- [A finite dimension](hyp:d) and [a real multivariate polynomial](hyp:p) determine [its
coefficient one-norm](goal), the sum of the absolute values of all monomial coefficients.
-/
noncomputable def mvCoeffL1 {d : ℕ} (p : MvPolynomial (Fin d) ℝ) : ℝ :=
  ∑ m ∈ p.support, |p.coeff m|

private lemma integral_cos_mul_cos_four (m n : ℕ) :
    (∫ t in Set.Icc (-Real.pi) Real.pi,
      Real.cos ((m : ℝ) * t) * Real.cos ((n : ℝ) * t)) =
        if m = 0 ∧ n = 0 then 2 * Real.pi else if m = n then Real.pi else 0 := by
  have hpoint (t : ℝ) :
      Real.cos ((m : ℝ) * t) * Real.cos ((n : ℝ) * t) =
        (Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) +
          Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * t)) / 2 := by
    rw [show ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) =
        (m : ℝ) * t - (n : ℝ) * t by push_cast; ring,
      show ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * t) =
        (m : ℝ) * t + (n : ℝ) * t by push_cast; ring,
      Real.cos_sub, Real.cos_add]
    ring
  simp_rw [hpoint]
  rw [MeasureTheory.integral_div]
  rw [MeasureTheory.integral_add
    ((show Continuous (fun t : ℝ => Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t)) by
      fun_prop).continuousOn.integrableOn_compact isCompact_Icc)
    ((show Continuous (fun t : ℝ => Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * t)) by
      fun_prop).continuousOn.integrableOn_compact isCompact_Icc)]
  have hcos (k : ℤ) (hk : k ≠ 0) :
      (∫ t in Set.Icc (-Real.pi) Real.pi, Real.cos ((k : ℝ) * t)) = 0 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (a := -Real.pi) (b := Real.pi)
        (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    rw [intervalIntegral.integral_comp_mul_left Real.cos hk0, integral_cos]
    simp
  have hcos_nat (k : ℕ) (hk : k ≠ 0) :
      (∫ t in Set.Icc (-Real.pi) Real.pi, Real.cos ((k : ℝ) * t)) = 0 := by
    convert hcos (k : ℤ) (by exact_mod_cast hk) using 1
    all_goals norm_num
  by_cases h00 : m = 0 ∧ n = 0
  · rcases h00 with ⟨rfl, rfl⟩
    simp [Real.pi_pos.le]
    ring
  · simp only [h00, if_false]
    by_cases hmn : m = n
    · subst n
      have hm0 : m ≠ 0 := by aesop
      simp only [sub_self, Int.cast_zero, zero_mul, Real.cos_zero]
      rw [show (∫ _t in Set.Icc (-Real.pi) Real.pi, (1 : ℝ)) = 2 * Real.pi by
        simp [Real.pi_pos.le]; ring,
        hcos ((m : ℤ) + (m : ℤ)) (by omega)]
      simp
    · simp only [hmn, if_false]
      rw [hcos ((m : ℤ) - (n : ℤ)) (by omega),
        hcos ((m : ℤ) + (n : ℤ)) (by omega)]
      norm_num

private lemma cosine_coeff_abs_le_four {n : ℕ} {q : ℝ → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ t, |q t| ≤ B) (a : ℕ → ℝ)
    (ha : ∀ t, q t = ∑ j ∈ Finset.range (n + 1),
      a j * Real.cos ((j : ℝ) * t)) {k : ℕ} (hk : k < n + 1) :
    |a k| ≤ 2 * B := by
  let c : ℝ → ℝ := fun t => Real.cos ((k : ℝ) * t)
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hint (j : ℕ) : IntegrableOn
      (fun t : ℝ => a j * Real.cos ((j : ℝ) * t) * c t)
      (Set.Icc (-Real.pi) Real.pi) := by
    exact (by fun_prop : Continuous
      (fun t : ℝ => a j * Real.cos ((j : ℝ) * t) * c t)).continuousOn
        |>.integrableOn_compact isCompact_Icc
  have heq :
      (∫ t in Set.Icc (-Real.pi) Real.pi, q t * c t) =
        a k * (if k = 0 then 2 * Real.pi else Real.pi) := by
    calc
      (∫ t in Set.Icc (-Real.pi) Real.pi, q t * c t) =
          ∫ t in Set.Icc (-Real.pi) Real.pi,
            ∑ j ∈ Finset.range (n + 1),
              a j * Real.cos ((j : ℝ) * t) * c t := by
            apply integral_congr_ae
            filter_upwards
            intro t
            rw [ha t, Finset.sum_mul]
      _ = ∑ j ∈ Finset.range (n + 1),
            ∫ t in Set.Icc (-Real.pi) Real.pi,
              a j * Real.cos ((j : ℝ) * t) * c t :=
          integral_finsetSum (Finset.range (n + 1)) (fun j _ => hint j)
      _ = ∑ j ∈ Finset.range (n + 1),
            a j * (if j = 0 ∧ k = 0 then 2 * Real.pi
              else if j = k then Real.pi else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          dsimp [c]
          rw [show (fun t : ℝ => a j * Real.cos ((j : ℝ) * t) *
              Real.cos ((k : ℝ) * t)) =
              fun t => a j * (Real.cos ((j : ℝ) * t) * Real.cos ((k : ℝ) * t)) by
                funext t; ring,
            MeasureTheory.integral_const_mul]
          exact congrArg (a j * ·) (integral_cos_mul_cos_four j k)
      _ = a k * (if k = 0 then 2 * Real.pi else Real.pi) := by
          rw [Finset.sum_eq_single k]
          · by_cases hk0 : k = 0 <;> simp [hk0]
          · intro j hj hjk
            by_cases hj0 : j = 0
            · have hk0 : k ≠ 0 := by aesop
              have h0k : 0 ≠ k := Ne.symm hk0
              simp [hj0, hk0, h0k]
            · simp [hjk, hj0]
          · exact fun hnot => (hnot (Finset.mem_range.mpr hk)).elim
  have hInt :
      |∫ t in Set.Icc (-Real.pi) Real.pi, q t * c t| ≤ 2 * Real.pi * B := by
    have hnorm := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := volume.restrict (Set.Icc (-Real.pi) Real.pi))
      (C := B) (by
        filter_upwards
        intro t
        rw [Real.norm_eq_abs, abs_mul]
        change |q t| * |Real.cos ((k : ℝ) * t)| ≤ B
        exact (mul_le_of_le_one_right (abs_nonneg (q t)) (abs_cos_le_one _)).trans
          (hbound t))
    have hnorm' :
        |∫ t in Set.Icc (-Real.pi) Real.pi, q t * c t| ≤
          B * (Real.pi + Real.pi) := by
      simpa [c, Measure.restrict_apply_univ, Real.pi_pos.le, Real.norm_eq_abs,
        mul_comm, mul_left_comm, mul_assoc] using hnorm
    nlinarith
  rw [heq] at hInt
  by_cases hk0 : k = 0
  · subst k
    simp only [if_pos, abs_mul, abs_of_pos (show 0 < 2 * Real.pi by positivity)] at hInt
    have := (mul_le_mul_iff_of_pos_left (show 0 < 2 * Real.pi by positivity)).mp
      (show (2 * Real.pi) * |a 0| ≤ (2 * Real.pi) * B by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hInt)
    exact this.trans (by linarith)
  · simp only [if_neg hk0, abs_mul, abs_of_pos Real.pi_pos] at hInt
    have := (mul_le_mul_iff_of_pos_left Real.pi_pos).mp
      (show Real.pi * |a k| ≤ Real.pi * (2 * B) by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hInt)
    exact this

private lemma polyCoeffL1_le_bounded (n : ℕ) (p : Polynomial ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hp : p.natDegree ≤ n)
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ B) :
    polyCoeffL1 p ≤ (2 * (n + 1) * (3 : ℝ) ^ n) * B := by
  classical
  rcases (polynomial_cos_is_even_trigPoly p hp).1 with ⟨a, b, hab⟩
  have hcos (t : ℝ) : p.eval (Real.cos t) =
      ∑ k ∈ Finset.range (n + 1), a k * Real.cos ((k : ℝ) * t) := by
    have ht := hab t
    have hnt := hab (-t)
    simp only [Real.cos_neg, mul_neg, Real.sin_neg] at hnt
    have hnt' : p.eval (Real.cos t) = ∑ k ∈ Finset.range (n + 1),
        (a k * Real.cos ((k : ℝ) * t) - b k * Real.sin ((k : ℝ) * t)) := by
      simpa [sub_eq_add_neg] using hnt
    calc
      p.eval (Real.cos t) = (p.eval (Real.cos t) + p.eval (Real.cos t)) / 2 := by ring
      _ = ((∑ k ∈ Finset.range (n + 1),
              (a k * Real.cos ((k : ℝ) * t) + b k * Real.sin ((k : ℝ) * t))) +
            (∑ k ∈ Finset.range (n + 1),
              (a k * Real.cos ((k : ℝ) * t) - b k * Real.sin ((k : ℝ) * t)))) / 2 := by
            rw [← ht, ← hnt']
      _ = ∑ k ∈ Finset.range (n + 1), a k * Real.cos ((k : ℝ) * t) := by
            rw [← Finset.sum_add_distrib, Finset.sum_div]
            apply Finset.sum_congr rfl
            intro k hk
            ring
  have ha (k : ℕ) (hk : k ∈ Finset.range (n + 1)) : |a k| ≤ 2 * B := by
    apply cosine_coeff_abs_le_four (q := fun t => p.eval (Real.cos t))
      hB
    · intro t
      exact hbound _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    · exact hcos
    · exact Finset.mem_range.mp hk
  rcases cosine_sum_exists_polynomial n a with ⟨p', hp'deg, hp'eval, hp'L1⟩
  have hpp' : p = p' := by
    let node : Fin (n + 1) → ℝ := fun j => (j : ℝ) / (n + 1 : ℝ)
    let angle : Fin (n + 1) → ℝ := fun j => Real.arccos (node j)
    have hnode_nonneg (j : Fin (n + 1)) : 0 ≤ node j := by
      dsimp [node]
      positivity
    have hnode_le_one (j : Fin (n + 1)) : node j ≤ 1 := by
      dsimp [node]
      rw [div_le_one (by positivity : (0 : ℝ) < n + 1)]
      exact_mod_cast (Nat.le_trans (Nat.le_of_lt_succ j.isLt) (Nat.le_add_right n 1))
    have hcos_angle (j : Fin (n + 1)) : Real.cos (angle j) = node j :=
      Real.cos_arccos (le_trans (by norm_num) (hnode_nonneg j)) (hnode_le_one j)
    have hnode_inj : Function.Injective node := by
      intro j k hjk
      dsimp [node] at hjk
      have hden : (n + 1 : ℝ) ≠ 0 := by positivity
      have : (j : ℝ) = (k : ℝ) := (div_left_inj' hden).mp hjk
      exact Fin.ext (by exact_mod_cast this)
    apply sub_eq_zero.mp
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (p - p') hnode_inj
    · intro j
      simp only [Polynomial.eval_sub]
      rw [← hcos_angle j, hcos (angle j), hp'eval (angle j)]
      ring
    · rw [Fintype.card_fin]
      exact lt_of_le_of_lt (Polynomial.natDegree_sub_le p p')
        (Nat.lt_succ_of_le (max_le hp hp'deg))
  rw [hpp']
  refine hp'L1.trans ?_
  calc
    (∑ k ∈ Finset.range (n + 1), |a k| * (3 : ℝ) ^ k) ≤
        ∑ k ∈ Finset.range (n + 1), (2 * B) * (3 : ℝ) ^ n := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul (ha k hk)
        (pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
        (by positivity) (by positivity)
    _ = (2 * (n + 1) * (3 : ℝ) ^ n) * B := by
      rw [Finset.sum_const, Finset.card_range]
      ring

private lemma abs_poly_coeff_le_coeffL1 (p : Polynomial ℝ) (i : ℕ) :
    |p.coeff i| ≤ polyCoeffL1 p := by
  by_cases hi : i ∈ p.support
  · exact Finset.single_le_sum (fun j _ => abs_nonneg (p.coeff j)) hi
  · have hi0 : p.coeff i = 0 := by
      by_contra hne
      exact hi (Polynomial.mem_support_iff.mpr hne)
    rw [hi0, abs_zero]
    exact Finset.sum_nonneg fun j _ => abs_nonneg (p.coeff j)

private lemma mvCoeffL1_finSucc {d n : ℕ} (p : MvPolynomial (Fin (d + 1)) ℝ)
    (hcoord : ∀ m ∈ p.support, ∀ i, m i ≤ n) :
    mvCoeffL1 p = ∑ i ∈ Finset.range (n + 1),
      mvCoeffL1 (((MvPolynomial.finSuccEquiv ℝ d) p).coeff i) := by
  classical
  let P := (MvPolynomial.finSuccEquiv ℝ d) p
  symm
  change (∑ i ∈ Finset.range (n + 1),
      ∑ m ∈ (P.coeff i).support, |(P.coeff i).coeff m|) =
    ∑ m ∈ p.support, |p.coeff m|
  rw [Finset.sum_sigma']
  apply Finset.sum_bij
      (fun z _ => Finsupp.cons z.1 z.2)
  · intro z hz
    rw [MvPolynomial.mem_support_iff]
    rw [← MvPolynomial.finSuccEquiv_coeff_coeff]
    exact MvPolynomial.mem_support_iff.mp (Finset.mem_sigma.mp hz).2
  · intro z₁ hz₁ z₂ hz₂ heq
    rcases z₁ with ⟨i₁, m₁⟩
    rcases z₂ with ⟨i₂, m₂⟩
    have hi : i₁ = i₂ := by
      have := congrArg (fun m : Fin (d + 1) →₀ ℕ => m 0) heq
      simpa using this
    subst i₂
    have hm : m₁ = m₂ := by
      have := congrArg Finsupp.tail heq
      simpa using this
    subst m₂
    rfl
  · intro m hm
    let z : (i : ℕ) × (Fin d →₀ ℕ) := ⟨m 0, m.tail⟩
    have hz : z ∈ (Finset.range (n + 1)).sigma
        (fun i => (((MvPolynomial.finSuccEquiv ℝ d) p).coeff i).support) := by
      apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hcoord m hm 0)), ?_⟩
      rw [MvPolynomial.mem_support_iff, MvPolynomial.finSuccEquiv_coeff_coeff,
        Finsupp.cons_tail]
      exact MvPolynomial.mem_support_iff.mp hm
    refine ⟨z, hz, ?_⟩
    exact Finsupp.cons_tail m
  · intro z hz
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]

private lemma mvCoeffL1_le_bounded {d n : ℕ} (p : MvPolynomial (Fin d) ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hcoord : ∀ m ∈ p.support, ∀ i, m i ≤ n)
    (hbound : ∀ x ∈ normalizedCube d, |MvPolynomial.eval x p| ≤ B) :
    mvCoeffL1 p ≤ ((2 : ℝ) * (n + 1) ^ 2 * (3 : ℝ) ^ n) ^ d * B := by
  induction d generalizing B with
  | zero =>
      have hx := hbound (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      have hm (m : Fin 0 →₀ ℕ) : m = 0 := by
        apply Finsupp.ext
        intro i
        exact Fin.elim0 i
      simpa [mvCoeffL1, MvPolynomial.eval_eq, hm] using hx
  | succ d ih =>
      classical
      let P := (MvPolynomial.finSuccEquiv ℝ d) p
      have hPdeg : P.natDegree ≤ n := by
        dsimp [P]
        rw [MvPolynomial.natDegree_finSuccEquiv]
        exact MvPolynomial.degreeOf_le_iff.mpr (fun m hm => hcoord m hm 0)
      have htail (i : ℕ) :
          ∀ m ∈ (P.coeff i).support, ∀ j, m j ≤ n := by
        intro m hm j
        have := hcoord (Finsupp.cons i m) (by
          rw [MvPolynomial.mem_support_iff, ← MvPolynomial.finSuccEquiv_coeff_coeff]
          exact MvPolynomial.mem_support_iff.mp hm) j.succ
        simpa using this
      have hcoeff_bound (i : ℕ) (hi : i < n + 1) (y : Fin d → ℝ)
          (hy : y ∈ normalizedCube d) :
          |MvPolynomial.eval y (P.coeff i)| ≤
            (2 * (n + 1) * (3 : ℝ) ^ n) * B := by
        let r : Polynomial ℝ := Polynomial.map (MvPolynomial.eval y) P
        have hrdeg : r.natDegree ≤ n :=
          Polynomial.natDegree_map_le.trans hPdeg
        have hrbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |r.eval x| ≤ B := by
          intro x hx
          dsimp [r]
          rw [← MvPolynomial.eval_eq_eval_mv_eval']
          apply hbound
          intro j
          refine Fin.cases hx (fun k => hy k) j
        calc
          |MvPolynomial.eval y (P.coeff i)| = |r.coeff i| := by
            dsimp [r]
            rw [MvPolynomial.coeff_eval_eq_eval_coeff]
          _ ≤ polyCoeffL1 r := abs_poly_coeff_le_coeffL1 r i
          _ ≤ (2 * (n + 1) * (3 : ℝ) ^ n) * B :=
            polyCoeffL1_le_bounded n r B hB hrdeg hrbound
      rw [mvCoeffL1_finSucc p hcoord]
      calc
        (∑ i ∈ Finset.range (n + 1), mvCoeffL1 (P.coeff i)) ≤
            ∑ i ∈ Finset.range (n + 1),
              (((2 : ℝ) * (n + 1) ^ 2 * (3 : ℝ) ^ n) ^ d *
                ((2 * (n + 1) * (3 : ℝ) ^ n) * B)) := by
          apply Finset.sum_le_sum
          intro i hi
          apply ih (P.coeff i) ((2 * (n + 1) * (3 : ℝ) ^ n) * B)
          · positivity
          · exact htail i
          · exact hcoeff_bound i (Finset.mem_range.mp hi)
        _ = ((2 : ℝ) * (n + 1) ^ 2 * (3 : ℝ) ^ n) ^ (d + 1) * B := by
          rw [Finset.sum_const, Finset.card_range, pow_succ]
          ring

private lemma natCast_succ_le_two_pow (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      push_cast at ih ⊢
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (n + 1)]

/-- For [integer order K](hyp:K) that is [strictly positive](hyp:hK), [a function on four
normalized coordinates](hyp:f) that [is continuous on the normalized cube](hyp:hf), [a
nonnegative uniform bound](hyp:B,hB), and [the corresponding bound on the function throughout
the cube](hyp:hbound), [its tensor convolution has a four-variable polynomial representation
with the stated support, degree, and exponential coefficient one-norm bounds](goal).
-/
theorem tensorConvolution_exists_mvPolynomial_four_coeffBound {K : ℕ} (hK : 0 < K)
    (f : (Fin 4 → ℝ) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ContinuousOn f (normalizedCube 4))
    (hbound : ∀ z ∈ normalizedCube 4, |f z| ≤ B) :
    ∃ p : MvPolynomial (Fin 4) ℝ,
      (∀ x : Fin 4 → ℝ, MvPolynomial.eval (cosPoint x) p = tensorConvolution K f x) ∧
      (∀ m ∈ p.support, ∀ i, m i ≤ 2 * (K - 1)) ∧
      p.totalDegree ≤ 8 * (K - 1) ∧
      mvCoeffL1 p ≤ (2 : ℝ) ^ (40 * K + 20) * B := by
  /-
  Proof route: expose the finite cosine coefficients of `jackson K`; expand
  the four translated factors, integrate their bounded coefficient functions,
  and discard all sine terms using coordinate evenness.  Replace each cosine
  frequency by `Polynomial.Chebyshev.T`, tensor the four univariate
  polynomials with `toMvPolynomial`, and use `chebyshev_coeffL1_le`.  Bounding
  the finite Fourier coefficients by the kernel mass and counting the at most
  `(2 * (K - 1) + 1)^4` indices leaves ample room in `2^(40*K+20)`.
  The same explicit construction supplies the evaluation, coordinate-support,
  and total-degree conjuncts; do not obtain the coefficient claim from the
  nonquantitative existence theorem by an arbitrary choice of representative.
  -/
  classical
  let n := 2 * (K - 1)
  rcases tensorConvolution_exists_mvPolynomial hK f hf with
    ⟨p, hp_eval, hp_coord, hp_total⟩
  have hcompact : IsCompact (periodBox 4) := by
    rw [show periodBox 4 = {u | ∀ i, u i ∈ Set.Icc (-Real.pi) Real.pi} by rfl]
    exact isCompact_pi_infinite fun _ => isCompact_Icc
  have hfcos (x : Fin 4 → ℝ) : Continuous
      (fun u : Fin 4 → ℝ => f (cosPoint (x - u))) := by
    apply hf.comp_continuous
    · unfold cosPoint
      fun_prop
    · exact fun u => cosPoint_mem_normalizedCube (x - u)
  have hjc : Continuous (tensorJackson K 4) := by
    unfold tensorJackson
    fun_prop
  have hint_f (x : Fin 4 → ℝ) : IntegrableOn
      (fun u : Fin 4 → ℝ => f (cosPoint (x - u)) * tensorJackson K 4 u)
      (periodBox 4) :=
    ((hfcos x).mul hjc).continuousOn.integrableOn_compact hcompact
  have hint_B : IntegrableOn
      (fun u : Fin 4 → ℝ => B * tensorJackson K 4 u) (periodBox 4) :=
    (continuous_const.mul hjc).continuousOn.integrableOn_compact hcompact
  have hsub (x : Fin 4 → ℝ) :
      tensorConvolution K (fun z => B - f z) x = B - tensorConvolution K f x := by
    unfold tensorConvolution
    rw [show (fun u : Fin 4 → ℝ =>
        (B - f (cosPoint (x - u))) * tensorJackson K 4 u) =
        fun u => B * tensorJackson K 4 u -
          f (cosPoint (x - u)) * tensorJackson K 4 u by funext u; ring,
      integral_sub hint_B (hint_f x), integral_const_mul,
      tensorJackson_integral_eq_one hK]
    ring
  have hadd (x : Fin 4 → ℝ) :
      tensorConvolution K (fun z => B + f z) x = B + tensorConvolution K f x := by
    unfold tensorConvolution
    rw [show (fun u : Fin 4 → ℝ =>
        (B + f (cosPoint (x - u))) * tensorJackson K 4 u) =
        fun u => B * tensorJackson K 4 u +
          f (cosPoint (x - u)) * tensorJackson K 4 u by funext u; ring,
      integral_add hint_B (hint_f x), integral_const_mul,
      tensorJackson_integral_eq_one hK]
    ring
  have hconv_bound (x : Fin 4 → ℝ) : |tensorConvolution K f x| ≤ B := by
    rw [abs_le]
    constructor
    · have hn := tensorConvolution_nonneg hK
          (f := fun z : Fin 4 → ℝ => B + f z) (fun z hz => by
            have := hbound z hz
            rw [abs_le] at this
            linarith) x
      rw [hadd] at hn
      linarith
    · have hn := tensorConvolution_nonneg hK
          (f := fun z : Fin 4 → ℝ => B - f z) (fun z hz => by
            have := hbound z hz
            rw [abs_le] at this
            linarith) x
      rw [hsub] at hn
      linarith
  have hp_bound : ∀ z ∈ normalizedCube 4, |MvPolynomial.eval z p| ≤ B := by
    intro z hz
    let x : Fin 4 → ℝ := fun i => Real.arccos (z i)
    have hcosx : cosPoint x = z := by
      funext i
      exact Real.cos_arccos (hz i).1 (hz i).2
    rw [← hcosx, hp_eval]
    exact hconv_bound x
  have hp_l1 : mvCoeffL1 p ≤
      ((2 : ℝ) * (n + 1) ^ 2 * (3 : ℝ) ^ n) ^ 4 * B :=
    mvCoeffL1_le_bounded p B hB hp_coord hp_bound
  have hn_factor :
      (2 : ℝ) * (n + 1) ^ 2 * (3 : ℝ) ^ n ≤ (2 : ℝ) ^ (4 * n + 3) := by
    have hsucc : (n : ℝ) + 1 ≤ (2 : ℝ) ^ (n + 1) := by
      simpa using natCast_succ_le_two_pow n
    have hthree : (3 : ℝ) ^ n ≤ (4 : ℝ) ^ n :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) n
    calc
      (2 : ℝ) * (n + 1) ^ 2 * (3 : ℝ) ^ n ≤
          2 * ((2 : ℝ) ^ (n + 1)) ^ 2 * ((4 : ℝ) ^ n) := by
        gcongr
      _ = (2 : ℝ) ^ (4 * n + 3) := by
        rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        calc
          (2 : ℝ) * 2 ^ ((n + 1) * 2) * 2 ^ (2 * n) =
              (2 : ℝ) ^ ((n + 1) * 2 + 1) * 2 ^ (2 * n) := by
                rw [pow_add, pow_one]
                ring
          _ = (2 : ℝ) ^ (((n + 1) * 2 + 1) + 2 * n) := by
            rw [pow_add]
            ring
          _ = (2 : ℝ) ^ (4 * n + 3) := by congr 1; omega
  have hn_power :
      ((2 : ℝ) * (n + 1) ^ 2 * (3 : ℝ) ^ n) ^ 4 ≤
        (2 : ℝ) ^ (40 * K + 20) := by
    calc
      ((2 : ℝ) * (n + 1) ^ 2 * (3 : ℝ) ^ n) ^ 4 ≤
          ((2 : ℝ) ^ (4 * n + 3)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hn_factor 4
      _ = (2 : ℝ) ^ (4 * (4 * n + 3)) := by rw [← pow_mul]; congr 1; omega
      _ ≤ (2 : ℝ) ^ (40 * K + 20) := by
        apply pow_le_pow_right₀ (by norm_num)
        dsimp [n]
        omega
  refine ⟨p, hp_eval, hp_coord, ?_, ?_⟩
  · simpa [n, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hp_total
  · exact hp_l1.trans (mul_le_mul_of_nonneg_right hn_power hB)

end Causalean.Mathlib.Analysis.JacksonApproximation

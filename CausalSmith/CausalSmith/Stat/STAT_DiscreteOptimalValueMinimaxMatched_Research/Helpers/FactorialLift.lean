import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.RingTheory.Binomial

/-! Centered falling-factorial lifts for Poisson counts. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open Finset Polynomial

-- @node: descPochhammer_mul_linearization
/-- Linearization of a product of two falling-factorial basis polynomials,
classified by the size of the overlap between the two ordered selections. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma descPochhammer_mul_linearization (a b : ℕ) :
    descPochhammer ℤ a * descPochhammer ℤ b =
      ∑ l ∈ range (min a b + 1),
        C (Nat.choose a l * Nat.choose b l * l.factorial : ℤ) *
          descPochhammer ℤ (a + b - l) := by
  classical
  wlog hab : a ≤ b generalizing a b
  · rw [mul_comm]
    simpa [Nat.min_comm, mul_comm, Nat.add_comm] using this b a (le_of_not_ge hab)
  rw [Nat.min_eq_left hab]
  have hadd := Ring.descPochhammer_smeval_add (R := ℤ[X]) b
    (Commute.all (X - C (a : ℤ)) (C (a : ℤ)))
  simp only [sub_add_cancel] at hadd
  have hsX (p : ℤ[X]) : p.smeval X = p := by
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval]
    simpa using Polynomial.eval₂_C_X p
  have hscomp (p : ℤ[X]) : p.smeval (X - C (a : ℤ)) =
      p.comp (X - C (a : ℤ)) := by
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval]
    have hhom : (RingHom.smulOneHom : ℤ →+* ℤ[X]) = C := by
      ext z
      simp
    rw [hhom]
    rfl
  have hsC (p : ℤ[X]) : p.smeval (C (a : ℤ)) = C (p.eval (a : ℤ)) := by
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval]
    simpa using Polynomial.eval₂_at_apply C (a : ℤ) (p := p)
  simp only [hsX, hscomp, hsC] at hadd
  rw [← Finset.Nat.sum_antidiagonal_swap] at hadd
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hadd
  simp only [Prod.swap, Prod.fst, Prod.snd, Nat.succ_eq_add_one] at hadd
  have heval (l : ℕ) : (descPochhammer ℤ l).eval (a : ℤ) =
      (a.descFactorial l : ℤ) := by
    simpa [Polynomial.eval_eq_smeval] using
      (Polynomial.descPochhammer_smeval_eq_descFactorial (R := ℤ) a l)
  have hbform : descPochhammer ℤ b =
      ∑ l ∈ range (b + 1),
        C ((b.choose l : ℤ) * (a.descFactorial l : ℤ)) *
          (descPochhammer ℤ (b - l)).comp (X - C (a : ℤ)) := by
    rw [hadd]
    apply Finset.sum_congr rfl
    intro l hl
    rw [heval]
    have hl' : l ≤ b := Nat.le_of_lt_succ (by simpa using Finset.mem_range.mp hl)
    rw [Nat.choose_symm hl']
    simp
    ring
  calc
    descPochhammer ℤ a * descPochhammer ℤ b =
        descPochhammer ℤ a *
          (∑ l ∈ range (b + 1),
            C ((b.choose l : ℤ) * (a.descFactorial l : ℤ)) *
              (descPochhammer ℤ (b - l)).comp (X - C (a : ℤ))) := by rw [hbform]
    _ = ∑ l ∈ range (b + 1),
          C ((b.choose l : ℤ) * (a.descFactorial l : ℤ)) *
            descPochhammer ℤ (a + (b - l)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _hl
      calc
        descPochhammer ℤ a *
            (C ((b.choose l : ℤ) * (a.descFactorial l : ℤ)) *
              (descPochhammer ℤ (b - l)).comp (X - C (a : ℤ))) =
            C ((b.choose l : ℤ) * (a.descFactorial l : ℤ)) *
              (descPochhammer ℤ a *
                (descPochhammer ℤ (b - l)).comp (X - C (a : ℤ))) := by ring
        _ = _ := by
          rw [show C (a : ℤ) = (a : ℤ[X]) by simp]
          rw [descPochhammer_mul]
    _ = ∑ l ∈ range (a + 1),
          C ((b.choose l : ℤ) * (a.descFactorial l : ℤ)) *
            descPochhammer ℤ (a + (b - l)) := by
      symm
      apply Finset.sum_subset
      · intro l hl
        exact Finset.mem_range.mpr
          ((Finset.mem_range.mp hl).trans_le (Nat.succ_le_succ hab))
      · intro l hlBig hlSmall
        have ha_lt : a < l := by
          have := Finset.mem_range.mp hlBig
          simpa [Finset.mem_range] using hlSmall
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr ha_lt]
        simp
    _ = ∑ l ∈ range (a + 1),
          C (Nat.choose a l * Nat.choose b l * l.factorial : ℤ) *
            descPochhammer ℤ (a + b - l) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hl' : l ≤ a := Nat.le_of_lt_succ (by simpa using Finset.mem_range.mp hl)
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      congr 1
      · push_cast
        ring
      · rw [Nat.add_sub_assoc (le_trans hl' hab) a]

-- @node: descFactorial_mul_identity
/-- Exact overlap expansion for the product of two descending factorials. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma descFactorial_mul_identity (N a b : ℕ) :
    N.descFactorial a * N.descFactorial b =
      ∑ l ∈ range (min a b + 1),
        Nat.choose a l * Nat.choose b l * l.factorial *
          N.descFactorial (a + b - l) := by
  have hp := congrArg (Polynomial.eval (N : ℤ))
    (descPochhammer_mul_linearization a b)
  simp only [Polynomial.eval_mul, Polynomial.eval_finset_sum, Polynomial.eval_C,
    descPochhammer_eval_eq_descFactorial] at hp
  exact_mod_cast hp

/-- Falling factorial `(N)_t`. -/
def fallingFactorial (N t : ℕ) : ℕ := ∏ j ∈ Finset.range t, (N - j)

-- @node: fallingFactorial_eq_descFactorial
/-- The paper's product definition of a falling factorial agrees with Mathlib's
descending factorial. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma fallingFactorial_eq_descFactorial (N t : ℕ) :
    fallingFactorial N t = N.descFactorial t := by
  exact (Nat.descFactorial_eq_prod_range N t).symm

-- @node: poisson_descFactorial_shift
/-- Shifting a Poisson falling-factorial summand by its order cancels the
factorial denominator. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma poisson_descFactorial_shift (lambda : NNReal) (t k : ℕ) :
    Real.exp (-(lambda : ℝ)) * (lambda : ℝ) ^ (k + t) /
          ((k + t).factorial : ℝ) * ((k + t).descFactorial t : ℝ) =
      ((lambda : ℝ) ^ t * Real.exp (-(lambda : ℝ))) *
        ((lambda : ℝ) ^ k / (k.factorial : ℝ)) := by
  have hfacNat : k.factorial * (k + t).descFactorial t = (k + t).factorial := by
    simpa [Nat.add_sub_cancel] using
      (Nat.factorial_mul_descFactorial (n := k + t) (k := t) (Nat.le_add_left t k))
  have hfac : (k.factorial : ℝ) * ((k + t).descFactorial t : ℝ) =
      ((k + t).factorial : ℝ) := by
    exact_mod_cast hfacNat
  rw [pow_add]
  field_simp [Nat.factorial_ne_zero]
  linear_combination ((lambda : ℝ) ^ k * (lambda : ℝ) ^ t) * hfac

-- @node: summable_poisson_descFactorial
/-- Every falling factorial is summable against a Poisson mass function. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma summable_poisson_descFactorial (lambda : NNReal) (t : ℕ) :
    Summable (fun N : ℕ =>
      Real.exp (-(lambda : ℝ)) * (lambda : ℝ) ^ N / (N.factorial : ℝ) *
        (N.descFactorial t : ℝ)) := by
  let f : ℕ → ℝ := fun N =>
    Real.exp (-(lambda : ℝ)) * (lambda : ℝ) ^ N / (N.factorial : ℝ) *
      (N.descFactorial t : ℝ)
  have hshift : Summable (fun k => f (k + t)) := by
    apply Summable.congr
      ((NormedSpace.expSeries_div_hasSum_exp (lambda : ℝ)).summable.mul_left
        ((lambda : ℝ) ^ t * Real.exp (-(lambda : ℝ))))
    intro k
    exact (poisson_descFactorial_shift lambda t k).symm
  exact (summable_nat_add_iff t).mp hshift

-- @node: integral_fallingFactorial_poisson
/-- The order-`t` falling factorial of a Poisson count has expectation equal
to the `t`-th power of its mean. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma integral_fallingFactorial_poisson (lambda : NNReal) (t : ℕ) :
    ∫ N : ℕ, (fallingFactorial N t : ℝ) ∂poissonMeasure lambda =
      (lambda : ℝ) ^ t := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul, fallingFactorial_eq_descFactorial]
  let f : ℕ → ℝ := fun N =>
    Real.exp (-(lambda : ℝ)) * (lambda : ℝ) ^ N / (N.factorial : ℝ) *
      (N.descFactorial t : ℝ)
  have hshift : Summable (fun k => f (k + t)) :=
    (summable_nat_add_iff t).mpr (summable_poisson_descFactorial lambda t)
  have hprefix : ∑ k ∈ Finset.range t, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkt : k < t := Finset.mem_range.mp hk
    simp [f, Nat.descFactorial_eq_zero_iff_lt.mpr hkt]
  calc
    ∑' N, Real.exp (-(lambda : ℝ)) * (lambda : ℝ) ^ N / ↑N.factorial *
        ↑(N.descFactorial t) = ∑' N, f N := by rfl
    _ = ∑ k ∈ Finset.range t, f k + ∑' k, f (k + t) :=
      (hshift.sum_add_tsum_nat_add').symm
    _ = ∑' k, (((lambda : ℝ) ^ t * Real.exp (-(lambda : ℝ))) *
        ((lambda : ℝ) ^ k / (k.factorial : ℝ))) := by
      rw [hprefix, zero_add]
      congr 1
      funext k
      exact poisson_descFactorial_shift lambda t k
    _ = ((lambda : ℝ) ^ t * Real.exp (-(lambda : ℝ))) * Real.exp (lambda : ℝ) := by
      rw [tsum_mul_left]
      simpa only [Real.exp_eq_exp_ℝ] using congrArg
        (fun z : ℝ => ((lambda : ℝ) ^ t * Real.exp (-(lambda : ℝ))) * z)
        (NormedSpace.expSeries_div_hasSum_exp (lambda : ℝ)).tsum_eq
    _ = (lambda : ℝ) ^ t := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
      simp

-- @node: integrable_fallingFactorial_poisson
/-- Every falling factorial of a Poisson count is integrable. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma integrable_fallingFactorial_poisson (lambda : NNReal) (t : ℕ) :
    Integrable (fun N : ℕ => (fallingFactorial N t : ℝ)) (poissonMeasure lambda) := by
  rw [integrable_poissonMeasure_iff]
  convert summable_poisson_descFactorial lambda t using 1
  funext N
  rw [fallingFactorial_eq_descFactorial, Real.norm_eq_abs, abs_of_nonneg]
  positivity

-- @node: integrable_fallingFactorial_mul_poisson
/-- A product of two falling factorials is integrable under every Poisson law. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma integrable_fallingFactorial_mul_poisson (lambda : NNReal) (a b : ℕ) :
    Integrable (fun N : ℕ =>
      (fallingFactorial N a : ℝ) * fallingFactorial N b) (poissonMeasure lambda) := by
  have hpoint (N : ℕ) :
      (fallingFactorial N a : ℝ) * fallingFactorial N b =
        ∑ l ∈ range (min a b + 1),
          (Nat.choose a l * Nat.choose b l * l.factorial : ℝ) *
            fallingFactorial N (a + b - l) := by
    simp only [fallingFactorial_eq_descFactorial]
    exact_mod_cast descFactorial_mul_identity N a b
  simp_rw [hpoint]
  apply integrable_finset_sum
  intro l _hl
  exact (integrable_fallingFactorial_poisson lambda (a + b - l)).const_mul _

-- @node: integral_fallingFactorial_mul_poisson
/-- The joint Poisson moment of two falling factorials is the exact finite
overlap expansion. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma integral_fallingFactorial_mul_poisson (lambda : NNReal) (a b : ℕ) :
    (∫ N : ℕ, (fallingFactorial N a : ℝ) * fallingFactorial N b
      ∂poissonMeasure lambda) =
      ∑ l ∈ range (min a b + 1),
        (Nat.choose a l : ℝ) * Nat.choose b l * Nat.factorial l *
          (lambda : ℝ) ^ (a + b - l) := by
  have hpoint (N : ℕ) :
      (fallingFactorial N a : ℝ) * fallingFactorial N b =
        ∑ l ∈ range (min a b + 1),
          (Nat.choose a l * Nat.choose b l * l.factorial : ℝ) *
            fallingFactorial N (a + b - l) := by
    simp only [fallingFactorial_eq_descFactorial]
    exact_mod_cast descFactorial_mul_identity N a b
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro l _hl
    rw [integral_const_mul, integral_fallingFactorial_poisson]
  · intro l _hl
    exact (integrable_fallingFactorial_poisson lambda (a + b - l)).const_mul _

/-- Centered factorial lift of a monomial. -/
noncomputable def centeredFactorial (m : ℝ) (h N : ℕ) (z : ℝ) : ℝ :=
  ∑ t ∈ Finset.range (h + 1), (Nat.choose h t : ℝ) * (-z) ^ (h - t) *
    (fallingFactorial N t : ℝ) / m ^ t
  -- @realizes \(U_h(N;z)\)(centered Poisson factorial polynomial)

-- @node: integral_centeredFactorial_poisson
/-- A centered factorial lift is unbiased for the corresponding centered
power under a Poisson count with mean `m*q`. This uses [the Poisson intensity is positive](hyp:hm), and [the cell masses satisfy their stated restrictions](hyp:hq). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma integral_centeredFactorial_poisson (m q z : ℝ) (hm : 0 < m) (hq : 0 ≤ q)
    (h : ℕ) :
    ∫ N : ℕ, centeredFactorial m h N z ∂poissonMeasure (m * q).toNNReal =
      (q - z) ^ h := by
  simp only [centeredFactorial]
  rw [integral_finsetSum]
  · simp_rw [integral_div, integral_const_mul,
      show ∀ t : ℕ, (∫ N : ℕ, (fallingFactorial N t : ℝ)
        ∂poissonMeasure (m * q).toNNReal) = (m * q) ^ t by
          intro t
          simpa [Real.coe_toNNReal (m * q) (mul_nonneg (le_of_lt hm) hq)] using
            integral_fallingFactorial_poisson (m * q).toNNReal t]
    have hratio (x : ℕ) :
        (Nat.choose h x : ℝ) * (-z) ^ (h - x) * (m * q) ^ x / m ^ x =
          (Nat.choose h x : ℝ) * (-z) ^ (h - x) * q ^ x := by
      rw [mul_pow]
      field_simp
    simp_rw [hratio]
    calc
      ∑ x ∈ Finset.range (h + 1), (Nat.choose h x : ℝ) * (-z) ^ (h - x) * q ^ x =
          ∑ x ∈ Finset.range (h + 1), q ^ x * (-z) ^ (h - x) * Nat.choose h x := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = (q + (-z)) ^ h := (add_pow q (-z) h).symm
      _ = (q - z) ^ h := by ring
  · intro t ht
    exact (integrable_fallingFactorial_poisson (m * q).toNNReal t).const_mul
      ((Nat.choose h t : ℝ) * (-z) ^ (h - t)) |>.div_const (m ^ t)

-- @node: integrable_centeredFactorial_mul_poisson
/-- Two centered factorial lifts have an integrable product under every
Poisson law. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma integrable_centeredFactorial_mul_poisson (lambda : NNReal) (m z : ℝ) (h t : ℕ) :
    Integrable (fun N : ℕ =>
      centeredFactorial m h N z * centeredFactorial m t N z)
      (poissonMeasure lambda) := by
  simp only [centeredFactorial, Finset.sum_mul, Finset.mul_sum]
  apply integrable_finset_sum
  intro a _ha
  apply integrable_finset_sum
  intro b _hb
  have hab := integrable_fallingFactorial_mul_poisson lambda b a
  have hc := hab.const_mul
      (((Nat.choose h b : ℝ) * (-z) ^ (h - b) / m ^ b) *
        ((Nat.choose t a : ℝ) * (-z) ^ (t - a) / m ^ a))
  exact hc.congr (Filter.Eventually.of_forall (fun N => by ring))

-- @node: integral_centeredFactorial_mul_poisson_expanded
/-- Expanding both lifts and classifying the overlap gives the raw finite-sum
form of their joint Poisson moment. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma integral_centeredFactorial_mul_poisson_expanded
    (lambda : NNReal) (m z : ℝ) (h t : ℕ) :
    (∫ N : ℕ, centeredFactorial m h N z * centeredFactorial m t N z
      ∂poissonMeasure lambda) =
      ∑ b ∈ range (t + 1), ∑ a ∈ range (h + 1),
        ((Nat.choose h a : ℝ) * (-z) ^ (h - a) / m ^ a) *
          ((Nat.choose t b : ℝ) * (-z) ^ (t - b) / m ^ b) *
            (∑ l ∈ range (min a b + 1),
              (Nat.choose a l : ℝ) * Nat.choose b l * Nat.factorial l *
                (lambda : ℝ) ^ (a + b - l)) := by
  simp only [centeredFactorial, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro b _hb
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro a _ha
      rw [show (fun N : ℕ =>
          (↑(h.choose a) * (-z) ^ (h - a) * ↑(fallingFactorial N a) / m ^ a) *
            (↑(t.choose b) * (-z) ^ (t - b) * ↑(fallingFactorial N b) / m ^ b)) =
          fun N => (((h.choose a : ℝ) * (-z) ^ (h - a) / m ^ a) *
            ((t.choose b : ℝ) * (-z) ^ (t - b) / m ^ b)) *
              ((fallingFactorial N a : ℝ) * fallingFactorial N b) by
            funext N; ring]
      rw [integral_const_mul, integral_fallingFactorial_mul_poisson]
      rw [Finset.mul_sum]
    · intro a _ha
      have hc := (integrable_fallingFactorial_mul_poisson lambda a b).const_mul
        (((h.choose a : ℝ) * (-z) ^ (h - a) / m ^ a) *
          ((t.choose b : ℝ) * (-z) ^ (t - b) / m ^ b))
      exact hc.congr (Filter.Eventually.of_forall (fun N => by ring))
  · intro b _hb
    apply integrable_finset_sum
    intro a _ha
    have hab := integrable_fallingFactorial_mul_poisson lambda a b
    have hc := hab.const_mul
        (((h.choose a : ℝ) * (-z) ^ (h - a) / m ^ a) *
          ((t.choose b : ℝ) * (-z) ^ (t - b) / m ^ b))
    exact hc.congr (Filter.Eventually.of_forall (fun N => by ring))

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

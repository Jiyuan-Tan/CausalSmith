module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentCoupling
public import Mathlib.Analysis.Calculus.Deriv.Pow
/-! Free-amplitude conditional mark arrays and their derivative bounds for the
second-order component contraction argument. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- The Fourier mark mass with a free amplitude and fixed perturbation and bump. -/
-- @node: amplitudeMarkMass
def amplitudeMarkMass (S q u : ℝ) (z : Bool × Bool) : ℝ :=
  (1 + (2*bit z.1-1)*u*S + (2*bit z.2-1)*(u^3*q-u)*S +
    (2*bit z.1-1)*(2*bit z.2-1)*u^2*(q-S^2))/4

/-- The first amplitude derivative of the four conditional masses. -/
-- @node: amplitudeMarkSlope
def amplitudeMarkSlope (S q u : ℝ) (z : Bool × Bool) : ℝ :=
  ((2*bit z.1-1)*S + (2*bit z.2-1)*(3*u^2*q-1)*S +
    (2*bit z.1-1)*(2*bit z.2-1)*2*u*(q-S^2))/4

/-- The second amplitude derivative of the four conditional masses. -/
-- @node: amplitudeMarkCurvature
def amplitudeMarkCurvature (S q u : ℝ) (z : Bool × Bool) : ℝ :=
  ((2*bit z.2-1)*6*u*q*S + (2*bit z.1-1)*(2*bit z.2-1)*2*(q-S^2))/4

/-- A Bernoulli Fourier mark has absolute value one.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:b). -/
-- @node: abs_bit_sign
lemma abs_bit_sign (b : Bool) : |2*bit b-1| = 1 := by
  cases b <;> norm_num [bit]

/-- The finite Fourier triangle inequality bounds the sum of absolute mark masses.  [the theorem's stated inputs and assumptions](hyp:a,b,c,d), and [the asserted conclusion follows](goal). -/
-- @node: markFourier_abs_sum_le
lemma markFourier_abs_sum_le (a b c d : ℝ) :
    (∑ z : Bool × Bool,
      |(a + (2*bit z.1-1)*b + (2*bit z.2-1)*c +
        (2*bit z.1-1)*(2*bit z.2-1)*d)/4|) ≤ |a|+|b|+|c|+|d| := by
  have hp (z : Bool × Bool) :
      |(a + (2*bit z.1-1)*b + (2*bit z.2-1)*c +
        (2*bit z.1-1)*(2*bit z.2-1)*d)/4| ≤ (|a|+|b|+|c|+|d|)/4 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    calc
      _ ≤ |a| + |(2*bit z.1-1)*b| + |(2*bit z.2-1)*c| +
          |(2*bit z.1-1)*(2*bit z.2-1)*d| :=
        by
          have h1 := abs_add_le a ((2*bit z.1-1)*b)
          have h2 := abs_add_le (a+(2*bit z.1-1)*b) ((2*bit z.2-1)*c)
          have h3 := abs_add_le (a+(2*bit z.1-1)*b+(2*bit z.2-1)*c)
            ((2*bit z.1-1)*(2*bit z.2-1)*d)
          linarith
      _ = _ := by simp only [abs_mul, abs_bit_sign, one_mul]
  have hs := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => hp z)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at hs
  linarith


/-- The free-amplitude mass is the product of the treatment and outcome Bernoulli factors.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:S,q,u,z). -/
-- @node: amplitudeMarkMass_factorization
lemma amplitudeMarkMass_factorization (S q u : ℝ) (z : Bool × Bool) :
    amplitudeMarkMass S q u z =
      ((1+(2*bit z.1-1)*u*S)/2) *
        ((1+(2*bit z.2-1)*(-u*S+(2*bit z.1-1)*u^2*q))/2) := by
  rcases z with ⟨a, b⟩
  cases a <;> cases b <;> norm_num [amplitudeMarkMass, bit] <;> ring

/-- Summing the four conditional masses gives one at every amplitude. [The displayed conclusion](goal) follows. -/
-- @node: amplitudeMarkMass_sum
lemma amplitudeMarkMass_sum (S q u : ℝ) :
    (∑ z : Bool × Bool, amplitudeMarkMass S q u z) = 1 := by
  simp [Fintype.sum_prod_type, amplitudeMarkMass, bit]
  ring

/-- The mass at zero amplitude is the fair pair mass.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:S,q,z). -/
-- @node: amplitudeMarkMass_zero
lemma amplitudeMarkMass_zero (S q : ℝ) (z : Bool × Bool) :
    amplitudeMarkMass S q 0 z = 1 / 4 := by
  simp [amplitudeMarkMass]

/-- The actual alternative is the free-amplitude array evaluated at the square-root separation.  [the theorem's stated inputs and assumptions](hyp:lam,x,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: amplitudeMarkMass_actual
lemma amplitudeMarkMass_actual (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam : SignVector hL) (x : Covariate) (z : Bool × Bool) :
    amplitudeMarkMass (perturbation hL lam x) (bump hL x)
      (Real.sqrt (separation hL)) z = conditionalLikelihood hL lam x z.1 z.2 / 4 := by
  rw [conditionalLikelihood_fourier hL hhL]
  have hs := Real.sq_sqrt (separation_unit_range hL hhL).1
  dsimp [amplitudeMarkMass]
  rw [pow_succ, hs]
  ring

/-- The polynomial first derivative is valid at every real amplitude.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:S,q,u,z). -/
-- @node: amplitudeMarkMass_hasDerivAt
lemma amplitudeMarkMass_hasDerivAt (S q u : ℝ) (z : Bool × Bool) :
    HasDerivAt (fun v => amplitudeMarkMass S q v z) (amplitudeMarkSlope S q u z) u := by
  convert (((hasDerivAt_const u (1 : ℝ)).add
    (((hasDerivAt_id u).const_mul (2*bit z.1-1)).mul_const S)).add
    (((((hasDerivAt_id u).pow 3).mul_const q).sub (hasDerivAt_id u)).const_mul
      (2*bit z.2-1) |>.mul_const S)).add
    ((((hasDerivAt_id u).pow 2).const_mul ((2*bit z.1-1)*(2*bit z.2-1))).mul_const
      (q-S^2)) |>.div_const 4 using 1 <;>
    first | rfl | (dsimp [amplitudeMarkMass, amplitudeMarkSlope]; ring)

/-- The polynomial second derivative is valid at every real amplitude.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:S,q,u,z). -/
-- @node: amplitudeMarkSlope_hasDerivAt
lemma amplitudeMarkSlope_hasDerivAt (S q u : ℝ) (z : Bool × Bool) :
    HasDerivAt (fun v => amplitudeMarkSlope S q v z) (amplitudeMarkCurvature S q u z) u := by
  convert (((hasDerivAt_const u ((2*bit z.1-1)*S)).add
    ((((((hasDerivAt_id u).pow 2).const_mul 3).mul_const q).sub
      (hasDerivAt_const u (1 : ℝ))).const_mul (2*bit z.2-1) |>.mul_const S)).add
    (((hasDerivAt_id u).const_mul ((2*bit z.1-1)*(2*bit z.2-1)*2)).mul_const
      (q-S^2))) |>.div_const 4 using 1 <;>
    first | rfl | (dsimp [amplitudeMarkSlope, amplitudeMarkCurvature]; ring)


/-- Legal free amplitudes keep both Bernoulli factors strictly positive.  [the theorem's stated inputs and assumptions](hyp:hq,hu,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:S,q,u,hS). -/
-- @node: amplitudeMarkMass_pos
lemma amplitudeMarkMass_pos (S q u : ℝ) (hS : |S| ≤ 3 / 2)
    (hq : q ∈ Icc 0 1) (hu : u ∈ Icc 0 (1 / 10)) (z : Bool × Bool) :
    0 < amplitudeMarkMass S q u z := by
  have hlin : |u*S| ≤ 3 / 20 := by
    rw [abs_mul, abs_of_nonneg hu.1]
    have := mul_le_mul hu.2 hS (abs_nonneg S) (by norm_num : (0 : ℝ) ≤ 1 / 10)
    norm_num at this
    exact this
  have hquad : |u^2*q| ≤ 1 / 100 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg u), abs_of_nonneg hq.1]
    have hu2 : u^2 ≤ 1 / 100 := by nlinarith [hu.1, hu.2]
    nlinarith [mul_le_mul_of_nonneg_left hq.2 (sq_nonneg u)]
  have ha : |(2*bit z.1-1)*u*S| ≤ 3 / 20 := by
    simpa only [mul_assoc, abs_mul, abs_bit_sign, one_mul] using hlin
  have hb : |(2*bit z.2-1)*(-u*S+(2*bit z.1-1)*u^2*q)| ≤ 4 / 25 := by
    rw [abs_mul, abs_bit_sign, one_mul]
    have htri := abs_add_le (-u*S) ((2*bit z.1-1)*u^2*q)
    have hfirst : |-u*S| = |u*S| := by rw [neg_mul, abs_neg]
    have hsecond : |(2*bit z.1-1)*u^2*q| = |u^2*q| := by
      rw [mul_assoc, abs_mul, abs_bit_sign, one_mul]
    rw [hfirst, hsecond] at htri
    linarith
  rw [amplitudeMarkMass_factorization]
  exact mul_pos (by linarith [(abs_le.mp ha).1]) (by linarith [(abs_le.mp hb).1])

/-- The four conditional masses have unit ℓ₁ norm on the free-amplitude path.  [the theorem's stated inputs and assumptions](hyp:hq,hu), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:S,q,u,hS). -/
-- @node: amplitudeMarkMass_abs_sum
lemma amplitudeMarkMass_abs_sum (S q u : ℝ) (hS : |S| ≤ 3 / 2)
    (hq : q ∈ Icc 0 1) (hu : u ∈ Icc 0 (1 / 10)) :
    (∑ z : Bool × Bool, |amplitudeMarkMass S q u z|) = 1 := by
  simp_rw [abs_of_pos (amplitudeMarkMass_pos S q u hS hq hu _)]
  exact amplitudeMarkMass_sum S q u

/-- The Fourier coefficients bound the ℓ₁ norm of the first derivative. [The displayed conclusion](goal) follows. -/
-- @node: amplitudeMarkSlope_abs_sum_le
lemma amplitudeMarkSlope_abs_sum_le (S q u : ℝ) :
    (∑ z : Bool × Bool, |amplitudeMarkSlope S q u z|) ≤
      |S| + |3*u^2*q-1| * |S| + 2*|u| * |q - S^2| := by
  have h := markFourier_abs_sum_le 0 S ((3*u^2*q-1)*S) (2*u*(q-S^2))
  have he (z : Bool × Bool) :
      amplitudeMarkSlope S q u z =
        (0+(2*bit z.1-1)*S+(2*bit z.2-1)*((3*u^2*q-1)*S)+
          (2*bit z.1-1)*(2*bit z.2-1)*(2*u*(q-S^2)))/4 := by
    dsimp [amplitudeMarkSlope]
    ring
  simp_rw [he]
  simpa only [abs_zero, zero_add, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)] using h

/-- The Fourier coefficients bound the ℓ₁ norm of the second derivative. [The displayed conclusion](goal) follows. -/
-- @node: amplitudeMarkCurvature_abs_sum_le
lemma amplitudeMarkCurvature_abs_sum_le (S q u : ℝ) :
    (∑ z : Bool × Bool, |amplitudeMarkCurvature S q u z|) ≤
      6*|u| * |q| * |S| + 2*|q - S^2| := by
  have h := markFourier_abs_sum_le 0 0 (6*u*q*S) (2*(q-S^2))
  have he (z : Bool × Bool) :
      amplitudeMarkCurvature S q u z =
        (0+(2*bit z.1-1)*0+(2*bit z.2-1)*(6*u*q*S)+
          (2*bit z.1-1)*(2*bit z.2-1)*(2*(q-S^2)))/4 := by
    dsimp [amplitudeMarkCurvature]
    ring
  simp_rw [he]
  simpa only [abs_zero, zero_add, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)] using h

/-- The first derivative has ℓ₁ norm at most four throughout the amplitude path.  [the theorem's stated inputs and assumptions](hyp:hq,hr,hu), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:S,q,u,hS). -/
-- @node: amplitudeMarkSlope_abs_sum_le_four
lemma amplitudeMarkSlope_abs_sum_le_four (S q u : ℝ) (hS : |S| ≤ 3 / 2)
    (hq : q ∈ Icc 0 1) (hr : |q - S^2| ≤ 1) (hu : u ∈ Icc 0 (1 / 10)) :
    (∑ z : Bool × Bool, |amplitudeMarkSlope S q u z|) ≤ 4 := by
  have hu2 : u^2 ≤ 1 / 100 := by nlinarith [hu.1, hu.2]
  have hcoef : |3*u^2*q-1| ≤ 1 := by
    apply abs_le.mpr
    constructor
    · nlinarith [mul_nonneg (sq_nonneg u) hq.1]
    · nlinarith [mul_le_mul_of_nonneg_left hq.2 (sq_nonneg u)]
  have hmiddle : |3*u^2*q-1| * |S| ≤ 3 / 2 := by
    have := mul_le_mul hcoef hS (abs_nonneg S) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using this
  have hlast : 2*|u| * |q - S^2| ≤ 1 / 5 := by
    rw [abs_of_nonneg hu.1]
    nlinarith [mul_le_mul_of_nonneg_left hr hu.1]
  exact (amplitudeMarkSlope_abs_sum_le S q u).trans (by linarith)

/-- The second derivative has ℓ₁ norm at most four throughout the amplitude path.  [the theorem's stated inputs and assumptions](hyp:hq,hr,hu), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:S,q,u,hS). -/
-- @node: amplitudeMarkCurvature_abs_sum_le_four
lemma amplitudeMarkCurvature_abs_sum_le_four (S q u : ℝ) (hS : |S| ≤ 3 / 2)
    (hq : q ∈ Icc 0 1) (hr : |q - S^2| ≤ 1) (hu : u ∈ Icc 0 (1 / 10)) :
    (∑ z : Bool × Bool, |amplitudeMarkCurvature S q u z|) ≤ 4 := by
  have hprod : u*q ≤ 1 / 10 := by
    nlinarith [hu.2, mul_le_mul_of_nonneg_left hq.2 hu.1]
  have hfirst : 6*u*q*|S| ≤ 9 / 10 := by
    have := mul_le_mul hprod hS (abs_nonneg S) (by norm_num : (0 : ℝ) ≤ 1 / 10)
    nlinarith
  have h := amplitudeMarkCurvature_abs_sum_le S q u
  rw [abs_of_nonneg hu.1, abs_of_nonneg hq.1] at h
  linarith

/-- The actual perturbation and bump satisfy all coefficient bounds used by the path.  [the theorem's stated inputs and assumptions](hyp:lam,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: amplitudeMark_coefficients_valid
lemma amplitudeMark_coefficients_valid (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (lam : SignVector hL) (x : Covariate) :
    |perturbation hL lam x| ≤ 3 / 2 ∧ bump hL x ∈ Icc 0 1 ∧
      |bump hL x-(perturbation hL lam x)^2| ≤ 1 := by
  exact ⟨perturbation_abs_le_three_halves hL hhL lam x, bump_range hL x,
    (perturbation_square_residual_abs_le_bump hL hhL lam x).trans (bump_range hL x).2⟩

/-- The actual square-root separation belongs to the path's amplitude interval.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: sqrt_separation_amplitude_range
lemma sqrt_separation_amplitude_range (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4) :
    Real.sqrt (separation hL) ∈ Icc 0 (1 / 10) := by
  have ht : separation hL ≤ 1 / 16384 := by
    dsimp [separation, kappa]
    linarith [hhL.2]
  have hs := Real.sq_sqrt (separation_unit_range hL hhL).1
  exact ⟨Real.sqrt_nonneg _, by nlinarith [Real.sqrt_nonneg (separation hL)]⟩


/-- At zero amplitude each first derivative is linear in the latent perturbation.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:S,q,z). -/
-- @node: amplitudeMarkSlope_zero
lemma amplitudeMarkSlope_zero (S q : ℝ) (z : Bool × Bool) :
    amplitudeMarkSlope S q 0 z = ((2*bit z.1-1)-(2*bit z.2-1))*S/4 := by
  dsimp [amplitudeMarkSlope]
  ring

/-- Averaging the zero-amplitude derivative cancels the independent fair signs. The result uses [the stated assumptions](hyp:hL) and establishes [the displayed conclusion](goal). -/
-- @node: amplitudeMarkSlope_sign_sum_zero
lemma amplitudeMarkSlope_sign_sum_zero (hL : ℝ) (x : Covariate) (z : Bool × Bool) :
    (∑ lam : SignVector hL,
      amplitudeMarkSlope (perturbation hL lam x) (bump hL x) 0 z) = 0 := by
  simp_rw [amplitudeMarkSlope_zero]
  rw [← Finset.sum_div, ← Finset.mul_sum, perturbation_sign_sum, mul_zero, zero_div]

/-- Every free-amplitude singleton mixture is exactly the fair mark law.  [the theorem's stated inputs and assumptions](hyp:x,u,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: amplitudeMarkMass_sign_sum_exact
lemma amplitudeMarkMass_sign_sum_exact (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (x : Covariate) (u : ℝ) (z : Bool × Bool) :
    (∑ lam : SignVector hL,
      amplitudeMarkMass (perturbation hL lam x) (bump hL x) u z) =
        (Fintype.card (SignVector hL) : ℝ)/4 := by
  have hquad : (∑ lam : SignVector hL, (perturbation hL lam x)^2) =
      (Fintype.card (SignVector hL) : ℝ)*bump hL x := by
    rw [perturbation_sign_square_sum, weighted_frame_square_partition hL hhL]
  simp only [amplitudeMarkMass, ← Finset.sum_div, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_sub_distrib,
    perturbation_sign_sum, hquad, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring


/-- The finite sign mixture of component mark masses along the amplitude path. -/
-- @node: componentAmplitudeMass
def componentAmplitudeMass (hL : ℝ) (n : ℕ) (x : Fin n → Covariate)
    (C : Finset (Fin n)) (z : Marks C) (u : ℝ) : ℝ :=
  (2 : ℝ)^(-((activeSigns hL).card : ℤ)) *
    ∑ lam : SignVector hL, ∏ i : C,
      amplitudeMarkMass (perturbation hL lam (x i)) (bump hL (x i)) u (z i)

/-- The amplitude path's endpoint is precisely the existing alternative component array.  [the theorem's stated inputs and assumptions](hyp:n,x,C,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: componentAmplitudeMass_actual
lemma componentAmplitudeMass_actual (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (C : Finset (Fin n)) (z : Marks C) :
    componentAmplitudeMass hL n x C z (Real.sqrt (separation hL)) =
      alternativeMass hL n x C z := by
  simp only [componentAmplitudeMass, amplitudeMarkMass_actual hL hhL, alternativeMass]

/-- At zero amplitude the component path equals the fair component array.  [the theorem's stated inputs and assumptions](hyp:C,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,x). -/
-- @node: componentAmplitudeMass_zero
lemma componentAmplitudeMass_zero (hL : ℝ) (n : ℕ) (x : Fin n → Covariate)
    (C : Finset (Fin n)) (z : Marks C) :
    componentAmplitudeMass hL n x C z 0 = nullMass n C z := by
  simp only [componentAmplitudeMass, amplitudeMarkMass_zero, Finset.prod_const,
    Finset.card_univ, Fintype.card_coe, Finset.sum_const, nsmul_eq_mul]
  rw [← mul_assoc, sign_weight_real_normalization, one_mul]
  simp [nullMass, zpow_neg, zpow_natCast, one_div]

/-- Differentiation of the finite mixture uses the ordinary finite product rule.  [the theorem's stated inputs and assumptions](hyp:C,z,u), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,x). -/
-- @node: componentAmplitudeMass_hasDerivAt
lemma componentAmplitudeMass_hasDerivAt (hL : ℝ) (n : ℕ) (x : Fin n → Covariate)
    (C : Finset (Fin n)) (z : Marks C) (u : ℝ) :
    HasDerivAt (componentAmplitudeMass hL n x C z)
      ((2 : ℝ)^(-((activeSigns hL).card : ℤ)) *
        ∑ lam : SignVector hL, ∑ i : C,
          (∏ j ∈ (Finset.univ : Finset C).erase i,
            amplitudeMarkMass (perturbation hL lam (x j)) (bump hL (x j)) u (z j)) *
              amplitudeMarkSlope (perturbation hL lam (x i)) (bump hL (x i)) u (z i)) u := by
  classical
  have hp (lam : SignVector hL) := HasDerivAt.fun_finsetProd
    (u := (Finset.univ : Finset C))
    (fun i _ => amplitudeMarkMass_hasDerivAt (perturbation hL lam (x i))
      (bump hL (x i)) u (z i))
  have hs := (HasDerivAt.fun_sum (u := (Finset.univ : Finset (SignVector hL)))
    (fun lam _ => hp lam)).const_mul ((2 : ℝ)^(-((activeSigns hL).card : ℤ)))
  convert hs using 1 <;> rfl

/-- Independent fair signs cancel the entire component path's first derivative at zero.  [the theorem's stated inputs and assumptions](hyp:C,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,x). -/
-- @node: componentAmplitudeMass_hasDerivAt_zero
lemma componentAmplitudeMass_hasDerivAt_zero (hL : ℝ) (n : ℕ) (x : Fin n → Covariate)
    (C : Finset (Fin n)) (z : Marks C) :
    HasDerivAt (componentAmplitudeMass hL n x C z) 0 0 := by
  classical
  have h := componentAmplitudeMass_hasDerivAt hL n x C z 0
  have hz : (∑ lam : SignVector hL, ∑ i : C,
      (∏ j ∈ (Finset.univ : Finset C).erase i,
        amplitudeMarkMass (perturbation hL lam (x j)) (bump hL (x j)) 0 (z j)) *
          amplitudeMarkSlope (perturbation hL lam (x i)) (bump hL (x i)) 0 (z i)) = 0 := by
    simp_rw [amplitudeMarkMass_zero]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, amplitudeMarkSlope_sign_sum_zero, mul_zero]
    simp
  simpa only [hz, mul_zero] using h
end CausalSmith.Stat.PrivateCateRoughdesign

module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.ChiSquare
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.Duality

/-! The four marked-count intensities induced by one latent cell, together
with their elementary bounds and the pushed-forward one-cell priors. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-- The real sign attached to a latent cell: `false` is −1 and `true` is +1. -/
def latentSignValue (z : LatentCell) : ℝ :=
  if latentSign z then 1 else -1

/-- The real-valued latent sign is measurable. -/
@[fun_prop] lemma latentSignValue_measurable : Measurable latentSignValue := by
  have hs : Measurable (latentSign : LatentCell → Bool) := by
    unfold latentSign
    fun_prop
  unfold latentSignValue
  exact Measurable.ite (hs (MeasurableSet.singleton true))
    measurable_const measurable_const

/-- The exposure-`2n` marked-count intensities of one latent cell. Coordinates
`0,1` are the two control marks; coordinates `2,3` are respectively the lower
and upper treated marks. -/
noncomputable def signedScoreIntensity (kappa gamma rho : ℝ) (J : ℕ)
    (z : LatentCell) : Fin 4 → ℝ := fun i =>
  let lambda := kappa * (J : ℝ) * latentIntensity z
  if i = 0 then lambda * (1 - latentPropensity z) / 2
  else if i = 1 then lambda * (1 - latentPropensity z) / 2
  else if i = 2 then
    lambda * latentPropensity z *
      (1 / 2 - gamma * rho * latentSignValue z * latentScore z / 4)
  else
    lambda * latentPropensity z *
      (1 / 2 + gamma * rho * latentSignValue z * latentScore z / 4)

/-- The one-cell prior pushed forward to its vector of four marked-count
intensities. -/
noncomputable def signedScoreIntensityPrior (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) (h : Bool) :
    Measure (Fin 4 → ℝ) :=
  Measure.map (signedScoreIntensity kappa gamma rho J) (oneCellPrior a J D h)

lemma signedScoreIntensityPrior_eq_map (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) (h : Bool) :
    signedScoreIntensityPrior kappa gamma rho a J D h =
      Measure.map (signedScoreIntensity kappa gamma rho J)
        (oneCellPrior a J D h) := by
  rfl

/-- At the common reference atom all four marked-count intensities equal
`kappa * J`. -/
lemma signedScoreIntensity_reference (kappa gamma rho : ℝ) (J : ℕ) :
    signedScoreIntensity kappa gamma rho J referenceLatent =
      fun _ => kappa * (J : ℝ) := by
  funext i
  fin_cases i <;>
    simp [signedScoreIntensity, referenceLatent, latentIntensity,
      latentPropensity, latentScore, latentSignValue, latentSign] <;> ring

/-- Every marked-count intensity is nonnegative under the stated parameter
and latent-coordinate bounds. -/
-- keep: validity certificate that the signed-score construction defines Poisson intensities
lemma signedScoreIntensity_nonneg (kappa gamma rho : ℝ) (J : ℕ)
    (z : LatentCell) (hkappa : 0 ≤ kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (hq : latentIntensity z ∈ Icc (0 : ℝ) 4)
    (he : latentPropensity z ∈ Icc (1 / 4 : ℝ) (1 / 2))
    (hu : latentScore z ∈ Icc (0 : ℝ) 1) :
    ∀ i, 0 ≤ signedScoreIntensity kappa gamma rho J z i := by
  rcases hgamma with ⟨hgamma0, hgamma1⟩
  rcases hrho with ⟨hrho0, hrho2⟩
  rcases hq with ⟨hq0, hq4⟩
  rcases he with ⟨he4, he2⟩
  rcases hu with ⟨hu0, hu1⟩
  have hlambda : 0 ≤ kappa * (J : ℝ) * latentIntensity z := by positivity
  have hprod0 : 0 ≤ gamma * rho * latentScore z := by
    exact mul_nonneg (mul_nonneg hgamma0 hrho0) hu0
  have hprod2 : gamma * rho * latentScore z ≤ 2 := by
    calc
      gamma * rho * latentScore z ≤ 1 * 2 * 1 := by gcongr
      _ = 2 := by norm_num
  have he0 : 0 ≤ latentPropensity z := (by norm_num : (0 : ℝ) ≤ 1 / 4).trans he4
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl | rfl
  · simp [signedScoreIntensity]
    exact div_nonneg (mul_nonneg hlambda (sub_nonneg.mpr (he2.trans (by norm_num))))
      (by norm_num)
  · simp [signedScoreIntensity]
    exact div_nonneg (mul_nonneg hlambda (sub_nonneg.mpr (he2.trans (by norm_num))))
      (by norm_num)
  · by_cases hs : latentSign z
    · simp [signedScoreIntensity, latentSignValue, hs]
      exact mul_nonneg (mul_nonneg hlambda he0) (by nlinarith)
    · simp [signedScoreIntensity, latentSignValue, hs]
      exact mul_nonneg (mul_nonneg hlambda he0) (by nlinarith)
  · by_cases hs : latentSign z
    · simp [signedScoreIntensity, latentSignValue, hs]
      exact mul_nonneg (mul_nonneg hlambda he0) (by nlinarith)
    · simp [signedScoreIntensity, latentSignValue, hs]
      exact mul_nonneg (mul_nonneg hlambda he0) (by nlinarith)

/-- A zero-intensity latent atom maps to the zero intensity vector. -/
lemma signedScoreIntensity_zero (kappa gamma rho : ℝ) (J : ℕ) (h : Bool) :
    signedScoreIntensity kappa gamma rho J (zeroLatent h) = 0 := by
  funext i
  fin_cases i <;>
    simp [signedScoreIntensity, zeroLatent, latentIntensity, latentPropensity]

/-- The centered marked-count coordinate obtained from a positive tilted-side
intensity, written as an affine polynomial in that intensity. -/
private noncomputable def signedScoreCenteredCoordinatePolynomial
    (kappa gamma rho a : ℝ) (J : ℕ) (h : Bool) (s : Fin 4) : Polynomial ℝ :=
  let Lambda := kappa * (J : ℝ)
  let sign : ℝ := if h then 1 else -1
  if s = 0 then
    Polynomial.C (-Lambda - Lambda * a / 8) +
      Polynomial.C (3 * Lambda / 8) * Polynomial.X
  else if s = 1 then
    Polynomial.C (-Lambda - Lambda * a / 8) +
      Polynomial.C (3 * Lambda / 8) * Polynomial.X
  else if s = 2 then
    Polynomial.C (Lambda * a / 8 - Lambda) +
      Polynomial.C (Lambda * (1 / 8 - gamma * rho * sign / 16)) * Polynomial.X
  else
    Polynomial.C (Lambda * a / 8 - Lambda) +
      Polynomial.C (Lambda * (1 / 8 + gamma * rho * sign / 16)) * Polynomial.X

/-- Evaluation of the affine coordinate polynomial agrees with the centered
marked-count intensity away from the guarded zero input. -/
private lemma signedScoreCenteredCoordinatePolynomial_eval
    (kappa gamma rho a x : ℝ) (J : ℕ) (h : Bool) (s : Fin 4)
    (hx : x ≠ 0) (hxa : x + a ≠ 0) :
    (signedScoreCenteredCoordinatePolynomial kappa gamma rho a J h s).eval x =
      signedScoreIntensity kappa gamma rho J (latentFromIntensity h a x) s -
        kappa * (J : ℝ) := by
  fin_cases s <;> cases h <;>
    simp [signedScoreCenteredCoordinatePolynomial, signedScoreIntensity,
      latentFromIntensity, hx, latentIntensity, latentPropensity, latentScore,
      latentSignValue, latentSign] <;>
    field_simp [hx, hxa] <;> ring

private lemma affinePolynomial_natDegree_le (u v : ℝ) :
    (Polynomial.C u + Polynomial.C v * Polynomial.X).natDegree ≤ 1 := by
  calc
    _ ≤ max (Polynomial.C u).natDegree
        (Polynomial.C v * Polynomial.X).natDegree :=
      Polynomial.natDegree_add_le _ _
    _ ≤ 1 := by
      apply max_le
      · simp
      · calc
          _ ≤ (Polynomial.C v).natDegree + Polynomial.X.natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ 1 := by simp

/-- Each centered coordinate polynomial is affine. -/
private lemma signedScoreCenteredCoordinatePolynomial_natDegree_le
    (kappa gamma rho a : ℝ) (J : ℕ) (h : Bool) (s : Fin 4) :
    (signedScoreCenteredCoordinatePolynomial kappa gamma rho a J h s).natDegree ≤ 1 := by
  simp only [signedScoreCenteredCoordinatePolynomial]
  by_cases h0 : s = 0
  · rw [if_pos h0]
    exact affinePolynomial_natDegree_le _ _
  rw [if_neg h0]
  by_cases h1 : s = 1
  · rw [if_pos h1]
    exact affinePolynomial_natDegree_le _ _
  rw [if_neg h1]
  by_cases h2 : s = 2
  · rw [if_pos h2]
    exact affinePolynomial_natDegree_le _ _
  rw [if_neg h2]
  exact affinePolynomial_natDegree_le _ _

private noncomputable def signedScoreCenteredIntensityPolynomial
    (kappa gamma rho a : ℝ) (J : ℕ) (h : Bool) (alpha : Fin 4 → ℕ) :
    Polynomial ℝ :=
  ∏ s, (signedScoreCenteredCoordinatePolynomial kappa gamma rho a J h s) ^ alpha s

private lemma signedScoreCenteredIntensityPolynomial_eval_sub
    (kappa gamma rho a x : ℝ) (J : ℕ) (alpha : Fin 4 → ℕ)
    (hx : x ≠ 0) (hxa : x + a ≠ 0) :
    (signedScoreCenteredIntensityPolynomial kappa gamma rho a J true alpha -
        signedScoreCenteredIntensityPolynomial kappa gamma rho a J false alpha).eval x =
      signedScoreCenteredMonomial (kappa * (J : ℝ)) alpha
          (signedScoreIntensity kappa gamma rho J
            (latentFromIntensity true a x)) -
        signedScoreCenteredMonomial (kappa * (J : ℝ)) alpha
          (signedScoreIntensity kappa gamma rho J
            (latentFromIntensity false a x)) := by
  rw [Polynomial.eval_sub,
    signedScoreCenteredMonomial_sub_eq_telescoping]
  simp only [signedScoreCenteredIntensityPolynomial, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_pow, Fin.prod_univ_four]
  rw [signedScoreCenteredCoordinatePolynomial_eval
      kappa gamma rho a x J true 0 hx hxa,
    signedScoreCenteredCoordinatePolynomial_eval
      kappa gamma rho a x J true 1 hx hxa,
    signedScoreCenteredCoordinatePolynomial_eval
      kappa gamma rho a x J true 2 hx hxa,
    signedScoreCenteredCoordinatePolynomial_eval
      kappa gamma rho a x J true 3 hx hxa,
    signedScoreCenteredCoordinatePolynomial_eval
      kappa gamma rho a x J false 0 hx hxa,
    signedScoreCenteredCoordinatePolynomial_eval
      kappa gamma rho a x J false 1 hx hxa,
    signedScoreCenteredCoordinatePolynomial_eval
      kappa gamma rho a x J false 2 hx hxa,
    signedScoreCenteredCoordinatePolynomial_eval
      kappa gamma rho a x J false 3 hx hxa]
  ring

private lemma signedScoreCenteredCoordinatePolynomial_eval_zero_eq
    (kappa gamma rho a : ℝ) (J : ℕ) (s : Fin 4) :
    (signedScoreCenteredCoordinatePolynomial kappa gamma rho a J true s).eval 0 =
      (signedScoreCenteredCoordinatePolynomial kappa gamma rho a J false s).eval 0 := by
  fin_cases s <;> simp [signedScoreCenteredCoordinatePolynomial]

private lemma signedScoreCenteredIntensityPolynomial_eval_zero_eq
    (kappa gamma rho a : ℝ) (J : ℕ) (alpha : Fin 4 → ℕ) :
    (signedScoreCenteredIntensityPolynomial kappa gamma rho a J true alpha).eval 0 =
      (signedScoreCenteredIntensityPolynomial kappa gamma rho a J false alpha).eval 0 := by
  simp only [signedScoreCenteredIntensityPolynomial, Polynomial.eval_prod,
    Polynomial.eval_pow]
  apply Finset.prod_congr rfl
  intro s _
  rw [signedScoreCenteredCoordinatePolynomial_eval_zero_eq]

private lemma signedScoreCenteredIntensityPolynomial_natDegree_le
    (kappa gamma rho a : ℝ) (J : ℕ) (h : Bool) (alpha : Fin 4 → ℕ) :
    (signedScoreCenteredIntensityPolynomial kappa gamma rho a J h alpha).natDegree ≤
      ∑ s, alpha s := by
  calc
    _ ≤ ∑ s, ((signedScoreCenteredCoordinatePolynomial
        kappa gamma rho a J h s) ^ alpha s).natDegree := by
      simpa only [signedScoreCenteredIntensityPolynomial] using
        Polynomial.natDegree_prod_le Finset.univ
          (fun s => (signedScoreCenteredCoordinatePolynomial
            kappa gamma rho a J h s) ^ alpha s)
    _ ≤ ∑ s, alpha s := by
      apply Finset.sum_le_sum
      intro s _
      calc
        _ ≤ alpha s *
            (signedScoreCenteredCoordinatePolynomial
              kappa gamma rho a J h s).natDegree := Polynomial.natDegree_pow_le
        _ ≤ alpha s * 1 := Nat.mul_le_mul_left _
          (signedScoreCenteredCoordinatePolynomial_natDegree_le
            kappa gamma rho a J h s)
        _ = alpha s := Nat.mul_one _

/-- Through matching degree `3J`, the true/false centered monomial difference
on the tilted support is intensity times a polynomial of strictly smaller
degree. -/
lemma signedScoreCenteredMonomial_latentFromIntensity_sign_sub_factor
    (kappa gamma rho a : ℝ) (J : ℕ) (alpha : Fin 4 → ℕ)
    (ha : 0 < a) (hpositive : 1 ≤ ∑ s, alpha s)
    (hdegree : (∑ s, alpha s) ≤ 3 * J) :
    ∃ p : Polynomial ℝ, p.natDegree < ∑ s, alpha s ∧
      ∀ x, x = 0 ∨ x ∈ Icc a 1 →
        signedScoreCenteredMonomial (kappa * (J : ℝ)) alpha
            (signedScoreIntensity kappa gamma rho J
              (latentFromIntensity true a x)) -
          signedScoreCenteredMonomial (kappa * (J : ℝ)) alpha
            (signedScoreIntensity kappa gamma rho J
              (latentFromIntensity false a x)) = x * p.eval x := by
  let qtrue := signedScoreCenteredIntensityPolynomial
    kappa gamma rho a J true alpha
  let qfalse := signedScoreCenteredIntensityPolynomial
    kappa gamma rho a J false alpha
  have hcoeff : (qtrue - qfalse).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_sub]
    exact sub_eq_zero.mpr
      (signedScoreCenteredIntensityPolynomial_eval_zero_eq
        kappa gamma rho a J alpha)
  obtain ⟨p, hp⟩ := Polynomial.X_dvd_iff.mpr hcoeff
  have hpdegree : p.natDegree < ∑ s, alpha s := by
    by_cases hp0 : p = 0
    · simp only [hp0, Polynomial.natDegree_zero]
      exact lt_of_lt_of_le Nat.zero_lt_one hpositive
    have hX0 : (Polynomial.X : Polynomial ℝ) ≠ 0 := Polynomial.X_ne_zero
    have hproddegree : (Polynomial.X * p).natDegree = 1 + p.natDegree := by
      rw [Polynomial.natDegree_mul hX0 hp0, Polynomial.natDegree_X]
    have hqdegree : (qtrue - qfalse).natDegree ≤ ∑ s, alpha s := by
      refine (Polynomial.natDegree_sub_le qtrue qfalse).trans ?_
      apply max_le
      · exact signedScoreCenteredIntensityPolynomial_natDegree_le
          kappa gamma rho a J true alpha
      · exact signedScoreCenteredIntensityPolynomial_natDegree_le
          kappa gamma rho a J false alpha
    rw [hp] at hqdegree
    rw [hproddegree] at hqdegree
    omega
  refine ⟨p, hpdegree, ?_⟩
  intro x hx
  rcases hx with rfl | hx
  · rw [show latentFromIntensity true a 0 = zeroLatent true by
          simp [latentFromIntensity],
        show latentFromIntensity false a 0 = zeroLatent false by
          simp [latentFromIntensity],
        signedScoreIntensity_zero, signedScoreIntensity_zero]
    simp
  have hx0 : x ≠ 0 := (ha.trans_le hx.1).ne'
  have hxa : x + a ≠ 0 := (add_pos (ha.trans_le hx.1) ha).ne'
  rw [← signedScoreCenteredIntensityPolynomial_eval_sub
      kappa gamma rho a x J alpha hx0 hxa]
  have heval := congrArg (Polynomial.eval x) hp
  simpa [qtrue, qfalse] using heval

/-- Tilting a dual side by `a / x` shifts every positive algebraic moment down
by one degree and multiplies it by `a`. -/
lemma tiltedSide_succ_moment (a : ℝ) (J j : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) (h : Bool)
    (ha : 0 < a) :
    (∫ x, x ^ (j + 1) ∂tiltedSide a J D h) =
      a * ∫ x, x ^ j ∂dualSide a J D h := by
  classical
  let w : Fin (3 * J + 2) → ℝ := fun i =>
    2 * (if h then max (D.weights i) 0 else max (-D.weights i) 0)
  have hw (i : Fin (3 * J + 2)) : 0 ≤ w i := by
    dsimp [w]
    split <;> positivity
  have hx (i : Fin (3 * J + 2)) : 0 < D.nodes i :=
    ha.trans_le (D.nodes_mem i).1
  have hintTilt (i : Fin (3 * J + 2)) :
      Integrable (fun x : ℝ => x ^ (j + 1))
        (ENNReal.ofReal (w i * a / D.nodes i) • Measure.dirac (D.nodes i)) :=
    (integrable_dirac (by finiteness)).smul_measure (by simp)
  have hintZero : Integrable (fun x : ℝ => x ^ (j + 1))
      (ENNReal.ofReal (1 - ∑ i, w i * a / D.nodes i) • Measure.dirac 0) :=
    (integrable_dirac (by finiteness)).smul_measure (by simp)
  have hintDual (i : Fin (3 * J + 2)) :
      Integrable (fun x : ℝ => x ^ j)
        (ENNReal.ofReal (w i) • Measure.dirac (D.nodes i)) :=
    (integrable_dirac (by finiteness)).smul_measure (by simp)
  rw [tiltedSide, dualSide]
  change (∫ x, x ^ (j + 1) ∂((
      ∑ i, ENNReal.ofReal (w i * a / D.nodes i) • Measure.dirac (D.nodes i)) +
        ENNReal.ofReal (1 - ∑ i, w i * a / D.nodes i) • Measure.dirac 0)) =
    a * ∫ x, x ^ j ∂∑ i, ENNReal.ofReal (w i) • Measure.dirac (D.nodes i)
  rw [integral_add_measure
      (integrable_finsetSum_measure.2 fun i _ => hintTilt i) hintZero,
    integral_finsetSum_measure (fun i _ => hintTilt i),
    integral_finsetSum_measure (fun i _ => hintDual i)]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (hw _), zero_pow (Nat.succ_ne_zero j), mul_zero, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.toReal_ofReal (div_nonneg (mul_nonneg (hw i) ha.le) (hx i).le)]
  field_simp [(hx i).ne']
  ring

private lemma tiltedSide_integrable_pow (a : ℝ) (J m : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) (h : Bool) :
    Integrable (fun x : ℝ => x ^ m) (tiltedSide a J D h) := by
  classical
  rw [tiltedSide]
  apply Integrable.add_measure
  · apply integrable_finsetSum_measure.2
    intro i _
    exact (integrable_dirac (by finiteness)).smul_measure (by simp)
  · exact (integrable_dirac (by finiteness)).smul_measure (by simp)

/-- Multiplication by the intensity transports a polynomial expectation under
the tilted sides to matched moments of the original dual sides. -/
lemma tiltedSide_mul_polynomial_eval_integral_eq (a : ℝ) (J r : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (p : Polynomial ℝ) (ha : 0 < a) (hp : p.natDegree < r)
    (hr : r ≤ 3 * J) :
    (∫ x, x * p.eval x ∂tiltedSide a J D true) =
      ∫ x, x * p.eval x ∂tiltedSide a J D false := by
  classical
  have hfun : (fun x : ℝ => x * p.eval x) =
      fun x => ∑ i ∈ Finset.range (p.natDegree + 1),
        p.coeff i * x ^ (i + 1) := by
    funext x
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
  rw [hfun,
    integral_finset_sum (Finset.range (p.natDegree + 1)) (fun i _ =>
      (tiltedSide_integrable_pow a J (i + 1) D true).const_mul (p.coeff i)),
    integral_finset_sum (Finset.range (p.natDegree + 1)) (fun i _ =>
      (tiltedSide_integrable_pow a J (i + 1) D false).const_mul (p.coeff i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, integral_const_mul,
    tiltedSide_succ_moment a J i D true ha,
    tiltedSide_succ_moment a J i D false ha,
    dualSide_moments_eq a J D i]
  exact le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    (le_trans (Nat.le_of_lt hp) hr)

/-- Every intensity obtained from the positive part of the tilted support lies
between zero and the reference intensity `kappa * J`. -/
lemma signedScoreIntensity_latentFromIntensity_mem_Icc
    (kappa gamma rho a x : ℝ) (J : ℕ) (s : Bool)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hrho : rho ∈ Icc (0 : ℝ) 2) (ha : 0 < a) (hx : x ∈ Icc a 1) :
    ∀ i, signedScoreIntensity kappa gamma rho J
      (latentFromIntensity s a x) i ∈ Icc 0 (kappa * (J : ℝ)) := by
  rcases hgamma with ⟨hgamma0, hgamma1⟩
  rcases hrho with ⟨hrho0, hrho2⟩
  rcases hx with ⟨hax, hx1⟩
  have hx0 : 0 < x := ha.trans_le hax
  have hxa : 0 < x + a := add_pos hx0 ha
  have hK : 0 ≤ kappa * (J : ℝ) := by positivity
  have hgr0 : 0 ≤ gamma * rho := mul_nonneg hgamma0 hrho0
  have hgr2 : gamma * rho ≤ 2 := by
    calc
      gamma * rho ≤ 1 * 2 := mul_le_mul hgamma1 hrho2 hrho0 (by norm_num)
      _ = 2 := by norm_num
  have hgrx0 : 0 ≤ gamma * rho * x := mul_nonneg hgr0 hx0.le
  have hgrx2 : gamma * rho * x ≤ 2 * x :=
    mul_le_mul_of_nonneg_right hgr2 hx0.le
  have hcontrol :
      kappa * (J : ℝ) * x * (1 - (1 / 4 + a / (4 * x))) / 2 =
        (kappa * (J : ℝ)) * ((3 * x - a) / 8) := by
    field_simp [hx0.ne']
    <;> ring
  have htminus :
      kappa * (J : ℝ) * x * (1 / 4 + a / (4 * x)) *
          (1 / 2 - gamma * rho * (x / (x + a)) / 4) =
        (kappa * (J : ℝ)) * ((x + a) / 8 - gamma * rho * x / 16) := by
    field_simp [hx0.ne', hxa.ne']
    <;> ring
  have htplus :
      kappa * (J : ℝ) * x * (1 / 4 + a / (4 * x)) *
          (1 / 2 + gamma * rho * (x / (x + a)) / 4) =
        (kappa * (J : ℝ)) * ((x + a) / 8 + gamma * rho * x / 16) := by
    field_simp [hx0.ne', hxa.ne']
    <;> ring
  have hc0 : 0 ≤ (3 * x - a) / 8 := by nlinarith
  have hc1 : (3 * x - a) / 8 ≤ 1 := by nlinarith
  have hm0 : 0 ≤ (x + a) / 8 - gamma * rho * x / 16 := by nlinarith
  have hm1 : (x + a) / 8 - gamma * rho * x / 16 ≤ 1 := by nlinarith
  have hp0 : 0 ≤ (x + a) / 8 + gamma * rho * x / 16 := by nlinarith
  have hp1 : (x + a) / 8 + gamma * rho * x / 16 ≤ 1 := by nlinarith
  intro i
  fin_cases i
  · have hv : signedScoreIntensity kappa gamma rho J
        (latentFromIntensity s a x) 0 =
          (kappa * (J : ℝ)) * ((3 * x - a) / 8) := by
      simpa [signedScoreIntensity, latentFromIntensity, hx0.ne', latentIntensity,
        latentPropensity] using hcontrol
    have hb : (kappa * (J : ℝ)) * ((3 * x - a) / 8) ∈
        Icc 0 (kappa * (J : ℝ)) := ⟨mul_nonneg hK hc0, by
      simpa using mul_le_mul_of_nonneg_left hc1 hK⟩
    have hz : signedScoreIntensity kappa gamma rho J
        (latentFromIntensity s a x) 0 ∈ Icc 0 (kappa * (J : ℝ)) := by
      rw [hv]
      exact hb
    simpa using hz
  · have hv : signedScoreIntensity kappa gamma rho J
        (latentFromIntensity s a x) 1 =
          (kappa * (J : ℝ)) * ((3 * x - a) / 8) := by
      simpa [signedScoreIntensity, latentFromIntensity, hx0.ne', latentIntensity,
        latentPropensity] using hcontrol
    have hb : (kappa * (J : ℝ)) * ((3 * x - a) / 8) ∈
        Icc 0 (kappa * (J : ℝ)) := ⟨mul_nonneg hK hc0, by
      simpa using mul_le_mul_of_nonneg_left hc1 hK⟩
    have hz : signedScoreIntensity kappa gamma rho J
        (latentFromIntensity s a x) 1 ∈ Icc 0 (kappa * (J : ℝ)) := by
      rw [hv]
      exact hb
    simpa using hz
  · cases s
    · have hv : signedScoreIntensity kappa gamma rho J
          (latentFromIntensity false a x) 2 =
            (kappa * (J : ℝ)) * ((x + a) / 8 + gamma * rho * x / 16) := by
        simp [signedScoreIntensity, latentFromIntensity, hx0.ne', latentIntensity,
          latentPropensity, latentScore, latentSignValue, latentSign]
        field_simp [hx0.ne', hxa.ne']
        <;> ring
      have hb : (kappa * (J : ℝ)) *
          ((x + a) / 8 + gamma * rho * x / 16) ∈
          Icc 0 (kappa * (J : ℝ)) := ⟨mul_nonneg hK hp0, by
        simpa using mul_le_mul_of_nonneg_left hp1 hK⟩
      have hz : signedScoreIntensity kappa gamma rho J
          (latentFromIntensity false a x) 2 ∈ Icc 0 (kappa * (J : ℝ)) := by
        rw [hv]
        exact hb
      simpa using hz
    · have hv : signedScoreIntensity kappa gamma rho J
          (latentFromIntensity true a x) 2 =
            (kappa * (J : ℝ)) * ((x + a) / 8 - gamma * rho * x / 16) := by
        simp [signedScoreIntensity, latentFromIntensity, hx0.ne', latentIntensity,
          latentPropensity, latentScore, latentSignValue, latentSign]
        field_simp [hx0.ne', hxa.ne']
        <;> ring
      have hb : (kappa * (J : ℝ)) *
          ((x + a) / 8 - gamma * rho * x / 16) ∈
          Icc 0 (kappa * (J : ℝ)) := ⟨mul_nonneg hK hm0, by
        simpa using mul_le_mul_of_nonneg_left hm1 hK⟩
      have hz : signedScoreIntensity kappa gamma rho J
          (latentFromIntensity true a x) 2 ∈ Icc 0 (kappa * (J : ℝ)) := by
        rw [hv]
        exact hb
      simpa using hz
  · cases s
    · have hv : signedScoreIntensity kappa gamma rho J
          (latentFromIntensity false a x) 3 =
            (kappa * (J : ℝ)) * ((x + a) / 8 - gamma * rho * x / 16) := by
        simp [signedScoreIntensity, latentFromIntensity, hx0.ne', latentIntensity,
          latentPropensity, latentScore, latentSignValue, latentSign]
        field_simp [hx0.ne', hxa.ne']
        <;> ring
      have hb : (kappa * (J : ℝ)) *
          ((x + a) / 8 - gamma * rho * x / 16) ∈
          Icc 0 (kappa * (J : ℝ)) := ⟨mul_nonneg hK hm0, by
        simpa using mul_le_mul_of_nonneg_left hm1 hK⟩
      have hz : signedScoreIntensity kappa gamma rho J
          (latentFromIntensity false a x) 3 ∈ Icc 0 (kappa * (J : ℝ)) := by
        rw [hv]
        exact hb
      simpa using hz
    · have hv : signedScoreIntensity kappa gamma rho J
          (latentFromIntensity true a x) 3 =
            (kappa * (J : ℝ)) * ((x + a) / 8 + gamma * rho * x / 16) := by
        simp [signedScoreIntensity, latentFromIntensity, hx0.ne', latentIntensity,
          latentPropensity, latentScore, latentSignValue, latentSign]
        field_simp [hx0.ne', hxa.ne']
        <;> ring
      have hb : (kappa * (J : ℝ)) *
          ((x + a) / 8 + gamma * rho * x / 16) ∈
          Icc 0 (kappa * (J : ℝ)) := ⟨mul_nonneg hK hp0, by
        simpa using mul_le_mul_of_nonneg_left hp1 hK⟩
      have hz : signedScoreIntensity kappa gamma rho J
          (latentFromIntensity true a x) 3 ∈ Icc 0 (kappa * (J : ℝ)) := by
        rw [hv]
        exact hb
      simpa using hz

/-- The marked-count intensity map is measurable. -/
@[fun_prop] lemma signedScoreIntensity_measurable (kappa gamma rho : ℝ) (J : ℕ) :
    Measurable (signedScoreIntensity kappa gamma rho J) := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;>
    simp [signedScoreIntensity, latentIntensity,
      latentPropensity, latentScore] <;> fun_prop

/-- The pushed-forward intensity prior retains the reference atom with its
original weight `1 / J`. -/
lemma signedScoreIntensityPrior_reference_le
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) (h : Bool) :
    ENNReal.ofReal (1 / (J : ℝ)) •
        Measure.dirac (fun _ : Fin 4 => kappa * (J : ℝ)) ≤
      signedScoreIntensityPrior kappa gamma rho a J D h := by
  rw [signedScoreIntensityPrior, oneCellPrior,
    Measure.map_add _ _ (signedScoreIntensity_measurable kappa gamma rho J),
    Measure.map_smul, Measure.map_dirac,
    signedScoreIntensity_reference]
  exact Measure.le_add_right le_rfl

/-- The pushed-forward one-cell prior is concentrated on nonnegative
intensity vectors. -/
lemma signedScoreIntensityPrior_ae_nonneg
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) (h : Bool)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hrho : rho ∈ Icc (0 : ℝ) 2) (ha : 0 < a) :
    ∀ᵐ v ∂signedScoreIntensityPrior kappa gamma rho a J D h,
      ∀ i, 0 ≤ v i := by
  have hout : MeasurableSet {v : Fin 4 → ℝ | ∀ i, 0 ≤ v i} := by
    measurability
  have hgood : MeasurableSet {z : LatentCell |
      ∀ i, 0 ≤ signedScoreIntensity kappa gamma rho J z i} := by
    measurability
  rw [signedScoreIntensityPrior,
    ae_map_iff (signedScoreIntensity_measurable kappa gamma rho J).aemeasurable
      hout,
    oneCellPrior, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    rw [ae_dirac_iff hgood]
    intro i
    rw [signedScoreIntensity_reference]
    positivity
  · apply Measure.ae_smul_measure
    rw [ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      rw [ae_map_iff (latentFromIntensity_measurable false a).aemeasurable hgood]
      filter_upwards [tiltedSide_ae_zero_or_mem_interval a J D (!h)] with x hx
      rcases hx with rfl | hx
      · intro i
        rw [show latentFromIntensity false a 0 = zeroLatent false by
          simp [latentFromIntensity], signedScoreIntensity_zero]
        exact le_rfl
      · exact fun i =>
          (signedScoreIntensity_latentFromIntensity_mem_Icc
            kappa gamma rho a x J false hkappa hgamma hrho ha hx i).1
    · apply Measure.ae_smul_measure
      rw [ae_map_iff (latentFromIntensity_measurable true a).aemeasurable hgood]
      filter_upwards [tiltedSide_ae_zero_or_mem_interval a J D h] with x hx
      rcases hx with rfl | hx
      · intro i
        rw [show latentFromIntensity true a 0 = zeroLatent true by
          simp [latentFromIntensity], signedScoreIntensity_zero]
        exact le_rfl
      · exact fun i =>
          (signedScoreIntensity_latentFromIntensity_mem_Icc
            kappa gamma rho a x J true hkappa hgamma hrho ha hx i).1

/-- Pushing a one-cell probability prior through the marked-count intensity
map again gives a probability measure. -/
lemma signedScoreIntensityPrior_isProbabilityMeasure
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) (h : Bool)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    IsProbabilityMeasure (signedScoreIntensityPrior kappa gamma rho a J D h) := by
  let := oneCellPrior_isProbabilityMeasure a J D h ha hJ
  exact Measure.isProbabilityMeasure_map
    (signedScoreIntensity_measurable kappa gamma rho J).aemeasurable

private lemma tiltedSide_integrable_of_atomic (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) (h : Bool)
    (f : ℝ → ℝ) : Integrable f (tiltedSide a J D h) := by
  classical
  rw [tiltedSide]
  apply Integrable.add_measure
  · apply integrable_finsetSum_measure.2
    intro i _
    exact (integrable_dirac (by finiteness)).smul_measure (by simp)
  · exact (integrable_dirac (by finiteness)).smul_measure (by simp)

private lemma signedScoreLikelihood_comp_integrable_oneCellPrior
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (z : SignedScoreCounts) :
    Integrable (fun u => signedScoreLikelihood (kappa * (J : ℝ))
      (signedScoreIntensity kappa gamma rho J u) z)
      (oneCellPrior a J D h) := by
  let f := fun u => signedScoreLikelihood (kappa * (J : ℝ))
    (signedScoreIntensity kappa gamma rho J u) z
  have hf : StronglyMeasurable f :=
    (signedScoreLikelihood_stronglyMeasurable_intensity
      (kappa * (J : ℝ)) z).comp_measurable
        (signedScoreIntensity_measurable kappa gamma rho J)
  have hmap (s t : Bool) : Integrable f
      (Measure.map (latentFromIntensity s a) (tiltedSide a J D t)) := by
    rw [integrable_map_measure hf.aestronglyMeasurable
      (latentFromIntensity_measurable s a).aemeasurable]
    exact tiltedSide_integrable_of_atomic a J D t (f ∘ latentFromIntensity s a)
  rw [oneCellPrior]
  apply Integrable.add_measure
  · exact (integrable_dirac (by finiteness)).smul_measure (by simp)
  · apply Integrable.smul_measure
    · apply Integrable.add_measure
      · exact (hmap false (!h)).smul_measure (by simp)
      · exact (hmap true h).smul_measure (by simp)
    · simp

/-- Each four-count likelihood is integrable under either pushed-forward
one-cell intensity prior. -/
lemma signedScoreLikelihood_integrable_intensityPrior
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (z : SignedScoreCounts) :
    Integrable (fun v => signedScoreLikelihood (kappa * (J : ℝ)) v z)
      (signedScoreIntensityPrior kappa gamma rho a J D h) := by
  rw [signedScoreIntensityPrior,
    integrable_map_measure
      (signedScoreLikelihood_stronglyMeasurable_intensity
        (kappa * (J : ℝ)) z).aestronglyMeasurable
      (signedScoreIntensity_measurable kappa gamma rho J).aemeasurable]
  exact signedScoreLikelihood_comp_integrable_oneCellPrior
    kappa gamma rho a J D h z

/-- The prior-predictive likelihood is pointwise bounded below by the exact
ENNReal-to-real weight of the retained reference atom. -/
lemma signedScoreMixtureLikelihood_intensityPrior_lower_bound
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (z : SignedScoreCounts) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    (ENNReal.ofReal (1 / (J : ℝ))).toReal ≤
      signedScoreMixtureLikelihood (kappa * (J : ℝ))
        (signedScoreIntensityPrior kappa gamma rho a J D h) z := by
  let pi := signedScoreIntensityPrior kappa gamma rho a J D h
  let f := fun v : Fin 4 → ℝ =>
    signedScoreLikelihood (kappa * (J : ℝ)) v z
  have hLambda : 0 < kappa * (J : ℝ) := by positivity
  have hnonneg : 0 ≤ᵐ[pi] f := by
    filter_upwards [signedScoreIntensityPrior_ae_nonneg
      kappa gamma rho a J D h hkappa.le hgamma hrho ha] with v hv
    exact signedScoreLikelihood_nonneg (kappa * (J : ℝ)) v z hLambda hv
  have hint : Integrable f pi :=
    signedScoreLikelihood_integrable_intensityPrior
      kappa gamma rho a J D h z
  have hmono := integral_mono_measure
    (signedScoreIntensityPrior_reference_le kappa gamma rho a J D h)
    hnonneg hint
  rw [signedScoreMixtureLikelihood_eq_integral]
  simpa only [integral_smul_measure, integral_dirac,
    signedScoreLikelihood_reference _ hLambda z, smul_eq_mul, mul_one, pi, f]
    using hmono

/-- The signed-score Poisson kernel is almost-everywhere measurable under
either concrete intensity prior. -/
lemma signedScorePoissonLaw_aemeasurable_intensityPrior
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    AEMeasurable signedScorePoissonLaw
      (signedScoreIntensityPrior kappa gamma rho a J D h) := by
  let Lambda := kappa * (J : ℝ)
  let Q := signedScoreReferenceLaw Lambda
  let K : (Fin 4 → ℝ) → Measure SignedScoreCounts := fun v =>
    Q.withDensity (fun z => ENNReal.ofReal
      (signedScoreLikelihood Lambda v z))
  have hK : Measurable K := by
    apply measurable_withDensity
    exact (signedScoreLikelihood_joint_measurable Lambda).ennreal_ofReal
  have heq : signedScorePoissonLaw =ᵐ[
      signedScoreIntensityPrior kappa gamma rho a J D h] K := by
    filter_upwards [signedScoreIntensityPrior_ae_nonneg
      kappa gamma rho a J D h hkappa.le hgamma hrho ha] with v hv
    exact signedScorePoissonLaw_eq_withDensity Lambda v (by positivity) hv
  exact hK.aemeasurable.congr heq.symm

/-- Either concrete intensity-prior predictive law is a probability measure. -/
lemma signedScoreMixtureLaw_intensityPrior_isProbabilityMeasure
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    IsProbabilityMeasure (signedScoreMixtureLaw
      (signedScoreIntensityPrior kappa gamma rho a J D h)) := by
  letI : IsProbabilityMeasure
      (signedScoreIntensityPrior kappa gamma rho a J D h) :=
    signedScoreIntensityPrior_isProbabilityMeasure
      kappa gamma rho a J D h ha hJ
  exact signedScoreMixtureLaw_isProbabilityMeasure _
    (signedScorePoissonLaw_aemeasurable_intensityPrior
      kappa gamma rho a J D h hkappa hgamma hrho ha hJ)

/-- The one-cell prior predictive law has its mixture likelihood as density
with respect to the common reference count law. -/
lemma signedScoreMixtureLaw_intensityPrior_eq_withDensity
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    signedScoreMixtureLaw
        (signedScoreIntensityPrior kappa gamma rho a J D h) =
      (signedScoreReferenceLaw (kappa * (J : ℝ))).withDensity
        (fun z => ENNReal.ofReal
          (signedScoreMixtureLikelihood (kappa * (J : ℝ))
            (signedScoreIntensityPrior kappa gamma rho a J D h) z)) := by
  apply signedScoreMixtureLaw_eq_withDensity
  · positivity
  · exact signedScorePoissonLaw_aemeasurable_intensityPrior
      kappa gamma rho a J D h hkappa hgamma hrho ha hJ
  · exact signedScoreIntensityPrior_ae_nonneg
      kappa gamma rho a J D h hkappa.le hgamma hrho ha
  · exact signedScoreLikelihood_integrable_intensityPrior
      kappa gamma rho a J D h

/-- The predictive law retains at least the reference-law mass contributed by
the common prior atom. -/
lemma signedScoreMixtureLaw_intensityPrior_reference_le
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    ENNReal.ofReal (1 / (J : ℝ)) •
        signedScoreReferenceLaw (kappa * (J : ℝ)) ≤
      signedScoreMixtureLaw
        (signedScoreIntensityPrior kappa gamma rho a J D h) := by
  rw [signedScoreMixtureLaw_intensityPrior_eq_withDensity
    kappa gamma rho a J D h hkappa hgamma hrho ha hJ,
    ← withDensity_const]
  apply withDensity_mono
  filter_upwards [] with z
  apply ENNReal.ofReal_le_ofReal
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (J : ℝ))] using
    signedScoreMixtureLikelihood_intensityPrior_lower_bound
      kappa gamma rho a J D h z hkappa hgamma hrho ha hJ

/-- The reference count law is absolutely continuous with respect to either
one-cell prior predictive law. -/
lemma signedScoreReferenceLaw_absolutelyContinuous_intensityPrior
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    signedScoreReferenceLaw (kappa * (J : ℝ)) ≪
      signedScoreMixtureLaw
        (signedScoreIntensityPrior kappa gamma rho a J D h) := by
  let c := ENNReal.ofReal (1 / (J : ℝ))
  have hc : c ≠ 0 := by positivity
  have hQscaled : signedScoreReferenceLaw (kappa * (J : ℝ)) ≪
      c • signedScoreReferenceLaw (kappa * (J : ℝ)) :=
    (Measure.AbsolutelyContinuous.rfl).smul_right hc
  exact hQscaled.trans (Measure.absolutelyContinuous_of_le
    (signedScoreMixtureLaw_intensityPrior_reference_le
      kappa gamma rho a J D h hkappa hgamma hrho ha hJ))

/-- The true one-cell predictive law is absolutely continuous with respect to
the false one-cell predictive law. -/
lemma signedScoreMixtureLaw_intensityPrior_absolutelyContinuous
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (hkappa : 0 < kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hrho : rho ∈ Icc (0 : ℝ) 2) (ha : 0 < a) (hJ : 1 ≤ J) :
    signedScoreMixtureLaw
        (signedScoreIntensityPrior kappa gamma rho a J D true) ≪
      signedScoreMixtureLaw
        (signedScoreIntensityPrior kappa gamma rho a J D false) := by
  have htrue : signedScoreMixtureLaw
      (signedScoreIntensityPrior kappa gamma rho a J D true) ≪
      signedScoreReferenceLaw (kappa * (J : ℝ)) := by
    rw [signedScoreMixtureLaw_intensityPrior_eq_withDensity
      kappa gamma rho a J D true hkappa hgamma hrho ha hJ]
    exact withDensity_absolutelyContinuous _ _
  exact htrue.trans
    (signedScoreReferenceLaw_absolutelyContinuous_intensityPrior
      kappa gamma rho a J D false hkappa hgamma hrho ha hJ)

/-- The retained reference atom makes either predictive density strictly
positive.  This is the nonvanishing premise needed to divide densities in
`Measure.rnDeriv_withDensity_right`. -/
lemma signedScoreMixtureLikelihood_intensityPrior_ofReal_ne_zero
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (z : SignedScoreCounts)
    (hkappa : 0 < kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hrho : rho ∈ Icc (0 : ℝ) 2) (ha : 0 < a) (hJ : 1 ≤ J) :
    ENNReal.ofReal (signedScoreMixtureLikelihood (kappa * (J : ℝ))
      (signedScoreIntensityPrior kappa gamma rho a J D h) z) ≠ 0 := by
  apply ne_of_gt
  rw [ENNReal.ofReal_pos]
  have hlower := signedScoreMixtureLikelihood_intensityPrior_lower_bound
    kappa gamma rho a J D h z hkappa hgamma hrho ha hJ
  have hJpos : (0 : ℝ) < J := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hJ)
  have hweight : 0 < (ENNReal.ofReal (1 / (J : ℝ))).toReal := by
    rw [ENNReal.toReal_ofReal (one_div_pos.mpr hJpos).le]
    exact one_div_pos.mpr hJpos
  exact lt_of_lt_of_le hweight hlower

/-- The predictive likelihood quotient is the Radon--Nikodym derivative of
the true one-cell mixture with respect to the false mixture, expressed under
their common reference law. -/
lemma signedScoreMixtureLaw_intensityPrior_rnDeriv_eq
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (hkappa : 0 < kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hrho : rho ∈ Icc (0 : ℝ) 2) (ha : 0 < a) (hJ : 1 ≤ J) :
    (signedScoreMixtureLaw
        (signedScoreIntensityPrior kappa gamma rho a J D true)).rnDeriv
        (signedScoreMixtureLaw
          (signedScoreIntensityPrior kappa gamma rho a J D false)) =ᵐ[
      signedScoreReferenceLaw (kappa * (J : ℝ))]
      fun z =>
        (ENNReal.ofReal (signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D false) z))⁻¹ *
        ENNReal.ofReal (signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D true) z) := by
  let Q := signedScoreReferenceLaw (kappa * (J : ℝ))
  let LT := signedScoreMixtureLikelihood (kappa * (J : ℝ))
    (signedScoreIntensityPrior kappa gamma rho a J D true)
  let LF := signedScoreMixtureLikelihood (kappa * (J : ℝ))
    (signedScoreIntensityPrior kappa gamma rho a J D false)
  let fT : SignedScoreCounts → ENNReal := fun z => ENNReal.ofReal (LT z)
  let fF : SignedScoreCounts → ENNReal := fun z => ENNReal.ofReal (LF z)
  have hmeasT : Measurable fT :=
    (signedScoreMixtureLikelihood_measurable _ _).ennreal_ofReal
  have hmeasF : Measurable fF :=
    (signedScoreMixtureLikelihood_measurable _ _).ennreal_ofReal
  have hF_ne_zero : ∀ᵐ z ∂Q, fF z ≠ 0 := by
    filter_upwards [] with z
    exact signedScoreMixtureLikelihood_intensityPrior_ofReal_ne_zero
      kappa gamma rho a J D false z hkappa hgamma hrho ha hJ
  have hF_ne_top : ∀ᵐ z ∂Q, fF z ≠ ⊤ := by
    filter_upwards [] with z
    exact ENNReal.ofReal_ne_top
  rw [signedScoreMixtureLaw_intensityPrior_eq_withDensity
      kappa gamma rho a J D true hkappa hgamma hrho ha hJ,
    signedScoreMixtureLaw_intensityPrior_eq_withDensity
      kappa gamma rho a J D false hkappa hgamma hrho ha hJ]
  have hright := Measure.rnDeriv_withDensity_right_of_absolutelyContinuous
    (withDensity_absolutelyContinuous Q fT) hmeasF.aemeasurable
      hF_ne_zero hF_ne_top
  have hleft := Measure.rnDeriv_withDensity Q hmeasT
  filter_upwards [hright, hleft] with z hzright hzleft
  rw [hzright, hzleft]

/-- Real-valued form of the preceding Radon--Nikodym identity, now stated
almost everywhere under the false predictive law, which is the integration
measure in `chiSqDiv`. -/
lemma signedScoreMixtureLaw_intensityPrior_rnDeriv_toReal_eq
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (hkappa : 0 < kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hrho : rho ∈ Icc (0 : ℝ) 2) (ha : 0 < a) (hJ : 1 ≤ J) :
    (fun z => ((signedScoreMixtureLaw
        (signedScoreIntensityPrior kappa gamma rho a J D true)).rnDeriv
        (signedScoreMixtureLaw
          (signedScoreIntensityPrior kappa gamma rho a J D false)) z).toReal) =ᵐ[
      signedScoreMixtureLaw
        (signedScoreIntensityPrior kappa gamma rho a J D false)]
      fun z =>
        signedScoreMixtureLikelihood (kappa * (J : ℝ))
            (signedScoreIntensityPrior kappa gamma rho a J D true) z /
          signedScoreMixtureLikelihood (kappa * (J : ℝ))
            (signedScoreIntensityPrior kappa gamma rho a J D false) z := by
  let Q := signedScoreReferenceLaw (kappa * (J : ℝ))
  let piT := signedScoreIntensityPrior kappa gamma rho a J D true
  let piF := signedScoreIntensityPrior kappa gamma rho a J D false
  let LT := signedScoreMixtureLikelihood (kappa * (J : ℝ)) piT
  let LF := signedScoreMixtureLikelihood (kappa * (J : ℝ)) piF
  have hfalseQ : signedScoreMixtureLaw piF ≪ Q := by
    rw [signedScoreMixtureLaw_intensityPrior_eq_withDensity
      kappa gamma rho a J D false hkappa hgamma hrho ha hJ]
    exact withDensity_absolutelyContinuous _ _
  have hrnQ := signedScoreMixtureLaw_intensityPrior_rnDeriv_eq
    kappa gamma rho a J D hkappa hgamma hrho ha hJ
  have hrnF := hfalseQ.ae_eq hrnQ
  filter_upwards [hrnF] with z hz
  have hT0 : 0 ≤ LT z := signedScoreMixtureLikelihood_nonneg _ _ _ (by positivity)
    (signedScoreIntensityPrior_ae_nonneg
      kappa gamma rho a J D true hkappa.le hgamma hrho ha)
  have hF0 : 0 ≤ LF z := signedScoreMixtureLikelihood_nonneg _ _ _ (by positivity)
    (signedScoreIntensityPrior_ae_nonneg
      kappa gamma rho a J D false hkappa.le hgamma hrho ha)
  rw [hz, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hF0, ENNReal.toReal_ofReal hT0, inv_mul_eq_div]

/-- Density domination converts the one-cell chi-square divergence into the
common-reference squared likelihood distance.  The separate integrability
hypothesis is the analytic obligation discharged by the subsequent Gram
series estimate. -/
lemma signedScoreMixtureLaw_intensityPrior_chiSqDiv_le_of_integrable
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (hkappa : 0 < kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hrho : rho ∈ Icc (0 : ℝ) 2) (ha : 0 < a) (hJ : 1 ≤ J)
    (hsq : Integrable (fun z =>
      (signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D true) z -
        signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D false) z) ^ 2)
      (signedScoreReferenceLaw (kappa * (J : ℝ)))) :
    Causalean.Stat.chiSqDiv
        (signedScoreMixtureLaw
          (signedScoreIntensityPrior kappa gamma rho a J D true))
        (signedScoreMixtureLaw
          (signedScoreIntensityPrior kappa gamma rho a J D false)) ≤
      (J : ℝ) * ∫ z,
        (signedScoreMixtureLikelihood (kappa * (J : ℝ))
            (signedScoreIntensityPrior kappa gamma rho a J D true) z -
          signedScoreMixtureLikelihood (kappa * (J : ℝ))
            (signedScoreIntensityPrior kappa gamma rho a J D false) z) ^ 2
        ∂signedScoreReferenceLaw (kappa * (J : ℝ)) := by
  let Q := signedScoreReferenceLaw (kappa * (J : ℝ))
  let piT := signedScoreIntensityPrior kappa gamma rho a J D true
  let piF := signedScoreIntensityPrior kappa gamma rho a J D false
  let LT := signedScoreMixtureLikelihood (kappa * (J : ℝ)) piT
  let LF := signedScoreMixtureLikelihood (kappa * (J : ℝ)) piF
  let P := signedScoreMixtureLaw piT
  let N := signedScoreMixtureLaw piF
  have hrn := signedScoreMixtureLaw_intensityPrior_rnDeriv_toReal_eq
    kappa gamma rho a J D hkappa hgamma hrho ha hJ
  have hchi : Causalean.Stat.chiSqDiv P N =
      ∫ z, (LT z / LF z - 1) ^ 2 ∂N := by
    rw [Causalean.Stat.chiSqDiv]
    apply integral_congr_ae
    filter_upwards [hrn] with z hz
    rw [hz]
  have hN : N = Q.withDensity (fun z => ENNReal.ofReal (LF z)) :=
    signedScoreMixtureLaw_intensityPrior_eq_withDensity
      kappa gamma rho a J D false hkappa hgamma hrho ha hJ
  have hmeasF : Measurable (fun z => ENNReal.ofReal (LF z)) :=
    (signedScoreMixtureLikelihood_measurable _ _).ennreal_ofReal
  have hfiniteF : ∀ᵐ z ∂Q, ENNReal.ofReal (LF z) < ⊤ := by
    filter_upwards [] with z
    exact ENNReal.ofReal_lt_top
  have hchange : (∫ z, (LT z / LF z - 1) ^ 2 ∂N) =
      ∫ z, LF z * (LT z / LF z - 1) ^ 2 ∂Q := by
    rw [hN, integral_withDensity_eq_integral_toReal_smul
      hmeasF hfiniteF]
    apply integral_congr_ae
    filter_upwards [] with z
    have hF0 : 0 ≤ LF z := signedScoreMixtureLikelihood_nonneg _ _ _
      (by positivity) (signedScoreIntensityPrior_ae_nonneg
        kappa gamma rho a J D false hkappa.le hgamma hrho ha)
    rw [ENNReal.toReal_ofReal hF0, smul_eq_mul]
  have hJpos : (0 : ℝ) < J := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hJ)
  have hpoint : ∀ z, LF z * (LT z / LF z - 1) ^ 2 ≤
      (J : ℝ) * (LT z - LF z) ^ 2 := by
    intro z
    have hlower := signedScoreMixtureLikelihood_intensityPrior_lower_bound
      kappa gamma rho a J D false z hkappa hgamma hrho ha hJ
    have hlower' : 1 / (J : ℝ) ≤ LF z := by
      simpa only [ENNReal.toReal_ofReal (one_div_pos.mpr hJpos).le] using hlower
    have hFpos : 0 < LF z := lt_of_lt_of_le (one_div_pos.mpr hJpos) hlower'
    have hone : 1 ≤ (J : ℝ) * LF z := by
      simpa only [mul_comm] using (div_le_iff₀ hJpos).mp hlower'
    calc
      LF z * (LT z / LF z - 1) ^ 2 = (LT z - LF z) ^ 2 / LF z := by
        field_simp
        <;> ring
      _ ≤ (J : ℝ) * (LT z - LF z) ^ 2 := by
        rw [div_le_iff₀ hFpos]
        nlinarith [sq_nonneg (LT z - LF z)]
  have hupper : Integrable (fun z =>
      (J : ℝ) * (LT z - LF z) ^ 2) Q := hsq.const_mul _
  rw [hchi, hchange]
  change (∫ z, LF z * (LT z / LF z - 1) ^ 2 ∂Q) ≤
    (J : ℝ) * ∫ z, (LT z - LF z) ^ 2 ∂Q
  have hFnonneg : ∀ z, 0 ≤ LF z := fun z =>
    signedScoreMixtureLikelihood_nonneg _ _ _ (by positivity)
      (signedScoreIntensityPrior_ae_nonneg
        kappa gamma rho a J D false hkappa.le hgamma hrho ha)
  calc
    (∫ z, LF z * (LT z / LF z - 1) ^ 2 ∂Q) ≤
        ∫ z, (J : ℝ) * (LT z - LF z) ^ 2 ∂Q :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun z =>
          mul_nonneg (hFnonneg z) (sq_nonneg _)))
        hupper (Filter.Eventually.of_forall hpoint)
    _ = (J : ℝ) * ∫ z, (LT z - LF z) ^ 2 ∂Q := by
      rw [integral_const_mul]

private lemma oneCellPrior_integrable_of_stronglyMeasurable
    (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (f : LatentCell → ℝ) (hf : StronglyMeasurable f) :
    Integrable f (oneCellPrior a J D h) := by
  have hmap (s t : Bool) : Integrable f
      (Measure.map (latentFromIntensity s a) (tiltedSide a J D t)) := by
    rw [integrable_map_measure hf.aestronglyMeasurable
      (latentFromIntensity_measurable s a).aemeasurable]
    exact tiltedSide_integrable_of_atomic a J D t (f ∘ latentFromIntensity s a)
  rw [oneCellPrior]
  apply Integrable.add_measure
  · exact (integrable_dirac (by finiteness)).smul_measure (by simp)
  · apply Integrable.smul_measure
    · apply Integrable.add_measure
      · exact (hmap false (!h)).smul_measure (by simp)
      · exact (hmap true h).smul_measure (by simp)
    · simp

private lemma signedScoreIntensityPrior_integrable_of_stronglyMeasurable
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (f : (Fin 4 → ℝ) → ℝ) (hf : StronglyMeasurable f) :
    Integrable f (signedScoreIntensityPrior kappa gamma rho a J D h) := by
  rw [signedScoreIntensityPrior,
    integrable_map_measure hf.aestronglyMeasurable
      (signedScoreIntensity_measurable kappa gamma rho J).aemeasurable]
  exact oneCellPrior_integrable_of_stronglyMeasurable a J D h
    (f ∘ signedScoreIntensity kappa gamma rho J)
    (hf.comp_measurable (signedScoreIntensity_measurable kappa gamma rho J))

private lemma signedScoreIntensityPrior_prod_integrable_of_stronglyMeasurable
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h0 h1 : Bool) (f : (Fin 4 → ℝ) × (Fin 4 → ℝ) → ℝ)
    (hf : StronglyMeasurable f) (ha : 0 < a) (hJ : 1 ≤ J) :
    Integrable f
      ((signedScoreIntensityPrior kappa gamma rho a J D h0).prod
        (signedScoreIntensityPrior kappa gamma rho a J D h1)) := by
  letI := signedScoreIntensityPrior_isProbabilityMeasure
    kappa gamma rho a J D h0 ha hJ
  letI := signedScoreIntensityPrior_isProbabilityMeasure
    kappa gamma rho a J D h1 ha hJ
  apply (integrable_prod_iff hf.aestronglyMeasurable).2
  constructor
  · filter_upwards [] with v
    apply signedScoreIntensityPrior_integrable_of_stronglyMeasurable
    exact hf.comp_measurable (by fun_prop)
  · apply signedScoreIntensityPrior_integrable_of_stronglyMeasurable
    exact hf.norm.integral_prod_right

/-- The three likelihood products needed to expand the squared mixture
difference are integrable for the concrete finite atomic intensity priors. -/
lemma signedScoreMixtureLikelihood_product_integrable_intensityPrior
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h0 h1 : Bool) (hkappa : 0 < kappa) (ha : 0 < a) (hJ : 1 ≤ J) :
    Integrable (fun z =>
      signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D h0) z *
        signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D h1) z)
      (signedScoreReferenceLaw (kappa * (J : ℝ))) := by
  let Lambda := kappa * (J : ℝ)
  let pi0 := signedScoreIntensityPrior kappa gamma rho a J D h0
  let pi1 := signedScoreIntensityPrior kappa gamma rho a J D h1
  let Q := signedScoreReferenceLaw Lambda
  letI : IsProbabilityMeasure pi0 :=
    signedScoreIntensityPrior_isProbabilityMeasure kappa gamma rho a J D h0 ha hJ
  letI : IsProbabilityMeasure pi1 :=
    signedScoreIntensityPrior_isProbabilityMeasure kappa gamma rho a J D h1 ha hJ
  let F : ((Fin 4 → ℝ) × (Fin 4 → ℝ)) × SignedScoreCounts → ℝ := fun p =>
    signedScoreLikelihood Lambda p.1.1 p.2 *
      signedScoreLikelihood Lambda p.1.2 p.2
  have hLambda : 0 < Lambda := by positivity
  have hFsm : StronglyMeasurable F := by
    apply StronglyMeasurable.mul
    · exact (signedScoreLikelihood_joint_stronglyMeasurable Lambda).comp_measurable
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    · exact (signedScoreLikelihood_joint_stronglyMeasurable Lambda).comp_measurable
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hjoint : Integrable F ((pi0.prod pi1).prod Q) := by
    apply (integrable_prod_iff hFsm.aestronglyMeasurable).2
    constructor
    · filter_upwards [] with p
      apply Integrable.of_integral_ne_zero
      rw [signedScoreLikelihood_inner Lambda p.1 p.2 hLambda]
      positivity
    · apply signedScoreIntensityPrior_prod_integrable_of_stronglyMeasurable
      · exact hFsm.norm.integral_prod_right
      · exact ha
      · exact hJ
  have hmix := signedScoreMixtureLikelihood_inner_prod
    Lambda pi0 pi1 hLambda hjoint
  apply Integrable.of_integral_ne_zero
  rw [hmix]
  have hgram : Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      Real.exp (∑ s : Fin 4,
        (p.1 s - Lambda) * (p.2 s - Lambda) / Lambda)) (pi0.prod pi1) := by
    apply signedScoreIntensityPrior_prod_integrable_of_stronglyMeasurable
    · fun_prop
    · exact ha
    · exact hJ
  apply ne_of_gt
  apply (integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)) hgram).2
  simp only [Function.support, ne_eq, Real.exp_ne_zero, not_false_eq_true,
    setOf_true, measure_univ]
  norm_num

private lemma signedScoreCenteredMonomial_stronglyMeasurable
    (Lambda : ℝ) (alpha : Fin 4 → ℕ) :
    StronglyMeasurable (signedScoreCenteredMonomial Lambda alpha) := by
  let y : Fin 4 → ℝ := 0
  have hdiff : StronglyMeasurable (fun x =>
      signedScoreCenteredMonomial Lambda alpha x -
        signedScoreCenteredMonomial Lambda alpha y) := by
    rw [show (fun x => signedScoreCenteredMonomial Lambda alpha x -
          signedScoreCenteredMonomial Lambda alpha y) = fun x =>
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
            ((x 3 - Lambda) ^ alpha 3 - (y 3 - Lambda) ^ alpha 3)) by
      funext x
      exact signedScoreCenteredMonomial_sub_eq_telescoping Lambda alpha x y]
    fun_prop
  have hadd := hdiff.add_const (signedScoreCenteredMonomial Lambda alpha y)
  simpa only [sub_add_cancel] using hadd

private lemma signedScoreCenteredMonomial_comp_integrable_oneCellPrior
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (alpha : Fin 4 → ℕ) (h : Bool) :
    Integrable
      (fun z => signedScoreCenteredMonomial (kappa * (J : ℝ)) alpha
        (signedScoreIntensity kappa gamma rho J z))
      (oneCellPrior a J D h) := by
  classical
  let f := fun z => signedScoreCenteredMonomial (kappa * (J : ℝ)) alpha
    (signedScoreIntensity kappa gamma rho J z)
  have hmonomial : StronglyMeasurable
      (signedScoreCenteredMonomial (kappa * (J : ℝ)) alpha) :=
    signedScoreCenteredMonomial_stronglyMeasurable _ _
  have hf : StronglyMeasurable f := by
    exact hmonomial.comp_measurable
      (signedScoreIntensity_measurable kappa gamma rho J)
  have hmap (s t : Bool) : Integrable f
      (Measure.map (latentFromIntensity s a) (tiltedSide a J D t)) := by
    rw [integrable_map_measure hf.aestronglyMeasurable
      (latentFromIntensity_measurable s a).aemeasurable]
    exact tiltedSide_integrable_of_atomic a J D t (f ∘ latentFromIntensity s a)
  rw [oneCellPrior]
  apply Integrable.add_measure
  · exact (integrable_dirac (by finiteness)).smul_measure (by simp)
  · apply Integrable.smul_measure
    · apply Integrable.add_measure
      · exact (hmap false (!h)).smul_measure (by simp)
      · exact (hmap true h).smul_measure (by simp)
    · simp

/-- The pushed-forward true and false one-cell priors match every centered
monomial through total degree `3J`. -/
lemma signedScoreIntensityPrior_centered_moments_eq
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (alpha : Fin 4 → ℕ) (ha : 0 < a) (hJ : 1 ≤ J)
    (hdeg : (∑ i, alpha i) ≤ 3 * J) :
    (∫ v, signedScoreCenteredMonomial (kappa * (J : ℝ)) alpha v
      ∂signedScoreIntensityPrior kappa gamma rho a J D true) =
    ∫ v, signedScoreCenteredMonomial (kappa * (J : ℝ)) alpha v
      ∂signedScoreIntensityPrior kappa gamma rho a J D false := by
  classical
  let g := fun z => signedScoreCenteredMonomial (kappa * (J : ℝ)) alpha
    (signedScoreIntensity kappa gamma rho J z)
  have hmonomial : StronglyMeasurable
      (signedScoreCenteredMonomial (kappa * (J : ℝ)) alpha) :=
    signedScoreCenteredMonomial_stronglyMeasurable _ _
  have hg : StronglyMeasurable g := by
    exact hmonomial.comp_measurable
      (signedScoreIntensity_measurable kappa gamma rho J)
  have hint (h : Bool) : Integrable g (oneCellPrior a J D h) :=
    signedScoreCenteredMonomial_comp_integrable_oneCellPrior
      kappa gamma rho a J D alpha h
  rw [signedScoreIntensityPrior, signedScoreIntensityPrior,
    integral_map_of_stronglyMeasurable
      (signedScoreIntensity_measurable kappa gamma rho J) hmonomial,
    integral_map_of_stronglyMeasurable
      (signedScoreIntensity_measurable kappa gamma rho J) hmonomial]
  change (∫ z, g z ∂oneCellPrior a J D true) =
    ∫ z, g z ∂oneCellPrior a J D false
  by_cases hzero : ∑ i, alpha i = 0
  · have halpha (i : Fin 4) : alpha i = 0 := by
      have hi : alpha i ≤ ∑ j, alpha j := Finset.single_le_sum
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hg_const : g = fun _ => g referenceLatent := by
      funext z
      have htel := signedScoreCenteredMonomial_sub_eq_telescoping
        (kappa * (J : ℝ)) alpha
        (signedScoreIntensity kappa gamma rho J z)
        (signedScoreIntensity kappa gamma rho J referenceLatent)
      simp only [halpha, pow_zero, sub_self, zero_mul, mul_zero, add_zero] at htel
      exact sub_eq_zero.mp htel
    rw [hg_const]
    letI := oneCellPrior_isProbabilityMeasure a J D true ha hJ
    letI := oneCellPrior_isProbabilityMeasure a J D false ha hJ
    simp
  · have hpositive : 1 ≤ ∑ i, alpha i := Nat.one_le_iff_ne_zero.mpr hzero
    obtain ⟨p, hpdegree, hp⟩ :=
      signedScoreCenteredMonomial_latentFromIntensity_sign_sub_factor
        kappa gamma rho a J alpha ha hpositive hdeg
    have hside :
        (∫ x, g (latentFromIntensity true a x) ∂tiltedSide a J D true) -
            ∫ x, g (latentFromIntensity false a x) ∂tiltedSide a J D true =
          (∫ x, g (latentFromIntensity true a x) ∂tiltedSide a J D false) -
            ∫ x, g (latentFromIntensity false a x) ∂tiltedSide a J D false := by
      rw [← integral_sub
          (tiltedSide_integrable_of_atomic a J D true
            (fun x => g (latentFromIntensity true a x)))
          (tiltedSide_integrable_of_atomic a J D true
            (fun x => g (latentFromIntensity false a x))),
        ← integral_sub
          (tiltedSide_integrable_of_atomic a J D false
            (fun x => g (latentFromIntensity true a x)))
          (tiltedSide_integrable_of_atomic a J D false
            (fun x => g (latentFromIntensity false a x)))]
      calc
        (∫ x, g (latentFromIntensity true a x) -
            g (latentFromIntensity false a x) ∂tiltedSide a J D true) =
            ∫ x, x * p.eval x ∂tiltedSide a J D true := by
          apply integral_congr_ae
          filter_upwards [tiltedSide_ae_zero_or_mem_interval a J D true]
            with x hx
          exact hp x hx
        _ = ∫ x, x * p.eval x ∂tiltedSide a J D false :=
          tiltedSide_mul_polynomial_eval_integral_eq
            a J (∑ i, alpha i) D p ha hpdegree hdeg
        _ = ∫ x, g (latentFromIntensity true a x) -
            g (latentFromIntensity false a x) ∂tiltedSide a J D false := by
          apply integral_congr_ae
          filter_upwards [tiltedSide_ae_zero_or_mem_interval a J D false]
            with x hx
          exact (hp x hx).symm
    have hmap (s t : Bool) : Integrable g
        (Measure.map (latentFromIntensity s a) (tiltedSide a J D t)) := by
      rw [integrable_map_measure hg.aestronglyMeasurable
        (latentFromIntensity_measurable s a).aemeasurable]
      exact tiltedSide_integrable_of_atomic a J D t
        (g ∘ latentFromIntensity s a)
    have hone (h : Bool) :
        (∫ z, g z ∂oneCellPrior a J D h) =
          (ENNReal.ofReal (1 / (J : ℝ))).toReal * g referenceLatent +
          (ENNReal.ofReal (1 - 1 / (J : ℝ))).toReal *
            ((1 / 2 : ENNReal).toReal *
                ∫ x, g (latentFromIntensity false a x) ∂tiltedSide a J D (!h) +
              (1 / 2 : ENNReal).toReal *
                ∫ x, g (latentFromIntensity true a x) ∂tiltedSide a J D h) := by
      have href : Integrable g
          (ENNReal.ofReal (1 / (J : ℝ)) • Measure.dirac referenceLatent) :=
        (integrable_dirac (by finiteness)).smul_measure (by simp)
      have hfalse : Integrable g
          ((1 / 2 : ENNReal) •
            Measure.map (latentFromIntensity false a) (tiltedSide a J D (!h))) :=
        (hmap false (!h)).smul_measure (by norm_num)
      have htrue : Integrable g
          ((1 / 2 : ENNReal) •
            Measure.map (latentFromIntensity true a) (tiltedSide a J D h)) :=
        (hmap true h).smul_measure (by norm_num)
      have hmix : Integrable g
          ((1 / 2 : ENNReal) •
              Measure.map (latentFromIntensity false a) (tiltedSide a J D (!h)) +
            (1 / 2 : ENNReal) •
              Measure.map (latentFromIntensity true a) (tiltedSide a J D h)) :=
        hfalse.add_measure htrue
      have hscaled : Integrable g
          (ENNReal.ofReal (1 - 1 / (J : ℝ)) •
            ((1 / 2 : ENNReal) •
                Measure.map (latentFromIntensity false a) (tiltedSide a J D (!h)) +
              (1 / 2 : ENNReal) •
                Measure.map (latentFromIntensity true a) (tiltedSide a J D h))) :=
        hmix.smul_measure (by simp)
      rw [oneCellPrior,
        integral_add_measure href hscaled,
        integral_smul_measure, integral_dirac,
        integral_smul_measure,
        integral_add_measure hfalse htrue,
        integral_smul_measure, integral_smul_measure,
        integral_map_of_stronglyMeasurable
          (latentFromIntensity_measurable false a) hg,
        integral_map_of_stronglyMeasurable
          (latentFromIntensity_measurable true a) hg]
      rfl
    rw [hone true, hone false]
    simp only [Bool.not_true, Bool.not_false]
    linear_combination
      (ENNReal.ofReal (1 - 1 / (J : ℝ))).toReal *
        (1 / 2 : ENNReal).toReal * hside

/-- The squared difference of two prior-predictive likelihoods expands into
the three Gram terms used in the one-cell comparison. -/
lemma signedScoreMixtureLikelihood_sq_sub_integral_eq
    (Lambda : ℝ) (pi0 pi1 : Measure (Fin 4 → ℝ))
    (h00 : Integrable (fun z =>
      signedScoreMixtureLikelihood Lambda pi0 z *
        signedScoreMixtureLikelihood Lambda pi0 z)
      (signedScoreReferenceLaw Lambda))
    (h11 : Integrable (fun z =>
      signedScoreMixtureLikelihood Lambda pi1 z *
        signedScoreMixtureLikelihood Lambda pi1 z)
      (signedScoreReferenceLaw Lambda))
    (h01 : Integrable (fun z =>
      signedScoreMixtureLikelihood Lambda pi0 z *
        signedScoreMixtureLikelihood Lambda pi1 z)
      (signedScoreReferenceLaw Lambda)) :
    (∫ z, (signedScoreMixtureLikelihood Lambda pi0 z -
        signedScoreMixtureLikelihood Lambda pi1 z) ^ 2
        ∂signedScoreReferenceLaw Lambda) =
      (∫ z, signedScoreMixtureLikelihood Lambda pi0 z *
        signedScoreMixtureLikelihood Lambda pi0 z
        ∂signedScoreReferenceLaw Lambda) +
      (∫ z, signedScoreMixtureLikelihood Lambda pi1 z *
        signedScoreMixtureLikelihood Lambda pi1 z
        ∂signedScoreReferenceLaw Lambda) -
      2 * ∫ z, signedScoreMixtureLikelihood Lambda pi0 z *
        signedScoreMixtureLikelihood Lambda pi1 z
        ∂signedScoreReferenceLaw Lambda := by
  have hpoint : (fun z =>
      (signedScoreMixtureLikelihood Lambda pi0 z -
        signedScoreMixtureLikelihood Lambda pi1 z) ^ 2) =
      fun z =>
        signedScoreMixtureLikelihood Lambda pi0 z *
            signedScoreMixtureLikelihood Lambda pi0 z +
          signedScoreMixtureLikelihood Lambda pi1 z *
            signedScoreMixtureLikelihood Lambda pi1 z -
          2 * (signedScoreMixtureLikelihood Lambda pi0 z *
            signedScoreMixtureLikelihood Lambda pi1 z) := by
    funext z
    ring
  rw [hpoint]
  integral_linearity

/-- The squared difference of the two concrete one-cell mixture likelihoods
is integrable under their common reference law. -/
lemma signedScoreMixtureLikelihood_sq_sub_integrable_intensityPrior
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (hkappa : 0 < kappa) (ha : 0 < a) (hJ : 1 ≤ J) :
    Integrable (fun z =>
      (signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D true) z -
        signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D false) z) ^ 2)
      (signedScoreReferenceLaw (kappa * (J : ℝ))) := by
  let Lambda := kappa * (J : ℝ)
  let piT := signedScoreIntensityPrior kappa gamma rho a J D true
  let piF := signedScoreIntensityPrior kappa gamma rho a J D false
  let LT := signedScoreMixtureLikelihood Lambda piT
  let LF := signedScoreMixtureLikelihood Lambda piF
  have hTT := signedScoreMixtureLikelihood_product_integrable_intensityPrior
    kappa gamma rho a J D true true hkappa ha hJ
  have hFF := signedScoreMixtureLikelihood_product_integrable_intensityPrior
    kappa gamma rho a J D false false hkappa ha hJ
  have hTF := signedScoreMixtureLikelihood_product_integrable_intensityPrior
    kappa gamma rho a J D true false hkappa ha hJ
  have hpoly : Integrable (fun z =>
      LT z * LT z + LF z * LF z - 2 * (LT z * LF z))
      (signedScoreReferenceLaw Lambda) :=
    (hTT.add hFF).sub (hTF.const_mul 2)
  apply hpoly.congr
  filter_upwards [] with z
  dsimp only [LT, LF]
  ring

/-- Concrete three-Gram-term expansion of the common-reference squared
likelihood distance. -/
lemma signedScoreMixtureLikelihood_sq_sub_integral_intensityPrior_eq
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (hkappa : 0 < kappa) (ha : 0 < a) (hJ : 1 ≤ J) :
    (∫ z, (signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D true) z -
        signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D false) z) ^ 2
        ∂signedScoreReferenceLaw (kappa * (J : ℝ))) =
      (∫ z, signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D true) z *
        signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D true) z
        ∂signedScoreReferenceLaw (kappa * (J : ℝ))) +
      (∫ z, signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D false) z *
        signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D false) z
        ∂signedScoreReferenceLaw (kappa * (J : ℝ))) -
      2 * ∫ z, signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D true) z *
        signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D false) z
        ∂signedScoreReferenceLaw (kappa * (J : ℝ)) := by
  apply signedScoreMixtureLikelihood_sq_sub_integral_eq
  · exact signedScoreMixtureLikelihood_product_integrable_intensityPrior
      kappa gamma rho a J D true true hkappa ha hJ
  · exact signedScoreMixtureLikelihood_product_integrable_intensityPrior
      kappa gamma rho a J D false false hkappa ha hJ
  · exact signedScoreMixtureLikelihood_product_integrable_intensityPrior
      kappa gamma rho a J D true false hkappa ha hJ

/-- The faithful one-cell density comparison: reference-atom domination costs
exactly the reciprocal retained weight `J`. -/
lemma signedScoreMixtureLaw_intensityPrior_chiSqDiv_le
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (hkappa : 0 < kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hrho : rho ∈ Icc (0 : ℝ) 2) (ha : 0 < a) (hJ : 1 ≤ J) :
    Causalean.Stat.chiSqDiv
        (signedScoreMixtureLaw
          (signedScoreIntensityPrior kappa gamma rho a J D true))
        (signedScoreMixtureLaw
          (signedScoreIntensityPrior kappa gamma rho a J D false)) ≤
      (J : ℝ) * ∫ z,
        (signedScoreMixtureLikelihood (kappa * (J : ℝ))
            (signedScoreIntensityPrior kappa gamma rho a J D true) z -
          signedScoreMixtureLikelihood (kappa * (J : ℝ))
            (signedScoreIntensityPrior kappa gamma rho a J D false) z) ^ 2
        ∂signedScoreReferenceLaw (kappa * (J : ℝ)) := by
  apply signedScoreMixtureLaw_intensityPrior_chiSqDiv_le_of_integrable
    kappa gamma rho a J D hkappa hgamma hrho ha hJ
  exact signedScoreMixtureLikelihood_sq_sub_integrable_intensityPrior
    kappa gamma rho a J D hkappa ha hJ

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

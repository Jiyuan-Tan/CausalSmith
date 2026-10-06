module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CoefficientEnvelopeFour
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Fixed-basis tensor-polynomial coefficients

Bounded coordinatewise-degree real multivariate polynomials are represented in one fixed
finite monomial basis. Evaluation at a fixed tensor grid determines every coefficient, so a
pointwise polynomial family has continuous coefficients when its grid values are continuous.
This applies to a Jackson family even if each representative was initially chosen separately.
-/

@[expose] public section

noncomputable section

open Causalean.Mathlib.Analysis.JacksonApproximation
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev

/-- [A bounded tensor index](hyp:a) determines [its finitely supported monomial exponent](goal).

The fixed monomial exponent associated with a tensor index of coordinatewise degree at most
`D`.
-/
def tensorExponent {d D : ℕ} (a : Fin d → Fin (D + 1)) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))

/-- [A multivariate polynomial and tensor index](hyp:p,a) determine [the associated fixed-basis coefficient](goal).

A polynomial's coefficient vector in the fixed tensor monomial basis.
-/
def tensorCoeffs {d D : ℕ} (p : MvPolynomial (Fin d) ℝ)
    (a : Fin d → Fin (D + 1)) : ℝ := p.coeff (tensorExponent a)

/-- [A finite tensor coefficient vector](hyp:c) determines [the multivariate polynomial synthesized in the fixed monomial basis](goal).

The fixed-basis polynomial synthesized from a tensor coefficient vector.
-/
def tensorPolynomial {d D : ℕ} (c : (Fin d → Fin (D + 1)) → ℝ) :
    MvPolynomial (Fin d) ℝ :=
  ∑ a, MvPolynomial.monomial (tensorExponent a) (c a)

/-- A polynomial of coordinatewise degree at most `D` equals the synthesis of its fixed-basis
coefficient vector. The support bound should be converted using `degreeOf_le_iff`, then `as_sum`.
-/
theorem tensorPolynomial_tensorCoeffs {d D : ℕ} (p : MvPolynomial (Fin d) ℝ)
    (hdeg : ∀ i, p.degreeOf i ≤ D) :
    tensorPolynomial (tensorCoeffs (D := D) p) = p := by
  classical
  have hinj : Function.Injective (tensorExponent (d := d) (D := D)) := by
    intro a b h
    funext i
    apply Fin.ext
    have hi := congrArg (fun m : Fin d →₀ ℕ => m i) h
    simpa [tensorExponent] using hi
  apply MvPolynomial.ext
  intro m
  by_cases hb : ∀ i, m i ≤ D
  · let a : Fin d → Fin (D + 1) := fun i => ⟨m i, Nat.lt_succ_of_le (hb i)⟩
    have ha : tensorExponent a = m := by
      apply Finsupp.ext
      intro i
      simp [a, tensorExponent]
    simp only [tensorPolynomial, tensorCoeffs, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro b _ hba
      have hne : tensorExponent b ≠ m := fun h => hba (hinj (h.trans ha.symm))
      simp [hne]
    · intro h
      exact (h (Finset.mem_univ a)).elim
  · have hm : m ∉ p.support := by
      intro hmem
      apply hb
      intro i
      exact (MvPolynomial.degreeOf_le_iff.mp (hdeg i)) m hmem
    have hc : p.coeff m = 0 := MvPolynomial.notMem_support_iff.mp hm
    simp only [tensorPolynomial, tensorCoeffs, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_zero]
    · exact hc.symm
    · intro a _
      have hne : tensorExponent a ≠ m := by
        intro h
        apply hb
        intro i
        have hi := congrArg (fun n : Fin d →₀ ℕ => n i) h
        have hi' : (a i : ℕ) = m i := by simpa [tensorExponent] using hi
        exact hi' ▸ Nat.lt_succ_iff.mp (a i).isLt
      simp [hne]

/-- Evaluation on the integer tensor grid determines a polynomial of coordinatewise degree at
most `D`. Prove this by induction on the number of coordinates using univariate root bounds.
-/
theorem tensorPolynomial_eq_of_grid {d D : ℕ}
    (p q : MvPolynomial (Fin d) ℝ)
    (hp : ∀ i, p.degreeOf i ≤ D) (hq : ∀ i, q.degreeOf i ≤ D)
    (hgrid : ∀ a : Fin d → Fin (D + 1),
      MvPolynomial.eval (fun i => (a i : ℝ)) p =
        MvPolynomial.eval (fun i => (a i : ℝ)) q) : p = q := by
  classical
  let S : Fin d → Finset ℝ := fun _ => Finset.univ.image (fun j : Fin (D + 1) => (j : ℝ))
  have hcard (i : Fin d) : (S i).card = D + 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b h
      change (a : ℝ) = (b : ℝ) at h
      apply Fin.ext
      exact_mod_cast h
  have hdeg' (i : Fin d) : (p - q).degreeOf i < (S i).card := by
    rw [hcard i]
    exact lt_of_le_of_lt (MvPolynomial.degreeOf_sub_le i p q)
      (Nat.lt_succ_of_le (max_le (hp i) (hq i)))
  have hzero : p - q = 0 :=
    MvPolynomial.eq_zero_of_eval_zero_at_prod_finset (p - q) S hdeg' (by
      intro x hx
      have hchoice : ∀ i : Fin d, ∃ a : Fin (D + 1), (a : ℝ) = x i := by
        intro i
        obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (hx i)
        exact ⟨a, ha⟩
      choose a ha using hchoice
      have he := hgrid a
      have hxa : (fun i => (a i : ℝ)) = x := funext ha
      simpa [MvPolynomial.eval_sub, hxa] using sub_eq_zero.mpr he)
  exact sub_eq_zero.mp hzero

private theorem tensorCoeffs_tensorPolynomial {d D : ℕ}
    (c : (Fin d → Fin (D + 1)) → ℝ) (a : Fin d → Fin (D + 1)) :
    tensorCoeffs (tensorPolynomial c) a = c a := by
  classical
  have hinj : Function.Injective (tensorExponent (d := d) (D := D)) := by
    intro b b' h
    funext i
    apply Fin.ext
    have hi := congrArg (fun m : Fin d →₀ ℕ => m i) h
    simpa [tensorExponent] using hi
  simp only [tensorCoeffs, tensorPolynomial, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    have hne : tensorExponent b ≠ tensorExponent a := fun h => hba (hinj h)
    simp [hne]
  · intro h
    exact (h (Finset.mem_univ a)).elim

private theorem tensorPolynomial_degreeOf_le {d D : ℕ}
    (c : (Fin d → Fin (D + 1)) → ℝ) (i : Fin d) :
    (tensorPolynomial c).degreeOf i ≤ D := by
  classical
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  have hc : (tensorPolynomial c).coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  simp only [tensorPolynomial, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial] at hc
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  split_ifs at ha with he
  · rw [← he]
    change (a i : ℕ) ≤ D
    exact Nat.le_of_lt_succ (a i).isLt
  · exact (ha rfl).elim

/-- [A parameter-indexed polynomial family](hyp:p), [a coordinatewise degree bound](hyp:hdeg), [continuous evaluations on a fixed tensor grid](hyp:hgrid), and [a coefficient index](hyp:a) give [a continuously varying recovered monomial coefficient](goal).

A degree-bounded polynomial family has continuous coefficients whenever each value on the
fixed integer tensor grid varies continuously with the parameter. The inverse of the finite
tensor Vandermonde evaluation map is linear and continuous.
-/
theorem continuous_tensorCoeffs_of_grid {Λ : Type*} [TopologicalSpace Λ]
    {d D : ℕ} (p : Λ → MvPolynomial (Fin d) ℝ)
    (hdeg : ∀ s i, (p s).degreeOf i ≤ D)
    (hgrid : ∀ a : Fin d → Fin (D + 1),
      Continuous (fun s => MvPolynomial.eval (fun i => (a i : ℝ)) (p s)))
    (a : Fin d → Fin (D + 1)) :
    Continuous (fun s => tensorCoeffs (D := D) (p s) a) := by
  classical
  let V := (Fin d → Fin (D + 1)) → ℝ
  let E : V →ₗ[ℝ] V :=
    { toFun := fun c b => ∑ a : Fin d → Fin (D + 1),
          c a * MvPolynomial.eval (fun i => (b i : ℝ))
            (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))
      map_add' := by
        intro c c'
        funext b
        change (∑ a, (c a + c' a) * _) =
          (∑ a, c a * _) + ∑ a, c' a * _
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c
        funext b
        change (∑ a, (r * c a) * _) = r * ∑ a, c a * _
        simp [mul_assoc, Finset.mul_sum] }
  have hEval (c : V) (b : Fin d → Fin (D + 1)) :
      E c b = MvPolynomial.eval (fun i => (b i : ℝ)) (tensorPolynomial c) := by
    change (∑ a, c a * MvPolynomial.eval (fun i => (b i : ℝ))
      (MvPolynomial.monomial (tensorExponent a) (1 : ℝ))) = _
    simp [tensorPolynomial, MvPolynomial.eval_monomial]
  have hcont : Continuous (fun s => E (tensorCoeffs (D := D) (p s))) := by
    apply continuous_pi
    intro b
    convert hgrid b using 1
    ext s
    rw [hEval, tensorPolynomial_tensorCoeffs (p s) (hdeg s)]
  have hinj : Function.Injective E := by
    intro c c' h
    have hgrid' (b : Fin d → Fin (D + 1)) :
        MvPolynomial.eval (fun i => (b i : ℝ)) (tensorPolynomial c) =
          MvPolynomial.eval (fun i => (b i : ℝ)) (tensorPolynomial c') := by
      have hb := congrArg (fun v : V => v b) h
      simpa only [hEval] using hb
    have heq := tensorPolynomial_eq_of_grid (tensorPolynomial c)
      (tensorPolynomial c') (tensorPolynomial_degreeOf_le c)
      (tensorPolynomial_degreeOf_le c') hgrid'
    funext b
    calc
      c b = tensorCoeffs (tensorPolynomial c) b := (tensorCoeffs_tensorPolynomial c b).symm
      _ = tensorCoeffs (tensorPolynomial c') b := by rw [heq]
      _ = c' b := tensorCoeffs_tensorPolynomial c' b
  let e := LinearEquiv.ofBijective E ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  have he : Continuous (e.symm : V → V) := e.symm.continuous_of_finiteDimensional
  have hcomp := he.comp hcont
  convert (continuous_apply a).comp hcomp using 1
  ext s
  change tensorCoeffs (p s) a = (e.symm (e (tensorCoeffs (p s)))) a
  simp

/-- The recovered coefficient of a degree-bounded polynomial family is measurable when its
fixed-grid evaluations are continuous. -/
theorem measurable_tensorCoeffs_of_grid {Λ : Type*} [TopologicalSpace Λ]
    [MeasurableSpace Λ] [BorelSpace Λ] {d D : ℕ}
    (p : Λ → MvPolynomial (Fin d) ℝ)
    (hdeg : ∀ s i, (p s).degreeOf i ≤ D)
    (hgrid : ∀ a : Fin d → Fin (D + 1),
      Continuous (fun s => MvPolynomial.eval (fun i => (a i : ℝ)) (p s)))
    (a : Fin d → Fin (D + 1)) :
    Measurable (fun s => tensorCoeffs (D := D) (p s) a) := by
  exact (continuous_tensorCoeffs_of_grid p hdeg hgrid a).measurable

/-- A polynomial bounded by `B` on the normalized tensor cube has a coefficient one-norm
bounded exponentially in its coordinatewise degree. This is the deterministic envelope used for
the Jackson coefficient path; the estimate is valid for every polynomial representative.
-/
theorem tensorCoeffs_l1_le_cube_bound {d D : ℕ}
    (p : MvPolynomial (Fin d) ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ i, p.degreeOf i ≤ D)
    (hbound : ∀ x ∈ normalizedCube d, |MvPolynomial.eval x p| ≤ B) :
    mvCoeffL1 p ≤ ((2 : ℝ) * (D + 1) ^ 2 * (3 : ℝ) ^ D) ^ d * B := by
  exact mvCoeffL1_le_bounded p B hB
    (fun m hm i => (MvPolynomial.degreeOf_le_iff.mp (hdeg i)) m hm) hbound

end Causalean.Mathlib.Analysis.Approximation.Chebyshev


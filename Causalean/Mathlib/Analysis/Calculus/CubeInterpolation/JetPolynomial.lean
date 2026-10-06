module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Basic
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Directional
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Grid
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.JetHomogeneous
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Polynomial realization of a finite Taylor jet

The diagonal evaluations of finitely many multilinear derivatives form a
multivariate polynomial. At a smooth point its coordinate derivatives recover
the corresponding coordinate derivatives of the original function.
-/

public section

open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- The order-`m` Taylor expression at a point is the evaluation of a
multivariate polynomial with degree at most `m` in each coordinate. -/
theorem taylor_expression_polynomial (d m : ℕ)
    (u : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    ∃ p : MvPolynomial (Fin d) ℝ,
      (∀ i, p.degreeOf i ≤ m) ∧
      ∀ y : Fin d → ℝ,
        MvPolynomial.eval y p =
          ∑ k ∈ Finset.range (m + 1),
            (Nat.factorial k : ℝ)⁻¹ *
              iteratedFDeriv ℝ k u x (fun _ => y - x) := by
  classical
  let q : ℕ → MvPolynomial (Fin d) ℝ := fun k =>
    ∑ f : Fin k → Fin d,
      MvPolynomial.C ((Nat.factorial k : ℝ)⁻¹ * coordPartial k u f x) *
        ∏ a : Fin k, (MvPolynomial.X (f a) - MvPolynomial.C (x (f a)))
  have hfactor :
      ∀ a : Fin d, (MvPolynomial.X a - MvPolynomial.C (x a)).totalDegree ≤ 1 := by
    intro a
    have h := MvPolynomial.totalDegree_add
      (MvPolynomial.X a : MvPolynomial (Fin d) ℝ) (-MvPolynomial.C (x a))
    simpa only [sub_eq_add_neg] using le_trans h (by simp :
      max (MvPolynomial.X a : MvPolynomial (Fin d) ℝ).totalDegree
        (-MvPolynomial.C (x a)).totalDegree ≤ 1)
  have hq (k : ℕ) : (q k).totalDegree ≤ k := by
    unfold q
    apply le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun f _ => ?_)
    apply le_trans (MvPolynomial.totalDegree_mul _ _) 
    have hc : (MvPolynomial.C ((Nat.factorial k : ℝ)⁻¹ * coordPartial k u f x) :
        MvPolynomial (Fin d) ℝ).totalDegree = 0 := MvPolynomial.totalDegree_C _
    rw [hc, zero_add]
    apply le_trans (MvPolynomial.totalDegree_finsetProd _ _)
    simpa using (Finset.sum_le_sum (s := Finset.univ) (fun a _ => hfactor (f a)))
  refine ⟨∑ k ∈ Finset.range (m + 1), q k, ?_, ?_⟩
  · intro i
    apply le_trans (MvPolynomial.degreeOf_le_totalDegree _ _)
    apply le_trans (MvPolynomial.totalDegree_finsetSum _ _)
    apply Finset.sup_le
    intro k hk
    exact (hq k).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  · intro y
    simp only [MvPolynomial.eval_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [q, MvPolynomial.eval_sum,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_prod,
      MvPolynomial.eval_sub, MvPolynomial.eval_X]
    rw [diagonal_derivative_coordinate_expansion u x (y - x)]
    simp_rw [Pi.sub_apply]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f hf
    ring

/-- If [a function is m times continuously differentiable at a point](hyp:hu) and [a polynomial
agrees everywhere with the function's order-m Taylor polynomial at that point](hyp:hp), then [every
coordinate partial derivative of the polynomial of order at most m, evaluated at the expansion
point, equals the corresponding coordinate partial of the function there](goal). -/
theorem taylor_polynomial_jet_match {d m : ℕ}
    {u : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hu : ContDiffAt ℝ m u x) {p : MvPolynomial (Fin d) ℝ}
    (hp : ∀ y : Fin d → ℝ,
      MvPolynomial.eval y p =
        ∑ k ∈ Finset.range (m + 1),
          (Nat.factorial k : ℝ)⁻¹ *
            iteratedFDeriv ℝ k u x (fun _ => y - x)) :
    ∀ j ≤ m, ∀ f : Fin j → Fin d,
      coordPartial j (fun z => MvPolynomial.eval z p) f x =
        coordPartial j u f x := by
  -- Differentiate the finite Taylor polynomial at its center. Higher
  -- homogeneous terms vanish there; symmetry of derivatives at `hu` gives
  -- the original ordered coordinate partial for the degree-`j` term.
  classical
  intro j hj f
  let H (k : ℕ) (z : Fin d → ℝ) : ℝ :=
    (Nat.factorial k : ℝ)⁻¹ *
      iteratedFDeriv ℝ k u x (fun _ => z - x)
  have hterm (k : ℕ) : ContDiff ℝ (j : WithTop ℕ∞) (H k) := by
    let A := (Nat.factorial k : ℝ)⁻¹ • iteratedFDeriv ℝ k u x
    let D : (Fin d → ℝ) →L[ℝ] (Fin k → (Fin d → ℝ)) :=
      ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ (Fin d → ℝ))
    have h : ContDiff ℝ ⊤ (fun z => A (D (z - x))) :=
      A.contDiff.comp (D.contDiff.comp (contDiff_id.sub contDiff_const))
    have heq : H k = (fun z => A (D (z - x))) := by
      funext z
      simp [H, A, D, smul_eq_mul]
    rw [heq]
    exact h.of_le le_top
  have hsum :
      coordPartial j (fun z => MvPolynomial.eval z p) f x =
        ∑ k ∈ Finset.range (m + 1), coordPartial j (H k) f x := by
    unfold coordPartial
    have heq : (fun z => MvPolynomial.eval z p) =
        (fun z => ∑ k ∈ Finset.range (m + 1), H k z) := by
      funext z
      exact hp z
    rw [heq, iteratedFDeriv_fun_sum_apply]
    · change (ContinuousMultilinearMap.applyAddHom
        (fun i => Pi.single (f i) (1 : ℝ)))
        (∑ k ∈ Finset.range (m + 1), iteratedFDeriv ℝ j (H k) x) = _
      simp only [map_sum]
      rfl
    · intro k hk
      exact (hterm k).contDiffAt
  rw [hsum]
  have hjmem : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hsingle :
      (∑ k ∈ Finset.range (m + 1), coordPartial j (H k) f x) =
        coordPartial j (H j) f x := by
    apply Finset.sum_eq_single j
    · intro k hk hkj
      rcases lt_or_gt_of_ne hkj with hlt | hgt
      · exact homogeneous_taylor_jet_above_degree hlt u x f
      · exact homogeneous_taylor_jet_below_degree hgt u x f
    · intro hnot
      exact (hnot hjmem).elim
  rw [hsingle]
  have hjm : (j : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by exact_mod_cast hj
  exact homogeneous_taylor_jet_at_degree (hu.of_le hjm) f

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

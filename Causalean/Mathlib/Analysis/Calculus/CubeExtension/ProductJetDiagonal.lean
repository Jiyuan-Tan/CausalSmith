module
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Diagonal Leibniz formula for within-set jets

The product rule for iterated Fréchet derivatives is first isolated on tuples
whose directions are all equal. This scalar identity is the analytic input to
the symmetric multilinear pairing formula in `ProductJetDifference`.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- Differentiating a diagonal jet along its fixed direction adds one derivative slot. -/
private theorem diagonal_fderivWithin
    {d n : ℕ} {S : Set (Fin d → ℝ)} (huniq : UniqueDiffOn ℝ S)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiffOn ℝ (n + 1) f S)
    {x : Fin d → ℝ} (hx : x ∈ S) (z : Fin d → ℝ) :
    (fderivWithin ℝ (fun y => iteratedFDerivWithin ℝ n f S y (fun _ => z)) S x) z =
      iteratedFDerivWithin ℝ (n + 1) f S x (fun _ => z) := by
  have hd : DifferentiableWithinAt ℝ (iteratedFDerivWithin ℝ n f S) S x :=
    hf.differentiableOn_iteratedFDerivWithin (by exact_mod_cast Nat.lt_succ_self n) huniq x hx
  rw [fderivWithin_continuousMultilinear_apply_const_apply (huniq x hx) hd]
  have ht : Fin.tail (fun _ : Fin (n + 1) => z) = (fun _ : Fin n => z) := rfl
  simpa only [ht] using (iteratedFDerivWithin_succ_apply_left (f := f) (s := S) (x := x)
    (n := n) (fun _ => z)).symm

/-- If [a set S has unique within-set derivatives](hyp:huniq), [two functions v
and w are m times continuously differentiable within S](hyp:hv,hw), and [x lies
in S](hyp:hx), then [the order-m within-S derivative of the product v·w at x,
evaluated with the same direction z in every slot, equals the sum over i ≤ m of
(m choose i) times the order-i within-S derivative of v times the order-(m − i)
within-S derivative of w, each evaluated with z in every slot](goal).

For `m = 0` this is the value-level product identity. For the induction step,
differentiate the lower-order formula in the repeated direction, using the
within-set first-derivative product rule and the `ContDiffOn` hypotheses.
The two shifted binomial sums combine by Pascal's identity. Mathlib's
`iteratedDerivWithin_mul` proves the analogous one-variable formula, while
`iteratedFDerivWithin_succ_apply_left` exposes the added slot here. -/
theorem iteratedFDerivWithin_mul_diagonal
    {d m : ℕ} {S : Set (Fin d → ℝ)}
    (huniq : UniqueDiffOn ℝ S)
    {v w : (Fin d → ℝ) → ℝ}
    (hv : ContDiffOn ℝ m v S) (hw : ContDiffOn ℝ m w S)
    {x : Fin d → ℝ} (hx : x ∈ S) (z : Fin d → ℝ) :
    iteratedFDerivWithin ℝ m (fun t => v t * w t) S x (fun _ => z) =
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        (iteratedFDerivWithin ℝ i v S x (fun _ => z) *
          iteratedFDerivWithin ℝ (m - i) w S x (fun _ => z)) := by
  induction m generalizing v w x with
  | zero =>
      simp [iteratedFDerivWithin_zero_apply]
  | succ n ih =>
      let V (i : ℕ) (y : Fin d → ℝ) :=
        iteratedFDerivWithin ℝ i v S y (fun _ => z)
      let W (i : ℕ) (y : Fin d → ℝ) :=
        iteratedFDerivWithin ℝ i w S y (fun _ => z)
      have hvn : ContDiffOn ℝ n v S := hv.of_le (by exact_mod_cast Nat.le_succ n)
      have hwn : ContDiffOn ℝ n w S := hw.of_le (by exact_mod_cast Nat.le_succ n)
      have hpoint : ∀ y ∈ S,
          iteratedFDerivWithin ℝ n (fun t => v t * w t) S y (fun _ => z) =
            ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (V i y * W (n - i) y) := by
        intro y hy
        exact ih hvn hwn hy
      have hVdiff (i : ℕ) (hi : i ≤ n) : DifferentiableWithinAt ℝ (V i) S x := by
        exact
          (hv.differentiableOn_iteratedFDerivWithin
            (by exact_mod_cast Nat.lt_of_le_of_lt hi (Nat.lt_succ_self n))
            huniq x hx).continuousMultilinear_apply_const _
      have hWdiff (i : ℕ) (hi : i ≤ n) : DifferentiableWithinAt ℝ (W i) S x := by
        exact
          (hw.differentiableOn_iteratedFDerivWithin
            (by exact_mod_cast Nat.lt_of_le_of_lt hi (Nat.lt_succ_self n))
            huniq x hx).continuousMultilinear_apply_const _
      have hVderiv (i : ℕ) (hi : i ≤ n) :
          (fderivWithin ℝ (V i) S x) z = V (i + 1) x := by
        exact diagonal_fderivWithin huniq
          (hv.of_le (by exact_mod_cast Nat.succ_le_succ hi)) hx z
      have hWderiv (i : ℕ) (hi : i ≤ n) :
          (fderivWithin ℝ (W i) S x) z = W (i + 1) x := by
        exact diagonal_fderivWithin huniq
          (hw.of_le (by exact_mod_cast Nat.succ_le_succ hi)) hx z
      have hsum :
          (fderivWithin ℝ (fun y => ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (V i y * W (n - i) y)) S x) z =
            ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
              (V i x * W (n + 1 - i) x + V (i + 1) x * W (n - i) x) := by
        rw [fderivWithin_fun_sum (huniq x hx)]
        · simp only [sum_apply]
          apply Finset.sum_congr rfl
          intro i hi
          have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [show (n + 1 - i) = (n - i) + 1 by omega]
          have hprod : DifferentiableWithinAt ℝ
              (fun y => V i y * W (n - i) y) S x := by
            exact (hVdiff i hin).mul (hWdiff (n - i) (Nat.sub_le n i))
          rw [fderivWithin_const_mul (huniq x hx) hprod (n.choose i : ℝ)]
          rw [smul_apply, smul_eq_mul,
            fderivWithin_fun_mul (huniq x hx) (hVdiff i hin)
              (hWdiff (n - i) (Nat.sub_le n i)), add_apply]
          simp only [smul_apply, smul_eq_mul]
          rw [hVderiv i hin, hWderiv (n - i) (Nat.sub_le n i)]
          ring
        · intro i hi
          have hprod : DifferentiableWithinAt ℝ
              (fun y => V i y * W (n - i) y) S x := by
            exact (hVdiff i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).mul
              (hWdiff (n - i) (Nat.sub_le n i))
          exact hprod.const_mul (n.choose i : ℝ)
      calc
        iteratedFDerivWithin ℝ (n + 1) (fun t => v t * w t) S x (fun _ => z) =
            (fderivWithin ℝ (fun y => iteratedFDerivWithin ℝ n
              (fun t => v t * w t) S y (fun _ => z)) S x) z := by
          symm
          exact diagonal_fderivWithin huniq (hv.mul hw) hx z
        _ = (fderivWithin ℝ (fun y => ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (V i y * W (n - i) y)) S x) z := by
          rw [fderivWithin_congr' hpoint hx]
        _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
              (V i x * W (n + 1 - i) x + V (i + 1) x * W (n - i) x) := hsum
        _ = ∑ i ∈ Finset.range (n + 2), ((n + 1).choose i : ℝ) *
              (V i x * W (n + 1 - i) x) := by
          calc
            _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
                  (V i x * W (n + 1 - i) x)) +
                (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
                  (V (i + 1) x * W (n - i) x)) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = _ := (Finset.sum_choose_succ_mul (fun i j => V i x * W j x) n).symm

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

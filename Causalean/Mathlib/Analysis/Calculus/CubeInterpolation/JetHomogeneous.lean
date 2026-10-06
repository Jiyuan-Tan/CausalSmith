module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Basic
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.JetSymmetry
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Jets of homogeneous Taylor terms

The homogeneous terms of a finite Fréchet Taylor expression have zero jets
away from their own degree. At the matching degree, symmetry of the iterated
derivative recovers the original ordered coordinate partial.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- A homogeneous Taylor term of degree `k` has zero coordinate partial of
every smaller order `j` at its center. -/
theorem homogeneous_taylor_jet_below_degree {d j k : ℕ} (hjk : j < k)
    (u : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (f : Fin j → Fin d) :
    coordPartial j
      (fun z => (Nat.factorial k : ℝ)⁻¹ *
        iteratedFDeriv ℝ k u x (fun _ => z - x)) f x = 0 := by
  let A := (Nat.factorial k : ℝ)⁻¹ • iteratedFDeriv ℝ k u x
  let D : (Fin d → ℝ) →L[ℝ] (Fin k → (Fin d → ℝ)) :=
    ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ (Fin d → ℝ))
  have hfun : (fun z => (Nat.factorial k : ℝ)⁻¹ *
      iteratedFDeriv ℝ k u x (fun _ => z - x)) =
      (fun z => A (D (z - x))) := by
    funext z
    simp [A, D, smul_eq_mul]
  unfold coordPartial
  rw [hfun]
  change (iteratedFDeriv ℝ j (fun z => (A ∘ D) (z - x)) x)
    (fun i => Pi.single (f i) (1 : ℝ)) = 0
  rw [iteratedFDeriv_comp_sub]
  simp only [sub_self]
  rw [D.iteratedFDeriv_comp_right A.contDiff 0 le_rfl, A.iteratedFDeriv_eq]
  have hzero : A.iteratedFDeriv j (0 : Fin k → (Fin d → ℝ)) = 0 := by
    apply norm_eq_zero.mp
    have h := A.norm_iteratedFDeriv_le' j (fun _ => (0 : Fin d → ℝ))
    simp only [Fintype.card_fin] at h
    have hz : (fun _ : Fin k => (0 : Fin d → ℝ)) = 0 := rfl
    rw [hz, norm_zero, zero_pow (by omega : k - j ≠ 0), mul_zero] at h
    exact le_antisymm (by simpa using h) (norm_nonneg _)
  simp only [map_zero]
  rw [hzero]
  simp

/-- A homogeneous Taylor term of degree `k` has zero coordinate partial of
every larger order `j` at its center. -/
theorem homogeneous_taylor_jet_above_degree {d j k : ℕ} (hkj : k < j)
    (u : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (f : Fin j → Fin d) :
    coordPartial j
      (fun z => (Nat.factorial k : ℝ)⁻¹ *
        iteratedFDeriv ℝ k u x (fun _ => z - x)) f x = 0 := by
  let A := (Nat.factorial k : ℝ)⁻¹ • iteratedFDeriv ℝ k u x
  let D : (Fin d → ℝ) →L[ℝ] (Fin k → (Fin d → ℝ)) :=
    ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ (Fin d → ℝ))
  have hfun : (fun z => (Nat.factorial k : ℝ)⁻¹ *
      iteratedFDeriv ℝ k u x (fun _ => z - x)) =
      (fun z => A (D (z - x))) := by
    funext z
    simp [A, D, smul_eq_mul]
  unfold coordPartial
  rw [hfun]
  change (iteratedFDeriv ℝ j (fun z => (A ∘ D) (z - x)) x)
    (fun i => Pi.single (f i) (1 : ℝ)) = 0
  rw [iteratedFDeriv_comp_sub]
  simp only [sub_self]
  rw [D.iteratedFDeriv_comp_right A.contDiff 0 le_rfl, A.iteratedFDeriv_eq]
  have hzero : A.iteratedFDeriv j (0 : Fin k → (Fin d → ℝ)) = 0 := by
    classical
    simp only [ContinuousMultilinearMap.iteratedFDeriv]
    apply Finset.sum_eq_zero
    intro e _
    have he : j ≤ k := by
      simpa using Fintype.card_le_of_injective e e.injective
    omega
  simp only [map_zero]
  rw [hzero]
  simp

/-- If [a function is k times continuously differentiable at a point](hyp:hu), then for [any
sequence of k coordinate directions](hyp:f), [the order-k coordinate partial along that sequence of
the degree-k Taylor term centred at the point, evaluated at the point, equals the same coordinate
partial of the function there](goal). -/
theorem homogeneous_taylor_jet_at_degree {d k : ℕ}
    {u : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hu : ContDiffAt ℝ k u x) (f : Fin k → Fin d) :
    coordPartial k
      (fun z => (Nat.factorial k : ℝ)⁻¹ *
        iteratedFDeriv ℝ k u x (fun _ => z - x)) f x =
      coordPartial k u f x := by
  -- Differentiation produces a permutation sum. The iterated derivative is
  -- symmetric at a C^k point, so division by k! leaves one ordered value.
  classical
  let A := (Nat.factorial k : ℝ)⁻¹ • iteratedFDeriv ℝ k u x
  let g' : (Fin d → ℝ) → ℝ := fun y => A (fun _ => y)
  have hfun : (fun z => (Nat.factorial k : ℝ)⁻¹ *
      iteratedFDeriv ℝ k u x (fun _ => z - x)) =
      (fun z => g' (z - x)) := by
    funext z
    simp [g', A, smul_eq_mul]
  unfold coordPartial
  rw [hfun, iteratedFDeriv_comp_sub]
  simp only [sub_self]
  change (iteratedFDeriv ℝ k (fun z => A (fun _ => z)) 0)
    (fun i => Pi.single (f i) (1 : ℝ)) = _
  rw [A.iteratedFDeriv_comp_diagonal]
  simp only [A, smul_apply, smul_eq_mul]
  have hperm (σ : Equiv.Perm (Fin k)) :
      iteratedFDeriv ℝ k u x (fun i => Pi.single (f (σ i)) (1 : ℝ)) =
        iteratedFDeriv ℝ k u x (fun i => Pi.single (f i) (1 : ℝ)) := by
    simpa only [Function.comp_def] using
      finite_order_iteratedFDeriv_perm hu
        (fun i => Pi.single (f i) (1 : ℝ)) σ
  simp_rw [hperm]
  have hn : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  simp [Fintype.card_perm, hn]

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

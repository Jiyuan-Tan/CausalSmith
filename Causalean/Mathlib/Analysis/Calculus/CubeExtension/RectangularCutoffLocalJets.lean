module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.JetNorm
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularCutoffZero
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Jet bounds inside the support box of a cutoff extension

Within-box derivative bounds for a response and ambient derivative bounds for
a fixed smooth cutoff control the product jets at interior box points. This
is the local estimate used before extending the bound by zero off the cutoff
support.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open scoped ContDiff

/-- If [the box with corners lo, hi strictly contains the normalized
cube](hyp:hmargin), [χ is smooth](hyp:hχ), and [its ambient derivatives of every
order up to m + 1 are bounded in operator norm by B ≥ 0](hyp:hB,hχbound), then
[there is a positive constant C such that for every response v in the intrinsic
Hölder ball of order m, exponent s and radius R ≥ 0 on the closed box, every
ambient derivative of order at most m of the zero extension of χ·v from the box
has operator norm at most C·R at each point of the open box](goal). The constant
does not depend on the response or its radius.

Use `norm_iteratedFDerivWithin_smul_le` on the closed box, the coordinate-basis
multilinear norm estimate, and equality of within and ambient derivatives at
interior points. Local equality of the cutoff extension with the product
transfers this estimate to its ambient jets. -/
theorem exists_rectCutoffExtension_local_jet_constant (d m : ℕ) (s : ℝ)
    (lo hi : Fin d → ℝ) (hmargin : ∀ i, lo i < -1 ∧ 1 < hi i)
    (χ : (Fin d → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (B : ℝ) (hB : 0 ≤ B)
    (hχbound : ∀ j ≤ m + 1, ∀ x,
      ‖iteratedFDeriv ℝ j χ x‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (v : (Fin d → ℝ) → ℝ) (R : ℝ), 0 ≤ R →
        HolderBallOn (rectBox lo hi) m s R v →
      ∀ j ≤ m, ∀ x ∈ rectOpenBox lo hi,
          ‖iteratedFDeriv ℝ j (rectCutoffExtension lo hi χ v) x‖ ≤ C * R := by
  classical
  obtain ⟨K, hK, hcoord⟩ := exists_coord_multilinear_norm_constant d m
  refine ⟨B * K * (2 : ℝ) ^ m + 1, by positivity, ?_⟩
  intro v R hR hv j hj x hx
  have hwidth : ∀ i, lo i < hi i := by
    intro i
    have h := hmargin i
    linarith
  have huniq : UniqueDiffOn ℝ (rectBox lo hi) :=
    uniqueDiffOn_rectBox lo hi hwidth
  have hopen : IsOpen (rectOpenBox lo hi) := by
    have h := isOpen_set_pi (Set.finite_univ : (Set.univ : Set (Fin d)).Finite)
      (s := fun i => Set.Ioo (lo i) (hi i)) (fun i _ => isOpen_Ioo)
    simpa [rectOpenBox, Set.pi, Set.mem_Ioo] using h
  have hsub : rectOpenBox lo hi ⊆ rectBox lo hi := by
    intro y hy i
    exact ⟨(hy i).1.le, (hy i).2.le⟩
  have hbox : x ∈ rectBox lo hi := hsub hx
  have hnhds : rectBox lo hi ∈ nhds x :=
    Filter.mem_of_superset (hopen.mem_nhds hx) hsub
  have hvAt : ContDiffAt ℝ m v x := hv.regularity.contDiffAt hnhds
  have hprod : ContDiffAt ℝ m (fun y => χ y * v y) x :=
    (hχ.contDiffAt.of_le (by exact_mod_cast le_top)).mul hvAt
  have hlocal : rectCutoffExtension lo hi χ v =ᶠ[nhds x]
      (fun y => χ y * v y) := by
    filter_upwards [hnhds] with y hy
    simp [rectCutoffExtension, hy]
  have hjet : iteratedFDeriv ℝ j (rectCutoffExtension lo hi χ v) x =
      iteratedFDeriv ℝ j (fun y => χ y * v y) x :=
    (hlocal.iteratedFDeriv ℝ j).eq_of_nhds
  have hwithin : ∀ k ≤ m, ‖iteratedFDerivWithin ℝ k v (rectBox lo hi) x‖ ≤ K * R := by
    intro k hk
    apply hcoord k hk _ R hR
    intro f
    simpa only [coordJetOn, Real.norm_eq_abs] using hv.derivBound k hk f x hbox
  have hsum := norm_iteratedFDerivWithin_smul_le
    (f := χ) (g := v) (s := rectBox lo hi)
    (hχ.contDiffOn.of_le (by exact_mod_cast le_top)) hv.regularity
    huniq hbox (n := j) (by exact_mod_cast hj)
  have hprodEq : iteratedFDerivWithin ℝ j (fun y => χ y * v y)
      (rectBox lo hi) x = iteratedFDeriv ℝ j (fun y => χ y * v y) x :=
    iteratedFDerivWithin_eq_iteratedFDeriv huniq
      (hprod.of_le (by exact_mod_cast hj)) hbox
  rw [hjet, ← hprodEq]
  have hsumBound :
      (∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i χ (rectBox lo hi) x‖ *
          ‖iteratedFDerivWithin ℝ (j - i) v (rectBox lo hi) x‖) ≤
        (2 : ℝ) ^ j * (B * (K * R)) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (B * (K * R)) := by
        apply Finset.sum_le_sum
        intro i hmem
        have hi' : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hmem)
        have hχi : ‖iteratedFDerivWithin ℝ i χ (rectBox lo hi) x‖ ≤ B := by
          rw [iteratedFDerivWithin_eq_iteratedFDeriv huniq
            (hχ.contDiffAt.of_le (by exact_mod_cast le_top)) hbox]
          exact hχbound i (by omega) x
        have hvi := hwithin (j - i) (by omega)
        have hBKR : 0 ≤ K * R := mul_nonneg hK.le hR
        calc
          (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i χ (rectBox lo hi) x‖ *
              ‖iteratedFDerivWithin ℝ (j - i) v (rectBox lo hi) x‖
              ≤ (j.choose i : ℝ) * B * (K * R) := by gcongr
          _ = (j.choose i : ℝ) * (B * (K * R)) := by ring
      _ = (2 : ℝ) ^ j * (B * (K * R)) := by
        rw [← Finset.sum_mul]
        norm_cast
        rw [Nat.sum_range_choose]
  calc
    ‖iteratedFDerivWithin ℝ j (fun y => χ y * v y) (rectBox lo hi) x‖
        ≤ (2 : ℝ) ^ j * (B * (K * R)) := hsum.trans hsumBound
    _ ≤ (2 : ℝ) ^ m * (B * (K * R)) := by
      gcongr
      norm_num
    _ ≤ (B * K * (2 : ℝ) ^ m + 1) * R := by
      have : 0 ≤ R := hR
      nlinarith

end Causalean.Mathlib.Analysis.Calculus.CubeExtension

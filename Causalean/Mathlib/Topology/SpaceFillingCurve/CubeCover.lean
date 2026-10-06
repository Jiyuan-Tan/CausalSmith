module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.CurveCells

/-!
# Dyadic cube cover

Every point of the closed unit cube lies in a cell of each finite dyadic grid.
This is the finite covering input for surjectivity of the limiting traversal.
-/

public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- Given [a cube dimension](hyp:d), [a dyadic traversal](hyp:T), [a dyadic level](hyp:n),
and [a point certified to lie in the unit cube](hyp:x,hx), [some level cell contains that point](goal). -/
theorem DyadicTraversal.cubeCell_cover {d : ℕ} (T : DyadicTraversal d)
    (n : ℕ) (x : Fin d → ℝ) (hx : InUnitCube x) :
    ∃ k : Fin (2 ^ (d * n)), dyadicCubeCell T n k x := by
  -- For each coordinate, clip `⌊2^n * x i⌋₊` to `2^n - 1`.
  -- The resulting grid tuple contains x, including coordinates equal to 1.
  -- Use `(T.bijective n).2` to obtain its traversal index.
  let q : ℕ := 2 ^ n
  have hq : 0 < q := by dsimp [q]; positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let a : Fin d → Fin q := fun i =>
    ⟨min ⌊(q : ℝ) * x i⌋₊ (q - 1),
      lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hq (by omega))⟩
  have ha (i : Fin d) :
      (a i).val / (q : ℝ) ≤ x i ∧
        x i ≤ ((a i).val + 1) / (q : ℝ) := by
    have hxi := hx i
    have hx0 : (0 : ℝ) ≤ x i := hxi.1
    have hx1 : x i ≤ 1 := hxi.2
    have hprod0 : (0 : ℝ) ≤ (q : ℝ) * x i := mul_nonneg hqR.le hx0
    have hprodle : (q : ℝ) * x i ≤ q := by nlinarith
    have hfloorle : ⌊(q : ℝ) * x i⌋₊ ≤ q :=
      Nat.floor_le_of_le hprodle
    by_cases hf : ⌊(q : ℝ) * x i⌋₊ < q
    · have hamin : (a i).val = ⌊(q : ℝ) * x i⌋₊ := by
        simp [a, Nat.min_eq_left (by omega : ⌊(q : ℝ) * x i⌋₊ ≤ q - 1)]
      have hlower := Nat.floor_le hprod0
      have hupper := Nat.lt_floor_add_one ((q : ℝ) * x i)
      rw [hamin]
      constructor
      · apply (div_le_iff₀ hqR).2
        nlinarith
      · apply (le_div_iff₀ hqR).2
        nlinarith
    · have heq : ⌊(q : ℝ) * x i⌋₊ = q := by omega
      have hlower := Nat.floor_le hprod0
      have hx_eq : x i = 1 := by rw [heq] at hlower; nlinarith
      have hamin : (a i).val = q - 1 := by simp [a, heq]
      rw [hamin, hx_eq]
      constructor
      · apply (div_le_iff₀ hqR).2
        have : q - 1 < q := Nat.sub_lt hq (by omega)
        simpa only [one_mul] using
          (show ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) by exact_mod_cast (Nat.le_of_lt this))
      · have hsub : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
        rw [show ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) by exact_mod_cast hsub]
        exact le_of_eq (div_self hqR.ne').symm
  have ha' : ∀ i, x i ∈ Set.Icc
      (((a i).val : ℝ) / (2 ^ n : ℝ))
      ((((a i).val : ℝ) + 1) / (2 ^ n : ℝ)) := by
    intro i
    simpa [q] using ha i
  obtain ⟨k, hk⟩ := (T.bijective n).2 a
  refine ⟨k, ?_⟩
  intro i
  simpa [dyadicCubeCell, hk] using ha' i

end Causalean.Mathlib.Topology.SpaceFillingCurve

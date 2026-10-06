module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.CurveCells

/-!
# Nearby parameter cells

Two parameters within one level's time-cell width can be assigned closed
time cells with equal or consecutive traversal indices.
-/

public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- Given [a cube dimension and level](hyp:d,n), [two unit-interval parameters](hyp:s,t,hs,ht), and [a gap no larger than one level-cell width](hyp:hgap),
[the parameters lie in equal or neighboring dyadic time cells](goal). -/
theorem exists_neighboring_timeCells (d n : ℕ) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hgap : |s - t| ≤ (1 : ℝ) / (2 : ℝ) ^ (d * n)) :
    ∃ k l : Fin (2 ^ (d * n)),
      s ∈ dyadicTimeCell d n k ∧ t ∈ dyadicTimeCell d n l ∧
      k.val ≤ l.val + 1 ∧ l.val ≤ k.val + 1 := by
  -- Clamp the floor of `2^(d*n) * s` and `2^(d*n) * t` at the final cell.
  -- Closed endpoints permit either adjacent index at a subdivision boundary.
  -- Write `q = 2^(d*n)` (strictly positive). For each `u ∈ [0,1]`, use
  -- `min ⌊q*u⌋₊ (q-1)`; `Nat.floor_le` and `Nat.lt_floor_add_one` put `u`
  -- in its closed cell, including `u=1`. Multiplying `hgap` by `q` shows
  -- `|q*s-q*t| ≤ 1`. The two clamped floors then differ by at most one;
  -- prove each orientation using `Nat.le_floor` and
  -- `Nat.floor_le_of_le`, with the final-cell clamp handled by `omega`.
  let q : ℕ := 2 ^ (d * n)
  have hq : 0 < q := by dsimp [q]; positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let idx (u : ℝ) : Fin q :=
    ⟨min ⌊(q : ℝ) * u⌋₊ (q - 1),
      lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hq (by omega))⟩
  have hcell (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      (idx u).val / (q : ℝ) ≤ u ∧
        u ≤ ((idx u).val + 1) / (q : ℝ) := by
    have hprod0 : (0 : ℝ) ≤ (q : ℝ) * u := mul_nonneg hqR.le hu.1
    have hprodle : (q : ℝ) * u ≤ q := by nlinarith [hu.2]
    have hfloorle : ⌊(q : ℝ) * u⌋₊ ≤ q := Nat.floor_le_of_le hprodle
    by_cases hf : ⌊(q : ℝ) * u⌋₊ < q
    · have hidx : (idx u).val = ⌊(q : ℝ) * u⌋₊ := by
        simp [idx, Nat.min_eq_left (by omega : ⌊(q : ℝ) * u⌋₊ ≤ q - 1)]
      have hlower := Nat.floor_le hprod0
      have hupper := Nat.lt_floor_add_one ((q : ℝ) * u)
      rw [hidx]
      constructor
      · apply (div_le_iff₀ hqR).2
        nlinarith
      · apply (le_div_iff₀ hqR).2
        nlinarith
    · have heq : ⌊(q : ℝ) * u⌋₊ = q := by omega
      have hlower := Nat.floor_le hprod0
      have hu_eq : u = 1 := by rw [heq] at hlower; nlinarith
      have hidx : (idx u).val = q - 1 := by simp [idx, heq]
      rw [hidx, hu_eq]
      constructor
      · apply (div_le_iff₀ hqR).2
        simpa only [one_mul] using
          (show ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) by exact_mod_cast (Nat.sub_le q 1))
      · have hsub : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
        rw [show ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) by exact_mod_cast hsub]
        exact le_of_eq (div_self hqR.ne').symm
  have hscaled : |(q : ℝ) * s - (q : ℝ) * t| ≤ 1 := by
    have hqpow : (q : ℝ) = (2 : ℝ) ^ (d * n) := by simp [q]
    have hgap' : |s - t| ≤ 1 / (q : ℝ) := by simpa [hqpow] using hgap
    have hmul := mul_le_mul_of_nonneg_left hgap' hqR.le
    rw [mul_div_cancel₀ _ hqR.ne'] at hmul
    calc
      |(q : ℝ) * s - (q : ℝ) * t| = |(q : ℝ) * (s - t)| := by rw [mul_sub]
      _ = (q : ℝ) * |s - t| := by rw [abs_mul, abs_of_pos hqR]
      _ ≤ 1 := hmul
  have hfloor_close (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
      (h : u ≤ v + 1) : ⌊u⌋₊ ≤ ⌊v⌋₊ + 1 := by
    have hvlt := Nat.lt_floor_add_one v
    have hult : u < ((⌊v⌋₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
    have hf := (Nat.floor_lt' (by omega : ⌊v⌋₊ + 2 ≠ 0)).2 hult
    omega
  have hst : (q : ℝ) * s ≤ (q : ℝ) * t + 1 := by
    have := (abs_le.mp hscaled).2
    linarith
  have hts : (q : ℝ) * t ≤ (q : ℝ) * s + 1 := by
    have := (abs_le.mp hscaled).1
    linarith
  have hfs : ⌊(q : ℝ) * s⌋₊ ≤ ⌊(q : ℝ) * t⌋₊ + 1 :=
    hfloor_close _ _ (mul_nonneg hqR.le hs.1) (mul_nonneg hqR.le ht.1) hst
  have hft : ⌊(q : ℝ) * t⌋₊ ≤ ⌊(q : ℝ) * s⌋₊ + 1 :=
    hfloor_close _ _ (mul_nonneg hqR.le ht.1) (mul_nonneg hqR.le hs.1) hts
  have hindices : (idx s).val ≤ (idx t).val + 1 ∧
      (idx t).val ≤ (idx s).val + 1 := by
    dsimp [idx]
    omega
  refine ⟨⟨(idx s).val, by simpa only [q] using (idx s).isLt⟩,
    ⟨(idx t).val, by simpa only [q] using (idx t).isLt⟩, ?_, ?_,
    hindices.1, hindices.2⟩
  · simpa only [dyadicTimeCell, Set.mem_Icc, Nat.cast_pow, Nat.cast_ofNat, q]
      using hcell s hs
  · simpa only [dyadicTimeCell, Set.mem_Icc, Nat.cast_pow, Nat.cast_ofNat, q]
      using hcell t ht

end Causalean.Mathlib.Topology.SpaceFillingCurve

module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CellAverages

/-! Orthogonal aggregation of the corrected-mean remainder bands in (27).
The initial band is separated before bounding the higher bands by their squared norms. -/

public section

noncomputable section
open scoped RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Distinct dyadic bands contribute only their own squared norms to a finite sum. -/
-- @node: band_remainder_sum_norm_sq
lemma band_remainder_sum_norm_sq (L T : ℕ) (hL : Dyadic L)
    (s : Finset ℕ) (hs : ∀ t ∈ s, t ≤ T) (r : ℕ → Hj (2 ^ T * L)) :
    ‖∑ t ∈ s, Qband L (2 ^ T * L) t (r t)‖ ^ 2 =
      ∑ t ∈ s, ‖Qband L (2 ^ T * L) t (r t)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro t ht
  rw [inner_sum]
  rw [Finset.sum_eq_single t]
  · exact real_inner_self_eq_norm_sq _
  · intro u hu hut
    exact (band_projection_algebra L T hL).2.1 t u (hs t ht) (hs u hu)
      (Ne.symm hut) (r t) (r u)
  · exact fun h => (h ht).elim

/-- Squared bounds on individual bands aggregate under a single square root. -/
-- @node: band_remainder_sum_norm_le
lemma band_remainder_sum_norm_le (L T : ℕ) (hL : Dyadic L)
    (s : Finset ℕ) (hs : ∀ t ∈ s, t ≤ T) (r : ℕ → Hj (2 ^ T * L))
    (b : ℕ → ℝ)
    (hb : ∀ t ∈ s, ‖Qband L (2 ^ T * L) t (r t)‖ ^ 2 ≤ b t) :
    ‖∑ t ∈ s, Qband L (2 ^ T * L) t (r t)‖ ≤ Real.sqrt (∑ t ∈ s, b t) := by
  have hbnon : 0 ≤ ∑ t ∈ s, b t :=
    Finset.sum_nonneg (fun t ht => (sq_nonneg _).trans (hb t ht))
  apply (Real.le_sqrt (norm_nonneg _) hbnon).2
  rw [band_remainder_sum_norm_sq L T hL s hs r]
  exact Finset.sum_le_sum hb

/-- Separating the initial band yields precisely the second-remainder envelope in (27).
The inputs are squared estimates for the higher bands; the aggregation itself introduces no
factor depending on the number of bands. -/
-- @node: multiband_remainder_norm_le_of_band_bounds
lemma multiband_remainder_norm_le_of_band_bounds (K L T : ℕ) (hL : Dyadic L)
    (kt : ℕ → ℕ) (r : ℕ → Hj (2 ^ T * L))
    (hzero : ‖Qband L (2 ^ T * L) 0 (r 0)‖ ≤ 2800 * (K : ℝ) ^ (-1 / 5 : ℝ))
    (hhigh : ∀ t ∈ Finset.range T,
      ‖Qband L (2 ^ T * L) (t + 1) (r (t + 1))‖ ^ 2 ≤
        2400 ^ 2 * ((kt (t + 1) : ℝ) ^ (-1 / 5 : ℝ) /
          ((2 ^ t * L : ℕ) : ℝ) ^ 2)) :
    ‖∑ t ∈ Finset.range (T + 1), Qband L (2 ^ T * L) t (r t)‖ ≤
      2800 * (K : ℝ) ^ (-1 / 5 : ℝ) +
        2400 * Real.sqrt (∑ t ∈ Finset.range T,
          (kt (t + 1) : ℝ) ^ (-1 / 5 : ℝ) / ((2 ^ t * L : ℕ) : ℝ) ^ 2) := by
  have htail : ‖∑ t ∈ Finset.range T,
      Qband L (2 ^ T * L) (t + 1) (r (t + 1))‖ ^ 2 ≤
      2400 ^ 2 * (∑ t ∈ Finset.range T,
        (kt (t + 1) : ℝ) ^ (-1 / 5 : ℝ) / ((2 ^ t * L : ℕ) : ℝ) ^ 2) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    calc
      _ = ∑ t ∈ Finset.range T, ‖Qband L (2 ^ T * L) (t + 1) (r (t + 1))‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [inner_sum, Finset.sum_eq_single t]
        · exact real_inner_self_eq_norm_sq _
        · intro u hu hut
          exact (band_projection_algebra L T hL).2.1 (t + 1) (u + 1)
            (by have := Finset.mem_range.mp ht; omega)
            (by have := Finset.mem_range.mp hu; omega)
            (by omega) (r (t + 1)) (r (u + 1))
        · exact fun h => (h ht).elim
      _ ≤ ∑ t ∈ Finset.range T, 2400 ^ 2 *
          ((kt (t + 1) : ℝ) ^ (-1 / 5 : ℝ) / ((2 ^ t * L : ℕ) : ℝ) ^ 2) :=
        Finset.sum_le_sum hhigh
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hsum : 0 ≤ ∑ t ∈ Finset.range T,
      (kt (t + 1) : ℝ) ^ (-1 / 5 : ℝ) / ((2 ^ t * L : ℕ) : ℝ) ^ 2 := by
    exact Finset.sum_nonneg (fun t _ =>
      div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _))
  have htail' : ‖∑ t ∈ Finset.range T,
      Qband L (2 ^ T * L) (t + 1) (r (t + 1))‖ ≤
      2400 * Real.sqrt (∑ t ∈ Finset.range T,
        (kt (t + 1) : ℝ) ^ (-1 / 5 : ℝ) / ((2 ^ t * L : ℕ) : ℝ) ^ 2) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
    simpa only [mul_pow, Real.sq_sqrt hsum] using htail
  rw [Finset.sum_range_succ']
  exact (norm_add_le _ _).trans (add_le_add htail' hzero) |>.trans_eq (add_comm _ _)

end CausalSmith.Stat.DensityEffectRoughNull

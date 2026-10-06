module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.HistogramCellRepresentation
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ResolutionBounds

/-! # Nested evaluation cells and the clipped pilot

Dyadic divisibility puts each evaluation cell inside a pilot cell. Consequently
histograms, the clipped pilot, and Taylor coefficients are constant there,
including the closed right endpoint of the final cell.
-/

public section
open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Increasing the exponent preserves divisibility of the exact dyadic resolutions.  Under [the displayed assumptions and inputs](hyp:n,p,q,hpq), [the stated conclusion holds](goal). -/
-- @node: dyadicResolution_dvd_of_le
lemma dyadicResolution_dvd_of_le (n : ℕ) (p q : ℝ) (hpq : p ≤ q) :
    dyadicResolution n p ∣ dyadicResolution n q := by
  unfold dyadicResolution
  split_ifs with hn
  · exact dvd_refl 1
  · apply pow_dvd_pow
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_right hpq
    have hm : (1 : ℝ) ≤ blockSize n 0 := by
      exact_mod_cast blockSize_pos_of_threshold n (Nat.le_of_not_gt hn) 0
    exact div_nonneg (Real.log_nonneg hm) (Real.log_pos (by norm_num)).le

/-- Both correction resolutions refine the pilot partition.  Under [the displayed assumptions and inputs](hyp:n), [the stated conclusion holds](goal). -/
-- @node: pilotResolution_dvd_correctionResolutions
lemma pilotResolution_dvd_correctionResolutions (n : ℕ) :
    pilotResolution n ∣ quadraticResolution n ∧ pilotResolution n ∣ cubicResolution n := by
  constructor
  · exact dyadicResolution_dvd_of_le n _ _ (by norm_num)
  · exact dyadicResolution_dvd_of_le n _ _ (by norm_num)

/-- For an integer refinement, every fine cell is contained in a coarse cell.  Under [the displayed assumptions and inputs](hyp:J,K,hJ,hK,hJK,l), [the stated conclusion holds](goal). -/
-- @node: cell_refinement_exists
lemma cell_refinement_exists {J K : ℕ} (hJ : 0 < J) (hK : 0 < K)
    (hJK : J ∣ K) (l : Fin K) : ∃ r : Fin J, cell K l ⊆ cell J r := by
  obtain ⟨m, rfl⟩ := hJK
  have hm : 0 < m := by nlinarith
  have hr : l.val / m < J := (Nat.div_lt_iff_lt_mul hm).2 (by simpa [Nat.mul_comm] using l.isLt)
  let r : Fin J := ⟨l.val / m, hr⟩
  refine ⟨r, ?_⟩
  have hlo : r.val * m ≤ l.val := by
    dsimp [r]
    exact Nat.div_mul_le_self _ _
  have hhi : l.val + 1 ≤ (r.val + 1) * m := by
    have hd := Nat.mod_lt l.val hm
    have he := Nat.mod_add_div l.val m
    dsimp [r]
    nlinarith
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hKr : (0 : ℝ) < J * m := mul_pos hJr hmr
  have hlower : (r.val : ℝ) / J ≤ (l.val : ℝ) / (J * m) := by
    apply (div_le_div_iff₀ hJr hKr).2
    have hh : (r.val : ℝ) * m ≤ l.val := by exact_mod_cast hlo
    nlinarith
  have hupper : ((l.val : ℝ) + 1) / (J * m) ≤ ((r.val : ℝ) + 1) / J := by
    apply (div_le_div_iff₀ hKr hJr).2
    have hh : (l.val : ℝ) + 1 ≤ (r.val + 1) * m := by exact_mod_cast hhi
    nlinarith
  intro x hx
  have hxspace := cell_subset_covariateSpace hK l hx
  unfold cell at hx ⊢
  simp only [Nat.cast_mul] at hx
  split_ifs at hx ⊢ with hf hc hc
  · exact ⟨hlower.trans hx.1, hx.2⟩
  · exact ⟨hlower.trans hx.1, hxspace.2⟩
  · have hlast : r.val + 1 = J := by
      have hrl := r.isLt
      nlinarith
    exact (hf hlast).elim
  · exact ⟨hlower.trans hx.1, hx.2.trans_le hupper⟩

/-- A marked histogram takes the same value at any two points in one cell.  Under [the displayed assumptions and inputs](hyp:n,K,hK,i,b,l,x,y,hx,hy), [the stated conclusion holds](goal). -/
-- @node: markedHistogram_eq_of_mem_cell
lemma markedHistogram_eq_of_mem_cell {n K : ℕ} (hK : 0 < K)
    (ω : TwoSample n n) (i : Fin 7) (b : Fin 4) (l : Fin K)
    {x y : ℝ} (hx : x ∈ cell K l) (hy : y ∈ cell K l) :
    markedHistogram ω i K b x = markedHistogram ω i K b y := by
  classical
  unfold markedHistogram
  split_ifs
  · rfl
  · apply Finset.sum_congr rfl
    intro r _
    have hmem : x ∈ cell K r ↔ y ∈ cell K r := by
      by_cases hrl : r = l
      · subst r
        exact iff_of_true hx hy
      · have hd := Set.disjoint_left.mp (cell_disjoint hK hrl)
        exact iff_of_false (fun h => hd h hx) (fun h => hd h hy)
    simp only [hmem]

/-- On any partition refining the pilot partition, the pilot equals its
midpoint value throughout each cell.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,n,K,hK,hdiv,l,x,hx), [the stated conclusion holds](goal). -/
-- @node: pilot_eq_midpoint_of_refinement
lemma pilot_eq_midpoint_of_refinement (c_f C_f : ℝ) {n K : ℕ}
    (hK : 0 < K) (hdiv : pilotResolution n ∣ K) (ω : TwoSample n n)
    (l : Fin K) {x : ℝ} (hx : x ∈ cell K l) :
    pilot c_f C_f ω x = pilot c_f C_f ω (midpoint K l) := by
  have hJ : 0 < pilotResolution n := by
    unfold pilotResolution dyadicResolution
    split_ifs <;> positivity
  obtain ⟨r, hr⟩ := cell_refinement_exists hJ hK hdiv l
  unfold pilot
  split_ifs
  · rfl
  · funext i
    rw [markedHistogram_eq_of_mem_cell hJ ω i 0 r (hr hx)
      (hr (midpoint_mem_cell hK l))]

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

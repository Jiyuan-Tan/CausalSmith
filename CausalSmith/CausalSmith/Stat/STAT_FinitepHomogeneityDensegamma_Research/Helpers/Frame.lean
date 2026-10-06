module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.MarkedTable
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Finite-moment homogeneity testing: Helpers/Frame. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- [Finite-overlap smooth-field tool](goal). The public frame object consists only of the displayed cosine/sine coordinates and their finite coefficient fields. Copula coupling, coarse opposite tents, marked tables and mixture integration are defined separately by `copulaPrior`. For positive rank K, the two active coordinates on each covariate cell are cos(π(Kx−i)/2) and sin(π(Kx−i)/2). This statement assumes [the K parameter](hyp:K), [the i parameter](hyp:i), [the x parameter](hyp:x). -/
-- @node: def:frame-handle
def frameCoord (K : ℕ) (i : Fin (K+1)) (x : ℝ) : ℝ :=
  if (i:ℝ)/K ≤ x ∧ x ≤ ((i:ℝ)+1)/K then Real.cos (Real.pi*((K:ℝ)*x-i)/2)
  else if 0 < i.val ∧ ((i:ℝ)-1)/K ≤ x ∧ x ≤ (i:ℝ)/K then Real.sin (Real.pi*((K:ℝ)*x-((i:ℝ)-1))/2)
  else 0 -- @realizes Frame(explicit cosine/sine finite-overlap frame)
/-- Sum the finite cosine/sine frame coordinates against the supplied coefficients. This statement assumes [the K parameter](hyp:K), [the coef parameter](hyp:coef), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def frameField (K : ℕ) (coef : Fin (K+1) → ℝ) (x : ℝ) : ℝ := ∑ i, coef i*frameCoord K i x
/-- On the covariate interval each frame coordinate is a cosine of clipped distance from its node. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: frameCoord_eq_clipped_cos
lemma frameCoord_eq_clipped_cos (K : ℕ) (hK : 0 < K) (i : Fin (K+1))
    (x : unitInterval) :
    frameCoord K i x = Real.cos (Real.pi * min 1 |(K:ℝ)*(x:ℝ)-(i:ℝ)| / 2) := by
  have hKr : (0:ℝ) < K := by exact_mod_cast hK
  have hx : 0 ≤ (x:ℝ) := x.2.1
  unfold frameCoord
  simp only [div_le_iff₀ hKr, le_div_iff₀ hKr]
  split
  · rename_i h
    rw [abs_of_nonneg (by nlinarith : 0 ≤ (K:ℝ)*(x:ℝ)-(i:ℝ)),
      min_eq_right (by nlinarith : (K:ℝ)*(x:ℝ)-(i:ℝ) ≤ 1)]
  · rename_i h
    split
    · rename_i h'
      have hl : (K:ℝ)*(x:ℝ) ≤ (i:ℝ) := by nlinarith [h'.2.2]
      rw [abs_of_nonpos (by linarith : (K:ℝ)*(x:ℝ)-(i:ℝ) ≤ 0),
        min_eq_right (by nlinarith [h'.2.1] : -((K:ℝ)*(x:ℝ)-(i:ℝ)) ≤ 1)]
      have he : Real.pi * -((K:ℝ)*(x:ℝ)-(i:ℝ)) / 2 =
          Real.pi/2 - Real.pi*((K:ℝ)*(x:ℝ)-((i:ℝ)-1))/2 := by ring
      rw [he, Real.cos_pi_div_two_sub]
    · rename_i h'
      have hd : 1 ≤ |(K:ℝ)*(x:ℝ)-(i:ℝ)| := by
        by_cases hi : i.val = 0
        · have hir : (i:ℝ) = 0 := by exact_mod_cast hi
          rw [hir, sub_zero, abs_of_nonneg (mul_nonneg hKr.le hx)]
          by_contra hh
          apply h
          constructor <;> nlinarith
        · have hip : 0 < i.val := Nat.pos_of_ne_zero hi
          by_contra hh
          have ha := abs_lt.mp (lt_of_not_ge hh)
          apply h'
          refine ⟨hip, ?_, ?_⟩
          · nlinarith [ha.1]
          · by_contra hh'
            apply h
            constructor <;> nlinarith [ha.2]
      rw [min_eq_left hd]
      simp only [mul_one, Real.cos_pi_div_two]

/-- Each coordinate is continuous because its clipped-distance cosine formula is continuous. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: continuous_frameCoord
@[fun_prop] lemma continuous_frameCoord (K : ℕ) (hK : 0 < K) (i : Fin (K+1)) :
    Continuous (fun x : unitInterval => frameCoord K i x) := by
  simp_rw [frameCoord_eq_clipped_cos K hK i]
  fun_prop

/-- The specified finite construction is continuous on its covariate domain. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: continuous_frameField
@[fun_prop] lemma continuous_frameField (K : ℕ) (hK : 0 < K) (coef : Fin (K+1) → ℝ) : Continuous (fun x : unitInterval => frameField K coef x) := by
  unfold frameField
  fun_prop
/-- A nonzero coordinate lies at distance strictly less than one from its fine-grid node. This statement assumes [the hK condition](hyp:hK), [the hi condition](hyp:hi). [This is the stated conclusion](goal). -/
-- @node: frameCoord_nonzero_distance
lemma frameCoord_nonzero_distance (K : ℕ) (hK : 0 < K) (i : Fin (K+1))
    (x : unitInterval) (hi : frameCoord K i x ≠ 0) :
    |(K:ℝ)*(x:ℝ)-(i:ℝ)| < 1 := by
  by_contra h
  apply hi
  rw [frameCoord_eq_clipped_cos K hK i x, min_eq_left (le_of_not_gt h)]
  simp only [mul_one, Real.cos_pi_div_two]

/-- Every covariate belongs to a closed fine cell, including the right endpoint. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: frame_cell_index
lemma frame_cell_index (K : ℕ) (hK : 0 < K) (x : unitInterval) :
    ∃ j : ℕ, j < K ∧ (j:ℝ) ≤ (K:ℝ)*(x:ℝ) ∧ (K:ℝ)*(x:ℝ) ≤ (j:ℝ)+1 := by
  let t : ℝ := (K:ℝ)*(x:ℝ)
  have ht : 0 ≤ t := mul_nonneg (Nat.cast_nonneg K) x.2.1
  have htK : t ≤ K := by dsimp [t]; nlinarith [x.2.2, (Nat.cast_nonneg K : (0:ℝ) ≤ K)]
  by_cases hf : Nat.floor t < K
  · exact ⟨Nat.floor t, hf, Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
  · refine ⟨K-1, by omega, ?_⟩
    have hj : ((K-1:ℕ):ℝ)+1 = K := by exact_mod_cast (show K-1+1=K by omega)
    have hfloor : (K:ℝ) ≤ Nat.floor t := by exact_mod_cast (Nat.le_of_not_gt hf)
    constructor
    · change ((K-1:ℕ):ℝ) ≤ t
      linarith [Nat.floor_le ht]
    · change t ≤ ((K-1:ℕ):ℝ)+1
      linarith

/-- The two coordinates of a fine cell form its cosine and sine partition of unity. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: frame_partition
lemma frame_partition (K : ℕ) (hK : 0 < K) (x : unitInterval) :
    ∑ i : Fin (K+1), frameCoord K i x^2 = 1 := by
  obtain ⟨j, hj, hl, hu⟩ := frame_cell_index K hK x
  let i0 : Fin (K+1) := ⟨j, by omega⟩
  let i1 : Fin (K+1) := ⟨j+1, by omega⟩
  have hi : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; dsimp [i0, i1] at this; omega
  have h0 : frameCoord K i0 x = Real.cos (Real.pi*((K:ℝ)*(x:ℝ)-j)/2) := by
    rw [frameCoord_eq_clipped_cos K hK i0 x]
    change Real.cos (Real.pi * min 1 |(K:ℝ)*(x:ℝ)-(j:ℝ)| / 2) = _
    rw [abs_of_nonneg (by linarith), min_eq_right (by linarith)]
  have h1 : frameCoord K i1 x = Real.sin (Real.pi*((K:ℝ)*(x:ℝ)-j)/2) := by
    rw [frameCoord_eq_clipped_cos K hK i1 x]
    change Real.cos (Real.pi * min 1 |(K:ℝ)*(x:ℝ)-((j+1:ℕ):ℝ)| / 2) = _
    rw [Nat.cast_add, Nat.cast_one, abs_of_nonpos (by linarith), min_eq_right (by linarith)]
    have he : Real.pi * -((K:ℝ)*(x:ℝ)-((j:ℝ)+1))/2 =
        Real.pi/2-Real.pi*((K:ℝ)*(x:ℝ)-j)/2 := by ring
    rw [he, Real.cos_pi_div_two_sub]
  have hz (i : Fin (K+1)) (hmem : i ∉ ({i0,i1} : Finset (Fin (K+1)))) :
      frameCoord K i x^2 = 0 := by
    have hval : i.val ≠ j ∧ i.val ≠ j+1 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff, i0, i1] using hmem
    have hzero : frameCoord K i x = 0 := by
      by_contra hn
      have ha := abs_lt.mp (frameCoord_nonzero_distance K hK i x hn)
      have hlo : (j:ℝ) < (i:ℝ)+1 := by linarith [ha.1]
      have hup : (i:ℝ) < ((j+2:ℕ):ℝ) := by push_cast; linarith [ha.2]
      have hlo' : j < i.val+1 := by exact_mod_cast hlo
      have hup' : i.val < j+2 := by exact_mod_cast hup
      omega
    rw [hzero]; norm_num
  calc
    _ = ∑ i ∈ ({i0,i1} : Finset (Fin (K+1))), frameCoord K i x^2 :=
      (Finset.sum_subset (Finset.subset_univ _) (fun i _ hmem => hz i hmem)).symm
    _ = frameCoord K i0 x^2+frameCoord K i1 x^2 := by simp [hi]
    _ = 1 := by rw [h0, h1]; exact Real.cos_sq_add_sin_sq _

/-- Frame overlap: the displayed mathematical construction or bound. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: frame_overlap
lemma frame_overlap (K : ℕ) (hK : 0 < K) (x : unitInterval) : (Finset.univ.filter (fun i : Fin (K+1) => frameCoord K i x ≠ 0)).card ≤ 2 := by
  let t : ℝ := (K:ℝ)*(x:ℝ)
  have ht : 0 ≤ t := mul_nonneg (Nat.cast_nonneg K) x.2.1
  have hf := Nat.floor_le ht
  have hf' := Nat.lt_floor_add_one t
  apply (Finset.card_le_card_of_injOn (s := Finset.univ.filter
    (fun i : Fin (K+1) => frameCoord K i x ≠ 0))
    (t := {Nat.floor t, Nat.floor t+1}) Fin.val ?_ ?_).trans Finset.card_le_two
  · intro i hi
    have ha := abs_lt.mp (frameCoord_nonzero_distance K hK i x (Finset.mem_filter.mp hi).2)
    have hl : (Nat.floor t : ℝ) < (i:ℝ)+1 := by dsimp [t] at *; linarith [ha.1]
    have hu : (i:ℝ) < (Nat.floor t : ℝ)+2 := by dsimp [t] at *; linarith [ha.2]
    have hl' : Nat.floor t < i.val+1 := by exact_mod_cast hl
    have hu' : i.val < Nat.floor t+2 := by exact_mod_cast hu
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro i hi j hj hij
    exact Fin.ext hij

end CausalSmith.Stat.FinitepHomogeneityDensegamma

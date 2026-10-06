module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.CalibrationRegularity
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairRootSelection
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ScalarImplicitFunction
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Smooth actual fair cells

The literal fair selector stays in its interior bracket. The comparator's
positive logarithm arguments and the shifted-risk denominator therefore make
the actual cell formulas smooth wherever the selected root is smooth. Compactness
then bounds all fixed-order derivatives of these fully substituted formulas.
-/
public section
noncomputable section
open scoped BigOperators ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The local sign interpolation is bounded on its entire real carrier. [the stated conclusion](goal) holds. -/
-- @node: localSignField_abs_le_two
lemma localSignField_abs_le_two (u : ℝ) (s : Bool × Bool) :
    |localSignField u s| ≤ 2 := by
  have hs (b : Bool) : |signValue b| = 1 := by
    cases b <;> norm_num [signValue]
  unfold localSignField
  calc
    _ ≤ |signValue s.1 * Real.cos (Real.pi*u/2)| +
        |signValue s.2 * Real.sin (Real.pi*u/2)| := abs_add_le _ _
    _ ≤ 2 := by
      simp only [abs_mul, hs, one_mul]
      linarith [Real.abs_cos_le_one (Real.pi*u/2), Real.abs_sin_le_one (Real.pi*u/2)]

/-- Any nonnegative logistic shift has a positive denominator at a positive risk. Under the stated assumptions. [The stated hypotheses](hyp:ht,hξ) hold, and [the stated conclusion follows](goal). -/
-- @node: riskShift_denominator_pos
lemma riskShift_denominator_pos (t ξ : ℝ) (ht : 0 ≤ t) (hξ : 0 ≤ ξ) :
    0 < 1 + (Real.exp t - 1)*ξ := by
  have hd : 0 ≤ Real.exp t - 1 := by
    have he := Real.add_one_le_exp t
    linarith
  positivity

/-- [A nonzero shifted-risk denominator makes the two-parameter risk map smooth. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:hden). -/
-- @node: riskShift_contDiffAt
lemma riskShift_contDiffAt (v : Fin 2 → ℝ)
    (hden : 1 + (Real.exp (v 0) - 1) * (v 1) ≠ 0) :
    ContDiffAt ℝ ⊤ (fun w : Fin 2 → ℝ => riskShift (w 0) (w 1)) v := by
  unfold riskShift
  exact (by fun_prop : ContDiffAt ℝ ⊤ (fun w : Fin 2 → ℝ => Real.exp (w 0)*w 1) v).div
    (by fun_prop) hden

/-- The actual logarithmic comparator is smooth through both zero axes and
on full neighborhoods of the endpoints of the prescribed effect interval. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ). -/
-- @node: comparatorEffect_contDiffAt
lemma comparatorEffect_contDiffAt (v : Fin 2 → ℝ)
    (ht : v 0 ∈ Set.Icc (0 : ℝ) (1 / 4)) (hδ : |v 1| ≤ 1 / 100) :
    ContDiffAt ℝ ⊤ (fun w : Fin 2 → ℝ => comparatorEffect (w 0) (w 1)) v := by
  obtain ⟨hB, ha, hb, _, _⟩ := fair_matching_denominators (v 0) (v 1) ht hδ
  unfold comparatorEffect
  dsimp only
  apply ContDiffAt.sub
  · apply ContDiffAt.add
    · fun_prop
    · apply ContDiffAt.log
      · apply ContDiffAt.sub contDiffAt_const
        apply ContDiffAt.div
        · fun_prop
        · fun_prop
        · exact ne_of_gt (mul_pos (by norm_num) hB)
      · exact ne_of_gt ha
  · apply ContDiffAt.log
    · apply ContDiffAt.add contDiffAt_const
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · exact ne_of_gt (mul_pos (by norm_num) hB)
    · exact ne_of_gt hb

/-- [The actual selected fair control risk remains interior before any
smoothness of the selector is used. [the documented result](goal) Under [the stated assumptions](hyp:hδ). -/
-- @node: localFairControlRisk_bounds
lemma localFairControlRisk_bounds (b : Bool) (s : Bool × Bool) (t δ u : ℝ)
    (hδ : |δ| ≤ 1 / 100) :
    (if b then fairRoot t δ u + δ*localSignField u s else fairRoot t δ u)
      ∈ Set.Icc (1 / 4 : ℝ) (3 / 5) := by
  have hp := fairRoot_mem_bracket t δ u
  have hz := localSignField_abs_le_two u s
  have hprod : |δ*localSignField u s| ≤ 1 / 50 := by
    rw [abs_mul]
    calc
      _ ≤ (1 / 100 : ℝ)*2 := mul_le_mul hδ hz (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  obtain ⟨hlo, hhi⟩ := abs_le.mp hprod
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
    constructor <;> linarith [hp.1, hp.2]

/-- [Composing the smooth actual root with the interior risk maps proves
smoothness of every actual fair cell, including the comparator cells. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ,hroot). -/
-- @node: localFairCell_contDiffAt_of_root
lemma localFairCell_contDiffAt_of_root (v : Fin 3 → ℝ)
    (ht : v 0 ∈ Set.Icc (0 : ℝ) (1 / 4)) (hδ : |v 1| ≤ 1 / 100)
    (hroot : ContDiffAt ℝ ∞ (fun w : Fin 3 → ℝ => fairRoot (w 0) (w 1) (w 2)) v)
    (b : Bool) (s : Bool × Bool) (a y : Bool) :
    ContDiffAt ℝ ∞ (localFairCell b s a y) v := by
  let p : (Fin 3 → ℝ) → ℝ := fun w => fairRoot (w 0) (w 1) (w 2)
  let μ : (Fin 3 → ℝ) → ℝ := fun w => if b then p w + w 1*localSignField (w 2) s else p w
  let T : (Fin 3 → ℝ) → ℝ := fun w => if b then w 0 else comparatorEffect (w 0) (w 1)
  have hp : ContDiffAt ℝ ∞ p v := hroot
  have hμ : ContDiffAt ℝ ∞ μ v := by
    cases b
    · exact hp
    · dsimp [μ]
      unfold localSignField
      fun_prop
  have hT : ContDiffAt ℝ ∞ T v := by
    cases b
    · have hf : ContDiffAt ℝ ∞ (fun w : Fin 3 → ℝ => ![w 0,w 1]) v := by
        apply contDiffAt_pi.mpr
        intro i
        fin_cases i
        · change ContDiffAt ℝ ∞ (fun w : Fin 3 → ℝ => w 0) v
          fun_prop
        · change ContDiffAt ℝ ∞ (fun w : Fin 3 → ℝ => w 1) v
          fun_prop
      exact ((comparatorEffect_contDiffAt ![v 0,v 1] ht hδ).of_le le_top).comp v hf
    · dsimp [T]
      fun_prop
  have hμpos : 0 ≤ μ v := by
    have h := (localFairControlRisk_bounds b s (v 0) (v 1) (v 2) hδ).1
    dsimp [μ, p]
    linarith
  have hTpos : 0 ≤ T v := by
    have h := comparatorEffect_range_bounds (v 0) (v 1) ht hδ
    cases b <;> dsimp [T] <;> linarith [ht.1]
  have hshift : ContDiffAt ℝ ∞ (fun w => riskShift (T w) (μ w)) v := by
    unfold riskShift
    apply ContDiffAt.div
    · fun_prop
    · fun_prop
    · exact ne_of_gt (riskShift_denominator_pos _ _ hTpos hμpos)
  change ContDiffAt ℝ ∞ (fun w => (1 / 2 : ℝ) *
    (if y then (if a then riskShift (T w) (μ w) else μ w)
      else 1-(if a then riskShift (T w) (μ w) else μ w))) v
  cases a <;> cases y <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop

/-- [The closed effect-amplitude-coordinate parameter region is compact. [the stated conclusion](goal) holds. -/
-- @node: fairParameterRegion_isCompact
lemma fairParameterRegion_isCompact (ε : ℝ) : IsCompact (fairParameterRegion ε) := by
  let K : Set (Fin 3 → ℝ) := Set.pi Set.univ
    (fun i => if i = 0 then Set.Icc (0 : ℝ) (1 / 4)
      else if i = 1 then Set.Icc (-ε) ε else Set.Icc (0 : ℝ) 1)
  have hK : IsCompact K := isCompact_univ_pi (fun i => by
    split
    · exact isCompact_Icc
    · split <;> exact isCompact_Icc)
  have heq : K = fairParameterRegion ε := by
    ext v
    simp only [K, Set.mem_pi, Set.mem_univ, forall_const, fairParameterRegion, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨by simpa using h 0, abs_le.mpr (by simpa using h 1), by simpa using h 2⟩
    · rintro ⟨h0,h1,h2⟩ i
      fin_cases i
      · simpa using h0
      · simpa using abs_le.mp h1
      · simpa using h2
  rwa [heq] at hK

/-- Smoothness to every finite order uniformly bounds each fixed derivative
on a compact parameter set; analyticity is not needed. [the documented result](goal) Under [the stated assumptions](hyp:f,hK,hf). -/
-- @node: calibration_compact_infty_derivative_bounds
lemma calibration_compact_infty_derivative_bounds (d : ℕ)
    (f : (Fin d → ℝ) → ℝ) (K : Set (Fin d → ℝ)) (hK : IsCompact K)
    (hf : ∀ v ∈ K, ContDiffAt ℝ ∞ f v) (m : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ v ∈ K, ‖iteratedFDeriv ℝ m f v‖ ≤ B := by
  have hc : ContinuousOn (iteratedFDeriv ℝ m f) K := by
    intro v hv
    exact ((hf v hv).continuousAt_iteratedFDeriv
      (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨max C 1,lt_of_lt_of_le (by norm_num) (le_max_right _ _),
    fun v hv => (hC v hv).trans (le_max_left _ _)⟩

/-- [Root smoothness on neighborhoods of the closed region supplies both cell
smoothness and all fixed-order bounds for the fully substituted roots and cells. [the documented result](goal) Under [the stated assumptions](hyp:hroot). Under [the stated assumptions](hyp:hε). -/
-- @node: localFairCell_smooth_derivative_bounds_of_root
lemma localFairCell_smooth_derivative_bounds_of_root (ε : ℝ) (hε : ε ≤ 1 / 100)
    (hroot : ∀ v ∈ fairParameterRegion ε,
      ContDiffAt ℝ ∞ (fun w : Fin 3 → ℝ => fairRoot (w 0) (w 1) (w 2)) v) :
    (∀ b s a y, ContDiffOn ℝ ∞ (localFairCell b s a y) (fairParameterRegion ε)) ∧
    (∀ m : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ v ∈ fairParameterRegion ε,
      ‖iteratedFDeriv ℝ m (fun w : Fin 3 → ℝ => fairRoot (w 0) (w 1) (w 2)) v‖ ≤ B ∧
      ∀ b s a y, ‖iteratedFDeriv ℝ m (localFairCell b s a y) v‖ ≤ B) := by
  have hcell (v : Fin 3 → ℝ) (hv : v ∈ fairParameterRegion ε) (b s a y) :=
    localFairCell_contDiffAt_of_root v hv.1 (hv.2.1.trans hε) (hroot v hv) b s a y
  refine ⟨fun b s a y v hv => (hcell v hv b s a y).contDiffWithinAt, ?_⟩
  intro m
  obtain ⟨Bq,hBq,hq⟩ := calibration_compact_infty_derivative_bounds 3 _ _
    (fairParameterRegion_isCompact ε) hroot m
  let I := Bool × (Bool × Bool) × Bool × Bool
  have hb : ∀ i : I, ∃ B : ℝ, 0 < B ∧ ∀ v ∈ fairParameterRegion ε,
      ‖iteratedFDeriv ℝ m (localFairCell i.1 i.2.1 i.2.2.1 i.2.2.2) v‖ ≤ B := by
    intro i
    exact calibration_compact_infty_derivative_bounds 3 _ _ (fairParameterRegion_isCompact ε)
      (fun v hv => hcell v hv _ _ _ _) m
  choose B hB hBound using hb
  refine ⟨Bq + ∑ i : I, B i, ?_, ?_⟩
  · exact add_pos hBq (Finset.sum_pos (fun i _ => hB i) Finset.univ_nonempty)
  · intro v hv
    refine ⟨(hq v hv).trans (le_add_of_nonneg_right
      (Finset.sum_nonneg (fun i _ => (hB i).le))), ?_⟩
    intro b s a y
    exact (hBound (b,s,a,y) v hv).trans ((Finset.single_le_sum
      (fun i _ => (hB i).le) (Finset.mem_univ (b,s,a,y))).trans
        (le_add_of_nonneg_left hBq.le))

end CausalSmith.Stat.LogoddsLowsmoothFrontier

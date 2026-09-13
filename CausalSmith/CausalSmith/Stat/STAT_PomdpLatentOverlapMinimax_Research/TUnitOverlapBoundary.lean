import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.BiasVariance
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.TwoPoint

set_option linter.style.longLine false

/-! # Unit-overlap boundary -/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory

-- @node: prop:unit-overlap-boundary
/-- At `C=1` the target and behavior stationary laws coincide, immediate weighting
has parametric risk, and the minimax rate is exactly order `T⁻¹`; for positive
mixing/overlap scales this exponent differs from the fixed-`C>1` exponent. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta). [the stated conclusion](goal). -/
theorem unit_overlap_boundary {t0 zeta : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    (∀ {T nX nH : Nat} (M : RawPomdpExperiment T nX nH),
      LatentOverlapClass t0 zeta 1 M →
      stationaryLaw (policyKernel M M.e) =
        stationaryLaw (policyKernel M M.b)) ∧
    (∃ cImmediate : ℝ, 0 < cImmediate ∧ ∀ T : Nat, 1 ≤ T →
      Causalean.Stat.worstCaseRisk
        (observedRisk (T := T) (t0 := t0) (zeta := zeta) (C := 1))
        (phiwObservable (T := T) 0) ≤
      cImmediate / T) ∧
    (∃ cLower cUpper : ℝ, 0 < cLower ∧ cLower ≤ cUpper ∧
      ∃ TStar : Nat, 1 ≤ TStar ∧ ∀ T ≥ TStar,
        cLower / T ≤ minimaxRisk T t0 zeta 1 ∧
          minimaxRisk T t0 zeta 1 ≤ cUpper / T) ∧
    rateExponent t0 zeta < 1 := by
  have halpha0 : 0 < mixingAlpha t0 := by
    simp only [mixingAlpha]
    positivity
  have halpha1 : mixingAlpha t0 < 1 := by
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr ht0)
  have hL1 : 1 < policyFactor zeta := by
    rw [policyFactor, Real.one_lt_exp_iff]
    exact hzeta
  let cI : ℝ := 2 *
    (policyFactor zeta * (1 + 4 / (policyFactor zeta - 1)) +
      4 / (1 - mixingAlpha t0))
  have hcI : 0 < cI := by
    dsimp [cI]
    positivity
  have himmediate : ∀ T : Nat, 1 ≤ T →
      Causalean.Stat.worstCaseRisk
        (observedRisk (T := T) (t0 := t0) (zeta := zeta) (C := 1))
        (phiwObservable (T := T) 0) ≤ cI / T := by
    intro T hT
    have hkT : 0 < T := Nat.zero_lt_of_lt hT
    let m0 := parametricModel T t0 zeta 1 false hT ht0 hzeta le_rfl
    letI : Nonempty (ModelIndex T t0 zeta 1) := ⟨m0⟩
    simp [phiwObservable, hkT]
    apply Causalean.Stat.worstCaseRisk_le
    intro m
    have h := radius_sensitive_phiw ht0 hzeta (C := (1 : ℝ)) le_rfl
      hT m.raw m.mem (k := 0) (by omega)
    change Causalean.Stat.sqRisk (obsLaw m.raw)
      (phiwEstimator 0 hkT m.raw.b m.raw.e) (targetValue m.raw) ≤ cI / T
    calc
      Causalean.Stat.sqRisk (obsLaw m.raw)
          (phiwEstimator 0 hkT m.raw.b m.raw.e) (targetValue m.raw) ≤
          (2 / (T : ℝ)) *
            (policyFactor zeta * (1 + 4 / (policyFactor zeta - 1)) +
              4 / (1 - mixingAlpha t0)) := by
        simpa [overlapRadius] using h
      _ = cI / T := by
        dsimp [cI]
        ring
  refine ⟨?_, ⟨cI, hcI, himmediate⟩, ?_, ?_⟩
  · intro T nX nH M hM
    have htv := stationary_tv_le_overlapRadius hM (C := (1 : ℝ)) le_rfl
    have htv0 : tvNorm (stationaryLaw (policyKernel M M.b) -
        stationaryLaw (policyKernel M M.e)) = 0 := by
      apply le_antisymm
      · simpa [overlapRadius] using htv
      · unfold tvNorm
        positivity
    have hsum : ∑ s, |stationaryLaw (policyKernel M M.b) s -
        stationaryLaw (policyKernel M M.e) s| = 0 := by
      unfold tvNorm at htv0
      norm_num at htv0
      simpa [Pi.sub_apply] using htv0
    funext s
    have habs : |stationaryLaw (policyKernel M M.b) s -
        stationaryLaw (policyKernel M M.e) s| = 0 := by
      apply le_antisymm
      · calc
          |stationaryLaw (policyKernel M M.b) s -
              stationaryLaw (policyKernel M M.e) s| ≤
              ∑ i, |stationaryLaw (policyKernel M M.b) i -
                stationaryLaw (policyKernel M M.e) i| :=
            Finset.single_le_sum
              (f := fun i ↦ |stationaryLaw (policyKernel M M.b) i -
                stationaryLaw (policyKernel M M.e) i|)
              (fun i _ ↦ abs_nonneg _) (Finset.mem_univ s)
          _ = 0 := hsum
      · exact abs_nonneg _
    exact (sub_eq_zero.mp (abs_eq_zero.mp habs)).symm
  · let cL : ℝ := Real.exp (-(1 / 4 : ℝ)) / 64
    let cU : ℝ := max cI cL
    refine ⟨cL, cU, ?_, le_max_right _ _, 1, le_rfl, ?_⟩
    · dsimp [cL]
      positivity
    · intro T hT
      have hfloor := (uniform_parametric_floor ht0 hzeta T hT (1 : ℝ) le_rfl).1
      have hmini : minimaxRisk T t0 zeta 1 ≤
          Causalean.Stat.worstCaseRisk
            (observedRisk (T := T) (t0 := t0) (zeta := zeta) (C := 1))
            (phiwObservable (T := T) 0) := by
        apply Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
        intro est m
        exact observedRisk_nonneg est m
      constructor
      · dsimp [cL]
        convert hfloor using 1 <;> field_simp
      · calc
          minimaxRisk T t0 zeta 1 ≤ _ := hmini
          _ ≤ cI / T := himmediate T hT
          _ ≤ cU / T := by
            exact div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg T)
  · unfold rateExponent
    have hprod : 0 < t0 * zeta := mul_pos ht0 hzeta
    rw [div_lt_one (by linarith)]
    linarith

end CausalSmith.Stat.PomdpLatentOverlapMinimax

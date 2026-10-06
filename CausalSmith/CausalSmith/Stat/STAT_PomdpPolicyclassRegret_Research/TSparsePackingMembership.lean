module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseRetention

/-! # Membership and separation of the sparse common-kernel packing -/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax

-- @node: prop:sparse-packing-membership
/-- For [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and [the policy-overlap scale assumption](hyp:hzeta),
this establishes [the sparse packing membership result](goal). -/
theorem sparse_packing_membership (t0 zeta : ℝ) (ht0 : 0 < t0)
    (hzeta : 0 < zeta) :
    ∃ a : ℝ, 0 < a ∧
      ∀ (T M : Nat) (hM : 2 ≤ M),
        ∃ (code : Fin M → Fin (codeDimension M) → Bool),
          ∃ hCode : CodeSeparated code,
          ∀ (Q : Nat) (C : ℝ) (hQ : 1 ≤ Q) (hC : 1 < C)
            (v : Fin M),
              PolicyListClass t0 zeta C
                (sparsePackingExperiment T M (codeDimension M) Q
                  (codeDimension_pos M hM) rfl hM t0 zeta C code hCode v) ∧
              ∀ w : Fin M, w ≠ v →
                policyValue
                  (sparsePackingExperiment T M (codeDimension M) Q
                    (codeDimension_pos M hM) rfl hM t0 zeta C code hCode v) v -
                policyValue
                  (sparsePackingExperiment T M (codeDimension M) Q
                    (codeDimension_pos M hM) rfl hM t0 zeta C code hCode v) w ≥
                  a * overlapRadius C * mixingAlpha t0 ^ Q := by
  let a : ℝ := sparseSignal t0 * (1 - mixingAlpha t0) *
    (1 - Real.exp (-(1 - (policyFactor zeta)⁻¹) / 8)) / 4
  have hα : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    apply Real.exp_lt_one_iff.mpr
    have h : 0 < 1 / t0 := by positivity
    linarith
  have hα0 : 0 < mixingAlpha t0 := by
    unfold mixingAlpha
    positivity
  have hc : 0 < sparseSignal t0 := by
    unfold sparseSignal
    linarith
  have hL : 1 < policyFactor zeta := by
    unfold policyFactor
    exact Real.one_lt_exp_iff.mpr hzeta
  have hκ : 0 < 1 - Real.exp (-(1 - (policyFactor zeta)⁻¹) / 8) := by
    have hinv : (policyFactor zeta)⁻¹ < 1 :=
      (inv_lt_one₀ (by linarith)).mpr hL
    have he : Real.exp (-(1 - (policyFactor zeta)⁻¹) / 8) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      linarith
    linarith
  refine ⟨a, ?_, ?_⟩
  · dsimp [a]
    positivity
  · intro T M hM
    obtain ⟨code, hCode⟩ := codeSeparated_exists M hM
    refine ⟨code, hCode, ?_⟩
    intro Q C hQ hC v
    let d := codeDimension M
    have hd : 0 < d := codeDimension_pos M hM
    constructor
    · exact {
        t0_pos := ht0
        zeta_pos := hzeta
        C_ge_one := hC.le
        finite_state := sparse_packing_finite_state T M d Q hd rfl hM
          t0 zeta C code hCode v
        sequential_ignorability := sparse_packing_sequential_ignorability T M d Q hd rfl hM
          t0 zeta C code hCode v
        stationary_start := sparse_packing_stationary_start T M d Q hd rfl hM
          t0 zeta C ht0 hzeta hC.le code hCode v
        uniform_contraction := sparse_packing_uniform_contraction T M d Q hd rfl hM
          t0 zeta C ht0 hzeta hC.le code hCode v
        action_overlap := sparse_packing_action_overlap T M d Q hd rfl hM
          t0 zeta C hzeta code hCode v
        latent_stationary_overlap := sparse_packing_latent_stationary_overlap T M d Q hd rfl hM
          t0 zeta C ht0 hzeta hC code hCode v
        supplied_list := sparse_packing_supplied_list T M d Q hd rfl hM
          t0 zeta C hzeta code hCode v }
    · intro w hw
      rw [sparse_packing_policy_value_formula T M d Q hd rfl hM
          t0 zeta C ht0 hzeta hC.le code hCode v v,
        sparse_packing_policy_value_formula T M d Q hd rfl hM
          t0 zeta C ht0 hzeta hC.le code hCode v w]
      have hvv : hammingDistance code v v = 0 := by simp [hammingDistance]
      simp only [hvv, Nat.cast_zero, mul_zero, zero_div, sub_zero, one_pow]
      have hq : 0 ≤ overlapRadius C := by
        change 0 ≤ (C - 1) / C
        exact div_nonneg (by linarith) (by linarith)
      have hp0 : 0 ≤ (policyFactor zeta)⁻¹ := by positivity
      have hp1 : (policyFactor zeta)⁻¹ < 1 :=
        (inv_lt_one₀ (by linarith)).mpr hL
      have hgap := sparse_terminal_value_gap_numeric code hCode v w hw.symm Q hQ hd
        (sparseSignal t0) (overlapRadius C) (mixingAlpha t0) (policyFactor zeta)⁻¹
        hc.le hq hα0.le hα hp0 hp1
      change _ ≥ a * overlapRadius C * mixingAlpha t0 ^ Q
      convert hgap using 1
      dsimp only [sparseEpsilon, depthMass, a, d]
      ring

end CausalSmith.Stat.PomdpPolicyclassRegret

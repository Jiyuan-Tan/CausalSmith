module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseObservedRewardAveraging
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.TContextualObservedWordCertificate

/-! # Contextual observed-word KL bound, including stationary prefixes -/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory InformationTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax

-- @node: thm:contextual-observed-kl
/-- For [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and [the policy-overlap scale assumption](hyp:hzeta),
this establishes [the contextual observed KL result](goal). -/
theorem contextual_observed_kl (t0 zeta : ℝ) (ht0 : 0 < t0)
    (hzeta : 0 < zeta) :
    resetRatio t0 < 1 ∧
      ∀ (T M Q : Nat) (hT : 1 ≤ T) (hM : 2 ≤ M) (hQ : 1 ≤ Q)
        (C : ℝ) (hC : 1 < C)
        (code : Fin M → Fin (codeDimension M) → Bool)
        (hCode : CodeSeparated code) (v : Fin M),
          (∀ w : FiniteObsView T (codeDimension M * hdepth Q) 2,
            0 < (sparseObservedPMF (T := T) (Q := Q) (codeDimension_pos M hM)
              t0 zeta C code ⟨0, by omega⟩ true w).toReal) ∧
          InformationTheory.klDiv
            (obsLaw (sparsePackingExperiment T M (codeDimension M) Q
              (codeDimension_pos M hM) rfl hM t0 zeta C code hCode v).Mx.toRawB)
            (sparseReferenceLaw T M (codeDimension M) Q
              (codeDimension_pos M hM) (by omega) t0 zeta C code) ≠ ⊤ ∧
          (InformationTheory.klDiv
              (obsLaw (sparsePackingExperiment T M (codeDimension M) Q
                (codeDimension_pos M hM) rfl hM t0 zeta C code hCode v).Mx.toRawB)
              (sparseReferenceLaw T M (codeDimension M) Q
                (codeDimension_pos M hM) (by omega) t0 zeta C code)).toReal ≤
              klConstant t0 zeta * T * overlapRadius C ^ 2 *
                mixingAlpha t0 ^ (2 * Q) *
                  policyFactor zeta ^ (-(Q : ℤ)) := by
  constructor
  · exact resetRatio_lt_one t0 ht0
  · intro T M Q hT hM hQ C hC code hCode v
    let hd := codeDimension_pos M hM
    let v0 : Fin M := ⟨0, by omega⟩
    have hfinite := sparse_observed_klDiv_ne_top (T := T) (Q := Q) hd
      t0 zeta C ht0 hzeta hC.le code v v0
    have hdecode := embed_klDiv_le
      (F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false)
      (G := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v0 true) rfl
    have hbudget := sparse_observed_klDiv_le_budget (T := T) (Q := Q) hd
      t0 zeta C ht0 hzeta hC.le (by omega) code v v0
    refine ⟨?_, ?_, ?_⟩
    · intro w
      exact sparse_fair_observed_pmf_pos hd t0 zeta C ht0 hzeta hC.le code v0 w
    · dsimp only [sparsePackingExperiment, ListPomdpExperiment.toRawB, sparseReferenceLaw]
      exact ne_top_of_le_ne_top hfinite hdecode
    · dsimp only [sparsePackingExperiment, ListPomdpExperiment.toRawB, sparseReferenceLaw]
      exact (ENNReal.toReal_mono hfinite hdecode).trans hbudget

end CausalSmith.Stat.PomdpPolicyclassRegret

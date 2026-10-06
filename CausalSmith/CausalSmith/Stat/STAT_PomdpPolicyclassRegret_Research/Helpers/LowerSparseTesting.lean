module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.LowerDepthTuning
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.TestingRegret
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.TContextualObservedKL
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.TSparsePackingMembership
public import Causalean.Stat.Minimax.FanoInformationRadius

/-! # Sparse common-kernel testing and minimax lower rate

The reference-law information radius transports equation (48) to the Fano
mixture. The common revealed policies make every observable selector one test,
and the sparse packing's value gap then gives equations (49) and (51).
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory InformationTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators ENNReal

/-- The reference-law KL budget bounds the mixture KL used by the proved Fano lemma. For
[the sample space](hyp:Ω), [the candidate-policy count](hyp:M),
[the candidate-policy count assumption](hyp:hM), [the probability law](hyp:P),
[the probability law assumption](hyp:hP), [the reference probability law](hyp:P0),
[the reference probability law assumption](hyp:hP0), and [the fin assumption](hyp:hfin), this
establishes [the lower reference KL controls mixture result](goal). -/
-- @node: lower_reference_kl_controls_mixture
lemma lower_reference_kl_controls_mixture {Ω : Type} [MeasurableSpace Ω]
    (M : Nat) (hM : 2 ≤ M) (P : Fin M → Measure Ω)
    (hP : ∀ v, IsProbabilityMeasure (P v)) (P0 : Measure Ω)
    (hP0 : IsProbabilityMeasure P0) (hfin : ∀ v, klDiv (P v) P0 ≠ ⊤) :
    (M : ℝ)⁻¹ * ∑ v, (klDiv (P v) (fanoMixture M P)).toReal ≤
      (M : ℝ)⁻¹ * ∑ v, (klDiv (P v) P0).toReal := by
  let : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  let : ∀ v, IsProbabilityMeasure (P v) := hP
  let : IsProbabilityMeasure P0 := hP0
  simpa [Causalean.Stat.uniformMutualInformation, Causalean.Stat.uniformMixture,
    Causalean.Stat.mixture, fanoMixture] using
    Causalean.Stat.uniformMutualInformation_le_average_kl P P0 hfin

/-- A componentwise reference budget forces every measurable test's error floor. For
[the sample space](hyp:Ω),
[the candidate-policy count](hyp:M), [the candidate-policy count assumption](hyp:hM),
[the probability law](hyp:P), [the probability law assumption](hyp:hP),
[the reference probability law](hyp:P0), [the reference probability law assumption](hyp:hP0),
[the fin assumption](hyp:hfin), [the KL assumption](hyp:hKL), [the ψ](hyp:ψ), and
[the ψ assumption](hyp:hψ), this establishes
[the lower test error of reference KL result](goal). -/
-- @node: lower_test_error_of_reference_kl
lemma lower_test_error_of_reference_kl {Ω : Type} [MeasurableSpace Ω]
    (M : Nat) (hM : 2 ≤ M)
    (P : Fin M → Measure Ω) (hP : ∀ v, IsProbabilityMeasure (P v))
    (P0 : Measure Ω) (hP0 : IsProbabilityMeasure P0)
    (hfin : ∀ v, klDiv (P v) P0 ≠ ⊤)
    (hKL : ∀ v, (klDiv (P v) P0).toReal ≤ Real.log (M : ℝ) / 32)
    (ψ : Ω → Fin M) (hψ : Measurable ψ) :
    1 / 8 < (M : ℝ)⁻¹ * ∑ v, (P v).real {w | ψ w ≠ v} := by
  apply testing_test_error_of_small_mixture_kl M hM P hP _ ψ hψ
  apply (lower_reference_kl_controls_mixture M hM P hP P0 hP0 hfin).trans
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) ↦ hKL v)
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  calc
    _ ≤ (M : ℝ)⁻¹ * ∑ _v : Fin M, Real.log (M : ℝ) / 32 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by simp; field_simp

/-- Observed laws of a model are probability measures. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), and [the model](hyp:m), this establishes
[the lower observed law probability result](goal). -/
-- @node: lower_observed_law_probability
lemma lower_observed_law_probability {T M : Nat} (m : ModelIndex T M) :
    IsProbabilityMeasure (obsLaw m.Mx.toRawB) := by
  let : IsProbabilityMeasure m.Mx.law := m.Mx.law_isProbability
  have hobs : Measurable (@obsProj T m.nX m.nH) := by fun_prop
  exact Measure.isProbabilityMeasure_map hobs.aemeasurable

/-- The sparse observed reference is a probability law. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the candidate-policy count assumption](hyp:hM), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), and
[the binary code](hyp:code), this establishes
[the lower sparse reference probability result](goal). -/
-- @node: lower_sparse_reference_probability
lemma lower_sparse_reference_probability {T M d Q : Nat} (hd : 0 < d)
    (hM : 0 < M) (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) :
    IsProbabilityMeasure (sparseReferenceLaw T M d Q hd hM t0 zeta C code) := by
  unfold sparseReferenceLaw obsLaw
  have hobs : Measurable (@obsProj T (d * hdepth Q) (2 * (Q + 1))) := by fun_prop
  exact Measure.isProbabilityMeasure_map hobs.aemeasurable

/-- Data processing preserves finiteness of the sparse reference divergence. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the dim assumption](hyp:hDim), [the candidate-policy count assumption](hyp:hM),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the code assumption](hyp:hCode), and [the codeword index](hyp:v), this establishes
[the lower sparse reference KL finite result](goal). -/
-- @node: lower_sparse_reference_kl_finite
lemma lower_sparse_reference_kl_finite {T M d Q : Nat} (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code) (v : Fin M) :
    klDiv (obsLaw (sparsePackingExperiment T M d Q hd hDim hM
      t0 zeta C code hCode v).Mx.toRawB)
      (sparseReferenceLaw T M d Q hd (by omega) t0 zeta C code) ≠ ⊤ := by
  have hfin := sparse_observed_klDiv_ne_top (T := T) (Q := Q) hd
    t0 zeta C ht0 hzeta hC code v ⟨0, by omega⟩
  have hdecode := embed_klDiv_le
    (F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false)
    (G := sparseFinite (T := T) (Q := Q) hd t0 zeta C code ⟨0, by omega⟩ true) rfl
  exact ne_top_of_le_ne_top hfin hdecode

/-- Across sparse alternatives the selector receives the same alphabet, behavior rule, and
target list, so it is one common observed-word test. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the dim assumption](hyp:hDim), [the candidate-policy count assumption](hyp:hM),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code),
[the code assumption](hyp:hCode), [the observable selector](hyp:sel),
[the codeword index](hyp:v), and [the observed word](hyp:w), this establishes
[the lower sparse selector common rule result](goal). -/
-- @node: lower_sparse_selector_common_rule
lemma lower_sparse_selector_common_rule {T M d Q : Nat} (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M) (t0 zeta C : ℝ)
    (code : Fin M → Fin d → Bool) (hCode : CodeSeparated code)
    (sel : ObservableSelector T M) (v : Fin M) (w : ObsView T (d * hdepth Q)) :
    sel.1 (sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v).nX
      (sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v).Mx.b
      (sparsePackingExperiment T M d Q hd hDim hM t0 zeta C code hCode v).Mx.E w =
    sel.1 (d * hdepth Q) (fun x a ↦ (sparseBehaviorPMF zeta d Q x a).toReal)
      (fun j x a ↦ (sparseTargetPMF (Q := Q) hd zeta code j x a).toReal) w := by
  rfl

/-- The packing and the reference information budget give equation (49), uniformly over
observable selectors and then over the minimax infimum. For [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and [the policy-overlap scale assumption](hyp:hzeta),
this establishes [the lower sparse minimax at depth result](goal). -/
-- @node: lower_sparse_minimax_at_depth
lemma lower_sparse_minimax_at_depth (t0 zeta : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ a : ℝ, 0 < a ∧ ∀ (T M Q : Nat) (C : ℝ),
      1 ≤ T → 2 ≤ M → 1 ≤ Q → 1 < C →
      klConstant t0 zeta * T * overlapRadius C ^ 2 *
        mixingAlpha t0 ^ (2 * Q) * policyFactor zeta ^ (-(Q : ℤ)) ≤
          Real.log (M : ℝ) / 32 →
      a / 8 * overlapRadius C * mixingAlpha t0 ^ Q ≤
        minimaxRegret T M t0 zeta C := by
  obtain ⟨a, ha, hpacking⟩ := sparse_packing_membership t0 zeta ht0 hzeta
  refine ⟨a, ha, ?_⟩
  intro T M Q C hT hM hQ hC hbudget
  obtain ⟨code, hCode, hmembers⟩ := hpacking T M hM
  let hd := codeDimension_pos M hM
  let models := fun v ↦ sparsePackingExperiment T M (codeDimension M) Q hd rfl hM
    t0 zeta C code hCode v
  let P : Fin M → Measure (ObsView T (codeDimension M * hdepth Q)) :=
    fun v ↦ obsLaw (models v).Mx.toRawB
  let P0 := sparseReferenceLaw T M (codeDimension M) Q hd (by omega) t0 zeta C code
  have hP : ∀ v, IsProbabilityMeasure (P v) :=
    fun v ↦ lower_observed_law_probability (models v)
  have hP0 : IsProbabilityMeasure P0 :=
    lower_sparse_reference_probability hd (by omega) t0 zeta C code
  have hfin : ∀ v, klDiv (P v) P0 ≠ ⊤ := fun v ↦
    lower_sparse_reference_kl_finite hd rfl hM t0 zeta C ht0 hzeta hC.le code hCode v
  have hKL : ∀ v, (klDiv (P v) P0).toReal ≤ Real.log (M : ℝ) / 32 := by
    intro v
    exact (((contextual_observed_kl t0 zeta ht0 hzeta).2
      T M Q hT hM hQ C hC code hCode v).2.2).trans hbudget
  have hq : 0 ≤ overlapRadius C := by
    change 0 ≤ (C - 1) / C
    exact div_nonneg (sub_nonneg.mpr hC.le) ((by norm_num : (0 : ℝ) ≤ 1).trans hC.le)
  have hgap0 : 0 ≤ a * overlapRadius C * mixingAlpha t0 ^ Q := by
    exact mul_nonneg (mul_nonneg ha.le hq) (pow_nonneg (Real.exp_pos _).le _)
  have hresult := testing_average_error_le_minimaxRegret hM t0 zeta C
    (a * overlapRadius C * mixingAlpha t0 ^ Q) (1 / 8) hgap0 models
    (fun v ↦ (hmembers Q C hQ hC v).1)
    (fun v w hw ↦ (hmembers Q C hQ hC v).2 w hw) (by
      intro sel
      let ψ : ObsView T (codeDimension M * hdepth Q) → Fin M :=
        sel.1 (codeDimension M * hdepth Q)
          (fun x a ↦ (sparseBehaviorPMF zeta (codeDimension M) Q x a).toReal)
          (fun j x a ↦ (sparseTargetPMF (Q := Q) hd zeta code j x a).toReal)
      have hψ : Measurable ψ := sel.2 _ _ _
      have htest := lower_test_error_of_reference_kl M hM P hP P0 hP0
        hfin hKL ψ hψ
      have hsame (v : Fin M) (w : ObsView T (codeDimension M * hdepth Q)) :
          sel.1 (models v).nX (models v).Mx.b (models v).Mx.E w = ψ w :=
        lower_sparse_selector_common_rule hd rfl hM t0 zeta C code hCode sel v w
      have heq : (M : ℝ)⁻¹ * ∑ v, (P v).real {w | ψ w ≠ v} =
          (M : ℝ)⁻¹ * ∑ v, (P v).real
            {w | sel.1 (models v).nX (models v).Mx.b (models v).Mx.E w ≠ v} := by
        apply congrArg (fun x : ℝ ↦ (M : ℝ)⁻¹ * x)
        apply Finset.sum_congr rfl
        intro v _
        apply congrArg (fun s : Set (ObsView T (codeDimension M * hdepth Q)) ↦
          (P v).real s)
        exact Set.ext fun w ↦
          (congrArg (fun j : Fin M ↦ j ≠ v) (hsame v w)).symm.to_iff
      exact htest.le.trans_eq heq)
  calc
    _ = (a * overlapRadius C * mixingAlpha t0 ^ Q) * (1 / 8) := by ring
    _ ≤ _ := hresult

/-- The observed-information constant is strictly positive. For [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), and [the mixing scale assumption](hyp:ht0), this
establishes [the lower KL constant positivity result](goal). -/
-- @node: lower_klConstant_pos
lemma lower_klConstant_pos (t0 zeta : ℝ) (ht0 : 0 < t0) :
    0 < klConstant t0 zeta := by
  have hα : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    apply Real.exp_lt_one_iff.mpr
    have hinv : 0 < 1 / t0 := by positivity
    linarith
  have hs : 0 < sparseSignal t0 := by
    unfold sparseSignal
    linarith
  unfold klConstant filterConstant
  positivity

/-- Depth tuning and the actual sparse experiment prove the hidden coordinate lower bound (51),
with constants depending only on the regime parameters. For [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and [the policy-overlap scale assumption](hyp:hzeta),
this establishes [the lower sparse hidden component result](goal). -/
-- @node: lower_sparse_hidden_component
lemma lower_sparse_hidden_component (t0 zeta : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ (c2 eta0 : ℝ), 0 < c2 ∧ 0 < eta0 ∧
      ∀ (T M : Nat) (C : ℝ), (hT : 1 ≤ T) → (hM : 2 ≤ M) → 1 < C →
        (listInformationRatio T M (by omega) hM) ≤ eta0 * overlapRadius C ^ 2 →
        c2 * (overlapRadius C ^ (1 - rateExponent t0 zeta) *
          (listInformationRatio T M (by omega) hM) ^ (rateExponent t0 zeta / 2)) ≤
            minimaxRegret T M t0 zeta C := by
  obtain ⟨a, ha, hdepth⟩ := lower_sparse_minimax_at_depth t0 zeta ht0 hzeta
  let B := klConstant t0 zeta
  have hB : 0 < B := lower_klConstant_pos t0 zeta ht0
  let c2 := a * mixingAlpha t0 / 8 * (32 * B) ^ (-(rateExponent t0 zeta / 2))
  refine ⟨c2, lowerDepthThreshold t0 zeta B,
    lower_hidden_rate_constant_pos t0 zeta B a hB ha,
    lowerDepthThreshold_pos t0 zeta B hB, ?_⟩
  intro T M C hT hM hC hsmall
  have hq : 0 < overlapRadius C := by
    change 0 < (C - 1) / C
    exact div_pos (sub_pos.mpr hC) ((by norm_num : (0 : ℝ) < 1).trans hC)
  have hu : 0 < (listInformationRatio T M (by omega) hM) := by
    unfold listInformationRatio
    exact div_pos (Real.log_pos (by exact_mod_cast (show 1 < M by omega)))
      (by exact_mod_cast (show 0 < T by omega))
  let Q := lowerTestingDepth t0 zeta B (overlapRadius C) ((listInformationRatio T M (by omega) hM))
  have hQ : 1 ≤ Q := (lower_testing_depth_bounds t0 zeta B (overlapRadius C)
    ((listInformationRatio T M (by omega) hM)) ht0 hzeta hB hq hu hsmall).1
  have hbudget := lower_testing_depth_trajectory_budget_le T M t0 zeta B
    (overlapRadius C) (by omega) hM ht0 hzeta hB hq
  have hminimax := hdepth T M Q C hT hM hQ hC hbudget
  have hgap := lower_testing_depth_frontier_gap_ge t0 zeta B (overlapRadius C)
    ((listInformationRatio T M (by omega) hM)) ht0 hzeta hB hq hu hsmall
  calc
    _ = a / 8 * ((mixingAlpha t0 * (32 * B) ^ (-(rateExponent t0 zeta / 2))) *
        (overlapRadius C ^ (1 - rateExponent t0 zeta) *
          (listInformationRatio T M (by omega) hM) ^ (rateExponent t0 zeta / 2))) := by
      dsimp [c2]
      ring
    _ ≤ a / 8 * (overlapRadius C * mixingAlpha t0 ^ Q) :=
      mul_le_mul_of_nonneg_left hgap (div_nonneg ha.le (by norm_num))
    _ = a / 8 * overlapRadius C * mixingAlpha t0 ^ Q := by ring
    _ ≤ _ := hminimax

end CausalSmith.Stat.PomdpPolicyclassRegret

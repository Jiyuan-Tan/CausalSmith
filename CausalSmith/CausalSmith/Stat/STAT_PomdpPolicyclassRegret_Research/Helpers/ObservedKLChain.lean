module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.KLHandle
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Finite observed-word KL and its chronological chain rule

These identities implement the expectation of the log likelihood in steps
(16)--(18) of the contextual observed KL proof. Zero-mass words contribute zero.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory InformationTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators ENNReal

/-- Inclusion of finite PMF supports implies absolute continuity of their laws. For
[the contraction coefficient](hyp:α), [the policy](hyp:p), [the p0](hyp:p0), and
[the support assumption](hyp:hsupport), this establishes
[the finite probability mass function absolutely continuous result](goal). -/
-- @node: finitePMF_absolutelyContinuous
lemma finitePMF_absolutelyContinuous {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p p0 : PMF α)
    (hsupport : ∀ a, p0 a = 0 → p a = 0) : p.toMeasure ≪ p0.toMeasure := by
  intro s hs
  have hzero : Disjoint p0.support (toMeasurable p0.toMeasure s) :=
    (p0.toMeasure_apply_eq_zero_iff (measurableSet_toMeasurable _ _)).mp
      (by simpa using hs)
  -- Use the measurable envelope so this also covers nonmeasurable null sets.
  have hz : ∀ a ∈ toMeasurable p0.toMeasure s, p0 a = 0 := by
    intro a ha
    exact not_not.mp (fun h ↦ Set.disjoint_left.mp hzero
      (by simpa [PMF.mem_support_iff] using h) ha)
  have hpz : p.toMeasure (toMeasurable p0.toMeasure s) = 0 := by
    apply (p.toMeasure_apply_eq_zero_iff (measurableSet_toMeasurable _ _)).mpr
    apply Set.disjoint_left.mpr
    intro a ha has
    have hpa : p a ≠ 0 := by simpa [PMF.mem_support_iff] using ha
    exact hpa (hsupport a (hz a has))
  exact measure_mono_null (subset_toMeasurable _ _) hpz

/-- At a positive reference atom, the Radon--Nikodym derivative is its mass ratio. The singleton
integral establishes this directly from absolute continuity. For
[the contraction coefficient](hyp:α), [the policy](hyp:p), [the p0](hyp:p0),
[the ac assumption](hyp:hac), [the action](hyp:a), and [the action assumption](hyp:ha), this
establishes [the finite probability mass function to real rn deriv result](goal). -/
-- @node: finitePMF_toReal_rnDeriv
lemma finitePMF_toReal_rnDeriv {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p p0 : PMF α)
    (hac : p.toMeasure ≪ p0.toMeasure) (a : α) (ha : 0 < (p0 a).toReal) :
    (p.toMeasure.rnDeriv p0.toMeasure a).toReal =
      (p a).toReal / (p0 a).toReal := by
  have h := Measure.setIntegral_toReal_rnDeriv hac ({a} : Set α)
  rw [integral_singleton] at h
  simp only [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    smul_eq_mul] at h
  apply (eq_div_iff (ne_of_gt ha)).mpr
  simpa only [mul_comm] using h

/-- The real KL of finite probability laws is the mass-weighted log ratio. Only reference atoms
in the support of the first law need positive mass. For [the contraction coefficient](hyp:α),
[the policy](hyp:p), [the p0](hyp:p0), and [the support assumption](hyp:hsupport), this
establishes [the finite probability mass function KL div equality sum result](goal). -/
-- @node: finitePMF_klDiv_eq_sum
lemma finitePMF_klDiv_eq_sum {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p p0 : PMF α)
    (hsupport : ∀ a, p0 a = 0 → p a = 0) :
    (klDiv p.toMeasure p0.toMeasure).toReal =
      ∑ a, (p a).toReal * Real.log ((p a).toReal / (p0 a).toReal) := by
  have hac := finitePMF_absolutelyContinuous p p0 hsupport
  rw [toReal_klDiv_of_measure_eq hac (by simp), integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro a _
  simp only [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    smul_eq_mul]
  by_cases hp : p a = 0
  · simp [hp]
  · have hp0 : p0 a ≠ 0 := fun h ↦ hp (hsupport a h)
    have ha : 0 < (p0 a).toReal := ENNReal.toReal_pos hp0 (p0.apply_ne_top a)
    rw [llr, finitePMF_toReal_rnDeriv p p0 hac a ha]

/-- Finite KL is finite under support inclusion, so its real value does not conceal an infinite
divergence. For [the contraction coefficient](hyp:α), [the policy](hyp:p), [the p0](hyp:p0), and
[the support assumption](hyp:hsupport), this establishes
[the finite probability mass function KL div ne top result](goal). -/
-- @node: finitePMF_klDiv_ne_top
lemma finitePMF_klDiv_ne_top {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p p0 : PMF α)
    (hsupport : ∀ a, p0 a = 0 → p a = 0) :
    klDiv p.toMeasure p0.toMeasure ≠ ⊤ := by
  exact klDiv_ne_top (finitePMF_absolutelyContinuous p p0 hsupport) Integrable.of_finite

/-- The expectation of the observed-prefix chain is exactly the finite-word KL. Prefixes on
words of zero alternative mass need no positivity condition. For [the time horizon](hyp:T),
[the observed-state count](hyp:nX), [the reward-symbol count](hyp:nR), [the policy](hyp:p),
[the p0](hyp:p0), and [the support assumption](hyp:hsupport), this establishes
[the observed probability mass function KL div equality chain result](goal). -/
-- @node: observedPMF_klDiv_eq_chain
lemma observedPMF_klDiv_eq_chain {T nX nR : Nat}
    (p p0 : PMF (FiniteObsView T nX nR))
    (hsupport : ∀ w, p0 w = 0 → p w = 0) :
    (klDiv p.toMeasure p0.toMeasure).toReal =
      ∑ w, (p w).toReal * observedChainLogRatio p p0 w := by
  rw [finitePMF_klDiv_eq_sum p p0 hsupport]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hp : p w = 0
  · simp [hp]
  · have hp0 : p0 w ≠ 0 := fun h ↦ hp (hsupport w h)
    rw [observedChainLogRatio_eq_log_ratio p p0 w
      (ENNReal.toReal_pos hp (p.apply_ne_top w))
      (ENNReal.toReal_pos hp0 (p0.apply_ne_top w))]

/-- Chronological expansion of finite observed-word KL into expected one-step prefix log
likelihoods, as used in step (18). For [the time horizon](hyp:T),
[the observed-state count](hyp:nX), [the reward-symbol count](hyp:nR), [the policy](hyp:p),
[the p0](hyp:p0), and [the support assumption](hyp:hsupport), this establishes
[the observed probability mass function KL div equality sum steps result](goal). -/
-- @node: observedPMF_klDiv_eq_sum_steps
lemma observedPMF_klDiv_eq_sum_steps {T nX nR : Nat}
    (p p0 : PMF (FiniteObsView T nX nR))
    (hsupport : ∀ w, p0 w = 0 → p w = 0) :
    (klDiv p.toMeasure p0.toMeasure).toReal =
      ∑ t : Fin T, ∑ w, (p w).toReal *
        Real.log ((observedWordPrefixMass p (t.val + 1) w /
          observedWordPrefixMass p t.val w) /
          (observedWordPrefixMass p0 (t.val + 1) w /
            observedWordPrefixMass p0 t.val w)) := by
  rw [observedPMF_klDiv_eq_chain p p0 hsupport]
  simp only [observedChainLogRatio, Finset.mul_sum]
  exact Finset.sum_comm

/-- Reward decoding transports the finite-word chain budget to the actual observed trajectory.
Finiteness is proved before taking real values. For [the time horizon](hyp:T),
[the observed-state count](hyp:nX), [the hidden-state count](hyp:nH),
[the reward-symbol count](hyp:nR), [the event family](hyp:F), [the g](hyp:G),
[the rew assumption](hyp:hrew), and [the support assumption](hyp:hsupport), this establishes
[the finite reward model observed KL div bound chain result](goal). -/
-- @node: finiteRewardModel_observed_klDiv_le_chain
lemma finiteRewardModel_observed_klDiv_le_chain {T nX nH nR : Nat}
    (F G : FiniteRewardModel T nX nH nR) (hrew : F.rew = G.rew)
    (hsupport : ∀ w, G.obsPMF w = 0 → F.obsPMF w = 0) :
    (klDiv (obsLaw (embed F)) (obsLaw (embed G))).toReal ≤
      ∑ t : Fin T, ∑ w, (F.obsPMF w).toReal *
        Real.log ((observedWordPrefixMass F.obsPMF (t.val + 1) w /
          observedWordPrefixMass F.obsPMF t.val w) /
          (observedWordPrefixMass G.obsPMF (t.val + 1) w /
            observedWordPrefixMass G.obsPMF t.val w)) := by
  have hfinite := finitePMF_klDiv_ne_top F.obsPMF G.obsPMF hsupport
  have hdecode := embed_klDiv_le (F := F) (G := G) hrew
  calc
    _ ≤ (klDiv F.obsPMF.toMeasure G.obsPMF.toMeasure).toReal :=
      ENNReal.toReal_mono hfinite hdecode
    _ = _ := observedPMF_klDiv_eq_sum_steps F.obsPMF G.obsPMF hsupport

/-- Specialization to the sparse common-kernel experiment and its fair reference law. Both
environments use the same reward-symbol decoding. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the dim assumption](hyp:hDim), [the candidate-policy count assumption](hyp:hM),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code),
[the code assumption](hyp:hCode), [the codeword index](hyp:v), and
[the support assumption](hyp:hsupport), this establishes
[the sparse observed KL div bound chain result](goal). -/
-- @node: sparse_observed_klDiv_le_chain
lemma sparse_observed_klDiv_le_chain (T M d Q : Nat) (hd : 0 < d)
    (hDim : d = codeDimension M) (hM : 2 ≤ M)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool)
    (hCode : CodeSeparated code) (v : Fin M)
    (hsupport : ∀ w,
      sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code ⟨0, by omega⟩ true w = 0 →
      sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code v false w = 0) :
    (klDiv
      (obsLaw (sparsePackingExperiment T M d Q hd hDim hM
        t0 zeta C code hCode v).Mx.toRawB)
      (sparseReferenceLaw T M d Q hd (by omega) t0 zeta C code)).toReal ≤
      ∑ t : Fin T, ∑ w : FiniteObsView T (d * hdepth Q) 2,
        (sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code v false w).toReal *
          Real.log ((observedWordPrefixMass
            (sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code v false) (t.val + 1) w /
            observedWordPrefixMass
              (sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code v false) t.val w) /
            (observedWordPrefixMass
              (sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code ⟨0, by omega⟩ true) (t.val + 1) w /
              observedWordPrefixMass
                (sparseObservedPMF (T := T) (Q := Q) hd t0 zeta C code ⟨0, by omega⟩ true) t.val w)) := by
  dsimp only [sparsePackingExperiment, ListPomdpExperiment.toRawB, sparseReferenceLaw, obsLaw,
    sparseObservedPMF]
  exact finiteRewardModel_observed_klDiv_le_chain
      (sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false)
      (sparseFinite (T := T) (Q := Q) hd t0 zeta C code ⟨0, by omega⟩ true)
      rfl hsupport

end CausalSmith.Stat.PomdpPolicyclassRegret

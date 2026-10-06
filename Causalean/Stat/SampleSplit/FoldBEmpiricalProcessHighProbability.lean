/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Limit.ProbabilityTransfer
public import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess

/-! # High-Probability Good-Set Bounds for Centered Fold Sums

This file supplies one-shot and K-fold centered empirical-process bounds when
the random score is square-integrable on an event whose probability tends to
one, together with almost-sure corollaries. The proofs replace the score by a
measurable finite-L² modification off the good event before applying the
pointwise theorem.
-/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
         {X : Type*} [MeasurableSpace X] {P : Measure X}

private lemma measurable_eLpNorm_of_uncurry
    [SFinite P]
    {g : Ω → X → ℝ} {p : ℝ≥0∞} (hp_zero : p ≠ 0) (hp_top : p ≠ ⊤)
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun ω => eLpNorm (g ω) p P) := by
  have h_int : Measurable (fun ω => ∫⁻ x, ‖g ω x‖ₑ ^ p.toReal ∂P) :=
    Measurable.lintegral_prod_right' ((hg.enorm).pow_const p.toReal)
  simpa [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp_top] using
    (h_int.pow_const (1 / p.toReal))

private lemma measurable_eLpNorm_of_uncurry_of_factor
    {mΩ : MeasurableSpace Ω} [SFinite P]
    {g : Ω → X → ℝ} {p : ℝ≥0∞} (hp_zero : p ≠ 0) (hp_top : p ≠ ⊤)
    (hg : @Measurable (Ω × X) ℝ
      (@Prod.instMeasurableSpace Ω X mΩ inferInstance) inferInstance
      (Function.uncurry g)) :
    Measurable[mΩ] (fun ω => eLpNorm (g ω) p P) := by
  have h_int : Measurable[mΩ]
      (fun ω => ∫⁻ x, ‖g ω x‖ₑ ^ p.toReal ∂P) :=
    Measurable.lintegral_prod_right' ((hg.enorm).pow_const p.toReal)
  simpa [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp_top] using
    (h_int.pow_const (1 / p.toReal))

private theorem exists_finiteLp_modification
    [SFinite P] (m_train : ℕ → MeasurableSpace Ω)
    (f : ℕ → Ω → X → ℝ)
    (hf_meas : ∀ n, Measurable (Function.uncurry (f n)))
    (hf_uncurry_train : ∀ n,
      Measurable[(m_train n).prod (inferInstance : MeasurableSpace X)]
        (Function.uncurry (f n))) :
    ∃ ftil : ℕ → Ω → X → ℝ,
      (∀ n, Measurable (Function.uncurry (ftil n))) ∧
      (∀ n, Measurable[(m_train n).prod (inferInstance : MeasurableSpace X)]
        (Function.uncurry (ftil n))) ∧
      (∀ n ω, MemLp (ftil n ω) 2 P) ∧
      (∀ n ω, (eLpNorm (ftil n ω) 2 P).toReal =
        (eLpNorm (f n ω) 2 P).toReal) ∧
      (∀ n ω, MemLp (f n ω) 2 P → ftil n ω = f n ω) := by
  let ftil : ℕ → Ω → X → ℝ := fun n ω x =>
    if eLpNorm (f n ω) 2 P < ⊤ then f n ω x else 0
  have hftil_meas : ∀ n, Measurable (Function.uncurry (ftil n)) := by
    intro n
    have hnorm : Measurable (fun p : Ω × X => eLpNorm (f n p.1) 2 P) :=
      (measurable_eLpNorm_of_uncurry (by norm_num) (by norm_num) (hf_meas n)).comp
        measurable_fst
    exact Measurable.ite (measurableSet_lt hnorm measurable_const)
      (hf_meas n) measurable_const
  have hftil_uncurry_train : ∀ n,
      Measurable[(m_train n).prod (inferInstance : MeasurableSpace X)]
        (Function.uncurry (ftil n)) := by
    intro n
    have hnorm :
        Measurable[(m_train n).prod (inferInstance : MeasurableSpace X)]
          (fun p : Ω × X => eLpNorm (f n p.1) 2 P) :=
      (measurable_eLpNorm_of_uncurry_of_factor
        (by norm_num) (by norm_num) (hf_uncurry_train n)).comp measurable_fst
    exact Measurable.ite (measurableSet_lt hnorm measurable_const)
      (hf_uncurry_train n) measurable_const
  have hftil_memLp : ∀ n ω, MemLp (ftil n ω) 2 P := by
    intro n ω
    by_cases hfinite : eLpNorm (f n ω) 2 P < ⊤
    · refine ⟨?_, ?_⟩
      · rw [show ftil n ω = f n ω by funext x; simp [ftil, hfinite]]
        exact ((hf_meas n).comp
          (Measurable.prodMk measurable_const measurable_id)).aestronglyMeasurable
      · simpa [ftil, hfinite] using hfinite
    · simp [ftil, hfinite]
  have hftil_norm : ∀ n ω,
      (eLpNorm (ftil n ω) 2 P).toReal =
        (eLpNorm (f n ω) 2 P).toReal := by
    intro n ω
    by_cases hfinite : eLpNorm (f n ω) 2 P < ⊤
    · simp [ftil, hfinite]
    · have htop : eLpNorm (f n ω) 2 P = ⊤ := top_unique (le_of_not_gt hfinite)
      simp [ftil, htop]
  have hftil_eq : ∀ n ω, MemLp (f n ω) 2 P → ftil n ω = f n ω := by
    intro n ω hω
    funext x
    simp [ftil, hω.eLpNorm_lt_top]
  exact ⟨ftil, hftil_meas, hftil_uncurry_train, hftil_memLp,
    hftil_norm, hftil_eq⟩

private lemma centeredSum_difference_tendsto_zero
    (S : IIDSample Ω X μ P) (eval : ℕ → Finset ℕ)
    (f g : ℕ → Ω → X → ℝ) (hgf : ∀ n, ∀ᵐ ω ∂μ, g n ω = f n ω) :
    Tendsto (fun n =>
      μ {ω | (Real.sqrt ((eval n).card : ℝ))⁻¹ *
              ∑ i ∈ eval n, (f n ω (S.Z i ω) - ∫ x, f n ω x ∂P) ≠
            (Real.sqrt ((eval n).card : ℝ))⁻¹ *
              ∑ i ∈ eval n, (g n ω (S.Z i ω) - ∫ x, g n ω x ∂P)})
      atTop (𝓝 0) := by
  have hzero : (fun n =>
      μ {ω | (Real.sqrt ((eval n).card : ℝ))⁻¹ *
              ∑ i ∈ eval n, (f n ω (S.Z i ω) - ∫ x, f n ω x ∂P) ≠
            (Real.sqrt ((eval n).card : ℝ))⁻¹ *
              ∑ i ∈ eval n, (g n ω (S.Z i ω) - ∫ x, g n ω x ∂P)}) =
      fun _ => 0 := by
    funext n
    apply ae_iff.mp
    filter_upwards [hgf n] with ω hω
    simp [hω]
  rw [hzero]
  exact tendsto_const_nhds

/-- For [an i.i.d. sample](hyp:S), [a one-shot split](hyp:split), and [random
scores](hyp:f) that are [jointly measurable](hyp:hf_meas), [training-fold
measurable](hyp:hf_uncurry_foldA), [square-integrable for almost every training
sample realization](hyp:hf_memLp), and [vanishing in L² in probability](hyp:hf_rate),
[the centered evaluation-fold empirical sum is negligible in probability](goal). -/
theorem foldB_centered_sum_isLittleOp_one_of_ae_memLp
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) (split : OneShotSplit S)
    (f : ℕ → Ω → X → ℝ)
    (hf_meas : ∀ n, Measurable (Function.uncurry (f n)))
    (hf_uncurry_foldA : ∀ n,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.foldA n) => S.Z i ω) inferInstance).prod
        (inferInstance : MeasurableSpace X)]
        (Function.uncurry (f n)))
    (hf_memLp : ∀ n, ∀ᵐ ω ∂μ, MemLp (f n ω) 2 P)
    (hf_rate : IsLittleOp
      (fun n ω => (eLpNorm (f n ω) 2 P).toReal) (fun _ => (1 : ℝ)) μ) :
    IsLittleOp
      (fun n ω =>
        (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
          ∑ i ∈ split.foldB n,
            (f n ω (S.Z i ω) - ∫ x, f n ω x ∂P))
      (fun _ => (1 : ℝ)) μ := by
  rcases exists_finiteLp_modification (P := P)
      (fun n => MeasurableSpace.comap
        (fun ω (i : split.foldA n) => S.Z i ω) inferInstance)
      f hf_meas hf_uncurry_foldA with
    ⟨ftil, hftil_meas, hftil_foldA, hftil_memLp, hftil_norm, hftil_eq⟩
  apply IsLittleOp.of_eq_on_asymptotic
    (centeredSum_difference_tendsto_zero S (fun n => split.foldB n)
      f ftil (fun n => (hf_memLp n).mono (hftil_eq n)))
  apply foldB_centered_sum_isLittleOp_one S split ftil hftil_meas hftil_foldA
    hftil_memLp
  simpa only [hftil_norm] using hf_rate

/-- For [an i.i.d. sample](hyp:S), [a one-shot split](hyp:split), [random
scores](hyp:f), [high-probability events](hyp:G), and [failure bounds](hyp:Δ)
that [vanish](hyp:hΔ) and [control their complements](hyp:hfail), assume the scores
are [jointly and training-fold measurable](hyp:hf_meas,hf_uncurry_foldA),
[square-integrable on each good event](hyp:hf_memLp), and [vanish in L² in
probability](hyp:hf_rate). Then [the centered evaluation-fold empirical sum
is negligible in probability](goal). -/
theorem foldB_centered_sum_isLittleOp_one_of_memLp_on_highProbEvent
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) (split : OneShotSplit S)
    (f : ℕ → Ω → X → ℝ) (G : ℕ → Set Ω) (Δ : ℕ → ℝ≥0∞)
    (hΔ : Tendsto Δ atTop (𝓝 0))
    (hfail : ∀ n, μ (G n)ᶜ ≤ Δ n)
    (hf_meas : ∀ n, Measurable (Function.uncurry (f n)))
    (hf_uncurry_foldA : ∀ n,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.foldA n) => S.Z i ω) inferInstance).prod
        (inferInstance : MeasurableSpace X)]
        (Function.uncurry (f n)))
    (hf_memLp : ∀ n ω, ω ∈ G n → MemLp (f n ω) 2 P)
    (hf_rate : IsLittleOp
      (fun n ω => (eLpNorm (f n ω) 2 P).toReal) (fun _ => (1 : ℝ)) μ) :
    IsLittleOp
      (fun n ω =>
        (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
          ∑ i ∈ split.foldB n,
            (f n ω (S.Z i ω) - ∫ x, f n ω x ∂P))
      (fun _ => (1 : ℝ)) μ := by
  rcases exists_finiteLp_modification (P := P)
      (fun n => MeasurableSpace.comap
        (fun ω (i : split.foldA n) => S.Z i ω) inferInstance)
      f hf_meas hf_uncurry_foldA with
    ⟨ftil, hftil_meas, hftil_foldA, hftil_memLp, hftil_norm, hftil_eq⟩
  apply isLittleOp_of_isLittleOp_on_highProbEvent
    (Xn := fun n ω =>
      (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
        ∑ i ∈ split.foldB n,
          (f n ω (S.Z i ω) - ∫ x, f n ω x ∂P))
    (Yn := fun n ω =>
      (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
        ∑ i ∈ split.foldB n,
          (ftil n ω (S.Z i ω) - ∫ x, ftil n ω x ∂P))
    G Δ hΔ hfail
  · intro n ω hω
    rw [hftil_eq n ω (hf_memLp n ω hω)]
  · apply foldB_centered_sum_isLittleOp_one S split ftil hftil_meas
      hftil_foldA hftil_memLp
    simpa only [hftil_norm] using hf_rate

/-- For [an i.i.d. sample](hyp:S), [a K-fold split and fixed fold](hyp:split,k),
and [random scores](hyp:f) that are [jointly measurable](hyp:hf_meas),
[training-complement measurable](hyp:hf_uncurry_train), [square-integrable for
almost every training sample realization](hyp:hf_memLp), and [vanishing in L² in
probability](hyp:hf_rate), [the centered fixed-fold empirical sum is negligible in
probability](goal). -/
theorem KFoldSplit.fold_centered_sum_isLittleOp_one_of_ae_memLp
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) {K : ℕ} (split : KFoldSplit S K) (k : Fin K)
    (f : ℕ → Ω → X → ℝ)
    (hf_meas : ∀ n, Measurable (Function.uncurry (f n)))
    (hf_uncurry_train : ∀ n,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => S.Z i ω) inferInstance).prod
        (inferInstance : MeasurableSpace X)]
        (Function.uncurry (f n)))
    (hf_memLp : ∀ n, ∀ᵐ ω ∂μ, MemLp (f n ω) 2 P)
    (hf_rate : IsLittleOp
      (fun n ω => (eLpNorm (f n ω) 2 P).toReal) (fun _ => (1 : ℝ)) μ) :
    IsLittleOp
      (fun n ω =>
        (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
          ∑ i ∈ split.fold n k,
            (f n ω (S.Z i ω) - ∫ x, f n ω x ∂P))
      (fun _ => (1 : ℝ)) μ := by
  rcases exists_finiteLp_modification (P := P)
      (fun n => MeasurableSpace.comap
        (fun ω (i : split.trainComplement n k) => S.Z i ω) inferInstance)
      f hf_meas hf_uncurry_train with
    ⟨ftil, hftil_meas, hftil_train, hftil_memLp, hftil_norm, hftil_eq⟩
  apply IsLittleOp.of_eq_on_asymptotic
    (centeredSum_difference_tendsto_zero S (fun n => split.fold n k)
      f ftil (fun n => (hf_memLp n).mono (hftil_eq n)))
  apply KFoldSplit.fold_centered_sum_isLittleOp_one S split k ftil
    hftil_meas hftil_train hftil_memLp
  simpa only [hftil_norm] using hf_rate

/-- For [an i.i.d. sample](hyp:S), [a K-fold split and fixed fold](hyp:split,k),
[random scores](hyp:f), [high-probability events](hyp:G), and [failure
bounds](hyp:Δ) that [vanish](hyp:hΔ) and [control their complements](hyp:hfail), assume the
scores are [jointly and training-complement
measurable](hyp:hf_meas,hf_uncurry_train), [square-integrable on each good
event](hyp:hf_memLp), and [vanish in L² in probability](hyp:hf_rate). Then [the
centered fixed-fold empirical sum is negligible in probability](goal). -/
theorem KFoldSplit.fold_centered_sum_isLittleOp_one_of_memLp_on_highProbEvent
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) {K : ℕ} (split : KFoldSplit S K) (k : Fin K)
    (f : ℕ → Ω → X → ℝ) (G : ℕ → Set Ω) (Δ : ℕ → ℝ≥0∞)
    (hΔ : Tendsto Δ atTop (𝓝 0))
    (hfail : ∀ n, μ (G n)ᶜ ≤ Δ n)
    (hf_meas : ∀ n, Measurable (Function.uncurry (f n)))
    (hf_uncurry_train : ∀ n,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => S.Z i ω) inferInstance).prod
        (inferInstance : MeasurableSpace X)]
        (Function.uncurry (f n)))
    (hf_memLp : ∀ n ω, ω ∈ G n → MemLp (f n ω) 2 P)
    (hf_rate : IsLittleOp
      (fun n ω => (eLpNorm (f n ω) 2 P).toReal) (fun _ => (1 : ℝ)) μ) :
    IsLittleOp
      (fun n ω =>
        (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
          ∑ i ∈ split.fold n k,
            (f n ω (S.Z i ω) - ∫ x, f n ω x ∂P))
      (fun _ => (1 : ℝ)) μ := by
  rcases exists_finiteLp_modification (P := P)
      (fun n => MeasurableSpace.comap
        (fun ω (i : split.trainComplement n k) => S.Z i ω) inferInstance)
      f hf_meas hf_uncurry_train with
    ⟨ftil, hftil_meas, hftil_train, hftil_memLp, hftil_norm, hftil_eq⟩
  apply isLittleOp_of_isLittleOp_on_highProbEvent
    (Xn := fun n ω =>
      (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
        ∑ i ∈ split.fold n k,
          (f n ω (S.Z i ω) - ∫ x, f n ω x ∂P))
    (Yn := fun n ω =>
      (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
        ∑ i ∈ split.fold n k,
          (ftil n ω (S.Z i ω) - ∫ x, ftil n ω x ∂P))
    G Δ hΔ hfail
  · intro n ω hω
    rw [hftil_eq n ω (hf_memLp n ω hω)]
  · apply KFoldSplit.fold_centered_sum_isLittleOp_one S split k ftil
      hftil_meas hftil_train hftil_memLp
    simpa only [hftil_norm] using hf_rate

end Causalean.Stat

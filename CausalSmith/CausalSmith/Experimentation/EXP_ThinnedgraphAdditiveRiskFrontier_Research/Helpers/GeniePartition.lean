module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BaselineTranslationAffinity
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.PartitionTranslationBound

/-!
# Genie-partition translation bound
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Mixing probability laws over a common finite marginal preserves a uniform TV bound.  [For the stated data and conditions](hyp:α,β,μ,P,Q,hP,hQ,hPm,hQm,c,hc), [the stated conclusion holds](goal). -/
-- @node: block_tvDist_bind_uniform_le
lemma block_tvDist_bind_uniform_le {α β : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    [MeasurableSpace β] (μ : Measure α) [IsProbabilityMeasure μ]
    (P Q : α → Measure β) (hP : ∀ a, IsProbabilityMeasure (P a))
    (hQ : ∀ a, IsProbabilityMeasure (Q a)) (hPm : Measurable P) (hQm : Measurable Q)
    (c : ℝ) (hc : ∀ a, Causalean.Stat.tvDist (P a) (Q a) ≤ c) :
    Causalean.Stat.tvDist (μ.bind P) (μ.bind Q) ≤ c := by
  let _ := hP
  let _ := hQ
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨E, hE⟩
  have hreal (K : α → Measure β) (hK : ∀ a, IsProbabilityMeasure (K a))
      (hKm : Measurable K) : (μ.bind K).real E = ∫ a, (K a).real E ∂μ := by
    let _ := hK
    rw [measureReal_def, Measure.bind_apply hE hKm.aemeasurable]
    exact (integral_toReal ((Measure.measurable_coe hE).comp hKm).aemeasurable
      (Filter.Eventually.of_forall (fun a => measure_lt_top (K a) E))).symm
  rw [hreal P hP hPm, hreal Q hQ hQm,
    ← integral_sub Integrable.of_finite Integrable.of_finite]
  calc
    _ ≤ ∫ a, |(P a).real E - (Q a).real E| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _ : α, c ∂μ := integral_mono Integrable.of_finite (integrable_const c)
      (fun a => (Causalean.Stat.abs_measureReal_sub_le_tvDist hE).trans (hc a))
    _ = c := by simp

/-- Giving the partition to the observer yields the product-translation upper bound on the
original-record distance.  [For the stated data and conditions](hyp:n,B,d,h,q,D,hB,hd,hfit,hh,hq,ha,hw,hi), [the stated conclusion holds](goal). -/
-- @node: genie_partition_tv_bound
lemma genie_partition_tv_bound (n B d : ℕ) (h q : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) (hB : 1 ≤ B) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1)
    (ha : AssignmentLaw D) (hw : AuditLaw D q) (hi : DesignIndependent D) :
    Causalean.Stat.tvDist (blockMixtureLawOf n B d D true h)
      (blockMixtureLawOf n B d D false h) ≤ 2 * Real.pi * h * Real.sqrt ((B : ℝ) / d) := by
  let := design_isProbabilityMeasure D q ha hw hi
  let := partitionLaw_probability B d
  let := blockBaselineLaw_probability B
  have hp (σ : Bool) (s : SourcePartition B d) : IsProbabilityMeasure
      (mixtureLaw D (blockBaselineLaw B) (fun U => blockSchedule n B d σ h (s, U))) :=
    mixtureLaw_probability D _ _ ((block_record_measurable n B d σ h).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
  rw [blockMixtureLawOf_bind_partition, blockMixtureLawOf_bind_partition]
  exact block_tvDist_bind_uniform_le _ _ _ (hp true) (hp false)
    (measurable_of_finite _) (measurable_of_finite _) _
    (fun s => partition_mixture_tv_le n B d hd hfit h hh.1 s D ha)

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

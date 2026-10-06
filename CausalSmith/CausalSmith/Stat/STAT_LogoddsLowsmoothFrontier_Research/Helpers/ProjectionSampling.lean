module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.ProjectionResidual
public import Causalean.Stat.Sample.PiTransport
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Finite sampling transport for projection variance

The finite product experiment is the pushforward of a canonical infinite IID
sample. Reindexing ordered pairs transports the exact residual second moment.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Ordered distinct finite indices and natural indices below n have identical sums.](goal) Under [the stated assumptions](hyp:F). -/
-- @node: projection_offDiag_sum_reindex
lemma projection_offDiag_sum_reindex (n : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag, F ij.1.val ij.2.val) =
      ∑ ij ∈ (Finset.range n).offDiag, F ij.1 ij.2 := by
  classical
  apply Finset.sum_bij (fun ij _ => (ij.1.val, ij.2.val))
  · intro ij hij
    simp only [Finset.mem_offDiag, Finset.mem_range]
    refine ⟨ij.1.isLt, ij.2.isLt, ?_⟩
    exact fun h => (Finset.mem_offDiag.mp hij).2.2 (Fin.ext h)
  · intro ij hij pq hpq heq
    exact Prod.ext (Fin.ext (congrArg Prod.fst heq)) (Fin.ext (congrArg Prod.snd heq))
  · intro ij hij
    obtain ⟨hi, hj, hne⟩ := Finset.mem_offDiag.mp hij
    refine ⟨(⟨ij.1, Finset.mem_range.mp hi⟩, ⟨ij.2, Finset.mem_range.mp hj⟩), ?_, rfl⟩
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
    exact fun h => hne (congrArg (fun z : Fin n => z.val) h)
  · intro ij hij
    rfl

/-- [The residual ordered average is the library U-statistic along the finite IID observable.](goal) Under [the stated assumptions](hyp:μ). -/
-- @node: projectionResidual_average_eq_uStatistic
lemma projectionResidual_average_eq_uStatistic (P : ObservedLaw) (W V : BoundedMark)
    (k n : ℕ) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : Causalean.Stat.IIDSample Ω Record μ P.measure) (ω : Ω) :
    ((n : ℝ) * ((n : ℝ) - 1))⁻¹ *
      ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
        projectionResidual P W V k (S.Z ij.1 ω) (S.Z ij.2 ω) =
      Causalean.Stat.uStatistic S (projectionResidual P W V k) n ω := by
  unfold Causalean.Stat.uStatistic
  rw [projection_offDiag_sum_reindex n
    (fun i j => projectionResidual P W V k (S.Z i ω) (S.Z j ω))]

/-- [Finite product expectations equal expectations along the finite observable of an IID sample.](goal) Under [the stated assumptions](hyp:μ,hF). Under [the stated assumptions](hyp:F). -/
-- @node: projection_integral_iid_transport
lemma projection_integral_iid_transport (P : ObservedLaw) (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : Causalean.Stat.IIDSample Ω Record μ P.measure)
    (F : (Fin n → Record) → ℝ) (hF : Measurable F) :
    (∫ o, F o ∂Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) =
      ∫ ω, F (fun i : Fin n => S.Z i ω) ∂μ := by
  unfold Causalean.Stat.UStatistic.LocalizedVariance.iidLaw
  rw [← Causalean.Stat.iidSample_finN_pushforward S n]
  exact integral_map (Causalean.Stat.iidSample_finN_measurable S n).aemeasurable
    hF.aestronglyMeasurable

/-- [The sharp residual second moment holds under the original finite product law.](goal) Under [the stated assumptions](hyp:hDesign,hn). -/
-- @node: projectionResidual_finite_secondMoment
lemma projectionResidual_finite_secondMoment (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k n : ℕ) (hn : 2 ≤ n) :
    (∫ o : Fin n → Record, (((n : ℝ) * ((n : ℝ) - 1))⁻¹ *
      ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
        projectionResidual P W V k (o ij.1) (o ij.2))^2
      ∂Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) =
      2 * (∫ z : Record × Record, (projectionResidual P W V k z.1 z.2)^2
        ∂(P.measure.prod P.measure)) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  let S := Causalean.Stat.iidSample_infinitePi P.measure
  have hm := projectionResidual_measurable P hDesign W V k
  rw [projection_integral_iid_transport P n S _ (by fun_prop)]
  simp_rw [projectionResidual_average_eq_uStatistic]
  exact projectionResidual_secondMoment P hDesign W V k S n hn

/-- [The finite experiment's residual contributes at most the sharp rank term.](goal) Under [the stated assumptions](hyp:hDesign,hn). -/
-- @node: projectionResidual_finite_secondMoment_le
lemma projectionResidual_finite_secondMoment_le (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k n : ℕ) (hn : 2 ≤ n) :
    (∫ o : Fin n → Record, (((n : ℝ) * ((n : ℝ) - 1))⁻¹ *
      ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
        projectionResidual P W V k (o ij.1) (o ij.2))^2
      ∂Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) ≤
      2 * k / ((n : ℝ) * ((n : ℝ) - 1)) := by
  rw [projectionResidual_finite_secondMoment P hDesign W V k n hn]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (projectionResidual_energy_le_rank P hDesign W V k)
      (by norm_num)) (mul_nonneg (by positivity) (by linarith))

/-- [The centered first projection is square integrable.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: projectionFirst_centered_memLp
lemma projectionFirst_centered_memLp (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) :
    MemLp (fun o => projectionFirst P W V k o - projectionMean P W V k) 2 P.measure := by
  have hf : MemLp (projectionFirst P W V k) 2 P.measure :=
    (memLp_two_iff_integrable_sq
      (projectionFirst_measurable P hDesign W V k).aestronglyMeasurable).mpr
      (symmetricProjectionKernel_first_sq_integrable P hDesign W V k)
  exact hf.sub (memLp_const _)

/-- [Independence gives the exact first-order contribution in the finite experiment.](goal) Under [the stated assumptions](hyp:hDesign,hn). -/
-- @node: projectionFirst_finite_secondMoment
lemma projectionFirst_finite_secondMoment (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k n : ℕ) (hn : 2 ≤ n) :
    (∫ o : Fin n → Record, (2 / (n : ℝ) *
      ∑ i, (projectionFirst P W V k (o i) - projectionMean P W V k))^2
      ∂Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) =
      4 / (n : ℝ) * (∫ x, (projectionFirst P W V k x - projectionMean P W V k)^2
        ∂P.measure) := by
  let f := fun x => projectionFirst P W V k x - projectionMean P W V k
  let μ := Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n
  let : IsProbabilityMeasure μ := by
    dsimp [μ, Causalean.Stat.UStatistic.LocalizedVariance.iidLaw]
    infer_instance
  have hm : Measurable f := (projectionFirst_measurable P hDesign W V k).sub_const _
  have hf : MemLp f 2 P.measure := projectionFirst_centered_memLp P hDesign W V k
  have hz : (∫ x, f x ∂P.measure) = 0 := projectionFirst_centered_integral P hDesign W V k
  have hi (i : Fin n) : Integrable (fun o : Fin n → Record => f (o i)) μ :=
    integrable_comp_eval (μ := fun _ : Fin n => P.measure) (hf.integrable (by norm_num))
  have hmean : (∫ o : Fin n → Record, ∑ i, f (o i) ∂μ) = 0 := by
    rw [integral_finsetSum _ (fun i _ => hi i)]
    have he (i : Fin n) : (∫ o : Fin n → Record, f (o i) ∂μ) = 0 := by
      rw [show μ = Measure.pi (fun _ : Fin n => P.measure) from rfl,
        integral_comp_eval hm.aestronglyMeasurable, hz]
    simp_rw [he]
    simp
  have hsm : Measurable (fun o : Fin n → Record => ∑ i, f (o i)) := by fun_prop
  have hv : Var[fun o : Fin n → Record => ∑ i, f (o i); μ] =
      (n : ℝ) * (∫ x, (f x)^2 ∂P.measure) := by
    have h := variance_sum_pi (ι := Fin n) (X := fun _ => f) (fun _ => hf)
    have he : (∑ i : Fin n, fun o : Fin n → Record => f (o i)) =
        (fun o => ∑ i, f (o i)) := by
      funext o
      simp
    rw [he] at h
    dsimp only [μ, Causalean.Stat.UStatistic.LocalizedVariance.iidLaw]
    rw [h]
    simp_rw [variance_eq_integral hm.aemeasurable, hz, sub_zero]
    simp
  rw [variance_eq_integral hsm.aemeasurable, hmean] at hv
  simp only [sub_zero] at hv
  change (∫ o : Fin n → Record, (2 / (n : ℝ) * ∑ i, f (o i))^2 ∂μ) = _
  simp_rw [mul_pow]
  rw [integral_const_mul, hv]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  dsimp only [f]
  field_simp
  ring

/-- [The first-order term contributes at most 4/n under the finite product law.](goal) Under [the stated assumptions](hyp:hDesign,hn). -/
-- @node: projectionFirst_finite_secondMoment_le
lemma projectionFirst_finite_secondMoment_le (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k n : ℕ) (hn : 2 ≤ n) :
    (∫ o : Fin n → Record, (2 / (n : ℝ) *
      ∑ i, (projectionFirst P W V k (o i) - projectionMean P W V k))^2
      ∂Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) ≤ 4 / (n : ℝ) := by
  rw [projectionFirst_finite_secondMoment P hDesign W V k n hn]
  have he := symmetricProjectionKernel_first_centered_energy_le_one P hDesign W V k
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _)

end CausalSmith.Stat.LogoddsLowsmoothFrontier

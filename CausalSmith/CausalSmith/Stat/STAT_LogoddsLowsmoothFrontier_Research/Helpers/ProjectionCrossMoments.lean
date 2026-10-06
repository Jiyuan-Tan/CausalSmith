module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.ProjectionSampling

/-! # Cross moments of the projection residual

Integrating out a residual coordinate makes its product with any square-integrable
one-record function vanish. These identities cover either shared record, and an
independent third record, in the first-order/residual covariance expansion.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Square integrability of the degenerate residual as a function of two records.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: projectionResidual_memLp
lemma projectionResidual_memLp (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) :
    MemLp (fun z : Record × Record => projectionResidual P W V k z.1 z.2)
      2 (P.measure.prod P.measure) := by
  exact (memLp_two_iff_integrable_sq
    (projectionResidual_measurable P hDesign W V k).aestronglyMeasurable).mpr
    (projectionResidual_sq_integrable P hDesign W V k)

/-- [A square-integrable function of the first record is orthogonal to the residual.](goal) Under [the stated assumptions](hyp:hDesign,f,hfm,hf). -/
-- @node: projectionResidual_cross_fst
lemma projectionResidual_cross_fst (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) (f : Record → ℝ)
    (hfm : Measurable f) (hf : MemLp f 2 P.measure) :
    (∫ z : Record × Record, f z.1 * projectionResidual P W V k z.1 z.2
      ∂(P.measure.prod P.measure)) = 0 := by
  have hfst : MemLp (fun z : Record × Record => f z.1) 2
      (P.measure.prod P.measure) :=
    (memLp_two_iff_integrable_sq (hfm.comp measurable_fst).aestronglyMeasurable).mpr
      (((memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mp hf).comp_fst P.measure)
  have hi : Integrable (fun z : Record × Record =>
      f z.1 * projectionResidual P W V k z.1 z.2) (P.measure.prod P.measure) :=
    hfst.integrable_mul (projectionResidual_memLp P hDesign W V k)
  rw [integral_prod _ hi]
  simp_rw [integral_const_mul, projectionResidual_integral_right P hDesign W V k,
    mul_zero]
  simp

/-- [A square-integrable function of the second record is orthogonal to the residual.](goal) Under [the stated assumptions](hyp:hDesign,f,hfm,hf). -/
-- @node: projectionResidual_cross_snd
lemma projectionResidual_cross_snd (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) (f : Record → ℝ)
    (hfm : Measurable f) (hf : MemLp f 2 P.measure) :
    (∫ z : Record × Record, f z.2 * projectionResidual P W V k z.1 z.2
      ∂(P.measure.prod P.measure)) = 0 := by
  have hsnd : MemLp (fun z : Record × Record => f z.2) 2
      (P.measure.prod P.measure) :=
    (memLp_two_iff_integrable_sq (hfm.comp measurable_snd).aestronglyMeasurable).mpr
      (((memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mp hf).comp_snd P.measure)
  have hi : Integrable (fun z : Record × Record =>
      f z.2 * projectionResidual P W V k z.1 z.2) (P.measure.prod P.measure) :=
    hsnd.integrable_mul (projectionResidual_memLp P hDesign W V k)
  rw [integral_prod_symm _ hi]
  simp_rw [integral_const_mul, projectionResidual_integral_left P hDesign W V k,
    mul_zero]
  simp

/-- [The residual has zero population mean.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: projectionResidual_integral
lemma projectionResidual_integral (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) :
    (∫ z : Record × Record, projectionResidual P W V k z.1 z.2
      ∂(P.measure.prod P.measure)) = 0 := by
  rw [integral_prod _ ((projectionResidual_memLp P hDesign W V k).integrable
    (by norm_num))]
  simp_rw [projectionResidual_integral_right P hDesign W V k]
  simp

/-- [A third independent record also gives zero cross moment with the residual.](goal) Under [the stated assumptions](hyp:hDesign,f). -/
-- @node: projectionResidual_cross_independent
lemma projectionResidual_cross_independent (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k : ℕ) (f : Record → ℝ) :
    (∫ z : Record × (Record × Record), f z.1 *
      projectionResidual P W V k z.2.1 z.2.2
      ∂(P.measure.prod (P.measure.prod P.measure))) = 0 := by
  rw [integral_prod_mul f (fun z : Record × Record => projectionResidual P W V k z.1 z.2),
    projectionResidual_integral P hDesign W V k, mul_zero]

/-- [Distinct sample coordinates have the product record law.](goal) Under [the stated assumptions](hyp:hij). -/
-- @node: projection_pair_map
lemma projection_pair_map (P : ObservedLaw) {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n).map
      (fun o => (o i, o j)) = P.measure.prod P.measure := by
  let μ := Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, Causalean.Stat.UStatistic.LocalizedVariance.iidLaw]
    infer_instance
  have hcoord : iIndepFun (fun a : Fin n => fun o : Fin n → Record => o a) μ := by
    dsimp [μ, Causalean.Stat.UStatistic.LocalizedVariance.iidLaw]
    simpa using (iIndepFun_pi (μ := fun _ : Fin n => P.measure)
      (X := fun _ : Fin n => id) (fun _ => aemeasurable_id))
  have h := (hcoord.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  simpa only [μ, Causalean.Stat.UStatistic.LocalizedVariance.iidLaw,
    (measurePreserving_eval (fun _ : Fin n => P.measure) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n => P.measure) j).map_eq] using h

/-- [A residual pair is square integrable in the finite experiment.](goal) Under [the stated assumptions](hyp:hDesign,hij). -/
-- @node: projectionResidual_finite_memLp
lemma projectionResidual_finite_memLp (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    MemLp (fun o : Fin n → Record => projectionResidual P W V k (o i) (o j)) 2
      (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) := by
  have hm := projectionResidual_measurable P hDesign W V k
  have hp : MeasurePreserving (fun o : Fin n → Record => (o i, o j))
      (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n)
      (P.measure.prod P.measure) := ⟨by fun_prop, projection_pair_map P hij⟩
  simpa only [Function.comp_def, Function.eval,
      Causalean.Stat.UStatistic.LocalizedVariance.iidLaw] using
    (projectionResidual_memLp P hDesign W V k).comp_measurePreserving hp

/-- [Every one-record term has zero cross moment with a distinct residual pair.](goal) Under [the stated assumptions](hyp:hDesign,f,hfm,hf,hij). -/
-- @node: projectionResidual_finite_cross
lemma projectionResidual_finite_cross (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k n : ℕ) (f : Record → ℝ)
    (hfm : Measurable f) (hf : MemLp f 2 P.measure)
    (a i j : Fin n) (hij : i ≠ j) :
    (∫ o : Fin n → Record, f (o a) * projectionResidual P W V k (o i) (o j)
      ∂Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) = 0 := by
  let μ := Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, Causalean.Stat.UStatistic.LocalizedVariance.iidLaw]
    infer_instance
  have hm := projectionResidual_measurable P hDesign W V k
  by_cases hai : a = i
  · subst a
    have hF : Measurable (fun z : Record × Record =>
        f z.1 * projectionResidual P W V k z.1 z.2) := by fun_prop
    have h := integral_map (μ := μ)
      (φ := fun o : Fin n → Record => (o i, o j)) (by fun_prop)
      hF.aestronglyMeasurable
    rw [projection_pair_map P hij] at h
    exact h.symm.trans (projectionResidual_cross_fst P hDesign W V k f hfm hf)
  by_cases haj : a = j
  · subst a
    have hF : Measurable (fun z : Record × Record =>
        f z.2 * projectionResidual P W V k z.1 z.2) := by fun_prop
    have h := integral_map (μ := μ)
      (φ := fun o : Fin n → Record => (o i, o j)) (by fun_prop)
      hF.aestronglyMeasurable
    rw [projection_pair_map P hij] at h
    exact h.symm.trans (projectionResidual_cross_snd P hDesign W V k f hfm hf)
  · have hcoord : iIndepFun (fun b : Fin n => fun o : Fin n → Record => o b) μ := by
      dsimp [μ, Causalean.Stat.UStatistic.LocalizedVariance.iidLaw]
      simpa using (iIndepFun_pi (μ := fun _ : Fin n => P.measure)
        (X := fun _ : Fin n => id) (fun _ => aemeasurable_id))
    have hind := hcoord.indepFun_prodMk (fun b => measurable_pi_apply b)
      i j a (Ne.symm hai) (Ne.symm haj)
    have hmap : μ.map (fun o : Fin n → Record => (o a, (o i, o j))) =
        P.measure.prod (P.measure.prod P.measure) := by
      have h := hind.symm.map_prod_eq_prod_map_map
        (measurable_pi_apply a).aemeasurable
        ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
      rw [projection_pair_map P hij] at h
      simpa only [μ, Causalean.Stat.UStatistic.LocalizedVariance.iidLaw,
        (measurePreserving_eval (fun _ : Fin n => P.measure) a).map_eq] using h
    have hF : Measurable (fun z : Record × (Record × Record) =>
        f z.1 * projectionResidual P W V k z.2.1 z.2.2) := by fun_prop
    have h := integral_map (μ := μ)
      (φ := fun o : Fin n → Record => (o a, (o i, o j))) (by fun_prop)
      hF.aestronglyMeasurable
    rw [hmap] at h
    exact h.symm.trans (projectionResidual_cross_independent P hDesign W V k f)

/-- [The first-order finite sum is square integrable.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: projectionFirst_finite_memLp
lemma projectionFirst_finite_memLp (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k n : ℕ) :
    MemLp (fun o : Fin n → Record => 2 / (n : ℝ) *
      ∑ i, (projectionFirst P W V k (o i) - projectionMean P W V k)) 2
      (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) := by
  classical
  have hi (i : Fin n) : MemLp (fun o : Fin n → Record =>
      projectionFirst P W V k (o i) - projectionMean P W V k) 2
      (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) := by
    simpa only [Function.comp_def, Function.eval,
      Causalean.Stat.UStatistic.LocalizedVariance.iidLaw] using
      (projectionFirst_centered_memLp P hDesign W V k).comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin n => P.measure) i)
  exact (memLp_finsetSum _ (fun i _ => hi i)).const_mul _

/-- [The residual average is square integrable in the finite experiment.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: projectionResidual_average_memLp
lemma projectionResidual_average_memLp (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k n : ℕ) :
    MemLp (fun o : Fin n → Record => ((n : ℝ) * ((n : ℝ) - 1))⁻¹ *
      ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
        projectionResidual P W V k (o ij.1) (o ij.2)) 2
      (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) := by
  classical
  exact (memLp_finsetSum _ (fun ij hij =>
    projectionResidual_finite_memLp P hDesign W V k n (Finset.mem_offDiag.mp hij).2.2)).const_mul _

/-- [The two finite Hoeffding components are orthogonal.](goal) Under [the stated assumptions](hyp:hDesign). -/
-- @node: projection_hoeffding_cross
lemma projection_hoeffding_cross (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k n : ℕ) :
    (∫ o : Fin n → Record,
      (2 / (n : ℝ) * ∑ i, (projectionFirst P W V k (o i) - projectionMean P W V k)) *
      (((n : ℝ) * ((n : ℝ) - 1))⁻¹ *
        ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
          projectionResidual P W V k (o ij.1) (o ij.2))
      ∂Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) = 0 := by
  classical
  let f := fun x => projectionFirst P W V k x - projectionMean P W V k
  let μ := Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n
  let s := (Finset.univ : Finset (Fin n)).offDiag
  have hfm : Measurable f := (projectionFirst_measurable P hDesign W V k).sub_const _
  have hf : MemLp f 2 P.measure := projectionFirst_centered_memLp P hDesign W V k
  have hfi (i : Fin n) : MemLp (fun o : Fin n → Record => f (o i)) 2 μ := by
    simpa only [Function.comp_def, Function.eval, μ,
      Causalean.Stat.UStatistic.LocalizedVariance.iidLaw] using
      hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => P.measure) i)
  have hi (a : Fin n) (ij : Fin n × Fin n) (hij : ij ∈ s) :
      Integrable (fun o : Fin n → Record =>
        f (o a) * projectionResidual P W V k (o ij.1) (o ij.2)) μ :=
    (hfi a).integrable_mul (projectionResidual_finite_memLp P hDesign W V k n
      (Finset.mem_offDiag.mp hij).2.2)
  have he (o : Fin n → Record) :
      (2 / (n : ℝ) * ∑ i, f (o i)) *
        (((n : ℝ) * ((n : ℝ) - 1))⁻¹ *
          ∑ ij ∈ s, projectionResidual P W V k (o ij.1) (o ij.2)) =
      (2 / (n : ℝ) * ((n : ℝ) * ((n : ℝ) - 1))⁻¹) *
        ∑ a, ∑ ij ∈ s, f (o a) * projectionResidual P W V k (o ij.1) (o ij.2) := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    ring
  change (∫ o : Fin n → Record, (2 / (n : ℝ) * ∑ i, f (o i)) *
    (((n : ℝ) * ((n : ℝ) - 1))⁻¹ *
      ∑ ij ∈ s, projectionResidual P W V k (o ij.1) (o ij.2)) ∂μ) = 0
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum _ (fun a _ =>
    integrable_finsetSum _ (fun ij hij => hi a ij hij))]
  have hz (a : Fin n) : (∫ o : Fin n → Record,
      ∑ ij ∈ s, f (o a) * projectionResidual P W V k (o ij.1) (o ij.2) ∂μ) = 0 := by
    rw [integral_finsetSum _ (fun ij hij => hi a ij hij)]
    apply Finset.sum_eq_zero
    intro ij hij
    exact projectionResidual_finite_cross P hDesign W V k n f hfm hf a ij.1 ij.2
      (Finset.mem_offDiag.mp hij).2.2
  simp_rw [hz]
  simp

/-- [Exact orthogonality assembles the sharp finite-sample variance bound.](goal) Under [the stated assumptions](hyp:hDesign,hn). -/
-- @node: projectionStatistic_variance_le
lemma projectionStatistic_variance_le (P : ObservedLaw) (hDesign : UniformDesign P)
    (W V : BoundedMark) (k n : ℕ) (hn : 2 ≤ n) :
    (∫ o : Fin n → Record, (projectionStatistic n k W.value V.value o -
      ∫ p, projectionStatistic n k W.value V.value p
        ∂Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n)^2
      ∂Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) ≤
      4 / (n : ℝ) + 2 * k / ((n : ℝ) * ((n : ℝ) - 1)) := by
  classical
  let μ := Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n
  let L := fun o : Fin n → Record => 2 / (n : ℝ) *
    ∑ i, (projectionFirst P W V k (o i) - projectionMean P W V k)
  let R := fun o : Fin n → Record => ((n : ℝ) * ((n : ℝ) - 1))⁻¹ *
    ∑ ij ∈ (Finset.univ : Finset (Fin n)).offDiag,
      projectionResidual P W V k (o ij.1) (o ij.2)
  have hLm : MemLp L 2 μ := projectionFirst_finite_memLp P hDesign W V k n
  have hRm : MemLp R 2 μ := projectionResidual_average_memLp P hDesign W V k n
  have hLs : Integrable (fun o => (L o)^2) μ :=
    (memLp_two_iff_integrable_sq hLm.aestronglyMeasurable).mp hLm
  have hRs : Integrable (fun o => (R o)^2) μ :=
    (memLp_two_iff_integrable_sq hRm.aestronglyMeasurable).mp hRm
  have hLR : Integrable (fun o => L o * R o) μ := hLm.integrable_mul hRm
  have hcross : (∫ o, L o * R o ∂μ) = 0 := projection_hoeffding_cross P hDesign W V k n
  have hLbound : (∫ o, (L o)^2 ∂μ) ≤ 4 / (n : ℝ) :=
    projectionFirst_finite_secondMoment_le P hDesign W V k n hn
  have hRbound : (∫ o, (R o)^2 ∂μ) ≤ 2 * k / ((n : ℝ) * ((n : ℝ) - 1)) :=
    projectionResidual_finite_secondMoment_le P hDesign W V k n hn
  rw [projectionStatistic_integral P hDesign W V k n hn]
  change (∫ o, (projectionStatistic n k W.value V.value o - projectionMean P W V k)^2 ∂μ) ≤ _
  simp_rw [projectionStatistic_hoeffding P W V k n hn]
  change (∫ o, (L o + R o)^2 ∂μ) ≤ _
  have hexpand (o : Fin n → Record) :
      (L o + R o)^2 = (L o)^2 + (R o)^2 + 2 * (L o * R o) := by ring
  simp_rw [hexpand]
  integral_linearity
  rw [hcross, mul_zero, add_zero]
  exact add_le_add hLbound hRbound

end CausalSmith.Stat.LogoddsLowsmoothFrontier

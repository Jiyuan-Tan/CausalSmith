module
public import Causalean.Mathlib.MeasureTheory.CondExpPreimage
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Likelihood-score projection through measurable statistics

This module develops guarded likelihood scores for dominated laws and proves
that pushing a law through any measurable statistic projects its score onto the
statistic's σ-algebra, provided the derivative density on the statistic's space
is assumed to be the pushforward of the source derivative density.  It also
gives the corresponding L² contraction, without conditional distributions or
regularity assumptions on the sample spaces.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Stat.ScoreProjection

variable {α : Type*} [MeasurableSpace α]

/-- A [density](hyp:q), [signed derivative density](hyp:qdot), and [observation](hyp:x)
determine [the guarded likelihood score](goal), [given by their quotient away from a
zero density and by zero at a zero density](step:1). -/
noncomputable def guardedScore (q qdot : α → ℝ) (x : α) : ℝ :=
  if q x = 0 then 0 else qdot x / q x

/-- [Measurable density and derivative functions](hyp:q,qdot,hq,hqdot) give [a measurable
guarded likelihood score](goal). -/
@[fun_prop] theorem measurable_guardedScore {q qdot : α → ℝ}
    (hq : Measurable q) (hqdot : Measurable qdot) :
    Measurable (guardedScore q qdot) := by
  unfold guardedScore
  exact Measurable.ite (hq (measurableSet_singleton 0)) measurable_const (hqdot.div hq)

/-- A [reference measure, density, and derivative density](hyp:ν,q,qdot) whose [derivative
vanishes wherever the density vanishes](hyp:hzero) satisfy [the almost-everywhere identity
between the derivative density and density times its guarded score](goal). -/
theorem derivative_eq_density_mul_guardedScore
    {ν : Measure α} {q qdot : α → ℝ}
    (hzero : ∀ᵐ x ∂ν, q x = 0 → qdot x = 0) :
    ∀ᵐ x ∂ν, qdot x = q x * guardedScore q qdot x := by
  filter_upwards [hzero] with x hx
  by_cases hq : q x = 0
  · simp [guardedScore, hq, hx hq]
  · simp [guardedScore, hq, mul_div_cancel₀ _ hq]

/-- A [reference measure and law](hyp:ν,μ), [measurable density and derivative density](hyp:q,qdot,hq),
[nonnegative density](hyp:hqnonneg), [zero-set derivative control](hyp:hzero), [density
representation of the law](hyp:hμ), and [integrable derivative density](hyp:hderivInt) give
[an integrable guarded likelihood score under the law](goal). -/
theorem integrable_guardedScore_of_derivative_integrable
    (ν μ : Measure α) (q qdot : α → ℝ)
    (hq : Measurable q)
    (hqnonneg : ∀ᵐ x ∂ν, 0 ≤ q x)
    (hzero : ∀ᵐ x ∂ν, q x = 0 → qdot x = 0)
    (hμ : μ = ν.withDensity (fun x => ENNReal.ofReal (q x)))
    (hderivInt : Integrable qdot ν) :
    Integrable (guardedScore q qdot) μ := by
  rw [hμ, integrable_withDensity_iff_integrable_smul' hq.ennreal_ofReal (by simp)]
  apply hderivInt.congr
  filter_upwards [hqnonneg, derivative_eq_density_mul_guardedScore hzero] with x hx hxeq
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]
  exact hxeq

/-- A [finite reference measure and law](hyp:ν,μ), [measurable density and derivative
density](hyp:q,qdot,hq), [nonnegative density](hyp:hqnonneg), [zero-set derivative
control](hyp:hzero), [density representation](hyp:hμ), and [measurable event](hyp:A,hA) make [the guarded-score
integral on that event equal the derivative-density integral](goal). -/
theorem setIntegral_guardedScore_eq_derivative
    (ν μ : Measure α) [IsFiniteMeasure ν]
    (q qdot : α → ℝ)
    (hq : Measurable q)
    (hqnonneg : ∀ᵐ x ∂ν, 0 ≤ q x)
    (hzero : ∀ᵐ x ∂ν, q x = 0 → qdot x = 0)
    (hμ : μ = ν.withDensity (fun x => ENNReal.ofReal (q x)))
    {A : Set α} (hA : MeasurableSet A) :
    ∫ x in A, guardedScore q qdot x ∂μ = ∫ x in A, qdot x ∂ν := by
  rw [hμ, restrict_withDensity hA,
    integral_withDensity_eq_integral_toReal_smul hq.ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hqnonneg,
    ae_restrict_of_ae (derivative_eq_density_mul_guardedScore hzero)] with x hxq hxeq
  rw [ENNReal.toReal_ofReal hxq, smul_eq_mul, ← hxeq]

variable {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
  (νΩ : Measure Ω) (νY : Measure Y) (μΩ : Measure Ω) (μY : Measure Y)
  [IsFiniteMeasure νΩ] [IsFiniteMeasure νY] [IsProbabilityMeasure μΩ]
  (T : Ω → Y) (qΩ qdotΩ : Ω → ℝ) (qY qdotY : Y → ℝ)

/-- A [measurable statistic](hyp:T,hT) with [its pushed-forward law](hyp:μΩ,μY,hμYmap),
[integrable source and statistic functions](hyp:f,g,hf,hg), and [a measurable statistic
function](hyp:hgmeas) has [its conditional expectation equal to the pulled-back statistic
function exactly when their integrals agree on every measurable statistic event](goal). -/
theorem condExp_eq_statistic_iff_integral_preimage_eq
    (hT : Measurable T) (hμYmap : μY = μΩ.map T)
    (f : Ω → ℝ) (g : Y → ℝ)
    (hf : Integrable f μΩ) (hg : Integrable g μY)
    (hgmeas : Measurable g) :
    (μΩ[f | MeasurableSpace.comap T inferInstance] =ᵐ[μΩ] fun ω => g (T ω)) ↔
      ∀ A : Set Y, MeasurableSet A →
        ∫ ω in T ⁻¹' A, f ω ∂μΩ = ∫ y in A, g y ∂μY := by
  have hmap (A : Set Y) (hA : MeasurableSet A) :
      ∫ ω in T ⁻¹' A, g (T ω) ∂μΩ = ∫ y in A, g y ∂μY := by
    rw [hμYmap]
    exact (setIntegral_map hA hgmeas.aestronglyMeasurable hT.aemeasurable).symm
  constructor
  · intro hcond A hA
    calc
      ∫ ω in T ⁻¹' A, f ω ∂μΩ =
          ∫ ω in T ⁻¹' A, (μΩ[f | MeasurableSpace.comap T inferInstance]) ω ∂μΩ :=
        (setIntegral_condExp hT.comap_le hf ⟨A, hA, rfl⟩).symm
      _ = ∫ ω in T ⁻¹' A, g (T ω) ∂μΩ :=
        setIntegral_congr_ae (hT hA) (hcond.mono fun ω hω _ => hω)
      _ = ∫ y in A, g y ∂μY := hmap A hA
  · intro hintegral
    have hgmap : Integrable g (μΩ.map T) := by simpa only [hμYmap] using hg
    have hgcomp : Integrable (fun ω => g (T ω)) μΩ := by
      simpa only [Function.comp_def] using hgmap.comp_measurable hT
    have hTcomap : Measurable[MeasurableSpace.comap T inferInstance] T :=
      comap_measurable T
    have hgstrong : StronglyMeasurable[MeasurableSpace.comap T inferInstance]
        (fun ω => g (T ω)) := hgmeas.stronglyMeasurable.comp_measurable hTcomap
    exact Causalean.Mathlib.MeasureTheory.condExp_eq_of_integral_preimage_eq
      μΩ T hT f (fun ω => g (T ω)) hf hgcomp hgstrong.aestronglyMeasurable
      (by
        intro A hA
        exact (hintegral A hA).trans (hmap A hA).symm)

/-- [Finite source and statistic reference measures](hyp:νΩ,νY), [source and statistic
laws](hyp:μΩ,μY), [a measurable statistic](hyp:T,hT), [densities and derivative
densities, all measurable except possibly the source derivative density](hyp:qΩ,qdotΩ,qY,qdotY,hqΩ,hqY,hqdotY), [nonnegative densities](hyp:hqΩnonneg,hqYnonneg),
[zero-set derivative controls](hyp:hzeroΩ,hzeroY), [the source and statistic density laws](hyp:hμΩ,hμYmap,hμYdensity), [an exact
derivative pushforward identity](hyp:hderivMap), and [a measurable statistic event](hyp:A,hA)
give [equal source-score and pulled-back statistic-score integrals on that event](goal). -/
theorem score_integral_preimage_eq
    (hT : Measurable T)
    (hqΩ : Measurable qΩ)
    (hqY : Measurable qY) (hqdotY : Measurable qdotY)
    (hqΩnonneg : ∀ᵐ ω ∂νΩ, 0 ≤ qΩ ω)
    (hqYnonneg : ∀ᵐ y ∂νY, 0 ≤ qY y)
    (hzeroΩ : ∀ᵐ ω ∂νΩ, qΩ ω = 0 → qdotΩ ω = 0)
    (hzeroY : ∀ᵐ y ∂νY, qY y = 0 → qdotY y = 0)
    (hμΩ : μΩ = νΩ.withDensity (fun ω => ENNReal.ofReal (qΩ ω)))
    (hμYmap : μY = μΩ.map T)
    (hμYdensity : μY = νY.withDensity (fun y => ENNReal.ofReal (qY y)))
    (hderivMap : ∀ A : Set Y, MeasurableSet A →
      ∫ ω in T ⁻¹' A, qdotΩ ω ∂νΩ = ∫ y in A, qdotY y ∂νY)
    (A : Set Y) (hA : MeasurableSet A) :
    ∫ ω in T ⁻¹' A, guardedScore qΩ qdotΩ ω ∂μΩ =
      ∫ ω in T ⁻¹' A, guardedScore qY qdotY (T ω) ∂μΩ := by
  have hmap :
      ∫ ω in T ⁻¹' A, guardedScore qY qdotY (T ω) ∂μΩ =
        ∫ y in A, guardedScore qY qdotY y ∂μY := by
    rw [hμYmap]
    exact (setIntegral_map hA
      (measurable_guardedScore hqY hqdotY).aestronglyMeasurable
      hT.aemeasurable).symm
  calc
    ∫ ω in T ⁻¹' A, guardedScore qΩ qdotΩ ω ∂μΩ =
        ∫ ω in T ⁻¹' A, qdotΩ ω ∂νΩ :=
      setIntegral_guardedScore_eq_derivative νΩ μΩ qΩ qdotΩ
        hqΩ hqΩnonneg hzeroΩ hμΩ (hT hA)
    _ = ∫ y in A, qdotY y ∂νY := hderivMap A hA
    _ = ∫ y in A, guardedScore qY qdotY y ∂μY :=
      (setIntegral_guardedScore_eq_derivative νY μY qY qdotY
        hqY hqYnonneg hzeroY hμYdensity hA).symm
    _ = ∫ ω in T ⁻¹' A, guardedScore qY qdotY (T ω) ∂μΩ := hmap.symm

/-- Take [finite reference measures on the source space and on the statistic's space](hyp:νΩ,νY),
[a source probability law and a statistic law](hyp:μΩ,μY), [a measurable statistic](hyp:T,hT),
and [real densities and derivative densities on both spaces, all measurable except possibly the
source derivative density](hyp:qΩ,qdotΩ,qY,qdotY,hqΩ,hqY,hqdotY).
Suppose [the densities are nonnegative almost everywhere under their reference
measures](hyp:hqΩnonneg,hqYnonneg), [each derivative density vanishes almost everywhere where
its density vanishes](hyp:hzeroΩ,hzeroY), [the source law has the source density with respect to
its reference measure, the statistic law is the law of the statistic under the source law, and
it has the statistic density with respect to its reference measure](hyp:hμΩ,hμYmap,hμYdensity),
[both guarded scores are integrable under their laws](hyp:hscoreΩInt,hscoreYInt), and
[the derivative densities are linked by the same pushforward: for every measurable set of
statistic values, the source derivative density integrated over the set's preimage equals the
statistic derivative density integrated over the set](hyp:hderivMap). Then [the conditional
expectation, under the source law, of the source guarded score given the statistic equals the
statistic's guarded score evaluated at the statistic, almost everywhere](goal).

The derivative densities are arbitrary signed functions; the pushforward link between them is
an assumption, not derived from a parametric family. -/
theorem condExp_guardedScore_eq_statistic_score
    (hT : Measurable T)
    (hqΩ : Measurable qΩ)
    (hqY : Measurable qY) (hqdotY : Measurable qdotY)
    (hqΩnonneg : ∀ᵐ ω ∂νΩ, 0 ≤ qΩ ω)
    (hqYnonneg : ∀ᵐ y ∂νY, 0 ≤ qY y)
    (hzeroΩ : ∀ᵐ ω ∂νΩ, qΩ ω = 0 → qdotΩ ω = 0)
    (hzeroY : ∀ᵐ y ∂νY, qY y = 0 → qdotY y = 0)
    (hμΩ : μΩ = νΩ.withDensity (fun ω => ENNReal.ofReal (qΩ ω)))
    (hμYmap : μY = μΩ.map T)
    (hμYdensity : μY = νY.withDensity (fun y => ENNReal.ofReal (qY y)))
    (hscoreΩInt : Integrable (guardedScore qΩ qdotΩ) μΩ)
    (hscoreYInt : Integrable (guardedScore qY qdotY) μY)
    (hderivMap : ∀ A : Set Y, MeasurableSet A →
      ∫ ω in T ⁻¹' A, qdotΩ ω ∂νΩ = ∫ y in A, qdotY y ∂νY) :
    μΩ[guardedScore qΩ qdotΩ | MeasurableSpace.comap T inferInstance] =ᵐ[μΩ]
      fun ω => guardedScore qY qdotY (T ω) := by
  apply (condExp_eq_statistic_iff_integral_preimage_eq μΩ μY T hT hμYmap
    (guardedScore qΩ qdotΩ) (guardedScore qY qdotY)
    hscoreΩInt hscoreYInt (measurable_guardedScore hqY hqdotY)).2
  intro A hA
  calc
    ∫ ω in T ⁻¹' A, guardedScore qΩ qdotΩ ω ∂μΩ =
        ∫ ω in T ⁻¹' A, guardedScore qY qdotY (T ω) ∂μΩ :=
      score_integral_preimage_eq νΩ νY μΩ μY T qΩ qdotΩ qY qdotY
        hT hqΩ hqY hqdotY hqΩnonneg hqYnonneg
        hzeroΩ hzeroY hμΩ hμYmap hμYdensity hderivMap A hA
    _ = ∫ y in A, guardedScore qY qdotY y ∂μY := by
      rw [hμYmap]
      exact (setIntegral_map hA
        (measurable_guardedScore hqY hqdotY).aestronglyMeasurable
        hT.aemeasurable).symm

/-- Take [finite reference measures on the source space and on the statistic's space](hyp:νΩ,νY),
[a source probability law and a statistic law](hyp:μΩ,μY), [a measurable statistic](hyp:T,hT),
and [real densities and derivative densities on both spaces, all measurable except possibly the
source derivative density](hyp:qΩ,qdotΩ,qY,qdotY,hqΩ,hqY,hqdotY).
Suppose [the densities are nonnegative almost everywhere under their reference
measures](hyp:hqΩnonneg,hqYnonneg), [each derivative density vanishes almost everywhere where
its density vanishes](hyp:hzeroΩ,hzeroY), [the source law has the source density with respect to
its reference measure, the statistic law is the law of the statistic under the source law, and
it has the statistic density with respect to its reference measure](hyp:hμΩ,hμYmap,hμYdensity),
[the statistic derivative density is integrable under its reference measure](hyp:hderivYInt),
[for every measurable set of statistic values, the source derivative density integrated over the
set's preimage equals the statistic derivative density integrated over the set](hyp:hderivMap),
and [the source guarded score is square-integrable under the source law](hyp:hscoreΩL2). Then
[the statistic's guarded score is square-integrable under the statistic law, and its second
moment is at most the second moment of the source guarded score under the source law](goal). -/
theorem statistic_score_memLp_and_secondMoment_le
    (hT : Measurable T)
    (hqΩ : Measurable qΩ)
    (hqY : Measurable qY) (hqdotY : Measurable qdotY)
    (hqΩnonneg : ∀ᵐ ω ∂νΩ, 0 ≤ qΩ ω)
    (hqYnonneg : ∀ᵐ y ∂νY, 0 ≤ qY y)
    (hzeroΩ : ∀ᵐ ω ∂νΩ, qΩ ω = 0 → qdotΩ ω = 0)
    (hzeroY : ∀ᵐ y ∂νY, qY y = 0 → qdotY y = 0)
    (hμΩ : μΩ = νΩ.withDensity (fun ω => ENNReal.ofReal (qΩ ω)))
    (hμYmap : μY = μΩ.map T)
    (hμYdensity : μY = νY.withDensity (fun y => ENNReal.ofReal (qY y)))
    (hderivYInt : Integrable qdotY νY)
    (hderivMap : ∀ A : Set Y, MeasurableSet A →
      ∫ ω in T ⁻¹' A, qdotΩ ω ∂νΩ = ∫ y in A, qdotY y ∂νY)
    (hscoreΩL2 : MemLp (guardedScore qΩ qdotΩ) 2 μΩ) :
    MemLp (guardedScore qY qdotY) 2 μY ∧
      (∫ y, guardedScore qY qdotY y ^ 2 ∂μY) ≤
        ∫ ω, guardedScore qΩ qdotΩ ω ^ 2 ∂μΩ := by
  have hscoreΩInt : Integrable (guardedScore qΩ qdotΩ) μΩ :=
    hscoreΩL2.integrable (by norm_num)
  have hscoreYInt : Integrable (guardedScore qY qdotY) μY :=
    integrable_guardedScore_of_derivative_integrable νY μY qY qdotY
      hqY hqYnonneg hzeroY hμYdensity hderivYInt
  have hprojection := condExp_guardedScore_eq_statistic_score
    νΩ νY μΩ μY T qΩ qdotΩ qY qdotY hT hqΩ hqY hqdotY
    hqΩnonneg hqYnonneg hzeroΩ hzeroY hμΩ hμYmap hμYdensity
    hscoreΩInt hscoreYInt hderivMap
  have hpull : MemLp (fun ω => guardedScore qY qdotY (T ω)) 2 μΩ :=
    (memLp_congr_ae hprojection).mp
      (MemLp.condExp (m := MeasurableSpace.comap T inferInstance)
        (by norm_num) hscoreΩL2)
  have hscoreY : MemLp (guardedScore qY qdotY) 2 μY := by
    rw [hμYmap]
    exact (memLp_map_measure_iff
      (measurable_guardedScore hqY hqdotY).aestronglyMeasurable
      hT.aemeasurable).2 hpull
  refine ⟨hscoreY, ?_⟩
  have hbound := integral_norm_condExp_rpow_le
    (m := MeasurableSpace.comap T inferInstance) (μ := μΩ)
    (f := guardedScore qΩ qdotΩ) (p := (2 : ℝ)) (by norm_num)
    (by
      convert hscoreΩL2.integrable_norm_pow (p := 2) (by norm_num) using 1
      ext x
      rw [← @Nat.cast_two ℝ, Real.rpow_natCast])
  have hmap :
      (∫ y, guardedScore qY qdotY y ^ 2 ∂μY) =
        ∫ ω, guardedScore qY qdotY (T ω) ^ 2 ∂μΩ := by
    rw [hμYmap]
    exact integral_map hT.aemeasurable
      ((measurable_guardedScore hqY hqdotY).pow_const 2).aestronglyMeasurable
  rw [hmap]
  have hprojSq :
      (∫ ω, guardedScore qY qdotY (T ω) ^ 2 ∂μΩ) =
        ∫ ω, (μΩ[guardedScore qΩ qdotΩ |
          MeasurableSpace.comap T inferInstance]) ω ^ 2 ∂μΩ := by
    apply integral_congr_ae
    filter_upwards [hprojection] with ω hω
    rw [hω]
  rw [hprojSq]
  have hsq (x : ℝ) : ‖x‖ ^ (2 : ℝ) = x ^ 2 := by
    rw [← @Nat.cast_two ℝ, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  simpa only [hsq] using hbound

end Causalean.Stat.ScoreProjection

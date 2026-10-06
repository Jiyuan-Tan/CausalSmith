module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.CitedGates
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.SymmetricLaw
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TranscriptPreprocessing
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Finite-mixture density helpers

Measurability, domination and real-valued density versions for finite input experiments.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- [Finite atomic laws depend measurably on their real weights](goal) when [each atom's weight is measurable in the parameter](hyp:hw). -/
-- @node: measurable_atomLaw_weights
@[fun_prop] lemma measurable_atomLaw_weights {H I : Type} [MeasurableSpace H]
    [MeasurableSpace I] [Fintype I] (w : H → I → ℝ)
    (hw : ∀ i, Measurable (fun h => w h i)) : Measurable (fun h => atomLaw (w h)) := by
  unfold atomLaw
  exact Finset.measurable_sum _ (fun i _ => (hw i).ennreal_ofReal.smul_measure _)

/-- [The symmetric finite full-data construction is measurable in its parameter](goal). -/
-- @node: measurable_symmetricLaw_parameter
@[fun_prop] lemma measurable_symmetricLaw_parameter {d : ℕ} :
    Measurable (symmetricLaw : (Fin d → ℝ) → Measure (FullRecord d)) := by
  unfold symmetricLaw
  apply measurable_atomLaw_weights
  intro w
  unfold bernMass
  split_ifs <;> fun_prop

/-- Assume [positive dimension](hyp:hd). [At zero contrast every observed record has strictly positive mass](goal). -/
-- @node: observed_symmetric_zero_atom
lemma observed_symmetric_zero_atom {d : ℕ} (hd : 0 < d) (o : ObsRecord d) :
    (observedLaw (symmetricLaw (fun _ : Fin d => 0))) {o} ≠ 0 := by
  have hcube : (fun _ : Fin d => (0 : ℝ)) ∈ parameterCube d := by
    intro j; constructor <;> norm_num
  haveI := symmetricLaw_probability (fun _ : Fin d => 0) hcube hd
  haveI : IsProbabilityMeasure (observedLaw (symmetricLaw (fun _ : Fin d => 0))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hatom : (observedLaw (symmetricLaw (fun _ : Fin d => 0))).real {o} =
      (d : ℝ)⁻¹ / 4 := by
    rw [observedLaw, Measure.real, Measure.map_apply (by fun_prop) MeasurableSet.of_discrete]
    change (symmetricLaw (fun _ : Fin d => 0)).real (observe ⁻¹' {o}) = _
    rw [symmetricLaw_real_event _ hcube]
    rcases o with ⟨j,a,y⟩
    cases a <;> cases y <;>
      simp [Fintype.sum_prod_type, Fintype.sum_bool, observe, cell, arm, outcome,
        outcome0, outcome1, potential, bernMass]
    <;> ring
  intro hz
  have : (0 : ℝ) < (d : ℝ)⁻¹ / 4 := by positivity
  rw [Measure.real, hz, ENNReal.toReal_zero] at hatom
  linarith

/-- Assume [measurability of rows](hyp:hrows) and [the stated hpos condition](hyp:hpos). [A mixture with positive mass on every finite input dominates every other mixture of the same rows, regardless of the output space](goal). -/
-- @node: finite_bind_absolutelyContinuous
lemma finite_bind_absolutelyContinuous {I Z : Type} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace Z]
    (mu nu : Measure I) (rows : I → Measure Z) (hrows : Measurable rows)
    (hpos : ∀ i, nu {i} ≠ 0) : mu.bind rows ≪ nu.bind rows := by
  intro E hE
  have hEm := measurableSet_toMeasurable (nu.bind rows) E
  have hzero : (nu.bind rows) (toMeasurable (nu.bind rows) E) = 0 := by
    rwa [measure_toMeasurable]
  rw [Measure.bind_apply hEm hrows.aemeasurable, lintegral_fintype] at hzero
  have hrow : ∀ i, rows i (toMeasurable (nu.bind rows) E) = 0 := by
    intro i
    have hi := (Finset.sum_eq_zero_iff.mp hzero) i (Finset.mem_univ i)
    exact (mul_eq_zero.mp hi).resolve_right (hpos i)
  apply le_antisymm _ zero_le
  calc
    _ ≤ (mu.bind rows) (toMeasurable (nu.bind rows) E) :=
      measure_mono (subset_toMeasurable _ _)
    _ = 0 := by
      rw [Measure.bind_apply hEm hrows.aemeasurable, lintegral_fintype]
      simp [hrow]

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN) and [the stated absolute-continuity property](hyp:hac). [The cited kernel RN gate supplies jointly measurable real densities for dominated Markov kernels; finiteness of each row permits conversion from extended densities](goal). -/
-- @node: real_kernel_density_of_gate
lemma real_kernel_density_of_gate (hRN : MeasurableKernelRadonNikodym)
    {H Z : Type} [MeasurableSpace H] [MeasurableSpace Z] [StandardBorelSpace Z]
    (K L : Kernel H Z) [IsMarkovKernel K] [IsMarkovKernel L]
    (hac : ∀ h, K h ≪ L h) :
    ∃ f : H × Z → ℝ, Measurable f ∧ ∀ h,
      (L h).withDensity (fun z => ENNReal.ofReal (f (h,z))) = K h := by
  obtain ⟨f, hf, hrep⟩ := hRN K L hac
  refine ⟨fun w => (f w).toReal, hf.ennreal_toReal, ?_⟩
  intro h
  have hfin : (∫⁻ z, f (h,z) ∂L h) < ∞ := by
    have hu := hrep h Set.univ MeasurableSet.univ
    rw [setLIntegral_univ] at hu
    rw [← hu]
    exact measure_lt_top _ _
  have hae : ∀ᵐ z ∂L h, f (h,z) ≠ ∞ := by
    exact (ae_lt_top (show Measurable (fun z => f (h,z)) by fun_prop) hfin.ne).mono
      (fun z hz => hz.ne)
  ext E hE
  rw [withDensity_apply _ hE, hrep h E hE]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hae] with z hz
  exact ENNReal.ofReal_toReal hz

end CausalSmith.Stat.LdpOptvalueUniformFrontier

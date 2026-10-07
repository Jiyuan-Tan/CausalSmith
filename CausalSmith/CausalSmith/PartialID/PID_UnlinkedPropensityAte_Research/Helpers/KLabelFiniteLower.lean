module

public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.OrderedIntervalPartition
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Measure geometry for finite-label lower bounds under arbitrary measurable cells.
-/

public section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,z,t,B,hBmeas,hBsub,ht), this result [establishes the stated mathematical conclusion](goal). -/
lemma boundedCell_absDeviation_tail_lower
    {a b z t : ℝ} {B : Set ℝ} (hBmeas : MeasurableSet B)
    (hBsub : B ⊆ Icc a b) (ht : 0 ≤ t) :
    volume.real B - 2 * t ≤
      (volume.restrict B).real {x : ℝ | t < |x - z|} := by
  let C : Set ℝ := Icc (z - t) (z + t)
  let T : Set ℝ := B ∩ {x : ℝ | t < |x - z|}
  have htailMeas : MeasurableSet {x : ℝ | t < |x - z|} := by
    exact measurableSet_lt measurable_const ((measurable_id.sub measurable_const).norm)
  have hTmeas : MeasurableSet T := hBmeas.inter htailMeas
  have hcover : B ⊆ C ∪ T := by
    intro x hx
    by_cases hxt : t < |x - z|
    · exact mem_union_right C ⟨hx, hxt⟩
    · left
      dsimp [C]
      rw [mem_Icc]
      have habs : |x - z| ≤ t := le_of_not_gt hxt
      exact ⟨by linarith [neg_le_abs (x - z)], by linarith [le_abs_self (x - z)]⟩
  have hBfinite : volume B ≠ ∞ :=
    (measure_ne_top_of_subset hBsub measure_Icc_lt_top.ne)
  have hTfinite : volume T ≠ ∞ :=
    (measure_ne_top_of_subset inter_subset_left hBfinite)
  have hCfinite : volume C ≠ ∞ := measure_Icc_lt_top.ne
  have hUnionFinite : volume (C ∪ T) ≠ ∞ :=
    (measure_union_lt_top hCfinite.lt_top hTfinite.lt_top).ne
  have hmass : volume.real B ≤ volume.real C + volume.real T :=
    (measureReal_mono hcover hUnionFinite).trans (measureReal_union_le C T)
  have hCmass : volume.real C = 2 * t := by
    dsimp [C]
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  have hTmass : volume.real T =
      (volume.restrict B).real {x : ℝ | t < |x - z|} := by
    rw [Measure.real_def, Measure.real_def, Measure.restrict_apply htailMeas]
    rw [inter_comm]
  rw [hCmass, hTmass] at hmass
  linarith

/-- Given [the stated mathematical inputs and assumptions](hyp:K,hK,m), this result [establishes the stated mathematical conclusion](goal). -/
lemma sum_cellMass_sq_lower (K : ℕ) (hK : 0 < K) (m : Fin K → ℝ) :
    (∑ j, m j) ^ 2 / K ≤ ∑ j, (m j) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := m)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  apply (div_le_iff₀ hKreal).2
  simpa [mul_comm] using h

/-- Given [the stated mathematical inputs and assumptions](hyp:a,b,z,B,hBmeas,hBsub), this result [establishes the stated mathematical conclusion](goal). -/
lemma boundedCell_absDeviation_integral_lower
    {a b z : ℝ} {B : Set ℝ} (hBmeas : MeasurableSet B)
    (hBsub : B ⊆ Icc a b) :
    volume.real B ^ 2 / 4 ≤ ∫ x in B, |x - z| := by
  let μ : Measure ℝ := volume.restrict B
  let q : ℝ → ℝ := fun t => μ.real {x : ℝ | t < |x - z|}
  have hμfinite : μ Set.univ ≠ ∞ := by
    dsimp [μ]
    rw [Measure.restrict_apply_univ]
    exact measure_ne_top_of_subset hBsub measure_Icc_lt_top.ne
  let _ : IsFiniteMeasure μ := ⟨hμfinite.lt_top⟩
  have hInt : Integrable (fun x : ℝ => |x - z|) μ := by
    apply Integrable.of_bound (by fun_prop) (|a| + |b| + |z| + 1)
    filter_upwards [ae_restrict_mem hBmeas] with x hx
    have hxI := hBsub hx
    have hxabs : |x| ≤ |a| + |b| := by
      apply abs_le.mpr
      constructor
      · calc
          -(|a| + |b|) ≤ -|a| := by linarith [abs_nonneg b]
          _ ≤ a := neg_abs_le a
          _ ≤ x := hxI.1
      · calc
          x ≤ b := hxI.2
          _ ≤ |b| := le_abs_self b
          _ ≤ |a| + |b| := by linarith [abs_nonneg a]
    calc
      ‖|x - z|‖ = |x - z| := by simp
      _ ≤ |x| + |z| := abs_sub x z
      _ ≤ |a| + |b| + |z| + 1 := by linarith
  have hnonneg : 0 ≤ᵐ[μ] (fun x : ℝ => |x - z|) :=
    Eventually.of_forall fun x => abs_nonneg _
  have hqmeas : Measurable q := by
    apply Measurable.ennreal_toReal
    exact Antitone.measurable fun s t hst => measure_mono fun _ hx => hst.trans_lt hx
  have hqnonneg : ∀ t, 0 ≤ q t := fun _ => measureReal_nonneg
  have hlayer := lintegral_eq_lintegral_meas_lt μ hnonneg hInt.aemeasurable
  have hqLIntegral :
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (q t)) =
        ∫⁻ t in Ioi (0 : ℝ), μ {x : ℝ | t < |x - z|} := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp [q]
    rw [Measure.real_def, ENNReal.ofReal_toReal]
    exact measure_ne_top_of_subset (subset_univ _) hμfinite
  have hqIntegralFinite :
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (q t)) < ∞ := by
    rw [hqLIntegral, ← hlayer]
    exact hInt.lintegral_lt_top
  have hqInt : IntegrableOn q (Ioi (0 : ℝ)) := by
    refine ⟨hqmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa [Real.norm_eq_abs, abs_of_nonneg (hqnonneg _), ENNReal.ofReal_eq_coe_nnreal]
      using hqIntegralFinite
  have hlayerReal := hInt.integral_eq_integral_meas_lt hnonneg
  change volume.real B ^ 2 / 4 ≤ ∫ x, |x - z| ∂μ
  rw [hlayerReal]
  let m : ℝ := volume.real B
  have hm : 0 ≤ m := measureReal_nonneg
  have hbaseInt : IntegrableOn (fun t : ℝ => m - 2 * t) (Ioc 0 (m / 2)) := by
    exact ((continuous_const.sub (continuous_const.mul continuous_id)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have htailInt : IntegrableOn q (Ioc 0 (m / 2)) :=
    hqInt.mono_set Ioc_subset_Ioi_self
  have hmono :
      (∫ t in Ioc 0 (m / 2), m - 2 * t) ≤
        ∫ t in Ioc 0 (m / 2), q t := by
    apply integral_mono_ae hbaseInt htailInt
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    dsimp [q, μ, m]
    exact boundedCell_absDeviation_tail_lower hBmeas hBsub ht.1.le
  have hsubset :
      (∫ t in Ioc 0 (m / 2), q t) ≤ ∫ t in Ioi 0, q t := by
    exact integral_mono_measure (Measure.restrict_mono_set volume Ioc_subset_Ioi_self)
      (Eventually.of_forall fun t => hqnonneg t) hqInt
  have hbase : (∫ t in Ioc 0 (m / 2), m - 2 * t) = m ^ 2 / 4 := by
    rw [← intervalIntegral.integral_of_le (by linarith)]
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const_mul]
      rw [integral_id]
      simp [intervalIntegral.integral_const, smul_eq_mul]
      ring
    · exact continuous_const.intervalIntegrable 0 (m / 2)
    · exact (continuous_const.mul continuous_id).intervalIntegrable 0 (m / 2)
  dsimp [m] at hbase
  rw [← hbase]
  exact hmono.trans hsubset

end

end CausalSmith.PartialID.UnlinkedPropensityAte

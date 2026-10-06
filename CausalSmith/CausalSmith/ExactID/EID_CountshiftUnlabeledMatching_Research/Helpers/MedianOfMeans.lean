module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Basic
public import Mathlib.Probability.Moments.Variance
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.MedianOfMeansCore

/-! Finite-variance block-median deviation. -/

public section

open MeasureTheory ProbabilityTheory

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

-- @node: medianOfMeans_deviation
lemma medianOfMeans_deviation {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Fin n → Ω → ℝ) (r0 : Fin n) (η σ : ℝ)
    (hη : 0 < η ∧ η < 1) (hσ : 0 ≤ σ)
    (hiid : iIndepFun Y μ)
    (hLp : ∀ r, MemLp (Y r) 2 μ)
    (hmeans : ∀ r s, ∫ ω, Y r ω ∂μ = ∫ ω, Y s ω ∂μ)
    (hvar : ∀ r, variance (Y r) μ ≤ σ ^ 2)
    (hn : 8 * momBlocks η ≤ n) :
    μ {ω | |medianOfMeans (momBlocks η) (fun r => Y r ω) -
      ∫ ω, Y r0 ω ∂μ| ≤
      8 * σ * Real.sqrt (Real.log (2 / η) / n)} ≥ ENNReal.ofReal (1 - η) := by
  classical
  let Y' : Fin n → Ω → ℝ := fun r => (hLp r).1.mk (Y r)
  have hYY' : ∀ r, Y r =ᵐ[μ] Y' r := fun r => (hLp r).1.ae_eq_mk
  have hY'meas : ∀ r, Measurable (Y' r) := fun r => (hLp r).1.measurable_mk
  have hY'Lp : ∀ r, MemLp (Y' r) 2 μ := fun r =>
    (memLp_congr_ae (hYY' r)).mp (hLp r)
  have hY'ind : iIndepFun Y' μ := hiid.congr hYY'
  have hY'means : ∀ r s, ∫ ω, Y' r ω ∂μ = ∫ ω, Y' s ω ∂μ := by
    intro r s
    rw [integral_congr_ae (hYY' r).symm, integral_congr_ae (hYY' s).symm]
    exact hmeans r s
  have hY'var : ∀ r, variance (Y' r) μ ≤ σ ^ 2 := by
    intro r
    rw [variance_congr (hYY' r).symm]
    exact hvar r
  have hall : ∀ᵐ ω ∂μ, ∀ r, Y r ω = Y' r ω := ae_all_iff.2 hYY'
  have hcenter : ∫ ω, Y r0 ω ∂μ = ∫ ω, Y' r0 ω ∂μ :=
    integral_congr_ae (hYY' r0)
  rcases hσ.eq_or_lt with rfl | hσpos
  · have hzero : ∀ r, variance (Y r) μ = 0 := by
      intro r
      exact le_antisymm (by simpa using hvar r) (variance_nonneg _ _)
    have hconst : ∀ᵐ ω ∂μ, ∀ r, Y r ω = ∫ x, Y r0 x ∂μ := by
      rw [ae_all_iff]
      intro r
      filter_upwards [ae_eq_integral_of_variance_eq_zero (hLp r) (hzero r)] with ω hω
      rw [hω, hmeans r r0]
    let k := momBlocks η
    have hkpos : 0 < k := by
      have hkreal : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le
        (mul_pos (by norm_num : (0 : ℝ) < 8) (mom_log_pos hη))
        (by simpa [k] using momBlocks_real_lower hη)
      exact_mod_cast hkreal
    have hk : k ≤ n := le_trans (by omega : k ≤ 8 * k) (by simpa [k] using hn)
    have hgood : ∀ᵐ ω ∂μ,
        |medianOfMeans k (fun r => Y r ω) - ∫ x, Y r0 x ∂μ| ≤ 0 := by
      filter_upwards [hconst] with ω hω
      apply medianOfMeans_mem_interval_of_majority hkpos (fun r => Y r ω)
        (∫ x, Y r0 x ∂μ) 0 (le_refl 0)
      have hb : ∀ s : Fin k, blockMean k (fun r => Y r ω) s = ∫ x, Y r0 x ∂μ := by
        intro s
        rw [blockMean_eq_sum_momBlock]
        simp_rw [hω]
        have hc := momBlock_card_pos (n := n) hk hkpos s
        simp [hc.ne']
      simp [hb]
      omega
    have hfull : μ {ω | |medianOfMeans k (fun r => Y r ω) -
        ∫ x, Y r0 x ∂μ| ≤ 0} = 1 := by
      apply le_antisymm
      · simpa using measure_mono (μ := μ) (show {ω |
          |medianOfMeans k (fun r => Y r ω) - ∫ x, Y r0 x ∂μ| ≤ 0} ⊆ Set.univ by simp)
      · simpa using measure_mono_ae (μ := μ) (s := Set.univ) (t := {ω |
          |medianOfMeans k (fun r => Y r ω) - ∫ x, Y r0 x ∂μ| ≤ 0})
          (hgood.mono fun _ h _ => h)
    rw [show 8 * 0 * Real.sqrt (Real.log (2 / η) / ↑n) = 0 by ring]
    rw [show μ {ω | |medianOfMeans (momBlocks η) (fun r => Y r ω) -
      ∫ x, Y r0 x ∂μ| ≤ 0} = 1 by simpa [k] using hfull]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · have hprime := medianOfMeans_deviation_measurable μ Y' r0 η σ hη hσpos hY'meas
      hY'ind hY'Lp hY'means hY'var hn
    have hevents : {ω | |medianOfMeans (momBlocks η) (fun r => Y r ω) -
        ∫ x, Y r0 x ∂μ| ≤ 8 * σ * Real.sqrt (Real.log (2 / η) / n)} =ᵐ[μ]
        {ω | |medianOfMeans (momBlocks η) (fun r => Y' r ω) -
        ∫ x, Y' r0 x ∂μ| ≤ 8 * σ * Real.sqrt (Real.log (2 / η) / n)} := by
      filter_upwards [hall] with ω hω
      have hfun : (fun r => Y r ω) = (fun r => Y' r ω) := funext (hω)
      change (|medianOfMeans (momBlocks η) (fun r => Y r ω) -
        ∫ x, Y r0 x ∂μ| ≤ 8 * σ * Real.sqrt (Real.log (2 / η) / n)) =
        (|medianOfMeans (momBlocks η) (fun r => Y' r ω) -
        ∫ x, Y' r0 x ∂μ| ≤ 8 * σ * Real.sqrt (Real.log (2 / η) / n))
      rw [hfun, hcenter]
    rw [measure_congr hevents]
    exact hprime

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

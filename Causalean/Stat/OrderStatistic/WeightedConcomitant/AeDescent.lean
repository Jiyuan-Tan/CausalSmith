module
public import Causalean.Stat.OrderStatistic.CDFTransport
public import Mathlib.Probability.Kernel.Disintegration.Integral

/-!
# Almost-everywhere descent through a marginal and a continuous CDF

These two measure-transport facts isolate the descent of an equality of
possibly nonmeasurable versions.  The target equality itself must be proved
almost everywhere; no global measurability of either version is assumed.
-/

public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open Causalean.Stat.OrderStatistic

noncomputable section

/-- For a probability law on real pairs, a set of first-coordinate values
whose full inverse image is null is itself null under the first marginal. -/
theorem fst_null_of_preimage_null (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ] (s : Set ℝ)
    (hs : μ (Prod.fst ⁻¹' s) = 0) : (μ.map Prod.fst) s = 0 := by
  obtain ⟨t, hst, htm, ht0⟩ := exists_measurable_superset_of_null hs
  let u : Set ℝ := {x | μ.condKernel x {y | (x, y) ∈ t} ≠ 0}
  have hF : Measurable (fun x => μ.condKernel x {y | (x, y) ∈ t}) :=
    ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := μ.condKernel) htm
  have hu : MeasurableSet u :=
    (measurableSet_singleton (0 : ENNReal)).compl.preimage hF
  have hsu : s ⊆ u := by
    intro x hx
    have hf : {y : ℝ | (x, y) ∈ t} = Set.univ := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact hst hx
    simp only [u, Set.mem_ofPred_eq, hf]
    simp
  have hu0 : μ.fst u = 0 := by
    have hi : (∫⁻ x, μ.condKernel x {y | (x, y) ∈ t} ∂μ.fst) = 0 := by
      rw [μ.lintegral_condKernel_mem htm, ht0]
    have hae := (lintegral_eq_zero_iff hF).mp hi
    exact (ae_iff).mp (hae.mono fun x hx => by
      change μ.condKernel x {y | (x, y) ∈ t} = 0 at hx
      exact hx)
  apply le_antisymm _ zero_le
  calc
    (μ.map Prod.fst) s ≤ (μ.map Prod.fst) u := measure_mono hsu
    _ = μ.fst u := rfl
    _ = 0 := hu0

/-- If two real functions of the first coordinate agree almost surely under a
probability law on real pairs, then they agree almost surely under its first marginal. -/
theorem ae_eq_of_comp_fst (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (f g : ℝ → ℝ)
    (h : (fun p : ℝ × ℝ => f p.1) =ᵐ[μ] (fun p => g p.1)) :
    f =ᵐ[μ.map Prod.fst] g := by
  apply (ae_iff).2
  exact fst_null_of_preimage_null μ {t | f t ≠ g t} (by
    simpa only [Set.preimage_setOf_eq, ne_eq] using (ae_iff).mp h)

/-- A [real probability law](hyp:ν) with [a continuous CDF](hyp:hcont) carries
[two real functions](hyp:f,g) that [agree after CDF composition](hyp:h) to
[agreement under the unit-uniform law](goal). -/
theorem ae_eq_of_comp_continuous_cdf (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (hcont : Continuous (fun t => ProbabilityTheory.cdf ν t))
    (f g : ℝ → ℝ)
    (h : (fun t => f (ProbabilityTheory.cdf ν t)) =ᵐ[ν]
      (fun t => g (ProbabilityTheory.cdf ν t))) :
    f =ᵐ[uniform01] g := by
  let ρ : Measure ℝ := Causalean.Stat.unifOI
  change (∀ᵐ t ∂ν, f (ProbabilityTheory.cdf ν t) = g (ProbabilityTheory.cdf ν t)) at h
  have hq : (fun u => f (ProbabilityTheory.cdf ν (Causalean.Stat.quantile ν u)))
      =ᵐ[ρ] (fun u => g (ProbabilityTheory.cdf ν (Causalean.Stat.quantile ν u))) := by
    have h' := ae_of_ae_map (Causalean.Stat.aemeasurable_quantile_unifOI ν)
      (p := fun t => f (ProbabilityTheory.cdf ν t) = g (ProbabilityTheory.cdf ν t))
      (by simpa only [Causalean.Stat.quantile_map_uniform] using h)
    change (∀ᵐ u ∂ρ, f (ProbabilityTheory.cdf ν (Causalean.Stat.quantile ν u)) =
      g (ProbabilityTheory.cdf ν (Causalean.Stat.quantile ν u)))
    exact h'
  have hc : (fun u => ProbabilityTheory.cdf ν (Causalean.Stat.quantile ν u))
      =ᵐ[ρ] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact Causalean.Stat.cdf_quantile_eq ν hu.1 hu.2 hcont.continuousAt
  have hfg : f =ᵐ[ρ] g := by
    filter_upwards [hq, hc] with u heq hid
    simpa only [id_eq, hid] using heq
  change f =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] g
  rw [← restrict_Ioo_eq_restrict_Icc]
  exact hfg

end
end Causalean.Stat.OrderStatistic.WeightedConcomitant

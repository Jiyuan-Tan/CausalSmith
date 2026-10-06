module
public import Causalean.Mathlib.Probability.StdNormalCDF
public import Causalean.Stat.Coupling.Monotone.ProductLoss.PIT
public import Causalean.Stat.OrderStatistic.Basic
public import Causalean.Stat.Quantile.CdfConvergence

/-!
# Continuous CDF transport and interval mass

These lemmas separate continuity, the probability-integral transform, and the
interval-mass identity used for density-envelope comparisons.
-/

public section

namespace Causalean.Stat.OrderStatistic

open MeasureTheory

noncomputable section

/-- Given [a real probability law](hyp:μ), [a real density](hyp:p), and [an equality representing the law by that density](hyp:hμ), [its cumulative distribution function is continuous](goal). -/
theorem cdf_continuous_of_withDensity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : ℝ → ℝ)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (p x))) :
    Continuous (fun x => ProbabilityTheory.cdf μ x) := by
  haveI : NullSingletonClass μ := hμ ▸ inferInstance
  exact Causalean.Mathlib.cdf_continuous_of_noAtoms μ

/-- Given [a real probability law](hyp:μ) and [continuity of its cumulative distribution function](hyp:hcont), [that CDF pushes the law forward to the unit-uniform law](goal). -/
theorem cdf_pushforward_of_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hcont : Continuous (fun x => ProbabilityTheory.cdf μ x)) :
    μ.map (fun x => ProbabilityTheory.cdf μ x) = uniform01 := by
  let ν : Measure ℝ := Causalean.Stat.unifOI
  have hquant : ν.map (Causalean.Stat.quantile μ) = μ :=
    Causalean.Stat.quantile_map_uniform μ
  have hcomp : (fun x => ProbabilityTheory.cdf μ x) ∘
      Causalean.Stat.quantile μ =ᵐ[ν] id := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u hu
    exact Causalean.Stat.cdf_quantile_eq μ hu.1 hu.2 (hcont.continuousAt)
  calc
    μ.map (fun x => ProbabilityTheory.cdf μ x) =
        (ν.map (Causalean.Stat.quantile μ)).map
          (fun x => ProbabilityTheory.cdf μ x) := by rw [hquant]
    _ = ν.map ((fun x => ProbabilityTheory.cdf μ x) ∘
          Causalean.Stat.quantile μ) := by
          exact (AEMeasurable.map_map_of_aemeasurable
            hcont.measurable.aemeasurable
            (Causalean.Stat.aemeasurable_quantile_unifOI μ))
    _ = ν := by simpa using (Measure.map_congr hcomp)
    _ = uniform01 := by
      change volume.restrict (Set.Ioo (0 : ℝ) 1) =
        volume.restrict (Set.Icc (0 : ℝ) 1)
      exact restrict_Ioo_eq_restrict_Icc

/-- Given [a real probability law](hyp:μ) and [ordered endpoints](hyp:hxy), [its CDF increment equals the interval's real-valued probability mass](goal). -/
theorem cdf_increment_eq_interval_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {x y : ℝ} (hxy : x ≤ y) :
    ProbabilityTheory.cdf μ y - ProbabilityTheory.cdf μ x =
      μ.real (Set.Ioc x y) := by
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
  have hdisj : Disjoint (Set.Iic x) (Set.Ioc x y) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact (not_lt_of_ge hz) hz'.1
  have hunion : Set.Iic x ∪ Set.Ioc x y = Set.Iic y := by
    ext z
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro (hz | ⟨_, hz⟩)
      · exact hz.trans hxy
      · exact hz
    · intro hz
      exact le_or_gt z x |>.elim (fun h => Or.inl h) (fun h => Or.inr ⟨h, hz⟩)
  have hadd := measureReal_union hdisj measurableSet_Ioc
    (μ := μ) (s₁ := Set.Iic x) (s₂ := Set.Ioc x y)
  rw [hunion] at hadd
  linarith

/-- Given [a sample size](hyp:n), [a monotone real transformation](hyp:f,hf), and [a real tuple](hyp:x), [sorting after transformation equals transforming the sorted tuple](goal). -/
theorem sortedSample_map_monotone (n : ℕ) (f : ℝ → ℝ) (hf : Monotone f)
    (x : Fin n → ℝ) :
    sortedSample n (fun i => f (x i)) = fun i => f (sortedSample n x i) := by
  unfold sortedSample
  have hmono : Monotone ((fun j : Fin n => f (x j)) ∘ Tuple.sort x) :=
    hf.comp (Tuple.monotone_sort x)
  exact ((Tuple.comp_sort_eq_comp_iff_monotone
    (f := fun j : Fin n => f (x j)) (σ := Tuple.sort x)).2 hmono).symm

end
end Causalean.Stat.OrderStatistic

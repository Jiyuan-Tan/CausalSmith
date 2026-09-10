import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.FiniteBandCoverage

/-! # Finite-sample simultaneous endpoint band -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw

universe u

/-- Conditional on the two registered concentration gates, the propagated
piecewise endpoint band has simultaneous finite-sample coverage.  For the specified model objects, [the stated conditions](hyp:hIID,hFactor,hHoeffding,hDkw,hPos,hAlpha), [the stated mathematical relationship holds](goal).
-/
-- @node: thm:finite-sample-simultaneous-band
theorem honestBand_simultaneous_coverage
    {Omega : Type u} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] (n : ℕ) (a : Bool) (alpha e : ℝ)
    (nu : Measure (Bool × ℝ))
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (Z : ℕ → Omega → Bool × ℝ)
    (hIID : IidObservationalSampling n Z mu nu)
    (hFactor : ∀ B : Set ℝ, MeasurableSet B →
      nu {z | z.1 = a ∧ z.2 ∈ B} = ENNReal.ofReal e * P B)
    (hHoeffding : HoeffdingBoundedMean.{u})
    (hDkw : DkwMassartCdfBand)
    (hPos : StrictPositivity e) (hAlpha : MiscoverageLevel alpha) :
    mu {ω | ∀ y : ℝ,
      cdfEndpoints (endpointPropensity e (Or.inl hPos)) (cdfProbability P y) ∈
      honestBand Z a n alpha ω y} ≥
      ENNReal.ofReal (1 - alpha) := by
  by_cases hn : n = 0
  · subst n
    have hset : {ω | ∀ y : ℝ,
        cdfEndpoints (endpointPropensity e (Or.inl hPos)) (cdfProbability P y) ∈
          honestBand Z a 0 alpha ω y} = Set.univ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro y
      rw [honestBand]
      simp only [armCount, Finset.univ_eq_empty, Finset.sum_empty, if_pos rfl]
      exact cdfEndpoints_mem_unitSquare _ _
    rw [hset, measure_univ]
    exact ENNReal.ofReal_le_one.mpr (by linarith [hAlpha.1])
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    letI : IsProbabilityMeasure nu := hIID.2.1
    let S : Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw.MarkedIID
        Omega n mu nu :=
      { Z := fun i => Z i
        measurable := hIID.2.2.1
        indep := hIID.2.2.2.1
        law := hIID.2.2.2.2 }
    have hfac : BooleanMarkFactorization nu a (ENNReal.ofReal e) P :=
      { positive := ENNReal.ofReal_ne_zero_iff.mpr hPos.1
        joint := hFactor }
    let E : Set Omega := {ω | |empiricalArmPropensity (fun i : Fin n => Z i ω) a - e| >
      Real.sqrt (Real.log (4 / alpha) / (2 * n))}
    let F : Set Omega := selectedCDFBadEvent (fun i : Fin n => Z i) a P (dkwRadius alpha)
    let C : Set Omega := {ω | ∀ y : ℝ,
      cdfEndpoints (endpointPropensity e (Or.inl hPos)) (cdfProbability P y) ∈
        honestBand Z a n alpha ω y}
    have hE : mu E ≤ ENNReal.ofReal (alpha / 2) := by
      exact hoeffdingGate_empiricalArmPropensity mu n hnpos a alpha e nu P Z hIID
        hFactor hHoeffding hPos hAlpha
    have hF : mu F ≤ ENNReal.ofReal (alpha / 2) := by
      apply conditionalMarkedSubsample_dkwRadius S a (ENNReal.ofReal e) P hfac alpha
        hAlpha.1 hAlpha.2.le
      exact dkwGate_fixedCDFBadSet hDkw P alpha hAlpha
    have hcover : Set.univ ⊆ C ∪ (E ∪ F) := by
      intro omega _
      by_cases he : omega ∈ E
      · exact Or.inr (Or.inl he)
      by_cases hf : omega ∈ F
      · exact Or.inr (Or.inr hf)
      · apply Or.inl
        apply honestBand_contains_of_good_events n a alpha e P Z omega hPos
        · exact le_of_not_gt he
        · exact hf
    have hone : (1 : ℝ≥0∞) ≤ mu C + (mu E + mu F) := by
      calc
        1 = mu Set.univ := measure_univ.symm
        _ ≤ mu (C ∪ (E ∪ F)) := measure_mono hcover
        _ ≤ mu C + mu (E ∪ F) := measure_union_le _ _
        _ ≤ mu C + (mu E + mu F) := by
          gcongr
          exact measure_union_le _ _
    have hbad : mu E + mu F ≤ ENNReal.ofReal alpha := by
      calc
        mu E + mu F ≤ ENNReal.ofReal (alpha / 2) + ENNReal.ofReal (alpha / 2) :=
          add_le_add hE hF
        _ = ENNReal.ofReal alpha := by
          rw [← ENNReal.ofReal_add (div_nonneg hAlpha.1.le (by norm_num))
            (div_nonneg hAlpha.1.le (by norm_num))]
          congr 1
          ring
    have hone' : (1 : ℝ≥0∞) ≤ mu C + ENNReal.ofReal alpha :=
      hone.trans (by gcongr)
    have hmain : (1 : ℝ≥0∞) - ENNReal.ofReal alpha ≤ mu C :=
      tsub_le_iff_right.mpr (by simpa [add_comm] using hone')
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hAlpha.1.le] at hmain
    exact hmain

end CausalSmith.SCM.PropensityLvSharpnessFrontier

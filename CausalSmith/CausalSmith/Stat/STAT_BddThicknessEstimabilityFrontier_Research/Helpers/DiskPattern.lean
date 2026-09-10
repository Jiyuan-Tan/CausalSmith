import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.Estimator
import Causalean.Stat.Concentration.Covering.VCCovering
import Causalean.Stat.Concentration.Covering.EuclideanRadialPolynomial.Geometry
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Conditional sub-Gaussian disk-pattern control -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

/-- Finite index patterns cut out by side-specific fixed-radius disks. -/
noncomputable def diskPatterns {n : ℕ} (P : BoundaryLaw) (scores : Fin n → Score) (h0 : ℝ) :
    Set (Finset (Fin n)) := by
  classical
  exact {S | S.Nonempty ∧ ∃ t : Fin 2, ∃ x ∈ assignmentBoundary P, ∃ h ∈ dyadicGrid n h0,
    S = Finset.univ.filter (fun i => scores i ∈ P.region t ∧ dist (scores i) x ≤ h)}

/-- The conditional product law of the outcomes given a score vector. -/
noncomputable def conditionalOutcomeProduct {n : ℕ} (R : Kernel Score ℝ)
    (_hR : IsMarkovKernel R) (scores : Fin n → Score) : Measure (Fin n → ℝ) := by
  letI := _hR
  exact Measure.pi fun i => R (scores i)

/-- The product score law. -/
noncomputable def scoreSampleLaw (P : BoundaryLaw) (n : ℕ) : Measure (Fin n → Score) := by
  letI := P.isProbability_score
  exact Measure.pi fun _ : Fin n => P.scoreLaw

/-- The maximum normalized residual sum over all nonempty disk patterns. -/
noncomputable def normalizedDiskResidualMax {n : ℕ} (P : BoundaryLaw)
    (scores : Fin n → Score) (outcomes : Fin n → ℝ) (σ h0 : ℝ) : ℝ≥0∞ := by
  classical
  exact ⨆ S : Finset (Fin n), ⨆ (_hS : S ∈ diskPatterns P scores h0), ENNReal.ofReal
      (|∑ i ∈ S, (outcomes i - P.sideRegression
        (if scores i ∈ P.region 1 then 1 else 0) (scores i))| /
          (σ * Real.sqrt S.card))

-- @node: subGaussian_lintegral_abs_le
/-- A centered sub-Gaussian MGF with scale `σ` has first absolute moment at
most `σ * sqrt (2π)`. -/
lemma subGaussian_lintegral_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hX : HasSubgaussianMGF X ⟨σ ^ 2, sq_nonneg σ⟩ μ) :
    (∫⁻ ω, ENNReal.ofReal |X ω| ∂μ) ≤
      ENNReal.ofReal (σ * Real.sqrt (2 * Real.pi)) := by
  have habs_int : Integrable (fun ω => |X ω|) μ := hX.integrable.abs
  have hgauss : IntegrableOn
      (fun t : ℝ => 2 * Real.exp (-(1 / (2 * σ ^ 2)) * t ^ 2)) (Ioi 0) := by
    exact ((integrableOn_Ioi_exp_neg_mul_sq_iff.mpr (by positivity)).const_mul 2)
  have htail : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      μ.real {ω | t < |X ω|} ≤ 2 * Real.exp (-(1 / (2 * σ ^ 2)) * t ^ 2) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have hsubset : {ω | t < |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
      intro ω hω
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      change t < |X ω| at hω
      rw [lt_abs] at hω
      exact hω.imp LT.lt.le LT.lt.le
    calc
      μ.real {ω | t < |X ω|}
          ≤ μ.real ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) := measureReal_mono hsubset
      _ ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | t ≤ -X ω} :=
        MeasureTheory.measureReal_union_le _ _
      _ ≤ Real.exp (-t ^ 2 / (2 * σ ^ 2)) + Real.exp (-t ^ 2 / (2 * σ ^ 2)) := by
        have h := add_le_add (hX.measure_ge_le ht0) (hX.neg.measure_ge_le ht0)
        change μ.real {ω | t ≤ X ω} + μ.real {ω | t ≤ -X ω} ≤
          Real.exp (-t ^ 2 / (2 * σ ^ 2)) + Real.exp (-t ^ 2 / (2 * σ ^ 2)) at h
        exact h
      _ = 2 * Real.exp (-(1 / (2 * σ ^ 2)) * t ^ 2) := by
        field_simp
        ring
  rw [lintegral_eq_lintegral_meas_lt μ
    (Filter.Eventually.of_forall fun _ => abs_nonneg _) habs_int.aemeasurable]
  calc
    ∫⁻ t in Ioi (0 : ℝ), μ {ω | t < |X ω|}
        ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
            (2 * Real.exp (-(1 / (2 * σ ^ 2)) * t ^ 2)) := by
          apply lintegral_mono_ae
          filter_upwards [htail] with t ht
          apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2
          simpa [Measure.real] using ht
    _ = ENNReal.ofReal
        (∫ t in Ioi (0 : ℝ), 2 * Real.exp (-(1 / (2 * σ ^ 2)) * t ^ 2)) := by
          symm
          exact ofReal_integral_eq_lintegral_ofReal hgauss
            (Filter.Eventually.of_forall fun _ => by positivity)
    _ = ENNReal.ofReal (2 * (Real.sqrt (Real.pi / (1 / (2 * σ ^ 2))) / 2)) := by
      congr 1
      rw [MeasureTheory.integral_const_mul, integral_gaussian_Ioi]
    _ = ENNReal.ofReal (σ * Real.sqrt (2 * Real.pi)) := by
      congr 1
      rw [show Real.pi / (1 / (2 * σ ^ 2)) = σ ^ 2 * (2 * Real.pi) by
        field_simp]
      rw [Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq_eq_abs, abs_of_pos hσ]
      ring

-- @node: lem:conditional-sub-gaussian-regression-moments
/-- The kernel assumption yields centered conditional moments, a two-sided tail,
and the explicit first absolute moment bound off each side-null set. -/
lemma conditional_subGaussian_regression_moments (P : BoundaryLaw) (σ : ℝ)
    (herrors : CenteredSubGaussianKernel P σ) :
    0 < σ ∧ ∃ R : Kernel Score ℝ,
      IsMarkovKernel R ∧ (scoreOutcomeLaw P).IsCondKernel R ∧
      ∀ t : Fin 2, ∃ N : Set Score,
      restrictedScore P t N = 0 ∧ ∀ z ∈ sideSupport P t \ N,
        Integrable (fun y : ℝ => y - P.sideRegression t z) (R z) ∧
        (∫ y, y - P.sideRegression t z ∂R z) = 0 ∧
        (∫ y, y ∂R z) = P.sideRegression t z ∧
        (∀ a : ℝ, (∫⁻ y, ENNReal.ofReal (Real.exp (a * (y - P.sideRegression t z))) ∂R z) ≤
          ENNReal.ofReal (Real.exp (σ ^ 2 * a ^ 2 / 2))) ∧
        (∫⁻ y, ENNReal.ofReal |y - P.sideRegression t z| ∂R z) ≤
          ENNReal.ofReal (σ * Real.sqrt (2 * Real.pi)) := by
  rcases herrors with ⟨hσ, R, hR, hcond, hkernel⟩
  refine ⟨hσ, R, hR, hcond, ?_⟩
  intro t
  rcases hkernel t with ⟨N, hN, hNprop⟩
  refine ⟨N, hN, ?_⟩
  intro z hz
  rcases hNprop z hz with ⟨hint, hcenter, hmean, hmgf⟩
  refine ⟨hint, hcenter, hmean, hmgf, ?_⟩
  letI : IsMarkovKernel R := hR
  letI : IsProbabilityMeasure (R z) := IsMarkovKernel.isProbabilityMeasure z
  let X : ℝ → ℝ := fun y => y - P.sideRegression t z
  have hexp (a : ℝ) : Integrable (fun y => Real.exp (a * X y)) (R z) := by
    constructor
    · fun_prop
    · rw [hasFiniteIntegral_iff_ofReal
          (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)]
      exact (hmgf a).trans_lt ENNReal.ofReal_lt_top
  have hsub : HasSubgaussianMGF X ⟨σ ^ 2, sq_nonneg σ⟩ (R z) := by
    refine ⟨hexp, ?_⟩
    intro a
    rw [mgf, integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _) (hexp a).aestronglyMeasurable]
    change (∫⁻ y, ENNReal.ofReal (Real.exp (a * X y)) ∂R z).toReal ≤
      Real.exp (σ ^ 2 * a ^ 2 / 2)
    have hm := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmgf a)
    simpa [X, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hm
  simpa [X] using subGaussian_lintegral_abs_le (R z) X σ hσ hsub

-- @env: S2
variable {n : ℕ}

-- @node: lem:disk-pattern-sub-gaussian-control
/-- Fixed-radius planar disk traces have cubic Sauer growth, and their
normalized residual sums satisfy the conditional union bound and expectation
bound used by all upper results. -/
lemma diskPattern_subGaussian_control (P : BoundaryLaw)
    (sampleMeasure : Measure (Sample n)) (σ h0 : ℝ)
    (hiid : IidSampling n P sampleMeasure)
    (herrors : CenteredSubGaussianKernel P σ)
    (hpartition : P.region 0 = (P.region 1)ᶜ) :
    ∃ R : Kernel Score ℝ, ∃ hR : IsMarkovKernel R,
      (scoreOutcomeLaw P).IsCondKernel R ∧
      (∀ scores : Fin n → Score, (diskPatterns P scores h0).encard ≤
        2 * (dyadicGrid n h0).card * ∑ j ∈ Finset.range 4, Nat.choose n j) ∧
      ∀ᵐ scores ∂scoreSampleLaw P n,
        (∀ z > 0,
          conditionalOutcomeProduct R hR scores
              {ys | z < (normalizedDiskResidualMax P scores ys σ h0).toReal} ≤
            ENNReal.ofReal (2 * ((diskPatterns P scores h0).encard.getD 0 : ℝ) *
              Real.exp (-(z ^ 2) / 2))) ∧
        (∫⁻ ys, normalizedDiskResidualMax P scores ys σ h0
            ∂conditionalOutcomeProduct R hR scores) ≤
          ENNReal.ofReal (Real.sqrt (2 * Real.log
            (2 * max 1 ((diskPatterns P scores h0).encard.getD 0 : ℝ))) + 1) := by sorry

end CausalSmith.Stat.BddThicknessEstimabilityFrontier

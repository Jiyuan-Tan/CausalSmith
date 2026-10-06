module
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.FuzzyCertificate

/-!
# Risk transfer from a finite paired fuzzy certificate

This module turns a finite two-prior testing certificate into a lower bound
for the exact real-valued minimax squared risk of the paired experiment.
-/

public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Given [a sample size and alphabet size](hyp:n,k) and [a valid finite fuzzy certificate](hyp:W), [the certificate's squared target separation lower-bounds the exact minimax squared risk](goal). -/
theorem FuzzyCertificate.minimax_lower {n k : ℕ}
    (W : FuzzyCertificate n k) :
    11 * W.delta ^ 2 / 512 ≤ twoSampleL1MinimaxRisk n k := by
  classical
  let Θ := Fin W.m × Bool
  let X := (Fin n → Fin k) × (Fin n → Fin k)
  let model : Θ → ProbabilitySimplex k × ProbabilitySimplex k :=
    fun θ => if θ.2 then W.θ₁ θ.1 else W.θ₀ θ.1
  let K : Kernel Θ X := Kernel.ofFunOfCountable (fun θ => twoSampleLaw n (model θ))
  let target : Θ → ℝ := fun θ => simplexL1 (model θ).1 (model θ).2
  let π₀ : Measure Θ := ∑ i : Fin W.m, W.w₀ i • Measure.dirac (i, false)
  let π₁ : Measure Θ := ∑ i : Fin W.m, W.w₁ i • Measure.dirac (i, true)
  have hp₀ : IsProbabilityMeasure π₀ := by
    apply isProbabilityMeasure_iff.mpr
    simp [π₀, Measure.coe_finsetSum, W.w₀_sum]
  have hp₁ : IsProbabilityMeasure π₁ := by
    apply isProbabilityMeasure_iff.mpr
    simp [π₁, Measure.coe_finsetSum, W.w₁_sum]
  letI : IsProbabilityMeasure π₀ := hp₀
  letI : IsProbabilityMeasure π₁ := hp₁
  have hK : ∀ θ, IsProbabilityMeasure (K θ) := by
    intro θ
    change IsProbabilityMeasure (twoSampleLaw n (model θ))
    infer_instance
  have htarget : Measurable target := measurable_of_finite target
  have hmass₀ (A : Set Θ) :
      π₀ A = ∑ i, if (i, false) ∈ A then W.w₀ i else 0 := by
    simp [π₀, Measure.coe_finsetSum, Measure.dirac_apply, Set.indicator, smul_eq_mul]
  have hmass₁ (A : Set Θ) :
      π₁ A = ∑ i, if (i, true) ∈ A then W.w₁ i else 0 := by
    simp [π₁, Measure.coe_finsetSum, Measure.dirac_apply, Set.indicator, smul_eq_mul]
  have hbad₀ : π₀.real {θ | W.delta / 4 < |target θ - W.center₀|} ≤ 1 / 8 := by
    rw [Measure.real, hmass₀]
    simp only [target, model]
    exact (ENNReal.toReal_mono (by norm_num) W.bad₀).trans_eq (by norm_num)
  have hbad₁ : π₁.real {θ | W.delta / 4 < |target θ - W.center₁|} ≤ 1 / 8 := by
    rw [Measure.real, hmass₁]
    simp only [target, model]
    exact (ENNReal.toReal_mono (by norm_num) W.bad₁).trans_eq (by norm_num)
  have hpredict₀ :
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive π₀ K =
        Causalean.Stat.mixture W.w₀ (fun i => twoSampleLaw n (W.θ₀ i)) := by
    ext A hA
    rw [Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_apply π₀ K hA]
    simp only [π₀, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
      Causalean.Stat.mixture_apply, smul_eq_mul]
    rfl
  have hpredict₁ :
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive π₁ K =
        Causalean.Stat.mixture W.w₁ (fun i => twoSampleLaw n (W.θ₁ i)) := by
    ext A hA
    rw [Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_apply π₁ K hA]
    simp only [π₁, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
      Causalean.Stat.mixture_apply, smul_eq_mul]
    rfl
  have htv : Causalean.Stat.tvDist
      (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive π₀ K)
      (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive π₁ K) ≤ 1 / 16 := by
    rw [hpredict₀, hpredict₁]
    exact W.predictive_close
  let c : ℝ := 11 * W.delta ^ 2 / 512
  have hbdd (est : TwoSampleEstimator n k) :
      BddAbove (Set.range (twoSampleL1Risk n est)) := by
    let C : ℝ := ∑ z : X, (|est.1 z| + 2)^2
    refine ⟨C, ?_⟩
    rintro _ ⟨RS, rfl⟩
    have hpoint (z : X) : (est.1 z - simplexL1 RS.1 RS.2)^2 ≤ C := by
      have hval := simplexL1_nonneg_le_two RS.1 RS.2
      have habs : |est.1 z - simplexL1 RS.1 RS.2| ≤ |est.1 z| + 2 := by
        calc
          _ ≤ |est.1 z| + |simplexL1 RS.1 RS.2| := abs_sub _ _
          _ ≤ |est.1 z| + 2 := by rw [abs_of_nonneg hval.1]; linarith
      have hsq : (est.1 z - simplexL1 RS.1 RS.2)^2 ≤ (|est.1 z| + 2)^2 := by
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 habs
      exact hsq.trans
        (Finset.single_le_sum (fun x _ => sq_nonneg (|est.1 x| + 2)) (Finset.mem_univ z))
    change (∫ z, (est.1 z - simplexL1 RS.1 RS.2)^2 ∂twoSampleLaw n RS) ≤ C
    calc
      _ ≤ ∫ _z, C ∂twoSampleLaw n RS :=
        integral_mono_ae Integrable.of_finite (integrable_const C) (ae_of_all _ hpoint)
      _ = C := by simp
  have hrisk (est : TwoSampleEstimator n k) (θ : Θ) :
      Causalean.Stat.Minimax.FuzzyHypotheses.squaredRisk K target est.1 θ =
        ENNReal.ofReal (twoSampleL1Risk n est (model θ)) := by
    unfold Causalean.Stat.Minimax.FuzzyHypotheses.squaredRisk twoSampleL1Risk
    change (∫⁻ z, ENNReal.ofReal ((est.1 z - target θ)^2) ∂twoSampleLaw n (model θ)) =
      ENNReal.ofReal (∫ z, (est.1 z - target θ)^2 ∂twoSampleLaw n (model θ))
    exact (ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
      (ae_of_all _ fun z => sq_nonneg _)).symm
  have hall (est : TwoSampleEstimator n k) :
      c ≤ Causalean.Stat.worstCaseRiskReal (twoSampleL1Risk n) est := by
    have hbound :=
      Causalean.Stat.Minimax.FuzzyHypotheses.twoFuzzyHypotheses_worstCase_lower_standard
      π₀ π₁ K target hK est.1 est.2 htarget W.center₀ W.center₁ W.delta
      W.delta_pos W.center_sep hbad₀ hbad₁ htv
    have hsup : Causalean.Stat.Minimax.FuzzyHypotheses.worstCaseSquaredRisk K target est.1 ≤
        ENNReal.ofReal (Causalean.Stat.worstCaseRiskReal (twoSampleL1Risk n) est) := by
      unfold Causalean.Stat.Minimax.FuzzyHypotheses.worstCaseSquaredRisk
      apply iSup_le
      intro θ
      rw [hrisk]
      exact ENNReal.ofReal_le_ofReal
        (Causalean.Stat.le_worstCaseRisk (hbdd est) (model θ))
    have hnonneg : 0 ≤ Causalean.Stat.worstCaseRiskReal (twoSampleL1Risk n) est := by
      have hθ := Causalean.Stat.le_worstCaseRisk (hbdd est) (W.θ₀ ⟨0, W.m_pos⟩)
      have hr : 0 ≤ twoSampleL1Risk n est (W.θ₀ ⟨0, W.m_pos⟩) := by
        unfold twoSampleL1Risk
        exact integral_nonneg fun z => sq_nonneg _
      exact hr.trans hθ
    exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mp (hbound.trans hsup)
  haveI : Nonempty (TwoSampleEstimator n k) :=
    ⟨⟨fun _ => 0, measurable_const⟩⟩
  exact Causalean.Stat.le_minimaxValue hall

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1

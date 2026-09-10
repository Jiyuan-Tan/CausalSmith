import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.TEqualPropensityL1Reduction
import Causalean.Stat.Minimax.MinimaxRisk

/-! A reusable two-model testing lower bound for the observed minimax problem. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory

/-- Two observed models separated by `2s` in target value and at total variation at
most one half force minimax squared risk at least `s²/4`. This uses [the stated support condition holds](hyp:hs), and [the two target values have the stated separation](hyp:hsep), and [the two experiments have the stated total-variation bound](hyp:htv). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma minimaxRisk_ge_two_model_tv {n d : ℕ} {epsilon s : ℝ}
    (P0 P1 : ModelLaw d epsilon) (hs : 0 ≤ s)
    (hsep : 2 * s ≤
      |observedOptimalValue P0.1 P0.2 - observedOptimalValue P1.1 P1.2|)
    (htv : Causalean.Stat.tvDist (productLaw P0.1 n) (productLaw P1.1 n) ≤ 1 / 2) :
    s ^ 2 / 4 ≤ minimaxRisk n d epsilon := by
  classical
  letI : Nonempty (Estimator n d) := ⟨⟨fun _ => 0, measurable_const⟩⟩
  unfold minimaxRisk
  apply Causalean.Stat.le_minimaxValue
  intro est
  let theta0 := observedOptimalValue P0.1 P0.2
  let theta1 := observedOptimalValue P1.1 P1.2
  have htest := Causalean.Stat.two_point_lower_bound_of_tvDist_le
    (P₀ := productLaw P0.1 n) (P₁ := productLaw P1.1 n) est.2
    (θ₀ := theta0) (θ₁ := theta1) (s := s) (c := (1 / 2 : ℝ))
    (by simpa [theta0, theta1] using hsep) htv
  have hprob : 1 / 4 ≤ max
      ((productLaw P0.1 n).real {z | s ≤ |est.1 z - theta0|})
      ((productLaw P1.1 n).real {z | s ≤ |est.1 z - theta1|}) := by
    convert htest using 1 <;> norm_num
  have hrisk (P : ModelLaw d epsilon) (theta : ℝ)
      (htheta : theta = observedOptimalValue P.1 P.2) :
      s ^ 2 * (productLaw P.1 n).real {z | s ≤ |est.1 z - theta|} ≤
        observedRisk epsilon n est P := by
    subst theta
    unfold observedRisk Causalean.Stat.sqRisk
    let f : (Fin n → Obs d) → ℝ := fun z =>
      (est.1 z - observedOptimalValue P.1 P.2) ^ 2
    have hf_nonneg : 0 ≤ f := fun z => sq_nonneg _
    have hf_int : Integrable f (productLaw P.1 n) := Integrable.of_finite
    have hmeas : MeasurableSet
        {z | s ^ 2 ≤ f z} := by
      exact measurableSet_le measurable_const
        ((est.2.sub measurable_const).pow_const 2)
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (μ := productLaw P.1 n) (f := f) (ae_of_all _ hf_nonneg) hf_int (s ^ 2)
    have hevent : {z | s ≤ |est.1 z - observedOptimalValue P.1 P.2|} =
        {z | s ^ 2 ≤ f z} := by
      ext z
      simp only [Set.mem_setOf_eq, f]
      simpa [abs_of_nonneg hs, sq_abs] using
        (sq_le_sq₀ hs
          (abs_nonneg (est.1 z - observedOptimalValue P.1 P.2))).symm
    rw [hevent]
    simpa [Measure.real, hmeas] using hmarkov
  have hrisk0 : s ^ 2 *
      (productLaw P0.1 n).real {z | s ≤ |est.1 z - theta0|} ≤
      observedRisk epsilon n est P0 := hrisk P0 theta0 rfl
  have hrisk1 : s ^ 2 *
      (productLaw P1.1 n).real {z | s ≤ |est.1 z - theta1|} ≤
      observedRisk epsilon n est P1 := hrisk P1 theta1 rfl
  have hmax : s ^ 2 / 4 ≤
      max (observedRisk epsilon n est P0) (observedRisk epsilon n est P1) := by
    calc
      s ^ 2 / 4 = s ^ 2 * (1 / 4) := by ring
      _ ≤ s ^ 2 * max
          ((productLaw P0.1 n).real {z | s ≤ |est.1 z - theta0|})
          ((productLaw P1.1 n).real {z | s ≤ |est.1 z - theta1|}) := by
        gcongr
      _ = max
          (s ^ 2 * (productLaw P0.1 n).real {z | s ≤ |est.1 z - theta0|})
          (s ^ 2 * (productLaw P1.1 n).real {z | s ≤ |est.1 z - theta1|}) := by
        rw [mul_max_of_nonneg _ _ (sq_nonneg s)]
      _ ≤ max (observedRisk epsilon n est P0) (observedRisk epsilon n est P1) :=
        max_le_max hrisk0 hrisk1
  exact hmax.trans (max_le
    (Causalean.Stat.le_worstCaseRisk (observedRisk_bddAbove est) P0)
    (Causalean.Stat.le_worstCaseRisk (observedRisk_bddAbove est) P1))

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

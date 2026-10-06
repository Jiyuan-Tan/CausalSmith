module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.T_KnownRadiusMinimaxFrontier
public import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.ParametricLower

/-! A quantitative one-cell two-point converse for the radius-zero class.
The explicit constant in the existing finite-cell construction is retained so
it can also certify loss for unrestricted measurable estimators. -/

public section

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory Set
open scoped ENNReal

/-- The quantitative version of the proved one-cell parametric construction. -/
-- @node: endpoint_parametric_lower_quantitative
lemma endpoint_parametric_lower_quantitative :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → 1 ≤ M → 0 ≤ sigma → sigma ≤ 2 →
        (1 / 100 : ℝ) * M ^ 2 / n ≤ minimaxRisk n d epsilon M sigma := by
  intro epsilon he0 hehalf
  intro n d M sigma hn hd hM hs0 hs2
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let k : Fin d := Classical.arbitrary (Fin d)
  let delta : ℝ := (2 / 5) / Real.sqrt n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hdelta0 : 0 ≤ delta := by dsimp [delta]; positivity
  have hdeltasq : delta ^ 2 = 4 / (25 * (n : ℝ)) := by
    dsimp [delta]
    rw [div_pow, Real.sq_sqrt hnR.le]
    ring
  have hsqrt_one : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hdeltaU : delta ≤ 2 / 5 := by
    dsimp [delta]
    exact div_le_self (by norm_num) hsqrt_one
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let u0 : ℝ := M * ((1 / 2 : ℝ) - 1 / 2)
  let u1 : ℝ := M * ((1 / 2 : ℝ) + delta - 1 / 2)
  have hu0 : |u0| ≤ M / 2 := by dsimp [u0]; simp; positivity
  have hu1 : |u1| ≤ M / 2 := by
    have hdhalf : delta ≤ 1 / 2 := hdeltaU.trans (by norm_num)
    rw [show u1 = M * delta by dsimp [u1]; ring, abs_mul,
      abs_of_nonneg hdelta0, abs_of_nonneg hM0.le]
    nlinarith
  let P0 : ModelClass d epsilon M sigma :=
    testModelClass k epsilon M sigma u0 he0 hehalf hM hs0 hs2 hu0
  let P1 : ModelClass d epsilon M sigma :=
    testModelClass k epsilon M sigma u1 he0 hehalf hM hs0 hs2 hu1
  let hv0 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_null
    (C := Fin 1) (m₀ := (1 / 2 : ℝ)) (g₀ := (1 / 2 : ℝ)) (g₁ := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let hv1 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_pert
    (C := Fin 1) (m₀ := (1 / 2 : ℝ)) (g₀ := (1 / 2 : ℝ)) (g₁ := (1 / 2 : ℝ))
    (δ := delta) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hdelta0 (by linarith)
  have hreg : (n : ℝ) *
      ((1 / 2 : ℝ) * delta ^ 2 / ((1 / 2 : ℝ) * (1 - 1 / 2))) ≤ Real.log 2 := by
    rw [hdeltasq]
    have hlog : (8 / 25 : ℝ) ≤ Real.log 2 :=
      le_trans (by norm_num) (le_of_lt Real.log_two_gt_d9)
    convert hlog using 1 <;> field_simp <;> ring
  have htvSource : Causalean.Stat.tvDist
      (Causalean.Estimation.MinimaxATE.productLaw hv0 n)
      (Causalean.Estimation.MinimaxATE.productLaw hv1 n) ≤ 1 / 2 :=
    Causalean.Estimation.MinimaxATE.Parametric.tvDist_productLaw_le_half
      hv0 hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hreg
  have hmap0 : productLaw n P0.law =
      Measure.map (fun sample i => testScaleBinaryObs k M (sample i))
        (Causalean.Estimation.MinimaxATE.productLaw hv0 n) := by
    simpa [P0, u0, testModelClass] using
      (test_product_map_null (n := n) k hM0 hv0 hu0)
  have hmap1 : productLaw n P1.law =
      Measure.map (fun sample i => testScaleBinaryObs k M (sample i))
        (Causalean.Estimation.MinimaxATE.productLaw hv1 n) := by
    simpa [P1, u1, testModelClass] using
      (test_product_map_pert (n := n) k hM0 hv1 hu1)
  have htv : Causalean.Stat.tvDist (productLaw n P0.law) (productLaw n P1.law) ≤ 1 / 2 := by
    rw [hmap0, hmap1]
    exact (CausalSmith.Stat.DiscreteAteMinimaxLoggap.tvDist_map_le
      (Causalean.Estimation.MinimaxATE.productLaw hv0 n)
      (Causalean.Estimation.MinimaxATE.productLaw hv1 n)
      (fun sample i => testScaleBinaryObs k M (sample i)) (by fun_prop)).trans htvSource
  have htau0 : rawAteFormula P0.law = 0 := by
    simpa [P0, u0, testModelClass] using
      (testRealLaw_rawAte k (show 0 < M / 2 by positivity) hu0)
  have htau1 : rawAteFormula P1.law = M * delta := by
    have hraw := testRealLaw_rawAte k (show 0 < M / 2 by positivity) hu1
    simpa [P1, u1, testModelClass] using hraw
  have hlow := test_minimax_two_point P0 P1 hM
    (mul_nonneg hM0.le hdelta0) htau0 htau1 htv
  rw [show (M * delta) ^ 2 = M ^ 2 * delta ^ 2 by ring, hdeltasq] at hlow
  convert hlow using 1 <;> field_simp <;> ring


end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open scoped ENNReal

/-- Jointly exchangeable radius-zero laws form a subclass of the paper's
separately exchangeable radius-zero laws; every sample risk is unchanged. -/
-- @node: jointRadiusZero_minimax_le
lemma jointRadiusZero_minimax_le (n : ℕ) (M : ℝ) (hn : 3 ≤ n) (hM : 1 ≤ M) :
    DiscreteAteHeterogeneityFrontier.minimaxRisk n n (1 / 4) M 0 ≤
      knownRadiusMinimaxRisk n M 0 := by
  letI : Nonempty (DiscreteAteHeterogeneityFrontier.Estimator n n M) :=
    ⟨knownRadiusEstimatorAsEstimator n M 0 (by linarith)⟩
  apply ciInf_mono
  · refine ⟨0, ?_⟩
    rintro _ ⟨est, rfl⟩
    exact Real.iSup_nonneg (fun P => integral_nonneg (fun _ => sq_nonneg _))
  intro est
  apply Real.iSup_le _ (Real.iSup_nonneg
    (fun Q => integral_nonneg (fun _ => sq_nonneg _)))
  intro P
  let Q := KnownRadiusClass.ofModelClass hn P
  have hb : BddAbove (Set.range (fun Q : KnownRadiusClass n M 0 =>
      DiscreteAteHeterogeneityFrontier.mse Q.law est.1)) := by
    refine ⟨(2 * M) ^ 2, ?_⟩
    rintro _ ⟨Q, rfl⟩
    exact knownRadiusClass_mse_bound Q est
  exact le_ciSup hb Q

/-- The concrete two-point subclass gives a stronger numerical lower bound
than the constant required at the exact-homogeneity endpoint. -/
-- @node: radiusZero_minimax_lower_quantitative
lemma radiusZero_minimax_lower_quantitative (n : ℕ) (M : ℝ)
    (hn : 3 ≤ n) (hM : 1 ≤ M) :
    (1 / 100 : ℝ) * M ^ 2 / n ≤ knownRadiusMinimaxRisk n M 0 := by
  exact (DiscreteAteHeterogeneityFrontier.endpoint_parametric_lower_quantitative
    (1 / 4) (by norm_num) (by norm_num) n n M 0
    (by omega) (by omega) hM (by norm_num) (by norm_num)).trans
      (jointRadiusZero_minimax_le n M hn hM)

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

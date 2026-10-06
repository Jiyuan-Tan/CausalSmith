module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.OneSidedBayes
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.CenteredBinary
public import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.ParametricLower

/-! A homogeneous two-point witness for the low radius regime. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open Causalean.Stat.Minimax.FuzzyHypotheses Causalean.Stat.Minimax.MomentMatchedMixture
open SharedDesignConstruction
open CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
open scoped ENNReal

/-- Signal threshold used to splice the homogeneous and mixture converses. -/
def converseSignalCutoff : ℝ := 100000000000000000000

/-- Conservative attenuation of the homogeneous perturbation. -/
def converseLowScale : ℝ := 100000000000

/-- The prescribed endpoint law has central second moment at most the square
of its endpoint scale. -/
lemma prescribedOutcomeLaw_second {M q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    Integrable (fun y => (y - M * (q - 1 / 2)) ^ 2)
        (prescribedOutcomeLaw M q) ∧
      ∫ y, (y - M * (q - 1 / 2)) ^ 2 ∂prescribedOutcomeLaw M q ≤ M ^ 2 := by
  have hiNeg : Integrable (fun y : ℝ => (y - M * (q - 1 / 2)) ^ 2)
      (Measure.dirac (-(M / 2))) :=
    integrable_dirac (by simp [enorm])
  have hiPos : Integrable (fun y : ℝ => (y - M * (q - 1 / 2)) ^ 2)
      (Measure.dirac (M / 2)) :=
    integrable_dirac (by simp [enorm])
  constructor
  · unfold prescribedOutcomeLaw
    exact Integrable.add_measure
      (Integrable.smul_measure hiNeg (by simp))
      (Integrable.smul_measure hiPos (by simp))
  · rw [prescribedOutcomeLaw, integral_add_measure, integral_smul_measure,
      integral_smul_measure]
    · simp [ENNReal.toReal_ofReal hq.1,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hq.2)]
      have hqprod : 0 ≤ q * (1 - q) := mul_nonneg hq.1 (sub_nonneg.mpr hq.2)
      have hqquarter : q * (1 - q) ≤ 1 / 4 := by
        nlinarith [sq_nonneg (q - 1 / 2)]
      nlinarith [sq_nonneg M]
    · exact Integrable.smul_measure hiNeg (by simp)
    · exact Integrable.smul_measure hiPos (by simp)

/-- The centered one-cell law is a legal member of every supplied radius
class.  Its only supported cell has zero deviation from the ATE. -/
noncomputable def centeredOneCellModelClass {n : ℕ} (k : Fin n) (M rho u : ℝ)
    (hM : 1 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2) (hu : |u| ≤ M / 2) :
    DiscreteAteHeterogeneityFrontier.ModelClass n (1 / 4) M rho := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let P := centeredOneCellLaw k M u hM0 hu
  refine
    { law := P
      epsilon_pos := by norm_num
      epsilon_lt_half := by norm_num
      M_ge_one := hM
      sigma_nonneg := hrho.1
      sigma_le_two := hrho.2
      consistency := ?_
      exchangeability := ?_
      overlap := ?_
      mean_normalization := ?_
      second_moment := ?_
      homogeneity := ?_ }
  · exact prescribedFiniteRealLaw_consistency M _ _ _ _ _ _ _ _ _
  · exact prescribedFiniteRealLaw_exchangeability M _ _ _ _ _ _ _ _ _
  · intro j hj
    change (1 / 4 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 - 1 / 4
    norm_num
  · intro a j hj
    change |M * ((if a then 1 / 2 + u / M else 1 / 2) - 1 / 2)| ≤ M / 2
    cases a
    · simp
      positivity
    · simp only [ite_true]
      rw [show M * (1 / 2 + u / M - 1 / 2) = u by
        field_simp [hM0.ne'] <;> ring]
      exact hu
  · intro a j hj
    change Integrable
          (fun y => (y - M * ((if a then 1 / 2 + u / M else 1 / 2) - 1 / 2)) ^ 2)
          (prescribedOutcomeLaw M (if a then 1 / 2 + u / M else 1 / 2)) ∧
        ∫ y, (y - M * ((if a then 1 / 2 + u / M else 1 / 2) - 1 / 2)) ^ 2
            ∂prescribedOutcomeLaw M (if a then 1 / 2 + u / M else 1 / 2) ≤ M ^ 2
    apply prescribedOutcomeLaw_second
    cases a
    · norm_num
    · simp only [ite_true]
      rw [abs_le] at hu
      constructor
      · rw [show 1 / 2 + u / M = (M / 2 + u) / M by field_simp [hM0.ne']]
        exact div_nonneg (by linarith) hM0.le
      · rw [show 1 / 2 + u / M ≤ 1 ↔ u ≤ M / 2 by
          constructor <;> intro h <;> field_simp at h ⊢ <;> nlinarith]
        exact hu.2
  · intro j hj
    have hmass (i : Fin n) : P.cellMass i = if i = k then 1 else 0 := by
      dsimp [P, centeredOneCellLaw, prescribedFiniteRealLaw, affineBinaryRealLaw]
      apply sharedDesignBinaryLaw_cellMass
    have hjk : j = k := by
      by_contra hne
      rw [hmass j, if_neg hne] at hj
      linarith
    subst j
    unfold DiscreteAteHeterogeneityFrontier.cellDeviation
      DiscreteAteHeterogeneityFrontier.rawAteFormula
      DiscreteAteHeterogeneityFrontier.cellEffect
    rw [Finset.sum_eq_single k]
    · rw [hmass k, if_pos rfl]
      simp [P, centeredOneCellLaw, prescribedFiniteRealLaw]
      exact mul_nonneg hrho.1 hM0.le
    · intro i hi hik
      simp [hmass, hik]
    · simp

lemma centeredOneCellLaw_rawAte {n : ℕ} (k : Fin n) (M u : ℝ)
    (hM : 0 < M) (hu : |u| ≤ M / 2) :
    DiscreteAteHeterogeneityFrontier.rawAteFormula
      (centeredOneCellLaw k M u hM hu) = u := by
  let P := centeredOneCellLaw k M u hM hu
  have hmass (i : Fin n) : P.cellMass i = if i = k then 1 else 0 := by
    dsimp [P, centeredOneCellLaw, prescribedFiniteRealLaw, affineBinaryRealLaw]
    apply sharedDesignBinaryLaw_cellMass
  unfold DiscreteAteHeterogeneityFrontier.rawAteFormula
    DiscreteAteHeterogeneityFrontier.cellEffect
  rw [Finset.sum_eq_single k]
  · rw [hmass k, if_pos rfl]
    simp [P, centeredOneCellLaw, prescribedFiniteRealLaw]
    field_simp [hM.ne']
  · intro i hi hik
    change P.cellMass i * _ = 0
    rw [hmass i, if_neg hik, zero_mul]
  · simp

lemma exp_neg_four_lt_one_sixteenth : Real.exp (-4) < (1 / 16 : ℝ) := by
  calc
    Real.exp (-4) = Real.exp (-1) ^ 4 := by
      rw [← Real.exp_nat_mul]
      norm_num
    _ < (1 / 2 : ℝ) ^ 4 :=
      pow_lt_pow_left₀ Real.exp_neg_one_lt_half (Real.exp_pos (-1)).le (by norm_num)
    _ = 1 / 16 := by norm_num

/-- Above the splice threshold, both exponential transfer errors fit inside
the explicit high-regime Bayes budget. -/
lemma selected_high_budget_of_cutoff_lt
    (n : ℕ) (rho : ℝ) (hn : 3 ≤ n) (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hhigh : converseSignalCutoff <
      (n : ℝ) * rho ^ 2 / Hrho n rho ^ 2) :
    2 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) +
        8 * Real.exp (-(n : ℝ) /
                (100000000000000 * (dualDegree n rho : ℝ) ^ 2)) < 5 / 8 := by
  have hH : 0 < Hrho n rho := lt_of_lt_of_le zero_lt_one (Hrho_one_le n rho)
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hrhosq : rho ^ 2 ≤ 4 := by nlinarith [sq_nonneg (rho - 2), hrho.1, hrho.2]
  have hsignal : converseSignalCutoff * Hrho n rho ^ 2 <
      (n : ℝ) * rho ^ 2 := by
    rwa [lt_div_iff₀ (sq_pos_of_pos hH)] at hhigh
  have hnlarge : (40 : ℝ) < n := by
    have hcut : (160 : ℝ) < converseSignalCutoff := by
      norm_num [converseSignalCutoff]
    have hHsq : 1 ≤ Hrho n rho ^ 2 := by nlinarith [Hrho_one_le n rho]
    have : converseSignalCutoff < 4 * (n : ℝ) := calc
      converseSignalCutoff ≤ converseSignalCutoff * Hrho n rho ^ 2 := by
        have hc : 0 ≤ converseSignalCutoff := by norm_num [converseSignalCutoff]
        nlinarith
      _ < (n : ℝ) * rho ^ 2 := hsignal
      _ ≤ 4 * (n : ℝ) := by nlinarith
    nlinarith
  have hpoisExponent : 4 < (n : ℝ) * (1 - Real.log 2) := by
    have hlog := Real.log_two_lt_d9
    nlinarith
  have hJ : (dualDegree n rho : ℝ) ≤ 65 * Hrho n rho :=
    dualDegree_le_sixtyFive_mul_Hrho n rho
  have hJ0 : 0 ≤ (dualDegree n rho : ℝ) := by positivity
  have hJsq : (dualDegree n rho : ℝ) ^ 2 ≤ 4225 * Hrho n rho ^ 2 := by
    nlinarith [sq_nonneg ((dualDegree n rho : ℝ) - 65 * Hrho n rho)]
  have hbernNumerator :
      4 * (100000000000000 : ℝ) * (dualDegree n rho : ℝ) ^ 2 < n := by
    have hcut :
        4 * (100000000000000 : ℝ) * 4225 < converseSignalCutoff / 4 := by
      norm_num [converseSignalCutoff]
    have hmain : (converseSignalCutoff / 4) * Hrho n rho ^ 2 < n := by
      have hnrho : (n : ℝ) * rho ^ 2 ≤ 4 * n := by nlinarith
      nlinarith [hsignal]
    calc
      4 * (100000000000000 : ℝ) * (dualDegree n rho : ℝ) ^ 2
          ≤ (4 * 100000000000000 * 4225) * Hrho n rho ^ 2 := by
            nlinarith [hJsq]
      _ < (converseSignalCutoff / 4) * Hrho n rho ^ 2 := by
        exact mul_lt_mul_of_pos_right hcut (sq_pos_of_pos hH)
      _ < n := hmain
  have hden : 0 < (100000000000000 : ℝ) * (dualDegree n rho : ℝ) ^ 2 := by
    have : 0 < dualDegree n rho := by unfold dualDegree; omega
    positivity
  have hbernExponent : 4 < (n : ℝ) /
      (100000000000000 * (dualDegree n rho : ℝ) ^ 2) := by
    rw [lt_div_iff₀ hden]
    simpa only [mul_assoc] using hbernNumerator
  have hpois : Real.exp (-(n : ℝ) * (1 - Real.log 2)) < 1 / 16 :=
    (Real.exp_lt_exp.mpr (by linarith [hpoisExponent])).trans
      exp_neg_four_lt_one_sixteenth
  have hbern : Real.exp (-(n : ℝ) /
      (100000000000000 * (dualDegree n rho : ℝ) ^ 2)) < 1 / 16 :=
    (Real.exp_lt_exp.mpr (by
      rw [neg_div]
      linarith [hbernExponent])).trans
      exp_neg_four_lt_one_sixteenth
  nlinarith

/-- The selected fuzzy construction supplies the high-regime legal fibre
once the signal exceeds the universal splice threshold. -/
theorem selectedHigh_exists_squaredRisk_lower
    (n : ℕ) (M rho : ℝ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hrho : 0 ≤ rho ∧ rho ≤ 2) (hrho0 : 0 < rho)
    (hhigh : converseSignalCutoff <
      (n : ℝ) * rho ^ 2 / Hrho n rho ^ 2)
    (T : (Fin n → SampleObs n) → ℝ) (hT : Measurable T) :
    ∃ P : KnownRadiusClass n M rho,
      ENNReal.ofReal
          (((3 * converseC2 * M * rho / (4 * Hrho n rho)) ^ 2 *
            (3 / 4 - 2 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) -
              8 * Real.exp (-(n : ℝ) /
                (100000000000000 * (dualDegree n rho : ℝ) ^ 2))) / 4)) ≤
        ∫⁻ x, ENNReal.ofReal ((T x - ateTarget P.law) ^ 2)
          ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law ∧
      (M = 1 →
        P.law.fullLaw {z | z.y0 ∉ ({-1 / 2, 1 / 2} : Set ℝ) ∨
          z.y1 ∉ ({-1 / 2, 1 / 2} : Set ℝ)} = 0 ∧
        ∀ a k, 0 < P.law.cellMass k →
          P.law.outcomeLaw a k (({-1 / 2, 1 / 2} : Set ℝ)ᶜ) = 0) := by
  exact selectedLatent_exists_squaredRisk_lower n M rho hn hM hrho hrho0 T hT
    ((selected_high_budget_of_cutoff_lt n rho hn hrho hhigh).trans (by norm_num))

/-- Under the low-regime inequality, a homogeneous one-cell binary pair gives
an explicit risk witness for every measurable estimator. -/
theorem homogeneousLow_exists_squaredRisk_lower
    (n : ℕ) (M rho : ℝ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hrho : 0 ≤ rho ∧ rho ≤ 2) (hrho0 : 0 < rho)
    (hlow : (n : ℝ) * rho ^ 2 / Hrho n rho ^ 2 ≤ converseSignalCutoff)
    (T : (Fin n → SampleObs n) → ℝ) (hT : Measurable T) :
    ∃ P : KnownRadiusClass n M rho,
      ENNReal.ofReal
          ((M * rho / Hrho n rho) ^ 2 / (32 * converseLowScale ^ 2)) ≤
        ∫⁻ x, ENNReal.ofReal ((T x - ateTarget P.law) ^ 2)
          ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law ∧
      (M = 1 →
        P.law.fullLaw {z | z.y0 ∉ ({-1 / 2, 1 / 2} : Set ℝ) ∨
          z.y1 ∉ ({-1 / 2, 1 / 2} : Set ℝ)} = 0 ∧
        ∀ a k, 0 < P.law.cellMass k →
          P.law.outcomeLaw a k (({-1 / 2, 1 / 2} : Set ℝ)ᶜ) = 0) ∧
      DiscreteAteHeterogeneityFrontier.ApproximateHomogeneity M 0 P.law := by
  let k : Fin n := ⟨0, by omega⟩
  let delta : ℝ := rho / (converseLowScale * Hrho n rho)
  have hH : 0 < Hrho n rho := lt_of_lt_of_le zero_lt_one (Hrho_one_le n rho)
  have hscale : 0 < converseLowScale := by norm_num [converseLowScale]
  have hdelta0 : 0 ≤ delta := by dsimp [delta]; positivity
  have hdeltapos : 0 < delta := by dsimp [delta]; positivity
  have hdeltaHalf : delta ≤ 1 / 2 := by
    have : delta ≤ 1 / 50000000000 := by
      dsimp [delta]
      rw [div_le_iff₀ (by
        unfold converseLowScale
        positivity : 0 < converseLowScale * Hrho n rho)]
      have hH1 := Hrho_one_le n rho
      unfold converseLowScale
      nlinarith [hrho.2]
    linarith
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let u0 : ℝ := M * ((1 / 2 : ℝ) - 1 / 2)
  let u1 : ℝ := M * ((1 / 2 : ℝ) + delta - 1 / 2)
  have hu0 : |u0| ≤ M / 2 := by dsimp [u0]; simp; linarith
  have hu1 : |u1| ≤ M / 2 := by
    rw [show u1 = M * delta by dsimp [u1]; ring, abs_mul, abs_of_nonneg hM0.le,
      abs_of_nonneg hdelta0]
    nlinarith
  let Q0m : DiscreteAteHeterogeneityFrontier.ModelClass n (1 / 4) M rho :=
    DiscreteAteHeterogeneityFrontier.testModelClass k (1 / 4) M rho u0
      (by norm_num) (by norm_num) hM hrho.1 hrho.2 hu0
  let Q1m : DiscreteAteHeterogeneityFrontier.ModelClass n (1 / 4) M rho :=
    DiscreteAteHeterogeneityFrontier.testModelClass k (1 / 4) M rho u1
      (by norm_num) (by norm_num) hM hrho.1 hrho.2 hu1
  let Q0 : KnownRadiusClass n M rho := KnownRadiusClass.ofModelClass hn Q0m
  let Q1 : KnownRadiusClass n M rho := KnownRadiusClass.ofModelClass hn Q1m
  let P0m : DiscreteAteHeterogeneityFrontier.ModelClass n (1 / 4) M rho :=
    centeredOneCellModelClass k M rho u0 hM hrho hu0
  let P1m : DiscreteAteHeterogeneityFrontier.ModelClass n (1 / 4) M rho :=
    centeredOneCellModelClass k M rho u1 hM hrho hu1
  let P0 : KnownRadiusClass n M rho := KnownRadiusClass.ofModelClass hn P0m
  let P1 : KnownRadiusClass n M rho := KnownRadiusClass.ofModelClass hn P1m
  let hv0 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_null
    (C := Fin 1) (m₀ := (1 / 2 : ℝ)) (g₀ := (1 / 2 : ℝ)) (g₁ := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let hv1 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_pert
    (C := Fin 1) (m₀ := (1 / 2 : ℝ)) (g₀ := (1 / 2 : ℝ)) (g₁ := (1 / 2 : ℝ))
    (δ := delta) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hdelta0 (by linarith)
  have hreg : (n : ℝ) *
      ((1 / 2 : ℝ) * delta ^ 2 / ((1 / 2 : ℝ) * (1 - 1 / 2))) ≤ Real.log 2 := by
    have hsmall : (n : ℝ) * delta ^ 2 ≤ 1 / 100 := by
      dsimp [delta]
      have hlow' := hlow
      calc
        (n : ℝ) * (rho / (converseLowScale * Hrho n rho)) ^ 2 =
            ((n : ℝ) * rho ^ 2 / Hrho n rho ^ 2) /
              converseLowScale ^ 2 := by
              field_simp [hH.ne', hscale.ne']
        _ ≤ converseSignalCutoff / converseLowScale ^ 2 := by gcongr
        _ = 1 / 100 := by
          norm_num [converseSignalCutoff, converseLowScale]
    have hlog : (1 / 50 : ℝ) ≤ Real.log 2 :=
      le_trans (by norm_num) (le_of_lt Real.log_two_gt_d9)
    calc
      (n : ℝ) * ((1 / 2 : ℝ) * delta ^ 2 /
          ((1 / 2 : ℝ) * (1 - 1 / 2))) = 2 * ((n : ℝ) * delta ^ 2) := by ring
      _ ≤ 2 * (1 / 100 : ℝ) := by gcongr
      _ = 1 / 50 := by norm_num
      _ ≤ Real.log 2 := hlog
  have htvSource : Causalean.Stat.tvDist
      (Causalean.Estimation.MinimaxATE.productLaw hv0 n)
      (Causalean.Estimation.MinimaxATE.productLaw hv1 n) ≤ 1 / 2 :=
    Causalean.Estimation.MinimaxATE.Parametric.tvDist_productLaw_le_half
      hv0 hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hreg
  have hmap0 : DiscreteAteHeterogeneityFrontier.productLaw n Q0.law =
      Measure.map (fun sample i =>
        DiscreteAteHeterogeneityFrontier.testScaleBinaryObs k M (sample i))
        (Causalean.Estimation.MinimaxATE.productLaw hv0 n) := by
    simpa [Q0, Q0m, u0, DiscreteAteHeterogeneityFrontier.testModelClass] using
      (DiscreteAteHeterogeneityFrontier.test_product_map_null
        (n := n) k hM0 hv0 hu0)
  have hmap1 : DiscreteAteHeterogeneityFrontier.productLaw n Q1.law =
      Measure.map (fun sample i =>
        DiscreteAteHeterogeneityFrontier.testScaleBinaryObs k M (sample i))
        (Causalean.Estimation.MinimaxATE.productLaw hv1 n) := by
    simpa [Q1, Q1m, u1, DiscreteAteHeterogeneityFrontier.testModelClass] using
      (DiscreteAteHeterogeneityFrontier.test_product_map_pert
        (n := n) k hM0 hv1 hu1)
  have htvQ : Causalean.Stat.tvDist
      (DiscreteAteHeterogeneityFrontier.productLaw n Q0.law)
      (DiscreteAteHeterogeneityFrontier.productLaw n Q1.law) ≤ 1 / 2 := by
    rw [hmap0, hmap1]
    exact (CausalSmith.Stat.DiscreteAteMinimaxLoggap.tvDist_map_le
      (Causalean.Estimation.MinimaxATE.productLaw hv0 n)
      (Causalean.Estimation.MinimaxATE.productLaw hv1 n)
      (fun sample i => DiscreteAteHeterogeneityFrontier.testScaleBinaryObs k M (sample i))
      (by fun_prop)).trans htvSource
  have htv : Causalean.Stat.tvDist
      (DiscreteAteHeterogeneityFrontier.productLaw n P0.law)
      (DiscreteAteHeterogeneityFrontier.productLaw n P1.law) ≤ 1 / 2 := by
    refine (centeredOneCell_product_tv_le (n := n) k M u0 u1 hM0 hu0 hu1).trans ?_
    simpa [Q0, Q1, Q0m, Q1m, P0, P1, P0m, P1m,
      DiscreteAteHeterogeneityFrontier.productLaw,
      DiscreteAteHeterogeneityFrontier.testModelClass,
      DiscreteAteHeterogeneityFrontier.testRealLaw] using htvQ
  have htau0 : ateTarget P0.law = 0 := by
    dsimp [P0, KnownRadiusClass.ofModelClass]
    simpa [P0m, centeredOneCellModelClass, u0, ateTarget] using
      (centeredOneCellLaw_rawAte k M u0 hM0 hu0)
  have htau1 : ateTarget P1.law = M * delta := by
    dsimp [P1, KnownRadiusClass.ofModelClass]
    simpa [P1m, centeredOneCellModelClass, u1, ateTarget] using
      (centeredOneCellLaw_rawAte k M u1 hM0 hu1)
  let f : Bool → Measure (Fin n → SampleObs n) := fun b =>
    if b then DiscreteAteHeterogeneityFrontier.productLaw n P1.law
    else DiscreteAteHeterogeneityFrontier.productLaw n P0.law
  let _ : ∀ b, IsProbabilityMeasure (f b) := fun b => by
    cases b <;> simp [f] <;> infer_instance
  let K := finiteSupportKernel f Set.univ Set.finite_univ false
  have hK (b : Bool) : K b = f b :=
    finiteSupportKernel_apply f Set.univ Set.finite_univ false b (Set.mem_univ b)
  let _ : IsMarkovKernel K := ⟨fun b =>
    finiteSupportKernel_isProbabilityMeasure f Set.univ Set.finite_univ false b⟩
  let pi0 : Measure Bool := Measure.dirac false
  let pi1 : Measure Bool := Measure.dirac true
  let target : Bool → ℝ := fun b => if b then M * delta / 2 else -(M * delta / 2)
  let T' : (Fin n → SampleObs n) → ℝ := fun x => T x - M * delta / 2
  have hT' : Measurable T' := hT.sub measurable_const
  have htest : (1 / 2 : ℝ) ≤
      (priorPredictive pi0 K).real {x | 0 ≤ T' x} +
        (priorPredictive pi1 K).real {x | T' x < 0} := by
    have hA : MeasurableSet {x : Fin n → SampleObs n | 0 ≤ T' x} :=
      measurableSet_le measurable_const hT'
    have htest0 := Causalean.Stat.one_sub_tvDist_le_test
      (μ := DiscreteAteHeterogeneityFrontier.productLaw n P0.law)
      (ν := DiscreteAteHeterogeneityFrontier.productLaw n P1.law) hA
    have hcomp : ({x : Fin n → SampleObs n | 0 ≤ T' x}ᶜ) = {x | T' x < 0} := by
      ext x
      simp
    rw [hcomp] at htest0
    have hpred0 : priorPredictive pi0 K =
        DiscreteAteHeterogeneityFrontier.productLaw n P0.law := by
      rw [priorPredictive, Measure.dirac_bind (Kernel.measurable K)]
      simpa [f] using hK false
    have hpred1 : priorPredictive pi1 K =
        DiscreteAteHeterogeneityFrontier.productLaw n P1.law := by
      rw [priorPredictive, Measure.dirac_bind (Kernel.measurable K)]
      simpa [f] using hK true
    rw [hpred0, hpred1]
    linarith
  have hbayes := oneSidedFuzzy_bayesRisk_lower pi0 pi1 K target T' hT'
    (∅ : Set Bool) ∅ MeasurableSet.empty MeasurableSet.empty
    (M * delta / 2) (1 / 2) 0 0 (by positivity)
    (by simp [pi0, target]) (by simp [pi1, target])
    (by simp [pi0]) (by simp [pi1]) htest
  have hq : 0 < (M * delta / 2) ^ 2 * ((1 / 2 : ℝ) - 0 - 0) / 2 := by
    positivity
  obtain ⟨b, hrisk⟩ := exists_fibre_of_oneSidedFuzzy_bayesRisk pi0 pi1 K target T'
    ((M * delta / 2) ^ 2 * ((1 / 2 : ℝ) - 0 - 0) / 2) hq hbayes
  cases b
  · refine ⟨P0, ?_, ?_, ?_⟩
    · have heq : ((M * delta / 2) ^ 2 * ((1 / 2 : ℝ) - 0 - 0) / 2) / 2 =
          (M * rho / Hrho n rho) ^ 2 / (32 * converseLowScale ^ 2) := by
        dsimp [delta]
        ring
      rw [← heq]
      rw [htau0]
      unfold squaredRisk at hrisk
      rw [show K false = DiscreteAteHeterogeneityFrontier.productLaw n P0.law by
        simpa [f] using hK false] at hrisk
      simp [target, T'] at hrisk
      simpa using hrisk
    · intro hM1
      simpa [P0, P0m, centeredOneCellModelClass] using
        (centeredOneCellLaw_endpoint_support k M u0 hM0 hu0 hM1)
    · simpa [P0, P0m, centeredOneCellModelClass] using
        (centeredOneCellModelClass k M 0 u0 hM (by norm_num) hu0).homogeneity
  · refine ⟨P1, ?_, ?_, ?_⟩
    · have heq : ((M * delta / 2) ^ 2 * ((1 / 2 : ℝ) - 0 - 0) / 2) / 2 =
          (M * rho / Hrho n rho) ^ 2 / (32 * converseLowScale ^ 2) := by
        dsimp [delta]
        ring
      rw [← heq]
      unfold squaredRisk at hrisk
      have hrisk' :
          ENNReal.ofReal
              (((M * delta / 2) ^ 2 * ((1 / 2 : ℝ) - 0 - 0) / 2) / 2) ≤
            ∫⁻ x, ENNReal.ofReal
                ((T x - M * delta / 2 - M * delta / 2) ^ 2)
              ∂DiscreteAteHeterogeneityFrontier.productLaw n P1.law := by
        rw [show K true = DiscreteAteHeterogeneityFrontier.productLaw n P1.law by
          simpa [f] using hK true] at hrisk
        simpa [target, T'] using hrisk
      rw [htau1]
      exact hrisk'.trans_eq (lintegral_congr fun x => by congr 1 <;> ring)
    · intro hM1
      simpa [P1, P1m, centeredOneCellModelClass] using
        (centeredOneCellLaw_endpoint_support k M u1 hM0 hu1 hM1)
    · simpa [P1, P1m, centeredOneCellModelClass] using
        (centeredOneCellModelClass k M 0 u1 hM (by norm_num) hu1).homogeneity

/-- The same centered homogeneous family supplies the parametric `1/n` floor
at every declared heterogeneity radius. -/
theorem centeredParametric_exists_squaredRisk_lower
    (n : ℕ) (M rho : ℝ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (T : (Fin n → SampleObs n) → ℝ) (hT : Measurable T) :
    ∃ P : KnownRadiusClass n M rho,
      ENNReal.ofReal
          (M ^ 2 / (288 * converseLowScale ^ 2 * (n : ℝ))) ≤
        ∫⁻ x, ENNReal.ofReal ((T x - ateTarget P.law) ^ 2)
          ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law ∧
      (M = 1 →
        P.law.fullLaw {z | z.y0 ∉ ({-1 / 2, 1 / 2} : Set ℝ) ∨
          z.y1 ∉ ({-1 / 2, 1 / 2} : Set ℝ)} = 0 ∧
        ∀ a k, 0 < P.law.cellMass k →
          P.law.outcomeLaw a k (({-1 / 2, 1 / 2} : Set ℝ)ᶜ) = 0) := by
  let r : ℝ := 1 / Real.sqrt n
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsSq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr2 : r ≤ 2 := by
    dsimp [r]
    rw [div_le_iff₀ hs]
    have hs1 : 1 ≤ Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_one]
      apply Real.sqrt_le_sqrt
      norm_num
      exact_mod_cast (show 1 ≤ n by omega)
    linarith
  have hH1 : 1 ≤ Hrho n r := Hrho_one_le n r
  have hH0 : 0 < Hrho n r := lt_of_lt_of_le zero_lt_one hH1
  have hnrSq : (n : ℝ) * r ^ 2 = 1 := by
    dsimp [r]
    field_simp [hs.ne']
    nlinarith [hsSq]
  have hlow : (n : ℝ) * r ^ 2 / Hrho n r ^ 2 ≤ converseSignalCutoff := by
    have hHs : 1 ≤ Hrho n r ^ 2 := by nlinarith
    rw [hnrSq]
    have : 1 / Hrho n r ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hH0)).2 hHs
    exact this.trans (by norm_num [converseSignalCutoff])
  obtain ⟨P, hrisk, hsupp, hhom⟩ :=
    homogeneousLow_exists_squaredRisk_lower n M r hn hM ⟨hr0.le, hr2⟩ hr0 hlow T hT
  let Q : KnownRadiusClass n M rho :=
    { P with
      radius := ⟨hrho, by
        intro k hk
        have hz := hhom k hk
        have hz0 : |DiscreteAteHeterogeneityFrontier.cellDeviation P.law k| = 0 :=
          le_antisymm (by simpa using hz) (abs_nonneg _)
        rw [hz0]
        exact mul_nonneg hrho.1 (by linarith)⟩ }
  refine ⟨Q, ?_, ?_⟩
  · have hH3 : Hrho n r ≤ 3 := by
      unfold Hrho
      rw [show (n : ℝ) * r ^ 2 = 1 from hnrSq]
      have hpos : 0 < Real.exp 1 + 1 := by positivity
      calc
        Real.log (Real.exp 1 + 1) ≤ Real.exp 1 + 1 - 1 :=
          Real.log_le_sub_one_of_pos hpos
        _ ≤ 3 := by linarith [Real.exp_one_lt_three]
    have hHs : Hrho n r ^ 2 ≤ 9 := by nlinarith
    have hrSq : r ^ 2 = 1 / (n : ℝ) := by
      apply (eq_div_iff hnR.ne').2
      nlinarith [hnrSq]
    have hreal : M ^ 2 / (288 * converseLowScale ^ 2 * (n : ℝ)) ≤
        (M * r / Hrho n r) ^ 2 / (32 * converseLowScale ^ 2) := by
      rw [div_pow, mul_pow, hrSq]
      have hn0 : (0 : ℝ) < n := hnR
      have hscale : 0 < converseLowScale := by norm_num [converseLowScale]
      field_simp [hH0.ne', hn0.ne', hscale.ne']
      nlinarith [sq_nonneg M]
    exact (ENNReal.ofReal_le_ofReal hreal).trans (by simpa [Q] using hrisk)
  · simpa [Q] using hsupp

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

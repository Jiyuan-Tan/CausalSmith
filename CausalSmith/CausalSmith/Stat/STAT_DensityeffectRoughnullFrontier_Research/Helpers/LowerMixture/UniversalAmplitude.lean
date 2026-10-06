module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.OrderedGrouping
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.RateBounds

/-! A public small amplitude makes the actual ordered Poisson experiment close,
uniformly over the explicit lower-bound ranks. This is the numerical choice in (44)--(45). -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The singleton coefficient constant from (36). -/
-- @node: lowerSingletonConstant
def lowerSingletonConstant : ℝ :=
  Real.exp ((5 / 3 : ℝ) ^ 2 - 1) * ((5 / 3 : ℝ) ^ 6 + (5 / 3 : ℝ) ^ 4)

/-- A numerical envelope for both terms in the tuned divergence budget. -/
-- @node: lowerBudgetConstant
def lowerBudgetConstant : ℝ :=
  128 * (100 / 81 : ℝ) * (1 / 210) ^ 2 * lowerSingletonConstant ^ 2 +
  512 * (100 / 81 : ℝ) * (1 / 210) ^ 2

/-- The amplitude is fixed before sample size and uses only public numerical constants. -/
-- @node: lowerPublicAmplitude
def lowerPublicAmplitude : ℝ := min (1 / 4) (1 / (64 * (lowerBudgetConstant + 1)))

/-- The chosen public amplitude satisfies the unchanged model parameter range. -/
-- @node: lowerPublicAmplitude_mem
lemma lowerPublicAmplitude_mem : lowerPublicAmplitude ∈ Set.Ioc 0 (1 / 4) := by
  have hC : 0 ≤ lowerBudgetConstant := by unfold lowerBudgetConstant; positivity
  constructor
  · unfold lowerPublicAmplitude
    exact lt_min (by norm_num) (by positivity)
  · exact min_le_left _ _

/-- Multiplying the public envelope by the amplitude leaves a margin below 1/16. -/
-- @node: lowerPublicAmplitude_budget
lemma lowerPublicAmplitude_budget :
    lowerBudgetConstant * lowerPublicAmplitude ≤ 1 / 16 := by
  have hC : 0 ≤ lowerBudgetConstant := by unfold lowerBudgetConstant; positivity
  have hd : 0 < 64 * (lowerBudgetConstant + 1) := by positivity
  have h := mul_le_mul_of_nonneg_left
    (min_le_right (1 / 4 : ℝ) (1 / (64 * (lowerBudgetConstant + 1)))) hC
  apply h.trans
  rw [mul_one_div]
  apply (div_le_iff₀ hd).2
  nlinarith

/-- The rate comparison (44) makes both tuned budget terms uniformly small. -/
-- @node: lower_public_tuned_budget_le
lemma lower_public_tuned_budget_le (n : ℕ) (hn : 0 < n) :
    let theta := lowerPublicAmplitude
    let k := lowerCovariateRank n
    let j := lowerOutcomeRank k
    8 * (((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
      ((k : ℝ) * lowerSingletonConstant * (2 * (n : ℝ) / k) ^ 2 *
        (lowerTau theta k) ^ 2 * (lowerGamma theta j) ^ 2) ^ 2 +
      ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
        (16 * (k : ℝ) * (2 * (n : ℝ) / k) ^ 2 * (lowerGamma theta j) ^ 4)) ≤ 1 / 16 := by
  have ht := lowerPublicAmplitude_mem
  have ht1 : lowerPublicAmplitude ≤ 1 := by linarith [ht.2]
  have h8 := pow_le_of_le_one ht.1.le ht1 (by norm_num : (8 : ℕ) ≠ 0)
  have h4 := pow_le_of_le_one ht.1.le ht1 (by norm_num : (4 : ℕ) ≠ 0)
  have hr : (n : ℝ) ^ (-2 / 29 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by norm_num)
  have h4r : lowerPublicAmplitude ^ 4 * (n : ℝ) ^ (-2 / 29 : ℝ) ≤
      lowerPublicAmplitude :=
    (mul_le_of_le_one_right (by positivity) hr).trans h4
  apply (lower_tuned_poisson_budget_le lowerPublicAmplitude lowerSingletonConstant n hn).trans
  calc
    _ ≤ (128 * (100 / 81 : ℝ) * (1 / 210) ^ 2 * lowerSingletonConstant ^ 2) *
        lowerPublicAmplitude + (512 * (100 / 81 : ℝ) * (1 / 210) ^ 2) *
        lowerPublicAmplitude := add_le_add
          (mul_le_mul_of_nonneg_left h8 (by positivity))
          (mul_le_mul_of_nonneg_left h4r (by positivity))
    _ = lowerBudgetConstant * lowerPublicAmplitude := by unfold lowerBudgetConstant; ring
    _ ≤ _ := lowerPublicAmplitude_budget

/-- The actual ordered Poisson alternatives have chi-square divergence at most 1/16,
with every smallness condition derived from the public amplitude and explicit ranks. -/
-- @node: lower_public_poisson_chiSqDiv_le
lemma lower_public_poisson_chiSqDiv_le (n : ℕ) (hn : 16 ≤ n) :
    let theta := lowerPublicAmplitude
    let k := lowerCovariateRank n
    let j := lowerOutcomeRank k
    let hp := lower_tuned_parameters theta lowerPublicAmplitude_mem n
    Causalean.Stat.chiSqDiv
      (lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerAlternativeLaw theta k j hp s.1 s.2) (2 * (n : NNReal)))
      (lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerNullLaw theta k j hp s.1 s.2) (2 * (n : NNReal))) ≤ 1 / 16 := by
  dsimp only
  let theta := lowerPublicAmplitude
  let k := lowerCovariateRank n
  let j := lowerOutcomeRank k
  let hp := lower_tuned_parameters theta lowerPublicAmplitude_mem n
  have hk : 0 < k := lower_dyadic_one_le ⟨_, rfl⟩
  have hj : 0 < j := lower_dyadic_one_le ⟨_, rfl⟩
  have hcoe : (((2 * (n : NNReal)) / k : NNReal) : ℝ) = 2 * (n : ℝ) / k := by
    simp
  have hx : (((2 * (n : NNReal)) / k : NNReal) : ℝ) ≤ 1 := by
    rw [hcoe]
    exact lower_tuned_poisson_mean_le_one n hn
  have hg := lowerGamma_mem_Icc theta k j hp
  have hr : (((2 * (n : NNReal)) / k : NNReal) : ℝ) * lowerGamma theta j ^ 2 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hx (sq_nonneg (lowerGamma theta j))
    nlinarith [hg.1, hg.2]
  let A : ℝ := ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
      ((k : ℝ) * lowerSingletonConstant * (2 * (n : ℝ) / k) ^ 2 *
        (lowerTau theta k) ^ 2 * (lowerGamma theta j) ^ 2) ^ 2
  let D : ℝ := ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
      (16 * (k : ℝ) * (2 * (n : ℝ) / k) ^ 2 * (lowerGamma theta j) ^ 4)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb : 8 * (A + D) ≤ 1 / 16 := lower_public_tuned_budget_le n (by omega)
  have hd : 2 * D ≤ 1 / 2 := by nlinarith
  have ha : A ≤ 1 / 2 := by nlinarith
  have h := lower_full_poisson_chiSqDiv_le theta k j hp hk hj
    (2 * (n : NNReal)) hx hr
    (by simpa only [hcoe, D, mul_assoc] using hd)
    (by simpa only [hcoe, A, lowerSingletonConstant] using ha)
  apply h.trans
  simpa only [hcoe, A, D, lowerSingletonConstant] using hb

/-- Equation (45) holds for the actual ordered experiments with the public amplitude. -/
-- @node: lower_public_poisson_tv_le
lemma lower_public_poisson_tv_le (n : ℕ) (hn : 16 ≤ n) :
    let theta := lowerPublicAmplitude
    let k := lowerCovariateRank n
    let j := lowerOutcomeRank k
    let hp := lower_tuned_parameters theta lowerPublicAmplitude_mem n
    Causalean.Stat.tvDist
      (lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerNullLaw theta k j hp s.1 s.2) (2 * (n : NNReal)))
      (lowerUniformPoissonMixture (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerAlternativeLaw theta k j hp s.1 s.2) (2 * (n : NNReal))) ≤ 1 / 8 := by
  dsimp only
  let theta := lowerPublicAmplitude
  let k := lowerCovariateRank n
  let j := lowerOutcomeRank k
  let hp := lower_tuned_parameters theta lowerPublicAmplitude_mem n
  have hk : 0 < k := lower_dyadic_one_le ⟨_, rfl⟩
  have hb := lower_public_poisson_chiSqDiv_le n hn
  dsimp only at hb
  rw [lower_full_poisson_chiSqDiv theta k j hp hk (2 * (n : NNReal))] at hb
  apply (lower_full_poisson_tv_le theta k j hp hk (2 * (n : NNReal))).trans
  have hs := Real.sqrt_le_sqrt hb
  have he : Real.sqrt (1 / 16 : ℝ) = 1 / 4 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  rw [he] at hs
  linarith

/-- The common alternative energy is positive and stays in the reporting range,
by the actual bump denominator bounds and legal amplitude envelopes. -/
-- @node: lowerSeparation_mem_Ioc
lemma lowerSeparation_mem_Ioc (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j) :
    lowerSeparation theta k j ∈ Set.Ioc 0 16 := by
  have hk : 0 < k := lower_dyadic_one_le hp.2.1
  have hj : 0 < j := lower_dyadic_one_le hp.2.2.1
  have ht := lowerTau_mem_Ioc theta k j hp hk
  have htp := ht.1
  have hg := lowerGamma_mem_Icc theta k j hp
  have hgp : 0 < lowerGamma theta j := by
    unfold lowerGamma
    exact div_pos hp.1.1 (by exact_mod_cast hj)
  have hc := lowerCphi_bounds (lowerTau theta k) ⟨ht.1.le, ht.2⟩
  have hcp : 0 < lowerCphi (lowerTau theta k) := by linarith [hc.1]
  have hd : 0 < 1 - lowerTau theta k ^ 2 := by nlinarith [ht.1, ht.2]
  have hc1 : lowerCphi (lowerTau theta k) ≤ 1 := by
    apply hc.2.trans
    apply (div_le_one hd).2
    nlinarith [ht.1, ht.2]
  have ht2 : lowerTau theta k ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hg2 : lowerGamma theta j ^ 2 ≤ 1 := by nlinarith [hg.1, hg.2]
  have hc2 : lowerCphi (lowerTau theta k) ^ 2 ≤ 1 := by nlinarith [hcp, hc1]
  have hp2 : lowerTau theta k ^ 2 * lowerGamma theta j ^ 2 ≤ 1 :=
    mul_le_one₀ ht2 (by positivity) hg2
  have hp3 : lowerTau theta k ^ 2 * lowerGamma theta j ^ 2 *
      lowerCphi (lowerTau theta k) ^ 2 ≤ 1 := mul_le_one₀ hp2 (by positivity) hc2
  unfold lowerSeparation
  constructor
  · positivity
  · linarith

end CausalSmith.Stat.DensityEffectRoughNull

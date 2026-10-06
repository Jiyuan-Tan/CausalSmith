module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.PoissonDesign

/-! Actual baseline-weighted outcome bump moments and the quantitative sign bounds
in (32)--(33). The weights use the non-flat null density of the lower experiment. -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The outcome-cell weight against the actual non-flat null baseline. -/
-- @node: lowerOutcomeWeight
def lowerOutcomeWeight (j : ℕ) (i : Fin j) : ℝ :=
  ∫ y, (lowerBump ((j : ℝ) * y - i.val)) ^ 2 / baselineDensity y ∂unitVolume

/-- The baseline-weighted square is integrable by its global envelope. -/
-- @node: lower_outcome_weight_integrable
lemma lower_outcome_weight_integrable (j : ℕ) (i : Fin j) :
    Integrable (fun y => (lowerBump ((j : ℝ) * y - i.val)) ^ 2 /
      baselineDensity y) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound (by
    apply Measurable.aestronglyMeasurable
    unfold baselineDensity
    fun_prop) 2
  filter_upwards [] with y
  have hb := lower_baseline_envelope_lipschitz.1 y
  have hp : 0 < baselineDensity y := by linarith [hb.1]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hp.le)]
  apply (div_le_iff₀ hp).2
  have hu := abs_le.mp (lowerBump_abs_le_one ((j : ℝ) * y - i.val))
  nlinarith [hu.1, hu.2, hb.1]

/-- The unweighted square in each outcome cell has exactly 1/(210j) mass. -/
-- @node: lower_outcome_cell_square_integral
lemma lower_outcome_cell_square_integral (j : ℕ) (i : Fin j) :
    (∫ y, (lowerBump ((j : ℝ) * y - i.val)) ^ 2 ∂unitVolume) =
      (j : ℝ)⁻¹ * (1 / 210) := by
  rw [lower_scaled_cell_integral j i (fun z => (lowerBump z) ^ 2),
    lower_bump_moments.2]
  intro z hz
  exact lowerBump_nonzero_support (fun h => hz (by simp [h]))

/-- The baseline envelope gives both sharp numerical cell-weight bounds in (33). -/
-- @node: lowerOutcomeWeight_bounds
lemma lowerOutcomeWeight_bounds (j : ℕ) (i : Fin j) :
    (10 / 11 : ℝ) * ((j : ℝ)⁻¹ * (1 / 210)) ≤ lowerOutcomeWeight j i ∧
    lowerOutcomeWeight j i ≤ (10 / 9 : ℝ) * ((j : ℝ)⁻¹ * (1 / 210)) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hi : Integrable (fun y => (lowerBump ((j : ℝ) * y - i.val)) ^ 2)
      unitVolume := by
    apply Integrable.of_bound (by apply Measurable.aestronglyMeasurable; fun_prop) 1
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hu := abs_le.mp (lowerBump_abs_le_one ((j : ℝ) * y - i.val))
    nlinarith [hu.1, hu.2]
  have hw := lower_outcome_weight_integrable j i
  have hpoint (y : ℝ) :
      (10 / 11 : ℝ) * (lowerBump ((j : ℝ) * y - i.val)) ^ 2 ≤
        (lowerBump ((j : ℝ) * y - i.val)) ^ 2 / baselineDensity y ∧
      (lowerBump ((j : ℝ) * y - i.val)) ^ 2 / baselineDensity y ≤
        (10 / 9 : ℝ) * (lowerBump ((j : ℝ) * y - i.val)) ^ 2 := by
    have hb := lower_baseline_envelope_lipschitz.1 y
    have hp : 0 < baselineDensity y := by linarith [hb.1]
    constructor
    · apply (le_div_iff₀ hp).2
      nlinarith [mul_le_mul_of_nonneg_left hb.2
        (sq_nonneg (lowerBump ((j : ℝ) * y - i.val)))]
    · apply (div_le_iff₀ hp).2
      nlinarith [mul_le_mul_of_nonneg_left hb.1
        (sq_nonneg (lowerBump ((j : ℝ) * y - i.val)))]
  constructor
  · have h := integral_mono (hi.const_mul (10 / 11)) hw (fun y => (hpoint y).1)
    simpa only [integral_const_mul, lower_outcome_cell_square_integral,
      lowerOutcomeWeight] using h
  · have h := integral_mono hw (hi.const_mul (10 / 9)) (fun y => (hpoint y).2)
    simpa only [integral_const_mul, lower_outcome_cell_square_integral,
      lowerOutcomeWeight] using h

/-- Actual outcome weights are nonnegative. -/
-- @node: lowerOutcomeWeight_nonneg
lemma lowerOutcomeWeight_nonneg (j : ℕ) (i : Fin j) : 0 ≤ lowerOutcomeWeight j i := by
  exact (by positivity : (0 : ℝ) ≤ (10 / 11) * ((j : ℝ)⁻¹ * (1 / 210))).trans
    (lowerOutcomeWeight_bounds j i).1

/-- Total outcome weight is bounded independently of the outcome rank. -/
-- @node: lowerOutcomeWeight_sum_le
lemma lowerOutcomeWeight_sum_le (j : ℕ) (hj : 0 < j) :
    (∑ i : Fin j, lowerOutcomeWeight j i) ≤ (10 / 9 : ℝ) * (1 / 210) := by
  classical
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin j))) =>
    (lowerOutcomeWeight_bounds j i).2)
  have hjn : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  calc
    _ ≤ ∑ _i : Fin j, (10 / 9 : ℝ) * ((j : ℝ)⁻¹ * (1 / 210)) := h
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; field_simp

/-- Squared outcome weights have the inverse-rank bound in (33). -/
-- @node: lowerOutcomeWeight_square_sum_le
lemma lowerOutcomeWeight_square_sum_le (j : ℕ) (hj : 0 < j) :
    (∑ i : Fin j, (lowerOutcomeWeight j i) ^ 2) ≤
      (100 / 81 : ℝ) * (1 / 210) ^ 2 / j := by
  classical
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin j))) =>
    (sq_le_sq₀ (lowerOutcomeWeight_nonneg j i) (by positivity)).2
      (lowerOutcomeWeight_bounds j i).2)
  have hjn : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  calc
    _ ≤ ∑ _i : Fin j, ((10 / 9 : ℝ) * ((j : ℝ)⁻¹ * (1 / 210))) ^ 2 := h
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; field_simp; ring

/-- Independent outcome signs cannot enlarge the total absolute overlap. -/
-- @node: lower_weightedSignOverlap_abs_le
lemma lower_weightedSignOverlap_abs_le (j : ℕ) (hj : 0 < j)
    (omega op : Fin j → Bool) :
    |weightedSignOverlap j (lowerOutcomeWeight j) omega op| ≤
      (10 / 9 : ℝ) * (1 / 210) := by
  classical
  calc
    _ ≤ ∑ i : Fin j, |lowerOutcomeWeight j i * signValue (omega i) * signValue (op i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin j, lowerOutcomeWeight j i := by
      apply Finset.sum_congr rfl
      intro i _
      cases omega i <;> cases op i <;>
        simp [signValue, abs_of_nonneg (lowerOutcomeWeight_nonneg j i)]
    _ ≤ _ := lowerOutcomeWeight_sum_le j hj

/-- Disjoint supports give the exact signed cross product, retaining the two signs. -/
-- @node: signedBumps_product_eq_sum
lemma signedBumps_product_eq_sum (j : ℕ) (omega op : Fin j → Bool) (y : ℝ) :
    signedBumps j omega y * signedBumps j op y =
      ∑ i : Fin j, (lowerBump ((j : ℝ) * y - i.val)) ^ 2 *
        (signValue (omega i) * signValue (op i)) := by
  classical
  by_cases h : ∃ i : Fin j, lowerBump ((j : ℝ) * y - i.val) ≠ 0
  · obtain ⟨i, hi⟩ := h
    rw [signedBumps_eq_active j omega y i hi, signedBumps_eq_active j op y i hi]
    rw [Finset.sum_eq_single i]
    · ring
    · intro l _ hli
      have hz : lowerBump ((j : ℝ) * y - l.val) = 0 := by
        by_contra hn
        exact hli (scaled_bumps_disjoint j y l i hn hi)
      simp [hz]
    · simp
  · have hz : ∀ i : Fin j, lowerBump ((j : ℝ) * y - i.val) = 0 := by
      simpa only [not_exists, not_not] using h
    rw [signedBumps_eq_zero j omega y hz, signedBumps_eq_zero j op y hz]
    simp [hz]

/-- The actual non-flat baseline cross moment is exactly the weighted sign overlap (32). -/
-- @node: lower_outcome_cross_moment_eq_overlap
lemma lower_outcome_cross_moment_eq_overlap (j : ℕ) (omega op : Fin j → Bool) :
    (∫ y, signedBumps j omega y * signedBumps j op y / baselineDensity y
      ∂unitVolume) = weightedSignOverlap j (lowerOutcomeWeight j) omega op := by
  classical
  simp_rw [signedBumps_product_eq_sum, Finset.sum_div]
  have hi (i : Fin j) : Integrable (fun y =>
      (lowerBump ((j : ℝ) * y - i.val)) ^ 2 *
        (signValue (omega i) * signValue (op i)) / baselineDensity y) unitVolume := by
    convert (lower_outcome_weight_integrable j i).mul_const
      (signValue (omega i) * signValue (op i)) using 1
    funext y
    ring
  rw [integral_finsetSum _ (fun i _ => hi i)]
  unfold weightedSignOverlap lowerOutcomeWeight
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_div_right_comm]
  rw [integral_mul_const]
  ring

/-- Replacing the exact singleton coefficient by (36) and using the actual weights
in (33) yields the two quantitative terms in the second inequality of (43).
The compact-range conditions are stated numerically, before experiment identification. -/
-- @node: lowerPoissonOverlap_actual_weights_excess_le
lemma lowerPoissonOverlap_actual_weights_excess_le (tau : ℝ)
    (ht : tau ∈ Set.Ioc 0 (1 / 4)) (xi : NNReal) (hx : (xi : ℝ) ≤ 1)
    (gamma : ℝ) (k j : ℕ) (hj : 0 < j)
    (hr : (xi : ℝ) * gamma ^ 2 ≤ 1)
    (hd : 2 * ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
      (16 * (k : ℝ) * (xi : ℝ) ^ 2 * gamma ^ 4) ≤ 1 / 2)
    (ha : ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
      ((k : ℝ) * (Real.exp ((5 / 3 : ℝ) ^ 2 - 1) *
        ((5 / 3 : ℝ) ^ 6 + (5 / 3 : ℝ) ^ 4)) *
        (xi : ℝ) ^ 2 * tau ^ 2 * gamma ^ 2) ^ 2 ≤ 1 / 2) :
    signPairExpectation j (fun omega op =>
      lowerPoissonOverlap tau ht xi gamma
        (weightedSignOverlap j (lowerOutcomeWeight j) omega op) ^ k) - 1 ≤
      8 * (((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
        ((k : ℝ) * (Real.exp ((5 / 3 : ℝ) ^ 2 - 1) *
          ((5 / 3 : ℝ) ^ 6 + (5 / 3 : ℝ) ^ 4)) *
          (xi : ℝ) ^ 2 * tau ^ 2 * gamma ^ 2) ^ 2 +
        ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
          (16 * (k : ℝ) * (xi : ℝ) ^ 2 * gamma ^ 4)) := by
  let s : ℝ := ∑ i : Fin j, (lowerOutcomeWeight j i) ^ 2
  let S : ℝ := (100 / 81 : ℝ) * (1 / 210) ^ 2 / j
  let a : ℝ := (k : ℝ) * lowerPoissonCoefficient tau ht xi gamma 1
  let A : ℝ := (k : ℝ) * (Real.exp ((5 / 3 : ℝ) ^ 2 - 1) *
    ((5 / 3 : ℝ) ^ 6 + (5 / 3 : ℝ) ^ 4)) * (xi : ℝ) ^ 2 * tau ^ 2 * gamma ^ 2
  let d : ℝ := 16 * (k : ℝ) * (xi : ℝ) ^ 2 * gamma ^ 4
  have hs : s ≤ S := lowerOutcomeWeight_square_sum_le j hj
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have ha0 : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) (lowerPoissonCoefficient_nonneg _ _ _ _ _)
  have haA : a ≤ A := by
    have h := mul_le_mul_of_nonneg_left
      (lowerPoissonCoefficient_one_le tau ht xi hx gamma) (Nat.cast_nonneg k)
    simpa only [a, A, mul_assoc] using h
  have hA0 : 0 ≤ A := ha0.trans haA
  have hsqa : s * a ^ 2 ≤ S * A ^ 2 :=
    mul_le_mul hs ((sq_le_sq₀ ha0 hA0).2 haA) (sq_nonneg a) hS0
  have hsd : s * d ≤ S * d := mul_le_mul_of_nonneg_right hs hd0
  have hcompactD : 2 * s * d ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hsd (by norm_num : (0 : ℝ) ≤ 2)
    dsimp [S, d] at h
    linarith
  have hcompactA : s * a ^ 2 ≤ 1 / 2 := hsqa.trans ha
  have hratio (omega op : Fin j → Bool) :
      4 * (xi : ℝ) * gamma ^ 2 *
        |weightedSignOverlap j (lowerOutcomeWeight j) omega op| ≤ 1 / 2 := by
    have h := mul_le_mul (by nlinarith [hr] : 4 * (xi : ℝ) * gamma ^ 2 ≤ 4)
      (lower_weightedSignOverlap_abs_le j hj omega op) (abs_nonneg _) (by norm_num)
    norm_num at h
    linarith
  have h := lowerPoissonOverlap_sign_excess_le tau ht xi gamma k j
    (lowerOutcomeWeight j) hratio hcompactD hcompactA
  change _ ≤ 8 * (S * A ^ 2 + S * d)
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add hsqa hsd) (by norm_num))

/-- Substituting the Poisson mean 2n/k gives exactly the two rational rate terms
in (43), with explicit constants and no rank-dependent prefactor. -/
-- @node: lower_poisson_budget_eq_fixed_size
lemma lower_poisson_budget_eq_fixed_size (n k j : ℕ) (hk : 0 < k) (hj : 0 < j)
    (tau gamma C : ℝ) :
    8 * (((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
      ((k : ℝ) * C * (2 * (n : ℝ) / k) ^ 2 * tau ^ 2 * gamma ^ 2) ^ 2 +
      ((100 / 81 : ℝ) * (1 / 210) ^ 2 / j) *
        (16 * (k : ℝ) * (2 * (n : ℝ) / k) ^ 2 * gamma ^ 4)) =
    (128 * (100 / 81 : ℝ) * (1 / 210) ^ 2 * C ^ 2) *
      ((n : ℝ) ^ 4 * tau ^ 4 * gamma ^ 4 / ((k : ℝ) ^ 2 * j)) +
    (512 * (100 / 81 : ℝ) * (1 / 210) ^ 2) *
      ((n : ℝ) ^ 2 * gamma ^ 4 / ((k : ℝ) * j)) := by
  have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hjn : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  field_simp
  ring

end CausalSmith.Stat.DensityEffectRoughNull

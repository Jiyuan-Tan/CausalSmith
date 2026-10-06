module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.EnergyDeviation

/-! Perturbation and covariance estimates assembling the energy budgets in (31). -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- A norm error and a reference signal envelope control the perturbed norm. -/
-- @node: energy_mean_norm_le
lemma energy_mean_norm_le {E : Type*} [SeminormedAddCommGroup E]
    (mu p : E) (s B : ℝ) (hp : ‖p‖ ≤ Real.sqrt s) (hb : ‖mu - p‖ ≤ B) :
    ‖mu‖ ≤ Real.sqrt s + B := by
  have h := norm_sub_norm_le mu p
  linarith

/-- Squaring a vector perturbed by at most B gives the signal-dependent error 2B√s+B². -/
-- @node: energy_norm_sq_perturbation
lemma energy_norm_sq_perturbation {E : Type*} [SeminormedAddCommGroup E]
    (mu p : E) (s B : ℝ) (hp : ‖p‖ ≤ Real.sqrt s) (hb : ‖mu - p‖ ≤ B) :
    |‖mu‖ ^ 2 - ‖p‖ ^ 2| ≤ 2 * B * Real.sqrt s + B ^ 2 := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hb
  have hn := energy_mean_norm_le mu p s B hp hb
  have hd : |‖mu‖ - ‖p‖| ≤ B := (abs_norm_sub_norm_le mu p).trans hb
  calc
    _ = |‖mu‖ - ‖p‖| * (‖mu‖ + ‖p‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      ring
    _ ≤ B * (2 * Real.sqrt s + B) :=
      mul_le_mul hd (by linarith) (by positivity) hB
    _ = _ := by ring

/-- The projection's energy deficit adds its approximation budget to the perturbation budget. -/
-- @node: energy_bias_of_projection_budget
lemma energy_bias_of_projection_budget {E : Type*} [SeminormedAddCommGroup E]
    (mu p : E) (s B R : ℝ) (hp : ‖p‖ ≤ Real.sqrt s)
    (hb : ‖mu - p‖ ≤ B) (hprojection : |‖p‖ ^ 2 - s| ≤ R) :
    |‖mu‖ ^ 2 - s| ≤ 2 * B * Real.sqrt s + B ^ 2 + R := by
  calc
    _ = |(‖mu‖ ^ 2 - ‖p‖ ^ 2) + (‖p‖ ^ 2 - s)| := by congr 1; ring
    _ ≤ |‖mu‖ ^ 2 - ‖p‖ ^ 2| + |‖p‖ ^ 2 - s| := abs_add_le _ _
    _ ≤ _ := add_le_add (energy_norm_sq_perturbation mu p s B hp hb) hprojection

/-- Each coefficient is bounded by the Euclidean norm. -/
-- @node: energy_coordinate_abs_le_norm
lemma energy_coordinate_abs_le_norm {J : ℕ} (f : Hj J) (i : Fin J) :
    |f i| ≤ ‖f‖ := by
  have hs : (f i) ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (f j)) (Finset.mem_univ i)
  nlinarith [sq_abs (f i), abs_nonneg (f i), norm_nonneg f]

/-- A finite entrywise bound controls the covariance form on the unit ball. -/
-- @node: covarianceForm_unit_bound
lemma covarianceForm_unit_bound {J : ℕ} (sigma : Matrix (Fin J) (Fin J) ℝ)
    (f : Hj J) (hf : ‖f‖ ≤ 1) :
    |covarianceForm sigma f| ≤ ∑ i, ∑ j, |sigma i j| := by
  unfold covarianceForm
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul, abs_mul]
  have hi := (energy_coordinate_abs_le_norm f i).trans hf
  have hj := (energy_coordinate_abs_le_norm f j).trans hf
  calc
    _ ≤ (1 * |sigma i j|) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hi (abs_nonneg _)) hj
        (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- Finite covariance matrices have a bounded unit-ball quadratic form. -/
-- @node: covarianceOpNorm_bddAbove
lemma covarianceOpNorm_bddAbove {J : ℕ} (sigma : Matrix (Fin J) (Fin J) ℝ) :
    BddAbove {r | ∃ f : Hj J, ‖f‖ ≤ 1 ∧ r = |covarianceForm sigma f|} := by
  refine ⟨∑ i, ∑ j, |sigma i j|, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  exact covarianceForm_unit_bound sigma f hf

/-- The quadratic form is homogeneous of degree two. -/
-- @node: covarianceForm_smul
lemma covarianceForm_smul {J : ℕ} (sigma : Matrix (Fin J) (Fin J) ℝ)
    (c : ℝ) (f : Hj J) : covarianceForm sigma (c • f) = c ^ 2 * covarianceForm sigma f := by
  simp only [covarianceForm, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Normalize a nonzero test vector to pass from the public operator allowance to its form. -/
-- @node: covarianceForm_le_opNorm_budget
lemma covarianceForm_le_opNorm_budget {J : ℕ} (sigma : Matrix (Fin J) (Fin J) ℝ)
    (W : ℝ) (hW : covarianceOpNorm sigma ≤ W) (f : Hj J) :
    covarianceForm sigma f ≤ W * ‖f‖ ^ 2 := by
  by_cases hf : f = 0
  · simp [hf, covarianceForm]
  · have hn : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
    have hunit : ‖‖f‖⁻¹ • f‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg f)),
        inv_mul_cancel₀ hn]
    have hs : |covarianceForm sigma (‖f‖⁻¹ • f)| ≤ covarianceOpNorm sigma :=
      le_csSup (covarianceOpNorm_bddAbove sigma) ⟨_, hunit, rfl⟩
    have heq : covarianceForm sigma f = ‖f‖ ^ 2 * covarianceForm sigma (‖f‖⁻¹ • f) := by
      rw [covarianceForm_smul]
      field_simp
    calc
      _ = _ := heq
      _ ≤ ‖f‖ ^ 2 * W := mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (hs.trans hW)) (sq_nonneg _)
      _ = _ := mul_comm _ _

/-- The exact independent-chain variance identity and covariance budgets give (31). -/
-- @node: energy_variance_of_covariance_budgets
lemma energy_variance_of_covariance_budgets {J : ℕ}
    (sigma : Matrix (Fin J) (Fin J) ℝ) (mu p : Hj J) (s B W V v : ℝ)
    (hp : ‖p‖ ≤ Real.sqrt s) (hb : ‖mu - p‖ ≤ B) (hW : 0 ≤ W)
    (hop : covarianceOpNorm sigma ≤ W) (htrace : covarianceSquareTrace sigma ≤ V)
    (hvar : v = 2 * covarianceForm sigma mu + covarianceSquareTrace sigma) :
    v ≤ 2 * W * (Real.sqrt s + B) ^ 2 + V := by
  have hn := energy_mean_norm_le mu p s B hp hb
  have hs := mul_self_le_mul_self (norm_nonneg mu) hn
  have hform := covarianceForm_le_opNorm_budget sigma W hop mu
  rw [hvar]
  have hh := mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hW)
  nlinarith

/-- A common larger moment multiplier preserves the bias allowance. -/
-- @node: BAllow_mono_constant
lemma BAllow_mono_constant (C D h : ℝ) (hCD : C ≤ D) (hh : 0 ≤ h)
    (m K L T q : ℕ) (kt : ℕ → ℕ) :
    BAllow C h m K L T q kt ≤ BAllow D h m K L T q kt := by
  unfold BAllow
  split_ifs
  · rfl
  · apply mul_le_mul_of_nonneg_right hCD
    positivity

/-- A common larger moment multiplier preserves the operator allowance. -/
-- @node: WAllow_mono_constant
lemma WAllow_mono_constant (C D : ℝ) (hCD : C ≤ D)
    (m T : ℕ) (kt : ℕ → ℕ) : WAllow C m T kt ≤ WAllow D m T kt := by
  unfold WAllow
  split_ifs
  · rfl
  · apply mul_le_mul_of_nonneg_right hCD
    positivity

/-- A common larger nonnegative moment multiplier preserves the square-trace allowance. -/
-- @node: VAllow_mono_constant
lemma VAllow_mono_constant (C D : ℝ) (hC : 0 ≤ C) (hCD : C ≤ D)
    (m J L T : ℕ) (kt : ℕ → ℕ) : VAllow C m J L T kt ≤ VAllow D m J L T kt := by
  have hs : C ^ 2 ≤ D ^ 2 := by nlinarith
  have hsum : 0 ≤ ∑ t ∈ Finset.range (T + 1),
      (bandDimension L t : ℝ) * (kt t : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun t _ => by positivity)
  unfold VAllow
  split_ifs
  · rfl
  · apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num))
    positivity

end CausalSmith.Stat.DensityEffectRoughNull

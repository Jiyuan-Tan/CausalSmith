module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Example
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Histogram
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Continuous antisymmetric bumps and the explicitly normalized lower-experiment nuisance formulas.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Antisymmetric compactly supported cubic bump. -/
def lowerBump (z : ℝ) : ℝ := if z ∈ Set.Icc 0 1 then z * (1 - z) * (2 * z - 1) else 0
/-- Signs are represented by Boolean coordinates. -/
def signValue (a : Bool) : ℝ := if a then 1 else - 1
/-- Disjoint scaled signed bumps with vanishing boundary values. -/
def signedBumps (k : ℕ) (signs : Fin k → Bool) (x : ℝ) : ℝ :=
  ∑ i : Fin k, signValue (signs i) * lowerBump ((k : ℝ) * x - i.val)
/-- Fixed lower-experiment propensity amplitude. -/
def lowerTau (theta : ℝ) (k : ℕ) : ℝ := theta * (k : ℝ) ^ (-1 / 10 : ℝ)
/-- Fixed lower-experiment density amplitude. -/
def lowerGamma (theta : ℝ) (j : ℕ) : ℝ := theta / j
/-- Propensity shared by the null and alternative sign experiments. -/
def lowerPropensity (theta : ℝ) (k : ℕ) (signs : Fin k → Bool) (x : ℝ) : ℝ :=
  (1 + lowerTau theta k * signedBumps k signs x) / 2
/-- Null conditional densities are the non-flat common baseline. -/
def lowerNullDensity (_a : Bool) (_x y : ℝ) : ℝ := baselineDensity y
/-- Alternative densities preserve normalization exactly. -/
def lowerAlternativeDensity (theta : ℝ) (k j : ℕ) (lambda : Fin k → Bool)
    (omega : Fin j → Bool) (a : Bool) (x y : ℝ) : ℝ :=
  baselineDensity y + if a then lowerGamma theta j * signedBumps k lambda x / 
    (1 + lowerTau theta k * signedBumps k lambda x) * signedBumps j omega y else 0
/-- Exact antisymmetric integral factor in the alternative contrast. -/
def lowerCphi (tau : ℝ) : ℝ :=
  ∫ z, (lowerBump z) ^ 2 / (1 - tau ^ 2 * (lowerBump z) ^ 2) ∂unitVolume
/-- Common alternative energy, independent of all signs. -/
def lowerSeparation (theta : ℝ) (k j : ℕ) : ℝ :=
  (lowerTau theta k) ^ 2 * (lowerGamma theta j) ^ 2 * (lowerCphi (lowerTau theta k)) ^ 2 / 210
/-- Exact polynomial bump moments. -/
-- @node: lower_bump_moments
lemma lower_bump_moments :
    (∫ z, lowerBump z ∂unitVolume) = 0 ∧
    (∫ z, (lowerBump z) ^ 2 ∂unitVolume) = 1 / 210 := by
  have hpoly : ∀ᵐ z ∂unitVolume, lowerBump z = z * (1 - z) * (2 * z - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    simp [lowerBump, hz]
  have hfirst : (∫ z, lowerBump z ∂unitVolume) =
      ∫ z in (0 : ℝ)..1, (-2 * z ^ 3 + 3 * z ^ 2 - z) := by
    rw [integral_congr_ae hpoly]
    unfold unitVolume
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    congr 1
    funext z
    ring
  have hsecond : (∫ z, (lowerBump z) ^ 2 ∂unitVolume) =
      ∫ z in (0 : ℝ)..1, (4 * z ^ 6 - 12 * z ^ 5 + 13 * z ^ 4 - 6 * z ^ 3 + z ^ 2) := by
    rw [integral_congr_ae (hpoly.mono (fun z hz => congrArg (fun r : ℝ => r ^ 2) hz))]
    unfold unitVolume
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    congr 1
    funext z
    ring
  constructor
  · rw [hfirst]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_add]
    · simp only [intervalIntegral.integral_const_mul, integral_pow, integral_id]
      norm_num
    all_goals (apply Continuous.intervalIntegrable; fun_prop)
  · rw [hsecond]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_add, intervalIntegral.integral_sub]
    · simp only [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
    all_goals (apply Continuous.intervalIntegrable; fun_prop)

/-- A nonzero bump lies strictly inside its unit cell. -/
-- @node: lowerBump_nonzero_support
lemma lowerBump_nonzero_support {z : ℝ} (hz : lowerBump z ≠ 0) : z ∈ Set.Ioo 0 1 := by
  by_cases h : z ∈ Set.Icc 0 1
  · have h0 : z ≠ 0 := by intro he; subst z; simp [lowerBump] at hz
    have h1 : z ≠ 1 := by intro he; subst z; simp [lowerBump] at hz
    exact ⟨lt_of_le_of_ne h.1 (Ne.symm h0), lt_of_le_of_ne h.2 h1⟩
  · simp [lowerBump, h] at hz

/-- The unscaled bump has absolute height at most one. -/
-- @node: lowerBump_abs_le_one
lemma lowerBump_abs_le_one (z : ℝ) : |lowerBump z| ≤ 1 := by
  by_cases h : z ∈ Set.Icc 0 1
  · have h0 : |z| ≤ 1 := by rw [abs_of_nonneg h.1]; exact h.2
    have h1 : |1 - z| ≤ 1 := by rw [abs_of_nonneg (by linarith [h.2])]; linarith [h.1]
    have h2 : |2 * z - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [h.1, h.2]
    simp only [lowerBump, if_pos h, abs_mul]
    calc
      |z| * |1 - z| * |2 * z - 1| ≤ 1 * 1 * 1 :=
        mul_le_mul (mul_le_mul h0 h1 (abs_nonneg _) (by norm_num)) h2
          (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · simp [lowerBump, h]

/-- The zero-extended polynomial bump is measurable. -/
-- @node: measurable_lowerBump
@[fun_prop] lemma measurable_lowerBump : Measurable lowerBump := by
  exact Measurable.ite measurableSet_Icc (by fun_prop) measurable_const

/-- Signed finite bump families are measurable. -/
-- @node: measurable_signedBumps
@[fun_prop] lemma measurable_signedBumps (k : ℕ) (signs : Fin k → Bool) :
    Measurable (signedBumps k signs) := by
  unfold signedBumps
  fun_prop

/-- Distinct scaled cells cannot both have a nonzero bump at the same point. -/
-- @node: scaled_bumps_disjoint
lemma scaled_bumps_disjoint (k : ℕ) (x : ℝ) (i l : Fin k)
    (hi : lowerBump ((k : ℝ) * x - i.val) ≠ 0)
    (hl : lowerBump ((k : ℝ) * x - l.val) ≠ 0) : i = l := by
  have h := lowerBump_nonzero_support hi
  have g := lowerBump_nonzero_support hl
  have hdiff : (i.val : ℝ) < l.val + 1 ∧ (l.val : ℝ) < i.val + 1 := by
    constructor <;> linarith [h.1, h.2, g.1, g.2]
  have hin : i.val < l.val + 1 := by exact_mod_cast hdiff.1
  have hln : l.val < i.val + 1 := by exact_mod_cast hdiff.2
  apply Fin.ext
  omega

/-- Disjointness preserves the height bound independently of the number of cells. -/
-- @node: signedBumps_abs_le_one
lemma signedBumps_abs_le_one (k : ℕ) (signs : Fin k → Bool) (x : ℝ) :
    |signedBumps k signs x| ≤ 1 := by
  classical
  by_cases h : ∃ i : Fin k, lowerBump ((k : ℝ) * x - i.val) ≠ 0
  · obtain ⟨i, hi⟩ := h
    have he : signedBumps k signs x = signValue (signs i) * lowerBump ((k : ℝ) * x - i.val) := by
      unfold signedBumps
      apply Finset.sum_eq_single i
      · intro l hl hli
        have hz : lowerBump ((k : ℝ) * x - l.val) = 0 := by
          by_contra hn
          exact hli (scaled_bumps_disjoint k x l i hn hi)
        simp [hz]
      · simp
    rw [he, abs_mul]
    have hs : |signValue (signs i)| = 1 := by cases signs i <;> norm_num [signValue]
    simpa [hs] using lowerBump_abs_le_one ((k : ℝ) * x - i.val)
  · have hz : signedBumps k signs x = 0 := by
      unfold signedBumps
      apply Finset.sum_eq_zero
      intro i hi
      have := not_exists.mp h i
      simp [not_ne_iff.mp this]
    simp [hz]

/-- Bounded measurable signed bumps are integrable on the unit interval. -/
-- @node: signedBumps_integrable
lemma signedBumps_integrable (k : ℕ) (signs : Fin k → Bool) :
    Integrable (signedBumps k signs) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using signedBumps_abs_le_one k signs x)

/-- Each rescaled bump still has zero integral on the containing unit interval. -/
-- @node: scaled_lowerBump_integral_zero
lemma scaled_lowerBump_integral_zero (k : ℕ) (i : Fin k) :
    (∫ x, lowerBump ((k : ℝ) * x - i.val) ∂unitVolume) = 0 := by
  have hk : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hi : (i.val : ℝ) + 1 ≤ k := by exact_mod_cast i.isLt
  have hs : Function.support lowerBump ⊆ Set.Ioc (-(i.val : ℝ)) ((k : ℝ) - i.val) := by
    intro z hz
    have h := lowerBump_nonzero_support hz
    constructor <;> linarith [h.1, h.2, (Nat.cast_nonneg i.val : (0 : ℝ) ≤ i.val)]
  have hs0 : Function.support lowerBump ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro z hz
    exact ⟨(lowerBump_nonzero_support hz).1, (lowerBump_nonzero_support hz).2.le⟩
  have hz : (∫ z, lowerBump z) = 0 := by
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hs0,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ← integral_Icc_eq_integral_Ioc]
    exact lower_bump_moments.1
  unfold unitVolume
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_mul_sub _ (ne_of_gt hk)]
  simp only [mul_zero, zero_sub, mul_one]
  rw [intervalIntegral.integral_eq_integral_of_support_subset hs, hz]
  simp

/-- Every signed outcome perturbation has exactly zero integral. -/
-- @node: signedBumps_integral_zero
lemma signedBumps_integral_zero (k : ℕ) (signs : Fin k → Bool) :
    (∫ x, signedBumps k signs x ∂unitVolume) = 0 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hi (i : Fin k) : Integrable (fun x => signValue (signs i) *
      lowerBump ((k : ℝ) * x - i.val)) unitVolume := by
    apply Integrable.const_mul
    apply Integrable.of_bound ((measurable_lowerBump.comp (by fun_prop)).aestronglyMeasurable) 1
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using
        lowerBump_abs_le_one ((k : ℝ) * x - i.val))
  unfold signedBumps
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp only [integral_const_mul, scaled_lowerBump_integral_zero, mul_zero, Finset.sum_const_zero]

end CausalSmith.Stat.DensityEffectRoughNull

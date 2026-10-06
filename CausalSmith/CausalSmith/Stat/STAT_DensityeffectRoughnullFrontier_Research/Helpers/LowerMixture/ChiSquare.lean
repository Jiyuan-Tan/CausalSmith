module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.CellMeasureBridge
public import Causalean.Stat.Minimax.ChiSquared
public import Causalean.Stat.Minimax.Mixture.SignOverlap
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
Weighted-sign exponential control for the chi-square comparison with the actual null mixture.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Weighted overlap of two independent outcome sign vectors. -/
def weightedSignOverlap (j : ℕ) (w : Fin j → ℝ)
    (omega omegaprime : Fin j → Bool) : ℝ :=
  ∑ i : Fin j, w i * signValue (omega i) * signValue (omegaprime i)
/-- Uniform finite expectation over two independent sign vectors. -/
def signPairExpectation (j : ℕ) (g : (Fin j → Bool) → (Fin j → Bool) → ℝ) : ℝ :=
  (Fintype.card (Fin j → Bool) : ℝ) ^ (-2 : ℤ) * ∑ omega, ∑ omegaprime, g omega omegaprime
/-- Completing the square gives the scalar Gaussian integral used by the sign bound. -/
-- @node: sign_gaussian_integral
lemma sign_gaussian_integral (b c e : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (-b * x ^ 2 + c * x + e)) volume ∧
    (∫ x : ℝ, Real.exp (-b * x ^ 2 + c * x + e)) =
      Real.exp (e + c ^ 2 / (4 * b)) * Real.sqrt (Real.pi / b) := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hform (x : ℝ) :
      Real.exp (-b * x ^ 2 + c * x + e) =
      Real.exp (e + c ^ 2 / (4 * b)) *
        Real.exp (-b * (x - c / (2 * b)) ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  simp_rw [hform]
  constructor
  · exact ((integrable_exp_neg_mul_sq hb).comp_sub_right (c / (2 * b))).const_mul _
  · rw [integral_const_mul,
      integral_sub_right_eq_self (fun x : ℝ => Real.exp (-b * x ^ 2)), integral_gaussian]

/-- The library signed-sum MGF bound also controls two independent weighted sign vectors. -/
-- @node: weighted_sign_linear_bound
lemma weighted_sign_linear_bound (j : ℕ) (w : Fin j → ℝ) (t : ℝ) :
    signPairExpectation j (fun omega omegaprime =>
      Real.exp (t * weightedSignOverlap j w omega omegaprime)) ≤
      Real.exp ((∑ i : Fin j, (w i) ^ 2) * t ^ 2 / 2) := by
  classical
  have hcard : (Fintype.card (Fin j → Bool) : ℝ) = (2 : ℝ) ^ j := by
    simp [Fintype.card_bool]
  have hpos : 0 < (Fintype.card (Fin j → Bool) : ℝ) := by
    rw [hcard]
    positivity
  have hinner (omega : Fin j → Bool) :
      (∑ omegaprime, Real.exp (t * weightedSignOverlap j w omega omegaprime)) /
        (Fintype.card (Fin j → Bool) : ℝ) ≤
      Real.exp ((∑ i : Fin j, (w i) ^ 2) * t ^ 2 / 2) := by
    have hsquares : (∑ i : Fin j, (w i * signValue (omega i)) ^ 2) =
        ∑ i : Fin j, (w i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      cases omega i <;> simp [signValue]
    have hm := Causalean.Stat.Concentration.BoundedVariation.signMGF_le
      (fun i : Fin j => w i * signValue (omega i)) t
    rw [hsquares] at hm
    convert hm using 1
    · rw [hcard]
      congr 1
      apply Finset.sum_congr rfl
      intro op hop
      congr 1
      unfold weightedSignOverlap
      apply congrArg (fun z : ℝ => t * z)
      apply Finset.sum_congr rfl
      intro i hi
      simp only [signValue]
      ring
    · congr 1
      ring
  unfold signPairExpectation
  rw [zpow_neg, zpow_ofNat]
  calc
    _ = (∑ omega, (∑ omegaprime,
        Real.exp (t * weightedSignOverlap j w omega omegaprime)) /
        (Fintype.card (Fin j → Bool) : ℝ)) /
        (Fintype.card (Fin j → Bool) : ℝ) := by
      simp only [← Finset.sum_div]
      field_simp
    _ ≤ (∑ _omega : Fin j → Bool,
        Real.exp ((∑ i : Fin j, (w i) ^ 2) * t ^ 2 / 2)) /
        (Fintype.card (Fin j → Bool) : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun omega _ => hinner omega) hpos.le
    _ = _ := by simp [mul_div_cancel_left₀]

/-- A quadratic exponential is the Gaussian average of its linear tilt. -/
-- @node: sign_gaussian_lift
lemma sign_gaussian_lift (a d z : ℝ) (hd : 0 ≤ d) :
    Real.exp (a * z + d * z ^ 2) =
      (Real.sqrt Real.pi)⁻¹ * ∫ x : ℝ,
        Real.exp (-x ^ 2 + (a + 2 * Real.sqrt d * x) * z) := by
  have hform : (fun x : ℝ => Real.exp (-x ^ 2 + (a + 2 * Real.sqrt d * x) * z)) =
      (fun x : ℝ => Real.exp (-1 * x ^ 2 + (2 * Real.sqrt d * z) * x + a * z)) := by
    funext x
    congr 1
    ring
  rw [hform, (sign_gaussian_integral 1 (2 * Real.sqrt d * z) (a * z) (by norm_num)).2]
  have hexp : a * z + (2 * Real.sqrt d * z) ^ 2 / (4 * 1) = a * z + d * z ^ 2 := by
    nlinarith [Real.sq_sqrt hd]
  rw [hexp]
  simp only [div_one]
  field_simp

/-- The upper Gaussian integral has exactly the square-completion factor in the paper. -/
-- @node: sign_gaussian_upper_integral
lemma sign_gaussian_upper_integral (s a d : ℝ) (hd : 0 ≤ d) (hsmall : 2 * s * d < 1) :
    Integrable (fun x : ℝ => Real.exp (-x ^ 2 + s * (a + 2 * Real.sqrt d * x) ^ 2 / 2)) volume ∧
    (Real.sqrt Real.pi)⁻¹ *
      (∫ x : ℝ, Real.exp (-x ^ 2 + s * (a + 2 * Real.sqrt d * x) ^ 2 / 2)) =
      (1 - 2 * s * d) ^ (-1 / 2 : ℝ) *
        Real.exp (s * a ^ 2 / (2 * (1 - 2 * s * d))) := by
  have hb : 0 < 1 - 2 * s * d := by linarith
  have hform : (fun x : ℝ => Real.exp (-x ^ 2 + s * (a + 2 * Real.sqrt d * x) ^ 2 / 2)) =
      (fun x : ℝ => Real.exp (-(1 - 2 * s * d) * x ^ 2 +
        (2 * s * a * Real.sqrt d) * x + s * a ^ 2 / 2)) := by
    funext x
    congr 1
    ring_nf
    rw [Real.sq_sqrt hd]
  rw [hform]
  have hg := sign_gaussian_integral (1 - 2 * s * d) (2 * s * a * Real.sqrt d)
    (s * a ^ 2 / 2) hb
  refine ⟨hg.1, ?_⟩
  rw [hg.2]
  have hexp : s * a ^ 2 / 2 + (2 * s * a * Real.sqrt d) ^ 2 /
      (4 * (1 - 2 * s * d)) = s * a ^ 2 / (2 * (1 - 2 * s * d)) := by
    simp only [mul_pow, Real.sq_sqrt hd]
    field_simp [ne_of_gt hb, show 1 - s * 2 * d ≠ 0 by nlinarith]
    ring
  rw [hexp]
  have hroot : (Real.sqrt Real.pi)⁻¹ * Real.sqrt (Real.pi / (1 - 2 * s * d)) =
      (1 - 2 * s * d) ^ (-1 / 2 : ℝ) := by
    rw [Real.sqrt_div Real.pi_pos.le]
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hb.le,
      ← Real.sqrt_eq_rpow]
    field_simp
  calc
    _ = ((Real.sqrt Real.pi)⁻¹ * Real.sqrt (Real.pi / (1 - 2 * s * d))) *
        Real.exp (s * a ^ 2 / (2 * (1 - 2 * s * d))) := by ring
    _ = _ := by rw [hroot]

/-- Finite sign averaging commutes with integrals of integrable summands. -/
-- @node: sign_pair_integral
lemma sign_pair_integral (j : ℕ)
    (f : (Fin j → Bool) → (Fin j → Bool) → ℝ → ℝ)
    (hf : ∀ omega op, Integrable (f omega op) volume) :
    Integrable (fun x => signPairExpectation j (fun omega op => f omega op x)) volume ∧
    (∫ x, signPairExpectation j (fun omega op => f omega op x)) =
      signPairExpectation j (fun omega op => ∫ x, f omega op x) := by
  classical
  have hi (omega : Fin j → Bool) : Integrable (fun x => ∑ op, f omega op x) volume :=
    integrable_finsetSum _ (fun op _ => hf omega op)
  constructor
  · exact (integrable_finsetSum _ (fun omega _ => hi omega)).const_mul _
  · unfold signPairExpectation
    rw [integral_const_mul, integral_finsetSum _ (fun omega _ => hi omega)]
    simp_rw [integral_finsetSum _ (fun op _ => hf _ op)]

/-- The exact linear coefficient is retained before averaging signs; a Gaussian
completion of the square controls the quadratic exponential without changing its sign. -/
-- @node: weighted_sign_quadratic_bound
lemma weighted_sign_quadratic_bound (j : ℕ) (w : Fin j → ℝ) (a d : ℝ)
    (hd : 0 ≤ d) (hsmall : 2 * (∑ i : Fin j, (w i) ^ 2) * d < 1) :
    signPairExpectation j (fun omega omegaprime =>
      Real.exp (a * weightedSignOverlap j w omega omegaprime + 
        d * (weightedSignOverlap j w omega omegaprime) ^ 2)) ≤
    (1 - 2 * (∑ i : Fin j, (w i) ^ 2) * d) ^ (-1 / 2 : ℝ) * 
      Real.exp ((∑ i : Fin j, (w i) ^ 2) * a ^ 2 /
        (2 * (1 - 2 * (∑ i : Fin j, (w i) ^ 2) * d))) := by
  classical
  let s : ℝ := ∑ i : Fin j, (w i) ^ 2
  let f : (Fin j → Bool) → (Fin j → Bool) → ℝ → ℝ := fun omega op x =>
    Real.exp (-x ^ 2 + (a + 2 * Real.sqrt d * x) * weightedSignOverlap j w omega op)
  have hf (omega op : Fin j → Bool) : Integrable (f omega op) volume := by
    convert (sign_gaussian_integral 1 (2 * Real.sqrt d * weightedSignOverlap j w omega op)
      (a * weightedSignOverlap j w omega op) (by norm_num)).1 using 1
    funext x
    dsimp [f]
    congr 1
    ring
  have hswap := sign_pair_integral j f hf
  have hlift : signPairExpectation j (fun omega op =>
      Real.exp (a * weightedSignOverlap j w omega op +
        d * (weightedSignOverlap j w omega op) ^ 2)) =
      (Real.sqrt Real.pi)⁻¹ *
        ∫ x, signPairExpectation j (fun omega op => f omega op x) := by
    rw [hswap.2]
    unfold signPairExpectation
    simp_rw [sign_gaussian_lift a d _ hd]
    dsimp [f]
    simp only [Finset.mul_sum]
    ring_nf
    apply Finset.sum_congr rfl
    intro omega ho
    apply Finset.sum_congr rfl
    intro op hop
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    ring
  have hbound (x : ℝ) : signPairExpectation j (fun omega op => f omega op x) ≤
      Real.exp (-x ^ 2 + s * (a + 2 * Real.sqrt d * x) ^ 2 / 2) := by
    have hfactor : signPairExpectation j (fun omega op => f omega op x) =
        Real.exp (-x ^ 2) * signPairExpectation j (fun omega op =>
          Real.exp ((a + 2 * Real.sqrt d * x) * weightedSignOverlap j w omega op)) := by
      dsimp [f]
      simp_rw [Real.exp_add]
      unfold signPairExpectation
      simp only [Finset.mul_sum]
      ring_nf
    rw [hfactor, Real.exp_add]
    exact mul_le_mul_of_nonneg_left
      (weighted_sign_linear_bound j w (a + 2 * Real.sqrt d * x)) (Real.exp_pos _).le
  have hg := sign_gaussian_upper_integral s a d hd hsmall
  rw [hlift]
  calc
    _ ≤ (Real.sqrt Real.pi)⁻¹ *
        ∫ x : ℝ, Real.exp (-x ^ 2 + s * (a + 2 * Real.sqrt d * x) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (integral_mono hswap.1 hg.1 hbound) (by positivity)
    _ = _ := hg.2

end CausalSmith.Stat.DensityEffectRoughNull

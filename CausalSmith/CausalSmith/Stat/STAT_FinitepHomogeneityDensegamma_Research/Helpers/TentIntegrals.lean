module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TentSmoothness
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact first and second moments of the paired triangular field. -/
public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Reflection about the midpoint preserves the compact triangular bump. [This is the stated conclusion](goal). -/
-- @node: tentBase_reflection
lemma tentBase_reflection (x : ℝ) : tentBase (1-x) = tentBase x := by
  unfold tentBase
  have h : (0 ≤ 1-x ∧ 1-x ≤ 1) ↔ (0 ≤ x ∧ x ≤ 1) := by constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [h, sub_sub_cancel, min_comm]

/-- The triangular bump has area one half and squared area one third. [This is the stated conclusion](goal). -/
-- @node: tentBase_integrals
lemma tentBase_integrals :
    (∫ x in (0:ℝ)..1, tentBase x) = 1/2 ∧
    (∫ x in (0:ℝ)..1, (tentBase x)^2) = 1/3 := by
  have hf (x : ℝ) (hx : x ∈ Icc (0:ℝ) (1/2)) : tentBase x = 2*x := by
    rw [tentBase, if_pos ⟨hx.1, by linarith [hx.2]⟩, min_eq_left (by linarith [hx.2])]
  have hi : (∫ x in (0:ℝ)..(1/2), tentBase x) = 1/4 := by
    rw [intervalIntegral.integral_congr (fun x hx => hf x (by simpa using hx)), intervalIntegral.integral_const_mul, integral_id]
    norm_num
  have hi2 : (∫ x in (0:ℝ)..(1/2), (tentBase x)^2) = 1/6 := by
    calc
      _ = ∫ x in (0:ℝ)..(1/2), 4*x^2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        rw [hf x (by simpa using hx)]
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num
  have hr (f : ℝ → ℝ) (h : ∀ x, f (1-x) = f x) :
      (∫ x in (1/2:ℝ)..1, f x) = ∫ x in (0:ℝ)..(1/2), f x := by
    conv_lhs => arg 1; ext x; rw [← h x]
    rw [intervalIntegral.integral_comp_sub_left]
    norm_num
  have hc := continuous_tentBase
  have hc2 : Continuous (fun x => (tentBase x)^2) := by fun_prop
  constructor
  · rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), hr _ tentBase_reflection, hi]
    norm_num
  · rw [← intervalIntegral.integral_add_adjacent_intervals (hc2.intervalIntegrable _ _) (hc2.intervalIntegrable _ _), hr _ (fun x => by rw [tentBase_reflection]), hi2]
    norm_num

/-- Extending an integration interval past a compact bump adds only zero integrals. This statement assumes [the hc condition](hyp:hc), [the hz condition](hyp:hz), [the ha condition](hyp:ha), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: integral_compact_bump_extension
lemma integral_compact_bump_extension (f : ℝ → ℝ) (hc : Continuous f)
    (hz : ∀ x, x ≤ 0 ∨ 1 ≤ x → f x = 0)
    (a b : ℝ) (ha : a ≤ 0) (hb : 1 ≤ b) :
    (∫ x in a..b, f x) = ∫ x in (0:ℝ)..1, f x := by
  have hleft : (∫ x in a..0, f x) = 0 := by
    calc
      _ = ∫ x in a..0, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hz x (Or.inl ((show x ∈ Icc a 0 by simpa [uIcc_of_le ha] using hx).2))
      _ = _ := by simp
  have hright : (∫ x in (1:ℝ)..b, f x) = 0 := by
    calc
      _ = ∫ x in (1:ℝ)..b, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hz x (Or.inr ((show x ∈ Icc 1 b by simpa [uIcc_of_le hb] using hx).1))
      _ = _ := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable a 1) (hc.intervalIntegrable 1 b),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable a 0) (hc.intervalIntegrable 0 1), hleft, hright]
  ring

/-- The compact tent vanishes at and outside its two support endpoints. This statement assumes [the hx condition](hyp:hx). [This is the stated conclusion](goal). -/
-- @node: tentBase_zero_outside
lemma tentBase_zero_outside (x : ℝ) (hx : x ≤ 0 ∨ 1 ≤ x) : tentBase x = 0 := by
  by_contra h
  have hs := tentBase_ne_zero_support x h
  rcases hx with hx | hx <;> linarith [hs.1, hs.2]

/-- Every full coarse cell contributes the same tent area and squared area. This statement assumes [the hM condition](hyp:hM), [the hi condition](hyp:hi). [This is the stated conclusion](goal). -/
-- @node: scaled_tent_integrals
lemma scaled_tent_integrals (M i : ℕ) (hM : 0 < M) (hi : i < M) :
    (∫ x in (0:ℝ)..1, tentBase ((M:ℝ)*x-i)) = (M:ℝ)⁻¹/2 ∧
    (∫ x in (0:ℝ)..1, (tentBase ((M:ℝ)*x-i))^2) = (M:ℝ)⁻¹/3 := by
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hi' : (i:ℝ)+1 ≤ M := by exact_mod_cast hi
  have ha : (M:ℝ)*0-i ≤ 0 := by simp
  have hb : 1 ≤ (M:ℝ)*1-i := by linarith
  constructor
  · rw [intervalIntegral.integral_comp_mul_sub _ hm,
      integral_compact_bump_extension _ continuous_tentBase tentBase_zero_outside _ _ ha hb,
      tentBase_integrals.1, smul_eq_mul]
    ring
  · change (∫ x in (0:ℝ)..1, (fun t => (tentBase t)^2) ((M:ℝ)*x-i)) = _
    rw [intervalIntegral.integral_comp_mul_sub (fun t => (tentBase t)^2) hm,
      integral_compact_bump_extension _ (by fun_prop) (fun x hx => by rw [tentBase_zero_outside x hx]; norm_num) _ _ ha hb,
      tentBase_integrals.2, smul_eq_mul]
    ring

/-- Adjacent compact tents have disjoint nonzero supports. [This is the stated conclusion](goal). -/
-- @node: tentBase_adjacent_mul_zero
lemma tentBase_adjacent_mul_zero (x : ℝ) : tentBase x * tentBase (x-1) = 0 := by
  by_cases h : tentBase x = 0
  · rw [h, zero_mul]
  · have hx := tentBase_ne_zero_support x h
    rw [tentBase_zero_outside (x-1) (Or.inl (by linarith [hx.2])), mul_zero]

/-- Disjointness eliminates every cross-pair and within-pair term in the squared field. [This is the stated conclusion](goal). -/
-- @node: coarseTent_square_sum
lemma coarseTent_square_sum (M : ℕ) (σ : Fin (M/2) → Bool) (x : ℝ) :
    (coarseTent M σ x)^2 = ∑ j : Fin (M/2),
      ((tentBase ((M:ℝ)*x-2*j.val))^2 + (tentBase ((M:ℝ)*x-(2*j.val+1)))^2) := by
  classical
  let f := fun j : Fin (M/2) => tentBase ((M:ℝ)*x-2*j.val)-tentBase ((M:ℝ)*x-(2*j.val+1))
  have hp (j : Fin (M/2)) : (signVal (σ j)*f j)^2 =
      (tentBase ((M:ℝ)*x-2*j.val))^2+(tentBase ((M:ℝ)*x-(2*j.val+1)))^2 := by
    have hz := tentBase_adjacent_mul_zero ((M:ℝ)*x-2*j.val)
    rw [show (M:ℝ)*x-2*j.val-1 = (M:ℝ)*x-(2*j.val+1) by ring] at hz
    have hs : (signVal (σ j))^2 = 1 := by cases σ j <;> norm_num [signVal]
    rw [mul_pow, hs, one_mul]
    dsimp [f]
    nlinarith
  rw [← Finset.sum_congr rfl (fun j _ => hp j)]
  by_cases hn : ∃ j, f j ≠ 0
  · obtain ⟨j, hj⟩ := hn
    have hz (k : Fin (M/2)) (hk : k ≠ j) : f k = 0 := by
      by_contra h
      exact hk (paired_bump_unique M x k j h hj)
    have he : coarseTent M σ x = signVal (σ j)*f j := by
      unfold coarseTent
      apply Finset.sum_eq_single j
      · intro k _ hk; change signVal (σ k)*f k = 0; rw [hz k hk, mul_zero]
      · simp
    rw [he]
    symm
    apply Finset.sum_eq_single j
    · intro k _ hk; rw [hz k hk, mul_zero]; norm_num
    · simp
  · have hz : ∀ j, f j = 0 := by simpa using hn
    have he : coarseTent M σ x = 0 := by
      unfold coarseTent
      apply Finset.sum_eq_zero
      intro j _; change signVal (σ j)*f j = 0; rw [hz j, mul_zero]
    simp [he, hz]

/-- Opposite adjacent tents center the field and signs preserve its squared integral. This statement assumes [the hM condition](hyp:hM), [the heven condition](hyp:heven). [This is the stated conclusion](goal). -/
-- @node: coarseTent_interval_moments
lemma coarseTent_interval_moments (M : ℕ) (hM : 0 < M) (heven : 2*(M/2) = M)
    (σ : Fin (M/2) → Bool) :
    (∫ x in (0:ℝ)..1, coarseTent M σ x) = 0 ∧
    (∫ x in (0:ℝ)..1, (coarseTent M σ x)^2) = 1/3 := by
  have hidx (j : Fin (M/2)) : 2*j.val < M ∧ 2*j.val+1 < M := by omega
  have hc (i : ℕ) : Continuous (fun x : ℝ => tentBase ((M:ℝ)*x-i)) := by fun_prop
  have hpair (j : Fin (M/2)) :
      (∫ x in (0:ℝ)..1, signVal (σ j)*(tentBase ((M:ℝ)*x-2*j.val)-tentBase ((M:ℝ)*x-(2*j.val+1)))) = 0 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)]
    norm_cast
    rw [(scaled_tent_integrals M (2*j.val) hM (hidx j).1).1,
      (scaled_tent_integrals M (2*j.val+1) hM (hidx j).2).1]
    ring
  constructor
  · unfold coarseTent
    rw [intervalIntegral.integral_finsetSum]
    · simp only [hpair, Finset.sum_const_zero]
    · intro j _; exact (show Continuous (fun x : ℝ => signVal (σ j)*(tentBase ((M:ℝ)*x-2*j.val)-tentBase ((M:ℝ)*x-(2*j.val+1)))) by fun_prop).intervalIntegrable _ _
  · simp_rw [coarseTent_square_sum]
    rw [intervalIntegral.integral_finsetSum]
    · have hp (j : Fin (M/2)) : (∫ x in (0:ℝ)..1,
          (tentBase ((M:ℝ)*x-2*j.val))^2+(tentBase ((M:ℝ)*x-(2*j.val+1)))^2) = 2*((M:ℝ)⁻¹/3) := by
        rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)]
        norm_cast
        rw [(scaled_tent_integrals M (2*j.val) hM (hidx j).1).2,
          (scaled_tent_integrals M (2*j.val+1) hM (hidx j).2).2]
        ring
      simp only [hp, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hm : (M:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
      have he : 2*(M/2:ℕ) = (M:ℝ) := by exact_mod_cast heven
      calc
        _ = (2*(M/2:ℕ):ℝ)*(M:ℝ)⁻¹/3 := by ring
        _ = _ := by rw [he, mul_inv_cancel₀ hm]
    · intro j _; apply Continuous.intervalIntegrable; fun_prop

/-- Passing from the unit-interval subtype to the real interval preserves the integral. [This is the stated conclusion](goal). -/
-- @node: integral_design_eq_interval
lemma integral_design_eq_interval (f : ℝ → ℝ) :
    (∫ x : unitInterval, f x ∂design) = ∫ x in (0:ℝ)..1, f x := by
  change (∫ x : unitInterval, f x) = _
  rw [unitInterval.measurePreserving_coe.integral_comp unitInterval.measurableEmbedding_coe,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

/-- The normalized original design gives the exact two geometric moments. This statement assumes [the hM condition](hyp:hM), [the heven condition](hyp:heven). [This is the stated conclusion](goal). -/
-- @node: coarseTent_design_moments
lemma coarseTent_design_moments (M : ℕ) (hM : 0 < M) (heven : 2*(M/2) = M)
    (σ : Fin (M/2) → Bool) :
    (∫ x : unitInterval, coarseTent M σ x ∂design) = 0 ∧
    (∫ x : unitInterval, (coarseTent M σ x)^2 ∂design) = 1/3 := by
  rw [integral_design_eq_interval (coarseTent M σ), integral_design_eq_interval (fun x => (coarseTent M σ x)^2)]
  exact coarseTent_interval_moments M hM heven σ

/-- A realization with the prescribed paired effect has its exact centered distance. This statement assumes [the hM condition](hyp:hM), [the heven condition](hyp:heven), [the hA condition](hyp:hA), [the hτ condition](hyp:hτ). [This is the stated conclusion](goal). -/
-- @node: hetDist_of_paired_effect
lemma hetDist_of_paired_effect (law : ObservedLaw) (M : ℕ) (hM : 0 < M)
    (heven : 2*(M/2) = M) (σ : Fin (M/2) → Bool) (A : ℝ) (hA : 0 ≤ A)
    (hτ : ∀ x : unitInterval, law.tau x = A*coarseTent M σ x) :
    meanTau law = 0 ∧ hetDist law = A/Real.sqrt 3 := by
  obtain ⟨hmean, hsq⟩ := coarseTent_design_moments M hM heven σ
  have hm : meanTau law = 0 := by
    unfold meanTau
    simp_rw [hτ]
    rw [integral_const_mul, hmean, mul_zero]
  refine ⟨hm, ?_⟩
  unfold hetDist
  rw [hm]
  simp_rw [hτ, sub_zero, mul_pow]
  rw [integral_const_mul, hsq, Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA,
    Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1), Real.sqrt_one]
  ring

end CausalSmith.Stat.FinitepHomogeneityDensegamma

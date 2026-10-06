module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExplicitRiskEnvelopes
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Sharp arbitrary-order Hölder--Taylor remainder

This file gives the exact Gamma-ratio remainder constant for a Taylor expansion
whose highest within-interval derivative is Hölder continuous.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The exact coefficient in the order-`k` Taylor remainder with a Hölder-`α`
top derivative. -/
-- @node: sharpTaylorRatio
noncomputable def sharpTaylorRatio (α : ℝ) (k : ℕ) : ℝ :=
  Real.Gamma (α + 1) / Real.Gamma (α + k + 1)

/-- Increasing the Taylor order divides the exact remainder coefficient by
the new integrated exponent. -/
-- @node: sharpTaylorRatio_succ
lemma sharpTaylorRatio_succ {α : ℝ} (hα : 0 < α) (k : ℕ) :
    sharpTaylorRatio α (k + 1) = sharpTaylorRatio α k / (α + k + 1) := by
  unfold sharpTaylorRatio
  have hpos : 0 < α + (k : ℝ) + 1 := by positivity
  have hne : α + (k : ℝ) + 1 ≠ 0 := hpos.ne'
  rw [show α + ((k + 1 : ℕ) : ℝ) + 1 = (α + (k : ℝ) + 1) + 1 by
    norm_num; ring]
  rw [Real.Gamma_add_one hne]
  field_simp

/-- Integrating the order-`k` Taylor polynomial of the within derivative gives
the nonconstant part of the order-`k+1` Taylor polynomial. -/
-- @node: integral_taylorWithin_deriv_eq
lemma integral_taylorWithin_deriv_eq
    (k : ℕ) (f : ℝ → ℝ) (s : Set ℝ) (x y : ℝ) :
    ∫ u in x..y,
        taylorWithinEval (derivWithin f s) k s x u =
      taylorWithinEval f (k + 1) s x y - f x := by
  have hd (u : ℝ) := hasDerivAt_taylorWithinEval_succ f k (s := s) (x₀ := x) (x := u)
  have hc : Continuous (fun u : ℝ => taylorWithinEval (derivWithin f s) k s x u) := by
    simp_rw [taylor_within_apply]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := x) (b := y) (fun u _ => hd u) (hc.intervalIntegrable x y)
  simpa using hi

/-- On a subinterval of `[0,1]`, integrating the derivative within `[0,1]`
recovers the endpoint increment. -/
-- @node: integral_derivWithin_unit_eq_sub
lemma integral_derivWithin_unit_eq_sub
    (f : ℝ → ℝ) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hf : ContDiffOn ℝ 1 f (Icc (0 : ℝ) 1)) :
    ∫ u in x..y, derivWithin f (Icc (0 : ℝ) 1) u = f y - f x := by
  by_cases heq : x = y
  · subst y
    simp
  let q := uIcc x y
  have hqsub : q ⊆ Icc (0 : ℝ) 1 := by
    intro u hu
    rw [mem_uIcc] at hu
    rcases hu with hu | hu <;> constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hqdiff : UniqueDiffOn ℝ q := uniqueDiffOn_uIcc heq
  have hlocal : ContDiffOn ℝ 1 f q := hf.mono hqsub
  rw [← intervalIntegral.integral_derivWithin_uIcc_of_contDiffOn_uIcc hlocal]
  apply intervalIntegral.integral_congr
  intro u hu
  exact (derivWithin_subset hqsub (hqdiff u hu)
    (hf.differentiableOn (by norm_num) u (hqsub hu))).symm

/-- A Taylor remainder is the integral of the preceding Taylor remainder for
the within derivative. -/
-- @node: taylorWithin_remainder_succ_integral
lemma taylorWithin_remainder_succ_integral
    (k : ℕ) (f : ℝ → ℝ) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hf : ContDiffOn ℝ (k + 1 : ℕ) f (Icc (0 : ℝ) 1)) :
    f y - taylorWithinEval f (k + 1) (Icc (0 : ℝ) 1) x y =
      ∫ u in x..y,
        (derivWithin f (Icc (0 : ℝ) 1) u -
          taylorWithinEval (derivWithin f (Icc (0 : ℝ) 1)) k
            (Icc (0 : ℝ) 1) x u) := by
  rw [intervalIntegral.integral_sub]
  · rw [integral_derivWithin_unit_eq_sub f hx hy (hf.of_le (by norm_num)),
      integral_taylorWithin_deriv_eq k f (Icc (0 : ℝ) 1) x y]
    ring
  · exact ((hf.continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num))
      (by norm_num)).mono (by
        intro u hu
        rw [mem_uIcc] at hu
        rcases hu with hu | hu <;> constructor <;>
          linarith [hx.1, hx.2, hy.1, hy.2])).intervalIntegrable
  · have hc : Continuous (fun u : ℝ =>
        taylorWithinEval (derivWithin f (Icc (0 : ℝ) 1)) k
          (Icc (0 : ℝ) 1) x u) := by
      simp_rw [taylor_within_apply]
      fun_prop
    exact hc.intervalIntegrable x y

/-- The sharp arbitrary-order Taylor remainder on a nondegenerate compact
interval. The coefficient is the exact Gamma ratio obtained by repeated
integration of the top Hölder modulus. -/
-- @node: sharp_holder_taylor_backward_remainder
theorem sharp_holder_taylor_backward_remainder
    (k : ℕ) (f : ℝ → ℝ) {α L x t : ℝ}
    (hα : 0 < α) (_hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hf : HolderSeminormLe k α L f)
    (hx : x ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (htx : t ≤ x) :
    |f t - taylorWithinEval f k (Icc (0 : ℝ) 1) x t| ≤
      sharpTaylorRatio α k * L * (x - t) ^ ((k : ℝ) + α) := by
  induction k generalizing f t with
  | zero =>
      have hΓ : Real.Gamma (α + 1) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by linarith)).ne'
      have hh := hf.2 t ht x hx
      rw [abs_of_nonpos (sub_nonpos.mpr htx)] at hh
      simpa [sharpTaylorRatio, hΓ, abs_sub_comm, add_comm] using hh
  | succ k ih =>
      let s := Icc (0 : ℝ) 1
      let g := derivWithin f s
      have hs : UniqueDiffOn ℝ s := uniqueDiffOn_Icc (by norm_num)
      have hg : HolderSeminormLe k α L g := by
        refine ⟨hf.1.derivWithin hs (by norm_num), ?_⟩
        intro x hx y hy
        simpa only [g, s, iteratedDerivWithin_succ'] using hf.2 x hx y hy
      have hrec := taylorWithin_remainder_succ_integral k f
        (x := x) (y := t) hx ht hf.1
      have hpoint : ∀ u ∈ Icc t x,
          |g u - taylorWithinEval g k s x u| ≤
            sharpTaylorRatio α k * L * (x - u) ^ ((k : ℝ) + α) := by
        intro u hu
        exact ih g hg ⟨ht.1.trans hu.1, hu.2.trans hx.2⟩ hu.2
      let C := sharpTaylorRatio α k * L
      let p := (k : ℝ) + α
      have hp : -1 < p := by
        dsimp [p]
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have hp0 : 0 ≤ p := by
        dsimp [p]
        exact add_nonneg (Nat.cast_nonneg k) hα.le
      have hC : 0 ≤ C := by
        dsimp [C, sharpTaylorRatio]
        positivity
      have hr : ContinuousOn (fun u => g u - taylorWithinEval g k s x u) (Icc t x) := by
        apply ContinuousOn.sub
        · exact (hf.1.continuousOn_derivWithin hs (by norm_num)).mono (by
            intro u hu
            exact ⟨ht.1.trans hu.1, hu.2.trans hx.2⟩)
        · have hc : Continuous (fun u : ℝ =>
              ∑ i ∈ Finset.range (k + 1),
                (((Nat.factorial i : ℝ)⁻¹ * (u - x) ^ i) •
                  iteratedDerivWithin i g s x)) := by
            fun_prop
          change ContinuousOn (fun u => taylorWithinEval g k s x u) (Icc t x)
          simp_rw [taylor_within_apply]
          exact hc.continuousOn
      have hmajor : ContinuousOn (fun u : ℝ => C * (x - u) ^ p) (Icc t x) := by
        apply continuousOn_const.mul
        exact (continuousOn_const.sub continuousOn_id).rpow_const (fun u hu =>
          Or.inr hp0)
      rw [hrec]
      calc
        |∫ u in x..t, (g u - taylorWithinEval g k s x u)| =
            |∫ u in t..x, (g u - taylorWithinEval g k s x u)| := by
              rw [intervalIntegral.integral_symm, abs_neg]
        _ ≤ ∫ u in t..x, |g u - taylorWithinEval g k s x u| :=
          intervalIntegral.abs_integral_le_integral_abs htx
        _ ≤ ∫ u in t..x, C * (x - u) ^ p := by
          apply intervalIntegral.integral_mono_on htx
            (hr.abs.intervalIntegrable_of_Icc htx)
            (hmajor.intervalIntegrable_of_Icc htx)
          intro u hu
          simpa only [C, p, g, s] using hpoint u hu
        _ = C * ((x - t) ^ (p + 1) / (p + 1)) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_comp_sub_left
              (f := fun x : ℝ => x ^ p) (a := t) (b := x) x]
          rw [integral_rpow (Or.inl hp)]
          simp only [sub_self,
            Real.zero_rpow (ne_of_gt (by linarith : 0 < p + 1)), sub_zero]
        _ = sharpTaylorRatio α (k + 1) * L *
            (x - t) ^ (((k + 1 : ℕ) : ℝ) + α) := by
          rw [sharpTaylorRatio_succ hα k]
          dsimp [C, p]
          have hp1 : (k : ℝ) + α + 1 ≠ 0 := by positivity
          have hexp : (k : ℝ) + α + 1 = ((k + 1 : ℕ) : ℝ) + α := by
            norm_num
            ring
          rw [hexp]
          norm_num [Nat.cast_add, Nat.cast_one]
          field_simp
          ring

/-- The sharp arbitrary-order Taylor remainder on a nondegenerate compact
interval. The coefficient is the exact Gamma ratio obtained by repeated
integration of the top Hölder modulus. -/
-- @node: sharp_holder_taylor_forward_remainder
theorem sharp_holder_taylor_forward_remainder
    (k : ℕ) (f : ℝ → ℝ) {α L x t : ℝ}
    (hα : 0 < α) (_hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hf : HolderSeminormLe k α L f)
    (hx : x ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hxt : x ≤ t) :
    |f t - taylorWithinEval f k (Icc (0 : ℝ) 1) x t| ≤
      sharpTaylorRatio α k * L * (t - x) ^ ((k : ℝ) + α) := by
  induction k generalizing f t with
  | zero =>
      have hΓ : Real.Gamma (α + 1) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by linarith)).ne'
      have hh := hf.2 t ht x hx
      rw [abs_of_nonneg (sub_nonneg.mpr hxt)] at hh
      simpa [sharpTaylorRatio, hΓ, abs_sub_comm, add_comm] using hh
  | succ k ih =>
      let s := Icc (0 : ℝ) 1
      let g := derivWithin f s
      have hs : UniqueDiffOn ℝ s := uniqueDiffOn_Icc (by norm_num)
      have hg : HolderSeminormLe k α L g := by
        refine ⟨hf.1.derivWithin hs (by norm_num), ?_⟩
        intro x hx y hy
        simpa only [g, s, iteratedDerivWithin_succ'] using hf.2 x hx y hy
      have hrec := taylorWithin_remainder_succ_integral k f
        (x := x) (y := t) hx ht hf.1
      have hpoint : ∀ u ∈ Icc x t,
          |g u - taylorWithinEval g k s x u| ≤
            sharpTaylorRatio α k * L * (u - x) ^ ((k : ℝ) + α) := by
        intro u hu
        exact ih g hg ⟨hx.1.trans hu.1, hu.2.trans ht.2⟩ hu.1
      let C := sharpTaylorRatio α k * L
      let p := (k : ℝ) + α
      have hp : -1 < p := by
        dsimp [p]
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have hp0 : 0 ≤ p := by
        dsimp [p]
        exact add_nonneg (Nat.cast_nonneg k) hα.le
      have hC : 0 ≤ C := by
        dsimp [C, sharpTaylorRatio]
        positivity
      have hr : ContinuousOn (fun u => g u - taylorWithinEval g k s x u) (Icc x t) := by
        apply ContinuousOn.sub
        · exact (hf.1.continuousOn_derivWithin hs (by norm_num)).mono (by
            intro u hu
            exact ⟨hx.1.trans hu.1, hu.2.trans ht.2⟩)
        · have hc : Continuous (fun u : ℝ =>
              ∑ i ∈ Finset.range (k + 1),
                (((Nat.factorial i : ℝ)⁻¹ * (u - x) ^ i) •
                  iteratedDerivWithin i g s x)) := by
            fun_prop
          change ContinuousOn (fun u => taylorWithinEval g k s x u) (Icc x t)
          simp_rw [taylor_within_apply]
          exact hc.continuousOn
      have hmajor : ContinuousOn (fun u : ℝ => C * (u - x) ^ p) (Icc x t) := by
        apply continuousOn_const.mul
        exact (continuousOn_id.sub continuousOn_const).rpow_const (fun u hu =>
          Or.inr hp0)
      rw [hrec]
      calc
        |∫ u in x..t, (g u - taylorWithinEval g k s x u)| ≤
            ∫ u in x..t, |g u - taylorWithinEval g k s x u| :=
          intervalIntegral.abs_integral_le_integral_abs hxt
        _ ≤ ∫ u in x..t, C * (u - x) ^ p := by
          apply intervalIntegral.integral_mono_on hxt
            (hr.abs.intervalIntegrable_of_Icc hxt)
            (hmajor.intervalIntegrable_of_Icc hxt)
          intro u hu
          simpa only [C, p, g, s] using hpoint u hu
        _ = C * ((t - x) ^ (p + 1) / (p + 1)) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_comp_sub_right
              (f := fun x : ℝ => x ^ p) (a := x) (b := t) x]
          rw [integral_rpow (Or.inl hp)]
          simp only [sub_self,
            Real.zero_rpow (ne_of_gt (by linarith : 0 < p + 1)), sub_zero]
        _ = sharpTaylorRatio α (k + 1) * L *
            (t - x) ^ (((k + 1 : ℕ) : ℝ) + α) := by
          rw [sharpTaylorRatio_succ hα k]
          dsimp [C, p]
          have hp1 : (k : ℝ) + α + 1 ≠ 0 := by positivity
          have hexp : (k : ℝ) + α + 1 = ((k + 1 : ℕ) : ℝ) + α := by
            norm_num
            ring
          rw [hexp]
          norm_num [Nat.cast_add, Nat.cast_one]
          field_simp
          ring

/-- The endpoint-one case of the arbitrary-center sharp Taylor bound. -/
-- @node: sharp_holder_taylor_endpoint_remainder
theorem sharp_holder_taylor_endpoint_remainder
    (k : ℕ) (f : ℝ → ℝ) {α L t : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hf : HolderSeminormLe k α L f)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |f t - taylorWithinEval f k (Icc (0 : ℝ) 1) 1 t| ≤
      sharpTaylorRatio α k * L * (1 - t) ^ ((k : ℝ) + α) := by
  exact sharp_holder_taylor_backward_remainder k f hα hα1 hL hf (by norm_num) ht ht.2

/-- The sharp within-Taylor bound at any two points of the closed horizon. -/
-- @node: sharp_holder_taylor_remainder
theorem sharp_holder_taylor_remainder
    (k : ℕ) (f : ℝ → ℝ) {α L x t : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hf : HolderSeminormLe k α L f)
    (hx : x ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |f t - taylorWithinEval f k (Icc (0 : ℝ) 1) x t| ≤
      sharpTaylorRatio α k * L * |t - x| ^ ((k : ℝ) + α) := by
  rcases le_total x t with hxt | htx
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hxt)] using
      sharp_holder_taylor_forward_remainder k f hα hα1 hL hf hx ht hxt
  · simpa only [abs_of_nonpos (sub_nonpos.mpr htx), neg_sub] using
      sharp_holder_taylor_backward_remainder k f hα hα1 hL hf hx ht htx

/-- For the paper's Hölder order, the generic sharp ratio is exactly the
declared explicit-risk ratio. -/
-- @node: taylorRatio_eq_sharpTaylorRatio
lemma taylorRatio_eq_sharpTaylorRatio (c : ClassConstants) :
    taylorRatio c = sharpTaylorRatio (c.beta - holderOrder c) (holderOrder c) := by
  by_cases hzero : holderOrder c = 0
  · have hΓ : Real.Gamma (c.beta + 1) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by linarith [c.beta_pos])).ne'
    simp [taylorRatio, sharpTaylorRatio, hzero, hΓ]
  · simp only [taylorRatio, hzero, ↓reduceIte, sharpTaylorRatio]
    congr 2 <;> ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

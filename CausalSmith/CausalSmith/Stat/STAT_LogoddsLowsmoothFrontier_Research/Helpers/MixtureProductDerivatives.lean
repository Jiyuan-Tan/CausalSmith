module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Finite-product derivative bounds for original-record components

Leibniz differentiation controls a product of bounded record densities by its
record count, rather than by an amplitude-dependent exponential constant. -/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Simultaneous bounds for the value and the first two derivatives of a
finite product. The second-order bound counts the diagonal and off-diagonal
Leibniz terms, as required by the component-mixture roadmap. [the documented result](goal) Under [the stated assumptions](hyp:f,x,hM,hs,h0,h1,h2). -/
-- @node: mixture_product_two_derivative_bounds
lemma mixture_product_two_derivative_bounds {ι : Type*}
    (I : Finset ι) (f : ι → ℝ → ℝ) (x M : ℝ) (hM : 1 ≤ M)
    (hs : ∀ i ∈ I, ContDiffAt ℝ 2 (f i) x)
    (h0 : ∀ i ∈ I, |f i x| ≤ 2)
    (h1 : ∀ i ∈ I, |deriv (f i) x| ≤ M)
    (h2 : ∀ i ∈ I, |iteratedDeriv 2 (f i) x| ≤ M) :
    |∏ i ∈ I, f i x| ≤ 2 ^ I.card ∧
    |deriv (fun z => ∏ i ∈ I, f i z) x| ≤ M * (I.card : ℝ) * 2 ^ I.card ∧
    |iteratedDeriv 2 (fun z => ∏ i ∈ I, f i z) x| ≤
      M ^ 2 * (I.card : ℝ) ^ 2 * 2 ^ I.card := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [iteratedDeriv_succ, iteratedDeriv_zero]
  | @insert i I hi ih =>
    have hsI := fun j hj => hs j (Finset.mem_insert_of_mem hj)
    have h0I := fun j hj => h0 j (Finset.mem_insert_of_mem hj)
    have h1I := fun j hj => h1 j (Finset.mem_insert_of_mem hj)
    have h2I := fun j hj => h2 j (Finset.mem_insert_of_mem hj)
    obtain ⟨hv, hd, hdd⟩ := ih hsI h0I h1I h2I
    have hsi := hs i (Finset.mem_insert_self i I)
    have hvi := h0 i (Finset.mem_insert_self i I)
    have hdi := h1 i (Finset.mem_insert_self i I)
    have hddi := h2 i (Finset.mem_insert_self i I)
    have hsp : ContDiffAt ℝ 2 (fun z => ∏ j ∈ I, f j z) x := contDiffAt_prod hsI
    have hdprod := (hsi.differentiableAt (by norm_num)).hasDerivAt.mul
      (hsp.differentiableAt (by norm_num)).hasDerivAt
    have hsecond := iteratedDeriv_fun_mul hsi hsp
    norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one] at hsecond
    simp only [Finset.prod_insert hi, Finset.card_insert_of_notMem hi,
      Nat.cast_add, Nat.cast_one, pow_succ]
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_mul]
      exact (mul_le_mul hvi hv (abs_nonneg _) (by norm_num)).trans_eq (by ring)
    · rw [show deriv (fun z => f i z * ∏ j ∈ I, f j z) x = _ from hdprod.deriv]
      calc
        _ ≤ |deriv (f i) x| * |∏ j ∈ I, f j x| +
            |f i x| * |deriv (fun z => ∏ j ∈ I, f j z) x| := by
          simpa only [abs_mul] using abs_add_le
            (deriv (f i) x * ∏ j ∈ I, f j x)
            (f i x * deriv (fun z => ∏ j ∈ I, f j z) x)
        _ ≤ M * 2 ^ I.card + 2 * (M * (I.card : ℝ) * 2 ^ I.card) := by
          gcongr
        _ ≤ _ := by
          nlinarith [mul_nonneg (by linarith : 0 ≤ M)
            (by positivity : 0 ≤ (2 : ℝ)^I.card)]
    · rw [hsecond]
      calc
        _ ≤ |f i x| * |iteratedDeriv 2 (fun z => ∏ j ∈ I, f j z) x| +
            2 * |deriv (f i) x| * |deriv (fun z => ∏ j ∈ I, f j z) x| +
            |iteratedDeriv 2 (f i) x| * |∏ j ∈ I, f j x| := by
          have hab := abs_add_le
            (f i x * iteratedDeriv 2 (fun z => ∏ j ∈ I, f j z) x)
            (2 * deriv (f i) x * deriv (fun z => ∏ j ∈ I, f j z) x)
          have habc := abs_add_le
            (f i x * iteratedDeriv 2 (fun z => ∏ j ∈ I, f j z) x +
              2 * deriv (f i) x * deriv (fun z => ∏ j ∈ I, f j z) x)
            (iteratedDeriv 2 (f i) x * ∏ j ∈ I, f j x)
          simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
            habc.trans (add_le_add hab (le_refl |iteratedDeriv 2 (f i) x * ∏ j ∈ I, f j x|))
        _ ≤ 2 * (M ^ 2 * (I.card : ℝ) ^ 2 * 2 ^ I.card) +
            2 * M * (M * (I.card : ℝ) * 2 ^ I.card) + M * 2 ^ I.card := by
          gcongr
        _ ≤ _ := by
          have hp : 0 ≤ (2 : ℝ) ^ I.card := by positivity
          have hm2 : M ≤ M ^ 2 := by nlinarith
          have hc : 0 ≤ (I.card : ℝ) := by positivity
          nlinarith [mul_nonneg (sub_nonneg.mpr hm2) hp,
            mul_nonneg (by positivity : 0 ≤ M ^ 2 * (I.card : ℝ)) hp]

/-- [Finite uniform averaging preserves the common second-derivative envelope;
subtracting a comparator costs exactly a factor of two. [the documented result](goal) Under [the stated assumptions](hyp:f,g,x,hs,hg,hf,hb). -/
-- @node: mixture_average_second_derivative_bound
lemma mixture_average_second_derivative_bound {σ : Type*} [Fintype σ] [Nonempty σ]
    (f : σ → ℝ → ℝ) (g : ℝ → ℝ) (x C : ℝ)
    (hs : ∀ s, ContDiffAt ℝ 2 (f s) x) (hg : ContDiffAt ℝ 2 g x)
    (hf : ∀ s, |iteratedDeriv 2 (f s) x| ≤ C)
    (hb : |iteratedDeriv 2 g x| ≤ C) :
    |iteratedDeriv 2 (fun z => (Fintype.card σ : ℝ)⁻¹ * ∑ s, f s z - g z) x| ≤
      2 * C := by
  classical
  have hsum : ContDiffAt ℝ 2 (fun z => ∑ s, f s z) x :=
    ContDiffAt.sum (fun s _ => hs s)
  rw [iteratedDeriv_fun_sub (contDiffAt_const.mul hsum) hg, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_sum (fun s _ => hs s)]
  have hcard : (Fintype.card σ : ℝ) ≠ 0 := by positivity
  have havg : |(Fintype.card σ : ℝ)⁻¹ * ∑ s, iteratedDeriv 2 (f s) x| ≤ C := by
    calc
      _ = (Fintype.card σ : ℝ)⁻¹ * |∑ s, iteratedDeriv 2 (f s) x| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (Fintype.card σ : ℝ)⁻¹ * ∑ s, |iteratedDeriv 2 (f s) x| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (Fintype.card σ : ℝ)⁻¹ * ∑ _s : σ, C := by
        gcongr with s
        exact hf s
      _ = C := by simp [hcard]
  have htri := abs_sub_le ((Fintype.card σ : ℝ)⁻¹ * ∑ s, iteratedDeriv 2 (f s) x)
    0 (iteratedDeriv 2 g x)
  simp only [sub_zero, zero_sub, abs_neg] at htri
  exact htri.trans (by linarith)

end CausalSmith.Stat.LogoddsLowsmoothFrontier

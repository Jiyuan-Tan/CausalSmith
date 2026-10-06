module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureAxes
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureDensities
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureHellinger
public import Mathlib.Analysis.Calculus.Taylor

/-! # Fair component cancellation through zero amplitude

Simultaneous reversal of endpoint signs proves evenness of the actual fair
component likelihoods, including all substituted roots and totalization.
Their difference from the comparator vanishes to first order at zero, as
required by the quadratic Taylor step in the original-record mixture proof.
-/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Negating the fair amplitude reverses every endpoint sign in the random table. [the stated conclusion](goal) holds. -/
-- @node: fairCells_neg_amplitude_reverse
lemma fairCells_neg_amplitude_reverse (k : ℕ) (σ : Fin (k + 1) → Bool) (t δ : ℝ) :
    fairCells true k σ t (-δ) = fairCells true k (fun i => !(σ i)) t δ := by
  funext a y x
  simp only [fairCells, fairRoot_even, signFieldZ_reverse, neg_mul, mul_neg, if_true]

/-- The comparator table is even in the amplitude, with its actual root substituted. [the stated conclusion](goal) holds. -/
-- @node: fairCells_comparator_even
lemma fairCells_comparator_even (k : ℕ) (σ : Fin (k + 1) → Bool) (t δ : ℝ) :
    fairCells false k σ t (-δ) = fairCells false k σ t δ := by
  funext a y x
  simp [fairCells, fairRoot_even, comparatorEffect_even]

/-- Sign reversal identifies actual observed laws, including the fallback law. [the stated conclusion](goal) holds. -/
-- @node: fairLaw_neg_amplitude_reverse
lemma fairLaw_neg_amplitude_reverse (k : ℕ) (σ : Fin (k + 1) → Bool) (t δ : ℝ) :
    fairLaw k σ t (-δ) = fairLaw k (fun i => !(σ i)) t δ := by
  simp only [fairLaw, fairCells_neg_amplitude_reverse]

/-- The actual observed comparator law is even in its amplitude. [the stated conclusion](goal) holds. -/
-- @node: fairComparator_even
lemma fairComparator_even (k : ℕ) (t δ : ℝ) :
    fairComparator k t (-δ) = fairComparator k t δ := by
  simp only [fairComparator, fairCells_comparator_even]

/-- The entire finite-prior sample measure is even, without revealing any signs. [the stated conclusion](goal) holds. -/
-- @node: fairMixture_even
lemma fairMixture_even (n k : ℕ) (t δ : ℝ) :
    fairMixture n k t (-δ) = fairMixture n k t δ := by
  unfold fairMixture finiteSignMixture
  simp only [fairLaw_neg_amplitude_reverse]
  congr 1
  exact endpointSign_prior_reverse k (fun σ =>
    Causalean.Stat.UStatistic.LocalizedVariance.iidLaw (fairLaw k σ t δ).measure n)

/-- Actual likelihood difference on any selected block of original records.
The sign prior remains hidden and all records in the block share its draw. -/
-- @node: fairComponentDifference
def fairComponentDifference {n : ℕ} (k : ℕ) (I : Finset (Fin n))
    (t : ℝ) (o : Fin n → Record) (δ : ℝ) : ℝ :=
  (Fintype.card (Fin (k + 1) → Bool) : ℝ)⁻¹ *
    (∑ σ : Fin (k + 1) → Bool, ∏ i ∈ I, recordCellDensity (fairLaw k σ t δ) (o i)) -
    ∏ i ∈ I, recordCellDensity (fairComparator k t δ) (o i)

/-- Every block mixture difference is even by reversal of the shared sign prior. [the stated conclusion](goal) holds. -/
-- @node: fairComponentDifference_even
lemma fairComponentDifference_even {n : ℕ} (k : ℕ) (I : Finset (Fin n))
    (t : ℝ) (o : Fin n → Record) (δ : ℝ) :
    fairComponentDifference k I t o (-δ) = fairComponentDifference k I t o δ := by
  unfold fairComponentDifference
  rw [fairComparator_even]
  simp only [fairLaw_neg_amplitude_reverse]
  rw [endpointSign_prior_reverse k (fun σ =>
    ∏ i ∈ I, recordCellDensity (fairLaw k σ t δ) (o i))]

/-- At zero amplitude every block mixture equals its product comparator. [the stated conclusion](goal) holds. -/
-- @node: fairComponentDifference_zero
lemma fairComponentDifference_zero {n : ℕ} (k : ℕ) (I : Finset (Fin n))
    (t : ℝ) (o : Fin n → Record) : fairComponentDifference k I t o 0 = 0 := by
  have hdraw (σ : Fin (k + 1) → Bool) : fairLaw k σ t 0 = fairComparator k t 0 := by
    simp only [fairLaw, fairComparator, fairCells_zero_amplitude]
  have hcard : (Fintype.card (Fin (k + 1) → Bool) : ℝ) ≠ 0 := by positivity
  simp only [fairComponentDifference, hdraw, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul, sub_self]

/-- An even real function has zero totalized derivative at zero. This also
covers nondifferentiable inputs, where Lean's derivative is defined as zero. [the documented result](goal) Under [the stated assumptions](hyp:hf). -/
-- @node: mixture_even_deriv_zero
lemma mixture_even_deriv_zero (f : ℝ → ℝ) (hf : ∀ δ, f (-δ) = f δ) :
    deriv f 0 = 0 := by
  have he : (fun δ => f (-δ)) = f := funext hf
  have h := deriv_comp_neg f 0
  rw [he] at h
  simp only [neg_zero] at h
  linarith

/-- [The linear term of every actual fair block difference vanishes. [the stated conclusion](goal) holds. -/
-- @node: fairComponentDifference_deriv_zero
lemma fairComponentDifference_deriv_zero {n : ℕ} (k : ℕ) (I : Finset (Fin n))
    (t : ℝ) (o : Fin n → Record) : deriv (fairComponentDifference k I t o) 0 = 0 := by
  exact mixture_even_deriv_zero _ (fairComponentDifference_even k I t o)

/-- The signed second-order Taylor bound when the constant and linear terms vanish. Evenness permits the same positive-interval argument for both signs. the documented result Under the stated assumptions. [The stated hypotheses](hyp:_hC,heven,hzero,hlinear,hSmooth,hSecond) hold, and [the stated conclusion follows](goal). -/
-- @node: mixture_even_quadratic_bound
lemma mixture_even_quadratic_bound (f : ℝ → ℝ) (δ C : ℝ)
    (_hC : 0 ≤ C) (heven : ∀ x, f (-x) = f x) (hzero : f 0 = 0)
    (hlinear : HasDerivAt f 0 0)
    (hSmooth : ContDiffOn ℝ 2 f (Set.Icc 0 |δ|))
    (hSecond : ∀ x ∈ Set.Ioo 0 |δ|, |iteratedDeriv 2 f x| ≤ C) :
    |f δ| ≤ C * δ ^ 2 / 2 := by
  by_cases hδ : δ = 0
  · subst δ
    simp [hzero]
  have hp : 0 < |δ| := abs_pos.mpr hδ
  have hWithin : derivWithin f (Set.Icc 0 |δ|) 0 = 0 :=
    hlinear.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc hp) 0 ⟨le_rfl, hp.le⟩)
  have hTaylor : taylorWithinEval f 1 (Set.Icc 0 |δ|) 0 |δ| = 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, taylorWithinEval_succ]
    simp only [Nat.zero_add, taylor_within_zero_eval, iteratedDerivWithin_one,
      hzero, hWithin, smul_zero, add_zero]
  have hs : ContDiffOn ℝ 2 f (Set.uIcc 0 |δ|) := by
    simpa only [Set.uIcc_of_le hp.le] using hSmooth
  obtain ⟨x, hx, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) (x₀ := 0) (x := |δ|) hp.ne hs
  rw [Set.uIoo_of_lt hp] at hx
  rw [Set.uIcc_of_le hp.le] at hrem
  have he : f |δ| = f δ := by
    rcases le_total 0 δ with hd | hd
    · rw [abs_of_nonneg hd]
    · rw [abs_of_nonpos hd, heven]
  rw [hTaylor, sub_zero, sub_zero] at hrem
  calc
    |f δ| = |iteratedDeriv 2 f x| * δ^2 / 2 := by
      rw [← he, hrem]
      norm_num [abs_mul, abs_div, sq_abs, abs_pow]
    _ ≤ C * δ ^ 2 / 2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hSecond x hx) (sq_nonneg δ)) (by norm_num)

/-- [Applying Taylor to the actual block difference needs only its smoothness
and second-derivative estimate; the two zero terms are already proved. [the documented result](goal) Under [the stated assumptions](hyp:hC,hDiff,hSmooth,hSecond). -/
-- @node: fairComponentDifference_quadratic_bound
lemma fairComponentDifference_quadratic_bound {n : ℕ} (k : ℕ) (I : Finset (Fin n))
    (t : ℝ) (o : Fin n → Record) (δ C : ℝ) (hC : 0 ≤ C)
    (hDiff : DifferentiableAt ℝ (fairComponentDifference k I t o) 0)
    (hSmooth : ContDiffOn ℝ 2 (fairComponentDifference k I t o) (Set.Icc 0 |δ|))
    (hSecond : ∀ x ∈ Set.Ioo 0 |δ|,
      |iteratedDeriv 2 (fairComponentDifference k I t o) x| ≤ C) :
    |fairComponentDifference k I t o δ| ≤ C * δ ^ 2 / 2 := by
  have hlinear := hDiff.hasDerivAt
  rw [fairComponentDifference_deriv_zero] at hlinear
  exact mixture_even_quadratic_bound _ δ C hC
    (fairComponentDifference_even k I t o) (fairComponentDifference_zero k I t o)
    hlinear hSmooth hSecond

/-- [The actual fair component Taylor estimate has the roadmap's coefficient.
The product differentiation bound is kept as an explicit remaining input. [the documented result](goal) Under [the stated assumptions](hyp:hDiff,hSmooth,hSecond). -/
-- @node: fairComponentDifference_taylor_bound
lemma fairComponentDifference_taylor_bound {n : ℕ} (k : ℕ) (I : Finset (Fin n))
    (t : ℝ) (o : Fin n → Record) (δ M : ℝ)
    (hDiff : DifferentiableAt ℝ (fairComponentDifference k I t o) 0)
    (hSmooth : ContDiffOn ℝ 2 (fairComponentDifference k I t o) (Set.Icc 0 |δ|))
    (hSecond : ∀ x ∈ Set.Ioo 0 |δ|,
      |iteratedDeriv 2 (fairComponentDifference k I t o) x| ≤
        2 * M ^ 2 * (I.card : ℝ) ^ 2 * 2 ^ I.card) :
    |fairComponentDifference k I t o δ| ≤
      M ^ 2 * (I.card : ℝ) ^ 2 * 2 ^ I.card * δ ^ 2 := by
  apply (fairComponentDifference_quadratic_bound k I t o δ _ (by positivity)
    hDiff hSmooth hSecond).trans_eq
  ring

/-- Exact singleton matching removes any one-record block, throughout the
support neighborhood and including the original observed cells. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ). Under [the stated assumptions](hyp:hk). -/
-- @node: fairComponentDifference_singleton
lemma fairComponentDifference_singleton {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (i : Fin n) (t : ℝ) (o : Fin n → Record) (δ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4)) (hδ : |δ| ≤ calibEps) :
    fairComponentDifference k {i} t o δ = 0 := by
  simp only [fairComponentDifference, Finset.prod_singleton, recordCellDensity,
    ← Finset.mul_sum]
  have hmatch := (calib_singletons_spec k hk).2 t δ ht hδ
    (o i).2.1 (o i).2.2 (o i).1
  calc
    _ = 4 * ((Fintype.card (Fin (k + 1) → Bool) : ℝ)⁻¹ *
      ∑ σ, (fairLaw k σ t δ).cells (o i).2.1 (o i).2.2 (o i).1) -
      4 * (fairComparator k t δ).cells (o i).2.1 (o i).2.2 (o i).1 := by ring
    _ = 0 := by rw [hmatch]; ring

/-- [Averaging products of densities with the common half-unit floor preserves
the component floor, despite dependence among records through the hidden signs. [the documented result](goal) Under [the stated assumptions](hyp:f,hf). -/
-- @node: mixture_average_product_lower
lemma mixture_average_product_lower {n : ℕ} (k : ℕ) (I : Finset (Fin n))
    (f : (Fin (k + 1) → Bool) → Fin n → ℝ)
    (hf : ∀ σ i, i ∈ I → (1 / 2 : ℝ) ≤ f σ i) :
    ((2 : ℝ) ^ I.card)⁻¹ ≤
      (Fintype.card (Fin (k + 1) → Bool) : ℝ)⁻¹ * ∑ σ, ∏ i ∈ I, f σ i := by
  have hprod (σ : Fin (k + 1) → Bool) :
      ((2 : ℝ) ^ I.card)⁻¹ ≤ ∏ i ∈ I, f σ i := by
    calc
      _ = ∏ _i ∈ I, (1 / 2 : ℝ) := by simp [one_div, inv_pow]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num) (hf σ)
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => hprod σ)
  have hcard : (Fintype.card (Fin (k + 1) → Bool) : ℝ) ≠ 0 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ (Fintype.card (Fin (k + 1) → Bool) : ℝ)⁻¹)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hcard, one_mul] using hscaled

/-- The actual fair component square-root discrepancy follows from its Taylor
bound and one-record density floors, with the precise exponential coefficient. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ,hDiff,hSmooth,hSecond). -/
-- @node: fair_component_hellinger_taylor_bound
lemma fair_component_hellinger_taylor_bound {n : ℕ} (k : ℕ) (I : Finset (Fin n))
    (t : ℝ) (o : Fin n → Record) (δ M : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4)) (hδ : |δ| ≤ 1 / 100)
    (hDiff : DifferentiableAt ℝ (fairComponentDifference k I t o) 0)
    (hSmooth : ContDiffOn ℝ 2 (fairComponentDifference k I t o) (Set.Icc 0 |δ|))
    (hSecond : ∀ x ∈ Set.Ioo 0 |δ|,
      |iteratedDeriv 2 (fairComponentDifference k I t o) x| ≤
        2 * M ^ 2 * (I.card : ℝ) ^ 2 * 2 ^ I.card) :
    (Real.sqrt ((Fintype.card (Fin (k + 1) → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i ∈ I, recordCellDensity (fairLaw k σ t δ) (o i)) -
      Real.sqrt (∏ i ∈ I, recordCellDensity (fairComparator k t δ) (o i))) ^ 2 ≤
      M ^ 4 * (I.card : ℝ) ^ 4 * 8 ^ I.card * δ ^ 4 := by
  have hfloor (σ : Fin (k + 1) → Bool) (i : Fin n) :
      (1 / 2 : ℝ) ≤ recordCellDensity (fairLaw k σ t δ) (o i) :=
    (fairDensity_bounds true k σ t δ ht hδ (o i).2.1 (o i).2.2 (o i).1).1
  have hcomp (i : Fin n) :
      (1 / 2 : ℝ) ≤ recordCellDensity (fairComparator k t δ) (o i) :=
    (fairDensity_bounds false k (fun _ => false) t δ ht hδ
      (o i).2.1 (o i).2.2 (o i).1).1
  have hFlo := mixture_average_product_lower k I
    (fun σ i => recordCellDensity (fairLaw k σ t δ) (o i)) (fun σ i _ => hfloor σ i)
  have hGlo : ((2 : ℝ) ^ I.card)⁻¹ ≤
      ∏ i ∈ I, recordCellDensity (fairComparator k t δ) (o i) := by
    calc
      _ = ∏ _i ∈ I, (1 / 2 : ℝ) := by simp [one_div, inv_pow]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num) (fun i _ => hcomp i)
  have hTaylor := fairComponentDifference_taylor_bound k I t o δ M hDiff hSmooth hSecond
  have hDifference : |fairComponentDifference k I t o δ| ≤
      2 * M ^ 2 * (I.card : ℝ) ^ 2 * 2 ^ I.card * |δ ^ 2| := by
    rw [abs_of_nonneg (sq_nonneg δ)]
    nlinarith [sq_nonneg M,
      mul_nonneg (by positivity : 0 ≤ M ^ 2 * (I.card : ℝ) ^ 2 * 2 ^ I.card) (sq_nonneg δ)]
  have h := mixture_component_pointwise_bound I.card M (δ ^ 2) _ _ hFlo hGlo hDifference
  convert h using 1 <;> ring

end CausalSmith.Stat.LogoddsLowsmoothFrontier

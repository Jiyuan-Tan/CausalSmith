module
public import Causalean.Stat.Minimax.HellingerAffinity

/-! # Component Hellinger bounds for the original-record mixtures

The density floor converts a component likelihood difference into the roadmap's
exponential component bound. Affinity tensorization then adds component bounds,
with exactly matching singleton components removed from the sum.
-/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- A positive common density floor controls squared square-root discrepancy. Under the stated assumptions. [The stated hypotheses](hyp:ha,hf,hg,_hd,hfg) hold, and [the stated conclusion follows](goal). -/
-- @node: mixture_sqrt_difference_le
lemma mixture_sqrt_difference_le (f g a d : ℝ) (ha : 0 < a)
    (hf : a ≤ f) (hg : a ≤ g) (_hd : 0 ≤ d) (hfg : |f - g| ≤ d) :
    (Real.sqrt f - Real.sqrt g) ^ 2 ≤ d ^ 2/(4 * a) := by
  have hf0 := ha.le.trans hf
  have hg0 := ha.le.trans hg
  have hsf := Real.sq_sqrt hf0
  have hsg := Real.sq_sqrt hg0
  have hsa := Real.sq_sqrt ha.le
  have hfl := Real.sqrt_le_sqrt hf
  have hgl := Real.sqrt_le_sqrt hg
  have hs : 4 * a ≤ (Real.sqrt f+Real.sqrt g) ^ 2 := by
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg f, Real.sqrt_nonneg g]
  have he : (Real.sqrt f-Real.sqrt g) ^ 2 * (Real.sqrt f+Real.sqrt g) ^ 2 = (f - g) ^ 2 := by
    calc
      _ = ((Real.sqrt f) ^ 2-(Real.sqrt g) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsf, hsg]
  have hsq : (f - g) ^ 2 ≤ d ^ 2 := by
    have := mul_self_le_mul_self (abs_nonneg (f - g)) hfg
    simpa only [← sq, sq_abs] using this
  apply (le_div_iff₀ (by positivity : 0 < 4 * a)).2
  calc
    _ ≤ (Real.sqrt f-Real.sqrt g) ^ 2 * (Real.sqrt f+Real.sqrt g) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = (f - g) ^ 2 := he
    _ ≤ d ^ 2 := hsq

/-- [The component density floor and mixed Taylor difference give the exact
M⁴ m⁴ 8ᵐ coefficient used by the mixture roadmap. The fair difference bound is
smaller and can use this same result. [the documented result](goal) Under [the stated assumptions](hyp:hf,hg,hfg). -/
-- @node: mixture_component_pointwise_bound
lemma mixture_component_pointwise_bound (m : ℕ) (M ω f g : ℝ)
    (hf : ((2 : ℝ) ^ m)⁻¹ ≤ f) (hg : ((2 : ℝ) ^ m)⁻¹ ≤ g)
    (hfg : |f - g| ≤ 2 * M ^ 2 * (m : ℝ) ^ 2 * 2 ^ m * |ω|) :
    (Real.sqrt f-Real.sqrt g) ^ 2 ≤ M ^ 4 * (m : ℝ) ^ 4 * 8 ^ m * ω ^ 2 := by
  have h := mixture_sqrt_difference_le f g ((2 : ℝ) ^ m)⁻¹
    (2 * M ^ 2 * (m : ℝ) ^ 2 * 2 ^ m * |ω|) (by positivity) hf hg (by positivity) hfg
  apply h.trans_eq
  have hp : (8 : ℝ) ^ m = (2 : ℝ) ^ m * (2 : ℝ) ^ m * (2 : ℝ) ^ m := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  rw [hp]
  field_simp
  simp only [sq_abs]
  ring

/-- [Integrating the component pointwise estimate against its probability
reference preserves its coefficient. No independence inside a component is used. [the documented result](goal) Under [the stated assumptions](hyp:μ,f,g,hf,hg,hfg). -/
-- @node: mixture_component_hellinger_bound
lemma mixture_component_hellinger_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ) (M ω : ℝ) (f g : Ω → ℝ)
    (hf : ∀ x, ((2 : ℝ) ^ m)⁻¹ ≤ f x) (hg : ∀ x, ((2 : ℝ) ^ m)⁻¹ ≤ g x)
    (hfg : ∀ x, |f x - g x| ≤ 2 * M ^ 2 * (m : ℝ) ^ 2 * 2 ^ m * |ω|) :
    Causalean.Stat.hellingerSqDensity μ f g ≤ M ^ 4 * (m : ℝ) ^ 4 * 8 ^ m * ω ^ 2 := by
  unfold Causalean.Stat.hellingerSqDensity
  calc
    _ ≤ ∫ _x : Ω, M ^ 4 * (m : ℝ) ^ 4 * 8 ^ m * ω ^ 2 ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _))
        (integrable_const _) (Filter.Eventually.of_forall (fun x =>
          mixture_component_pointwise_bound m M ω (f x) (g x) (hf x) (hg x) (hfg x)))
    _ = _ := by simp

/-- [Affinities of normalized integrable nonnegative densities lie in [0,1].
The upper bound follows from the nonnegative Hellinger discrepancy identity. [the documented result](goal) Under [the stated assumptions](hyp:μ,f,g,hf,hg,hf0,hg0,hf1,hg1). -/
-- @node: mixture_affinity_bounds
lemma mixture_affinity_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf1 : ∫ x, f x ∂μ = 1) (hg1 : ∫ x, g x ∂μ = 1) :
    0 ≤ Causalean.Stat.densityAffinity μ f g ∧
      Causalean.Stat.densityAffinity μ f g ≤ 1 := by
  refine ⟨integral_nonneg (fun x => Real.sqrt_nonneg _), ?_⟩
  have hn : 0 ≤ Causalean.Stat.hellingerSqDensity μ f g :=
    integral_nonneg (fun x => sq_nonneg _)
  rw [Causalean.Stat.hellingerSqDensity_eq_two_mul_one_sub_affinity μ f g
    hf hg hf0 hg0 hf1 hg1] at hn
  linarith

/-- [For conditionally independent components, the full Hellinger discrepancy
is at most the sum of the component discrepancies. This combines the library's
exact tensorized affinity with its finite product defect inequality. [the documented result](goal) Under [the stated assumptions](hyp:μ,f,g,hf,hg,hf0,hg0,hf1,hg1). -/
-- @node: mixture_hellinger_tensor_le_sum
lemma mixture_hellinger_tensor_le_sum {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (μ i)]
    (f g : ∀ i, Ω i → ℝ) (hf : ∀ i, Integrable (f i) (μ i))
    (hg : ∀ i, Integrable (g i) (μ i))
    (hf0 : ∀ i x, 0 ≤ f i x) (hg0 : ∀ i x, 0 ≤ g i x)
    (hf1 : ∀ i, ∫ x, f i x ∂μ i = 1) (hg1 : ∀ i, ∫ x, g i x ∂μ i = 1) :
    Causalean.Stat.hellingerSqDensity (Measure.pi μ)
      (fun x => ∏ i, f i (x i)) (fun x => ∏ i, g i (x i)) ≤
      ∑ i, Causalean.Stat.hellingerSqDensity (μ i) (f i) (g i) := by
  have hF : Integrable (fun x => ∏ i, f i (x i)) (Measure.pi μ) :=
    Integrable.fintype_prod_dep hf
  have hG : Integrable (fun x => ∏ i, g i (x i)) (Measure.pi μ) :=
    Integrable.fintype_prod_dep hg
  have hF0 : ∀ x : (∀ i, Ω i), 0 ≤ ∏ i, f i (x i) := fun x => Finset.prod_nonneg (fun i _ => hf0 i (x i))
  have hG0 : ∀ x : (∀ i, Ω i), 0 ≤ ∏ i, g i (x i) := fun x => Finset.prod_nonneg (fun i _ => hg0 i (x i))
  have hF1 : ∫ x, (∏ i, f i (x i)) ∂Measure.pi μ = 1 := by
    rw [integral_fintype_prod_eq_prod]
    simp [hf1]
  have hG1 : ∫ x, (∏ i, g i (x i)) ∂Measure.pi μ = 1 := by
    rw [integral_fintype_prod_eq_prod]
    simp [hg1]
  rw [Causalean.Stat.hellingerSqDensity_eq_two_mul_one_sub_affinity
    (Measure.pi μ) _ _ hF hG hF0 hG0 hF1 hG1,
    Causalean.Stat.densityAffinity_pi μ f g hf0 hg0]
  have hb := fun i => mixture_affinity_bounds (μ i) (f i) (g i)
    (hf i) (hg i) (hf0 i) (hg0 i) (hf1 i) (hg1 i)
  calc
    _ ≤ 2 * ∑ i, (1-Causalean.Stat.densityAffinity (μ i) (f i) (g i)) :=
      mul_le_mul_of_nonneg_left (Causalean.Stat.one_sub_prod_le_sum _
        (fun i => (hb i).1) (fun i => (hb i).2)) (by norm_num)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (Causalean.Stat.hellingerSqDensity_eq_two_mul_one_sub_affinity
        (μ i) (f i) (g i) (hf i) (hg i) (hf0 i) (hg0 i) (hf1 i) (hg1 i)).symm

/-- [Exact singleton matching removes those components from the conditional
Hellinger bound, leaving precisely the weighted sum over components of size at least two. [the documented result](goal) Under [the stated assumptions](hyp:μ,f,g,hf,hg,hf1,hg1,hm,hflo,hglo,hSingleton,hDifference). -/
-- @node: mixture_hellinger_tensor_without_singletons
lemma mixture_hellinger_tensor_without_singletons {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f g : ∀ i, Ω i → ℝ) (m : ι → ℕ) (M ω : ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (hg : ∀ i, Integrable (g i) (μ i))
    (hf1 : ∀ i, ∫ x, f i x ∂μ i = 1) (hg1 : ∀ i, ∫ x, g i x ∂μ i = 1)
    (hm : ∀ i, 1 ≤ m i)
    (hflo : ∀ i x, ((2 : ℝ) ^ (m i))⁻¹ ≤ f i x)
    (hglo : ∀ i x, ((2 : ℝ) ^ (m i))⁻¹ ≤ g i x)
    (hSingleton : ∀ i, m i = 1 → f i = g i)
    (hDifference : ∀ i, 2 ≤ m i → ∀ x,
      |f i x - g i x| ≤ 2 * M ^ 2 * (m i : ℝ) ^ 2 * 2 ^ (m i) * |ω|) :
    Causalean.Stat.hellingerSqDensity (Measure.pi μ)
      (fun x => ∏ i, f i (x i)) (fun x => ∏ i, g i (x i)) ≤
      M ^ 4 * ω ^ 2 * ∑ i ∈ Finset.univ.filter (fun i => 2 ≤ m i),
        (m i : ℝ) ^ 4 * 8 ^ (m i) := by
  classical
  have hf0 : ∀ i x, 0 ≤ f i x := fun i x =>
    (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ (m i))⁻¹).trans (hflo i x)
  have hg0 : ∀ i x, 0 ≤ g i x := fun i x =>
    (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ (m i))⁻¹).trans (hglo i x)
  apply (mixture_hellinger_tensor_le_sum μ f g hf hg hf0 hg0 hf1 hg1).trans
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => 2 ≤ m i),
        Causalean.Stat.hellingerSqDensity (μ i) (f i) (g i) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hn
      have hmi : m i = 1 := by
        have : ¬ 2 ≤ m i := by simpa only [Finset.mem_filter, hi, true_and] using hn
        have := hm i
        omega
      rw [hSingleton i hmi]
      simp [Causalean.Stat.hellingerSqDensity]
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => 2 ≤ m i),
        M ^ 4 * (m i : ℝ) ^ 4 * 8 ^ (m i) * ω ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mixture_component_hellinger_bound (μ i) (m i) M ω (f i) (g i)
        (hflo i) (hglo i) (hDifference i (Finset.mem_filter.mp hi).2)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

/-- [A polynomial tail majorant proves the finite cubic geometric sum bound
in the occupancy roadmap. It avoids differentiating an infinite power series. [the documented result](goal) Under [the stated assumptions](hyp:hq0,hq). -/
-- @node: mixture_cubic_geometric_tail
lemma mixture_cubic_geometric_tail (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4)
    (a N : ℕ) :
    ∑ j ∈ Finset.range N, (((a+j : ℕ) : ℝ) + 2) ^ 3 * q ^ j ≤
      2 * (a : ℝ) ^ 3+12 * (a : ℝ) ^ 2+30 * (a : ℝ)+32 := by
  induction N generalizing a with
  | zero => simp only [Finset.range_zero, Nat.cast_add, Finset.sum_empty]; positivity
  | succ N ih =>
    rw [Finset.sum_range_succ']
    have hShift : (∑ j ∈ Finset.range N, (((a+(j+1) : ℕ) : ℝ) + 2) ^ 3 * q ^ (j+1)) =
        q * ∑ j ∈ Finset.range N, ((((a+1)+j : ℕ) : ℝ) + 2) ^ 3 * q ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [pow_succ, Nat.add_assoc, Nat.add_comm 1 j]
      ring
    rw [hShift]
    have hP : 0 ≤ 2 * ((a+1 : ℕ) : ℝ) ^ 3+12 * ((a+1 : ℕ) : ℝ) ^ 2+
        30 * ((a+1 : ℕ) : ℝ)+32 := by positivity
    have hA : 0 ≤ (a : ℝ) := by positivity
    have hA3 : 0 ≤ (a : ℝ) ^ 3 := by positivity
    have h1 := mul_le_mul_of_nonneg_left (ih (a+1)) hq0
    have h2 := mul_le_mul_of_nonneg_right hq hP
    push_cast at h1 h2 ⊢
    simp only [pow_zero, mul_one, add_zero] at *
    nlinarith [sq_nonneg (a : ℝ)]

/-- [At occupancy parameter at most one quarter, the finite non-singleton
cubic series is bounded by 32 times that parameter, as in the paper. [the documented result](goal) Under [the stated assumptions](hyp:hq0,hq). -/
-- @node: mixture_cubic_geometric_bound
lemma mixture_cubic_geometric_bound (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4) (N : ℕ) :
    ∑ j ∈ Finset.range N, ((j : ℝ)+2) ^ 3 * q ^ (j+1) ≤ 32 * q := by
  have h := mixture_cubic_geometric_tail q hq0 hq 0 N
  simp only [Nat.cast_zero, zero_pow (by decide : 3 ≠ 0),
    zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] at h
  calc
    _ = q * ∑ j ∈ Finset.range N, ((j : ℝ)+2) ^ 3 * q ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring
    _ ≤ q * 32 := mul_le_mul_of_nonneg_left h hq0
    _ = _ := mul_comm _ _

end CausalSmith.Stat.LogoddsLowsmoothFrontier

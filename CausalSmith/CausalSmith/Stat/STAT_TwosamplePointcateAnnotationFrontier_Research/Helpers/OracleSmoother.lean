module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Estimator
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.CitedGates
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.LocalPolynomial
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.UpperAssembly
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.FuzzyBlockTesting
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.OracleBlockInformation

/-!
# Oracle smoother primitives

Explicit supplied-propensity smoothing, bounded record moments, full-window
Legendre geometry, and bandwidth identities for the oracle upper-risk proof.
-/

@[expose] public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


/-- Explicit clipped known-design degree-two smoother of the inverse-propensity pseudo-outcome.  Given [the specified input d](hyp:d), [the specified input gamma](hyp:gamma), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input w](hyp:w), [the specified input e](hyp:e), [oracle smoother](goal) is the corresponding construction. -/
def oracleSmoother (d : ℕ) (gamma : ℝ) (n m : ℕ)
    (w : Sample d n m) (e : Cov d → ℝ) : ℝ :=
  let h := (n:ℝ)^(-(1/(2*gamma+d)))
  clip ((n:ℝ)⁻¹ * ∑ i : Fin n,
    locWeight h (w.1.1 i).1 * (∑ u : PolyIdx d, r0 d h u * coarseBasis h (w.1.1 i).1 u) *
      (bit (w.1.1 i).2.1 * bit (w.1.1 i).2.2 / e (w.1.1 i).1 -
        (1-bit (w.1.1 i).2.1) * bit (w.1.1 i).2.2 / (1-e (w.1.1 i).1)))
/-- The inverse-propensity response is a bounded signed binary outcome under overlap.  Given [the specified input a](hyp:a), [the specified input y](hyp:y), [the specified input e](hyp:e), [the specified input he](hyp:he), [the specified input he'](hyp:he'), [the overlap level eps](hyp:eps), [the oracle binary response bound conclusion](goal) holds. -/
lemma oracle_binary_response_bound (a y : Bool) (e eps : ℝ) (heps : 0 < eps)
    (he : eps ≤ e) (he' : e ≤ 1 - eps) :
    |bit a * bit y / e - (1-bit a) * bit y / (1-e)| ≤ eps⁻¹ := by
  have hp : 0 < e := by linarith
  have hq : 0 < 1-e := by linarith
  have hi : 1/e ≤ eps⁻¹ := by rw [one_div]; exact inv_anti₀ heps he
  have hj : 1/(1-e) ≤ eps⁻¹ := by rw [one_div]; exact inv_anti₀ heps (by linarith)
  have hk : (0:ℝ) ≤ eps⁻¹ := inv_nonneg.mpr heps.le
  cases a <;> cases y <;>
    simp only [bit, Bool.false_eq_true, if_false, if_true, zero_mul, one_mul,
      sub_zero, sub_self, zero_div, zero_sub, abs_neg, abs_zero,
      abs_of_nonneg (by positivity : 0 ≤ 1/e),
      abs_of_nonneg (by positivity : 0 ≤ 1/(1-e))] <;> first | exact hi | exact hj | exact hk | norm_num

/-- The zero extension of the supplied propensity also preserves the global response bound.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input z](hyp:z), [the oracle designated response bound conclusion](goal) holds. -/
lemma oracle_designated_response_bound {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (z : Cov d × Bool × Bool) :
    |bit z.2.1 * bit z.2.2 / designatedPropensity P hP z.1 -
      (1-bit z.2.1) * bit z.2.2 / (1-designatedPropensity P hP z.1)| ≤ eps⁻¹ := by
  have heps := hP.eps_pos
  have hhalf := hP.eps_le_half
  by_cases hx : z.1 ∈ cube d
  · have he := (canonicalLaw_spec P hP).2.2.2.1.2 z.1 hx
    apply oracle_binary_response_bound _ _ _ eps heps
    · simpa only [designatedPropensity, if_pos hx] using he.1
    · simpa only [designatedPropensity, if_pos hx] using he.2
  · have h1 : (1:ℝ) ≤ eps⁻¹ := by
      rw [← one_div, le_div_iff₀ heps]; linarith
    simp only [designatedPropensity, if_neg hx, div_zero, sub_zero, div_one, zero_sub, abs_neg]
    rcases z with ⟨x, a, y⟩
    cases a <;> cases y <;> norm_num [bit] <;> linarith

/-- The evaluation kernel has a uniform bound on the localized cube.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the oracle evaluation kernel bound conclusion](goal) holds. -/
lemma oracle_evaluation_kernel_bound (d : ℕ) (h : ℝ) (hh : 0 < h)
    (x : Cov d) (hx : x ∈ locCube d h) :
    |∑ u : PolyIdx d, r0 d h u * coarseBasis h x u| ≤
      (Fintype.card (PolyIdx d):ℝ) * ((4:ℝ)^d)^2 := by
  have hc : x0 d ∈ locCube d h := by
    intro i
    change (1/2:ℝ) ∈ Icc (1/2-h/2) (1/2+h/2)
    constructor <;> linarith
  calc
    _ ≤ ∑ u : PolyIdx d, |r0 d h u * coarseBasis h x u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u : PolyIdx d, ((4:ℝ)^d)^2 := by
      apply Finset.sum_le_sum
      intro u _
      rw [abs_mul, pow_two]
      exact mul_le_mul (coarseBasis_abs_bound d h hh (x0 d) hc u)
        (coarseBasis_abs_bound d h hh x hx u) (abs_nonneg _) (by positivity)
    _ = _ := by simp

/-- Every localized oracle summand has finite moments, before averaging or clipping.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input Z](hyp:Z), [the specified input hZ](hyp:hZ), [the oracle summand mem lp top conclusion](goal) holds. -/
lemma oracle_summand_memLp_top {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (hh : 0 < h) (Z : Ω → Cov d × Bool × Bool) (hZ : Measurable Z) :
    MemLp (fun w => locWeight h (Z w).1 *
      ((∑ u : PolyIdx d, r0 d h u * coarseBasis h (Z w).1 u) *
        (bit (Z w).2.1 * bit (Z w).2.2 / designatedPropensity P hP (Z w).1 -
          (1-bit (Z w).2.1) * bit (Z w).2.2 / (1-designatedPropensity P hP (Z w).1)))) ∞ μ := by
  apply population_localized_record_memLp μ d h hh (fun w => (Z w).1)
    (by fun_prop) _ (by fun_prop)
    ((Fintype.card (PolyIdx d):ℝ) * ((4:ℝ)^d)^2 * eps⁻¹) (by have := hP.eps_pos; positivity)
  intro w hw
  rw [abs_mul]
  exact mul_le_mul (oracle_evaluation_kernel_bound d h hh (Z w).1 hw)
    (oracle_designated_response_bound P hP (Z w)) (abs_nonneg _) (by positivity)

/-- Oracle windows up to unit side length remain in the known-design cube.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the oracle loc cube subset cube conclusion](goal) holds. -/
lemma oracle_locCube_subset_cube (d : ℕ) (h : ℝ) (hh : h ≤ 1) :
    locCube d h ⊆ cube d := by
  intro x hx i
  constructor <;> linarith [(hx i).1, (hx i).2]

/-- Known-design weighted integration equals localization for the full oracle window.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input f](hyp:f), [the oracle uniform localization integral conclusion](goal) holds. -/
lemma oracle_uniform_localization_integral (d : ℕ) (h : ℝ)
    (hh : 0 < h) (hh' : h ≤ 1) (f : Cov d → ℝ) :
    (∫ x, locWeight h x * f x ∂uniformLaw d) = ∫ x, f x ∂locLaw d h := by
  have hfun : (fun x => locWeight h x * f x) =
      (locCube d h).indicator (fun x => h^(-(d:ℝ)) * f x) := by
    funext x
    by_cases hx : x ∈ locCube d h <;> simp [locWeight, hx]
  rw [hfun, integral_indicator (isClosed_locCube d h).measurableSet]
  unfold uniformLaw locLaw
  rw [Measure.restrict_restrict (isClosed_locCube d h).measurableSet,
    Set.inter_eq_left.mpr (oracle_locCube_subset_cube d h hh'),
    integral_const_mul, integral_smul_measure]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hh.le _)]
  rfl

/-- Coarse Legendre orthonormality is a scaling identity for every positive window.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input u](hyp:u), [the specified input v](hyp:v), [the oracle coarse orthonormal conclusion](goal) holds. -/
lemma oracle_coarse_orthonormal (d : ℕ) (h : ℝ) (hh : 0 < h) (u v : PolyIdx d) :
    (∫ x, coarseBasis h x u * coarseBasis h x v ∂locLaw d h) =
      if u = v then 1 else 0 := by
  rw [locLaw, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
  simp only [coarseBasis, ← Finset.prod_mul_distrib]
  rw [locCube, euclidean_box_product_integral d (1/2-h/2) (1/2+h/2)
    (fun i x => legendre (u.1 i) ((x-1/2)/h) * legendre (v.1 i) ((x-1/2)/h))]
  simp only [smul_eq_mul]
  have hk (w : PolyIdx d) (i : Fin d) : w.1 i ≤ 2 :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (w.1 j)) (Finset.mem_univ i)).trans w.2
  simp_rw [scaled_legendre_orthogonality h hh _ _ (hk u _) (hk v _)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hnorm : h ^ (-(d:ℝ)) * h^d = 1 := by
    rw [Real.rpow_neg hh.le, Real.rpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hh.ne')]
  rw [← mul_assoc, hnorm, one_mul]
  by_cases huv : u = v
  · subst v
    simp
  · rw [if_neg huv]
    have hne : ∃ i, u.1 i ≠ v.1 i := by
      by_contra hn
      apply huv
      apply Subtype.ext
      funext i
      exact not_ne_iff.mp (not_exists.mp hn i)
    obtain ⟨i, hi⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Full-window coarse coordinates are square integrable by their orthonormal norms.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input u](hyp:u), [the oracle coarse basis mem lp conclusion](goal) holds. -/
lemma oracle_coarseBasis_memLp (d : ℕ) (h : ℝ) (hh : 0 < h) (u : PolyIdx d) :
    MemLp (fun x => coarseBasis h x u) 2 (locLaw d h) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  by_contra hi
  have hz := integral_undef hi
  have ho := oracle_coarse_orthonormal d h hh u u
  simp only [ite_true, ← pow_two] at ho
  rw [hz] at ho
  norm_num at ho

/-- The squared oracle evaluation-kernel norm is the sum of squared target coordinates.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the oracle evaluation kernel square integral conclusion](goal) holds. -/
lemma oracle_evaluation_kernel_square_integral (d : ℕ) (h : ℝ) (hh : 0 < h) :
    (∫ x, (∑ u : PolyIdx d, r0 d h u * coarseBasis h x u)^2 ∂locLaw d h) =
      ∑ u : PolyIdx d, (r0 d h u)^2 := by
  simp_rw [mul_comm (r0 d h _) (coarseBasis h _ _)]
  exact finite_orthonormal_square_norm (locLaw d h) (fun u x => coarseBasis h x u)
    (oracle_coarseBasis_memLp d h hh) (fun i j => by
      have ho := oracle_coarse_orthonormal d h hh i j
      by_cases hij : i = j
      · simp only [if_pos hij] at ho ⊢; exact ho
      · simp only [if_neg hij] at ho ⊢; exact ho) (r0 d h)

/-- Uniform-design scaling gives the exact squared weighted-kernel energy.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the oracle weighted kernel square integral conclusion](goal) holds. -/
lemma oracle_weighted_kernel_square_integral (d : ℕ) (h : ℝ)
    (hh : 0 < h) (hh' : h ≤ 1) :
    (∫ x, (locWeight h x *
      (∑ u : PolyIdx d, r0 d h u * coarseBasis h x u))^2 ∂uniformLaw d) =
      h^(-(d:ℝ)) * ∑ u : PolyIdx d, (r0 d h u)^2 := by
  have he (x : Cov d) : (locWeight h x *
      (∑ u : PolyIdx d, r0 d h u * coarseBasis h x u))^2 =
      locWeight h x * (h^(-(d:ℝ)) *
        (∑ u : PolyIdx d, r0 d h u * coarseBasis h x u)^2) := by
    by_cases hx : x ∈ locCube d h
    · simp only [locWeight, if_pos hx]; ring
    · simp only [locWeight, if_neg hx, zero_mul, zero_pow (by norm_num : 2 ≠ 0)]
  simp_rw [he]
  rw [oracle_uniform_localization_integral d h hh hh', integral_const_mul,
    oracle_evaluation_kernel_square_integral d h hh]

/-- Bounded pseudo-outcomes and the exact kernel energy bound the oracle record second moment.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input Z](hyp:Z), [the specified input hZ](hyp:hZ), [the specified input hdesign](hyp:hdesign), [the oracle summand second moment bound conclusion](goal) holds. -/
lemma oracle_summand_second_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1)
    (Z : Ω → Cov d × Bool × Bool) (hZ : Measurable Z)
    (hdesign : μ.map (fun w => (Z w).1) = uniformLaw d) :
    (∫ w, (locWeight h (Z w).1 *
      ((∑ u : PolyIdx d, r0 d h u * coarseBasis h (Z w).1 u) *
        (bit (Z w).2.1 * bit (Z w).2.2 / designatedPropensity P hP (Z w).1 -
          (1-bit (Z w).2.1) * bit (Z w).2.2 / (1-designatedPropensity P hP (Z w).1))))^2 ∂μ) ≤
      eps⁻¹^2 * (h^(-(d:ℝ)) * ∑ u : PolyIdx d, (r0 d h u)^2) := by
  let K := fun x : Cov d => ∑ u : PolyIdx d, r0 d h u * coarseBasis h x u
  let R := fun w => bit (Z w).2.1 * bit (Z w).2.2 / designatedPropensity P hP (Z w).1 -
    (1-bit (Z w).2.1) * bit (Z w).2.2 / (1-designatedPropensity P hP (Z w).1)
  have hk : MemLp (fun w => locWeight h (Z w).1 * K (Z w).1) ∞ μ := by
    apply population_localized_record_memLp μ d h hh (fun w => (Z w).1)
      (by fun_prop) _ (by dsimp [K]; fun_prop)
      ((Fintype.card (PolyIdx d):ℝ) * ((4:ℝ)^d)^2) (by positivity)
    intro w hw
    exact oracle_evaluation_kernel_bound d h hh (Z w).1 hw
  have hki := (hk.mono_exponent (show (2:ℝ≥0∞) ≤ ∞ from le_top)).integrable_sq
  have hsi := ((oracle_summand_memLp_top μ P hP h hh Z hZ).mono_exponent
    (show (2:ℝ≥0∞) ≤ ∞ from le_top)).integrable_sq
  have hpoint (w : Ω) : (locWeight h (Z w).1 * (K (Z w).1 * R w))^2 ≤
      eps⁻¹^2 * (locWeight h (Z w).1 * K (Z w).1)^2 := by
    have hb : |R w| ≤ eps⁻¹ := oracle_designated_response_bound P hP (Z w)
    have hr : (R w)^2 ≤ eps⁻¹^2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    calc
      _ = (locWeight h (Z w).1 * K (Z w).1)^2 * (R w)^2 := by ring
      _ ≤ (locWeight h (Z w).1 * K (Z w).1)^2 * eps⁻¹^2 :=
        mul_le_mul_of_nonneg_left hr (sq_nonneg _)
      _ = _ := by ring
  have hm := integral_map (μ := μ) (by fun_prop : AEMeasurable (fun w => (Z w).1) μ)
    (f := fun x => (locWeight h x * K x)^2) (by dsimp [K]; fun_prop)
  rw [hdesign] at hm
  calc
    _ ≤ ∫ w, eps⁻¹^2 * (locWeight h (Z w).1 * K (Z w).1)^2 ∂μ :=
      integral_mono hsi (hki.const_mul (eps⁻¹^2)) hpoint
    _ = _ := by
      rw [integral_const_mul, ← hm]
      exact congrArg (fun t : ℝ => eps⁻¹^2*t) (oracle_weighted_kernel_square_integral d h hh hh')

/-- The oracle bandwidth is positive and its whole support fits in the design cube.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input gamma](hyp:gamma), [the specified input hn](hyp:hn), [the specified input hg](hyp:hg), [the oracle bandwidth bounds conclusion](goal) holds. -/
lemma oracle_bandwidth_bounds (d n : ℕ) (gamma : ℝ)
    (hn : 2 ≤ n) (hg : 1 ≤ gamma) :
    0 < (n:ℝ)^(-(1/(2*gamma+d))) ∧ (n:ℝ)^(-(1/(2*gamma+d))) ≤ 1 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hD : 0 < 2*gamma+d := by linarith
  refine ⟨Real.rpow_pos_of_pos hn0 _, ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (by positivity))

/-- At the oracle bandwidth the Taylor remainder has exactly the oracle rate.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input gamma](hyp:gamma), [the specified input hn](hyp:hn), [the oracle bandwidth bias identity conclusion](goal) holds. -/
lemma oracle_bandwidth_bias_identity (d n : ℕ) (gamma : ℝ) (hn : 0 < n) :
    ((n:ℝ)^(-(1/(2*gamma+d))))^gamma = oracleRate d gamma n := by
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  unfold oracleRate
  congr 1
  ring

/-- The oracle bandwidth also balances the stochastic standard-deviation term exactly.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input gamma](hyp:gamma), [the specified input hn](hyp:hn), [the specified input hg](hyp:hg), [the oracle bandwidth sampling identity conclusion](goal) holds. -/
lemma oracle_bandwidth_sampling_identity (d n : ℕ) (gamma : ℝ)
    (hn : 0 < n) (hg : 1 ≤ gamma) :
    ((n:ℝ)*((n:ℝ)^(-(1/(2*gamma+d))))^d)^(-(1/2:ℝ)) =
      oracleRate d gamma n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hD : 0 < 2*gamma+d := by nlinarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
  conv_lhs => arg 1; arg 1; rw [← Real.rpow_one (n:ℝ)]
  rw [← Real.rpow_add hn0, ← Real.rpow_mul hn0.le]
  unfold oracleRate
  congr 1
  field_simp
  <;> ring

/-- Given [dimension d](hyp:d), [smoothness γ](hyp:gamma), [sample sizes n and m](hyp:n,m), and [a Borel supplied propensity e](hyp:he), [the explicit oracle smoother is Borel](goal). -/
@[fun_prop] lemma measurable_oracleSmoother (d : ℕ) (gamma : ℝ) (n m : ℕ)
    (e : Cov d → ℝ) (he : Measurable e) :
    Measurable (fun w : Sample d n m => oracleSmoother d gamma n m w e) := by
  unfold oracleSmoother clip
  fun_prop

/-- For [a primitive law P](hyp:P) [in the model class](hyp:hP) at [overlap level eps](hyp:eps) and [sample sizes n and m](hyp:n,m), [the oracle smoother using its designated propensity is Borel](goal). -/
@[fun_prop] lemma measurable_oracleSmoother_designated {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) (n m : ℕ) :
    Measurable (fun w => oracleSmoother d gamma n m w (designatedPropensity P hP)) := by
  fun_prop

/-- Clipping bounds the smoother on every dataset, including inputs outside the model support.  Given [the specified input d](hyp:d), [the specified input gamma](hyp:gamma), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input w](hyp:w), [the specified input e](hyp:e), [the oracle smoother bounded conclusion](goal) holds. -/
lemma oracleSmoother_bounded (d : ℕ) (gamma : ℝ) (n m : ℕ)
    (w : Sample d n m) (e : Cov d → ℝ) :
    |oracleSmoother d gamma n m w e| ≤ 1 := by
  unfold oracleSmoother clip
  dsimp only
  apply abs_le.mpr
  constructor
  · simpa only [neg_div] using (le_max_left (-1 : ℝ) _)
  · exact max_le (by norm_num) (min_le_left _ _)

/-- The oracle decision space requires a Borel section for every supplied function.
The zero branch makes the explicit smoother a total admissible rule.  Given [the specified input d](hyp:d), [the specified input gamma](hyp:gamma), [the specified input n](hyp:n), [the specified input m](hyp:m), [oracle smoother decision](goal) is the corresponding construction. -/
def oracleSmootherDecision (d : ℕ) (gamma : ℝ) (n m : ℕ) : OracleDecision d n m :=
  ⟨fun w e => if Measurable e then oracleSmoother d gamma n m w e else 0, by
    intro e
    by_cases he : Measurable e
    · simp only [if_pos he]
      exact measurable_oracleSmoother d gamma n m e he
    · simp only [if_neg he]
      fun_prop⟩

/-- The total oracle rule agrees with the stipulated smoother on every class member.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input w](hyp:w), [the oracle smoother decision designated conclusion](goal) holds. -/
lemma oracleSmootherDecision_designated {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) (n m : ℕ)
    (w : Sample d n m) :
    (oracleSmootherDecision d gamma n m).1 w (designatedPropensity P hP) =
      oracleSmoother d gamma n m w (designatedPropensity P hP) := by
  simp only [oracleSmootherDecision, if_pos (measurable_designatedPropensity P hP)]

/-- A uniform risk bound for the explicit smoother transfers to oracle minimax risk
by using its total Borel extension as the candidate decision.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input B](hyp:B), [the specified input hbound](hyp:hbound), [the oracle risk le of oracle smoother conclusion](goal) holds. -/
lemma oracleRisk_le_of_oracleSmoother (d : ℕ) (alpha beta gamma L eps : ℝ) (n m : ℕ)
    (B : ℝ≥0∞)
    (hbound : ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
      (∫⁻ w, ENNReal.ofReal
        |oracleSmoother d gamma n m w (designatedPropensity P hP) - tau P hP (x0 d)|
        ∂experiment P n m) ≤ B) :
    oracleRisk d alpha beta gamma L eps n m ≤ B := by
  unfold oracleRisk
  apply (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk
    (oracleSmootherDecision d gamma n m)).trans
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro P
  simp only [oracleSmootherDecision_designated]
  exact hbound P.1 P.2


end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

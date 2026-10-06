module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.Density
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Exact Taylor cancellation for the contraction argument

Taylor expansion at zero works on either side of zero with the exact factorial
constant. Matching moments cancel its finite polynomial; only the remainders
contribute to a difference of supported prior means.
-/

public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Assume [the stated hf condition](hyp:hf) and [the stated hu condition](hyp:hu). [On a nondegenerate interval, the Taylor polynomial of a globally smooth function uses its ordinary derivatives, including at an endpoint](goal). -/
-- @node: taylorWithinEval_zero_eq_sum
lemma taylorWithinEval_zero_eq_sum (f : ℝ → ℝ) (k : ℕ)
    (hf : ContDiff ℝ k f) (u : ℝ) (hu : u ≠ 0) :
    taylorWithinEval f k (Set.uIcc 0 u) 0 u =
      ∑ q ∈ Finset.range (k + 1), iteratedDeriv q f 0 / (q.factorial : ℝ) * u^q := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro q hq
  rw [iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_uIcc (Ne.symm hu))
    ((hf.of_le (by exact_mod_cast (show q ≤ k by simpa using Finset.mem_range.mp hq))).contDiffAt)
    Set.left_mem_uIcc]
  simp only [sub_zero, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Assume [the stated hk condition](hyp:hk), [the stated hf condition](hyp:hf), [nonnegative amplitude](hyp:ha), [the stated hu condition](hyp:hu), [a nonnegative bias bound](hyp:_hB), and [the stated hderiv condition](hyp:hderiv). [A uniform kth derivative bound gives the exact Taylor remainder bound at zero, for positive and negative coordinates alike](goal). -/
-- @node: coordinate_taylor_remainder_abs_le
lemma coordinate_taylor_remainder_abs_le (f : ℝ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hf : ContDiff ℝ k f) (a B u : ℝ) (ha : 0 ≤ a)
    (hu : u ∈ Set.Icc (-a) a) (_hB : 0 ≤ B)
    (hderiv : ∀ x ∈ Set.Icc (-a) a,
      |iteratedDeriv k f x| ≤ (k.factorial : ℝ) * B) :
    |f u - ∑ q ∈ Finset.range k,
      iteratedDeriv q f 0 / (q.factorial : ℝ) * u^q| ≤ |u|^k * B := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  by_cases hu0 : u = 0
  · subst u
    simp [Finset.sum_range_succ', iteratedDeriv_zero]
  have hsegment : Set.uIcc 0 u ⊆ Set.Icc (-a) a :=
    Set.uIcc_subset_Icc (by constructor <;> linarith) hu
  obtain ⟨x, hx, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (n := l) (Ne.symm hu0) hf.contDiffOn
  rw [taylorWithinEval_zero_eq_sum f l (hf.of_le (by exact_mod_cast Nat.le_succ l)) u hu0,
    sub_zero] at heq
  rw [heq, abs_div, abs_mul, abs_pow,
    abs_of_nonneg (a := ((l + 1).factorial : ℝ)) (by positivity)]
  calc
    |iteratedDeriv (l + 1) f x| * |u|^(l + 1) / ((l + 1).factorial : ℝ) ≤
        (((l + 1).factorial : ℝ) * B) * |u|^(l + 1) / ((l + 1).factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right (hderiv x (hsegment ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
        (by positivity)
    _ = |u|^(l + 1) * B := by
      field_simp

/-- Assume [the stated hnu condition](hyp:hnu) and [the stated hf condition](hyp:hf). [Compactly supported probability priors integrate every continuous scalar coordinate function; no extra moment hypothesis is needed](goal). -/
-- @node: integrable_continuous_amplitudePrior
lemma integrable_continuous_amplitudePrior (a : ℝ) (nu : Measure ℝ)
    (hnu : AmplitudePrior a nu) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable f nu := by
  have : IsProbabilityMeasure nu := hnu.1
  have hmem : ∀ᵐ u ∂nu, u ∈ Set.Icc (-a) a := by
    rw [ae_iff]
    exact hnu.2
  have h := hf.integrableOn_Icc (μ := nu) (a := -a) (b := a)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hmem] at h

/-- Assume [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), and [the stated hmom condition](hyp:hmom). [Matching moments cancel any finite Taylor polynomial of degree below k](goal). -/
-- @node: matchingMoments_taylor_polynomial
lemma matchingMoments_taylor_polynomial (a : ℝ) (nu0 nu1 : Measure ℝ)
    (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1)
    (k : ℕ) (hmom : MatchingMoments k nu0 nu1) (c : ℕ → ℝ) :
    (∫ u, ∑ q ∈ Finset.range k, c q * u^q ∂nu0) =
      ∫ u, ∑ q ∈ Finset.range k, c q * u^q ∂nu1 := by
  have hint (nu : Measure ℝ) (hnu : AmplitudePrior a nu) (q : ℕ) :
      Integrable (fun u : ℝ => c q * u^q) nu :=
    integrable_continuous_amplitudePrior a nu hnu _ (by fun_prop)
  rw [integral_finsetSum _ (fun q _ => hint nu0 hnu0 q),
    integral_finsetSum _ (fun q _ => hint nu1 hnu1 q)]
  apply Finset.sum_congr rfl
  intro q hq
  rw [integral_const_mul, integral_const_mul, hmom q (Finset.mem_range.mp hq)]

/-- Assume [nonnegative amplitude](hyp:ha), [a nonnegative bias bound](hyp:hB), [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), [the stated hk condition](hyp:hk), [the stated hmom condition](hyp:hmom), [the stated hf condition](hyp:hf), and [the stated hderiv condition](hyp:hderiv). [A matched pair of supported priors differs only through Taylor remainders. The exact derivative bound yields twice the single-prior remainder radius](goal). -/
-- @node: matchingMoments_smooth_integral_sub_le
lemma matchingMoments_smooth_integral_sub_le (a B : ℝ) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (nu0 nu1 : Measure ℝ) (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1)
    (k : ℕ) (hk : 1 ≤ k) (hmom : MatchingMoments k nu0 nu1)
    (f : ℝ → ℝ) (hf : ContDiff ℝ k f)
    (hderiv : ∀ x ∈ Set.Icc (-a) a,
      |iteratedDeriv k f x| ≤ (k.factorial : ℝ) * B) :
    |(∫ u, f u ∂nu0) - (∫ u, f u ∂nu1)| ≤ 2 * a^k * B := by
  let T := fun u : ℝ => ∑ q ∈ Finset.range k,
    iteratedDeriv q f 0 / (q.factorial : ℝ) * u^q
  have hT : Continuous T := by fun_prop
  have hcancel : (∫ u, T u ∂nu0) = ∫ u, T u ∂nu1 :=
    matchingMoments_taylor_polynomial a nu0 nu1 hnu0 hnu1 k hmom _
  have hrem (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
      |∫ u, f u - T u ∂nu| ≤ a^k * B := by
    have : IsProbabilityMeasure nu := hnu.1
    have hi := integrable_continuous_amplitudePrior a nu hnu _ (hf.continuous.sub hT)
    have hmem : ∀ᵐ u ∂nu, u ∈ Set.Icc (-a) a := by
      rw [ae_iff]; exact hnu.2
    calc
      _ ≤ ∫ u, |f u - T u| ∂nu := abs_integral_le_integral_abs
      _ ≤ ∫ _u, a^k * B ∂nu := by
        apply integral_mono_ae hi.abs (integrable_const _)
        filter_upwards [hmem] with u hu
        exact (coordinate_taylor_remainder_abs_le f k hk hf a B u ha hu hB hderiv).trans
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (abs_nonneg u) (abs_le.mpr hu) k) hB)
      _ = a^k * B := by simp
  have heq : (∫ u, f u ∂nu0) - (∫ u, f u ∂nu1) =
      (∫ u, f u - T u ∂nu0) - (∫ u, f u - T u ∂nu1) := by
    rw [integral_sub (integrable_continuous_amplitudePrior a nu0 hnu0 f hf.continuous)
      (integrable_continuous_amplitudePrior a nu0 hnu0 T hT),
      integral_sub (integrable_continuous_amplitudePrior a nu1 hnu1 f hf.continuous)
      (integrable_continuous_amplitudePrior a nu1 hnu1 T hT), hcancel]
    ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith [hrem nu0 hnu0, hrem nu1 hnu1])

/-- Assume [the stated hc condition](hyp:hc). [Derivatives of a finite polynomial density family are integrable whenever its coefficients are integrable](goal). -/
-- @node: integrable_finitePolynomial_iteratedDeriv
lemma integrable_finitePolynomial_iteratedDeriv {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (m : ℕ) (c : Fin m → Ω → ℝ)
    (hc : ∀ q, Integrable (c q) mu) (k : ℕ) (u : ℝ) :
    Integrable (fun z => iteratedDeriv k (fun x : ℝ => ∑ q, c q z * x^q.val) u) mu := by
  have hexpand (z : Ω) :
      iteratedDeriv k (fun x : ℝ => ∑ q, c q z * x^q.val) u =
        ∑ q, c q z * iteratedDeriv k (fun x : ℝ => x^q.val) u := by
    rw [iteratedDeriv_fun_sum (by intro q _; fun_prop)]
    simp_rw [iteratedDeriv_const_mul_field]
  simp_rw [hexpand]
  exact integrable_finsetSum _ (fun q _ => (hc q).mul_const _)

/-- Assume [the stated hc condition](hyp:hc). [Coefficientwise integration commutes with every coordinate derivative of an integrable finite polynomial density family](goal). -/
-- @node: finitePolynomial_iteratedDeriv_integral
lemma finitePolynomial_iteratedDeriv_integral {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (m : ℕ) (c : Fin m → Ω → ℝ)
    (hc : ∀ q, Integrable (c q) mu) (k : ℕ) (u : ℝ) :
    iteratedDeriv k (fun x : ℝ => ∫ z, ∑ q, c q z * x^q.val ∂mu) u =
      ∫ z, iteratedDeriv k (fun x : ℝ => ∑ q, c q z * x^q.val) u ∂mu := by
  have hint (x : ℝ) : (∫ z, ∑ q, c q z * x^q.val ∂mu) =
      ∑ q, (∫ z, c q z ∂mu) * x^q.val := by
    rw [integral_finsetSum _ (fun q _ => (hc q).mul_const _)]
    simp_rw [integral_mul_const]
  simp_rw [hint]
  rw [iteratedDeriv_fun_sum (by intro q _; fun_prop)]
  simp_rw [iteratedDeriv_const_mul_field]
  have hexpand (z : Ω) :
      iteratedDeriv k (fun x : ℝ => ∑ q, c q z * x^q.val) u =
        ∑ q, c q z * iteratedDeriv k (fun x : ℝ => x^q.val) u := by
    rw [iteratedDeriv_fun_sum (by intro q _; fun_prop)]
    simp_rw [iteratedDeriv_const_mul_field]
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun q _ => (hc q).mul_const _)]
  simp_rw [integral_mul_const]

/-- Assume [the stated hc condition](hyp:hc), [the stated hk condition](hyp:hk), [nonnegative amplitude](hyp:ha), [the stated hu condition](hyp:hu), [a nonnegative bias bound](hyp:hB), and [the stated hderiv condition](hyp:hderiv). [A finite polynomial family with a uniform kth-derivative L1 bound has the exact coordinate Taylor remainder bound in L1. Testing against the sign of the remainder reduces the assertion to scalar Taylor's theorem, avoiding any parameter-dependent exceptional sets](goal). -/
-- @node: finitePolynomial_taylor_remainder_L1
lemma finitePolynomial_taylor_remainder_L1 {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (m : ℕ) (c : Fin m → Ω → ℝ)
    (hc : ∀ q, Integrable (c q) mu) (k : ℕ) (hk : 1 ≤ k)
    (a B u : ℝ) (ha : 0 ≤ a) (hu : u ∈ Set.Icc (-a) a) (hB : 0 ≤ B)
    (hderiv : ∀ x ∈ Set.Icc (-a) a,
      (∫ z, |iteratedDeriv k (fun t : ℝ => ∑ q, c q z * t^q.val) x| ∂mu) ≤
        (k.factorial : ℝ) * B) :
    (∫ z, |(∑ q, c q z * u^q.val) - ∑ v ∈ Finset.range k,
      iteratedDeriv v (fun t : ℝ => ∑ q, c q z * t^q.val) 0 /
        (v.factorial : ℝ) * u^v| ∂mu) ≤ |u|^k * B := by
  let F := fun x : ℝ => fun z : Ω => ∑ q, c q z * x^q.val
  let R := fun z : Ω => F u z - ∑ v ∈ Finset.range k,
    iteratedDeriv v (fun t => F t z) 0 / (v.factorial : ℝ) * u^v
  have hF (x : ℝ) : Integrable (F x) mu :=
    integrable_finsetSum _ (fun q _ => (hc q).mul_const _)
  have hD (v : ℕ) (x : ℝ) : Integrable (fun z => iteratedDeriv v (fun t => F t z) x) mu :=
    integrable_finitePolynomial_iteratedDeriv mu m c hc v x
  have hR : Integrable R mu := (hF u).sub (integrable_finsetSum _
    (fun v _ => ((hD v 0).div_const _).mul_const _))
  let g := fun z : Ω => R z / |R z|
  have hg : AEStronglyMeasurable g mu :=
    hR.aestronglyMeasurable.div₀ hR.abs.aestronglyMeasurable
  have hgb (z : Ω) : |g z| ≤ 1 := by
    dsimp [g]
    rw [abs_div, abs_abs]
    by_cases hz : R z = 0
    · simp [hz]
    · rw [div_self (abs_ne_zero.mpr hz)]
  have hgR (z : Ω) : g z * R z = |R z| := by
    dsimp [g]
    by_cases hz : R z = 0
    · simp [hz]
    · field_simp [abs_ne_zero.mpr hz]
      nlinarith [sq_abs (R z)]
  have hgc (q : Fin m) : Integrable (fun z => g z * c q z) mu :=
    (hc q).bdd_mul hg (Filter.Eventually.of_forall (fun z => by simpa using hgb z))
  let f := fun x : ℝ => ∫ z, g z * F x z ∂mu
  have hfpoly (x : ℝ) : f x = ∑ q, (∫ z, g z * c q z ∂mu) * x^q.val := by
    dsimp [f, F]
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [integral_finsetSum _ (fun q _ => (hgc q).mul_const _)]
    simp_rw [integral_mul_const]
  have hf : ContDiff ℝ k f := by
    have heq := funext hfpoly
    rw [heq]
    fun_prop
  have hfD (v : ℕ) (x : ℝ) : iteratedDeriv v f x =
      ∫ z, g z * iteratedDeriv v (fun t => F t z) x ∂mu := by
    have heq : f = (fun t : ℝ => ∫ z, ∑ q, (g z * c q z) * t^q.val ∂mu) := by
      ext t
      simp [f, F, Finset.mul_sum, mul_assoc]
    rw [heq, finitePolynomial_iteratedDeriv_integral mu m _ hgc]
    apply integral_congr_ae
    filter_upwards [] with z
    have heqz : (fun t : ℝ => ∑ q, (g z * c q z) * t^q.val) =
        (fun t : ℝ => g z * F t z) := by
      ext t
      simp [F, Finset.mul_sum, mul_assoc]
    rw [heqz, iteratedDeriv_const_mul_field]
  have hfd (x : ℝ) (hx : x ∈ Set.Icc (-a) a) :
      |iteratedDeriv k f x| ≤ (k.factorial : ℝ) * B := by
    rw [hfD]
    calc
      _ ≤ ∫ z, |g z * iteratedDeriv k (fun t => F t z) x| ∂mu :=
        abs_integral_le_integral_abs
      _ ≤ ∫ z, |iteratedDeriv k (fun t => F t z) x| ∂mu := by
        apply integral_mono_ae ((hD k x).bdd_mul hg
          (Filter.Eventually.of_forall (fun z => by simpa using hgb z))).abs (hD k x).abs
        filter_upwards [] with z
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (hgb z)
      _ ≤ _ := hderiv x hx
  have hscalar := coordinate_taylor_remainder_abs_le f k hk hf a B u ha hu hB hfd
  have heq : f u - ∑ v ∈ Finset.range k,
      iteratedDeriv v f 0 / (v.factorial : ℝ) * u^v = ∫ z, |R z| ∂mu := by
    rw [show (∫ z, |R z| ∂mu) = ∫ z, g z * R z ∂mu by simp_rw [hgR]]
    simp_rw [R, mul_sub, Finset.mul_sum, div_eq_mul_inv, ← mul_assoc]
    rw [integral_sub ((hF u).bdd_mul hg
      (Filter.Eventually.of_forall (fun z => by simpa using hgb z)))
      (integrable_finsetSum _ (fun v _ =>
        (((hD v 0).bdd_mul hg (Filter.Eventually.of_forall
          (fun z => by simpa using hgb z))).mul_const _).mul_const _))]
    rw [integral_finsetSum]
    · simp_rw [hfD, integral_mul_const, mul_assoc]
      rfl
    · intro v _
      simpa only [mul_assoc] using (((hD v 0).bdd_mul hg
        (Filter.Eventually.of_forall (fun z => by simpa using hgb z))).mul_const
          ((v.factorial : ℝ)⁻¹)).mul_const (u^v)
  rw [heq, abs_of_nonneg (integral_nonneg (fun z => abs_nonneg (R z)))] at hscalar
  exact hscalar

end CausalSmith.Stat.LdpOptvalueUniformFrontier

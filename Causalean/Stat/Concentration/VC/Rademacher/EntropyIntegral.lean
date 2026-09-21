module
public import Causalean.Stat.Concentration.VC.EmpiricalCover
public import Causalean.Stat.Concentration.Covering.DudleyEntropy
public import Causalean.Stat.Concentration.Covering.SqrtLogIntegral
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime
public import Causalean.Stat.Concentration.Rademacher.Contraction
public import Causalean.Stat.Concentration.Rademacher.Symmetrization
public import Causalean.Tactic.IntegralLinearity
public import Causalean.Mathlib.Analysis.ClipInterval

/-!
# Polynomial entropy integrals for anchored classes

This file anchors a function class at a reference member, transports
polynomial empirical-cover certificates through anchoring and negation, and
bounds the resulting Dudley entropy integral. These deterministic chaining
estimates feed the conditional and variance-adaptive Rademacher bounds.
-/

@[expose] public section

namespace Causalean.Stat.Concentration

open MeasureTheory

universe u v

variable {𝒳 : Type u} [MeasurableSpace 𝒳] {ι : Type v}

/-- For [a function class](hyp:F) and [a chosen reference function](hyp:i₀), the [anchored
function class](goal) subtracts that reference function from every member of the class. This
recentering supplies a zero function for the entropy-integral Rademacher bound. -/
noncomputable def anchoredClass (F : ι → 𝒳 → ℝ) (i₀ : ι) :
    ι → 𝒳 → ℝ := fun i x => F i x - F i₀ x

/-- If [every function in a class is measurable](hyp:hmeas), then [every function obtained by
subtracting a fixed member of the class is measurable](goal). -/
lemma anchoredClass_measurable
    (F : ι → 𝒳 → ℝ) (i₀ : ι) (hmeas : ∀ i, Measurable (F i)) :
    ∀ i, Measurable (anchoredClass F i₀ i) :=
  fun i => (hmeas i).sub (hmeas i₀)

private lemma anchoredClass_empiricalDist
    (F : ι → 𝒳 → ℝ) (i₀ i j : ι) {n : ℕ} (S : Fin n → 𝒳) :
    empiricalDist S (anchoredClass F i₀ i) (anchoredClass F i₀ j) =
      empiricalDist S (F i) (F j) := by
  simp only [empiricalDist]
  congr 1
  funext x
  simp [anchoredClass]

/-- If a function class [has a polynomial empirical L2 covering bound](hyp:hcover) and [all of
its functions are measurable](hyp:hmeas), then [the class anchored by subtracting any fixed
member has the same covering bound](goal). -/
lemma HasPolynomialEmpiricalL2Cover.anchoredClass
    {F : ι → 𝒳 → ℝ} {U A p : ℝ}
    (hcover : HasPolynomialEmpiricalL2Cover F U A p)
    (i₀ : ι) (hmeas : ∀ i, Measurable (F i)) :
    HasPolynomialEmpiricalL2Cover (anchoredClass F i₀) U A p := by
  intro m S hm ε hε hε1
  obtain ⟨C, hC, hcard⟩ := hcover S hm ε hε hε1
  refine ⟨C, ?_, hcard⟩
  intro i
  obtain ⟨j, hj, hij⟩ := hC i
  refine ⟨j, hj, ?_⟩
  rw [measureL2Dist_finiteSampleMeasure_eq_empiricalDist S hm
      (anchoredClass_measurable F i₀ hmeas i)
      (anchoredClass_measurable F i₀ hmeas j),
    anchoredClass_empiricalDist]
  rwa [← measureL2Dist_finiteSampleMeasure_eq_empiricalDist S hm (hmeas i) (hmeas j)]

/-- If a function class [has a polynomial empirical L2 covering bound](hyp:hcover) and [all of
its functions are measurable](hyp:hmeas), then [negating every function preserves that covering
bound](goal). -/
lemma HasPolynomialEmpiricalL2Cover.neg
    {F : ι → 𝒳 → ℝ} {U A p : ℝ}
    (hcover : HasPolynomialEmpiricalL2Cover F U A p)
    (hmeas : ∀ i, Measurable (F i)) :
    HasPolynomialEmpiricalL2Cover (fun i x => -F i x) U A p := by
  intro m S hm ε hε hε1
  obtain ⟨C, hC, hcard⟩ := hcover S hm ε hε hε1
  refine ⟨C, ?_, hcard⟩
  intro i
  obtain ⟨j, hj, hij⟩ := hC i
  refine ⟨j, hj, ?_⟩
  rw [measureL2Dist_finiteSampleMeasure_eq_empiricalDist S hm
      (hmeas i).fun_neg (hmeas j).fun_neg]
  have heq : empiricalDist S (fun x => -F i x) (fun x => -F j x) =
      empiricalDist S (F i) (F j) := by
    unfold empiricalDist empiricalNorm
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    change (-F i (S k) - -F j (S k)) ^ 2 = (F i (S k) - F j (S k)) ^ 2
    ring
  rw [heq]
  rwa [← measureL2Dist_finiteSampleMeasure_eq_empiricalDist S hm (hmeas i) (hmeas j)]

/-- If [the envelope level is nonnegative](hyp:hU) and [every function is pointwise bounded in
absolute value by that level](hyp:henvelope), then [each function's empirical L2 norm is at most
the envelope level](goal). -/
lemma empiricalNorm_le_of_envelope
    (F : ι → 𝒳 → ℝ) {U : ℝ} (hU : 0 ≤ U)
    (henvelope : ∀ i x, |F i x| ≤ U)
    {n : ℕ} (S : Fin n → 𝒳) (i : ι) : empiricalNorm S (F i) ≤ U := by
  simp only [causal_defs_simps]
  rw [Real.sqrt_le_iff]
  constructor
  · exact hU
  · by_cases hn : n = 0
    · subst n
      simp [hU]
    · have hnR : 0 < (n : ℝ) := by positivity
      calc
        (1 / (n : ℝ)) * ∑ k : Fin n, F i (S k) ^ 2
            ≤ (1 / (n : ℝ)) * ∑ _k : Fin n, U ^ 2 := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity)
              rw [sq_le_sq]
              simpa [abs_of_nonneg hU] using henvelope i (S k)
        _ = U ^ 2 := by
              simp [Finset.sum_const, nsmul_eq_mul]
              field_simp

/-- If [every function in the class has empirical L2 norm at most a common radius](hyp:hR), then
[subtracting a fixed class member gives empirical L2 norm at most twice that radius](goal). -/
lemma empiricalNorm_anchored_le
    (F : ι → 𝒳 → ℝ) (i₀ : ι) {n : ℕ} (S : Fin n → 𝒳)
    {R : ℝ} (hR : ∀ i, empiricalNorm S (F i) ≤ R) (i : ι) :
    empiricalNorm S (anchoredClass F i₀ i) ≤ 2 * R := by
  letI := empiricalPMet S
  calc
    empiricalNorm S (anchoredClass F i₀ i) = dist (F i) (F i₀) := by
      rfl
    _ ≤ dist (F i) 0 + dist 0 (F i₀) := dist_triangle _ _ _
    _ = empiricalNorm S (F i) + empiricalNorm S (F i₀) := by
      simp only [dist_comm (0 : 𝒳 → ℝ)]
      change empiricalNorm S (F i - 0) + empiricalNorm S (F i₀ - 0) = _
      simp
    _ ≤ R + R := add_le_add (hR i) (hR i₀)
    _ = 2 * R := by ring

private lemma intervalIntegrable_sqrt_log_ratio_positive
    {a b δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ) :
    IntervalIntegrable (fun x : ℝ => Real.sqrt (Real.log (δ / x))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hdiv : ContinuousOn (fun x : ℝ => δ / x) (Set.Icc a b) :=
    continuousOn_const.div continuousOn_id (fun x hx => by linarith [hx.1])
  simpa [Set.uIcc_of_le hab, Function.comp_def] using Real.continuous_sqrt.comp_continuousOn
    (hdiv.log (fun x hx => div_ne_zero hδ.ne' (by linarith [hx.1])))

/-- Given [a positive lower integration limit](hyp:hε), [an ordered integration
interval](hyp:hεR), and [a positive numerator](hyp:hσ), [the logarithmic
square-root kernel integrates to at most that numerator](goal), even when the
interval extends beyond it. -/
private lemma sqrtLog_partial_integral_le
    {ε R σ : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (hσ : 0 < σ) :
    (∫ x in ε..R, Real.sqrt (Real.log (σ / x))) ≤ σ := by
  have hint := intervalIntegrable_sqrt_log_ratio_positive (δ := σ) hε hεR hσ
  by_cases hRσ : R ≤ σ
  · have hmono :
        (∫ x in ε..R, Real.sqrt (Real.log (σ / x))) ≤
          ∫ x in ε..σ, Real.sqrt (Real.log (σ / x)) := by
      exact intervalIntegral.integral_mono_interval le_rfl hεR hRσ
        (by filter_upwards; intro x; exact Real.sqrt_nonneg _)
        (intervalIntegrable_sqrt_log_div hε (hεR.trans hRσ))
    exact hmono.trans ((sqrtLog_integral_le hε (hεR.trans hRσ)).trans (by linarith))
  · have hσR : σ < R := lt_of_not_ge hRσ
    by_cases hεσ : ε ≤ σ
    · have hi1 := intervalIntegrable_sqrt_log_div hε hεσ
      have hi2 := intervalIntegrable_sqrt_log_ratio_positive (δ := σ) hσ hσR.le hσ
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
      have hzero : (∫ x in σ..R, Real.sqrt (Real.log (σ / x))) = 0 := by
        rw [← intervalIntegral.integral_zero]
        apply intervalIntegral.integral_congr
        intro x hx
        have hxIcc : x ∈ Set.Icc σ R := by
          simpa [Set.uIcc_of_le hσR.le] using hx
        have hxpos : 0 < x := lt_of_lt_of_le hσ hxIcc.1
        have hratio : σ / x ≤ 1 := (div_le_one hxpos).2 hxIcc.1
        exact Real.sqrt_eq_zero_of_nonpos (Real.log_nonpos (by positivity) hratio)
      rw [hzero, add_zero]
      exact (sqrtLog_integral_le hε hεσ).trans (by linarith)
    · have hσε : σ < ε := lt_of_not_ge hεσ
      have hzero : (∫ x in ε..R, Real.sqrt (Real.log (σ / x))) = 0 := by
        rw [← intervalIntegral.integral_zero]
        apply intervalIntegral.integral_congr
        intro x hx
        have hxIcc : x ∈ Set.Icc ε R := by
          simpa [Set.uIcc_of_le hεR] using hx
        have hxpos : 0 < x := lt_of_lt_of_le hε hxIcc.1
        have hratio : σ / x ≤ 1 := (div_le_one hxpos).2 (hσε.le.trans hxIcc.1)
        exact Real.sqrt_eq_zero_of_nonpos (Real.log_nonpos (by positivity) hratio)
      rw [hzero]
      exact hσ.le

/-- For [a measurable observation space, nonempty function index set, and function
class](hyp:𝒳,ι,F), [an envelope, entropy cutoff, covering constant, entropy exponent,
integration lower limit, and empirical radius](hyp:U,σ,A,p,ε,R), if [the class has polynomial
empirical covering numbers](hyp:hcover), [every function is measurable](hyp:hmeas), [the
envelope and cutoff are positive with the cutoff below the envelope](hyp:hU,hσ,hσU), [the
covering constant and exponent satisfy their lower bounds](hyp:hA,hp), then for [a finite
sample](hyp:n,S) with [positive size](hyp:hn), [positive lower integration limit](hyp:hε),
[that limit below the radius](hyp:hεR), and [radius below the envelope](hyp:hRU), [the square-
root log-covering-number integral is bounded by the stated radius and cutoff terms](goal). -/
lemma polynomialCover_entropyIntegral_le
    [Nonempty ι]
    {F : ι → 𝒳 → ℝ} {U σ A p ε R : ℝ}
    (hcover : HasPolynomialEmpiricalL2Cover F U A p)
    (hmeas : ∀ i, Measurable (F i))
    (hU : 0 < U) (hσ : 0 < σ) (hσU : σ < U)
    (hA : Real.exp 1 ≤ A) (hp : 1 ≤ p)
    {n : ℕ} (S : Fin n → 𝒳) (hn : 0 < n)
    (hε : 0 < ε) (hεR : ε ≤ R) (hRU : R ≤ U) :
    let htot := hcover.totallyBounded hmeas hU S hn
    (∫ x in ε..R, Real.sqrt (Real.log (coveringNumber' htot x))) ≤
      R * Real.sqrt (p * vcMaximalLog A U σ) +
        σ * Real.sqrt p := by
  dsimp only
  let htot := hcover.totallyBounded hmeas hU S hn
  letI : Nonempty (EmpiricalFunctionSpace F S) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty ι)⟩⟩
  have hA0 : 0 < A := lt_of_lt_of_le (Real.exp_pos 1) hA
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hratio : Real.exp 1 < A * U / σ := by
    have hUσ : 1 < U / σ := (one_lt_div₀ hσ).2 hσU
    calc
      Real.exp 1 ≤ A := hA
      _ < A * (U / σ) := by nlinarith
      _ = A * U / σ := by ring
  have hlog : vcMaximalLog A U σ = Real.log (A * U / σ) := by
    simp [vcMaximalLog, max_eq_right hratio.le]
  have hL0 : 0 ≤ vcMaximalLog A U σ := by
    rw [hlog]
    have he1 : (1 : ℝ) ≤ Real.exp 1 := by
      simpa using (Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num))
    exact Real.log_nonneg (he1.trans hratio.le)
  have hpoint : ∀ x ∈ Set.Icc ε R,
      Real.sqrt (Real.log (coveringNumber' htot x)) ≤
        Real.sqrt (p * vcMaximalLog A U σ) +
          Real.sqrt p * Real.sqrt (Real.log (σ / x)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hε hx.1
    have hxU : x / U ≤ 1 := (div_le_one hU).2 (hx.2.trans hRU)
    have hxU0 : 0 < x / U := div_pos hx0 hU
    have hcov := hcover.coveringNumber_le hmeas hU S hn (x / U) hxU0 hxU
    have hbase : 0 < A * U / x := by positivity
    have hcard0 : 0 < (coveringNumber' htot x : ℝ) := by
      exact_mod_cast coveringNumber'_nonzero Set.univ_nonempty htot hx0
    have hcard : (coveringNumber' htot x : ℝ) ≤ Real.rpow (A * U / x) p := by
      convert hcov using 1 <;> field_simp <;> ring
    have hlogcov : Real.log (coveringNumber' htot x) ≤ p * Real.log (A * U / x) := by
      calc
        Real.log (coveringNumber' htot x) ≤ Real.log (Real.rpow (A * U / x) p) :=
          Real.log_le_log hcard0 hcard
        _ = p * Real.log (A * U / x) := Real.log_rpow hbase p
    have hmain : Real.sqrt (Real.log (coveringNumber' htot x)) ≤
        Real.sqrt (p * Real.log (A * U / x)) :=
      Real.sqrt_le_sqrt hlogcov
    by_cases hxσ : x ≤ σ
    · have hσx : 1 ≤ σ / x := (one_le_div hx0).2 hxσ
      have hlogsx : 0 ≤ Real.log (σ / x) := Real.log_nonneg hσx
      have hsplit : Real.log (A * U / x) =
          vcMaximalLog A U σ + Real.log (σ / x) := by
        rw [hlog]
        rw [← Real.log_mul (by positivity : A * U / σ ≠ 0) (by positivity : σ / x ≠ 0)]
        congr 1
        field_simp
      have ha : 0 ≤ p * vcMaximalLog A U σ := mul_nonneg hp0 hL0
      have hb : 0 ≤ p * Real.log (σ / x) := mul_nonneg hp0 hlogsx
      have hsqrtadd : Real.sqrt (p * vcMaximalLog A U σ +
          p * Real.log (σ / x)) ≤
          Real.sqrt (p * vcMaximalLog A U σ) +
            Real.sqrt (p * Real.log (σ / x)) := by
        have hsq1 := Real.sq_sqrt ha
        have hsq2 := Real.sq_sqrt hb
        have hsq12 := Real.sq_sqrt (add_nonneg ha hb)
        nlinarith [Real.sqrt_nonneg (p * vcMaximalLog A U σ),
          Real.sqrt_nonneg (p * Real.log (σ / x))]
      calc
        _ ≤ Real.sqrt (p * Real.log (A * U / x)) := hmain
        _ = Real.sqrt (p * vcMaximalLog A U σ + p * Real.log (σ / x)) := by
          rw [hsplit]
          ring_nf
        _ ≤ Real.sqrt (p * vcMaximalLog A U σ) +
            Real.sqrt (p * Real.log (σ / x)) := hsqrtadd
        _ = _ := by rw [Real.sqrt_mul hp0, Real.sqrt_mul hp0]
    · have hσx : σ < x := lt_of_not_ge hxσ
      have hlogle : Real.log (A * U / x) ≤ vcMaximalLog A U σ := by
        rw [hlog]
        apply Real.log_le_log (by positivity)
        exact div_le_div_of_nonneg_left (mul_nonneg hA0.le hU.le) hσ hσx.le
      have hple : p * Real.log (A * U / x) ≤ p * vcMaximalLog A U σ :=
        mul_le_mul_of_nonneg_left hlogle hp0
      have hzero : Real.sqrt (Real.log (σ / x)) = 0 := by
        apply Real.sqrt_eq_zero_of_nonpos
        exact Real.log_nonpos (by positivity) ((div_le_one hx0).2 hσx.le)
      rw [hzero, mul_zero, add_zero]
      exact hmain.trans (Real.sqrt_le_sqrt hple)
  have hintLeft : IntervalIntegrable
      (fun x : ℝ => Real.sqrt (Real.log (coveringNumber' htot x))) volume ε R := by
    apply AntitoneOn.intervalIntegrable
    refine antitoneOn_iff_forall_lt.mpr ?_
    intro a ha b hb hab
    apply Real.sqrt_le_sqrt
    apply Real.log_le_log
    · exact_mod_cast coveringNumber'_nonzero Set.univ_nonempty htot (by
        have : b ∈ Set.Icc ε R := by simpa [Set.uIcc_of_le hεR] using hb
        exact lt_of_lt_of_le hε this.1)
    · norm_cast
      apply coveringNumber'_antitone
      · have : a ∈ Set.Icc ε R := by simpa [Set.uIcc_of_le hεR] using ha
        exact lt_of_lt_of_le hε this.1
      · have : b ∈ Set.Icc ε R := by simpa [Set.uIcc_of_le hεR] using hb
        exact lt_of_lt_of_le hε this.1
      · exact hab.le
  have hintConst : IntervalIntegrable
      (fun _x : ℝ => Real.sqrt (p * vcMaximalLog A U σ)) volume ε R :=
    intervalIntegrable_const
  have hintKernel : IntervalIntegrable
      (fun x : ℝ => Real.sqrt p * Real.sqrt (Real.log (σ / x))) volume ε R :=
    (intervalIntegrable_sqrt_log_ratio_positive hε hεR hσ).const_mul _
  have hintRight : IntervalIntegrable
      (fun x : ℝ => Real.sqrt (p * vcMaximalLog A U σ) +
        Real.sqrt p * Real.sqrt (Real.log (σ / x))) volume ε R := by
    exact hintConst.add hintKernel
  have hmono := intervalIntegral.integral_mono_on hεR hintLeft hintRight hpoint
  have hkernel := sqrtLog_partial_integral_le hε hεR hσ
  calc
    (∫ x in ε..R, Real.sqrt (Real.log (coveringNumber' htot x)))
        ≤ ∫ x in ε..R, (Real.sqrt (p * vcMaximalLog A U σ) +
          Real.sqrt p * Real.sqrt (Real.log (σ / x))) := hmono
    _ = (R - ε) * Real.sqrt (p * vcMaximalLog A U σ) +
          Real.sqrt p * (∫ x in ε..R, Real.sqrt (Real.log (σ / x))) := by
      rw [intervalIntegral.integral_add hintConst hintKernel]
      rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
      simp [smul_eq_mul]
    _ ≤ R * Real.sqrt (p * vcMaximalLog A U σ) + σ * Real.sqrt p := by
      have hs1 : (R - ε) * Real.sqrt (p * vcMaximalLog A U σ) ≤
          R * Real.sqrt (p * vcMaximalLog A U σ) := by
        nlinarith [Real.sqrt_nonneg (p * vcMaximalLog A U σ)]
      have hs2 : Real.sqrt p * (∫ x in ε..R, Real.sqrt (Real.log (σ / x))) ≤
          Real.sqrt p * σ := mul_le_mul_of_nonneg_left hkernel (Real.sqrt_nonneg _)
      nlinarith
    _ = _ := by ring



end Causalean.Stat.Concentration

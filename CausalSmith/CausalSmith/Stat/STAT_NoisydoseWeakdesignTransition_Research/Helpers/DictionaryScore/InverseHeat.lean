module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DictionaryScore.HeatAlgebra

/-! Helpers — DictionaryScore — InverseHeat -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]


/-- The polynomial localization weight is continuous on the entire real line. [This is the stated conclusion](goal). -/
-- @node: qM_continuous
lemma qM_continuous (m : ℕ) : Continuous (qM m) := by
  exact (qMPoly m).continuous

/-- The sixth power defining the latent weight is nonnegative, even off the dose support. [This is the stated conclusion](goal). -/
-- @node: qM_nonneg
lemma qM_nonneg (m : ℕ) (t : ℝ) : 0 ≤ qM m t := by
  unfold qM qMPoly
  rw [Polynomial.eval_pow]
  positivity

/-- Nonnegative design exponents give continuous, finite weighted polynomial moments. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: qM_weighted_continuous
lemma qM_weighted_continuous (kappa : ℝ) (hkappa : 0 ≤ kappa) (m : ℕ) :
    Continuous (fun t => |t| ^ kappa * qM m t) := by
  exact (continuous_abs.rpow_const (fun _ => Or.inr hkappa)).mul (qM_continuous m)

/-- Compact latent support makes each nonnegative-exponent polynomial moment integrable. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: qM_weighted_integrable
lemma qM_weighted_integrable (kappa : ℝ) (hkappa : 0 ≤ kappa) (m : ℕ) :
    Integrable (fun t => |t| ^ kappa * qM m t)
      (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
  exact (qM_weighted_continuous kappa hkappa m).integrableOn_Icc

/-- The continuous odd-degree weight is positive on a neighborhood of the target. [Under the stated conditions](hyp:hm,hmpos). [This is the stated conclusion](goal). -/
-- @node: qM_positive_near_zero
lemma qM_positive_near_zero (m : ℕ) (hm : Odd m) (hmpos : 0 < m) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t, |t| < delta → 0 < qM m t := by
  have hzero : qM m 0 = 1 := by
    simpa using qM_trig m hm hmpos 0 (by norm_num)
  have hn : ∀ᶠ t in nhds (0 : ℝ), 0 < qM m t :=
    (qM_continuous m).continuousAt.eventually (lt_mem_nhds (show (0 : ℝ) < qM m 0 by rw [hzero]; norm_num))
  obtain ⟨delta, hdelta, hball⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨delta, hdelta, ?_⟩
  intro t ht
  exact hball (by simpa [Real.dist_eq] using ht)

/-- A positive neighborhood and the power design weight give a strictly positive denominator. [Under the stated conditions](hyp:hkappa,hm,hmpos). [This is the stated conclusion](goal). -/
-- @node: qM_weightMoment_pos
lemma qM_weightMoment_pos (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (m : ℕ) (hm : Odd m) (hmpos : 0 < m) :
    0 < weightMoment kappa (qM m) := by
  obtain ⟨delta, hdelta, hpos⟩ := qM_positive_near_zero m hm hmpos
  let t : ℝ := min delta 1 / 4
  have htpos : 0 < t := by dsimp [t]; positivity
  have htdelta : |t| < delta := by
    rw [abs_of_pos htpos]
    dsimp [t]
    have := min_le_left delta 1
    linarith
  have htupper : t ≤ 1/2 := by
    dsimp [t]
    have := min_le_right delta 1
    linarith
  have hint : 0 < ∫ t in (-1/2 : ℝ)..(1/2), |t| ^ kappa * qM m t := by
    apply intervalIntegral.integral_pos (by norm_num)
      (qM_weighted_continuous kappa hkappa m).continuousOn
    · intro x hx
      exact mul_nonneg (Real.rpow_nonneg (abs_nonneg x) _) (qM_nonneg m x)
    · exact ⟨t, ⟨by linarith, htupper⟩,
        mul_pos (Real.rpow_pos_of_pos (abs_pos.mpr (ne_of_gt htpos)) _) (hpos t htdelta)⟩
  simpa only [weightMoment, intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2),
    integral_Icc_eq_integral_Ioc] using hint

/-- All polynomial functions have finite Gaussian moments, by finite monomial expansion. [This is the stated conclusion](goal). -/
-- @node: polynomial_eval_gaussian_integrable
lemma polynomial_eval_gaussian_integrable (p : Polynomial ℝ) :
    Integrable (fun z => p.eval z) (gaussianReal 0 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      convert hp.add hq using 1
      · rfl
      · ext z
        exact Polynomial.eval_add
  | monomial j a =>
      have habs := (memLp_id_gaussianReal' (μ := 0) (v := 1) (j : ℝ≥0∞)
        (by simp)).integrable_norm_pow'
      have hpow : Integrable (fun z : ℝ => z^j) (gaussianReal 0 1) := by
        apply habs.mono' (by fun_prop)
        exact Eventually.of_forall (fun z => by simp [norm_pow])
      simpa only [Polynomial.eval_monomial] using hpow.const_mul a

/-- Affine substitution preserves polynomiality, so inverse-heat derivatives are Gaussian integrable. [This is the stated conclusion](goal). -/
-- @node: polynomial_shift_gaussian_integrable
lemma polynomial_shift_gaussian_integrable (p : Polynomial ℝ) (t sigma : ℝ) :
    Integrable (fun z => p.eval (t+sigma*z)) (gaussianReal 0 1) := by
  convert polynomial_eval_gaussian_integrable
    (p.comp (Polynomial.C t + Polynomial.C sigma * Polynomial.X)) using 1
  ext z
  simp

/-- Every affine Gaussian evaluation of the finite inverse-heat sum is integrable. [This is the stated conclusion](goal). -/
-- @node: ellM_gaussian_integrable
lemma ellM_gaussian_integrable (sigma : ℝ) (m : ℕ) (t : ℝ) :
    Integrable (fun z => ellM sigma m (t+sigma*z)) (gaussianReal 0 1) := by
  unfold ellM
  apply integrable_finset_sum
  intro j hj
  exact (polynomial_shift_gaussian_integrable
    ((Polynomial.derivative^[2*j]) (qMPoly m)) t sigma).const_mul _

/-- Compact weighted dose support and Gaussian moments integrate every affine polynomial. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: polynomial_weighted_gaussian_prod_integrable
lemma polynomial_weighted_gaussian_prod_integrable (kappa sigma : ℝ)
    (hkappa : 0 ≤ kappa) (p : Polynomial ℝ) :
    Integrable (fun x : ℝ × ℝ => |x.1| ^ kappa * p.eval (x.1 + sigma*x.2))
      ((volume.restrict (Icc (-1/2 : ℝ) (1/2))).prod (gaussianReal 0 1)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      convert hp.add hq using 1
      · rfl
      · ext x
        rw [Polynomial.eval_add, mul_add]
        rfl
  | monomial j a =>
      have hterm : ∀ i ∈ Finset.range (j+1),
          Integrable (fun x : ℝ × ℝ =>
            (|x.1| ^ kappa * x.1^i) *
              ((sigma*x.2)^(j-i) * (j.choose i : ℝ)))
            ((volume.restrict (Icc (-1/2 : ℝ) (1/2))).prod (gaussianReal 0 1)) := by
        intro i hi
        have ht : Integrable (fun t : ℝ => |t| ^ kappa * t^i)
            (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
          exact ((continuous_abs.rpow_const (fun _ => Or.inr hkappa)).mul
            (continuous_id.pow i)).integrableOn_Icc
        have hz : Integrable (fun z : ℝ =>
            (sigma*z)^(j-i) * (j.choose i : ℝ)) (gaussianReal 0 1) := by
          simpa using (polynomial_shift_gaussian_integrable
            (Polynomial.X^(j-i)) 0 sigma).mul_const (j.choose i : ℝ)
        exact ht.mul_prod hz
      have hsum := integrable_finset_sum (Finset.range (j+1)) hterm
      convert hsum.const_mul a using 1
      ext x
      simp only [Polynomial.eval_monomial, add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The finite inverse-heat derivative sum is an ordinary polynomial on the whole line. [This is the stated conclusion](goal). -/
-- @node: ellM_eq_polynomial
lemma ellM_eq_polynomial (sigma : ℝ) (m : ℕ) :
    ∃ p : Polynomial ℝ, ∀ t, ellM sigma m t = p.eval t := by
  refine ⟨∑ j ∈ Finset.range (3*(m-1)+1),
    Polynomial.C ((-(sigma^2)/2)^j / (j.factorial : ℝ)) *
      ((Polynomial.derivative^[2*j]) (qMPoly m)), ?_⟩
  intro t
  simp only [ellM, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]

/-- The squared inverse-heat weight has a finite weighted joint Gaussian moment. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: ellM_weighted_sq_integrable
lemma ellM_weighted_sq_integrable (kappa sigma : ℝ) (hkappa : 0 ≤ kappa) (m : ℕ) :
    Integrable (fun x : ℝ × ℝ => |x.1| ^ kappa * (ellM sigma m (x.1+sigma*x.2))^2)
      ((volume.restrict (Icc (-1/2 : ℝ) (1/2))).prod (gaussianReal 0 1)) := by
  obtain ⟨p, hp⟩ := ellM_eq_polynomial sigma m
  simp_rw [hp]
  have hi := polynomial_weighted_gaussian_prod_integrable kappa sigma hkappa (p^2)
  simp_rw [Polynomial.eval_pow] at hi
  exact hi

/-- Finite polynomial Gaussian moments discharge the extended second-moment obligation. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: ellM_VqENN_lt_top
lemma ellM_VqENN_lt_top (kappa sigma : ℝ) (hkappa : 0 ≤ kappa) (m : ℕ) :
    VqENN kappa sigma (ellM sigma m) < ⊤ := by
  have hi := ellM_weighted_sq_integrable kappa sigma hkappa m
  have hn : ∀ x : ℝ × ℝ, 0 ≤ |x.1| ^ kappa * (ellM sigma m (x.1+sigma*x.2))^2 :=
    fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)
  have hf := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).mp hi.hasFiniteIntegral
  rw [lintegral_prod _ (by fun_prop)] at hf
  simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)] at hf
  have hm : ∀ t : ℝ, Measurable (fun z => ENNReal.ofReal ((ellM sigma m (t+sigma*z))^2)) := by
    intro t
    fun_prop
  simp_rw [lintegral_const_mul _ (hm _)] at hf
  exact ENNReal.mul_lt_top (by norm_num : (16 : ℝ≥0∞) < ⊤) hf

/-- The public polynomial second moment is an ordinary nonnegative joint integral. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: ellM_Vq_integral
lemma ellM_Vq_integral (kappa sigma : ℝ) (hkappa : 0 ≤ kappa) (m : ℕ) :
    Vq kappa sigma (ellM sigma m) =
      16 * ∫ t in Icc (-1/2 : ℝ) (1/2),
        |t| ^ kappa * (∫ z, (ellM sigma m (t+sigma*z))^2 ∂gaussianReal 0 1) := by
  have hi := ellM_weighted_sq_integrable kappa sigma hkappa m
  have hn : ∀ x : ℝ × ℝ, 0 ≤ |x.1| ^ kappa * (ellM sigma m (x.1+sigma*x.2))^2 :=
    fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)
  have he := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)
  rw [lintegral_prod _ (by fun_prop)] at he
  simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)] at he
  have hm : ∀ t : ℝ, Measurable (fun z => ENNReal.ofReal ((ellM sigma m (t+sigma*z))^2)) := by
    intro t
    fun_prop
  simp_rw [lintegral_const_mul _ (hm _)] at he
  have hj := integral_prod _ hi
  simp_rw [integral_const_mul] at hj
  rw [Vq, VqENN, ENNReal.toReal_mul, ← he, ENNReal.toReal_ofReal
    (integral_nonneg hn), hj]
  norm_num

/-- The public polynomial variance is the finite sum of weighted derivative-square moments (S12). [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: ellM_Vq_derivative_sum
lemma ellM_Vq_derivative_sum (kappa sigma : ℝ) (hkappa : 0 ≤ kappa) (m : ℕ) :
    Vq kappa sigma (ellM sigma m) =
      16 * ∑ j ∈ Finset.range (6*(m-1)+1),
        (sigma^(2*j) / (Nat.factorial j : ℝ)) *
          ∫ t in Icc (-1/2 : ℝ) (1/2),
            |t| ^ kappa * ((polyDeriv j (qMPoly m)).eval t)^2 := by
  rw [ellM_Vq_integral kappa sigma hkappa m]
  simp_rw [ellM_gaussian_second_moment, Finset.mul_sum]
  have heq (t : ℝ) (j : ℕ) :
      |t| ^ kappa * (sigma^(2*j) * ((polyDeriv j (qMPoly m)).eval t)^2 /
        (Nat.factorial j : ℝ)) =
      (sigma^(2*j) / (Nat.factorial j : ℝ)) *
        (|t| ^ kappa * ((polyDeriv j (qMPoly m)).eval t)^2) := by ring
  simp_rw [heq]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    rw [Finset.mul_sum]
  · intro j hj
    apply Integrable.const_mul
    have hc : Continuous (fun t : ℝ =>
        |t| ^ kappa * ((polyDeriv j (qMPoly m)).eval t)^2) :=
      (continuous_abs.rpow_const (fun _ => Or.inr hkappa)).mul
        ((polyDeriv j (qMPoly m)).continuous.pow 2)
    exact hc.integrableOn_Icc

/-- Uniform derivative bounds imply the public polynomial variance envelope in S13. [Under the stated conditions](hyp:hkappa,hC,hderiv). [This is the stated conclusion](goal). -/
-- @node: ellM_Vq_le_of_derivative_bound
lemma ellM_Vq_le_of_derivative_bound (kappa sigma : ℝ) (hkappa : 0 ≤ kappa)
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ t ∈ Icc (-1/2 : ℝ) (1/2), ∀ j ≤ 6*(m-1),
      |(polyDeriv j (qMPoly m)).eval t| ≤ C * ((6*(m-1)).descFactorial j : ℝ)) :
    Vq kappa sigma (ellM sigma m) ≤
      16 * weightMoment kappa (fun _ => 1) *
        (C^2 * (1 + (6*(m-1) : ℕ)*sigma^2)^(6*(m-1))) := by
  let B := C^2 * (1 + (6*(m-1) : ℕ)*sigma^2)^(6*(m-1))
  have hi := ellM_weighted_sq_integrable kappa sigma hkappa m
  have hleft : Integrable (fun t => |t| ^ kappa *
      (∫ z, (ellM sigma m (t+sigma*z))^2 ∂gaussianReal 0 1))
      (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
    convert hi.integral_prod_left using 1
    ext t
    simp only [integral_const_mul]
  have hright : Integrable (fun t : ℝ => |t| ^ kappa * B)
      (volume.restrict (Icc (-1/2 : ℝ) (1/2))) :=
    ((continuous_abs.rpow_const (fun _ => Or.inr hkappa)).mul continuous_const).integrableOn_Icc
  have hb : ∀ᵐ t ∂volume.restrict (Icc (-1/2 : ℝ) (1/2)),
      |t| ^ kappa * (∫ z, (ellM sigma m (t+sigma*z))^2 ∂gaussianReal 0 1) ≤
        |t| ^ kappa * B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (abs_nonneg _) _)
    simp_rw [ellM_eq_finiteInverseHeat]
    exact finiteInverseHeat_gaussian_second_moment_le (qMPoly m) (6*(m-1))
      (qMPoly_natDegree_le m) t sigma C hC (hderiv t ht)
  rw [ellM_Vq_integral kappa sigma hkappa m]
  calc
    _ ≤ 16 * ∫ t in Icc (-1/2 : ℝ) (1/2), |t| ^ kappa * B :=
      mul_le_mul_of_nonneg_left (integral_mono_ae hleft hright hb) (by norm_num)
    _ = _ := by rw [integral_mul_const]; simp only [weightMoment, mul_one]; ring

/-- Monomial expansion gives the exact finite derivative evaluation used in S13. [Under the stated conditions](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: polyDeriv_eval_coeff_sum
lemma polyDeriv_eval_coeff_sum (p : Polynomial ℝ) (D j : ℕ)
    (hp : p.natDegree ≤ D) (t : ℝ) :
    (polyDeriv j p).eval t = ∑ i ∈ Finset.range (D+1),
      p.coeff i * (i.descFactorial j : ℝ) * t^(i-j) := by
  have he := p.as_sum_range_C_mul_X_pow' (n := D+1) (by omega)
  conv_lhs => rw [he, polyDeriv_sum]
  simp only [polyDeriv_C_mul, polyDeriv_X_pow, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_assoc]

/-- On the unit interval, coefficient absolute mass controls every polynomial derivative,
with the descending factorial of any public degree bound. [Under the stated conditions](hyp:hp,ht). [This is the stated conclusion](goal). -/
-- @node: polyDeriv_eval_le_coeff_mass
lemma polyDeriv_eval_le_coeff_mass (p : Polynomial ℝ) (D j : ℕ)
    (hp : p.natDegree ≤ D) (t : ℝ) (ht : |t| ≤ 1) :
    |(polyDeriv j p).eval t| ≤
      (∑ i ∈ Finset.range (D+1), |p.coeff i|) * (D.descFactorial j : ℝ) := by
  rw [polyDeriv_eval_coeff_sum p D j hp t, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hiD : i ≤ D := by have := Finset.mem_range.mp hi; omega
  have hf : (i.descFactorial j : ℝ) ≤ (D.descFactorial j : ℝ) := by
    exact_mod_cast Nat.descFactorial_le j hiD
  have htone : |t|^(i-j) ≤ 1 := pow_le_one₀ (abs_nonneg _) ht
  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (i.descFactorial j : ℝ))]
  calc
    _ ≤ |p.coeff i| * (i.descFactorial j : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left htone (by positivity)
    _ ≤ |p.coeff i| * (D.descFactorial j : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hf (abs_nonneg _)

/-- The exact Hermite second moment has an unconditional coefficient-mass envelope.
This isolates the remaining exponential coefficient estimate in S13 from all Gaussian algebra. [Under the stated conditions](hyp:hp,ht). [This is the stated conclusion](goal). -/
-- @node: finiteInverseHeat_second_moment_le_coeff_mass
lemma finiteInverseHeat_second_moment_le_coeff_mass (p : Polynomial ℝ) (D : ℕ)
    (hp : p.natDegree ≤ D) (t sigma : ℝ) (ht : |t| ≤ 1) :
    (∫ z, ((finiteInverseHeat D sigma p).eval (t+sigma*z))^2 ∂gaussianReal 0 1) ≤
      (∑ i ∈ Finset.range (D+1), |p.coeff i|)^2 * (1+(D : ℝ)*sigma^2)^D := by
  apply finiteInverseHeat_gaussian_second_moment_le p D hp t sigma
    (∑ i ∈ Finset.range (D+1), |p.coeff i|) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  intro j _
  exact polyDeriv_eval_le_coeff_mass p D j hp t ht

/-- The declared polynomial inverse has a public variance bound computed directly from
its finite monomial coefficients, with no derivative-bound premise (roadmap S13). [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: ellM_Vq_le_coeff_mass
lemma ellM_Vq_le_coeff_mass (kappa sigma : ℝ) (hkappa : 0 ≤ kappa) (m : ℕ) :
    Vq kappa sigma (ellM sigma m) ≤
      16 * weightMoment kappa (fun _ => 1) *
        ((∑ i ∈ Finset.range (6*(m-1)+1), |(qMPoly m).coeff i|)^2 *
          (1 + (6*(m-1) : ℕ)*sigma^2)^(6*(m-1))) := by
  apply ellM_Vq_le_of_derivative_bound kappa sigma hkappa m
    (∑ i ∈ Finset.range (6*(m-1)+1), |(qMPoly m).coeff i|)
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  intro t ht j _
  apply polyDeriv_eval_le_coeff_mass (qMPoly m) (6*(m-1)) j (qMPoly_natDegree_le m)
  rw [abs_le]
  constructor <;> linarith [ht.1, ht.2]

/-- With zero noise, only the zeroth derivative survives in the inverse-heat sum. [This is the stated conclusion](goal). -/
-- @node: ellM_zero_noise
lemma ellM_zero_noise (m : ℕ) (t : ℝ) : ellM 0 m t = qM m t := by
  unfold ellM
  rw [Finset.sum_eq_single 0]
  · simp [qM]
  · intro j hj hjzero
    simp [hjzero]
  · simp

/-- At zero noise the polynomial pair satisfies the exact inverse relation directly. [This is the stated conclusion](goal). -/
-- @node: ellM_zero_noise_inverse
lemma ellM_zero_noise_inverse (m : ℕ) (t : ℝ) :
    (∫ z, ellM 0 m (t+0*z) ∂gaussianReal 0 1) = qM m t := by
  simp [ellM_zero_noise]

/-- Every valid polynomial pair is admissible in the noiseless channel. [Under the stated conditions](hyp:hkappa,hvalid). [This is the stated conclusion](goal). -/
-- @node: inverseheat_pair_admissible_zero
lemma inverseheat_pair_admissible_zero (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (m : ℕ) (hvalid : Odd m ∧ 0 < m) :
    PairAdmissible kappa 0 ⟨qM m, ellM 0 m⟩ ∧ VqENN kappa 0 (ellM 0 m) < ⊤ := by
  refine ⟨⟨(qM_continuous m).measurable, ellM_measurable 0 m,
    fun t ht => qM_nonneg m t, qM_weighted_integrable kappa hkappa m,
    qM_weightMoment_pos kappa hkappa m hvalid.1 hvalid.2,
    fun t ht => ellM_gaussian_integrable 0 m t,
    fun t ht => ellM_zero_noise_inverse m t⟩,
    ellM_VqENN_lt_top kappa 0 hkappa m⟩

/-- Degree one gives the constant polynomial weight everywhere. [This is the stated conclusion](goal). -/
-- @node: qM_one
lemma qM_one (t : ℝ) : qM 1 t = 1 := by
  simp [qM, qMPoly, Polynomial.Chebyshev.U_zero]

/-- The degree-one inverse-heat sum is exactly the constant inverse, for every noise scale. [This is the stated conclusion](goal). -/
-- @node: ellM_one
lemma ellM_one (sigma t : ℝ) : ellM sigma 1 t = 1 := by
  simp [ellM, qMPoly, Polynomial.Chebyshev.U_zero]

/-- The constant dictionary pair is admissible without any analytic inversion placeholder. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: inverseheat_pair_admissible_one
lemma inverseheat_pair_admissible_one (kappa sigma : ℝ) (hkappa : 0 ≤ kappa) :
    PairAdmissible kappa sigma ⟨qM 1, ellM sigma 1⟩ ∧
      VqENN kappa sigma (ellM sigma 1) < ⊤ := by
  constructor
  · refine ⟨(qM_continuous 1).measurable, ellM_measurable sigma 1,
      fun t ht => qM_nonneg 1 t, qM_weighted_integrable kappa hkappa 1,
      qM_weightMoment_pos kappa hkappa 1 (by decide) (by norm_num),
      fun t ht => ellM_gaussian_integrable sigma 1 t, ?_⟩
    intro t ht
    simp [ellM_one, qM_one]
  · have hi : Integrable (fun t : ℝ => |t| ^ kappa)
        (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
      simpa only [qM_one, mul_one] using qM_weighted_integrable kappa hkappa 1
    have hfinite : (∫⁻ t in Icc (-1/2 : ℝ) (1/2), ENNReal.ofReal (|t| ^ kappa)) < ⊤ :=
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
        (fun t : ℝ => Real.rpow_nonneg (abs_nonneg t) kappa))).mp hi.hasFiniteIntegral
    simpa [VqENN, ellM_one] using ENNReal.mul_lt_top (by norm_num : (16 : ℝ≥0∞) < ⊤) hfinite

/-- Exact polynomial inversion has positive finite weighted moments and finite Gaussian second moments. [Under the stated conditions](hyp:hvalid,hkappa,hsigma). [This is the stated conclusion](goal). -/
-- @node: inverseheat_pair_admissible
lemma inverseheat_pair_admissible (kappa sigma : ℝ) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (hsigma : sigma ∈ Icc (0 : ℝ) (1/4)) (m : ℕ) (hvalid : Odd m ∧ 0 < m) :
    PairAdmissible kappa sigma ⟨qM m, ellM sigma m⟩ ∧ VqENN kappa sigma (⟨qM m, ellM sigma m⟩ : WeightPair).ell < ⊤ := by
  by_cases hzero : sigma = 0
  · subst sigma
    exact inverseheat_pair_admissible_zero kappa hkappa.1 m hvalid
  have hanalytic :
      (∀ t ∈ Icc (-1/2 : ℝ) (1/2),
        ∫ z, ellM sigma m (t+sigma*z) ∂gaussianReal 0 1 = qM m t) ∧
      VqENN kappa sigma (ellM sigma m) < ⊤ := by
    refine ⟨?_, ellM_VqENN_lt_top kappa sigma hkappa.1 m⟩
    intro t ht
    exact ellM_gaussian_inverse sigma m t
  exact ⟨⟨(qM_continuous m).measurable, ellM_measurable sigma m,
    fun t ht => qM_nonneg m t, qM_weighted_integrable kappa hkappa.1 m,
    qM_weightMoment_pos kappa hkappa.1 m hvalid.1 hvalid.2,
    fun t ht => ellM_gaussian_integrable sigma m t, hanalytic.1⟩, hanalytic.2⟩

end CausalSmith.Stat.NoisydoseWeakdesignTransition

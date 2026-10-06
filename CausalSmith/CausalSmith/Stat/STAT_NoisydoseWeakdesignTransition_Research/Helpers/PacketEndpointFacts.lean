module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketGeometry
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketKernelNormalization
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketMass
public import Mathlib.Analysis.InnerProductSpace.NormPow
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Endpoint packet regularity, normalization and moment cancellation. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators ContDiff
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]


open Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi
/-- Zero extension provides the packet support for both constructions. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hu). -/
-- @node: packetPsi_support
lemma packetPsi_support (kappa : ℝ) (m : ℕ) (u : ℝ)
    (hu : u ∉ Icc (-1 : ℝ) 1) : packetPsi kappa m u = 0 := by
  rw [packetPsi, if_neg hu]
/-- Squaring the dose coordinate makes the endpoint packet even. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: packetPsi_endpoint_even
lemma packetPsi_endpoint_even (kappa : ℝ) (hkappa : 0 < kappa) (m : ℕ) :
    Function.Even (packetPsi kappa m) := by
  intro u
  have hs : -u ∈ Icc (-1 : ℝ) 1 ↔ u ∈ Icc (-1 : ℝ) 1 := by
    simp only [mem_Icc]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [packetPsi, hs, if_pos hkappa, neg_sq]
/-- Legal division at the endpoint yields unit value at the target. [Under the stated conditions](hyp:hNorm,hkappa,hm). [This is the stated conclusion](goal). -/
-- @node: packetPsi_endpoint_zero
lemma packetPsi_endpoint_zero (hNorm : JacobiNormOrthogonality)
    (kappa : ℝ) (hkappa : 0 < kappa) (m : ℕ) (hm : 4 ≤ m) :
    packetPsi kappa m 0 = 1 := by
  have hn := ne_of_gt (packetKernel_endpoint_pos hNorm kappa hkappa m hm)
  simp [packetPsi, hkappa, hn]
/-- Odd weighted moments of any even packet cancel by reflection of the integration interval. [Under the stated conditions](hyp:heven,hj). [This is the stated conclusion](goal). -/
-- @node: even_packet_odd_moment
lemma even_packet_odd_moment (kappa : ℝ) (psi : ℝ → ℝ) (heven : Function.Even psi)
    (j : ℕ) (hj : Odd j) :
    ∫ u in Icc (-1 : ℝ) 1, |u|^kappa * u^j * psi u = 0 := by
  let f : ℝ → ℝ := fun u => |u|^kappa * u^j * psi u
  have hodd : ∀ u, f (-u) = -f u := by
    intro u
    dsimp [f]
    rw [abs_neg, hj.neg_pow, heven u]
    ring
  have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1) f
  simp only [neg_neg] at h
  simp_rw [hodd] at h
  rw [intervalIntegral.integral_neg] at h
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  change (∫ u in (-1 : ℝ)..1, f u) = 0
  linarith

/-- Each standard Jacobi polynomial is smooth as a finite sum of monomials. [This is the stated conclusion](goal). -/
-- @node: stdJacobi_contDiff
@[fun_prop] lemma stdJacobi_contDiff (a b : ℝ) (j : ℕ) :
    ContDiff ℝ 1 (stdJacobi a b j) := by
  unfold stdJacobi jacobiShifted
  fun_prop

/-- A filtered kernel is smooth in its second coordinate since its spectral sum is finite. [This is the stated conclusion](goal). -/
-- @node: filteredJacobiKernel_contDiff
@[fun_prop] lemma filteredJacobiKernel_contDiff (a b : ℝ) (eta : ℝ → ℝ)
    (m : ℕ) (x : ℝ) : ContDiff ℝ 1 (filteredJacobiKernel a b eta m x) := by
  unfold filteredJacobiKernel
  fun_prop

/-- Both choices of the packet kernel are finite polynomial sums. [This is the stated conclusion](goal). -/
-- @node: packetKernel_contDiff
@[fun_prop] lemma packetKernel_contDiff (kappa : ℝ) (m : ℕ) :
    ContDiff ℝ 1 (packetKernel kappa m) := by
  unfold packetKernel
  split_ifs <;> fun_prop

/-- The fourth-order positive taper equals an expression with a smooth cubed norm.
This identity includes both support endpoints, where the taper vanishes. [This is the stated conclusion](goal). -/
-- @node: packet_taper_identity
lemma packet_taper_identity (u : ℝ) :
    (if u ∈ Icc (-1 : ℝ) 1 then (1-u^2)^4 else 0) =
      ((1-u^2)^4 + (1-u^2)*|1-u^2|^3)/2 := by
  by_cases hu : u ∈ Icc (-1 : ℝ) 1
  · have h : 0 ≤ 1-u^2 := by
      have := hu.1
      have := hu.2
      nlinarith
    rw [if_pos hu, abs_of_nonneg h]
    ring
  · have h : 1-u^2 ≤ 0 := by
      simp only [mem_Icc, not_and_or, not_le] at hu
      rcases hu with hu | hu <;> nlinarith
    rw [if_neg hu, abs_of_nonpos h]
    ring

/-- The fourth-order taper has a continuously differentiable zero extension. [This is the stated conclusion](goal). -/
-- @node: packet_taper_contDiff
lemma packet_taper_contDiff :
    ContDiff ℝ 1 (fun u : ℝ => if u ∈ Icc (-1 : ℝ) 1 then (1-u^2)^4 else 0) := by
  have hbase : ContDiff ℝ 1 (fun u : ℝ => 1-u^2) := by fun_prop
  have hnorm : ContDiff ℝ 1 (fun u : ℝ => |1-u^2|^3) := by
    simpa only [Real.norm_eq_abs, Real.rpow_natCast] using
      hbase.norm_rpow (p := (3 : ℕ)) (by norm_num)
  simp_rw [packet_taper_identity]
  exact (hbase.pow 4 |>.add (hbase.mul hnorm)).div_const 2

/-- The finite polynomial kernel times the fourth-order taper is continuously differentiable
on the whole line, including the two endpoints of its zero extension (P1), (P10). [This is the stated conclusion](goal). -/
-- @node: packetPsi_contDiff
@[fun_prop] lemma packetPsi_contDiff (kappa : ℝ) (m : ℕ) :
    ContDiff ℝ 1 (packetPsi kappa m) := by
  have hkernel : ContDiff ℝ 1 (fun u : ℝ =>
      if 0 < kappa then packetKernel kappa m (2*u^2-1) / packetKernel kappa m (-1)
      else packetKernel kappa m u / packetKernel kappa m 0) := by
    split_ifs <;> fun_prop
  have heq : packetPsi kappa m = fun u =>
      (if u ∈ Icc (-1 : ℝ) 1 then (1-u^2)^4 else 0) *
      (if 0 < kappa then packetKernel kappa m (2*u^2-1) / packetKernel kappa m (-1)
       else packetKernel kappa m u / packetKernel kappa m 0) := by
    funext u
    simp only [packetPsi]
    split_ifs <;> simp
  rw [heq]
  exact packet_taper_contDiff.mul hkernel

/-- Every active spectral degree strictly exceeds m and is strictly below 2m (P4). [Under the stated conditions](hyp:hm,hj). [This is the stated conclusion](goal). -/
-- @node: packetFilter_active_index
lemma packetFilter_active_index (m j : ℕ) (hm : 0 < m)
    (hj : packetFilter ((j : ℝ)/m) ≠ 0) : m < j ∧ j < 2*m := by
  have hs : (j : ℝ)/m ∈ Ioo (9/8 : ℝ) (15/8) := by
    rw [← packetFilter_support]
    exact hj
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hlo := (lt_div_iff₀ hmp).mp hs.1
  have hhi := (div_lt_iff₀ hmp).mp hs.2
  constructor
  · exact_mod_cast (show (m : ℝ) < j by nlinarith)
  · exact_mod_cast (show (j : ℝ) < 2*m by nlinarith)

/-- Each filtered spectral summand annihilates every polynomial of degree at most m (P4).
The inactive terms vanish, and the active terms use the cited Jacobi orthogonality leaf. [Under the stated conditions](hyp:hNorm,ha,hb,hm,hR). [This is the stated conclusion](goal). -/
-- @node: packet_spectral_term_orthogonal
lemma packet_spectral_term_orthogonal (hNorm : JacobiNormOrthogonality)
    (a b : ℝ) (ha : -1/2 < a) (hb : -1/2 < b) (m : ℕ) (hm : 0 < m)
    (j : ℕ) (x : ℝ) (R : Polynomial ℝ) (hR : R.degree ≤ (m : WithBot ℕ)) :
    (∫ z in Icc (-1 : ℝ) 1, jacobiWeight a b z *
      (packetFilter ((j : ℝ)/m) * stdJacobi a b j x * stdJacobi a b j z /
        jacobiSqNorm a b j) * R.eval z) = 0 := by
  by_cases hj : packetFilter ((j : ℝ)/m) = 0
  · simp only [hj, zero_mul, zero_div, mul_zero, integral_zero]
  · have hactive := (packetFilter_active_index m j hm hj).1
    have hdeg : R.degree < (j : WithBot ℕ) :=
      hR.trans_lt (by exact_mod_cast hactive)
    have horth := (hNorm a b ha hb j).1 R hdeg
    have heq : (fun z => jacobiWeight a b z *
        (packetFilter ((j : ℝ)/m) * stdJacobi a b j x * stdJacobi a b j z /
          jacobiSqNorm a b j) * R.eval z) =
        (fun z => (packetFilter ((j : ℝ)/m) * stdJacobi a b j x / jacobiSqNorm a b j) *
          (jacobiWeight a b z * stdJacobi a b j z * R.eval z)) := by
      funext z
      ring
    rw [heq, integral_const_mul, horth, mul_zero]

/-- The zeroth Jacobi polynomial is the constant one. [This is the stated conclusion](goal). -/
-- @node: stdJacobi_degree_zero
lemma stdJacobi_degree_zero (a b z : ℝ) : stdJacobi a b 0 z = 1 := by
  simp [stdJacobi, jacobiShifted, rising]

/-- Positivity of the zeroth squared norm supplies integrability of the Jacobi weight,
including a negative endpoint exponent. No extra integrability premise is needed. [Under the stated conditions](hyp:hNorm,ha,hb). [This is the stated conclusion](goal). -/
-- @node: jacobiWeight_integrableOn
lemma jacobiWeight_integrableOn (hNorm : JacobiNormOrthogonality)
    (a b : ℝ) (ha : -1/2 < a) (hb : -1/2 < b) :
    IntegrableOn (jacobiWeight a b) (Icc (-1 : ℝ) 1) := by
  have hn := (hNorm a b ha hb 0).2.1
  have he : jacobiSqNorm a b 0 = ∫ z in Icc (-1 : ℝ) 1, jacobiWeight a b z := by
    simp only [jacobiSqNorm, stdJacobi_degree_zero, one_pow, mul_one]
  rw [he] at hn
  exact Integrable.of_integral_ne_zero (ne_of_gt hn)

/-- The spectral term times any polynomial is integrable under the Jacobi weight.
Compactness bounds the continuous polynomial factor even when the weight is singular. [Under the stated conditions](hyp:hNorm,ha,hb). [This is the stated conclusion](goal). -/
-- @node: packet_spectral_term_integrableOn
lemma packet_spectral_term_integrableOn (hNorm : JacobiNormOrthogonality)
    (a b : ℝ) (ha : -1/2 < a) (hb : -1/2 < b) (m j : ℕ)
    (x : ℝ) (R : Polynomial ℝ) :
    IntegrableOn (fun z => jacobiWeight a b z *
      (packetFilter ((j : ℝ)/m) * stdJacobi a b j x * stdJacobi a b j z /
        jacobiSqNorm a b j) * R.eval z) (Icc (-1 : ℝ) 1) := by
  have hp : Continuous (fun z =>
      (packetFilter ((j : ℝ)/m) * stdJacobi a b j x * stdJacobi a b j z /
        jacobiSqNorm a b j) * R.eval z) := by
    fun_prop
  simpa only [mul_assoc] using
    (jacobiWeight_integrableOn hNorm a b ha hb).mul_continuousOn
      hp.continuousOn isCompact_Icc

/-- Finite-sum linearity assembles the spectral orthogonality into the filtered
kernel's polynomial cancellation. This is the Jacobi-integral side of (P4). [Under the stated conditions](hyp:hNorm,ha,hb,hm,hR). [This is the stated conclusion](goal). -/
-- @node: packet_filtered_kernel_orthogonal
lemma packet_filtered_kernel_orthogonal (hNorm : JacobiNormOrthogonality)
    (a b : ℝ) (ha : -1/2 < a) (hb : -1/2 < b) (m : ℕ) (hm : 0 < m)
    (x : ℝ) (R : Polynomial ℝ) (hR : R.degree ≤ (m : WithBot ℕ)) :
    (∫ z in Icc (-1 : ℝ) 1,
      jacobiWeight a b z * filteredJacobiKernel a b packetFilter m x z * R.eval z) = 0 := by
  have heq : (fun z =>
      jacobiWeight a b z * filteredJacobiKernel a b packetFilter m x z * R.eval z) =
      (fun z => ∑ j ∈ Finset.range (2*m+1), jacobiWeight a b z *
        (packetFilter ((j : ℝ)/m) * stdJacobi a b j x * stdJacobi a b j z /
          jacobiSqNorm a b j) * R.eval z) := by
    funext z
    simp only [filteredJacobiKernel, Finset.mul_sum, Finset.sum_mul]
  rw [heq, integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j hj
    exact packet_spectral_term_orthogonal hNorm a b ha hb m hm j x R hR
  · intro j hj
    exact packet_spectral_term_integrableOn hNorm a b ha hb m j x R

/-- Orthogonality cancels the transformed even-moment polynomial in (P4). [Under the stated conditions](hyp:hNorm,hkappa,hm,hs). [This is the stated conclusion](goal). -/
-- @node: packet_endpoint_transformed_moment_zero
lemma packet_endpoint_transformed_moment_zero (hNorm : JacobiNormOrthogonality)
    (kappa : ℝ) (hkappa : 0 < kappa) (m s : ℕ) (hm : 0 < m) (hs : s ≤ m) :
    (∫ z in Icc (-1 : ℝ) 1, jacobiWeight 4 ((kappa-1)/2) z *
      packetKernel kappa m z * ((1+z)/2)^s) = 0 := by
  let R : Polynomial ℝ := (Polynomial.C (1/2) * (Polynomial.X + Polynomial.C 1))^s
  have hR : R.degree ≤ (m : WithBot ℕ) := by
    dsimp [R]
    simp only [Polynomial.degree_pow, Polynomial.degree_C_mul (by norm_num : (1/2 : ℝ) ≠ 0),
      Polynomial.degree_X_add_C, nsmul_eq_mul, mul_one]
    exact_mod_cast hs
  have heval (z : ℝ) : R.eval z = ((1+z)/2)^s := by
    simp only [R, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_X]
    congr 1
    ring
  simpa only [packetKernel, if_pos hkappa, heval] using
    packet_filtered_kernel_orthogonal hNorm 4 ((kappa-1)/2) (by norm_num)
      (by linarith) m hm (-1) R hR

/-- The quadratic substitution's Jacobian turns the endpoint Jacobi weight into
its original dose power weight, with a fixed strictly positive scalar. [Under the stated conditions](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: packet_endpoint_weight_substitution
lemma packet_endpoint_weight_substitution (kappa u : ℝ) (s : ℕ) (hu : 0 < u) :
    jacobiWeight 4 ((kappa-1)/2) (2*u^2-1) * ((1+(2*u^2-1))/2)^s * (4*u) =
      (2^4 * (2 : ℝ)^((kappa-1)/2) * 4) *
        (u^kappa * u^(2*s) * (1-u^2)^4) := by
  have hleft : 1-(2*u^2-1) = 2*(1-u^2) := by ring
  have hright : 1+(2*u^2-1) = 2*u^2 := by ring
  have hpow : (u^2)^((kappa-1)/2) * u = u^kappa := by
    rw [← Real.rpow_natCast u 2, ← Real.rpow_mul hu.le]
    have hexp : (2 : ℝ)*((kappa-1)/2) = kappa-1 := by ring
    norm_num only [Nat.cast_ofNat] at ⊢
    rw [hexp]
    calc
      u^(kappa-1) * u = u^(kappa-1) * u^(1 : ℝ) := by rw [Real.rpow_one]
      _ = u^kappa := by rw [← Real.rpow_add hu]; congr 1; ring
  rw [jacobiWeight, hleft, hright,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg u)]
  have hhalf : (2*u^2)/2 = u^2 := by ring
  rw [hhalf]
  norm_num only [Real.rpow_ofNat]
  rw [mul_pow, ← pow_mul]
  calc
    _ = (2^4 * (2 : ℝ)^((kappa-1)/2) * 4) *
        (((u^2)^((kappa-1)/2) * u) * u^(2*s) * (1-u^2)^4) := by ring
    _ = _ := by rw [hpow]; norm_num [Real.rpow_ofNat]

/-- Substitution z = 2u² - 1 and Jacobi orthogonality cancel each unnormalized
endpoint packet moment on the positive half interval (P4). [Under the stated conditions](hyp:hNorm,hkappa,hm,hs). [This is the stated conclusion](goal). -/
-- @node: packet_endpoint_half_moment_zero
lemma packet_endpoint_half_moment_zero (hNorm : JacobiNormOrthogonality)
    (kappa : ℝ) (hkappa : 0 < kappa) (m s : ℕ) (hm : 0 < m) (hs : s ≤ m) :
    (∫ u in (0 : ℝ)..1,
      u^kappa * u^(2*s) * (1-u^2)^4 * packetKernel kappa m (2*u^2-1)) = 0 := by
  let g : ℝ → ℝ := fun z => jacobiWeight 4 ((kappa-1)/2) z *
    packetKernel kappa m z * ((1+z)/2)^s
  let A : ℝ := (2 : ℝ)^(4 : ℕ) * (2 : ℝ)^((kappa-1)/2) * 4
  have hA : A ≠ 0 := by dsimp [A]; positivity
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := 1) (f := fun u : ℝ => 2*u^2-1)
    (f' := fun u => 4*u) (g := g)
    (by fun_prop) (by
      intro u hu
      have he : 4*u = 2*(2*u) := by ring
      rw [he]
      simpa using (((hasDerivAt_id u).pow 2).const_mul 2).sub_const 1)
    (by intro u hu; simp only [min_eq_left (by norm_num : (0 : ℝ) ≤ 1)] at hu; linarith [hu.1])
  have hzero : (∫ z in (-1 : ℝ)..1, g z) = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
    exact packet_endpoint_transformed_moment_zero hNorm kappa hkappa m s hm hs
  norm_num only [mul_zero, zero_pow, mul_one, one_pow, zero_sub, sub_self, sub_zero,
    one_mul, Nat.ofNat_pos] at hsub
  have heq : (∫ u in (0 : ℝ)..1, (g ∘ (fun u : ℝ => 2*u^2-1)) u * (4*u)) =
      A * (∫ u in (0 : ℝ)..1,
        u^kappa * u^(2*s) * (1-u^2)^4 * packetKernel kappa m (2*u^2-1)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    have hup : 0 < u := hu.1
    have hw := packet_endpoint_weight_substitution kappa u s hup
    dsimp [g, Function.comp_def, A]
    calc
      _ = (jacobiWeight 4 ((kappa-1)/2) (2*u^2-1) *
        ((1+(2*u^2-1))/2)^s * (4*u)) * packetKernel kappa m (2*u^2-1) := by ring
      _ = _ := by rw [hw]; ring
  rw [heq, hzero] at hsub
  exact (mul_eq_zero.mp hsub).resolve_left hA

/-- Legal normalization preserves the vanishing even moment on the positive half interval. [Under the stated conditions](hyp:hNorm,hkappa,hm,hs). [This is the stated conclusion](goal). -/
-- @node: packetPsi_endpoint_half_moment_zero
lemma packetPsi_endpoint_half_moment_zero (hNorm : JacobiNormOrthogonality)
    (kappa : ℝ) (hkappa : 0 < kappa) (m s : ℕ) (hm : 0 < m) (hs : s ≤ m) :
    (∫ u in (0 : ℝ)..1, |u|^kappa * u^(2*s) * packetPsi kappa m u) = 0 := by
  calc
    _ = (∫ u in (0 : ℝ)..1,
        u^kappa * u^(2*s) * (1-u^2)^4 * packetKernel kappa m (2*u^2-1)) /
          packetKernel kappa m (-1) := by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro u hu
      have hmem : u ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hu.1], hu.2.le⟩
      dsimp only
      rw [packetPsi, if_pos hmem, if_pos hkappa, abs_of_pos hu.1]
      ring
    _ = 0 := by rw [packet_endpoint_half_moment_zero hNorm kappa hkappa m s hm hs, zero_div]

/-- Reflection joins the two half intervals and proves the endpoint packet's full
even weighted moment cancellation (P4), including the zeroth moment. [Under the stated conditions](hyp:hNorm,hkappa,hm,hs). [This is the stated conclusion](goal). -/
-- @node: packetPsi_endpoint_even_moment_zero
lemma packetPsi_endpoint_even_moment_zero (hNorm : JacobiNormOrthogonality)
    (kappa : ℝ) (hkappa : 0 < kappa) (m s : ℕ) (hm : 0 < m) (hs : s ≤ m) :
    (∫ u in Icc (-1 : ℝ) 1, |u|^kappa * u^(2*s) * packetPsi kappa m u) = 0 := by
  let f : ℝ → ℝ := fun u => |u|^kappa * u^(2*s) * packetPsi kappa m u
  have hkappa0 : 0 ≤ kappa := hkappa.le
  have hf : Continuous f := by dsimp [f]; fun_prop
  have heven : ∀ u, f (-u) = f u := by
    intro u
    simp only [f, abs_neg, Even.neg_pow (show Even (2*s) from even_two_mul s),
      packetPsi_endpoint_even kappa hkappa m u]
  have hpos : (∫ u in (0 : ℝ)..1, f u) = 0 :=
    packetPsi_endpoint_half_moment_zero hNorm kappa hkappa m s hm hs
  have hneg : (∫ u in (-1 : ℝ)..0, f u) = 0 := by
    have he := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) f
    simp only [heven, neg_zero] at he
    exact he.symm.trans hpos
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  change (∫ u in (-1 : ℝ)..1, f u) = 0
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-1) 0) (hf.intervalIntegrable 0 1), hneg, hpos, add_zero]

/-- The squared weighted packet mass is bounded by its supremum times its absolute mass (P8).
Integrability follows from the constructed packet's continuity on the compact interval. [Under the stated conditions](hyp:hkappa,hsup). [This is the stated conclusion](goal). -/
-- @node: packetPsi_square_mass_le
lemma packetPsi_square_mass_le (kappa : ℝ) (hkappa : 0 ≤ kappa) (m : ℕ)
    (C : ℝ) (hsup : ∀ u, |packetPsi kappa m u| ≤ C) :
    (∫ u in Icc (-1 : ℝ) 1, |u|^kappa * (packetPsi kappa m u)^2) ≤
      C * (∫ u in Icc (-1 : ℝ) 1, |u|^kappa * |packetPsi kappa m u|) := by
  have hw : Continuous (fun u : ℝ => |u|^kappa) := by fun_prop
  have hp := (packetPsi_contDiff kappa m).continuous
  have hi := (hw.mul (hp.pow 2)).continuousOn.integrableOn_Icc (μ := volume) (a := (-1 : ℝ)) (b := 1)
  have ha := (hw.mul hp.abs).continuousOn.integrableOn_Icc (μ := volume) (a := (-1 : ℝ)) (b := 1)
  rw [← integral_const_mul]
  apply integral_mono hi (ha.const_mul C)
  intro u
  have hab : (packetPsi kappa m u)^2 = |packetPsi kappa m u| * |packetPsi kappa m u| := by
    nlinarith [sq_abs (packetPsi kappa m u)]
  change |u|^kappa * (packetPsi kappa m u)^2 ≤ C * (|u|^kappa * |packetPsi kappa m u|)
  rw [hab]
  calc
    _ ≤ |u|^kappa * (C * |packetPsi kappa m u|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hsup u) (abs_nonneg _))
        (Real.rpow_nonneg (abs_nonneg _) _)
    _ = _ := by ring

end CausalSmith.Stat.NoisydoseWeakdesignTransition

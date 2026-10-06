module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketGeometry
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! Nearby-argument limits for the endpoint packet derivative estimate (P9). -/
public section
noncomputable section
open Set Filter
open scoped Topology
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- Comparing nearby increments of two differentiable functions compares their derivatives.
This is the division by the increment and passage to the limit used in (P9). [Under the stated conditions](hyp:hf,hg,h). [This is the stated conclusion](goal). -/
-- @node: packet_derivative_le_of_increment_bound
lemma packet_derivative_le_of_increment_bound {f g : ℝ → ℝ} {df dg x C : ℝ}
    (hf : HasDerivAt f df x) (hg : HasDerivAt g dg x)
    (h : ∀ᶠ y in 𝓝 x, |f y-f x| ≤ C*|g y-g x|) : |df| ≤ C*|dg| := by
  apply le_of_tendsto_of_tendsto hf.tendsto_slope.abs (hg.tendsto_slope.abs.const_mul C)
  filter_upwards [h.filter_mono nhdsWithin_le_nhds] with y hy
  simpa only [slope_def_field, abs_div, mul_div_assoc] using
    div_le_div_of_nonneg_right hy (abs_nonneg (y-x))

/-- The finite Jacobi sum is symmetric in its two arguments. [This is the stated conclusion](goal). -/
-- @node: filteredJacobiKernel_symm
lemma filteredJacobiKernel_symm (a b : ℝ) (eta : ℝ → ℝ) (m : ℕ) (x y : ℝ) :
    filteredJacobiKernel a b eta m x y = filteredJacobiKernel a b eta m y x := by
  unfold filteredJacobiKernel
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The cited angular Lipschitz estimate bounds the ordinary derivative at each interior
Jacobi coordinate. The same uniform constant works for all degrees and coordinates. [Under the stated conditions](hyp:hLip,ha,hb,heta,hS). [This is the stated conclusion](goal). -/
-- @node: filteredJacobiKernel_derivative_bound
lemma filteredJacobiKernel_derivative_bound (hLip : FilteredJacobiLipschitz)
    (a b : ℝ) (ha : -1/2 < a) (hb : -1/2 < b)
    (eta : ℝ → ℝ) (heta : SmoothJacobiFilter eta) (S : ℝ) (hS : 0 < S) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ x ∈ Ioo (-1 : ℝ) 1,
      ∀ y ∈ Icc (-1 : ℝ) 1,
      |deriv (fun t => filteredJacobiKernel a b eta m t y) x| ≤
        (C*(m : ℝ)^2 /
          (Real.sqrt (jacobiRegularizedWeight a b m y * jacobiRegularizedWeight a b m x) *
            (1+m*jacobiAngularDistance y x)^S)) * (1/Real.sqrt (1-x^2)) := by
  obtain ⟨C, hC, hkernel⟩ := hLip a b ha hb eta heta S 1 hS (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro m hm x hx y hy
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have harc := Real.hasDerivAt_arccos (x := x) (by linarith [hx.1]) (by linarith [hx.2])
  have hdiff : DifferentiableAt ℝ (fun t => filteredJacobiKernel a b eta m t y) x := by
    unfold filteredJacobiKernel stdJacobi
      Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.jacobiShifted
    fun_prop
  have hnear : ∀ᶠ t in 𝓝 x, t ∈ Icc (-1 : ℝ) 1 ∧
      jacobiAngularDistance t x ≤ 1/(m : ℝ) := by
    have hi : ∀ᶠ t in 𝓝 x, t ∈ Ioo (-1 : ℝ) 1 := isOpen_Ioo.mem_nhds hx
    have hd : ContinuousAt (fun t => jacobiAngularDistance t x) x := by
      unfold jacobiAngularDistance
      fun_prop
    have he := hd.tendsto.eventually (gt_mem_nhds (show
        jacobiAngularDistance x x < 1/(m : ℝ) by
          simp only [jacobiAngularDistance, sub_self, abs_zero]; positivity))
    filter_upwards [hi, he] with t ht hd
    exact ⟨⟨ht.1.le, ht.2.le⟩, hd.le⟩
  have hbound := packet_derivative_le_of_increment_bound hdiff.hasDerivAt harc
    (C := C*(m : ℝ)^2 /
      (Real.sqrt (jacobiRegularizedWeight a b m y * jacobiRegularizedWeight a b m x) *
        (1+m*jacobiAngularDistance y x)^S)) (by
      filter_upwards [hnear] with t ht
      have hk := hkernel m hm t ht.1 x ⟨hx.1.le, hx.2.le⟩ y hy x ⟨hx.1.le, hx.2.le⟩
        ht.2 (by simp [jacobiAngularDistance, hmp.le])
      convert hk using 1 <;> simp only [jacobiAngularDistance, Function.comp_apply] <;> ring)
  simpa only [abs_neg, abs_of_nonneg (by positivity : 0 ≤ 1/Real.sqrt (1-x^2))] using hbound

/-- The angular derivative of the quadratic endpoint coordinate has the magnitude in (P9).
The exclusion of zero is needed only for the arccos chain rule. [Under the stated conditions](hyp:hu0,hu). [This is the stated conclusion](goal). -/
-- @node: packet_endpoint_angular_derivative_abs
lemma packet_endpoint_angular_derivative_abs (u : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 1)
    (hu0 : u ≠ 0) :
    |-(1/Real.sqrt (1-(2*u^2-1)^2))*(4*u)| = 2/Real.sqrt (1-u^2) := by
  have hD : 0 < 1-u^2 := by nlinarith [hu.1, hu.2]
  have he : 1-(2*u^2-1)^2 = (2*u)^2*(1-u^2) := by ring
  have hs : Real.sqrt (1-(2*u^2-1)^2) = 2*|u| *Real.sqrt (1-u^2) := by
    rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hs, abs_mul, abs_neg, abs_div, abs_one,
    abs_of_nonneg (by positivity : 0 ≤ 2*|u| *Real.sqrt (1-u^2)), abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  field_simp [ne_of_gt (abs_pos.mpr hu0), ne_of_gt (Real.sqrt_pos.mpr hD)]
  <;> ring

/-- The nearby-argument Lipschitz estimate gives the derivative of the endpoint kernel
along the quadratic dose coordinate, with the exact angular loss in (P9). [Under the stated conditions](hyp:hLip,hkappa,hS). [This is the stated conclusion](goal). -/
-- @node: packetKernel_endpoint_composed_derivative_bound
lemma packetKernel_endpoint_composed_derivative_bound (hLip : FilteredJacobiLipschitz)
    (kappa : ℝ) (hkappa : 0 < kappa) (S : ℝ) (hS : 0 < S) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 4 ≤ m → ∀ u ∈ Ioo (-1 : ℝ) 1, u ≠ 0 →
      |deriv (fun v => packetKernel kappa m (2*v^2-1)) u| ≤
        (C*(m : ℝ)^2 /
          (Real.sqrt (jacobiRegularizedWeight 4 ((kappa-1)/2) m (-1) *
            jacobiRegularizedWeight 4 ((kappa-1)/2) m (2*u^2-1)) *
              (1+m*jacobiAngularDistance (-1) (2*u^2-1))^S)) *
        (2/Real.sqrt (1-u^2)) := by
  obtain ⟨C, hC, hkernel⟩ := hLip 4 ((kappa-1)/2) (by norm_num) (by linarith)
    packetFilter packetFilter_smoothJacobiFilter S 1 hS (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro m hm u hu hu0
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hz : 2*u^2-1 ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> nlinarith [sq_pos_of_ne_zero hu0, hu.1, hu.2]
  have hcoord : HasDerivAt (fun v : ℝ => 2*v^2-1) (4*u) u := by
    have hd := (((hasDerivAt_id (𝕜 := ℝ) u).pow 2).const_mul 2).sub_const 1
    simp only [Nat.cast_ofNat, show (2-1 : ℕ) = 1 from rfl, pow_one, mul_one, id_eq] at hd
    convert hd using 1 <;> first | rfl | ring
  have harc := (Real.hasDerivAt_arccos (x := 2*u^2-1)
    (by linarith [hz.1]) (by linarith [hz.2])).comp u hcoord
  have hdiff : DifferentiableAt ℝ (fun v => packetKernel kappa m (2*v^2-1)) u := by
    unfold packetKernel filteredJacobiKernel stdJacobi
      Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.jacobiShifted
    split_ifs <;> fun_prop
  have hnear : ∀ᶠ v in 𝓝 u, v ∈ Ioo (-1 : ℝ) 1 ∧
      jacobiAngularDistance (2*v^2-1) (2*u^2-1) ≤ 1/(m : ℝ) := by
    have hi : ∀ᶠ v in 𝓝 u, v ∈ Ioo (-1 : ℝ) 1 := isOpen_Ioo.mem_nhds hu
    have hd : ContinuousAt (fun v => jacobiAngularDistance (2*v^2-1) (2*u^2-1)) u := by
      unfold jacobiAngularDistance
      fun_prop
    have he := hd.tendsto.eventually (gt_mem_nhds (show
      jacobiAngularDistance (2*u^2-1) (2*u^2-1) < 1/(m : ℝ) by
        simp only [jacobiAngularDistance, sub_self, abs_zero]; positivity))
    filter_upwards [hi, he] with v hv hd
    exact ⟨hv, hd.le⟩
  have hbound := packet_derivative_le_of_increment_bound hdiff.hasDerivAt harc
    (C := C*(m : ℝ)^2 /
      (Real.sqrt (jacobiRegularizedWeight 4 ((kappa-1)/2) m (-1) *
        jacobiRegularizedWeight 4 ((kappa-1)/2) m (2*u^2-1)) *
          (1+m*jacobiAngularDistance (-1) (2*u^2-1))^S)) (by
      filter_upwards [hnear] with v hv
      have hk := hkernel m (by omega) (2*v^2-1)
        (packet_endpoint_coordinate_mem v ⟨hv.1.1.le, hv.1.2.le⟩)
        (2*u^2-1) ⟨hz.1.le, hz.2.le⟩ (-1) (by norm_num)
        (2*u^2-1) ⟨hz.1.le, hz.2.le⟩ hv.2
        (by simp [jacobiAngularDistance, hmp.le])
      simp only [packetKernel, if_pos hkappa]
      rw [filteredJacobiKernel_symm (x := -1), filteredJacobiKernel_symm (x := -1)]
      convert hk using 1 <;> simp only [jacobiAngularDistance, Function.comp_apply] <;> ring)
  simpa only [packet_endpoint_angular_derivative_abs u hu hu0] using hbound

/-- The cubed taper squared is controlled by the regularized weight after extracting
its endpoint degree power. This drops the extra nonnegative decay factor in (P5). [Under the stated conditions](hyp:hkappa,hm,hu). [This is the stated conclusion](goal). -/
-- @node: packet_endpoint_derivative_taper_weight_lower
lemma packet_endpoint_derivative_taper_weight_lower (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (m : ℕ) (hm : 0 < m) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    (1-u^2)^6 * (m : ℝ)^(-kappa) ≤
      jacobiRegularizedWeight 4 ((kappa-1)/2) m (2*u^2-1) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have he : 0 ≤ (m : ℝ)^(-2 : ℝ) := (Real.rpow_pos_of_pos hmp _).le
  have hD : 0 ≤ 1-u^2 := by nlinarith [hu.1, hu.2]
  have hD1 : 1-u^2 ≤ 1 := by nlinarith [sq_nonneg u]
  have hfirst : (1-u^2)^6 ≤ (2*(1-u^2)+(m : ℝ)^(-2 : ℝ))^(4+1/2 : ℝ) := by
    calc
      _ = (1-u^2)^(6 : ℝ) := by norm_num [Real.rpow_ofNat]
      _ ≤ (1-u^2)^(4+1/2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge' hD hD1 (by norm_num) (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow hD (by linarith) (by norm_num)
  have hsecond : (m : ℝ)^(-kappa) ≤ (2*u^2+(m : ℝ)^(-2 : ℝ))^(kappa/2) := by
    calc
      _ = ((m : ℝ)^(-2 : ℝ))^(kappa/2) := by
        rw [← Real.rpow_mul hmp.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow he (by nlinarith [sq_nonneg u]) (by linarith)
  have hexp : (kappa-1)/2+1/2 = kappa/2 := by ring
  have hleft : 1-(2*u^2-1)+(m : ℝ)^(-2 : ℝ) = 2*(1-u^2)+(m : ℝ)^(-2 : ℝ) := by ring
  have hright : 1+(2*u^2-1)+(m : ℝ)^(-2 : ℝ) = 2*u^2+(m : ℝ)^(-2 : ℝ) := by ring
  rw [jacobiRegularizedWeight, hleft, hright, hexp]
  exact mul_le_mul hfirst hsecond (Real.rpow_nonneg hmp.le _) (Real.rpow_nonneg (by linarith) _)

/-- The cubed taper cancels the square-root weight loss in the endpoint localization estimate. [Under the stated conditions](hyp:hkappa,hm,hu). [This is the stated conclusion](goal). -/
-- @node: packet_endpoint_derivative_taper_sqrt_weight
lemma packet_endpoint_derivative_taper_sqrt_weight (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (m : ℕ) (hm : 0 < m) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    (1-u^2)^3 * (m : ℝ)^(-kappa) ≤
      Real.sqrt (jacobiRegularizedWeight 4 ((kappa-1)/2) m (-1) *
        jacobiRegularizedWeight 4 ((kappa-1)/2) m (2*u^2-1)) := by
  apply Real.le_sqrt_of_sq_le
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have h := mul_le_mul (packet_endpoint_weight_lower kappa m hm)
    (packet_endpoint_derivative_taper_weight_lower kappa hkappa m hm u hu)
    (mul_nonneg (by positivity) (Real.rpow_nonneg hmp.le _))
    (jacobiRegularizedWeight_pos 4 ((kappa-1)/2) m hm (-1) (by norm_num)).le
  convert h using 1 <;> first | ring | rfl


end CausalSmith.Stat.NoisydoseWeakdesignTransition

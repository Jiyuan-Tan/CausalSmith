module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketKernelNormalization
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Angular geometry and taper comparisons for endpoint packet localization (P5)--(P6). -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
noncomputable section
open Set
open scoped ContDiff
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- The explicit filter is the standard smooth exponential glue composed with a quadratic. [This is the stated conclusion](goal). -/
-- @node: packetFilter_eq_expNegInvGlue
lemma packetFilter_eq_expNegInvGlue (s : ℝ) :
    packetFilter s = expNegInvGlue ((s-9/8)*(15/8-s)) := by
  by_cases hs : s ∈ Ioo (9/8 : ℝ) (15/8)
  · have hp : 0 < (s-9/8)*(15/8-s) := mul_pos (by linarith [hs.1]) (by linarith [hs.2])
    simp [packetFilter, hs, expNegInvGlue, not_le.mpr hp, neg_div, one_div, mul_comm]
  · have hp : (s-9/8)*(15/8-s) ≤ 0 := by
      simp only [mem_Ioo, not_and_or, not_lt] at hs
      rcases hs with hs | hs <;> nlinarith
    rw [packetFilter, if_neg hs, expNegInvGlue.zero_of_nonpos hp]

/-- The fixed filter is smooth to every order, including the two support endpoints. [This is the stated conclusion](goal). -/
-- @node: packetFilter_contDiff
@[fun_prop] lemma packetFilter_contDiff : ContDiff ℝ ∞ packetFilter := by
  have hquad : ContDiff ℝ ∞ (fun s : ℝ => (s-9/8)*(15/8-s)) := by fun_prop
  have h := expNegInvGlue.contDiff.comp hquad
  simpa only [Function.comp_def, ← packetFilter_eq_expNegInvGlue] using h

/-- Nonzero filter values lie strictly between the two spectral cutoffs. [This is the stated conclusion](goal). -/
-- @node: packetFilter_support
lemma packetFilter_support : Function.support packetFilter = Ioo (9/8 : ℝ) (15/8) := by
  ext s
  constructor
  · intro hs
    by_contra h
    exact hs (by rw [packetFilter, if_neg h])
  · intro hs
    exact ne_of_gt (packetFilter_pos s hs)

/-- The explicit filter satisfies the common hypothesis of both cited localization gates. [This is the stated conclusion](goal). -/
-- @node: packetFilter_smoothJacobiFilter
lemma packetFilter_smoothJacobiFilter : SmoothJacobiFilter packetFilter := by
  refine ⟨packetFilter_contDiff.contDiffOn, ?_⟩
  rw [packetFilter_support]
  intro s hs
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- Compactness gives one strictly positive filter lower bound on the central spectral band. [This is the stated conclusion](goal). -/
-- @node: packetFilter_uniform_lower
lemma packetFilter_uniform_lower : ∃ d : ℝ, 0 < d ∧
    ∀ s ∈ Icc (5/4 : ℝ) (7/4), d ≤ packetFilter s := by
  obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (5/4 : ℝ) (7/4)).Nonempty from ⟨3/2, by norm_num⟩)
    packetFilter_contDiff.continuous.continuousOn
  refine ⟨packetFilter s, packetFilter_pos s ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
  exact hmin



/-- The quadratic endpoint coordinate stays in the Jacobi interval. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hu). -/
-- @node: packet_endpoint_coordinate_mem
lemma packet_endpoint_coordinate_mem (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    2*u^2-1 ∈ Icc (-1 : ℝ) 1 := by
  have hs : u^2 ≤ 1 := by nlinarith [hu.1, hu.2]
  constructor <;> nlinarith [sq_nonneg u]

/-- The endpoint angular distance is exactly twice the arcsine of the dose magnitude. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hu). -/
-- @node: packet_endpoint_angular_eq
lemma packet_endpoint_angular_eq (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    jacobiAngularDistance (-1) (2*u^2-1) = 2*Real.arcsin |u| := by
  have hab : |u| ≤ 1 := abs_le.mpr hu
  have ha : 0 ≤ Real.arcsin |u| := Real.arcsin_nonneg.mpr (abs_nonneg u)
  have hb := Real.arcsin_le_pi_div_two |u|
  have hc : Real.arccos (2*u^2-1) = Real.pi - 2*Real.arcsin |u| := by
    apply Real.arccos_eq_of_eq_cos (by linarith) (by linarith)
    rw [Real.cos_pi_sub, Real.cos_two_mul, Real.cos_sq',
      Real.sin_arcsin (by linarith [abs_nonneg u]) hab, sq_abs]
    ring
  rw [jacobiAngularDistance, Real.arccos_neg_one, hc]
  rw [abs_of_nonneg (by linarith)]
  ring

/-- The angular distance dominates the dose magnitude, so angular decay implies dose decay. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hu). -/
-- @node: packet_endpoint_angular_lower
lemma packet_endpoint_angular_lower (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    |u| ≤ jacobiAngularDistance (-1) (2*u^2-1) := by
  rw [packet_endpoint_angular_eq u hu]
  have ha : 0 ≤ Real.arcsin |u| := Real.arcsin_nonneg.mpr (abs_nonneg u)
  have hs := Real.sin_le ha
  rw [Real.sin_arcsin (by linarith [abs_nonneg u]) (abs_le.mpr hu)] at hs
  linarith

/-- Regularization keeps the Jacobi weight strictly positive at every legal coordinate. [Under the stated conditions](hyp:hm,hx). [This is the stated conclusion](goal). -/
-- @node: jacobiRegularizedWeight_pos
lemma jacobiRegularizedWeight_pos (a b : ℝ) (m : ℕ) (hm : 0 < m)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < jacobiRegularizedWeight a b m x := by
  have he : 0 < (m : ℝ)^(-2 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hm) _
  exact mul_pos (Real.rpow_pos_of_pos (by linarith [hx.2]) _)
    (Real.rpow_pos_of_pos (by linarith [hx.1]) _)

/-- At the endpoint the regularized weight dominates the normalization power. [Under the stated conditions](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: packet_endpoint_weight_lower
lemma packet_endpoint_weight_lower (kappa : ℝ) (m : ℕ) (hm : 0 < m) :
    (m : ℝ)^(-kappa) ≤ jacobiRegularizedWeight 4 ((kappa-1)/2) m (-1) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have he : 0 ≤ (m : ℝ)^(-2 : ℝ) := (Real.rpow_pos_of_pos hmp _).le
  have hp : 1 ≤ (2+(m : ℝ)^(-2 : ℝ))^(4+1/2 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hexp : (kappa-1)/2+1/2 = kappa/2 := by ring
  have hepow : ((m : ℝ)^(-2 : ℝ))^(kappa/2) = (m : ℝ)^(-kappa) := by
    rw [← Real.rpow_mul hmp.le]
    congr 1
    ring
  simp only [jacobiRegularizedWeight, sub_neg_eq_add, add_neg_cancel, zero_add, hexp]
  norm_num only at ⊢
  rw [hepow]
  norm_num at hp
  simpa using mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hmp.le (-kappa))

/-- The fourth-order taper squared is controlled by the regularized weight after extracting
its endpoint degree power. This drops the extra nonnegative decay factor in (P5). [Under the stated conditions](hyp:hkappa,hm,hu). [This is the stated conclusion](goal). -/
-- @node: packet_endpoint_taper_weight_lower
lemma packet_endpoint_taper_weight_lower (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (m : ℕ) (hm : 0 < m) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    (1-u^2)^8 * (m : ℝ)^(-kappa) ≤
      jacobiRegularizedWeight 4 ((kappa-1)/2) m (2*u^2-1) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have he : 0 ≤ (m : ℝ)^(-2 : ℝ) := (Real.rpow_pos_of_pos hmp _).le
  have hD : 0 ≤ 1-u^2 := by nlinarith [hu.1, hu.2]
  have hD1 : 1-u^2 ≤ 1 := by nlinarith [sq_nonneg u]
  have hfirst : (1-u^2)^8 ≤ (2*(1-u^2)+(m : ℝ)^(-2 : ℝ))^(4+1/2 : ℝ) := by
    calc
      _ = (1-u^2)^(8 : ℝ) := by norm_num [Real.rpow_ofNat]
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

/-- The taper cancels the square-root weight loss in the endpoint localization estimate. [Under the stated conditions](hyp:hkappa,hm,hu). [This is the stated conclusion](goal). -/
-- @node: packet_endpoint_taper_sqrt_weight
lemma packet_endpoint_taper_sqrt_weight (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (m : ℕ) (hm : 0 < m) (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    (1-u^2)^4 * (m : ℝ)^(-kappa) ≤
      Real.sqrt (jacobiRegularizedWeight 4 ((kappa-1)/2) m (-1) *
        jacobiRegularizedWeight 4 ((kappa-1)/2) m (2*u^2-1)) := by
  apply Real.le_sqrt_of_sq_le
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have h := mul_le_mul (packet_endpoint_weight_lower kappa m hm)
    (packet_endpoint_taper_weight_lower kappa hkappa m hm u hu)
    (mul_nonneg (by positivity) (Real.rpow_nonneg hmp.le _))
    (jacobiRegularizedWeight_pos 4 ((kappa-1)/2) m hm (-1) (by norm_num)).le
  convert h using 1 <;> first | ring | rfl

/-- The cited localization estimate and positive normalization give arbitrary uniform
polynomial decay of the endpoint packet, after its fourth-order taper (P5)--(P6). [Under the stated conditions](hyp:hLocalization,hNorm,hGamma,hkappa,hS). [This is the stated conclusion](goal). -/
-- @node: packetPsi_endpoint_localization
lemma packetPsi_endpoint_localization (hLocalization : FilteredJacobiLocalization)
    (hNorm : JacobiNormOrthogonality) (hGamma : GammaRatioAsymptotic)
    (kappa : ℝ) (hkappa : 0 < kappa) (S : ℝ) (hS : 0 < S) :
    ∃ A : ℝ, 0 < A ∧ ∀ m : ℕ, 4 ≤ m → ∀ u : ℝ,
      |packetPsi kappa m u| ≤ A*(1+(m : ℝ)*|u|)^(-S) := by
  obtain ⟨c0, C0, hc0, hC0, hnormalization⟩ :=
    packetKernel_endpoint_power_bounds hNorm hGamma kappa hkappa
  obtain ⟨C, hC, hkernel⟩ := hLocalization 4 ((kappa-1)/2) (by norm_num)
    (by linarith) packetFilter packetFilter_smoothJacobiFilter S hS
  refine ⟨C/c0, div_pos hC hc0, ?_⟩
  intro m hm u
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  by_cases hu : u ∈ Icc (-1 : ℝ) 1
  · let t : ℝ := (1-u^2)^4
    let B : ℝ := Real.sqrt (jacobiRegularizedWeight 4 ((kappa-1)/2) m (-1) *
      jacobiRegularizedWeight 4 ((kappa-1)/2) m (2*u^2-1))
    let Q : ℝ := (1+(m : ℝ)*jacobiAngularDistance (-1) (2*u^2-1))^S
    let R : ℝ := (1+(m : ℝ)*|u|)^S
    let N : ℝ := packetKernel kappa m (-1)
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hB : 0 < B := Real.sqrt_pos.mpr (mul_pos
      (jacobiRegularizedWeight_pos 4 ((kappa-1)/2) m (by omega) (-1) (by norm_num))
      (jacobiRegularizedWeight_pos 4 ((kappa-1)/2) m (by omega) _
        (packet_endpoint_coordinate_mem u hu)))
    have hQ : 0 < Q := Real.rpow_pos_of_pos
      (by have := abs_nonneg (Real.arccos (-1)-Real.arccos (2*u^2-1));
          dsimp [jacobiAngularDistance] at *; positivity) _
    have hR : 0 < R := Real.rpow_pos_of_pos (by positivity) _
    have hQR : R ≤ Q := Real.rpow_le_rpow (by positivity)
      (by nlinarith [packet_endpoint_angular_lower u hu]) hS.le
    have hN : 0 < N := packetKernel_endpoint_pos hNorm kappa hkappa m hm
    have hnorm : c0*((m : ℝ)^kappa*m) ≤ N := by
      have he : (m : ℝ)^(kappa+1) = (m : ℝ)^kappa*m := by
        rw [Real.rpow_add hmp, Real.rpow_one]
      simpa only [he] using (hnormalization m hm).1
    have htB : t/B ≤ (m : ℝ)^kappa := by
      apply (div_le_iff₀ hB).mpr
      have h := mul_le_mul_of_nonneg_right
        (packet_endpoint_taper_sqrt_weight kappa hkappa.le m (by omega) u hu)
        (Real.rpow_nonneg hmp.le kappa)
      have he : (m : ℝ)^(-kappa)*(m : ℝ)^kappa = 1 := by
        rw [← Real.rpow_add hmp]; simp
      change (t*(m : ℝ)^(-kappa))*(m : ℝ)^kappa ≤ B*(m : ℝ)^kappa at h
      rw [mul_assoc, he, mul_one] at h
      simpa only [mul_comm] using h
    have hK : |packetKernel kappa m (2*u^2-1)| ≤ C*m/(B*Q) := by
      simpa only [packetKernel, if_pos hkappa] using
        hkernel m (by omega) (-1) (by norm_num) _ (packet_endpoint_coordinate_mem u hu)
    calc
      |packetPsi kappa m u| = t*|packetKernel kappa m (2*u^2-1)|/N := by
        rw [packetPsi, if_pos hu, if_pos hkappa, abs_mul, abs_div,
          abs_of_nonneg ht, abs_of_pos hN]
        ring
      _ ≤ t*(C*m/(B*Q))/N := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hK ht) hN.le
      _ = (t/B)*(C*m/Q)/N := by ring
      _ ≤ (m : ℝ)^kappa*(C*m/Q)/N := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right htB (by positivity)) hN.le
      _ ≤ (C/c0)/Q := by
        apply (div_le_iff₀ hN).mpr
        calc
          _ = ((C/c0)/Q)*(c0*((m : ℝ)^kappa*m)) := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ ≤ (C/c0)/R := div_le_div_of_nonneg_left (by positivity) hR hQR
      _ = (C/c0)*(1+(m : ℝ)*|u|)^(-S) := by
        rw [Real.rpow_neg (by positivity : 0 ≤ 1+(m : ℝ)*|u|)]
        rfl
  · rw [packetPsi, if_neg hu, abs_zero]
    positivity

end CausalSmith.Stat.NoisydoseWeakdesignTransition

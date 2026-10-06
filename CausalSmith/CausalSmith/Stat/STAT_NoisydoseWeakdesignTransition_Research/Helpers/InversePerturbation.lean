module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DirectPerturbation
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketEndpoint

/-! Scaled inverse-regime packet profiles and their weighted cancellations, equations (20)--(23). -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
noncomputable section
open MeasureTheory Set
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- The packet derivative bound gives the global increment bound, including the zero extension. [Under the stated conditions](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: packetPsi_increment_bound
lemma packetPsi_increment_bound (kappa C c : ℝ) (m : ℕ)
    (hp : PacketBounds kappa C c m) (s t : ℝ) :
    |packetPsi kappa m s-packetPsi kappa m t| ≤ C*m*|s-t| := by
  rcases hp with ⟨_, _, hdiff, _, _, _, hd, _, _, _⟩
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x (_ : x ∈ (univ : Set ℝ)) => hdiff.differentiable (by norm_num) x)
    (fun x (_ : x ∈ (univ : Set ℝ)) => by simpa only [Real.norm_eq_abs] using hd x)
    convex_univ (mem_univ t) (mem_univ s)

/-- The scaled packet is supported on the stipulated radius. [Under the stated conditions](hyp:h,hell,ht). [This is the stated conclusion](goal). -/
-- @node: inversePerturbation_support
lemma inversePerturbation_support (beta kappa epsilon h ell : ℝ) (m : ℕ)
    (hell : 0 < ell) (t : ℝ) (ht : t ∉ Icc (-ell) ell) :
    epsilon*h^beta*packetPsi kappa m (t/ell) = 0 := by
  have hout : t/ell ∉ Icc (-1 : ℝ) 1 := by
    intro hi
    apply ht
    constructor
    · have := (le_div_iff₀ hell).mp hi.1
      linarith
    · simpa only [one_mul] using (div_le_iff₀ hell).mp hi.2
  rw [packetPsi_support kappa m (t/ell) hout, mul_zero]

/-- The scaled packet has the exact tuning amplitude at the target. [Under the stated conditions](hyp:h,hp). [This is the stated conclusion](goal). -/
-- @node: inversePerturbation_zero
lemma inversePerturbation_zero (beta kappa epsilon h ell C c : ℝ) (m : ℕ)
    (hp : PacketBounds kappa C c m) :
    epsilon*h^beta*packetPsi kappa m (0/ell) = epsilon*h^beta := by
  rcases hp with ⟨_, _, _, _, hz, _⟩
  rw [zero_div, hz, mul_one]

/-- The packet supremum bound scales by the nonnegative tuning amplitude. [Under the stated conditions](hyp:h,hp,he,hh). [This is the stated conclusion](goal). -/
-- @node: inversePerturbation_abs_bound
lemma inversePerturbation_abs_bound (beta kappa epsilon h ell C c : ℝ) (m : ℕ)
    (hp : PacketBounds kappa C c m) (he : 0 ≤ epsilon) (hh : 0 < h) (t : ℝ) :
    |epsilon*h^beta*packetPsi kappa m (t/ell)| ≤ epsilon*h^beta*C := by
  rcases hp with ⟨_, _, _, _, _, hsup, _⟩
  rw [abs_mul, abs_of_nonneg (mul_nonneg he (Real.rpow_nonneg hh.le _))]
  exact mul_le_mul_of_nonneg_left (hsup _) (by positivity)

/-- The two distance cases in (21) give a scale-free Hölder bound for the inverse packet. [Under the stated conditions](hyp:hp,he,hC,hell,hm,hb). [This is the stated conclusion](goal). -/
-- @node: inversePerturbation_holder_bound
lemma inversePerturbation_holder_bound (beta kappa epsilon ell C c : ℝ) (m : ℕ)
    (hp : PacketBounds kappa C c m) (hb : beta ∈ Icc (0 : ℝ) 1)
    (he : 0 ≤ epsilon) (hC : 0 ≤ C) (hell : 0 < ell) (hm : 0 < m) (s t : ℝ) :
    |epsilon*(ell/m)^beta*packetPsi kappa m (s/ell)-
      epsilon*(ell/m)^beta*packetPsi kappa m (t/ell)| ≤
      2*epsilon*C*|s-t|^beta := by
  let h : ℝ := ell/m
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < h := div_pos hell hmR
  have hA : 0 ≤ epsilon*h^beta := by positivity
  have hnear : |epsilon*h^beta*packetPsi kappa m (s/ell)-
      epsilon*h^beta*packetPsi kappa m (t/ell)| ≤ epsilon*h^beta*C*(|s-t|/h) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hA]
    have hi := packetPsi_increment_bound kappa C c m hp (s/ell) (t/ell)
    rw [← sub_div, abs_div, abs_of_pos hell] at hi
    calc
      _ ≤ (epsilon*h^beta)*(C*m*(|s-t|/ell)) := mul_le_mul_of_nonneg_left hi hA
      _ = _ := by dsimp [h]; field_simp
  by_cases hst : |s-t| ≤ h
  · have hr : |s-t|/h ≤ (|s-t|/h)^beta := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge'
        (div_nonneg (abs_nonneg _) hh.le) ((div_le_one hh).mpr hst) hb.1 hb.2
    calc
      _ ≤ epsilon*h^beta*C*(|s-t|/h) := hnear
      _ ≤ epsilon*h^beta*C*((|s-t|/h)^beta) := by gcongr
      _ = epsilon*C*|s-t|^beta := by
        rw [Real.div_rpow (abs_nonneg _) hh.le]; field_simp
      _ ≤ _ := by
        nlinarith [mul_nonneg (mul_nonneg he hC)
          (Real.rpow_nonneg (abs_nonneg (s-t)) beta)]
  · have hs := inversePerturbation_abs_bound beta kappa epsilon h ell C c m hp he hh s
    have ht := inversePerturbation_abs_bound beta kappa epsilon h ell C c m hp he hh t
    have hpow : h^beta ≤ |s-t|^beta :=
      Real.rpow_le_rpow hh.le (le_of_lt (lt_of_not_ge hst)) hb.1
    calc
      _ ≤ |epsilon*h^beta*packetPsi kappa m (s/ell)|+
          |epsilon*h^beta*packetPsi kappa m (t/ell)| := by
        simpa using abs_sub_le (epsilon*h^beta*packetPsi kappa m (s/ell)) 0
          (epsilon*h^beta*packetPsi kappa m (t/ell))
      _ ≤ 2*epsilon*C*h^beta := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

/-- The packet times the design density is an integrable compact signed density. [Under the stated conditions](hyp:hk). [This is the stated conclusion](goal). -/
-- @node: inversePerturbation_signed_integrable
@[fun_prop] lemma inversePerturbation_signed_integrable
    (beta kappa epsilon h ell : ℝ) (m : ℕ) (hk : 0 ≤ kappa) :
    Integrable (fun t => witnessDesignDensity kappa t *
      (epsilon*h^beta*packetPsi kappa m (t/ell))) := by
  have hc : Continuous (fun t : ℝ => (kappa+1)*2^kappa*|t|^kappa *
      (epsilon*h^beta*packetPsi kappa m (t/ell))) := by
    have hp := (packetPsi_contDiff kappa m).continuous
    fun_prop
  have heq : (fun t => witnessDesignDensity kappa t *
      (epsilon*h^beta*packetPsi kappa m (t/ell))) =
      (Icc (-1/2 : ℝ) (1/2)).indicator (fun t : ℝ =>
        (kappa+1)*2^kappa*|t|^kappa*(epsilon*h^beta*packetPsi kappa m (t/ell))) := by
    funext t
    simp only [witnessDesignDensity, indicator_apply]
    split_ifs <;> simp
  rw [heq]
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

/-- Small inverse-regime packet amplitudes give the two actual continuous threshold profiles,
with the paper's range and radius-one Hölder seminorm. [Under the stated conditions](hyp:hp,he,heSmall,hC,hell,hm,hb,hamp). [This is the stated conclusion](goal). -/
-- @node: inverse_threshold_profiles
lemma inverse_threshold_profiles (beta kappa epsilon ell C c : ℝ) (m : ℕ)
    (hp : PacketBounds kappa C c m)
    (hb : beta ∈ Icc (0 : ℝ) 1) (he : 0 ≤ epsilon) (heSmall : 2*epsilon*C ≤ 1)
    (hC : 0 ≤ C) (hell : 0 < ell) (hm : 0 < m)
    (hamp : epsilon*(ell/m)^beta*C ≤ 3/8) :
    ∃ muPlus muMinus : ThresholdProfile,
      (∀ a : Dose, (muPlus a : ℝ) = 1/2 + (epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell)) ∧
        (muMinus a : ℝ) = 1/2 - (epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell))) ∧
      (∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧
        (muMinus a : ℝ) ∈ Icc (1/8) (7/8)) ∧
      (∀ a b, |(muPlus a : ℝ)-(muPlus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta ∧
        |(muMinus a : ℝ)-(muMinus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < ell/m := div_pos hell hmR
  have hcontinuous := (packetPsi_contDiff kappa m).continuous
  have hbounds (a : Dose) := inversePerturbation_abs_bound beta kappa epsilon (ell/m) ell C c m
    hp he hh ((a : ℝ)-a0)
  have hlower (a : Dose) := (abs_le.mp (hbounds a)).1
  have hupper (a : Dose) := (abs_le.mp (hbounds a)).2
  have hplus (a : Dose) : 1/2 + (epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell)) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hlower a, hupper a]
  have hminus (a : Dose) : 1/2 - (epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell)) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hlower a, hupper a]
  let muPlus : ThresholdProfile :=
    ⟨fun a => ⟨1/2 + (epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell)), hplus a⟩, by fun_prop⟩
  let muMinus : ThresholdProfile :=
    ⟨fun a => ⟨1/2 - (epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell)), hminus a⟩, by fun_prop⟩
  refine ⟨muPlus, muMinus, (fun a => ⟨rfl, rfl⟩), ?_, ?_⟩
  · intro a
    change (1/2 + (epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell)) ∈ Icc (1/8 : ℝ) (7/8)) ∧
      (1/2 - (epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell)) ∈ Icc (1/8 : ℝ) (7/8))
    constructor <;> constructor <;> linarith [hlower a, hupper a]
  · intro a b
    have hinc := inversePerturbation_holder_bound beta kappa epsilon ell C c m hp hb he hC hell hm
      ((a : ℝ)-a0) ((b : ℝ)-a0)
    rw [sub_sub_sub_cancel_right] at hinc
    have hfinal := hinc.trans (mul_le_of_le_one_left
      (Real.rpow_nonneg (abs_nonneg ((a : ℝ)-(b : ℝ))) beta) heSmall)
    change |(1/2 + (epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell)))-
        (1/2 + (epsilon*(ell/m)^beta*packetPsi kappa m (((b : ℝ)-a0)/ell)))| ≤ _ ∧
      |(1/2 - (epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell)))-
        (1/2 - (epsilon*(ell/m)^beta*packetPsi kappa m (((b : ℝ)-a0)/ell)))| ≤ _
    constructor
    · simpa only [add_sub_add_left_eq_sub] using hfinal
    · simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hfinal


/-- On a packet's support the public design density is its unclipped power law. [Under the stated conditions](hyp:h,hell). [This is the stated conclusion](goal). -/
-- @node: inversePerturbation_weighted_scale
lemma inversePerturbation_weighted_scale (beta kappa epsilon h ell : ℝ) (m j : ℕ)
    (hell : ell ∈ Ioc (0 : ℝ) (1/4)) (t : ℝ) :
    t^j * (witnessDesignDensity kappa t *
      (epsilon*h^beta*packetPsi kappa m (t/ell))) =
      ((kappa+1)*2^kappa*(epsilon*h^beta)*ell^kappa*ell^j) *
        (|t/ell|^kappa*(t/ell)^j*packetPsi kappa m (t/ell)) := by
  by_cases ht : t ∈ Icc (-ell) ell
  · have htlarge : t ∈ Icc (-1/2 : ℝ) (1/2) := by
      constructor <;> linarith [ht.1, ht.2, hell.2]
    rw [witnessDesignDensity, if_pos htlarge]
    have hscale : t = ell*(t/ell) := by field_simp [hell.1.ne']
    have habs : |t|^kappa = ell^kappa*|t/ell|^kappa := by
      conv_lhs => rw [hscale, abs_mul, abs_of_pos hell.1]
      exact Real.mul_rpow hell.1.le (abs_nonneg _)
    have hpow : t^j = ell^j*(t/ell)^j := by
      conv_lhs => rw [hscale, mul_pow]
    rw [habs, hpow]
    ring
  · have hpsi : packetPsi kappa m (t/ell) = 0 := by
      have hzero := inversePerturbation_support 0 kappa 1 1 ell m hell.1 t ht
      simpa using hzero
    simp [hpsi]

/-- Change of variables transfers every weighted packet cancellation to the signed latent density. [Under the stated conditions](hyp:h,hp,hell,hj). [This is the stated conclusion](goal). -/
-- @node: inversePerturbation_moment_zero
lemma inversePerturbation_moment_zero (beta kappa epsilon h ell C c : ℝ) (m j : ℕ)
    (hp : PacketBounds kappa C c m) (hell : ell ∈ Ioc (0 : ℝ) (1/4))
    (hj : (j : ℝ) < c*m) :
    (∫ t, t^j * (witnessDesignDensity kappa t *
      (epsilon*h^beta*packetPsi kappa m (t/ell)))) = 0 := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, hcancel⟩
  simp_rw [inversePerturbation_weighted_scale beta kappa epsilon h ell m j hell]
  rw [integral_const_mul, Measure.integral_comp_div
    (fun u => |u|^kappa*u^j*packetPsi kappa m u) ell]
  have hfull : (∫ u, |u|^kappa*u^j*packetPsi kappa m u) =
      ∫ u in Icc (-1 : ℝ) 1, |u|^kappa*u^j*packetPsi kappa m u := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    rw [packetPsi_support kappa m u hu, mul_zero]
  rw [hfull, hcancel j hj]
  simp

/-- The floor cancellation order only uses moments strictly below the packet's real cutoff. [Under the stated conditions](hyp:hc,hj). [This is the stated conclusion](goal). -/
-- @node: packet_floor_moment_cutoff
lemma packet_floor_moment_cutoff (c : ℝ) (m j : ℕ) (hc : 0 ≤ c)
    (hj : j < Nat.floor (c*m)) : (j : ℝ) < c*m := by
  have hfloor : (Nat.floor (c*m) : ℝ) ≤ c*m := Nat.floor_le (by positivity)
  exact (show (j : ℝ) < Nat.floor (c*m) by exact_mod_cast hj).trans_le hfloor

/-- The packet absolute-mass bound scales as h to the power beta plus kappa plus one, as in (23). [Under the stated conditions](hyp:hp,hk,he,hm,hell). [This is the stated conclusion](goal). -/
-- @node: inversePerturbation_absolute_mass_le
lemma inversePerturbation_absolute_mass_le (beta kappa epsilon ell C c : ℝ) (m : ℕ)
    (hp : PacketBounds kappa C c m) (hk : 0 ≤ kappa) (he : 0 ≤ epsilon)
    (hell : ell ∈ Ioc (0 : ℝ) (1/4)) (hm : 0 < m) :
    (∫ t, |witnessDesignDensity kappa t *
      (epsilon*(ell/m)^beta*packetPsi kappa m (t/ell))|) ≤
      (kappa+1)*2^kappa*epsilon*C*(ell/m)^(beta+kappa+1) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < ell/m := div_pos hell.1 hmR
  have hell0 : 0 < ell := hell.1
  let A : ℝ := (kappa+1)*2^kappa*(epsilon*(ell/m)^beta)*ell^kappa
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hid (t : ℝ) : |witnessDesignDensity kappa t *
      (epsilon*(ell/m)^beta*packetPsi kappa m (t/ell))| =
      A*(|t/ell|^kappa*|packetPsi kappa m (t/ell)|) := by
    have hs := inversePerturbation_weighted_scale beta kappa epsilon (ell/m) ell m 0 hell t
    simp only [pow_zero, one_mul, mul_one] at hs
    rw [hs, abs_mul, abs_of_nonneg hA, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  simp_rw [hid]
  rw [integral_const_mul, Measure.integral_comp_div
    (fun u => |u|^kappa*|packetPsi kappa m u|) ell, abs_of_pos hell.1, smul_eq_mul]
  have hfull : (∫ u, |u|^kappa*|packetPsi kappa m u|) =
      ∫ u in Icc (-1 : ℝ) 1, |u|^kappa*|packetPsi kappa m u| := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    simp [packetPsi_support kappa m u hu]
  rw [hfull]
  rcases hp with ⟨_, _, _, _, _, _, _, hmass, _, _⟩
  calc
    _ ≤ A*(ell*(C*(m : ℝ)^(-kappa-1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass hell.1.le) hA
    _ = (kappa+1)*2^kappa*epsilon*C*(ell/m)^(beta+kappa+1) := by
      have hr : (ell/m)^(beta+kappa+1) =
          (ell/m)^beta * ell^kappa * ell * (m : ℝ)^(-kappa-1) := by
        rw [show beta+kappa+1 = beta+(kappa+1) by ring, Real.rpow_add hh,
          Real.div_rpow hell.1.le hmR.le (kappa+1),
          Real.rpow_add hell.1, Real.rpow_one,
          show -kappa-1 = -(kappa+1) by ring, Real.rpow_neg hmR.le]
        ring
      rw [hr]
      dsimp [A]
      ring

end CausalSmith.Stat.NoisydoseWeakdesignTransition

module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.InversePerturbation
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.ObservedMarkedChiSquare

/-! Equation (27): observed chi-square control from compact signed perturbations and packet mass. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]

/-- The threshold mean formula identifies its signed density on the entire real line. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hformula). -/
-- @node: markedSignedProfile_eq_perturbation
lemma markedSignedProfile_eq_perturbation (kappa : ℝ) (mu : ThresholdProfile)
    (delta : ℝ → ℝ)
    (hformula : ∀ a : Dose, (mu a : ℝ) = 1/2 + delta ((a : ℝ)-a0)) :
    markedSignedProfile kappa mu = fun t => witnessDesignDensity kappa t * delta t := by
  funext t
  by_cases ht : t ∈ Icc (-1/2 : ℝ) (1/2)
  · have ha : t+a0 ∈ Icc (0 : ℝ) 1 := by dsimp [a0]; constructor <;> linarith [ht.1, ht.2]
    have hp : ((Set.projIcc 0 1 zero_le_one (t+a0) : Dose) : ℝ) = t+a0 :=
      congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ha)
    simp only [markedSignedProfile, hformula, hp, add_sub_cancel_right, add_sub_cancel_left]
  · simp only [markedSignedProfile, witnessDesignDensity, if_neg ht, zero_mul]

/-- Equations (12), (24), and (26) give the observed moment-tail comparison for any constructed mean. [Under the stated conditions](hyp:hell,hk,hs,hrange,hformula,hsupp,hmom). [This is the stated conclusion](goal). -/
-- @node: observed_perturbation_chiSq_moment_bound
lemma observed_perturbation_chiSq_moment_bound (E : PathSpace S) (kappa sigma ell : ℝ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (hs : sigma ∈ Ioc (0 : ℝ) (1/4))
    (hell : 0 ≤ ell) (J : ℕ) (mu : ThresholdProfile) (delta : ℝ → ℝ)
    (hrange : ∀ a, (mu a : ℝ) ∈ Icc (1/8) (7/8))
    (hformula : ∀ a : Dose, (mu a : ℝ) = 1/2 + delta ((a : ℝ)-a0))
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → delta t = 0)
    (hmom : ∀ j < J, ∫ t, t^j * (witnessDesignDensity kappa t * delta t) = 0) :
    Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa mu))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤
      (4 / (Real.exp (-1/2)*sigma^(kappa+1))) *
        (∫ t, |witnessDesignDensity kappa t * delta t|)^2 * momentTail sigma ell J := by
  have hid := markedSignedProfile_eq_perturbation kappa mu delta hformula
  have hv : Integrable (fun t => witnessDesignDensity kappa t * delta t) := by
    rw [← hid]
    exact marked_profile_signed_integrable kappa hk.1 mu
  have hm : Measurable (fun t => witnessDesignDensity kappa t * delta t) := by
    rw [← hid]
    unfold markedSignedProfile
    have hk0 : 0 ≤ kappa := hk.1
    fun_prop
  have hb := gaussian_observed_energy_moment_bound kappa sigma ell hk hs hell J
    _ hv hm (fun t ht => by rw [hsupp t ht, mul_zero]) hmom
  have hc := (observed_marked_chiSq_identity E kappa sigma hk hs mu hrange).2
  change Causalean.Stat.chiSqDiv _ _ = 4 * ∫ w,
    (smoothSigned sigma (markedSignedProfile kappa mu) w)^2 /
      smoothSigned sigma (witnessDesignDensity kappa) w at hc
  rw [hc, hid]
  exact (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring)

/-- A bound on absolute signed mass gives the precise bandwidth power in equation (27). [Under the stated conditions](hyp:h,hh,hell,hK,hk,hs,hrange,hformula,hsupp,hmom,hmass). [This is the stated conclusion](goal). -/
-- @node: observed_perturbation_chiSq_scaled_bound
lemma observed_perturbation_chiSq_scaled_bound (E : PathSpace S) (beta kappa sigma h ell K : ℝ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (hs : sigma ∈ Ioc (0 : ℝ) (1/4))
    (hh : 0 < h) (hell : 0 ≤ ell) (hK : 0 ≤ K) (J : ℕ)
    (mu : ThresholdProfile) (delta : ℝ → ℝ)
    (hrange : ∀ a, (mu a : ℝ) ∈ Icc (1/8) (7/8))
    (hformula : ∀ a : Dose, (mu a : ℝ) = 1/2 + delta ((a : ℝ)-a0))
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → delta t = 0)
    (hmom : ∀ j < J, ∫ t, t^j * (witnessDesignDensity kappa t * delta t) = 0)
    (hmass : (∫ t, |witnessDesignDensity kappa t * delta t|) ≤ K*h^(beta+kappa+1)) :
    Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa mu))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤
      (4 / Real.exp (-1/2)*K^2)*sigma^(-kappa-1)*h^(2*beta+2*kappa+2)*
        momentTail sigma ell J := by
  have ht : 0 ≤ momentTail sigma ell J := by
    unfold momentTail
    exact tsum_nonneg (fun j => by split_ifs <;> positivity)
  have hmass0 : 0 ≤ ∫ t, |witnessDesignDensity kappa t * delta t| :=
    integral_nonneg (fun t => abs_nonneg _)
  have hsq := pow_le_pow_left₀ hmass0 hmass 2
  have hc : 0 ≤ 4 / (Real.exp (-1/2)*sigma^(kappa+1)) := div_nonneg (by norm_num)
    (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hs.1.le _))
  calc
    _ ≤ (4 / (Real.exp (-1/2)*sigma^(kappa+1))) *
        (∫ t, |witnessDesignDensity kappa t * delta t|)^2 * momentTail sigma ell J :=
      observed_perturbation_chiSq_moment_bound E kappa sigma ell hk hs hell J mu delta
        hrange hformula hsupp hmom
    _ ≤ (4 / (Real.exp (-1/2)*sigma^(kappa+1))) *
        (K*h^(beta+kappa+1))^2 * momentTail sigma ell J := by gcongr
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hh.le]
      norm_num only [Nat.cast_ofNat]
      rw [show (beta+kappa+1)* (2 : ℝ) = 2*beta+2*kappa+2 by ring,
        show -kappa-1 = -(kappa+1) by ring, Real.rpow_neg hs.1.le]
      ring

/-- Both signs share the same mass and moment control, hence the same observed comparison constant. [Under the stated conditions](hyp:h,hh,hell,hK,hk,hs,hrange,hformula,hsupp,hmom,hmass). [This is the stated conclusion](goal). -/
-- @node: observed_perturbation_pair_chiSq_scaled_bound
lemma observed_perturbation_pair_chiSq_scaled_bound (E : PathSpace S)
    (beta kappa sigma h ell K : ℝ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (hs : sigma ∈ Ioc (0 : ℝ) (1/4))
    (hh : 0 < h) (hell : 0 ≤ ell) (hK : 0 ≤ K) (J : ℕ)
    (muPlus muMinus : ThresholdProfile) (delta : ℝ → ℝ)
    (hrange : ∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧
      (muMinus a : ℝ) ∈ Icc (1/8) (7/8))
    (hformula : ∀ a : Dose, (muPlus a : ℝ) = 1/2 + delta ((a : ℝ)-a0) ∧
      (muMinus a : ℝ) = 1/2 - delta ((a : ℝ)-a0))
    (hsupp : ∀ t, t ∉ Icc (-ell) ell → delta t = 0)
    (hmom : ∀ j < J, ∫ t, t^j * (witnessDesignDensity kappa t * delta t) = 0)
    (hmass : (∫ t, |witnessDesignDensity kappa t * delta t|) ≤ K*h^(beta+kappa+1)) :
    let B := (4 / Real.exp (-1/2)*K^2)*sigma^(-kappa-1)*h^(2*beta+2*kappa+2)*
      momentTail sigma ell J
    Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ B ∧
    Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ B := by
  constructor
  · exact observed_perturbation_chiSq_scaled_bound E beta kappa sigma h ell K hk hs hh hell hK
      J muPlus delta (fun a => (hrange a).1) (fun a => (hformula a).1) hsupp hmom hmass
  · apply observed_perturbation_chiSq_scaled_bound E beta kappa sigma h ell K hk hs hh hell hK
      J muMinus (fun t => -delta t) (fun a => (hrange a).2)
    · intro a
      simpa only [sub_eq_add_neg] using (hformula a).2
    · intro t ht
      rw [hsupp t ht, neg_zero]
    · intro j hj
      simp only [mul_neg, integral_neg, hmom j hj, neg_zero]
    · simpa only [mul_neg, abs_neg] using hmass

/-- The packet's scaled mass and exact cancellations establish equation (27) for both inverse alternatives. [Under the stated conditions](hyp:hp,he,hC,hc,hm,hk,hs,hell,hrange,hformula). [This is the stated conclusion](goal). -/
-- @node: inverse_profile_pair_chiSq_bound
lemma inverse_profile_pair_chiSq_bound (E : PathSpace S)
    (beta kappa sigma epsilon ell Cpacket cPacket : ℝ) (m : ℕ)
    (hp : PacketBounds kappa Cpacket cPacket m)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (hs : sigma ∈ Ioc (0 : ℝ) (1/4))
    (he : 0 ≤ epsilon) (hC : 0 ≤ Cpacket) (hc : 0 ≤ cPacket)
    (hell : ell ∈ Ioc (0 : ℝ) (1/4)) (hm : 0 < m)
    (muPlus muMinus : ThresholdProfile)
    (hrange : ∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧
      (muMinus a : ℝ) ∈ Icc (1/8) (7/8))
    (hformula : ∀ a : Dose,
      (muPlus a : ℝ) = 1/2 + epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell) ∧
      (muMinus a : ℝ) = 1/2 - epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell)) :
    let K := (kappa+1)*2^kappa*epsilon*Cpacket
    let B := (4 / Real.exp (-1/2)*K^2)*sigma^(-kappa-1)*(ell/m)^(2*beta+2*kappa+2)*
      momentTail sigma ell (Nat.floor (cPacket*m))
    Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ B ∧
    Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ B := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply observed_perturbation_pair_chiSq_scaled_bound E beta kappa sigma (ell/m) ell
    ((kappa+1)*2^kappa*epsilon*Cpacket) hk hs (div_pos hell.1 hmR) hell.1.le
    (by have hk0 := hk.1; positivity) (Nat.floor (cPacket*m)) muPlus muMinus
    (fun t => epsilon*(ell/m)^beta*packetPsi kappa m (t/ell)) hrange hformula
  · exact inversePerturbation_support beta kappa epsilon (ell/m) ell m hell.1
  · intro j hj
    exact inversePerturbation_moment_zero beta kappa epsilon (ell/m) ell Cpacket cPacket
      m j hp hell (packet_floor_moment_cutoff cPacket m j hc hj)
  · exact inversePerturbation_absolute_mass_le beta kappa epsilon ell Cpacket cPacket
      m hp hk.1 he hell hm

/-- The compact direct bump has the bandwidth mass required after equation (27). [Under the stated conditions](hyp:h,hk,he,hh). [This is the stated conclusion](goal). -/
-- @node: directPerturbation_absolute_mass_le
lemma directPerturbation_absolute_mass_le (beta kappa epsilon h : ℝ)
    (hk : 0 ≤ kappa) (he : 0 ≤ epsilon) (hh : 0 < h) :
    (∫ t, |witnessDesignDensity kappa t * directPerturbation beta epsilon h t|) ≤
      (2*(kappa+1)*2^kappa*epsilon)*h^(beta+kappa+1) := by
  let A := (kappa+1)*2^kappa*h^kappa*(epsilon*h^beta)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hi := (directPerturbation_signed_integrable beta kappa epsilon h hk hh).abs
  have hs : (∫ t, |witnessDesignDensity kappa t * directPerturbation beta epsilon h t|) =
      ∫ t in Icc (-h) h, |witnessDesignDensity kappa t * directPerturbation beta epsilon h t| := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [directPerturbation_support beta epsilon h t ht, mul_zero, abs_zero]
  rw [hs]
  have hb : ∀ t ∈ Icc (-h) h,
      |witnessDesignDensity kappa t * directPerturbation beta epsilon h t| ≤ A := by
    intro t ht
    have hd := directPerturbation_bounds beta epsilon h t he hh
    rw [abs_of_nonneg (mul_nonneg (witnessDesignDensity_nonneg kappa t hk) hd.1)]
    have hg : witnessDesignDensity kappa t ≤ (kappa+1)*2^kappa*h^kappa := by
      unfold witnessDesignDensity
      split_ifs
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _) (abs_le.mpr ht) hk) (by positivity)
      · positivity
    exact mul_le_mul hg hd.2 hd.1 (by positivity)
  calc
    _ ≤ ∫ _t in Icc (-h) h, A :=
      setIntegral_mono_on hi.integrableOn (continuous_const.integrableOn_Icc) measurableSet_Icc hb
    _ = (2*(kappa+1)*2^kappa*epsilon)*h^(beta+kappa+1) := by
      rw [setIntegral_const, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
      rw [Real.rpow_add hh, Real.rpow_add hh, Real.rpow_one]
      dsimp [A]
      ring

/-- The latent quadratic energy in equation (18) has the direct-regime bandwidth power. [Under the stated conditions](hyp:h,hk,he,hh). [This is the stated conclusion](goal). -/
-- @node: directPerturbation_quadratic_energy_le
lemma directPerturbation_quadratic_energy_le (beta kappa epsilon h : ℝ)
    (hk : 0 ≤ kappa) (he : 0 ≤ epsilon) (hh : 0 < h) :
    (∫ t, witnessDesignDensity kappa t * (directPerturbation beta epsilon h t)^2) ≤
      (2*(kappa+1)*2^kappa*epsilon^2)*h^(2*beta+kappa+1) := by
  have hcont : Continuous (fun t : ℝ => (kappa+1)*2^kappa*|t|^kappa *
      (directPerturbation beta epsilon h t)^2) := by fun_prop
  have hid : (fun t => witnessDesignDensity kappa t * (directPerturbation beta epsilon h t)^2) =
      (Icc (-1/2 : ℝ) (1/2)).indicator (fun t : ℝ =>
        (kappa+1)*2^kappa*|t|^kappa * (directPerturbation beta epsilon h t)^2) := by
    funext t
    simp only [witnessDesignDensity, indicator_apply]
    split_ifs <;> simp
  have hi : Integrable (fun t => witnessDesignDensity kappa t *
      (directPerturbation beta epsilon h t)^2) := by
    rw [hid]
    exact hcont.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hm := (directPerturbation_signed_integrable beta kappa epsilon h hk hh).abs
  have hA : 0 ≤ epsilon*h^beta := mul_nonneg he (Real.rpow_nonneg hh.le _)
  calc
    _ ≤ ∫ t, (epsilon*h^beta)*|witnessDesignDensity kappa t * directPerturbation beta epsilon h t| := by
      apply integral_mono hi (hm.const_mul _)
      intro t
      have hb := directPerturbation_bounds beta epsilon h t he hh
      have hg := witnessDesignDensity_nonneg kappa t hk
      dsimp only
      rw [abs_of_nonneg (mul_nonneg hg hb.1)]
      nlinarith [mul_nonneg hg (mul_nonneg hb.1 (sub_nonneg.mpr hb.2))]
    _ = (epsilon*h^beta)*(∫ t, |witnessDesignDensity kappa t * directPerturbation beta epsilon h t|) :=
      integral_const_mul _ _
    _ ≤ (epsilon*h^beta)*((2*(kappa+1)*2^kappa*epsilon)*h^(beta+kappa+1)) :=
      mul_le_mul_of_nonneg_left (directPerturbation_absolute_mass_le beta kappa epsilon h hk he hh) hA
    _ = _ := by
      have hr : h^(2*beta+kappa+1) = h^beta*h^(beta+kappa+1) := by
        rw [show 2*beta+kappa+1 = beta+(beta+kappa+1) by ring, Real.rpow_add hh]
      rw [hr]
      ring

/-- The direct pair also obeys equation (27), with cancellation order zero. [Under the stated conditions](hyp:h,he,hh,hk,hs,hrange,hformula). [This is the stated conclusion](goal). -/
-- @node: direct_profile_pair_chiSq_bound
lemma direct_profile_pair_chiSq_bound (E : PathSpace S)
    (beta kappa sigma epsilon h : ℝ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (hs : sigma ∈ Ioc (0 : ℝ) (1/4))
    (he : 0 ≤ epsilon) (hh : 0 < h) (muPlus muMinus : ThresholdProfile)
    (hrange : ∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧
      (muMinus a : ℝ) ∈ Icc (1/8) (7/8))
    (hformula : ∀ a : Dose,
      (muPlus a : ℝ) = 1/2 + directPerturbation beta epsilon h ((a : ℝ)-a0) ∧
      (muMinus a : ℝ) = 1/2 - directPerturbation beta epsilon h ((a : ℝ)-a0)) :
    let K := 2*(kappa+1)*2^kappa*epsilon
    let B := (4 / Real.exp (-1/2)*K^2)*sigma^(-kappa-1)*h^(2*beta+2*kappa+2)*
      momentTail sigma h 0
    Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ B ∧
    Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ B := by
  apply observed_perturbation_pair_chiSq_scaled_bound E beta kappa sigma h h
    (2*(kappa+1)*2^kappa*epsilon) hk hs hh hh.le
    (by have hk0 := hk.1; positivity) 0 muPlus muMinus
    (directPerturbation beta epsilon h) hrange hformula
  · exact directPerturbation_support beta epsilon h
  · intro j hj
    exact False.elim (Nat.not_lt_zero j hj)
  · exact directPerturbation_absolute_mass_le beta kappa epsilon h hk.1 he hh

end CausalSmith.Stat.NoisydoseWeakdesignTransition

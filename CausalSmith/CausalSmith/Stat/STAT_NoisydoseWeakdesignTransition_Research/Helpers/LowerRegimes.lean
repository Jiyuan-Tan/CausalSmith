module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DirectObservedContraction
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.InversePerturbation
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.LowerAssembly
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.LowerCompactTuning
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.LowerTuning
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.ObservedPerturbationBounds
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketEndpoint
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketInterior
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.ZeroNoiseObserved

/-! Helpers — LowerRegimes -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
universe u
variable {S : Type*} [MeasurableSpace S]


/-- The same centered perturbation determines both threshold profiles. Direct tuning uses
h0=n^(-1/d); inverse tuning uses the normalized packet, h=ell/m and J=floor(cPacket*m).
Support and weighted cancellations are conclusions about that constructed perturbation. -/
def LowerProfileConstruction (beta kappa : ℝ) (n : ℕ) (sigma epsilon cPacket : ℝ)
    (muPlus muMinus : ThresholdProfile) (h ell : ℝ) (m J : ℕ) : Prop :=
  let delta : ℝ → ℝ := if sigma ≤ directScale beta kappa n then
    directPerturbation beta epsilon (directScale beta kappa n)
    else fun t => epsilon*h^beta*packetPsi kappa m (t/ell)
  h ∈ Ioc (0 : ℝ) (1/4) ∧ -- @realizes h(positive bandwidth at most 1/4)
  ell ∈ Ioc (0 : ℝ) (1/4) ∧ -- @realizes ellrad(positive support radius at most 1/4)
  (sigma ≤ directScale beta kappa n →
    h = directScale beta kappa n ∧ ell = h ∧ J = 0) ∧
  (directScale beta kappa n < sigma →
    4 ≤ m ∧ h = ell/m ∧ J = Nat.floor (cPacket*m) ∧ 1 ≤ J) ∧ -- @realizes Jmom(cancellation order from packet degree)
  (∀ a : Dose, (muPlus a : ℝ) = 1/2 + delta ((a : ℝ)-a0) ∧
    (muMinus a : ℝ) = 1/2 - delta ((a : ℝ)-a0)) ∧
  (∀ t, t ∉ Icc (-ell) ell → delta t = 0) ∧
  Integrable (fun t => witnessDesignDensity kappa t * delta t) ∧
  (∀ j : ℕ, j < J → ∫ t, t^j * (witnessDesignDensity kappa t * delta t) = 0)

/-- Equations (14)--(15) provide legal direct-regime profiles with the full localization
construction, including compact support and signed-density integrability. [Under the stated conditions](hyp:hk,he,heSmall,hsigma). [This is the stated conclusion](goal). [Under the stated conditions](hyp:hb,hk,he,heSmall,hh,hamp,hsigma). [This is the stated conclusion](goal). [Under the stated conditions](hyp:hb,hk,he,heSmall,hh,hamp,hsigma). [This is the stated conclusion](goal). [Under the stated conditions](hyp:hb,hk,he,heSmall,hh,hamp,hsigma). [This is the stated conclusion](goal). -/
-- @node: direct_lower_profile_construction
lemma direct_lower_profile_construction (beta kappa : ℝ) (n : ℕ)
    (sigma epsilon cPacket : ℝ) (hb : beta ∈ Icc (0 : ℝ) 1) (hk : 0 ≤ kappa)
    (he : 0 ≤ epsilon) (heSmall : 4*epsilon ≤ 1)
    (hh : directScale beta kappa n ∈ Ioc (0 : ℝ) (1/4))
    (hamp : epsilon*(directScale beta kappa n)^beta ≤ 3/8)
    (hsigma : sigma ≤ directScale beta kappa n) :
    ∃ muPlus muMinus : ThresholdProfile,
      (∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧ (muMinus a : ℝ) ∈ Icc (1/8) (7/8)) ∧
      (∀ a b, |(muPlus a : ℝ)-(muPlus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta ∧
        |(muMinus a : ℝ)-(muMinus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta) ∧
      LowerProfileConstruction beta kappa n sigma epsilon cPacket muPlus muMinus
        (directScale beta kappa n) (directScale beta kappa n) 0 0 := by
  obtain ⟨muPlus, muMinus, hformula, hrange, hholder⟩ :=
    direct_threshold_profiles beta epsilon (directScale beta kappa n) hb he heSmall hh.1 hamp
  refine ⟨muPlus, muMinus, hrange, hholder, ?_⟩
  simp only [LowerProfileConstruction, if_pos hsigma]
  refine ⟨hh, hh, (fun _ => ⟨True.intro, True.intro, True.intro⟩), ?_, hformula, ?_,
    directPerturbation_signed_integrable beta kappa epsilon _ hk hh.1, ?_⟩
  · intro hinverse
    exact False.elim (not_lt_of_ge hsigma hinverse)
  · intro t ht
    exact directPerturbation_support beta epsilon _ t ht
  · intro j hj
    exact False.elim (Nat.not_lt_zero j hj)

/-- The direct profiles satisfy their localization construction and the Gaussian-series
comparison (27) whenever the public noise is positive. [Under the stated conditions](hyp:he,heSmall,hsigma,hb,hk,hh,hamp,hs). [This is the stated conclusion](goal). -/
-- @node: direct_lower_profile_chiSq_construction
lemma direct_lower_profile_chiSq_construction (E : PathSpace S)
    (beta kappa : ℝ) (n : ℕ) (sigma epsilon cPacket : ℝ)
    (hb : beta ∈ Icc (0 : ℝ) 1) (hk : kappa ∈ Icc (0 : ℝ) 2)
    (he : 0 ≤ epsilon) (heSmall : 4*epsilon ≤ 1)
    (hh : directScale beta kappa n ∈ Ioc (0 : ℝ) (1/4))
    (hamp : epsilon*(directScale beta kappa n)^beta ≤ 3/8)
    (hsigma : sigma ≤ directScale beta kappa n)
    (hs : sigma ∈ Icc (0 : ℝ) (1/4)) :
    let h := directScale beta kappa n
    let K := 2*(kappa+1)*2^kappa*epsilon
    let B := (4 / Real.exp (-1/2)*K^2)*sigma^(-kappa-1)*h^(2*beta+2*kappa+2)*
      momentTail sigma h 0
    ∃ muPlus muMinus : ThresholdProfile,
      (∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧ (muMinus a : ℝ) ∈ Icc (1/8) (7/8)) ∧
      (∀ a b, |(muPlus a : ℝ)-(muPlus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta ∧
        |(muMinus a : ℝ)-(muMinus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta) ∧
      LowerProfileConstruction beta kappa n sigma epsilon cPacket muPlus muMinus h h 0 0 ∧
      (0 < sigma →
        Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
          (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ B ∧
        Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
          (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ B) := by
  obtain ⟨muPlus, muMinus, hrange, hholder, hconstruction⟩ :=
    direct_lower_profile_construction beta kappa n sigma epsilon cPacket hb hk.1
      he heSmall hh hamp hsigma
  refine ⟨muPlus, muMinus, hrange, hholder, hconstruction, ?_⟩
  intro hs0
  have hformula : ∀ a : Dose,
      (muPlus a : ℝ) = 1/2 + directPerturbation beta epsilon (directScale beta kappa n) ((a : ℝ)-a0) ∧
      (muMinus a : ℝ) = 1/2 - directPerturbation beta epsilon (directScale beta kappa n) ((a : ℝ)-a0) := by
    have hf := hconstruction.2.2.2.2.1
    simpa only [if_pos hsigma] using hf
  exact direct_profile_pair_chiSq_bound E beta kappa sigma epsilon
    (directScale beta kappa n) hk ⟨hs0, hs.2⟩ he hh.1 muPlus muMinus hrange hformula

/-- Equations (13)--(16) and the positive-noise comparison (27) hold for the
same direct profiles after a deterministic, noise-independent sample cutoff.
The amplitude and bandwidth range conditions are derived from the public tuning. [Under the stated conditions](hyp:he,heSmall,hb,hk). [This is the stated conclusion](goal). -/
-- @node: direct_lower_profile_frontier_construction
lemma direct_lower_profile_frontier_construction (beta kappa epsilon cPacket : ℝ)
    (hb : beta ∈ Ioc (0 : ℝ) 1) (hk : kappa ∈ Icc (0 : ℝ) 2)
    (he : 0 ≤ epsilon) (heSmall : epsilon ≤ 1/8) :
    ∃ n0 : ℕ, 2 ≤ n0 ∧
      ∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S,
      ∀ n ≥ n0, ∀ sigma ∈ Icc (0 : ℝ) (1/4),
      sigma ≤ directScale beta kappa n →
      ∃ muPlus muMinus : ThresholdProfile,
        (∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧
          (muMinus a : ℝ) ∈ Icc (1/8) (7/8)) ∧
        (∀ a b, |(muPlus a : ℝ)-(muPlus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta ∧
          |(muMinus a : ℝ)-(muMinus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta) ∧
        |causalTarget E (lowerWitnessLaw E kappa muPlus)-
          causalTarget E (lowerWitnessLaw E kappa muMinus)| =
            (2*epsilon)*frontierRate beta kappa sigma n ∧
        LowerProfileConstruction beta kappa n sigma epsilon cPacket muPlus muMinus
          (directScale beta kappa n) (directScale beta kappa n) 0 0 ∧
        (0 < sigma →
          let h := directScale beta kappa n
          let K := 2*(kappa+1)*2^kappa*epsilon
          let B := (4/Real.exp (-1/2)*K^2)*sigma^(-kappa-1)*
            h^(2*beta+2*kappa+2)*momentTail sigma h 0
          Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
            (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ B ∧
          Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
            (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ B) := by
  have hd : 0 < effDim beta kappa := by unfold effDim; linarith [hb.1, hk.1]
  obtain ⟨n0, hn0, hcutoff⟩ := lower_direct_scale_sample_cutoff beta kappa hd
  refine ⟨n0, hn0, ?_⟩
  intro S _ E n hn sigma hs hsigma
  have hh := hcutoff n hn
  have hb0 : beta ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
  have hamp : epsilon*(directScale beta kappa n)^beta ≤ 3/8 := by
    have hr := Real.rpow_le_one hh.1.le (hh.2.trans (by norm_num)) hb0.1
    have := mul_le_mul_of_nonneg_left hr he
    linarith
  obtain ⟨muPlus, muMinus, hrange, hholder, hconstruction, hchi⟩ :=
    direct_lower_profile_chiSq_construction E beta kappa n sigma epsilon cPacket
      hb0 hk he (by linarith) hh hamp hsigma hs
  have hformula : ∀ a : Dose,
      (muPlus a : ℝ) = 1/2 + directPerturbation beta epsilon (directScale beta kappa n) ((a : ℝ)-a0) ∧
      (muMinus a : ℝ) = 1/2 - directPerturbation beta epsilon (directScale beta kappa n) ((a : ℝ)-a0) := by
    have hf := hconstruction.2.2.2.2.1
    simpa only [if_pos hsigma] using hf
  exact ⟨muPlus, muMinus, hrange, hholder,
    direct_profile_frontier_separation E beta kappa epsilon sigma n hk he hh.1
      hsigma muPlus muMinus hformula, hconstruction, hchi⟩

/-- The direct profile construction also supplies equation (18) for every positive noise,
with its sample budget independent of the noise scale. [Under the stated conditions](hyp:he,heSmall,hsigma,hd,hn,hb,hk,hh,hamp,hs). [This is the stated conclusion](goal). -/
-- @node: direct_lower_profile_observed_budget_construction
lemma direct_lower_profile_observed_budget_construction (E : PathSpace S)
    (beta kappa : ℝ) (n : ℕ) (sigma epsilon cPacket : ℝ)
    (hb : beta ∈ Icc (0 : ℝ) 1) (hk : kappa ∈ Icc (0 : ℝ) 2)
    (he : 0 ≤ epsilon) (heSmall : 4*epsilon ≤ 1)
    (hh : directScale beta kappa n ∈ Ioc (0 : ℝ) (1/4))
    (hamp : epsilon*(directScale beta kappa n)^beta ≤ 3/8)
    (hsigma : sigma ≤ directScale beta kappa n)
    (hs : sigma ∈ Icc (0 : ℝ) (1/4)) (hd : 0 < effDim beta kappa) (hn : 0 < n) :
    ∃ muPlus muMinus : ThresholdProfile,
      (∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧ (muMinus a : ℝ) ∈ Icc (1/8) (7/8)) ∧
      (∀ a b, |(muPlus a : ℝ)-(muPlus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta ∧
        |(muMinus a : ℝ)-(muMinus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta) ∧
      LowerProfileConstruction beta kappa n sigma epsilon cPacket muPlus muMinus
        (directScale beta kappa n) (directScale beta kappa n) 0 0 ∧
      (0 < sigma →
        (n : ℝ)*Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
          (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤
            (8*(kappa+1)*2^kappa)*epsilon^2 ∧
        (n : ℝ)*Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
          (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤
            (8*(kappa+1)*2^kappa)*epsilon^2) := by
  obtain ⟨muPlus, muMinus, hrange, hholder, hconstruction⟩ :=
    direct_lower_profile_construction beta kappa n sigma epsilon cPacket hb hk.1
      he heSmall hh hamp hsigma
  refine ⟨muPlus, muMinus, hrange, hholder, hconstruction, ?_⟩
  intro hs0
  have hformula : ∀ a : Dose,
      (muPlus a : ℝ) = 1/2 + directPerturbation beta epsilon (directScale beta kappa n) ((a : ℝ)-a0) ∧
      (muMinus a : ℝ) = 1/2 - directPerturbation beta epsilon (directScale beta kappa n) ((a : ℝ)-a0) := by
    have hf := hconstruction.2.2.2.2.1
    simpa only [if_pos hsigma] using hf
  exact direct_profile_pair_observed_sample_budget E beta kappa sigma epsilon n hk
    ⟨hs0, hs.2⟩ he hd hn muPlus muMinus hrange hformula

/-- The direct branch supplies separation, localization, Gaussian-series comparison and observed product-TV control at level τ with one noise-independent cutoff. [Under the stated conditions](hyp:he,heSmall,hb,hk,htau,hbudget). [This is the stated conclusion](goal). -/
-- @node: direct_lower_profile_complete_construction
lemma direct_lower_profile_complete_construction (beta kappa epsilon cPacket : ℝ)
    (hb : beta ∈ Ioc (0 : ℝ) 1) (hk : kappa ∈ Icc (0 : ℝ) 2)
    (he : 0 ≤ epsilon) (heSmall : epsilon ≤ 1/8)
    (tau : ℝ) (htau : 0 ≤ tau)
    (hbudget : (8*(kappa+1)*2^kappa)*epsilon^2 ≤ Real.log (1 + tau^2)) :
    ∃ n0 : ℕ, 2 ≤ n0 ∧
      ∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S,
      ∀ n ≥ n0, ∀ sigma ∈ Icc (0 : ℝ) (1/4),
      sigma ≤ directScale beta kappa n →
      ∃ muPlus muMinus : ThresholdProfile,
        (∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧
          (muMinus a : ℝ) ∈ Icc (1/8) (7/8)) ∧
        (∀ a b, |(muPlus a : ℝ)-(muPlus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta ∧
          |(muMinus a : ℝ)-(muMinus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta) ∧
        |causalTarget E (lowerWitnessLaw E kappa muPlus)-
          causalTarget E (lowerWitnessLaw E kappa muMinus)| =
            (2*epsilon)*frontierRate beta kappa sigma n ∧
        Causalean.Stat.tvDist (experiment n sigma (lowerWitnessLaw E kappa muPlus))
          (experiment n sigma (lowerWitnessLaw E kappa muMinus)) ≤ tau ∧
        LowerProfileConstruction beta kappa n sigma epsilon cPacket muPlus muMinus
          (directScale beta kappa n) (directScale beta kappa n) 0 0 ∧
        (0 < sigma →
          let h := directScale beta kappa n
          let K := 2*(kappa+1)*2^kappa*epsilon
          let B := (4/Real.exp (-1/2)*K^2)*sigma^(-kappa-1)*
            h^(2*beta+2*kappa+2)*momentTail sigma h 0
          Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
            (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ B ∧
          Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
            (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ B) := by
  obtain ⟨n0, hn0, hprofiles⟩ :=
    direct_lower_profile_frontier_construction beta kappa epsilon cPacket hb hk he heSmall
  refine ⟨n0, hn0, ?_⟩
  intro S _ E n hn sigma hs hsigma
  obtain ⟨muPlus, muMinus, hrange, hholder, hsep, hconstruction, hchi⟩ :=
    hprofiles S E n hn sigma hs hsigma
  have hd : 0 < effDim beta kappa := by unfold effDim; linarith [hb.1, hk.1]
  have hnpos : 0 < n := by omega
  have hformula : ∀ a : Dose,
      (muPlus a : ℝ) = 1/2 + directPerturbation beta epsilon
        (directScale beta kappa n) ((a : ℝ)-a0) ∧
      (muMinus a : ℝ) = 1/2 - directPerturbation beta epsilon
        (directScale beta kappa n) ((a : ℝ)-a0) := by
    have hf := hconstruction.2.2.2.2.1
    simpa only [if_pos hsigma] using hf
  exact ⟨muPlus, muMinus, hrange, hholder, hsep,
    direct_profile_pair_observed_tv_bound E beta kappa sigma epsilon n hk hs he hd hnpos
      tau htau hbudget muPlus muMinus hrange hformula, hconstruction, hchi⟩

/-- Equations (20)--(23) give legal inverse-regime profiles and the full scaled
localization construction, using the same packet and cancellation order throughout. [Under the stated conditions](hyp:hp,hk,he,hC,hc,heSmall,hm,hsigma,hb,hell,hJ,hamp). [This is the stated conclusion](goal). -/
-- @node: inverse_lower_profile_construction
lemma inverse_lower_profile_construction (beta kappa : ℝ) (n : ℕ)
    (sigma epsilon ell Cpacket cPacket : ℝ) (m : ℕ)
    (hp : PacketBounds kappa Cpacket cPacket m)
    (hb : beta ∈ Icc (0 : ℝ) 1) (hk : 0 ≤ kappa)
    (he : 0 ≤ epsilon) (hC : 0 ≤ Cpacket) (hc : 0 ≤ cPacket)
    (heSmall : 2*epsilon*Cpacket ≤ 1) (hell : ell ∈ Ioc (0 : ℝ) (1/4))
    (hm : 4 ≤ m) (hJ : 1 ≤ Nat.floor (cPacket*m))
    (hamp : epsilon*(ell/m)^beta*Cpacket ≤ 3/8)
    (hsigma : directScale beta kappa n < sigma) :
    ∃ muPlus muMinus : ThresholdProfile,
      (∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧ (muMinus a : ℝ) ∈ Icc (1/8) (7/8)) ∧
      (∀ a b, |(muPlus a : ℝ)-(muPlus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta ∧
        |(muMinus a : ℝ)-(muMinus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta) ∧
      LowerProfileConstruction beta kappa n sigma epsilon cPacket muPlus muMinus
        (ell/m) ell m (Nat.floor (cPacket*m)) := by
  have hm0 : 0 < m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hh : ell/m ∈ Ioc (0 : ℝ) (1/4) :=
    ⟨div_pos hell.1 (by linarith),
      (div_le_self hell.1.le hmR).trans hell.2⟩
  obtain ⟨muPlus, muMinus, hformula, hrange, hholder⟩ :=
    inverse_threshold_profiles beta kappa epsilon ell Cpacket cPacket m hp hb he heSmall
      hC hell.1 hm0 hamp
  refine ⟨muPlus, muMinus, hrange, hholder, ?_⟩
  simp only [LowerProfileConstruction, if_neg (not_le.mpr hsigma)]
  refine ⟨hh, hell, ?_, (fun _ => ⟨hm, True.intro, True.intro, hJ⟩), hformula, ?_,
    inversePerturbation_signed_integrable beta kappa epsilon (ell/m) ell m hk, ?_⟩
  · intro hdirect
    exact False.elim (not_le_of_gt hsigma hdirect)
  · intro t ht
    exact inversePerturbation_support beta kappa epsilon (ell/m) ell m hell.1 t ht
  · intro j hj
    exact inversePerturbation_moment_zero beta kappa epsilon (ell/m) ell Cpacket cPacket
      m j hp hell (packet_floor_moment_cutoff cPacket m j hc hj)

/-- The inverse profiles satisfy both the full localization construction and the observed comparison (27). [Under the stated conditions](hyp:hp,he,hC,hc,heSmall,hm,hsigma,hb,hk,hs,hell,hJ,hamp). [This is the stated conclusion](goal). -/
-- @node: inverse_lower_profile_chiSq_construction
lemma inverse_lower_profile_chiSq_construction (E : PathSpace S)
    (beta kappa : ℝ) (n : ℕ) (sigma epsilon ell Cpacket cPacket : ℝ) (m : ℕ)
    (hp : PacketBounds kappa Cpacket cPacket m)
    (hb : beta ∈ Icc (0 : ℝ) 1) (hk : kappa ∈ Icc (0 : ℝ) 2)
    (hs : sigma ∈ Ioc (0 : ℝ) (1/4))
    (he : 0 ≤ epsilon) (hC : 0 ≤ Cpacket) (hc : 0 ≤ cPacket)
    (heSmall : 2*epsilon*Cpacket ≤ 1) (hell : ell ∈ Ioc (0 : ℝ) (1/4))
    (hm : 4 ≤ m) (hJ : 1 ≤ Nat.floor (cPacket*m))
    (hamp : epsilon*(ell/m)^beta*Cpacket ≤ 3/8)
    (hsigma : directScale beta kappa n < sigma) :
    let K := (kappa+1)*2^kappa*epsilon*Cpacket
    let B := (4 / Real.exp (-1/2)*K^2)*sigma^(-kappa-1)*(ell/m)^(2*beta+2*kappa+2)*
      momentTail sigma ell (Nat.floor (cPacket*m))
    ∃ muPlus muMinus : ThresholdProfile,
      (∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧ (muMinus a : ℝ) ∈ Icc (1/8) (7/8)) ∧
      (∀ a b, |(muPlus a : ℝ)-(muPlus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta ∧
        |(muMinus a : ℝ)-(muMinus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta) ∧
      LowerProfileConstruction beta kappa n sigma epsilon cPacket muPlus muMinus
        (ell/m) ell m (Nat.floor (cPacket*m)) ∧
      Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
        (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ B ∧
      Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
        (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ B := by
  obtain ⟨muPlus, muMinus, hrange, hholder, hconstruction⟩ :=
    inverse_lower_profile_construction beta kappa n sigma epsilon ell Cpacket cPacket m
      hp hb hk.1 he hC hc heSmall hell hm hJ hamp hsigma
  have hformula : ∀ a : Dose,
      (muPlus a : ℝ) = 1/2 + epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell) ∧
      (muMinus a : ℝ) = 1/2 - epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell) := by
    have hf := hconstruction.2.2.2.2.1
    simpa only [if_neg (not_le.mpr hsigma)] using hf
  have hbounds := inverse_profile_pair_chiSq_bound E beta kappa sigma epsilon ell
    Cpacket cPacket m hp hk hs he hC hc hell (by omega) muPlus muMinus hrange hformula
  exact ⟨muPlus, muMinus, hrange, hholder, hconstruction, hbounds⟩

/-- Equations (30)--(35) assemble the rounded intermediate degree, legal radius,
positive cancellation order and uniform Gaussian-series sample budget. [Under the stated conditions](hyp:hk,hd,hs,ha,ha1,hCI,hc,hthreshold,hS,hSL,hsL,haCI,haSmall,hexp). [This is the stated conclusion](goal). -/
-- @node: lower_intermediate_tuning
lemma lower_intermediate_tuning (beta kappa sigma a CI cPacket : ℝ) (n : ℕ)
    (hk : 0 ≤ kappa) (hd : 0 ≤ effDim beta kappa) (hs : 0 < sigma)
    (ha : 0 < a) (ha1 : a ≤ 1) (hCI : 4 ≤ CI) (hc : 0 < cPacket)
    (hthreshold : 2 ≤ cPacket*CI)
    (hS : 1 ≤ Real.log (Real.exp 1+(n : ℝ)*sigma^effDim beta kappa))
    (hSL : Real.log (Real.exp 1+(n : ℝ)*sigma^effDim beta kappa) ≤ logScale n)
    (hsL : sigma*Real.sqrt (logScale n) ≤ 1)
    (haCI : a*Real.sqrt (CI+1) ≤ 1/4)
    (haSmall : a^2 ≤ (cPacket/2)/2)
    (hexp : Real.exp 1*a^2/(cPacket/2) ≤ Real.exp (-1/(cPacket/2))) :
    let S := Real.log (Real.exp 1+(n : ℝ)*sigma^effDim beta kappa)
    let m := Nat.ceil (CI*S)
    let ell := a*sigma*Real.sqrt m
    let J := Nat.floor (cPacket*m)
    4 ≤ m ∧ 1 ≤ J ∧ ell ∈ Ioc (0 : ℝ) (1/4) ∧
      ell/(m : ℝ) ∈ Ioc (0 : ℝ) (1/4) ∧ ell/(m : ℝ) ≤ sigma ∧
      (a/Real.sqrt (CI+1))*(sigma/Real.sqrt S) ≤ ell/(m : ℝ) ∧
      (n : ℝ)*(sigma^(-kappa-1)*(ell/m)^(2*beta+2*kappa+2)*momentTail sigma ell J) ≤ 2 := by
  dsimp only
  let S := Real.log (Real.exp 1+(n : ℝ)*sigma^effDim beta kappa)
  let m := Nat.ceil (CI*S)
  let ell := a*sigma*Real.sqrt m
  let J := Nat.floor (cPacket*m)
  have hCI1 : 1 ≤ CI := by linarith
  obtain ⟨hlo, hhi, hm1⟩ := lower_intermediate_degree_bounds CI S hCI1 hS
  have hCIm : CI ≤ (m : ℝ) := by
    calc
      CI ≤ CI*S := le_mul_of_one_le_right (by linarith) hS
      _ ≤ _ := hlo
  have hm4 : 4 ≤ m := by exact_mod_cast (hCI.trans hCIm)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hthreshold' : 2 ≤ cPacket*m :=
    hthreshold.trans (mul_le_mul_of_nonneg_left hCIm hc.le)
  obtain ⟨horder, hJ⟩ := lower_packet_cancellation_order cPacket m hthreshold'
  obtain ⟨hell, hh0, hhs⟩ := lower_intermediate_radius_bounds sigma a CI S (logScale n)
    hs ha ha1 hCI1 hS hSL hsL haCI
  have hh : ell/(m : ℝ) ∈ Ioc (0 : ℝ) (1/4) :=
    ⟨hh0, (div_le_self hell.1.le hmR).trans hell.2⟩
  have hdegree : S ≤ (m : ℝ) := by
    calc
      S ≤ CI*S := le_mul_of_one_le_left (by linarith) hCI1
      _ ≤ _ := hlo
  refine ⟨hm4, hJ, hell, hh, hhs,
    lower_intermediate_bandwidth_comparison sigma a CI S hs ha hCI1 hS, ?_⟩
  exact lower_intermediate_gaussian_sample_budget beta kappa sigma (ell/m) ell a
    (cPacket/2) n m J hk hd hh.1 hhs (by positivity) (by omega)
    (lower_intermediate_lambda_identity sigma a m hs) horder haSmall hexp hdegree

/-- Equations (35)--(36) hold for the actual intermediate threshold profiles, with
one rounded packet degree and cancellation order for construction and observed distance. [Under the stated conditions](hyp:ha,ha1,hCI,hc,hthreshold,he,hC,heSmall,hpacket,hinverse,hb,hk,hs,hS,hSL,hsL,haCI,haSmall,hexp). [This is the stated conclusion](goal). -/
-- @node: intermediate_lower_profile_sample_budget
lemma intermediate_lower_profile_sample_budget (E : PathSpace S)
    (beta kappa sigma epsilon a CI Cpacket cPacket : ℝ) (n : ℕ)
    (hb : beta ∈ Icc (0 : ℝ) 1) (hk : kappa ∈ Icc (0 : ℝ) 2)
    (hs : sigma ∈ Ioc (0 : ℝ) (1/4))
    (ha : 0 < a) (ha1 : a ≤ 1) (hCI : 4 ≤ CI) (hc : 0 < cPacket)
    (hthreshold : 2 ≤ cPacket*CI)
    (hS : 1 ≤ Real.log (Real.exp 1+(n : ℝ)*sigma^effDim beta kappa))
    (hSL : Real.log (Real.exp 1+(n : ℝ)*sigma^effDim beta kappa) ≤ logScale n)
    (hsL : sigma*Real.sqrt (logScale n) ≤ 1)
    (haCI : a*Real.sqrt (CI+1) ≤ 1/4)
    (haSmall : a^2 ≤ (cPacket/2)/2)
    (hexp : Real.exp 1*a^2/(cPacket/2) ≤ Real.exp (-1/(cPacket/2)))
    (he : 0 ≤ epsilon) (hC : 0 ≤ Cpacket) (heSmall : epsilon*Cpacket ≤ 1/8)
    (hpacket : ∀ m : ℕ, 4 ≤ m → PacketBounds kappa Cpacket cPacket m)
    (hinverse : directScale beta kappa n < sigma) :
    let S := Real.log (Real.exp 1+(n : ℝ)*sigma^effDim beta kappa)
    let m := Nat.ceil (CI*S)
    let ell := a*sigma*Real.sqrt m
    let J := Nat.floor (cPacket*m)
    let K := (kappa+1)*2^kappa*epsilon*Cpacket
    ∃ muPlus muMinus : ThresholdProfile,
      (∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧ (muMinus a : ℝ) ∈ Icc (1/8) (7/8)) ∧
      (∀ a b, |(muPlus a : ℝ)-(muPlus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta ∧
        |(muMinus a : ℝ)-(muMinus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta) ∧
      LowerProfileConstruction beta kappa n sigma epsilon cPacket muPlus muMinus
        (ell/m) ell m J ∧
      (2*epsilon)*(a/Real.sqrt (CI+1))^beta*(sigma/Real.sqrt S)^beta ≤
        |causalTarget E (lowerWitnessLaw E kappa muPlus)-causalTarget E (lowerWitnessLaw E kappa muMinus)| ∧
      (n : ℝ)*Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
        (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ 2*(4/Real.exp (-1/2)*K^2) ∧
      (n : ℝ)*Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
        (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ 2*(4/Real.exp (-1/2)*K^2) := by
  dsimp only
  let S := Real.log (Real.exp 1+(n : ℝ)*sigma^effDim beta kappa)
  let m := Nat.ceil (CI*S)
  let ell := a*sigma*Real.sqrt m
  let J := Nat.floor (cPacket*m)
  let K := (kappa+1)*2^kappa*epsilon*Cpacket
  have hs0 := hs.1
  have hd : 0 ≤ effDim beta kappa := by dsimp [effDim]; linarith [hb.1, hk.1]
  obtain ⟨hm, hJ, hell, hh, hhs, hcompare, hsample⟩ := lower_intermediate_tuning
    beta kappa sigma a CI cPacket n hk.1 hd hs.1 ha ha1 hCI hc hthreshold
    hS hSL hsL haCI haSmall hexp
  have hp := hpacket m hm
  have hamp : epsilon*(ell/m)^beta*Cpacket ≤ 3/8 := by
    have hr := Real.rpow_le_one hh.1.le (hh.2.trans (by norm_num)) hb.1
    have := mul_le_mul_of_nonneg_left hr (mul_nonneg he hC)
    nlinarith
  obtain ⟨muPlus, muMinus, hrange, hholder, hconstruction, hplus, hminus⟩ :=
    inverse_lower_profile_chiSq_construction E beta kappa n sigma epsilon ell Cpacket
      cPacket m hp hb hk hs he hC hc.le (by linarith) hell hm hJ hamp hinverse
  have hformula : ∀ a : Dose,
      (muPlus a : ℝ) = 1/2 + epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell) ∧
      (muMinus a : ℝ) = 1/2 - epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell) := by
    have hf := hconstruction.2.2.2.2.1
    simpa only [if_neg (not_le.mpr hinverse)] using hf
  refine ⟨muPlus, muMinus, hrange, hholder, hconstruction, ?_, ?_, ?_⟩
  · rw [inverse_profile_target_separation E beta kappa epsilon (ell/m) ell Cpacket
      cPacket m hk hp he hh.1.le muPlus muMinus hformula]
    have hr := Real.rpow_le_rpow (by positivity :
      0 ≤ (a/Real.sqrt (CI+1))*(sigma/Real.sqrt S)) hcompare hb.1
    rw [Real.mul_rpow (by positivity : 0 ≤ a/Real.sqrt (CI+1))
      (by positivity : 0 ≤ sigma/Real.sqrt S)] at hr
    have := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*epsilon by positivity)
    nlinarith
  all_goals
    have hconst : 0 ≤ 4/Real.exp (-1/2)*K^2 := by positivity
    calc
      _ ≤ (n : ℝ)*((4/Real.exp (-1/2)*K^2)*sigma^(-kappa-1)*
          (ell/m)^(2*beta+2*kappa+2)*momentTail sigma ell J) :=
        mul_le_mul_of_nonneg_left (by assumption) (Nat.cast_nonneg n)
      _ = (4/Real.exp (-1/2)*K^2)*((n : ℝ)*(sigma^(-kappa-1)*
          (ell/m)^(2*beta+2*kappa+2)*momentTail sigma ell J)) := by ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hsample hconst]

/-- The concrete compact tuning assembles (46)--(47) for the actual threshold profiles,
with the same packet, bandwidth and cancellation order used in (27). [Under the stated conditions](hyp:hn,hL,ht,hCM,he,hC,hc,heSmall,hpacket,hM,hthreshold,hsize,hinverse,hb,hk,hs,hell,hlarge,hbudget). [This is the stated conclusion](goal). -/
-- @node: compact_lower_profile_sample_budget
lemma compact_lower_profile_sample_budget (E : PathSpace S)
    (beta kappa sigma epsilon CM ell Cpacket cPacket M : ℝ) (n : ℕ)
    (hb : beta ∈ Icc (0 : ℝ) 1) (hk : kappa ∈ Icc (0 : ℝ) 2) (hn : 0 < n)
    (hs : sigma ∈ Ioc (0 : ℝ) (1/4))
    (hL : 1 ≤ logScale n) (ht : 1 ≤ sigma^2*logScale n)
    (hCM : 1 ≤ CM) (hell : ell ∈ Ioc (0 : ℝ) (1/4))
    (he : 0 ≤ epsilon) (hC : 0 ≤ Cpacket) (hc : 0 < cPacket)
    (heSmall : epsilon*Cpacket ≤ 1/8)
    (hpacket : ∀ m : ℕ, 4 ≤ m → PacketBounds kappa Cpacket cPacket m)
    (hM : 4 ≤ M) (hthreshold : 2 ≤ cPacket*M) (hsize : M^2 ≤ logScale n)
    (hlarge : 2*Real.exp 1 ≤ (cPacket/2)*CM/(Real.exp 1*ell^2))
    (hbudget : 8 ≤ (cPacket/2)*CM) (hinverse : directScale beta kappa n < sigma) :
    let B := Real.log (Real.exp 1+sigma^2*logScale n)
    let m := Nat.ceil (CM*logScale n/B)
    let J := Nat.floor (cPacket*m)
    let K := (kappa+1)*2^kappa*epsilon*Cpacket
    ∃ muPlus muMinus : ThresholdProfile,
      (∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧ (muMinus a : ℝ) ∈ Icc (1/8) (7/8)) ∧
      (∀ a b, |(muPlus a : ℝ)-(muPlus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta ∧
        |(muMinus a : ℝ)-(muMinus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta) ∧
      LowerProfileConstruction beta kappa n sigma epsilon cPacket muPlus muMinus
        (ell/m) ell m J ∧
      (2*epsilon)*(ell/(2*CM))^beta*(B/logScale n)^beta ≤
        |causalTarget E (lowerWitnessLaw E kappa muPlus)-causalTarget E (lowerWitnessLaw E kappa muMinus)| ∧
      (n : ℝ)*Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
        (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ 2*(4/Real.exp (-1/2)*K^2) ∧
      (n : ℝ)*Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
        (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ 2*(4/Real.exp (-1/2)*K^2) := by
  dsimp only
  let B := Real.log (Real.exp 1+sigma^2*logScale n)
  let m := Nat.ceil (CM*logScale n/B)
  let J := Nat.floor (cPacket*m)
  let K := (kappa+1)*2^kappa*epsilon*Cpacket
  have hell0 := hell.1
  have hCM0 : 0 < CM := by linarith
  have hL0 : 0 < logScale n := by linarith
  have hB0 : 0 < B := Real.log_pos (by
    have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    nlinarith [sq_nonneg sigma])
  have hd : 0 ≤ effDim beta kappa := by dsimp [effDim]; linarith [hb.1, hk.1]
  obtain ⟨hm, hJ, hh, hhs, hcompare, hsample⟩ := lower_compact_tuning beta kappa sigma
    CM ell cPacket M n hk.1 hd hn hs hL ht hCM hell hc hM hthreshold hsize hlarge hbudget
  have hp := hpacket m hm
  have hamp : epsilon*(ell/m)^beta*Cpacket ≤ 3/8 := by
    have hr := Real.rpow_le_one hh.1.le (hh.2.trans (by norm_num)) hb.1
    have := mul_le_mul_of_nonneg_left hr (mul_nonneg he hC)
    nlinarith
  obtain ⟨muPlus, muMinus, hrange, hholder, hconstruction, hplus, hminus⟩ :=
    inverse_lower_profile_chiSq_construction E beta kappa n sigma epsilon ell Cpacket
      cPacket m hp hb hk hs he hC hc.le (by linarith) hell hm hJ hamp hinverse
  have hformula : ∀ a : Dose,
      (muPlus a : ℝ) = 1/2 + epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell) ∧
      (muMinus a : ℝ) = 1/2 - epsilon*(ell/m)^beta*packetPsi kappa m (((a : ℝ)-a0)/ell) := by
    have hf := hconstruction.2.2.2.2.1
    simpa only [if_neg (not_le.mpr hinverse)] using hf
  refine ⟨muPlus, muMinus, hrange, hholder, hconstruction, ?_, ?_, ?_⟩
  · rw [inverse_profile_target_separation E beta kappa epsilon (ell/m) ell Cpacket
      cPacket m hk hp he hh.1.le muPlus muMinus hformula]
    have hr := Real.rpow_le_rpow (by positivity : 0 ≤ (ell/(2*CM))*(B/logScale n)) hcompare hb.1
    rw [Real.mul_rpow (by positivity : 0 ≤ ell/(2*CM)) (by
      dsimp [B]; positivity : 0 ≤ B/logScale n)] at hr
    have := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*epsilon by positivity)
    nlinarith
  all_goals
    have hconst : 0 ≤ 4/Real.exp (-1/2)*K^2 := by positivity
    calc
      _ ≤ (n : ℝ)*((4/Real.exp (-1/2)*K^2)*sigma^(-kappa-1)*
          (ell/m)^(2*beta+2*kappa+2)*momentTail sigma ell J) :=
        mul_le_mul_of_nonneg_left (by assumption) (Nat.cast_nonneg n)
      _ = (4/Real.exp (-1/2)*K^2)*((n : ℝ)*(sigma^(-kappa-1)*
          (ell/m)^(2*beta+2*kappa+2)*momentTail sigma ell J)) := by ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hsample hconst]

/-- All three law witnesses are the explicit product-seed threshold laws. Their profiles,
localization, cancellations and observed Gaussian-series bounds share the same tuning data. -/
def LowerWitnessConstruction (E : PathSpace S) (beta kappa : ℝ) (n : ℕ)
    (sigma epsilon cPacket C : ℝ) (Pplus Pminus Pstar : Measure (StructSpace S)) : Prop :=
  ∃ muPlus muMinus : ThresholdProfile, ∃ h ell : ℝ, ∃ m J : ℕ,
    LowerProfileConstruction beta kappa n sigma epsilon cPacket muPlus muMinus h ell m J ∧
    Pplus = lowerWitnessLaw E kappa muPlus ∧
    Pminus = lowerWitnessLaw E kappa muMinus ∧
    Pstar = lowerWitnessLaw E kappa referenceProfile ∧
    (0 < sigma →
      Causalean.Stat.chiSqDiv (obsLaw sigma Pplus) (obsLaw sigma Pstar) ≤
        C*sigma^(-kappa-1)*h^(2*beta+2*kappa+2)*momentTail sigma ell J ∧
      Causalean.Stat.chiSqDiv (obsLaw sigma Pminus) (obsLaw sigma Pstar) ≤
        C*sigma^(-kappa-1)*h^(2*beta+2*kappa+2)*momentTail sigma ell J)

/-- Regime tuning supplies legal threshold profiles with observed separation, observed product total variation at most a prescribed positive level τ, and Gaussian-series control. [Under the stated conditions](hyp:hLocalization_of_gate,hLipschitz_of_gate,hNorm_of_gate,hGamma_of_gate,hbeta,hkappa,htau). [This is the stated conclusion](goal). -/
-- @node: lower_regime_witnesses
lemma lower_regime_witnesses (hLocalization_of_gate : FilteredJacobiLocalization)
    (hLipschitz_of_gate : FilteredJacobiLipschitz)
    (hNorm_of_gate : JacobiNormOrthogonality)
    (hGamma_of_gate : GammaRatioAsymptotic)
    (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (tau : ℝ) (htau : 0 < tau) :
    ∃ c C epsilon Cpacket cPacket : ℝ,
      0 < c ∧ 0 < C ∧ 0 < epsilon ∧ 0 < Cpacket ∧ 0 < cPacket ∧
      (∀ m : ℕ, 4 ≤ m → PacketBounds kappa Cpacket cPacket m) ∧
      ∃ n0 : ℕ, ∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S, ∀ n ≥ n0, ∀ sigma ∈ Icc (0 : ℝ) (1/4),
      ∃ muPlus muMinus : ThresholdProfile,
        (∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧ (muMinus a : ℝ) ∈ Icc (1/8) (7/8)) ∧
        (∀ a b, |(muPlus a : ℝ)-(muPlus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta ∧
          |(muMinus a : ℝ)-(muMinus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta) ∧
        c*frontierRate beta kappa sigma n ≤
          |causalTarget E (lowerWitnessLaw E kappa muPlus)-causalTarget E (lowerWitnessLaw E kappa muMinus)| ∧
        Causalean.Stat.tvDist (experiment n sigma (lowerWitnessLaw E kappa muPlus))
          (experiment n sigma (lowerWitnessLaw E kappa muMinus)) ≤ tau ∧
        ∃ h ell : ℝ, ∃ m J : ℕ,
          LowerProfileConstruction beta kappa n sigma epsilon cPacket muPlus muMinus h ell m J ∧
          (0 < sigma →
            Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
              (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤
                C*sigma^(-kappa-1)*h^(2*beta+2*kappa+2)*momentTail sigma ell J ∧
            Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
              (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤
                C*sigma^(-kappa-1)*h^(2*beta+2*kappa+2)*momentTail sigma ell J) := by
  obtain ⟨Cpacket, cPacket, hCpacket, hcPacket, hpacket⟩ :
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ m : ℕ, 4 ≤ m → PacketBounds kappa C c m := by
    by_cases hk0 : kappa = 0
    · exact packetinterior_bounds hLocalization_of_gate hLipschitz_of_gate
        hNorm_of_gate hGamma_of_gate kappa hk0
    · exact packetendpoint_bounds hLocalization_of_gate hLipschitz_of_gate
        hNorm_of_gate hGamma_of_gate kappa ⟨lt_of_le_of_ne hkappa.1 (Ne.symm hk0), hkappa.2⟩
  obtain ⟨M, CI, hM, hcM, hCI, hcCI, hMCI⟩ := lower_packet_degree_constants cPacket hcPacket
  obtain ⟨a, ha, ha1, haCI, haSmall, haExp⟩ :=
    lower_intermediate_radius_constant CI cPacket hCI hcPacket
  obtain ⟨CM, hCM, hCMlarge, hCMbudget⟩ :=
    lower_compact_multiplier_constant cPacket (1/8) hcPacket (by norm_num)
  let D := 8*(kappa+1)*2^kappa
  let I := 4/Real.exp (-1/2)*((kappa+1)*2^kappa*Cpacket)^2
  let F := 4/Real.exp (-1/2)*(2*(kappa+1)*2^kappa)^2
  have hD : 0 < D := by dsimp [D]; have := hkappa.1; positivity
  have hI : 0 < I := by dsimp [I]; have := hkappa.1; positivity
  have hF : 0 < F := by dsimp [F]; have := hkappa.1; positivity
  obtain ⟨epsilon, he, heSmall, he4, heC, heBudget⟩ :=
    lower_common_amplitude_constant Cpacket (max D (2*I)) tau hCpacket
      (lt_of_lt_of_le hD (le_max_left _ _)) htau
  have hdb : D*epsilon^2 ≤ Real.log (1 + tau^2) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg epsilon)).trans heBudget
  have hib : 2*(4/Real.exp (-1/2)*((kappa+1)*2^kappa*epsilon*Cpacket)^2) ≤
      Real.log (1 + tau^2) := by
    have h := (mul_le_mul_of_nonneg_right (le_max_right D (2*I))
      (sq_nonneg epsilon)).trans heBudget
    dsimp [I] at h
    nlinarith [h]
  let C := max F I * epsilon^2
  have hC : 0 < C := by dsimp [C]; positivity
  have hFC : 4/Real.exp (-1/2)*(2*(kappa+1)*2^kappa*epsilon)^2 ≤ C := by
    have h := mul_le_mul_of_nonneg_right (le_max_left F I) (sq_nonneg epsilon)
    dsimp [F, C] at *
    nlinarith
  have hIC : 4/Real.exp (-1/2)*((kappa+1)*2^kappa*epsilon*Cpacket)^2 ≤ C := by
    have h := mul_le_mul_of_nonneg_right (le_max_right F I) (sq_nonneg epsilon)
    dsimp [I, C] at *
    nlinarith
  let c := (2*epsilon)*min 1 (min ((a/Real.sqrt (CI+1))^beta) (((1/8)/(2*CM))^beta))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcD : c ≤ 2*epsilon := by
    exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans_eq (mul_one _)
  have hcI : c ≤ (2*epsilon)*(a/Real.sqrt (CI+1))^beta :=
    mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _)) (by positivity)
  have hcM' : c ≤ (2*epsilon)*((1/8)/(2*CM))^beta :=
    mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) (by positivity)
  obtain ⟨nd, hnd, hDirect⟩ := direct_lower_profile_complete_construction
    beta kappa epsilon cPacket hbeta hkappa he.le heSmall tau htau.le hdb
  obtain ⟨nl, hnl, hLog⟩ := lower_log_sample_cutoff (M : ℝ)
  refine ⟨c, C, epsilon, Cpacket, cPacket, hc, hC, he, hCpacket, hcPacket, hpacket,
    max nd nl, ?_⟩
  intro S _ E n hn sigma hs
  have hnD : nd ≤ n := (le_max_left _ _).trans hn
  have hnL : nl ≤ n := (le_max_right _ _).trans hn
  have hn2 : 2 ≤ n := hnd.trans hnD
  have hnpos : 0 < n := by omega
  have hb0 : beta ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hbeta.1], hbeta.2⟩
  have hd : 0 ≤ effDim beta kappa := by dsimp [effDim]; linarith [hbeta.1, hkappa.1]
  have hwindow := lower_intermediate_log_window beta kappa sigma n hd hs hn2
  have hL : 1 ≤ logScale n := hwindow.1.trans hwindow.2
  have hL0 : 0 < logScale n := by linarith
  have hroot : 0 < Real.sqrt (logScale n) := Real.sqrt_pos.mpr hL0
  have helbow : (logScale n)^(-1/2 : ℝ) = 1/Real.sqrt (logScale n) := by
    rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by ring, Real.rpow_neg hL0.le,
      ← Real.sqrt_eq_rpow, one_div]
  have htail (ell : ℝ) (J : ℕ) : 0 ≤ momentTail sigma ell J := by
    unfold momentTail
    exact tsum_nonneg (fun j => by positivity)
  have hcompare (h ell : ℝ) (J : ℕ) (hh : 0 ≤ h) {B : ℝ} (hB : B ≤ C) :
      B*sigma^(-kappa-1)*h^(2*beta+2*kappa+2)*momentTail sigma ell J ≤
        C*sigma^(-kappa-1)*h^(2*beta+2*kappa+2)*momentTail sigma ell J := by
    apply mul_le_mul_of_nonneg_right _ (htail ell J)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hh _)
    exact mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hs.1 _)
  by_cases hdirect : sigma ≤ directScale beta kappa n
  · obtain ⟨muPlus, muMinus, hrange, hholder, hsep, htv, hconstruction, hchi⟩ :=
      hDirect S E n hnD sigma hs hdirect
    refine ⟨muPlus, muMinus, hrange, hholder, ?_, htv,
      directScale beta kappa n, directScale beta kappa n, 0, 0, hconstruction, ?_⟩
    · rw [hsep]
      apply mul_le_mul_of_nonneg_right hcD
      simp only [frontierRate, frontierScale, if_pos hdirect]
      exact Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) _
    · intro hs0
      obtain ⟨hp, hm⟩ := hchi hs0
      exact ⟨hp.trans (hcompare _ _ _ hconstruction.1.1.le hFC), hm.trans (hcompare _ _ _ hconstruction.1.1.le hFC)⟩
  have hinverse : directScale beta kappa n < sigma := lt_of_not_ge hdirect
  have hs0 : 0 < sigma := lt_trans (Real.rpow_pos_of_pos (by exact_mod_cast hnpos) _) hinverse
  have hs' : sigma ∈ Ioc (0 : ℝ) (1/4) := ⟨hs0, hs.2⟩
  have finish (muPlus muMinus : ThresholdProfile) (ell : ℝ) (m : ℕ)
      (hrange : ∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧ (muMinus a : ℝ) ∈ Icc (1/8) (7/8))
      (hconstruction : LowerProfileConstruction beta kappa n sigma epsilon cPacket
        muPlus muMinus (ell/m) ell m (Nat.floor (cPacket*m)))
      (hplus : (n : ℝ)*Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
        (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤
          2*(4/Real.exp (-1/2)*((kappa+1)*2^kappa*epsilon*Cpacket)^2))
      (hminus : (n : ℝ)*Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
        (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤
          2*(4/Real.exp (-1/2)*((kappa+1)*2^kappa*epsilon*Cpacket)^2)) :
      Causalean.Stat.tvDist (experiment n sigma (lowerWitnessLaw E kappa muPlus))
        (experiment n sigma (lowerWitnessLaw E kappa muMinus)) ≤ tau ∧
      (0 < sigma →
        Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
          (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤
            C*sigma^(-kappa-1)*(ell/m)^(2*beta+2*kappa+2)*momentTail sigma ell (Nat.floor (cPacket*m)) ∧
        Causalean.Stat.chiSqDiv (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
          (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤
            C*sigma^(-kappa-1)*(ell/m)^(2*beta+2*kappa+2)*momentTail sigma ell (Nat.floor (cPacket*m))) := by
    have hm := (hconstruction.2.2.2.1 hinverse).1
    have hf := hconstruction.2.2.2.2.1
    simp only [if_neg hdirect] at hf
    have hchi := inverse_profile_pair_chiSq_bound E beta kappa sigma epsilon ell
      Cpacket cPacket m (hpacket m hm) hkappa hs' he.le hCpacket.le hcPacket.le
      hconstruction.2.1 (by omega) muPlus muMinus hrange hf
    refine ⟨lower_observed_experiment_tv_le E kappa sigma hkappa muPlus muMinus n tau htau.le
      (obsLaw_witness_ac E kappa sigma hkappa hs muPlus (fun a => (hrange a).1))
      (obsLaw_witness_ac E kappa sigma hkappa hs muMinus (fun a => (hrange a).2))
      (obsLaw_witness_sqdev_integrable E kappa sigma hkappa hs muPlus (fun a => (hrange a).1))
      (obsLaw_witness_sqdev_integrable E kappa sigma hkappa hs muMinus (fun a => (hrange a).2))
      (hplus.trans hib) (hminus.trans hib), ?_⟩
    intro _
    exact ⟨hchi.1.trans (hcompare _ _ _ hconstruction.1.1.le hIC), hchi.2.trans (hcompare _ _ _ hconstruction.1.1.le hIC)⟩
  by_cases hinter : sigma ≤ (logScale n)^(-1/2 : ℝ)
  · have hsL : sigma*Real.sqrt (logScale n) ≤ 1 := by
      rw [helbow] at hinter
      exact (le_div_iff₀ hroot).mp hinter
    obtain ⟨muPlus, muMinus, hrange, hholder, hconstruction, hsep, hp, hm⟩ :=
      intermediate_lower_profile_sample_budget E beta kappa sigma epsilon a CI Cpacket
        cPacket n hb0 hkappa hs' ha ha1 hCI hcPacket hcCI hwindow.1 hwindow.2 hsL
        haCI haSmall haExp he.le hCpacket.le heC hpacket hinverse
    obtain ⟨htv, hchi⟩ := finish muPlus muMinus _ _ hrange hconstruction hp hm
    refine ⟨muPlus, muMinus, hrange, hholder, ?_, htv, _, _, _, _, hconstruction, hchi⟩
    apply le_trans _ hsep
    simp only [frontierRate, frontierScale, if_neg hdirect, if_pos hinter, fourierScale]
    exact mul_le_mul_of_nonneg_right hcI (by positivity)
  · have ht : 1 ≤ sigma^2*logScale n := by
      have hgt : 1 < sigma*Real.sqrt (logScale n) := by
        rw [helbow] at hinter
        exact (div_lt_iff₀ hroot).mp (lt_of_not_ge hinter)
      have hid : (sigma*Real.sqrt (logScale n))^2 = sigma^2*logScale n := by
        rw [mul_pow, Real.sq_sqrt hL0.le]
      rw [← hid]
      nlinarith only [hgt]
    obtain ⟨muPlus, muMinus, hrange, hholder, hconstruction, hsep, hp, hm⟩ :=
      compact_lower_profile_sample_budget E beta kappa sigma epsilon CM (1/8) Cpacket
        cPacket M n hb0 hkappa hnpos hs' hL ht hCM (by norm_num) he.le hCpacket.le
        hcPacket heC hpacket (by exact_mod_cast hM) hcM (hLog n hnL) hCMlarge hCMbudget hinverse
    obtain ⟨htv, hchi⟩ := finish muPlus muMinus _ _ hrange hconstruction hp hm
    refine ⟨muPlus, muMinus, hrange, hholder, ?_, htv, _, _, _, _, hconstruction, hchi⟩
    apply le_trans _ hsep
    simp only [frontierRate, frontierScale, if_neg hdirect, if_neg hinter, polynomialScale]
    have hB : 0 ≤ Real.log (Real.exp 1+sigma^2*logScale n) :=
      Real.log_nonneg (by linarith only [ht, Real.exp_pos (1 : ℝ)])
    exact mul_le_mul_of_nonneg_right hcM'
      (Real.rpow_nonneg (div_nonneg hB hL0.le) beta)

end CausalSmith.Stat.NoisydoseWeakdesignTransition

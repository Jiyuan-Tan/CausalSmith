module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DictionaryScore.FourierWitness
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DictionaryScore.PolynomialEnvelope
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DictionaryScore.PolynomialLocalization
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DictionaryScore.PolynomialWitness

/-! Helpers — DictionaryScore -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]


/-- Each restricted stratum law is dominated by its normalized conditional law. [This is the stated conclusion](goal). -/
-- @node: restricted_stratum_le_stratumLaw
lemma restricted_stratum_le_stratumLaw (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (x : Bool) :
    P.restrict {w | sX w = x} ≤ stratumLaw P x := by
  intro B
  change (P.restrict {w | sX w = x}) B ≤
    (P {w | sX w = x})⁻¹ * (P.restrict {w | sX w = x}) B
  exact le_mul_of_one_le_left (zero_le) (ENNReal.one_le_inv.mpr prob_le_one)

/-- The design envelope controls nonnegative latent-dose integrals in each stratum. [Under the stated conditions](hyp:hdesign,f,hf). [This is the stated conclusion](goal). -/
-- @node: stratum_latent_lintegral_le
lemma stratum_latent_lintegral_le (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (kappa : ℝ) {K : ClassConstants} (hdesign : WeakDesign K.clo K.chi kappa P)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (x : Bool) :
    (∫⁻ w, f (latentCentered w) ∂P.restrict {w | sX w = x}) ≤
      ENNReal.ofReal K.chi * ∫⁻ t in Icc (-1/2 : ℝ) (1/2), ENNReal.ofReal (|t| ^ kappa) * f t := by
  obtain ⟨g, hg, hlaw, henv⟩ := hdesign
  have ht : Measurable (latentCentered : StructSpace S → ℝ) := by
    unfold latentCentered sA a0
    fun_prop
  calc
    _ ≤ ∫⁻ w, f (latentCentered w) ∂stratumLaw P x :=
      lintegral_mono' (restricted_stratum_le_stratumLaw P x) le_rfl
    _ = ∫⁻ t, f t ∂(stratumLaw P x).map latentCentered := (lintegral_map hf ht).symm
    _ = ∫⁻ t in Icc (-1/2 : ℝ) (1/2), ENNReal.ofReal (g x t) * f t := by
      rw [hlaw x, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
      rfl
    _ ≤ ∫⁻ t in Icc (-1/2 : ℝ) (1/2), ENNReal.ofReal K.chi * (ENNReal.ofReal (|t| ^ kappa) * f t) := by
      apply lintegral_mono_ae
      filter_upwards [henv x] with t ht
      have he : ENNReal.ofReal (g x t) ≤ ENNReal.ofReal K.chi * ENNReal.ofReal (|t| ^ kappa) := by
        calc
          _ ≤ ENNReal.ofReal (K.chi * |t| ^ kappa) := ENNReal.ofReal_le_ofReal ht.2
          _ = _ := by rw [ENNReal.ofReal_mul (K.clo_pos.le.trans K.clo_le_chi)]
      simpa only [mul_assoc] using mul_le_mul' he (le_refl (f t))
    _ = _ := lintegral_const_mul _ (by fun_prop)

/-- Summing the two strata gives a finite-envelope bound for the marginal latent dose. [Under the stated conditions](hyp:hdesign,f,hf). [This is the stated conclusion](goal). -/
-- @node: latent_lintegral_le_two_envelopes
lemma latent_lintegral_le_two_envelopes (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (kappa : ℝ) {K : ClassConstants} (hdesign : WeakDesign K.clo K.chi kappa P)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, f (latentCentered w) ∂P) ≤
      (ENNReal.ofReal K.chi * ∫⁻ t in Icc (-1/2 : ℝ) (1/2), ENNReal.ofReal (|t| ^ kappa) * f t) +
      (ENNReal.ofReal K.chi * ∫⁻ t in Icc (-1/2 : ℝ) (1/2), ENNReal.ofReal (|t| ^ kappa) * f t) := by
  have hs : MeasurableSet {w : StructSpace S | sX w = false} := by
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  have hc : {w : StructSpace S | sX w = false}ᶜ = {w | sX w = true} := by
    ext w
    cases sX w <;> simp
  have hsplit := Measure.restrict_add_restrict_compl (μ := P) hs
  rw [hc] at hsplit
  rw [← hsplit, lintegral_add_measure]
  exact add_le_add (stratum_latent_lintegral_le P kappa hdesign f hf false)
    (stratum_latent_lintegral_le P kappa hdesign f hf true)

/-- Finite public second moments imply law-level inverse integrability over the causal model. [Under the stated conditions](hyp:hP,hq,hV,hkappa,hsigma). [This is the stated conclusion](goal). -/
-- @node: dictionary_pair_law_admissible
lemma dictionary_pair_law_admissible (E : PathSpace S) (beta kappa sigma : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P) (q : WeightPair)
    (hq : PairAdmissible kappa sigma q) (hV : VqENN kappa sigma q.ell < ⊤) :
    LawAdmissible sigma P q := by
  have hell : Measurable q.ell := hq.2.1
  have ht : Measurable (latentCentered : StructSpace S → ℝ) := by
    unfold latentCentered sA a0
    fun_prop
  have hz : Measurable (sZ : StructSpace S → ℝ) := by fun_prop
  have hv : Measurable (fun w : StructSpace S => q.ell (observedCentered sigma w)) := by
    unfold observedCentered contaminatedDose sA sZ
    fun_prop
  have hind : IndepFun latentCentered sZ P := by
    have h := hP.errorIndependence.comp measurable_id
      (show Measurable (fun p : Bool × ℝ × S => p.2.1 - a0) by fun_prop)
    exact h.symm
  have hjoint : P.map (fun w => (latentCentered w, sZ w)) =
      (P.map latentCentered).prod (gaussianReal 0 1) := by
    rw [hind.map_prod_eq_prod_map_map ht.aemeasurable hz.aemeasurable,
      hP.gaussianChannel]
  let f : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal ((q.ell (p.1+sigma*p.2))^2)
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  let J : ℝ≥0∞ := ∫⁻ t in Icc (-1/2 : ℝ) (1/2), ENNReal.ofReal (|t| ^ kappa) *
    (∫⁻ z, ENNReal.ofReal ((q.ell (t+sigma*z))^2) ∂gaussianReal 0 1)
  have hJ : ENNReal.ofReal K.chi * J < ⊤ := by
    have hV' : 16 * J < ⊤ := hV
    have h16 : J ≤ 16 * J := le_mul_of_one_le_left zero_le (by norm_num)
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt h16 hV')
  have hsecond : (∫⁻ w, ENNReal.ofReal ((q.ell (observedCentered sigma w))^2) ∂P) ≤
      ENNReal.ofReal K.chi * J + ENNReal.ofReal K.chi * J := by
    calc
      _ = ∫⁻ w, f (latentCentered w, sZ w) ∂P := by
        congr 1
        funext w
        dsimp [f, observedCentered, contaminatedDose, latentCentered]
        congr 3
        ring
      _ = ∫⁻ p, f p ∂P.map (fun w => (latentCentered w, sZ w)) :=
        (lintegral_map hf (ht.prodMk hz)).symm
      _ = ∫⁻ t, ∫⁻ z, f (t,z) ∂gaussianReal 0 1 ∂P.map latentCentered := by
        rw [hjoint, lintegral_prod _ hf.aemeasurable]
      _ = ∫⁻ w, (∫⁻ z, f (latentCentered w,z) ∂gaussianReal 0 1) ∂P :=
        lintegral_map hf.lintegral_prod_right' ht
      _ ≤ _ := latent_lintegral_le_two_envelopes P kappa hP.weakDesign
        (fun t => ∫⁻ z, f (t,z) ∂gaussianReal 0 1) hf.lintegral_prod_right'
  have hsq : Integrable (fun w => (q.ell (observedCentered sigma w))^2) P := by
    refine ⟨(hv.pow_const 2).aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun w => sq_nonneg _))).2
    exact hsecond.trans_lt (ENNReal.add_lt_top.mpr ⟨hJ, hJ⟩)
  exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    ((memLp_two_iff_integrable_sq hv.aestronglyMeasurable).mpr hsq)

/-- The constant dictionary element is the degree-one polynomial inverse pair. [This is the stated conclusion](goal). -/
-- @node: constant_pair_eq_inverseheat_one
lemma constant_pair_eq_inverseheat_one (sigma : ℝ) :
    pairOf sigma .const = (⟨qM 1, ellM sigma 1⟩ : WeightPair) := by
  have hp : qMPoly 1 = 1 := by simp [qMPoly, Polynomial.Chebyshev.U_zero]
  have hq : (fun _ : ℝ => (1 : ℝ)) = qM 1 := by
    funext t
    simp [qM, hp]
  have hell : (fun _ : ℝ => (1 : ℝ)) = ellM sigma 1 := by
    funext t
    simp [ellM, hp]
  exact congrArg₂ WeightPair.mk hq hell

/-- Every dictionary member satisfies its family's admissibility domain. [Under the stated conditions](hyp:htag,hkappa,hsigma). [This is the stated conclusion](goal). -/
-- @node: dictionary_pair_admissible
lemma dictionary_pair_admissible (kappa sigma : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (n : ℕ) (tag : DictTag) (htag : tag ∈ weightDictionary n sigma) :
    PairAdmissible kappa sigma (pairOf sigma tag) ∧
      VqENN kappa sigma (pairOf sigma tag).ell < ⊤ := by
  cases tag with
  | const =>
      rw [constant_pair_eq_inverseheat_one]
      exact inverseheat_pair_admissible_one kappa sigma hkappa.1
  | fourier k =>
      have hupper : dyadicBandwidth k ≤ 1/4 := by
        simp [weightDictionary, dictionaryList] at htag
        simpa only [one_div] using htag.2.2
      exact fourier_pair_admissible kappa sigma hkappa hsigma (dyadicBandwidth k)
        ⟨by unfold dyadicBandwidth; positivity, hupper⟩
  | poly j =>
      have hodd : Odd (2^j+1) := by
        simp [weightDictionary, dictionaryList] at htag
        exact htag.2.1
      exact inverseheat_pair_admissible kappa sigma hkappa hsigma (2^j+1)
        ⟨hodd, Nat.succ_pos _⟩

/-- The factor by which the public certificate can exceed the unit-constant reference certificate: [the largest of one, the upper envelope over sixty-four times the lower envelope, and the square root of the upper envelope over sixteen divided by sixteen times the minimum stratum mass times the lower envelope](goal), for [the public class constants](hyp:K). -/
@[no_expose]
def scoreScale (K : ClassConstants) : ℝ :=
  max 1 (max (K.chi / (64 * K.clo)) (Real.sqrt (K.chi / 16) / (16 * K.pmin * K.clo)))

/-- [The score scale of any public class constants](hyp:K) [is positive](goal). -/
lemma scoreScale_pos (K : ClassConstants) : 0 < scoreScale K :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

/-- [For an admissible inverse pair](hyp:hq), [the public error certificate at class constants K is at most the score scale times the unit-constant reference certificate](goal). -/
lemma Aq_le_scoreScale_mul_unitAq (K : ClassConstants) (beta kappa sigma : ℝ) (n : ℕ)
    (q : WeightPair) (hq : PairAdmissible kappa sigma q) :
    Aq K beta kappa n sigma q ≤ scoreScale K * unitAq beta kappa n sigma q := by
  have hI : 0 < weightMoment kappa q.q := hq.2.2.2.2.1
  have hp := K.pmin_pos
  have hB : 0 ≤ unitBq beta kappa q.q := by
    unfold unitBq
    apply div_nonneg _ hI.le
    apply mul_nonneg (by norm_num)
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hq.2.2.1 u hu)
  have hc : 0 ≤ 12 / unitbq kappa q.q := by unfold unitbq; positivity
  have hs : 0 ≤ Real.sqrt (Vq kappa sigma q.ell / n) := Real.sqrt_nonneg _
  have ht : 0 ≤ 2 * Real.sqrt (3 / n) := by positivity
  have hlo := K.clo_pos
  have hchi : 0 ≤ K.chi := hlo.le.trans K.clo_le_chi
  have hBK : Bq K beta kappa q.q = K.chi / (64 * K.clo) * unitBq beta kappa q.q := by
    unfold Bq unitBq
    field_simp
  have hsq : Real.sqrt (pubVq K kappa sigma q.ell / n) =
      Real.sqrt (K.chi / 16) * Real.sqrt (Vq kappa sigma q.ell / n) := by
    rw [pubVq_eq, mul_div_assoc, Real.sqrt_mul (div_nonneg hchi (by norm_num))]
  have hcoef : 12 / bq K kappa q.q * Real.sqrt (pubVq K kappa sigma q.ell / n) =
      Real.sqrt (K.chi / 16) / (16 * K.pmin * K.clo) *
        (12 / unitbq kappa q.q * Real.sqrt (Vq kappa sigma q.ell / n)) := by
    rw [hsq]
    unfold bq unitbq
    field_simp
  have hA : Aq K beta kappa n sigma q =
      K.chi / (64 * K.clo) * unitBq beta kappa q.q +
      Real.sqrt (K.chi / 16) / (16 * K.pmin * K.clo) *
        (12 / unitbq kappa q.q * Real.sqrt (Vq kappa sigma q.ell / n)) +
      2 * Real.sqrt (3 / n) := by
    unfold Aq
    rw [hBK, hcoef]
  have hU : unitAq beta kappa n sigma q = unitBq beta kappa q.q +
      12 / unitbq kappa q.q * Real.sqrt (Vq kappa sigma q.ell / n) + 2 * Real.sqrt (3 / n) := rfl
  have h1 : 1 ≤ scoreScale K := le_max_left _ _
  have h2 : K.chi / (64 * K.clo) ≤ scoreScale K := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : Real.sqrt (K.chi / 16) / (16 * K.pmin * K.clo) ≤ scoreScale K :=
    (le_max_right _ _).trans (le_max_right _ _)
  have e1 := mul_le_mul_of_nonneg_right h2 hB
  have e2 := mul_le_mul_of_nonneg_right h3 (mul_nonneg hc hs)
  have e3 := mul_le_mul_of_nonneg_right h1 ht
  rw [hA, hU, mul_add, mul_add]
  linarith

/-- [A dictionary tag](hyp:htag) whose [unit-constant reference score is at most a multiple of a rate](hyp:h) [has public score at most the score scale times that multiple of the rate](goal), [for a design exponent between zero and two](hyp:hkappa) and [an error scale between zero and one quarter](hyp:hsigma). -/
lemma score_le_of_unitScore_le (K : ClassConstants) (beta kappa sigma : ℝ)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) (hsigma : sigma ∈ Icc (0 : ℝ) (1/4)) (n : ℕ)
    (tag : DictTag) (htag : tag ∈ weightDictionary n sigma) {C r : ℝ}
    (h : unitScore beta kappa n sigma tag ≤ C * r) :
    score K beta kappa n sigma tag ≤ scoreScale K * C * r := by
  obtain ⟨hq, _⟩ := dictionary_pair_admissible kappa sigma hkappa hsigma n tag htag
  apply (Aq_le_scoreScale_mul_unitAq K beta kappa sigma n _ hq).trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h (scoreScale_pos K).le

/-- Every dictionary pair is admissible, and branch-specific witnesses control the selected public score uniformly. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: lem:dictionary-score-rate
lemma dictionary_score_rate (E : PathSpace S) (K : ClassConstants) (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    (∀ n : ℕ, 0 < n → ∀ sigma ∈ Icc (0 : ℝ) (1/4), ∀ tag ∈ weightDictionary n sigma,
      PairAdmissible kappa sigma (pairOf sigma tag) ∧
      VqENN kappa sigma (pairOf sigma tag).ell < ⊤ ∧
      ∀ P : modelClass E K beta kappa sigma,
        LawAdmissible sigma (P.1 : Measure (StructSpace S)) (pairOf sigma tag)) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n ≥ n0, ∀ sigma ∈ Icc (0 : ℝ) (1/4),
      score K beta kappa n sigma (selectedTag K beta kappa n sigma) ≤ C*frontierRate beta kappa sigma n ∧
      (sigma ≤ (logScale n)^(-1/2 : ℝ) → ∃ k : ℕ,
        DictTag.fourier k ∈ weightDictionary n sigma ∧
        score K beta kappa n sigma (.fourier k) ≤ C*frontierRate beta kappa sigma n) ∧
      ((logScale n)^(-1/2 : ℝ) < sigma → ∃ j : ℕ,
        DictTag.poly j ∈ weightDictionary n sigma ∧
        score K beta kappa n sigma (.poly j) ≤ C*frontierRate beta kappa sigma n)) := by
  constructor
  · intro n hn sigma hsigma tag htag
    obtain ⟨hq, hV⟩ := dictionary_pair_admissible kappa sigma hkappa hsigma n tag htag
    refine ⟨hq, hV, ?_⟩
    intro P
    exact dictionary_pair_law_admissible E beta kappa sigma hkappa hsigma
      (P.1 : Measure (StructSpace S)) P.2 (pairOf sigma tag) hq hV
  · obtain ⟨CF, hCF, nF, hF⟩ := fourier_dictionary_witness beta kappa hbeta hkappa
    obtain ⟨CM, hCM, nM, hM⟩ := inverseheat_dictionary_witness beta kappa hbeta hkappa
    refine ⟨scoreScale K * max CF CM, mul_pos (scoreScale_pos K) (lt_max_of_lt_left hCF), max 3 (max nF nM), ?_⟩
    intro n hn sigma hsigma
    have hnF : nF ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
    have hnM : nM ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
    have hnreal : (1 : ℝ) ≤ n := by
      exact_mod_cast (show 1 ≤ n by omega)
    have hexp : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hlog : 0 ≤ logScale n := Real.log_nonneg (by
      exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hnreal)
    have hrho : 0 ≤ frontierRate beta kappa sigma n := Real.rpow_nonneg (by
      unfold frontierScale
      split_ifs
      · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
      · exact div_nonneg hsigma.1 (Real.sqrt_nonneg _)
      · exact div_nonneg (Real.log_nonneg (by
          have hm : 0 ≤ sigma^2 * logScale n := mul_nonneg (sq_nonneg sigma) hlog
          linarith)) hlog) _
    have hFourier : sigma ≤ (logScale n)^(-1/2 : ℝ) → ∃ k : ℕ,
        DictTag.fourier k ∈ weightDictionary n sigma ∧
        score K beta kappa n sigma (.fourier k) ≤ scoreScale K * max CF CM * frontierRate beta kappa sigma n := by
      intro hbranch
      obtain ⟨k, hk, hscore⟩ := hF n hnF sigma hsigma hbranch
      exact ⟨k, hk, score_le_of_unitScore_le K beta kappa sigma hkappa hsigma n _ hk (hscore.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrho))⟩
    have hPoly : (logScale n)^(-1/2 : ℝ) < sigma → ∃ j : ℕ,
        DictTag.poly j ∈ weightDictionary n sigma ∧
        score K beta kappa n sigma (.poly j) ≤ scoreScale K * max CF CM * frontierRate beta kappa sigma n := by
      intro hbranch
      obtain ⟨j, hj, hscore⟩ := hM n hnM sigma hsigma hbranch
      exact ⟨j, hj, score_le_of_unitScore_le K beta kappa sigma hkappa hsigma n _ hj (hscore.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hrho))⟩
    refine ⟨?_, hFourier, hPoly⟩
    obtain ⟨_, hmin⟩ := selectedTag_minimizes K beta kappa n sigma
    by_cases hbranch : sigma ≤ (logScale n)^(-1/2 : ℝ)
    · obtain ⟨k, hk, hbound⟩ := hFourier hbranch
      exact (hmin _ hk).trans hbound
    · obtain ⟨j, hj, hbound⟩ := hPoly (lt_of_not_ge hbranch)
      exact (hmin _ hj).trans hbound

end CausalSmith.Stat.NoisydoseWeakdesignTransition

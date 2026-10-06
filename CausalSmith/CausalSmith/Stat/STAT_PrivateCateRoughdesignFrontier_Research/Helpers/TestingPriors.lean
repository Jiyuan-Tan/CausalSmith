module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentContraction
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentCoupling
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.Construction
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.DirectCoupling
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.CosineCertificate
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.CosineRegularity
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.PrivateComparison
/-! Two finite, class-supported priors with fixed target separation and uniformly close
outputs under every private Markov kernel. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- A finite prior uniformly averages the observed product laws of its constituent causal laws. -/
def finiteProductMixture (n s : ℕ) (family : Fin s → CausalLaw) : Measure (Dataset n) :=
  (s : ℝ≥0∞)⁻¹ • ∑ i : Fin s, dataLaw n (family i)

/-- The direct alternative has the localized contrast prescribed by the construction.  [the theorem's stated inputs and assumptions](hyp:x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: directAlternative_contrast
lemma directAlternative_contrast (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (x : Covariate) : tau (directAlternative hL hhL) x = separation hL * bump hL x := by
  change (1/2 + separation hL * bump hL x) - 1/2 = _
  ring

/-- The direct alternative has exactly the common target required by the testing prior.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: directAlternative_target
lemma directAlternative_target (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4) :
    theta (directAlternative hL hhL) = separation hL := by
  rw [theta, directAlternative_contrast, bump_at_target hL hhL.1.le, mul_one]

/-- Scaling the bump cancels its inverse-radius modulus, giving radius-three regularity.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: directAlternative_contrast_lipschitz
lemma directAlternative_contrast_lipschitz (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4) :
    ContrastLipschitz (directAlternative hL hhL) := by
  intro x y
  rw [directAlternative_contrast, directAlternative_contrast, ← mul_sub, abs_mul]
  have ht : 0 ≤ separation hL := (separation_le_sqrt hL hhL).1
  rw [abs_of_nonneg ht]
  calc
    _ ≤ separation hL * ((2*Real.pi/hL)*|(x : ℝ)-y|) :=
      mul_le_mul_of_nonneg_left (bump_difference_bound hL hhL.1 x y) ht
    _ = (2*Real.pi*kappa)*|(x : ℝ)-y| := by
      unfold separation
      field_simp [hhL.1.ne']
    _ ≤ L*|(x : ℝ)-y| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      norm_num [kappa, L]
      linarith [Real.pi_lt_four]

/-- The explicit direct law satisfies every condition of the complete unknown-density model.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: directAlternative_completeModel
lemma directAlternative_completeModel (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4) :
    CompleteModel (directAlternative hL hhL) := by
  apply binaryCausalLaw_completeModel (fun _ => 1/2) (fun _ => 1/2) (directMu1 hL)
    measurable_const measurable_const (measurable_directMu1 hL)
    (direct_parameters_range hL hhL)
  · exact binaryCausalLaw_exchangeability _ _ _ measurable_const measurable_const
      (measurable_directMu1 hL) (direct_parameters_range hL hhL)
  · intro x
    norm_num
  · intro x y
    simp only [sub_self, abs_zero]
    exact mul_nonneg (by norm_num [L]) (Real.rpow_nonneg (abs_nonneg _) _)
  · intro x y
    simp only [sub_self, abs_zero]
    exact mul_nonneg (by norm_num [L]) (Real.rpow_nonneg (abs_nonneg _) _)
  · exact directAlternative_contrast_lipschitz hL hhL

/-- A singleton uniform prior is the observed product law itself.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,P). -/
-- @node: finiteProductMixture_singleton
lemma finiteProductMixture_singleton (n : ℕ) (P : CausalLaw) :
    finiteProductMixture n 1 (fun _ => P) = dataLaw n P := by
  simp [finiteProductMixture]

/-- Enumerating all sign vectors gives exactly the uniform sign mixture.  [the theorem's stated inputs and assumptions](hyp:e), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,hL,hhL). -/
-- @node: finiteProductMixture_signs
lemma finiteProductMixture_signs (n : ℕ) (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (e : Fin (Fintype.card (SignVector hL)) ≃ SignVector hL) :
    finiteProductMixture n (Fintype.card (SignVector hL))
      (fun i => cosineFamily hL hhL (e i)) = signMixture hL hhL n := by
  classical
  have hc0 : (Fintype.card (SignVector hL) : ℝ≥0∞) ≠ 0 := by positivity
  have hcT : (Fintype.card (SignVector hL) : ℝ≥0∞) ≠ ⊤ := by finiteness
  have hw : ENNReal.ofReal ((2 : ℝ)^(-((activeSigns hL).card : ℤ))) =
      (Fintype.card (SignVector hL) : ℝ≥0∞)⁻¹ := by
    calc
      _ = _ * ((Fintype.card (SignVector hL) : ℝ≥0∞) *
          (Fintype.card (SignVector hL) : ℝ≥0∞)⁻¹) := by
        rw [ENNReal.mul_inv_cancel hc0 hcT, mul_one]
      _ = _ := by rw [← mul_assoc, sign_weight_normalization, one_mul]
  have hs : (∑ i : Fin (Fintype.card (SignVector hL)),
      dataLaw n (cosineFamily hL hhL (e i))) =
      ∑ lam : SignVector hL, dataLaw n (cosineFamily hL hhL lam) := by
    exact Finset.sum_equiv e (by simp) (by simp)
  simp only [finiteProductMixture, signMixture, hw, hs]

/-- The sampling-radius sign experiment remains close after every Markov release.  [the theorem's stated inputs and assumptions](hyp:n,hL,hhL,hscale,n,B,M), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:gate). -/
-- @node: sampling_sign_output_TV_le
lemma sampling_sign_output_TV_le (gate : BoundedDifferencesMGF)
    (n : ℕ) (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (hscale : (n : ℝ) ^ 2 * hL ^ 8 ≤ 1 / 4 ^ 8)
    {B : Type*} [MeasurableSpace B] (M : Kernel (Dataset n) B) [IsMarkovKernel M] :
    TV (M ∘ₘ dataLaw n fairNull) (M ∘ₘ signMixture hL hhL n) ≤ 1 / 4 := by
  let := signMixture_probability hL hhL n
  have hm : Measurable observe := by unfold observe X A Y; fun_prop
  let : IsProbabilityMeasure (Pobs fairNull) := Measure.isProbabilityMeasure_map hm.aemeasurable
  let : IsProbabilityMeasure (dataLaw n fairNull) := by
    unfold dataLaw
    infer_instance
  have hcert := positive_family_certificate hL hhL gate n
  let v := 160*(n : ℝ)^2*(separation hL)^2*hL*deltaL hL
  have hv : 0 ≤ v ∧ v ≤ 1 / 16 := by
    have hid : v = 160*kappa^2*((n : ℝ)^2*hL^8) := by
      dsimp [v, separation, deltaL]
      ring
    rw [hid]
    constructor
    · positivity
    · have hb := mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 160*kappa^2)
      norm_num [kappa] at hb ⊢
      linarith
  have hchi : Causalean.Stat.chiSqDiv (signMixture hL hhL n) (dataLaw n fairNull) ≤
      1 / 4 := by
    have hx := exp_privacy_increment_le v ⟨hv.1, hv.2.trans (by norm_num)⟩
    have hc := hcert.2.2.2.2.2.1
    change Causalean.Stat.chiSqDiv _ _ ≤ Real.exp v - 1 at hc
    linarith
  have htv := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv
    (signMixture hL hhL n) (dataLaw n fairNull) hcert.2.2.2.2.2.2.1 hcert.2.2.2.2.2.2.2
  have hroot : Real.sqrt (Causalean.Stat.chiSqDiv (signMixture hL hhL n)
      (dataLaw n fairNull)) ≤ 1 / 2 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num, by nlinarith⟩
  change Causalean.Stat.tvDist _ _ ≤ _
  rw [Causalean.Stat.tvDist_symm]
  exact (kernel_TV_contraction M _ _).trans (by change TV _ _ ≤ _ at htv; linarith)

/-- The proof selects signs when the sampling scale is a maximum, or when the sparse scale
strictly dominates both other scales. At sample size times budget at most one it selects the
direct family; otherwise ties favor sampling, then direct, then sparse. -/
def testingUsesSigns (n : ℕ) (epsilon : ℝ) : Prop :=
  let a := (n : ℝ)^(-1/4 : ℝ)
  let b := ((n : ℝ)^2*epsilon)^(-1/7 : ℝ)
  let c := ((n : ℝ)*epsilon)^(-1/2 : ℝ)
  1 < (n : ℝ)*epsilon ∧ ((b ≤ a ∧ c ≤ a) ∨ (a < b ∧ c < b))

/-- In every branch selecting the direct experiment, the benchmark is the capped
square-root privacy scale, including ties with the sparse scale. The result uses [the stated assumptions](hyp:hn,he,hnot) and establishes [the displayed conclusion](goal). -/
-- @node: testing_direct_rate
lemma testing_direct_rate (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n) (he : 0 < epsilon)
    (hnot : ¬ testingUsesSigns n epsilon) :
    rate n epsilon = min 1 (((n : ℝ)*epsilon)^(-1/2 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbase : 0 < (n : ℝ)*epsilon := mul_pos hn0 he
  by_cases hbudget : 1 < (n : ℝ)*epsilon
  · let a := (n : ℝ)^(-1/4 : ℝ)
    let b := ((n : ℝ)^2*epsilon)^(-1/7 : ℝ)
    let c := ((n : ℝ)*epsilon)^(-1/2 : ℝ)
    have hac : a ≤ c := by
      by_contra h
      have hca : c < a := lt_of_not_ge h
      by_cases hba : b ≤ a
      · exact hnot ⟨hbudget, Or.inl ⟨hba, hca.le⟩⟩
      · have hab : a < b := lt_of_not_ge hba
        exact hnot ⟨hbudget, Or.inr ⟨hab, hca.trans hab⟩⟩
    have hbc : b ≤ c := by
      by_contra h
      have hcb : c < b := lt_of_not_ge h
      exact hnot ⟨hbudget, Or.inr ⟨hac.trans_lt hcb, hcb⟩⟩
    dsimp [a, b, c] at hac hbc
    simp only [rate, max_eq_right hbc, max_eq_right hac]
  · have hc : 1 ≤ ((n : ℝ)*epsilon)^(-1/2 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_nonpos hbase (le_of_not_gt hbudget)
        (by norm_num : (-1/2 : ℝ) ≤ 0)
    rw [rate, min_eq_left (hc.trans ((le_max_right _ _).trans (le_max_right _ _))),
      min_eq_left hc]

/-- The selected direct radius has the uniformly small privacy-transport scale
computed in the testing-prior roadmap.  [the theorem's stated inputs and assumptions](hyp:he,hnot), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon,hn). -/
-- @node: testing_direct_privacy_scale_le
lemma testing_direct_privacy_scale_le (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n)
    (he : 0 < epsilon) (hnot : ¬ testingUsesSigns n epsilon) :
    2*epsilon*(n : ℝ)*separation (rate n epsilon / 4)*(rate n epsilon / 4) ≤ kappa/8 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbase : 0 < (n : ℝ)*epsilon := mul_pos hn0 he
  have hr0 : 0 ≤ rate n epsilon := (rate_pos n epsilon (by omega)).le
  have hr := testing_direct_rate n epsilon hn he hnot
  have hrc : rate n epsilon ≤ ((n : ℝ)*epsilon)^(-1/2 : ℝ) := by
    rw [hr]
    exact min_le_right _ _
  have hc0 : 0 ≤ ((n : ℝ)*epsilon)^(-1/2 : ℝ) := Real.rpow_nonneg hbase.le _
  have hp : (((n : ℝ)*epsilon)^(-1/2 : ℝ))^2 = ((n : ℝ)*epsilon)⁻¹ := by
    rw [← Real.rpow_mul_natCast hbase.le]
    norm_num [Real.rpow_neg_one]
  have hsquare : (rate n epsilon)^2 ≤ ((n : ℝ)*epsilon)⁻¹ := by
    rw [← hp]
    nlinarith
  have hscale : ((n : ℝ)*epsilon)*(rate n epsilon)^2 ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hsquare hbase.le
    simpa only [mul_inv_cancel₀ hbase.ne'] using hm
  calc
    _ = (kappa/8)*(((n : ℝ)*epsilon)*(rate n epsilon)^2) := by
      unfold separation
      ring
    _ ≤ (kappa/8)*1 := mul_le_mul_of_nonneg_left hscale (by norm_num [kappa])
    _ = _ := mul_one _

/-- The proof-selected uniform sign mixture or direct product law at one quarter of the
benchmark has the stated separation and TV bound after every private standard-Borel release.  [the theorem's stated inputs and assumptions](hyp:boundedDifferences_of_gate,cayley_of_gate,n,epsilon,hn,he), and [the asserted conclusion follows](goal). -/
-- @node: lem:frontier-testing-priors
lemma frontier_testing_priors
    (boundedDifferences_of_gate : BoundedDifferencesMGF)
    (cayley_of_gate : CayleyLabeledTreeCount)
    (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n) (he : 0 < epsilon ∧ epsilon ≤ 1) :
    ∃ (s0 s1 : ℕ) (F0 : Fin s0 → CausalLaw) (F1 : Fin s1 → CausalLaw) (Delta : ℝ),
      0 < s0 ∧ 0 < s1 ∧ (2 : ℝ)^(-14 : ℤ)*rate n epsilon ≤ Delta ∧
      (∀ i, CompleteModel (F0 i) ∧ theta (F0 i) = 0) ∧
      (∀ i, CompleteModel (F1 i) ∧ theta (F1 i) = Delta) ∧
      (∃ hL : ℝ, ∃ hhL : 0 < hL ∧ hL ≤ 1/4,
        hL = rate n epsilon / 4 ∧
        (∀ i, F0 i = fairNull) ∧
        (testingUsesSigns n epsilon →
          (∀ i, ∃ lam : SignVector hL, F1 i = cosineFamily hL hhL lam) ∧
          finiteProductMixture n s1 F1 = signMixture hL hhL n) ∧
        (¬ testingUsesSigns n epsilon →
          (∀ i, F1 i = directAlternative hL hhL) ∧
          finiteProductMixture n s1 F1 = dataLaw n (directAlternative hL hhL))) ∧
      (∀ (B : Type*) [MeasurableSpace B] [StandardBorelSpace B]
        (M : Kernel (Dataset n) B) [IsMarkovKernel M], PrivateKernel n epsilon M →
        TV (M ∘ₘ finiteProductMixture n s0 F0)
          (M ∘ₘ finiteProductMixture n s1 F1) ≤ 1 / 4) := by
  classical
  let hL := rate n epsilon / 4
  have hhL : 0 < hL ∧ hL ≤ 1 / 4 := by
    constructor
    · exact div_pos (rate_pos n epsilon (by omega)) (by norm_num)
    · have hr : rate n epsilon ≤ 1 := min_le_left _ _
      dsimp [hL]
      linarith
  have hsep : separation hL = (2 : ℝ)^(-14 : ℤ) * rate n epsilon := by
    dsimp [separation, kappa, hL]
    norm_num
    ring
  by_cases hsign : testingUsesSigns n epsilon
  · let s := Fintype.card (SignVector hL)
    let e : Fin s ≃ SignVector hL := (Fintype.equivFin (SignVector hL)).symm
    refine ⟨1, s, (fun _ => fairNull), (fun i => cosineFamily hL hhL (e i)),
      separation hL, by omega, Fintype.card_pos, hsep.ge, ?_, ?_, ?_, ?_⟩
    · intro i
      exact ⟨fairNull_completeModel, fairNull_target⟩
    · intro i
      exact ⟨cosineFamily_completeModel hL hhL (e i), cosineFamily_target hL hhL (e i)⟩
    · refine ⟨hL, hhL, rfl, (fun _ => rfl), ?_, ?_⟩
      · intro _
        exact ⟨fun i => ⟨e i, rfl⟩, finiteProductMixture_signs n hL hhL e⟩
      · intro hnot
        exact False.elim (hnot hsign)
    · intro B _ _ M _ hM
      rw [finiteProductMixture_singleton, finiteProductMixture_signs n hL hhL e]
      rcases hsign with ⟨hbudget, hsampling | hsparse⟩
      · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        have ha1 := Real.rpow_le_one_of_one_le_of_nonpos hn1
          (by norm_num : (-1 / 4 : ℝ) ≤ 0)
        have hr : rate n epsilon = (n : ℝ)^(-1 / 4 : ℝ) := by
          simp only [rate, max_eq_left (max_le hsampling.1 hsampling.2), min_eq_right ha1]
        refine sampling_sign_output_TV_le boundedDifferences_of_gate n hL hhL ?_ M
        have hp : ((n : ℝ)^(-1 / 4 : ℝ))^8 = ((n : ℝ)^2)⁻¹ := by
          rw [← Real.rpow_mul_natCast hn0.le]
          norm_num
        dsimp [hL]
        rw [hr, div_pow, hp]
        have hn2 : (n : ℝ)^2 ≠ 0 := pow_ne_zero _ hn0.ne'
        field_simp [hn2]
        norm_num
      · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        let b := ((n : ℝ)^2*epsilon)^(-1 / 7 : ℝ)
        have he0 := he.1
        have hbase : 0 < (n : ℝ)^2*epsilon := by positivity
        have hb : 0 < b := Real.rpow_pos_of_pos hbase _
        have hbase1 : 1 ≤ (n : ℝ)^2*epsilon := by nlinarith
        have hb1 : b ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hbase1 (by norm_num)
        have hr : rate n epsilon = b := by
          simp only [rate, max_eq_left hsparse.2.le, max_eq_right hsparse.1.le]
          exact min_eq_right hb1
        have hocc : (n : ℝ)*b^5 ≤ 1 := by
          have hc0 : 0 < ((n : ℝ)*epsilon)^(-1 / 2 : ℝ) := by positivity
          have hl := (Real.log_le_log_iff hc0 hb).mpr hsparse.2.le
          dsimp [b] at hl
          rw [Real.log_rpow (by positivity), Real.log_rpow hbase,
            Real.log_mul hn0.ne' he.1.ne', Real.log_mul (by positivity) he.1.ne',
            Real.log_pow] at hl
          rw [← Real.log_le_log_iff (by positivity : 0 < (n : ℝ)*b^5) zero_lt_one,
            Real.log_mul hn0.ne' (pow_pos hb 5).ne', Real.log_pow, Real.log_one]
          dsimp [b]
          rw [Real.log_rpow hbase, Real.log_mul (by positivity) he.1.ne', Real.log_pow]
          linarith
        have hcap : (n : ℝ)*deltaL hL ≤ 1 / 128 := by
          dsimp [deltaL, hL]
          rw [hr, div_pow]
          nlinarith
        have hout := ((measurable_component_contraction hL hhL n cayley_of_gate
          boundedDifferences_of_gate epsilon he M hM).2.2.2.2 hcap).2
        have hp : b^7 = ((n : ℝ)^2*epsilon)⁻¹ := by
          dsimp [b]
          rw [← Real.rpow_mul_natCast hbase.le]
          norm_num [Real.rpow_neg_one]
        have hid : 2048*epsilon*separation hL*(n : ℝ)^2*hL*deltaL hL =
            2048*kappa / 4^7 := by
          dsimp [separation, deltaL, hL]
          rw [hr]
          calc
            _ = (2048*kappa / 4^7) * (((n : ℝ)^2*epsilon)*b^7) := by ring
            _ = _ := by rw [hp, mul_inv_cancel₀ hbase.ne', mul_one]
        change Causalean.Stat.tvDist _ _ ≤ _
        rw [Causalean.Stat.tvDist_symm]
        rw [hid] at hout
        exact hout.trans (by norm_num [kappa])
  · refine ⟨1, 1, (fun _ => fairNull), (fun _ => directAlternative hL hhL),
      separation hL, by omega, by omega, hsep.ge, ?_, ?_, ?_, ?_⟩
    · intro i
      exact ⟨fairNull_completeModel, fairNull_target⟩
    · intro i
      exact ⟨directAlternative_completeModel hL hhL, directAlternative_target hL hhL⟩
    · refine ⟨hL, hhL, rfl, (fun _ => rfl), ?_, ?_⟩
      · intro hy
        exact False.elim (hsign hy)
      · intro _
        exact ⟨fun _ => rfl, finiteProductMixture_singleton n _⟩
    · intro B _ _ M _ hM
      rw [finiteProductMixture_singleton, finiteProductMixture_singleton]
      have hm : Measurable observe := by unfold observe X A Y; fun_prop
      let : IsProbabilityMeasure (Pobs fairNull) :=
        Measure.isProbabilityMeasure_map hm.aemeasurable
      let : IsProbabilityMeasure (Pobs (directAlternative hL hhL)) :=
        Measure.isProbabilityMeasure_map hm.aemeasurable
      let : IsProbabilityMeasure (dataLaw n fairNull) := by unfold dataLaw; infer_instance
      let : IsProbabilityMeasure (dataLaw n (directAlternative hL hhL)) := by
        unfold dataLaw; infer_instance
      have hcoupling : ∃ γ : Measure (Dataset n × Dataset n),
          Causalean.Stat.IsCoupling γ (dataLaw n fairNull)
            (dataLaw n (directAlternative hL hhL)) ∧
          (∫⁻ z, (dHam n z.1 z.2 : ℝ≥0∞) ∂γ) ≤
            ENNReal.ofReal ((n : ℝ)*separation hL*hL) := by
        exact ⟨directDatasetCoupling hL n, directDatasetCoupling_isCoupling hL hhL n,
          directDatasetCoupling_cost_le hL hhL n⟩
      obtain ⟨γ, hγ, hcost⟩ := hcoupling
      have hout := private_TV_le_coupling_cost n epsilon he M hM _ _ γ hγ
      have hscale : 2*epsilon*((n : ℝ)*separation hL*hL) ≤ kappa/8 := by
        simpa only [mul_assoc] using testing_direct_privacy_scale_le n epsilon hn he.1 hsign
      have htv : ENNReal.ofReal (TV (M ∘ₘ dataLaw n fairNull)
          (M ∘ₘ dataLaw n (directAlternative hL hhL))) ≤ ENNReal.ofReal (kappa/8) := by
        calc
          _ ≤ ENNReal.ofReal (2*epsilon)*ENNReal.ofReal ((n : ℝ)*separation hL*hL) :=
            hout.trans (mul_le_mul' le_rfl hcost)
          _ = ENNReal.ofReal (2*epsilon*((n : ℝ)*separation hL*hL)) := by
            rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) he.1.le : 0 ≤ 2*epsilon)]
          _ ≤ _ := ENNReal.ofReal_le_ofReal hscale
      have hreal := (ENNReal.ofReal_le_ofReal_iff (by norm_num [kappa] : 0 ≤ kappa/8)).mp htv
      exact hreal.trans (by norm_num [kappa])
end CausalSmith.Stat.PrivateCateRoughdesign

module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.BlockRisk
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.LocalMembership
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.RiskBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Score-threshold overlap regret — all-procedure minimax lower bound

The concrete potential-outcome law uses Mathlib measures.
The abstract POSystem and strict-overlap ATE model have different scope.
Product experiments match the paper sampling model; lower-pair proofs
reuse Causalean chi-square and total variation lemmas.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

/-- The local pair's all-procedure risk floor under its chi-square constraint. -/
-- @node: blockPair_two_point_risk
lemma blockPair_two_point_risk (m q h : ℝ) (n : ℕ)
    (hm : 0 < m ∧ m ≤ 1) (hq : 0 < q ∧ q ≤ 1/2)
    (hh : 0 < h ∧ h ≤ 1/2)
    (hinfo : 8*(n:ℝ)*m*q*h^2 ≤ 1/32) :
    ∀ Φ : Learner n, LearnerClass n Φ →
      max (∫ du, rawRegret (blockPair m q h true)
            (fun x => Φ (blockLogger m q) du.1 du.2 x)
            ∂experiment (blockPair m q h true) n)
          (∫ du, rawRegret (blockPair m q h false)
            (fun x => Φ (blockLogger m q) du.1 du.2 x)
            ∂experiment (blockPair m q h false) n) ≥ m*h/4 := by
  intro Φ hΦ
  have hw (σ : Bool) : WellFormed (blockPair m q h σ) :=
    blockPair_wellFormed m q h σ hq.1.le (by linarith [hq.2])
      hh.1.le (by linarith [hh.2])
  haveI := blockPair_obsLaw_probability m q h true
  haveI := blockPair_obsLaw_probability m q h false
  haveI := experiment_isProbability (blockPair m q h true) n (hw true)
  haveI := experiment_isProbability (blockPair m q h false) n (hw false)
  have hac := blockPair_obsLaw_sign_absolutelyContinuous m q h
    (by linarith [hh.1]) (by linarith [hh.2])
  have hint := blockPair_obsLaw_sign_sq_integrable m q h
    (by linarith [hh.1]) (by linarith [hh.2])
  have hb : (n:ℝ) * Causalean.Stat.chiSqDiv
      (blockPair m q h true).obsLaw (blockPair m q h false).obsLaw ≤ 1/32 := by
    calc
      _ ≤ (n:ℝ) * (8*m*q*h^2) := mul_le_mul_of_nonneg_left
        (blockPair_obsLaw_sign_chiSqDiv_bound m q h hm.1.le hm.2
          hq.1.le (by linarith [hq.2]) hh.1.le hh.2) (Nat.cast_nonneg n)
      _ = 8*(n:ℝ)*m*q*h^2 := by ring
      _ ≤ _ := hinfo
  have htv : Causalean.Stat.tvDist (experiment (blockPair m q h true) n)
      (experiment (blockPair m q h false) n) < 1/4 := by
    rw [lowerInformation_experiment_tv _ _ n (hw true) (hw false)]
    have ht := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv
      (Measure.pi (fun _ : Fin n => (blockPair m q h true).obsLaw))
      (Measure.pi (fun _ : Fin n => (blockPair m q h false).obsLaw))
      (Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous
        _ _ hac n) (Causalean.Stat.pi_iid_integrable_sq_dev _ _ hac hint n)
    have hbound := lowerInformation_product_chi_bound _ _ hac hint n (1/32) hb
    have he := Real.add_one_le_exp (-(1/32:ℝ))
    rw [Real.exp_neg] at he
    have hmul : (31/32:ℝ) * Real.exp (1/32) ≤ 1 := by
      apply (le_div_iff₀ (Real.exp_pos _)).mp
      rw [one_div]
      linarith
    have hs : Real.sqrt (Real.exp (1/32) - 1) < 1/2 :=
      (Real.sqrt_lt' (by norm_num)).2 (by linarith)
    exact (ht.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbound)
      (by norm_num))).trans_lt (by linarith)
  have he : Measurable (fun x : Set.Icc (0:ℝ) 1 => blockLogger m q x) := by fun_prop
  have hepos : ∀ x ∈ Set.Icc (0:ℝ) 1, blockLogger m q x ∈ Set.Ioo (0:ℝ) 1 := by
    intro x hx
    unfold blockLogger
    split_ifs <;> constructor <;> linarith [hq.1, hq.2]
  obtain ⟨ψ, hψ, hvalid⟩ := learner_family_representative n (blockLogger m q) he hepos Φ hΦ
  have hp (w : (Fin n → Observation) × ℝ) : ψ w ∈ binaryPolicyClass :=
    hψ.comp (measurable_const.prodMk measurable_id)
  have hi (σ : Bool) : Integrable (fun w => rawRegret (blockPair m q h σ) (ψ w))
      (experiment (blockPair m q h σ) n) := by
    haveI := experiment_isProbability (blockPair m q h σ) n (hw σ)
    apply Integrable.of_bound
      (blockPair_regret_family_measurable m q h σ ψ hψ).aestronglyMeasurable 1
    filter_upwards with w
    have hb := blockPair_policy_regret_bounds m q h σ hh.1.le
      (by linarith [hh.2]) (ψ w) (hp w)
    simpa [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
  have hreg (σ : Bool) :
      (∫ du, rawRegret (blockPair m q h σ) (ψ du) ∂experiment (blockPair m q h σ) n) =
      ∫ du, rawRegret (blockPair m q h σ)
        (fun x => Φ (blockLogger m q) du.1 du.2 x) ∂experiment (blockPair m q h σ) n := by
    apply integral_congr_ae
    filter_upwards [learner_input_support_of_wellFormed n _ (hw σ)] with du hdu
    unfold rawRegret rawWelfare
    rw [blockPair_score_uniform]
    congr 1
    apply integral_congr_ae
    filter_upwards [(ae_restrict_mem measurableSet_Icc :
      ∀ᵐ x ∂uniformRandomizer, x ∈ Set.Icc (0:ℝ) 1)] with x hx
    rw [hvalid du.1 du.2 hdu.1 hdu.2 hx]
  have hf := lowerInformation_separated_loss_floor
    (experiment (blockPair m q h true) n) (experiment (blockPair m q h false) n)
    _ _ (hi true) (hi false) (blockPair_regret_family_measurable m q h false ψ hψ)
    (fun w => (blockPair_policy_regret_bounds m q h true hh.1.le
      (by linarith [hh.2]) (ψ w) (hp w)).1)
    (fun w => (blockPair_policy_regret_bounds m q h false hh.1.le
      (by linarith [hh.2]) (ψ w) (hp w)).1)
    (m*h) (mul_pos hm.1 hh.1)
    (fun w => blockPair_policy_regret_sum m q h hm.1.le hm.2 hh.1
      (by linarith [hh.2]) (ψ w) (hp w)) htv
  rw [hreg true, hreg false] at hf
  have hK : 0 ≤ m*h := (mul_pos hm.1 hh.1).le
  linarith


/-- The local experiment eventually has positive parameters in the two-point window. -/
-- @node: localPair_parameters_eventually
lemma localPair_parameters_eventually (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (0 < mLoc α γ θ n ∧ mLoc α γ θ n ≤ 1) ∧
      (0 < qLoc α γ θ n ∧ qLoc α γ θ n ≤ 1/2) ∧
      (0 < hLoc α γ θ n ∧ hLoc α γ θ n ≤ 1/2) := by
  filter_upwards [localPair_scales_eventually α γ θ hα hγ hθ] with n hn
  exact hn.2

/-- The local tuning makes the product information bound exactly one sixty-fourth. -/
-- @node: localPair_information_scale
lemma localPair_information_scale (α γ θ : ℝ) (n : ℕ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) (hn : 0 < n) :
    8*(n:ℝ)*mLoc α γ θ n*qLoc α γ θ n*(hLoc α γ θ n)^2 = 1/64 := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hb : 0 < betaExp α γ θ := by unfold betaExp; positivity
  have hd : 0 < DExp α γ θ := by unfold DExp; positivity
  have hh : 0 < hLoc α γ θ n := by unfold hLoc; positivity
  have hp : (hLoc α γ θ n)^(DExp α γ θ) = (64*(n:ℝ))⁻¹ := by
    rw [hLoc, ← Real.rpow_mul (by positivity)]
    have he : -(1/DExp α γ θ)*DExp α γ θ = -1 := by field_simp
    rw [he, Real.rpow_neg_one]
  calc
    8*(n:ℝ)*mLoc α γ θ n*qLoc α γ θ n*(hLoc α γ θ n)^2 =
        (n:ℝ)*(hLoc α γ θ n)^(DExp α γ θ) := by
      rw [mLoc, qLoc, DExp, Real.rpow_add hh, Real.rpow_add hh,
        Real.rpow_two]
      ring
    _ = 1/64 := by rw [hp]; field_simp

/-- The local two-point floor is a positive constant times the local risk power. -/
-- @node: localPair_risk_scale
lemma localPair_risk_scale (α γ θ : ℝ) (n : ℕ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) (hn : 0 < n) :
    mLoc α γ θ n*hLoc α γ θ n/4 =
      ((64:ℝ)^(-((α+1)/DExp α γ θ))/32) *
        (n:ℝ)^(-((α+1)/DExp α γ θ)) := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hh : 0 < hLoc α γ θ n := by unfold hLoc; positivity
  calc
    mLoc α γ θ n*hLoc α γ θ n/4 = (hLoc α γ θ n)^(α+1)/32 := by
      rw [mLoc, Real.rpow_add hh, Real.rpow_one]
      ring
    _ = ((64*(n:ℝ))^(-((α+1)/DExp α γ θ)))/32 := by
      rw [hLoc, ← Real.rpow_mul (by positivity)]
      congr 2
      ring
    _ = _ := by rw [Real.mul_rpow (by norm_num) hn'.le]; ring

/-- Joint measurability gives Borel realized policies on almost every supported experiment. -/
-- @node: learnerPolicy_measurable_ae
lemma learnerPolicy_measurable_ae (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (Φ : Learner n) (hΦ : LearnerClass n Φ) :
    ∀ᵐ du ∂experiment P n, (fun x => Φ e du.1 du.2 x) ∈ binaryPolicyClass := by
  have hψ : Measurable (fun o : FullRow => (⟨o.X,o.A,o.Y⟩ : Observation)) := by
    apply measurable_comap_iff.mpr
    exact (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ × ℝ × ℝ =>
      (t.1,t.2.1,t.2.2.1))).comp (comap_measurable _)
  have hX : Measurable (fun o : Observation => o.X) := by
    exact (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ => t.1)).comp
      (comap_measurable _)
  have hY : Measurable (fun o : Observation => o.Y) := by
    exact (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ => t.2.2)).comp
      (comap_measurable _)
  have hobs : ∀ᵐ o ∂P.obsLaw,
      o.X ∈ Set.Icc (0:ℝ) 1 ∧ o.Y ∈ Set.Icc (-1:ℝ) 1 := by
    apply (ae_map_iff hψ.aemeasurable
      ((hX measurableSet_Icc).inter (hY measurableSet_Icc))).2
    filter_upwards [ae_iff.mpr hP.wf.2.1, ae_iff.mpr hP.wf.2.2.1] with o hx hy
    exact ⟨hx,hy⟩
  haveI : IsProbabilityMeasure P.full := hP.wf.1
  haveI : IsProbabilityMeasure P.obsLaw := Measure.isProbabilityMeasure_map hψ.aemeasurable
  have hdata : ∀ᵐ d ∂sampleLaw P n, ∀ i,
      (d i).X ∈ Set.Icc (0:ℝ) 1 ∧ (d i).Y ∈ Set.Icc (-1:ℝ) 1 :=
    Filter.eventually_all.2 (fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => P.obsLaw) (i := i)).eventually hobs)
  have hU : ∀ᵐ u ∂uniformRandomizer, u ∈ Set.Icc (0:ℝ) 1 := by
    exact ae_restrict_mem measurableSet_Icc
  have he : Measurable (fun x : Set.Icc (0:ℝ) 1 => e x) := by
    have heq : (fun x : Set.Icc (0:ℝ) 1 => e x) = fun x : Set.Icc (0:ℝ) 1 => P.logger x :=
      funext (fun x => hP.known x.2)
    rw [heq]
    exact hP.wf.2.2.2.1
  have hJoint := (hΦ e he hP.loggerSpace).1
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hdata,
    Measure.quasiMeasurePreserving_snd.ae hU] with du hd hu
  change Measurable (fun x : Set.Icc (0:ℝ) 1 => Φ e du.1 du.2 x)
  let d' : Fin n → {o : Observation //
      o.X ∈ Set.Icc (0:ℝ) 1 ∧ o.Y ∈ Set.Icc (-1:ℝ) 1} :=
    fun i => ⟨du.1 i, hd i⟩
  exact hJoint.comp (show Measurable (fun x : Set.Icc (0:ℝ) 1 =>
    (d', (⟨du.2, hu⟩ : Set.Icc (0:ℝ) 1), x)) by fun_prop)

/-- The minimax policy wrapper agrees with raw regret for admissible learners. -/
-- @node: expectedRegret_eq_raw
lemma expectedRegret_eq_raw (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (Φ : Learner n) (hΦ : LearnerClass n Φ) :
    (∫ du, regret (P.toWellFormedLaw hP.wf hP.bounded)
      (measurablePolicy (fun x => Φ e du.1 du.2 x))
      ∂experiment P n) =
    ∫ du, rawRegret P (fun x => Φ e du.1 du.2 x) ∂experiment P n := by
  apply integral_congr_ae
  filter_upwards [learnerPolicy_measurable_ae α γ θ n P e hP Φ hΦ] with du hdu
  simp [regret, RowLaw.toWellFormedLaw, measurablePolicy, hdu]

/-- A legal common-logger pair's risk floor transfers to the minimax value. -/
-- @node: minimaxRegret_lower_of_two_point
lemma minimaxRegret_lower_of_two_point (α γ θ : ℝ) (n : ℕ) (b : ℝ)
    (pair : Bool → RowLaw) (e : ℝ → ℝ)
    (hmem : ∀ σ, LawClass α γ θ n (pair σ) e)
    (hrisk : ∀ Φ : Learner n, LearnerClass n Φ →
      b ≤ max (∫ du, rawRegret (pair true) (fun x => Φ e du.1 du.2 x)
        ∂experiment (pair true) n)
        (∫ du, rawRegret (pair false) (fun x => Φ e du.1 du.2 x)
        ∂experiment (pair false) n)) :
    b ≤ minimaxRegret α γ θ n := by
  haveI : Nonempty {Φ : Learner n // LearnerClass n Φ} :=
    ⟨⟨fun _ _ _ _ => false, by
      intro e he heRange
      exact ⟨measurable_const, fun e' heq z => rfl⟩⟩⟩
  unfold minimaxRegret
  apply le_ciInf
  intro Φ
  have hBdd : BddAbove (Set.range (fun Pe :
      {Pe : RowLaw × (ℝ → ℝ) // LawClass α γ θ n Pe.1 Pe.2} =>
      ∫ du, regret (Pe.1.1.toWellFormedLaw Pe.2.wf Pe.2.bounded)
        (measurablePolicy (fun x => Φ.1 Pe.1.2 du.1 du.2 x)) ∂experiment Pe.1.1 n)) := by
    refine ⟨4, ?_⟩
    rintro y ⟨Pe, rfl⟩
    dsimp only
    rw [expectedRegret_eq_raw α γ θ n Pe.1.1 Pe.1.2 Pe.2 Φ.1 Φ.2]
    exact (expectedRawRegret_bounds α γ θ n Pe.1.1 Pe.1.2 Pe.2 Φ.1).2
  have hle (σ : Bool) :
      (∫ du, rawRegret (pair σ) (fun x => Φ.1 e du.1 du.2 x)
        ∂experiment (pair σ) n) ≤
      ⨆ Pe : {Pe : RowLaw × (ℝ → ℝ) // LawClass α γ θ n Pe.1 Pe.2},
        ∫ du, regret (Pe.1.1.toWellFormedLaw Pe.2.wf Pe.2.bounded)
          (measurablePolicy (fun x => Φ.1 Pe.1.2 du.1 du.2 x)) ∂experiment Pe.1.1 n := by
    rw [← expectedRegret_eq_raw α γ θ n (pair σ) e (hmem σ) Φ.1 Φ.2]
    exact le_ciSup_of_le hBdd ⟨(pair σ, e), hmem σ⟩ le_rfl
  exact (hrisk Φ.1 Φ.2).trans (max_le (hle true) (hle false))

-- @node: lower_rate_max_eq
/-- The two lower-bound powers combine at the smaller risk exponent. -/
lemma lower_rate_max_eq (α γ θ : ℝ) (n : ℕ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) (hn : 1 ≤ n) :
    max ((n:ℝ)^(-((α+1)/DExp α γ θ)))
      ((n:ℝ)^(-(θ/(θ+1)))) = (n:ℝ)^(-rExp α γ θ) := by
  have hd : 0 < α + θ * γ := by positivity
  have hb : 0 ≤ betaExp α γ θ := by
    unfold betaExp
    positivity
  have hs : 0 < sLoc α γ θ := by
    unfold sLoc
    positivity
  have hlocal : sLoc α γ θ / (sLoc α γ θ + 1) =
      (α+1)/DExp α γ θ := by
    unfold sLoc DExp
    dsimp [betaExp]
    field_simp
    ring
  have hhigh : sHi θ / (sHi θ + 1) = θ/(θ+1) := by rfl
  have hnreal : (1:ℝ) ≤ n := by exact_mod_cast hn
  rcases le_total (sLoc α γ θ) (sHi θ) with h | h
  · have hr : (α+1)/DExp α γ θ ≤ θ/(θ+1) := by
      rw [← hlocal, ← hhigh]
      exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by nlinarith [h])
    have hp : (n:ℝ)^(-(θ/(θ+1))) ≤
        (n:ℝ)^(-((α+1)/DExp α γ θ)) :=
      Real.rpow_le_rpow_of_exponent_le hnreal (by linarith)
    simp [rExp, sExp, min_eq_left h, hlocal, max_eq_left hp]
  · have hr : θ/(θ+1) ≤ (α+1)/DExp α γ θ := by
      rw [← hlocal, ← hhigh]
      exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by nlinarith [h])
    have hp : (n:ℝ)^(-((α+1)/DExp α γ θ)) ≤
        (n:ℝ)^(-(θ/(θ+1))) :=
      Real.rpow_le_rpow_of_exponent_le hnreal (by linarith)
    simp [rExp, sExp, min_eq_right h, hhigh, max_eq_right hp]

-- @node: thm:lower-all-procedure
/-- Both mechanisms give a uniform lower bound against all fixed-logger learners. -/
theorem lower_all_procedure (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ c : ℝ, ∃ N : ℕ, 0 < c ∧
      ∀ n ≥ N,
        c*max ((n:ℝ)^(-((α+1)/DExp α γ θ)))
          ((n:ℝ)^(-(θ/(θ+1)))) ≤ minimaxRegret α γ θ n ∧
        c*max ((n:ℝ)^(-((α+1)/DExp α γ θ)))
          ((n:ℝ)^(-(θ/(θ+1)))) = c*(n:ℝ)^(-rExp α γ θ) := by
  obtain ⟨c, N, hc, hLower⟩ :
      ∃ c : ℝ, ∃ N : ℕ, 0 < c ∧
        ∀ n ≥ N,
          c*max ((n:ℝ)^(-((α+1)/DExp α γ θ)))
            ((n:ℝ)^(-(θ/(θ+1)))) ≤ minimaxRegret α γ θ n := by
    obtain ⟨Nloc, hLocMem⟩ := localPair_mem_lawClass α γ θ hα hγ hθ
    obtain ⟨Nhi, hHiMem⟩ := highPair_mem_lawClass α γ θ hα hγ hθ
    obtain ⟨c1, c2, hc1, hc2, hHiInfo⟩ :=
      high_information_all_procedure α γ θ hα hγ hθ
    let cLoc : ℝ := (64:ℝ)^(-((α+1)/DExp α γ θ))/32
    have hcLoc : 0 < cLoc := by dsimp [cLoc]; positivity
    have hc : 0 < min cLoc c2 := lt_min hcLoc hc2
    have hbound : ∀ᶠ n : ℕ in Filter.atTop,
        min cLoc c2 * max ((n:ℝ)^(-((α+1)/DExp α γ θ)))
          ((n:ℝ)^(-(θ/(θ+1)))) ≤ minimaxRegret α γ θ n := by
      filter_upwards [Filter.eventually_ge_atTop Nloc,
        Filter.eventually_ge_atTop Nhi, Filter.eventually_ge_atTop 1,
        localPair_parameters_eventually α γ θ hα hγ hθ, hHiInfo]
        with n hnLoc hnHi hn1 hparams hInfo
      have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
      have hlocal : cLoc*(n:ℝ)^(-((α+1)/DExp α γ θ)) ≤
          minimaxRegret α γ θ n := by
        apply minimaxRegret_lower_of_two_point α γ θ n _
          (localPair α γ θ n) (localLogger α γ θ n) (hLocMem n hnLoc)
        intro Φ hΦ
        have hi : 8*(n:ℝ)*mLoc α γ θ n*qLoc α γ θ n*(hLoc α γ θ n)^2 ≤
            1/32 := by
          rw [localPair_information_scale α γ θ n hα hγ hθ hn]
          norm_num
        have h := blockPair_two_point_risk (mLoc α γ θ n) (qLoc α γ θ n)
          (hLoc α γ θ n) n hparams.1 hparams.2.1 hparams.2.2 hi Φ hΦ
        rw [localPair_risk_scale α γ θ n hα hγ hθ hn] at h
        exact h
      have hhigh : c2*(n:ℝ)^(-(θ/(θ+1))) ≤ minimaxRegret α γ θ n := by
        apply minimaxRegret_lower_of_two_point α γ θ n _
          (highPair α θ n) (highLogger α θ n) (fun σ => (hHiMem n hnHi σ).1)
        intro Φ hΦ
        have h := hInfo.2.2.2 Φ hΦ
        rw [h.2] at h
        exact h.1
      rw [mul_max_of_nonneg _ _ hc.le]
      apply max_le
      · exact (mul_le_mul_of_nonneg_right (min_le_left _ _)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans hlocal
      · exact (mul_le_mul_of_nonneg_right (min_le_right _ _)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans hhigh
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hbound
    exact ⟨min cLoc c2, N, hc, hN⟩
  refine ⟨c, max N 1, hc, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  constructor
  · exact hLower n hnN
  · rw [lower_rate_max_eq α γ θ n hα hγ hθ hn1]

end CausalSmith.Stat.ScorethresholdOverlapRegret

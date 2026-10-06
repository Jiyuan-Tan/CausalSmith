module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerTrialSharp
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Product

/-! Testing estimates for the Bernoulli trial pair. -/

@[expose] public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:S,T,μ,ν,f,hf), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialReadout_tv_le {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : S → T) (hf : Measurable f) :
    Causalean.Stat.tvDist (μ.map f) (ν.map f) ≤ Causalean.Stat.tvDist μ ν := by
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  intro A
  simp only [Measure.real_def, Measure.map_apply hf A.property]
  exact Causalean.Stat.abs_measureReal_sub_le_tvDist (hf A.property)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,p), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenter_releasedLaw_map {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε) (p : ℝ) :
    releasedLaw (trialCenterFullLaw g hOverlap p) =
      ((trialOutcomeLaw p).prod trialArmLaw).map
        (fun ya : OutcomeSpace × ArmSpace =>
          (g (trialCenterScore hOverlap), ya.2,
            if ya.2 then ya.1 else trialZeroOutcome)) := by
  unfold releasedLaw trialCenterFullLaw
  rw [Measure.map_map (by unfold releasedRecord label arm observed; fun_prop)
    (trialCenterRow_measurable g hOverlap)]
  rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,p,q,hp0,hp1,hq0,hq1,n), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenter_productReleased_tv_le_latent {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    Causalean.Stat.tvDist
      (Measure.pi (fun _ : Fin n => releasedLaw (trialCenterFullLaw g hOverlap p)))
      (Measure.pi (fun _ : Fin n => releasedLaw (trialCenterFullLaw g hOverlap q))) ≤
    Causalean.Stat.tvDist
      (Measure.pi (fun _ : Fin n => (trialOutcomeLaw p).prod trialArmLaw))
      (Measure.pi (fun _ : Fin n => (trialOutcomeLaw q).prod trialArmLaw)) := by
  let f : OutcomeSpace × ArmSpace → Observation J := fun ya =>
    (g (trialCenterScore hOverlap), ya.2,
      if ya.2 then ya.1 else trialZeroOutcome)
  have hf : Measurable f := by
    dsimp [f]
    have hcond : MeasurableSet {ya : OutcomeSpace × ArmSpace | ya.2 = true} :=
      measurableSet_eq_fun measurable_snd measurable_const
    have hobs : Measurable (fun ya : OutcomeSpace × ArmSpace =>
        if ya.2 then ya.1 else trialZeroOutcome) :=
      Measurable.ite hcond measurable_fst measurable_const
    fun_prop (disch := assumption)
  have hp : IsProbabilityMeasure ((trialOutcomeLaw p).prod trialArmLaw) := by
    letI : IsProbabilityMeasure (trialOutcomeLaw p) :=
      trialOutcomeLaw_isProbabilityMeasure p hp0 hp1
    letI : IsProbabilityMeasure trialArmLaw := trialArmLaw_isProbabilityMeasure
    infer_instance
  have hq : IsProbabilityMeasure ((trialOutcomeLaw q).prod trialArmLaw) := by
    letI : IsProbabilityMeasure (trialOutcomeLaw q) :=
      trialOutcomeLaw_isProbabilityMeasure q hq0 hq1
    letI : IsProbabilityMeasure trialArmLaw := trialArmLaw_isProbabilityMeasure
    infer_instance
  letI := hp
  letI := hq
  have hmap (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
      Measure.pi (fun _ : Fin n => releasedLaw (trialCenterFullLaw g hOverlap r)) =
      (Measure.pi (fun _ : Fin n => (trialOutcomeLaw r).prod trialArmLaw)).map
        (fun z i => f (z i)) := by
    letI : IsProbabilityMeasure (trialOutcomeLaw r) :=
      trialOutcomeLaw_isProbabilityMeasure r hr0 hr1
    letI : IsProbabilityMeasure trialArmLaw := trialArmLaw_isProbabilityMeasure
    rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
    simp only [trialCenter_releasedLaw_map]
    rfl
  rw [hmap p hp0 hp1, hmap q hq0 hq1]
  exact trialReadout_tv_le _ _ _ (measurable_pi_lambda _ fun _ => hf.comp (measurable_pi_apply _))

/-- Given [the stated mathematical inputs and assumptions](hyp:p,q,hq0,hq1), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialOutcomeLaw_withDensity_center (p q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    trialOutcomeLaw p = (trialOutcomeLaw q).withDensity (fun y : OutcomeSpace =>
      if y = trialOneOutcome then ENNReal.ofReal (p / q)
      else ENNReal.ofReal ((1 - p) / (1 - q))) := by
  let f : OutcomeSpace → ENNReal := fun y =>
    if y = trialOneOutcome then ENNReal.ofReal (p / q)
    else ENNReal.ofReal ((1 - p) / (1 - q))
  have hqne : ENNReal.ofReal q ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  have h1qne : ENNReal.ofReal (1 - q) ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  change trialOutcomeLaw p = (trialOutcomeLaw q).withDensity f
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator hs f]
  unfold trialOutcomeLaw
  dsimp [f]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  simp only [lintegral_dirac]
  have h10 : trialZeroOutcome ≠ trialOneOutcome := by
    norm_num [trialZeroOutcome, trialOneOutcome]
  by_cases h1 : trialOneOutcome ∈ s
  · by_cases h0 : trialZeroOutcome ∈ s
    · simp [h1, h0, ENNReal.ofReal_div_of_pos hq0,
          ENNReal.ofReal_div_of_pos (sub_pos.mpr hq1),
          ENNReal.mul_div_cancel hqne ENNReal.ofReal_ne_top,
          ENNReal.mul_div_cancel h1qne ENNReal.ofReal_ne_top,
          h10]
    · simp [h1, h0, ENNReal.ofReal_div_of_pos hq0,
          ENNReal.mul_div_cancel hqne ENNReal.ofReal_ne_top,
          h10]
  · by_cases h0 : trialZeroOutcome ∈ s
    · simp [h1, h0, ENNReal.ofReal_div_of_pos (sub_pos.mpr hq1),
          ENNReal.mul_div_cancel h1qne ENNReal.ofReal_ne_top,
          h10]
    · simp [h1, h0, f, h10]

/-- Given [the stated mathematical inputs and assumptions](hyp:u,hu), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialOutcomeLaw_chisq_center (u : ℝ) (hu : |u| < 1 / 2) :
    Causalean.Stat.chiSqDiv (trialOutcomeLaw (1 / 2 + u))
      (trialOutcomeLaw (1 / 2)) = 4 * u ^ 2 := by
  let p : ℝ := 1 / 2 + u
  let q : ℝ := 1 / 2
  have hub := abs_lt.mp hu
  have hp0 : 0 ≤ p := by dsimp [p]; linarith
  have hp1 : p ≤ 1 := by dsimp [p]; linarith
  have hq0 : 0 < q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  letI : IsProbabilityMeasure (trialOutcomeLaw q) :=
    trialOutcomeLaw_isProbabilityMeasure q hq0.le hq1.le
  let f : OutcomeSpace → ENNReal := fun y =>
    if y = trialOneOutcome then ENNReal.ofReal (p / q)
    else ENNReal.ofReal ((1 - p) / (1 - q))
  have hf : Measurable f := by
    dsimp [f]
    exact Measurable.ite (measurableSet_singleton trialOneOutcome)
      measurable_const measurable_const
  have hwd : trialOutcomeLaw p = (trialOutcomeLaw q).withDensity f :=
    trialOutcomeLaw_withDensity_center p q hq0 hq1
  have hrn : (trialOutcomeLaw p).rnDeriv (trialOutcomeLaw q) =ᵐ[trialOutcomeLaw q] f := by
    rw [hwd]
    exact Measure.rnDeriv_withDensity _ hf
  change Causalean.Stat.chiSqDiv (trialOutcomeLaw p) (trialOutcomeLaw q) = 4 * u ^ 2
  rw [Causalean.Stat.chiSqDiv]
  trans ∫ y, ((f y).toReal - 1) ^ 2 ∂(trialOutcomeLaw q)
  · exact integral_congr_ae <| hrn.mono fun y hy => by
      dsimp
      rw [hy]
  unfold trialOutcomeLaw
  rw [integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    simp [f, trialOneOutcome, trialZeroOutcome,
      ENNReal.toReal_ofReal (div_nonneg hp0 hq0.le),
      ENNReal.toReal_ofReal
        (div_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1.le))]
    dsimp [p, q]
    norm_num [q]
    ring
  · exact Integrable.smul_measure (integrable_dirac (by simp [enorm])) (by simp)
  · exact Integrable.smul_measure (integrable_dirac (by simp [enorm])) (by simp)

/-- Given [the stated mathematical inputs and assumptions](hyp:u), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialOutcomeLaw_ac_integrable_center (u : ℝ) :
    trialOutcomeLaw (1 / 2 + u) ≪ trialOutcomeLaw (1 / 2) ∧
    Integrable (fun y : OutcomeSpace =>
      (((trialOutcomeLaw (1 / 2 + u)).rnDeriv (trialOutcomeLaw (1 / 2)) y).toReal - 1) ^ 2)
      (trialOutcomeLaw (1 / 2)) := by
  constructor
  · rw [trialOutcomeLaw_withDensity_center (1 / 2 + u) (1 / 2)
      (by norm_num) (by norm_num)]
    exact withDensity_absolutelyContinuous _ _
  · unfold trialOutcomeLaw
    apply Integrable.add_measure
    · exact Integrable.smul_measure (integrable_dirac (by simp [enorm])) (by simp)
    · exact Integrable.smul_measure (integrable_dirac (by simp [enorm])) (by simp)

/-- Given [the stated mathematical inputs and assumptions](hyp:S,T,μ,ν,ρ,hac,hint), this result [establishes the stated mathematical conclusion](goal). -/
lemma trial_ancillary_integrable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ ν : Measure S) (ρ : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hac : μ ≪ ν)
    (hint : Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ 2) ν) :
    Integrable (fun z => (((μ.prod ρ).rnDeriv (ν.prod ρ) z).toReal - 1) ^ 2)
      (ν.prod ρ) := by
  have hrn := Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.rnDeriv_prod_eq
    μ ν ρ ρ hac (Measure.AbsolutelyContinuous.refl ρ)
  have hself : ∀ᵐ z ∂ν.prod ρ, ρ.rnDeriv ρ z.2 = 1 := by
    have hs : ∀ᵐ y ∂ρ, ρ.rnDeriv ρ y = 1 := by
      filter_upwards [ρ.rnDeriv_self] with y hy
      exact hy
    have hmap : ∀ᵐ y ∂Measure.map Prod.snd (ν.prod ρ), ρ.rnDeriv ρ y = 1 := by
      simpa [MeasurePreserving.map_eq (measurePreserving_snd (μ := ν) (ν := ρ))]
        using hs
    exact (ae_map_iff (measurePreserving_snd (μ := ν) (ν := ρ)).aemeasurable
      (measurableSet_eq_fun (Measure.measurable_rnDeriv ρ ρ) measurable_const)).mp hmap
  have heq : (fun z => (((μ.prod ρ).rnDeriv (ν.prod ρ) z).toReal - 1) ^ 2)
      =ᵐ[ν.prod ρ] (fun z => ((μ.rnDeriv ν z.1).toReal - 1) ^ 2) := by
    filter_upwards [hrn, hself] with z hz hs
    simp [hz, hs]
  exact (hint.comp_fst ρ).congr heq.symm

/-- Given [the stated mathematical inputs and assumptions](hyp:S,μ,ν,hac,hint,n), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialProduct_tv_le_of_chisq {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν)
    (hint : Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ 2) ν)
    (n : ℕ) :
    Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => μ))
      (Measure.pi (fun _ : Fin n => ν)) ≤
      (1 / 2 : ℝ) * Real.sqrt ((1 + Causalean.Stat.chiSqDiv μ ν) ^ n - 1) := by
  have hacn : Measure.pi (fun _ : Fin n => μ) ≪
      Measure.pi (fun _ : Fin n => ν) :=
    Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous μ ν hac n
  have hintn := Causalean.Stat.pi_iid_integrable_sq_dev μ ν hac hint n
  have htv := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv
    (Measure.pi (fun _ : Fin n => μ))
    (Measure.pi (fun _ : Fin n => ν)) hacn hintn
  rw [show Causalean.Stat.chiSqDiv
      (Measure.pi (fun _ : Fin n => μ))
      (Measure.pi (fun _ : Fin n => ν)) =
      (1 + Causalean.Stat.chiSqDiv μ ν) ^ n - 1 by
        linarith [Causalean.Stat.one_add_chiSqDiv_pi_iid_general μ ν hac hint n]] at htv
  exact htv

/-- Given [the stated mathematical inputs and assumptions](hyp:u,hu), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenter_latent_chisq_center (u : ℝ) (hu : |u| < 1 / 2) :
    Causalean.Stat.chiSqDiv
      ((trialOutcomeLaw (1 / 2 + u)).prod trialArmLaw)
      ((trialOutcomeLaw (1 / 2)).prod trialArmLaw) = 4 * u ^ 2 := by
  have hub := abs_lt.mp hu
  letI : IsProbabilityMeasure (trialOutcomeLaw (1 / 2 + u)) :=
    trialOutcomeLaw_isProbabilityMeasure _ (by linarith) (by linarith)
  letI : IsProbabilityMeasure (trialOutcomeLaw (1 / 2)) :=
    trialOutcomeLaw_isProbabilityMeasure _ (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure trialArmLaw := trialArmLaw_isProbabilityMeasure
  have h := trialOutcomeLaw_ac_integrable_center u
  rw [Causalean.Stat.chiSqDiv_prod_ancillary _ _ trialArmLaw h.1 h.2]
  exact trialOutcomeLaw_chisq_center u hu

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,g,hOverlap,u,hu,n), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenter_productReleased_tv_bound {ε : ℝ} {J : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (u : ℝ) (hu : |u| < 1 / 2) (n : ℕ) :
    Causalean.Stat.tvDist
      (Measure.pi (fun _ : Fin n =>
        releasedLaw (trialCenterFullLaw g hOverlap (1 / 2 + u))))
      (Measure.pi (fun _ : Fin n =>
        releasedLaw (trialCenterFullLaw g hOverlap (1 / 2)))) ≤
      (1 / 2 : ℝ) * Real.sqrt ((1 + 4 * u ^ 2) ^ n - 1) := by
  have hub := abs_lt.mp hu
  let μ := (trialOutcomeLaw (1 / 2 + u)).prod trialArmLaw
  let ν := (trialOutcomeLaw (1 / 2)).prod trialArmLaw
  letI : IsProbabilityMeasure (trialOutcomeLaw (1 / 2 + u)) :=
    trialOutcomeLaw_isProbabilityMeasure _ (by linarith) (by linarith)
  letI : IsProbabilityMeasure (trialOutcomeLaw (1 / 2)) :=
    trialOutcomeLaw_isProbabilityMeasure _ (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure trialArmLaw := trialArmLaw_isProbabilityMeasure
  have h := trialOutcomeLaw_ac_integrable_center u
  have hac : μ ≪ ν := h.1.prod (Measure.AbsolutelyContinuous.refl trialArmLaw)
  have hint : Integrable (fun z => ((μ.rnDeriv ν z).toReal - 1) ^ 2) ν :=
    trial_ancillary_integrable _ _ trialArmLaw h.1 h.2
  calc
    _ ≤ Causalean.Stat.tvDist
        (Measure.pi (fun _ : Fin n => μ))
        (Measure.pi (fun _ : Fin n => ν)) :=
      trialCenter_productReleased_tv_le_latent g hOverlap
        (1 / 2 + u) (1 / 2) (by linarith) (by linarith)
        (by norm_num) (by norm_num) n
    _ ≤ (1 / 2 : ℝ) * Real.sqrt ((1 + Causalean.Stat.chiSqDiv μ ν) ^ n - 1) :=
      trialProduct_tv_le_of_chisq μ ν hac hint n
    _ = _ := by rw [trialCenter_latent_chisq_center u hu]

/-- Given [the stated mathematical inputs and assumptions](hyp:S,T,μ,ν,ρ), this result [establishes the stated mathematical conclusion](goal). -/
lemma trial_commonLog_tv_le {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ ν : Measure S) (ρ : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    Causalean.Stat.tvDist (μ.prod ρ) (ν.prod ρ) ≤
      Causalean.Stat.tvDist μ ν := by
  have h := Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_prod_le_add μ ν ρ ρ
  have hself : Causalean.Stat.tvDist ρ ρ = 0 := by
    unfold Causalean.Stat.tvDist
    simp
  simpa [hself] using h

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,hOverlap,hg,u,hu,Qj,hTrial,hLog,hInd), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenter_jointExperiment_tv_bound {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (hg : Measurable g) (u : ℝ) (hu : |u| < 1 / 2)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : JointTrialIID g Qj) (hLog : ExternalLogIID g Qj)
    (hInd : ExternalLogIndependent g Qj) :
    Causalean.Stat.tvDist
      (Qj (trialCenterFullLaw g hOverlap (1 / 2 + u))
        (Measure.dirac (trialCenterScore hOverlap)))
      (Qj (trialCenterFullLaw g hOverlap (1 / 2))
        (Measure.dirac (trialCenterScore hOverlap))) ≤
      (1 / 2 : ℝ) * Real.sqrt ((1 + 4 * u ^ 2) ^ n - 1) := by
  have hub := abs_lt.mp hu
  let H : Measure (ScoreSpace ε) := Measure.dirac (trialCenterScore hOverlap)
  let P1 := trialCenterFullLaw g hOverlap (1 / 2 + u)
  let P0 := trialCenterFullLaw g hOverlap (1 / 2)
  have hPH1 : (P1, H) ∈ ExternalLaws g :=
    ⟨trialCenterFullLaw_isProbabilityMeasure g hOverlap _ (by linarith) (by linarith),
      inferInstance,
      trialCenterFullLaw_externalScoreLaw g hOverlap hg _ (by linarith) (by linarith)⟩
  have hPH0 : (P0, H) ∈ ExternalLaws g :=
    ⟨trialCenterFullLaw_isProbabilityMeasure g hOverlap _ (by norm_num) (by norm_num),
      inferInstance,
      trialCenterFullLaw_externalScoreLaw g hOverlap hg _ (by norm_num) (by norm_num)⟩
  have hQ (P : Measure (FullRow ε J)) (hPH : (P, H) ∈ ExternalLaws g) :
      Qj P H = (Measure.pi (fun _ : Fin n => releasedLaw P)).prod
        (Measure.pi (fun _ : Fin m => H)) := by
    rw [hInd (P, H) hPH, hTrial (P, H) hPH, hLog (P, H) hPH]
  rw [hQ P1 hPH1, hQ P0 hPH0]
  letI : IsProbabilityMeasure (releasedLaw P1) := by
    exact @Measure.isProbabilityMeasure_map _ _ _ _ P1 hPH1.2.2.probabilityP _
      (by unfold releasedRecord label arm observed; fun_prop :
        Measurable (releasedRecord (ε := ε) (J := J))).aemeasurable
  letI : IsProbabilityMeasure (releasedLaw P0) := by
    exact @Measure.isProbabilityMeasure_map _ _ _ _ P0 hPH0.2.2.probabilityP _
      (by unfold releasedRecord label arm observed; fun_prop :
        Measurable (releasedRecord (ε := ε) (J := J))).aemeasurable
  letI : IsProbabilityMeasure H := inferInstance
  calc
    _ ≤ Causalean.Stat.tvDist
        (Measure.pi (fun _ : Fin n => releasedLaw P1))
        (Measure.pi (fun _ : Fin n => releasedLaw P0)) :=
      trial_commonLog_tv_le _ _ (Measure.pi (fun _ : Fin m => H))
    _ ≤ _ := trialCenter_productReleased_tv_bound g hOverlap u hu n

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,C,Q0,Q1,θ0,θ1,α,hθ,hcover0,hcover1), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalInterval_twoPoint_expectedLength {ε : ℝ} {J n m : ℕ}
    (C : ExternalIntervalProcedure ε J n m)
    (Q0 Q1 : Measure (ExternalSample ε J n m))
    [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
    (θ0 θ1 α : ℝ) (hθ : θ0 ≤ θ1)
    (hcover0 : 1 - α ≤ Q0.real {x | C.contains x θ0})
    (hcover1 : 1 - α ≤ Q1.real {x | C.contains x θ1}) :
    (θ1 - θ0) * (1 - 2 * α - Causalean.Stat.tvDist Q0 Q1) ≤
      ∫ x, C.length x ∂Q0 := by
  let A0 : Set (ExternalSample ε J n m) := {x | C.contains x θ0}
  let A1 : Set (ExternalSample ε J n m) := {x | C.contains x θ1}
  let I := A0 ∩ A1
  have hA (θ : ℝ) : MeasurableSet {x | C.contains x θ} := by
    change MeasurableSet {x | C.lo x ≤ θ ∧ θ ≤ C.hi x}
    exact (measurableSet_le C.measurable_lo measurable_const).inter
      (measurableSet_le measurable_const C.measurable_hi)
  have hA0 : MeasurableSet A0 := hA θ0
  have hA1 : MeasurableSet A1 := hA θ1
  have hI : MeasurableSet I := hA0.inter hA1
  have htransfer : 1 - α - Causalean.Stat.tvDist Q0 Q1 ≤ Q0.real A1 := by
    have htv := Causalean.Stat.measureReal_sub_le_tvDist
      (μ := Q0) (ν := Q1) hA1
    dsimp [A1] at htv
    linarith
  have hmass : 1 - 2 * α - Causalean.Stat.tvDist Q0 Q1 ≤ Q0.real I := by
    have hu : Q0.real (A0 ∪ A1) ≤ 1 := measureReal_le_one
    have hsum := measureReal_union_add_inter (μ := Q0) (s := A0) (t := A1)
      hA1 (measure_ne_top Q0 A0) (measure_ne_top Q0 A1)
    change Q0.real (A0 ∪ A1) + Q0.real I = Q0.real A0 + Q0.real A1 at hsum
    linarith
  have hlenMeas : Measurable C.length := C.measurable_hi.sub C.measurable_lo
  have hlenNonneg (x : ExternalSample ε J n m) : 0 ≤ C.length x :=
    sub_nonneg.mpr (C.ordered x)
  have hlenBound (x : ExternalSample ε J n m) : C.length x ≤ 2 := by
    dsimp [ExternalIntervalProcedure.length]
    linarith [C.lower_bound x, C.upper_bound x]
  have hlenInt : Integrable C.length Q0 := by
    apply Integrable.of_bound hlenMeas.aestronglyMeasurable 2
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hlenNonneg x)]
    exact hlenBound x
  have hindInt : Integrable (I.indicator (fun _ => θ1 - θ0)) Q0 :=
    (integrable_const _).indicator hI
  have hpoint (x : ExternalSample ε J n m) :
      I.indicator (fun _ => θ1 - θ0) x ≤ C.length x := by
    by_cases hx : x ∈ I
    · rw [Set.indicator_of_mem hx]
      have hx0 : C.lo x ≤ θ0 ∧ θ0 ≤ C.hi x := hx.1
      have hx1 : C.lo x ≤ θ1 ∧ θ1 ≤ C.hi x := hx.2
      dsimp [ExternalIntervalProcedure.length]
      linarith
    · rw [Set.indicator_of_notMem hx]
      exact hlenNonneg x
  have hmono := integral_mono hindInt hlenInt hpoint
  rw [integral_indicator_const (θ1 - θ0) hI] at hmono
  simp only [smul_eq_mul] at hmono
  rw [mul_comm (Q0.real I) (θ1 - θ0)] at hmono
  exact (mul_le_mul_of_nonneg_left hmass (sub_nonneg.mpr hθ)).trans hmono

/-- Given [the stated mathematical inputs and assumptions](hyp:α,hα,n,hn), this result [establishes the stated mathematical conclusion](goal). -/
lemma trial_calibrated_perturbation (α : ℝ) (hα : 0 < α ∧ α < 1 / 2)
    (n : ℕ) (hn : 0 < n) :
    let β := 1 - 2 * α
    let u := Real.sqrt (Real.log (1 + β ^ 2) / (n : ℝ)) / 2
    0 < u ∧ |u| < 1 / 2 ∧
      (1 + 4 * u ^ 2) ^ n ≤ 1 + β ^ 2 := by
  dsimp
  let β : ℝ := 1 - 2 * α
  let x : ℝ := Real.log (1 + β ^ 2)
  let u : ℝ := Real.sqrt (x / (n : ℝ)) / 2
  have hβ0 : 0 < β := by dsimp [β]; linarith [hα.2]
  have hβ1 : β < 1 := by dsimp [β]; linarith [hα.1]
  have hβsq : β ^ 2 < 1 := by nlinarith
  have hx0 : 0 < x := by
    dsimp [x]
    exact Real.log_pos (by nlinarith [sq_pos_of_pos hβ0])
  have hxle : x ≤ β ^ 2 := by
    dsimp [x]
    nlinarith [Real.log_le_sub_one_of_pos (show 0 < 1 + β ^ 2 by positivity)]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq0 : 0 < x / (n : ℝ) := div_pos hx0 hn0
  have hq1 : x / (n : ℝ) < 1 := (div_lt_one hn0).2 (by linarith)
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : |u| < 1 / 2 := by
    rw [abs_of_pos hu0]
    dsimp [u]
    have hs : Real.sqrt (x / (n : ℝ)) < 1 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
      simpa using hq1
    linarith
  have h4u : 4 * u ^ 2 = x / (n : ℝ) := by
    dsimp [u]
    calc
      4 * (Real.sqrt (x / (n : ℝ)) / 2) ^ 2 =
          (Real.sqrt (x / (n : ℝ))) ^ 2 := by ring
      _ = x / (n : ℝ) := Real.sq_sqrt hq0.le
  have hpow : (1 + 4 * u ^ 2) ^ n ≤ 1 + β ^ 2 := by
    rw [h4u]
    have h := Real.one_sub_div_pow_le_exp_neg (n := n) (t := -x)
      (by linarith : -x ≤ (n : ℝ))
    have hexp : Real.exp x = 1 + β ^ 2 := Real.exp_log (by positivity)
    simpa only [neg_div, sub_neg_eq_add, neg_neg, hexp] using h
  exact ⟨hu0, hu1, hpow⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:α,n), this result [establishes the stated mathematical conclusion](goal). -/
lemma trial_calibrated_coefficient (α : ℝ) (n : ℕ) :
    let β := 1 - 2 * α
    let u := Real.sqrt (Real.log (1 + β ^ 2) / (n : ℝ)) / 2
    β * u / 2 = trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ := by
  dsimp [trialCertificate]
  rw [Real.sqrt_div (Real.log_nonneg (by nlinarith [sq_nonneg (1 - 2 * α)]))
    (n : ℝ)]
  ring

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,C,Q0,Q1,α,hα,hn,u,hu,hcover0,hcover1,htv), this result [establishes the stated mathematical conclusion](goal). -/
lemma trial_calibrated_honest_expectedLength {ε : ℝ} {J n m : ℕ}
    (C : ExternalIntervalProcedure ε J n m)
    (Q0 Q1 : Measure (ExternalSample ε J n m))
    [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
    (α : ℝ) (hα : 0 < α ∧ α < 1 / 2) (hn : 0 < n)
    (u : ℝ)
    (hu : u = Real.sqrt (Real.log (1 + (1 - 2 * α) ^ 2) / (n : ℝ)) / 2)
    (hcover0 : 1 - α ≤ Q0.real {x | C.contains x (1 / 2)})
    (hcover1 : 1 - α ≤ Q1.real {x | C.contains x (1 / 2 + u)})
    (htv : Causalean.Stat.tvDist Q0 Q1 ≤
      (1 / 2 : ℝ) * Real.sqrt ((1 + 4 * u ^ 2) ^ n - 1)) :
    trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ ≤
      ∫ x, C.length x ∂Q0 := by
  have hcal := trial_calibrated_perturbation α hα n hn
  dsimp at hcal
  rw [← hu] at hcal
  rcases hcal with ⟨hu0, _, hpow⟩
  let β : ℝ := 1 - 2 * α
  have hβ0 : 0 < β := by dsimp [β]; linarith [hα.2]
  have htvhalf : Causalean.Stat.tvDist Q0 Q1 ≤ β / 2 := by
    calc
      _ ≤ (1 / 2 : ℝ) * Real.sqrt ((1 + 4 * u ^ 2) ^ n - 1) := htv
      _ ≤ (1 / 2 : ℝ) * Real.sqrt (β ^ 2) := by
        apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
        dsimp [β] at hpow ⊢
        linarith
      _ = β / 2 := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hβ0]; ring
  have hlen := externalInterval_twoPoint_expectedLength C Q0 Q1
    (1 / 2) (1 / 2 + u) α (by linarith) hcover0 hcover1
  have hcoef : β * u / 2 ≤
      u * (1 - 2 * α - Causalean.Stat.tvDist Q0 Q1) := by
    dsimp [β] at htvhalf ⊢
    nlinarith [mul_nonneg (le_of_lt hu0)
      (show 0 ≤ 1 - 2 * α - 2 * Causalean.Stat.tvDist Q0 Q1 by linarith)]
  have hident := trial_calibrated_coefficient α n
  dsimp at hident
  rw [← hu] at hident
  rw [← hident]
  have hlen' : u * (1 - 2 * α - Causalean.Stat.tvDist Q0 Q1) ≤
      ∫ x, C.length x ∂Q0 := by
    convert hlen using 1 <;> ring
  exact hcoef.trans hlen'

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,Qj,hTrial,hLog,hInd,PH,hPH), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalLaw_jointExperiment_probability {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : JointTrialIID g Qj) (hLog : ExternalLogIID g Qj)
    (hInd : ExternalLogIndependent g Qj)
    (PH : Measure (FullRow ε J) × Measure (ScoreSpace ε))
    (hPH : PH ∈ ExternalLaws g) : IsProbabilityMeasure (Qj PH.1 PH.2) := by
  have hrel : IsProbabilityMeasure (releasedLaw PH.1) := by
    exact @Measure.isProbabilityMeasure_map _ _ _ _ PH.1 hPH.2.2.probabilityP _
      (by unfold releasedRecord label arm observed; fun_prop :
        Measurable (releasedRecord (ε := ε) (J := J))).aemeasurable
  letI : IsProbabilityMeasure (releasedLaw PH.1) := hrel
  letI : IsProbabilityMeasure PH.2 := hPH.2.1
  rw [hInd PH hPH, hTrial PH hPH, hLog PH hPH]
  infer_instance

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,hOverlap,hg,α,hα,hn,Qj,hTrial,hLog,hInd,C,hC), this result [establishes the stated mathematical conclusion](goal). -/
lemma trialCenter_honest_expectedLength {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hOverlap : Overlap ε)
    (hg : Measurable g) (α : ℝ) (hα : 0 < α ∧ α < 1 / 2) (hn : 0 < n)
    (Qj : Measure (FullRow ε J) → Measure (ScoreSpace ε) →
      Measure (ExternalSample ε J n m))
    (hTrial : JointTrialIID g Qj) (hLog : ExternalLogIID g Qj)
    (hInd : ExternalLogIndependent g Qj)
    (C : ExternalIntervalProcedure ε J n m)
    (hC : C ∈ externalHonestProcedures g Qj α) :
    trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ ≤
      ∫ x, C.length x ∂(Qj (trialCenterFullLaw g hOverlap (1 / 2))
        (Measure.dirac (trialCenterScore hOverlap))) := by
  let u : ℝ := Real.sqrt (Real.log (1 + (1 - 2 * α) ^ 2) / (n : ℝ)) / 2
  have hcal := trial_calibrated_perturbation α hα n hn
  dsimp at hcal
  change 0 < u ∧ |u| < 1 / 2 ∧ _ at hcal
  have hu : |u| < 1 / 2 := hcal.2.1
  let H : Measure (ScoreSpace ε) := Measure.dirac (trialCenterScore hOverlap)
  let P0 := trialCenterFullLaw g hOverlap (1 / 2)
  let P1 := trialCenterFullLaw g hOverlap (1 / 2 + u)
  have hub := abs_lt.mp hu
  have hPH0 : (P0, H) ∈ ExternalLaws g :=
    ⟨trialCenterFullLaw_isProbabilityMeasure g hOverlap _ (by norm_num) (by norm_num),
      inferInstance,
      trialCenterFullLaw_externalScoreLaw g hOverlap hg _ (by norm_num) (by norm_num)⟩
  have hPH1 : (P1, H) ∈ ExternalLaws g :=
    ⟨trialCenterFullLaw_isProbabilityMeasure g hOverlap _ (by linarith) (by linarith),
      inferInstance,
      trialCenterFullLaw_externalScoreLaw g hOverlap hg _ (by linarith) (by linarith)⟩
  let Q0 := Qj P0 H
  let Q1 := Qj P1 H
  letI : IsProbabilityMeasure Q0 :=
    externalLaw_jointExperiment_probability g Qj hTrial hLog hInd (P0, H) hPH0
  letI : IsProbabilityMeasure Q1 :=
    externalLaw_jointExperiment_probability g Qj hTrial hLog hInd (P1, H) hPH1
  have hQ0 : Q0 = externalExperiment n m P0 H := by
    dsimp [Q0, externalExperiment]
    rw [hInd (P0, H) hPH0, hTrial (P0, H) hPH0,
      hLog (P0, H) hPH0]
  have hQ1 : Q1 = externalExperiment n m P1 H := by
    dsimp [Q1, externalExperiment]
    rw [hInd (P1, H) hPH1, hTrial (P1, H) hPH1,
      hLog (P1, H) hPH1]
  have hc0 := hC (P0, H) hPH0
  have hc1 := hC (P1, H) hPH1
  change 1 - α ≤ (externalExperiment n m P0 H).real
    {x | C.contains x (ate P0)} at hc0
  change 1 - α ≤ (externalExperiment n m P1 H).real
    {x | C.contains x (ate P1)} at hc1
  rw [← hQ0] at hc0
  rw [← hQ1] at hc1
  rw [trialCenterFullLaw_ate g hOverlap _ (by norm_num) (by norm_num)] at hc0
  rw [trialCenterFullLaw_ate g hOverlap _ (by linarith) (by linarith)] at hc1
  have htv : Causalean.Stat.tvDist Q0 Q1 ≤
      (1 / 2 : ℝ) * Real.sqrt ((1 + 4 * u ^ 2) ^ n - 1) := by
    rw [Causalean.Stat.tvDist_symm]
    exact trialCenter_jointExperiment_tv_bound g hOverlap hg u hu Qj hTrial hLog hInd
  exact trial_calibrated_honest_expectedLength C Q0 Q1 α hα hn u rfl
    hc0 hc1 htv

end
end CausalSmith.PartialID.UnlinkedPropensityAte

module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.Spacing
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.Matching

/-! # Pointwise and class-uniform oracle spacing -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

variable {d m N : ℕ} {β L cX CX cg Cg : ℝ}

-- @node: fairCoin_probability
lemma fairCoin_probability : IsProbabilityMeasure fairCoin := by
  constructor
  simpa [fairCoin] using ENNReal.inv_two_add_inv_two

-- @node: randomizerLaw_probability
lemma randomizerLaw_probability : IsProbabilityMeasure randomizerLaw := by
  constructor
  norm_num [randomizerLaw, Real.volume_Icc]

-- @node: pilotUnitLaw_probability
lemma pilotUnitLaw_probability (P : Measure (UnitRecord d))
    (hP : IsProbabilityMeasure P) : IsProbabilityMeasure (pilotUnitLaw P) := by
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure fairCoin := fairCoin_probability
  unfold pilotUnitLaw
  have hm : Measurable (fun ua : UnitRecord d × Bool => observedPilot ua.1 ua.2) := by
    unfold observedPilot
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.ite
    · exact measurable_snd (measurableSet_singleton true)
    · fun_prop
    · fun_prop
  exact Measure.isProbabilityMeasure_map hm.aemeasurable

-- @node: latentTwoWaveLaw_designDomain_ae
lemma latentTwoWaveLaw_designDomain_ae (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (hclass : RegularScoreClass P g L β cX CX cg Cg) :
    ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      designInput w ∈ designDomain m N d := by
  letI : IsProbabilityMeasure P := hclass.covariate_density.1
  letI : IsProbabilityMeasure fairCoin := fairCoin_probability
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    pilotUnitLaw_probability P hclass.covariate_density.1
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  have hcube_meas : MeasurableSet (cube d) := by
    unfold cube
    measurability
  have hXmap : ∀ᵐ x ∂P.map Prod.fst, x ∈ cube d := by
    change cube d ∈ ae (P.map Prod.fst)
    rw [mem_ae_iff]
    apply hclass.covariate_density.2.1
    simp [cubeMeasure, hcube_meas]
  have hX : ∀ᵐ u ∂P, u.1 ∈ cube d :=
    ae_of_ae_map measurable_fst.aemeasurable hXmap
  have hpilot : ∀ᵐ v ∂pilotUnitLaw P, v.1 ∈ cube d := by
    unfold pilotUnitLaw
    have hm : Measurable (fun ua : UnitRecord d × Bool => observedPilot ua.1 ua.2) := by
      unfold observedPilot
      apply Measurable.prodMk
      · fun_prop
      apply Measurable.prodMk
      · fun_prop
      apply Measurable.ite
      · exact measurable_snd (measurableSet_singleton true)
      · fun_prop
      · fun_prop
    rw [ae_map_iff hm.aemeasurable (by measurability)]
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [hX] with u hu
    filter_upwards [] with a
    simpa [observedPilot] using hu
  have hpilots : ∀ᵐ p ∂Measure.pi (fun _ : Fin m => pilotUnitLaw P),
      ∀ r, (p r).1 ∈ cube d := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hpilot
  have hmains : ∀ᵐ us ∂Measure.pi (fun _ : Fin N => P),
      ∀ i, (us i).1 ∈ cube d := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hX
  have hU : ∀ᵐ u ∂randomizerLaw, u ∈ Set.Icc (0 : ℝ) 1 := by
    unfold randomizerLaw
    exact ae_restrict_mem measurableSet_Icc
  have hdommeas : MeasurableSet
      {w : WaveInput m N d | designInput w ∈ designDomain m N d} := by
    unfold designInput designDomain cube
    measurability
  unfold latentTwoWaveLaw
  rw [Measure.ae_prod_iff_ae_ae hdommeas]
  rw [Measure.ae_prod_iff_ae_ae (by
    unfold designInput designDomain cube
    measurability)]
  filter_upwards [hpilots] with p hp
  filter_upwards [hmains] with us hus
  filter_upwards [hU] with u hu
  exact ⟨hp, hus, hu⟩

-- @node: oracleLoss_eq_latent_integral
lemma oracleLoss_eq_latent_integral (P : Measure (UnitRecord d))
    (g : XSpace d → ℝ) (M : MainCovariates N d → Match N)
    (hP : IsProbabilityMeasure P)
    (hpilot : IsProbabilityMeasure (Measure.pi fun _ : Fin m => pilotUnitLaw P))
    (hrandomizer : IsProbabilityMeasure randomizerLaw) :
    oracleLoss P g N M =
      ∫ w, pairLoss g (fun i => (w.1.2 i).1)
        (M (fun i => (w.1.2 i).1)) / (N : ℝ)
        ∂latentTwoWaveLaw (m := m) (N := N) P := by
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure (Measure.pi fun _ : Fin m => pilotUnitLaw P) := hpilot
  letI : IsProbabilityMeasure randomizerLaw := hrandomizer
  unfold oracleLoss latentTwoWaveLaw
  let f : MainSample N d → ℝ := fun us =>
    pairLoss g (fun i => (us i).1) (M (fun i => (us i).1)) / (N : ℝ)
  change (∫ us, f us ∂Measure.pi fun _ : Fin N => P) =
    ∫ w, f w.1.2 ∂((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
      (Measure.pi fun _ : Fin N => P)).prod randomizerLaw
  symm
  calc
    (∫ w, f w.1.2 ∂((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
      (Measure.pi fun _ : Fin N => P)).prod randomizerLaw) =
        ∫ z, f z.2 ∂(Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
          (Measure.pi fun _ : Fin N => P) := by
            simpa using (integral_fun_fst (μ :=
              (Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
                (Measure.pi fun _ : Fin N => P)) (ν := randomizerLaw)
                (fun z : PilotSample m d × MainSample N d => f z.2))
    _ = ∫ us, f us ∂Measure.pi fun _ : Fin N => P := by
      simpa using (integral_fun_snd (μ := Measure.pi fun _ : Fin m => pilotUnitLaw P)
        (ν := Measure.pi fun _ : Fin N => P) f)

-- @node: lem:pointwise-oracle-spacing
lemma pointwise_oracle_spacing (P : Measure (UnitRecord d))
    (g : XSpace d → ℝ) (hclass : RegularScoreClass P g L β cX CX cg Cg)
    (hscore : IsHalfSumVersion P g)
    (hpars : ValidClassParameters d β L cX CX cg Cg)
    (hN : Even N) (hN2 : 2 ≤ N) :
    1 / (Cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) ≤
      oracleLoss P g N (fun x => oracleMatching g x hN hN2) ∧
    oracleLoss P g N (fun x => oracleMatching g x hN hN2) ≤
      1 / (cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) ∧
    (∀ (m : ℕ) (D : Design m N d), MatchingDesignClass D →
      (∀ w : WaveInput m N d,
        pairLoss g (fun i => (w.1.2 i).1) (oracleMatching g (fun i => (w.1.2 i).1) hN hN2) ≤
          pairLoss g (fun i => (w.1.2 i).1) (D (designInput w))) ∧
      1 / (Cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) ≤ risk P g D ∧
      oracleLoss P g N (fun x => oracleMatching g x hN hN2) ≤ risk P g D) := by
  obtain ⟨hlower, hupper⟩ :=
    score_oracle_spacing_bound hN hN2 P g hpars hclass
  refine ⟨hlower, hupper, ?_⟩
  intro m D hD
  have hpoint : ∀ w : WaveInput m N d,
      pairLoss g (fun i => (w.1.2 i).1)
          (oracleMatching g (fun i => (w.1.2 i).1) hN hN2) ≤
        pairLoss g (fun i => (w.1.2 i).1) (D (designInput w)) := by
    intro w
    exact adjacent_matching_minimizes hN hN2 g
      (fun i => (w.1.2 i).1) (D (designInput w))
  have hrisk : oracleLoss P g N (fun x => oracleMatching g x hN hN2) ≤
      risk P g D := by
    have hP : IsProbabilityMeasure P := hclass.covariate_density.1
    letI : IsProbabilityMeasure P := hP
    letI : IsProbabilityMeasure (pilotUnitLaw P) := pilotUnitLaw_probability P hP
    have hpilot : IsProbabilityMeasure
        (Measure.pi fun _ : Fin m => pilotUnitLaw P) := inferInstance
    letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
    letI : IsProbabilityMeasure (latentTwoWaveLaw (m := m) (N := N) P) := by
      unfold latentTwoWaveLaw
      infer_instance
    rw [oracleLoss_eq_latent_integral P g
      (fun x => oracleMatching g x hN hN2) hP hpilot randomizerLaw_probability]
    have hdesign_meas : MeasurableSet (designDomain m N d) := by
      unfold designDomain cube
      measurability
    have hinput_meas : Measurable (designInput (m := m) (N := N) (d := d)) := by
      unfold designInput
      fun_prop
    have hinput_ae := latentTwoWaveLaw_designDomain_ae (m := m) (N := N) P g hclass
    have hmap_ae : ∀ᵐ v ∂(latentTwoWaveLaw (m := m) (N := N) P).map designInput,
        v ∈ designDomain m N d := by
      exact (ae_map_iff hinput_meas.aemeasurable hdesign_meas).2 hinput_ae
    have hD_ae : AEMeasurable (fun w : WaveInput m N d => D (designInput w))
        (latentTwoWaveLaw (m := m) (N := N) P) := by
      have hDmap : AEMeasurable D
          ((latentTwoWaveLaw (m := m) (N := N) P).map designInput) := by
        rw [← Measure.restrict_eq_self_of_ae_mem hmap_ae]
        exact aemeasurable_restrict_of_measurable_subtype hdesign_meas hD.2.1
      exact hDmap.comp_measurable hinput_meas
    let q : UnitRecord d → ℝ := fun u => g u.1
    let ν : Measure ℝ := P.map q
    let ρ : Measure ℝ := (volume : Measure ℝ).restrict scoreInterval
    have hreg : ν ≪ ρ ∧
        ∀ᵐ t ∂ρ, cg ≤ (ν.rnDeriv ρ t).toReal ∧
          (ν.rnDeriv ρ t).toReal ≤ Cg := by
      simpa [RegularScorePushforward, ν, ρ, q] using
        hclass.regular_score_pushforward
    have hρne : ρ ≠ 0 := by
      intro hz
      have hz' := congrArg (fun μ : Measure ℝ => μ scoreInterval) hz
      norm_num [ρ, scoreInterval, Real.volume_Icc] at hz'
    have hνne : ν ≠ 0 := by
      intro hz
      have hb := hreg.2
      rw [hz] at hb
      have hf : ∀ᵐ _t ∂ρ, False := by
        filter_upwards [hb, Measure.rnDeriv_zero ρ] with t ht ht0
        have : cg ≤ 0 := by simpa [ht0] using ht.1
        have hcg : 0 < cg := by
          rcases hpars with ⟨_, _, _, _, _, _, _, hcg, _, _⟩
          exact hcg
        linarith
      letI : (ae ρ).NeBot := (ae_neBot.mpr hρne)
      exact (Filter.Eventually.exists hf).choose_spec
    have hq : AEMeasurable q P := AEMeasurable.of_map_ne_zero hνne
    let F : WaveInput m N d → Fin N → ℝ := fun w i => q (w.1.2 i)
    have hFmain : AEMeasurable (fun us : MainSample N d => fun i => q (us i))
        (Measure.pi fun _ : Fin N => P) := by
      exact aemeasurable_pi_lambda _ fun i =>
        hq.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_eval (fun _ : Fin N => P) i)
    have hF : AEMeasurable F (latentTwoWaveLaw (m := m) (N := N) P) := by
      simpa [F, latentTwoWaveLaw] using
        ((hFmain.comp_snd (μ := Measure.pi fun _ : Fin m => pilotUnitLaw P)).comp_fst
          (ν := randomizerLaw))
    have hPairMap : Measurable (fun t : (Fin N → ℝ) × Match N =>
        ((1 / 2 : ℝ) * ∑ i : Fin N,
          (t.1 i - t.1 (t.2.val i)) ^ 2) / (N : ℝ)) := by
      classical
      have hEval (i : Fin N) :
          Measurable (fun t : (Fin N → ℝ) × Match N => t.1 (t.2.val i)) := by
        have heq : (fun t : (Fin N → ℝ) × Match N => t.1 (t.2.val i)) =
            fun t => ∑ j : Fin N, if t.2.val i = j then t.1 j else 0 := by
          funext t
          simp
        rw [heq]
        have hidx : Measurable (fun t : (Fin N → ℝ) × Match N => t.2.val i) :=
          (measurable_from_top : Measurable (fun M : Match N => M.val i)).comp
            measurable_snd
        apply Finset.measurable_sum
        intro j hj
        apply Measurable.ite
        · exact hidx (measurableSet_singleton j)
        · exact (measurable_pi_apply j).comp measurable_fst
        · exact measurable_const
      apply Measurable.div_const
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro i hi
      exact (((measurable_pi_apply i).comp measurable_fst).sub (hEval i)).pow_const 2
    have hPairAE : AEMeasurable
        (fun w : WaveInput m N d =>
          pairLoss g (fun i => (w.1.2 i).1) (D (designInput w)) / (N : ℝ))
        (latentTwoWaveLaw (m := m) (N := N) P) := by
      have hprod := hF.prodMk hD_ae
      convert hPairMap.comp_aemeasurable hprod using 1
      funext w
      simp [F, q, pairLoss]
    have hνsupp : ∀ᵐ t ∂ν, t ∈ scoreInterval := by
      change scoreInterval ∈ ae ν
      rw [mem_ae_iff]
      apply hreg.1
      simp [ρ, scoreInterval]
    have hqscore : ∀ᵐ u ∂P, q u ∈ scoreInterval :=
      ae_of_ae_map hq hνsupp
    have hmainscore : ∀ᵐ us ∂Measure.pi (fun _ : Fin N => P),
        ∀ i, q (us i) ∈ scoreInterval := by
      apply Measure.ae_pi_le_pi
      exact Filter.eventually_pi fun _ => hqscore
    have hmidscore : ∀ᵐ z ∂(Measure.pi (fun _ : Fin m => pilotUnitLaw P)).prod
        (Measure.pi fun _ : Fin N => P), ∀ i, q (z.2 i) ∈ scoreInterval := by
      have hmaps : ∀ᵐ us ∂Measure.map Prod.snd
          ((Measure.pi (fun _ : Fin m => pilotUnitLaw P)).prod
            (Measure.pi fun _ : Fin N => P)),
          ∀ i, q (us i) ∈ scoreInterval :=
        (Measure.quasiMeasurePreserving_snd (μ := Measure.pi fun _ : Fin m => pilotUnitLaw P)
          (ν := Measure.pi fun _ : Fin N => P)).absolutelyContinuous.ae_le hmainscore
      exact ae_of_ae_map measurable_snd.aemeasurable hmaps
    have hwscore : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
        ∀ i, q (w.1.2 i) ∈ scoreInterval := by
      unfold latentTwoWaveLaw
      have hmaps : ∀ᵐ z ∂Measure.map Prod.fst
          (((Measure.pi (fun _ : Fin m => pilotUnitLaw P)).prod
            (Measure.pi fun _ : Fin N => P)).prod randomizerLaw),
          ∀ i, q (z.2 i) ∈ scoreInterval :=
        (Measure.quasiMeasurePreserving_fst (μ :=
          (Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
            (Measure.pi fun _ : Fin N => P)) (ν := randomizerLaw)).absolutelyContinuous.ae_le
          hmidscore
      exact ae_of_ae_map measurable_fst.aemeasurable hmaps
    have hI : Integrable
        (fun w : WaveInput m N d =>
          pairLoss g (fun i => (w.1.2 i).1) (D (designInput w)) / (N : ℝ))
        (latentTwoWaveLaw (m := m) (N := N) P) := by
      apply Integrable.of_mem_Icc 0 (1 / 8 : ℝ) hPairAE
      filter_upwards [hwscore] with w hw
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hterm (i : Fin N) :
          (g (w.1.2 i).1 - g (w.1.2 ((D (designInput w)).val i)).1) ^ 2 ≤
            (1 / 4 : ℝ) := by
        have hi := hw i
        have hj := hw ((D (designInput w)).val i)
        dsimp [q, scoreInterval] at hi hj
        rcases hi with ⟨hi0, hi1⟩
        rcases hj with ⟨hj0, hj1⟩
        nlinarith [sq_nonneg
          (g (w.1.2 i).1 - g (w.1.2 ((D (designInput w)).val i)).1)]
      have hsum : (∑ i : Fin N,
          (g (w.1.2 i).1 - g (w.1.2 ((D (designInput w)).val i)).1) ^ 2) ≤
          (N : ℝ) / 4 := by
        calc
          _ ≤ ∑ _i : Fin N, (1 / 4 : ℝ) :=
            Finset.sum_le_sum (fun i _ => hterm i)
          _ = (N : ℝ) / 4 := by simp; ring
      constructor
      · unfold pairLoss
        positivity
      · apply (div_le_iff₀ hNpos).2
        unfold pairLoss
        nlinarith
    unfold risk
    apply integral_mono_of_nonneg
    · filter_upwards [] with w
      unfold pairLoss
      positivity
    · exact hI
    · filter_upwards [] with w
      exact div_le_div_of_nonneg_right (hpoint w) (by exact_mod_cast (show 0 ≤ N by omega))
  exact ⟨hpoint, hlower.trans hrisk, hrisk⟩

-- @node: lem:oracle-spacing
lemma oracle_spacing (hclass_nonempty :
    ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
      RegularScoreModel P g L β cX CX cg Cg)
    (hpars : ValidClassParameters d β L cX CX cg Cg) :
    ∃ c C : ℝ, c = 1 / (3 * Cg ^ 2) ∧ C = 1 / (cg ^ 2) ∧
      0 < c ∧ c < C ∧
      (∀ N : ℕ, ∀ hN : Even N, ∀ hN2 : 2 ≤ N,
        (∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
          RegularScoreModel P g L β cX CX cg Cg ∧
          c * (N : ℝ) ^ (-2 : ℝ) ≤
            oracleLoss P g N (fun x => oracleMatching g x hN hN2)) ∧
        (∀ P : Measure (UnitRecord d), ∀ g : XSpace d → ℝ,
          RegularScoreModel P g L β cX CX cg Cg →
          oracleLoss P g N (fun x => oracleMatching g x hN hN2) ≤
            C * (N : ℝ) ^ (-2 : ℝ)) ∧
        (∀ m : ℕ, ∀ D : Design m N d, MatchingDesignClass D →
          ∀ P : Measure (UnitRecord d), ∀ g : XSpace d → ℝ,
            RegularScoreModel P g L β cX CX cg Cg →
              oracleLoss P g N (fun x => oracleMatching g x hN hN2) ≤
                risk P g D)) := by
  rcases hclass_nonempty with ⟨P₀, g₀, hmodel₀⟩
  refine ⟨1 / (3 * Cg ^ 2), 1 / cg ^ 2, rfl, rfl, ?_, ?_, ?_⟩
  · rcases hpars with ⟨_, _, _, _, _, _, _, hcg, _, hCg⟩
    positivity
  · rcases hpars with ⟨_, _, _, _, _, _, _, hcg, hcg2, hCg⟩
    have : cg < Cg := by linarith
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [sq_nonneg cg, sq_nonneg Cg]
  · intro N hN hN2
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hA : (0 : ℝ) < Cg := by
      rcases hpars with ⟨_, _, _, _, _, _, _, _, _, hCg⟩
      linarith
    have ha : (0 : ℝ) < cg := by
      rcases hpars with ⟨_, _, _, _, _, _, _, hcg, _, _⟩
      exact hcg
    have hpow : (N : ℝ) ^ (-2 : ℝ) = 1 / (N : ℝ) ^ 2 := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (by positivity)]
      simp [one_div]
    have hden : (N : ℝ) ^ 2 ≤ ((N : ℝ) + 1) * ((N : ℝ) + 2) := by nlinarith
    have hden' : ((N : ℝ) + 1) * ((N : ℝ) + 2) ≤ 3 * (N : ℝ) ^ 2 := by
      have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
      nlinarith [sq_nonneg ((N : ℝ) - 2)]
    have hpoint (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
        (hm : RegularScoreModel P g L β cX CX cg Cg) :=
      pointwise_oracle_spacing P g hm hm.half_sum_version hpars hN hN2
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨P₀, g₀, hmodel₀, ?_⟩
      have h := (hpoint P₀ g₀ hmodel₀).1
      rw [hpow]
      apply le_trans ?_ h
      have hb : 1 / (3 * Cg ^ 2 * (N : ℝ) ^ 2) ≤
          1 / (Cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith [mul_le_mul_of_nonneg_left hden' (sq_nonneg Cg)]
      simpa only [one_div, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hb
    · intro P g hm
      have h := (hpoint P g hm).2.1
      rw [hpow]
      apply le_trans h
      have hb : 1 / (cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) ≤
          1 / (cg ^ 2 * (N : ℝ) ^ 2) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith [mul_le_mul_of_nonneg_left hden (sq_nonneg cg)]
      simpa only [one_div, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hb
    · intro m D hD P g hm
      have h := (hpoint P g hm).2.2 m D hD
      exact h.2.2


end CausalSmith.Experimentation.PilotscorePairingFrontier

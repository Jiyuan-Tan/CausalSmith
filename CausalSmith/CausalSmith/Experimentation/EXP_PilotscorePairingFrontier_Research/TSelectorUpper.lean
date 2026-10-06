module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers

/-! # Uniform upper bound for the rate selector -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

-- @node: geometric_risk_bound_high_dim
lemma geometric_risk_bound_high_dim (d m N : ℕ) (β L cX CX cg Cg : ℝ)
    (hd : 2 ≤ d) (hN : Even N) (hN2 : 2 ≤ N)
    (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (hmodel : RegularScoreModel P g L β cX CX cg Cg) :
    risk P g (fun input : PilotSample m d × MainCovariates N d × ℝ =>
      geometricMatching input.2.1 hN hN2) ≤
      (L ^ 2 / 2 * (32 * (d : ℝ)) ^ β) *
        (N : ℝ) ^ (-2 * β / d) := by
  have hL : 0 ≤ L := hmodel.parameters.2.2.2.1.le
  have hβ0 : 0 < β := hmodel.parameters.2.1
  have hβ1 : β ≤ 1 := hmodel.parameters.2.2.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdom := latentTwoWaveLaw_designDomain_ae (m := m) (N := N) P g hmodel
  let B : ℝ := L ^ 2 * ((1 / 2 : ℝ) * (32 * (d : ℝ)) ^ β *
    (N : ℝ) ^ (1 - 2 * β / d)) / (N : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      pairLoss g (fun i => (w.1.2 i).1)
          (geometricMatching (fun i => (w.1.2 i).1) hN hN2) / (N : ℝ) ≤ B := by
    filter_upwards [hdom] with w hw
    have hcost := geometric_pairLoss_holder_rate hd hN hN2 g L β hL hβ0 hβ1
      hmodel.holder_score (fun i => (w.1.2 i).1) hw.2.1
    exact (div_le_div_iff_of_pos_right hNpos).2 hcost
  have hnonneg : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      0 ≤ pairLoss g (fun i => (w.1.2 i).1)
          (geometricMatching (fun i => (w.1.2 i).1) hN hN2) / (N : ℝ) := by
    filter_upwards [] with w
    unfold pairLoss
    positivity
  letI : IsProbabilityMeasure P := hmodel.covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    pilotUnitLaw_probability P hmodel.covariate_density.1
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  letI : IsProbabilityMeasure (latentTwoWaveLaw (m := m) (N := N) P) := by
    unfold latentTwoWaveLaw
    infer_instance
  unfold risk
  change (∫ w, pairLoss g (fun i => (w.1.2 i).1)
    (geometricMatching (fun i => (w.1.2 i).1) hN hN2) / (N : ℝ)
      ∂latentTwoWaveLaw (m := m) (N := N) P) ≤ _
  have hrisk := integral_mono_of_nonneg hnonneg (integrable_const B) hbound
  have hformula : B =
      (L ^ 2 / 2 * (32 * (d : ℝ)) ^ β) *
        (N : ℝ) ^ (-2 * β / d) := by
    calc
      B = (L ^ 2 / 2 * (32 * (d : ℝ)) ^ β) *
          ((N : ℝ) ^ (1 - 2 * β / d) * (N : ℝ) ^ (-1 : ℝ)) := by
            dsimp [B]
            rw [div_eq_mul_inv, ← Real.rpow_neg_one]
            ring
      _ = _ := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  simpa [hformula] using hrisk

private lemma euclideanDistance_sq_one (x y : XSpace 1) :
    (euclideanDistance x y) ^ 2 = (x 0 - y 0) ^ 2 := by
  unfold euclideanDistance
  rw [Real.sq_sqrt]
  · simp
  · positivity

private lemma geometricCost_eq_coordinate_pairLoss (N : ℕ)
    (x : MainCovariates N 1) (M : Match N) :
    geometricCost x M = pairLoss (fun z : XSpace 1 => z 0) x M := by
  unfold geometricCost pairLoss
  simp_rw [euclideanDistance_sq_one]

/-- In one dimension, geometric optimality transfers the Lipschitz score loss to
the adjacent-coordinate matching.  The remaining probabilistic input for the
sharp endpoint is a spacing bound for the one-dimensional covariate marginal. -/
private lemma geometric_pairLoss_one_le_coordinate_oracle (N : ℕ)
    (hN : Even N) (hN2 : 2 ≤ N) (g : XSpace 1 → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hg : HolderScore g L 1) (x : MainCovariates N 1)
    (hx : ∀ i, x i ∈ cube 1) :
    pairLoss g x (geometricMatching x hN hN2) ≤
      L ^ 2 * pairLoss (fun z : XSpace 1 => z 0) x
        (oracleMatching (fun z : XSpace 1 => z 0) x hN hN2) := by
  have hscore := holder_pairLoss_le_geometricCost_lipschitz
    g L hL hg x hx (geometricMatching x hN hN2)
  have hoptimal :
      geometricCost x (geometricMatching x hN hN2) ≤
        geometricCost x
          (oracleMatching (fun z : XSpace 1 => z 0) x hN hN2) :=
    (Classical.choose_spec (exists_geometricMatching x hN hN2) _).1
  have hoptimal' :
      geometricCost x (geometricMatching x hN hN2) ≤
        pairLoss (fun z : XSpace 1 => z 0) x
          (oracleMatching (fun z : XSpace 1 => z 0) x hN hN2) := by
    calc
      _ ≤ geometricCost x
          (oracleMatching (fun z : XSpace 1 => z 0) x hN hN2) := hoptimal
      _ = _ := geometricCost_eq_coordinate_pairLoss _ _ _
  exact hscore.trans (mul_le_mul_of_nonneg_left hoptimal' (sq_nonneg L))

private lemma geometric_risk_bound_one_dim (m N : ℕ) (β L cX CX cg Cg : ℝ)
    (hpars : ValidClassParameters 1 β L cX CX cg Cg)
    (hN : Even N) (hN2 : 2 ≤ N) (P : Measure (UnitRecord 1))
    (g : XSpace 1 → ℝ) (hmodel : RegularScoreModel P g L β cX CX cg Cg) :
    risk P g (fun input : PilotSample m 1 × MainCovariates N 1 × ℝ =>
      geometricMatching input.2.1 hN hN2) ≤
      (L ^ 2 / 2) * 2 ^ β * (1 / cX ^ 2) ^ β *
        (N : ℝ) ^ (-2 * β) := by
  let coord : XSpace 1 → ℝ := fun x => x 0
  let A : MainSample N 1 → ℝ := fun us =>
    pairLoss coord (fun i => (us i).1)
      (oracleMatching coord (fun i => (us i).1) hN hN2) / (N : ℝ)
  let G : MainSample N 1 → ℝ := fun us =>
    pairLoss g (fun i => (us i).1)
      (geometricMatching (fun i => (us i).1) hN hN2) / (N : ℝ)
  have hβ0 : 0 < β := hpars.2.1
  have hβ1 : β ≤ 1 := hpars.2.2.1
  have hL : 0 ≤ L := hpars.2.2.2.1.le
  have hcX : 0 < cX := hpars.2.2.2.2.1
  have hCX : cX ≤ CX := hpars.2.2.2.2.2.1.trans hpars.2.2.2.2.2.2.1
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  letI : IsProbabilityMeasure P := hmodel.covariate_density.1
  letI : IsProbabilityMeasure (Measure.pi fun _ : Fin N => P) := inferInstance
  have hAi : Integrable A (Measure.pi fun _ : Fin N => P) := by
    exact integrable_coordinate_oracle_loss_one_dim hN hN2 P hmodel.covariate_density
  have hAnonneg : ∀ us, 0 ≤ A us := by
    intro us
    dsimp [A]
    unfold pairLoss
    positivity
  have hApi : Integrable (fun us => (A us) ^ β) (Measure.pi fun _ : Fin N => P) := by
    have hmeas := (Real.continuous_rpow_const hβ0.le).aestronglyMeasurable.comp_aemeasurable
      hAi.aestronglyMeasurable.aemeasurable
    apply Integrable.mono' ((integrable_const 1).add hAi) hmeas
    filter_upwards [] with us
    change |A us ^ β| ≤ 1 + A us
    rw [abs_of_nonneg (Real.rpow_nonneg (hAnonneg us) β)]
    by_cases hA : A us ≤ 1
    · exact (Real.rpow_le_one (hAnonneg us) hA hβ0.le).trans (by linarith [hAnonneg us])
    · have hA1 : 1 ≤ A us := le_of_not_ge hA
      exact le_trans (Real.rpow_le_self_of_one_le hA1 hβ1) (le_add_of_nonneg_left zero_le_one)
  have hjensen : (∫ us, (A us) ^ β ∂Measure.pi fun _ : Fin N => P) ≤
      (∫ us, A us ∂Measure.pi fun _ : Fin N => P) ^ β := by
    exact (Real.concaveOn_rpow hβ0.le hβ1).le_map_integral
      (Real.continuous_rpow_const hβ0.le).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall hAnonneg) hAi hApi
  have hcube : ∀ᵐ u ∂P, u.1 ∈ cube 1 := by
    have hcube_meas : MeasurableSet (cube 1) := by unfold cube; measurability
    have hxmap : cube 1 ∈ ae (P.map Prod.fst) := by
      rw [mem_ae_iff]
      apply hmodel.covariate_density.2.1
      simp [cubeMeasure, hcube_meas]
    exact ae_of_ae_map measurable_fst.aemeasurable hxmap
  have hcubes : ∀ᵐ us ∂Measure.pi (fun _ : Fin N => P),
      ∀ i, (us i).1 ∈ cube 1 := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hcube
  have hpoint : G ≤ᵐ[Measure.pi fun _ : Fin N => P]
      fun us => (L ^ 2 / 2) * (2 * A us) ^ β := by
    filter_upwards [hcubes] with us hus
    let x : MainCovariates N 1 := fun i => (us i).1
    let M := geometricMatching x hN hN2
    have hp := holder_pairLoss_le_geometricCost_rpow (by omega) g L β hL hβ0 hβ1
      hmodel.holder_score x hus M
    have hopt : geometricCost x M ≤
        geometricCost x (oracleMatching coord x hN hN2) :=
      (Classical.choose_spec (exists_geometricMatching x hN hN2) _).1
    have hpow : (2 * geometricCost x M) ^ β ≤
        (2 * pairLoss coord x (oracleMatching coord x hN hN2)) ^ β := by
      apply Real.rpow_le_rpow
      · exact mul_nonneg (by norm_num) (by unfold geometricCost; positivity)
      · simpa [coord, geometricCost_eq_coordinate_pairLoss] using
          mul_le_mul_of_nonneg_left hopt (by norm_num : (0 : ℝ) ≤ 2)
      · exact hβ0.le
    have hp' := hp.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpow (by positivity)) (sq_nonneg L))
    dsimp [G, A, x, M, coord]
    calc
      _ ≤ (L ^ 2 * ((1 / 2 : ℝ) * (N : ℝ) ^ (1 - β) *
          (2 * pairLoss (fun z : XSpace 1 => z 0) (fun i => (us i).1)
            (oracleMatching (fun z : XSpace 1 => z 0) (fun i => (us i).1) hN hN2)) ^ β)) /
            (N : ℝ) := (div_le_div_iff_of_pos_right hNr).2 hp'
      _ = (L ^ 2 / 2) *
          (2 * (pairLoss (fun z : XSpace 1 => z 0) (fun i => (us i).1)
            (oracleMatching (fun z : XSpace 1 => z 0) (fun i => (us i).1) hN hN2) /
              (N : ℝ))) ^ β := by
        have hC : 0 ≤ pairLoss (fun z : XSpace 1 => z 0) (fun i => (us i).1)
            (oracleMatching (fun z : XSpace 1 => z 0) (fun i => (us i).1) hN hN2) := by
          unfold pairLoss
          positivity
        have hNpow : (N : ℝ) ^ (1 - β) / (N : ℝ) = 1 / (N : ℝ) ^ β := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hNr]
          have hexp : 1 - β + (-1 : ℝ) = -β := by ring
          rw [hexp, Real.rpow_neg hNr.le, one_div]
        calc
          _ = (L ^ 2 / 2) * ((N : ℝ) ^ (1 - β) / (N : ℝ)) *
              (2 * pairLoss (fun z : XSpace 1 => z 0) (fun i => (us i).1)
                (oracleMatching (fun z : XSpace 1 => z 0)
                  (fun i => (us i).1) hN hN2)) ^ β := by ring
          _ = (L ^ 2 / 2) * (1 / (N : ℝ) ^ β) *
              (2 * pairLoss (fun z : XSpace 1 => z 0) (fun i => (us i).1)
                (oracleMatching (fun z : XSpace 1 => z 0)
                  (fun i => (us i).1) hN hN2)) ^ β := by rw [hNpow]
          _ = _ := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hC]
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (div_nonneg hC hNr.le),
              Real.div_rpow hC hNr.le]
            ring
  have hupperi : Integrable (fun us => (L ^ 2 / 2) * (2 * A us) ^ β)
      (Measure.pi fun _ : Fin N => P) := by
    have htwo : Integrable (fun us => (2 * A us) ^ β)
        (Measure.pi fun _ : Fin N => P) := by
      have heq : (fun us => (2 * A us) ^ β) = fun us => 2 ^ β * (A us) ^ β := by
        funext us
        rw [Real.mul_rpow (by norm_num) (hAnonneg us)]
      rw [heq]
      exact hApi.const_mul _
    exact htwo.const_mul _
  have hGnonneg : 0 ≤ᵐ[Measure.pi fun _ : Fin N => P] G := by
    filter_upwards [] with us
    dsimp [G]
    unfold pairLoss
    positivity
  have hmain : (∫ us, G us ∂Measure.pi fun _ : Fin N => P) ≤
      (L ^ 2 / 2) * 2 ^ β * (1 / cX ^ 2) ^ β *
        (N : ℝ) ^ (-2 * β) := by
    have hmono := integral_mono_of_nonneg hGnonneg hupperi hpoint
    have hspacing := (coordinate_oracle_spacing_bound_one_dim hN hN2 P
      hmodel.covariate_density hcX hCX).2
    have hAint : (∫ us, A us ∂Measure.pi fun _ : Fin N => P) =
        oracleLoss P coord N (fun x => oracleMatching coord x hN hN2) := rfl
    have hAupper : (∫ us, A us ∂Measure.pi fun _ : Fin N => P) ≤
        1 / (cX ^ 2 * (N : ℝ) ^ 2) := by
      rw [hAint]
      calc
        _ ≤ 1 / (cX ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := hspacing
        _ ≤ 1 / (cX ^ 2 * (N : ℝ) ^ 2) := by
          apply one_div_le_one_div_of_le
          · positivity
          · nlinarith [sq_pos_of_pos hcX, hNr]
    calc
      _ ≤ ∫ us, (L ^ 2 / 2) * (2 * A us) ^ β
          ∂Measure.pi fun _ : Fin N => P := hmono
      _ = (L ^ 2 / 2) * 2 ^ β *
          (∫ us, (A us) ^ β ∂Measure.pi fun _ : Fin N => P) := by
        rw [integral_const_mul]
        simp_rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (hAnonneg _)]
        rw [integral_const_mul]
        ring
      _ ≤ (L ^ 2 / 2) * 2 ^ β *
          (∫ us, A us ∂Measure.pi fun _ : Fin N => P) ^ β := by
        gcongr
      _ ≤ (L ^ 2 / 2) * 2 ^ β * (1 / (cX ^ 2 * (N : ℝ) ^ 2)) ^ β := by
        gcongr
        exact integral_nonneg_of_ae (Filter.Eventually.of_forall hAnonneg)
      _ = _ := by
        have hsplit : 1 / (cX ^ 2 * (N : ℝ) ^ 2) =
            (1 / cX ^ 2) * (1 / (N : ℝ) ^ 2) := by
          field_simp [hcX.ne', hNr.ne']
        have hNinv : (1 / (N : ℝ) ^ 2) ^ β =
            (N : ℝ) ^ (-2 * β) := by
          rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg hNr.le,
            ← Real.rpow_mul hNr.le]
          congr 1
        rw [hsplit, Real.mul_rpow (by positivity) (by positivity), hNinv]
        ring
  have heq := oracleLoss_eq_latent_integral (m := m) (N := N) P g
    (fun x => geometricMatching x hN hN2) hmodel.covariate_density.1
    (by letI : IsProbabilityMeasure P := hmodel.covariate_density.1
        letI : IsProbabilityMeasure (pilotUnitLaw P) :=
          pilotUnitLaw_probability P hmodel.covariate_density.1
        infer_instance)
    randomizerLaw_probability
  unfold risk
  change (∫ w, pairLoss g (fun i => (w.1.2 i).1)
      (geometricMatching (fun i => (w.1.2 i).1) hN hN2) / (N : ℝ)
        ∂latentTwoWaveLaw (m := m) (N := N) P) ≤ _
  rw [← heq]
  change (∫ us, G us ∂Measure.pi fun _ : Fin N => P) ≤ _
  exact hmain

private lemma plugIn_pairLoss_bound (d m N : ℕ) (β : ℝ)
    (hN : Even N) (hN2 : 2 ≤ N) (g : XSpace d → ℝ)
    (pilot : PilotSample m d) (x : MainCovariates N d) :
    pairLoss g x (plugInMatching β pilot x hN hN2) ≤
      4 * pairLoss g x (oracleMatching g x hN hN2) +
        12 * ∑ i : Fin N, (g (x i) - histogramScore β pilot (x i)) ^ 2 := by
  simpa [plugInMatching, oracleMatching] using
    adjacent_matching_stability hN hN2 g (histogramScore β pilot) x

private lemma latent_iid_average_integral (d m N : ℕ) (hNpos : 0 < N)
    (P : Measure (UnitRecord d))
    (F : PilotSample m d → UnitRecord d → ℝ)
    (hP : IsProbabilityMeasure P)
    (hpilot : IsProbabilityMeasure (pilotUnitLaw P))
    (hrandomizer : IsProbabilityMeasure randomizerLaw)
    (hF : Integrable (Function.uncurry F)
      ((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod P)) :
    (∫ w, (∑ i : Fin N, F w.1.1 (w.1.2 i)) / (N : ℝ)
      ∂latentTwoWaveLaw (m := m) (N := N) P) =
      ∫ pilot, ∫ u, F pilot u ∂P
        ∂(Measure.pi fun _ : Fin m => pilotUnitLaw P) := by
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure (pilotUnitLaw P) := hpilot
  letI : IsProbabilityMeasure randomizerLaw := hrandomizer
  let μp := Measure.pi fun _ : Fin m => pilotUnitLaw P
  let μN := Measure.pi fun _ : Fin N => P
  let μmid := μp.prod μN
  have heval (i : Fin N) : Measure.map (Function.eval i) μN = P := by
    dsimp [μN]
    rw [Measure.pi_map_eval]
    simp
  have hmap (i : Fin N) :
      Measure.map (fun z : PilotSample m d × MainSample N d => (z.1, z.2 i)) μmid =
        μp.prod P := by
    have h := Measure.map_prod_map μp μN measurable_id (measurable_pi_apply i)
    rw [Measure.map_id, heval i] at h
    change Measure.map (Prod.map id (Function.eval i)) μmid = μp.prod P
    simpa [μmid] using h.symm
  have hcoord_int (i : Fin N) :
      (∫ z, F z.1 (z.2 i) ∂μmid) =
        ∫ q, Function.uncurry F q ∂μp.prod P := by
    let T : PilotSample m d × MainSample N d → PilotSample m d × UnitRecord d :=
      fun z => (z.1, z.2 i)
    have hT : Measurable T :=
      measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
    have hFmap : Integrable (Function.uncurry F) (Measure.map T μmid) := by
      rw [show Measure.map T μmid = μp.prod P from hmap i]
      exact hF
    calc
      (∫ z, F z.1 (z.2 i) ∂μmid) =
          ∫ q, Function.uncurry F q ∂Measure.map T μmid := by
            simpa [T, Function.uncurry] using
              (integral_map hT.aemeasurable hFmap.aestronglyMeasurable).symm
      _ = _ := by rw [show Measure.map T μmid = μp.prod P from hmap i]
  have hcoord_intg (i : Fin N) : Integrable (fun z => F z.1 (z.2 i)) μmid := by
    have hF' : Integrable (Function.uncurry F)
        (Measure.map (fun z : PilotSample m d × MainSample N d => (z.1, z.2 i)) μmid) := by
      rw [hmap i]
      exact hF
    exact hF'.comp_aemeasurable
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)).aemeasurable
  have hsum : Integrable (fun z : PilotSample m d × MainSample N d =>
      ∑ i : Fin N, F z.1 (z.2 i)) μmid := by
    apply integrable_finset_sum Finset.univ
    intro i hi
    exact hcoord_intg i
  let G : PilotSample m d × MainSample N d → ℝ := fun z =>
    (∑ i : Fin N, F z.1 (z.2 i)) / (N : ℝ)
  have hG : Integrable G μmid := hsum.div_const _
  change (∫ w, G w.1 ∂μmid.prod randomizerLaw) = _
  rw [integral_fun_fst G]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  dsimp [G]
  rw [integral_div, integral_finset_sum Finset.univ (fun i _ => hcoord_intg i)]
  simp_rw [hcoord_int]
  rw [integral_prod (Function.uncurry F) hF]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  field_simp
  rfl

private lemma histogram_error_average_integral (d m N : ℕ)
    (beta L cX CX cg Cg : ℝ)
    (hbeta : 0 < beta) (hm : 1 ≤ m) (hN2 : 2 ≤ N)
    (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (hmodel : RegularScoreModel P g L beta cX CX cg Cg) :
    (∫ w, (∑ i : Fin N,
        (g (w.1.2 i).1 - histogramScore beta w.1.1 (w.1.2 i).1) ^ 2) / (N : ℝ)
      ∂latentTwoWaveLaw (m := m) (N := N) P) =
      ∫ pilot, ∫ u, (histogramScore beta pilot u.1 - g u.1) ^ 2 ∂P
        ∂(Measure.pi fun _ : Fin m => pilotUnitLaw P) := by
  have hF := integrable_histogramScore_sq_error m d beta hbeta hm P g hmodel
  have htransfer := latent_iid_average_integral d m N (by omega) P
    (fun pilot u => (g u.1 - histogramScore beta pilot u.1) ^ 2)
    hmodel.covariate_density.1
    (histogram_pilotUnitLaw_probability P hmodel.covariate_density.1)
    randomizerLaw_probability hF
  rw [htransfer]
  apply integral_congr_ae
  filter_upwards [] with pilot
  apply integral_congr_ae
  filter_upwards [] with u
  ring

private lemma integrable_histogram_error_average (d m N : ℕ)
    (beta L cX CX cg Cg : ℝ) (hbeta : 0 < beta) (hm : 1 ≤ m)
    (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (hmodel : RegularScoreModel P g L beta cX CX cg Cg) :
    Integrable (fun w : WaveInput m N d =>
      (∑ i : Fin N,
        (g (w.1.2 i).1 - histogramScore beta w.1.1 (w.1.2 i).1) ^ 2) / (N : ℝ))
      (latentTwoWaveLaw (m := m) (N := N) P) := by
  letI : IsProbabilityMeasure P := hmodel.covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    histogram_pilotUnitLaw_probability P hmodel.covariate_density.1
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  let μp := Measure.pi fun _ : Fin m => pilotUnitLaw P
  let μN := Measure.pi fun _ : Fin N => P
  let μmid := μp.prod μN
  let F : PilotSample m d → UnitRecord d → ℝ := fun pilot u =>
    (g u.1 - histogramScore beta pilot u.1) ^ 2
  have hF : Integrable (Function.uncurry F) (μp.prod P) := by
    exact integrable_histogramScore_sq_error m d beta hbeta hm P g hmodel
  have heval (i : Fin N) : Measure.map (Function.eval i) μN = P := by
    dsimp [μN]
    rw [Measure.pi_map_eval]
    simp
  have hcoord (i : Fin N) : Integrable (fun z => F z.1 (z.2 i)) μmid := by
    let T : PilotSample m d × MainSample N d → PilotSample m d × UnitRecord d :=
      fun z => (z.1, z.2 i)
    have hmap : Measure.map T μmid = μp.prod P := by
      have h := Measure.map_prod_map μp μN measurable_id (measurable_pi_apply i)
      rw [Measure.map_id, heval i] at h
      change Measure.map (Prod.map id (Function.eval i)) μmid = μp.prod P
      simpa [T, μmid] using h.symm
    have hF' : Integrable (Function.uncurry F) (Measure.map T μmid) := by
      rw [hmap]
      exact hF
    exact hF'.comp_aemeasurable
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)).aemeasurable
  have hsum : Integrable (fun z : PilotSample m d × MainSample N d =>
      ∑ i : Fin N, F z.1 (z.2 i)) μmid := by
    apply integrable_finset_sum Finset.univ
    intro i hi
    exact hcoord i
  exact (hsum.div_const (N : ℝ)).comp_fst randomizerLaw

private lemma integrable_oracle_loss_integrand (d m N : ℕ)
    (β L cX CX cg Cg : ℝ) (hpars : ValidClassParameters d β L cX CX cg Cg)
    (hN : Even N) (hN2 : 2 ≤ N) (P : Measure (UnitRecord d))
    (g : XSpace d → ℝ) (hmodel : RegularScoreModel P g L β cX CX cg Cg) :
    Integrable (fun w : WaveInput m N d =>
      pairLoss g (fun i => (w.1.2 i).1)
        (oracleMatching g (fun i => (w.1.2 i).1) hN hN2) / (N : ℝ))
      (latentTwoWaveLaw (m := m) (N := N) P) := by
  letI : IsProbabilityMeasure P := hmodel.covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    pilotUnitLaw_probability P hmodel.covariate_density.1
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  let O : WaveInput m N d → ℝ := fun w =>
    pairLoss g (fun i => (w.1.2 i).1)
      (oracleMatching g (fun i => (w.1.2 i).1) hN hN2) / (N : ℝ)
  have heq : oracleLoss P g N (fun x => oracleMatching g x hN hN2) =
      ∫ w, O w ∂latentTwoWaveLaw (m := m) (N := N) P :=
    oracleLoss_eq_latent_integral P g (fun x => oracleMatching g x hN hN2)
      hmodel.covariate_density.1 inferInstance randomizerLaw_probability
  have hlo := (pointwise_oracle_spacing P g hmodel hmodel.half_sum_version
    hpars hN hN2).1
  have hCg : 0 < Cg := by
    rcases hpars with ⟨_, _, _, _, _, _, _, _, _, hCg⟩
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlowerpos : 0 < 1 / (Cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
    positivity
  have hintpos : 0 < ∫ w, O w ∂latentTwoWaveLaw (m := m) (N := N) P := by
    rw [← heq]
    exact lt_of_lt_of_le hlowerpos hlo
  by_contra hnot
  rw [integral_undef hnot] at hintpos
  linarith

private lemma plugIn_risk_bound_of_histogram (d m N : ℕ) (β L cX CX cg Cg Ch : ℝ)
    (hpars : ValidClassParameters d β L cX CX cg Cg) (hm : 1 ≤ m)
    (hN : Even N) (hN2 : 2 ≤ N) (P : Measure (UnitRecord d))
    (g : XSpace d → ℝ) (hmodel : RegularScoreModel P g L β cX CX cg Cg)
    (hhist : ∀ m : ℕ, 1 ≤ m → ∀ P : Measure (UnitRecord d), ∀ g : XSpace d → ℝ,
      RegularScoreModel P g L β cX CX cg Cg →
        (∫ pilot, ∫ u, (histogramScore β pilot u.1 - g u.1) ^ 2 ∂P
          ∂(Measure.pi fun _ : Fin m => pilotUnitLaw P)) ≤
            Ch * (m : ℝ) ^ (-2 * β / (2 * β + d))) :
      risk P g (fun input : PilotSample m d × MainCovariates N d × ℝ =>
        plugInMatching β input.1 input.2.1 hN hN2) ≤
        4 / (cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) +
          12 * Ch * (m : ℝ) ^ (-2 * β / (2 * β + d)) := by
  let O : WaveInput m N d → ℝ := fun w =>
    pairLoss g (fun i => (w.1.2 i).1)
      (oracleMatching g (fun i => (w.1.2 i).1) hN hN2) / (N : ℝ)
  let E : WaveInput m N d → ℝ := fun w =>
    (∑ i : Fin N,
      (g (w.1.2 i).1 - histogramScore β w.1.1 (w.1.2 i).1) ^ 2) / (N : ℝ)
  let Q : WaveInput m N d → ℝ := fun w =>
    pairLoss g (fun i => (w.1.2 i).1)
      (plugInMatching β w.1.1 (fun i => (w.1.2 i).1) hN hN2) / (N : ℝ)
  have hOi : Integrable O (latentTwoWaveLaw (m := m) (N := N) P) :=
    integrable_oracle_loss_integrand d m N β L cX CX cg Cg hpars hN hN2 P g hmodel
  have hEi : Integrable E (latentTwoWaveLaw (m := m) (N := N) P) :=
    integrable_histogram_error_average d m N β L cX CX cg Cg hpars.2.1 hm P g hmodel
  have hupper : Integrable (fun w => 4 * O w + 12 * E w)
      (latentTwoWaveLaw (m := m) (N := N) P) :=
    hOi.const_mul 4 |>.add (hEi.const_mul 12)
  have hQnonneg : 0 ≤ᵐ[latentTwoWaveLaw (m := m) (N := N) P] Q := by
    filter_upwards [] with w
    dsimp [Q]
    unfold pairLoss
    positivity
  have hpoint : Q ≤ᵐ[latentTwoWaveLaw (m := m) (N := N) P]
      fun w => 4 * O w + 12 * E w := by
    filter_upwards [] with w
    have hp := plugIn_pairLoss_bound d m N β hN hN2 g w.1.1
      (fun i => (w.1.2 i).1)
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    dsimp [Q, O, E]
    calc
      _ ≤ (4 * pairLoss g (fun i => (w.1.2 i).1)
              (oracleMatching g (fun i => (w.1.2 i).1) hN hN2) +
            12 * ∑ i : Fin N,
              (g (w.1.2 i).1 - histogramScore β w.1.1 (w.1.2 i).1) ^ 2) /
            (N : ℝ) := (div_le_div_iff_of_pos_right hNr).2 hp
      _ = _ := by ring
  have hmono : (∫ w, Q w ∂latentTwoWaveLaw (m := m) (N := N) P) ≤
      ∫ w, (4 * O w + 12 * E w)
        ∂latentTwoWaveLaw (m := m) (N := N) P :=
    integral_mono_of_nonneg hQnonneg hupper hpoint
  have hOeq : (∫ w, O w ∂latentTwoWaveLaw (m := m) (N := N) P) =
      oracleLoss P g N (fun x => oracleMatching g x hN hN2) := by
    symm
    exact oracleLoss_eq_latent_integral P g (fun x => oracleMatching g x hN hN2)
      hmodel.covariate_density.1
      (by letI : IsProbabilityMeasure P := hmodel.covariate_density.1
          letI : IsProbabilityMeasure (pilotUnitLaw P) :=
            pilotUnitLaw_probability P hmodel.covariate_density.1
          infer_instance)
      randomizerLaw_probability
  have hEeq : (∫ w, E w ∂latentTwoWaveLaw (m := m) (N := N) P) =
      ∫ pilot, ∫ u, (histogramScore β pilot u.1 - g u.1) ^ 2 ∂P
        ∂(Measure.pi fun _ : Fin m => pilotUnitLaw P) := by
    exact histogram_error_average_integral d m N β L cX CX cg Cg hpars.2.1 hm hN2 P g hmodel
  have horacle := (pointwise_oracle_spacing P g hmodel hmodel.half_sum_version
    hpars hN hN2).2.1
  unfold risk
  change (∫ w, Q w ∂latentTwoWaveLaw (m := m) (N := N) P) ≤ _
  calc
    _ ≤ ∫ w, (4 * O w + 12 * E w)
        ∂latentTwoWaveLaw (m := m) (N := N) P := hmono
    _ = 4 * (∫ w, O w ∂latentTwoWaveLaw (m := m) (N := N) P) +
        12 * (∫ w, E w ∂latentTwoWaveLaw (m := m) (N := N) P) := by
          rw [integral_add (hOi.const_mul 4) (hEi.const_mul 12),
            integral_const_mul, integral_const_mul]
    _ ≤ 4 * (1 / (cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2))) +
        12 * (Ch * (m : ℝ) ^ (-2 * β / (2 * β + d))) := by
          rw [hOeq, hEeq]
          gcongr
          exact hhist m hm P g hmodel
    _ = _ := by ring

private lemma plugIn_risk_bound (d m N : ℕ) (β L cX CX cg Cg : ℝ)
    (hpars : ValidClassParameters d β L cX CX cg Cg) (hm : 1 ≤ m)
    (hN : Even N) (hN2 : 2 ≤ N) (P : Measure (UnitRecord d))
    (g : XSpace d → ℝ) (hmodel : RegularScoreModel P g L β cX CX cg Cg) :
    ∃ Ch : ℝ, 0 < Ch ∧
      risk P g (fun input : PilotSample m d × MainCovariates N d × ℝ =>
        plugInMatching β input.1 input.2.1 hN hN2) ≤
        4 / (cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) +
          12 * Ch * (m : ℝ) ^ (-2 * β / (2 * β + d)) := by
  obtain ⟨Ch, hCh, hhist⟩ := histogram_l2_rate
    (d := d) (β := β) (L := L) (cX := cX) (CX := CX) (cg := cg) (Cg := Cg)
    hpars.1 hpars.2.1 hpars.2.2.1
  refine ⟨Ch, hCh, ?_⟩
  exact plugIn_risk_bound_of_histogram d m N β L cX CX cg Cg Ch
    hpars hm hN hN2 P g hmodel hhist

/-- The plug-in matching is measurable in the pilot sample and main covariates. -/
-- @node: plugInMatching_measurable
lemma plugInMatching_measurable (m d N : ℕ) (β : ℝ)
    (hN : Even N) (hN2 : 2 ≤ N) :
    Measurable (fun z : PilotSample m d × MainCovariates N d =>
      plugInMatching β z.1 z.2 hN hN2) := by
  unfold plugInMatching
  apply adjSortMatching_measurable hN hN2
  intro i
  let T : PilotSample m d × MainCovariates N d → PilotSample m d × XSpace d :=
    fun z => (z.1, z.2 i)
  have hT : Measurable T :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  have h := (histogramScore_measurable m d β).comp hT
  change Measurable ((fun q : PilotSample m d × XSpace d =>
    histogramScore β q.1 q.2) ∘ T)
  exact h

/-- The selector is measurable on its full input space. -/
-- @node: selectorDesign_measurable
lemma selectorDesign_measurable (m d N : ℕ) (β : ℝ)
    (hN : Even N) (hN2 : 2 ≤ N) :
    Measurable (selectorDesign (m := m) (d := d) (N := N) β hN hN2) := by
  unfold selectorDesign
  split
  · exact (geometricMatching_measurable hN hN2).comp
      (measurable_fst.comp measurable_snd)
  · unfold plugInMatching
    apply adjSortMatching_measurable hN hN2
    intro i
    let T : PilotSample m d × MainCovariates N d × ℝ →
        PilotSample m d × XSpace d := fun z => (z.1, z.2.1 i)
    have hT : Measurable T := measurable_fst.prodMk
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
    have h := (histogramScore_measurable m d β).comp hT
    change Measurable ((fun q : PilotSample m d × XSpace d =>
      histogramScore β q.1 q.2) ∘ T)
    exact h

/-- A globally measurable matching rule induces its fair paired randomization law. -/
-- @node: pairedRandomization_of_measurable
lemma pairedRandomization_of_measurable (D : Design m N d)
    (hD : Measurable D) (P : Measure (UnitRecord d)) :
    PairedRandomization P D (fun w => pairedCoinLaw (D (designInput w))) := by
  unfold PairedRandomization
  let f : WaveInput m N d → Match N := fun w => D (designInput w)
  let K : Match N → Measure (Match N × (Fin N → Bool)) :=
    fun M => (pairedCoinLaw M).map (fun z => (M, z))
  have hinput : Measurable (designInput (m := m) (N := N) (d := d)) := by
    unfold designInput
    fun_prop
  have hf : Measurable f := hD.comp hinput
  have hK : Measurable K := measurable_of_finite _
  have hdirac : AEMeasurable (fun w => Measure.dirac (f w))
      (latentTwoWaveLaw (m := m) (N := N) P) :=
    (Measure.measurable_dirac.comp hf).aemeasurable
  change (latentTwoWaveLaw (m := m) (N := N) P).bind (fun w => K (f w)) =
    ((latentTwoWaveLaw (m := m) (N := N) P).map f).bind K
  rw [← Measure.bind_dirac_eq_map _ hf, Measure.bind_bind hdirac hK.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [] with w
  exact (Measure.dirac_bind hK (f w)).symm

/-- The selector belongs to the admissible class of measurable paired designs. -/
-- @node: selectorDesign_matchingDesignClass
lemma selectorDesign_matchingDesignClass (m d N : ℕ) (β : ℝ)
    (hN : Even N) (hN2 : 2 ≤ N) :
    MatchingDesignClass
      (selectorDesign (m := m) (d := d) (N := N) β hN hN2) := by
  refine ⟨⟨hN, hN2⟩, ?_, ?_⟩
  · exact (selectorDesign_measurable m d N β hN hN2).comp measurable_subtype_coe
  · intro P _
    exact pairedRandomization_of_measurable _
      (selectorDesign_measurable m d N β hN hN2) P

-- @node: thm:selector-upper
theorem selector_upper (d : ℕ) (β L cX CX cg Cg : ℝ)
    (hpars : ValidClassParameters d β L cX CX cg Cg) :
    ∃ C : ℝ, 0 < C ∧
      ∀ m N : ℕ, 1 ≤ m → (hN : Even N) → (hN2 : 2 ≤ N) →
        MatchingDesignClass (selectorDesign (d := d) (m := m) (N := N) β hN hN2) ∧
        ∀ P : Measure (UnitRecord d), ∀ g : XSpace d → ℝ,
          RegularScoreModel P g L β cX CX cg Cg →
            risk P g (selectorDesign (d := d) (m := m) (N := N) β hN hN2) ≤
              C * jointFrontier d m N β := by
  obtain ⟨Ch, hCh, hhist⟩ := histogram_l2_rate
    (d := d) (β := β) (L := L) (cX := cX) (CX := CX) (cg := cg) (Cg := Cg)
    hpars.1 hpars.2.1 hpars.2.2.1
  let Kgeo : ℝ := if d = 1 then
      (L ^ 2 / 2) * 2 ^ β * (1 / cX ^ 2) ^ β
    else (L ^ 2 / 2) * (32 * (d : ℝ)) ^ β
  let Kplug : ℝ := 4 / cg ^ 2 + 12 * Ch
  let C : ℝ := Kgeo + Kplug
  have hL : 0 < L := hpars.2.2.2.1
  have hcX : 0 < cX := hpars.2.2.2.2.1
  have hcg : 0 < cg := hpars.2.2.2.2.2.2.2.1
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hpars.1
  have hKgeo : 0 < Kgeo := by
    dsimp [Kgeo]
    split <;> positivity
  have hKplug : 0 < Kplug := by
    dsimp [Kplug]
    positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro m N hm hN hN2
  refine ⟨selectorDesign_matchingDesignClass m d N β hN hN2, ?_⟩
  intro P g hmodel
  let G : ℝ := (N : ℝ) ^ (-2 * β / d)
  let H : ℝ := (m : ℝ) ^ (-2 * β / (2 * β + d))
  let B : ℝ := (N : ℝ) ^ (-2 : ℝ) + H
  have hNnat : 0 < N := by omega
  have hmnat : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hmr : (0 : ℝ) < m := by exact_mod_cast hmnat
  have hG0 : 0 ≤ G := Real.rpow_nonneg hNr.le _
  have hH0 : 0 ≤ H := Real.rpow_nonneg hmr.le _
  have hNrate0 : 0 ≤ (N : ℝ) ^ (-2 : ℝ) := Real.rpow_nonneg hNr.le _
  have hB0 : 0 ≤ B := add_nonneg hNrate0 hH0
  have hgeo : risk P g (fun input : PilotSample m d × MainCovariates N d × ℝ =>
      geometricMatching input.2.1 hN hN2) ≤ Kgeo * G := by
    by_cases hd1 : d = 1
    · subst d
      have h := geometric_risk_bound_one_dim m N β L cX CX cg Cg hpars
        hN hN2 P g hmodel
      simpa [Kgeo, G] using h
    · have hdpos : 1 ≤ d := hpars.1
      have hd : 2 ≤ d := by omega
      have h := geometric_risk_bound_high_dim d m N β L cX CX cg Cg hd
        hN hN2 P g hmodel
      simpa [Kgeo, G, hd1] using h
  have hplugin0 := plugIn_risk_bound_of_histogram d m N β L cX CX cg Cg Ch
    hpars hm hN hN2 P g hmodel hhist
  have horacle_rate :
      4 / (cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) ≤
        (4 / cg ^ 2) * (N : ℝ) ^ (-2 : ℝ) := by
    have hden : cg ^ 2 * (N : ℝ) ^ 2 ≤
        cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2) := by
      nlinarith [sq_pos_of_pos hcg, hNr]
    have hone : 1 / (cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) ≤
        1 / (cg ^ 2 * (N : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact hden
    calc
      _ = 4 * (1 / (cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2))) := by ring
      _ ≤ 4 * (1 / (cg ^ 2 * (N : ℝ) ^ 2)) := by gcongr
      _ = (4 / cg ^ 2) * (N : ℝ) ^ (-2 : ℝ) := by
        rw [Real.rpow_neg hNr.le]
        norm_num [Real.rpow_natCast]
        field_simp [hcg.ne', hNr.ne']
  have hplugin : risk P g (fun input : PilotSample m d × MainCovariates N d × ℝ =>
      plugInMatching β input.1 input.2.1 hN hN2) ≤ Kplug * B := by
    calc
      _ ≤ 4 / (cg ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) + 12 * Ch * H := by
        simpa [H] using hplugin0
      _ ≤ (4 / cg ^ 2) * (N : ℝ) ^ (-2 : ℝ) + 12 * Ch * H := by
        gcongr
      _ ≤ Kplug * B := by
        dsimp [Kplug, B]
        nlinarith [mul_nonneg (le_of_lt (show 0 < 4 / cg ^ 2 by positivity)) hH0,
          mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hCh.le) hNrate0]
  by_cases hsel : G ≤ B
  · have hrisk : risk P g
        (selectorDesign (d := d) (m := m) (N := N) β hN hN2) ≤ Kgeo * G := by
      have hcond : (N : ℝ) ^ (-2 * β / d) ≤
          (N : ℝ) ^ (-2 : ℝ) + (m : ℝ) ^ (-2 * β / (2 * β + d)) := by
        change G ≤ B
        exact hsel
      have hdesign : selectorDesign (d := d) (m := m) (N := N) β hN hN2 =
        fun input : PilotSample m d × MainCovariates N d × ℝ =>
            geometricMatching input.2.1 hN hN2 := by
        funext input
        unfold selectorDesign
        rw [if_pos hcond]
      rw [hdesign]
      exact hgeo
    have hmin : jointFrontier d m N β = G := by
      unfold jointFrontier
      change min G B = G
      exact min_eq_left hsel
    rw [hmin]
    change risk P g (selectorDesign (d := d) (m := m) (N := N) β hN hN2) ≤ C * G
    exact hrisk.trans (mul_le_mul_of_nonneg_right
      (by dsimp [C]; linarith [hKplug]) hG0)
  · have hBlt : B < G := lt_of_not_ge hsel
    have hrisk : risk P g
        (selectorDesign (d := d) (m := m) (N := N) β hN hN2) ≤ Kplug * B := by
      have hcond : ¬((N : ℝ) ^ (-2 * β / d) ≤
          (N : ℝ) ^ (-2 : ℝ) + (m : ℝ) ^ (-2 * β / (2 * β + d))) := by
        change ¬ G ≤ B
        exact hsel
      have hdesign : selectorDesign (d := d) (m := m) (N := N) β hN hN2 =
        fun input : PilotSample m d × MainCovariates N d × ℝ =>
            plugInMatching β input.1 input.2.1 hN hN2 := by
        funext input
        unfold selectorDesign
        rw [if_neg hcond]
      rw [hdesign]
      exact hplugin
    have hmin : jointFrontier d m N β = B := by
      unfold jointFrontier
      change min G B = B
      exact min_eq_right hBlt.le
    rw [hmin]
    change risk P g (selectorDesign (d := d) (m := m) (N := N) β hN hN2) ≤ C * B
    exact hrisk.trans (mul_le_mul_of_nonneg_right
      (by dsimp [C]; linarith [hKgeo]) hB0)

end CausalSmith.Experimentation.PilotscorePairingFrontier

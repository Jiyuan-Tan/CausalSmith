module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.AnchorVariance
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.Geometry
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.OracleSpacing

/-!
# One-dimensional geometric upper bound for anchor scores

This module isolates the sharp spacing argument needed at the one-dimensional
endpoint.  It uses only the covariate-density condition and the Hölder bound.
-/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

private lemma anchor_euclideanDistance_sq_one (x y : XSpace 1) :
    (euclideanDistance x y) ^ 2 = (x 0 - y 0) ^ 2 := by
  unfold euclideanDistance
  rw [Real.sq_sqrt]
  · simp
  · positivity

private lemma anchor_geometricCost_eq_coordinate_pairLoss (N : ℕ)
    (x : MainCovariates N 1) (M : Match N) :
    geometricCost x M = pairLoss (fun z : XSpace 1 => z 0) x M := by
  unfold geometricCost pairLoss
  simp_rw [anchor_euclideanDistance_sq_one]

/-- In dimension one, geometric matching has the spacing-rate upper bound for
any Hölder score under a covariate density bounded below by `cX`. -/
-- @node: anchor_geometric_risk_bound_one_dim_raw
lemma anchor_geometric_risk_bound_one_dim_raw (m N : ℕ) (β cX CX : ℝ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hcX : 0 < cX) (hCX : cX ≤ CX)
    (hN : Even N) (hN2 : 2 ≤ N) (P : Measure (UnitRecord 1))
    (g : XSpace 1 → ℝ) (hg : HolderScore g 1 β)
    (hdensity : CovariateDensity P cX CX) :
    risk P g (fun input : PilotSample m 1 × MainCovariates N 1 × ℝ =>
      geometricMatching input.2.1 hN hN2) ≤
      (1 / 2 : ℝ) * 2 ^ β * (1 / cX ^ 2) ^ β *
        (N : ℝ) ^ (-2 * β) := by
  let coord : XSpace 1 → ℝ := fun x => x 0
  let A : MainSample N 1 → ℝ := fun us =>
    pairLoss coord (fun i => (us i).1)
      (oracleMatching coord (fun i => (us i).1) hN hN2) / (N : ℝ)
  let G : MainSample N 1 → ℝ := fun us =>
    pairLoss g (fun i => (us i).1)
      (geometricMatching (fun i => (us i).1) hN hN2) / (N : ℝ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  letI : IsProbabilityMeasure P := hdensity.1
  letI : IsProbabilityMeasure (Measure.pi fun _ : Fin N => P) := inferInstance
  have hAi : Integrable A (Measure.pi fun _ : Fin N => P) := by
    exact integrable_coordinate_oracle_loss_one_dim hN hN2 P hdensity
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
      exact le_trans (Real.rpow_le_self_of_one_le hA1 hβ1)
        (le_add_of_nonneg_left zero_le_one)
  have hjensen : (∫ us, (A us) ^ β ∂Measure.pi fun _ : Fin N => P) ≤
      (∫ us, A us ∂Measure.pi fun _ : Fin N => P) ^ β := by
    exact (Real.concaveOn_rpow hβ0.le hβ1).le_map_integral
      (Real.continuous_rpow_const hβ0.le).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall hAnonneg) hAi hApi
  have hcube : ∀ᵐ u ∂P, u.1 ∈ cube 1 := by
    have hcube_meas : MeasurableSet (cube 1) := by unfold cube; measurability
    have hxmap : cube 1 ∈ ae (P.map Prod.fst) := by
      rw [mem_ae_iff]
      apply hdensity.2.1
      simp [cubeMeasure, hcube_meas]
    exact ae_of_ae_map measurable_fst.aemeasurable hxmap
  have hcubes : ∀ᵐ us ∂Measure.pi (fun _ : Fin N => P),
      ∀ i, (us i).1 ∈ cube 1 := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hcube
  have hpoint : G ≤ᵐ[Measure.pi fun _ : Fin N => P]
      fun us => (1 / 2 : ℝ) * (2 * A us) ^ β := by
    filter_upwards [hcubes] with us hus
    let x : MainCovariates N 1 := fun i => (us i).1
    let M := geometricMatching x hN hN2
    have hp := holder_pairLoss_le_geometricCost_rpow (by omega) g 1 β
      (by norm_num) hβ0 hβ1 hg x hus M
    have hopt : geometricCost x M ≤
        geometricCost x (oracleMatching coord x hN hN2) :=
      (Classical.choose_spec (exists_geometricMatching x hN hN2) _).1
    have hpow : (2 * geometricCost x M) ^ β ≤
        (2 * pairLoss coord x (oracleMatching coord x hN hN2)) ^ β := by
      apply Real.rpow_le_rpow
      · exact mul_nonneg (by norm_num) (by unfold geometricCost; positivity)
      · simpa [coord, anchor_geometricCost_eq_coordinate_pairLoss] using
          mul_le_mul_of_nonneg_left hopt (by norm_num : (0 : ℝ) ≤ 2)
      · exact hβ0.le
    have hp' := hp.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpow (by positivity)) (sq_nonneg (1 : ℝ)))
    dsimp [G, A, x, M, coord]
    calc
      _ ≤ ((1 : ℝ) ^ 2 * ((1 / 2 : ℝ) * (N : ℝ) ^ (1 - β) *
          (2 * pairLoss (fun z : XSpace 1 => z 0) (fun i => (us i).1)
            (oracleMatching (fun z : XSpace 1 => z 0) (fun i => (us i).1) hN hN2)) ^ β)) /
            (N : ℝ) := (div_le_div_iff_of_pos_right hNr).2 hp'
      _ = (1 / 2 : ℝ) *
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
          _ = (1 / 2 : ℝ) * ((N : ℝ) ^ (1 - β) / (N : ℝ)) *
              (2 * pairLoss (fun z : XSpace 1 => z 0) (fun i => (us i).1)
                (oracleMatching (fun z : XSpace 1 => z 0)
                  (fun i => (us i).1) hN hN2)) ^ β := by ring
          _ = (1 / 2 : ℝ) * (1 / (N : ℝ) ^ β) *
              (2 * pairLoss (fun z : XSpace 1 => z 0) (fun i => (us i).1)
                (oracleMatching (fun z : XSpace 1 => z 0)
                  (fun i => (us i).1) hN hN2)) ^ β := by rw [hNpow]
          _ = _ := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hC]
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (div_nonneg hC hNr.le),
              Real.div_rpow hC hNr.le]
            ring
  have hupperi : Integrable (fun us => (1 / 2 : ℝ) * (2 * A us) ^ β)
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
      (1 / 2 : ℝ) * 2 ^ β * (1 / cX ^ 2) ^ β *
        (N : ℝ) ^ (-2 * β) := by
    have hmono := integral_mono_of_nonneg hGnonneg hupperi hpoint
    have hspacing := (coordinate_oracle_spacing_bound_one_dim hN hN2 P
      hdensity hcX hCX).2
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
      _ ≤ ∫ us, (1 / 2 : ℝ) * (2 * A us) ^ β
          ∂Measure.pi fun _ : Fin N => P := hmono
      _ = (1 / 2 : ℝ) * 2 ^ β *
          (∫ us, (A us) ^ β ∂Measure.pi fun _ : Fin N => P) := by
        rw [integral_const_mul]
        simp_rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (hAnonneg _)]
        rw [integral_const_mul]
        ring
      _ ≤ (1 / 2 : ℝ) * 2 ^ β *
          (∫ us, A us ∂Measure.pi fun _ : Fin N => P) ^ β := by gcongr
      _ ≤ (1 / 2 : ℝ) * 2 ^ β *
          (1 / (cX ^ 2 * (N : ℝ) ^ 2)) ^ β := by
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
    (fun x => geometricMatching x hN hN2) hdensity.1
    (by letI : IsProbabilityMeasure P := hdensity.1
        letI : IsProbabilityMeasure (pilotUnitLaw P) :=
          pilotUnitLaw_probability P hdensity.1
        infer_instance)
    randomizerLaw_probability
  unfold risk
  change (∫ w, pairLoss g (fun i => (w.1.2 i).1)
      (geometricMatching (fun i => (w.1.2 i).1) hN hN2) / (N : ℝ)
        ∂latentTwoWaveLaw (m := m) (N := N) P) ≤ _
  rw [← heq]
  change (∫ us, G us ∂Measure.pi fun _ : Fin N => P) ≤ _
  exact hmain

end CausalSmith.Experimentation.PilotscorePairingFrontier

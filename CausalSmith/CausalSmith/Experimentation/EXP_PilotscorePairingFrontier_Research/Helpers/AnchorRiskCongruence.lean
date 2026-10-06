module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.OracleSpacing

/-!
# Risk congruence for half-sum score versions

Matching risk depends on a score only through its values at the iid main-wave
covariates.  This file transports an almost-everywhere equality under the unit
law to every main-wave coordinate and then through the full latent experiment,
allowing arbitrary pilot-dependent matching designs.
-/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

/-- If two [scores agree at the recorded covariate almost everywhere under the
unit law](hyp:hgg), then their [matching risks are equal](goal) for every
[design](hyp:D), provided the [unit law is a probability measure](hyp:hP). -/
lemma risk_congr_of_ae_covariate_score {d m N : ℕ}
    (P : Measure (UnitRecord d)) (hP : IsProbabilityMeasure P)
    (g g' : XSpace d → ℝ)
    (hgg : (fun u : UnitRecord d => g u.1) =ᵐ[P] fun u => g' u.1)
    (D : Design m N d) :
    risk P g D = risk P g' D := by
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure (pilotUnitLaw P) := pilotUnitLaw_probability P hP
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  have hmain : ∀ᵐ us ∂Measure.pi (fun _ : Fin N => P),
      ∀ i, g (us i).1 = g' (us i).1 := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hgg
  let mainProjection : WaveInput m N d → MainSample N d := fun a => a.1.2
  have hmainProjection : Measurable mainProjection := by
    dsimp [mainProjection]
    fun_prop
  have hmap :
      (latentTwoWaveLaw (m := m) (N := N) P).map mainProjection =
        Measure.pi (fun _ : Fin N => P) := by
    unfold latentTwoWaveLaw
    rw [show mainProjection = Prod.snd ∘ Prod.fst by rfl,
      ← Measure.map_map measurable_snd measurable_fst,
      Measure.map_fst_prod]
    simp only [measure_univ, one_smul]
    rw [Measure.map_snd_prod]
    simp
  have hlatent : ∀ᵐ a ∂latentTwoWaveLaw (m := m) (N := N) P,
      ∀ i, g (a.1.2 i).1 = g' (a.1.2 i).1 := by
    have ht : ∀ᵐ a ∂latentTwoWaveLaw (m := m) (N := N) P,
        ∀ i, g ((mainProjection a) i).1 = g' ((mainProjection a) i).1 := by
      have hpush : ∀ᵐ y ∂(latentTwoWaveLaw (m := m) (N := N) P).map mainProjection,
          ∀ i, g (y i).1 = g' (y i).1 := by
        rw [hmap]
        exact hmain
      exact ae_of_ae_map hmainProjection.aemeasurable hpush
    simpa [mainProjection] using ht
  unfold risk latentTwoWaveLaw
  apply integral_congr_ae
  filter_upwards [hlatent] with a ha
  apply congrArg (fun t : ℝ => t / (N : ℝ))
  unfold pairLoss
  apply congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
  apply Finset.sum_congr rfl
  intro i hi
  rw [ha i, ha ((D (designInput a)).val i)]

/-- Any two [half-sum regression versions](hyp:hg,hg') for the same
[probability law](hyp:hP) have [identical matching risk](goal) under every
[possibly pilot-dependent design](hyp:D). -/
lemma risk_eq_of_isHalfSumVersion {d m N : ℕ}
    (P : Measure (UnitRecord d)) (hP : IsProbabilityMeasure P)
    (g g' : XSpace d → ℝ) (hg : IsHalfSumVersion P g)
    (hg' : IsHalfSumVersion P g') (D : Design m N d) :
    risk P g D = risk P g' D := by
  apply risk_congr_of_ae_covariate_score P hP g g' _ D
  filter_upwards [hg, hg'] with u hu hu'
  exact hu.trans hu'.symm

end CausalSmith.Experimentation.PilotscorePairingFrontier

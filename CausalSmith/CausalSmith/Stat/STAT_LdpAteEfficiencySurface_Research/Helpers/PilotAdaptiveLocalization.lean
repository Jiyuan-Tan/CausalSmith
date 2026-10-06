module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAdaptiveInputs

/-! # Localization bounds for adaptive pilot inputs -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Under [the supplied quantities and conditions](hyp:p,m), [the pilot theta interior assertion](goal) holds. For [the displayed quantities and conditions](hyp:z), these specify the stated inputs. -/
lemma pilotTheta_interior (p ε : ℝ) (m : ℕ → ℕ) {n : ℕ}
    (z : Transcript (pilotOutputFamily n)) :
    InteriorMeans (pilotTheta p ε m z) := by
  have hδ : 0 < ((m n + 2 : ℝ)⁻¹) := by positivity
  have hhalf : ((m n + 2 : ℝ)⁻¹) ≤ 1 / 2 := by
    rw [one_div]
    have hden : (2 : ℝ) ≤ m n + 2 := by
      exact_mod_cast Nat.le_add_left 2 (m n)
    simpa [one_div] using one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 2) hden
  have h0 := clipInterior_interior ((m n + 2 : ℝ)⁻¹)
    (((Real.exp ε + 3) * pilotFrequency m z 1 - 1) /
      (Real.exp ε - 1) / controlProb p) hδ hhalf
  have h1 := clipInterior_interior ((m n + 2 : ℝ)⁻¹)
    (((Real.exp ε + 3) * pilotFrequency m z 3 - 1) /
      (Real.exp ε - 1) / p) hδ hhalf
  simpa [InteriorMeans, pilotTheta] using
    And.intro h0.1 (And.intro h0.2 (And.intro h1.1 h1.2))

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under the supplied quantities and conditions, the adaptive pilot rare event integral le assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hr,hq,hmn,hmpos,hδ0l,hδ0r,hδ1l,hδ1r), [the adaptive Pilot Rare Event integral le](goal).

Under the stated assumptions, the adaptive Pilot Rare Event integral le. -/
lemma adaptivePilotRareEvent_integral_le
    (θ : TrialParameter) (p ε r q : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hr : 0 < r) (hq : 0 < q) {n : ℕ} (hmn : m n ≤ n) (hmpos : 0 < m n)
    (hδ0l : (m n + 2 : ℝ)⁻¹ + r ≤ θ 0)
    (hδ0r : (m n + 2 : ℝ)⁻¹ + r ≤ 1 - θ 0)
    (hδ1l : (m n + 2 : ℝ)⁻¹ + r ≤ θ 1)
    (hδ1r : (m n + 2 : ℝ)⁻¹ + r ≤ 1 - θ 1) :
    let a0 := r * controlProb p * (Real.exp ε - 1) / (Real.exp ε + 3)
    let a1 := r * p * (Real.exp ε - 1) / (Real.exp ε + 3)
    let μ := transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n
    ∫ z in {z | r ≤ |pilotTheta p ε m z 0 - θ 0| ∨
        r ≤ |pilotTheta p ε m z 1 - θ 1|},
        (1 + adaptiveScoreVariance select θ (pilotTheta p ε m z) p ε +
          adaptiveScoreMoment select q θ (pilotTheta p ε m z) p ε) ∂μ ≤
      (1 + (pilotPhiUpper p ε) ^ 2 + (pilotPhiUpper p ε) ^ q) *
        (ENNReal.ofReal (1 / ((m n : ℝ) * a0 ^ 2)) +
          ENNReal.ofReal (1 / ((m n : ℝ) * a1 ^ 2))).toReal := by
  dsimp only
  let μ := transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n
  let A : Set (Transcript (pilotOutputFamily n)) :=
    {z | r ≤ |pilotTheta p ε m z 0 - θ 0| ∨
      r ≤ |pilotTheta p ε m z 1 - θ 1|}
  let C := 1 + (pilotPhiUpper p ε) ^ 2 + (pilotPhiUpper p ε) ^ q
  let f : Transcript (pilotOutputFamily n) → ℝ := fun z =>
    1 + adaptiveScoreVariance select θ (pilotTheta p ε m z) p ε +
      adaptiveScoreMoment select q θ (pilotTheta p ε m z) p ε
  letI : IsProbabilityMeasure μ :=
    transcriptLaw_isProbability (pilotEstimator p ε m select hselect hp hε) θ p hp hθ n
  have hfint : IntegrableOn f A μ := Integrable.of_finite
  have hcint : IntegrableOn (fun _ : Transcript (pilotOutputFamily n) => C) A μ :=
    integrableOn_const
  have hpoint (z : Transcript (pilotOutputFamily n)) : f z ≤ C := by
    exact (adaptiveRareEventIntegrand_bounds select θ (pilotTheta p ε m z) p ε q
      hselect hp hθ
      (pilotTheta_interior p ε m z) hε hq).2
  have hdev : μ A ≤
      ENNReal.ofReal (1 / ((m n : ℝ) *
        (r * controlProb p * (Real.exp ε - 1) / (Real.exp ε + 3)) ^ 2)) +
      ENNReal.ofReal (1 / ((m n : ℝ) *
        (r * p * (Real.exp ε - 1) / (Real.exp ε + 3)) ^ 2)) := by
    simpa [μ, A] using pilotTheta_deviation_le select θ p ε r m hselect hp hθ hε hr hmn hmpos
      hδ0l hδ0r hδ1l hδ1r
  have hdevReal : μ.real A ≤
      (ENNReal.ofReal (1 / ((m n : ℝ) *
        (r * controlProb p * (Real.exp ε - 1) / (Real.exp ε + 3)) ^ 2)) +
      ENNReal.ofReal (1 / ((m n : ℝ) *
        (r * p * (Real.exp ε - 1) / (Real.exp ε + 3)) ^ 2))).toReal := by
    rw [measureReal_def]
    exact ENNReal.toReal_mono (by simp) hdev
  have hC : 0 ≤ C := by
    dsimp [C]
    have hB := pilotPhiUpper_nonneg p ε hp hε
    positivity
  change ∫ z in A, f z ∂μ ≤ C * _
  calc
    (∫ z in A, f z ∂μ) ≤ ∫ _z in A, C ∂μ := by
      apply integral_mono_ae hfint hcint
      exact Filter.Eventually.of_forall hpoint
    _ = C * μ.real A := by
      rw [setIntegral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ C * _ := mul_le_mul_of_nonneg_left hdevReal hC

end CausalSmith.Stat.LdpAteEfficiencySurface

module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialFisherRecursion
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialPriorInformationEnvelope
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialVanTreesRiskBridge
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialPriorRadiusLimit

/-! # Universal sequential local asymptotic lower bound -/

public section
noncomputable section
namespace CausalSmith.Stat.LdpAteEfficiencySurface

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal
open Causalean.Stat.Minimax.ObservationDependentVanTrees

/-- the likelihood score vt density eq transcript score assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hη,ha), [the likelihood Score vt Density eq transcript Score](goal).

Under the stated assumptions, the likelihood Score vt Density eq transcript Score. -/
lemma likelihoodScore_vtDensity_eq_transcriptScore
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ d : TrialParameter) (p ell upper a : ℝ)
    (n : ℕ) (hp : InteriorAssignment p)
    (hη : InteriorMeans (parameterPath θ d a)) (ha : a ∈ Icc ell upper)
    (z : Transcript (Z n)) :
    likelihoodScore (vtDensity P θ d p n ell upper)
        (vtDensityDeriv P θ d p n ell upper) a z =
      conditionalTranscriptDirectionalScore P (parameterPath θ d a) d p n z := by
  rw [conditionalTranscriptDirectionalScore_eq_guarded
    P (parameterPath θ d a) d p n hp hη z]
  unfold likelihoodScore vtDensity vtDensityDeriv
  simp only [ha, ↓reduceIte]


/-- the fisher information vt density eq transcript score energy assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hη,ha), [the fisher Information vt Density eq transcript Score Energy](goal).

Under the stated assumptions, the fisher Information vt Density eq transcript Score Energy. -/
lemma fisherInformation_vtDensity_eq_transcriptScoreEnergy
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ d : TrialParameter) (p ell upper a : ℝ)
    (n : ℕ) (hp : InteriorAssignment p)
    (hη : InteriorMeans (parameterPath θ d a)) (ha : a ∈ Icc ell upper) :
    fisherInformation (transcriptReferenceMeasure P n)
        (vtDensity P θ d p n ell upper)
        (vtDensityDeriv P θ d p n ell upper) a =
      ∫ z, conditionalTranscriptDirectionalScore P
          (parameterPath θ d a) d p n z ^ 2
        ∂transcriptLaw P (parameterPath θ d a) p n := by
  let q := transcriptMixtureRealDensity P (parameterPath θ d a) p n
  let s := conditionalTranscriptDirectionalScore P (parameterPath θ d a) d p n
  have hqnonneg (z : Transcript (Z n)) : 0 ≤ q z :=
    transcriptMixtureRealDensity_nonneg P (parameterPath θ d a) p n hp hη z
  unfold fisherInformation
  rw [show (fun z => vtDensity P θ d p n ell upper a z *
      likelihoodScore (vtDensity P θ d p n ell upper)
        (vtDensityDeriv P θ d p n ell upper) a z ^ 2) =
      fun z => q z * s z ^ 2 by
    funext z
    rw [likelihoodScore_vtDensity_eq_transcriptScore
      P θ d p ell upper a n hp hη ha z]
    simp [q, s, vtDensity, ha]]
  rw [← transcriptLaw_eq_withDensity_mixture
    P (parameterPath θ d a) p n hp hη]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_transcriptMixtureRealDensity
      P (parameterPath θ d a) p n).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with z
  rw [ENNReal.toReal_ofReal (hqnonneg z), smul_eq_mul]


/-- the fisher information scaled selected le upper envelope assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hn,ha,hη), [the fisher Information scaled Selected le upper Envelope](goal).

Under the stated assumptions, the fisher Information scaled Selected le upper Envelope. -/
lemma fisherInformation_scaledSelected_le_upperEnvelope
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p R a : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (n : ℕ) (hn : 0 < n)
    (ha : a ∈ Icc (-R) R)
    (hη : InteriorMeans (parameterPath θ
      (direction (selectedDirection θ p ε hp hθ hε)) (a / Real.sqrt n))) :
    fisherInformation (transcriptReferenceMeasure P n)
        (vtDensity P θ
          (scaledDirection ((Real.sqrt n)⁻¹)
            (direction (selectedDirection θ p ε hp hθ hε)))
          p n (-R) R)
        (vtDensityDeriv P θ
          (scaledDirection ((Real.sqrt n)⁻¹)
            (direction (selectedDirection θ p ε hp hθ hε)))
          p n (-R) R) a ≤
      upperEnvelope
        (parameterPath θ
          (direction (selectedDirection θ p ε hp hθ hε))
          (a / Real.sqrt n)) p ε
        (selectedDirection θ p ε hp hθ hε) := by
  let v := direction (selectedDirection θ p ε hp hθ hε)
  let c := (Real.sqrt n)⁻¹
  let η := parameterPath θ v (a / Real.sqrt n)
  have hpath : parameterPath θ (scaledDirection c v) a = η := by
    funext k
    simp [η, v, c, parameterPath, scaledDirection]
    ring
  rw [fisherInformation_vtDensity_eq_transcriptScoreEnergy
    P θ (scaledDirection c v) p (-R) R a n hp (hpath ▸ hη) ha]
  rw [hpath]
  have hb := transcriptScaledDirectionalFisher_le
    P η p (selectedDirection θ p ε hp hθ hε) c hp hη hε n
  calc
    (∫ z, conditionalTranscriptDirectionalScore P η
        (scaledDirection c v) p n z ^ 2 ∂transcriptLaw P η p n) ≤
      c ^ 2 * ((n : ℝ) * upperEnvelope η p ε
        (selectedDirection θ p ε hp hθ hε)) := by simpa [v] using hb
    _ = upperEnvelope η p ε
        (selectedDirection θ p ε hp hθ hε) := by
      have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
      have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnreal)
      dsimp [c]
      rw [inv_pow]
      rw [show (Real.sqrt (n : ℝ)) ^ 2 = n by
        exact Real.sq_sqrt (Nat.cast_nonneg n)]
      field_simp
    _ = _ := rfl


/-- [the integrable vt likelihood fisher section assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,d,p,ell,upper,a,n,hp,hinterior), these specify the stated inputs. -/
lemma integrable_vtLikelihoodFisher_section
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ d : TrialParameter) (p ell upper a : ℝ)
    (n : ℕ) (hp : InteriorAssignment p)
    (hinterior : ∀ a ∈ Icc ell upper,
      InteriorMeans (parameterPath θ d a)) :
    Integrable (fun z => vtDensity P θ d p n ell upper a z *
      likelihoodScore (vtDensity P θ d p n ell upper)
        (vtDensityDeriv P θ d p n ell upper) a z ^ 2)
      (transcriptReferenceMeasure P n) := by
  by_cases ha : a ∈ Icc ell upper
  · let η := parameterPath θ d a
    let q := transcriptMixtureRealDensity P η p n
    let score := conditionalTranscriptDirectionalScore P η d p n
    have hη := hinterior a ha
    have hs : Integrable (fun z => score z ^ 2) (transcriptLaw P η p n) :=
      (conditionalTranscriptDirectionalScore_memLp_two
        P η d p n hp hη).integrable_sq
    rw [← transcriptLaw_eq_withDensity_mixture P η p n hp hη] at hs
    have hs' := (integrable_withDensity_iff_integrable_smul'
      (measurable_transcriptMixtureRealDensity P η p n).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hs
    convert hs' using 1
    funext z
    rw [likelihoodScore_vtDensity_eq_transcriptScore
      P θ d p ell upper a n hp hη ha z]
    have hq := transcriptMixtureRealDensity_nonneg P η p n hp hη z
    simp [vtDensity, ha, η, score, ENNReal.toReal_ofReal hq, smul_eq_mul]
  · simp [vtDensity, likelihoodScore, ha]


/-- the scaled selected fisher integrable and control assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hR,hn,hinterior,henvInt), [the scaled Selected fisher integrable and control](goal).

Under the stated assumptions, the scaled Selected fisher integrable and control. -/
lemma scaledSelected_fisher_integrable_and_control
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p R : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (hinterior : ∀ a ∈ Icc (-R) R, InteriorMeans
      (parameterPath θ
        (direction (selectedDirection θ p ε hp hθ hε))
        (a / Real.sqrt n)))
    (henvInt : Integrable (fun a => sequentialVTPrior R a *
      upperEnvelope
        (parameterPath θ
          (direction (selectedDirection θ p ε hp hθ hε))
          (a / Real.sqrt n)) p ε
        (selectedDirection θ p ε hp hθ hε))
      (parameterMeasure (-R) R)) :
    Integrable (fun z : ℝ × Transcript (Z n) =>
      sequentialVTPrior R z.1 *
        vtDensity P θ
          (scaledDirection ((Real.sqrt n)⁻¹)
            (direction (selectedDirection θ p ε hp hθ hε)))
          p n (-R) R z.1 z.2 *
        (likelihoodScore
          (vtDensity P θ
            (scaledDirection ((Real.sqrt n)⁻¹)
              (direction (selectedDirection θ p ε hp hθ hε)))
            p n (-R) R)
          (vtDensityDeriv P θ
            (scaledDirection ((Real.sqrt n)⁻¹)
              (direction (selectedDirection θ p ε hp hθ hε)))
            p n (-R) R) z.1 z.2) ^ 2)
      ((parameterMeasure (-R) R).prod (transcriptReferenceMeasure P n)) ∧
    (∫ a, sequentialVTPrior R a *
      fisherInformation (transcriptReferenceMeasure P n)
        (vtDensity P θ
          (scaledDirection ((Real.sqrt n)⁻¹)
            (direction (selectedDirection θ p ε hp hθ hε)))
          p n (-R) R)
        (vtDensityDeriv P θ
          (scaledDirection ((Real.sqrt n)⁻¹)
            (direction (selectedDirection θ p ε hp hθ hε)))
          p n (-R) R) a
      ∂parameterMeasure (-R) R) ≤
      sequentialPriorInformationEnvelope θ p ε R hp hθ hε n := by
  let v := direction (selectedDirection θ p ε hp hθ hε)
  let d := scaledDirection ((Real.sqrt n)⁻¹) v
  let q := vtDensity P θ d p n (-R) R
  let dq := vtDensityDeriv P θ d p n (-R) R
  let w := sequentialVTPrior R
  let ν := transcriptReferenceMeasure P n
  let π := parameterMeasure (-R) R
  let F : ℝ × Transcript (Z n) → ℝ := fun z =>
    w z.1 * q z.1 z.2 * (likelihoodScore q dq z.1 z.2) ^ 2
  let env : ℝ → ℝ := fun a => upperEnvelope
    (parameterPath θ v (a / Real.sqrt n)) p ε
      (selectedDirection θ p ε hp hθ hε)
  let info : ℝ → ℝ := fun a => fisherInformation ν q dq a
  have hpath (a : ℝ) : parameterPath θ d a =
      parameterPath θ v (a / Real.sqrt n) := by
    funext k
    simp [d, v, parameterPath, scaledDirection, div_eq_mul_inv]
    ring
  have hmeas := sequentialVanTreesProductMeasurable
    P θ d p R n hR (P.estimate n) (P.estimate_measurable n)
  have hFmeas : AEStronglyMeasurable F (π.prod ν) := by
    exact hmeas.fisherSq.aestronglyMeasurable
  have hFnonneg (z : ℝ × Transcript (Z n)) : 0 ≤ F z := by
    dsimp [F]
    exact mul_nonneg
      (mul_nonneg (sequentialVTPrior_facts hR |>.nonneg z.1)
        (vtDensity_nonneg P θ d p n (-R) R hp
          (by
            intro a ha
            exact hpath a ▸ hinterior a ha) z.1 z.2))
      (sq_nonneg _)
  have hsection (a : ℝ) : Integrable (fun z => F (a, z)) ν := by
    have hs := integrable_vtLikelihoodFisher_section
      P θ d p (-R) R a n hp (by
        intro b hb
        exact hpath b ▸ hinterior b hb)
    exact (hs.const_mul (w a)).congr (Filter.Eventually.of_forall fun z => by
      dsimp [F]
      ring)
  let G : ℝ → ℝ := fun a => ∫ z, ‖F (a, z)‖ ∂ν
  have hGmeas : AEStronglyMeasurable G π := by
    exact hFmeas.norm.integral_prod_right'
  have hG_eq (a : ℝ) : G a = w a * info a := by
    calc
      G a = ∫ z, F (a, z) ∂ν := by
        apply integral_congr_ae
        filter_upwards with z
        rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg (a, z))]
      _ = w a * ∫ z, q a z * (likelihoodScore q dq a z) ^ 2 ∂ν := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with z
        dsimp [F]
        ring
      _ = w a * info a := rfl
  have hGInt : Integrable G π := by
    apply henvInt.mono' hGmeas
    have hmem : ∀ᵐ a ∂π, a ∈ Icc (-R) R := by
      dsimp [π, parameterMeasure]
      exact ae_restrict_mem measurableSet_Icc
    filter_upwards [hmem] with a ha
    rw [hG_eq, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (sequentialVTPrior_facts hR |>.nonneg a)
        (by
          dsimp [info]
          rw [fisherInformation_vtDensity_eq_transcriptScoreEnergy
            P θ d p (-R) R a n hp
            (by
              exact hpath a ▸ hinterior a ha) ha]
          exact integral_nonneg fun _ => sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (by
        dsimp [info, env]
        simpa [d, v] using fisherInformation_scaledSelected_le_upperEnvelope
          P θ p R a hp hθ hε n hn ha (hinterior a ha))
      (sequentialVTPrior_facts hR |>.nonneg a)
  have hFInt : Integrable F (π.prod ν) :=
    (integrable_prod_iff hFmeas).2
      ⟨Filter.Eventually.of_forall hsection, hGInt⟩
  constructor
  · simpa [F, π, ν, w, q, dq, d, v] using hFInt
  · have hweightedInt : Integrable (fun a => w a * info a) π := by
      exact hGInt.congr (Filter.Eventually.of_forall fun a => hG_eq a)
    calc
      (∫ a, sequentialVTPrior R a *
          fisherInformation (transcriptReferenceMeasure P n)
            (vtDensity P θ d p n (-R) R)
            (vtDensityDeriv P θ d p n (-R) R) a ∂π) ≤
        ∫ a, w a * env a ∂π := by
          apply integral_mono_ae
            (by simpa [w, info, q, dq, ν, d, v] using hweightedInt)
            (by simpa [w, env, π, v] using henvInt)
          have hmem : ∀ᵐ a ∂π, a ∈ Icc (-R) R := by
            dsimp [π, parameterMeasure]
            exact ae_restrict_mem measurableSet_Icc
          filter_upwards [hmem] with a ha
          exact mul_le_mul_of_nonneg_left
            (by
              dsimp [info, env, ν, q, dq, d, v]
              exact fisherInformation_scaledSelected_le_upperEnvelope
                P θ p R a hp hθ hε n hn ha (hinterior a ha))
            (sequentialVTPrior_facts hR |>.nonneg a)
      _ = sequentialPriorInformationEnvelope θ p ε R hp hθ hε n := by
        rfl


/-- Every sequentially private procedure has local asymptotic risk at least the stationary minimax reciprocal information. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the sequential local Asymptotic Risk lower bound](goal).

Under the stated assumptions, the sequential local Asymptotic Risk lower bound. -/
lemma sequential_localAsymptoticRisk_lower_bound
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    ENNReal.ofReal (Vstar θ p ε) ≤ localAsymptoticRisk P θ p := by
  let t := selectedDirection θ p ε hp hθ hε
  let v := direction t
  let normv := Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2)
  let H : ℝ → ℝ := fun R => R * normv
  let info : ℝ → ℕ → ℝ := fun R n =>
    sequentialPriorInformationEnvelope θ p ε R hp hθ hε n
  have hnormv : 0 < normv := by
    have hsum : 0 < (v 0) ^ 2 + (v 1) ^ 2 := by
      dsimp [v]
      simp [direction]
      nlinarith [sq_nonneg t, sq_nonneg (t + 1)]
    exact Real.sqrt_pos.2 hsum
  have hH : ∀ R, 0 < R → 0 < H R := by
    intro R hR
    exact mul_pos hR hnormv
  have hinfo : ∀ R, 0 < R → Tendsto (info R) atTop (nhds (Jstar θ p ε)) := by
    intro R hR
    exact tendsto_sequentialPriorInformationEnvelope θ p ε R hp hθ hε hR
  have hlower : ∀ R, 0 < R → ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (1 / (info R n + 40 / R ^ 2)) ≤
        localWorstRisk P θ p (H R) n := by
    intro R hR
    have hinterior := eventually_parameterPath_compactScaled_interior
      θ v R hθ
    have henvInt := eventually_integrable_priorWeighted_upperEnvelope
      θ p ε R hp hθ hε hR
    filter_upwards [eventually_gt_atTop (0 : ℕ), hinterior, henvInt]
      with n hn hnInterior hnEnvInt
    have hcontrol := scaledSelected_fisher_integrable_and_control
      P θ p R hp hθ hε hR n hn hnInterior hnEnvInt
    have hpath (a : ℝ) : parameterPath θ
        (scaledDirection ((Real.sqrt n)⁻¹) v) a =
        parameterPath θ v (a / Real.sqrt n) := by
      funext k
      simp [parameterPath, scaledDirection, div_eq_mul_inv]
      ring
    have hactualInterior : ∀ a ∈ Icc (-R) R, InteriorMeans
        (parameterPath θ (scaledDirection ((Real.sqrt n)⁻¹) v) a) := by
      intro a ha
      exact hpath a ▸ hnInterior a ha
    have havgNonneg : 0 ≤ ∫ a, sequentialVTPrior R a *
        fisherInformation (transcriptReferenceMeasure P n)
          (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R)
          (vtDensityDeriv P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
            p n (-R) R) a
        ∂parameterMeasure (-R) R := by
      apply integral_nonneg_of_ae
      have hmem : ∀ᵐ a ∂parameterMeasure (-R) R, a ∈ Icc (-R) R := by
        unfold parameterMeasure
        exact ae_restrict_mem measurableSet_Icc
      filter_upwards [hmem] with a ha
      apply mul_nonneg (sequentialVTPrior_facts hR |>.nonneg a)
      rw [fisherInformation_vtDensity_eq_transcriptScoreEnergy
        P θ (scaledDirection ((Real.sqrt n)⁻¹) v) p (-R) R a n hp
        (hactualInterior a ha) ha]
      exact integral_nonneg fun _ => sq_nonneg _
    have hinfoPos : 0 < priorInformation (-R) R
          (sequentialVTPrior R) (sequentialVTPriorDeriv R) +
        ∫ a, sequentialVTPrior R a *
          fisherInformation (transcriptReferenceMeasure P n)
            (vtDensity P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
              p n (-R) R)
            (vtDensityDeriv P θ (scaledDirection ((Real.sqrt n)⁻¹) v)
              p n (-R) R) a
          ∂parameterMeasure (-R) R := by
      rw [(sequentialVTPrior_facts hR).information]
      have hprior : 0 < 40 / R ^ 2 := div_pos (by norm_num) (sq_pos_of_pos hR)
      linarith
    have hbound := ofReal_vanTreesEnvelope_le_localWorstRisk_of_fisher_control_allErrors
      P θ v p R (H R) (info R n) n hn hR hp hactualInterior
      (le_rfl : R * Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2) ≤ H R)
      hcontrol.1 hcontrol.2 hinfoPos
    have hcontrast : contrast v = 1 := by
      simpa [v, t] using contrast_selectedDirection θ p ε hp hθ hε
    simpa [hcontrast] using hbound
  have hrecip := inv_information_le_localAsymptoticRisk_of_priorRadius_family
    P θ p (Jstar θ p ε) H info
    (Jstar_pos_interior θ p ε hp hθ hε) hH hinfo hlower
  simpa [Vstar, one_div] using hrecip

end CausalSmith.Stat.LdpAteEfficiencySurface

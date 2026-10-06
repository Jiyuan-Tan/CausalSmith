module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TwoCell
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TwoCellInterval

/-!
# Two-cell attainment from component estimates

This assembly separates the binary/vector sampling calculation from the already
proved projection, Markov coverage, and interval length arguments. Component
bounds are proof inputs here, not extra assumptions on the paper theorem.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Fix [the sampling scheme S](hyp:S) and [the privacy budget](hyp:eps). [The binary baseline and two vector-coordinate estimates required by the roadmap. Existence of this certificate remains a proof obligation in the calibration theorem](goal). -/
-- @node: TwoCellComponents
def TwoCellComponents {n : ℕ} (S : SamplingScheme n 2) (eps : ℝ) : Prop :=
  ∃ (Q : LocalProtocol n (ObsRecord 2)), NoninteractiveClass Q eps ∧ FiniteMessages Q ∧
    ∃ (B x0 x1 : Estimator Q), TranscriptOnly Q B ∧ TranscriptOnly Q x0 ∧
      TranscriptOnly Q x1 ∧ ∀ P ∈ causalClass 2,
        squaredRisk (decisionLaw S Q P) B (baseline P) ≤
          ENNReal.ofReal (1 / (4 * (n / 2 : ℕ) * (privacyDelta eps) ^ 2)) ∧
        squaredRisk (decisionLaw S Q P) x0 (contrast P 0) ≤
          ENNReal.ofReal (4 / ((n - n / 2 : ℕ) * (privacyDelta eps) ^ 2)) ∧
        squaredRisk (decisionLaw S Q P) x1 (contrast P 1) ≤
          ENNReal.ofReal (4 / ((n - n / 2 : ℕ) * (privacyDelta eps) ^ 2))

/-- Assume [the stated b condition](hyp:hB), [the stated hx0 condition](hyp:hx0), and [the stated hx1 condition](hyp:hx1). [Combining transcript-only components preserves the transcript-only property](goal). -/
-- @node: twoCellEstimator_transcriptOnly
lemma twoCellEstimator_transcriptOnly {n : ℕ} (Q : LocalProtocol n (ObsRecord 2))
    (B x0 x1 : Estimator Q) (hB : TranscriptOnly Q B)
    (hx0 : TranscriptOnly Q x0) (hx1 : TranscriptOnly Q x1) :
    TranscriptOnly Q (twoCellEstimator Q B x0 x1) := by
  obtain ⟨b, hb, hbeq⟩ := hB
  obtain ⟨t0, ht0, ht0eq⟩ := hx0
  obtain ⟨t1, ht1, ht1eq⟩ := hx1
  refine ⟨fun z => twoCellValueEstimate (b z) (t0 z) (t1 z),
    measurable_twoCellValueEstimate b t0 t1 hb ht0 ht1, ?_⟩
  intro w
  change twoCellValueEstimate (B.1 w) (x0.1 w) (x1.1 w) = _
  rw [hbeq, ht0eq, ht1eq]

/-- Assume [the stated allowed condition](hyp:hAllowed), [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), [the stated ht condition](hyp:ht), and [the stated components condition](hyp:hComponents). [Component MSEs give both unsaturated upper orders with the roadmap's constant 1000](goal). -/
-- @node: two_cell_unsaturated_attainment_of_components
lemma two_cell_unsaturated_attainment_of_components {n : ℕ} (eps : ℝ)
    (hAllowed : Allowed n 2 eps) (S : SamplingScheme n 2)
    (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (ht : 1 < (n : ℝ) * eps ^ 2) (hComponents : TwoCellComponents S eps) :
    CausalAttainment S eps (min 1 (1 / (n * eps ^ 2)))
      (min 1 (1 / (Real.sqrt n * eps))) 1000 := by
  obtain ⟨Q, hNI, hFinite, B, x0, x1, hTB, hT0, hT1, hMSE⟩ := hComponents
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
  have htpos : 0 < (n : ℝ) * eps ^ 2 := mul_pos hn (sq_pos_of_pos hAllowed.2.2.1)
  have hspos : 0 < Real.sqrt n * eps :=
    mul_pos (Real.sqrt_pos.mpr hn) hAllowed.2.2.1
  have hssq : (Real.sqrt n * eps)^2 = (n : ℝ) * eps ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hn.le]
  have hs : 1 < Real.sqrt n * eps := by nlinarith
  have hr : min 1 (1 / ((n : ℝ) * eps ^ 2)) = 1 / ((n : ℝ) * eps ^ 2) :=
    min_eq_right ((div_le_one htpos).mpr ht.le)
  have hh : min 1 (1 / (Real.sqrt n * eps)) = 1 / (Real.sqrt n * eps) :=
    min_eq_right ((div_le_one hspos).mpr hs.le)
  rw [hr, hh]
  refine ⟨Q, hNI, twoCellEstimator Q B x0 x1, twoCellInterval eps Q B x0 x1,
    twoCellEstimator_transcriptOnly Q B x0 x1 hTB hT0 hT1, ?_⟩
  intro P hP
  letI := hP.1
  haveI := sampling_decisionLaw_probability S hIID hRandom Q P hP.2
  obtain ⟨hB, hx0, hx1⟩ := hMSE P hP
  have hRisk := two_cell_risk_of_component_mse eps hAllowed Q (decisionLaw S Q P)
    B x0 x1 P hP.2 hB hx0 hx1
  refine ⟨hRisk.trans (ENNReal.ofReal_le_ofReal ?_),
    twoCellInterval_coverage_of_risk eps hAllowed Q B x0 x1 _ (value P)
      (causal_value_range P hP.2 (by norm_num)) hRisk,
    (twoCellInterval_expectedLength_le eps hAllowed Q B x0 x1 _).trans
      (ENNReal.ofReal_le_ofReal ?_)⟩
  · calc
      88 / ((n : ℝ) * eps ^ 2) ≤ 1000 / ((n : ℝ) * eps ^ 2) :=
        (div_le_div_iff_of_pos_right htpos).mpr (by norm_num)
      _ = _ := by ring
  · calc
      200 / (Real.sqrt n * eps) ≤ 1000 / (Real.sqrt n * eps) :=
        (div_le_div_iff_of_pos_right hspos).mpr (by norm_num)
      _ = _ := by ring

end CausalSmith.Stat.LdpOptvalueUniformFrontier

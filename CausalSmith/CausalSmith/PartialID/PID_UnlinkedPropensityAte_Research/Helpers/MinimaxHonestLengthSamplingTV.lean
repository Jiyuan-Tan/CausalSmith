module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.MinimaxHonestLengthSamplingPair

/-! Product total-variation bound for the arbitrary-score sampling pair. -/

public section

open MeasureTheory

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,g,hg,hOverlap,p,q,hp0,hp1,hq0,hq1,n), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSampling_productReleased_tv_le_latent {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (hOverlap : Overlap ε)
    (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    Causalean.Stat.tvDist
      (Measure.pi (fun _ : Fin n =>
        releasedLaw (directSamplingFullLaw H g p)))
      (Measure.pi (fun _ : Fin n =>
        releasedLaw (directSamplingFullLaw H g q))) ≤
    Causalean.Stat.tvDist
      (Measure.pi (fun _ : Fin n =>
        (trialOutcomeLaw p).prod (samplingDesignLaw H g)))
      (Measure.pi (fun _ : Fin n =>
        (trialOutcomeLaw q).prod (samplingDesignLaw H g))) := by
  let f : OutcomeSpace × (LabelSpace K × ArmSpace) → Observation K :=
    samplingReadout
  have hf : Measurable f := samplingReadout_measurable
  let _ : IsProbabilityMeasure (samplingDesignLaw H g) :=
    samplingDesignLaw_isProbabilityMeasure H g hg hOverlap
  let _ : IsProbabilityMeasure (trialOutcomeLaw p) :=
    trialOutcomeLaw_isProbabilityMeasure p hp0 hp1
  let _ : IsProbabilityMeasure (trialOutcomeLaw q) :=
    trialOutcomeLaw_isProbabilityMeasure q hq0 hq1
  have hmap (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
      Measure.pi (fun _ : Fin n =>
          releasedLaw (directSamplingFullLaw H g r)) =
        (Measure.pi (fun _ : Fin n =>
          (trialOutcomeLaw r).prod (samplingDesignLaw H g))).map
            (fun z i => f (z i)) := by
    let _ : IsProbabilityMeasure (trialOutcomeLaw r) :=
      trialOutcomeLaw_isProbabilityMeasure r hr0 hr1
    rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
    simp only [directSamplingFullLaw_releasedLaw H g hg r hr0 hr1]
    rfl
  rw [hmap p hp0 hp1, hmap q hq0 hq1]
  exact trialReadout_tv_le _ _ _
    (measurable_pi_lambda _ fun _ => hf.comp (measurable_pi_apply _))

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,H,g,hg,hOverlap,u,hu,n), this result [establishes the stated mathematical conclusion](goal). -/
lemma directSampling_productReleased_tv_bound {ε : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (hOverlap : Overlap ε)
    (u : ℝ) (hu : |u| < 1 / 2) (n : ℕ) :
    Causalean.Stat.tvDist
      (Measure.pi (fun _ : Fin n => releasedLaw
        (directSamplingFullLaw H g (1 / 2 + u))))
      (Measure.pi (fun _ : Fin n => releasedLaw
        (directSamplingFullLaw H g (1 / 2)))) ≤
      (1 / 2 : ℝ) * Real.sqrt ((1 + 4 * u ^ 2) ^ n - 1) := by
  have hub := abs_lt.mp hu
  let ρ := samplingDesignLaw H g
  let μ := (trialOutcomeLaw (1 / 2 + u)).prod ρ
  let ν := (trialOutcomeLaw (1 / 2)).prod ρ
  let _ : IsProbabilityMeasure (trialOutcomeLaw (1 / 2 + u)) :=
    trialOutcomeLaw_isProbabilityMeasure _ (by linarith) (by linarith)
  let _ : IsProbabilityMeasure (trialOutcomeLaw (1 / 2)) :=
    trialOutcomeLaw_isProbabilityMeasure _ (by norm_num) (by norm_num)
  let _ : IsProbabilityMeasure ρ :=
    samplingDesignLaw_isProbabilityMeasure H g hg hOverlap
  have h := trialOutcomeLaw_ac_integrable_center u
  have hac : μ ≪ ν := h.1.prod (Measure.AbsolutelyContinuous.refl ρ)
  have hint : Integrable
      (fun z => ((μ.rnDeriv ν z).toReal - 1) ^ 2) ν :=
    trial_ancillary_integrable _ _ ρ h.1 h.2
  calc
    _ ≤ Causalean.Stat.tvDist
        (Measure.pi (fun _ : Fin n => μ))
        (Measure.pi (fun _ : Fin n => ν)) :=
      directSampling_productReleased_tv_le_latent H g hg hOverlap
        (1 / 2 + u) (1 / 2) (by linarith) (by linarith)
        (by norm_num) (by norm_num) n
    _ ≤ (1 / 2 : ℝ) *
        Real.sqrt ((1 + Causalean.Stat.chiSqDiv μ ν) ^ n - 1) :=
      trialProduct_tv_le_of_chisq μ ν hac hint n
    _ = _ := by
      change (1 / 2 : ℝ) * Real.sqrt
          ((1 + Causalean.Stat.chiSqDiv
            ((trialOutcomeLaw (1 / 2 + u)).prod ρ)
            ((trialOutcomeLaw (1 / 2)).prod ρ)) ^ n - 1) = _
      rw [Causalean.Stat.chiSqDiv_prod_ancillary
        (trialOutcomeLaw (1 / 2 + u)) (trialOutcomeLaw (1 / 2)) ρ h.1 h.2]
      rw [trialOutcomeLaw_chisq_center u hu]

end
end CausalSmith.PartialID.UnlinkedPropensityAte

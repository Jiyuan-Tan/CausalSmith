module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.MinimaxHonestLengthFiniteLabel

/-! Outer-infimum finite-label lower bounds for honest confidence intervals. -/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:n,K), [this definition](goal) introduces the corresponding object. -/
def fullATEIntervalProcedure (n K : ℕ) : IntervalProcedure n K where
  lo := fun _ => -1
  hi := fun _ => 1
  measurable_lo := measurable_const
  measurable_hi := measurable_const
  lower_bound := fun _ => le_rfl
  ordered := fun _ => by norm_num
  upper_bound := fun _ => le_rfl

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,P), this result [establishes the stated mathematical conclusion](goal). -/
lemma ate_mem_Icc_of_probability {ε : ℝ} {K : ℕ}
    (P : Measure (FullRow ε K)) [IsProbabilityMeasure P] :
    ate P ∈ Icc (-1 : ℝ) 1 := by
  let d : FullRow ε K → ℝ := fun ω => (outcome1 ω : ℝ) - (outcome0 ω : ℝ)
  have hdMeas : Measurable d := by
    dsimp [d]
    unfold outcome1 outcome0
    fun_prop
  have hdBounds (ω : FullRow ε K) : -1 ≤ d ω ∧ d ω ≤ 1 := by
    have h0 := (outcome0 ω).property
    have h1 := (outcome1 ω).property
    change 0 ≤ (outcome0 ω : ℝ) ∧ (outcome0 ω : ℝ) ≤ 1 at h0
    change 0 ≤ (outcome1 ω : ℝ) ∧ (outcome1 ω : ℝ) ≤ 1 at h1
    dsimp [d]
    constructor <;> linarith
  have hdInt : Integrable d P := by
    apply Integrable.of_bound hdMeas.aestronglyMeasurable 1
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact abs_le.mpr (hdBounds ω)
  have hlower := integral_mono (integrable_const (-1 : ℝ)) hdInt
    (fun ω => (hdBounds ω).1)
  have hupper := integral_mono hdInt (integrable_const (1 : ℝ))
    (fun ω => (hdBounds ω).2)
  constructor
  · simpa [ate, d, probReal_univ] using hlower
  · simpa [ate, d, probReal_univ] using hupper

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,n,H,g,hg,α,hα), this result [establishes the stated mathematical conclusion](goal). -/
lemma fullATEIntervalProcedure_honest {ε : ℝ} {K n : ℕ}
    (H : Measure (ScoreSpace ε))
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (α : ℝ) (hα : 0 ≤ α) :
    (g, fullATEIntervalProcedure n K) ∈ honestProcedures n K H α := by
  refine ⟨hg, ?_⟩
  intro P hP
  let _ : IsProbabilityMeasure P := hP.1
  let _ : IsProbabilityMeasure (releasedLaw P) :=
    @Measure.isProbabilityMeasure_map _ _ _ _ P hP.1 _
      (by
        exact (by
          unfold releasedRecord label arm observed
          fun_prop : Measurable (releasedRecord (ε := ε) (J := K))).aemeasurable)
  let _ : IsProbabilityMeasure
      (Measure.pi (fun _ : Fin n => releasedLaw P)) := inferInstance
  have hate := ate_mem_Icc_of_probability P
  have hevent :
      {x | (fullATEIntervalProcedure n K).contains x (ate P)} = Set.univ := by
    ext x
    simp [IntervalProcedure.contains, fullATEIntervalProcedure, hate.1, hate.2]
  rw [hevent, probReal_univ]
  linarith

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,mf,α,hOverlap,hα,hmf,H,f,hDensity,n,K,_hn,hK), this result [establishes the stated mathematical conclusion](goal). -/
lemma minimaxHonestLength_finiteLabel_lower {ε mf α : ℝ}
    (hOverlap : Overlap ε) (hα : 0 < α ∧ α < 1 / 2)
    (hmf : 0 < mf)
    (H : Measure (ScoreSpace ε)) (f : ScoreSpace ε → ℝ)
    [IsProbabilityMeasure H] (hDensity : LowerScoreDensity H f mf)
    (n K : ℕ) (_hn : 0 < n) (hK : 0 < K) :
    (1 - 2 * α) * mf * (1 - 2 * ε) ^ 2 /
        (2 * (1 - ε) * K) ≤ minimaxHonestLength n K H α := by
  let V : Set ℝ := {v : ℝ | ∃ gC ∈ honestProcedures n K H α,
    v = sSup {u : ℝ | ∃ P ∈ CausalLaws H gC.1,
      u = ∫ x, gC.2.length x
        ∂(Measure.pi (fun _ : Fin n => releasedLaw P))}}
  have hVne : V.Nonempty := by
    let r0 : LabelSpace K := ⟨0, hK⟩
    let g0 : ScoreSpace ε → LabelSpace K := fun _ => r0
    let C0 := fullATEIntervalProcedure n K
    have hg0 : Measurable g0 := measurable_const
    have hC0 : (g0, C0) ∈ honestProcedures n K H α :=
      fullATEIntervalProcedure_honest H g0 hg0 α hα.1.le
    exact ⟨sSup {u : ℝ | ∃ P ∈ CausalLaws H g0,
      u = ∫ x, C0.length x
        ∂(Measure.pi (fun _ : Fin n => releasedLaw P))},
      ⟨(g0, C0), hC0, rfl⟩⟩
  unfold minimaxHonestLength
  change _ ≤ sInf V
  apply le_csInf hVne
  rintro v ⟨gC, hgC, rfl⟩
  have hlower := honestProcedure_finiteLabel_expectedLength_lower
    mf hOverlap hmf K hK H f hDensity n α hα.2.le
    gC.1 gC.2 hgC.1 hgC
  calc
    (1 - 2 * α) * mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε) * K) =
        (1 - 2 * α) *
          (mf * (1 - 2 * ε) ^ 2 / (2 * (1 - ε) * K)) := by ring
    _ ≤ _ := hlower

end
end CausalSmith.PartialID.UnlinkedPropensityAte

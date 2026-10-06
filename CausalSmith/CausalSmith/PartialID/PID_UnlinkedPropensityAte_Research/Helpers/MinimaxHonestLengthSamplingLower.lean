module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.MinimaxHonestLengthFiniteLabelOuter
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.MinimaxHonestLengthSamplingTV

/-! Fixed-score sampling lower bound for honest interval length. -/

public section

open MeasureTheory Set

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,n,H,g,C,hOverlap,hg,α,hα,hn,hHonest), this result [establishes the stated mathematical conclusion](goal). -/
lemma honestProcedure_sampling_baseline_expectedLength_lower
    {ε : ℝ} {K n : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (C : IntervalProcedure n K)
    (hOverlap : Overlap ε) (hg : Measurable g)
    (α : ℝ) (hα : 0 < α ∧ α < 1 / 2) (hn : 0 < n)
    (hHonest : (g, C) ∈ honestProcedures n K H α) :
    let P₀ := directSamplingFullLaw H g (1 / 2)
    trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ ≤
      ∫ x, C.length x
        ∂(Measure.pi (fun _ : Fin n => releasedLaw P₀)) := by
  dsimp
  let β : ℝ := 1 - 2 * α
  let u : ℝ := Real.sqrt (Real.log (1 + β ^ 2) / (n : ℝ)) / 2
  let P₀ := directSamplingFullLaw H g (1 / 2)
  let P₁ := directSamplingFullLaw H g (1 / 2 + u)
  let Q₀ := Measure.pi (fun _ : Fin n => releasedLaw P₀)
  let Q₁ := Measure.pi (fun _ : Fin n => releasedLaw P₁)
  have hcal := trial_calibrated_perturbation α hα n hn
  change 0 < u ∧ |u| < 1 / 2 ∧
    (1 + 4 * u ^ 2) ^ n ≤ 1 + β ^ 2 at hcal
  rcases hcal with ⟨hu0, hu, hpow⟩
  have hub := abs_lt.mp hu
  have hP0 : P₀ ∈ CausalLaws H g := by
    dsimp [P₀]
    exact directSamplingFullLaw_mem_causalLaws H g hg hOverlap (1 / 2)
      (by norm_num) (by norm_num)
  have hP1 : P₁ ∈ CausalLaws H g := by
    dsimp only [P₁]
    exact directSamplingFullLaw_mem_causalLaws H g hg hOverlap _
      (by linarith) (by linarith)
  let _ : IsProbabilityMeasure P₀ := hP0.1
  let _ : IsProbabilityMeasure P₁ := hP1.1
  let _ : IsProbabilityMeasure (releasedLaw P₀) :=
    @Measure.isProbabilityMeasure_map _ _ _ _ P₀ hP0.1 _
      (by
        exact (by
          unfold releasedRecord label arm observed
          fun_prop : Measurable (releasedRecord (ε := ε) (J := K))).aemeasurable)
  let _ : IsProbabilityMeasure (releasedLaw P₁) :=
    @Measure.isProbabilityMeasure_map _ _ _ _ P₁ hP1.1 _
      (by
        exact (by
          unfold releasedRecord label arm observed
          fun_prop : Measurable (releasedRecord (ε := ε) (J := K))).aemeasurable)
  let _ : IsProbabilityMeasure Q₀ := inferInstance
  let _ : IsProbabilityMeasure Q₁ := inferInstance
  have hate0 : ate P₀ = 1 / 2 := by
    dsimp [P₀]
    exact directSamplingFullLaw_ate H g hg hOverlap (1 / 2)
      (by norm_num) (by norm_num)
  have hate1 : ate P₁ = 1 / 2 + u := by
    dsimp [P₁]
    exact directSamplingFullLaw_ate H g hg hOverlap (1 / 2 + u)
      (by linarith) (by linarith)
  have hcover0 : 1 - α ≤ Q₀.real {x | C.contains x (1 / 2)} := by
    rw [← hate0]
    exact hHonest.2 P₀ hP0
  have hcover1 : 1 - α ≤ Q₁.real {x | C.contains x (1 / 2 + u)} := by
    rw [← hate1]
    exact hHonest.2 P₁ hP1
  have htv : Causalean.Stat.tvDist Q₀ Q₁ ≤
      (1 / 2 : ℝ) * Real.sqrt ((1 + 4 * u ^ 2) ^ n - 1) := by
    rw [Causalean.Stat.tvDist_symm]
    dsimp [Q₀, Q₁, P₀, P₁]
    exact directSampling_productReleased_tv_bound H g hg hOverlap u hu n
  have hβ0 : 0 < β := by dsimp [β]; linarith [hα.2]
  have htvhalf : Causalean.Stat.tvDist Q₀ Q₁ ≤ β / 2 := by
    calc
      _ ≤ (1 / 2 : ℝ) * Real.sqrt ((1 + 4 * u ^ 2) ^ n - 1) := htv
      _ ≤ (1 / 2 : ℝ) * Real.sqrt (β ^ 2) := by
        apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
        linarith
      _ = β / 2 := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hβ0]; ring
  have hlen := intervalProcedure_twoPoint_expectedLength C Q₀ Q₁
    (1 / 2) (1 / 2 + u) α (by linarith) hcover0 hcover1
  have hcoef : β * u / 2 ≤
      u * (1 - 2 * α - Causalean.Stat.tvDist Q₀ Q₁) := by
    dsimp [β] at htvhalf ⊢
    nlinarith [mul_nonneg hu0.le
      (show 0 ≤ 1 - 2 * α - 2 * Causalean.Stat.tvDist Q₀ Q₁ by linarith)]
  have hident := trial_calibrated_coefficient α n
  change β * u / 2 =
    trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ at hident
  rw [← hident]
  change β * u / 2 ≤ ∫ x, C.length x ∂Q₀
  have hlen' : u * (1 - 2 * α - Causalean.Stat.tvDist Q₀ Q₁) ≤
      ∫ x, C.length x ∂Q₀ := by
    convert hlen using 1
    ring
  exact hcoef.trans hlen'

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,n,H,g,C,hOverlap,hg,α,hα,hn,hHonest), this result [establishes the stated mathematical conclusion](goal). -/
lemma honestProcedure_sampling_worstCaseExpectedLength_lower
    {ε : ℝ} {K n : ℕ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (g : ScoreSpace ε → LabelSpace K) (C : IntervalProcedure n K)
    (hOverlap : Overlap ε) (hg : Measurable g)
    (α : ℝ) (hα : 0 < α ∧ α < 1 / 2) (hn : 0 < n)
    (hHonest : (g, C) ∈ honestProcedures n K H α) :
    trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ ≤
      sSup {v : ℝ | ∃ P ∈ CausalLaws H g,
        v = ∫ x, C.length x
          ∂(Measure.pi (fun _ : Fin n => releasedLaw P))} := by
  let P₀ := directSamplingFullLaw H g (1 / 2)
  have hP0 : P₀ ∈ CausalLaws H g := by
    dsimp [P₀]
    exact directSamplingFullLaw_mem_causalLaws H g hg hOverlap (1 / 2)
      (by norm_num) (by norm_num)
  have hlower := honestProcedure_sampling_baseline_expectedLength_lower
    H g C hOverlap hg α hα hn hHonest
  have hBdd : BddAbove {v : ℝ | ∃ P ∈ CausalLaws H g,
      v = ∫ x, C.length x
        ∂(Measure.pi (fun _ : Fin n => releasedLaw P))} := by
    refine ⟨2, ?_⟩
    rintro v ⟨P, hP, rfl⟩
    let _ : IsProbabilityMeasure P := hP.1
    let _ : IsProbabilityMeasure (releasedLaw P) :=
      @Measure.isProbabilityMeasure_map _ _ _ _ P hP.1 _
        (by
          exact (by
            unfold releasedRecord label arm observed
            fun_prop : Measurable (releasedRecord (ε := ε) (J := K))).aemeasurable)
    let _ : IsProbabilityMeasure
        (Measure.pi (fun _ : Fin n => releasedLaw P)) := inferInstance
    exact intervalProcedure_expectedLength_le_two C _
  exact hlower.trans (le_csSup hBdd ⟨P₀, hP0, rfl⟩)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,n,K,hOverlap,hα,H,hn,hK), this result [establishes the stated mathematical conclusion](goal). -/
lemma minimaxHonestLength_sampling_lower {ε α : ℝ} {n K : ℕ}
    (hOverlap : Overlap ε) (hα : 0 < α ∧ α < 1 / 2)
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (hn : 0 < n) (hK : 0 < K) :
    trialCertificate α * (Real.sqrt (n : ℝ))⁻¹ ≤
      minimaxHonestLength n K H α := by
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
  exact honestProcedure_sampling_worstCaseExpectedLength_lower
    H gC.1 gC.2 hOverlap hgC.1 α hα hn hgC

end
end CausalSmith.PartialID.UnlinkedPropensityAte

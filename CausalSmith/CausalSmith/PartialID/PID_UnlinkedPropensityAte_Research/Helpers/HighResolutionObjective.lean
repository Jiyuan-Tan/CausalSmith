module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.HighResolutionCost
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.HighResolutionFiniteInfimum
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.TAllLabelAmbiguity

/-! The fixed-release ambiguity as a finite paired quantization objective. -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,f,g,hg,hOverlap,hfpos,i), this result [establishes the stated mathematical conclusion](goal). -/
lemma highResolutionCellValues_nonempty_bddBelow
    {ε : ℝ} {K : ℕ} (f : ScoreSpace ε → ℝ)
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (hOverlap : Overlap ε) (hfpos : ∀ e, 0 < f e)
    (i : LabelSpace K × Fin 2) :
    let cost : (LabelSpace K × Fin 2) → ℝ → ℝ := fun i z =>
      ∫ x in realScoreCell g i.1,
        highResolutionBeta f i.2 x z * |x - z|
    (independentCenterValues (fun _ => Icc ε (1 - ε)) cost i).Nonempty ∧
      BddBelow (independentCenterValues
        (fun _ => Icc ε (1 - ε)) cost i) := by
  dsimp only
  have hεle : ε ≤ 1 - ε := by linarith [hOverlap.2]
  have hcellMeas : MeasurableSet (realScoreCell g i.1) :=
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image'
      (measurableSet_eq_fun hg measurable_const)
  have hcostNonneg (z : ℝ) (hz : z ∈ Icc ε (1 - ε)) :
      0 ≤ ∫ x in realScoreCell g i.1,
        highResolutionBeta f i.2 x z * |x - z| := by
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict hcellMeas] with x hx
    rcases hx with ⟨e, he, rfl⟩
    exact mul_nonneg
      (le_of_lt (highResolutionBeta_pos hOverlap f hfpos i.2
        (e : ℝ) z e.property hz))
      (abs_nonneg _)
  constructor
  · refine ⟨_, ε, ⟨le_refl _, hεle⟩, rfl⟩
  · refine ⟨0, ?_⟩
    rintro v ⟨z, hz, rfl⟩
    exact hcostNonneg z hz

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,f,g), this result [establishes the stated mathematical conclusion](goal). -/
lemma independentCenterTotalValues_eq_pairedPartitionValues
    {ε : ℝ} {K : ℕ} (f : ScoreSpace ε → ℝ)
    (g : ScoreSpace ε → LabelSpace K) :
    let cost : (LabelSpace K × Fin 2) → ℝ → ℝ := fun i z =>
      ∫ x in realScoreCell g i.1,
        highResolutionBeta f i.2 x z * |x - z|
    independentCenterTotalValues (fun _ => Icc ε (1 - ε)) cost =
      {v : ℝ | ∃ z : Fin K → Fin 2 → ℝ,
        (∀ r s, z r s ∈ Icc ε (1 - ε)) ∧
        v = pairedPartitionCost 2 K (highResolutionBeta f)
          (realScoreCell g) z} := by
  dsimp only
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨fun r s => z (r, s), ?_, ?_⟩
    · intro r s
      exact hz (r, s)
    · simp only [pairedPartitionCost, Fintype.sum_prod_type]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨fun i => z i.1 i.2, ?_, ?_⟩
    · intro i
      exact hz i.1 i.2
    · simp only [pairedPartitionCost, Fintype.sum_prod_type]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,mf,Mf,K,H,f,hDensity,g,hg,hOverlap,_hfcont,hfpos), this result [establishes the stated mathematical conclusion](goal). -/
theorem worstCaseAmbiguity_eq_highResolutionObjective
    {ε mf Mf : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) (f : ScoreSpace ε → ℝ)
    (hDensity : BoundedScoreDensity H f mf Mf)
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g)
    (hOverlap : Overlap ε) (_hfcont : Continuous f)
    (hfpos : ∀ e, 0 < f e) :
    worstCaseAmbiguity H g =
      sInf {v : ℝ | ∃ z : Fin K → Fin 2 → ℝ,
        (∀ r s, z r s ∈ Icc ε (1 - ε)) ∧
        v = pairedPartitionCost 2 K (highResolutionBeta f)
          (realScoreCell g) z} := by
  let _ : IsProbabilityMeasure H := hDensity.probability
  let cost : (LabelSpace K × Fin 2) → ℝ → ℝ := fun i z =>
    ∫ x in realScoreCell g i.1,
      highResolutionBeta f i.2 x z * |x - z|
  have hlocal (i : LabelSpace K × Fin 2) :
      (independentCenterValues (fun _ => Icc ε (1 - ε)) cost i).Nonempty ∧
        BddBelow (independentCenterValues
          (fun _ => Icc ε (1 - ε)) cost i) := by
    simpa only [cost] using
      highResolutionCellValues_nonempty_bddBelow
        f g hg hOverlap hfpos i
  have hεle : ε ≤ 1 - ε := by linarith [hOverlap.2]
  have hassembly :
      sInf (independentCenterTotalValues
        (fun _ : LabelSpace K × Fin 2 => Icc ε (1 - ε)) cost) =
        ∑ i : LabelSpace K × Fin 2,
          sInf (independentCenterValues
            (fun _ => Icc ε (1 - ε)) cost i) :=
    sInf_independentCenterTotalValues_Icc_eq_sum_of_bddBelow
      ε (1 - ε) hεle cost (fun i => (hlocal i).2)
  have hscalar (r : LabelSpace K) :
      cellAbsoluteDeviation H g true r +
          cellAbsoluteDeviation H g false r =
        ∑ s : Fin 2,
          sInf (independentCenterValues
            (fun _ : LabelSpace K × Fin 2 => Icc ε (1 - ε))
            cost (r, s)) := by
    rw [sum_cellAbsoluteDeviation_eq_highResolutionInfs
      H f hDensity g hg r hOverlap hfpos]
    rw [Fin.sum_univ_two]
    change
      sInf {v : ℝ | ∃ z ∈ Icc ε (1 - ε),
        v = ∫ x in realScoreCell g r,
          highResolutionBeta f 1 x z * |x - z|} +
        sInf {v : ℝ | ∃ z ∈ Icc ε (1 - ε),
          v = ∫ x in realScoreCell g r,
            highResolutionBeta f 0 x z * |x - z|} =
      sInf {v : ℝ | ∃ z ∈ Icc ε (1 - ε),
        v = ∫ x in realScoreCell g r,
          highResolutionBeta f 0 x z * |x - z|} +
        sInf {v : ℝ | ∃ z ∈ Icc ε (1 - ε),
          v = ∫ x in realScoreCell g r,
            highResolutionBeta f 1 x z * |x - z|}
    exact add_comm _ _
  rw [(worstCaseAmbiguity_eq H g hOverlap hg).1]
  calc
    (∑ r : LabelSpace K,
        (cellAbsoluteDeviation H g true r +
          cellAbsoluteDeviation H g false r)) =
        ∑ r : LabelSpace K, ∑ s : Fin 2,
          sInf (independentCenterValues
            (fun _ : LabelSpace K × Fin 2 => Icc ε (1 - ε))
            cost (r, s)) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hscalar r
    _ = ∑ i : LabelSpace K × Fin 2,
          sInf (independentCenterValues
            (fun _ => Icc ε (1 - ε)) cost i) := by
      rw [Fintype.sum_prod_type]
    _ = sInf (independentCenterTotalValues
          (fun _ : LabelSpace K × Fin 2 => Icc ε (1 - ε)) cost) :=
      hassembly.symm
    _ = sInf {v : ℝ | ∃ z : Fin K → Fin 2 → ℝ,
          (∀ r s, z r s ∈ Icc ε (1 - ε)) ∧
          v = pairedPartitionCost 2 K (highResolutionBeta f)
            (realScoreCell g) z} := by
      rw [independentCenterTotalValues_eq_pairedPartitionValues f g]

end
end CausalSmith.PartialID.UnlinkedPropensityAte

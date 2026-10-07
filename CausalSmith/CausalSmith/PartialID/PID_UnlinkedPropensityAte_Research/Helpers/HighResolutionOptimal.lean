module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.HighResolutionObjective
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.HighResolutionPartitionRelease

/-! Identification of optimal finite-label ambiguity with paired quantization. -/

public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ι,p,A,hp,hne,hbelow), this result [establishes the stated mathematical conclusion](goal). -/
lemma sInf_feasibleFiberInfs_eq_sInf_feasibleValues
    {ι : Type*} (p : ι → Prop) (A : ι → Set ℝ)
    (hp : ∃ i, p i) (hne : ∀ i, p i → (A i).Nonempty)
    (hbelow : BddBelow {x : ℝ | ∃ i, p i ∧ x ∈ A i}) :
    sInf {v : ℝ | ∃ i, p i ∧ v = sInf (A i)} =
      sInf {x : ℝ | ∃ i, p i ∧ x ∈ A i} := by
  rcases hbelow with ⟨lower, hlower⟩
  have hfiberBelow (i : ι) (hi : p i) : BddBelow (A i) := by
    refine ⟨lower, ?_⟩
    intro x hx
    exact hlower ⟨i, hi, hx⟩
  have hflatBelow : BddBelow {x : ℝ | ∃ i, p i ∧ x ∈ A i} :=
    ⟨lower, hlower⟩
  have hflatNe : {x : ℝ | ∃ i, p i ∧ x ∈ A i}.Nonempty := by
    rcases hp with ⟨i, hi⟩
    rcases hne i hi with ⟨x, hx⟩
    exact ⟨x, i, hi, hx⟩
  have houterNe : {v : ℝ | ∃ i, p i ∧ v = sInf (A i)}.Nonempty := by
    rcases hp with ⟨i, hi⟩
    exact ⟨sInf (A i), i, hi, rfl⟩
  have houterBelow :
      BddBelow {v : ℝ | ∃ i, p i ∧ v = sInf (A i)} := by
    refine ⟨lower, ?_⟩
    rintro v ⟨i, hi, rfl⟩
    apply le_csInf (hne i hi)
    intro x hx
    exact hlower ⟨i, hi, hx⟩
  apply le_antisymm
  · apply le_csInf hflatNe
    rintro x ⟨i, hi, hx⟩
    exact (csInf_le houterBelow ⟨i, hi, rfl⟩).trans
      (csInf_le (hfiberBelow i hi) hx)
  · apply le_csInf houterNe
    rintro v ⟨i, hi, rfl⟩
    apply le_csInf (hne i hi)
    intro x hx
    exact csInf_le hflatBelow ⟨i, hi, hx⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,f,hOverlap,hfpos,B,hB,z,hz), this result [establishes the stated mathematical conclusion](goal). -/
lemma highResolution_pairedPartitionCost_nonneg
    {ε : ℝ} {K : ℕ} (f : ScoreSpace ε → ℝ)
    (hOverlap : Overlap ε) (hfpos : ∀ e, 0 < f e)
    (B : Fin K → Set ℝ) (hB : IsIntervalPartition ε (1 - ε) K B)
    (z : Fin K → Fin 2 → ℝ)
    (hz : ∀ r s, z r s ∈ Icc ε (1 - ε)) :
    0 ≤ pairedPartitionCost 2 K (highResolutionBeta f) B z := by
  unfold pairedPartitionCost
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro s hs
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict (hB.1 r)] with x hx
  have hxIcc : x ∈ Icc ε (1 - ε) := by
    rw [← hB.2.2]
    exact Set.mem_iUnion_of_mem r hx
  exact mul_nonneg
    (le_of_lt (highResolutionBeta_pos hOverlap f hfpos s x (z r s)
      hxIcc (hz r s)))
    (abs_nonneg _)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,f), this result [establishes the stated mathematical conclusion](goal). -/
lemma measurableReleaseValues_eq_intervalPartitionValues
    {ε : ℝ} {K : ℕ} (f : ScoreSpace ε → ℝ) :
    {v : ℝ | ∃ g : ScoreSpace ε → LabelSpace K,
      Measurable g ∧ ∃ z : Fin K → Fin 2 → ℝ,
        (∀ r s, z r s ∈ Icc ε (1 - ε)) ∧
        v = pairedPartitionCost 2 K (highResolutionBeta f)
          (realScoreCell g) z} =
    {v : ℝ | ∃ (B : Fin K → Set ℝ) (z : Fin K → Fin 2 → ℝ),
      IsIntervalPartition ε (1 - ε) K B ∧
        (∀ r s, z r s ∈ Icc ε (1 - ε)) ∧
        v = pairedPartitionCost 2 K (highResolutionBeta f) B z} := by
  ext v
  constructor
  · rintro ⟨g, hg, z, hz, rfl⟩
    exact ⟨realScoreCell g, z, measurableRelease_intervalPartition g hg,
      hz, rfl⟩
  · rintro ⟨B, z, hB, hz, rfl⟩
    let g := intervalPartitionRelease B hB
    refine ⟨g, intervalPartitionRelease_measurable B hB, z, hz, ?_⟩
    unfold g
    have hcells : realScoreCell (intervalPartitionRelease B hB) = B := by
      funext r
      exact realScoreCell_intervalPartitionRelease B hB r
    rw [hcells]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,mf,Mf,K,H,f,hDensity,hOverlap,hfcont,hfpos,hK), this result [establishes the stated mathematical conclusion](goal). -/
theorem optimalKAmbiguity_eq_optimalPairedCost
    {ε mf Mf : ℝ} {K : ℕ}
    (H : Measure (ScoreSpace ε)) (f : ScoreSpace ε → ℝ)
    (hDensity : BoundedScoreDensity H f mf Mf)
    (hOverlap : Overlap ε) (hfcont : Continuous f)
    (hfpos : ∀ e, 0 < f e) (hK : 0 < K) :
    optimalKAmbiguity ε K H =
      optimalPairedCost ε (1 - ε) 2 K (highResolutionBeta f) := by
  let A : (ScoreSpace ε → LabelSpace K) → Set ℝ := fun g =>
    {v : ℝ | ∃ z : Fin K → Fin 2 → ℝ,
      (∀ r s, z r s ∈ Icc ε (1 - ε)) ∧
      v = pairedPartitionCost 2 K (highResolutionBeta f)
        (realScoreCell g) z}
  have hεle : ε ≤ 1 - ε := by linarith [hOverlap.2]
  have hAne (g : ScoreSpace ε → LabelSpace K) : (A g).Nonempty := by
    let z : Fin K → Fin 2 → ℝ := fun _ _ => ε
    refine ⟨pairedPartitionCost 2 K (highResolutionBeta f)
      (realScoreCell g) z, z, ?_, rfl⟩
    intro r s
    exact ⟨le_rfl, hεle⟩
  have hreleaseNe : ∃ g : ScoreSpace ε → LabelSpace K, Measurable g := by
    let r0 : LabelSpace K := ⟨0, hK⟩
    exact ⟨fun _ => r0, measurable_const⟩
  have hflatBelow : BddBelow
      {v : ℝ | ∃ g : ScoreSpace ε → LabelSpace K,
        Measurable g ∧ v ∈ A g} := by
    refine ⟨0, ?_⟩
    rintro v ⟨g, hg, z, hz, rfl⟩
    exact highResolution_pairedPartitionCost_nonneg f hOverlap hfpos
      (realScoreCell g) (measurableRelease_intervalPartition g hg) z hz
  have hflatten :
      sInf {v : ℝ | ∃ g : ScoreSpace ε → LabelSpace K,
        Measurable g ∧ v = sInf (A g)} =
      sInf {v : ℝ | ∃ g : ScoreSpace ε → LabelSpace K,
        Measurable g ∧ v ∈ A g} :=
    sInf_feasibleFiberInfs_eq_sInf_feasibleValues
      (fun g : ScoreSpace ε → LabelSpace K => Measurable g) A
      hreleaseNe (fun g hg => hAne g) hflatBelow
  have houter :
      {d : ℝ | ∃ g ∈ kLabelReleases ε K,
        d = worstCaseAmbiguity H g} =
      {v : ℝ | ∃ g : ScoreSpace ε → LabelSpace K,
        Measurable g ∧ v = sInf (A g)} := by
    ext v
    constructor
    · rintro ⟨g, hg, rfl⟩
      change Measurable g at hg
      refine ⟨g, hg, ?_⟩
      exact worstCaseAmbiguity_eq_highResolutionObjective
        H f hDensity g hg hOverlap hfcont hfpos
    · rintro ⟨g, hg, rfl⟩
      refine ⟨g, ?_, ?_⟩
      · exact hg
      · symm
        exact worstCaseAmbiguity_eq_highResolutionObjective
          H f hDensity g hg hOverlap hfcont hfpos
  unfold optimalKAmbiguity optimalPairedCost
  rw [houter, hflatten]
  change
    sInf {v : ℝ | ∃ g : ScoreSpace ε → LabelSpace K,
      Measurable g ∧ ∃ z : Fin K → Fin 2 → ℝ,
        (∀ r s, z r s ∈ Icc ε (1 - ε)) ∧
        v = pairedPartitionCost 2 K (highResolutionBeta f)
          (realScoreCell g) z} = _
  rw [measurableReleaseValues_eq_intervalPartitionValues f]

end
end CausalSmith.PartialID.UnlinkedPropensityAte

module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.TKLabelRate
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.HighResolutionOptimal
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.HighResolutionOrderedCost

/-! Sharp high-resolution constant and ordered companding releases. -/

@[expose] public section

open MeasureTheory Set Filter
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,H,f,K), [this definition](goal) introduces the corresponding object. -/
def compandingAmbiguity {ε : ℝ} (H : Measure (ScoreSpace ε))
    (f : ScoreSpace ε → ℝ) (K : ℕ) : ℝ :=
  if hK : 0 < K then worstCaseAmbiguity H (compandingRelease f K hK) else 0

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,H,f,hOverlap,hDensity,hfcont,hfpos), this result [establishes the stated mathematical conclusion](goal). -/
lemma exists_boundedScoreDensity_of_continuous {ε : ℝ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (f : ScoreSpace ε → ℝ)
    (hOverlap : Overlap ε)
    (hDensity : H = ((volume : Measure ℝ).comap
      (Subtype.val : ScoreSpace ε → ℝ)).withDensity
        (fun e => ENNReal.ofReal (f e)))
    (hfcont : Continuous f) (hfpos : ∀ e, 0 < f e) :
    ∃ mf Mf : ℝ, BoundedScoreDensity H f mf Mf := by
  have hne : (Set.univ : Set (ScoreSpace ε)).Nonempty :=
    ⟨⟨ε, ⟨le_refl _, by linarith [hOverlap.2]⟩⟩, Set.mem_univ _⟩
  obtain ⟨mf, hmf, hmf_le⟩ :=
    isCompact_univ.exists_forall_le' hfcont.continuousOn
      (fun e _ => hfpos e)
  obtain ⟨Mf, hMf⟩ :=
    isCompact_univ.exists_bound_of_continuousOn hfcont.continuousOn
  refine ⟨mf, Mf, ⟨inferInstance, ?_, ?_⟩⟩
  · refine ⟨hfcont.measurable, hDensity, ?_⟩
    exact Filter.Eventually.of_forall (fun e => hmf_le e (Set.mem_univ e))
  · exact Filter.Eventually.of_forall (fun e =>
      (le_abs_self _).trans (by simpa using hMf e (Set.mem_univ e)))

-- @node: thm:sharp-high-resolution-constant
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,H,f,hDensity,hOverlap,hfcont,hfpos), this result [establishes the stated mathematical conclusion](goal). -/
theorem tendsto_K_mul_optimalKAmbiguity {ε : ℝ}
    (H : Measure (ScoreSpace ε)) [IsProbabilityMeasure H]
    (f : ScoreSpace ε → ℝ)
    (hDensity : H = ((volume : Measure ℝ).comap
      (Subtype.val : ScoreSpace ε → ℝ)).withDensity
        (fun e => ENNReal.ofReal (f e)))
    (hOverlap : Overlap ε)
    (hfcont : Continuous f) (hfpos : ∀ e, 0 < f e) :
    Tendsto (fun K : ℕ => (K : ℝ) * optimalKAmbiguity ε K H)
      atTop (nhds ((1 / 4 : ℝ) *
        (∫ t in ε..(1 - ε),
          Real.sqrt (densityExtension f t / (t * (1 - t)))) ^ 2)) ∧
    (∃ gK : (K : ℕ) → (hK : 0 < K) → ScoreSpace ε → LabelSpace K,
      Tendsto (fun K : ℕ => (K : ℝ) *
        (if hK : 0 < K then worstCaseAmbiguity H (gK K hK) else 0))
        atTop (nhds ((1 / 4 : ℝ) *
          (∫ t in ε..(1 - ε),
            Real.sqrt (densityExtension f t / (t * (1 - t)))) ^ 2)) ∧
      ∀ K (hK : 0 < K),
        Measurable (gK K hK) ∧
        ∀ r : LabelSpace K, ∀ x z : ScoreSpace ε,
          x ∈ cell (gK K hK) r →
          z ∈ cell (gK K hK) r →
          ∀ y : ScoreSpace ε, x ≤ y → y ≤ z →
            y ∈ cell (gK K hK) r) := by
  obtain ⟨mf, Mf, hBounded⟩ :=
    exists_boundedScoreDensity_of_continuous H f hOverlap hDensity hfcont hfpos
  have hab : ε < 1 - ε := by linarith [hOverlap.2]
  have hquant := pairedQuantization_tendsto ε (1 - ε) hab 2 (by norm_num)
    (highResolutionBeta f)
    (highResolutionBeta_continuousOn hOverlap f hfcont)
    (highResolutionBeta_pos hOverlap f hfpos)
  have hdiag :
      (∫ t in ε..(1 - ε),
        Real.sqrt (pairedDiagonalWeight 2 (highResolutionBeta f) t)) =
      ∫ t in ε..(1 - ε),
        Real.sqrt (densityExtension f t / (t * (1 - t))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    change Real.sqrt (pairedDiagonalWeight 2 (highResolutionBeta f) t) =
      Real.sqrt (densityExtension f t / (t * (1 - t)))
    rw [highResolutionBeta_diagonal hOverlap f t]
    simpa only [Set.uIcc_of_le hab.le] using ht
  rw [hdiag] at hquant
  have hoptEq :
      (fun K : ℕ => (K : ℝ) * optimalKAmbiguity ε K H) =ᶠ[atTop]
      (fun K : ℕ => (K : ℝ) *
        optimalPairedCost ε (1 - ε) 2 K (highResolutionBeta f)) := by
    apply (eventually_atTop.2 ⟨1, ?_⟩)
    intro K hK
    change (K : ℝ) * optimalKAmbiguity ε K H =
      (K : ℝ) * optimalPairedCost ε (1 - ε) 2 K (highResolutionBeta f)
    rw [optimalKAmbiguity_eq_optimalPairedCost
      H f hBounded hOverlap hfcont hfpos (Nat.zero_lt_of_lt hK)]
  have hopt :
      Tendsto (fun K : ℕ => (K : ℝ) * optimalKAmbiguity ε K H)
        atTop (nhds ((1 / 4 : ℝ) *
          (∫ t in ε..(1 - ε),
            Real.sqrt (densityExtension f t / (t * (1 - t)))) ^ 2)) :=
    hquant.1.congr' hoptEq.symm
  refine ⟨hopt, ?_⟩
  let gK : (K : ℕ) → (hK : 0 < K) →
      ScoreSpace ε → LabelSpace K := fun K hK =>
    highResolutionOrderedRelease hOverlap f hfcont hfpos K hK
  refine ⟨gK, ?_, ?_⟩
  · let middle : ℕ → ℝ := fun K => (K : ℝ) *
      (if hK : 0 < K then worstCaseAmbiguity H (gK K hK) else 0)
    let upper : ℕ → ℝ := fun K => (K : ℝ) *
      pairedPartitionCost 2 K (highResolutionBeta f)
        (pairedCompandingCell ε (1 - ε) 2 K (highResolutionBeta f))
        (pairedCompandingMidpoint ε (1 - ε) 2 K (highResolutionBeta f))
    have hlower : ∀ K : ℕ,
        (K : ℝ) * optimalKAmbiguity ε K H ≤ middle K := by
      intro K
      by_cases hK : 0 < K
      · simp only [middle, dif_pos hK]
        exact mul_le_mul_of_nonneg_left
          (optimalKAmbiguity_le_highResolutionOrderedRelease
            H hOverlap f hfcont hfpos K hK)
          (Nat.cast_nonneg K)
      · have hK0 : K = 0 := by omega
        subst K
        simp [middle]
    have hupper : ∀ K : ℕ, middle K ≤ upper K := by
      intro K
      by_cases hK : 0 < K
      · simp only [middle, dif_pos hK, upper]
        exact mul_le_mul_of_nonneg_left
          (highResolutionOrderedRelease_worstCaseAmbiguity_le_compandingCost
            H f hBounded hOverlap hfcont hfpos K hK)
          (Nat.cast_nonneg K)
      · have hK0 : K = 0 := by omega
        subst K
        simp [middle, upper]
    exact hopt.squeeze hquant.2.1 hlower hupper
  · intro K hK
    refine ⟨highResolutionOrderedRelease_measurable
      hOverlap f hfcont hfpos K hK, ?_⟩
    intro r x z hx hz y hxy hyz
    exact (highResolutionOrderedRelease_cell_ordConnected
      hOverlap f hfcont hfpos K hK r).out hx hz ⟨hxy, hyz⟩

end
end CausalSmith.PartialID.UnlinkedPropensityAte

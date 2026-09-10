import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.Certificate

/-! # Canonical representatives of Gaussian quotient balls -/

open scoped BigOperators
open MeasureTheory Filter Set

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section
open Classical

/-- Canonical reference-arm representatives of a closed quotient ball. -/
def canonicalFaceRepresentatives [NeZero K] (S : Finset (Fin K)) (M : ℝ) :
    Set (Fin K → ℝ) :=
  {h | quotientNorm S h ≤ M ∧ h (referenceArm S) = 0 ∧
    ∀ k, k ∉ S → h k = 0}

-- @node: canonicalFaceRepresentatives_cover
/-- The canonical representatives form a compact set and cover exactly the
closed quotient ball emitted by the reference-contrast construction. -/
lemma canonicalFaceRepresentatives_cover [NeZero K] (S : Finset (Fin K))
    (hS : S.Nonempty) (M : ℝ) (hM : 0 ≤ M) :
    IsCompact (canonicalFaceRepresentatives S M) ∧
      ExactQuotientBallRepresentativeCoverage S M
        (canonicalFaceRepresentatives S M) := by
  have href : referenceArm S ∈ S := by
    simp only [referenceArm, dif_pos hS]
    exact S.min'_mem hS
  let lift : (QuotientIndex S → ℝ) → (Fin K → ℝ) := fun g k =>
    if hk : k ∈ S then
      if hkr : k ≠ referenceArm S then g ⟨k, hk, hkr⟩ else 0
    else 0
  have hlift_ref (g : QuotientIndex S → ℝ) : lift g (referenceArm S) = 0 := by
    simp [lift, href]
  have hlift_out (g : QuotientIndex S → ℝ) (k : Fin K) (hk : k ∉ S) :
      lift g k = 0 := by simp [lift, hk]
  have hlift_contrast (g : QuotientIndex S → ℝ) (k : QuotientIndex S) :
      contrastCoordinate S (lift g) k.1 = g k := by
    simp [contrastCoordinate, lift, k.2.1, k.2.2, href]
  have hsum_lift (g : QuotientIndex S → ℝ) :
      ∑ k ∈ S, (contrastCoordinate S (lift g) k) ^ 2 = ∑ i, (g i) ^ 2 := by
    calc
      _ = ∑ k ∈ S.filter (fun k => k ≠ referenceArm S),
          (contrastCoordinate S (lift g) k) ^ 2 := by
            symm
            apply Finset.sum_filter_of_ne
            intro k hkS hne
            by_contra hk
            subst k
            simp [contrastCoordinate] at hne
      _ = ∑ i : QuotientIndex S, (contrastCoordinate S (lift g) i.1) ^ 2 := by
            apply Finset.sum_subtype
            intro k
            simp
      _ = _ := by simp [hlift_contrast]
  constructor
  · let ball : Set (QuotientIndex S → ℝ) := {g | ∑ i, (g i) ^ 2 ≤ M ^ 2}
    have hball_closed : IsClosed ball := by
      apply isClosed_le
      · fun_prop
      · fun_prop
    have hball_bounded : Bornology.IsBounded ball := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨M, ?_⟩
      intro g hg
      rw [pi_norm_le_iff_of_nonneg hM]
      intro i
      rw [Real.norm_eq_abs]
      apply (sq_le_sq₀ (abs_nonneg _) hM).mp
      rw [sq_abs]
      exact le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (g j))
        (Finset.mem_univ i)) hg
    have hball_compact : IsCompact ball :=
      Metric.isCompact_of_isClosed_isBounded hball_closed hball_bounded
    have hlift_cont : Continuous lift := by
      apply continuous_pi
      intro k
      dsimp [lift]
      split_ifs <;> fun_prop
    have himage : lift '' ball = canonicalFaceRepresentatives S M := by
      apply Set.ext
      intro h
      constructor
      · rintro ⟨g, hg, rfl⟩
        refine ⟨?_, hlift_ref g, hlift_out g⟩
        rw [quotientNorm, hsum_lift]
        exact (Real.sqrt_le_iff).2 ⟨hM, hg⟩
      · intro hh
        let g : QuotientIndex S → ℝ := fun i => contrastCoordinate S h i.1
        refine ⟨g, ?_, ?_⟩
        · change (∑ i : QuotientIndex S, (contrastCoordinate S h i.1) ^ 2) ≤ M ^ 2
          have hsum : ∑ i : QuotientIndex S, (contrastCoordinate S h i.1) ^ 2 =
              ∑ k ∈ S, (contrastCoordinate S h k) ^ 2 := by
            symm
            calc
              _ = ∑ k ∈ S.filter (fun k => k ≠ referenceArm S),
                  (contrastCoordinate S h k) ^ 2 := by
                    symm
                    apply Finset.sum_filter_of_ne
                    intro k hkS hne
                    by_contra hk
                    subst k
                    simp [contrastCoordinate] at hne
              _ = _ := by
                    apply Finset.sum_subtype
                    intro k
                    simp
          rw [hsum]
          have hq := hh.1
          rw [quotientNorm] at hq
          have hn : 0 ≤ ∑ k ∈ S, (contrastCoordinate S h k) ^ 2 := by positivity
          have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) hM).2 hq
          simpa [Real.sq_sqrt hn] using hsquare
        · funext k
          by_cases hk : k ∈ S
          · by_cases hkr : k ≠ referenceArm S
            · simp [lift, g, hk, hkr, contrastCoordinate, hh.2.1]
            · simp only [not_ne_iff] at hkr
              subst k
              simp [lift, href, hh.2.1]
          · simp [lift, hk, hh.2.2 k hk]
    rw [← himage]
    exact hball_compact.image hlift_cont
  · apply Set.ext
    intro g
    constructor
    · rintro ⟨h, hh, rfl⟩
      change (∑ i, (quotientObservation S (fun k => h k.1) i) ^ 2) ≤ M ^ 2
      have hq : quotientNorm S h ≤ M := hh.1
      have hobs (i : QuotientIndex S) :
          quotientObservation S (fun k => h k.1) i = contrastCoordinate S h i.1 := by
        simp [quotientObservation, activeReferenceValue, contrastCoordinate, href]
      rw [show (∑ i : QuotientIndex S,
          (quotientObservation S (fun k => h k.1) i) ^ 2) =
          ∑ i : QuotientIndex S, (contrastCoordinate S h i.1) ^ 2 by simp [hobs]]
      have hsum : ∑ i : QuotientIndex S, (contrastCoordinate S h i.1) ^ 2 =
          ∑ k ∈ S, (contrastCoordinate S h k) ^ 2 := by
        symm
        calc
          _ = ∑ k ∈ S.filter (fun k => k ≠ referenceArm S),
              (contrastCoordinate S h k) ^ 2 := by
                symm
                apply Finset.sum_filter_of_ne
                intro k hkS hne
                by_contra hk
                subst k
                simp [contrastCoordinate] at hne
          _ = _ := by
                apply Finset.sum_subtype
                intro k
                simp
      rw [hsum]
      have hnonneg : 0 ≤ ∑ k ∈ S, (contrastCoordinate S h k) ^ 2 := by positivity
      rw [quotientNorm] at hq
      have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) hM).2 hq
      simpa [Real.sq_sqrt hnonneg] using hsquare
    · intro hg
      refine ⟨lift g, ?_, ?_⟩
      · refine ⟨?_, hlift_ref g, hlift_out g⟩
        rw [quotientNorm, hsum_lift]
        exact (Real.sqrt_le_iff).2 ⟨hM, hg⟩
      · funext i
        calc
          g i = contrastCoordinate S (lift g) i.1 := (hlift_contrast g i).symm
          _ = quotientObservation S (fun k => lift g k.1) i := by
            simp [quotientObservation, activeReferenceValue, contrastCoordinate, href]

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

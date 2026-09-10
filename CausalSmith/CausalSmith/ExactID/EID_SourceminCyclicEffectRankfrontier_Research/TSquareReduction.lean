import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.TSharpEffectFrontier

/-!
# Square LiNG-D reduction
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open MeasureTheory Set

universe u

noncomputable def squareCandidates {p : ℕ} (C : SquareMatrix p) (x : Fin p) :
    Set (SquareMatrix p × SquareMatrix p) :=
  {M | M ∈ liNGDCandidateOutput.{u} C⁻¹ ∧
    CompletionFiber C (le_refl p) x M.1 M.2}

lemma inverseDiagonalMatrix_mul_rowPermutationMatrix {n : ℕ} (W : SquareMatrix n)
    (pi : Equiv.Perm (Fin n)) (d : Fin n → ℝ) (hd : d = fun i => W (pi i) i) :
    inverseDiagonalMatrix d * rowPermutationMatrix pi = rowPermuteAssignment W pi := by
  ext i k
  simp only [inverseDiagonalMatrix, rowPermutationMatrix, rowPermuteAssignment,
    Matrix.mul_apply, Matrix.diagonal_apply, hd]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

lemma rowPermuteAssignment_mul_eq_rowPermuteNormalize {n : ℕ} (W : SquareMatrix n)
    (pi : Equiv.Perm (Fin n)) :
    rowPermuteAssignment W pi * W = rowPermuteNormalize W pi := by
  ext i k
  simp only [rowPermuteAssignment, rowPermuteNormalize, Matrix.mul_apply]
  rw [Finset.sum_eq_single (pi i)]
  · simp [div_eq_inv_mul]
  · intro j _ hji
    simp [show pi i ≠ j from Ne.symm hji]
  · simp

-- @node: thm:square-reduction
theorem square_reduction {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (C : SquareMatrix p) (ε : Fin p → Ω → ℝ)
    (hp : 2 ≤ p) (x y : Fin p) (hy : y ≠ x)
    (hC : FullRowRank C) (hC0 : NonzeroColumns C) (hCdir : DistinctDirections C)
    (hind : ProbabilityTheory.iIndepFun ε μ) (hnd : NondegenerateSources μ ε)
    (hng : NonGaussianSources μ ε)
    (LacerdaSquareRowPermutation_of_gate : LacerdaSquareRowPermutation.{u})
    (LacerdaDistributionEntailmentEquivalence_of_gate :
      LacerdaDistributionEntailmentEquivalence.{u}) :
    latentIndices p p = ∅ ∧
    {theta | ∃ M ∈ squareCandidates.{u} C x,
      ∃ hM : CompletionFiber C (le_refl p) x M.1 M.2,
        theta = equilibriumEffect C (le_refl p) x ⟨y, hy⟩ M.1 M.2 hM} =
      effectFrontier C x y := by
  have hrows : LinearIndependent ℝ C.row := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    rw [Set.finrank, ← Matrix.rank_eq_finrank_span_row, hC]
    simp
  have hCdet : C.det ≠ 0 := by
    have hunit : IsUnit C := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det C).mp hunit)
  have hCinv : C⁻¹⁻¹ = C :=
    Matrix.nonsing_inv_nonsing_inv C ((isUnit_iff_ne_zero).2 hCdet)
  have hqual : QualitativelyNondegenerateSources μ ε := by
    refine ⟨hnd.1, hnd.2.1, ?_⟩
    intro j
    rintro ⟨c, hc⟩
    have hv := ProbabilityTheory.variance_id_map (hnd.2.1 j)
    rw [hc, ProbabilityTheory.variance_dirac] at hv
    linarith [hnd.2.2 j]
  have hW : IsSquareICAUnmixing.{u} C⁻¹ := by
    constructor
    · rw [Matrix.det_nonsing_inv]
      simpa using hCdet
    · refine ⟨Ω, inferInstance, μ, ε, ?_⟩
      simpa only [hCinv] using
        (show IsIrreducibleICARepresentation μ C ε (observedLaw μ C ε) from
          ⟨le_rfl, hnd.1, hnd.2.1, hC0, hCdir, hind, hqual, hng, rfl⟩)
  constructor
  · ext k
    simp [latentIndices]
  · ext theta
    constructor
    · rintro ⟨M, ⟨_hLiNGD, hM⟩, _hM', rfl⟩
      let j := assignedSource M.2 hM.monomial x
      have hj := assignedSource_mem_admissibleSources C (le_refl p) x M.1 M.2 hM
      refine ⟨j, hj, ?_⟩
      simpa [j, Subsingleton.elim _hM' hM] using
        (interventionRatio C (le_refl p) x ⟨y, hy⟩ M.1 M.2 hM).2
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨D, hcert⟩ := certifiedCompletion_mem_fiber C x ⟨hp, le_rfl⟩ hC
      let Q := (certifiedCompletion C x D j hj).1
      let H := (certifiedCompletion C x D j hj).2
      have hF : CompletionFiber C (le_refl p) x Q H := by
        simpa [Q, H] using (hcert j hj).2.2.1
      let tr := D.trace ⟨j, hj⟩
      have hT : D.basisExtension = C := by
        ext i k
        simpa using D.observedRows i k
      have hW0 : D.inverseBasis = C⁻¹ := by
        rw [D.inverse_eq, hT]
      have hnone : tr.shearRow = none := by
        cases hs : tr.shearRow with
        | none => rfl
        | some ell =>
            exfalso
            exact (Nat.not_lt_of_ge ell.property ell.1.isLt)
      have hnoshear := tr.noShear_spec (tr.noShear_iff.mp hnone)
      have htrQ : Q = tr.Q := by
        simpa [Q, certifiedCompletion] using (hcert j hj).1.symm
      have htrH : H = tr.H := by
        simpa [H, certifiedCompletion] using (hcert j hj).2.1.symm
      have hsInv : tr.shearedInverse = C⁻¹ := hnoshear.2.trans hW0
      have hdformula : tr.diagonal = fun i => C⁻¹ (tr.flippedAssignment i) i := by
        rw [tr.diagonal_spec]
        funext i
        rw [hsInv]
        simp [rowPermutationMatrix, Matrix.mul_apply]
      have hdiag : ∀ i, C⁻¹ (tr.flippedAssignment i) i ≠ 0 := by
        intro i
        have hi := tr.diagonal_nonzero i
        rw [congrFun hdformula i] at hi
        exact hi
      have hQ : Q = rowPermuteNormalize C⁻¹ tr.flippedAssignment := by
        calc
          Q = inverseDiagonalMatrix tr.diagonal * rowPermutationMatrix tr.flippedAssignment *
              tr.shearedInverse := htrQ.trans tr.Q_formula
          _ = inverseDiagonalMatrix tr.diagonal * rowPermutationMatrix tr.flippedAssignment *
              C⁻¹ := by rw [hsInv]
          _ = rowPermuteAssignment C⁻¹ tr.flippedAssignment * C⁻¹ := by
            rw [inverseDiagonalMatrix_mul_rowPermutationMatrix C⁻¹ tr.flippedAssignment
              tr.diagonal hdformula]
          _ = rowPermuteNormalize C⁻¹ tr.flippedAssignment :=
            rowPermuteAssignment_mul_eq_rowPermuteNormalize C⁻¹ tr.flippedAssignment
      have hH : H = rowPermuteAssignment C⁻¹ tr.flippedAssignment := by
        calc
          H = inverseDiagonalMatrix tr.diagonal * rowPermutationMatrix tr.flippedAssignment :=
            htrH.trans tr.H_formula
          _ = rowPermuteAssignment C⁻¹ tr.flippedAssignment := by
            exact inverseDiagonalMatrix_mul_rowPermutationMatrix C⁻¹ tr.flippedAssignment
              tr.diagonal hdformula
      have hLiNGD : (Q, H) ∈ liNGDCandidateOutput.{u} C⁻¹ := by
        refine ⟨hW, tr.flippedAssignment, hdiag, ?_⟩
        rw [Prod.ext_iff]
        exact ⟨hQ, hH⟩
      refine ⟨(Q, H), ⟨hLiNGD, hF⟩, hF, ?_⟩
      have hassigned : assignedSource H hF.monomial x = j := by
        change assignedSource (D.completion ⟨j, hj⟩).2 hF.monomial x = j
        have hcast : Fin.castLE D.dim_le x = x := Fin.ext rfl
        simpa only [hcast,
          Subsingleton.elim hF.monomial (D.valid ⟨j, hj⟩).monomial] using
          D.assigned ⟨j, hj⟩
      simpa [hassigned] using
        (interventionRatio C (le_refl p) x ⟨y, hy⟩ Q H hF).2.symm

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

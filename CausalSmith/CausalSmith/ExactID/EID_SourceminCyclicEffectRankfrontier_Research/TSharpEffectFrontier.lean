import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Helpers.LawFiber

/-!
# Sharp law-fiber effect frontier
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open MeasureTheory Set

universe u

def ResponsePointIdentified {p : ℕ} (P : Measure (Vec p)) (x : Fin p) : Prop :=
  ∃ rho, ∀ M : LawCompletion.{u} p, ∀ hM : LawCompletionFiber P x M,
    observedResponse M x hM = rho

def ScalarPointIdentified {p : ℕ} (P : Measure (Vec p))
    (x : Fin p) (y : {i : Fin p // i ≠ x}) : Prop :=
  ∃ theta, ∀ M : LawCompletion.{u} p, ∀ hM : LawCompletionFiber P x M,
    observedResponse M x hM y = theta

lemma admissibleSources_nonempty_of_fullRowRank {p n : ℕ}
    (C : MixingMatrix p n) (hC : FullRowRank C) (x : Fin p) :
    (admissibleSources C x).Nonempty := by
  have hsurj : Function.Surjective C.mulVec := by
    change Function.Surjective C.mulVecLin
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    change C.rank = Module.finrank ℝ (Fin p → ℝ)
    rw [hC]
    simp
  obtain ⟨z, hz⟩ := hsurj (Pi.single x 1)
  have hzx : ∑ j, C x j * z j = 1 := by
    have hx := congrFun hz x
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hx
  have hex : ∃ j, C x j * z j ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hzx
  obtain ⟨j, hjprod⟩ := hex
  have hCx : C x j ≠ 0 := left_ne_zero_of_mul hjprod
  have hzj : z j ≠ 0 := right_ne_zero_of_mul hjprod
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCx, ?_⟩⟩
  let A : Matrix {i : Fin p // i ≠ x} (Fin n) ℝ := fun i k => C i.1 k
  have hrowsC : LinearIndependent ℝ C.row := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    rw [Set.finrank, ← Matrix.rank_eq_finrank_span_row, hC]
    simp
  have hrowsA : LinearIndependent ℝ A.row :=
    hrowsC.comp Subtype.val Subtype.val_injective
  have hArank : A.rank = p - 1 := by
    rw [hrowsA.rank_matrix]
    simp
  let B := deleteRowCol C x j
  let R : Matrix {k : Fin n // k ≠ j} (Fin n) ℝ := Matrix.of fun k l =>
    if l = j then -(z k.1 / z j) else if k.1 = l then 1 else 0
  have hAzero (i : {i : Fin p // i ≠ x}) : ∑ k, A i k * z k = 0 := by
    have hi := congrFun hz i.1
    simpa [A, Matrix.mulVec, dotProduct, Pi.single_apply, i.2] using hi
  have hmul : B * R = A := by
    ext i l
    change ∑ k, B i k * R k l = A i l
    by_cases hlj : l = j
    · subst l
      simp only [R, Matrix.of_apply, if_pos]
      change ∑ k : {k : Fin n // k ≠ j}, C i.1 k.1 * -(z k.1 / z j) = C i.1 j
      have hrest : ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j, A i k * z k =
          -(A i j * z j) := by
        have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
          (fun k => A i k * z k) (Finset.mem_univ j)
        rw [hAzero i] at hsplit
        linarith
      calc
        ∑ k : {k : Fin n // k ≠ j}, C i.1 k.1 * -(z k.1 / z j) =
            -(∑ k ∈ (Finset.univ : Finset (Fin n)).erase j, A i k * z k) / z j := by
              have hsub :
                  (∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
                    C i.1 k * -(z k / z j)) =
                  ∑ k : {k : Fin n // k ≠ j}, C i.1 k.1 * -(z k.1 / z j) := by
                apply Finset.sum_subtype
                simp
              rw [← hsub, ← Finset.sum_neg_distrib, Finset.sum_div]
              apply Finset.sum_congr rfl
              intro k _
              simp only [A]
              field_simp
        _ = A i j := by rw [hrest]; field_simp
    · simp only [R, Matrix.of_apply, if_neg hlj]
      change ∑ k : {k : Fin n // k ≠ j}, C i.1 k.1 *
        (if k.1 = l then 1 else 0) = C i.1 l
      rw [Finset.sum_eq_single (⟨l, hlj⟩ : {k : Fin n // k ≠ j})]
      · simp
      · intro k _ hkl
        simp [show k.1 ≠ l by intro h; exact hkl (Subtype.ext h)]
      · simp
  have hrankLower : A.rank ≤ B.rank := by
    rw [← hmul]
    exact Matrix.rank_mul_le_left _ _
  have hrankUpper : B.rank ≤ p - 1 := by
    simpa [B] using Matrix.rank_le_card_height B
  exact le_antisymm hrankUpper (hArank ▸ hrankLower)

-- @node: thm:sharp-effect-frontier
theorem sharp_effect_frontier {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ)
    (hp : 2 ≤ p) (hpn : p ≤ n) (x : Fin p)
    (hC : FullRowRank C) (hC0 : NonzeroColumns C) (hCdir : DistinctDirections C)
    (hind : ProbabilityTheory.iIndepFun ε μ) (hnd : NondegenerateSources μ ε)
    (hng : NonGaussianSources μ ε)
    (DaiIrreducibleOICAUniqueness_of_gate : DaiIrreducibleOICAUniqueness.{u, u}) :
    ∃ D : CertificateData C x,
    projectiveDirections.{u} (observedLaw μ C ε) =
        {D | ∃ j, D = projectiveClass (C.col j)} ∧
    (admissibleSources C x).Nonempty ∧
    (∀ M : LawCompletion.{u} p,
      LawCompletionFiber (observedLaw μ C ε) x M → M.dim = n) ∧
    {rho | ∃ M : LawCompletion.{u} p,
      ∃ hM : LawCompletionFiber (observedLaw μ C ε) x M,
        rho = observedResponse M x hM} =
        responseFrontier C x ∧
    (∀ (y : Fin p) (hy : y ≠ x),
      {theta | ∃ M : LawCompletion.{u} p,
        ∃ hM : LawCompletionFiber (observedLaw μ C ε) x M,
          theta = observedResponse M x hM ⟨y, hy⟩} = effectFrontier C x y) ∧
    (∀ (pi : Equiv.Perm (Fin n)) (scale : Fin n → ℝ), (∀ j, scale j ≠ 0) →
      responseFrontier (permuteScaleColumns C pi scale) x = responseFrontier C x ∧
      ∀ y, effectFrontier (permuteScaleColumns C pi scale) x y = effectFrontier C x y) ∧
    (ResponsePointIdentified.{u} (observedLaw μ C ε) x ↔
      (responseFrontier C x).Nonempty ∧ (responseFrontier C x).Subsingleton) ∧
    (∀ (y : Fin p) (hy : y ≠ x),
      ScalarPointIdentified.{u} (observedLaw μ C ε) x ⟨y, hy⟩ ↔
        (effectFrontier C x y).Nonempty ∧ (effectFrontier C x y).Subsingleton) ∧
    (∀ (y : Fin p) (hy : y ≠ x), ¬ (effectFrontier C x y).Subsingleton →
      ∃ (j k : Fin n) (hj : j ∈ admissibleSources C x)
          (hk : k ∈ admissibleSources C x), j ≠ k ∧ C y j / C x j ≠ C y k / C x k ∧
        let Qj := (certifiedCompletion C x D j hj).1
        let Hj := (certifiedCompletion C x D j hj).2
        let Qk := (certifiedCompletion C x D k hk).1
        let Hk := (certifiedCompletion C x D k hk).2
        let hFj := D.valid ⟨j, hj⟩
        let hFk := D.valid ⟨k, hk⟩
          let Mj := embedFixedCompletion μ hpn Qj Hj ε hFj.solvable
          let Mk := embedFixedCompletion μ hpn Qk Hk ε hFk.solvable
          ∃ hLawj : LawCompletionFiber (observedLaw μ C ε) x Mj,
          ∃ hLawk : LawCompletionFiber (observedLaw μ C ε) x Mk,
          observedResponse Mj x hLawj ⟨y, hy⟩ ≠
            observedResponse Mk x hLawk ⟨y, hy⟩) ∧
    CubicExactIrreducibleCertificateEnumeration C ⟨hp, hpn⟩ hC hC0 hCdir x D ∧
    WorstCaseDenseOutputOptimal := by
  have hrefqual : QualitativelyNondegenerateSources μ ε := by
    refine ⟨hnd.1, hnd.2.1, ?_⟩
    intro j
    rintro ⟨c, hc⟩
    have hv := ProbabilityTheory.variance_id_map (hnd.2.1 j)
    rw [hc, ProbabilityTheory.variance_dirac] at hv
    linarith [hnd.2.2 j]
  have href : IsQualitativeIrreducibleICARepresentation μ C ε (observedLaw μ C ε) :=
    ⟨hnd.1, hnd.2.1, hC0, hCdir, hind, hrefqual, rfl⟩
  have hdirections : projectiveDirections.{u} (observedLaw μ C ε) =
      {D | ∃ j, D = projectiveClass (C.col j)} := by
    ext E
    constructor
    · rintro ⟨m, Ξ, mΞ, ν, A, ξ, _hpm, _hprob, _hmeas, hrep, j, rfl⟩
      letI : MeasurableSpace Ξ := mΞ
      rcases hrep with
        ⟨_, hνprob, hξmeas, hA0, hAdir, hAind, hAqual, _hAng, hAlaw⟩
      obtain ⟨_, hsets, _⟩ :=
        DaiIrreducibleOICAUniqueness_of_gate inferInstance inferInstance μ ν C A ε ξ href hng
          hA0 hAdir hAind hAqual hAlaw
      rw [hsets]
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      refine ⟨n, Ω, inferInstance, μ, C, ε, hpn, hnd.1, hnd.2.1, ?_, j, rfl⟩
      exact ⟨hpn, hnd.1, hnd.2.1, hC0, hCdir, hind, hrefqual, hng, rfl⟩
  obtain ⟨D, _hkernel, _hadmissible, hcompletion, _hrational,
      _htrace, hcubic, hoptimal⟩ :=
    shared_kernel_matching_certificate C ⟨hp, hpn⟩ hC x
  have hcanonical (j : Fin n) (hj : j ∈ admissibleSources C x) :
      let Q := (certifiedCompletion C x D j hj).1
      let H := (certifiedCompletion C x D j hj).2
      let hFix := D.valid ⟨j, hj⟩
      let M := embedFixedCompletion μ D.dim_le Q H ε hFix.solvable
      ∃ hLaw : LawCompletionFiber (observedLaw μ C ε) x M,
        observedResponse M x hLaw = (fun i => C i.1 j / C x j) := by
    dsimp only
    let Q := (certifiedCompletion C x D j hj).1
    let H := (certifiedCompletion C x D j hj).2
    let hFix := D.valid ⟨j, hj⟩
    let M := embedFixedCompletion μ D.dim_le Q H ε hFix.solvable
    have hmix : M.observedMixing = C := by
      funext i k
      exact hFix.fixedLaw i k
    have hLaw : LawCompletionFiber (observedLaw μ C ε) x M := by
      refine
        { probability := hnd.1
          unitDiagonal := hFix.unitDiagonal
          monomial := hFix.monomial
          postSolvable := hFix.postSolvable
          sourceConditions := ⟨hind, hnd, hng⟩
          irreducible := ?_
          lawMatch := ?_ }
      · constructor
        · intro k
          rw [hmix]
          exact hC0 k
        · intro k l hkl
          rw [hmix]
          exact hCdir k l hkl
      · change observedLaw μ M.observedMixing ε = observedLaw μ C ε
        rw [hmix]
        rfl
    refine ⟨hLaw, ?_⟩
    have hassigned : assignedSource H hFix.monomial (Fin.castLE D.dim_le x) = j :=
      D.assigned ⟨j, hj⟩
    rw [(lawResponse_eq_inverse_ratio (Ω := Ω) (observedLaw μ C ε) x M hLaw).2]
    funext i
    change equilibriumEffect C D.dim_le x i Q H hFix = C i.1 j / C x j
    simpa [hassigned] using (interventionRatio C D.dim_le x i Q H hFix).2
  have hnonempty : (admissibleSources C x).Nonempty :=
    admissibleSources_nonempty_of_fullRowRank C hC x
  have hresponse :
      {rho | ∃ M : LawCompletion.{u} p,
        ∃ hM : LawCompletionFiber (observedLaw μ C ε) x M,
          rho = observedResponse M x hM} = responseFrontier C x := by
    ext rho
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact (lawFiber_response_rank μ C ε x ⟨hp, hpn⟩ hC0 hCdir hind hnd hng
        DaiIrreducibleOICAUniqueness_of_gate M hM).2.choose_spec.choose_spec.2.2.2.2.2
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨hLaw, hrho⟩ := hcanonical j hj
      exact ⟨_, hLaw, hrho.symm⟩
  have hscalar (y : Fin p) (hy : y ≠ x) :
      {theta | ∃ M : LawCompletion.{u} p,
        ∃ hM : LawCompletionFiber (observedLaw μ C ε) x M,
          theta = observedResponse M x hM ⟨y, hy⟩} = effectFrontier C x y := by
    ext theta
    constructor
    · rintro ⟨M, hM, rfl⟩
      obtain ⟨_, j, _, _, hj, _, _, hrho, _⟩ :=
        lawFiber_response_rank μ C ε x ⟨hp, hpn⟩ hC0 hCdir hind hnd hng
          DaiIrreducibleOICAUniqueness_of_gate M hM
      exact ⟨j, hj, congrFun hrho ⟨y, hy⟩⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨hLaw, hrho⟩ := hcanonical j hj
      exact ⟨_, hLaw, (congrFun hrho ⟨y, hy⟩).symm⟩
  have hdimLaw (M : LawCompletion.{u} p)
      (hM : LawCompletionFiber (observedLaw μ C ε) x M) : M.dim = n :=
    (lawFiber_response_rank μ C ε x ⟨hp, hpn⟩ hC0 hCdir hind hnd hng
      DaiIrreducibleOICAUniqueness_of_gate M hM).1
  refine ⟨D, hdirections, hnonempty, hdimLaw, hresponse, hscalar, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro pi scale hscale
    exact ⟨(frontier_monomial_invariance C pi scale hscale x x).2.1,
      fun y => (frontier_monomial_invariance C pi scale hscale x y).2.2⟩
  · constructor
    · rintro ⟨rho, hrho⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨j, hj⟩ := hnonempty
        exact ⟨fun i => C i.1 j / C x j, j, hj, rfl⟩
      · intro a ha b hb
        rw [← hresponse] at ha hb
        obtain ⟨Ma, hMa, rfl⟩ := ha
        obtain ⟨Mb, hMb, rfl⟩ := hb
        exact (hrho Ma hMa).trans (hrho Mb hMb).symm
    · rintro ⟨hne, hsub⟩
      obtain ⟨rho, hrho⟩ := hne
      refine ⟨rho, ?_⟩
      intro M hM
      apply hsub
      · rw [← hresponse]
        exact ⟨M, hM, rfl⟩
      · exact hrho
  · intro y hy
    constructor
    · rintro ⟨theta, htheta⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨j, hj⟩ := hnonempty
        exact ⟨C y j / C x j, j, hj, rfl⟩
      · intro a ha b hb
        rw [← hscalar y hy] at ha hb
        obtain ⟨Ma, hMa, rfl⟩ := ha
        obtain ⟨Mb, hMb, rfl⟩ := hb
        exact (htheta Ma hMa).trans (htheta Mb hMb).symm
    · rintro ⟨hne, hsub⟩
      obtain ⟨theta, htheta⟩ := hne
      refine ⟨theta, ?_⟩
      intro M hM
      apply hsub
      · rw [← hscalar y hy]
        exact ⟨M, hM, rfl⟩
      · exact htheta
  · intro y hy hnot
    obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hnot
    rcases ha with ⟨j, hj, rfl⟩
    rcases hb with ⟨k, hk, rfl⟩
    have hjk : j ≠ k := by
      intro h
      subst k
      exact hab rfl
    refine ⟨j, k, hj, hk, hjk, hab, ?_⟩
    dsimp only
    obtain ⟨hLawj, hrhoj⟩ := hcanonical j hj
    obtain ⟨hLawk, hrhok⟩ := hcanonical k hk
    refine ⟨hLawj, hLawk, ?_⟩
    intro heq
    have hjcoord := congrFun hrhoj ⟨y, hy⟩
    have hkcoord := congrFun hrhok ⟨y, hy⟩
    exact hab (hjcoord.symm.trans (heq.trans hkcoord))
  · rcases hcubic with ⟨algorithm, halgorithm, hinput, hcomputes⟩
    refine ⟨algorithm, ?_, hinput, hcomputes⟩
    rcases halgorithm with ⟨c, n0, hc, hall⟩
    refine ⟨c, n0, hc, ?_⟩
    intro p' n' C' hdim' hC' _hC0' _hCdir' x' hn0
    exact hall C' hdim' hC' x' hn0
  · exact hoptimal

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

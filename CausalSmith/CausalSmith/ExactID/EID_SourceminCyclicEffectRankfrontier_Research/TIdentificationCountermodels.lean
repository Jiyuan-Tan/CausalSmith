import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.TSharpEffectFrontier
import Mathlib.Data.Set.Card

/-!
# Point-identification criteria and exact countermodels
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open MeasureTheory Set

universe u

def selectedEffectMatrix {p n : ℕ} (C : MixingMatrix p n) (x y : Fin p)
    (J : Finset (Fin n)) : Matrix (Fin 2) {j : Fin n // j ∈ J} ℝ :=
  fun i j => if i.1 = 0 then C x j.1 else C y j.1

lemma responseFrontier_ncard_eq_admissibleSources_card {p n : ℕ}
    (C : MixingMatrix p n) (x : Fin p) (hCdir : DistinctDirections C) :
    (responseFrontier C x).ncard = (admissibleSources C x).card := by
  let phi : {j : Fin n // j ∈ admissibleSources C x} → {i : Fin p // i ≠ x} → ℝ :=
    fun j i => C i.1 j.1 / C x j.1
  have hphi : Function.Injective phi := by
    intro j k heq
    apply Subtype.ext
    by_contra hjk
    apply hCdir j.1 k.1 hjk (C x j.1 / C x k.1)
    funext i
    have hjx : C x j.1 ≠ 0 := (Finset.mem_filter.mp j.2).2.1
    have hkx : C x k.1 ≠ 0 := (Finset.mem_filter.mp k.2).2.1
    by_cases hix : i = x
    · subst i
      simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    · have hi := congrFun heq ⟨i, hix⟩
      dsimp [phi] at hi
      simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hjx, hkx] at hi ⊢
      simpa [mul_comm] using hi
  have hrange : responseFrontier C x = Set.range phi := by
    ext rho
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j.1, j.2, rfl⟩
  rw [hrange, Set.ncard_range_of_injective hphi, Nat.card_eq_fintype_card,
    Fintype.card_coe]

lemma set_ncard_eq_one_iff_nonempty_subsingleton {α : Type*} (s : Set α) :
    s.ncard = 1 ↔ s.Nonempty ∧ s.Subsingleton := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := Set.ncard_eq_one.mp h
    simp
  · rintro ⟨⟨a, ha⟩, hsub⟩
    rw [Set.ncard_eq_one]
    refine ⟨a, Set.eq_singleton_iff_unique_mem.mpr ⟨ha, ?_⟩⟩
    intro b hb
    exact hsub hb ha

set_option maxHeartbeats 800000 in
-- The dependent-column rank comparison needs extra elaboration time on this finite matrix.
lemma selectedEffectMatrix_rank_one_iff_effectFrontier_subsingleton {p n : ℕ}
    (C : MixingMatrix p n) (x y : Fin p)
    (hne : (admissibleSources C x).Nonempty) :
    (selectedEffectMatrix C x y (admissibleSources C x)).rank = 1 ↔
      (effectFrontier C x y).Subsingleton := by
  classical
  let J := admissibleSources C x
  let A := selectedEffectMatrix C x y J
  obtain ⟨j, hj⟩ := hne
  have hjx : C x j ≠ 0 := (Finset.mem_filter.mp hj).2.1
  have hrank_pos : 1 ≤ A.rank := by
    change 0 < A.rank
    rw [Matrix.rank, Module.finrank_pos_iff_exists_ne_zero]
    let e : {k : Fin n // k ∈ J} → ℝ := Pi.single ⟨j, hj⟩ 1
    refine ⟨⟨A.mulVec e, ⟨e, rfl⟩⟩, ?_⟩
    intro hz
    have hz0 := congrFun (congrArg Subtype.val hz) (0 : Fin 2)
    simp only [A, selectedEffectMatrix, Matrix.mulVec, dotProduct, Fin.isValue] at hz0
    rw [Finset.sum_eq_single ⟨j, hj⟩] at hz0
    · exact hjx (by simpa [e] using hz0)
    · intro k _ hkj
      simp [e, hkj]
    · simp
  constructor
  · intro hrank a ha b hb
    rcases ha with ⟨j', hj', rfl⟩
    rcases hb with ⟨k', hk', rfl⟩
    by_contra hratio
    have hjx' : C x j' ≠ 0 := (Finset.mem_filter.mp hj').2.1
    have hkx' : C x k' ≠ 0 := (Finset.mem_filter.mp hk').2.1
    have hjk : j' ≠ k' := by
      intro h
      subst k'
      exact hratio rfl
    let g : Fin 2 → {k : Fin n // k ∈ J} := fun i =>
      if i.1 = 0 then ⟨j', hj'⟩ else ⟨k', hk'⟩
    have hg : Function.Injective g := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [g]
    have hdet : (A.submatrix (Equiv.refl (Fin 2)) g).det ≠ 0 := by
      rw [Matrix.det_fin_two]
      simp only [Matrix.submatrix_apply, Equiv.refl_apply]
      simp [A, selectedEffectMatrix, g]
      intro hz
      apply hratio
      field_simp [hjx', hkx']
      nlinarith
    have htwo : (A.submatrix (Equiv.refl (Fin 2)) g).rank = 2 := by
      simpa using Matrix.rank_of_det_ne_zero hdet
    have := Matrix.rank_submatrix_le A (Equiv.refl (Fin 2)) g
    rw [htwo, hrank] at this
    omega
  · intro hsub
    have hall (k : {k : Fin n // k ∈ J}) :
        C y k.1 / C x k.1 = C y j / C x j := by
      apply hsub
      · exact ⟨k.1, k.2, rfl⟩
      · exact ⟨j, hj, rfl⟩
    let w : Fin 2 → ℝ := fun i => if i.1 = 0 then 1 else C y j / C x j
    let v : {k : Fin n // k ∈ J} → ℝ := fun k => C x k.1
    have hA : A = Matrix.vecMulVec w v := by
      ext i k
      fin_cases i
      · change C x k.1 = 1 * C x k.1
        ring
      · have hkx : C x k.1 ≠ 0 := (Finset.mem_filter.mp k.2).2.1
        have hk := hall k
        change C y k.1 = (C y j / C x j) * C x k.1
        field_simp [hjx, hkx] at hk ⊢
        simpa [mul_comm] using hk
    apply Nat.le_antisymm
    · change A.rank ≤ 1
      rw [hA]
      exact Matrix.rank_vecMulVec_le w v
    · exact hrank_pos

-- @node: prop:identification-and-countermodels
theorem identification_and_countermodels {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ)
    (hp : 2 ≤ p) (hpn : p ≤ n) (x : Fin p)
    (hC : FullRowRank C) (hC0 : NonzeroColumns C) (hCdir : DistinctDirections C)
    (hind : ProbabilityTheory.iIndepFun ε μ) (hnd : NondegenerateSources μ ε)
    (hng : NonGaussianSources μ ε)
    (DaiIrreducibleOICAUniqueness_of_gate : DaiIrreducibleOICAUniqueness.{u, u}) :
    ∃ D : CertificateData C x,
    (ResponsePointIdentified.{u} (observedLaw μ C ε) x ↔
      (responseFrontier C x).ncard = 1) ∧
    ((responseFrontier C x).ncard = 1 ↔ (admissibleSources C x).card = 1) ∧
    ((responseFrontier C x).ncard ≠ 1 →
      ∃ (j k : Fin n) (hj : j ∈ admissibleSources C x)
          (hk : k ∈ admissibleSources C x), j ≠ k ∧
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
          observedResponse Mj x hLawj ≠ observedResponse Mk x hLawk ∧
          CubicWitnessPairAfterSharedInverse C ⟨hp, hpn⟩ hC hC0 hCdir x
            D j k hj hk) ∧
    (∀ y : {i : Fin p // i ≠ x},
      (ScalarPointIdentified.{u} (observedLaw μ C ε) x y ↔
        (effectFrontier C x y.1).ncard = 1) ∧
      ((effectFrontier C x y.1).ncard = 1 ↔
        (selectedEffectMatrix C x y.1 (admissibleSources C x)).rank = 1) ∧
      (¬ (effectFrontier C x y.1).Subsingleton →
        ∃ (j k : Fin n) (hj : j ∈ admissibleSources C x)
            (hk : k ∈ admissibleSources C x),
          C y.1 j / C x j ≠ C y.1 k / C x k ∧
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
            observedResponse Mj x hLawj y ≠ observedResponse Mk x hLawk y) ∧
      effectFrontier C x y.1 = (fun rho => rho y) '' responseFrontier C x) := by
  obtain ⟨D, _hdirections, hJne, _hdim, _hresponse, _hscalar, _hinvariance,
      hresponseId, hscalarId, hcounter, hcubic, _hoptimal⟩ :=
    sharp_effect_frontier μ C ε hp hpn x hC hC0 hCdir hind hnd hng
      DaiIrreducibleOICAUniqueness_of_gate
  have hpair (j k : Fin n) (hj : j ∈ admissibleSources C x)
      (hk : k ∈ admissibleSources C x) :
      CubicWitnessPairAfterSharedInverse C ⟨hp, hpn⟩ hC hC0 hCdir x D j k hj hk := by
    exact cubicWitnessPairAfterSharedInverse_of_irreducibleEnumeration
      C ⟨hp, hpn⟩ hC hC0 hCdir x D hcubic j k hj hk
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · rw [hresponseId]
    rw [set_ncard_eq_one_iff_nonempty_subsingleton]
  · rw [responseFrontier_ncard_eq_admissibleSources_card C x hCdir]
  · intro hcard
    have hnot : ¬ (responseFrontier C x).Subsingleton := by
      intro hsub
      have hne : (responseFrontier C x).Nonempty := by
        obtain ⟨j, hj⟩ := hJne
        exact ⟨_, j, hj, rfl⟩
      exact hcard ((set_ncard_eq_one_iff_nonempty_subsingleton _).2 ⟨hne, hsub⟩)
    obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hnot
    rcases ha with ⟨j, hj, rfl⟩
    rcases hb with ⟨k, hk, rfl⟩
    have hjk : j ≠ k := by intro h; subst k; exact hab rfl
    dsimp only
    let Qj := (certifiedCompletion C x D j hj).1
    let Hj := (certifiedCompletion C x D j hj).2
    let Qk := (certifiedCompletion C x D k hk).1
    let Hk := (certifiedCompletion C x D k hk).2
    let hFj := D.valid ⟨j, hj⟩
    let hFk := D.valid ⟨k, hk⟩
    let Mj := embedFixedCompletion μ hpn Qj Hj ε hFj.solvable
    let Mk := embedFixedCompletion μ hpn Qk Hk ε hFk.solvable
    have hcanonical (l : Fin n) (hl : l ∈ admissibleSources C x) :
        let Q := (certifiedCompletion C x D l hl).1
        let H := (certifiedCompletion C x D l hl).2
        let hFix := D.valid ⟨l, hl⟩
        let M := embedFixedCompletion μ hpn Q H ε hFix.solvable
        ∃ hLaw : LawCompletionFiber (observedLaw μ C ε) x M,
          observedResponse M x hLaw = (fun i => C i.1 l / C x l) := by
      dsimp only
      let Q := (certifiedCompletion C x D l hl).1
      let H := (certifiedCompletion C x D l hl).2
      let hFix := D.valid ⟨l, hl⟩
      let M := embedFixedCompletion μ hpn Q H ε hFix.solvable
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
        · exact ⟨fun k => hmix.symm ▸ hC0 k,
            fun k l hkl => hmix.symm ▸ hCdir k l hkl⟩
        · change observedLaw μ M.observedMixing ε = observedLaw μ C ε
          rw [hmix]
          rfl
      refine ⟨hLaw, ?_⟩
      have hassigned : assignedSource H hFix.monomial (Fin.castLE D.dim_le x) = l :=
        D.assigned ⟨l, hl⟩
      rw [(lawResponse_eq_inverse_ratio (Ω := Ω) (observedLaw μ C ε) x M hLaw).2]
      funext i
      change equilibriumEffect C D.dim_le x i Q H hFix = C i.1 l / C x l
      simpa [hassigned] using (interventionRatio C D.dim_le x i Q H hFix).2
    obtain ⟨hLawj, hrhoj⟩ := hcanonical j hj
    obtain ⟨hLawk, hrhok⟩ := hcanonical k hk
    refine ⟨j, k, hj, hk, hjk, hLawj, hLawk, ?_, ?_⟩
    · exact fun heq => hab (hrhoj.symm.trans (heq.trans hrhok))
    · exact hpair j k hj hk
  · intro y
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hscalarId y.1 y.2]
      rw [set_ncard_eq_one_iff_nonempty_subsingleton]
    · rw [selectedEffectMatrix_rank_one_iff_effectFrontier_subsingleton C x y.1 hJne]
      have hRne : (effectFrontier C x y.1).Nonempty := by
        obtain ⟨j, hj⟩ := hJne
        exact ⟨_, j, hj, rfl⟩
      exact set_ncard_eq_one_iff_nonempty_subsingleton _ |>.trans
        (and_iff_right hRne)
    · intro hn
      obtain ⟨j, k, hj, hk, _hjk, hratio, hrest⟩ := hcounter y.1 y.2 hn
      exact ⟨j, k, hj, hk, hratio, hrest⟩
    · ext theta
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨(fun i => C i.1 j / C x j), ⟨j, hj, rfl⟩, rfl⟩
      · rintro ⟨rho, ⟨j, hj, rfl⟩, rfl⟩
        exact ⟨j, hj, rfl⟩

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

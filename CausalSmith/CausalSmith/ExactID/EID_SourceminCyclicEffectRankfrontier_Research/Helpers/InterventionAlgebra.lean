import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Basic.Frontier

/-!
# Intervention algebra

Adjugate/cofactor consequences for fixed-law and law-level cyclic completions.
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open MeasureTheory

universe u

/-- Reindexing equivalence between `Fin m` and the indices away from one pivot in `Fin (m+1)`. -/
noncomputable def finSuccEquivAway {m : ℕ} (x : Fin (m + 1)) :
    Fin m ≃ {i : Fin (m + 1) // i ≠ x} :=
  Equiv.ofBijective
    (fun k => ⟨x.succAbove k, Fin.succAbove_ne x k⟩)
    ⟨fun _ _ h => Fin.succAbove_right_injective (congrArg Subtype.val h), by
      intro i
      have hi : i.1 ∈ ({x}ᶜ : Set (Fin (m + 1))) := by simpa using i.2
      rw [← Fin.range_succAbove] at hi
      obtain ⟨k, hk⟩ := hi
      exact ⟨k, Subtype.ext hk⟩⟩

/-- A nonsingular principal deletion minor makes the corresponding diagonal inverse entry nonzero. -/
lemma inverse_diagonal_ne_zero_of_delete_det_ne_zero {n : ℕ} (Q : SquareMatrix n)
    (x : Fin n) (hQ : Q.det ≠ 0) (hx : (deleteSquare Q x).det ≠ 0) :
    Q⁻¹ x x ≠ 0 := by
  have hn : n ≠ 0 := by
    intro hn
    have hxlt := x.isLt
    omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hminor : (Q.submatrix x.succAbove x.succAbove).det ≠ 0 := by
    have hreindex := Matrix.det_submatrix_equiv_self (finSuccEquivAway x) (deleteSquare Q x)
    have heq : (deleteSquare Q x).submatrix (finSuccEquivAway x) (finSuccEquivAway x) =
        Q.submatrix x.succAbove x.succAbove := by
      ext i j
      rfl
    rw [heq] at hreindex
    rwa [hreindex]
  have hinv := Matrix.nonsing_inv_apply Q ((isUnit_iff_ne_zero).2 hQ)
  rw [hinv]
  change (↑((isUnit_iff_ne_zero).2 hQ).unit⁻¹ : ℝ) * Q.adjugate x x ≠ 0
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  exact mul_ne_zero (Units.ne_zero _) (mul_ne_zero (by positivity) hminor)

-- @node: lem:intervention-ratio
lemma interventionRatio {p n : ℕ} (C : MixingMatrix p n) (hpn : p ≤ n)
    (x : Fin p) (y : {i : Fin p // i ≠ x}) (Q H : SquareMatrix n)
    (hM : CompletionFiber C hpn x Q H) :
    let j := assignedSource H hM.monomial (Fin.castLE hpn x)
    C x j ≠ 0 ∧
      equilibriumEffect C hpn x y Q H hM = C y j / C x j := by
  let xx := Fin.castLE hpn x
  let yy := Fin.castLE hpn y.1
  let j := assignedSource H hM.monomial xx
  let h := H xx j
  have hh : h ≠ 0 := by
    exact (Classical.choose_spec (hM.monomial.1 xx)).1
  have hcol : ∀ k, k ≠ xx → H k j = 0 := by
    intro k hk
    by_contra hkj
    have hu := hM.monomial.2 j
    exact hk (hu.unique hkj hh)
  have hmul (i : Fin n) : (Q⁻¹ * H) i j = Q⁻¹ i xx * h := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single xx
    · intro k _ hk
      rw [hcol k hk, mul_zero]
    · simp
  have hCx : C x j = Q⁻¹ xx xx * h := by
    rw [← hM.fixedLaw x j]
    exact hmul xx
  have hCy : C y.1 j = Q⁻¹ yy xx * h := by
    rw [← hM.fixedLaw y.1 j]
    exact hmul yy
  have hdiag : Q⁻¹ xx xx ≠ 0 :=
    inverse_diagonal_ne_zero_of_delete_det_ne_zero Q xx hM.solvable hM.postSolvable
  dsimp only
  constructor
  · rw [hCx]
    exact mul_ne_zero hdiag hh
  · change Q⁻¹ yy xx / Q⁻¹ xx xx = C y.1 j / C x j
    rw [hCx, hCy]
    field_simp

/-- The reduced structural matrix sends the restricted inverse column to the negative omitted
column, scaled by the omitted diagonal inverse entry. -/
lemma deleteSquare_mulVec_inverseColumn {n : ℕ} (Q : SquareMatrix n) (x : Fin n)
    (hQ : Q.det ≠ 0) :
    (deleteSquare Q x).mulVec (fun k => Q⁻¹ k.1 x) =
      fun k => -Q k.1 x * Q⁻¹ x x := by
  funext k
  have hfull := congrArg (fun A : SquareMatrix n => A k.1 x)
    (Q.mul_nonsing_inv ((isUnit_iff_ne_zero).2 hQ))
  rw [Matrix.mul_apply] at hfull
  simp only [Matrix.mulVec, dotProduct, deleteSquare, Matrix.submatrix_apply]
  rw [Fintype.sum_eq_add_sum_compl x] at hfull
  simp only [Matrix.one_apply, ne_eq, k.2, if_false] at hfull
  calc
    (∑ i : {i : Fin n // i ≠ x}, Q k.1 i.1 * Q⁻¹ i.1 x) =
        ∑ i with i ≠ x, Q k.1 i * Q⁻¹ i x := by
      simpa using (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => Q k.1 i * Q⁻¹ i x) (p := fun i => i ≠ x))
    _ = -Q k.1 x * Q⁻¹ x x := by
      have hfull' : Q k.1 x * Q⁻¹ x x +
          (∑ i with i ≠ x, Q k.1 i * Q⁻¹ i x) = 0 := by
        have hcomp : ({x}ᶜ : Finset (Fin n)) =
            Finset.univ.filter (fun i => i ≠ x) := by
          ext i
          simp
        rw [hcomp] at hfull
        exact hfull
      linarith

/-- Solving the reduced intervention equations gives the corresponding inverse-column ratio. -/
lemma deleteSquare_inverse_mulVec_eq_inverseRatio {n : ℕ} (Q : SquareMatrix n) (x : Fin n)
    (hQ : Q.det ≠ 0) (hx : (deleteSquare Q x).det ≠ 0)
    (i : {i : Fin n // i ≠ x}) :
    (deleteSquare Q x)⁻¹.mulVec (fun k => -Q k.1 x) i =
      Q⁻¹ i.1 x / Q⁻¹ x x := by
  have hrel := deleteSquare_mulVec_inverseColumn Q x hQ
  have happ := congrArg (fun v => (deleteSquare Q x)⁻¹.mulVec v) hrel
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ((isUnit_iff_ne_zero).2 hx)] at happ
  simp only [Matrix.one_mulVec] at happ
  have hi := congrFun happ i
  simp only [Matrix.mulVec, dotProduct] at hi ⊢
  have hdiag : Q⁻¹ x x ≠ 0 :=
    inverse_diagonal_ne_zero_of_delete_det_ne_zero Q x hQ hx
  apply (eq_div_iff hdiag).2
  rw [Finset.sum_mul]
  calc
    (∑ k, (deleteSquare Q x)⁻¹ i k * -Q k.1 x * Q⁻¹ x x) =
        ∑ k, (deleteSquare Q x)⁻¹ i k * (-Q k.1 x * Q⁻¹ x x) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = Q⁻¹ i.1 x := hi.symm

-- @node: lem:law-hard-intervention-response
lemma lawResponse_eq_inverse_ratio {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (P : Measure (Vec p)) (x : Fin p) (M : LawCompletion.{u} p)
    (hM : LawCompletionFiber P x M) :
    (∀ i : {i : Fin p // i ≠ x}, HasDerivAt (lawInterventionPath M x i 0)
      (M.Q⁻¹ (M.liftObserved i.1) (M.liftObserved x) /
        M.Q⁻¹ (M.liftObserved x) (M.liftObserved x)) 0) ∧
      observedResponse M x hM = fun i =>
        M.Q⁻¹ (M.liftObserved i.1) (M.liftObserved x) /
          M.Q⁻¹ (M.liftObserved x) (M.liftObserved x) := by
  let xx := M.liftObserved x
  have hpath (i : {i : Fin p // i ≠ x}) :
      lawInterventionPath M x i 0 = fun t =>
        t * (M.Q⁻¹ (M.liftObserved i.1) xx / M.Q⁻¹ xx xx) := by
    funext t
    simp only [lawInterventionPath, Matrix.mulVec, dotProduct, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_sub]
    calc
      (∑ k, (deleteSquare M.Q xx)⁻¹ (M.liftObservedAway x i) k *
          -(M.Q k.1 xx * t)) =
          t * ∑ k, (deleteSquare M.Q xx)⁻¹ (M.liftObservedAway x i) k *
            (-M.Q k.1 xx) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = t * (M.Q⁻¹ (M.liftObserved i.1) xx / M.Q⁻¹ xx xx) := by
        have hr := deleteSquare_inverse_mulVec_eq_inverseRatio M.Q xx M.solvable
          hM.postSolvable (M.liftObservedAway x i)
        simp only [Matrix.mulVec, dotProduct] at hr
        rw [hr]
        rfl
  constructor
  · intro i
    rw [hpath i]
    simpa [xx] using (hasDerivAt_id (𝕜 := ℝ) 0).mul_const
      (M.Q⁻¹ (M.liftObserved i.1) xx / M.Q⁻¹ xx xx)
  · funext i
    rw [observedResponse, hpath i]
    simpa [xx] using HasDerivAt.deriv ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const
      (M.Q⁻¹ (M.liftObserved i.1) xx / M.Q⁻¹ xx xx))

/-- A monomial source-assignment matrix is nonsingular. -/
lemma monomialSourceAssignment_det_ne_zero {n : ℕ} (H : SquareMatrix n)
    (hH : MonomialSourceAssignment H) : H.det ≠ 0 := by
  have hcols : LinearIndependent ℝ H.col := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    obtain ⟨i, hij, _⟩ := hH.2 j
    have hcoord := congrFun hg i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
    rw [Finset.sum_eq_single j] at hcoord
    · exact (mul_eq_zero.mp hcoord).resolve_right hij
    · intro k _ hkj
      have hik : H i k = 0 := by
        by_contra hik
        exact hkj ((hH.1 i).unique hik hij)
      simp [hik]
    · simp
  have huH : IsUnit H := (Matrix.linearIndependent_cols_iff_isUnit).mp hcols
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det H).mp huH)

/-- In the inverse mixing matrix, an equation's assigned source has a nonzero coefficient. -/
lemma inverseMixing_assignedSource_ne_zero {n : ℕ} (Q H : SquareMatrix n)
    (hQ : Q.det ≠ 0) (hdiag : UnitStructuralDiagonal Q)
    (hH : MonomialSourceAssignment H) (x : Fin n) :
    (Q⁻¹ * H)⁻¹ (assignedSource H hH x) x ≠ 0 := by
  let j := assignedSource H hH x
  have hj : H x j ≠ 0 := (Classical.choose_spec (hH.1 x)).1
  have hrow : ∀ k, k ≠ j → H x k = 0 := by
    intro k hkj
    by_contra hk
    exact hkj ((hH.1 x).unique hk hj)
  have hHdet := monomialSourceAssignment_det_ne_zero H hH
  have hHunit : IsUnit H.det := (isUnit_iff_ne_zero).2 hHdet
  have hprod := Matrix.mul_nonsing_inv H hHunit
  have hentry (k : Fin n) := congrArg (fun A : SquareMatrix n => A x k) hprod
  have hHinv_off : ∀ k, k ≠ x → H⁻¹ j k = 0 := by
    intro k hk
    have heq := hentry k
    rw [Matrix.mul_apply, Finset.sum_eq_single j] at heq
    · simp only [Matrix.one_apply, Ne.symm hk, if_false] at heq
      exact (mul_eq_zero.mp heq).resolve_left hj
    · intro l _ hlj
      rw [hrow l hlj, zero_mul]
    · simp
  have hHinv_diag : H⁻¹ j x ≠ 0 := by
    have heq := hentry x
    rw [Matrix.mul_apply, Finset.sum_eq_single j] at heq
    · simp only [Matrix.one_apply, if_pos] at heq
      intro hz
      rw [hz, mul_zero] at heq
      norm_num at heq
    · intro l _ hlj
      rw [hrow l hlj, zero_mul]
    · simp
  change (Q⁻¹ * H)⁻¹ j x ≠ 0
  rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv Q
    ((isUnit_iff_ne_zero).2 hQ), Matrix.mul_apply]
  rw [Finset.sum_eq_single x]
  · rw [hdiag x]
    simpa using hHinv_diag
  · intro k _ hk
    rw [hHinv_off k hk, zero_mul]
  · simp

/-- A nonzero inverse coefficient forces full row rank after deleting its row and column. -/
lemma deleteRowCol_rank_of_inverse_entry_ne_zero {p n : ℕ} (C : MixingMatrix p n)
    (hpn : p ≤ n) (x : Fin p) (T : SquareMatrix n)
    (hT : T.det ≠ 0) (hfixed : ∀ i j, T (Fin.castLE hpn i) j = C i j)
    (j : Fin n) (hinv : T⁻¹ j (Fin.castLE hpn x) ≠ 0) :
    (deleteRowCol C x j).rank = p - 1 := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    exact Fin.elim0 j
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let xx : Fin (m + 1) := Fin.castLE hpn x
  let A : Matrix (Fin m) (Fin m) ℝ :=
    T.submatrix xx.succAbove j.succAbove
  have hadj : T.adjugate j xx ≠ 0 := by
    rw [Matrix.nonsing_inv_apply T ((isUnit_iff_ne_zero).2 hT)] at hinv
    exact (mul_ne_zero_iff.mp hinv).2
  have hAdet : A.det ≠ 0 := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at hadj
    exact (mul_ne_zero_iff.mp hadj).2
  have hLI : LinearIndependent ℝ A.row :=
    Matrix.linearIndependent_rows_of_det_ne_zero hAdet
  let f : {i : Fin p // i ≠ x} → Fin m := fun i =>
    (finSuccEquivAway xx).symm
      ⟨Fin.castLE hpn i.1, by
        intro hi
        apply i.2
        exact Fin.castLE_injective hpn hi⟩
  have hrowmap (i : {i : Fin p // i ≠ x}) :
      xx.succAbove (f i) = Fin.castLE hpn i.1 := by
    change ((finSuccEquivAway xx) (f i)).1 = Fin.castLE hpn i.1
    simp [f]
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Fin.castLE_injective hpn
    rw [← hrowmap a, ← hrowmap b, hab]
  have hLIf : LinearIndependent ℝ (fun i => A.row (f i)) :=
    hLI.comp f hf
  have hentry (i : {i : Fin p // i ≠ x}) (k : Fin m) :
      A (f i) k = C i.1 (finSuccEquivAway j k).1 := by
    change T (xx.succAbove (f i)) (j.succAbove k) = _
    rw [hrowmap]
    exact hfixed i.1 (j.succAbove k)
  have hdelLI : LinearIndependent ℝ (deleteRowCol C x j).row := by
    rw [Fintype.linearIndependent_iff] at hLIf ⊢
    intro g hg i
    apply hLIf g
    funext k
    have hk := congrFun hg (finSuccEquivAway j k)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk ⊢
    calc
      (∑ a, g a * A (f a) k) =
          ∑ a, g a * C a.1 (finSuccEquivAway j k).1 := by
            apply Finset.sum_congr rfl
            intro a _
            rw [hentry]
      _ = 0 := hk
  simpa using hdelLI.rank_matrix

-- @node: lem:necessary-deletion-rank
lemma assignedSource_mem_admissibleSources {p n : ℕ} (C : MixingMatrix p n)
    (hpn : p ≤ n) (x : Fin p) (Q H : SquareMatrix n)
    (hM : CompletionFiber C hpn x Q H) :
    assignedSource H hM.monomial (Fin.castLE hpn x) ∈ admissibleSources C x := by
  let j := assignedSource H hM.monomial (Fin.castLE hpn x)
  have hCx : C x j ≠ 0 := by
    let xx := Fin.castLE hpn x
    have hj : H xx j ≠ 0 := (Classical.choose_spec (hM.monomial.1 xx)).1
    have hcol : ∀ k, k ≠ xx → H k j = 0 := by
      intro k hk
      by_contra hkj
      exact hk ((hM.monomial.2 j).unique hkj hj)
    rw [← hM.fixedLaw x j, Matrix.mul_apply, Finset.sum_eq_single xx]
    · exact mul_ne_zero
        (inverse_diagonal_ne_zero_of_delete_det_ne_zero Q xx
          hM.solvable hM.postSolvable) hj
    · intro k _ hk
      rw [hcol k hk, mul_zero]
    · simp
  have hHdet := monomialSourceAssignment_det_ne_zero H hM.monomial
  have hTdet : (Q⁻¹ * H).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv]
    exact mul_ne_zero (by simpa using inv_ne_zero hM.solvable) hHdet
  have hinv : (Q⁻¹ * H)⁻¹ j (Fin.castLE hpn x) ≠ 0 := by
    simpa [j] using inverseMixing_assignedSource_ne_zero Q H hM.solvable
      hM.unitDiagonal hM.monomial (Fin.castLE hpn x)
  simp only [admissibleSources, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hCx, deleteRowCol_rank_of_inverse_entry_ne_zero C hpn x (Q⁻¹ * H)
    hTdet hM.fixedLaw j hinv⟩

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Helpers.KernelMatching
import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Helpers.CitedGates

/-!
# Law-fiber canonicalization and representative invariance
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open MeasureTheory Set

universe u v

def permuteScaleColumns {p n : ℕ} (C : MixingMatrix p n)
    (pi : Equiv.Perm (Fin n)) (scale : Fin n → ℝ) : MixingMatrix p n :=
  fun i k => C i (pi k) * scale k

-- @node: lem:frontier-monomial-invariance
lemma frontier_monomial_invariance {p n : ℕ} (C : MixingMatrix p n)
    (pi : Equiv.Perm (Fin n)) (scale : Fin n → ℝ) (hscale : ∀ k, scale k ≠ 0)
    (x y : Fin p) :
    (∀ k, k ∈ admissibleSources (permuteScaleColumns C pi scale) x ↔
      pi k ∈ admissibleSources C x) ∧
    responseFrontier (permuteScaleColumns C pi scale) x = responseFrontier C x ∧
    effectFrontier (permuteScaleColumns C pi scale) x y = effectFrontier C x y := by
  have hrank (k : Fin n) :
      (deleteRowCol (permuteScaleColumns C pi scale) x k).rank =
        (deleteRowCol C x (pi k)).rank := by
    let e : {l : Fin n // l ≠ k} ≃ {l : Fin n // l ≠ pi k} :=
      { toFun := fun l => ⟨pi l.1, fun h => l.2 (pi.injective h)⟩
        invFun := fun l => ⟨pi.symm l.1, fun h => l.2 (by simpa using congrArg pi h)⟩
        left_inv := by intro l; ext; simp
        right_inv := by intro l; ext; simp }
    let A := (deleteRowCol C x (pi k)).submatrix (Equiv.refl _) e
    let D : Matrix {l : Fin n // l ≠ k} {l : Fin n // l ≠ k} ℝ :=
      Matrix.diagonal (fun l => scale l.1)
    have hmat : deleteRowCol (permuteScaleColumns C pi scale) x k = A * D := by
      ext i l
      simp only [deleteRowCol, permuteScaleColumns, Matrix.submatrix_apply]
      rw [Matrix.mul_apply, Finset.sum_eq_single l]
      · rw [show A i l = C i.1 (pi l.1) by rfl]
        simp [D]
      · intro j _ hj
        simp [D, hj]
      · simp
    rw [hmat, Matrix.rank_mul_eq_left_of_det_ne_zero]
    · exact Matrix.rank_submatrix _ (Equiv.refl _) e
    · rw [Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hscale i.1)
  have hadm (k : Fin n) :
      k ∈ admissibleSources (permuteScaleColumns C pi scale) x ↔
        pi k ∈ admissibleSources C x := by
    simp only [admissibleSources, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hrank k]
    simp [permuteScaleColumns, hscale k]
  refine ⟨hadm, ?_, ?_⟩
  · ext rho
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨pi k, (hadm k).mp hk, ?_⟩
      funext i
      simp only [permuteScaleColumns]
      have hCx : C x (pi k) ≠ 0 :=
        (Finset.mem_filter.mp ((hadm k).mp hk)).2.1
      field_simp [hscale k, hCx]
    · rintro ⟨j, hj, rfl⟩
      refine ⟨pi.symm j, (hadm (pi.symm j)).mpr (by simpa), ?_⟩
      funext i
      simp only [permuteScaleColumns, Equiv.apply_symm_apply]
      have hCx : C x j ≠ 0 := (Finset.mem_filter.mp hj).2.1
      field_simp [hscale (pi.symm j), hCx]
  · ext theta
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨pi k, (hadm k).mp hk, ?_⟩
      simp only [permuteScaleColumns]
      have hCx : C x (pi k) ≠ 0 :=
        (Finset.mem_filter.mp ((hadm k).mp hk)).2.1
      field_simp [hscale k, hCx]
    · rintro ⟨j, hj, rfl⟩
      refine ⟨pi.symm j, (hadm (pi.symm j)).mpr (by simpa), ?_⟩
      simp only [permuteScaleColumns, Equiv.apply_symm_apply]
      have hCx : C x j ≠ 0 := (Finset.mem_filter.mp hj).2.1
      field_simp [hscale (pi.symm j), hCx]

def embedFixedCompletion {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ} (μ : Measure Ω)
    (hpn : p ≤ n) (Q H : SquareMatrix n) (ε : Fin n → Ω → ℝ)
    (hQ : ObservationalSolvability Q) : LawCompletion.{u} p :=
  ⟨Ω, inferInstance, μ, ⟨n, hpn⟩, ⟨(Q, H, ε), hQ⟩⟩

def castLawMatrix {p n : ℕ} (M : LawCompletion.{u} p) (hDim : M.dim = n)
    (A : SquareMatrix M.dim) : SquareMatrix n :=
  fun i j => A (Fin.cast hDim.symm i) (Fin.cast hDim.symm j)

noncomputable def canonicalizedLawAssignment {p n : ℕ} (M : LawCompletion.{u} p)
    (hDim : M.dim = n) (pi : Equiv.Perm (Fin n)) (scale : Fin n → ℝ) : SquareMatrix n :=
  castLawMatrix M hDim M.H * Matrix.diagonal (fun k => (scale k)⁻¹) *
    rowPermutationMatrix pi

lemma canonicalizedLawAssignment_apply {p n : ℕ} (M : LawCompletion.{u} p)
    (hDim : M.dim = n) (pi : Equiv.Perm (Fin n)) (scale : Fin n → ℝ)
    (i j : Fin n) :
    canonicalizedLawAssignment M hDim pi scale i j =
      castLawMatrix M hDim M.H i (pi.symm j) * (scale (pi.symm j))⁻¹ := by
  simp only [canonicalizedLawAssignment, Matrix.mul_apply, rowPermutationMatrix,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (pi.symm j)]
  · rw [Finset.sum_eq_single (pi.symm j)]
    · simp
    · intro k _ hk
      simp [Matrix.diagonal, hk]
    · simp
  · intro k _ hk
    have hneq : pi k ≠ j := by
      intro h
      apply hk
      simpa using congrArg pi.symm h
    simp [hneq]
  · simp

/-- The law-level completion can be rescaled/relabelled into the fixed-`C` fiber without changing
its structural matrix, intervention minor, or response ratios. -/
-- @node: lem:monomial-law-canonicalization
lemma monomial_law_canonicalization {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ) (x : Fin p)
    (M : LawCompletion.{u} p) (hM : LawCompletionFiber (observedLaw μ C ε) x M)
    (hDim : M.dim = n) (pi : Equiv.Perm (Fin n)) (scale : Fin n → ℝ)
    (hscale : ∀ k, scale k ≠ 0)
    (hA : HEq M.observedMixing (permuteScaleColumns C pi scale)) :
    ∃ (hpn : p ≤ n) (Q : SquareMatrix n),
      let HC := canonicalizedLawAssignment M hDim pi scale
      ∃ hFix : CompletionFiber C hpn x Q HC,
      HC = castLawMatrix M hDim M.H * Matrix.diagonal (fun k => (scale k)⁻¹) *
        rowPermutationMatrix pi ∧
      HEq Q M.Q ∧
      PostinterventionSolvability Q (Fin.castLE hpn x) ∧
      (∀ i : Fin p,
        let k := Fin.cast hDim
          (lawAssignedSource (P := observedLaw μ C ε) (x := x) hM i)
        assignedSource HC hFix.monomial (Fin.castLE hpn i) = pi k ∧
          (∃ hAlign : HasUniqueAlignedSource (P := observedLaw μ C ε)
              (x := x) hM C i,
            pi k = alignedSource (P := observedLaw μ C ε) (x := x)
              hM C i hAlign)) ∧
      (∀ (y : Fin p) (hy : y ≠ x),
        equilibriumEffect C hpn x ⟨y, hy⟩ Q HC hFix =
          observedResponse M x hM ⟨y, hy⟩) := by
  subst n
  have hAeq : M.observedMixing = permuteScaleColumns C pi scale := eq_of_heq hA
  have projective_scale (z : Vec p) (s : ℝ) (hs : s ≠ 0) :
      projectiveClass (s • z) = projectiveClass z := by
    ext w
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t * s, mul_ne_zero ht hs, ?_⟩
      simp [smul_smul]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t * s⁻¹, mul_ne_zero ht (inv_ne_zero hs), ?_⟩
      simp [smul_smul, hs]
  have hCdir' : DistinctDirections C := by
    intro j l hjl t heq
    have hab : pi.symm j ≠ pi.symm l := fun h => hjl (pi.symm.injective h)
    apply hM.irreducible.2 (pi.symm j) (pi.symm l) hab
      (scale (pi.symm j) * t * (scale (pi.symm l))⁻¹)
    funext i
    rw [hAeq]
    simp only [Matrix.col_apply, permuteScaleColumns, Equiv.apply_symm_apply,
      Pi.smul_apply, smul_eq_mul]
    have hi := congrFun heq i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    change C i j = t * C i l at hi
    rw [hi]
    field_simp [hscale]
  let HC := canonicalizedLawAssignment M rfl pi scale
  have hmono : MonomialSourceAssignment HC := by
    constructor
    · intro i
      obtain ⟨k, hk, hku⟩ := hM.monomial.1 i
      refine ⟨pi k, ?_, ?_⟩
      · change canonicalizedLawAssignment M rfl pi scale i (pi k) ≠ 0
        rw [canonicalizedLawAssignment_apply]
        simpa [castLawMatrix] using mul_ne_zero hk (inv_ne_zero (hscale k))
      · intro j hj
        change canonicalizedLawAssignment M rfl pi scale i j ≠ 0 at hj
        rw [canonicalizedLawAssignment_apply] at hj
        have horig : M.H i (pi.symm j) ≠ 0 := by
          exact (mul_ne_zero_iff.mp hj).1
        simpa using congrArg pi (hku _ horig)
    · intro j
      obtain ⟨i, hi, hiu⟩ := hM.monomial.2 (pi.symm j)
      refine ⟨i, ?_, ?_⟩
      · change canonicalizedLawAssignment M rfl pi scale i j ≠ 0
        rw [canonicalizedLawAssignment_apply]
        simpa [castLawMatrix] using
          mul_ne_zero hi (inv_ne_zero (hscale (pi.symm j)))
      · intro l hl
        change canonicalizedLawAssignment M rfl pi scale l j ≠ 0 at hl
        rw [canonicalizedLawAssignment_apply] at hl
        exact hiu _ (mul_ne_zero_iff.mp hl).1
  have hfixed : FixedLawMatch C M.2.2.2.1.2 M.Q HC := by
    intro i j
    rw [show HC = M.H * Matrix.diagonal (fun k => (scale k)⁻¹) *
        rowPermutationMatrix pi by rfl]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    simp only [Matrix.mul_apply, rowPermutationMatrix, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (pi.symm j)]
    · rw [Finset.sum_eq_single (pi.symm j)]
      · simp only [Matrix.diagonal_apply_eq, Equiv.apply_symm_apply, if_pos]
        change M.observedMixing i (pi.symm j) * (scale (pi.symm j))⁻¹ = C i j
        rw [hAeq]
        simp [permuteScaleColumns, hscale]
      · intro k _ hk
        simp [Matrix.diagonal, hk]
      · simp
    · intro k _ hk
      have hneq : pi k ≠ j := by
        intro h
        apply hk
        simpa using congrArg pi.symm h
      simp [hneq]
    · simp
  let hFix : CompletionFiber C M.2.2.2.1.2 x M.Q HC :=
    { unitDiagonal := hM.unitDiagonal
      monomial := hmono
      solvable := M.solvable
      fixedLaw := hfixed
      postSolvable := hM.postSolvable }
  refine ⟨M.2.2.2.1.2, M.Q, hFix, rfl, HEq.rfl, hM.postSolvable, ?_, ?_⟩
  · intro i
    dsimp only
    let k := Fin.cast rfl
      (lawAssignedSource (P := observedLaw μ C ε) (x := x) hM i)
    have hk : M.H (M.liftObserved i) k ≠ 0 :=
      (Classical.choose_spec (hM.monomial.1 (M.liftObserved i))).1
    have hkC : HC (M.liftObserved i) (pi k) ≠ 0 := by
      change canonicalizedLawAssignment M rfl pi scale (M.liftObserved i) (pi k) ≠ 0
      rw [canonicalizedLawAssignment_apply]
      simpa [castLawMatrix] using mul_ne_zero hk (inv_ne_zero (hscale k))
    have hassigned : assignedSource HC hFix.monomial (M.liftObserved i) = pi k :=
      ((Classical.choose_spec (hFix.monomial.1 (M.liftObserved i))).2 _ hkC).symm
    refine ⟨hassigned, ?_⟩
    have hcol : M.observedMixing.col k = scale k • C.col (pi k) := by
      funext a
      rw [hAeq]
      change C a (pi k) * scale k = scale k * C a (pi k)
      ring
    have hclass : projectiveClass (M.observedMixing.col k) =
        projectiveClass (C.col (pi k)) := by
      rw [hcol]
      exact projective_scale _ _ (hscale k)
    have hunique : HasUniqueAlignedSource (P := observedLaw μ C ε)
        (x := x) hM C i := by
      refine ⟨pi k, ?_, ?_⟩
      · simpa [k] using hclass
      · intro j hj
        by_contra hne
        have heq : projectiveClass (C.col (pi k)) = projectiveClass (C.col j) :=
          hclass.symm.trans (by simpa [k] using hj)
        have hmem : C.col (pi k) ∈ projectiveClass (C.col (pi k)) :=
          ⟨1, one_ne_zero, by simp⟩
        rw [heq] at hmem
        obtain ⟨t, _ht, ht⟩ := hmem
        exact hCdir' (pi k) j (Ne.symm hne) t ht
    refine ⟨hunique, ?_⟩
    exact (Classical.choose_spec hunique).2 (pi k) (by simpa [k] using hclass)
  · intro y hy
    rw [(lawResponse_eq_inverse_ratio (Ω := Ω) (observedLaw μ C ε) x M hM).2]
    rfl

-- @node: lem:law-fiber-response-rank
lemma lawFiber_response_rank {Ω : Type v} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ) (x : Fin p)
    (hdim : ValidPopulationDimensions p n)
    (hC0 : NonzeroColumns C) (hCdir : DistinctDirections C)
    (hind : ProbabilityTheory.iIndepFun ε μ) (hnd : NondegenerateSources μ ε)
    (hng : NonGaussianSources μ ε)
    (DaiIrreducibleOICAUniqueness_of_gate : DaiIrreducibleOICAUniqueness.{v, u})
    (M : LawCompletion.{u} p) (hM : LawCompletionFiber (observedLaw μ C ε) x M) :
    M.dim = n ∧
    ∃ j : Fin n, ∃ hAlign : HasUniqueAlignedSource
      (P := observedLaw μ C ε) (x := x) hM C x,
    alignedSource (P := observedLaw μ C ε) (x := x) hM C x hAlign = j ∧
      j ∈ admissibleSources C x ∧ C x j ≠ 0 ∧
      (deleteRowCol C x j).rank = p - 1 ∧
      observedResponse M x hM = (fun i => C i.1 j / C x j) ∧
      observedResponse M x hM ∈ responseFrontier C x := by
  have hrefqual : QualitativelyNondegenerateSources μ ε := by
    refine ⟨hnd.1, hnd.2.1, ?_⟩
    intro k
    rintro ⟨c, hc⟩
    have hv := ProbabilityTheory.variance_id_map (hnd.2.1 k)
    rw [hc, ProbabilityTheory.variance_dirac] at hv
    linarith [hnd.2.2 k]
  have hMqual : QualitativelyNondegenerateSources M.measure M.xi := by
    refine ⟨hM.sourceConditions.2.1.1, hM.sourceConditions.2.1.2.1, ?_⟩
    intro k
    rintro ⟨c, hc⟩
    have hv := ProbabilityTheory.variance_id_map (hM.sourceConditions.2.1.2.1 k)
    rw [hc, ProbabilityTheory.variance_dirac] at hv
    linarith [hM.sourceConditions.2.1.2.2 k]
  have href : IsQualitativeIrreducibleICARepresentation μ C ε (observedLaw μ C ε) :=
    ⟨hnd.1, hnd.2.1, hC0, hCdir, hind, hrefqual, rfl⟩
  obtain ⟨hdim, hdirections, _⟩ :=
    DaiIrreducibleOICAUniqueness_of_gate (p := p) (n := n) (m := M.dim)
      (Ω := Ω) (Ξ := M.carrier) inferInstance inferInstance
      μ M.measure C M.observedMixing ε M.xi href hng
      hM.irreducible.1 hM.irreducible.2 hM.sourceConditions.1
      hMqual hM.lawMatch
  have hDim : M.dim = n := hdim.symm
  subst n
  have hmatch (k : Fin M.dim) : ∃! j : Fin M.dim,
      projectiveClass (M.observedMixing.col k) = projectiveClass (C.col j) := by
    have hkA : projectiveClass (M.observedMixing.col k) ∈
        {D | ∃ l, D = projectiveClass (M.observedMixing.col l)} := ⟨k, rfl⟩
    rw [← hdirections] at hkA
    obtain ⟨j, hj⟩ := hkA
    refine ⟨j, hj, ?_⟩
    intro l hl
    by_contra hjl
    have heq : projectiveClass (C.col j) = projectiveClass (C.col l) :=
      hj.symm.trans hl
    have hjmem : C.col j ∈ projectiveClass (C.col j) :=
      ⟨1, one_ne_zero, by simp⟩
    rw [heq] at hjmem
    obtain ⟨t, _ht, ht⟩ := hjmem
    exact hCdir j l (Ne.symm hjl) t ht
  let f : Fin M.dim → Fin M.dim := fun k => Classical.choose (hmatch k)
  have hfclass (k : Fin M.dim) :
      projectiveClass (M.observedMixing.col k) = projectiveClass (C.col (f k)) :=
    (Classical.choose_spec (hmatch k)).1
  have hf : Function.Injective f := by
    intro k l hkl
    by_contra hne
    have heq : projectiveClass (M.observedMixing.col k) =
        projectiveClass (M.observedMixing.col l) := by rw [hfclass k, hfclass l, hkl]
    have hkmem : M.observedMixing.col k ∈
        projectiveClass (M.observedMixing.col k) := ⟨1, one_ne_zero, by simp⟩
    rw [heq] at hkmem
    obtain ⟨t, _ht, ht⟩ := hkmem
    exact hM.irreducible.2 k l hne t ht
  let pi : Equiv.Perm (Fin M.dim) := Equiv.ofBijective f hf.bijective_of_finite
  have hpif (k : Fin M.dim) : pi k = f k := rfl
  have hscale_exists (k : Fin M.dim) : ∃ t : ℝ, t ≠ 0 ∧
      M.observedMixing.col k = t • C.col (pi k) := by
    have hkmem : M.observedMixing.col k ∈
        projectiveClass (M.observedMixing.col k) := ⟨1, one_ne_zero, by simp⟩
    rw [hfclass k, ← hpif] at hkmem
    exact hkmem
  let scale : Fin M.dim → ℝ := fun k => Classical.choose (hscale_exists k)
  have hscale (k : Fin M.dim) : scale k ≠ 0 :=
    (Classical.choose_spec (hscale_exists k)).1
  have hcols (k : Fin M.dim) :
      M.observedMixing.col k = scale k • C.col (pi k) :=
    (Classical.choose_spec (hscale_exists k)).2
  have hA : HEq M.observedMixing (permuteScaleColumns C pi scale) := by
    apply heq_of_eq
    funext i k
    calc
      M.observedMixing i k = (scale k • C.col (pi k)) i := congrFun (hcols k) i
      _ = C i (pi k) * scale k := by
        change scale k * C i (pi k) = C i (pi k) * scale k
        exact mul_comm _ _
  obtain ⟨hpn, Q, hFix, _hHC, _hQ, _hpost, hassign, hresponse⟩ :=
    monomial_law_canonicalization μ C ε x M hM rfl pi scale hscale hA
  let k := lawAssignedSource (P := observedLaw μ C ε) (x := x) hM x
  obtain ⟨hassigned, hAlign, halign⟩ := hassign x
  let j : Fin M.dim := pi k
  have hj : j ∈ admissibleSources C x := by
    have hj' := assignedSource_mem_admissibleSources C hpn x Q
      (canonicalizedLawAssignment M rfl pi scale) hFix
    rw [hassigned] at hj'
    exact hj'
  have hjparts := (Finset.mem_filter.mp hj).2
  have hrho : observedResponse M x hM = fun i => C i.1 j / C x j := by
    funext i
    have hratio := interventionRatio C hpn x i Q
      (canonicalizedLawAssignment M rfl pi scale) hFix
    rw [hassigned] at hratio
    exact (hresponse i.1 i.2).symm.trans hratio.2
  refine ⟨rfl, j, hAlign, ?_, hj, hjparts.1, hjparts.2, hrho, ?_⟩
  · exact halign.symm
  · exact ⟨j, hj, hrho⟩

-- @node: lem:canonical-exact-c-law-witness
lemma canonical_exact_law_witness {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (C : MixingMatrix p n) (ε : Fin n → Ω → ℝ) (x : Fin p)
    (hdim : ValidPopulationDimensions p n)
    (hC : FullRowRank C) (hC0 : NonzeroColumns C) (hCdir : DistinctDirections C)
    (hind : ProbabilityTheory.iIndepFun ε μ) (hnd : NondegenerateSources μ ε)
    (hng : NonGaussianSources μ ε) :
    ∃ D : CertificateData C x, ∀ (j : Fin n) (hj : j ∈ admissibleSources C x),
      let Q := (certifiedCompletion C x D j hj).1
      let H := (certifiedCompletion C x D j hj).2
      let hFix := D.valid ⟨j, hj⟩
      let M := embedFixedCompletion μ D.dim_le Q H ε hFix.solvable
      ∃ hLaw : LawCompletionFiber (observedLaw μ C ε) x M,
        ∃ hAlign : HasUniqueAlignedSource (P := observedLaw μ C ε)
          (x := x) hLaw C x,
        alignedSource (P := observedLaw μ C ε) (x := x) hLaw C x hAlign = j ∧
        observedResponse M x hLaw = (fun i => C i.1 j / C x j) ∧
        (IsRationalMatrix C → IsRationalMatrix Q ∧ IsRationalMatrix H) := by
  obtain ⟨D, hcert⟩ := certifiedCompletion_mem_fiber C x hdim hC
  refine ⟨D, ?_⟩
  intro j hj
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
      · intro j k hjk
        rw [hmix]
        exact hCdir j k hjk
    · change observedLaw μ M.observedMixing ε = observedLaw μ C ε
      rw [hmix]
      rfl
  refine ⟨hLaw, ?_⟩
  have hassigned : assignedSource H hFix.monomial (Fin.castLE D.dim_le x) = j :=
    D.assigned ⟨j, hj⟩
  have hclass : projectiveClass (M.observedMixing.col
      (lawAssignedSource (P := observedLaw μ C ε) (x := x) hLaw x)) =
      projectiveClass (C.col j) := by
    rw [show lawAssignedSource (P := observedLaw μ C ε) (x := x) hLaw x = j by
      exact hassigned]
    rw [hmix]
    rfl
  have hunique : HasUniqueAlignedSource (P := observedLaw μ C ε)
      (x := x) hLaw C x := by
    refine ⟨j, hclass, ?_⟩
    intro k hk
    by_contra hkj
    have heq : projectiveClass (C.col j) = projectiveClass (C.col k) :=
      hclass.symm.trans hk
    have hjmem : C.col j ∈ projectiveClass (C.col j) :=
      ⟨1, one_ne_zero, by simp⟩
    obtain ⟨t, _ht, heqt⟩ : C.col j ∈ projectiveClass (C.col k) := heq ▸ hjmem
    exact hCdir j k (Ne.symm hkj) t heqt
  refine ⟨hunique, ?_, ?_, ?_⟩
  · exact ((Classical.choose_spec hunique).2 j hclass).symm
  · rw [(lawResponse_eq_inverse_ratio (Ω := Ω) (observedLaw μ C ε) x M hLaw).2]
    funext i
    change equilibriumEffect C D.dim_le x i Q H hFix = C i.1 j / C x j
    simpa [hassigned] using (interventionRatio C D.dim_le x i Q H hFix).2
  · exact (hcert j hj).2.2.2.2

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

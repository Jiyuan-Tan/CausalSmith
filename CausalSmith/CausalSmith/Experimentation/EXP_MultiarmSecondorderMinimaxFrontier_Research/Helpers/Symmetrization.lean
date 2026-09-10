import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.OrbitRiskBridge

/-! Simultaneous unit permutation and exact orbit-procedure correspondence. -/

open scoped BigOperators

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

variable {K n : ℕ} (c : Contrast ℝ K)

/-- Simultaneous invariance of both the assignment law and estimator. -/
def IsInvariantProcedure (p : Procedure K n c) : Prop :=
  (∀ (σ : Equiv.Perm (Unit n)) A, p.1.p (permuteAssign σ A) = p.1.p A) ∧
  (∀ (σ : Equiv.Perm (Unit n)) A y,
    p.2 (permuteAssign σ A) (permuteObserved σ y) = p.2 A y)

/-- A procedure is invariant when simultaneous relabeling of units leaves both its assignment probabilities and its estimates unchanged. -/
abbrev InvariantProcedure (K n : ℕ) (c : Contrast ℝ K) :=
  {p : Procedure K n c // IsInvariantProcedure c p}

/-- The design and estimator are the stated common-permutation averages. -/
noncomputable def IsPermutationAverage
    (p pbar : Procedure K n c) : Prop := by
  classical
  letI := Fintype.ofFinite (Equiv.Perm (Unit n))
  exact
    (∀ A, pbar.1.p A =
      (Fintype.card (Equiv.Perm (Unit n)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A)) ∧
    (∀ A y, (pbar.2 A y : ℝ) =
      if h : 0 < ∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A) then
        clip c ((∑ σ : Equiv.Perm (Unit n),
          p.1.p (permuteAssign σ A) *
            (p.2 (permuteAssign σ A) (permuteObserved σ y) : ℝ)) /
          ∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A))
      else 0)

/-- The paper's averaged-permutation risk domination, not a pointwise comparison. -/
noncomputable def OrbitAverageDomination
    (p : Procedure K n c) (q : OrbitProcedure K n c) : Prop := by
  classical
  letI := Fintype.ofFinite (Equiv.Perm (Unit n))
  exact ∀ z,
      orbitRisk c q (scheduleCounts z) ≤
        (Fintype.card (Equiv.Perm (Unit n)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Unit n), labeledRisk c p (permuteSchedule σ z)

/-- Every labeled procedure has an averaged invariant representative. -/
noncomputable def LosslessSymmetrization (n : ℕ) (c : Contrast ℝ K) : Prop := by
  classical
  letI := Fintype.ofFinite (Equiv.Perm (Unit n))
  exact ∀ p : Procedure K n c,
    ∃ (pbar : Procedure K n c) (q : OrbitProcedure K n c),
      IsInvariantProcedure c pbar ∧ IsPermutationAverage c p pbar ∧
      (∀ z,
        labeledRisk c pbar z ≤
          (Fintype.card (Equiv.Perm (Unit n)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Unit n), labeledRisk c p (permuteSchedule σ z)) ∧
      OrbitAverageDomination c p q

/-- Explicit equations identifying an invariant labeled procedure with `(π,δ)`. -/
def RealizesOrbitProcedure (p : Procedure K n c) (q : OrbitProcedure K n c) : Prop :=
  (∀ A, p.1.p A = q.1.p (assignmentCounts A) / allocationOrbitCard (assignmentCounts A)) ∧
  (∀ A y, (p.2 A y : ℝ) = (q.2 (assignmentCounts A) (observedCounts A y) : ℝ))

/-- Exact two-way identification of invariant labeled procedures with `(π,δ)`. -/
def ExactInvariantProcedureCorrespondence (n : ℕ) (c : Contrast ℝ K) : Prop :=
  ∃ e : InvariantProcedure K n c ≃ OrbitProcedure K n c,
    (∀ p, RealizesOrbitProcedure c p.1 (e p)) ∧
    (∀ q, RealizesOrbitProcedure c (e.symm q).1 q) ∧
    (∀ p z, orbitRisk c (e p) (scheduleCounts z) = labeledRisk c p.1 z)

/-- An allocation representative chooses a canonical labeled assignment for each allocation-count vector. -/
noncomputable def allocationRepresentative (r : AllocVec K n) : Assign K n :=
  Classical.choose (assignmentCounts_surjective r)

/-- [the allocation representative spec property holds](goal). -/
lemma allocationRepresentative_spec (r : AllocVec K n) :
    assignmentCounts (allocationRepresentative r) = r :=
  Classical.choose_spec (assignmentCounts_surjective r)

/-- An observation representative chooses a canonical observed-outcome vector for each compatible allocation and success-count pair. -/
noncomputable def observationRepresentative (r : AllocVec K n) (x : ObsVec r) :
    Assign K n × ObservedOutcome n :=
  let h := observedCounts_realizable r x
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

/-- [the observation representative assignment property holds](goal). -/
lemma observationRepresentative_assignment (r : AllocVec K n) (x : ObsVec r) :
    assignmentCounts (observationRepresentative r x).1 = r := by
  exact (Classical.choose_spec (Classical.choose_spec (observedCounts_realizable r x))).1

/-- [the observation representative counts property holds](goal). -/
lemma observationRepresentative_counts (r : AllocVec K n) (x : ObsVec r) :
    (observedCounts (observationRepresentative r x).1
      (observationRepresentative r x).2).1 = x.1 := by
  funext a
  apply Fin.ext
  exact (Classical.choose_spec (Classical.choose_spec (observedCounts_realizable r x))).2 a

private lemma orbitEstimator_eq_of_counts (q : OrbitEstimator K n c)
    {r s : AllocVec K n} (h : r = s) (x : ObsVec r) (y : ObsVec s)
    (hxy : x.1 = y.1) : q r x = q s y := by
  subst s
  congr 1
  exact Subtype.ext hxy

private lemma finiteDesign_ext {Ω : Type*} [Fintype Ω]
    (D E : Causalean.Experimentation.DesignBased.FiniteDesign Ω)
    (h : ∀ x, D.p x = E.p x) : D = E := by
  cases D with
  | mk dp hdp hsumD =>
    cases E with
    | mk ep hep hsumE =>
      simp only [Causalean.Experimentation.DesignBased.FiniteDesign.mk.injEq]
      funext x
      exact h x

/-- Inflate an orbit procedure uniformly over each labeled allocation orbit. -/
noncomputable def orbitToInvariantProcedure (q : OrbitProcedure K n c) :
    InvariantProcedure K n c := by
  classical
  let D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign K n) :=
    { p := fun A => q.1.p (assignmentCounts A) / allocationOrbitCard (assignmentCounts A)
      p_nonneg := fun A => div_nonneg (q.1.p_nonneg _) (Nat.cast_nonneg _)
      p_sum := by
        rw [← Finset.sum_fiberwise Finset.univ assignmentCounts
          (fun A => q.1.p (assignmentCounts A) /
            allocationOrbitCard (assignmentCounts A))]
        calc
          ∑ r : AllocVec K n,
              ∑ A : Assign K n with assignmentCounts A = r,
                q.1.p (assignmentCounts A) / allocationOrbitCard (assignmentCounts A) =
              ∑ r : AllocVec K n, q.1.p r := by
                apply Finset.sum_congr rfl
                intro r _
                have hr : (allocationOrbitCard r : ℝ) ≠ 0 := by
                  exact_mod_cast (Nat.ne_of_gt (allocationOrbitCard_pos r))
                rw [Finset.sum_congr rfl (fun A hA => by
                  simp only [Finset.mem_filter] at hA
                  rw [hA.2])]
                rw [Finset.sum_const, nsmul_eq_mul]
                have hcard : (Finset.univ.filter fun A : Assign K n =>
                    assignmentCounts A = r).card =
                    allocationOrbitCard r := by
                  unfold allocationOrbitCard
                  simp only [Fintype.card_subtype]
                rw [hcard]
                norm_num
                exact mul_div_cancel₀ _ hr
          _ = 1 := q.1.p_sum }
  let est : Estimator K n c := fun A y => q.2 (assignmentCounts A) (observedCounts A y)
  refine ⟨(D, est), ?_⟩
  constructor
  · intro σ A
    simp only [D]
    rw [assignmentCounts_permute]
  · intro σ A y
    simp only [est]
    have hA := assignmentCounts_permute A σ
    have hy := observedCounts_permute A y σ
    exact orbitEstimator_eq_of_counts c q.2 hA _ _ hy

/-- [the orbit to invariant procedure realizes property holds](goal). -/
lemma orbitToInvariantProcedure_realizes (q : OrbitProcedure K n c) :
    RealizesOrbitProcedure c (orbitToInvariantProcedure c q).1 q := by
  constructor
  · intro A
    simp [orbitToInvariantProcedure]
  · intro A y
    simp [orbitToInvariantProcedure]

private lemma invariant_design_eq_of_counts (p : Procedure K n c)
    (hp : IsInvariantProcedure c p) {A B : Assign K n}
    (hAB : assignmentCounts A = assignmentCounts B) : p.1.p A = p.1.p B := by
  obtain ⟨σ, hσ⟩ := (assignmentCounts_eq_iff_perm A B).mp hAB
  rw [← hσ]
  exact (hp.1 σ A).symm

private lemma invariant_estimator_eq_of_counts (p : Procedure K n c)
    (hp : IsInvariantProcedure c p) {A B : Assign K n}
    {y v : ObservedOutcome n}
    (hA : assignmentCounts A = assignmentCounts B)
    (hx : (observedCounts A y).1 = (observedCounts B v).1) :
    p.2 A y = p.2 B v := by
  obtain ⟨σ, hσA, hσy⟩ :=
    (assignmentObservedCounts_eq_iff_perm A B y v).mp ⟨hA, hx⟩
  rw [← hσA, ← hσy]
  exact (hp.2 σ A y).symm

/-- Collapse an invariant labeled procedure to allocation and observation orbits. -/
noncomputable def invariantToOrbitProcedure (p : InvariantProcedure K n c) :
    OrbitProcedure K n c := by
  classical
  let D : Causalean.Experimentation.DesignBased.FiniteDesign (AllocVec K n) :=
    { p := fun r => (allocationOrbitCard r : ℝ) *
          p.1.1.p (allocationRepresentative r)
      p_nonneg := fun r => mul_nonneg (Nat.cast_nonneg _) (p.1.1.p_nonneg _)
      p_sum := by
        calc
          ∑ r : AllocVec K n, (allocationOrbitCard r : ℝ) *
              p.1.1.p (allocationRepresentative r) =
              ∑ r : AllocVec K n,
                ∑ A : Assign K n with assignmentCounts A = r, p.1.1.p A := by
                  apply Finset.sum_congr rfl
                  intro r _
                  have hrep : assignmentCounts (allocationRepresentative r) = r :=
                    allocationRepresentative_spec r
                  rw [Finset.sum_congr rfl (fun A hA => by
                    simp only [Finset.mem_filter] at hA
                    rw [invariant_design_eq_of_counts (c := c) p.1 p.2
                      (hA.2.trans hrep.symm)])]
                  rw [Finset.sum_const, nsmul_eq_mul]
                  congr 1
                  norm_num
                  unfold allocationOrbitCard
                  simp only [Fintype.card_subtype]
          _ = ∑ A : Assign K n, p.1.1.p A :=
            Finset.sum_fiberwise Finset.univ assignmentCounts (fun A => p.1.1.p A)
          _ = 1 := p.1.1.p_sum }
  let est : OrbitEstimator K n c := fun r x =>
    p.1.2 (observationRepresentative r x).1 (observationRepresentative r x).2
  exact (D, est)

/-- [the invariant to orbit procedure realizes property holds](goal). -/
lemma invariantToOrbitProcedure_realizes (p : InvariantProcedure K n c) :
    RealizesOrbitProcedure c p.1 (invariantToOrbitProcedure c p) := by
  classical
  constructor
  · intro A
    have hcard : (allocationOrbitCard (assignmentCounts A) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (allocationOrbitCard_pos (assignmentCounts A)))
    rw [show (invariantToOrbitProcedure c p).1.p (assignmentCounts A) =
        (allocationOrbitCard (assignmentCounts A) : ℝ) *
          p.1.1.p (allocationRepresentative (assignmentCounts A)) by
      simp [invariantToOrbitProcedure]]
    rw [mul_div_cancel_left₀ _ hcard]
    exact invariant_design_eq_of_counts (c := c) p.1 p.2
      ((allocationRepresentative_spec (assignmentCounts A)).symm)
  · intro A y
    change (p.1.2 A y : ℝ) =
      (p.1.2 (observationRepresentative (assignmentCounts A) (observedCounts A y)).1
        (observationRepresentative (assignmentCounts A) (observedCounts A y)).2 : ℝ)
    congr 1
    apply invariant_estimator_eq_of_counts (c := c) p.1 p.2
    · exact (observationRepresentative_assignment
        (assignmentCounts A) (observedCounts A y)).symm
    · exact (observationRepresentative_counts
        (assignmentCounts A) (observedCounts A y)).symm

private lemma orbitInvariant_left_inv (p : InvariantProcedure K n c) :
    orbitToInvariantProcedure c (invariantToOrbitProcedure c p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · apply finiteDesign_ext
    intro A
    exact (orbitToInvariantProcedure_realizes c
      (invariantToOrbitProcedure c p)).1 A |>.trans
        ((invariantToOrbitProcedure_realizes c p).1 A).symm
  · funext A y
    apply Subtype.ext
    exact (orbitToInvariantProcedure_realizes c
      (invariantToOrbitProcedure c p)).2 A y |>.trans
        ((invariantToOrbitProcedure_realizes c p).2 A y).symm

private lemma orbitInvariant_right_inv (q : OrbitProcedure K n c) :
    invariantToOrbitProcedure c (orbitToInvariantProcedure c q) = q := by
  classical
  apply Prod.ext
  · apply finiteDesign_ext
    intro r
    have hcard : (allocationOrbitCard r : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (allocationOrbitCard_pos r))
    change (allocationOrbitCard r : ℝ) *
        (q.1.p (assignmentCounts (allocationRepresentative r)) /
          allocationOrbitCard (assignmentCounts (allocationRepresentative r))) = q.1.p r
    rw [allocationRepresentative_spec]
    exact mul_div_cancel₀ _ hcard
  · funext r x
    change q.2 (assignmentCounts (observationRepresentative r x).1)
        (observedCounts (observationRepresentative r x).1
          (observationRepresentative r x).2) = q.2 r x
    exact orbitEstimator_eq_of_counts c q.2
      (observationRepresentative_assignment r x) _ _
      (observationRepresentative_counts r x)

/-- The explicit equivalence between invariant labeled and orbit procedures. -/
noncomputable def invariantOrbitEquiv (K n : ℕ) (c : Contrast ℝ K) :
    InvariantProcedure K n c ≃ OrbitProcedure K n c where
  toFun := invariantToOrbitProcedure c
  invFun := orbitToInvariantProcedure c
  left_inv := orbitInvariant_left_inv c
  right_inv := orbitInvariant_right_inv c

/-- [the exact invariant procedure correspondence property holds](goal). -/
lemma exact_invariant_procedure_correspondence :
    ExactInvariantProcedureCorrespondence n c := by
  refine ⟨invariantOrbitEquiv K n c, ?_, ?_, ?_⟩
  · exact invariantToOrbitProcedure_realizes c
  · intro q
    exact orbitToInvariantProcedure_realizes c q
  · intro p z
    exact (labeledRisk_eq_orbitRisk_of_realizes c p.1
      (invariantOrbitEquiv K n c p)
      ((invariantToOrbitProcedure_realizes c p).1)
      ((invariantToOrbitProcedure_realizes c p).2) z).symm

private lemma permuteAssign_comp (σ τ : Equiv.Perm (Unit n)) (A : Assign K n) :
    permuteAssign σ (permuteAssign τ A) = permuteAssign (τ.trans σ) A := by
  funext i
  simp [permuteAssign]

private lemma permuteObserved_comp (σ τ : Equiv.Perm (Unit n)) (y : ObservedOutcome n) :
    permuteObserved σ (permuteObserved τ y) = permuteObserved (τ.trans σ) y := by
  funext i
  simp [permuteObserved]

private def leftComposePerm (τ : Equiv.Perm (Unit n)) :
    Equiv.Perm (Equiv.Perm (Unit n)) where
  toFun σ := τ.trans σ
  invFun σ := τ.symm.trans σ
  left_inv σ := by ext i; simp
  right_inv σ := by ext i; simp

/-- The simultaneous permutation average appearing in the paper. -/
noncomputable def permutationAverageProcedure (p : Procedure K n c) : Procedure K n c := by
  classical
  letI := Fintype.ofFinite (Equiv.Perm (Unit n))
  let M : ℝ := Fintype.card (Equiv.Perm (Unit n))
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  let D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign K n) :=
    { p := fun A => M⁻¹ * ∑ σ : Equiv.Perm (Unit n),
          p.1.p (permuteAssign σ A)
      p_nonneg := fun A => mul_nonneg (inv_nonneg.mpr hMpos.le)
        (Finset.sum_nonneg fun _ _ => p.1.p_nonneg _)
      p_sum := by
        rw [← Finset.mul_sum]
        rw [Finset.sum_comm]
        have hσ : ∀ σ : Equiv.Perm (Unit n),
            ∑ A : Assign K n, p.1.p (permuteAssign σ A) = 1 := by
          intro σ
          let e : Assign K n ≃ Assign K n :=
            { toFun := permuteAssign σ
              invFun := permuteAssign σ.symm
              left_inv := fun A => by funext i; simp [permuteAssign]
              right_inv := fun A => by funext i; simp [permuteAssign] }
          simpa [e] using (e.sum_comp p.1.p).trans p.1.p_sum
        simp_rw [hσ]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change M⁻¹ * (M * 1) = 1
        field_simp }
  let est : Estimator K n c := fun A y =>
    if h : 0 < ∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A) then
      ⟨clip c ((∑ σ : Equiv.Perm (Unit n),
          p.1.p (permuteAssign σ A) *
            (p.2 (permuteAssign σ A) (permuteObserved σ y) : ℝ)) /
        ∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A)),
        clip_mem c _⟩
    else ⟨0, by
      have hLc : 0 ≤ Lc c := Finset.sum_nonneg fun _ _ => abs_nonneg _
      constructor <;> linarith⟩
  exact (D, est)

/-- [the permutation average procedure spec property holds](goal). -/
lemma permutationAverageProcedure_spec (p : Procedure K n c) :
    IsPermutationAverage c p (permutationAverageProcedure c p) := by
  classical
  letI := Fintype.ofFinite (Equiv.Perm (Unit n))
  constructor
  · intro A
    simp [permutationAverageProcedure]
  · intro A y
    simp only [permutationAverageProcedure]
    split <;> rfl

/-- [the permutation average procedure invariant property holds](goal). -/
lemma permutationAverageProcedure_invariant (p : Procedure K n c) :
    IsInvariantProcedure c (permutationAverageProcedure c p) := by
  classical
  letI := Fintype.ofFinite (Equiv.Perm (Unit n))
  constructor
  · intro τ A
    simp only [permutationAverageProcedure]
    congr 1
    rw [show (∑ σ : Equiv.Perm (Unit n),
        p.1.p (permuteAssign σ (permuteAssign τ A))) =
        ∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign (τ.trans σ) A) by
          apply Finset.sum_congr rfl
          intro σ _
          rw [permuteAssign_comp]]
    exact Equiv.sum_comp (leftComposePerm τ)
      (fun σ => p.1.p (permuteAssign σ A))
  · intro τ A y
    apply Subtype.ext
    simp only [permutationAverageProcedure]
    have hden : (∑ σ : Equiv.Perm (Unit n),
          p.1.p (permuteAssign σ (permuteAssign τ A))) =
        ∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A) := by
      simp_rw [permuteAssign_comp]
      exact Equiv.sum_comp (leftComposePerm τ)
        (fun σ => p.1.p (permuteAssign σ A))
    have hnum : (∑ σ : Equiv.Perm (Unit n),
          p.1.p (permuteAssign σ (permuteAssign τ A)) *
            (p.2 (permuteAssign σ (permuteAssign τ A))
              (permuteObserved σ (permuteObserved τ y)) : ℝ)) =
        ∑ σ : Equiv.Perm (Unit n),
          p.1.p (permuteAssign σ A) *
            (p.2 (permuteAssign σ A) (permuteObserved σ y) : ℝ) := by
      simp_rw [permuteAssign_comp, permuteObserved_comp]
      exact Equiv.sum_comp (leftComposePerm τ) (fun σ =>
        p.1.p (permuteAssign σ A) *
          (p.2 (permuteAssign σ A) (permuteObserved σ y) : ℝ))
    by_cases h : 0 < ∑ σ : Equiv.Perm (Unit n),
        p.1.p (permuteAssign σ (permuteAssign τ A))
    · have h' : 0 < ∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A) :=
        hden ▸ h
      simp only [dif_pos h, dif_pos h', Set.mem_Icc, Subtype.coe_mk]
      rw [hnum, hden]
    · have h' : ¬ 0 < ∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A) := by
        intro hp
        exact h (hden.symm ▸ hp)
      simp only [dif_neg h, dif_neg h', Set.mem_Icc, Subtype.coe_mk]

private lemma weighted_mean_sq_le {ι : Type*} [Fintype ι]
    (w a : ι → ℝ) (t : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hS : 0 < ∑ i, w i) :
    (∑ i, w i) * ((∑ i, w i * a i) / (∑ i, w i) - t) ^ 2 ≤
      ∑ i, w i * (a i - t) ^ 2 := by
  classical
  let S := ∑ i, w i
  have hsqrt (i : ι) : Real.sqrt (w i) ^ 2 = w i := Real.sq_sqrt (hw i)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * (a i - t))
  have hleft : (∑ i, Real.sqrt (w i) *
      (Real.sqrt (w i) * (a i - t))) = ∑ i, w i * (a i - t) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, ← pow_two, hsqrt]
  have hfirst : (∑ i, Real.sqrt (w i) ^ 2) = S := by
    simp_rw [hsqrt]
    rfl
  have hsecond : (∑ i, (Real.sqrt (w i) * (a i - t)) ^ 2) =
      ∑ i, w i * (a i - t) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, hsqrt]
  rw [hleft, hfirst, hsecond] at hcs
  have hmean : (∑ i, w i * a i) / S - t =
      (∑ i, w i * (a i - t)) / S := by
    have hsum : ∑ i, w i * (a i - t) = (∑ i, w i * a i) - S * t := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    rw [hsum]
    have hcancel : S * t / S = t := mul_div_cancel_left₀ t (ne_of_gt hS)
    rw [sub_div, hcancel]
  change S * ((∑ i, w i * a i) / S - t) ^ 2 ≤ _
  rw [hmean, div_pow]
  calc
    S * ((∑ i, w i * (a i - t)) ^ 2 / S ^ 2) =
        (∑ i, w i * (a i - t)) ^ 2 / S := by field_simp
    _ ≤ (S * ∑ i, w i * (a i - t) ^ 2) / S :=
      div_le_div_of_nonneg_right hcs hS.le
    _ = ∑ i, w i * (a i - t) ^ 2 :=
      mul_div_cancel_left₀ _ (ne_of_gt hS)

private lemma permutationWeightedMean_mem (p : Procedure K n c)
    (A : Assign K n) (y : ObservedOutcome n)
    (hS : by
      classical
      letI := Fintype.ofFinite (Equiv.Perm (Unit n))
      exact 0 < ∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A)) : by
  classical
  letI := Fintype.ofFinite (Equiv.Perm (Unit n))
  exact (∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A) *
        (p.2 (permuteAssign σ A) (permuteObserved σ y) : ℝ)) /
        ∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A) ∈
      Set.Icc (-Lc c / 2) (Lc c / 2) := by
  classical
  letI := Fintype.ofFinite (Equiv.Perm (Unit n))
  have hnonneg (σ : Equiv.Perm (Unit n)) : 0 ≤ p.1.p (permuteAssign σ A) :=
    p.1.p_nonneg _
  constructor
  · apply (le_div_iff₀ hS).mpr
    calc
      (-Lc c / 2) * (∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A)) =
          ∑ σ : Equiv.Perm (Unit n),
            p.1.p (permuteAssign σ A) * (-Lc c / 2) := by
              rw [← Finset.sum_mul]
              ring
      _ ≤ ∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A) *
          (p.2 (permuteAssign σ A) (permuteObserved σ y) : ℝ) := by
            apply Finset.sum_le_sum
            intro σ _
            exact mul_le_mul_of_nonneg_left
              (p.2 (permuteAssign σ A) (permuteObserved σ y)).property.1 (hnonneg σ)
  · apply (div_le_iff₀ hS).mpr
    calc
      ∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A) *
          (p.2 (permuteAssign σ A) (permuteObserved σ y) : ℝ) ≤
          ∑ σ : Equiv.Perm (Unit n),
            p.1.p (permuteAssign σ A) * (Lc c / 2) := by
              apply Finset.sum_le_sum
              intro σ _
              exact mul_le_mul_of_nonneg_left
                (p.2 (permuteAssign σ A) (permuteObserved σ y)).property.2 (hnonneg σ)
      _ = (Lc c / 2) *
          (∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A)) := by
        rw [← Finset.sum_mul]
        ring

private lemma tauC_permuteSchedule (σ : Equiv.Perm (Unit n)) (z : Schedule K n) :
    tauC c (permuteSchedule σ z) = tauC c z := by
  classical
  unfold tauC permuteSchedule
  congr 1
  simpa using Equiv.sum_comp σ.symm
    (fun i : Unit n => ∑ a, c a * if z i a then 1 else 0)

private lemma obsOutcome_permute (σ : Equiv.Perm (Unit n))
    (z : Schedule K n) (A : Assign K n) :
    obsOutcome (permuteSchedule σ z) (permuteAssign σ A) =
      permuteObserved σ (obsOutcome z A) := by
  funext i
  rfl

private lemma labeledRisk_permute_eq (p : Procedure K n c)
    (σ : Equiv.Perm (Unit n)) (z : Schedule K n) :
    labeledRisk c p (permuteSchedule σ z) =
      ∑ A : Assign K n, p.1.p (permuteAssign σ A) *
        ((p.2 (permuteAssign σ A) (permuteObserved σ (obsOutcome z A)) : ℝ) -
          tauC c z) ^ 2 := by
  classical
  let e : Assign K n ≃ Assign K n :=
    { toFun := permuteAssign σ
      invFun := permuteAssign σ.symm
      left_inv := fun A => by funext i; simp [permuteAssign]
      right_inv := fun A => by funext i; simp [permuteAssign] }
  unfold labeledRisk Causalean.Experimentation.DesignBased.FiniteDesign.mse
    Causalean.Experimentation.DesignBased.FiniteDesign.E
  rw [tauC_permuteSchedule c]
  rw [← e.sum_comp (fun A => p.1.p A *
    ((p.2 A (obsOutcome (permuteSchedule σ z) A) : ℝ) - tauC c z) ^ 2)]
  apply Finset.sum_congr rfl
  intro A _
  rw [show e A = permuteAssign σ A by rfl, obsOutcome_permute]

private lemma labeledRisk_permutationAverage_le (p : Procedure K n c)
    (z : Schedule K n) : by
  classical
  letI := Fintype.ofFinite (Equiv.Perm (Unit n))
  exact labeledRisk c (permutationAverageProcedure c p) z ≤
    (Fintype.card (Equiv.Perm (Unit n)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Unit n), labeledRisk c p (permuteSchedule σ z) := by
  classical
  letI := Fintype.ofFinite (Equiv.Perm (Unit n))
  let M : ℝ := Fintype.card (Equiv.Perm (Unit n))
  have hMinv : 0 ≤ M⁻¹ := by
    dsimp [M]
    positivity
  rw [show (∑ σ : Equiv.Perm (Unit n),
      labeledRisk c p (permuteSchedule σ z)) =
      ∑ σ : Equiv.Perm (Unit n), ∑ A : Assign K n,
        p.1.p (permuteAssign σ A) *
          ((p.2 (permuteAssign σ A)
            (permuteObserved σ (obsOutcome z A)) : ℝ) - tauC c z) ^ 2 by
        apply Finset.sum_congr rfl
        intro σ _
        exact labeledRisk_permute_eq c p σ z]
  unfold labeledRisk Causalean.Experimentation.DesignBased.FiniteDesign.mse
    Causalean.Experimentation.DesignBased.FiniteDesign.E
  rw [Finset.sum_congr rfl (fun A _ => by
    rw [(permutationAverageProcedure_spec c p).1 A])]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  rw [mul_assoc]
  have hmInv : 0 < (Fintype.card (Equiv.Perm (Unit n)) : ℝ)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hmInv.le
  let S := ∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A)
  have hSnonneg : 0 ≤ S := Finset.sum_nonneg fun _ _ => p.1.p_nonneg _
  change S * (((permutationAverageProcedure c p).2 A (obsOutcome z A) : ℝ) -
      tauC c z) ^ 2 ≤
    ∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A) *
      ((p.2 (permuteAssign σ A) (permuteObserved σ (obsOutcome z A)) : ℝ) -
        tauC c z) ^ 2
  by_cases hS : 0 < S
  · let μ := (∑ σ : Equiv.Perm (Unit n), p.1.p (permuteAssign σ A) *
        (p.2 (permuteAssign σ A)
          (permuteObserved σ (obsOutcome z A)) : ℝ)) / S
    have hμmem : μ ∈ Set.Icc (-Lc c / 2) (Lc c / 2) := by
      exact permutationWeightedMean_mem c p A (obsOutcome z A) hS
    have hclip : clip c μ = μ := by
      simp [clip, min_eq_right hμmem.2, max_eq_right hμmem.1]
    have hest : ((permutationAverageProcedure c p).2 A (obsOutcome z A) : ℝ) = μ := by
      have havg := (permutationAverageProcedure_spec c p).2 A (obsOutcome z A)
      rw [dif_pos hS] at havg
      exact havg.trans hclip
    rw [hest]
    exact weighted_mean_sq_le
      (fun σ : Equiv.Perm (Unit n) => p.1.p (permuteAssign σ A))
      (fun σ => (p.2 (permuteAssign σ A)
        (permuteObserved σ (obsOutcome z A)) : ℝ)) (tauC c z)
      (fun σ => p.1.p_nonneg _) hS
  · have hSzero : S = 0 := le_antisymm (le_of_not_gt hS) hSnonneg
    rw [hSzero, zero_mul]
    exact Finset.sum_nonneg fun σ _ => mul_nonneg (p.1.p_nonneg _) (sq_nonneg _)

/-- [averaging any labeled procedure over unit permutations produces an invariant procedure without increasing worst-case risk, and invariant procedures correspond exactly to orbit procedures](goal). -/
lemma lossless_symmetrization : LosslessSymmetrization n c := by
  intro p
  let pbar := permutationAverageProcedure c p
  have hinv : IsInvariantProcedure c pbar := permutationAverageProcedure_invariant c p
  let pinv : InvariantProcedure K n c := ⟨pbar, hinv⟩
  let q := invariantToOrbitProcedure c pinv
  refine ⟨pbar, q, hinv, permutationAverageProcedure_spec c p,
    labeledRisk_permutationAverage_le c p, ?_⟩
  unfold OrbitAverageDomination
  intro z
  have hrisk : orbitRisk c q (scheduleCounts z) = labeledRisk c pbar z :=
    (labeledRisk_eq_orbitRisk_of_realizes c pbar q
      ((invariantToOrbitProcedure_realizes c pinv).1)
      ((invariantToOrbitProcedure_realizes c pinv).2) z).symm
  rw [hrisk]
  exact labeledRisk_permutationAverage_le c p z

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

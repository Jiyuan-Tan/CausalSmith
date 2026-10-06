module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.TLabelRateLowerBound

/-! Projective support and sharp targets for the duplicate-baseline experiment. -/

public section

open MeasureTheory ProbabilityTheory

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- A compatible projective direction supported on one coordinate has that
coordinate as its sharp target. -/
-- @node: targetSet_eq_singleton_of_singleton_support
lemma targetSet_eq_singleton_of_singleton_support {p q : ℕ}
    (v : Fin q → Fin p → ℝ) (g : Fin q) (i : Fin p)
    (hcompat : (assignmentFiber v).Nonempty)
    (hsupport : support v g = {i}) : targetSet v g = {i} := by
  rcases hcompat with ⟨f, hf⟩
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨f', hf', rfl⟩
    have hmem : f' g ∈ support v g := hf'.1 g
    simpa [hsupport] using hmem
  · intro x hx
    have hmem : f g ∈ support v g := hf.1 g
    have hfi : f g = i := by simpa [hsupport] using hmem
    subst x
    exact ⟨f, hf, hfi⟩

/-- A singleton direction fixes one target and forces a two-coordinate
direction to use its other coordinate. -/
-- @node: targetSet_eq_other_of_two_supports
lemma targetSet_eq_other_of_two_supports {p q : ℕ}
    (v : Fin q → Fin p → ℝ) (g₀ g₁ : Fin q) (i j : Fin p)
    (hcompat : (assignmentFiber v).Nonempty)
    (hg : g₀ ≠ g₁)
    (hzero : support v g₀ = {i})
    (hone : support v g₁ = {i, j}) : targetSet v g₁ = {j} := by
  rcases hcompat with ⟨f, hf⟩
  have forced (f' : Fin q ↪ Fin p) (hf' : f' ∈ assignmentFiber v) : f' g₁ = j := by
    have hfi : f' g₀ = i := by
      have hm := hf'.1 g₀
      simpa [hzero] using hm
    have hmem : f' g₁ = i ∨ f' g₁ = j := by
      simpa [hone] using (hf'.1 g₁)
    rcases hmem with hi | hj
    · exact False.elim (hg (f'.injective (hfi.trans hi.symm)))
    · exact hj
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨f', hf', rfl⟩
    simp [forced f' hf']
  · intro x hx
    subst x
    exact ⟨f, hf, forced f hf⟩

/-- Projective reduction preserves the coordinate support of every observed
shift, since its within-class scale is nonzero. -/
-- @node: projectiveReduction_support_eq_shift_support
lemma projectiveReduction_support_eq_shift_support {p M : ℕ}
    (d : Fin M → Fin p → ℝ) (r : ProjectiveReduction d) (m : Fin M) :
    support r.v (r.κ m) = Finset.univ.filter (fun i => d m i ≠ 0) := by
  ext i
  have hc := r.c_ne m
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [r.decomp m]
  simp [Pi.smul_apply, smul_eq_mul, hc]

/-- The two support patterns in the duplicate-baseline construction force the
alternative target even when projective class labels are arbitrary. -/
-- @node: projectiveReduction_two_support_targets
lemma projectiveReduction_two_support_targets {p M : ℕ}
    (d : Fin M → Fin p → ℝ) (r : ProjectiveReduction d)
    (m₀ m₁ : Fin M) (i j : Fin p)
    (hcompat : (assignmentFiber r.v).Nonempty) (hij : i ≠ j)
    (hzero : Finset.univ.filter (fun k => d m₀ k ≠ 0) = {i})
    (hone : Finset.univ.filter (fun k => d m₁ k ≠ 0) = {i, j}) :
    targetSet r.v (r.κ m₀) = {i} ∧
      targetSet r.v (r.κ m₁) = {j} := by
  have hs₀ : support r.v (r.κ m₀) = {i} := by
    rw [projectiveReduction_support_eq_shift_support]
    exact hzero
  have hs₁ : support r.v (r.κ m₁) = {i, j} := by
    rw [projectiveReduction_support_eq_shift_support]
    exact hone
  have hg : r.κ m₀ ≠ r.κ m₁ := by
    intro heq
    have hmem : j ∈ ({i} : Finset (Fin p)) := by
      rw [← hs₀, heq, hs₁]
      simp
    have hji : j = i := by simpa using hmem
    exact hij hji.symm
  exact ⟨targetSet_eq_singleton_of_singleton_support r.v (r.κ m₀) i hcompat hs₀,
    targetSet_eq_other_of_two_supports r.v (r.κ m₀) (r.κ m₁) i j
      hcompat hg hs₀ hs₁⟩

/-- The explicit baseline and alternative shifts in the lower-bound experiment
have the asserted sharp target sets. -/
-- @node: projectiveReduction_explicit_shift_targets
lemma projectiveReduction_explicit_shift_targets {p M : ℕ} [NeZero p]
    (d : Fin M → Fin p → ℝ) (r : ProjectiveReduction d)
    (m₀ m₁ : Fin M) (j : Fin p) (h : ℝ)
    (hcompat : (assignmentFiber r.v).Nonempty)
    (hj : j ≠ 0) (hh : h ≠ 0)
    (hzero : d m₀ = Pi.single 0 1)
    (hone : d m₁ = fun i => (Pi.single 0 (1 : ℝ) : Fin p → ℝ) i +
      h * (Pi.single j (1 : ℝ) : Fin p → ℝ) i) :
    targetSet r.v (r.κ m₀) = {0} ∧
      targetSet r.v (r.κ m₁) = {j} := by
  apply projectiveReduction_two_support_targets d r m₀ m₁ 0 j hcompat hj.symm
  · ext i
    rw [hzero]
    by_cases hi : i = 0
    · subst i
      simp
    · simp [Pi.single_apply, hi]
  · ext i
    rw [hone]
    by_cases hi0 : i = 0
    · subst i
      simp [Pi.single_apply, Ne.symm hj]
    · by_cases hij : i = j
      · subst i
        simp [Pi.single_apply, hj, hh]
      · simp [Pi.single_apply, hi0, hij]

/-- Representatives of distinct projective classes cannot be scalar multiples. -/
-- @node: projectiveReduction_representatives_distinct
lemma projectiveReduction_representatives_distinct {p M : ℕ}
    (d : Fin M → Fin p → ℝ) (r : ProjectiveReduction d)
    {g h : Fin r.q} (hgh : g ≠ h) : ¬ ProjSim r.v g h := by
  rintro ⟨c, hc, hsim⟩
  obtain ⟨m, hm⟩ := r.κ_surj g
  obtain ⟨m', hm'⟩ := r.κ_surj h
  have hproj : ProjSim d m m' := by
    refine ⟨r.c m * c / r.c m',
      div_ne_zero (mul_ne_zero (r.c_ne m) hc) (r.c_ne m'), ?_⟩
    calc
      d m = r.c m • r.v g := by rw [r.decomp m, hm]
      _ = (r.c m * c) • r.v h := by rw [hsim, smul_smul]
      _ = (r.c m * c / r.c m') • d m' := by
        rw [r.decomp m', hm', smul_smul, div_mul_cancel₀]
        exact r.c_ne m'
  exact hgh (hm ▸ hm' ▸ (r.classes m m').mpr hproj)

/-- Every projective reduction of shifts from a model has a feasible assignment. -/
-- @node: model_projectiveReduction_assignment_nonempty
lemma model_projectiveReduction_assignment_nonempty {p M : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (𝔐 : AtomicCountModel p M Ω μ)
    (r : ProjectiveReduction (obsShift μ 𝔐)) :
    (assignmentFiber r.v).Nonempty := by
  have hdistinct : ∀ g h, g ≠ h → ¬ ProjSim r.v g h :=
    fun g h hgh => projectiveReduction_representatives_distinct
      (obsShift μ 𝔐) r hgh
  apply generatedDirections_assignment_nonempty μ 𝔐 r.v hdistinct
  exact ⟨r, rfl, Equiv.refl _, fun _ => rfl⟩

/-- The displayed baseline and alternative shifts admit a projective reduction
whose sharp target at environment two is the asserted label. -/
-- @node: noisyIncomplete_projective_targets
lemma noisyIncomplete_projective_targets
    {p : ℕ} [NeZero p] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (𝔐 : AtomicCountModel p p Ω μ)
    (hp : 4 ≤ p) (j : Fin p) (h : ℝ) (hh : h ≠ 0)
    (hshifts : if j = 0 then
      ∀ m, obsShift μ 𝔐 m = Pi.single 0 1
     else
      obsShift μ 𝔐 1 = (fun i =>
        (Pi.single 0 (1 : ℝ) : Fin p → ℝ) i + h * (Pi.single j (1 : ℝ) : Fin p → ℝ) i) ∧
      ∀ m, m ≠ 1 → obsShift μ 𝔐 m = Pi.single 0 1) :
    ∃ r : ProjectiveReduction (obsShift μ 𝔐),
      targetSet r.v (r.κ 1) = {if j = 0 then 0 else j} := by
  have h01 : (0 : Fin p) ≠ 1 := by
    intro heq
    have hv := congrArg Fin.val heq
    simp [Fin.val_one, Nat.mod_eq_of_lt (show 1 < p by omega)] at hv
  have hnonzero : ∀ m, obsShift μ 𝔐 m ≠ 0 := by
    intro m hm
    have hcoord : obsShift μ 𝔐 m 0 = 1 := by
      by_cases hj : j = 0
      · simp only [if_pos hj] at hshifts
        rw [hshifts m]
        simp
      · simp only [if_neg hj] at hshifts
        by_cases hm1 : m = 1
        · rw [hm1, hshifts.1]
          simp [Pi.single_apply, Ne.symm hj]
        · rw [hshifts.2 m hm1]
          simp
    rw [hm] at hcoord
    norm_num at hcoord
  let r := projectiveReduction (obsShift μ 𝔐) hnonzero
  have hcompat := model_projectiveReduction_assignment_nonempty μ 𝔐 r
  refine ⟨r, ?_⟩
  by_cases hj : j = 0
  · simp only [if_pos hj] at hshifts ⊢
    apply targetSet_eq_singleton_of_singleton_support r.v (r.κ 1) 0 hcompat
    rw [projectiveReduction_support_eq_shift_support, hshifts 1]
    ext i
    by_cases hi : i = 0
    · subst i; simp
    · simp [Pi.single_apply, hi]
  · simp only [if_neg hj] at hshifts ⊢
    exact (projectiveReduction_explicit_shift_targets (obsShift μ 𝔐) r 0 1 j h
      hcompat hj hh (hshifts.2 0 h01) hshifts.1).2

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

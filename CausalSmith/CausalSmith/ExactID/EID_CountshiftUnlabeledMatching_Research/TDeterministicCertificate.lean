module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.TCompatibilityCompletion
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.CompatibleModelRealization

/-! Sharp deterministic correct-or-abstain threshold for all labels. -/

public section

open MeasureTheory Matrix

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- An error-bounded thresholded edge must be present in the population support. -/
-- @node: noisyGraph_edge_of_approx
lemma noisyGraph_edge_of_approx {p : ℕ} (d dhat : Fin p → Fin p → ℝ)
    (ε : {x : ℝ // 0 < x})
    (happrox : ∀ m i, |dhat m i - d m i| ≤ (ε : ℝ))
    {m i : Fin p}
    (hedge : noisyGraph dhat ⟨ε.val, le_of_lt ε.property⟩ m i) :
    d m i ≠ 0 := by
  intro hzero
  have hbound := happrox m i
  simp only [hzero, sub_zero] at hbound
  exact not_lt_of_ge hbound hedge

/-- Any accepted matching is the unique matching of the true support graph. -/
-- @node: oneSidedCertificate_of_unique_population_matching
lemma oneSidedCertificate_of_unique_population_matching {p : ℕ}
    (d dhat : Fin p → Fin p → ℝ) (ε : {x : ℝ // 0 < x})
    (t : Equiv.Perm (Fin p))
    (hunique : ∀ σ : Equiv.Perm (Fin p),
      (∀ m, d m (σ m) ≠ 0) → σ = t)
    (happrox : ∀ m i, |dhat m i - d m i| ≤ (ε : ℝ)) :
    oneSidedCertificate dhat ε = some t ∨
      oneSidedCertificate dhat ε = none := by
  classical
  unfold oneSidedCertificate
  split_ifs with h
  · left
    congr 1
    apply hunique
    intro m
    exact noisyGraph_edge_of_approx d dhat ε happrox (Classical.choose_spec h.exists m)
  · exact Or.inr rfl

/-- A unique population matching is returned when all of its thresholded edges survive. -/
-- @node: oneSidedCertificate_eq_of_target_edges
lemma oneSidedCertificate_eq_of_target_edges {p : ℕ}
    (d dhat : Fin p → Fin p → ℝ) (ε : {x : ℝ // 0 < x})
    (t : Equiv.Perm (Fin p))
    (hunique : ∀ σ : Equiv.Perm (Fin p),
      (∀ m, d m (σ m) ≠ 0) → σ = t)
    (happrox : ∀ m i, |dhat m i - d m i| ≤ (ε : ℝ))
    (htarget : ∀ m, (ε : ℝ) < |dhat m (t m)|) :
    oneSidedCertificate dhat ε = some t := by
  classical
  have huniqueNoisy : ∃! σ : Equiv.Perm (Fin p),
      ∀ m, noisyGraph dhat ⟨ε.val, le_of_lt ε.property⟩ m (σ m) := by
    refine ⟨t, htarget, ?_⟩
    intro σ hσ
    apply hunique σ
    intro m
    exact noisyGraph_edge_of_approx d dhat ε happrox (hσ m)
  unfold oneSidedCertificate
  split_ifs with h
  · congr 1
    exact hunique (Classical.choose h.exists)
      (fun m => noisyGraph_edge_of_approx d dhat ε happrox
        (Classical.choose_spec h.exists m))
  · exact False.elim (h huniqueNoisy)

/-- Direct entries above twice the error radius survive thresholding. -/
-- @node: noisyGraph_target_edge_of_margin
lemma noisyGraph_target_edge_of_margin {p : ℕ}
    (d dhat : Fin p → Fin p → ℝ) (ε : {x : ℝ // 0 < x})
    (t : Equiv.Perm (Fin p))
    (happrox : ∀ m i, |dhat m i - d m i| ≤ (ε : ℝ))
    (hmargin : ∀ m, 2 * (ε : ℝ) < |d m (t m)|) :
    ∀ m, noisyGraph dhat ⟨ε.val, le_of_lt ε.property⟩ m (t m) := by
  intro m
  change (ε : ℝ) < |dhat m (t m)|
  have htri := abs_sub_abs_le_abs_sub (d m (t m)) (dhat m (t m))
  have herr := happrox m (t m)
  rw [abs_sub_comm] at herr
  linarith [hmargin m]

/-- The observable shift at its intervention target equals the direct strength. -/
-- @node: obsShift_target_eq_strength
lemma obsShift_target_eq_strength {p : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (𝔐 : AtomicCountModel p p Ω μ) (m : Fin p) :
    obsShift μ 𝔐 m (𝔐.t m) = 𝔐.α m := by
  have hshift : obsShift μ 𝔐 m =
      totalEffect 𝔐.A *ᵥ
        (fun i => 𝔐.η m.succ i - 𝔐.η 0 i) := by
    funext j
    rw [obsShift, obsMean_eq_structural_mean μ 𝔐 m.succ,
      obsMean_eq_structural_mean μ 𝔐 0]
    exact (congrFun (Matrix.mulVec_sub (totalEffect 𝔐.A)
      (𝔐.η m.succ) (𝔐.η 0)) j).symm
  have hdiag := acyclic_mechanism_totalEffect_diagonal 𝔐.A 𝔐.acyclic
  rw [congrFun hshift (𝔐.t m), 𝔐.atomic m]
  simp [Matrix.mulVec_smul, Matrix.mulVec_single, hdiag]

/-- Every direct strength dominates the finite minimum direct strength. -/
-- @node: minStrength_le_abs_strength
lemma minStrength_le_abs_strength {p : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (𝔐 : AtomicCountModel p p Ω μ) (m : Fin p) :
    minStrength μ 𝔐 ≤ |𝔐.α m| := by
  unfold minStrength
  apply csInf_le
  · exact ⟨0, by rintro x ⟨m', rfl⟩; exact abs_nonneg _⟩
  · exact ⟨m, rfl⟩

/-- A margin above twice the error radius retains every true target edge. -/
-- @node: noisyGraph_model_target_edges_of_margin
lemma noisyGraph_model_target_edges_of_margin {p : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (𝔐 : AtomicCountModel p p Ω μ)
    (dhat : Fin p → Fin p → ℝ) (ε : {x : ℝ // 0 < x})
    (happrox : ∀ m i, |dhat m i - obsShift μ 𝔐 m i| ≤ (ε : ℝ))
    (hmargin : 2 * (ε : ℝ) < minStrength μ 𝔐) :
    ∀ m, noisyGraph dhat ⟨ε.val, le_of_lt ε.property⟩ m (𝔐.t m) := by
  intro m
  have htarget : 2 * (ε : ℝ) < |obsShift μ 𝔐 m (𝔐.t m)| := by
    rw [obsShift_target_eq_strength]
    exact hmargin.trans_le (minStrength_le_abs_strength μ 𝔐 m)
  change (ε : ℝ) < |dhat m (𝔐.t m)|
  have htri := abs_sub_abs_le_abs_sub
    (obsShift μ 𝔐 m (𝔐.t m)) (dhat m (𝔐.t m))
  have herr := happrox m (𝔐.t m)
  rw [abs_sub_comm] at herr
  linarith

/-- A full-cover model has a unique support-respecting target permutation. -/
-- @node: model_shift_unique_matching
lemma model_shift_unique_matching {p : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (𝔐 : AtomicCountModel p p Ω μ) (ht : Function.Bijective 𝔐.t) :
    ∀ σ : Equiv.Perm (Fin p),
      (∀ m, obsShift μ 𝔐 m (σ m) ≠ 0) →
        σ = Equiv.ofBijective 𝔐.t ht := by
  classical
  let tPerm := Equiv.ofBijective 𝔐.t ht
  let f : Fin p ↪ Fin p := tPerm.toEmbedding
  have hshift (m : Fin p) : obsShift μ 𝔐 m =
      totalEffect 𝔐.A *ᵥ
        (fun i => 𝔐.η m.succ i - 𝔐.η 0 i) := by
    funext j
    rw [obsShift, obsMean_eq_structural_mean μ 𝔐 m.succ,
      obsMean_eq_structural_mean μ 𝔐 0]
    exact (congrFun (Matrix.mulVec_sub (totalEffect 𝔐.A)
      (𝔐.η m.succ) (𝔐.η 0)) j).symm
  have hcol (m i : Fin p) :
      obsShift μ 𝔐 m i = 𝔐.α m * totalEffect 𝔐.A i (𝔐.t m) := by
    rw [hshift m, 𝔐.atomic m]
    simp [Matrix.mulVec_smul, Matrix.mulVec_single]
  have hf : f ∈ assignmentFiber (obsShift μ 𝔐) := by
    constructor
    · intro m
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
      change obsShift μ 𝔐 m (𝔐.t m) ≠ 0
      rw [obsShift_target_eq_strength]
      exact 𝔐.nonvanishing m
    · intro i hcycle
      have hgraph (j k : Fin p) :
          Hf (obsShift μ 𝔐) f j k →
            j ≠ k ∧ totalEffect 𝔐.A k j ≠ 0 := by
        rintro ⟨m, rfl, hmem, hne⟩
        refine ⟨hne.symm, ?_⟩
        have hnonzero : obsShift μ 𝔐 m k ≠ 0 := by
          simpa [support] using hmem
        rw [hcol] at hnonzero
        exact (mul_ne_zero_iff.mp hnonzero).2
      exact (acyclic_mechanism_totalEffect_acyclic 𝔐.A 𝔐.acyclic i)
        (hcycle.lift id (fun j k h => hgraph j k h))
  intro σ hσ
  have heq : σ.toEmbedding = f := by
    apply assignment_unique_on_range (obsShift μ 𝔐) f hf σ.toEmbedding
    intro m
    constructor
    · simpa [support] using hσ m
    · exact ⟨tPerm.symm (σ m), by simp [f, tPerm]⟩
  apply Equiv.ext
  intro m
  exact congrArg (fun e : Fin p ↪ Fin p => e m) heq

/-- Coordinate shifts along a permutation form a compatible full-cover family. -/
-- @node: diagonal_shift_assignment
lemma diagonal_shift_assignment {p : ℕ} (σ : Equiv.Perm (Fin p))
    (a : ℝ) (ha : a ≠ 0) :
    σ.toEmbedding ∈ assignmentFiber
      (fun m i => if i = σ m then a else 0) := by
  classical
  constructor
  · intro m
    simp [support, ha]
  · have hempty : ∀ j k, ¬ Hf (fun m i => if i = σ m then a else 0)
        σ.toEmbedding j k := by
      intro j k ⟨m, hm, hk, hne⟩
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have hkm : k = σ m := by
        by_contra h
        simp [h] at hk
      exact hne (hkm.trans hm)
    have hno : ∀ j k, ¬ Relation.TransGen
        (Hf (fun m i => if i = σ m then a else 0) σ.toEmbedding) j k := by
      intro j k h
      induction h with
      | single hs => exact hempty _ _ hs
      | tail _ _ ih => exact ih
    intro i hcycle
    exact hno i i hcycle

-- @node: minStrength_eq_of_constant
lemma minStrength_eq_of_constant {p : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (𝔐 : AtomicCountModel p p Ω μ) (a : ℝ) (ha : 0 < a)
    (hα : ∀ m, 𝔐.α m = a) : minStrength μ 𝔐 = a := by
  classical
  have hset : {x : ℝ | ∃ m : Fin p, x = |𝔐.α m|} = {a} := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      simp [hα m, abs_of_pos ha]
    · intro hx
      have hp : 0 < p := 𝔐.p_pos
      have m : Fin p := ⟨0, hp⟩
      have hxa : x = a := by simpa using hx
      exact ⟨m, by simpa [hα m, abs_of_pos ha] using hxa⟩
  simp [minStrength, hset]

-- @node: thm:deterministic-certificate
theorem deterministic_certificate {p : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (𝔐 : AtomicCountModel p p Ω μ)
    (ht : Function.Bijective 𝔐.t)
    (dhat : Fin p → Fin p → ℝ) (ε : {x : ℝ // 0 < x})
    (happrox : ∀ m i, |dhat m i - obsShift μ 𝔐 m i| ≤ (ε : ℝ)) :
    (oneSidedCertificate dhat ε = some (Equiv.ofBijective 𝔐.t ht) ∨
      oneSidedCertificate dhat ε = none) ∧
    (2 * (ε : ℝ) < minStrength μ 𝔐 →
      oneSidedCertificate dhat ε = some (Equiv.ofBijective 𝔐.t ht)) ∧
    (∀ (p' : ℕ) (a ε' : ℝ), 2 ≤ p' → 0 < a → a / 2 ≤ ε' →
      ∃ (Ω₁ Ω₂ : Type) (ms₁ : MeasurableSpace Ω₁)
        (ms₂ : MeasurableSpace Ω₂) (μ₁ : Measure Ω₁)
        (μ₂ : Measure Ω₂),
        letI : MeasurableSpace Ω₁ := ms₁
        letI : MeasurableSpace Ω₂ := ms₂
        ∃ (𝔐₁ : AtomicCountModel p' p' Ω₁ μ₁)
          (𝔐₂ : AtomicCountModel p' p' Ω₂ μ₂),
          Function.Bijective 𝔐₁.t ∧ Function.Bijective 𝔐₂.t ∧
          𝔐₁.t ≠ 𝔐₂.t ∧
          minStrength μ₁ 𝔐₁ = a ∧ minStrength μ₂ 𝔐₂ = a ∧
          ∃ Dbar : Fin p' → Fin p' → ℝ,
            (∀ m i, |Dbar m i - obsShift μ₁ 𝔐₁ m i| ≤ ε') ∧
            (∀ m i, |Dbar m i - obsShift μ₂ 𝔐₂ m i| ≤ ε') ∧
            ∀ rule : (Fin p' → Fin p' → ℝ) → Equiv.Perm (Fin p'),
              (rule Dbar : Fin p' → Fin p') ≠ 𝔐₁.t ∨
              (rule Dbar : Fin p' → Fin p') ≠ 𝔐₂.t) := by
  constructor
  · exact oneSidedCertificate_of_unique_population_matching
      (obsShift μ 𝔐) dhat ε (Equiv.ofBijective 𝔐.t ht)
      (model_shift_unique_matching μ 𝔐 ht) happrox
  constructor
  · intro hmargin
    exact oneSidedCertificate_eq_of_target_edges
      (obsShift μ 𝔐) dhat ε (Equiv.ofBijective 𝔐.t ht)
      (model_shift_unique_matching μ 𝔐 ht) happrox
      (by intro m
          change (ε : ℝ) < |dhat m (𝔐.t m)|
          exact noisyGraph_model_target_edges_of_margin μ 𝔐 dhat ε happrox hmargin m)
  · intro p' a ε' hp' ha hε'
    classical
    have hp0 : 0 < p' := by omega
    let z : Fin p' := ⟨0, hp0⟩
    let j : Fin p' := ⟨1, by omega⟩
    let σ₁ : Equiv.Perm (Fin p') := Equiv.refl _
    let σ₂ : Equiv.Perm (Fin p') := Equiv.swap z j
    let v₁ : Fin p' → Fin p' → ℝ := fun m i => if i = σ₁ m then a else 0
    let v₂ : Fin p' → Fin p' → ℝ := fun m i => if i = σ₂ m then a else 0
    have hneq : σ₁ ≠ σ₂ := by
      intro heq
      have hj : z ≠ j := by simp [z, j]
      have hval := congrArg (fun σ : Equiv.Perm (Fin p') => σ z) heq
      simp [σ₁, σ₂, Equiv.swap_apply_left] at hval
      exact hj hval
    have hf₁ : σ₁.toEmbedding ∈ assignmentFiber v₁ :=
      diagonal_shift_assignment σ₁ a (ne_of_gt ha)
    have hf₂ : σ₂.toEmbedding ∈ assignmentFiber v₂ :=
      diagonal_shift_assignment σ₂ a (ne_of_gt ha)
    obtain ⟨Ω₁, ms₁, μ₁, 𝔐₁, ht₁, hα₁, hd₁⟩ :=
      compatible_model_exact_shifts hp0 hp0 v₁ σ₁.toEmbedding hf₁
    obtain ⟨Ω₂, ms₂, μ₂, 𝔐₂, ht₂, hα₂, hd₂⟩ :=
      compatible_model_exact_shifts hp0 hp0 v₂ σ₂.toEmbedding hf₂
    letI : MeasurableSpace Ω₁ := ms₁
    letI : MeasurableSpace Ω₂ := ms₂
    have hb₁ : Function.Bijective 𝔐₁.t := by
      rw [ht₁]
      exact σ₁.bijective
    have hb₂ : Function.Bijective 𝔐₂.t := by
      rw [ht₂]
      exact σ₂.bijective
    have hα₁' : ∀ m, 𝔐₁.α m = a := by
      intro m
      rw [hα₁]
      simp [v₁]
    have hα₂' : ∀ m, 𝔐₂.α m = a := by
      intro m
      rw [hα₂]
      simp [v₂]
    have htneq : 𝔐₁.t ≠ 𝔐₂.t := by
      intro heq
      apply hneq
      apply Equiv.ext
      intro m
      have hm := congrFun heq m
      simpa [ht₁, ht₂] using hm
    let Dbar : Fin p' → Fin p' → ℝ := fun m i => (v₁ m i + v₂ m i) / 2
    have hvals (σ : Equiv.Perm (Fin p')) (m i : Fin p') :
        0 ≤ (if i = σ m then a else 0) ∧
        (if i = σ m then a else 0) ≤ a := by
      split_ifs <;> constructor <;> linarith
    refine ⟨Ω₁, Ω₂, ms₁, ms₂, μ₁, μ₂, 𝔐₁, 𝔐₂,
      hb₁, hb₂, htneq,
      minStrength_eq_of_constant μ₁ 𝔐₁ a ha hα₁',
      minStrength_eq_of_constant μ₂ 𝔐₂ a ha hα₂', Dbar, ?_, ?_, ?_⟩
    · intro m i
      rw [hd₁ m]
      have h₁ := hvals σ₁ m i
      have h₂ := hvals σ₂ m i
      change |(v₁ m i + v₂ m i) / 2 - v₁ m i| ≤ ε'
      rw [abs_le]
      dsimp [v₁, v₂] at h₁ h₂ ⊢
      constructor <;> linarith
    · intro m i
      rw [hd₂ m]
      have h₁ := hvals σ₁ m i
      have h₂ := hvals σ₂ m i
      change |(v₁ m i + v₂ m i) / 2 - v₂ m i| ≤ ε'
      rw [abs_le]
      dsimp [v₁, v₂] at h₁ h₂ ⊢
      constructor <;> linarith
    · intro rule
      by_cases h : (rule Dbar : Fin p' → Fin p') = 𝔐₁.t
      · right
        intro h₂
        exact htneq (h.symm.trans h₂)
      · exact Or.inl h

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

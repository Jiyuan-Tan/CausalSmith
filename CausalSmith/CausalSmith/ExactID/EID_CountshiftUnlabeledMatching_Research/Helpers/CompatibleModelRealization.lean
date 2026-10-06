module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.StructuralMean
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.Matching
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.Triangular

/-! Realization and necessity for compatible direction families. -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

-- @node: generatedDirections_assignment_nonempty
lemma generatedDirections_assignment_nonempty {p q M : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (𝔐 : AtomicCountModel p M Ω μ)
    (v : Fin q → Fin p → ℝ) (_hdistinct : ∀ g h, g ≠ h → ¬ ProjSim v g h)
    (hgen : GeneratesDirections μ 𝔐 v) : (assignmentFiber v).Nonempty := by
  obtain ⟨r, hrq, e, he⟩ := hgen
  have hshift (m : Fin M) : obsShift μ 𝔐 m =
      𝔐.α m • (totalEffect 𝔐.A).col (𝔐.t m) := by
    rw [show obsShift μ 𝔐 m = totalEffect 𝔐.A *ᵥ
        (fun i => 𝔐.η m.succ i - 𝔐.η 0 i) by
      funext j
      rw [obsShift, obsMean_eq_structural_mean μ 𝔐 m.succ,
        obsMean_eq_structural_mean μ 𝔐 0]
      exact (congrFun (Matrix.mulVec_sub (totalEffect 𝔐.A)
        (𝔐.η m.succ) (𝔐.η 0)) j).symm,
      𝔐.atomic m, Matrix.mulVec_smul, Matrix.mulVec_single]
    simp [MulOpposite.op_one]
  have hrep (g : Fin q) : ∃ m : Fin M, r.κ m = e.symm g := by
    exact r.κ_surj (e.symm g)
  let m : Fin q → Fin M := fun g => Classical.choose (hrep g)
  have hm (g : Fin q) : r.κ (m g) = e.symm g := Classical.choose_spec (hrep g)
  let f0 : Fin q → Fin p := fun g => 𝔐.t (m g)
  have hf0 : Function.Injective f0 := by
    intro g h hgh
    change 𝔐.t (m g) = 𝔐.t (m h) at hgh
    by_contra hne
    have hprojShift : ProjSim (obsShift μ 𝔐) (m g) (m h) := by
      refine ⟨𝔐.α (m g) / 𝔐.α (m h), div_ne_zero (𝔐.nonvanishing _) (𝔐.nonvanishing _), ?_⟩
      rw [hshift, hshift, hgh]
      rw [smul_smul, div_mul_cancel₀ _ (𝔐.nonvanishing _)]
    have hk := (r.classes (m g) (m h)).mpr hprojShift
    rw [hm, hm] at hk
    exact hne (e.symm.injective hk)
  let f : Fin q ↪ Fin p := ⟨f0, hf0⟩
  refine ⟨f, ?_, ?_⟩
  · intro g
    have hdecomp := r.decomp (m g)
    rw [hm g, he (e.symm g), e.apply_symm_apply] at hdecomp
    have hv : v g (f g) ≠ 0 := by
      intro hz
      have hzshift := congrFun hdecomp (f g)
      rw [hshift] at hzshift
      change 𝔐.α (m g) * totalEffect 𝔐.A (𝔐.t (m g)) (𝔐.t (m g)) =
        r.c (m g) * v g (f g) at hzshift
      rw [acyclic_mechanism_totalEffect_diagonal 𝔐.A 𝔐.acyclic, hz,
        mul_one, mul_zero] at hzshift
      exact 𝔐.nonvanishing _ hzshift
    simpa [support] using hv
  · intro i hcycle
    apply (acyclic_mechanism_totalEffect_acyclic 𝔐.A 𝔐.acyclic i)
    apply hcycle.lift id
    intro a b hab
    obtain ⟨g, hfa, hb, hba⟩ := hab
    have hdecomp := r.decomp (m g)
    rw [hm g, he (e.symm g), e.apply_symm_apply] at hdecomp
    have hvb : v g b ≠ 0 := by simpa [support] using hb
    have hentry : totalEffect 𝔐.A b (f g) ≠ 0 := by
      intro hz
      have hz' : totalEffect 𝔐.A b (𝔐.t (m g)) = 0 := by
        simpa [f, f0] using hz
      have hzshift := congrFun hdecomp b
      rw [hshift] at hzshift
      change 𝔐.α (m g) * totalEffect 𝔐.A b (𝔐.t (m g)) =
        r.c (m g) * v g b at hzshift
      rw [hz', mul_zero] at hzshift
      exact hvb (mul_eq_zero.mp hzshift.symm |>.resolve_left (r.c_ne _))
    subst a
    exact ⟨hba.symm, hentry⟩

-- @node: poissonCountLaw_parameter_measurable
lemma poissonCountLaw_parameter_measurable {p : ℕ} :
    Measurable (fun sz : (Fin p → ℝ) × (Fin p → ℝ) =>
      poissonCountLaw sz.1 sz.2) := by
  refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
  have heval : (fun sz : (Fin p → ℝ) × (Fin p → ℝ) =>
      poissonCountLaw sz.1 sz.2 A) = fun sz => ∑' x : Fin p → ℕ,
        A.indicator (fun x => ∏ j, ENNReal.ofReal
          (Real.exp (-(Real.toNNReal (sz.1 j * Real.exp (sz.2 j)) : ℝ)) *
            (Real.toNNReal (sz.1 j * Real.exp (sz.2 j)) : ℝ) ^ x j /
              (x j).factorial)) x := by
    funext sz
    rw [← Measure.tsum_indicator_apply_singleton _ A hA, poissonCountLaw]
    apply tsum_congr
    intro x
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
      rw [Measure.pi_singleton]
      congr 1
      funext j
      exact poissonMeasure_singleton _ _
    · simp [Set.indicator, hx]
  rw [heval]
  exact Measurable.tsum fun x => by
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
      fun_prop
    · simp [Set.indicator, hx]

-- @node: poissonCountLaw_attach_measurable_general
lemma poissonCountLaw_attach_measurable_general {p : ℕ} :
    Measurable (fun sz : (Fin p → ℝ) × (Fin p → ℝ) =>
      (poissonCountLaw sz.1 sz.2).map (fun x => (sz, x))) := by
  refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
  have heval : (fun sz : (Fin p → ℝ) × (Fin p → ℝ) =>
      ((poissonCountLaw sz.1 sz.2).map (fun x => (sz, x))) A) =
      fun sz => ∑' x : Fin p → ℕ,
        A.indicator (fun y => ∏ j, ENNReal.ofReal
          (Real.exp (-(Real.toNNReal (sz.1 j * Real.exp (sz.2 j)) : ℝ)) *
            (Real.toNNReal (sz.1 j * Real.exp (sz.2 j)) : ℝ) ^ x j /
              (x j).factorial)) (sz, x) := by
    funext sz
    rw [Measure.map_apply (by fun_prop) hA,
      ← Measure.tsum_indicator_apply_singleton _ _ (hA.preimage (by fun_prop)),
      poissonCountLaw]
    apply tsum_congr
    intro x
    by_cases hx : (sz, x) ∈ A
    · have hx' : x ∈ (fun y => (sz, y)) ⁻¹' A := hx
      rw [Set.indicator_of_mem hx']
      rw [Measure.pi_singleton]
      rw [Set.indicator_of_mem hx]
      congr 1
      funext j
      exact poissonMeasure_singleton _ _
    · simp [Set.indicator, hx]
  rw [heval]
  exact Measurable.tsum fun x => by
    have hp : Measurable (fun sz : (Fin p → ℝ) × (Fin p → ℝ) =>
        ∏ j, ENNReal.ofReal
          (Real.exp (-(Real.toNNReal (sz.1 j * Real.exp (sz.2 j)) : ℝ)) *
            (Real.toNNReal (sz.1 j * Real.exp (sz.2 j)) : ℝ) ^ x j /
              (x j).factorial)) := by fun_prop
    exact hp.indicator (hA.preimage (by fun_prop))

-- @node: acyclic_completion_to_mechanism
lemma acyclic_completion_to_mechanism {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ i, B i i = 1)
    (hacyclic : ∀ i, ¬ Relation.TransGen
      (fun j k => j ≠ k ∧ B k j ≠ 0) i i) :
    AcyclicMechanism (1 - B⁻¹) ∧ totalEffect (1 - B⁻¹) = B := by
  classical
  let edge : Fin p → Fin p → Prop := fun j k => j ≠ k ∧ B k j ≠ 0
  let G := Causalean.Graph.DAG.ofAcyclic edge hacyclic
  let rank : Fin p → ℕᵒᵈ ×ₗ Fin p :=
    fun i => toLex (OrderDual.toDual (G.topoOrder i), i)
  have hrank : Function.Injective rank := by
    intro i j hij
    exact congrArg (fun x : ℕᵒᵈ ×ₗ Fin p => (ofLex x).2) hij
  let ord : LinearOrder (Fin p) := LinearOrder.lift' rank hrank
  have htriB : @Matrix.IsUpperTriangular (Fin p) ℝ _ ord.toLT B := by
    intro i j hij
    by_contra hne
    have hedge : G.edge j i := by
      rw [Causalean.Graph.DAG.ofAcyclic_edge]
      constructor
      · intro hji
        subst j
        exact (lt_irrefl (rank i)) hij
      · exact hne
    have hlt := G.topoOrder_lt j i hedge
    have hle : G.topoOrder i ≤ G.topoOrder j := by
      have hkey : rank j < rank i := hij
      rcases (Prod.Lex.lt_iff.mp hkey) with h | h
      · exact Nat.le_of_lt h
      · exact le_of_eq h.1.symm
    exact (not_lt_of_ge hle) hlt
  have hunit := acyclic_unit_matrix_invertible B hdiag hacyclic
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B hunit
  have htriInv : @Matrix.IsUpperTriangular (Fin p) ℝ _ ord.toLT B⁻¹ := by
    letI : LinearOrder (Fin p) := ord
    exact Matrix.blockTriangular_inv_of_blockTriangular htriB
  have hdiagInv (i : Fin p) : B⁻¹ i i = 1 := by
    have hmul := congrArg (fun C : Matrix (Fin p) (Fin p) ℝ => C i i)
      (Matrix.mul_nonsing_inv B hunit)
    have hsum : (B * B⁻¹) i i = B i i * B⁻¹ i i := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_single i
      · intro k _ hki
        rcases @lt_trichotomy (Fin p) ord k i with h | h | h
        · simp [htriB h]
        · exact (hki h).elim
        · simp [htriInv h]
      · simp
    simpa [hsum, hdiag] using hmul
  constructor
  · constructor
    · intro i
      simp [Matrix.sub_apply, hdiagInv]
    · intro i hcycle
      have hedge : ∀ j k, (1 - B⁻¹) k j ≠ 0 → ord.lt k j := by
        intro j k hne
        have hjk : j ≠ k := by
          intro h
          subst k
          simp [Matrix.sub_apply, hdiagInv] at hne
        rcases @lt_trichotomy (Fin p) ord j k with h | h | h
        · exact False.elim (hne (by
            simp [Matrix.sub_apply, Ne.symm hjk, htriInv h]))
        · exact False.elim (hjk h)
        · exact h
      have hpath : Relation.TransGen (fun a b => ord.lt b a) i i :=
        hcycle.lift id (by intro j k h; exact hedge j k h)
      letI : LinearOrder (Fin p) := ord
      have hstrict : ∀ {j k}, Relation.TransGen (fun a b => ord.lt b a) j k →
          ord.lt k j := by
        intro j k h
        induction h with
        | single h => exact h
        | tail h₁ h₂ ih => exact @lt_trans (Fin p) ord.toPreorder _ _ _ h₂ ih
      exact (@lt_irrefl (Fin p) ord.toPreorder i) (hstrict hpath)
  · unfold totalEffect
    rw [sub_sub_cancel, Matrix.nonsing_inv_nonsing_inv B hunit]

-- @node: compatible_canonical_completion
lemma compatible_canonical_completion {p q : ℕ} (v : Fin q → Fin p → ℝ)
    (f : Fin q ↪ Fin p) (hf : f ∈ assignmentFiber v) :
    ∃ B : Matrix (Fin p) (Fin p) ℝ,
      (∀ g i, B i (f g) = v g i / v g (f g)) ∧
      (∀ i, B i i = 1) ∧
      ∀ i, ¬ Relation.TransGen (fun j k => j ≠ k ∧ B k j ≠ 0) i i := by
  classical
  let B : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun i j =>
    if h : j ∈ Set.range f then
      v (Classical.choose h) i / v (Classical.choose h) j
    else if i = j then 1 else 0
  have hcol (g : Fin q) (i : Fin p) :
      B i (f g) = v g i / v g (f g) := by
    have h : f g ∈ Set.range f := ⟨g, rfl⟩
    simp only [B, Matrix.of_apply, dif_pos h]
    have heq : Classical.choose h = g := f.injective (Classical.choose_spec h)
    rw [heq]
  have hdiag (i : Fin p) : B i i = 1 := by
    by_cases h : i ∈ Set.range f
    · obtain ⟨g, rfl⟩ := h
      rw [hcol]
      exact div_self (by simpa [support] using hf.1 g)
    · change (if h' : i ∈ Set.range f then _ else if i = i then 1 else 0) = 1
      rw [dif_neg h]
      simp
  have hedge (i j : Fin p) (hij : i ≠ j ∧ B j i ≠ 0) : Hf v f i j := by
    by_cases h : i ∈ Set.range f
    · let g := Classical.choose h
      have hfg : f g = i := Classical.choose_spec h
      have hj : v g j ≠ 0 := by
        intro hz
        apply hij.2
        rw [← hfg, hcol, hz]
        simp
      exact ⟨g, hfg, by simpa [support] using hj, hij.1.symm⟩
    · have hzero : B j i = 0 := by
        change (if h' : i ∈ Set.range f then _ else if j = i then 1 else 0) = 0
        rw [dif_neg h]
        simp [hij.1.symm]
      exact False.elim (hij.2 hzero)
  refine ⟨B, hcol, hdiag, ?_⟩
  intro i hcycle
  exact hf.2 i (hcycle.lift id (by intro a b hab; exact hedge a b hab))

private abbrev CompatibleFiber (p : ℕ) :=
  ((Fin p → ℝ) × (Fin p → ℝ)) × (Fin p → ℕ)

private abbrev CompatibleSpace (p q : ℕ) := Fin (q + 1) → CompatibleFiber p

private def compatibleEta {p q : ℕ} (v : Fin q → Fin p → ℝ)
    (f : Fin q ↪ Fin p) : Fin (q + 1) → Fin p → ℝ :=
  Fin.cases 0 (fun g => v g (f g) • Pi.single (f g) 1)

private def compatibleBase {p q : ℕ} (B : Matrix (Fin p) (Fin p) ℝ)
    (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p) (m : Fin (q + 1)) :
    Measure ((Fin p → ℝ) × (Fin p → ℝ)) :=
  (multivariateGaussian 0 (1 : Matrix (Fin p) (Fin p) ℝ)).map fun u =>
    (fun _ => 1, B *ᵥ (compatibleEta v f m + WithLp.ofLp u))

private def compatibleKernel {p : ℕ}
    (sz : (Fin p → ℝ) × (Fin p → ℝ)) : Measure (CompatibleFiber p) :=
  (poissonCountLaw sz.1 sz.2).map fun x => (sz, x)

private def compatibleEnvLaw {p q : ℕ} (B : Matrix (Fin p) (Fin p) ℝ)
    (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p) (m : Fin (q + 1)) :
    Measure (CompatibleFiber p) :=
  (compatibleBase B v f m).bind compatibleKernel

private def compatibleLaw {p q : ℕ} (B : Matrix (Fin p) (Fin p) ℝ)
    (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p) :
    Measure (CompatibleSpace p q) := Measure.pi fun m => compatibleEnvLaw B v f m

private lemma compatibleCount_probability {p : ℕ} (s z : Fin p → ℝ) :
    IsProbabilityMeasure (poissonCountLaw s z) := by
  let _ (j : Fin p) : IsProbabilityMeasure
      (poissonMeasure (Real.toNNReal (s j * Real.exp (z j)))) := inferInstance
  unfold poissonCountLaw
  infer_instance

private lemma compatibleBase_probability {p q : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (v : Fin q → Fin p → ℝ)
    (f : Fin q ↪ Fin p) (m : Fin (q + 1)) :
    IsProbabilityMeasure (compatibleBase B v f m) := by
  unfold compatibleBase
  exact Measure.isProbabilityMeasure_map (by fun_prop)

private lemma compatibleKernel_probability {p : ℕ} (sz) :
    IsProbabilityMeasure (compatibleKernel (p := p) sz) := by
  unfold compatibleKernel
  let _ := compatibleCount_probability sz.1 sz.2
  exact Measure.isProbabilityMeasure_map (by fun_prop)

private lemma compatibleEnv_probability {p q : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (v : Fin q → Fin p → ℝ)
    (f : Fin q ↪ Fin p) (m : Fin (q + 1)) :
    IsProbabilityMeasure (compatibleEnvLaw B v f m) := by
  let _ := compatibleBase_probability B v f m
  unfold compatibleEnvLaw
  exact MeasureTheory.isProbabilityMeasure_bind
    poissonCountLaw_attach_measurable_general.aemeasurable
    (ae_of_all _ compatibleKernel_probability)

private lemma compatibleLaw_probability {p q : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (v : Fin q → Fin p → ℝ)
    (f : Fin q ↪ Fin p) : IsProbabilityMeasure (compatibleLaw B v f) := by
  let _ (m : Fin (q + 1)) := compatibleEnv_probability B v f m
  unfold compatibleLaw
  infer_instance

private lemma compatibleLaw_map_eval {p q : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (v : Fin q → Fin p → ℝ)
    (f : Fin q ↪ Fin p) (m : Fin (q + 1)) :
    (compatibleLaw B v f).map (fun ω => ω m) = compatibleEnvLaw B v f m := by
  let _ (i : Fin (q + 1)) := compatibleEnv_probability B v f i
  rw [compatibleLaw, Measure.pi_map_eval]
  simp

private lemma compatibleEnv_map_condition {p q : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (v : Fin q → Fin p → ℝ)
    (f : Fin q ↪ Fin p) (m : Fin (q + 1)) :
    (compatibleEnvLaw B v f m).map Prod.fst = compatibleBase B v f m := by
  let _ := compatibleBase_probability B v f m
  have hk : Measurable (compatibleKernel (p := p)) :=
    poissonCountLaw_attach_measurable_general
  ext A hA
  rw [Measure.map_apply measurable_fst hA, compatibleEnvLaw]
  rw [
    Measure.bind_apply (hA.preimage measurable_fst)
      hk.aemeasurable]
  simp only [Set.preimage]
  have hfun : (fun sz : (Fin p → ℝ) × (Fin p → ℝ) =>
      compatibleKernel sz {x | x.1 ∈ A}) = fun sz =>
      (poissonCountLaw sz.1 sz.2) {x | sz ∈ A} := by
    funext sz
    change (Measure.map (fun x : Fin p → ℕ => (sz, x))
      (poissonCountLaw sz.1 sz.2)) (Prod.fst ⁻¹' A) = _
    rw [Measure.map_apply (by fun_prop)
      (hA.preimage measurable_fst)]
    congr 1
  rw [hfun]
  rw [show (fun sz : (Fin p → ℝ) × (Fin p → ℝ) =>
      (poissonCountLaw sz.1 sz.2) {x | sz ∈ A}) = A.indicator 1 by
    funext sz
    by_cases hsz : sz ∈ A
    · simp [hsz, isProbabilityMeasure_iff.mp
        (compatibleCount_probability sz.1 sz.2)]
    · simp [hsz]]
  rw [lintegral_indicator hA]
  exact setLIntegral_one A

private lemma compatibleLaw_map_condition {p q : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (v : Fin q → Fin p → ℝ)
    (f : Fin q ↪ Fin p) (m : Fin (q + 1)) :
    (compatibleLaw B v f).map (fun ω => (ω m).1) = compatibleBase B v f m := by
  rw [← compatibleEnv_map_condition B v f m,
    ← compatibleLaw_map_eval B v f m, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

private lemma compatibleLaw_map_disturbance {p q : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (hunit : IsUnit B.det)
    (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p) (m : Fin (q + 1)) :
    (compatibleLaw B v f).map (fun ω => WithLp.toLp 2
      (B⁻¹ *ᵥ (ω m).1.2 - compatibleEta v f m)) =
      multivariateGaussian 0 (1 : Matrix (Fin p) (Fin p) ℝ) := by
  rw [show (fun ω : CompatibleSpace p q => WithLp.toLp 2
      (B⁻¹ *ᵥ (ω m).1.2 - compatibleEta v f m)) =
      (fun sz => WithLp.toLp 2 (B⁻¹ *ᵥ sz.2 - compatibleEta v f m)) ∘
        (fun ω => (ω m).1) by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), compatibleLaw_map_condition,
    compatibleBase,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp : (fun sz : (Fin p → ℝ) × (Fin p → ℝ) => WithLp.toLp 2
      (B⁻¹ *ᵥ sz.2 - compatibleEta v f m)) ∘
      (fun u : EuclideanSpace ℝ (Fin p) =>
        (fun _ => 1, B *ᵥ (compatibleEta v f m + WithLp.ofLp u))) = id := by
    funext u
    apply WithLp.ofLp_injective
    ext i
    simp only [Function.comp_apply, id_eq, WithLp.ofLp_toLp]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hunit, Matrix.one_mulVec]
    simp
  rw [hcomp, Measure.map_id]

private def compatibleModel {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p) (hf : f ∈ assignmentFiber v)
    (B : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ i, B i i = 1)
    (hacyclic : ∀ i, ¬ Relation.TransGen (fun j k => j ≠ k ∧ B k j ≠ 0) i i) :
    AtomicCountModel p q (CompatibleSpace p q) (compatibleLaw B v f) := by
  have hunit := acyclic_unit_matrix_invertible B hdiag hacyclic
  have hmech := acyclic_completion_to_mechanism B hdiag hacyclic
  let η := compatibleEta v f
  let ξ : Fin (q + 1) → CompatibleSpace p q → Fin p → ℝ :=
    fun m ω => B⁻¹ *ᵥ (ω m).1.2 - η m
  refine {
    p_pos := hp
    M_pos := hq
    A := 1 - B⁻¹
    η := η
    Ωc := fun _ => 1
    α := fun g => v g (f g)
    t := f
    ξ := ξ
    S := fun m ω => (ω m).1.1
    X := fun m ω => (ω m).2
    acyclic := hmech.1
    atomic := ?_
    nonvanishing := ?_
    gaussian := ?_
    poisson := ?_ }
  · intro g
    ext i
    simp [η, compatibleEta]
  · intro g hz
    have := hf.1 g
    simpa [support, hz] using this
  · intro m
    refine ⟨Matrix.PosDef.one, ?_⟩
    have hmap := compatibleLaw_map_disturbance B hunit v f m
    refine ⟨AEMeasurable.of_map_ne_zero ?_, hmap⟩
    rw [hmap]
    exact IsProbabilityMeasure.ne_zero _
  · intro m _
    have hlatent (ω : CompatibleSpace p q) :
        latentState (1 - B⁻¹) η ξ m ω = (ω m).1.2 := by
      change totalEffect (1 - B⁻¹) *ᵥ
        (η m + (B⁻¹ *ᵥ (ω m).1.2 - η m)) = _
      rw [hmech.2]
      have hadd : η m + (B⁻¹ *ᵥ (ω m).1.2 - η m) = B⁻¹ *ᵥ (ω m).1.2 := by
        abel
      rw [hadd]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hunit, Matrix.one_mulVec]
    have hSmap : (compatibleLaw B v f).map (fun ω => (ω m).1.1) =
        Measure.dirac (fun _ : Fin p => (1 : ℝ)) := by
      rw [show (fun ω : CompatibleSpace p q => (ω m).1.1) =
          Prod.fst ∘ (fun ω => (ω m).1) by rfl,
        ← Measure.map_map (by fun_prop) (by fun_prop), compatibleLaw_map_condition,
        compatibleBase, Measure.map_map (by fun_prop) (by fun_prop)]
      rw [show Prod.fst ∘ (fun u : EuclideanSpace ℝ (Fin p) =>
          (fun _ => (1 : ℝ), B *ᵥ (compatibleEta v f m + WithLp.ofLp u))) =
          fun _ => fun _ => (1 : ℝ) by rfl]
      rw [Measure.map_const,
        isProbabilityMeasure_iff.mp
          (inferInstance : IsProbabilityMeasure
            (multivariateGaussian 0 (1 : Matrix (Fin p) (Fin p) ℝ))),
        one_smul]
    have hpositive : ∀ᵐ ω ∂compatibleLaw B v f, ∀ i, 0 < (ω m).1.1 i := by
      have hm : MeasurableSet {s : Fin p → ℝ | ∀ i, 0 < s i} := by measurability
      rw [← ae_map_iff
        ((by fun_prop : Measurable (fun ω : CompatibleSpace p q => (ω m).1.1))).aemeasurable
        hm, hSmap]
      simp
    refine ⟨hpositive, ?_, ?_, ?_⟩
    · simpa only [hlatent] using
        (show Measurable (fun ω : CompatibleSpace p q => (ω m).1) by fun_prop).aemeasurable
    · simpa only [hlatent] using
        (show Measurable (fun ω : CompatibleSpace p q => ω m) by fun_prop).aemeasurable
    · have hfull : (fun ω : CompatibleSpace p q =>
          ((((ω m).1.1, latentState (1 - B⁻¹) η ξ m ω), (ω m).2))) =
          fun ω => ω m := by
          funext ω
          simp only [hlatent]
      rw [hfull, compatibleLaw_map_eval, compatibleEnvLaw,
        show (fun ω : CompatibleSpace p q =>
          ((ω m).1.1, latentState (1 - B⁻¹) η ξ m ω)) =
          fun ω => (ω m).1 by funext ω; simp only [hlatent],
        compatibleLaw_map_condition]
      rfl

-- @node: compatible_model_realization
lemma compatible_model_realization {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (v : Fin q → Fin p → ℝ) (hv : ∀ g, v g ≠ 0)
    (hdistinct : ∀ g h, g ≠ h → ¬ ProjSim v g h)
    (hfiber : (assignmentFiber v).Nonempty) :
    ∃ (Ω : Type) (ms : MeasurableSpace Ω) (μ : Measure Ω),
      letI : MeasurableSpace Ω := ms
      ∃ 𝔐 : AtomicCountModel p q Ω μ, GeneratesDirections μ 𝔐 v := by
  obtain ⟨f, hf⟩ := hfiber
  obtain ⟨B, hcol, hdiag, hacyclic⟩ := compatible_canonical_completion v f hf
  let μ := compatibleLaw B v f
  let 𝔐 := compatibleModel hp hq v f hf B hdiag hacyclic
  let _ : IsProbabilityMeasure μ := compatibleLaw_probability B v f
  have hshift (g : Fin q) : obsShift μ 𝔐 g = v g := by
    have hs : obsShift μ 𝔐 g = totalEffect 𝔐.A *ᵥ
        (fun i => 𝔐.η g.succ i - 𝔐.η 0 i) := by
      funext i
      rw [obsShift, obsMean_eq_structural_mean μ 𝔐 g.succ,
        obsMean_eq_structural_mean μ 𝔐 0]
      exact (congrFun (Matrix.mulVec_sub (totalEffect 𝔐.A)
        (𝔐.η g.succ) (𝔐.η 0)) i).symm
    rw [hs]
    change totalEffect (1 - B⁻¹) *ᵥ
      (fun i => compatibleEta v f g.succ i - compatibleEta v f 0 i) = v g
    rw [(acyclic_completion_to_mechanism B hdiag hacyclic).2]
    have heta : (fun i => compatibleEta v f g.succ i - compatibleEta v f 0 i) =
        v g (f g) • Pi.single (f g) 1 := by
      ext i
      simp [compatibleEta]
    rw [heta, Matrix.mulVec_smul, Matrix.mulVec_single]
    ext i
    simp only [Pi.smul_apply]
    have hn : v g (f g) ≠ 0 := by simpa [support] using hf.1 g
    simp only [MulOpposite.op_one, one_smul, smul_eq_mul]
    change v g (f g) * B i (f g) = v g i
    rw [hcol]
    field_simp
  let r : ProjectiveReduction (obsShift μ 𝔐) := {
    q := q
    κ := id
    v := v
    c := fun _ => 1
    κ_surj := Function.surjective_id
    v_ne := hv
    c_ne := fun _ => one_ne_zero
    decomp := fun g => by rw [hshift]; simp
    classes := fun g h => by
      constructor
      · intro hgh
        change g = h at hgh
        subst h
        exact ⟨1, one_ne_zero, by simp⟩
      · intro hproj
        by_contra hne
        apply hdistinct g h hne
        obtain ⟨c, hc, heq⟩ := hproj
        refine ⟨c, hc, ?_⟩
        rw [← hshift g, ← hshift h]
        exact heq }
  refine ⟨CompatibleSpace p q, inferInstance, μ, 𝔐, r, rfl,
    Equiv.refl (Fin q), ?_⟩
  intro g
  rfl

/-! The exact version retains the selected assignment and the unnormalized shifts. -/

-- @node: compatible_model_exact_shifts
lemma compatible_model_exact_shifts {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p)
    (hf : f ∈ assignmentFiber v) :
    ∃ (Ω : Type) (ms : MeasurableSpace Ω) (μ : Measure Ω),
      letI : MeasurableSpace Ω := ms
      ∃ 𝔐 : AtomicCountModel p q Ω μ,
        𝔐.t = f ∧ (∀ g, 𝔐.α g = v g (f g)) ∧
        ∀ g, obsShift μ 𝔐 g = v g := by
  obtain ⟨B, hcol, hdiag, hacyclic⟩ := compatible_canonical_completion v f hf
  let μ := compatibleLaw B v f
  let 𝔐 := compatibleModel hp hq v f hf B hdiag hacyclic
  refine ⟨CompatibleSpace p q, inferInstance, μ, 𝔐, rfl, (fun _ => rfl), ?_⟩
  intro g
  have hs : obsShift μ 𝔐 g = totalEffect 𝔐.A *ᵥ
      (fun i => 𝔐.η g.succ i - 𝔐.η 0 i) := by
    funext i
    rw [obsShift, obsMean_eq_structural_mean μ 𝔐 g.succ,
      obsMean_eq_structural_mean μ 𝔐 0]
    exact (congrFun (Matrix.mulVec_sub (totalEffect 𝔐.A)
      (𝔐.η g.succ) (𝔐.η 0)) i).symm
  rw [hs]
  change totalEffect (1 - B⁻¹) *ᵥ
    (fun i => compatibleEta v f g.succ i - compatibleEta v f 0 i) = v g
  rw [(acyclic_completion_to_mechanism B hdiag hacyclic).2]
  have heta : (fun i => compatibleEta v f g.succ i - compatibleEta v f 0 i) =
      v g (f g) • Pi.single (f g) 1 := by
    ext i
    simp [compatibleEta]
  rw [heta, Matrix.mulVec_smul, Matrix.mulVec_single]
  ext i
  simp only [Pi.smul_apply]
  have hn : v g (f g) ≠ 0 := by simpa [support] using hf.1 g
  simp only [MulOpposite.op_one, one_smul, smul_eq_mul]
  change v g (f g) * B i (f g) = v g i
  rw [hcol]
  field_simp

-- @node: compatible_model_exists_iff_assignment_nonempty
lemma compatible_model_exists_iff_assignment_nonempty {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (v : Fin q → Fin p → ℝ)
    (hv : ∀ g, v g ≠ 0) (hdistinct : ∀ g h, g ≠ h → ¬ ProjSim v g h) :
    ((∃ (M : ℕ) (Ω : Type) (ms : MeasurableSpace Ω) (μ : Measure Ω),
        letI : MeasurableSpace Ω := ms
        ∃ 𝔐 : AtomicCountModel p M Ω μ, GeneratesDirections μ 𝔐 v) ↔
      (assignmentFiber v).Nonempty) := by
  constructor
  · rintro ⟨M, Ω, ms, μ, 𝔐, hgen⟩
    exact generatedDirections_assignment_nonempty μ 𝔐 v hdistinct hgen
  · intro hf
    obtain ⟨Ω, ms, μ, 𝔐, hgen⟩ := compatible_model_realization hp hq v hv hdistinct hf
    exact ⟨q, Ω, ms, μ, 𝔐, hgen⟩

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

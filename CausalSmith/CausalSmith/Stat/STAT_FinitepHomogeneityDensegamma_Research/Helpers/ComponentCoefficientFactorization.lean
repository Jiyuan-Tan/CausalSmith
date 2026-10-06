module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentCoefficientGeometry
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentBoundaryGeometry
public import Causalean.Experimentation.DesignBased.ProductBlock

/-! Finite coefficient averaging over disjoint blocks. The binary independence theorem
is iterated here; the geometric localization of the actual likelihood remains a separate step. -/
@[expose] public section
noncomputable section
open scoped BigOperators
open Causalean.Experimentation.DesignBased
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Uniform averaging over a finite Boolean cube is unchanged after discarding coordinates on which the integrand does not depend. [This is the stated conclusion](goal). -/
-- @node: uniform_bool_cube_restrict
lemma uniform_bool_cube_restrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Prop) [DecidablePred p] (F : ({i // p i} → Bool) → ℝ) :
    (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ x : ι → Bool, F (fun i => x i) =
      (Fintype.card ({i // p i} → Bool) : ℝ)⁻¹ *
        ∑ y : {i // p i} → Bool, F y := by
  classical
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => Bool)
  have hsum : (∑ x : ι → Bool, F (fun i => x i)) =
      ∑ x : ({i // p i} → Bool) × ({i // ¬ p i} → Bool), F x.1 := by
    exact Fintype.sum_equiv e _ _ (fun x => rfl)
  rw [hsum]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_fun]
  have hc : Fintype.card {i // p i} + Fintype.card {i // ¬ p i} =
      Fintype.card ι := by
    rw [Fintype.card_subtype_compl]
    exact Nat.add_sub_of_le (Fintype.card_subtype_le p)
  norm_num [Fintype.card_bool]
  have hpow : (2 : ℝ) ^ Fintype.card ι =
      2 ^ Fintype.card {i // p i} *
        2 ^ (Fintype.card ι - Fintype.card {i // p i}) := by
    rw [← pow_add, Nat.add_sub_of_le (Fintype.card_subtype_le p)]
  rw [hpow]
  field_simp
  rw [← Finset.mul_sum]

/-- Uniform Boolean-cube averaging commutes with restriction along any finite coordinate embedding. [This is the stated conclusion](goal). -/
-- @node: uniform_bool_cube_embedding
lemma uniform_bool_cube_embedding {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ↪ ι) (F : (κ → Bool) → ℝ) :
    (Fintype.card (ι → Bool) : ℝ)⁻¹ *
        ∑ x : ι → Bool, F (fun k => x (e k)) =
      (Fintype.card (κ → Bool) : ℝ)⁻¹ * ∑ y : κ → Bool, F y := by
  classical
  let _ : Fintype (Set.range e) := Subtype.fintype (fun i => i ∈ Set.range e)
  let er : κ ≃ Set.range e := e.toEquivRange
  let q : (κ → Bool) ≃ (Set.range e → Bool) :=
    Equiv.piCongrLeft (fun _ => Bool) er
  have h := uniform_bool_cube_restrict (fun i : ι => i ∈ Set.range e)
    (fun s => F (q.symm s))
  have hleft : (∑ x : ι → Bool, F (q.symm (fun i : Set.range e => x i))) =
      ∑ x : ι → Bool, F (fun k => x (e k)) := by
    apply Finset.sum_congr rfl
    intro x _
    congr 1
  have hcard : Fintype.card ({i : ι // i ∈ Set.range e} → Bool) =
      Fintype.card (κ → Bool) := by
    exact Fintype.card_congr q.symm
  have hsum : (∑ s : Set.range e → Bool, F (q.symm s)) =
      ∑ y : κ → Bool, F y := by
    exact (Fintype.sum_equiv q _ _ (fun y => by simp)).symm
  rw [hleft] at h
  calc
    _ = (Fintype.card ({i : ι // i ∈ Set.range e} → Bool) : ℝ)⁻¹ *
        ∑ s : Set.range e → Bool, F (q.symm s) := h
    _ = _ := by
      congr 1
      · exact congrArg Inv.inv (by exact_mod_cast hcard)

/-- Two normalized finite product laws have the same expectation for a function that is local to coordinates where their one-coordinate weights agree. This statement assumes [the hw condition](hyp:hw), [the hw' condition](hyp:hw'), [the hlocal condition](hyp:hlocal), [the hagrees condition](hyp:hagrees). [This is the stated conclusion](goal). -/
-- @node: finite_weighted_local_congr
lemma finite_weighted_local_congr {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Nonempty α] (w w' : ι → α → ℝ)
    (hw : ∀ i, ∑ q, w i q = 1) (hw' : ∀ i, ∑ q, w' i q = 1)
    (p : ι → Prop) (f : (ι → α) → ℝ)
    (hlocal : ∀ x y, (∀ i, p i → x i = y i) → f x = f y)
    (hagrees : ∀ i, p i → w i = w' i) :
    (∑ x : ι → α, (∏ i, w i (x i)) * f x) =
      ∑ x : ι → α, (∏ i, w' i (x i)) * f x := by
  classical
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => α)
  let F : ({i // p i} → α) → ℝ := fun xs =>
    f (e.symm (xs, fun _ => Classical.choice inferInstance))
  have hf (x : ι → α) : f x = F (fun i => x i) := by
    apply hlocal
    intro i hi
    simp [e, hi]
  have marginal (v : ι → α → ℝ) (hv : ∀ i, ∑ q, v i q = 1) :
      (∑ x : ι → α, (∏ i, v i (x i)) * f x) =
        ∑ xs : {i // p i} → α,
          (∏ i : {i // p i}, v (i : ι) (xs i)) * F xs := by
    have hprod (z : ({i // p i} → α) × ({i // ¬ p i} → α)) :
        (∏ i, v i ((e.symm z) i)) =
          (∏ i : {i // p i}, v (i : ι) (z.1 i)) *
            ∏ i : {i // ¬ p i}, v (i : ι) (z.2 i) := by
      rw [← Fintype.prod_subtype_mul_prod_subtype p]
      congr 1
      · apply Fintype.prod_congr
        intro i
        simp [e, i.property]
      · apply Fintype.prod_congr
        intro i
        simp [e, i.property]
    have hcomp : ∑ ys : {i // ¬ p i} → α,
        ∏ i : {i // ¬ p i}, v (i : ι) (ys i) = 1 := by
      rw [show (∑ ys : {i // ¬ p i} → α,
          ∏ i : {i // ¬ p i}, v (i : ι) (ys i)) =
          ∏ i : {i // ¬ p i}, ∑ q, v (i : ι) q by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]]
      simp [hv]
    calc
      _ = ∑ z : ({i // p i} → α) × ({i // ¬ p i} → α),
          ((∏ i : {i // p i}, v (i : ι) (z.1 i)) *
            ∏ i : {i // ¬ p i}, v (i : ι) (z.2 i)) * F z.1 := by
        exact Fintype.sum_equiv e _ _ (fun x => by
          rw [hf x]
          have hp := hprod (e x)
          rw [e.symm_apply_apply] at hp
          rw [hp]
          simp [e])
      _ = ∑ xs : {i // p i} → α,
          (∏ i : {i // p i}, v (i : ι) (xs i)) * F xs := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro xs _
        rw [show (∑ ys : {i // ¬ p i} → α,
            ((∏ i : {i // p i}, v (i : ι) (xs i)) *
              ∏ i : {i // ¬ p i}, v (i : ι) (ys i)) * F xs) =
              ((∏ i : {i // p i}, v (i : ι) (xs i)) * F xs) *
                ∑ ys : {i // ¬ p i} → α,
                  ∏ i : {i // ¬ p i}, v (i : ι) (ys i) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ys _
          ring]
        rw [hcomp, mul_one]
  rw [marginal w hw, marginal w' hw']
  apply Finset.sum_congr rfl
  intro xs _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [hagrees (i : ι) i.property]

/-- A conditional coefficient expectation only uses coarse-sign values at the undisclosed coordinates on which its integrand depends. This statement assumes [the hlocal condition](hyp:hlocal), [the hsign condition](hyp:hsign). [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_local_congr
lemma conditionalPairWeight_local_congr (ν : Bool) (K M : ℕ)
    (σ τ : Fin (M / 2) → Bool) (δ : Disclosure K)
    (S : Finset (Fin (K + 1))) (f : CoefficientPairs K → ℝ)
    (hlocal : ∀ p p', (∀ i ∈ S, p i = p' i) → f p = f p')
    (hsign : ∀ i ∈ S, δ i = none →
      coarseTent M σ ((i : ℝ) / K) = coarseTent M τ ((i : ℝ) / K)) :
    (∑ p, conditionalPairWeight ν K M σ δ p * f p) =
      ∑ p, conditionalPairWeight ν K M τ δ p * f p := by
  classical
  let w (ρ : Fin (M / 2) → Bool) (i : Fin (K + 1)) (q : Bool × Bool) : ℝ :=
    match δ i with
    | some r => if q = r then 1 else 0
    | none => pairWeight ν (coarseTent M ρ ((i : ℝ) / K)) q.1 q.2
  have hw (ρ : Fin (M / 2) → Bool) (i : Fin (K + 1)) : ∑ q, w ρ i q = 1 := by
    cases hd : δ i with
    | some r => simp [w, hd]
    | none => simpa only [w, hd] using pairWeight_sum ν (coarseTent M ρ ((i : ℝ) / K))
  change (∑ p, (∏ i, w σ i (p i)) * f p) =
    ∑ p, (∏ i, w τ i (p i)) * f p
  apply finite_weighted_local_congr (w σ) (w τ) (hw σ) (hw τ)
    (fun i => i ∈ S) f
  · exact fun p p' hp => hlocal p p' (fun i hi => hp i hi)
  · intro i hi
    funext q
    cases hd : δ i with
    | some r => simp [w, hd]
    | none => simp [w, hd, hsign i hi hd]

/-- On a record of a component, the smoothed coarse tent uses only the sign owned by that component. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the heven condition](hyp:heven), [the hactual condition](hyp:hactual), [the hC condition](hyp:hC), [the hi condition](hyp:hi). [This is the stated conclusion](goal). -/
-- @node: smoothedTent_component_local
lemma smoothedTent_component_local (n K M : ℕ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K) (heven : 2 ∣ M)
    (aug : Augmentation n K)
    (hactual : ∃ q : CoefficientPairs K, aug.2.2 = disclose K M q)
    {C : Finset (Fin n)} (hC : C ∈ components n K M aug)
    {i : Fin n} (hi : i ∈ C) (σ : Fin (M / 2) → Bool) :
    smoothedTent K M σ (aug.1 i) =
      smoothedTent K M
        (fun _ => σ ⟨pairIndex M aug C, pairIndex_lt_half n K M hM heven aug hC⟩)
        (aug.1 i) := by
  classical
  obtain ⟨q, hq⟩ := hactual
  unfold smoothedTent
  apply Finset.sum_congr rfl
  intro j _
  by_cases hjframe : frameCoord K j (aug.1 i) = 0
  · simp [hjframe]
  congr 1
  cases hd : aug.2.2 j with
  | none =>
      have hj : j ∈ activeUndisclosedSupport aug C := by
        simp only [activeUndisclosedSupport, Finset.mem_filter, Finset.mem_univ, true_and, hd]
        exact ⟨i, hi, hjframe⟩
      exact coarseTent_activeUndisclosedSupport_local n K M hK hM hdiv heven
        aug ⟨q, hq⟩ hC hj σ
  | some r =>
      have hb : boundaryNode K M j := by
        rw [hq] at hd
        unfold disclose at hd
        split at hd
        · assumption
        · simp at hd
      rw [coarseTent_boundaryNode_zero K M hK j hb σ,
        coarseTent_boundaryNode_zero K M hK j hb]

/-- The record likelihood on a component can replace the global coarse sign field by that component's owning sign. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the heven condition](hyp:heven), [the hactual condition](hyp:hactual), [the hC condition](hyp:hC), [the hi condition](hyp:hi). [This is the stated conclusion](goal). -/
-- @node: labelDensity_component_sign_local
lemma labelDensity_component_sign_local (ν : Bool) (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K) (heven : 2 ∣ M)
    (aug : Augmentation n K)
    (hactual : ∃ q : CoefficientPairs K, aug.2.2 = disclose K M q)
    {C : Finset (Fin n)} (hC : C ∈ components n K M aug)
    {i : Fin n} (hi : i ∈ C) (σ : Fin (M / 2) → Bool)
    (pairs : CoefficientPairs K) (label : Bool × Bool) :
    labelDensity ν K M a u (σ, pairs) (aug.1 i) (aug.2.1 i) label =
      labelDensity ν K M a u
        ((fun _ => σ ⟨pairIndex M aug C,
          pairIndex_lt_half n K M hM heven aug hC⟩), pairs)
        (aug.1 i) (aug.2.1 i) label := by
  have hs := smoothedTent_component_local n K M hK hM hdiv heven
    aug hactual hC hi σ
  simp only [labelDensity, copulaZeta, copulaT, copulaXi, copulaUpsilon]
  rw [hs]

/-- A normalized product coefficient law factors any finite family of functions of pairwise disjoint coordinate blocks. No occupancy or block-size restriction is used. This statement assumes [the hw0 condition](hyp:hw0), [the hw1 condition](hyp:hw1), [the hdisj condition](hyp:hdisj), [the hlocal condition](hyp:hlocal). [This is the stated conclusion](goal). -/
-- @node: finite_weighted_disjoint_blocks
lemma finite_weighted_disjoint_blocks {ι α κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (w : ι → α → ℝ)
    (hw0 : ∀ i q, 0 ≤ w i q) (hw1 : ∀ i, ∑ q, w i q = 1)
    (s : Finset κ) (S : κ → Finset ι) (f : κ → (ι → α) → ℝ)
    (hdisj : (↑s : Set κ).PairwiseDisjoint S)
    (hlocal : ∀ k ∈ s, ∀ p p', (∀ i ∈ S k, p i = p' i) → f k p = f k p') :
    (∑ p : ι → α, (∏ i, w i (p i)) * ∏ k ∈ s, f k p) =
      ∏ k ∈ s, ∑ p : ι → α, (∏ i, w i (p i)) * f k p := by
  classical
  let D (i : ι) : FiniteDesign α := ⟨w i, hw0 i, hw1 i⟩
  change (prodDesign D).E (fun p => ∏ k ∈ s, f k p) =
    ∏ k ∈ s, (prodDesign D).E (f k)
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    simp only [Finset.prod_insert hk]
    rw [FiniteDesign.E_prod_block_mul D (S k) (f k) (fun p => ∏ j ∈ s, f j p)]
    · rw [ih]
      · intro j hj l hl hne
        exact hdisj (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hl) hne
      · intro j hj
        exact hlocal j (Finset.mem_insert_of_mem hj)
    · exact hlocal k (Finset.mem_insert_self _ _)
    · intro p p' hp
      apply Finset.prod_congr rfl
      intro j hj
      apply hlocal j (Finset.mem_insert_of_mem hj) p p'
      intro i hi
      apply hp i
      intro hik
      exact Finset.disjoint_left.mp
        (hdisj (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj)
          (by intro he; subst j; exact hk hj)) hik hi

/-- The actual conditional coefficient prior factors block-local likelihoods; disclosed coordinates are included with their point-mass weights rather than discarded. This statement assumes [the hdisj condition](hyp:hdisj), [the hlocal condition](hyp:hlocal). [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_disjoint_blocks
lemma conditionalPairWeight_disjoint_blocks {κ : Type*}
    (ν : Bool) (K M : ℕ) (σ : Fin (M / 2) → Bool) (δ : Disclosure K)
    (s : Finset κ) (S : κ → Finset (Fin (K + 1)))
    (f : κ → CoefficientPairs K → ℝ)
    (hdisj : (↑s : Set κ).PairwiseDisjoint S)
    (hlocal : ∀ k ∈ s, ∀ p p', (∀ i ∈ S k, p i = p' i) → f k p = f k p') :
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p * ∏ k ∈ s, f k p) =
      ∏ k ∈ s, ∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p * f k p := by
  classical
  let w (i : Fin (K+1)) (q : Bool × Bool) : ℝ := match δ i with
    | some r => if q = r then 1 else 0
    | none => pairWeight ν (coarseTent M σ ((i:ℝ)/K)) q.1 q.2
  have hw0 (i : Fin (K+1)) (q : Bool × Bool) : 0 ≤ w i q := by
    cases hd : δ i with
    | some r => simp [w, hd]; split <;> norm_num
    | none => simpa only [w, hd] using
        pairWeight_nonneg ν _ (coarseTent_abs_le_one M σ ((i:ℝ)/K)) q.1 q.2
  have hw1 (i : Fin (K+1)) : ∑ q, w i q = 1 := by
    cases hd : δ i with
    | some r => simp [w, hd]
    | none => simpa only [w, hd] using pairWeight_sum ν (coarseTent M σ ((i:ℝ)/K))
  exact finite_weighted_disjoint_blocks w hw0 hw1 s S f hdisj hlocal

/-- With the disclosed pairs fixed, the actual complete record likelihood factors over components whenever their remaining coefficient blocks are disjoint. The localization hypotheses concern coordinate dependence, not a discrepancy or rate bound. This statement assumes [the hdisj condition](hyp:hdisj), [the hlocal condition](hyp:hlocal). [This is the stated conclusion](goal). -/
-- @node: conditional_record_product_factorization
lemma conditional_record_product_factorization (ν : Bool) (n K M : ℕ) (a u : ℝ)
    (σ : Fin (M / 2) → Bool) (aug : Augmentation n K) (labels : Labels n)
    (S : Finset (Fin n) → Finset (Fin (K + 1)))
    (hdisj : (↑(components n K M aug) : Set (Finset (Fin n))).PairwiseDisjoint S)
    (hlocal : ∀ C ∈ components n K M aug, ∀ p p',
      (∀ j ∈ S C, p j = p' j) →
      (∏ i ∈ C, labelDensity ν K M a u (σ, disclosureClamp aug.2.2 p)
        (aug.1 i) (aug.2.1 i) (labels i)) =
      ∏ i ∈ C, labelDensity ν K M a u (σ, disclosureClamp aug.2.2 p')
        (aug.1 i) (aug.2.1 i) (labels i)) :
    (∑ p, conditionalPairWeight ν K M σ aug.2.2 p *
      ∏ i : Fin n, labelDensity ν K M a u (σ,p) (aug.1 i) (aug.2.1 i) (labels i)) =
      ∏ C ∈ components n K M aug, ∑ p, conditionalPairWeight ν K M σ aug.2.2 p *
        ∏ i ∈ C, labelDensity ν K M a u (σ,p) (aug.1 i) (aug.2.1 i) (labels i) := by
  classical
  rw [← conditionalPairWeight_clamp_average ν K M σ aug.2.2]
  simp_rw [prod_records_eq_prod_components n K M aug]
  rw [conditionalPairWeight_disjoint_blocks ν K M σ aug.2.2
    (components n K M aug) S _ hdisj hlocal]
  apply Finset.prod_congr rfl
  intro C _
  exact conditionalPairWeight_clamp_average ν K M σ aug.2.2
    (fun p => ∏ i ∈ C, labelDensity ν K M a u (σ,p) (aug.1 i) (aug.2.1 i) (labels i))

/-- Under an actual boundary disclosure, a fixed global coarse-sign likelihood factors into component likelihoods carrying only their owning coarse sign. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the heven condition](hyp:heven), [the hactual condition](hyp:hactual), [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
-- @node: conditional_record_component_factorization
lemma conditional_record_component_factorization (ν : Bool) (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K) (heven : 2 ∣ M)
    (σ : Fin (M / 2) → Bool) (aug : Augmentation n K) (labels : Labels n)
    (hactual : ∃ q : CoefficientPairs K, aug.2.2 = disclose K M q)
    (g : Finset (Fin n) → Fin (M / 2))
    (hg : ∀ C ∈ components n K M aug, (g C).val = pairIndex M aug C) :
    (∑ p, conditionalPairWeight ν K M σ aug.2.2 p *
      ∏ i : Fin n, labelDensity ν K M a u (σ,p)
        (aug.1 i) (aug.2.1 i) (labels i)) =
      ∏ C ∈ components n K M aug,
        componentDensity ν (σ (g C)) n K M a u aug C labels := by
  classical
  rw [conditional_record_product_factorization ν n K M a u σ aug labels
    (activeUndisclosedSupport aug)
    (activeUndisclosedSupport_pairwiseDisjoint n K M hK hM hdiv aug hactual)
    (fun C hC p p' hp =>
      componentLikelihood_clamp_local ν a u σ aug C labels p p' hp)]
  apply Finset.prod_congr rfl
  intro C hC
  let owner : Fin (M / 2) :=
    ⟨pairIndex M aug C, pairIndex_lt_half n K M hM heven aug hC⟩
  have hgowner : g C = owner := Fin.ext (hg C hC)
  let τ : Fin (M / 2) → Bool := fun _ => σ owner
  rw [hgowner]
  change (∑ p, conditionalPairWeight ν K M σ aug.2.2 p *
      ∏ i ∈ C, labelDensity ν K M a u (σ,p)
        (aug.1 i) (aug.2.1 i) (labels i)) =
    ∑ p, conditionalPairWeight ν K M τ aug.2.2 p *
      ∏ i ∈ C, labelDensity ν K M a u (τ,p)
        (aug.1 i) (aug.2.1 i) (labels i)
  calc
    _ = ∑ p, conditionalPairWeight ν K M σ aug.2.2 p *
        ∏ i ∈ C, labelDensity ν K M a u
          (σ, disclosureClamp aug.2.2 p)
          (aug.1 i) (aug.2.1 i) (labels i) := by
      exact (conditionalPairWeight_clamp_average ν K M σ aug.2.2
        (fun p => ∏ i ∈ C, labelDensity ν K M a u (σ,p)
          (aug.1 i) (aug.2.1 i) (labels i))).symm
    _ = ∑ p, conditionalPairWeight ν K M τ aug.2.2 p *
        ∏ i ∈ C, labelDensity ν K M a u
          (σ, disclosureClamp aug.2.2 p)
          (aug.1 i) (aug.2.1 i) (labels i) := by
      apply conditionalPairWeight_local_congr ν K M σ τ aug.2.2
        (activeUndisclosedSupport aug C)
      · exact fun p p' hp => componentLikelihood_clamp_local ν a u σ aug C labels
          p p' hp
      · intro j hj _
        exact coarseTent_activeUndisclosedSupport_local n K M hK hM hdiv heven
          aug hactual hC hj σ
    _ = ∑ p, conditionalPairWeight ν K M τ aug.2.2 p *
        ∏ i ∈ C, labelDensity ν K M a u
          (τ, disclosureClamp aug.2.2 p)
          (aug.1 i) (aug.2.1 i) (labels i) := by
      apply Finset.sum_congr rfl
      intro p _
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact labelDensity_component_sign_local ν n K M a u hK hM hdiv heven
        aug hactual hC hi σ (disclosureClamp aug.2.2 p) (labels i)
    _ = ∑ p, conditionalPairWeight ν K M τ aug.2.2 p *
        ∏ i ∈ C, labelDensity ν K M a u (τ,p)
          (aug.1 i) (aug.2.1 i) (labels i) := by
      exact conditionalPairWeight_clamp_average ν K M τ aug.2.2
        (fun p => ∏ i ∈ C, labelDensity ν K M a u (τ,p)
          (aug.1 i) (aug.2.1 i) (labels i))

end CausalSmith.Stat.FinitepHomogeneityDensegamma

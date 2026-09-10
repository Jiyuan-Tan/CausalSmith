import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.Kneser
import Causalean.Experimentation.DesignBased.Product
import Causalean.Experimentation.DesignBased.ProductVariance
import Mathlib.Logic.Equiv.Fintype

/-!
# Uniform ordered partitions and the independent two-stage design

Only the uniform law on ordered disjoint group tuples is new.  The independent
combination with complete treatment randomization uses the existing dependent
product design and its pushforward operation.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased

-- @env: S3
variable (n M G G1 : ℕ)

/-- Ordered tuples of pairwise-disjoint groups. -/
abbrev PartitionTuple (n M G : ℕ) :=
  {T : Fin G → Omega n M //
    ∀ g g', g ≠ g' → Disjoint (T g).1 (T g').1}
  -- @realizes \mathbf A_n(ordered pairwise-disjoint group tuple)

/-- Complete treatment assignments to the realized groups. -/
abbrev TreatmentSpace (G G1 : ℕ) :=
  {S : Finset (Fin G) // S.card = G1}
  -- @realizes \mathbf Z_n(exactly G1 treated groups)

/-- [If the requested groups fit in the population](hyp:hMG), [the ordered partition space is nonempty](goal). -/
lemma partitionTuple_nonempty (hMG : M * G ≤ n) : Nonempty (PartitionTuple n M G) := by
  classical
  have hGM : G * M ≤ n := by simpa [Nat.mul_comm] using hMG
  let E : Fin G × Fin M ↪ Fin n :=
    finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb hGM)
  let e (g : Fin G) : Fin M ↪ Fin n :=
    (⟨fun i => (g, i), by
      intro i j hij
      exact congrArg Prod.snd hij⟩ : Fin M ↪ Fin G × Fin M).trans E
  let T : Fin G → Omega n M := fun g =>
    ⟨Finset.univ.map (e g), by simp⟩
  exact ⟨⟨T, by
    intro g g' hgg'
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [T, Finset.mem_map] at hx hx'
    obtain ⟨i, -, rfl⟩ := hx
    obtain ⟨j, -, hij⟩ := hx'
    change E (g', j) = E (g, i) at hij
    have hp : (g, i) = (g', j) := E.injective hij.symm
    exact hgg' (congrArg Prod.fst hp)⟩⟩

/-- The uniform first-stage law. -/
noncomputable def uniformPartitionTuple (hMG : M * G ≤ n) :
    FiniteDesign (PartitionTuple n M G) := by
  letI : Nonempty (PartitionTuple n M G) := partitionTuple_nonempty n M G hMG
  exact uniformFiniteDesign (PartitionTuple n M G)

/-- The two dependent coordinate spaces: partition tuple, then treatment set. -/
def twoStageSpace (n M G G1 : ℕ) : Bool → Type
  | false => PartitionTuple n M G
  | true => TreatmentSpace G G1

/-- For [the population and group-count parameters](hyp:n,M,G,G1) and [a stage indicator](hyp:i), [the two-stage sample space has a finite enumeration](goal). -/
noncomputable instance twoStageSpaceFintype (i : Bool) :
    Fintype (twoStageSpace n M G G1 i) := by
  cases i <;> simp only [twoStageSpace] <;> infer_instance

/-- Coordinate designs for the dependent product. -/
noncomputable def twoStageDesigns (hMG : M * G ≤ n) (hG1 : G1 ≤ G) :
    ∀ i, FiniteDesign (twoStageSpace n M G G1 i) := by
  intro i
  cases i
  · simpa only [twoStageSpace] using uniformPartitionTuple n M G hMG
  · simpa only [twoStageSpace] using completeRandomization G1 (by simpa using hG1)

/-- The two Boolean-indexed stage coordinates, repackaged as an ordinary pair. -/
-- @node: twoStagePairEquiv
def twoStagePairEquiv : (∀ i, twoStageSpace n M G G1 i) ≃
    PartitionTuple n M G × TreatmentSpace G G1 where
  toFun w := (w false, w true)
  invFun p := fun b => match b with
    | false => p.1
    | true => p.2
  left_inv w := by funext b; cases b <;> rfl
  right_inv p := rfl

-- @node: def:random-partition-design
/-- Independent uniform partition and complete group-treatment randomization. -/
noncomputable def randomPartitionDesign (hMG : M * G ≤ n) (hG1 : G1 ≤ G) :
    FiniteDesign (PartitionTuple n M G × TreatmentSpace G G1) :=
  (prodDesign (twoStageDesigns n M G G1 hMG hG1)).map
    (twoStagePairEquiv n M G G1)

-- @node: partitionTuplePermEquiv
/-- Relabeling population units by a permutation relabels ordered partition tuples. -/
def partitionTuplePermEquiv (σ : Equiv.Perm (Fin n)) :
    PartitionTuple n M G ≃ PartitionTuple n M G where
  toFun T := ⟨fun g => ⟨T.1 g |>.1.map σ.toEmbedding, by simp [(T.1 g).2]⟩, by
    intro g g' hgg'
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_map] at hx hx'
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, hij⟩ := hx'
    exact Finset.disjoint_left.mp (T.2 g g' hgg') hi
      (σ.injective hij.symm ▸ hj)⟩
  invFun T := ⟨fun g => ⟨T.1 g |>.1.map σ.symm.toEmbedding, by simp [(T.1 g).2]⟩, by
    intro g g' hgg'
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_map] at hx hx'
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, hij⟩ := hx'
    exact Finset.disjoint_left.mp (T.2 g g' hgg') hi
      (σ.symm.injective hij.symm ▸ hj)⟩
  left_inv T := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    ext x
    simp
  right_inv T := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    ext x
    simp

-- @node: orderedDisjointPairPermEquiv
/-- Relabeling population units by a permutation relabels ordered disjoint pairs. -/
def orderedDisjointPairPermEquiv (σ : Equiv.Perm (Fin n)) :
    OrderedDisjointPair n M ≃ OrderedDisjointPair n M where
  toFun P := ⟨(⟨P.1.1.1.map σ.toEmbedding, by simp [P.1.1.2]⟩,
      ⟨P.1.2.1.map σ.toEmbedding, by simp [P.1.2.2]⟩), by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_map] at hx hx'
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, hij⟩ := hx'
    exact Finset.disjoint_left.mp P.2 hi (σ.injective hij.symm ▸ hj)⟩
  invFun P := ⟨(⟨P.1.1.1.map σ.symm.toEmbedding, by simp [P.1.1.2]⟩,
      ⟨P.1.2.1.map σ.symm.toEmbedding, by simp [P.1.2.2]⟩), by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_map] at hx hx'
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, hij⟩ := hx'
    exact Finset.disjoint_left.mp P.2 hi (σ.symm.injective hij.symm ▸ hj)⟩
  left_inv P := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> ext x <;> simp
  right_inv P := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> ext x <;> simp

-- @node: orderedDisjointPair_perm_exists
/-- For two ordered disjoint pairs, [one population relabeling maps the first pair to the second](goal). -/
lemma orderedDisjointPair_perm_exists (P Q : OrderedDisjointPair n M) :
    ∃ σ : Equiv.Perm (Fin n),
      P.1.1.1.map σ.toEmbedding = Q.1.1.1 ∧
      P.1.2.1.map σ.toEmbedding = Q.1.2.1 := by
  classical
  let e1 : ↥P.1.1.1 ≃ ↥Q.1.1.1 := P.1.1.1.equivOfCardEq (by rw [P.1.1.2, Q.1.1.2])
  let e2 : ↥P.1.2.1 ≃ ↥Q.1.2.1 := P.1.2.1.equivOfCardEq (by rw [P.1.2.2, Q.1.2.2])
  let f : ↥P.1.1.1 ⊕ ↥P.1.2.1 → Fin n := Sum.elim Subtype.val Subtype.val
  let q : ↥P.1.1.1 ⊕ ↥P.1.2.1 → Fin n :=
    Sum.elim (fun i => (e1 i).1) (fun i => (e2 i).1)
  have hf : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext hxy)
      | inr y =>
        change x.1 = y.1 at hxy
        have hy : x.1 ∈ P.1.2.1 := hxy.symm ▸ y.2
        exact False.elim (Finset.disjoint_left.mp P.2 x.2 hy)
    | inr x =>
      cases y with
      | inl y =>
        change x.1 = y.1 at hxy
        have hx : y.1 ∈ P.1.2.1 := hxy ▸ x.2
        exact False.elim (Finset.disjoint_left.mp P.2 y.2 hx)
      | inr y => exact congrArg Sum.inr (Subtype.ext hxy)
  have hq : Function.Injective q := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (e1.injective (Subtype.ext hxy))
      | inr y =>
        change (e1 x).1 = (e2 y).1 at hxy
        have hy : (e1 x).1 ∈ Q.1.2.1 := hxy.symm ▸ (e2 y).2
        exact False.elim (Finset.disjoint_left.mp Q.2 (e1 x).2 hy)
    | inr x =>
      cases y with
      | inl y =>
        change (e2 x).1 = (e1 y).1 at hxy
        have hx : (e1 y).1 ∈ Q.1.2.1 := hxy ▸ (e2 x).2
        exact False.elim (Finset.disjoint_left.mp Q.2 (e1 y).2 hx)
      | inr y => exact congrArg Sum.inr (e2.injective (Subtype.ext hxy))
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f q hf hq
  refine ⟨σ, ?_, ?_⟩
  · apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      have hiσ := hσ (Sum.inl ⟨i, hi⟩)
      change σ i = (e1 ⟨i, hi⟩).1 at hiσ
      change σ i ∈ Q.1.1.1
      rw [hiσ]
      exact (e1 ⟨i, hi⟩).2
    · intro x hx
      let j : ↥Q.1.1.1 := ⟨x, hx⟩
      let i := e1.symm j
      exact Finset.mem_map.mpr ⟨i.1, i.2, by
        have hiσ := hσ (Sum.inl i)
        change σ i.1 = (e1 i).1 at hiσ
        simpa [i, j] using hiσ⟩
  · apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      have hiσ := hσ (Sum.inr ⟨i, hi⟩)
      change σ i = (e2 ⟨i, hi⟩).1 at hiσ
      change σ i ∈ Q.1.2.1
      rw [hiσ]
      exact (e2 ⟨i, hi⟩).2
    · intro x hx
      let j : ↥Q.1.2.1 := ⟨x, hx⟩
      let i := e2.symm j
      exact Finset.mem_map.mpr ⟨i.1, i.2, by
        have hiσ := hσ (Sum.inr i)
        change σ i.1 = (e2 i).1 at hiσ
        simpa [i, j] using hiσ⟩

/-- The realized group in coordinate `g`. -/
def groupAt (w : PartitionTuple n M G × TreatmentSpace G G1) (g : Fin G) : Omega n M :=
  w.1.1 g

/-- [When the groups fit in the population, there is at least one group, and the treatment count is feasible](hyp:hMG,hG,hG1), [each group coordinate is marginally uniform on the slice](goal). -/
lemma marginal_uniform_coord (hMG : M * G ≤ n) (hG : 0 < G) (hG1 : G1 ≤ G)
    (g : Fin G) (f : Omega n M → ℝ) :
    (randomPartitionDesign n M G G1 hMG hG1).E (fun w => f (groupAt n M G G1 w g)) =
      (slice n M (le_trans (Nat.le_mul_of_pos_right M hG) hMG)).E f := by
  classical
  let hM : M ≤ n := le_trans (Nat.le_mul_of_pos_right M hG) hMG
  let D := uniformPartitionTuple n M G hMG
  have hprod :
      (randomPartitionDesign n M G G1 hMG hG1).E
          (fun w => f (groupAt n M G G1 w g)) =
        D.E (fun T => f (T.1 g)) := by
    rw [randomPartitionDesign, FiniteDesign.E_map]
    exact FiniteDesign.E_prod_apply (twoStageDesigns n M G G1 hMG hG1) false
      (fun T => f (T.1 g))
  rw [hprod]
  let A0 : Omega n M := (Classical.choice (partitionTuple_nonempty n M G hMG)).1 g
  let c : ℕ := Fintype.card {T : PartitionTuple n M G // T.1 g = A0}
  have hfiber : ∀ A : Omega n M,
      Fintype.card {T : PartitionTuple n M G // T.1 g = A} = c := by
    intro A
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq A.1 A0.1 (by rw [A.2, A0.2])
    let e : {T : PartitionTuple n M G // T.1 g = A} ≃
        {T : PartitionTuple n M G // T.1 g = A0} :=
      (partitionTuplePermEquiv n M G σ).subtypeEquiv
        (by
          intro T
          constructor
          · intro hT
            apply Subtype.ext
            simpa [partitionTuplePermEquiv, hT] using hσ
          · intro hm
            apply Subtype.ext
            apply Finset.map_injective σ.toEmbedding
            have hm' := congrArg (fun S : Omega n M => S.1) hm
            simpa [partitionTuplePermEquiv, hσ] using hm'
          )
    exact Fintype.card_congr e
  have hcpos : 0 < c := by
    let T0 : PartitionTuple n M G := Classical.choice (partitionTuple_nonempty n M G hMG)
    have hnon : Nonempty {T : PartitionTuple n M G // T.1 g = T0.1 g} :=
      ⟨⟨T0, rfl⟩⟩
    rw [← hfiber (T0.1 g)]
    exact Fintype.card_pos
  have hsum : (∑ T : PartitionTuple n M G, f (T.1 g)) = c * ∑ A : Omega n M, f A := by
    rw [← Fintype.sum_fiberwise (fun T : PartitionTuple n M G => T.1 g)
      (fun T => f (T.1 g))]
    simp_rw [show ∀ A : Omega n M,
      (∑ T : {T : PartitionTuple n M G // T.1 g = A}, f (T.1.1 g)) =
        c * f A by
          intro A
          calc
            (∑ T : {T : PartitionTuple n M G // T.1 g = A}, f (T.1.1 g)) =
                ∑ _T : {T : PartitionTuple n M G // T.1 g = A}, f A := by
              apply Finset.sum_congr rfl
              intro T _
              rw [T.2]
            _ = c * f A := by simp [nsmul_eq_mul, hfiber A]
      ]
    rw [Finset.mul_sum]
  have hcard : Fintype.card (PartitionTuple n M G) = c * Fintype.card (Omega n M) := by
    calc
      Fintype.card (PartitionTuple n M G) =
          ∑ A : Omega n M,
            Fintype.card {T : PartitionTuple n M G // T.1 g = A} := by
        simpa using Fintype.card_congr
          (Equiv.sigmaFiberEquiv (fun T : PartitionTuple n M G => T.1 g)).symm
      _ = c * Fintype.card (Omega n M) := by simp [hfiber, Nat.mul_comm]
  simp only [D, uniformPartitionTuple, uniformFiniteDesign, FiniteDesign.E, slice,
    completeRandomization]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsum, hcard]
  simp only [Fintype.card_finset_len]
  push_cast
  field_simp [show (c : ℝ) ≠ 0 by exact_mod_cast hcpos.ne']

/-- [When the groups and treatment count are feasible, two groups fit in the population, and the selected coordinates differ](hyp:hMG,hG1,h2M,hgg'), [the two coordinates are uniform over ordered disjoint pairs](goal). -/
lemma marginal_uniform_ordered_disjoint_pair (hMG : M * G ≤ n) (hG1 : G1 ≤ G)
    (h2M : 2 * M ≤ n) (g g' : Fin G) (hgg' : g ≠ g')
    (f : OrderedDisjointPair n M → ℝ) :
    (randomPartitionDesign n M G G1 hMG hG1).E
      (fun w => f ⟨(groupAt n M G G1 w g, groupAt n M G G1 w g'),
        w.1.2 g g' hgg'⟩) =
      (orderedDisjointPairDesign n M h2M).E f := by
  classical
  let D := uniformPartitionTuple n M G hMG
  let pairAt (T : PartitionTuple n M G) : OrderedDisjointPair n M :=
    ⟨(T.1 g, T.1 g'), T.2 g g' hgg'⟩
  have hprod :
      (randomPartitionDesign n M G G1 hMG hG1).E
          (fun w => f ⟨(groupAt n M G G1 w g, groupAt n M G G1 w g'),
            w.1.2 g g' hgg'⟩) = D.E (fun T => f (pairAt T)) := by
    rw [randomPartitionDesign, FiniteDesign.E_map]
    exact FiniteDesign.E_prod_apply (twoStageDesigns n M G G1 hMG hG1) false
      (fun T => f (pairAt T))
  rw [hprod]
  let P0 : OrderedDisjointPair n M :=
    pairAt (Classical.choice (partitionTuple_nonempty n M G hMG))
  let c : ℕ := Fintype.card {T : PartitionTuple n M G // pairAt T = P0}
  have hfiber : ∀ P : OrderedDisjointPair n M,
      Fintype.card {T : PartitionTuple n M G // pairAt T = P} = c := by
    intro P
    obtain ⟨σ, hσ1, hσ2⟩ := orderedDisjointPair_perm_exists n M P P0
    have hσP : orderedDisjointPairPermEquiv n M σ P = P0 := by
      apply Subtype.ext
      apply Prod.ext <;> apply Subtype.ext
      · exact hσ1
      · exact hσ2
    let e : {T : PartitionTuple n M G // pairAt T = P} ≃
        {T : PartitionTuple n M G // pairAt T = P0} :=
      (partitionTuplePermEquiv n M G σ).subtypeEquiv (by
        intro T
        have hcomm : pairAt (partitionTuplePermEquiv n M G σ T) =
            orderedDisjointPairPermEquiv n M σ (pairAt T) := rfl
        rw [hcomm, ← hσP]
        exact (orderedDisjointPairPermEquiv n M σ).injective.eq_iff.symm)
    exact Fintype.card_congr e
  have hcpos : 0 < c := by
    let T0 : PartitionTuple n M G := Classical.choice (partitionTuple_nonempty n M G hMG)
    have hnon : Nonempty {T : PartitionTuple n M G // pairAt T = pairAt T0} :=
      ⟨⟨T0, rfl⟩⟩
    rw [← hfiber (pairAt T0)]
    exact Fintype.card_pos
  have hsum : (∑ T : PartitionTuple n M G, f (pairAt T)) =
      c * ∑ P : OrderedDisjointPair n M, f P := by
    rw [← Fintype.sum_fiberwise pairAt (fun T => f (pairAt T))]
    simp_rw [show ∀ P : OrderedDisjointPair n M,
      (∑ T : {T : PartitionTuple n M G // pairAt T = P}, f (pairAt T.1)) =
        c * f P by
          intro P
          calc
            (∑ T : {T : PartitionTuple n M G // pairAt T = P}, f (pairAt T.1)) =
                ∑ _T : {T : PartitionTuple n M G // pairAt T = P}, f P := by
              apply Finset.sum_congr rfl
              intro T _
              rw [T.2]
            _ = c * f P := by simp [nsmul_eq_mul, hfiber P]]
    rw [Finset.mul_sum]
  have hcard : Fintype.card (PartitionTuple n M G) =
      c * Fintype.card (OrderedDisjointPair n M) := by
    calc
      Fintype.card (PartitionTuple n M G) =
          ∑ P : OrderedDisjointPair n M,
            Fintype.card {T : PartitionTuple n M G // pairAt T = P} := by
        simpa using Fintype.card_congr (Equiv.sigmaFiberEquiv pairAt).symm
      _ = c * Fintype.card (OrderedDisjointPair n M) := by
        simp [hfiber, Nat.mul_comm]
  simp only [D, uniformPartitionTuple, uniformFiniteDesign, FiniteDesign.E,
    orderedDisjointPairDesign]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hsum, hcard]
  push_cast
  field_simp [show (c : ℝ) ≠ 0 by exact_mod_cast hcpos.ne']

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

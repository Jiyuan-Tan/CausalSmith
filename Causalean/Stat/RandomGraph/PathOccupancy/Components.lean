module
public import Causalean.Stat.RandomGraph.PathOccupancy.PairClasses
public import Causalean.Stat.RandomGraph.PathOccupancy.Path
public import Causalean.Stat.RandomGraph.PathOccupancy.Probability

/-!
# Components of arbitrary local subrelations

Components are the equivalence classes of the symmetric, reflexive, transitive
closure of the supplied relation. No eligible edge is required to be present.
Pointwise domination by sums over labelled subsets permits the relation to
depend on both cells and marks, or on additional randomness.
-/

@[expose] public section

open scoped BigOperators

namespace Causalean.Stat.RandomGraph.PathOccupancy

/-- [The component](goal) of [a sample label](hyp:i) under [a relation](hyp:R)
contains all labels equivalent to it under the equivalence closure. -/
noncomputable def component {n : ℕ} (R : Fin n → Fin n → Prop) (i : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (Relation.EqvGen R i)

/-- [The component partition](goal) of [a relation on labels](hyp:R) is the
set of its distinct equivalence classes, each included once. -/
noncomputable def components {n : ℕ} (R : Fin n → Fin n → Prop) :
    Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.image (component R)

/-- [A relation and cell assignment](hyp:R,x) are [admissible for the coarse
count](goal), [M](hyp:M), when each edge joins equal or neighbouring cells
in the same coarse cell. -/
def Admissible {n K : ℕ} (M : ℕ) (x : Fin n → Fin K)
    (R : Fin n → Fin n → Prop) : Prop :=
  ∀ i j, R i j → Adjacent (x i) (x j) ∧
    (x i).val / (K / M) = (x j).val / (K / M)

/-- [Two subsets and an assignment](hyp:C,D,x) [share a coarse-pair
envelope](goal) for [coarse count M](hyp:M) when every cell in both subsets
lies in one consecutive paired coarse class. -/
def SameCoarsePair {n K : ℕ} (M : ℕ) (C D : Finset (Fin n))
    (x : Fin n → Fin K) : Prop :=
  ∃ p < M / 2, (∀ i ∈ C, pairClass K M (x i) = p) ∧
    (∀ j ∈ D, pairClass K M (x j) = p)

/-- [The single-component score](goal) of [a subset and marking](hyp:C,b)
is cardinality to the eighth times eight to the cardinality, when at least
two labels are marked, and zero otherwise. -/
noncomputable def singleWeight {n : ℕ} (C : Finset (Fin n))
    (b : Fin n → Bool) : ℝ := by
  classical
  exact (C.card : ℝ) ^ 8 * 8 ^ C.card * if 2 ≤ markCount C b then 1 else 0

/-- [The total single-component score](goal) for [a relation and marking](hyp:R,b)
is the sum of the two-mark single-component weights over its partition. -/
noncomputable def singleScore {n : ℕ} (R : Fin n → Fin n → Prop)
    (b : Fin n → Bool) : ℝ := ∑ C ∈ components R, singleWeight C b

/-- [The paired weight](goal) for [two subsets, cells, and marks](hyp:C,D,x,b)
at [coarse count M](hyp:M) is the product of their fourth-power exponential
weights if each size is at least two, each contains a mark, and they share
a coarse-pair envelope; otherwise it is zero. -/
noncomputable def pairWeight {n K : ℕ} (M : ℕ) (C D : Finset (Fin n))
    (x : Fin n → Fin K) (b : Fin n → Bool) : ℝ := by
  classical
  exact if 2 ≤ C.card ∧ 2 ≤ D.card ∧ 1 ≤ markCount C b ∧
      1 ≤ markCount D b ∧ SameCoarsePair M C D x then
    (C.card : ℝ) ^ 4 * 8 ^ C.card * (D.card : ℝ) ^ 4 * 8 ^ D.card else 0

/-- [The distinct-component paired score](goal) for [coarse count, relation,
cells, and marks](hyp:M,R,x,b) is half the ordered sum over distinct components
of size at least two with at least one mark each and a shared coarse pair. -/
noncomputable def pairedScore {n K : ℕ} (M : ℕ) (R : Fin n → Fin n → Prop)
    (x : Fin n → Fin K) (b : Fin n → Bool) : ℝ := by
  classical
  exact (1 / 2 : ℝ) * ∑ C ∈ components R,
    ∑ D ∈ (components R).erase C, pairWeight M C D x b

/-- [The equivalence classes of any relation](hyp:R) [are nonempty, cover
all sample labels, and are disjoint when distinct](goal). -/
theorem components_partition {n : ℕ} (R : Fin n → Fin n → Prop) :
    (∀ C ∈ components R, C.Nonempty) ∧
    (∀ i : Fin n, ∃ C ∈ components R, i ∈ C) ∧
    (∀ C ∈ components R, ∀ D ∈ components R, C ≠ D → Disjoint C D) := by
  classical
  have hmem : ∀ i j, j ∈ component R i ↔ Relation.EqvGen R i j := by
    intro i j
    simp [component]
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨i, (hmem i i).mpr (.refl i)⟩
  · intro i
    exact ⟨component R i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩,
      (hmem i i).mpr (.refl i)⟩
  · intro C hC D hD hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hD
    apply Finset.disjoint_left.mpr
    intro k hik hjk
    apply hne
    have hij : Relation.EqvGen R i j :=
      .trans i k j ((hmem i k).mp hik) (.symm j k ((hmem j k).mp hjk))
    ext l
    rw [hmem, hmem]
    exact ⟨fun hil => .trans j i l (.symm i j hij) hil,
      fun hjl => .trans i j l hij hjl⟩

/-- For [an admissible local relation](hyp:hR), [each component](hyp:hC)
has [connected occupied cells and lies in one coarse cell](goal), for
[the coarse count, cells, relation, and component](hyp:M,x,R,C). -/
theorem component_geometry {n K : ℕ} (M : ℕ) (x : Fin n → Fin K)
    (R : Fin n → Fin n → Prop) (hR : Admissible M x R)
    (C : Finset (Fin n)) (hC : C ∈ components R) :
    PathConnected (C.image x) ∧
      ∃ q, ∀ i ∈ C, (x i).val / (K / M) = q := by
  classical
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hC
  have hmem : ∀ i, i ∈ component R a ↔ Relation.EqvGen R a i := by
    intro i
    simp [component]
  let S : component R a → component R a → Prop := fun i j => R i j
  -- Lift closure paths to the class: each intermediate vertex is equivalent to a.
  have hlift : ∀ i j, Relation.EqvGen R i j →
      ∀ (hi : i ∈ component R a) (hj : j ∈ component R a),
        Relation.EqvGen S ⟨i, hi⟩ ⟨j, hj⟩ := by
    intro i j hij
    induction hij with
    | rel i j hij =>
        intro hi hj
        exact .rel _ _ hij
    | refl i =>
        intro hi hj
        exact .refl _
    | symm i j hij ih =>
        intro hj hi
        exact .symm _ _ (ih hi hj)
    | trans i j k hij hjk ihij ihjk =>
        intro hi hk
        have hj := (hmem j).mpr (.trans a i j ((hmem i).mp hi) hij)
        exact .trans _ _ _ (ihij hi hj) (ihjk hj hk)
  constructor
  · apply connected_image_of_local_relation (component R a) x
      ⟨a, (hmem a).mpr (.refl a)⟩ S
    · intro i j hij
      exact (hR i j hij).1
    · intro i j
      have hij : Relation.EqvGen R (i : Fin n) (j : Fin n) :=
        .trans (i : Fin n) a (j : Fin n) (.symm a i ((hmem i).mp i.property))
          ((hmem j).mp j.property)
      exact hlift i j hij i.property j.property
  · refine ⟨(x a).val / (K / M), ?_⟩
    intro i hi
    have heq : ∀ u v, Relation.EqvGen R u v →
        (x u).val / (K / M) = (x v).val / (K / M) := by
      intro u v huv
      induction huv with
      | rel u v huv => exact (hR u v huv).2
      | refl u => rfl
      | symm u v huv ih => exact ih.symm
      | trans u v w huv hvw ihuv ihvw => exact ihuv.trans ihvw
    exact (heq a i ((hmem i).mp hi)).symm

open Classical in
/-- For [admissible cells and relation](hyp:hR), [the single-component
score is bounded by the sum over all connected labelled subsets](goal), for
[the given coarse count, cells, relation, and marks](hyp:M,x,R,b).

This is pointwise, so the relation may depend arbitrarily on cells and marks.
-/
theorem singleScore_le_subsets {n K : ℕ} (M : ℕ) (x : Fin n → Fin K)
    (R : Fin n → Fin n → Prop) (b : Fin n → Bool) (hR : Admissible M x R) :
    singleScore R b ≤ ∑ C ∈ Finset.univ.powerset,
      if PathConnected (C.image x) then singleWeight C b else 0 := by
  have hn : ∀ C : Finset (Fin n), 0 ≤ singleWeight C b := by
    intro C
    unfold singleWeight
    positivity
  unfold singleScore
  calc
    _ = ∑ C ∈ components R,
        if PathConnected (C.image x) then singleWeight C b else 0 := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [if_pos (component_geometry M x R hR C hC).1]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (fun C _ => Finset.mem_powerset.mpr (Finset.subset_univ C)) (by
        intro C _ _
        split_ifs <;> first | exact hn C | exact le_rfl)

open Classical in
/-- For [an admissible relation](hyp:hR), [the distinct-component score is
bounded by half the sum over ordered disjoint connected labelled subsets](goal),
for [the coarse count, cells, relation, and marks](hyp:M,x,R,b).

Keep disjointness of labels, not occupied cells. Sizes at least two are retained
inside pairWeight, which makes the empty relation contribute zero.
-/
theorem pairedScore_le_subsets {n K : ℕ} (M : ℕ) (x : Fin n → Fin K)
    (R : Fin n → Fin n → Prop) (b : Fin n → Bool) (hR : Admissible M x R) :
    pairedScore M R x b ≤ (1 / 2 : ℝ) *
      ∑ C ∈ Finset.univ.powerset, ∑ D ∈ Finset.univ.powerset,
        if Disjoint C D ∧ PathConnected (C.image x) ∧ PathConnected (D.image x)
        then pairWeight M C D x b else 0 := by
  let f : Finset (Fin n) → Finset (Fin n) → ℝ := fun C D =>
    if Disjoint C D ∧ PathConnected (C.image x) ∧ PathConnected (D.image x)
    then pairWeight M C D x b else 0
  have hn : ∀ C D, 0 ≤ f C D := by
    intro C D
    dsimp [f]
    split_ifs
    · unfold pairWeight
      split_ifs <;> positivity
    · exact le_rfl
  have hsub : components R ⊆ Finset.univ.powerset := by
    intro C _
    exact Finset.mem_powerset.mpr (Finset.subset_univ C)
  unfold pairedScore
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ = ∑ C ∈ components R, ∑ D ∈ (components R).erase C, f C D := by
      apply Finset.sum_congr rfl
      intro C hC
      apply Finset.sum_congr rfl
      intro D hD
      obtain ⟨hne, hD⟩ := Finset.mem_erase.mp hD
      have hdis := (components_partition R).2.2 C hC D hD hne.symm
      dsimp [f]
      rw [if_pos ⟨hdis, (component_geometry M x R hR C hC).1,
        (component_geometry M x R hR D hD).1⟩]
    _ ≤ ∑ C ∈ components R, ∑ D ∈ Finset.univ.powerset, f C D := by
      apply Finset.sum_le_sum
      intro C _
      exact Finset.sum_le_sum_of_subset_of_nonneg
        ((Finset.erase_subset C (components R)).trans hsub)
        (fun D _ _ => hn C D)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro C _ _
      exact Finset.sum_nonneg (fun D _ => hn C D))

end Causalean.Stat.RandomGraph.PathOccupancy

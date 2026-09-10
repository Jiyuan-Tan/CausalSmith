import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.Asymptotics
import Causalean.Experimentation.DesignBased.Designs.Coin
import Causalean.Experimentation.DesignBased.Product
import Causalean.Experimentation.DesignBased.ProductVariance
import Causalean.Experimentation.DesignBased.FiniteDesignMeasure

open scoped BigOperators
open Finset

/-!
# Product Rademacher schedule priors and observation channel

This file realizes the common-sign and independent-arm product priors as finite
product designs, embeds their signs into additive schedules, and records the
one-realization observation channel.
-/

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased

-- @env: S4
variable (n M G G1 : ℕ)

/-- Convert a fair coin to a Rademacher sign. -/
def rademacherSign (b : Bool) : ℝ := if b then 1 else -1

/-- Common-arm product Rademacher prior. -/
noncomputable def priorSame (n : ℕ) : FiniteDesign (Fin n → Bool) :=
  prodDesign (fun _ : Fin n => coinDesign (1 / 2) (by norm_num) (by norm_num))
  -- @realizes \mathbb H_n^{\mathrm{same}}(independent common-arm Rademacher signs)

/-- Independent-arm product Rademacher prior. -/
noncomputable def priorIndependent (n : ℕ) : FiniteDesign (Fin n × Bool → Bool) :=
  prodDesign (fun _ : Fin n × Bool => coinDesign (1 / 2) (by norm_num) (by norm_num))
  -- @realizes \mathbb H_n^{\mathrm{ind}}(independent unit-by-arm Rademacher signs)

/-- Additive schedule induced by common signs. -/
def samePriorSchedule (u : Fin n → Bool) : PotentialOutcome n M :=
  fun _ i _ => rademacherSign (u i.1)

/-- Additive schedule induced by independent arm-specific signs. -/
def independentPriorSchedule (u : Fin n × Bool → Bool) : PotentialOutcome n M :=
  fun _ i z => rademacherSign (u (i.1, z))

/-- One observed realization: partition, treatment allocation, and observed outcomes
for every member of every realized group. -/
structure ObservedData (n M G G1 : ℕ) where
  partition : PartitionTuple n M G
  treatment : TreatmentSpace G G1
  outcomes : (g : Fin G) → {i : Fin n // i ∈ (partition.1 g).1} → ℝ
  -- @realizes \mathcal O_n(partition assignment and observed member outcomes)

/-- The one-realization observation channel. -/
def observe (Y : PotentialOutcome n M)
    (w : PartitionTuple n M G × TreatmentSpace G G1) : ObservedData n M G G1 where
  partition := w.1
  treatment := w.2
  outcomes := fun g i => Y (w.1.1 g) i (g ∈ w.2.1)

/-- A generic statistic of one realization. -/
abbrev VarianceStatistic (n M G G1 : ℕ) := ObservedData n M G G1 → ℝ
  -- @realizes \widehat S_n(arbitrary one-realization statistic)

-- @node: selectSwapEquiv
/-- For [the stated inputs](hyp:z), [select swap equiv](goal) is defined by the formula below. -/
def selectSwapEquiv {ι : Type*} [DecidableEq ι] (z : ι → Bool) :
    (ι × Bool → Bool) ≃ (ι → Bool) × (ι → Bool) where
  toFun u := (fun i => u (i, z i), fun i => u (i, !z i))
  invFun w := fun q => if q.2 = z q.1 then w.1 q.1 else w.2 q.1
  left_inv u := by
    funext q
    rcases q with ⟨i, b⟩
    cases b <;> cases hz : z i <;> simp [hz]
  right_inv w := by
    rcases w with ⟨v, t⟩
    apply Prod.ext <;> funext i
    · simp
    · have hne : !z i ≠ z i := by cases z i <;> simp
      simp

-- @node: fairCoinWeight
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:u), [the fair coin weight result holds](goal). -/
lemma fairCoinWeight {ι : Type*} [Fintype ι] (u : ι → Bool) :
    (∏ i, if u i = true then (1 : ℝ) / 2 else 1 - 1 / 2) =
      ((1 : ℝ) / 2) ^ Fintype.card ι := by
  calc
    (∏ i, if u i = true then (1 : ℝ) / 2 else 1 - 1 / 2) =
        ∏ _i : ι, ((1 : ℝ) / 2) := by
      apply Finset.prod_congr rfl
      intro i _
      cases u i <;> norm_num
    _ = ((1 : ℝ) / 2) ^ Fintype.card ι := by simp

-- @node: priorIndependent_E_select
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,z,f), [the stated expectation identity holds](goal). -/
lemma priorIndependent_E_select {n : ℕ} (z : Fin n → Bool)
    (f : (Fin n → Bool) → ℝ) :
    (priorIndependent n).E (fun u => f (fun i => u (i, z i))) =
      (priorSame n).E f := by
  classical
  unfold priorIndependent priorSame FiniteDesign.E prodDesign
  simp only [coinDesign, cond_eq_ite]
  simp_rw [fairCoinWeight]
  let e := selectSwapEquiv z
  calc
    (∑ x : (Fin n × Bool → Bool), (1 / 2 : ℝ) ^ Fintype.card (Fin n × Bool) *
        f (fun i => x (i, z i))) =
        ∑ y : (Fin n → Bool) × (Fin n → Bool),
          (1 / 2 : ℝ) ^ Fintype.card (Fin n × Bool) * f y.1 := by
      apply Fintype.sum_equiv e
        (fun x : Fin n × Bool → Bool =>
          (1 / 2 : ℝ) ^ Fintype.card (Fin n × Bool) * f (fun i => x (i, z i)))
        (fun y : (Fin n → Bool) × (Fin n → Bool) =>
          (1 / 2 : ℝ) ^ Fintype.card (Fin n × Bool) * f y.1)
      intro x
      simp [e, selectSwapEquiv]
    _ = ∑ x, (1 / 2 : ℝ) ^ Fintype.card (Fin n) * f x := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
        Fintype.card_fun, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_mul, pow_two]
      have hpow : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n * f x) =
            ((2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) * ((1 / 2 : ℝ) ^ n * f x) := by ring
        _ = (1 / 2 : ℝ) ^ n * f x := by rw [hpow, one_mul]

-- @node: observedArmSelector
/-- For [the stated inputs](hyp:n,M,G,G1,w,i), [observed arm selector](goal) is defined by the formula below. -/
def observedArmSelector {n M G G1 : ℕ}
    (w : PartitionTuple n M G × TreatmentSpace G G1) (i : Fin n) : Bool :=
  decide (∃ g : Fin G, i ∈ (w.1.1 g).1 ∧ g ∈ w.2.1)

-- @node: observedArmSelector_of_mem
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,w,g,i,hi), [the observed arm selector of mem result holds](goal). -/
lemma observedArmSelector_of_mem {n M G G1 : ℕ}
    (w : PartitionTuple n M G × TreatmentSpace G G1) (g : Fin G) (i : Fin n)
    (hi : i ∈ (w.1.1 g).1) : observedArmSelector w i = decide (g ∈ w.2.1) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [observedArmSelector, decide_eq_true_eq]
  constructor
  · rintro ⟨g', hi', hg'⟩
    by_cases hgg : g' = g
    · exact hgg ▸ hg'
    · exact False.elim (Finset.disjoint_left.mp (w.1.2 g' g hgg) hi' hi)
  · intro hg
    exact ⟨g, hi, hg⟩

-- @node: observe_independent_eq_same_selected
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,w,u), [the stated equality holds](goal). -/
lemma observe_independent_eq_same_selected {n M G G1 : ℕ}
    (w : PartitionTuple n M G × TreatmentSpace G G1)
    (u : Fin n × Bool → Bool) :
    observe n M G G1 (independentPriorSchedule n M u) w =
      observe n M G G1
        (samePriorSchedule n M (fun i => u (i, observedArmSelector w i))) w := by
  rcases w with ⟨T, Z⟩
  unfold observe
  congr
  funext g i
  change rademacherSign (u (i.1, decide (g ∈ Z.1))) =
    rademacherSign (u (i.1, observedArmSelector (T, Z) i.1))
  rw [observedArmSelector_of_mem (T, Z) g i.1 i.2]

-- @node: finiteDesign_E_swap
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,E,f), [the stated expectation identity holds](goal). -/
lemma finiteDesign_E_swap {α β : Type*} [Fintype α] [Fintype β]
    (D : FiniteDesign α) (E : FiniteDesign β) (f : α → β → ℝ) :
    D.E (fun a => E.E (f a)) = E.E (fun b => D.E (fun a => f a b)) := by
  unfold FiniteDesign.E
  calc
    (∑ a, D.p a * ∑ b, E.p b * f a b) =
        ∑ a, ∑ b, D.p a * (E.p b * f a b) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    _ = ∑ b, ∑ a, E.p b * (D.p a * f a b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ b, E.p b * ∑ a, D.p a * f a b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

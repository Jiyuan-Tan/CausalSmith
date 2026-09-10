import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.OrbitLikelihood
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Sym.Card

/-! Orbit cardinalities and contingency-table counting identities. -/

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

open Finset

variable {K n : ℕ}

-- @node: finCountEquivNatCount
/-- Bounded coordinates summing to `n` are equivalent to natural coordinates summing to `n`. -/
noncomputable def finCountEquivNatCount (α : Type*) [Fintype α] (n : ℕ) :
    {f : α → Fin (n + 1) // ∑ a, (f a : ℕ) = n} ≃
      {f : α → ℕ // ∑ a, f a = n} where
  toFun f := ⟨fun a => f.1 a, f.2⟩
  invFun f := ⟨fun a => ⟨f.1 a, by
    rw [Nat.lt_succ_iff]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a) |>.trans_eq f.2⟩,
    f.2⟩
  left_inv f := by ext a; rfl
  right_inv f := by apply Subtype.ext; funext a; rfl

-- @node: natCountEquivAntidiag
/-- Natural count vectors of total `n` are the full finite antidiagonal. -/
noncomputable def natCountEquivAntidiag (α : Type*) [Fintype α] [DecidableEq α] (n : ℕ) :
    {f : α → ℕ // ∑ a, f a = n} ≃
      ↥(Finset.piAntidiag (Finset.univ : Finset α) n) where
  toFun f := ⟨f.1, by simp [Finset.mem_piAntidiag, f.2]⟩
  invFun f := ⟨f.1, (Finset.mem_piAntidiag.mp f.2).1⟩
  left_inv f := by apply Subtype.ext; funext a; rfl
  right_inv f := by ext a; rfl

-- @node: boundedCountVectorCardinality
/-- [the stated side condition holds](hyp:hα), [Stars and bars for bounded coordinates whose fixed total makes the bounds automatic.](goal) -/
lemma boundedCountVectorCardinality (α : Type*) [Fintype α] [DecidableEq α]
    (hα : 0 < Fintype.card α) (n : ℕ) :
    Fintype.card {f : α → Fin (n + 1) // ∑ a, (f a : ℕ) = n} =
      Nat.choose (n + Fintype.card α - 1) (Fintype.card α - 1) := by
  rw [Fintype.card_congr ((finCountEquivNatCount α n).trans
    (natCountEquivAntidiag α n))]
  rw [Fintype.card_coe]
  let e : Sym α n ↪ (α → ℕ) :=
    ⟨fun m a => m.1.count a, Multiset.count_injective.comp Sym.coe_injective⟩
  have hmap : ((Finset.univ : Finset α).sym n).map e =
      Finset.piAntidiag (Finset.univ : Finset α) n :=
    Finset.map_sym_eq_piAntidiag Finset.univ n
  calc
    #(Finset.piAntidiag (Finset.univ : Finset α) n) =
        #(((Finset.univ : Finset α).sym n).map e) := congrArg Finset.card hmap.symm
    _ = #((Finset.univ : Finset α).sym n) := Finset.card_map e
    _ = #(Finset.univ : Finset (Sym α n)) := by simp
    _ = Fintype.card (Sym α n) := Finset.card_univ
    _ = Nat.choose (Fintype.card α + n - 1) n := Sym.card_sym_eq_choose n
    _ = Nat.choose (n + Fintype.card α - 1) (Fintype.card α - 1) := by
      have hleft : Fintype.card α + n - 1 = n + (Fintype.card α - 1) := by omega
      have hright : n + Fintype.card α - 1 = n + (Fintype.card α - 1) := by omega
      rw [hleft, hright]
      exact Nat.choose_symm_add

/-- Allocation counts together with compatible success counts are equivalent to
counts of arm/outcome pairs. -/
-- @node: allocationObservationEquivNatCount
noncomputable def allocationObservationEquivNatCount :
    (Σ r : AllocVec K n, ObsVec r) ≃
      {f : Arm K × Bool → ℕ // ∑ q, f q = n} where
  toFun q := ⟨fun ab => if ab.2 then q.2.1 ab.1 else q.1.1 ab.1 - q.2.1 ab.1, by
    rw [Fintype.sum_prod_type]
    calc
      ∑ a, ((q.2.1 a : ℕ) + ((q.1.1 a : ℕ) - (q.2.1 a : ℕ))) =
          ∑ a, (q.1.1 a : ℕ) := by
        apply Finset.sum_congr rfl
        intro a _
        exact Nat.add_sub_of_le (q.2.2 a)
      _ = n := q.1.2⟩
  invFun f := by
    let r : AllocVec K n :=
      ⟨fun a => ⟨f.1 (a, true) + f.1 (a, false), by
        rw [Nat.lt_succ_iff]
        calc
          f.1 (a, true) + f.1 (a, false) = ∑ b : Bool, f.1 (a, b) := by simp
          _ ≤ ∑ a, ∑ b : Bool, f.1 (a, b) := by
            have hnonneg : ∀ a : Arm K, 0 ≤ ∑ b : Bool, f.1 (a, b) :=
              fun a => Finset.sum_nonneg fun _ _ => Nat.zero_le _
            exact Finset.single_le_sum (fun a _ => hnonneg a) (Finset.mem_univ a)
          _ = ∑ q, f.1 q := by rw [Fintype.sum_prod_type]
          _ = n := f.2⟩,
        by
          change (∑ a, (f.1 (a, true) + f.1 (a, false))) = n
          calc
            _ = ∑ a, ∑ b : Bool, f.1 (a, b) := by
              apply Finset.sum_congr rfl
              intro a _
              simp
            _ = ∑ q, f.1 q := by rw [Fintype.sum_prod_type]
            _ = n := f.2⟩
    exact ⟨r, ⟨fun a => ⟨f.1 (a, true), by
      rw [Nat.lt_succ_iff]
      exact (Nat.le_add_right _ _).trans (Fin.is_le (r.1 a))⟩,
      fun a => Nat.le_add_right _ _⟩⟩
  left_inv q := by
    apply Sigma.ext
    · apply Subtype.ext
      funext a
      apply Fin.ext
      simp only
      exact Nat.add_sub_of_le (q.2.2 a)
    · apply (Subtype.heq_iff_coe_eq (fun x => by
        constructor <;> intro hx a
        · simpa [Nat.add_sub_of_le (q.2.2 a)] using hx a
        · simpa [Nat.add_sub_of_le (q.2.2 a)] using hx a)).2
      rfl
  right_inv f := by
    apply Subtype.ext
    funext ab
    cases ab with
    | mk a b => cases b <;> simp

/-- [there are at least two treatment arms](hyp:hK), [The allocation/observation orbit pairs have the stars-and-bars cardinality for `2K` arm/outcome cells.](goal) -/
-- @node: allocation_observation_cardinality
lemma allocation_observation_cardinality (hK : AdmissibleArmCount K) :
    (∑ r : AllocVec K n, Fintype.card (ObsVec r)) =
      Nat.choose (n + 2 * K - 1) (2 * K - 1) := by
  letI : Fintype {f : Arm K × Bool → ℕ // ∑ q, f q = n} :=
    Fintype.ofEquiv ↥(Finset.piAntidiag (Finset.univ : Finset (Arm K × Bool)) n)
      (natCountEquivAntidiag (Arm K × Bool) n).symm
  rw [← Fintype.card_sigma]
  rw [Fintype.card_congr (allocationObservationEquivNatCount (K := K) (n := n))]
  rw [Fintype.card_congr (natCountEquivAntidiag (Arm K × Bool) n)]
  rw [Fintype.card_coe]
  let e : Sym (Arm K × Bool) n ↪ ((Arm K × Bool) → ℕ) :=
    ⟨fun m a => m.1.count a, Multiset.count_injective.comp Sym.coe_injective⟩
  have hmap : ((Finset.univ : Finset (Arm K × Bool)).sym n).map e =
      Finset.piAntidiag (Finset.univ : Finset (Arm K × Bool)) n :=
    Finset.map_sym_eq_piAntidiag Finset.univ n
  calc
    #(Finset.piAntidiag (Finset.univ : Finset (Arm K × Bool)) n) =
        #(((Finset.univ : Finset (Arm K × Bool)).sym n).map e) :=
      congrArg Finset.card hmap.symm
    _ = #((Finset.univ : Finset (Arm K × Bool)).sym n) := Finset.card_map e
    _ = #(Finset.univ : Finset (Sym (Arm K × Bool) n)) := by simp
    _ = Fintype.card (Sym (Arm K × Bool) n) := Finset.card_univ
    _ = Nat.choose (Fintype.card (Arm K × Bool) + n - 1) n := Sym.card_sym_eq_choose n
    _ = Nat.choose (n + 2 * K - 1) (2 * K - 1) := by
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      have hKpos : 0 < K := by unfold AdmissibleArmCount at hK; omega
      have hleft : K * 2 + n - 1 = n + (2 * K - 1) := by omega
      have hright : n + 2 * K - 1 = n + (2 * K - 1) := by omega
      rw [hleft, hright]
      exact Nat.choose_symm_add

/-- [the response count cardinality property holds](goal). -/
lemma response_count_cardinality :
    Fintype.card (CountVec K n) = Nat.choose (n + 2 ^ K - 1) (2 ^ K - 1) := by
  unfold CountVec RespType Arm
  simpa using boundedCountVectorCardinality (Fin K → Bool) (by simp) n

/-- [there are at least two treatment arms](hyp:hK), [the allocation count cardinality property holds](goal). -/
lemma allocation_count_cardinality (hK : AdmissibleArmCount K) :
    Fintype.card (AllocVec K n) = Nat.choose (n + K - 1) (K - 1) := by
  have hKpos : 0 < K := by
    unfold AdmissibleArmCount at hK
    omega
  unfold AllocVec Arm
  simpa using boundedCountVectorCardinality (Fin K) (by simpa using hKpos) n

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmSchedulePrior
import Mathlib.Data.Nat.Choose.Sum

/-!
Exact transformed-score fibers for the canonical two-arm schedule prior.

This module proves the binomial statistic law, its normalized boundary cases,
and the state-independent uniform conditional score kernel used by the
Rao--Blackwell assembly.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

-- @node: twoArmScoreSupportEquiv
/-- The two arm score support equiv property holds. -/
noncomputable def twoArmScoreSupportEquiv (n x : ℕ) :
    {s : Unit n → Bool // (Finset.univ.filter fun i ↦ s i).card = x} ≃
      {P : Finset (Unit n) // P ∈ Finset.univ.powersetCard x} where
  toFun s := ⟨Finset.univ.filter fun i ↦ s.1 i, by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.filter_subset _ _, s.2⟩⟩
  invFun P := ⟨fun i ↦ i ∈ P.1, by
    change (Finset.univ.filter fun i ↦ decide (i ∈ P.1) = true).card = x
    rw [show (Finset.univ.filter fun i ↦ decide (i ∈ P.1) = true) = P.1 by
      ext i
      simp]
    exact (Finset.mem_powersetCard.mp P.2).2⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    simp
  right_inv P := by
    apply Subtype.ext
    ext i
    simp

-- @node: twoArmScoreSupport_card
/-- [the two arm score support cardinality property holds](goal). -/
lemma twoArmScoreSupport_card (n x : ℕ) :
    Fintype.card {s : Unit n → Bool //
      (Finset.univ.filter fun i ↦ s i).card = x} = Nat.choose n x := by
  classical
  rw [Fintype.card_congr (twoArmScoreSupportEquiv n x)]
  simp

-- @node: twoArmXMass_eq_sum_scoreMass
/-- [the two arm xmass equals sums score mass](goal). -/
lemma twoArmXMass_eq_sum_scoreMass {n : ℕ} (θ : EffectTriple n)
    (A : Assign 2 n) (x : Fin (n + 1)) :
    (∑ z : Schedule 2 n,
      if twoArmX z A = x then canonicalScheduleKernel θ z else 0) =
    ∑ s : Unit n → Bool,
      if (Finset.univ.filter fun i ↦ s i).card = (x : ℕ) then
        ∑ z : Schedule 2 n,
          if (fun i ↦ twoArmS z A i) = s then canonicalScheduleKernel θ z else 0
      else 0 := by
  classical
  rw [show (∑ s : Unit n → Bool,
      if (Finset.univ.filter fun i ↦ s i).card = (x : ℕ) then
        ∑ z : Schedule 2 n,
          if (fun i ↦ twoArmS z A i) = s then canonicalScheduleKernel θ z else 0
      else 0) =
      ∑ s : Unit n → Bool, ∑ z : Schedule 2 n,
        if (Finset.univ.filter fun i ↦ s i).card = (x : ℕ) ∧
            (fun i ↦ twoArmS z A i) = s then canonicalScheduleKernel θ z else 0 by
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : (Finset.univ.filter fun i ↦ s i).card = (x : ℕ)
    · simp [hs]
    · simp [hs]]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  let sz := fun i ↦ twoArmS z A i
  have hx : twoArmX z A = x ↔
      (Finset.univ.filter fun i ↦ sz i).card = (x : ℕ) := by
    rw [Fin.ext_iff]
    exact Iff.rfl
  by_cases hzx : twoArmX z A = x
  · rw [if_pos hzx]
    have hc : (Finset.univ.filter fun i ↦ sz i).card = (x : ℕ) := hx.mp hzx
    rw [Finset.sum_eq_single sz]
    · simp [sz, hc]
    · intro s _ hs
      have hne : (fun i ↦ twoArmS z A i) ≠ s := by
        intro h
        exact hs h.symm
      simp [hne]
    · simp
  · rw [if_neg hzx]
    have hc : (Finset.univ.filter fun i ↦ sz i).card ≠ (x : ℕ) := by
      exact fun h ↦ hzx (hx.mpr h)
    symm
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s = sz
    · subst s
      simp [hc]
    · have hne : (fun i ↦ twoArmS z A i) ≠ s := by
        intro h
        exact hs h.symm
      simp [hne]

-- @node: twoArmCanonicalScore_mass
/-- [the two arm canonical score mass property holds](goal). -/
lemma twoArmCanonicalScore_mass {n : ℕ} (θ : EffectTriple n)
    (A : Assign 2 n) (s : Unit n → Bool) :
    (∑ z : Schedule 2 n,
      if (fun i ↦ twoArmS z A i) = s then canonicalScheduleKernel θ z else 0) =
      (Fintype.card (TwoArmScoreScheduleFiber θ A s) : ℝ) /
        ((Nat.factorial n : ℝ) /
          (Nat.factorial (θ.1.1 : ℕ) * Nat.factorial (θ.1.2.1 : ℕ) *
            Nat.factorial (θ.1.2.2 : ℕ)) * 2 ^ (θ.1.2.2 : ℕ)) := by
  classical
  rw [← twoArmCanonicalScoreFiber_mass (θ := θ) A s]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hs : (fun i ↦ twoArmS z A i) = s
  · by_cases ht : hasEffectTriple θ z
    · simp [hs, ht]
    · simp [hs, ht, canonicalScheduleKernel]
  · simp [hs]

-- @node: twoArmCanonicalScore_mass_eq_binomial
/-- [the stated probability condition holds](hyp:hp), [the observed count satisfies its stated condition](hyp:hx), [the two arm canonical score mass equals binomial](goal). -/
lemma twoArmCanonicalScore_mass_eq_binomial {n : ℕ} (θ : EffectTriple n)
    (A : Assign 2 n) (s : Unit n → Bool)
    (hp : (θ.1.1 : ℕ) ≤ (Finset.univ.filter fun i ↦ s i).card)
    (hx : (Finset.univ.filter fun i ↦ s i).card ≤
      (θ.1.1 : ℕ) + (θ.1.2.2 : ℕ)) :
    (∑ z : Schedule 2 n,
      if (fun i ↦ twoArmS z A i) = s then canonicalScheduleKernel θ z else 0) =
      binomialHalf (θ.1.2.2 : ℕ)
          ((Finset.univ.filter fun i ↦ s i).card - (θ.1.1 : ℕ)) /
        Nat.choose n (Finset.univ.filter fun i ↦ s i).card := by
  classical
  rw [← twoArmCanonicalScoreFiber_mass_eq_binomial (θ := θ) A s hp hx]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hs : (fun i ↦ twoArmS z A i) = s
  · by_cases ht : hasEffectTriple θ z
    · simp [hs, ht]
    · simp [hs, ht, canonicalScheduleKernel]
  · simp [hs]

-- @node: twoArmXMass_eq_binomial_of_support
/-- [the stated probability condition holds](hyp:hp), [the observed count satisfies its stated condition](hyp:hx), [the two arm xmass equals binomial when support](goal). -/
lemma twoArmXMass_eq_binomial_of_support {n : ℕ} (θ : EffectTriple n)
    (A : Assign 2 n) (x : Fin (n + 1))
    (hp : (θ.1.1 : ℕ) ≤ (x : ℕ))
    (hx : (x : ℕ) ≤ (θ.1.1 : ℕ) + (θ.1.2.2 : ℕ)) :
    (∑ z : Schedule 2 n,
      if twoArmX z A = x then canonicalScheduleKernel θ z else 0) =
      binomialHalf (θ.1.2.2 : ℕ) ((x : ℕ) - (θ.1.1 : ℕ)) := by
  classical
  rw [twoArmXMass_eq_sum_scoreMass]
  let b := binomialHalf (θ.1.2.2 : ℕ) ((x : ℕ) - (θ.1.1 : ℕ))
  have hsum : (∑ s : Unit n → Bool,
      if (Finset.univ.filter fun i ↦ s i).card = (x : ℕ) then
        ∑ z : Schedule 2 n,
          if (fun i ↦ twoArmS z A i) = s then canonicalScheduleKernel θ z else 0
      else 0) =
      ∑ s : Unit n → Bool,
        if (Finset.univ.filter fun i ↦ s i).card = (x : ℕ) then
          b / Nat.choose n (x : ℕ) else 0 := by
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : (Finset.univ.filter fun i ↦ s i).card = (x : ℕ)
    · simp only [hs, if_pos]
      rw [twoArmCanonicalScore_mass_eq_binomial θ A s]
      · simp [b, hs]
      · simpa [hs] using hp
      · simpa [hs] using hx
    · simp [hs]
  rw [hsum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.card_subtype]
  rw [twoArmScoreSupport_card]
  have hxn : (x : ℕ) ≤ n := Nat.le_of_lt_succ x.isLt
  have hchoose : (Nat.choose n (x : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hxn).ne'
  dsimp [b]
  field_simp

-- @node: twoArmCanonicalScore_mass_eq_zero_of_lt
/-- [the observed count satisfies its stated condition](hyp:hx), [the two arm canonical score mass equals zero when is less than](goal). -/
lemma twoArmCanonicalScore_mass_eq_zero_of_lt {n : ℕ} (θ : EffectTriple n)
    (A : Assign 2 n) (s : Unit n → Bool)
    (hx : (Finset.univ.filter fun i ↦ s i).card < (θ.1.1 : ℕ)) :
    (∑ z : Schedule 2 n,
      if (fun i ↦ twoArmS z A i) = s then canonicalScheduleKernel θ z else 0) = 0 := by
  rw [twoArmCanonicalScore_mass, twoArmScoreScheduleFiber_card]
  rw [Nat.choose_eq_zero_of_lt hx]
  simp

-- @node: twoArmCanonicalScore_mass_eq_zero_of_gt
/-- [the observed count satisfies its stated condition](hyp:hx), [the two arm canonical score mass equals zero when is greater than](goal). -/
lemma twoArmCanonicalScore_mass_eq_zero_of_gt {n : ℕ} (θ : EffectTriple n)
    (A : Assign 2 n) (s : Unit n → Bool)
    (hx : (θ.1.1 : ℕ) + (θ.1.2.2 : ℕ) <
      (Finset.univ.filter fun i ↦ s i).card) :
    (∑ z : Schedule 2 n,
      if (fun i ↦ twoArmS z A i) = s then canonicalScheduleKernel θ z else 0) = 0 := by
  have htrue : (Finset.univ.filter fun i ↦ s i).card ≤ n := by
    simpa using Finset.card_le_card
      (Finset.filter_subset (fun i ↦ s i) Finset.univ)
  have hfalse : (Finset.univ.filter fun i ↦ !(s i)).card =
      n - (Finset.univ.filter fun i ↦ s i).card := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Unit n))) (p := fun i ↦ s i)
    simp only [Finset.card_univ, Fintype.card_fin] at hpart
    have heq : (Finset.univ.filter fun i ↦ !(s i)) =
        Finset.univ.filter fun i ↦ ¬ s i := by
      ext i
      cases hs : s i <;> simp [hs]
    rw [heq]
    omega
  have hm : n - (Finset.univ.filter fun i ↦ s i).card < (θ.1.2.1 : ℕ) := by
    have ht := θ.2
    omega
  rw [twoArmCanonicalScore_mass, twoArmScoreScheduleFiber_card, hfalse]
  rw [Nat.choose_eq_zero_of_lt hm]
  simp

-- @node: twoArmXMass_eq_zero_of_outside
/-- [the stated side condition holds](hyp:hout), [the two arm xmass equals zero when outside](goal). -/
lemma twoArmXMass_eq_zero_of_outside {n : ℕ} (θ : EffectTriple n)
    (A : Assign 2 n) (x : Fin (n + 1))
    (hout : (x : ℕ) < (θ.1.1 : ℕ) ∨
      (θ.1.1 : ℕ) + (θ.1.2.2 : ℕ) < (x : ℕ)) :
    (∑ z : Schedule 2 n,
      if twoArmX z A = x then canonicalScheduleKernel θ z else 0) = 0 := by
  classical
  rw [twoArmXMass_eq_sum_scoreMass]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : (Finset.univ.filter fun i ↦ s i).card = (x : ℕ)
  · rw [if_pos hs]
    rcases hout with hout | hout
    · exact twoArmCanonicalScore_mass_eq_zero_of_lt θ A s (by omega)
    · exact twoArmCanonicalScore_mass_eq_zero_of_gt θ A s (by omega)
  · simp [hs]

-- @node: twoArmXMass_eq_binomial_sum
/-- [the two arm xmass equals binomial sums](goal). -/
lemma twoArmXMass_eq_binomial_sum {n : ℕ} (θ : EffectTriple n)
    (A : Assign 2 n) (x : Fin (n + 1)) :
    (∑ z : Schedule 2 n,
      if twoArmX z A = x then canonicalScheduleKernel θ z else 0) =
      ∑ k ∈ Finset.range ((θ.1.2.2 : ℕ) + 1),
        if (x : ℕ) = (θ.1.1 : ℕ) + k then
          binomialHalf (θ.1.2.2 : ℕ) k else 0 := by
  classical
  by_cases hp : (θ.1.1 : ℕ) ≤ (x : ℕ)
  · by_cases hx : (x : ℕ) ≤ (θ.1.1 : ℕ) + (θ.1.2.2 : ℕ)
    · rw [twoArmXMass_eq_binomial_of_support θ A x hp hx]
      rw [Finset.sum_eq_single ((x : ℕ) - (θ.1.1 : ℕ))]
      · have heq : (x : ℕ) = (θ.1.1 : ℕ) + ((x : ℕ) - (θ.1.1 : ℕ)) := by omega
        rw [if_pos heq]
      · intro k hk hne
        have hkne : (x : ℕ) ≠ (θ.1.1 : ℕ) + k := by
          intro h
          apply hne
          omega
        simp [hkne]
      · intro hnot
        exfalso
        apply hnot
        simp only [Finset.mem_range]
        omega
    · have hout : (θ.1.1 : ℕ) + (θ.1.2.2 : ℕ) < (x : ℕ) := by omega
      rw [twoArmXMass_eq_zero_of_outside θ A x (Or.inr hout)]
      symm
      apply Finset.sum_eq_zero
      intro k hk
      have hklt : k ≤ (θ.1.2.2 : ℕ) := by
        simp only [Finset.mem_range] at hk
        omega
      have hne : (x : ℕ) ≠ (θ.1.1 : ℕ) + k := by omega
      simp [hne]
  · have hout : (x : ℕ) < (θ.1.1 : ℕ) := by omega
    rw [twoArmXMass_eq_zero_of_outside θ A x (Or.inl hout)]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hne : (x : ℕ) ≠ (θ.1.1 : ℕ) + k := by omega
    simp [hne]

-- @node: canonicalScheduleKernel_sum
/-- [the canonical schedule kernel sums](goal). -/
lemma canonicalScheduleKernel_sum {n : ℕ} (θ : EffectTriple n) :
    ∑ z : Schedule 2 n, canonicalScheduleKernel θ z = 1 := by
  classical
  let A : Assign 2 n := fun _ ↦ 0
  rw [show (∑ z : Schedule 2 n, canonicalScheduleKernel θ z) =
      ∑ x : Fin (n + 1), ∑ z : Schedule 2 n,
        if twoArmX z A = x then canonicalScheduleKernel θ z else 0 by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.sum_eq_single (twoArmX z A)]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp]
  simp_rw [twoArmXMass_eq_binomial_sum]
  rw [Finset.sum_comm]
  have hkbound (k : ℕ) (hk : k ∈ Finset.range ((θ.1.2.2 : ℕ) + 1)) :
      (θ.1.1 : ℕ) + k < n + 1 := by
    have ht := θ.2
    simp only [Finset.mem_range] at hk
    omega
  rw [show (∑ k ∈ Finset.range ((θ.1.2.2 : ℕ) + 1),
      ∑ x : Fin (n + 1),
        if (x : ℕ) = (θ.1.1 : ℕ) + k then binomialHalf (θ.1.2.2 : ℕ) k else 0) =
      ∑ k ∈ Finset.range ((θ.1.2.2 : ℕ) + 1),
        binomialHalf (θ.1.2.2 : ℕ) k by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_eq_single ⟨(θ.1.1 : ℕ) + k, hkbound k hk⟩]
    · simp
    · intro x _ hx
      have hne : (x : ℕ) ≠ (θ.1.1 : ℕ) + k := by
        intro h
        apply hx
        exact Fin.ext h
      simp [hne]
    · simp]
  unfold binomialHalf
  rw [← Finset.sum_div]
  have hchoose :
      (∑ i ∈ Finset.range ((θ.1.2.2 : ℕ) + 1),
        (Nat.choose (θ.1.2.2 : ℕ) i : ℝ)) = (2 ^ (θ.1.2.2 : ℕ) : ℕ) := by
    exact_mod_cast Nat.sum_range_choose (θ.1.2.2 : ℕ)
  rw [hchoose]
  norm_num

-- @node: twoArmCanonicalConditionalScore_mass
/-- [the stated side condition holds](hyp:hsx), [the two arm canonical conditional score mass property holds](goal). -/
lemma twoArmCanonicalConditionalScore_mass {n : ℕ} (θ : EffectTriple n)
    (A : Assign 2 n) (x : Fin (n + 1)) (s : Unit n → Bool)
    (hsx : (Finset.univ.filter fun i ↦ s i).card = (x : ℕ)) :
    (∑ z : Schedule 2 n,
      if twoArmX z A = x ∧ (fun i ↦ twoArmS z A i) = s
        then canonicalScheduleKernel θ z else 0) =
    (∑ z : Schedule 2 n,
      if twoArmX z A = x then canonicalScheduleKernel θ z else 0) /
        Nat.choose n (x : ℕ) := by
  classical
  have hleft : (∑ z : Schedule 2 n,
      if twoArmX z A = x ∧ (fun i ↦ twoArmS z A i) = s
        then canonicalScheduleKernel θ z else 0) =
      ∑ z : Schedule 2 n,
        if (fun i ↦ twoArmS z A i) = s then canonicalScheduleKernel θ z else 0 := by
    apply Finset.sum_congr rfl
    intro z _
    by_cases hs : (fun i ↦ twoArmS z A i) = s
    · have hx : twoArmX z A = x := by
        rw [Fin.ext_iff]
        change (Finset.univ.filter fun i ↦ twoArmS z A i).card = (x : ℕ)
        simpa [hs] using hsx
      simp [hs, hx]
    · simp [hs]
  rw [hleft]
  by_cases hp : (θ.1.1 : ℕ) ≤ (x : ℕ)
  · by_cases hx : (x : ℕ) ≤ (θ.1.1 : ℕ) + (θ.1.2.2 : ℕ)
    · rw [twoArmCanonicalScore_mass_eq_binomial θ A s]
      · rw [twoArmXMass_eq_binomial_of_support θ A x hp hx]
        simp [hsx]
      · simpa [hsx] using hp
      · simpa [hsx] using hx
    · have hout : (θ.1.1 : ℕ) + (θ.1.2.2 : ℕ) < (x : ℕ) := by omega
      rw [twoArmCanonicalScore_mass_eq_zero_of_gt θ A s (by omega)]
      rw [twoArmXMass_eq_zero_of_outside θ A x (Or.inr hout)]
      simp
  · have hout : (x : ℕ) < (θ.1.1 : ℕ) := by omega
    rw [twoArmCanonicalScore_mass_eq_zero_of_lt θ A s (by omega)]
    rw [twoArmXMass_eq_zero_of_outside θ A x (Or.inl hout)]
    simp

-- @node: hasTwoArmScalarKernel_canonical
/-- [has two arm scalar kernel canonical](goal). -/
lemma hasTwoArmScalarKernel_canonical {n : ℕ} (θ : EffectTriple n) :
    HasTwoArmScalarKernel θ := by
  refine ⟨twoArmXMass_eq_binomial_sum θ, ?_, ?_⟩
  · intro _A
    exact canonicalScheduleKernel_sum θ
  · intro A x s hs
    rw [← Finset.sum_div]
    exact twoArmCanonicalConditionalScore_mass θ A x s hs

-- @node: twoArmTau_eq_effectTriple
/-- [the stated side condition holds](hyp:hz), [the two arm tau equals effect triple](goal). -/
lemma twoArmTau_eq_effectTriple {n : ℕ} {θ : EffectTriple n}
    {z : Schedule 2 n} (hz : hasEffectTriple θ z) :
    tauC twoArmContrast z =
      ((((θ.1.1 : ℕ) : ℝ) - ((θ.1.2.1 : ℕ) : ℝ)) / n) := by
  have hpoint (i : Unit n) :
      (∑ a, twoArmContrast a * if z i a then 1 else 0) =
        (if z i 0 && !(z i 1) then (1 : ℝ) else 0) -
        (if !(z i 0) && z i 1 then (1 : ℝ) else 0) := by
    cases h0 : z i 0 <;> cases h1 : z i 1 <;>
      simp [twoArmContrast, ratContrastToReal, twoArmContrastQ,
        Fin.sum_univ_succ, h0, h1]
  unfold tauC
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  have hp : (∑ i : Unit n,
      if z i 0 && !(z i 1) then (1 : ℝ) else 0) =
      (Finset.univ.filter fun i ↦ z i 0 && !(z i 1)).card := by
    rw [Finset.sum_ite]
    simp
  have hm : (∑ i : Unit n,
      if !(z i 0) && z i 1 then (1 : ℝ) else 0) =
      (Finset.univ.filter fun i ↦ !(z i 0) && z i 1).card := by
    rw [Finset.sum_ite]
    simp
  rw [hp, hm, hz.1, hz.2.1]
  rw [div_eq_inv_mul]


end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

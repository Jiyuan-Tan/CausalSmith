import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Basic
import Causalean.Stat.FiniteRaoBlackwell.KernelBridge
import Causalean.Stat.Minimax.FiniteKernelBayes
import Mathlib.Data.Nat.Choose.Multinomial

/-!
Lift of an arbitrary prior on two-arm effect-class triples to complete labeled
binary schedules, together with the assignment-ancillary scalar kernel.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

/-- Two-arm effect-class counts `(p_+,p_-,r_0)` summing to `n`. -/
def EffectTriple (n : ℕ) :=
  {θ : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) //
    (θ.1 : ℕ) + (θ.2.1 : ℕ) + (θ.2.2 : ℕ) = n}

/-- The effect triple collection has a finite enumeration. -/
instance (n : ℕ) : Fintype (EffectTriple n) := by
  unfold EffectTriple
  infer_instance

/-- An effect prior is a finite probability distribution over two-arm effect-count triples. -/
abbrev EffectPrior (n : ℕ) :=
  Causalean.Experimentation.DesignBased.FiniteDesign (EffectTriple n)

/-- Finite binomial `(r,1/2)` mass. -/
noncomputable def binomialHalf (r k : ℕ) : ℝ :=
  (Nat.choose r k : ℝ) / 2 ^ r

/-- Scalar Bayes risk for `X=p_+ + Binomial(r_0,1/2)`. -/
noncomputable def scalarBayesRisk {n : ℕ} (nu : EffectPrior n) : ℝ :=
  sInf {v : ℝ | ∃ f : ℕ → ℝ,
    v = ∑ θ, nu.p θ * ∑ k ∈ Finset.range (((θ.1).2.2 : ℕ) + 1),
      binomialHalf ((θ.1).2.2 : ℕ) k *
        (f (((θ.1).1 : ℕ) + k) -
          ((((θ.1).1 : ℕ) : ℝ) - (((θ.1).2.1 : ℕ) : ℝ)) / n) ^ 2}

/-- Bayes risk of the complete-schedule lift under a fixed arbitrary design. -/
noncomputable def fullScheduleBayesRisk {n : ℕ}
    (lift : Causalean.Experimentation.DesignBased.FiniteDesign (Schedule 2 n))
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n)) : ℝ :=
  sInf {v : ℝ | ∃ est : Estimator 2 n twoArmContrast,
    v = lift.E (fun z => labeledRisk twoArmContrast (D, est) z)}

/-- The schedule statistic `S_i=Y_i(1)` on arm 1 and `1-Y_i(2)` on arm 2. -/
def twoArmS (z : Schedule 2 n) (A : Assign 2 n) (i : Unit n) : Bool :=
  if A i = 0 then z i 0 else !(z i 1)

/-- The observable scalar count, retained in its exact support. -/
-- @realizes X_2(observable scalar count in Fin (n + 1))
def twoArmX (z : Schedule 2 n) (A : Assign 2 n) : Fin (n + 1) :=
  ⟨(Finset.univ.filter fun i => twoArmS z A i).card,
    Nat.lt_succ_iff.mpr (by
      simpa using Finset.card_le_card
        (Finset.filter_subset (fun i => twoArmS z A i) Finset.univ))⟩

/-- Has effect triple. -/
def hasEffectTriple (θ : EffectTriple n) (z : Schedule 2 n) : Prop :=
  (Finset.univ.filter fun i => z i 0 && !(z i 1)).card = (θ.1.1 : ℕ) ∧
  (Finset.univ.filter fun i => !(z i 0) && z i 1).card = (θ.1.2.1 : ℕ) ∧
  (Finset.univ.filter fun i => z i 0 = z i 1).card = (θ.1.2.2 : ℕ)

-- @node: twoArmEffectClass_indicator_partition
/-- [The positive, negative, and zero-effect predicates partition the four two-arm response types pointwise.](goal) -/
lemma twoArmEffectClass_indicator_partition (z : Schedule 2 n) (i : Unit n) :
    (if z i 0 && !(z i 1) then 1 else 0) +
        (if !(z i 0) && z i 1 then 1 else 0) +
        (if z i 0 = z i 1 then 1 else 0) = 1 := by
  cases h₀ : z i 0 <;> cases h₁ : z i 1 <;> simp [h₀, h₁]

-- @node: hasEffectTriple_counts_sum
/-- [A schedule in an effect-triple fiber has the advertised three class counts and those counts exhaust the population.](goal) -/
lemma hasEffectTriple_counts_sum {θ : EffectTriple n} {z : Schedule 2 n}
    (h : hasEffectTriple θ z) :
    (Finset.univ.filter fun i => z i 0 && !(z i 1)).card +
        (Finset.univ.filter fun i => !(z i 0) && z i 1).card +
        (Finset.univ.filter fun i => z i 0 = z i 1).card = n := by
  rw [h.1, h.2.1, h.2.2]
  exact θ.2

-- @node: twoArmS_of_positive_effect
/-- [A positive-effect response type contributes one to the transformed score under either assignment arm.](goal) -/
lemma twoArmS_of_positive_effect (z : Schedule 2 n) (A : Assign 2 n) (i : Unit n)
    (h : z i 0 && !(z i 1)) : twoArmS z A i = true := by
  have hz : z i 0 = true ∧ z i 1 = false := by simpa using h
  by_cases hA : A i = 0
  · simpa [twoArmS, hA] using hz.1
  · simpa [twoArmS, hA] using hz.2

-- @node: twoArmS_of_negative_effect
/-- [A negative-effect response type contributes zero to the transformed score under either assignment arm.](goal) -/
lemma twoArmS_of_negative_effect (z : Schedule 2 n) (A : Assign 2 n) (i : Unit n)
    (h : !(z i 0) && z i 1) : twoArmS z A i = false := by
  have hz : z i 0 = false ∧ z i 1 = true := by simpa using h
  by_cases hA : A i = 0
  · simpa [twoArmS, hA] using hz.1
  · simpa [twoArmS, hA] using hz.2

-- @node: twoArmS_of_zero_effect
/-- [the stated side condition holds](hyp:h), [On a zero-effect response type, assignment either preserves or flips its common fair bit, exactly as in the paper's schedule construction.](goal) -/
lemma twoArmS_of_zero_effect (z : Schedule 2 n) (A : Assign 2 n) (i : Unit n)
    (h : z i 0 = z i 1) :
    twoArmS z A i = if A i = 0 then z i 0 else !(z i 0) := by
  by_cases hA : A i = 0 <;> simp [twoArmS, hA, h]

-- @node: twoArmScheduleOfScoreChoices
/-- Reconstruct the unique two-arm schedule from its positive and negative
effect sets and its transformed score vector. -/
def twoArmScheduleOfScoreChoices (A : Assign 2 n) (s : Unit n → Bool)
    (P N : Finset (Unit n)) : Schedule 2 n := fun i a =>
  if i ∈ P then a = 0
  else if i ∈ N then a ≠ 0
  else if A i = 0 then s i else !(s i)

-- @node: twoArmScheduleOfScoreChoices_score
/-- [the positive-effect set has the prescribed cardinality](hyp:hP), [the negative-effect set has the prescribed cardinality](hyp:hN), [Disjoint choices drawn respectively from the one and zero coordinates reconstruct a schedule with the prescribed transformed score.](goal) -/
lemma twoArmScheduleOfScoreChoices_score (A : Assign 2 n) (s : Unit n → Bool)
    {P N : Finset (Unit n)}
    (hP : P ⊆ Finset.univ.filter fun i ↦ s i)
    (hN : N ⊆ Finset.univ.filter fun i ↦ !(s i)) :
    (fun i ↦ twoArmS (twoArmScheduleOfScoreChoices A s P N) A i) = s := by
  funext i
  by_cases hiP : i ∈ P
  · have hsi : s i = true := by
      have := hP hiP
      simpa using (Finset.mem_filter.mp this).2
    by_cases hA : A i = 0
    · simp [twoArmS, twoArmScheduleOfScoreChoices, hiP, hA, hsi]
    · have hA1 : A i = 1 := Fin.eq_one_of_ne_zero _ hA
      simp [twoArmS, twoArmScheduleOfScoreChoices, hiP, hA, hA1, hsi]
  · by_cases hiN : i ∈ N
    · have hsi : s i = false := by
        have := hN hiN
        simpa using (Finset.mem_filter.mp this).2
      by_cases hA : A i = 0
      · simp [twoArmS, twoArmScheduleOfScoreChoices, hiP, hiN, hA, hsi]
      · have hA1 : A i = 1 := Fin.eq_one_of_ne_zero _ hA
        simp [twoArmS, twoArmScheduleOfScoreChoices, hiP, hiN, hA, hA1, hsi]
    · by_cases hA : A i = 0
      · simp [twoArmS, twoArmScheduleOfScoreChoices, hiP, hiN, hA]
      · have hA1 : A i = 1 := Fin.eq_one_of_ne_zero _ hA
        cases hs : s i <;>
          simp [twoArmS, twoArmScheduleOfScoreChoices, hiP, hiN, hA, hA1, hs]

-- @node: twoArmScheduleOfScoreChoices_effects
/-- [the positive-effect set has the prescribed cardinality](hyp:hP), [the negative-effect set has the prescribed cardinality](hyp:hN), [The reconstructed schedule has positive set `P`, negative set `N`, and zero-effect set their complement.](goal) -/
lemma twoArmScheduleOfScoreChoices_effects (A : Assign 2 n) (s : Unit n → Bool)
    {P N : Finset (Unit n)}
    (hP : P ⊆ Finset.univ.filter fun i ↦ s i)
    (hN : N ⊆ Finset.univ.filter fun i ↦ !(s i)) :
    (Finset.univ.filter fun i ↦
      twoArmScheduleOfScoreChoices A s P N i 0 &&
        !(twoArmScheduleOfScoreChoices A s P N i 1)) = P ∧
    (Finset.univ.filter fun i ↦
      !(twoArmScheduleOfScoreChoices A s P N i 0) &&
        twoArmScheduleOfScoreChoices A s P N i 1) = N ∧
    (Finset.univ.filter fun i ↦
      twoArmScheduleOfScoreChoices A s P N i 0 =
        twoArmScheduleOfScoreChoices A s P N i 1) =
      Finset.univ \ (P ∪ N) := by
  have hdisj : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro i hiP hiN
    have hp := (Finset.mem_filter.mp (hP hiP)).2
    have hn := (Finset.mem_filter.mp (hN hiN)).2
    cases hs : s i <;> simp [hs] at hp hn
  constructor
  · ext i
    by_cases hiP : i ∈ P <;> by_cases hiN : i ∈ N
    · exact (Finset.disjoint_left.mp hdisj hiP hiN).elim
    · simp [twoArmScheduleOfScoreChoices, hiP, hiN]
    · simp [twoArmScheduleOfScoreChoices, hiP, hiN]
    · by_cases hA : A i = 0 <;>
        cases hs : s i <;>
        simp [twoArmScheduleOfScoreChoices, hiP, hiN, hA, hs]
  · constructor
    · ext i
      by_cases hiP : i ∈ P <;> by_cases hiN : i ∈ N
      · exact (Finset.disjoint_left.mp hdisj hiP hiN).elim
      · simp [twoArmScheduleOfScoreChoices, hiP, hiN]
      · simp [twoArmScheduleOfScoreChoices, hiP, hiN]
      · by_cases hA : A i = 0 <;>
          cases hs : s i <;>
          simp [twoArmScheduleOfScoreChoices, hiP, hiN, hA, hs]
    · ext i
      by_cases hiP : i ∈ P <;> by_cases hiN : i ∈ N
      · exact (Finset.disjoint_left.mp hdisj hiP hiN).elim
      · simp [twoArmScheduleOfScoreChoices, hiP, hiN]
      · simp [twoArmScheduleOfScoreChoices, hiP, hiN]
      · by_cases hA : A i = 0 <;>
          cases hs : s i <;>
          simp [twoArmScheduleOfScoreChoices, hiP, hiN, hA, hs]

/-- Schedules in one fixed effect-triple and transformed-score fiber. -/
def TwoArmScoreScheduleFiber (θ : EffectTriple n) (A : Assign 2 n)
    (s : Unit n → Bool) :=
  {z : Schedule 2 n // hasEffectTriple θ z ∧ (fun i ↦ twoArmS z A i) = s}

/-- The two independent subset choices parametrizing a fixed score fiber. -/
def TwoArmScoreChoices (θ : EffectTriple n) (s : Unit n → Bool) :=
  {P // P ∈ (Finset.univ.filter fun i ↦ s i).powersetCard (θ.1.1 : ℕ)} ×
  {N // N ∈ (Finset.univ.filter fun i ↦ !(s i)).powersetCard (θ.1.2.1 : ℕ)}

/-- The two arm score schedule fiber collection has a finite enumeration. -/
noncomputable instance (θ : EffectTriple n) (A : Assign 2 n) (s : Unit n → Bool) :
    Fintype (TwoArmScoreScheduleFiber θ A s) := by
  classical
  unfold TwoArmScoreScheduleFiber
  infer_instance

/-- The two arm score choices collection has a finite enumeration. -/
noncomputable instance (θ : EffectTriple n) (s : Unit n → Bool) :
    Fintype (TwoArmScoreChoices θ s) := by
  classical
  unfold TwoArmScoreChoices
  infer_instance

-- @node: twoArmScoreScheduleFiberEquiv
/-- A fixed transformed-score fiber is exactly a pair of subset choices for
the positive and negative effect classes. -/
noncomputable def twoArmScoreScheduleFiberEquiv (θ : EffectTriple n)
    (A : Assign 2 n) (s : Unit n → Bool) :
    TwoArmScoreScheduleFiber θ A s ≃ TwoArmScoreChoices θ s where
  toFun z :=
    (⟨Finset.univ.filter fun i ↦ z.1 i 0 && !(z.1 i 1), by
      rw [Finset.mem_powersetCard]
      refine ⟨?_, z.2.1.1⟩
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have hs := congrFun z.2.2 i
      rw [twoArmS_of_positive_effect z.1 A i hi.2] at hs
      exact hs.symm⟩,
    ⟨Finset.univ.filter fun i ↦ !(z.1 i 0) && z.1 i 1, by
      rw [Finset.mem_powersetCard]
      refine ⟨?_, z.2.1.2.1⟩
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have hs := congrFun z.2.2 i
      rw [twoArmS_of_negative_effect z.1 A i hi.2] at hs
      simpa using hs.symm⟩)
  invFun q := ⟨twoArmScheduleOfScoreChoices A s q.1.1 q.2.1, by
    rcases Finset.mem_powersetCard.mp q.1.2 with ⟨hP, hcP⟩
    rcases Finset.mem_powersetCard.mp q.2.2 with ⟨hN, hcN⟩
    have he := twoArmScheduleOfScoreChoices_effects A s hP hN
    refine ⟨⟨?_, ?_, ?_⟩, twoArmScheduleOfScoreChoices_score A s hP hN⟩
    · rw [he.1, hcP]
    · rw [he.2.1, hcN]
    · rw [he.2.2]
      have hsub : q.1.1 ∪ q.2.1 ⊆ (Finset.univ : Finset (Unit n)) := by simp
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_union_of_disjoint]
      · rw [Finset.card_univ, Fintype.card_fin, hcP, hcN]
        have ht := θ.2
        omega
      · apply Finset.disjoint_left.mpr
        intro i hiP hiN
        have hp := (Finset.mem_filter.mp (hP hiP)).2
        have hn := (Finset.mem_filter.mp (hN hiN)).2
        cases hs : s i
        · simp [hs] at hp
        · simp [hs] at hn
    ⟩
  left_inv z := by
    apply Subtype.ext
    funext i a
    fin_cases a <;> cases h0 : z.1 i 0 <;> cases h1 : z.1 i 1
    all_goals
      have hs := congrFun z.2.2 i
      by_cases hA : A i = 0
      · simp [twoArmScheduleOfScoreChoices, twoArmS, h0, h1, hA] at hs ⊢ <;>
          assumption
      · have hA1 : A i = 1 := Fin.eq_one_of_ne_zero _ hA
        simp [twoArmScheduleOfScoreChoices, twoArmS, h0, h1, hA1] at hs ⊢ <;>
          assumption
  right_inv q := by
    rcases Finset.mem_powersetCard.mp q.1.2 with ⟨hP, _⟩
    rcases Finset.mem_powersetCard.mp q.2.2 with ⟨hN, _⟩
    apply Prod.ext
    · apply Subtype.ext
      exact (twoArmScheduleOfScoreChoices_effects A s hP hN).1
    · apply Subtype.ext
      exact (twoArmScheduleOfScoreChoices_effects A s hP hN).2.1

-- @node: twoArmScoreScheduleFiber_card
/-- [The exact number of complete schedules producing a prescribed transformed score vector is the product of the two subset counts.](goal) -/
lemma twoArmScoreScheduleFiber_card (θ : EffectTriple n) (A : Assign 2 n)
    (s : Unit n → Bool) :
    Fintype.card (TwoArmScoreScheduleFiber θ A s) =
      Nat.choose (Finset.univ.filter fun i ↦ s i).card (θ.1.1 : ℕ) *
      Nat.choose (Finset.univ.filter fun i ↦ !(s i)).card (θ.1.2.1 : ℕ) := by
  rw [Fintype.card_congr (twoArmScoreScheduleFiberEquiv θ A s)]
  unfold TwoArmScoreChoices
  rw [Fintype.card_prod]
  simp only [TwoArmScoreChoices, Fintype.card_coe, Finset.card_powersetCard]

-- @node: twoArmCanonicalDenominator_eq_choose
/-- [the stated side condition holds](hyp:h), [The ordered-partition normalizer is the product of the two successive subset-choice counts, including all zero-count boundary cases.](goal) -/
lemma twoArmCanonicalDenominator_eq_choose {n p m r : ℕ} (h : p + m + r = n) :
    (Nat.factorial n : ℝ) /
        ((Nat.factorial p : ℝ) * Nat.factorial m * Nat.factorial r) =
      (Nat.choose n p : ℝ) * Nat.choose (n - p) m := by
  have hp : p ≤ n := by omega
  have hm : m ≤ n - p := by omega
  rw [Nat.cast_choose ℝ hp, Nat.cast_choose ℝ hm]
  have hsub : n - p - m = r := by omega
  rw [hsub]
  field_simp

-- @node: twoArmChooseFiber_identity
/-- [the stated side condition holds](hyp:h), [the positive-effect count satisfies its stated condition](hyp:hpx), [the residual count satisfies its stated condition](hyp:hxr), [The factorial identity converting the score-fiber count into its binomial mass, on the exact support `p ≤ x ≤ p+r`.](goal) -/
lemma twoArmChooseFiber_identity {n p m r x : ℕ} (h : p + m + r = n)
    (hpx : p ≤ x) (hxr : x ≤ p + r) :
    (Nat.choose n x : ℝ) * Nat.choose x p * Nat.choose (n - x) m =
      Nat.choose n p * Nat.choose (n - p) m * Nat.choose r (x - p) := by
  have hx : x ≤ n := by omega
  have hm : m ≤ n - x := by omega
  have hp : p ≤ n := by omega
  have hmp : m ≤ n - p := by omega
  have hxp : x - p ≤ r := by omega
  rw [Nat.cast_choose ℝ hx, Nat.cast_choose ℝ hpx,
    Nat.cast_choose ℝ hm, Nat.cast_choose ℝ hp,
    Nat.cast_choose ℝ hmp, Nat.cast_choose ℝ hxp]
  have h1 : n - p = m + r := by omega
  have h2 : n - x = m + (r - (x - p)) := by omega
  rw [h1, h2]
  simp only [Nat.add_sub_cancel_left]
  field_simp

/-- The ordered-partition plus independent-fair-bit schedule kernel. -/
noncomputable def canonicalScheduleKernel (θ : EffectTriple n) (z : Schedule 2 n) : ℝ :=
  by
    classical
    exact if _h : hasEffectTriple θ z then
      1 / ((Nat.factorial n : ℝ) /
        (Nat.factorial (θ.1.1 : ℕ) * Nat.factorial (θ.1.2.1 : ℕ) *
          Nat.factorial (θ.1.2.2 : ℕ)) * 2 ^ (θ.1.2.2 : ℕ))
    else 0

-- @node: twoArmCanonicalScoreFiber_mass
/-- [The canonical kernel mass of one exact transformed-score vector is its score-fiber cardinality divided by the ordered-partition/fair-bit normalizer.](goal) -/
lemma twoArmCanonicalScoreFiber_mass {θ : EffectTriple n} (A : Assign 2 n)
    (s : Unit n → Bool) :
    (by classical exact ∑ z : Schedule 2 n,
      (if hasEffectTriple θ z ∧ (fun i ↦ twoArmS z A i) = s
        then canonicalScheduleKernel θ z else 0)) =
      (Fintype.card (TwoArmScoreScheduleFiber θ A s) : ℝ) /
        ((Nat.factorial n : ℝ) /
          (Nat.factorial (θ.1.1 : ℕ) * Nat.factorial (θ.1.2.1 : ℕ) *
            Nat.factorial (θ.1.2.2 : ℕ)) * 2 ^ (θ.1.2.2 : ℕ)) := by
  classical
  simp only [canonicalScheduleKernel]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  have hsum :
      (∑ x ∈ (Finset.univ.filter fun z : Schedule 2 n ↦
          hasEffectTriple θ z ∧ (fun i ↦ twoArmS z A i) = s),
        if _h : hasEffectTriple θ x then
          1 / ((Nat.factorial n : ℝ) /
            (Nat.factorial (θ.1.1 : ℕ) * Nat.factorial (θ.1.2.1 : ℕ) *
              Nat.factorial (θ.1.2.2 : ℕ)) * 2 ^ (θ.1.2.2 : ℕ)) else 0) =
        ∑ _x ∈ (Finset.univ.filter fun z : Schedule 2 n ↦
          hasEffectTriple θ z ∧ (fun i ↦ twoArmS z A i) = s),
          1 / ((Nat.factorial n : ℝ) /
            (Nat.factorial (θ.1.1 : ℕ) * Nat.factorial (θ.1.2.1 : ℕ) *
              Nat.factorial (θ.1.2.2 : ℕ)) * 2 ^ (θ.1.2.2 : ℕ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_filter] at hx
    simp [hx.2.1]
  rw [hsum, Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.card_subtype (fun z : Schedule 2 n ↦
    hasEffectTriple θ z ∧ (fun i ↦ twoArmS z A i) = s)]
  change ((Fintype.card (TwoArmScoreScheduleFiber θ A s) : ℕ) : ℝ) * _ = _
  simp [div_eq_mul_inv]

-- @node: twoArmX_eq_score_card
/-- [The scalar statistic is exactly the number of true coordinates in the transformed score vector.](goal) -/
lemma twoArmX_eq_score_card (z : Schedule 2 n) (A : Assign 2 n) :
    (twoArmX z A : ℕ) =
      (Finset.univ.filter fun i ↦ twoArmS z A i).card := by
  rfl

-- @node: twoArmCanonicalScoreFiber_mass_eq_binomial
/-- [the stated probability condition holds](hyp:hp), [the observed count satisfies its stated condition](hyp:hx), [On its exact support, the canonical mass of a fixed transformed-score vector is the binomial mass divided by the number of vectors with that score.](goal) -/
lemma twoArmCanonicalScoreFiber_mass_eq_binomial {θ : EffectTriple n}
    (A : Assign 2 n) (s : Unit n → Bool)
    (hp : (θ.1.1 : ℕ) ≤ (Finset.univ.filter fun i ↦ s i).card)
    (hx : (Finset.univ.filter fun i ↦ s i).card ≤
      (θ.1.1 : ℕ) + (θ.1.2.2 : ℕ)) :
    (by classical exact ∑ z : Schedule 2 n,
      (if hasEffectTriple θ z ∧ (fun i ↦ twoArmS z A i) = s
        then canonicalScheduleKernel θ z else 0)) =
      binomialHalf (θ.1.2.2 : ℕ)
          ((Finset.univ.filter fun i ↦ s i).card - (θ.1.1 : ℕ)) /
        Nat.choose n (Finset.univ.filter fun i ↦ s i).card := by
  classical
  let x := (Finset.univ.filter fun i ↦ s i).card
  let p := (θ.1.1 : ℕ)
  let m := (θ.1.2.1 : ℕ)
  let r := (θ.1.2.2 : ℕ)
  have hsum : p + m + r = n := θ.2
  have hxn : x ≤ n := by
    dsimp [x]
    simpa using Finset.card_le_card
      (Finset.filter_subset (fun i ↦ s i) Finset.univ)
  have hchoose : (Nat.choose n x : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hxn).ne'
  have hfalse : (Finset.univ.filter fun i ↦ !(s i)).card = n - x := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Unit n))) (p := fun i ↦ s i)
    simp only [Finset.card_univ, Fintype.card_fin] at hpart
    have heq : (Finset.univ.filter fun i ↦ !(s i)) =
        Finset.univ.filter fun i ↦ ¬ s i := by
      ext i
      cases hs : s i <;> simp [hs]
    rw [heq]
    omega
  rw [twoArmCanonicalScoreFiber_mass, twoArmScoreScheduleFiber_card]
  rw [hfalse]
  change ((Nat.choose x p * Nat.choose (n - x) m : ℕ) : ℝ) /
      ((Nat.factorial n : ℝ) /
        (Nat.factorial p * Nat.factorial m * Nat.factorial r) * 2 ^ r) = _
  rw [Nat.cast_mul, twoArmCanonicalDenominator_eq_choose hsum]
  unfold binomialHalf
  change (Nat.choose x p : ℝ) * Nat.choose (n - x) m /
      ((Nat.choose n p : ℝ) * Nat.choose (n - p) m * 2 ^ r) =
    (Nat.choose r (x - p) : ℝ) / 2 ^ r / Nat.choose n x
  have hid := twoArmChooseFiber_identity hsum hp hx
  have hpN : p ≤ n := by omega
  have hmN : m ≤ n - p := by omega
  have hnp : (Nat.choose n p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hpN).ne'
  have hnm : (Nat.choose (n - p) m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hmN).ne'
  have hden : (Nat.choose n p : ℝ) * Nat.choose (n - p) m ≠ 0 := by
    exact mul_ne_zero hnp hnm
  field_simp [hchoose, hden]
  simpa [x, p, m, r, mul_assoc, mul_left_comm, mul_comm] using hid

/-- A lift is the actual `ν`-mixture of the canonical schedule kernels. -/
def IsCanonicalNuLift (nu : EffectPrior n)
    (lift : Causalean.Experimentation.DesignBased.FiniteDesign (Schedule 2 n)) : Prop :=
  ∀ z, lift.p z = ∑ θ, nu.p θ * canonicalScheduleKernel θ z

/-- The paper's conditional binomial, assignment-ancillarity, and uniform-`S` claims. -/
def HasTwoArmScalarKernel (θ : EffectTriple n) : Prop :=
  (∀ (A : Assign 2 n) (x : Fin (n + 1)),
    ∑ z : Schedule 2 n,
      (if twoArmX z A = x then canonicalScheduleKernel θ z else 0) =
      ∑ k ∈ Finset.range ((θ.1.2.2 : ℕ) + 1),
        if (x : ℕ) = (θ.1.1 : ℕ) + k then binomialHalf (θ.1.2.2 : ℕ) k else 0) ∧
  (∀ A : Assign 2 n,
    ∑ z : Schedule 2 n, canonicalScheduleKernel θ z = 1) ∧
  (∀ (A : Assign 2 n) (x : Fin (n + 1)) (s : Unit n → Bool),
    (Finset.univ.filter fun i => s i).card = x →
    ∑ z : Schedule 2 n,
      (if twoArmX z A = x ∧ (fun i => twoArmS z A i) = s
        then canonicalScheduleKernel θ z else 0) =
    ∑ z : Schedule 2 n,
      (if twoArmX z A = x then canonicalScheduleKernel θ z else 0) /
        Nat.choose n x)

/-- Estimator-wise two-stage Rao--Blackwell domination through the scalar count. -/
def RaoBlackwellThroughX (nu : EffectPrior n)
    (lift : Causalean.Experimentation.DesignBased.FiniteDesign (Schedule 2 n)) : Prop :=
  ∀ (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n))
    (est : Estimator 2 n twoArmContrast),
    ∃ f : ℕ → ℝ,
      (∑ θ, nu.p θ * ∑ k ∈ Finset.range ((θ.1.2.2 : ℕ) + 1),
        binomialHalf (θ.1.2.2 : ℕ) k *
          (f ((θ.1.1 : ℕ) + k) -
            (((θ.1.1 : ℕ) : ℝ) - ((θ.1.2.1 : ℕ) : ℝ)) / n) ^ 2) ≤
      lift.E (fun z => labeledRisk twoArmContrast (D, est) z)

-- @node: scalarBayesRisk_le_rho2_of_scheduleKernel
/-- [the schedule kernel has the stated scalar representation](hyp:hkernel), [Once a complete-schedule lift has the scalar Bayes risk for every assignment law, that scalar risk is a lower bound for the unrestricted two-arm minimax value.](goal) -/
lemma scalarBayesRisk_le_rho2_of_scheduleKernel {n : ℕ} (nu : EffectPrior n)
    (lift : Causalean.Experimentation.DesignBased.FiniteDesign (Schedule 2 n))
    (hkernel : ∀ D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n),
      fullScheduleBayesRisk lift D = scalarBayesRisk nu) :
    scalarBayesRisk nu ≤ rho2 n := by
  let _ : Nonempty (Procedure 2 n twoArmContrast) :=
    ⟨contrastWeightedProcedure 2 n twoArmContrast⟩
  unfold rho2 rhoN
  apply Causalean.Stat.le_minimaxValue
  intro p
  rw [← hkernel p.1]
  unfold fullScheduleBayesRisk
  have hbdd : BddBelow {v : ℝ | ∃ est : Estimator 2 n twoArmContrast,
      v = lift.E (fun z ↦ labeledRisk twoArmContrast (p.1, est) z)} := by
    refine ⟨0, ?_⟩
    rintro v ⟨est, rfl⟩
    exact Finset.sum_nonneg fun z _ ↦
      mul_nonneg (lift.p_nonneg z) (p.1.mse_nonneg _ _)
  calc
    sInf {v : ℝ | ∃ est : Estimator 2 n twoArmContrast,
        v = lift.E (fun z ↦ labeledRisk twoArmContrast (p.1, est) z)} ≤
        lift.E (fun z ↦ labeledRisk twoArmContrast p z) :=
      csInf_le hbdd ⟨p.2, rfl⟩
    _ ≤ Causalean.Stat.worstCaseRisk
        (fun q z ↦ labeledRisk twoArmContrast q z) p :=
      Causalean.Stat.finiteDesign_expectedLoss_le_worstCaseRisk lift
        (fun q z ↦ labeledRisk twoArmContrast q z)
        (fun q z ↦ q.1.mse_nonneg _ _) p

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

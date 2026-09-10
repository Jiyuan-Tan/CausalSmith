import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Inference

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw
open scoped BigOperators

lemma test_mass_identity {k : ℕ} {radius : ℝ} {a b : AtomicLaw k radius}
    (γ : TransportPlan a b) (p q : Fin k → Prop) [DecidablePred p] [DecidablePred q] :
    (∑ i, if p i then a.weight i else 0) - (∑ j, if q j then b.weight j else 0) =
      (∑ i, ∑ j, if p i ∧ ¬ q j then γ.mass i j else 0) -
      (∑ i, ∑ j, if ¬ p i ∧ q j then γ.mass i j else 0) := by
  simp_rw [← γ.fst_marginal, ← γ.snd_marginal]
  have hp : (∑ i, if p i then ∑ j, γ.mass i j else 0) =
      ∑ i, ∑ j, if p i then γ.mass i j else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_ite_irrel]
    simp
  have hq : (∑ j, if q j then ∑ i, γ.mass i j else 0) =
      ∑ j, ∑ i, if q j then γ.mass i j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_ite_irrel]
    simp
  rw [hp, hq, Finset.sum_comm (f := fun j i => if q j then γ.mass i j else 0)]
  classical
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hp : p i <;> by_cases hq : q j <;> simp [hp, hq]

lemma test_mass_gap {k : ℕ} {radius gap : ℝ} {a b : AtomicLaw k radius}
    (γ : TransportPlan a b) (p q : Fin k → Prop) [DecidablePred p] [DecidablePred q]
    (hgap : 0 ≤ gap)
    (hcross : ∀ i j, 0 < γ.mass i j → (p i ∧ ¬ q j) ∨ (¬ p i ∧ q j) →
      gap ≤ |a.atom i - b.atom j|) :
    gap * |(∑ i, if p i then a.weight i else 0) -
      (∑ j, if q j then b.weight j else 0)| ≤ transportCost γ := by
  classical
  let S : ℝ := ∑ i, ∑ j, if p i ∧ ¬ q j then γ.mass i j else 0
  let T : ℝ := ∑ i, ∑ j, if ¬ p i ∧ q j then γ.mass i j else 0
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    split_ifs <;> simp_all [γ.nonneg]
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    split_ifs <;> simp_all [γ.nonneg]
  rw [test_mass_identity γ p q]
  calc
    gap * |S - T| ≤ gap * (S + T) := by
      gcongr
      rw [abs_le]
      constructor <;> linarith
    _ = ∑ i, ∑ j, gap *
        ((if p i ∧ ¬ q j then γ.mass i j else 0) +
          (if ¬ p i ∧ q j then γ.mass i j else 0)) := by
      simp [S, T, Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    _ ≤ ∑ i, ∑ j, γ.mass i j * |a.atom i - b.atom j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hp : p i <;> by_cases hq : q j
      · simp [hp, hq, mul_nonneg (γ.nonneg i j) (abs_nonneg _)]
      · simp only [hp, hq, true_and, not_false_eq_true, ↓reduceIte,
          not_true_eq_false, false_and, add_zero]
        by_cases hm : 0 < γ.mass i j
        · nlinarith [hcross i j hm (Or.inl ⟨hp, hq⟩)]
        · have : γ.mass i j = 0 := le_antisymm (le_of_not_gt hm) (γ.nonneg i j)
          simp [this]
      · simp only [hp, hq, false_and, ↓reduceIte, not_false_eq_true,
          true_and, not_true_eq_false, zero_add]
        by_cases hm : 0 < γ.mass i j
        · nlinarith [hcross i j hm (Or.inr ⟨hp, hq⟩)]
        · have : γ.mass i j = 0 := le_antisymm (le_of_not_gt hm) (γ.nonneg i j)
          simp [this]
      · simp [hp, hq, mul_nonneg (γ.nonneg i j) (abs_nonneg _)]
    _ = transportCost γ := rfl

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.AtomicLaw

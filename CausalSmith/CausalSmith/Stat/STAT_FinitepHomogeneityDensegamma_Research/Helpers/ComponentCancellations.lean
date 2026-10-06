module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentBounds

/-! Exact conditional marginal cancellations for the full-record component likelihoods. -/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Summing the outcome sign preserves the fair propensity-sign marginal of a copula pair. [This is the stated conclusion](goal). -/
-- @node: pairWeight_fst_sum
lemma pairWeight_fst_sum (ν : Bool) (g : ℝ) (l : Bool) :
    ∑ h : Bool, pairWeight ν g l h = 1/2 := by
  cases ν <;> cases l <;> simp [pairWeight, signVal] <;> ring

/-- Summing the propensity sign preserves the fair outcome-sign marginal of a copula pair. [This is the stated conclusion](goal). -/
-- @node: pairWeight_snd_sum
lemma pairWeight_snd_sum (ν : Bool) (g : ℝ) (h : Bool) :
    ∑ l : Bool, pairWeight ν g l h = 1/2 := by
  cases ν <;> cases h <;> simp [pairWeight, signVal] <;> ring

/-- A product coefficient law averages any function of the first coordinates using only their marginals. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: finite_pair_average_fst
lemma finite_pair_average_fst {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → Bool → Bool → ℝ) (m : ι → Bool → ℝ)
    (hm : ∀ i l, ∑ h : Bool, w i l h = m i l) (F : (ι → Bool) → ℝ) :
    (∑ p : ι → Bool × Bool, (∏ i, w i (p i).1 (p i).2) * F (fun i => (p i).1)) =
      ∑ l : ι → Bool, (∏ i, m i (l i)) * F l := by
  classical
  let e : (ι → Bool × Bool) ≃ (ι → Bool) × (ι → Bool) :=
    { toFun := fun p => (fun i => (p i).1, fun i => (p i).2)
      invFun := fun z i => (z.1 i, z.2 i)
      left_inv := fun p => by rfl
      right_inv := fun z => by rfl }
  trans ∑ z : (ι → Bool) × (ι → Bool), (∏ i, w i (z.1 i) (z.2 i)) * F z.1
  · exact Fintype.sum_equiv e _ _ (fun p => rfl)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  dsimp only
  rw [← Finset.sum_mul, ← Fintype.prod_sum]
  simp_rw [hm]

/-- A product coefficient law averages any function of the second coordinates using only their marginals. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: finite_pair_average_snd
lemma finite_pair_average_snd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → Bool → Bool → ℝ) (m : ι → Bool → ℝ)
    (hm : ∀ i h, ∑ l : Bool, w i l h = m i h) (F : (ι → Bool) → ℝ) :
    (∑ p : ι → Bool × Bool, (∏ i, w i (p i).1 (p i).2) * F (fun i => (p i).2)) =
      ∑ h : ι → Bool, (∏ i, m i (h i)) * F h := by
  classical
  let e : (ι → Bool × Bool) ≃ (ι → Bool × Bool) :=
    { toFun := fun p i => ((p i).2, (p i).1)
      invFun := fun p i => ((p i).2, (p i).1)
      left_inv := fun p => by rfl
      right_inv := fun p => by rfl }
  trans ∑ p : ι → Bool × Bool, (∏ i, w i (p i).2 (p i).1) * F (fun i => (p i).1)
  · exact Fintype.sum_equiv e _ _ (fun p => rfl)
  exact finite_pair_average_fst (fun i l h => w i h l) m hm F

/-- Disclosure fixes the revealed propensity signs; all unrevealed propensity signs remain independent and fair. [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_fst_average
lemma conditionalPairWeight_fst_average (ν : Bool) (K M : ℕ)
    (σ : Fin (M / 2) → Bool) (δ : Disclosure K) (F : (Fin (K + 1) → Bool) → ℝ) :
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p * F (fun i => (p i).1)) =
      ∑ l : Fin (K + 1) → Bool,
        (∏ i, match δ i with
          | some q => if l i = q.1 then (1:ℝ) else 0
          | none => 1/2) * F l := by
  classical
  unfold conditionalPairWeight
  refine finite_pair_average_fst
    (fun i l h => match δ i with
      | some q => if (l,h) = q then (1:ℝ) else 0
      | none => pairWeight ν (coarseTent M σ ((i:ℝ)/K)) l h)
    (fun i l => match δ i with
      | some q => if l = q.1 then (1:ℝ) else 0
      | none => 1/2) ?_ F
  intro i l
  cases δ i with
  | none => exact pairWeight_fst_sum _ _ _
  | some q =>
    rcases q with ⟨l', h'⟩
    cases l <;> cases l' <;> cases h' <;> simp

/-- Disclosure fixes the revealed outcome signs; all unrevealed outcome signs remain independent and fair. [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_snd_average
lemma conditionalPairWeight_snd_average (ν : Bool) (K M : ℕ)
    (σ : Fin (M / 2) → Bool) (δ : Disclosure K) (F : (Fin (K + 1) → Bool) → ℝ) :
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p * F (fun i => (p i).2)) =
      ∑ h : Fin (K + 1) → Bool,
        (∏ i, match δ i with
          | some q => if h i = q.2 then (1:ℝ) else 0
          | none => 1/2) * F h := by
  classical
  unfold conditionalPairWeight
  refine finite_pair_average_snd
    (fun i l h => match δ i with
      | some q => if (l,h) = q then (1:ℝ) else 0
      | none => pairWeight ν (coarseTent M σ ((i:ℝ)/K)) l h)
    (fun i h => match δ i with
      | some q => if h = q.2 then (1:ℝ) else 0
      | none => 1/2) ?_ F
  intro i h
  cases δ i with
  | none => exact pairWeight_snd_sum _ _ _
  | some q =>
    rcases q with ⟨l', h'⟩
    cases h <;> cases l' <;> cases h' <;> simp

/-- A component likelihood depending only on propensity coefficients agrees under every coarse sign and prior. This statement assumes [the hF condition](hyp:hF). [This is the stated conclusion](goal). -/
-- @node: componentDensity_of_fst_likelihood
lemma componentDensity_of_fst_likelihood (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n)
    (F : (Fin (K + 1) → Bool) → ℝ)
    (hF : ∀ ν sign p, (∏ i ∈ C,
      labelDensity ν K M a u ((fun _ => sign), p) (aug.1 i) (aug.2.1 i) (labels i)) =
      F (fun i => (p i).1)) (ν sign : Bool) :
    componentDensity ν sign n K M a u aug C labels = nullComponent n K M a u aug C labels := by
  unfold nullComponent componentDensity
  simp_rw [hF]
  rw [conditionalPairWeight_fst_average, conditionalPairWeight_fst_average]

/-- A component likelihood depending only on outcome coefficients agrees under every coarse sign and prior. This statement assumes [the hF condition](hyp:hF). [This is the stated conclusion](goal). -/
-- @node: componentDensity_of_snd_likelihood
lemma componentDensity_of_snd_likelihood (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n)
    (F : (Fin (K + 1) → Bool) → ℝ)
    (hF : ∀ ν sign p, (∏ i ∈ C,
      labelDensity ν K M a u ((fun _ => sign), p) (aug.1 i) (aug.2.1 i) (labels i)) =
      F (fun i => (p i).2)) (ν sign : Bool) :
    componentDensity ν sign n K M a u aug C labels = nullComponent n K M a u aug C labels := by
  unfold nullComponent componentDensity
  simp_rw [hF]
  rw [conditionalPairWeight_snd_average, conditionalPairWeight_snd_average]

/-- Full treatment-label likelihoods of a component without marks have exactly the common propensity marginal. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: componentDensity_no_marks
lemma componentDensity_no_marks (ν sign : Bool) (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n)
    (hm : ∀ i ∈ C, aug.2.1 i = false) :
    componentDensity ν sign n K M a u aug C labels = nullComponent n K M a u aug C labels := by
  apply componentDensity_of_fst_likelihood n K M a u aug C labels
    (fun l => ∏ i ∈ C, (1+signVal (labels i).1*(a*frameField K (fun j => signVal (l j)) (aug.1 i))))
    _ ν sign
  intro ν sign p
  apply Finset.prod_congr rfl
  intro i hi
  simp only [labelDensity, hm i hi, Bool.false_eq_true, if_false, copulaXi]

/-- With zero outcome amplitude every component law uses only the common propensity-coordinate marginal. [This is the stated conclusion](goal). -/
-- @node: componentDensity_zero_outcome_amplitude
lemma componentDensity_zero_outcome_amplitude (ν sign : Bool) (n K M : ℕ) (a : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    componentDensity ν sign n K M a 0 aug C labels = nullComponent n K M a 0 aug C labels := by
  apply componentDensity_of_fst_likelihood n K M a 0 aug C labels
    (fun l => ∏ i ∈ C, (1+signVal (labels i).1*(a*frameField K (fun j => signVal (l j)) (aug.1 i))))
    _ ν sign
  intro ν sign p
  apply Finset.prod_congr rfl
  intro i hi
  simp [labelDensity, copulaXi, copulaUpsilon, copulaZeta, copulaT]

/-- With zero propensity amplitude every component law uses only the common outcome-coordinate marginal. [This is the stated conclusion](goal). -/
-- @node: componentDensity_zero_propensity_amplitude
lemma componentDensity_zero_propensity_amplitude (ν sign : Bool) (n K M : ℕ) (u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    componentDensity ν sign n K M 0 u aug C labels = nullComponent n K M 0 u aug C labels := by
  apply componentDensity_of_snd_likelihood n K M 0 u aug C labels
    (fun h => ∏ i ∈ C, if aug.2.1 i then
      1+signVal (labels i).2*(u*frameField K (fun j => signVal (h j)) (aug.1 i)) else 1)
    _ ν sign
  intro ν sign p
  apply Finset.prod_congr rfl
  intro i hi
  simp [labelDensity, copulaXi, copulaUpsilon, copulaZeta, copulaT]

/-- Both discrepancies vanish identically on either amplitude axis, as required for integrating the mixed derivatives. [This is the stated conclusion](goal). -/
-- @node: component_discrepancies_on_axes
lemma component_discrepancies_on_axes (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    evenDiscrepancy n K M a 0 aug C labels = 0 ∧
    oddDiscrepancy n K M a 0 aug C labels = 0 ∧
    evenDiscrepancy n K M 0 u aug C labels = 0 ∧
    oddDiscrepancy n K M 0 u aug C labels = 0 := by
  unfold evenDiscrepancy oddDiscrepancy averageComponent
  rw [componentDensity_zero_outcome_amplitude, componentDensity_zero_outcome_amplitude,
    componentDensity_zero_propensity_amplitude, componentDensity_zero_propensity_amplitude]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Absence of marked records cancels both discrepancies without discarding the treatment labels. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: component_discrepancies_no_marks
lemma component_discrepancies_no_marks (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n)
    (hm : (C.filter (fun i => aug.2.1 i)).card = 0) :
    evenDiscrepancy n K M a u aug C labels = 0 ∧
    oddDiscrepancy n K M a u aug C labels = 0 := by
  have hnone : ∀ i ∈ C, aug.2.1 i = false := by
    intro i hi
    have hz : C.filter (fun i => aug.2.1 i) = ∅ := Finset.card_eq_zero.mp hm
    by_cases hb : aug.2.1 i = true
    · have : i ∈ C.filter (fun i => aug.2.1 i) := Finset.mem_filter.mpr ⟨hi, hb⟩
      rw [hz] at this
      exact False.elim (by simp at this)
    · exact Bool.eq_false_iff.mpr hb
  unfold evenDiscrepancy oddDiscrepancy averageComponent
  rw [componentDensity_no_marks true true n K M a u aug C labels hnone,
    componentDensity_no_marks true false n K M a u aug C labels hnone]
  constructor <;> ring

/-- A component with no marks contributes zero to both chi-square activities. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: component_activities_no_marks
lemma component_activities_no_marks (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n))
    (hm : (C.filter (fun i => aug.2.1 i)).card = 0) :
    componentEvenActivity n K M a u aug C = 0 ∧
    componentOddActivity n K M a u aug C = 0 := by
  have hz := fun labels => component_discrepancies_no_marks n K M a u aug C labels hm
  constructor
  · simp only [componentEvenActivity, (hz _).1, zero_pow (by decide : 2 ≠ 0),
      zero_div, Finset.sum_const_zero, mul_zero]
  · simp only [componentOddActivity, (hz _).2, zero_pow (by decide : 2 ≠ 0),
      zero_div, Finset.sum_const_zero, mul_zero]

/-- Both chi-square activities vanish on the amplitude axes before any derivative estimate is invoked. [This is the stated conclusion](goal). -/
-- @node: component_activities_on_axes
lemma component_activities_on_axes (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) :
    componentEvenActivity n K M a 0 aug C = 0 ∧
    componentOddActivity n K M a 0 aug C = 0 ∧
    componentEvenActivity n K M 0 u aug C = 0 ∧
    componentOddActivity n K M 0 u aug C = 0 := by
  have hz := fun labels => component_discrepancies_on_axes n K M a u aug C labels
  constructor
  · simp only [componentEvenActivity, (hz _).1, zero_pow (by decide : 2 ≠ 0),
      zero_div, Finset.sum_const_zero, mul_zero]
  constructor
  · simp only [componentOddActivity, (hz _).2.1, zero_pow (by decide : 2 ≠ 0),
      zero_div, Finset.sum_const_zero, mul_zero]
  constructor
  · simp only [componentEvenActivity, (hz _).2.2.1, zero_pow (by decide : 2 ≠ 0),
      zero_div, Finset.sum_const_zero, mul_zero]
  · simp only [componentOddActivity, (hz _).2.2.2, zero_pow (by decide : 2 ≠ 0),
      zero_div, Finset.sum_const_zero, mul_zero]

end CausalSmith.Stat.FinitepHomogeneityDensegamma

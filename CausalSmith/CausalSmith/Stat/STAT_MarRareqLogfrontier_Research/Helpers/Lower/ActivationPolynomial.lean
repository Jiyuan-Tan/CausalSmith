module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.IntervalPriors
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! The conditional rare-cell likelihood in equation (6) is polynomial,
with degree at most the number of revealed activations. Matching moments
therefore identifies its prior averages below the activation cutoff. -/

@[expose] public section

open MeasureTheory Polynomial

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- For [the specified inputs and assumptions](hyp:H,a,flag,arrival,one), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: activationRareOutcomePolynomial
noncomputable def activationRareOutcomePolynomial (H : ℝ)
    (a flag arrival one : Bool) : Polynomial ℝ :=
  if !flag then if !arrival && !one then 1 else 0
  else if one then if arrival && a then C H⁻¹ else 0
  else if arrival then
    if a then C H⁻¹ * (X - 1) else C H⁻¹ * X
  else 1 - C H⁻¹ * X

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,x,a,flag,arrival,one,hx), [the stated mathematical conclusion holds](goal). -/
-- @node: activationRareOutcomePolynomial_eval
lemma activationRareOutcomePolynomial_eval (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (x : Fin d) (a flag arrival one : Bool)
    (hx : x.val < rareCount η n d q) :
    (activationRareOutcomePolynomial (lowerEndpoint n q) a flag arrival one).eval (z x) =
      augmentedOutcomeWeight η n d q z x a flag arrival one := by
  cases a <;> cases flag <;> cases arrival <;> cases one <;>
    simp only [activationRareOutcomePolynomial, augmentedOutcomeWeight, lowerCellZ, hx,
      Bool.not_false, Bool.not_true, Bool.false_eq_true,
      Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and,
      if_true, if_false, eval_zero, eval_one, eval_C, eval_mul, eval_sub, eval_X]
      <;> simp [div_eq_mul_inv, mul_comm]

/-- Given [the specified inputs and assumptions](hyp:H,a,flag,arrival,one), [the stated mathematical conclusion holds](goal). -/
-- @node: activationRareOutcomePolynomial_natDegree
lemma activationRareOutcomePolynomial_natDegree (H : ℝ)
    (a flag arrival one : Bool) :
    (activationRareOutcomePolynomial H a flag arrival one).natDegree ≤
      if flag then 1 else 0 := by
  have hmul : (C H⁻¹ * X : Polynomial ℝ).natDegree ≤ 1 := by
    simpa using (natDegree_mul_le (p := (C H⁻¹ : Polynomial ℝ)) (q := X))
  have hsub : (X - 1 : Polynomial ℝ).natDegree ≤ 1 := by
    simpa using (natDegree_sub_le (X : Polynomial ℝ) 1)
  have hmulsub : (C H⁻¹ * (X - 1) : Polynomial ℝ).natDegree ≤ 1 := by
    exact (natDegree_mul_le (p := C H⁻¹) (q := X - 1)).trans (by simpa using hsub)
  have hlast : (1 - C H⁻¹ * X : Polynomial ℝ).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) hmul)
  cases a <;> cases flag <;> cases arrival <;> cases one <;>
    simp [activationRareOutcomePolynomial] <;> assumption

/-- For [the specified inputs and assumptions](hyp:ι,s,H,a,flag,arrival,one), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: activationRareCellPolynomial
noncomputable def activationRareCellPolynomial {ι : Type*} (s : Finset ι)
    (H : ℝ) (a flag arrival one : ι → Bool) : Polynomial ℝ :=
  ∏ i ∈ s, activationRareOutcomePolynomial H (a i) (flag i) (arrival i) (one i)

/-- Given [the specified inputs and assumptions](hyp:ι,s,H,a,flag,arrival,one), [the stated mathematical conclusion holds](goal). -/
-- @node: activationRareCellPolynomial_natDegree
lemma activationRareCellPolynomial_natDegree {ι : Type*} (s : Finset ι)
    (H : ℝ) (a flag arrival one : ι → Bool) :
    (activationRareCellPolynomial s H a flag arrival one).natDegree ≤
      ∑ i ∈ s, if flag i then 1 else 0 := by
  apply (natDegree_prod_le s _).trans
  exact Finset.sum_le_sum (fun i _ =>
    activationRareOutcomePolynomial_natDegree H (a i) (flag i) (arrival i) (one i))

/-- Given [the specified inputs and assumptions](hyp:ι,s,η,n,d,q,z,x,a,flag,arrival,one,hx), [the stated mathematical conclusion holds](goal). -/
-- @node: activationRareCellPolynomial_eval
lemma activationRareCellPolynomial_eval {ι : Type*} (s : Finset ι)
    (η : ℝ) (n d : ℕ) (q : ℝ) (z : Fin d → ℝ) (x : Fin d)
    (a flag arrival one : ι → Bool) (hx : x.val < rareCount η n d q) :
    (activationRareCellPolynomial s (lowerEndpoint n q) a flag arrival one).eval (z x) =
      ∏ i ∈ s, augmentedOutcomeWeight η n d q z x (a i) (flag i) (arrival i) (one i) := by
  simp only [activationRareCellPolynomial, eval_prod]
  exact Finset.prod_congr rfl (fun i _ =>
    activationRareOutcomePolynomial_eval η n d q z x _ _ _ _ hx)

/-- Given [the specified inputs and assumptions](hyp:H,π₀,π₁,h₀,h₁,K,hm,p,hp), [the stated mathematical conclusion holds](goal). -/
-- @node: finiteReciprocalPrior_polynomial_integral_eq
lemma finiteReciprocalPrior_polynomial_integral_eq {H : ℝ} {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior H π₀) (h₁ : FiniteReciprocalPrior H π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ K) :
    (∫ z, p.eval z ∂π₀) = ∫ z, p.eval z ∂π₁ := by
  simp_rw [eval_eq_sum_range]
  rw [integral_finsetSum _ (fun i _ => finiteReciprocalPrior_integrable h₀ _),
    integral_finsetSum _ (fun i _ => finiteReciprocalPrior_integrable h₁ _)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, integral_const_mul, hm i]
  exact (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hp

/-- Given [the specified inputs and assumptions](hyp:ι,s,H,π₀,π₁,h₀,h₁,K,hm,a,flag,arrival,one,hcount), [the stated mathematical conclusion holds](goal). -/
-- @node: activationRareCellPolynomial_integral_eq
lemma activationRareCellPolynomial_integral_eq {ι : Type*} (s : Finset ι)
    {H : ℝ} {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior H π₀) (h₁ : FiniteReciprocalPrior H π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (a flag arrival one : ι → Bool)
    (hcount : (∑ i ∈ s, if flag i then 1 else 0) ≤ K) :
    (∫ z, (activationRareCellPolynomial s H a flag arrival one).eval z ∂π₀) =
      ∫ z, (activationRareCellPolynomial s H a flag arrival one).eval z ∂π₁ := by
  exact finiteReciprocalPrior_polynomial_integral_eq h₀ h₁ K hm _
    ((activationRareCellPolynomial_natDegree s H a flag arrival one).trans hcount)

/-- Given [the specified inputs and assumptions](hyp:ι,s,H,π₀,π₁,h₀,h₁,K,hm,M,hM,j,j',a,flag,arrival,one,hcount), [the stated mathematical conclusion holds](goal). -/
-- @node: activationRareCellPolynomial_grid_integral_eq
lemma activationRareCellPolynomial_grid_integral_eq {ι : Type*} (s : Finset ι)
    {H : ℝ} {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior H π₀) (h₁ : FiniteReciprocalPrior H π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (M : ℕ) (hM : 1 ≤ M) (j j' : Fin (M + 1))
    (a flag arrival one : ι → Bool)
    (hcount : (∑ i ∈ s, if flag i then 1 else 0) ≤ K) :
    (∫ z, (activationRareCellPolynomial s H a flag arrival one).eval z
      ∂intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M)) =
    ∫ z, (activationRareCellPolynomial s H a flag arrival one).eval z
      ∂intervalInterpolatedPrior π₀ π₁ ((j' : ℝ) / M) := by
  have hgrid := intervalInterpolatedPrior_grid h₀ h₁ K hm M hM
  exact activationRareCellPolynomial_integral_eq s (hgrid j).1 (hgrid j').1 K
    ((hgrid j).2.1 j') a flag arrival one hcount

end CausalSmith.Stat.MarRareqLogfrontier

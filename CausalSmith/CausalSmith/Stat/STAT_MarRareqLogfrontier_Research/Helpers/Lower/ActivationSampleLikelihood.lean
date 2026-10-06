module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationProduct

/-! Full augmented sample likelihood cancellation below the activation cutoff
in equation (6). Reservoir and zero-mass cells contribute constant polynomials;
only rare cells consume the matched-moment budget. -/

@[expose] public section

open MeasureTheory Polynomial

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- For [the specified inputs and assumptions](hyp:η,n,d,q,x,a,flag,arrival,one), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: activationOutcomePolynomial
noncomputable def activationOutcomePolynomial (η : ℝ) (n d : ℕ) (q : ℝ)
    (x : Fin d) (a flag arrival one : Bool) : Polynomial ℝ :=
  if x.val < rareCount η n d q then
    activationRareOutcomePolynomial (lowerEndpoint n q) a flag arrival one
  else C (augmentedOutcomeWeight η n d q (fun _ => 0) x a flag arrival one)

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,x,a,flag,arrival,one), [the stated mathematical conclusion holds](goal). -/
-- @node: activationOutcomePolynomial_eval
lemma activationOutcomePolynomial_eval (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (x : Fin d) (a flag arrival one : Bool) :
    (activationOutcomePolynomial η n d q x a flag arrival one).eval (z x) =
      augmentedOutcomeWeight η n d q z x a flag arrival one := by
  by_cases hx : x.val < rareCount η n d q
  · simp only [activationOutcomePolynomial, hx, if_true]
    exact activationRareOutcomePolynomial_eval η n d q z x a flag arrival one hx
  · cases a <;> cases flag <;> cases arrival <;> cases one <;>
      simp [activationOutcomePolynomial, augmentedOutcomeWeight, lowerCellZ, hx]

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,x,a,flag,arrival,one), [the stated mathematical conclusion holds](goal). -/
-- @node: activationOutcomePolynomial_natDegree
lemma activationOutcomePolynomial_natDegree (η : ℝ) (n d : ℕ) (q : ℝ)
    (x : Fin d) (a flag arrival one : Bool) :
    (activationOutcomePolynomial η n d q x a flag arrival one).natDegree ≤
      if x.val < rareCount η n d q then (if flag then 1 else 0) else 0 := by
  by_cases hx : x.val < rareCount η n d q
  · simp only [activationOutcomePolynomial, hx, if_true]
    exact activationRareOutcomePolynomial_natDegree _ a flag arrival one
  · simp [activationOutcomePolynomial, hx]

/-- Given [the specified inputs and assumptions](hyp:ι,s,η,n,d,q,cell,a,flag,arrival,one,z), [the stated mathematical conclusion holds](goal). -/
-- @node: activationSampleOutcome_factorization
lemma activationSampleOutcome_factorization {ι : Type*} (s : Finset ι)
    (η : ℝ) (n d : ℕ) (q : ℝ) (cell : ι → Fin d)
    (a flag arrival one : ι → Bool) (z : Fin d → ℝ) :
    (∏ i ∈ s, augmentedOutcomeWeight η n d q z (cell i)
      (a i) (flag i) (arrival i) (one i)) =
      ∏ x : Fin d, (∏ i ∈ s.filter (fun i => cell i = x),
        activationOutcomePolynomial η n d q x (a i) (flag i)
          (arrival i) (one i)).eval (z x) := by
  classical
  rw [← Finset.prod_fiberwise s cell]
  apply Finset.prod_congr rfl
  intro x _
  rw [eval_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]
  exact (activationOutcomePolynomial_eval η n d q z x _ _ _ _).symm

/-- Given [the specified inputs and assumptions](hyp:ι,s,η,n,d,q,cell,π₀,π₁,h₀,h₁,K,hm,a,flag,arrival,one,hcount), [the stated mathematical conclusion holds](goal). -/
-- @node: activationSampleOutcome_integral_eq
lemma activationSampleOutcome_integral_eq {ι : Type*} (s : Finset ι)
    (η : ℝ) (n d : ℕ) (q : ℝ) (cell : ι → Fin d)
    {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (a flag arrival one : ι → Bool)
    (hcount : ∀ x : Fin d, x.val < rareCount η n d q →
      (∑ i ∈ s.filter (fun i => cell i = x), if flag i then 1 else 0) ≤ K) :
    (∫ z, ∏ i ∈ s, augmentedOutcomeWeight η n d q z (cell i)
      (a i) (flag i) (arrival i) (one i) ∂Measure.pi (fun _ : Fin d => π₀)) =
      ∫ z, ∏ i ∈ s, augmentedOutcomeWeight η n d q z (cell i)
        (a i) (flag i) (arrival i) (one i) ∂Measure.pi (fun _ : Fin d => π₁) := by
  classical
  simp_rw [activationSampleOutcome_factorization]
  apply finiteReciprocalPrior_product_polynomial_integral_eq h₀ h₁ K hm
  intro x
  apply (natDegree_prod_le _ _).trans
  by_cases hx : x.val < rareCount η n d q
  · exact (Finset.sum_le_sum (fun i _ => by
      simpa only [hx, if_true] using
        activationOutcomePolynomial_natDegree η n d q x (a i) (flag i)
          (arrival i) (one i))).trans (hcount x hx)
  · have hzero : (∑ i ∈ s.filter (fun i => cell i = x),
        (activationOutcomePolynomial η n d q x (a i) (flag i)
          (arrival i) (one i)).natDegree) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [activationOutcomePolynomial, hx]
    rw [hzero]
    exact Nat.zero_le K

/-- Given [the specified inputs and assumptions](hyp:ι,s,η,n,d,q,cell,π₀,π₁,h₀,h₁,K,hm,a,flag,arrival,one,hcount), [the stated mathematical conclusion holds](goal). -/
-- @node: activationSampleWeight_integral_eq
lemma activationSampleWeight_integral_eq {ι : Type*} (s : Finset ι)
    (η : ℝ) (n d : ℕ) (q : ℝ) (cell : ι → Fin d)
    {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (a flag arrival one : ι → Bool)
    (hcount : ∀ x : Fin d, x.val < rareCount η n d q →
      (∑ i ∈ s.filter (fun i => cell i = x), if flag i then 1 else 0) ≤ K) :
    (∫ z, ∏ i ∈ s, (baselineMass η n d q (cell i) / 2 *
      bernWeight (q * lowerEndpoint n q) (flag i) *
      augmentedOutcomeWeight η n d q z (cell i) (a i) (flag i) (arrival i) (one i))
      ∂Measure.pi (fun _ : Fin d => π₀)) =
    ∫ z, ∏ i ∈ s, (baselineMass η n d q (cell i) / 2 *
      bernWeight (q * lowerEndpoint n q) (flag i) *
      augmentedOutcomeWeight η n d q z (cell i) (a i) (flag i) (arrival i) (one i))
      ∂Measure.pi (fun _ : Fin d => π₁) := by
  simp_rw [Finset.prod_mul_distrib]
  rw [integral_const_mul, integral_const_mul]
  rw [activationSampleOutcome_integral_eq s η n d q cell h₀ h₁ K hm
    a flag arrival one hcount]

/-- Given [the specified inputs and assumptions](hyp:ι,s,η,n,d,q,cell,π₀,π₁,h₀,h₁,K,hm,M,hM,j,j',a,flag,arrival,one,hcount), [the stated mathematical conclusion holds](goal). -/
-- @node: activationSampleWeight_grid_integral_eq
lemma activationSampleWeight_grid_integral_eq {ι : Type*} (s : Finset ι)
    (η : ℝ) (n d : ℕ) (q : ℝ) (cell : ι → Fin d)
    {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (M : ℕ) (hM : 1 ≤ M) (j j' : Fin (M + 1))
    (a flag arrival one : ι → Bool)
    (hcount : ∀ x : Fin d, x.val < rareCount η n d q →
      (∑ i ∈ s.filter (fun i => cell i = x), if flag i then 1 else 0) ≤ K) :
    (∫ z, ∏ i ∈ s, (baselineMass η n d q (cell i) / 2 *
      bernWeight (q * lowerEndpoint n q) (flag i) *
      augmentedOutcomeWeight η n d q z (cell i) (a i) (flag i) (arrival i) (one i))
      ∂Measure.pi (fun _ : Fin d => intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M))) =
    ∫ z, ∏ i ∈ s, (baselineMass η n d q (cell i) / 2 *
      bernWeight (q * lowerEndpoint n q) (flag i) *
      augmentedOutcomeWeight η n d q z (cell i) (a i) (flag i) (arrival i) (one i))
      ∂Measure.pi (fun _ : Fin d => intervalInterpolatedPrior π₀ π₁ ((j' : ℝ) / M)) := by
  have hgrid := intervalInterpolatedPrior_grid h₀ h₁ K hm M hM
  exact activationSampleWeight_integral_eq s η n d q cell (hgrid j).1 (hgrid j').1 K
    ((hgrid j).2.1 j') a flag arrival one hcount

end CausalSmith.Stat.MarRareqLogfrontier

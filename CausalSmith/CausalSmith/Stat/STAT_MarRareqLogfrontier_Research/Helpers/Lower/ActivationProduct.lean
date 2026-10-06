module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationPolynomial
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationPriorTarget
public import Mathlib.MeasureTheory.Integral.Pi

/-! Joint rare-cell likelihood cancellation under independent moment-matched
priors, the exact-cancellation step preceding the tail bound in equation (6). -/

public section

open MeasureTheory Polynomial

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:J,H,π₀,π₁,h₀,h₁,K,hm,p,hp), [the stated mathematical conclusion holds](goal). -/
-- @node: finiteReciprocalPrior_product_polynomial_integral_eq
lemma finiteReciprocalPrior_product_polynomial_integral_eq
    {J : ℕ} {H : ℝ} {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior H π₀) (h₁ : FiniteReciprocalPrior H π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (p : Fin J → Polynomial ℝ) (hp : ∀ x, (p x).natDegree ≤ K) :
    (∫ z, ∏ x, (p x).eval (z x) ∂Measure.pi (fun _ : Fin J => π₀)) =
      ∫ z, ∏ x, (p x).eval (z x) ∂Measure.pi (fun _ : Fin J => π₁) := by
  let := h₀.1
  let := h₁.1
  rw [integral_fintype_prod_eq_prod (fun x t => (p x).eval t),
    integral_fintype_prod_eq_prod (fun x t => (p x).eval t)]
  exact Finset.prod_congr rfl (fun x _ =>
    finiteReciprocalPrior_polynomial_integral_eq h₀ h₁ K hm (p x) (hp x))

/-- Given [the specified inputs and assumptions](hyp:ι,s,J,cell,H,a,flag,arrival,one,z), [the stated mathematical conclusion holds](goal). -/
-- @node: activationRareRecords_factorization
lemma activationRareRecords_factorization {ι : Type*} (s : Finset ι)
    {J : ℕ} (cell : ι → Fin J) (H : ℝ)
    (a flag arrival one : ι → Bool) (z : Fin J → ℝ) :
    (∏ i ∈ s, (activationRareOutcomePolynomial H (a i) (flag i)
      (arrival i) (one i)).eval (z (cell i))) =
      ∏ x : Fin J, (activationRareCellPolynomial (s.filter (fun i => cell i = x))
        H a flag arrival one).eval (z x) := by
  classical
  rw [← Finset.prod_fiberwise s cell]
  apply Finset.prod_congr rfl
  intro x _
  simp only [activationRareCellPolynomial, eval_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- Given [the specified inputs and assumptions](hyp:ι,s,J,cell,H,π₀,π₁,h₀,h₁,K,hm,a,flag,arrival,one,hcount), [the stated mathematical conclusion holds](goal). -/
-- @node: activationRareRecords_integral_eq
lemma activationRareRecords_integral_eq {ι : Type*} (s : Finset ι)
    {J : ℕ} (cell : ι → Fin J) {H : ℝ} {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior H π₀) (h₁ : FiniteReciprocalPrior H π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (a flag arrival one : ι → Bool)
    (hcount : ∀ x, (∑ i ∈ s.filter (fun i => cell i = x), if flag i then 1 else 0) ≤ K) :
    (∫ z, ∏ i ∈ s, (activationRareOutcomePolynomial H (a i) (flag i)
      (arrival i) (one i)).eval (z (cell i)) ∂Measure.pi (fun _ : Fin J => π₀)) =
      ∫ z, ∏ i ∈ s, (activationRareOutcomePolynomial H (a i) (flag i)
        (arrival i) (one i)).eval (z (cell i)) ∂Measure.pi (fun _ : Fin J => π₁) := by
  classical
  simp_rw [activationRareRecords_factorization]
  apply finiteReciprocalPrior_product_polynomial_integral_eq h₀ h₁ K hm
  intro x
  exact (activationRareCellPolynomial_natDegree _ H a flag arrival one).trans (hcount x)

/-- Given [the specified inputs and assumptions](hyp:ι,s,J,cell,H,π₀,π₁,h₀,h₁,K,hm,M,hM,j,j',a,flag,arrival,one,hcount), [the stated mathematical conclusion holds](goal). -/
-- @node: activationRareRecords_grid_integral_eq
lemma activationRareRecords_grid_integral_eq {ι : Type*} (s : Finset ι)
    {J : ℕ} (cell : ι → Fin J) {H : ℝ} {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior H π₀) (h₁ : FiniteReciprocalPrior H π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (M : ℕ) (hM : 1 ≤ M) (j j' : Fin (M + 1))
    (a flag arrival one : ι → Bool)
    (hcount : ∀ x, (∑ i ∈ s.filter (fun i => cell i = x), if flag i then 1 else 0) ≤ K) :
    (∫ z, ∏ i ∈ s, (activationRareOutcomePolynomial H (a i) (flag i)
      (arrival i) (one i)).eval (z (cell i))
        ∂Measure.pi (fun _ : Fin J => intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M))) =
      ∫ z, ∏ i ∈ s, (activationRareOutcomePolynomial H (a i) (flag i)
        (arrival i) (one i)).eval (z (cell i))
        ∂Measure.pi (fun _ : Fin J => intervalInterpolatedPrior π₀ π₁ ((j' : ℝ) / M)) := by
  have hgrid := intervalInterpolatedPrior_grid h₀ h₁ K hm M hM
  exact activationRareRecords_integral_eq s cell (hgrid j).1 (hgrid j').1 K
    ((hgrid j).2.1 j') a flag arrival one hcount

/-- Given [the specified inputs and assumptions](hyp:ι,s,η,n,d,q,cell,a,flag,arrival,one,z), [the stated mathematical conclusion holds](goal). -/
-- @node: activationRareRecords_augmented_eq
lemma activationRareRecords_augmented_eq {ι : Type*} (s : Finset ι)
    (η : ℝ) (n d : ℕ) (q : ℝ)
    (cell : ι → Fin (rareCount η n d q))
    (a flag arrival one : ι → Bool) (z : Fin (rareCount η n d q) → ℝ) :
    (∏ i ∈ s, (activationRareOutcomePolynomial (lowerEndpoint n q)
      (a i) (flag i) (arrival i) (one i)).eval (z (cell i))) =
      ∏ i ∈ s, augmentedOutcomeWeight η n d q (activationExtendRare η n d q z)
        ((cell i).castLE ((min_le_left _ _).trans (Nat.sub_le d 1)))
        (a i) (flag i) (arrival i) (one i) := by
  apply Finset.prod_congr rfl
  intro i _
  have heval := activationRareOutcomePolynomial_eval η n d q
    (activationExtendRare η n d q z)
    ((cell i).castLE ((min_le_left _ _).trans (Nat.sub_le d 1)))
    (a i) (flag i) (arrival i) (one i) (cell i).isLt
  rw [activationExtendRare_eval] at heval
  exact heval

/-- Given [the specified inputs and assumptions](hyp:ι,s,η,n,d,q,cell,π₀,π₁,h₀,h₁,K,hm,M,hM,j,j',a,flag,arrival,one,hcount), [the stated mathematical conclusion holds](goal). -/
-- @node: activationRareRecords_augmented_grid_integral_eq
lemma activationRareRecords_augmented_grid_integral_eq {ι : Type*} (s : Finset ι)
    (η : ℝ) (n d : ℕ) (q : ℝ)
    (cell : ι → Fin (rareCount η n d q)) {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (K : ℕ) (hm : ∀ v : ℕ, v ≤ K → (∫ z, z ^ v ∂π₀) = ∫ z, z ^ v ∂π₁)
    (M : ℕ) (hM : 1 ≤ M) (j j' : Fin (M + 1))
    (a flag arrival one : ι → Bool)
    (hcount : ∀ x, (∑ i ∈ s.filter (fun i => cell i = x), if flag i then 1 else 0) ≤ K) :
    (∫ z, ∏ i ∈ s, augmentedOutcomeWeight η n d q (activationExtendRare η n d q z)
      ((cell i).castLE ((min_le_left _ _).trans (Nat.sub_le d 1)))
      (a i) (flag i) (arrival i) (one i)
      ∂Measure.pi (fun _ : Fin (rareCount η n d q) =>
        intervalInterpolatedPrior π₀ π₁ ((j : ℝ) / M))) =
      ∫ z, ∏ i ∈ s, augmentedOutcomeWeight η n d q (activationExtendRare η n d q z)
        ((cell i).castLE ((min_le_left _ _).trans (Nat.sub_le d 1)))
        (a i) (flag i) (arrival i) (one i)
        ∂Measure.pi (fun _ : Fin (rareCount η n d q) =>
          intervalInterpolatedPrior π₀ π₁ ((j' : ℝ) / M)) := by
  simp_rw [← activationRareRecords_augmented_eq]
  exact activationRareRecords_grid_integral_eq s cell h₀ h₁ K hm M hM j j'
    a flag arrival one hcount

end CausalSmith.Stat.MarRareqLogfrontier

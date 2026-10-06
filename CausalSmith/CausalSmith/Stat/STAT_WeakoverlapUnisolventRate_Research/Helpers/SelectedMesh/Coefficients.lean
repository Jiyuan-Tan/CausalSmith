module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Template
public import Mathlib.Algebra.Order.Chebyshev

/-! # Design-fixed coefficient differences -/
@[expose] public section
namespace CausalSmith.Stat.WeakOverlap
open scoped Classical

/-- The treated-cell count depends only on covariates and treatment arms. [For the stated inputs and conditions](hyp:d,n,m,j,ω,ξ,k,ℓ,hdesign), [the asserted conclusion holds](goal). -/
lemma treatedCount_eq_of_design_eq {d n : ℕ} (m j : ℕ)
    (ω ξ : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (ℓ : Fin d → Fin (m + 1))
    (hdesign : ∀ i, (ξ i).1 = (ω i).1 ∧ (ξ i).2.1 = (ω i).2.1) :
    treatedCount m j ξ k ℓ = treatedCount m j ω k ℓ := by
  classical
  unfold treatedCount
  congr 1
  ext i
  obtain ⟨hx, ha⟩ := hdesign i
  simp [hx, ha]

/-- Equal designs give the same equal-cell Gram matrix. [For the stated inputs and conditions](hyp:d,n,m,j,ω,ξ,k,hdesign), [the asserted conclusion holds](goal). -/
lemma gramHat_eq_of_design_eq {d n : ℕ} (m j : ℕ)
    (ω ξ : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (hdesign : ∀ i, (ξ i).1 = (ω i).1 ∧ (ξ i).2.1 = (ω i).2.1) :
    gramHat m j ξ k = gramHat m j ω k := by
  classical
  ext α α'
  unfold gramHat
  apply congrArg (fun z : ℝ => (tensorCount d m : ℝ)⁻¹ * z)
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [treatedCount_eq_of_design_eq m j ω ξ k ℓ hdesign]
  apply congrArg (fun z : ℝ => (treatedCount m j ω k ℓ : ℝ)⁻¹ * z)
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨hx, ha⟩ := hdesign i
  simp [hx, ha]

/-- The change in a response moment is the design-weighted sum of the
observation-wise changes in treated outcomes. [For the stated inputs and conditions](hyp:d,n,m,j,ω,ξ,k,hdesign,α), [the asserted conclusion holds](goal). -/
lemma responseMoment_sub_of_design_eq {d n : ℕ} (m j : ℕ)
    (ω ξ : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (hdesign : ∀ i, (ξ i).1 = (ω i).1 ∧ (ξ i).2.1 = (ω i).2.1)
    (α : MonoIndex d m) :
    (responseMoment m j ξ k - responseMoment m j ω k) α =
      (tensorCount d m : ℝ)⁻¹ *
        ∑ ℓ : Fin d → Fin (m + 1), (treatedCount m j ω k ℓ : ℝ)⁻¹ *
          ∑ i : Fin n, if (ω i).2.1 = true ∧
              (ω i).1 ∈ scaledMicroCell d m j k ℓ then
              monoVec d m (fun a => ((ω i).1 a - cubeCorner d j k a) /
                meshWidth j) α * ((ξ i).2.2 - (ω i).2.2)
            else 0 := by
  classical
  simp only [Pi.sub_apply, responseMoment]
  simp only [treatedCount_eq_of_design_eq m j ω ξ k _ hdesign]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨hx, ha⟩ := hdesign i
  simp only [hx, ha]
  split_ifs <;> ring

/-- At a fixed design, a coefficient difference is the inverse Gram matrix
applied to the difference of response moments. [For the stated inputs and conditions](hyp:d,n,m,j,ω,ξ,k,hdesign), [the asserted conclusion holds](goal). -/
lemma coefHat_sub_of_design_eq {d n : ℕ} (m j : ℕ)
    (ω ξ : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (hdesign : ∀ i, (ξ i).1 = (ω i).1 ∧ (ξ i).2.1 = (ω i).2.1) :
    coefHat m j ξ k - coefHat m j ω k =
      Matrix.mulVec (gramHat m j ω k)⁻¹
        (responseMoment m j ξ k - responseMoment m j ω k) := by
  rw [coefHat, coefHat, gramHat_eq_of_design_eq m j ω ξ k hdesign]
  exact (Matrix.mulVec_sub _ _ _).symm

/-- At a fixed design, each coefficient difference is a finite linear
combination of the treated outcome changes. [For the stated inputs and conditions](hyp:d,n,m,j,ω,ξ,k,hdesign,α), [the asserted conclusion holds](goal). -/
lemma coefHat_sub_coordinate_of_design_eq {d n : ℕ} (m j : ℕ)
    (ω ξ : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (hdesign : ∀ i, (ξ i).1 = (ω i).1 ∧ (ξ i).2.1 = (ω i).2.1)
    (α : MonoIndex d m) :
    (coefHat m j ξ k - coefHat m j ω k) α =
      ∑ α' : MonoIndex d m,
        (gramHat m j ω k)⁻¹ α α' *
          ((tensorCount d m : ℝ)⁻¹ *
            ∑ ℓ : Fin d → Fin (m + 1),
              (treatedCount m j ω k ℓ : ℝ)⁻¹ *
                ∑ i : Fin n, if (ω i).2.1 = true ∧
                    (ω i).1 ∈ scaledMicroCell d m j k ℓ then
                    monoVec d m (fun a => ((ω i).1 a - cubeCorner d j k a) /
                      meshWidth j) α' * ((ξ i).2.2 - (ω i).2.2)
                  else 0) := by
  classical
  rw [coefHat_sub_of_design_eq m j ω ξ k hdesign]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro α' _
  rw [responseMoment_sub_of_design_eq m j ω ξ k hdesign α']

/-- Replacing each outcome by its design-conditional mean isolates the
treated residual in every coefficient coordinate. [For the stated inputs and conditions](hyp:d,n,m,j,ω,mean,k,α), [the asserted conclusion holds](goal). -/
lemma coefHat_sub_conditionalMeanSample_coordinate {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (mean : Fin n → ℝ)
    (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m) :
    (coefHat m j ω k -
      coefHat m j (fun i => ((ω i).1, (ω i).2.1, mean i)) k) α =
      ∑ α' : MonoIndex d m,
        (gramHat m j ω k)⁻¹ α α' *
          ((tensorCount d m : ℝ)⁻¹ *
            ∑ ℓ : Fin d → Fin (m + 1),
              (treatedCount m j ω k ℓ : ℝ)⁻¹ *
                ∑ i : Fin n, if (ω i).2.1 = true ∧
                    (ω i).1 ∈ scaledMicroCell d m j k ℓ then
                    monoVec d m (fun a => ((ω i).1 a - cubeCorner d j k a) /
                      meshWidth j) α' * ((ω i).2.2 - mean i)
                  else 0) := by
  classical
  have hd : ∀ i,
      ((fun i => ((ω i).1, (ω i).2.1, mean i)) i).1 = (ω i).1 ∧
      ((fun i => ((ω i).1, (ω i).2.1, mean i)) i).2.1 = (ω i).2.1 := by
    intro i
    exact ⟨rfl, rfl⟩
  have h := coefHat_sub_coordinate_of_design_eq m j
    (fun i => ((ω i).1, (ω i).2.1, mean i)) ω k hd α
  rw [gramHat_eq_of_design_eq m j _ _ k hd] at h
  simp only [treatedCount_eq_of_design_eq m j _ _ _ _ hd] at h
  exact h

/-- The fixed-design weight of one response in a coefficient coordinate. For [the stated inputs and conditions](hyp:m,j,ω,k,α,i), [the `coefResidualWeight` object being defined](goal). -/
noncomputable def coefResidualWeight {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (α : MonoIndex d m) (i : Fin n) : ℝ :=
  ∑ α' : MonoIndex d m, (gramHat m j ω k)⁻¹ α α' *
    ((tensorCount d m : ℝ)⁻¹ *
      ∑ ℓ : Fin d → Fin (m + 1),
        (treatedCount m j ω k ℓ : ℝ)⁻¹ *
          if (ω i).2.1 = true ∧
              (ω i).1 ∈ scaledMicroCell d m j k ℓ then
            monoVec d m (fun a => ((ω i).1 a - cubeCorner d j k a) /
              meshWidth j) α'
          else 0)

/-- A coefficient residual weight vanishes for an untreated observation. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,α,i,ha), [the asserted conclusion holds](goal). -/
lemma coefResidualWeight_zero_of_untreated {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (α : MonoIndex d m) (i : Fin n)
    (ha : (ω i).2.1 = false) :
    coefResidualWeight m j ω k α i = 0 := by
  simp [coefResidualWeight, ha]

/-- Residual weights are fixed on each fibre of the covariate and arm design. [For the stated inputs and conditions](hyp:d,n,m,j,ω,ξ,k,α,i,hdesign), [the asserted conclusion holds](goal). -/
lemma coefResidualWeight_eq_of_design_eq {d n : ℕ} (m j : ℕ)
    (ω ξ : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (α : MonoIndex d m) (i : Fin n)
    (hdesign : ∀ i, (ξ i).1 = (ω i).1 ∧ (ξ i).2.1 = (ω i).2.1) :
    coefResidualWeight m j ξ k α i = coefResidualWeight m j ω k α i := by
  unfold coefResidualWeight
  rw [gramHat_eq_of_design_eq m j ω ξ k hdesign]
  apply Finset.sum_congr rfl
  intro α' _
  apply congrArg (fun z : ℝ => (gramHat m j ω k)⁻¹ α α' *
    ((tensorCount d m : ℝ)⁻¹ * z))
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [treatedCount_eq_of_design_eq m j ω ξ k ℓ hdesign]
  obtain ⟨hx, ha⟩ := hdesign i
  simp [hx, ha]

/-- A centered coefficient is one observation-wise weighted residual sum.
The weights depend only on the covariates and treatment arms. [For the stated inputs and conditions](hyp:d,n,m,j,ω,mean,k,α), [the asserted conclusion holds](goal). -/
lemma coefHat_sub_conditionalMeanSample_weighted_sum {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (mean : Fin n → ℝ)
    (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m) :
    (coefHat m j ω k -
      coefHat m j (fun i => ((ω i).1, (ω i).2.1, mean i)) k) α =
      ∑ i : Fin n, coefResidualWeight m j ω k α i *
        ((ω i).2.2 - mean i) := by
  classical
  rw [coefHat_sub_conditionalMeanSample_coordinate]
  simp only [coefResidualWeight]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp only [mul_assoc, ite_mul, zero_mul]
  conv_lhs =>
    arg 2
    ext α'
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- On a design fibre, every residual coefficient uses the weights from the
conditioning design, even when the outcomes vary. [For the stated inputs and conditions](hyp:d,n,m,j,ω,ξ,mean,k,α,hdesign), [the asserted conclusion holds](goal). -/
lemma coefHat_sub_conditionalMeanSample_weighted_sum_of_design_eq
    {d n : ℕ} (m j : ℕ)
    (ω ξ : Fin n → Obs d) (mean : Fin n → ℝ)
    (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m)
    (hdesign : ∀ i, (ξ i).1 = (ω i).1 ∧ (ξ i).2.1 = (ω i).2.1) :
    (coefHat m j ξ k -
      coefHat m j (fun i => ((ξ i).1, (ξ i).2.1, mean i)) k) α =
      ∑ i : Fin n, coefResidualWeight m j ω k α i *
        ((ξ i).2.2 - mean i) := by
  rw [coefHat_sub_conditionalMeanSample_weighted_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [coefResidualWeight_eq_of_design_eq m j ω ξ k α i hdesign]

/-- Squared observation weights in one treated microcell cost one inverse
count. This is the counting step in the conditional variance proxy. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,ℓ,c,R,hc), [the asserted conclusion holds](goal). -/
lemma treatedCell_weight_square_le_inverse_count {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (ℓ : Fin d → Fin (m + 1)) (c : Fin n → ℝ) (R : ℝ)
    (hc : ∀ i, (ω i).2.1 = true ∧
        (ω i).1 ∈ scaledMicroCell d m j k ℓ → |c i| ≤ R) :
    (∑ i : Fin n,
        (if (ω i).2.1 = true ∧
            (ω i).1 ∈ scaledMicroCell d m j k ℓ then
          (treatedCount m j ω k ℓ : ℝ)⁻¹ * c i else 0) ^ 2) ≤
      R ^ 2 * (treatedCount m j ω k ℓ : ℝ)⁻¹ := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i =>
    (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ)
  have hcard : S.card = treatedCount m j ω k ℓ := rfl
  by_cases hzero : S.card = 0
  · have hcount0 : treatedCount m j ω k ℓ = 0 := hcard.symm.trans hzero
    simp [hcount0]
  · have hN : (0 : ℝ) < treatedCount m j ω k ℓ := by
      exact_mod_cast Nat.pos_of_ne_zero (hcard ▸ hzero)
    have hbound : ∀ i ∈ S, c i ^ 2 ≤ R ^ 2 := by
      intro i hi
      have hi' : (ω i).2.1 = true ∧
          (ω i).1 ∈ scaledMicroCell d m j k ℓ :=
        (Finset.mem_filter.mp hi).2
      nlinarith [abs_le.mp (hc i hi')]
    have hsum :
        (∑ i : Fin n,
          (if (ω i).2.1 = true ∧
              (ω i).1 ∈ scaledMicroCell d m j k ℓ then
            (treatedCount m j ω k ℓ : ℝ)⁻¹ * c i else 0) ^ 2) =
        ∑ i ∈ S, ((treatedCount m j ω k ℓ : ℝ)⁻¹ * c i) ^ 2 := by
      simp [S, Finset.sum_filter]
    rw [hsum]
    calc
      (∑ i ∈ S, ((treatedCount m j ω k ℓ : ℝ)⁻¹ * c i) ^ 2) ≤
          ∑ _i ∈ S, ((treatedCount m j ω k ℓ : ℝ)⁻¹ * R) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have := hbound i hi
        nlinarith [sq_nonneg (treatedCount m j ω k ℓ : ℝ)⁻¹]
      _ = R ^ 2 * (treatedCount m j ω k ℓ : ℝ)⁻¹ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [hcard]
        field_simp

/-- Collect the fixed-design coefficient weight by template cell.  The
matrix row and monomial vector form one scalar coefficient per observation. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,α,i), [the asserted conclusion holds](goal). -/
lemma coefResidualWeight_cell_sum {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (α : MonoIndex d m) (i : Fin n) :
    coefResidualWeight m j ω k α i =
      (tensorCount d m : ℝ)⁻¹ *
        ∑ ℓ : Fin d → Fin (m + 1),
          (treatedCount m j ω k ℓ : ℝ)⁻¹ *
            if (ω i).2.1 = true ∧
                (ω i).1 ∈ scaledMicroCell d m j k ℓ then
              ∑ α' : MonoIndex d m,
                (gramHat m j ω k)⁻¹ α α' *
                  monoVec d m
                    (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α'
            else 0 := by
  classical
  unfold coefResidualWeight
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ℓ _
  by_cases hc : (ω i).2.1 = true ∧
      (ω i).1 ∈ scaledMicroCell d m j k ℓ
  · simp only [if_pos hc]
    apply Finset.sum_congr rfl
    intro α' _
    ring
  · simp [hc]

/-- A fixed finite number of template cells converts the cellwise
inverse-count estimate into a bound for their combined observation weight. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,c,R,hc), [the asserted conclusion holds](goal). -/
lemma treatedCell_combined_weight_square_le {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (c : (Fin d → Fin (m + 1)) → Fin n → ℝ) (R : ℝ)
    (hc : ∀ ℓ i, (ω i).2.1 = true ∧
        (ω i).1 ∈ scaledMicroCell d m j k ℓ → |c ℓ i| ≤ R) :
    (∑ i : Fin n,
      (∑ ℓ : Fin d → Fin (m + 1),
        if (ω i).2.1 = true ∧
            (ω i).1 ∈ scaledMicroCell d m j k ℓ then
          (treatedCount m j ω k ℓ : ℝ)⁻¹ * c ℓ i else 0) ^ 2) ≤
      (tensorCount d m : ℝ) * R ^ 2 *
        ∑ ℓ : Fin d → Fin (m + 1),
          (treatedCount m j ω k ℓ : ℝ)⁻¹ := by
  classical
  have hpoint (i : Fin n) :
      (∑ ℓ : Fin d → Fin (m + 1),
        if (ω i).2.1 = true ∧
            (ω i).1 ∈ scaledMicroCell d m j k ℓ then
          (treatedCount m j ω k ℓ : ℝ)⁻¹ * c ℓ i else 0) ^ 2 ≤
      (tensorCount d m : ℝ) *
        ∑ ℓ : Fin d → Fin (m + 1),
          (if (ω i).2.1 = true ∧
              (ω i).1 ∈ scaledMicroCell d m j k ℓ then
            (treatedCount m j ω k ℓ : ℝ)⁻¹ * c ℓ i else 0) ^ 2 := by
    simpa [tensorCount, Fintype.card_fun, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun ℓ : Fin d → Fin (m + 1) =>
          if (ω i).2.1 = true ∧
              (ω i).1 ∈ scaledMicroCell d m j k ℓ then
            (treatedCount m j ω k ℓ : ℝ)⁻¹ * c ℓ i else 0))
  calc
    _ ≤ ∑ i : Fin n, (tensorCount d m : ℝ) *
        ∑ ℓ : Fin d → Fin (m + 1),
          (if (ω i).2.1 = true ∧
              (ω i).1 ∈ scaledMicroCell d m j k ℓ then
            (treatedCount m j ω k ℓ : ℝ)⁻¹ * c ℓ i else 0) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact hpoint i
    _ = (tensorCount d m : ℝ) *
        ∑ ℓ : Fin d → Fin (m + 1),
          ∑ i : Fin n,
            (if (ω i).2.1 = true ∧
                (ω i).1 ∈ scaledMicroCell d m j k ℓ then
              (treatedCount m j ω k ℓ : ℝ)⁻¹ * c ℓ i else 0) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (tensorCount d m : ℝ) *
        ∑ ℓ : Fin d → Fin (m + 1),
          R ^ 2 * (treatedCount m j ω k ℓ : ℝ)⁻¹ := by
      gcongr
      exact treatedCell_weight_square_le_inverse_count m j ω k ℓ (c ℓ) R
        (hc ℓ)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- A bounded inverse-Gram row evaluation gives the coefficient coordinate
the inverse-count variance scale. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,α,R,hrow), [the asserted conclusion holds](goal). -/
lemma coefResidualWeight_square_sum_le {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (α : MonoIndex d m) (R : ℝ)
    (hrow : ∀ (ℓ : Fin d → Fin (m + 1)) (i : Fin n),
      (ω i).2.1 = true ∧
        (ω i).1 ∈ scaledMicroCell d m j k ℓ →
      |(tensorCount d m : ℝ)⁻¹ *
        ∑ α' : MonoIndex d m,
          (gramHat m j ω k)⁻¹ α α' *
            monoVec d m
              (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α'| ≤ R) :
    (∑ i : Fin n, (coefResidualWeight m j ω k α i) ^ 2) ≤
      (tensorCount d m : ℝ) * R ^ 2 *
        ∑ ℓ : Fin d → Fin (m + 1),
          (treatedCount m j ω k ℓ : ℝ)⁻¹ := by
  classical
  let c : (Fin d → Fin (m + 1)) → Fin n → ℝ := fun _ℓ i =>
    (tensorCount d m : ℝ)⁻¹ *
      ∑ α' : MonoIndex d m,
        (gramHat m j ω k)⁻¹ α α' *
          monoVec d m
            (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α'
  have hrepr (i : Fin n) :
      coefResidualWeight m j ω k α i =
        ∑ ℓ : Fin d → Fin (m + 1),
          if (ω i).2.1 = true ∧
              (ω i).1 ∈ scaledMicroCell d m j k ℓ then
            (treatedCount m j ω k ℓ : ℝ)⁻¹ * c ℓ i else 0 := by
    rw [coefResidualWeight_cell_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ℓ _
    by_cases hc : (ω i).2.1 = true ∧
        (ω i).1 ∈ scaledMicroCell d m j k ℓ
    · simp only [if_pos hc]
      dsimp [c]
      ring
    · simp [hc]
  simp_rw [hrepr]
  exact treatedCell_combined_weight_square_le m j ω k c R
    (fun ℓ i hi => hrow ℓ i hi)

set_option maxHeartbeats 800000 in
-- Normalizing the three nested finite sums can exceed the project default.
/-- Equal-cell response moments exactly reproduce a polynomial in the local
monomial basis. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,θ,hresponse), [the asserted conclusion holds](goal). -/
lemma responseMoment_eq_gramHat_mulVec_of_polynomial {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (θ : MonoIndex d m → ℝ)
    (hresponse : ∀ i : Fin n, (ω i).2.1 = true →
      (ω i).2.2 = ∑ α : MonoIndex d m,
        monoVec d m
          (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α * θ α) :
    responseMoment m j ω k = (gramHat m j ω k).mulVec θ := by
  classical
  funext α
  change ((tensorCount d m : ℝ)⁻¹ *
      ∑ ℓ : Fin d → Fin (m + 1), (treatedCount m j ω k ℓ : ℝ)⁻¹ *
        ∑ i : Fin n, if (ω i).2.1 = true ∧
            (ω i).1 ∈ scaledMicroCell d m j k ℓ then
          monoVec d m
              (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α *
            (ω i).2.2 else 0) =
    ∑ α' : MonoIndex d m,
      ((tensorCount d m : ℝ)⁻¹ *
        ∑ ℓ : Fin d → Fin (m + 1), (treatedCount m j ω k ℓ : ℝ)⁻¹ *
          ∑ i : Fin n, if (ω i).2.1 = true ∧
              (ω i).1 ∈ scaledMicroCell d m j k ℓ then
            monoVec d m
                (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α *
              monoVec d m
                (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α'
            else 0) * θ α'
  calc
    _ = (tensorCount d m : ℝ)⁻¹ *
        ∑ ℓ : Fin d → Fin (m + 1), (treatedCount m j ω k ℓ : ℝ)⁻¹ *
          ∑ i : Fin n, ∑ α' : MonoIndex d m,
            if (ω i).2.1 = true ∧
                (ω i).1 ∈ scaledMicroCell d m j k ℓ then
              monoVec d m
                  (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α *
                monoVec d m
                  (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α' *
                    θ α' else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro ℓ _
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with hi
      · rw [hresponse i hi.1, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro α' _
        ring
      · simp
    _ = _ := by
      let F : (Fin d → Fin (m + 1)) → Fin n → MonoIndex d m → ℝ :=
        fun ℓ i α' => if (ω i).2.1 = true ∧
            (ω i).1 ∈ scaledMicroCell d m j k ℓ then
          monoVec d m
              (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α *
            monoVec d m
              (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α'
        else 0
      have hrotate :
          (∑ ℓ, ∑ i, ∑ α',
              (tensorCount d m : ℝ)⁻¹ *
                ((treatedCount m j ω k ℓ : ℝ)⁻¹ * (F ℓ i α' * θ α'))) =
            ∑ α', ∑ ℓ, ∑ i,
              (tensorCount d m : ℝ)⁻¹ *
                ((treatedCount m j ω k ℓ : ℝ)⁻¹ * (F ℓ i α' * θ α')) := by
        calc
          _ = ∑ i, ∑ ℓ, ∑ α',
              (tensorCount d m : ℝ)⁻¹ *
                ((treatedCount m j ω k ℓ : ℝ)⁻¹ * (F ℓ i α' * θ α')) :=
            Finset.sum_comm
          _ = ∑ i, ∑ α', ∑ ℓ,
              (tensorCount d m : ℝ)⁻¹ *
                ((treatedCount m j ω k ℓ : ℝ)⁻¹ * (F ℓ i α' * θ α')) := by
            apply Finset.sum_congr rfl
            intro i _
            exact Finset.sum_comm
          _ = ∑ α', ∑ i, ∑ ℓ,
              (tensorCount d m : ℝ)⁻¹ *
                ((treatedCount m j ω k ℓ : ℝ)⁻¹ * (F ℓ i α' * θ α')) :=
            Finset.sum_comm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro α' _
            exact Finset.sum_comm
      simp only [Finset.mul_sum, Finset.sum_mul, mul_ite, mul_zero, ite_mul]
      simpa only [F, ite_mul, mul_ite, zero_mul, mul_zero, mul_assoc] using hrotate

/-- On an occupied equal-cell design, fitting polynomial responses recovers
their coefficient vector exactly. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,θ,hcount,hresponse), [the asserted conclusion holds](goal). -/
lemma coefHat_eq_of_polynomial_response {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (θ : MonoIndex d m → ℝ)
    (hcount : ∀ ℓ : Fin d → Fin (m + 1), 0 < treatedCount m j ω k ℓ)
    (hresponse : ∀ i : Fin n, (ω i).2.1 = true →
      (ω i).2.2 = ∑ α : MonoIndex d m,
        monoVec d m
          (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α * θ α) :
    coefHat m j ω k = θ := by
  classical
  rw [coefHat, responseMoment_eq_gramHat_mulVec_of_polynomial m j ω k θ hresponse,
    Matrix.mulVec_mulVec]
  have hdet : (gramHat m j ω k).det ≠ 0 :=
    (gramHat_minEig_ge_of_pos d m n ω j k hcount).2.2.1
  rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

/-- Feasibility forces every treated template cell to be occupied. [For the stated inputs and conditions](hyp:d,n,m,j,β,ω,hfeasible), [the asserted conclusion holds](goal). -/
lemma meshFeasible_treatedCount_pos {d n : ℕ} (m j : ℕ) (β : ℝ)
    (ω : Fin n → Obs d) (hfeasible : meshFeasible m β ω j) :
    ∀ (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1)),
      0 < treatedCount m j ω k ℓ := by
  intro k ℓ
  have hlower := hfeasible.2 k ℓ
  have hwidth : 0 < meshWidth j := by unfold meshWidth; positivity
  have hthreshold : 0 < meshWidth j ^ (-2 * β) := Real.rpow_pos_of_pos hwidth _
  exact_mod_cast hthreshold.trans_le hlower

/-- A coordinate of a matrix-vector product is controlled by the finite
Euclidean operator norm. [For the stated inputs and conditions](hyp:ι,M,v,i), [the asserted conclusion holds](goal). -/
lemma mulVec_coordinate_le_finiteL2OpNorm {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (v : ι → ℝ) (i : ι) :
    |M.mulVec v i| ≤ finiteL2OpNorm M * finiteL2Norm v := by
  classical
  have hsquare : (M.mulVec v i) ^ 2 ≤
      ∑ j : ι, (M.mulVec v j) ^ 2 := by
    exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hcoord : |M.mulVec v i| ≤ finiteL2Norm (M.mulVec v) := by
    rw [finiteL2Norm, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsquare
  exact hcoord.trans (finiteL2Norm_mulVec_le_opNorm M v)

/-- A uniform coordinate bound controls the Euclidean norm of a finite
vector by the square root of its dimension. [For the stated inputs and conditions](hyp:ι,v,r,hr,hv), [the asserted conclusion holds](goal). -/
lemma finiteL2Norm_le_sqrt_card_mul {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hv : ∀ i, |v i| ≤ r) :
    finiteL2Norm v ≤ Real.sqrt (Fintype.card ι : ℝ) * r := by
  classical
  have hsq (i : ι) : v i ^ 2 ≤ r ^ 2 := by
    rw [← sq_abs (v i), ← sq_abs r, abs_of_nonneg hr]
    exact pow_le_pow_left₀ (abs_nonneg _) (hv i) 2
  have hsum : (∑ i, v i ^ 2) ≤ (Fintype.card ι : ℝ) * r ^ 2 := by
    calc
      _ ≤ ∑ _i : ι, r ^ 2 := Finset.sum_le_sum fun i _ => hsq i
      _ = (Fintype.card ι : ℝ) * r ^ 2 := by simp
  have hsqrt := Real.sqrt_le_sqrt hsum
  rw [← finiteL2Norm] at hsqrt
  calc
    finiteL2Norm v ≤ Real.sqrt ((Fintype.card ι : ℝ) * r ^ 2) := hsqrt
    _ = Real.sqrt (Fintype.card ι : ℝ) * r := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hr]

/-- If every treated response perturbation entering a template cell is at
most `r`, then every coordinate of the equal-cell response moment changes by
at most `r`. [For the stated inputs and conditions](hyp:d,n,m,j,ω,ξ,k,hdesign,hcount,r,hr,hresponse,α), [the asserted conclusion holds](goal). -/
lemma responseMoment_sub_coordinate_le_of_pointwise {d n : ℕ} (m j : ℕ)
    (ω ξ : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (hdesign : ∀ i, (ξ i).1 = (ω i).1 ∧ (ξ i).2.1 = (ω i).2.1)
    (hcount : ∀ ℓ : Fin d → Fin (m + 1), 0 < treatedCount m j ω k ℓ)
    (r : ℝ) (hr : 0 ≤ r)
    (hresponse : ∀ (ℓ : Fin d → Fin (m + 1)) (i : Fin n),
      (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ →
      |(ξ i).2.2 - (ω i).2.2| ≤ r)
    (α : MonoIndex d m) :
    |(responseMoment m j ξ k - responseMoment m j ω k) α| ≤ r := by
  classical
  rw [responseMoment_sub_of_design_eq m j ω ξ k hdesign α]
  have hJ : 0 < (tensorCount d m : ℝ) := by
    dsimp [tensorCount]
    positivity
  have hcell (ℓ : Fin d → Fin (m + 1)) :
      |(treatedCount m j ω k ℓ : ℝ)⁻¹ *
          ∑ i : Fin n, if (ω i).2.1 = true ∧
              (ω i).1 ∈ scaledMicroCell d m j k ℓ then
              monoVec d m (fun a => ((ω i).1 a - cubeCorner d j k a) /
                meshWidth j) α * ((ξ i).2.2 - (ω i).2.2)
            else 0| ≤ r := by
    let z : Fin n → Fin d → ℝ := fun i a =>
      ((ω i).1 a - cubeCorner d j k a) / meshWidth j
    have hterm (i : Fin n) :
        |if (ω i).2.1 = true ∧
            (ω i).1 ∈ scaledMicroCell d m j k ℓ then
            monoVec d m (z i) α * ((ξ i).2.2 - (ω i).2.2)
          else 0| ≤
        if (ω i).2.1 = true ∧
            (ω i).1 ∈ scaledMicroCell d m j k ℓ then r else 0 := by
      by_cases hi : (ω i).2.1 = true ∧
          (ω i).1 ∈ scaledMicroCell d m j k ℓ
      · simp only [if_pos hi, abs_mul]
        have hz : z i ∈ cube d := microCube_subset_cube d m ℓ hi.2
        have hmono : |monoVec d m (z i) α| ≤ 1 := by
          have hcoord : 0 ≤ monoVec d m (z i) α ∧ monoVec d m (z i) α ≤ 1 := by
            unfold monoVec
            constructor
            · apply Finset.prod_nonneg
              intro a ha
              exact pow_nonneg ((Set.mem_univ_pi.mp hz a).1) _
            · apply Finset.prod_le_one
              · intro a ha
                exact pow_nonneg ((Set.mem_univ_pi.mp hz a).1) _
              · intro a ha
                exact pow_le_one₀ ((Set.mem_univ_pi.mp hz a).1)
                  ((Set.mem_univ_pi.mp hz a).2)
          rw [abs_of_nonneg hcoord.1]
          exact hcoord.2
        simpa using
          (mul_le_mul hmono (hresponse ℓ i hi) (abs_nonneg _) (by norm_num))
      · simp [hi, hr]
    have hsum :
        |∑ i : Fin n, if (ω i).2.1 = true ∧
              (ω i).1 ∈ scaledMicroCell d m j k ℓ then
              monoVec d m (z i) α * ((ξ i).2.2 - (ω i).2.2)
            else 0| ≤
          ∑ i : Fin n, if (ω i).2.1 = true ∧
              (ω i).1 ∈ scaledMicroCell d m j k ℓ then r else 0 :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => hterm i)
    have hweights :
        (treatedCount m j ω k ℓ : ℝ)⁻¹ *
          (∑ i : Fin n, if (ω i).2.1 = true ∧
              (ω i).1 ∈ scaledMicroCell d m j k ℓ then r else 0) = r := by
      have hw := treatedCount_inv_weight_sum m j ω k ℓ (hcount ℓ)
      unfold treatedCellWeightSum at hw
      calc
        _ = ((treatedCount m j ω k ℓ : ℝ)⁻¹ *
            ∑ i : Fin n, if (ω i).2.1 = true ∧
              (ω i).1 ∈ scaledMicroCell d m j k ℓ then 1 else 0) * r := by
                rw [mul_assoc]
                congr 1
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i hi
                split_ifs <;> ring
        _ = r := by rw [hw, one_mul]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (treatedCount m j ω k ℓ : ℝ)⁻¹)]
    exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq hweights
  calc
    |(tensorCount d m : ℝ)⁻¹ * ∑ ℓ, _| =
        (tensorCount d m : ℝ)⁻¹ * |∑ ℓ, _| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (tensorCount d m : ℝ)⁻¹ * ∑ _ℓ : Fin d → Fin (m + 1), r := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun ℓ _ => hcell ℓ)
    _ = r := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, tensorCount]
      field_simp

/-- On an occupied equal-cell design, a coordinatewise response-moment
perturbation is stable under inversion of the empirical Gram matrix. [For the stated inputs and conditions](hyp:d,n,m,j,ω,ξ,k,hdesign,hcount,r,hr,hmoment,α), [the asserted conclusion holds](goal). -/
lemma coefHat_sub_coordinate_le_of_responseMoment {d n : ℕ} (m j : ℕ)
    (ω ξ : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (hdesign : ∀ i, (ξ i).1 = (ω i).1 ∧ (ξ i).2.1 = (ω i).2.1)
    (hcount : ∀ ℓ : Fin d → Fin (m + 1), 0 < treatedCount m j ω k ℓ)
    (r : ℝ) (hr : 0 ≤ r)
    (hmoment : ∀ α : MonoIndex d m,
      |(responseMoment m j ξ k - responseMoment m j ω k) α| ≤ r)
    (α : MonoIndex d m) :
    |(coefHat m j ξ k - coefHat m j ω k) α| ≤
      (2 / templateLambda d m) *
        (Real.sqrt (Fintype.card (MonoIndex d m) : ℝ) * r) := by
  classical
  letI : Nonempty (MonoIndex d m) :=
    ⟨⟨fun _ => 0, by simp [monoIdx]⟩⟩
  rw [coefHat_sub_of_design_eq m j ω ξ k hdesign]
  refine (mulVec_coordinate_le_finiteL2OpNorm
    (gramHat m j ω k)⁻¹
    (responseMoment m j ξ k - responseMoment m j ω k) α).trans ?_
  have hop := (gramHat_minEig_ge_of_pos d m n ω j k hcount).2.2.2
  have hnorm := finiteL2Norm_le_sqrt_card_mul
    (responseMoment m j ξ k - responseMoment m j ω k) r hr hmoment
  have hfac : 0 ≤ 2 / templateLambda d m :=
    (div_pos (by norm_num) (templateLambda_pos d m)).le
  exact (mul_le_mul hop hnorm (by exact Real.sqrt_nonneg _) hfac).trans_eq
    (by ring)

/-- Pointwise treated-response approximation on every occupied microcell
implies a dimension-explicit bound for each fitted coefficient. [For the stated inputs and conditions](hyp:d,n,m,j,ω,ξ,k,hdesign,hcount,r,hr,hresponse,α), [the asserted conclusion holds](goal). -/
lemma coefHat_sub_coordinate_le_of_pointwise {d n : ℕ} (m j : ℕ)
    (ω ξ : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (hdesign : ∀ i, (ξ i).1 = (ω i).1 ∧ (ξ i).2.1 = (ω i).2.1)
    (hcount : ∀ ℓ : Fin d → Fin (m + 1), 0 < treatedCount m j ω k ℓ)
    (r : ℝ) (hr : 0 ≤ r)
    (hresponse : ∀ (ℓ : Fin d → Fin (m + 1)) (i : Fin n),
      (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ →
      |(ξ i).2.2 - (ω i).2.2| ≤ r)
    (α : MonoIndex d m) :
    |(coefHat m j ξ k - coefHat m j ω k) α| ≤
      (2 / templateLambda d m) *
        (Real.sqrt (Fintype.card (MonoIndex d m) : ℝ) * r) := by
  apply coefHat_sub_coordinate_le_of_responseMoment m j ω ξ k hdesign hcount r hr
  intro α'
  exact responseMoment_sub_coordinate_le_of_pointwise
    m j ω ξ k hdesign hcount r hr hresponse α'

/-- An occupied equal-cell fit is stable around any local polynomial whose
values uniformly approximate the treated responses entering its microcells. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,θ,hcount,r,hr,hresponse,α), [the asserted conclusion holds](goal). -/
lemma coefHat_sub_polynomial_coordinate_le {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (θ : MonoIndex d m → ℝ)
    (hcount : ∀ ℓ : Fin d → Fin (m + 1), 0 < treatedCount m j ω k ℓ)
    (r : ℝ) (hr : 0 ≤ r)
    (hresponse : ∀ (ℓ : Fin d → Fin (m + 1)) (i : Fin n),
      (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ →
      |(ω i).2.2 - ∑ α : MonoIndex d m,
        monoVec d m
          (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α * θ α| ≤ r)
    (α : MonoIndex d m) :
    |coefHat m j ω k α - θ α| ≤
      (2 / templateLambda d m) *
        (Real.sqrt (Fintype.card (MonoIndex d m) : ℝ) * r) := by
  classical
  let ξ : Fin n → Obs d := fun i =>
    ((ω i).1, (ω i).2.1,
      ∑ α : MonoIndex d m,
        monoVec d m
          (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α * θ α)
  have hdesign : ∀ i, (ω i).1 = (ξ i).1 ∧ (ω i).2.1 = (ξ i).2.1 := by
    intro i
    exact ⟨rfl, rfl⟩
  have hcountξ : ∀ ℓ : Fin d → Fin (m + 1), 0 < treatedCount m j ξ k ℓ := by
    intro ℓ
    rw [treatedCount_eq_of_design_eq m j ω ξ k ℓ]
    · exact hcount ℓ
    · intro i
      exact ⟨rfl, rfl⟩
  have hpoly : coefHat m j ξ k = θ := by
    apply coefHat_eq_of_polynomial_response m j ξ k θ
    · exact hcountξ
    · intro i hi
      rfl
  have hpert := coefHat_sub_coordinate_le_of_pointwise
    m j ξ ω k hdesign hcountξ r hr
    (fun ℓ i hi => by simpa only [ξ, abs_sub_comm] using hresponse ℓ i hi) α
  simpa only [Pi.sub_apply, hpoly] using hpert

/-- Conditioning of the equal-cell Gram matrix bounds each evaluation of
an inverse-Gram row at a normalized covariate. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,α,z,V,hcount,hV), [the asserted conclusion holds](goal). -/
lemma inverseGram_row_monoVec_le {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (α : MonoIndex d m) (z : Fin d → ℝ) (V : ℝ)
    (hcount : ∀ ℓ : Fin d → Fin (m + 1), 0 < treatedCount m j ω k ℓ)
    (hV : finiteL2Norm (monoVec d m z) ≤ V) :
    |(tensorCount d m : ℝ)⁻¹ *
      ∑ α' : MonoIndex d m,
        (gramHat m j ω k)⁻¹ α α' * monoVec d m z α'| ≤
      (tensorCount d m : ℝ)⁻¹ * ((2 / templateLambda d m) * V) := by
  classical
  have : Nonempty (MonoIndex d m) :=
    ⟨⟨fun _ => 0, by simp [monoIdx]⟩⟩
  have hJ : 0 ≤ (tensorCount d m : ℝ)⁻¹ := by positivity
  have hOp := (gramHat_minEig_ge_of_pos d m n ω j k hcount).2.2.2
  have hcoord := mulVec_coordinate_le_finiteL2OpNorm
    (gramHat m j ω k)⁻¹ (monoVec d m z) α
  have hprod :
      finiteL2OpNorm ((gramHat m j ω k)⁻¹) *
          finiteL2Norm (monoVec d m z) ≤
        (2 / templateLambda d m) * V := by
    have hoppos := finiteL2OpNorm_nonneg ((gramHat m j ω k)⁻¹)
    have hvpos : 0 ≤ finiteL2Norm (monoVec d m z) := Real.sqrt_nonneg _
    exact (mul_le_mul_of_nonneg_left hV hoppos).trans
      (mul_le_mul_of_nonneg_right hOp (le_trans hvpos hV))
  simp only [Matrix.mulVec, dotProduct] at hcoord
  rw [abs_mul, abs_of_nonneg hJ]
  exact mul_le_mul_of_nonneg_left (hcoord.trans hprod) hJ

/-- On the unit cube, every monomial coordinate has magnitude at most one,
so the whole template vector has norm at most the square root of its size. [For the stated inputs and conditions](hyp:d,m,z,hz), [the asserted conclusion holds](goal). -/
lemma monoVec_finiteL2Norm_le_dimension (d m : ℕ)
    (z : Fin d → ℝ) (hz : z ∈ cube d) :
    finiteL2Norm (monoVec d m z) ≤
      Real.sqrt (Fintype.card (MonoIndex d m) : ℝ) := by
  classical
  have hcoord (α : MonoIndex d m) : 0 ≤ monoVec d m z α ∧
      monoVec d m z α ≤ 1 := by
    unfold monoVec
    constructor
    · apply Finset.prod_nonneg
      intro i hi
      exact pow_nonneg ((Set.mem_univ_pi.mp hz i).1) _
    · apply Finset.prod_le_one
      · intro i hi
        exact pow_nonneg ((Set.mem_univ_pi.mp hz i).1) _
      · intro i hi
        exact pow_le_one₀ ((Set.mem_univ_pi.mp hz i).1) ((Set.mem_univ_pi.mp hz i).2)
  have hsum : (∑ α : MonoIndex d m, monoVec d m z α ^ 2) ≤
      (Fintype.card (MonoIndex d m) : ℝ) := by
    calc
      _ ≤ ∑ _α : MonoIndex d m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro α _
        nlinarith [hcoord α]
      _ = _ := by simp
  exact Real.sqrt_le_sqrt hsum

/-- Clipping to the outcome range cannot increase error relative to a target
already in that range. [For the stated inputs and conditions](hyp:B,u,y,hB,hy), [the asserted conclusion holds](goal). -/
lemma selectedMesh_clip_error_le {B u y : ℝ} (hB : 0 ≤ B) (hy : |y| ≤ B) :
    |max (-B) (min B u) - y| ≤ |u - y| := by
  have hylo : -B ≤ y := (abs_le.mp hy).1
  have hyhi : y ≤ B := (abs_le.mp hy).2
  by_cases huhi : u ≤ B
  · rw [min_eq_right huhi]
    by_cases hulo : -B ≤ u
    · rw [max_eq_right hulo]
    · rw [max_eq_left (le_of_not_ge hulo)]
      rw [abs_of_nonpos (sub_nonpos.mpr hylo)]
      have huy : u ≤ y := (lt_of_not_ge hulo).le.trans hylo
      rw [abs_of_nonpos (sub_nonpos.mpr huy)]
      linarith
  · rw [min_eq_left (le_of_not_ge huhi), max_eq_right (by linarith)]
    rw [abs_of_nonneg (sub_nonneg.mpr hyhi)]
    have hyu : y ≤ u := hyhi.trans (le_of_lt (lt_of_not_ge huhi))
    rw [abs_of_nonneg (sub_nonneg.mpr hyu)]
    linarith

/-- A uniform coordinate error in local polynomial coefficients yields a
uniform evaluation error on the normalized unit cube. [For the stated inputs and conditions](hyp:d,m,z,hz,a,b,ε,hε), [the asserted conclusion holds](goal). -/
lemma monoVec_evaluation_sub_le_card_mul {d m : ℕ}
    (z : Fin d → ℝ) (hz : z ∈ cube d)
    (a b : MonoIndex d m → ℝ) (ε : ℝ)
    (hε : ∀ α, |a α - b α| ≤ ε) :
    |(∑ α, monoVec d m z α * a α) -
        ∑ α, monoVec d m z α * b α| ≤
      (Fintype.card (MonoIndex d m) : ℝ) * ε := by
  classical
  have hmono (α : MonoIndex d m) : |monoVec d m z α| ≤ 1 := by
    have hcoord : 0 ≤ monoVec d m z α ∧ monoVec d m z α ≤ 1 := by
      unfold monoVec
      constructor
      · apply Finset.prod_nonneg
        intro i hi
        exact pow_nonneg ((Set.mem_univ_pi.mp hz i).1) _
      · apply Finset.prod_le_one
        · intro i hi
          exact pow_nonneg ((Set.mem_univ_pi.mp hz i).1) _
        · intro i hi
          exact pow_le_one₀ ((Set.mem_univ_pi.mp hz i).1)
            ((Set.mem_univ_pi.mp hz i).2)
    rw [abs_of_nonneg hcoord.1]
    exact hcoord.2
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ α, (monoVec d m z α * a α - monoVec d m z α * b α)|
        = |∑ α, monoVec d m z α * (a α - b α)| := by
            congr 1
            apply Finset.sum_congr rfl
            intro α _
            ring
    _ ≤ ∑ α, |monoVec d m z α * (a α - b α)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _α : MonoIndex d m, ε := by
      apply Finset.sum_le_sum
      intro α _
      rw [abs_mul]
      calc
        |monoVec d m z α| * |a α - b α| ≤ 1 * ε :=
          mul_le_mul (hmono α) (hε α) (abs_nonneg _) zero_le_one
        _ = ε := one_mul ε
    _ = (Fintype.card (MonoIndex d m) : ℝ) * ε := by simp

/-- Combining coefficient control with clipping leaves only the deterministic
local-polynomial approximation error. [For the stated inputs and conditions](hyp:d,m,B,y,ε,z,hz,a,b,hB,hy,hε), [the asserted conclusion holds](goal). -/
lemma clipped_monoVec_error_le_card_mul_add {d m : ℕ} {B y ε : ℝ}
    (z : Fin d → ℝ) (hz : z ∈ cube d)
    (a b : MonoIndex d m → ℝ) (hB : 0 ≤ B) (hy : |y| ≤ B)
    (hε : ∀ α, |a α - b α| ≤ ε) :
    |max (-B) (min B (∑ α, monoVec d m z α * a α)) - y| ≤
      (Fintype.card (MonoIndex d m) : ℝ) * ε +
        |(∑ α, monoVec d m z α * b α) - y| := by
  have hclip := selectedMesh_clip_error_le hB hy
    (u := ∑ α, monoVec d m z α * a α)
  have hsplit :
      |(∑ α, monoVec d m z α * a α) - y| ≤
        |(∑ α, monoVec d m z α * a α) -
            ∑ α, monoVec d m z α * b α| +
          |(∑ α, monoVec d m z α * b α) - y| := by
    rw [show (∑ α, monoVec d m z α * a α) - y =
        ((∑ α, monoVec d m z α * a α) -
          ∑ α, monoVec d m z α * b α) +
        ((∑ α, monoVec d m z α * b α) - y) by ring]
    exact abs_add_le _ _
  exact hclip.trans (hsplit.trans (add_le_add
    (monoVec_evaluation_sub_le_card_mul z hz a b ε hε) (le_refl _)))

/-- At a positive selected mesh, coefficient control plus a local polynomial
approximation controls the actual clipped estimator at a fixed point. [For the stated inputs and conditions](hyp:d,n,β,B,y,ε,δ,ω,x,θ,hselected,hz,hB,hy,hcoef,hbias), [the asserted conclusion holds](goal). -/
lemma equalCellEstimator_error_le_of_selected_coefficients {d n : ℕ}
    {β B y ε δ : ℝ} (ω : Fin n → Obs d) (x : Fin d → ℝ)
    (θ : MonoIndex d (polynomialDegree β) → ℝ)
    (hselected : 0 < countSelectedMesh (polynomialDegree β) β ω)
    (hz : (fun a =>
      (x a - cubeCorner d ((feasibleIndices (polynomialDegree β) β ω).sup id)
        (cubeIndex d ((feasibleIndices (polynomialDegree β) β ω).sup id) x) a) /
        countSelectedMesh (polynomialDegree β) β ω) ∈ cube d)
    (hB : 0 ≤ B) (hy : |y| ≤ B)
    (hcoef : ∀ α,
      |coefHat (polynomialDegree β)
          ((feasibleIndices (polynomialDegree β) β ω).sup id) ω
          (cubeIndex d ((feasibleIndices (polynomialDegree β) β ω).sup id) x) α - θ α| ≤ ε)
    (hbias :
      |(∑ α,
          monoVec d (polynomialDegree β)
            (fun a =>
              (x a - cubeCorner d
                ((feasibleIndices (polynomialDegree β) β ω).sup id)
                (cubeIndex d ((feasibleIndices (polynomialDegree β) β ω).sup id) x) a) /
                countSelectedMesh (polynomialDegree β) β ω) α * θ α) - y| ≤ δ) :
    |equalCellEstimator β B ω x - y| ≤
      (Fintype.card (MonoIndex d (polynomialDegree β)) : ℝ) * ε + δ := by
  let j := (feasibleIndices (polynomialDegree β) β ω).sup id
  let k := cubeIndex d j x
  let z : Fin d → ℝ := fun a =>
    (x a - cubeCorner d j k a) /
      countSelectedMesh (polynomialDegree β) β ω
  have hne : countSelectedMesh (polynomialDegree β) β ω ≠ 0 := ne_of_gt hselected
  have hbase := clipped_monoVec_error_le_card_mul_add z
    (by simpa [z, j, k] using hz)
    (coefHat (polynomialDegree β) j ω k) θ hB hy
    (by simpa [j, k] using hcoef)
  unfold equalCellEstimator
  simp only [hne, ↓reduceIte]
  change |max (-B) (min B
      (∑ α, monoVec d (polynomialDegree β) z α *
        coefHat (polynomialDegree β) j ω k α)) - y| ≤ _
  exact hbase.trans (add_le_add_right (by simpa [z, j, k] using hbias) _)


/-- Every occupied template cell has the same dimension-only inverse-Gram
row bound. This supplies the row premise of the squared-weight estimate. [For the stated inputs and conditions](hyp:d,n,m,j,ω,k,α,hcount), [the asserted conclusion holds](goal). -/
lemma inverseGram_row_bound_on_scaledMicroCell {d n : ℕ} (m j : ℕ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (α : MonoIndex d m)
    (hcount : ∀ ℓ : Fin d → Fin (m + 1), 0 < treatedCount m j ω k ℓ) :
    ∀ (ℓ : Fin d → Fin (m + 1)) (i : Fin n),
      (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ →
      |(tensorCount d m : ℝ)⁻¹ *
        ∑ α' : MonoIndex d m,
          (gramHat m j ω k)⁻¹ α α' *
            monoVec d m
              (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α'| ≤
      (tensorCount d m : ℝ)⁻¹ *
        ((2 / templateLambda d m) *
          Real.sqrt (Fintype.card (MonoIndex d m) : ℝ)) := by
  intro ℓ i hi
  apply inverseGram_row_monoVec_le m j ω k α _ _ hcount
  exact monoVec_finiteL2Norm_le_dimension d m _
    (microCube_subset_cube d m ℓ hi.2)

end CausalSmith.Stat.WeakOverlap

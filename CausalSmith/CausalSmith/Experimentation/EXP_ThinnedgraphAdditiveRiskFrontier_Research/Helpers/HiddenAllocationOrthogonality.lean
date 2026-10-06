module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.HiddenAllocationEnergy

/-!
# Orthogonality of hidden-allocation response supports

Different sets of active response rows are orthogonal under the independent row
reference. Positive degrees within an active row are not assumed orthogonal.
The finite weighted and Pythagorean identities assemble the support-group step
of the hidden-allocation contraction roadmap.
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

/-- The constant row coefficient is one almost everywhere under the reference law.  [For the stated data and conditions](hyp:d,h), [the stated conclusion holds](goal). -/
-- @node: walshCoeff_zero_reference_ae
lemma walshCoeff_zero_reference_ae (d : ℕ) (h : ℝ) :
    walshCoeff d h 0 =ᵐ[volume.withDensity
      (fun w => ENNReal.ofReal (refDensity d h w))] (fun _ => 1) := by
  change ∀ᵐ w ∂volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w)),
    walshCoeff d h 0 w = 1
  rw [ae_withDensity_iff (by fun_prop)]
  filter_upwards [] with w hw
  exact walshCoeff_zero d h w (lt_of_le_of_ne (refDensity_nonneg d h w)
    (by intro hz; apply hw; rw [← hz]; simp))

/-- The nonconstant row coefficients have zero mean under the actual reference law.  [For the stated data and conditions](hyp:d,h,hd,s,hs), [the stated conclusion holds](goal). -/
-- @node: walshCoeff_reference_centered
lemma walshCoeff_reference_centered (d : ℕ) (h : ℝ) (hd : 1 ≤ d)
    (s : ℕ) (hs : 1 ≤ s) :
    (∫ w, walshCoeff d h s w ∂volume.withDensity
      (fun w => ENNReal.ofReal (refDensity d h w))) = 0 := by
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (refDensity_nonneg d h _), smul_eq_mul]
  simpa only [mul_comm] using walshCoeff_centered d h hd s hs

/-- A nonconstant coefficient is orthogonal to the constant coefficient.  [For the stated data and conditions](hyp:d,h,hd,s,t,hst), [the stated conclusion holds](goal). -/
-- @node: walshCoeff_reference_cross_zero
lemma walshCoeff_reference_cross_zero (d : ℕ) (h : ℝ) (hd : 1 ≤ d)
    (s t : ℕ) (hst : (1 ≤ s ∧ t = 0) ∨ (s = 0 ∧ 1 ≤ t)) :
    (∫ w, walshCoeff d h s w * walshCoeff d h t w ∂volume.withDensity
      (fun w => ENNReal.ofReal (refDensity d h w))) = 0 := by
  rcases hst with ⟨hs, rfl⟩ | ⟨rfl, ht⟩
  · calc
      _ = ∫ w, walshCoeff d h s w ∂volume.withDensity
          (fun w => ENNReal.ofReal (refDensity d h w)) := by
        apply integral_congr_ae
        filter_upwards [walshCoeff_zero_reference_ae d h] with w hw
        rw [hw, mul_one]
      _ = 0 := walshCoeff_reference_centered d h hd s hs
  · calc
      _ = ∫ w, walshCoeff d h t w ∂volume.withDensity
          (fun w => ENNReal.ofReal (refDensity d h w)) := by
        apply integral_congr_ae
        filter_upwards [walshCoeff_zero_reference_ae d h] with w hw
        rw [hw, one_mul]
      _ = 0 := walshCoeff_reference_centered d h hd t ht

/-- Cross products of arbitrary row coefficient products are integrable, since each
row coefficient is bounded by one.  [For the stated data and conditions](hyp:B,d,h,s,t), [the stated conclusion holds](goal). -/
-- @node: walshCoeff_product_cross_integrable
lemma walshCoeff_product_cross_integrable (B d : ℕ) (h : ℝ) (s t : Fin B → ℕ) :
    Integrable (fun y : Fin B → ℝ =>
      (∏ ℓ, walshCoeff d h (s ℓ) (y ℓ)) *
        (∏ ℓ, walshCoeff d h (t ℓ) (y ℓ)))
      (Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) := by
  let := referenceRowLaw_probability d h
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_mul]
  apply mul_le_one₀
  · rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
      (fun ℓ _ => walshCoeff_abs_le_one d h (y ℓ) (s ℓ))
  · exact abs_nonneg _
  · rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
      (fun ℓ _ => walshCoeff_abs_le_one d h (y ℓ) (t ℓ))

/-- A row active in exactly one coefficient product forces their reference cross
integral to vanish; degrees on shared active rows may differ.  [For the stated data and conditions](hyp:B,d,h,hd,s,t,hst), [the stated conclusion holds](goal). -/
-- @node: walshCoeff_product_support_orthogonal
lemma walshCoeff_product_support_orthogonal (B d : ℕ) (h : ℝ) (hd : 1 ≤ d)
    (s t : Fin B → ℕ)
    (hst : ∃ ℓ, (1 ≤ s ℓ ∧ t ℓ = 0) ∨ (s ℓ = 0 ∧ 1 ≤ t ℓ)) :
    (∫ y : Fin B → ℝ,
      (∏ ℓ, walshCoeff d h (s ℓ) (y ℓ)) *
        (∏ ℓ, walshCoeff d h (t ℓ) (y ℓ))
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) = 0 := by
  let := referenceRowLaw_probability d h
  simp_rw [← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod
    (fun ℓ w => walshCoeff d h (s ℓ) w * walshCoeff d h (t ℓ) w)]
  obtain ⟨ℓ, hℓ⟩ := hst
  exact Finset.prod_eq_zero (Finset.mem_univ ℓ)
    (walshCoeff_reference_cross_zero d h hd (s ℓ) (t ℓ) hℓ)

/-- Finite weighted allocation sums have integrable cross products, with no
regularity premises on their finite weights.  [For the stated data and conditions](hyp:ι,κ,B,d,h,S,T,w,v,s,t), [the stated conclusion holds](goal). -/
-- @node: hidden_support_sum_cross_integrable
lemma hidden_support_sum_cross_integrable {ι κ : Type*} (B d : ℕ) (h : ℝ)
    (S : Finset ι) (T : Finset κ) (w : ι → ℝ) (v : κ → ℝ)
    (s : ι → Fin B → ℕ) (t : κ → Fin B → ℕ) :
    Integrable (fun y : Fin B → ℝ =>
      (∑ i ∈ S, w i * ∏ ℓ, walshCoeff d h (s i ℓ) (y ℓ)) *
        (∑ j ∈ T, v j * ∏ ℓ, walshCoeff d h (t j ℓ) (y ℓ)))
      (Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) := by
  simp_rw [Finset.sum_mul_sum]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  have he (y : Fin B → ℝ) :
      (w i * ∏ ℓ, walshCoeff d h (s i ℓ) (y ℓ)) *
        (v j * ∏ ℓ, walshCoeff d h (t j ℓ) (y ℓ)) =
      (w i * v j) * ((∏ ℓ, walshCoeff d h (s i ℓ) (y ℓ)) *
        (∏ ℓ, walshCoeff d h (t j ℓ) (y ℓ))) := by ring
  simp_rw [he]
  exact (walshCoeff_product_cross_integrable B d h (s i) (t j)).const_mul _

/-- Orthogonality survives the finite weighted sums over constrained allocations
within two different response-support groups.  [For the stated data and conditions](hyp:ι,κ,B,d,h,hd,S,T,w,v,s,t,hst), [the stated conclusion holds](goal). -/
-- @node: hidden_support_sum_orthogonal
lemma hidden_support_sum_orthogonal {ι κ : Type*} (B d : ℕ) (h : ℝ) (hd : 1 ≤ d)
    (S : Finset ι) (T : Finset κ) (w : ι → ℝ) (v : κ → ℝ)
    (s : ι → Fin B → ℕ) (t : κ → Fin B → ℕ)
    (hst : ∀ i ∈ S, ∀ j ∈ T, ∃ ℓ,
      (1 ≤ s i ℓ ∧ t j ℓ = 0) ∨ (s i ℓ = 0 ∧ 1 ≤ t j ℓ)) :
    (∫ y : Fin B → ℝ,
      (∑ i ∈ S, w i * ∏ ℓ, walshCoeff d h (s i ℓ) (y ℓ)) *
        (∑ j ∈ T, v j * ∏ ℓ, walshCoeff d h (t j ℓ) (y ℓ))
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) = 0 := by
  have hi (i : ι) (j : κ) : Integrable (fun y : Fin B → ℝ =>
      (w i * ∏ ℓ, walshCoeff d h (s i ℓ) (y ℓ)) *
        (v j * ∏ ℓ, walshCoeff d h (t j ℓ) (y ℓ)))
      (Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) := by
    simpa only [Finset.sum_singleton] using hidden_support_sum_cross_integrable
      B d h {i} {j} w v s t
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finsetSum S (fun i _ => integrable_finsetSum T (fun j _ => hi i j))]
  apply Finset.sum_eq_zero
  intro i hiS
  rw [integral_finsetSum T (fun j _ => hi i j)]
  apply Finset.sum_eq_zero
  intro j hjT
  have he (y : Fin B → ℝ) :
      (w i * ∏ ℓ, walshCoeff d h (s i ℓ) (y ℓ)) *
        (v j * ∏ ℓ, walshCoeff d h (t j ℓ) (y ℓ)) =
      (w i * v j) * ((∏ ℓ, walshCoeff d h (s i ℓ) (y ℓ)) *
        (∏ ℓ, walshCoeff d h (t j ℓ) (y ℓ))) := by ring
  simp_rw [he]
  rw [integral_const_mul,
    walshCoeff_product_support_orthogonal B d h hd (s i) (t j) (hst i hiS j hjT), mul_zero]

/-- The squared norm of a finite orthogonal family is the sum of its squared norms.  [For the stated data and conditions](hyp:ι,Ω,μ,S,v,hi,ho), [the stated conclusion holds](goal). -/
-- @node: hidden_orthogonal_sum_energy
lemma hidden_orthogonal_sum_energy {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (v : ι → Ω → ℝ)
    (hi : ∀ i ∈ S, ∀ j ∈ S, Integrable (fun y => v i y * v j y) μ)
    (ho : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (∫ y, v i y * v j y ∂μ) = 0) :
    (∫ y, (∑ i ∈ S, v i y) ^ 2 ∂μ) = ∑ i ∈ S, ∫ y, v i y ^ 2 ∂μ := by
  classical
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [integral_finsetSum S (fun i hiS =>
    integrable_finsetSum S (fun j hjS => hi i hiS j hjS))]
  apply Finset.sum_congr rfl
  intro i hiS
  rw [integral_finsetSum S (fun j hjS => hi i hiS j hjS)]
  exact Finset.sum_eq_single i (fun j hjS hji => ho i hiS j hjS hji.symm)
    (fun h => (h hiS).elim)

/-- The allocation sums grouped by different active response supports have additive
squared norms. This is the support-group assembly used before weighted Cauchy–Schwarz.  [For the stated data and conditions](hyp:ι,κ,B,d,h,hd,G,S,w,s,hst), [the stated conclusion holds](goal). -/
-- @node: hidden_support_group_energy
lemma hidden_support_group_energy {ι κ : Type*} (B d : ℕ) (h : ℝ) (hd : 1 ≤ d)
    (G : Finset ι) (S : ι → Finset κ) (w : ι → κ → ℝ)
    (s : ι → κ → Fin B → ℕ)
    (hst : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → ∀ u ∈ S i, ∀ v ∈ S j,
      ∃ ℓ, (1 ≤ s i u ℓ ∧ s j v ℓ = 0) ∨ (s i u ℓ = 0 ∧ 1 ≤ s j v ℓ)) :
    (∫ y : Fin B → ℝ,
      (∑ i ∈ G, ∑ u ∈ S i, w i u * ∏ ℓ, walshCoeff d h (s i u ℓ) (y ℓ)) ^ 2
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) =
    ∑ i ∈ G, ∫ y : Fin B → ℝ,
      (∑ u ∈ S i, w i u * ∏ ℓ, walshCoeff d h (s i u ℓ) (y ℓ)) ^ 2
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w))) := by
  apply hidden_orthogonal_sum_energy
  · intro i hi j hj
    exact hidden_support_sum_cross_integrable B d h (S i) (S j) (w i) (w j) (s i) (s j)
  · intro i hi j hj hij
    exact hidden_support_sum_orthogonal B d h hd (S i) (S j) (w i) (w j) (s i) (s j)
      (hst i hi j hj hij)

/-- Distinct active-row sets supply a row that is positive in exactly one degree
vector. This is only finite support bookkeeping, with no analytic premise.  [For the stated data and conditions](hyp:B,s,t,A,E,hs,ht,hAE), [the stated conclusion holds](goal). -/
-- @node: hidden_degree_support_witness
lemma hidden_degree_support_witness (B : ℕ) (s t : Fin B → ℕ)
    (A E : Finset (Fin B))
    (hs : ∀ ℓ, s ℓ ≠ 0 ↔ ℓ ∈ A) (ht : ∀ ℓ, t ℓ ≠ 0 ↔ ℓ ∈ E)
    (hAE : A ≠ E) :
    ∃ ℓ, (1 ≤ s ℓ ∧ t ℓ = 0) ∨ (s ℓ = 0 ∧ 1 ≤ t ℓ) := by
  classical
  by_contra hw
  push Not at hw
  apply hAE
  ext ℓ
  rw [← hs ℓ, ← ht ℓ]
  have := hw ℓ
  omega

/-- Grouping allocation degrees by their explicit active-row sets automatically
provides the orthogonality premises and the exact squared-norm decomposition.  [For the stated data and conditions](hyp:ι,κ,B,d,h,hd,G,S,w,s,A,hs,hA), [the stated conclusion holds](goal). -/
-- @node: hidden_active_support_group_energy
lemma hidden_active_support_group_energy {ι κ : Type*} (B d : ℕ) (h : ℝ) (hd : 1 ≤ d)
    (G : Finset ι) (S : ι → Finset κ) (w : ι → κ → ℝ)
    (s : ι → κ → Fin B → ℕ) (A : ι → Finset (Fin B))
    (hs : ∀ i ∈ G, ∀ u ∈ S i, ∀ ℓ, s i u ℓ ≠ 0 ↔ ℓ ∈ A i)
    (hA : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → A i ≠ A j) :
    (∫ y : Fin B → ℝ,
      (∑ i ∈ G, ∑ u ∈ S i, w i u * ∏ ℓ, walshCoeff d h (s i u ℓ) (y ℓ)) ^ 2
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) =
    ∑ i ∈ G, ∫ y : Fin B → ℝ,
      (∑ u ∈ S i, w i u * ∏ ℓ, walshCoeff d h (s i u ℓ) (y ℓ)) ^ 2
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w))) := by
  apply hidden_support_group_energy B d h hd G S w s
  intro i hi j hj hij u hu v hv
  exact hidden_degree_support_witness B (s i u) (s j v) (A i) (A j)
    (hs i hi u hu) (hs j hj v hv) (hA i hi j hj hij)

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

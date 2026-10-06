module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.NestedCells
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.QuadraticProjectionBias

/-! # Spatial Taylor terms and exact projection means

The pilot is constant on each nested cell, so the spatial quadratic Taylor
term is exactly the midpoint-frozen cell sum. Its difference from the exact
conditional quadratic mean has the already established BQ bound.
-/

public section
open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The histogram cells form an exact finite partition, including the endpoint one.  Under [the displayed assumptions and inputs](hyp:K,hK), [the stated conclusion holds](goal). -/
-- @node: iUnion_cell_eq_covariateSpace
lemma iUnion_cell_eq_covariateSpace {K : ℕ} (hK : 0 < K) :
    (⋃ l : Fin K, cell K l) = covariateSpace := by
  ext x
  constructor
  · intro hx
    obtain ⟨l, hl⟩ := mem_iUnion.mp hx
    exact cell_subset_covariateSpace hK l hl
  · intro hx
    obtain ⟨l, hl⟩ := exists_cell_of_mem_covariateSpace hK x hx
    exact mem_iUnion.mpr ⟨l, hl⟩

/-- Integration of a Taylor monomial is exactly the sum over nested cells
with its pilot and coefficient frozen at the cell midpoint.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,n,K,q,hK,hdiv,F,hF,a,idx), [the stated conclusion holds](goal). -/
-- @node: spatial_pilot_monomial_eq_cell_sum
lemma spatial_pilot_monomial_eq_cell_sum (c_f C_f : ℝ) {n K q : ℕ}
    (hK : 0 < K) (hdiv : pilotResolution n ∣ K) (ω : TwoSample n n)
    (F : ℝ → Fin 7 → ℝ) (hF : ∀ i, ContinuousOn (fun x => F x i) covariateSpace)
    (a : (Fin 7 → ℝ) → ℝ) (idx : Fin q → Fin 7) :
    (∫ x in covariateSpace, a (pilot c_f C_f ω x) *
      ∏ j : Fin q, (F x (idx j) - pilot c_f C_f ω x (idx j))) =
    ∑ l : Fin K, ∫ x in cell K l, a (pilot c_f C_f ω (midpoint K l)) *
      ∏ j : Fin q, (F x (idx j) - pilot c_f C_f ω (midpoint K l) (idx j)) := by
  classical
  let f := fun x => a (pilot c_f C_f ω x) *
    ∏ j : Fin q, (F x (idx j) - pilot c_f C_f ω x (idx j))
  let g := fun (l : Fin K) x => a (pilot c_f C_f ω (midpoint K l)) *
    ∏ j : Fin q, (F x (idx j) - pilot c_f C_f ω (midpoint K l) (idx j))
  have heq (l : Fin K) : EqOn f (g l) (cell K l) := by
    intro x hx
    dsimp [f, g]
    rw [pilot_eq_midpoint_of_refinement c_f C_f hK hdiv ω l hx]
  have hi (l : Fin K) : IntegrableOn f (cell K l) := by
    have hg : ContinuousOn (g l) covariateSpace := by
      dsimp [g]
      fun_prop
    have hgint : IntegrableOn (g l) (cell K l) :=
      hg.integrableOn_Icc.mono_set (cell_subset_covariateSpace hK l)
    exact (integrableOn_congr_fun (heq l) (measurableSet_cell K l)).2 hgint
  change (∫ x in covariateSpace, f x) = ∑ l : Fin K, ∫ x in cell K l, g l x
  rw [← iUnion_cell_eq_covariateSpace hK,
    integral_iUnion_fintype (fun l => measurableSet_cell K l)
      (fun l r hlr => cell_disjoint hK hlr) hi]
  apply Finset.sum_congr rfl
  intro l _
  exact setIntegral_congr_fun (measurableSet_cell K l) (heq l)

/-- Every spatial Taylor monomial with exactly one within-cell residual
has zero cell integral: the pilot-derived coefficient and all projected
factors are constant on that cell. This covers every quadratic and cubic
single-residual term without an extra constancy premise.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,q,hP,hK,hdiv,l,i,a,idx), [the stated conclusion holds](goal). -/
-- @node: spatial_pilot_single_residual_cancellation
lemma spatial_pilot_single_residual_cancellation (c_f C_f L : ℝ)
    (P : TransportLaw) (n K q : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (hdiv : pilotResolution n ∣ K) (ω : TwoSample n n)
    (l : Fin K) (i : Fin 7) (a : (Fin 7 → ℝ) → ℝ) (idx : Fin q → Fin 7) :
    (∫ x in cell K l, a (pilot c_f C_f ω x) *
      (∏ j : Fin q, (cellAverage
        (fun y => markedDensityVector c_f C_f L P n hP y (idx j)) K l -
          pilot c_f C_f ω x (idx j))) *
      (markedDensityVector c_f C_f L P n hP x i -
        cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l)) = 0 := by
  apply one_residual_cell_product_cancellation c_f C_f L P n K q hP hK l i
    (fun x => a (pilot c_f C_f ω x))
    (fun j x => cellAverage
      (fun y => markedDensityVector c_f C_f L P n hP y (idx j)) K l -
        pilot c_f C_f ω x (idx j))
    (a (pilot c_f C_f ω (midpoint K l)))
    (fun j => cellAverage
      (fun y => markedDensityVector c_f C_f L P n hP y (idx j)) K l -
        pilot c_f C_f ω (midpoint K l) (idx j))
  · intro x hx
    rw [pilot_eq_midpoint_of_refinement c_f C_f hK hdiv ω l hx]
  · intro j x hx
    rw [pilot_eq_midpoint_of_refinement c_f C_f hK hdiv ω l hx]

/-- The exact quadratic projection bias is the spatial quadratic Taylor
term minus the exact conditional mean of the quadratic statistic.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated conclusion holds](goal). -/
-- @node: quadraticCellProjectionBias_eq_spatial_sub_projectionMean
lemma quadraticCellProjectionBias_eq_spatial_sub_projectionMean (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (ω : TwoSample n n) (A : Bool) :
    quadraticCellProjectionBias c_f C_f L P n (quadraticResolution n) hP ω A =
      (∑ i : Fin 7, ∑ j : Fin 7, ∫ x in covariateSpace,
        (dPhi2 A (pilot c_f C_f ω x) i j / 2) *
          (markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i) *
          (markedDensityVector c_f C_f L P n hP x j - pilot c_f C_f ω x j)) -
        quadraticProjectionMean c_f C_f L P n hP ω A := by
  classical
  have hK : 0 < quadraticResolution n := by
    unfold quadraticResolution dyadicResolution
    split_ifs <;> positivity
  have hterm (i j : Fin 7) := spatial_pilot_monomial_eq_cell_sum c_f C_f hK
    (pilotResolution_dvd_correctionResolutions n).1 ω
    (markedDensityVector c_f C_f L P n hP)
    (markedDensityVector_continuousOn c_f C_f L P n hP)
    (fun v => dPhi2 A v i j / 2) ![i, j]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hterm
  simp_rw [← mul_assoc] at hterm
  rw [quadraticCellProjectionBias_eq_sub_projectionMean]
  simp_rw [hterm]

/-- Roadmap (11) applies directly to the true spatial Taylor term, without
a midpoint approximation or any extra assumption on the training data.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: quadratic_spatial_projection_bias_integrated_sq_sample_rate
lemma quadratic_spatial_projection_bias_integrated_sq_sample_rate (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    (∫ ω, ((∑ i : Fin 7, ∑ j : Fin 7, ∫ x in covariateSpace,
        (dPhi2 A (pilot c_f C_f ω x) i j / 2) *
          (markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i) *
          (markedDensityVector c_f C_f L P n hP x j - pilot c_f C_f ω x j)) -
        quadraticProjectionMean c_f C_f L P n hP ω A) ^ 2 ∂dataLaw P n n) ≤
      (7 : ℝ) ^ 4 * (fourthDerivativeEnvelope c_f C_f) ^ 2 *
        (3 * (1 + C_f) * L) ^ 4 * (2 : ℝ) ^ (1 / 2 : ℝ) *
        (5 : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  simp_rw [← quadraticCellProjectionBias_eq_spatial_sub_projectionMean c_f C_f L P n hP]
  exact quadraticCellProjectionBias_integrated_sq_sample_rate c_f C_f L P n hn hP A

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

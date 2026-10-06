module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.SharpProjectionBias
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.SpatialProjectionBridge

/-! # Exact spatial cubic projection bias

The cubic Taylor projection error is assembled from the exact cell errors.
Nested pilot cells identify it with the spatial Taylor term minus the exact
conditional mean, retaining all seven coordinates and the factor one sixth.
-/

@[expose] public section
open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The exact cubic projection error summed over coordinates and cells.  For [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,A), [the stated object is defined](goal). -/
-- @node: cubicCellProjectionBias
noncomputable def cubicCellProjectionBias (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (ω : TwoSample n n) (A : Bool) : ℝ :=
  let F := markedDensityVector c_f C_f L P n hP
  ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, ∑ l : Fin K,
    let t := pilot c_f C_f ω (midpoint K l)
    let a := fun q => cellAverage (fun y => F y q) K l
    ∫ x in cell K l, (dPhi3 A t i j k / 6) *
      ((F x i - t i) * (F x j - t j) * (F x k - t k) -
        (a i - t i) * (a j - t j) * (a k - t k))

set_option maxHeartbeats 1000000 in
-- Normalizing four nested sums with exact marked-density integrals exceeds the default limit.
/-- The midpoint cell sum is the exact cubic Taylor term minus the
projection polynomial appearing in the conditional mean.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated conclusion holds](goal). -/
-- @node: cubicCellProjectionBias_eq_sub_projectionMean
lemma cubicCellProjectionBias_eq_sub_projectionMean (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (ω : TwoSample n n) (A : Bool) :
    cubicCellProjectionBias c_f C_f L P n (cubicResolution n) hP ω A =
      (∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, ∑ l : Fin (cubicResolution n),
        ∫ x in cell (cubicResolution n) l,
          (dPhi3 A (pilot c_f C_f ω (midpoint (cubicResolution n) l)) i j k / 6) *
            (markedDensityVector c_f C_f L P n hP x i -
              pilot c_f C_f ω (midpoint (cubicResolution n) l) i) *
            (markedDensityVector c_f C_f L P n hP x j -
              pilot c_f C_f ω (midpoint (cubicResolution n) l) j) *
            (markedDensityVector c_f C_f L P n hP x k -
              pilot c_f C_f ω (midpoint (cubicResolution n) l) k)) -
        cubicProjectionMean c_f C_f L P n hP ω A := by
  classical
  let K := cubicResolution n
  let F := markedDensityVector c_f C_f L P n hP
  have hK : 0 < K := by
    dsimp [K]
    unfold cubicResolution dyadicResolution
    split_ifs <;> positivity
  have hcell (i j k : Fin 7) (l : Fin K) (ti tj tk c : ℝ) :
      (∫ x in cell K l, c *
        ((F x i - ti) * (F x j - tj) * (F x k - tk) -
          (cellAverage (fun y => F y i) K l - ti) *
          (cellAverage (fun y => F y j) K l - tj) *
          (cellAverage (fun y => F y k) K l - tk))) =
      (∫ x in cell K l, c * (F x i - ti) * (F x j - tj) * (F x k - tk)) -
      (K : ℝ)⁻¹ * (c * (cellAverage (fun y => F y i) K l - ti) *
        (cellAverage (fun y => F y j) K l - tj) *
        (cellAverage (fun y => F y k) K l - tk)) := by
    have hi := markedDensityVector_continuousOn c_f C_f L P n hP i
    have hj := markedDensityVector_continuousOn c_f C_f L P n hP j
    have hk := markedDensityVector_continuousOn c_f C_f L P n hP k
    have hint : IntegrableOn (fun x => c * (F x i - ti) * (F x j - tj) *
        (F x k - tk)) (cell K l) :=
      (show ContinuousOn _ covariateSpace by dsimp [F]; fun_prop).integrableOn_Icc.mono_set
        (cell_subset_covariateSpace hK l)
    have hfinite : volume (cell K l) ≠ ⊤ := by
      rw [volume_cell hK l]
      exact ENNReal.ofReal_ne_top
    conv_lhs => arg 2; ext x; rw [mul_sub, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    rw [integral_sub hint (integrableOn_const hfinite)]
    rw [setIntegral_const, Measure.real, volume_cell hK l,
      ENNReal.toReal_ofReal (by positivity)]
    simp only [smul_eq_mul, one_div]
    ring
  dsimp only [K, F] at hcell
  rw [cubicProjectionMean_eq]
  unfold cubicCellProjectionBias
  dsimp only
  simp_rw [hcell, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Nested pilot constancy identifies the cubic cell bias with the true
spatial cubic Taylor term minus its exact conditional projection mean.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated conclusion holds](goal). -/
-- @node: cubicCellProjectionBias_eq_spatial_sub_projectionMean
lemma cubicCellProjectionBias_eq_spatial_sub_projectionMean (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (ω : TwoSample n n) (A : Bool) :
    cubicCellProjectionBias c_f C_f L P n (cubicResolution n) hP ω A =
      (∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, ∫ x in covariateSpace,
        (dPhi3 A (pilot c_f C_f ω x) i j k / 6) *
          (markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i) *
          (markedDensityVector c_f C_f L P n hP x j - pilot c_f C_f ω x j) *
          (markedDensityVector c_f C_f L P n hP x k - pilot c_f C_f ω x k)) -
        cubicProjectionMean c_f C_f L P n hP ω A := by
  classical
  have hK : 0 < cubicResolution n := by
    unfold cubicResolution dyadicResolution
    split_ifs <;> positivity
  have hterm (i j k : Fin 7) := spatial_pilot_monomial_eq_cell_sum c_f C_f hK
    (pilotResolution_dvd_correctionResolutions n).2 ω
    (markedDensityVector c_f C_f L P n hP)
    (markedDensityVector_continuousOn c_f C_f L P n hP)
    (fun v => dPhi3 A v i j k / 6) ![i, j, k]
  simp [Fin.prod_univ_three] at hterm
  simp_rw [← mul_assoc] at hterm
  rw [cubicCellProjectionBias_eq_sub_projectionMean]
  simp_rw [hterm]

/-- Summing midpoint-frozen cellwise pilot errors gives their exact spatial L1 norm.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,n,K,hK,hdiv,F,hF,i), [the stated conclusion holds](goal). -/
-- @node: pilot_error_cell_L1_sum_eq
lemma pilot_error_cell_L1_sum_eq (c_f C_f : ℝ) {n K : ℕ}
    (hK : 0 < K) (hdiv : pilotResolution n ∣ K) (ω : TwoSample n n)
    (F : ℝ → ℝ) (hF : ContinuousOn F covariateSpace) (i : Fin 7) :
    (∑ l : Fin K, ∫ x in cell K l,
      |F x - pilot c_f C_f ω (midpoint K l) i|) =
      ∫ x in covariateSpace, |F x - pilot c_f C_f ω x i| := by
  classical
  let f := fun x => |F x - pilot c_f C_f ω x i|
  let g := fun (l : Fin K) x => |F x - pilot c_f C_f ω (midpoint K l) i|
  have heq (l : Fin K) : EqOn f (g l) (cell K l) := by
    intro x hx
    dsimp [f, g]
    rw [pilot_eq_midpoint_of_refinement c_f C_f hK hdiv ω l hx]
  have hi (l : Fin K) : IntegrableOn f (cell K l) := by
    have hg : ContinuousOn (g l) covariateSpace := by
      dsimp [g]
      fun_prop
    exact (integrableOn_congr_fun (heq l) (measurableSet_cell K l)).2
      (hg.integrableOn_Icc.mono_set (cell_subset_covariateSpace hK l))
  change (∑ l : Fin K, ∫ x in cell K l, g l x) = ∫ x in covariateSpace, f x
  rw [← iUnion_cell_eq_covariateSpace hK,
    integral_iUnion_fintype (fun l => measurableSet_cell K l)
      (fun l r hlr => cell_disjoint hK hlr) hi]
  apply Finset.sum_congr rfl
  intro l _
  exact (setIntegral_congr_fun (measurableSet_cell K l) (heq l)).symm

/-- Roadmap (12): after exact single-residual cancellation, the global cubic
bias retains the pilot L1 error, with the constants C1 and C2 of the paper.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,hdiv,A), [the stated conclusion holds](goal). -/
-- @node: cubicCellProjectionBias_abs_le_L1
lemma cubicCellProjectionBias_abs_le_L1 (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (hdiv : pilotResolution n ∣ K) (ω : TwoSample n n) (A : Bool) :
    let B := 3 * (1 + C_f) * L * (1 / (K : ℝ)) ^ holderExponent
    |cubicCellProjectionBias c_f C_f L P n K hP ω A| ≤
      (fourthDerivativeEnvelope c_f C_f / 2) * (7 : ℝ) ^ 2 * B ^ 2 *
        (∑ i : Fin 7, ∫ x in covariateSpace,
          |markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i|) +
      (fourthDerivativeEnvelope c_f C_f / 6) * (7 : ℝ) ^ 3 * B ^ 3 := by
  classical
  dsimp only
  let B := 3 * (1 + C_f) * L * (1 / (K : ℝ)) ^ holderExponent
  let M := fourthDerivativeEnvelope c_f C_f
  let E := fun (i : Fin 7) (l : Fin K) =>
    ∫ x in cell K l, |markedDensityVector c_f C_f L P n hP x i -
      pilot c_f C_f ω (midpoint K l) i|
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  have he (i : Fin 7) := pilot_error_cell_L1_sum_eq c_f C_f hK hdiv ω
    (fun x => markedDensityVector c_f C_f L P n hP x i)
    (markedDensityVector_continuousOn c_f C_f L P n hP i) i
  unfold cubicCellProjectionBias
  dsimp only
  calc
    _ ≤ ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, ∑ l : Fin K,
        (M / 6) * (B ^ 2 * (E i l + E j l + E k l) + B ^ 3 / (K : ℝ)) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro l _
      exact cubic_midpoint_cell_projection_L1_bound c_f C_f L P n K hn hP hK ω A l i j k
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp_rw [show ∀ i, (∑ l : Fin K, E i l) =
        ∫ x in covariateSpace, |markedDensityVector c_f C_f L P n hP x i -
          pilot c_f C_f ω x i| from he]
      simp only [← Finset.mul_sum]
      dsimp [M, B]
      field_simp
      ring

/-- The pilot-sensitive roadmap (12) bound applies to the spatial cubic
Taylor term and the exact projection mean, without extra premises.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: cubic_spatial_projection_bias_abs_le_L1
lemma cubic_spatial_projection_bias_abs_le_L1 (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (ω : TwoSample n n) (A : Bool) :
    let B := 3 * (1 + C_f) * L * (1 / (cubicResolution n : ℝ)) ^ holderExponent
    |(∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, ∫ x in covariateSpace,
        (dPhi3 A (pilot c_f C_f ω x) i j k / 6) *
          (markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i) *
          (markedDensityVector c_f C_f L P n hP x j - pilot c_f C_f ω x j) *
          (markedDensityVector c_f C_f L P n hP x k - pilot c_f C_f ω x k)) -
        cubicProjectionMean c_f C_f L P n hP ω A| ≤
      (fourthDerivativeEnvelope c_f C_f / 2) * (7 : ℝ) ^ 2 * B ^ 2 *
        (∑ i : Fin 7, ∫ x in covariateSpace,
          |markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i|) +
      (fourthDerivativeEnvelope c_f C_f / 6) * (7 : ℝ) ^ 3 * B ^ 3 := by
  dsimp only
  rw [← cubicCellProjectionBias_eq_spatial_sub_projectionMean]
  have hK : 0 < cubicResolution n := by
    unfold cubicResolution dyadicResolution
    split_ifs <;> positivity
  exact cubicCellProjectionBias_abs_le_L1 c_f C_f L P n (cubicResolution n) hn hP hK
    (pilotResolution_dvd_correctionResolutions n).2 ω A

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

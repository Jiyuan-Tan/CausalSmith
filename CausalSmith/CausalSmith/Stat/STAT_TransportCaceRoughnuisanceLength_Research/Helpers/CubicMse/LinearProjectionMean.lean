module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.SpatialTaylorAssembly

/-! # Exact finite-cell representation of the linear projected mean

The spatial linear Taylor term has no projection bias: on any refinement of
the pilot partition it is exactly the weighted sum of cell-average shifts.
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- A linear cell integral is exactly its cell-average shift times cell width.  Under [the displayed assumptions and inputs](hyp:K,hK,l,f,hf,a,t), [the stated conclusion holds](goal). -/
-- @node: integral_linear_cell_eq_average_shift
lemma integral_linear_cell_eq_average_shift {K : ℕ} (hK : 0 < K)
    (l : Fin K) (f : ℝ → ℝ) (hf : IntegrableOn f (cell K l)) (a t : ℝ) :
    (∫ x in cell K l, a * (f x - t)) =
      (K : ℝ)⁻¹ * a * (cellAverage f K l - t) := by
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hfinite : volume (cell K l) ≠ ⊤ := by
    rw [volume_cell hK l]
    exact ENNReal.ofReal_ne_top
  rw [integral_const_mul, integral_sub hf (integrableOn_const hfinite),
    setIntegral_const, Measure.real, volume_cell hK l,
    ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul, one_div, cellAverage]
  field_simp

/-- The linear projected mean has an exact finite-cell formula on every
refinement of the pilot partition, with no spatial approximation error.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,hdiv,A), [the stated conclusion holds](goal). -/
-- @node: linearProjectionMean_eq_cell_sum
lemma linearProjectionMean_eq_cell_sum (c_f C_f L : ℝ) (P : TransportLaw)
    (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (hdiv : pilotResolution n ∣ K) (ω : TwoSample n n) (A : Bool) :
    linearProjectionMean c_f C_f L P n hP ω A =
      (K : ℝ)⁻¹ * ∑ i : Fin 7, ∑ l : Fin K,
        dPhi1 A (pilot c_f C_f ω (midpoint K l)) i *
          (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
            pilot c_f C_f ω (midpoint K l) i) := by
  classical
  have hterm (i : Fin 7) := spatial_pilot_monomial_eq_cell_sum c_f C_f hK
    hdiv ω (markedDensityVector c_f C_f L P n hP)
    (markedDensityVector_continuousOn c_f C_f L P n hP)
    (fun v => dPhi1 A v i) (![i] : Fin 1 → Fin 7)
  simp only [Fin.prod_univ_one, Matrix.cons_val_zero] at hterm
  unfold linearProjectionMean
  simp_rw [hterm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_linear_cell_eq_average_shift hK l _
    ((markedDensityVector_continuousOn c_f C_f L P n hP i).integrableOn_Icc.mono_set
      (cell_subset_covariateSpace hK l))]
  ring

/-- The first coordinate derivative has the explicit rational formula on its
natural domain, where both assignment densities are nonzero.  Under [the displayed assumptions and inputs](hyp:A,v,i,h1,h2), [the stated conclusion holds](goal). -/
-- @node: dPhi1_eq_explicit
lemma dPhi1_eq_explicit (A : Bool) (v : DensityVector) (i : Fin 7)
    (h1 : v 1 ≠ 0) (h2 : v 2 ≠ 0) :
    dPhi1 A v i =
      cubicRatioD1Apply 0 (if A then 4 else 6) 2 (basis i) v -
        cubicRatioD1Apply 0 (if A then 3 else 5) 1 (basis i) v := by
  have heq : Phi A = cubicRatioTerm 0 (if A then 4 else 6) 2 -
      cubicRatioTerm 0 (if A then 3 else 5) 1 := by
    funext y
    cases A <;> simp [Phi, cubicRatioTerm, div_eq_mul_inv] <;> ring
  have hd := (hasFDerivAt_cubicRatioTerm 0 (if A then 4 else 6) 2 v h2).sub
    (hasFDerivAt_cubicRatioTerm 0 (if A then 3 else 5) 1 v h1)
  rw [dPhi1, heq, hd.fderiv, sub_apply,
    cubicRatioD1_apply, cubicRatioD1_apply]

/-- The linear coefficient evaluated at the clipped pilot is measurable with
respect to training; no held-out observation enters this coefficient.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A,x,i), [the stated conclusion holds](goal). -/
@[fun_prop]
-- @node: stronglyMeasurable_dPhi1_pilot_trainingSigma
lemma stronglyMeasurable_dPhi1_pilot_trainingSigma
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) (x : ℝ) (i : Fin 7) :
    StronglyMeasurable[trainingSigma n]
      (fun ω : TwoSample n n => dPhi1 A (pilot c_f C_f ω x) i) := by
  have hexplicit : StronglyMeasurable[trainingSigma n]
      (fun ω : TwoSample n n =>
        cubicRatioD1Apply 0 (if A then 4 else 6) 2 (basis i) (pilot c_f C_f ω x) -
          cubicRatioD1Apply 0 (if A then 3 else 5) 1 (basis i) (pilot c_f C_f ω x)) := by
    unfold cubicRatioD1Apply basis
    fun_prop
  convert hexplicit using 1
  funext ω
  have hv := pilot_mem_clippingRectangle c_f C_f L P n hn hP ω x
  have hcf : 0 < c_f := hP.sourceBounds.1.1
  exact dPhi1_eq_explicit A _ i
    (ne_of_gt (lt_of_lt_of_le (by positivity : 0 < c_f / 4) hv.2.1.1))
    (ne_of_gt (lt_of_lt_of_le (by positivity : 0 < c_f / 4) hv.2.2.1.1))

/-- The spatial linear projected mean is training measurable, as follows from
its exact finite-cell representation.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
@[fun_prop]
-- @node: stronglyMeasurable_linearProjectionMean
lemma stronglyMeasurable_linearProjectionMean (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    StronglyMeasurable[trainingSigma n]
      (fun ω : TwoSample n n => linearProjectionMean c_f C_f L P n hP ω A) := by
  have hK : 0 < pilotResolution n := by
    unfold pilotResolution dyadicResolution
    split_ifs <;> positivity
  simp_rw [linearProjectionMean_eq_cell_sum c_f C_f L P n (pilotResolution n)
    hP hK (dvd_refl _) ]
  fun_prop

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

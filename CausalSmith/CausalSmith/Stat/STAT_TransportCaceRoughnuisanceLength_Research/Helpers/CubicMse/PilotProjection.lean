module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.Cancellation
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CellMoments

/-! # Deterministic cell projection bias for the clipped pilot

The seven marked densities have Hölder modulus `3 (1 + C_f) L`. Cell averaging
therefore introduces at most this modulus times the cell width to power `1/8`.
Together with clipping contraction, this separates eighth-power pilot error
into histogram fluctuation and a deterministic projection contribution.
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Two points in the same histogram cell are separated by at most its width.  Under [the displayed assumptions and inputs](hyp:K,hK,l,x,y,hx,hy), [the stated conclusion holds](goal). -/
-- @node: cell_distance_le_inv
lemma cell_distance_le_inv {K : ℕ} (hK : 0 < K) (l : Fin K)
    (x y : ℝ) (hx : x ∈ cell K l) (hy : y ∈ cell K l) :
    |x - y| ≤ 1 / (K : ℝ) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold cell at hx hy
  split_ifs at hx hy with hlast
  · have hl : (l.val : ℝ) + 1 = K := by exact_mod_cast hlast
    have hwidth : 1 - (l.val : ℝ) / K = 1 / K := by
      apply (eq_div_iff hKr.ne').2
      field_simp
      linarith
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  · rw [abs_le]
    have hwidth : ((l.val : ℝ) + 1) / K - (l.val : ℝ) / K = 1 / K := by ring
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- Averaging on a cell preserves a uniform bound on oscillation around a fixed value.  Under [the displayed assumptions and inputs](hyp:K,hK,l,f,c,B,hf,hB), [the stated conclusion holds](goal). -/
-- @node: cellAverage_sub_le_of_oscillation
lemma cellAverage_sub_le_of_oscillation {K : ℕ} (hK : 0 < K) (l : Fin K)
    (f : ℝ → ℝ) (c B : ℝ) (hf : IntegrableOn f (cell K l))
    (hB : ∀ y ∈ cell K l, |f y - c| ≤ B) :
    |cellAverage f K l - c| ≤ B := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hvol := volume_cell hK l
  have hreal : (volume.restrict (cell K l)).real univ = 1 / (K : ℝ) := by
    rw [Measure.real, Measure.restrict_apply_univ, hvol,
      ENNReal.toReal_ofReal (by positivity)]
  let : IsFiniteMeasure (volume.restrict (cell K l)) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.ofReal_lt_top⟩
  have hi : Integrable (fun y => f y - c) (volume.restrict (cell K l)) :=
    hf.sub (integrable_const c)
  have heq : cellAverage f K l - c = (K : ℝ) * ∫ y in cell K l, f y - c := by
    rw [integral_sub hf (integrable_const c), integral_const]
    simp only [smul_eq_mul]
    rw [hreal]
    unfold cellAverage
    field_simp
  rw [heq, abs_mul, abs_of_pos hKr]
  calc
    (K : ℝ) * |∫ y in cell K l, f y - c| ≤
        (K : ℝ) * ∫ y in cell K l, |f y - c| := by
      gcongr
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => f y - c)
    _ ≤ (K : ℝ) * ∫ _y in cell K l, B := by
      apply mul_le_mul_of_nonneg_left _ hKr.le
      exact integral_mono_ae hi.abs (integrable_const B)
        (ae_restrict_of_forall_mem (measurableSet_cell K l) fun y hy => hB y hy)
    _ = B := by
      rw [integral_const]
      simp only [smul_eq_mul]
      rw [hreal]
      field_simp

/-- Each marked density is continuous on the covariate interval.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,i), [the stated conclusion holds](goal). -/
-- @node: markedDensityVector_continuousOn
lemma markedDensityVector_continuousOn (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n) (i : Fin 7) :
    ContinuousOn (fun x => markedDensityVector c_f C_f L P n hP x i) covariateSpace := by
  have hc (f : ℝ → ℝ) (hf : HolderOn f L) : ContinuousOn f covariateSpace := by
    have hmap : ContinuousOn (fun x : ℝ => ![x]) covariateSpace := by fun_prop
    have hmaps : MapsTo (fun x : ℝ => ![x]) covariateSpace
        {v : Fin 1 → ℝ | v 0 ∈ covariateSpace} := by
      intro x hx; simpa using hx
    simpa [Function.comp_def] using hf.2.1.continuousOn.comp hmap hmaps
  have hs := hc P.fS hP.sourceHolder
  have ht := hc P.fT hP.targetHolder
  have he := hc P.e hP.propensityHolder
  have hm (A z : Bool) := hc (P.m A z) (hP.armHolder.1 A z)
  fin_cases i <;> dsimp [markedDensityVector] <;> fun_prop

/-- The marked-density projection bias is bounded by the common Hölder modulus times cell width.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l,x,hx,i), [the stated conclusion holds](goal). -/
-- @node: markedDensityVector_cell_bias
lemma markedDensityVector_cell_bias (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (l : Fin K) (x : ℝ) (hx : x ∈ cell K l) (i : Fin 7) :
    |cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
      markedDensityVector c_f C_f L P n hP x i| ≤
        3 * (1 + C_f) * L * (1 / (K : ℝ)) ^ holderExponent := by
  have hc := markedDensityVector_continuousOn c_f C_f L P n hP i
  have hint : IntegrableOn (fun y => markedDensityVector c_f C_f L P n hP y i)
      (cell K l) :=
    (hc.integrableOn_Icc).mono_set (cell_subset_covariateSpace hK l)
  apply cellAverage_sub_le_of_oscillation hK l _ _ _ hint
  intro y hy
  have hxy := markedDensityVector_holder_modulus c_f C_f L P n hP y x
    (cell_subset_covariateSpace hK l hy) (cell_subset_covariateSpace hK l hx) i
  refine hxy.trans ?_
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (abs_nonneg _) (cell_distance_le_inv hK l y x hy hx)
      (by norm_num [holderExponent]))
  have hC : 0 ≤ C_f := hP.sourceBounds.2.1.le.trans' (by norm_num)
  have hL : 0 ≤ L := hP.sourceHolder.1.le.trans' (by norm_num)
  positivity

/-- The clipped pilot's eighth-power error is controlled by its centered histogram
fluctuation plus the explicit `H⁸/K₀` projection-bias contribution.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,l,x,hx,i), [the stated conclusion holds](goal). -/
-- @node: pilot_error_eighth_projection_bound
lemma pilot_error_eighth_projection_bound (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (ω : TwoSample n n)
    (l : Fin (pilotResolution n))
    (x : ℝ) (hx : x ∈ cell (pilotResolution n) l) (i : Fin 7) :
    |pilot c_f C_f ω x i - markedDensityVector c_f C_f L P n hP x i| ^ (8 : ℕ) ≤
      2 ^ (7 : ℕ) *
        (|markedHistogram ω i (pilotResolution n) 0 x -
          cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i)
            (pilotResolution n) l| ^ (8 : ℕ) +
          (3 * (1 + C_f) * L) ^ (8 : ℕ) / (pilotResolution n : ℝ)) := by
  have hK : 0 < pilotResolution n := by
    unfold pilotResolution dyadicResolution
    split_ifs <;> positivity
  have hb := markedDensityVector_cell_bias c_f C_f L P n (pilotResolution n)
    hP hK l x hx i
  have hp := pow_le_pow_left₀ (abs_nonneg _) hb 8
  have heq :
      (3 * (1 + C_f) * L * (1 / (pilotResolution n : ℝ)) ^ holderExponent) ^
        (8 : ℕ) = (3 * (1 + C_f) * L) ^ (8 : ℕ) / (pilotResolution n : ℝ) := by
    have hwidth : 0 ≤ 1 / (pilotResolution n : ℝ) :=
      (one_div_pos.mpr (Nat.cast_pos.mpr hK)).le
    rw [mul_pow, ← Real.rpow_mul_natCast hwidth,
      show holderExponent * ((8 : ℕ) : ℝ) = 1 by norm_num [holderExponent], Real.rpow_one]
    ring
  rw [heq] at hp
  exact (pilot_error_eighth_split c_f C_f L P n hn hP ω x
    (cell_subset_covariateSpace hK l hx) i
    (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i)
      (pilotResolution n) l)).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hp) (by norm_num))

/-- The deterministic eighth-power pilot bias has precisely the constant in equation (6).  Under [the displayed assumptions and inputs](hyp:n,hn,C_f,L), [the stated conclusion holds](goal). -/
-- @node: pilot_eighth_projection_bias_rate
lemma pilot_eighth_projection_bias_rate (n : ℕ) (hn : threshold ≤ n)
    (C_f L : ℝ) :
    2 ^ (7 : ℕ) * ((3 * (1 + C_f) * L) ^ (8 : ℕ) / (pilotResolution n : ℝ)) ≤
      2 ^ (8 : ℕ) * (3 * (1 + C_f) * L) ^ (8 : ℕ) *
        (5 : ℝ) ^ (4 / 5 : ℝ) * (n : ℝ) ^ (-(4 / 5 : ℝ)) := by
  have h := mul_le_mul_of_nonneg_left (pilotResolution_inv_le_sample_rate n hn)
    (show 0 ≤ (2 : ℝ) ^ (7 : ℕ) * (3 * (1 + C_f) * L) ^ (8 : ℕ) by positivity)
  convert h using 1 <;> first | rfl | ring

/-- Clipping and the exact dyadic bias rate reduce the pointwise pilot error to
its centered histogram fluctuation, without a stochastic bound as a premise.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,l,x,hx,i), [the stated conclusion holds](goal). -/
-- @node: pilot_error_eighth_sample_rate_split
lemma pilot_error_eighth_sample_rate_split (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (ω : TwoSample n n)
    (l : Fin (pilotResolution n))
    (x : ℝ) (hx : x ∈ cell (pilotResolution n) l) (i : Fin 7) :
    |pilot c_f C_f ω x i - markedDensityVector c_f C_f L P n hP x i| ^ (8 : ℕ) ≤
      2 ^ (7 : ℕ) *
        |markedHistogram ω i (pilotResolution n) 0 x -
          cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i)
            (pilotResolution n) l| ^ (8 : ℕ) +
      2 ^ (8 : ℕ) * (3 * (1 + C_f) * L) ^ (8 : ℕ) *
        (5 : ℝ) ^ (4 / 5 : ℝ) * (n : ℝ) ^ (-(4 / 5 : ℝ)) := by
  have h := pilot_error_eighth_projection_bound c_f C_f L P n hn hP ω l x hx i
  rw [mul_add] at h
  exact h.trans (add_le_add_right (pilot_eighth_projection_bias_rate n hn C_f L) _)

/-- After removing the two one-residual terms, the quadratic projection
error is exactly the product of the two within-cell residuals.  Under [the displayed assumptions and inputs](hyp:K,hK,l,f,g,hf,hg,d,e,c,hf0,hg0), [the stated conclusion holds](goal). -/
-- @node: quadratic_cell_projection_identity
lemma quadratic_cell_projection_identity {K : ℕ} (hK : 0 < K) (l : Fin K)
    (f g : ℝ → ℝ) (hf : ContinuousOn f covariateSpace)
    (hg : ContinuousOn g covariateSpace) (d e c : ℝ)
    (hf0 : (∫ x in cell K l, f x) = 0)
    (hg0 : (∫ x in cell K l, g x) = 0) :
    (∫ x in cell K l, c * ((d + f x) * (e + g x) - d * e)) =
      ∫ x in cell K l, c * (f x * g x) := by
  have hi (u : ℝ → ℝ) (hu : ContinuousOn u covariateSpace) :
      IntegrableOn u (cell K l) :=
    hu.integrableOn_Icc.mono_set (cell_subset_covariateSpace hK l)
  have hfg : ContinuousOn (fun x => c * (f x * g x)) covariateSpace := by fun_prop
  have hdf : ContinuousOn (fun x => (c * e) * f x) covariateSpace := by fun_prop
  have hdg : ContinuousOn (fun x => (c * d) * g x) covariateSpace := by fun_prop
  have hsum : ContinuousOn (fun x => c * (f x * g x) + (c * e) * f x)
      covariateSpace := by fun_prop
  have hpoint : (fun x => c * ((d + f x) * (e + g x) - d * e)) =
      (fun x => (c * (f x * g x) + (c * e) * f x) + (c * d) * g x) := by
    funext x
    ring
  rw [hpoint, integral_add (hi _ hsum) (hi _ hdg),
    integral_add (hi _ hfg) (hi _ hdf)]
  simp only [integral_const_mul, hf0, hg0, mul_zero, add_zero]

/-- The cubic projection error has precisely the three two-residual terms
and the three-residual term; every single-residual contribution cancels.  Under [the displayed assumptions and inputs](hyp:K,hK,l,f,g,h,hf,hg,hh,d,e,b,c,hf0,hg0,hh0), [the stated conclusion holds](goal). -/
-- @node: cubic_cell_projection_identity
lemma cubic_cell_projection_identity {K : ℕ} (hK : 0 < K) (l : Fin K)
    (f g h : ℝ → ℝ) (hf : ContinuousOn f covariateSpace)
    (hg : ContinuousOn g covariateSpace) (hh : ContinuousOn h covariateSpace)
    (d e b c : ℝ)
    (hf0 : (∫ x in cell K l, f x) = 0)
    (hg0 : (∫ x in cell K l, g x) = 0)
    (hh0 : (∫ x in cell K l, h x) = 0) :
    (∫ x in cell K l, c * ((d + f x) * (e + g x) * (b + h x) - d * e * b)) =
      ∫ x in cell K l, c *
        (d * g x * h x + e * f x * h x + b * f x * g x + f x * g x * h x) := by
  let R : ℝ → ℝ := fun x => c *
    (d * g x * h x + e * f x * h x + b * f x * g x + f x * g x * h x)
  have hi (u : ℝ → ℝ) (hu : ContinuousOn u covariateSpace) :
      IntegrableOn u (cell K l) :=
    hu.integrableOn_Icc.mono_set (cell_subset_covariateSpace hK l)
  have hR : ContinuousOn R covariateSpace := by dsimp [R]; fun_prop
  have h1 : ContinuousOn (fun x => (c * e * b) * f x) covariateSpace := by fun_prop
  have h2 : ContinuousOn (fun x => (c * d * b) * g x) covariateSpace := by fun_prop
  have h3 : ContinuousOn (fun x => (c * d * e) * h x) covariateSpace := by fun_prop
  have hR1 : ContinuousOn (fun x => R x + (c * e * b) * f x)
      covariateSpace := hR.add h1
  have hR2 : ContinuousOn (fun x => (R x + (c * e * b) * f x) + (c * d * b) * g x)
      covariateSpace := hR1.add h2
  have hpoint :
      (fun x => c * ((d + f x) * (e + g x) * (b + h x) - d * e * b)) =
      (fun x => ((R x + (c * e * b) * f x) + (c * d * b) * g x) +
        (c * d * e) * h x) := by
    funext x
    dsimp [R]
    ring
  rw [hpoint, integral_add (hi _ hR2) (hi _ h3),
    integral_add (hi _ hR1) (hi _ h2), integral_add (hi _ hR) (hi _ h1)]
  simp only [integral_const_mul, hf0, hg0, hh0, mul_zero, add_zero]
  simp only [R, integral_const_mul]

/-- Within-cell marked-density residuals retain the already proved continuity.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,l,i), [the stated conclusion holds](goal). -/
-- @node: markedDensity_cell_residual_continuousOn
lemma markedDensity_cell_residual_continuousOn (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (l : Fin K) (i : Fin 7) :
    ContinuousOn (fun x => markedDensityVector c_f C_f L P n hP x i -
      cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l)
      covariateSpace := by
  have hf := markedDensityVector_continuousOn c_f C_f L P n hP i
  fun_prop

/-- Exact quadratic Taylor projection identity for the actual marked densities
and arbitrary cell values of the pilot and Taylor coefficient.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l,i,j,ti,tj,c), [the stated conclusion holds](goal). -/
-- @node: markedDensity_quadratic_cell_projection_identity
lemma markedDensity_quadratic_cell_projection_identity (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (l : Fin K) (i j : Fin 7) (ti tj c : ℝ) :
    let F := markedDensityVector c_f C_f L P n hP
    let ai := cellAverage (fun y => F y i) K l
    let aj := cellAverage (fun y => F y j) K l
    (∫ x in cell K l, c * ((F x i - ti) * (F x j - tj) - (ai - ti) * (aj - tj))) =
      ∫ x in cell K l, c * ((F x i - ai) * (F x j - aj)) := by
  dsimp only
  convert quadratic_cell_projection_identity hK l
    (fun x => markedDensityVector c_f C_f L P n hP x i -
      cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l)
    (fun x => markedDensityVector c_f C_f L P n hP x j -
      cellAverage (fun y => markedDensityVector c_f C_f L P n hP y j) K l)
    (markedDensity_cell_residual_continuousOn c_f C_f L P n K hP l i)
    (markedDensity_cell_residual_continuousOn c_f C_f L P n K hP l j)
    (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l - ti)
    (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y j) K l - tj) c
    (one_residual_cell_cancellation c_f C_f L P n K hP hK l i)
    (one_residual_cell_cancellation c_f C_f L P n K hP hK l j) using 1
  congr 1
  funext x
  ring

/-- Exact cubic Taylor projection identity for the actual marked densities.
Only products with two or three within-cell residuals survive integration.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l,i,j,k,ti,tj,tk,c), [the stated conclusion holds](goal). -/
-- @node: markedDensity_cubic_cell_projection_identity
lemma markedDensity_cubic_cell_projection_identity (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (l : Fin K) (i j k : Fin 7) (ti tj tk c : ℝ) :
    let F := markedDensityVector c_f C_f L P n hP
    let ai := cellAverage (fun y => F y i) K l
    let aj := cellAverage (fun y => F y j) K l
    let ak := cellAverage (fun y => F y k) K l
    let ei := fun x => F x i - ai
    let ej := fun x => F x j - aj
    let ek := fun x => F x k - ak
    (∫ x in cell K l, c * ((F x i - ti) * (F x j - tj) * (F x k - tk) -
      (ai - ti) * (aj - tj) * (ak - tk))) =
      ∫ x in cell K l, c * ((ai - ti) * ej x * ek x +
        (aj - tj) * ei x * ek x + (ak - tk) * ei x * ej x + ei x * ej x * ek x) := by
  dsimp only
  convert cubic_cell_projection_identity hK l
    (fun x => markedDensityVector c_f C_f L P n hP x i -
      cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l)
    (fun x => markedDensityVector c_f C_f L P n hP x j -
      cellAverage (fun y => markedDensityVector c_f C_f L P n hP y j) K l)
    (fun x => markedDensityVector c_f C_f L P n hP x k -
      cellAverage (fun y => markedDensityVector c_f C_f L P n hP y k) K l)
    (markedDensity_cell_residual_continuousOn c_f C_f L P n K hP l i)
    (markedDensity_cell_residual_continuousOn c_f C_f L P n K hP l j)
    (markedDensity_cell_residual_continuousOn c_f C_f L P n K hP l k)
    (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l - ti)
    (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y j) K l - tj)
    (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y k) K l - tk) c
    (one_residual_cell_cancellation c_f C_f L P n K hP hK l i)
    (one_residual_cell_cancellation c_f C_f L P n K hP hK l j)
    (one_residual_cell_cancellation c_f C_f L P n K hP hK l k) using 1
  congr 1
  funext x
  ring

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ExactBiasAssembly
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.IntegratedRemainder

/-! # Pilot-sensitive cubic projection bias

The surviving two-residual terms retain the absolute training shifts rather
than a uniform envelope. This is the cellwise estimate needed in roadmap (12).
The integrated pilot moment supplies the L1 control in roadmap (7).
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The four surviving cubic residual terms are bounded while retaining each
projected pilot error as a factor.  Under [the displayed assumptions and inputs](hyp:K,hK,l,f,g,h,hf,hg,hh,d,e,b,c,B,hB,hfB,hgB,hhB), [the stated conclusion holds](goal). -/
-- @node: cubic_residual_integral_abs_le_shifts
lemma cubic_residual_integral_abs_le_shifts {K : ℕ} (hK : 0 < K) (l : Fin K)
    (f g h : ℝ → ℝ) (hf : ContinuousOn f covariateSpace)
    (hg : ContinuousOn g covariateSpace) (hh : ContinuousOn h covariateSpace)
    (d e b c B : ℝ) (hB : 0 ≤ B)
    (hfB : ∀ x ∈ cell K l, |f x| ≤ B)
    (hgB : ∀ x ∈ cell K l, |g x| ≤ B)
    (hhB : ∀ x ∈ cell K l, |h x| ≤ B) :
    |∫ x in cell K l, c *
      (d * g x * h x + e * f x * h x + b * f x * g x + f x * g x * h x)| ≤
      |c| * ((|d| + |e| + |b|) * B ^ 2 + B ^ 3) / (K : ℝ) := by
  let R := fun x => c *
    (d * g x * h x + e * f x * h x + b * f x * g x + f x * g x * h x)
  have hi : IntegrableOn R (cell K l) := by
    exact (show ContinuousOn R covariateSpace by dsimp [R]; fun_prop).integrableOn_Icc.mono_set
      (cell_subset_covariateSpace hK l)
  have hfinite : volume (cell K l) ≠ ⊤ := by
    rw [volume_cell hK l]
    exact ENNReal.ofReal_ne_top
  have hpoint (x : ℝ) (hx : x ∈ cell K l) :
      |R x| ≤ |c| * ((|d| + |e| + |b|) * B ^ 2 + B ^ 3) := by
    have h1 : |d * g x * h x| ≤ |d| * B ^ 2 := by
      simp only [abs_mul]
      calc
        _ ≤ |d| * B * B := by
          gcongr
          · exact hgB x hx
          · exact hhB x hx
        _ = _ := by ring
    have h2 : |e * f x * h x| ≤ |e| * B ^ 2 := by
      simp only [abs_mul]
      calc
        _ ≤ |e| * B * B := by
          gcongr
          · exact hfB x hx
          · exact hhB x hx
        _ = _ := by ring
    have h3 : |b * f x * g x| ≤ |b| * B ^ 2 := by
      simp only [abs_mul]
      calc
        _ ≤ |b| * B * B := by
          gcongr
          · exact hfB x hx
          · exact hgB x hx
        _ = _ := by ring
    have h4 : |f x * g x * h x| ≤ B ^ 3 := by
      simp only [abs_mul]
      calc
        _ ≤ B * B * B := by
          gcongr
          · exact hfB x hx
          · exact hgB x hx
          · exact hhB x hx
        _ = _ := by ring
    dsimp [R]
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
    calc
      |_ + _ + _ + _| ≤
          |d * g x * h x| + |e * f x * h x| + |b * f x * g x| + |f x * g x * h x| :=
        (abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ |d| * B ^ 2 + |e| * B ^ 2 + |b| * B ^ 2 + B ^ 3 :=
        add_le_add (add_le_add (add_le_add h1 h2) h3) h4
      _ = _ := by ring
  calc
    _ ≤ ∫ x in cell K l, |R x| := abs_integral_le_integral_abs
    _ ≤ ∫ _x in cell K l, |c| * ((|d| + |e| + |b|) * B ^ 2 + B ^ 3) :=
      setIntegral_mono_on hi.abs (integrableOn_const hfinite)
        (measurableSet_cell K l) hpoint
    _ = _ := by
      rw [setIntegral_const, Measure.real, volume_cell hK l,
        ENNReal.toReal_ofReal (by positivity)]
      simp only [smul_eq_mul]
      ring

/-- Exact single-residual cancellation yields a cubic cell bias bound with
three individual projected pilot errors, as required by roadmap (12).  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l,i,j,k,ti,tj,tk,c), [the stated conclusion holds](goal). -/
-- @node: markedDensity_cubic_cell_projection_abs_le_shifts
lemma markedDensity_cubic_cell_projection_abs_le_shifts (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (l : Fin K) (i j k : Fin 7) (ti tj tk c : ℝ) :
    let F := markedDensityVector c_f C_f L P n hP
    let ai := cellAverage (fun y => F y i) K l
    let aj := cellAverage (fun y => F y j) K l
    let ak := cellAverage (fun y => F y k) K l
    let B := 3 * (1 + C_f) * L * (1 / (K : ℝ)) ^ holderExponent
    |∫ x in cell K l, c * ((F x i - ti) * (F x j - tj) * (F x k - tk) -
      (ai - ti) * (aj - tj) * (ak - tk))| ≤
      |c| * ((|ai - ti| + |aj - tj| + |ak - tk|) * B ^ 2 + B ^ 3) / (K : ℝ) := by
  dsimp only
  rw [markedDensity_cubic_cell_projection_identity c_f C_f L P n K hP hK l i j k ti tj tk c]
  apply cubic_residual_integral_abs_le_shifts hK l
    _ _ _
    (markedDensity_cell_residual_continuousOn c_f C_f L P n K hP l i)
    (markedDensity_cell_residual_continuousOn c_f C_f L P n K hP l j)
    (markedDensity_cell_residual_continuousOn c_f C_f L P n K hP l k)
  · have hC : 0 ≤ C_f := hP.sourceBounds.2.1.le.trans' (by norm_num)
    have hL : 0 ≤ L := hP.sourceHolder.1.le.trans' (by norm_num)
    positivity
  · intro x hx
    exact markedDensity_sub_cellAverage_abs_le c_f C_f L P n K hP hK l x hx i
  · intro x hx
    exact markedDensity_sub_cellAverage_abs_le c_f C_f L P n K hP hK l x hx j
  · intro x hx
    exact markedDensity_sub_cellAverage_abs_le c_f C_f L P n K hP hK l x hx k

/-- A projected error divided by the cell resolution is at most the cell's
L1 error; no uniform bound on the pilot error is substituted.  Under [the displayed assumptions and inputs](hyp:K,hK,l,f,t,hf), [the stated conclusion holds](goal). -/
-- @node: cellAverage_sub_abs_div_le_integral_abs
lemma cellAverage_sub_abs_div_le_integral_abs {K : ℕ} (hK : 0 < K)
    (l : Fin K) (f : ℝ → ℝ) (t : ℝ) (hf : IntegrableOn f (cell K l)) :
    |cellAverage f K l - t| / (K : ℝ) ≤ ∫ x in cell K l, |f x - t| := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hfinite : volume (cell K l) ≠ ⊤ := by
    rw [volume_cell hK l]
    exact ENNReal.ofReal_ne_top
  have heq : cellAverage f K l - t = (K : ℝ) * ∫ x in cell K l, f x - t := by
    rw [integral_sub hf (integrableOn_const hfinite), setIntegral_const,
      Measure.real, volume_cell hK l, ENNReal.toReal_ofReal (by positivity)]
    dsimp [cellAverage]
    field_simp
  rw [heq, abs_mul, abs_of_pos hKr, mul_div_cancel_left₀ _ hKr.ne']
  exact abs_integral_le_integral_abs

/-- Roadmap (7): the clipped pilot's spatial L1 error has the same squared
moment rate as its pointwise error, by Jensen and Fubini.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,i), [the stated conclusion holds](goal). -/
-- @node: pilot_error_L1_second_moment
lemma pilot_error_L1_second_moment (c_f C_f L : ℝ) (P : TransportLaw)
    (n : ℕ) (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (i : Fin 7) :
    (∫ ω, (∫ x in covariateSpace,
      |pilot c_f C_f ω x i - markedDensityVector c_f C_f L P n hP x i|) ^ 2
        ∂dataLaw P n n) ≤
      (2 * (1 + C_f + C_f ^ 2) * (5 : ℝ) ^ (1 / 5 : ℝ) +
        (2 : ℝ) ^ (5 / 4 : ℝ) * (3 * (1 + C_f) * L) ^ 2 *
          (5 : ℝ) ^ (1 / 5 : ℝ)) * (n : ℝ) ^ (-(1 / 5 : ℝ)) := by
  classical
  let μ := dataLaw P n n
  let ν := volume.restrict covariateSpace
  let : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure μ := by
    dsimp [μ]
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
    infer_instance
  let : IsProbabilityMeasure ν := ⟨by simp [ν, covariateSpace]⟩
  let F := covariateSpace.indicator
    (fun x => markedDensityVector c_f C_f L P n hP x i)
  let g := fun (ω : TwoSample n n) (x : ℝ) => |pilot c_f C_f ω x i - F x|
  have hg : Measurable (Function.uncurry g) := by
    have hF := measurable_markedDensityVector_indicator c_f C_f L P n hP i
    dsimp [g, F, Function.uncurry]
    fun_prop
  have hC : 0 ≤ C_f := hP.sourceBounds.2.1.le.trans' (by norm_num)
  have hb (ω : TwoSample n n) : ∀ᵐ x ∂ν, |g ω x| ≤ 2 * C_f := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro x hx
    change x ∈ covariateSpace at hx
    dsimp [g, F]
    rw [Set.indicator_of_mem hx, abs_abs]
    simpa only [two_mul] using (abs_sub _ _).trans (add_le_add
      (clippingRectangle_coordinate_abs_le c_f C_f hP.sourceBounds.1.1 hC _
        (pilot_mem_clippingRectangle c_f C_f L P n hn hP ω x) i)
      (clippingRectangle_coordinate_abs_le c_f C_f hP.sourceBounds.1.1 hC _
        (markedDensityVector_mem_clippingRectangle c_f C_f L P n hP x hx) i))
  have hm : ∀ᵐ x ∂ν, (∫ ω, (g ω x) ^ 2 ∂μ) ≤
      (2 * (1 + C_f + C_f ^ 2) * (5 : ℝ) ^ (1 / 5 : ℝ) +
        (2 : ℝ) ^ (5 / 4 : ℝ) * (3 * (1 + C_f) * L) ^ 2 *
          (5 : ℝ) ^ (1 / 5 : ℝ)) * (n : ℝ) ^ (-(1 / 5 : ℝ)) := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro x hx
    change x ∈ covariateSpace at hx
    simpa only [g, F, Set.indicator_of_mem hx, sq_abs, μ] using
      pilot_second_moment c_f C_f L P n hn hP i x hx
  have hj := integrated_second_moment_le_of_majorant μ ν g g (2 * C_f) _ hg hb
    (fun ω => Filter.Eventually.of_forall fun x => (abs_of_nonneg (abs_nonneg _)).le) hm
  have heq (ω : TwoSample n n) :
      (∫ x in covariateSpace,
        |pilot c_f C_f ω x i - markedDensityVector c_f C_f L P n hP x i|) =
      ∫ x, g ω x ∂ν := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change x ∈ covariateSpace at hx
    dsimp [g, F]
    rw [Set.indicator_of_mem hx]
  simpa only [heq, μ] using hj

/-- The exact cubic Taylor coefficient gives a cell bias controlled by the
three L1 pilot errors and the third power of the Hölder projection modulus.
Summing this inequality yields the constants C1 and C2 in roadmap (12).  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,A,l,i,j,k), [the stated conclusion holds](goal). -/
-- @node: cubic_midpoint_cell_projection_L1_bound
lemma cubic_midpoint_cell_projection_L1_bound (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K) (ω : TwoSample n n)
    (A : Bool) (l : Fin K) (i j k : Fin 7) :
    let F := markedDensityVector c_f C_f L P n hP
    let t := pilot c_f C_f ω (midpoint K l)
    let a := fun q => cellAverage (fun y => F y q) K l
    let B := 3 * (1 + C_f) * L * (1 / (K : ℝ)) ^ holderExponent
    |∫ x in cell K l, (dPhi3 A t i j k / 6) *
      ((F x i - t i) * (F x j - t j) * (F x k - t k) -
        (a i - t i) * (a j - t j) * (a k - t k))| ≤
      (fourthDerivativeEnvelope c_f C_f / 6) *
        (B ^ 2 * ((∫ x in cell K l, |F x i - t i|) +
          (∫ x in cell K l, |F x j - t j|) +
          (∫ x in cell K l, |F x k - t k|)) + B ^ 3 / (K : ℝ)) := by
  dsimp only
  let F := markedDensityVector c_f C_f L P n hP
  let t := pilot c_f C_f ω (midpoint K l)
  let B := 3 * (1 + C_f) * L * (1 / (K : ℝ)) ^ holderExponent
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hB : 0 ≤ B := by
    have hC : 0 ≤ C_f := hP.sourceBounds.2.1.le.trans' (by norm_num)
    have hL : 0 ≤ L := hP.sourceHolder.1.le.trans' (by norm_num)
    dsimp [B]
    positivity
  have hc : |dPhi3 A t i j k / 6| ≤ fourthDerivativeEnvelope c_f C_f / 6 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    exact div_le_div_of_nonneg_right
      (dPhi3_abs_le c_f C_f hP.sourceBounds.1 hP.sourceBounds.2.1 A t
        (pilot_mem_clippingRectangle c_f C_f L P n hn hP ω (midpoint K l)) i j k)
      (by norm_num)
  have hshift (q : Fin 7) :
      |cellAverage (fun y => F y q) K l - t q| / (K : ℝ) ≤
        ∫ x in cell K l, |F x q - t q| :=
    cellAverage_sub_abs_div_le_integral_abs hK l _ _
      ((markedDensityVector_continuousOn c_f C_f L P n hP q).integrableOn_Icc.mono_set
        (cell_subset_covariateSpace hK l))
  have hs := add_le_add (add_le_add (hshift i) (hshift j)) (hshift k)
  calc
    _ ≤ |dPhi3 A t i j k / 6| *
        ((|cellAverage (fun y => F y i) K l - t i| +
          |cellAverage (fun y => F y j) K l - t j| +
          |cellAverage (fun y => F y k) K l - t k|) * B ^ 2 + B ^ 3) / (K : ℝ) :=
      markedDensity_cubic_cell_projection_abs_le_shifts c_f C_f L P n K hP hK l
        i j k (t i) (t j) (t k) (dPhi3 A t i j k / 6)
    _ ≤ (fourthDerivativeEnvelope c_f C_f / 6) *
        ((|cellAverage (fun y => F y i) K l - t i| +
          |cellAverage (fun y => F y j) K l - t j| +
          |cellAverage (fun y => F y k) K l - t k|) * B ^ 2 + B ^ 3) / (K : ℝ) := by
      apply div_le_div_of_nonneg_right _ hKr.le
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (fourthDerivativeEnvelope c_f C_f / 6) *
        (B ^ 2 * (|cellAverage (fun y => F y i) K l - t i| / (K : ℝ) +
          |cellAverage (fun y => F y j) K l - t j| / (K : ℝ) +
          |cellAverage (fun y => F y k) K l - t k| / (K : ℝ)) + B ^ 3 / (K : ℝ)) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _
        (by
          have hcf := hP.sourceBounds.1.1
          unfold fourthDerivativeEnvelope
          positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hs (sq_nonneg B)) le_rfl

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

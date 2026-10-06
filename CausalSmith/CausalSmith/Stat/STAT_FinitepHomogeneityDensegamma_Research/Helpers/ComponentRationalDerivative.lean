module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentPropensityDerivative

/-! Exact derivatives and uniform bounds for the rational record-density correction. -/
@[expose] public section
noncomputable section
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The only rational amplitude factor in the marked-record copula correction, with `t` equal to the squared propensity frame field. This statement assumes [the t parameter](hyp:t), [the a parameter](hyp:a). [This is the stated defined object](goal). -/
-- @node: correctionFactor
def correctionFactor (t a : ℝ) : ℝ := a * (1 - a^2*t) / (1 - a^2)

/-- The first amplitude derivative of the rational correction factor. This statement assumes [the t parameter](hyp:t), [the a parameter](hyp:a). [This is the stated defined object](goal). -/
-- @node: correctionSlope
def correctionSlope (t a : ℝ) : ℝ :=
  1 + (1-t) * (a^2 * (3-a^2)) / (1-a^2)^2

/-- The second amplitude derivative of the rational correction factor. This statement assumes [the t parameter](hyp:t), [the a parameter](hyp:a). [This is the stated defined object](goal). -/
-- @node: correctionCurvature
def correctionCurvature (t a : ℝ) : ℝ :=
  (1-t) * (2*a*(3+a^2)) / (1-a^2)^3

/-- The quotient rule gives the exact first derivative away from the two poles. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: correctionFactor_hasDerivAt
lemma correctionFactor_hasDerivAt (t a : ℝ) (ha : 1-a^2 ≠ 0) :
    HasDerivAt (correctionFactor t) (correctionSlope t a) a := by
  have hid := hasDerivAt_id a
  have hn := hid.mul ((hasDerivAt_const a (1:ℝ)).sub ((hid.pow 2).mul_const t))
  have hd := (hasDerivAt_const a (1:ℝ)).sub (hid.pow 2)
  convert hn.div hd ha using 1 <;>
    first | rfl | (simp [correctionFactor, correctionSlope, id] <;> field_simp <;> ring)

/-- A second application of the quotient rule gives the exact curvature. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: correctionSlope_hasDerivAt
lemma correctionSlope_hasDerivAt (t a : ℝ) (ha : 1-a^2 ≠ 0) :
    HasDerivAt (correctionSlope t) (correctionCurvature t a) a := by
  have hid := hasDerivAt_id a
  have hn := ((hid.pow 2).mul ((hasDerivAt_const a (3:ℝ)).sub (hid.pow 2))).const_mul (1-t)
  have hd := ((hasDerivAt_const a (1:ℝ)).sub (hid.pow 2)).pow 2
  have hh := (hn.div hd (pow_ne_zero 2 ha)).const_add 1
  convert hh using 1 <;>
    first | rfl | (simp [correctionSlope, correctionCurvature, id] <;> field_simp <;> ring)

/-- On the amplitude rectangle the denominator is uniformly bounded away from zero. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: correction_denominator_bounds
lemma correction_denominator_bounds (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1/16) :
    0 ≤ a^2 ∧ a^2 ≤ 1/256 ∧ 15/16 ≤ 1-a^2 ∧ 1-a^2 ≤ 1 := by
  have hs := mul_nonneg ha.1 (sub_nonneg.mpr ha.2)
  have ht := sq_nonneg (a - 1/16)
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith [sq_nonneg a]

/-- The first derivative of the rational correction is bounded by two when the squared frame field lies between zero and two. This statement assumes [the ht condition](hyp:ht), [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: correctionSlope_bound
lemma correctionSlope_bound (t a : ℝ) (ht : 0 ≤ t ∧ t ≤ 2)
    (ha : 0 ≤ a ∧ a ≤ 1/16) : |correctionSlope t a| ≤ 2 := by
  have hd := correction_denominator_bounds a ha
  have hpos : 0 < 1-a^2 := by linarith [hd.2.2.1]
  have ht' : |1-t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hn : 0 ≤ a^2*(3-a^2) := mul_nonneg hd.1 (by linarith [hd.2.1])
  have hn' : a^2*(3-a^2) ≤ 3/256 := by nlinarith [sq_nonneg (a^2)]
  have hden : (15/16:ℝ)^2 ≤ (1-a^2)^2 := by nlinarith [hd.2.2.1]
  have hb : |(1-t) * (a^2*(3-a^2)) / (1-a^2)^2| ≤ 1 := by
    simp only [abs_div, abs_mul, abs_of_nonneg hn, abs_pow, abs_of_pos hpos]
    apply (div_le_one (by positivity : 0 < (1-a^2)^2)).mpr
    have hm := mul_le_mul_of_nonneg_right ht' hn
    nlinarith
  unfold correctionSlope
  calc
    |1 + (1-t) * (a^2*(3-a^2)) / (1-a^2)^2| ≤
        |(1:ℝ)| + |(1-t) * (a^2*(3-a^2)) / (1-a^2)^2| := abs_add_le _ _
    _ ≤ 2 := by norm_num at *; linarith

/-- The second derivative of the rational correction is bounded by one on the same rectangle. This statement assumes [the ht condition](hyp:ht), [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: correctionCurvature_bound
lemma correctionCurvature_bound (t a : ℝ) (ht : 0 ≤ t ∧ t ≤ 2)
    (ha : 0 ≤ a ∧ a ≤ 1/16) : |correctionCurvature t a| ≤ 1 := by
  have hd := correction_denominator_bounds a ha
  have hpos : 0 < 1-a^2 := by linarith [hd.2.2.1]
  have ht' : |1-t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hn : 0 ≤ 2*a*(3+a^2) := mul_nonneg (mul_nonneg (by norm_num) ha.1) (by positivity)
  have hn' : 2*a*(3+a^2) ≤ 1/2 := by
    have hh := mul_le_mul ha.2 (show 3+a^2 ≤ 4 by linarith [hd.2.1])
      (by positivity : 0 ≤ 3+a^2) (by norm_num : (0:ℝ) ≤ 1/16)
    nlinarith
  have hden : (15/16:ℝ)^3 ≤ (1-a^2)^3 := by
    gcongr
    exact hd.2.2.1
  unfold correctionCurvature
  rw [abs_div, abs_mul, abs_of_nonneg hn, abs_of_nonneg (by positivity : 0 ≤ (1-a^2)^3)]
  apply (div_le_one (by positivity : 0 < (1-a^2)^3)).mpr
  have hm := mul_le_mul_of_nonneg_right ht' hn
  nlinarith

/-- The marked-record interaction is a bilinear coordinate product minus precisely the rational correction whose derivatives were bounded above. [This is the stated conclusion](goal). -/
-- @node: copulaZeta_correctionFactor
lemma copulaZeta_correctionFactor (ν : Bool) (K M : ℕ) (a u : ℝ)
    (idx : CopulaIndex K M) (x : unitInterval) :
    copulaZeta ν K M a u idx x =
      u * (a * frameField K (fun j => signVal (idx.2 j).1) x *
        frameField K (fun j => signVal (idx.2 j).2) x -
        (if ν then 1 else 0) * kappa0 * smoothedTent K M idx.1 x *
          correctionFactor ((frameField K (fun j => signVal (idx.2 j).1) x)^2) a) := by
  simp only [copulaZeta, copulaXi, copulaUpsilon, copulaT, correctionFactor]
  ring

/-- The propensity derivative of an actual full-record label density at any amplitude. This statement assumes [the ν parameter](hyp:ν), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the idx parameter](hyp:idx), [the x parameter](hyp:x), [the marked parameter](hyp:marked), [the label parameter](hyp:label). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. [Defining clause 3](step:3) is used. -/
-- @node: labelPropensityDerivative
def labelPropensityDerivative (ν : Bool) (K M : ℕ) (a u : ℝ)
    (idx : CopulaIndex K M) (x : unitInterval) (marked : Bool) (label : Bool × Bool) : ℝ :=
  let Λ := frameField K (fun j => signVal (idx.2 j).1) x
  let H := frameField K (fun j => signVal (idx.2 j).2) x
  signVal label.1 * Λ + if marked then
    signVal label.1 * signVal label.2 * u *
      (Λ * H - (if ν then 1 else 0) * kappa0 * smoothedTent K M idx.1 x *
        correctionSlope (Λ^2) a) else 0

/-- The propensity curvature of an actual full-record label density at any amplitude. This statement assumes [the ν parameter](hyp:ν), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the idx parameter](hyp:idx), [the x parameter](hyp:x), [the marked parameter](hyp:marked), [the label parameter](hyp:label). [This is the stated defined object](goal). -/
-- @node: labelPropensityCurvature
def labelPropensityCurvature (ν : Bool) (K M : ℕ) (a u : ℝ)
    (idx : CopulaIndex K M) (x : unitInterval) (marked : Bool) (label : Bool × Bool) : ℝ :=
  if marked then -signVal label.1 * signVal label.2 * u *
    (if ν then 1 else 0) * kappa0 * smoothedTent K M idx.1 x *
      correctionCurvature ((frameField K (fun j => signVal (idx.2 j).1) x)^2) a else 0

/-- The quotient-rule derivative enters the complete record density, retaining both treatment and outcome labels and the correction at every non-pole amplitude. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: labelDensity_hasDerivAt_propensity
lemma labelDensity_hasDerivAt_propensity (ν : Bool) (K M : ℕ) (a u : ℝ)
    (ha : 1-a^2 ≠ 0) (idx : CopulaIndex K M) (x : unitInterval)
    (marked : Bool) (label : Bool × Bool) :
    HasDerivAt (fun b => labelDensity ν K M b u idx x marked label)
      (labelPropensityDerivative ν K M a u idx x marked label) a := by
  let Λ := frameField K (fun j => signVal (idx.2 j).1) x
  let H := frameField K (fun j => signVal (idx.2 j).2) x
  let c := (if ν then (1:ℝ) else 0) * kappa0 * smoothedTent K M idx.1 x
  have hlin := (hasDerivAt_id a).mul_const Λ
  have hz := (((hlin.mul_const H).sub
    ((correctionFactor_hasDerivAt (Λ^2) a ha).const_mul c)).const_mul u)
  have hbase := (hlin.const_mul (signVal label.1)).const_add 1
  cases marked with
  | false =>
    convert hbase using 1 <;> first | rfl | (simp [labelDensity, copulaXi,
      labelPropensityDerivative, Λ])
  | true =>
    have hh := (hbase.add (hasDerivAt_const a (signVal label.2 * (u*H)))).add
      (hz.const_mul (signVal label.1 * signVal label.2))
    convert hh using 1 <;> first
    | rfl
    | (cases ν <;> simp [labelDensity, copulaXi, copulaUpsilon, copulaZeta_correctionFactor,
        labelPropensityDerivative, Λ, H, c] <;> first | (funext b; simp only [Pi.add_apply] <;> ring) | ring)

/-- The exact second derivative of the record density follows from the rational curvature; all other propensity dependence is affine. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: labelPropensityDerivative_hasDerivAt
lemma labelPropensityDerivative_hasDerivAt (ν : Bool) (K M : ℕ) (a u : ℝ)
    (ha : 1-a^2 ≠ 0) (idx : CopulaIndex K M) (x : unitInterval)
    (marked : Bool) (label : Bool × Bool) :
    HasDerivAt (fun b => labelPropensityDerivative ν K M b u idx x marked label)
      (labelPropensityCurvature ν K M a u idx x marked label) a := by
  let Λ := frameField K (fun j => signVal (idx.2 j).1) x
  let H := frameField K (fun j => signVal (idx.2 j).2) x
  let c := (if ν then (1:ℝ) else 0) * kappa0 * smoothedTent K M idx.1 x
  cases marked with
  | false =>
    simpa [labelPropensityDerivative, labelPropensityCurvature] using
      hasDerivAt_const a (signVal label.1 * Λ)
  | true =>
    have hh := ((((hasDerivAt_const a (Λ*H)).sub
      ((correctionSlope_hasDerivAt (Λ^2) a ha).const_mul c)).const_mul
        (signVal label.1 * signVal label.2 * u)).const_add (signVal label.1 * Λ))
    convert hh using 1 <;> first
    | rfl
    | (cases ν <;> simp [labelPropensityDerivative, labelPropensityCurvature, Λ, H, c] <;> ring)

/-- The signed smooth-frame field satisfies the squared-field premise of both rational bounds, so the bounds apply to every actual latent index and covariate. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: frame_correction_derivative_bounds
lemma frame_correction_derivative_bounds (K M : ℕ) (hK : 0 < K) (a : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 1/16) (idx : CopulaIndex K M) (x : unitInterval) :
    let t := (frameField K (fun j => signVal (idx.2 j).1) x)^2
    |correctionSlope t a| ≤ 2 ∧ |correctionCurvature t a| ≤ 1 := by
  have hs (b : Bool) : |signVal b| ≤ 1 := by cases b <;> norm_num [signVal]
  have hf := frameField_abs_le_sqrt_two K hK (fun j => signVal (idx.2 j).1)
    (fun j => hs _) x
  have ht : (frameField K (fun j => signVal (idx.2 j).1) x)^2 ≤ 2 := by
    have hh := mul_self_le_mul_self (abs_nonneg _) hf
    rw [← sq, sq_abs] at hh
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  exact ⟨correctionSlope_bound _ a ⟨sq_nonneg _, ht⟩ ha,
    correctionCurvature_bound _ a ⟨sq_nonneg _, ht⟩ ha⟩

/-- Both propensity derivatives of every record density obey the roadmap's common bound of four, uniformly over latent signs, covariates and all record categories. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: label_propensity_derivative_bounds
lemma label_propensity_derivative_bounds (ν : Bool) (K M : ℕ) (hK : 0 < K)
    (a u : ℝ) (ha : 0 ≤ a ∧ a ≤ 1/16) (hu : 0 ≤ u ∧ u ≤ 1/16)
    (idx : CopulaIndex K M) (x : unitInterval) (marked : Bool) (label : Bool × Bool) :
    |labelPropensityDerivative ν K M a u idx x marked label| ≤ 4 ∧
    |labelPropensityCurvature ν K M a u idx x marked label| ≤ 4 := by
  let Λ := frameField K (fun j => signVal (idx.2 j).1) x
  let H := frameField K (fun j => signVal (idx.2 j).2) x
  let c := (if ν then (1:ℝ) else 0) * kappa0 * smoothedTent K M idx.1 x
  have hs (b : Bool) : |signVal b| = 1 := by cases b <;> norm_num [signVal]
  have hΛ : |Λ| ≤ 2 := frameField_abs_le_two K hK _ (fun j => (hs _).le) x
  have hH : |H| ≤ 2 := frameField_abs_le_two K hK _ (fun j => (hs _).le) x
  have hc : |c| ≤ 1/16 := by
    have hg := smoothedTent_abs_le_one K M hK idx.1 x
    cases ν <;> simp only [c, Bool.false_eq_true, ↓reduceIte, zero_mul, abs_zero,
      one_mul, kappa0, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/16)]
    · norm_num
    · nlinarith
  have hr := frame_correction_derivative_bounds K M hK a ha idx x
  have hi : |Λ*H - c*correctionSlope (Λ^2) a| ≤ 33/8 := by
    calc
      _ ≤ |Λ| * |H| + |c| * |correctionSlope (Λ^2) a| := by
        simpa only [sub_eq_add_neg, abs_neg, abs_mul] using
          abs_add_le (Λ*H) (-(c*correctionSlope (Λ^2) a))
      _ ≤ 2*2 + (1/16)*2 := by gcongr <;> first | assumption | exact hr.1
      _ = 33/8 := by norm_num
  cases marked with
  | false =>
    simp only [labelPropensityDerivative, labelPropensityCurvature, Bool.false_eq_true,
      ↓reduceIte, add_zero, abs_mul, hs, one_mul]
    exact ⟨hΛ.trans (by norm_num), by norm_num⟩
  | true =>
    constructor
    · change |signVal label.1 * Λ + signVal label.1 * signVal label.2 * u *
        (Λ*H-c*correctionSlope (Λ^2) a)| ≤ 4
      calc
        _ ≤ |signVal label.1 * Λ| +
          |signVal label.1 * signVal label.2 * u * (Λ*H-c*correctionSlope (Λ^2) a)| :=
            abs_add_le _ _
        _ = |Λ| + u * |Λ*H-c*correctionSlope (Λ^2) a| := by
          simp only [abs_mul, hs, abs_of_nonneg hu.1, one_mul]
        _ ≤ 2 + (1/16)*(33/8) := by gcongr <;> first | assumption | exact hu.2
        _ ≤ 4 := by norm_num
    · have he : labelPropensityCurvature ν K M a u idx x true label =
          -signVal label.1 * signVal label.2 * u * c * correctionCurvature (Λ^2) a := by
        simp only [labelPropensityCurvature, ↓reduceIte, c, Λ]
        ring
      rw [he]
      simp only [abs_mul, abs_neg, hs, abs_of_nonneg hu.1, one_mul]
      calc
        u * |c| * |correctionCurvature (Λ^2) a| ≤ (1/16)*(1/16)*1 := by gcongr <;> first | exact hu.2 | exact hc | exact hr.2
        _ ≤ 4 := by norm_num

/-- A component of size at most one has at most one mark, so its even discrepancy vanishes by the exact one-mark coefficient calculation. This statement assumes [the hC condition](hyp:hC). [This is the stated conclusion](goal). -/
-- @node: evenDiscrepancy_small_component
lemma evenDiscrepancy_small_component (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n)
    (hC : C.card ≤ 1) : evenDiscrepancy n K M a u aug C labels = 0 := by
  exact evenDiscrepancy_at_most_one_mark n K M a u aug C labels
    ((Finset.card_filter_le _ _).trans hC)

end CausalSmith.Stat.FinitepHomogeneityDensegamma

module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ResolutionBounds
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Reduction
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Clipped pilot moment bounds -/

@[expose] public section

open MeasureTheory
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

-- @node: abs_clip_sub_le
/-- Given [the supplied inputs](hyp:lo,hi,x,y,hlo,hhi), [the stated result about abs clip sub le holds](goal). -/
lemma abs_clip_sub_le (lo hi x y : ℝ) (hlo : lo ≤ y) (hhi : y ≤ hi) :
    |clip lo hi x - y| ≤ |x - y| := by
  have hmin : |min hi x - y| ≤ |x - y| := by
    rcases le_total x hi with hx | hx
    · rw [min_eq_right hx]
    · rw [min_eq_left hx]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  have hmax : |max lo (min hi x) - y| ≤ |min hi x - y| := by
    rcases le_total lo (min hi x) with hx | hx
    · rw [max_eq_right hx]
    · rw [max_eq_left hx]
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  exact le_trans hmax hmin

-- @node: pilot_error_le_histogram_error
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hn,hP,x,hx,i), [the stated result about pilot error le histogram error holds](goal). -/
lemma pilot_error_le_histogram_error (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (ω : TwoSample n n)
    (x : ℝ) (hx : x ∈ covariateSpace) (i : Fin 7) :
    |pilot c_f C_f ω x i - markedDensityVector c_f C_f L P n hP x i| ≤
      |markedHistogram ω i (pilotResolution n) 0 x -
        markedDensityVector c_f C_f L P n hP x i| := by
  have hrect := markedDensityVector_mem_clippingRectangle c_f C_f L P n hP x hx
  rcases hrect with ⟨h0, h1, h2, hrest⟩
  have hlarge : ¬ n < threshold := by omega
  rw [pilot, if_neg hlarge]
  fin_cases i <;> simp only [clipChannel, if_true] <;>
    apply abs_clip_sub_le <;>
    first | exact h0.1 | exact h0.2 | exact h1.1 | exact h1.2 |
      exact h2.1 | exact h2.2 |
      exact (hrest _ (by decide)).1 | exact (hrest _ (by decide)).2

/-- The one-dimensional Hölder-ball condition controls function increments.  Under [the displayed assumptions and inputs](hyp:f,L,hf,x,y,hx,hy), [the stated conclusion holds](goal). -/
-- @node: HolderOn_abs_sub_le
lemma HolderOn_abs_sub_le (f : ℝ → ℝ) (L : ℝ) (hf : HolderOn f L)
    (x y : ℝ) (hx : x ∈ covariateSpace) (hy : y ∈ covariateSpace) :
    |f x - f y| ≤ L * |x - y| ^ holderExponent := by
  have hceil : ⌈holderExponent⌉₊ = 1 := by
    apply (Nat.ceil_eq_iff (by decide)).2
    norm_num [holderExponent]
  have h := hf.2.2.2 ![x] (by simpa using hx) ![y] (by simpa using hy)
  rw [hceil] at h
  simp only [Nat.sub_self, Nat.cast_zero, sub_zero] at h
  change ‖(continuousMultilinearCurryFin0 ℝ (Fin 1 → ℝ) ℝ).symm (f x) -
    (continuousMultilinearCurryFin0 ℝ (Fin 1 → ℝ) ℝ).symm (f y)‖ ≤
    L * ‖![x] - ![y]‖ ^ holderExponent at h
  rw [← map_sub, LinearIsometryEquiv.norm_map] at h
  have heq : (![x] - ![y] : Fin 1 → ℝ) = fun _ => x - y := by
    ext i; fin_cases i; rfl
  simpa [heq, pi_norm_const, Real.norm_eq_abs] using h

/-- All seven marked densities have the common Hölder modulus used in the pilot analysis.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,x,y,hx,hy,i), [the stated conclusion holds](goal). -/
-- @node: markedDensityVector_holder_modulus
lemma markedDensityVector_holder_modulus (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (x y : ℝ) (hx : x ∈ covariateSpace) (hy : y ∈ covariateSpace)
    (i : Fin 7) :
    |markedDensityVector c_f C_f L P n hP x i -
      markedDensityVector c_f C_f L P n hP y i| ≤
      3 * (1 + C_f) * L * |x - y| ^ holderExponent := by
  let d := |x - y| ^ holderExponent
  have hd : 0 ≤ d := Real.rpow_nonneg (abs_nonneg _) _
  have hL : 0 ≤ L := hP.sourceHolder.1.le.trans' (by norm_num)
  have hC : 0 ≤ C_f := hP.sourceBounds.2.1.le.trans' (by norm_num)
  have hs := HolderOn_abs_sub_le P.fS L hP.sourceHolder x y hx hy
  have ht := HolderOn_abs_sub_le P.fT L hP.targetHolder x y hx hy
  have he := HolderOn_abs_sub_le P.e L hP.propensityHolder x y hx hy
  have hm (A z : Bool) := HolderOn_abs_sub_le (P.m A z) L
    (hP.armHolder.1 A z) x y hx hy
  have hfs (z : ℝ) (hz : z ∈ covariateSpace) : |P.fS z| ≤ C_f := by
    have hb := hP.sourceBounds.2.2.2.2.2 z hz
    rw [abs_of_nonneg (le_trans hP.sourceBounds.1.1.le hb.1)]
    exact hb.2
  have hem (z : ℝ) (hz : z ∈ covariateSpace) :
      |P.e z| ≤ 1 ∧ |1 - P.e z| ≤ 1 := by
    have hb := hP.overlap z hz
    constructor <;> rw [abs_le] <;> constructor <;> linarith [hb.1, hb.2]
  have hmul (a b c e A B H J : ℝ)
      (ha : |a| ≤ A) (he' : |e| ≤ B)
      (hab : |a - b| ≤ H) (hce : |c - e| ≤ J)
      (hA : 0 ≤ A) (hB : 0 ≤ B) :
      |a * c - b * e| ≤ A * J + H * B := by
    calc
      _ = |a * (c - e) + (a - b) * e| := by congr 1; ring
      _ ≤ |a| * |c - e| + |a - b| * |e| := by
        simpa only [abs_mul] using abs_add_le (a * (c - e)) ((a - b) * e)
      _ ≤ _ := add_le_add (mul_le_mul ha hce (abs_nonneg _) hA)
        (mul_le_mul hab he' (abs_nonneg _) (le_trans (abs_nonneg _) hab))
  have hq (z : Bool) :
      |P.fS x * (if z then P.e x else 1 - P.e x) -
        P.fS y * (if z then P.e y else 1 - P.e y)| ≤ (1 + C_f) * L * d := by
    have heg : |(if z then P.e x else 1 - P.e x) -
        (if z then P.e y else 1 - P.e y)| ≤ L * d := by
      cases z
      · change |1 - P.e x - (1 - P.e y)| ≤ _
        rw [show 1 - P.e x - (1 - P.e y) = -(P.e x - P.e y) by ring, abs_neg]
        exact he
      · exact he
    have hgb : |(if z then P.e y else 1 - P.e y)| ≤ 1 := by
      cases z <;> simp only [Bool.false_eq_true, if_false, if_true]
      · exact (hem y hy).2
      · exact (hem y hy).1
    have hh := hmul _ _ _ _ C_f 1 (L * d) (L * d) (hfs x hx) hgb hs heg hC (by norm_num)
    convert hh using 1 <;> ring
  have hr (A z : Bool) :
      |P.fS x * (if z then P.e x else 1 - P.e x) * P.m A z x -
        P.fS y * (if z then P.e y else 1 - P.e y) * P.m A z y| ≤
          3 * (1 + C_f) * L * d := by
    have hqa : |P.fS x * (if z then P.e x else 1 - P.e x)| ≤ C_f := by
      rw [abs_mul]
      have hgb : |(if z then P.e x else 1 - P.e x)| ≤ 1 := by
        cases z
        · exact (hem x hx).2
        · exact (hem x hx).1
      simpa using mul_le_mul (hfs x hx) hgb (abs_nonneg _) hC
    have hmb : |P.m A z y| ≤ 1 := by
      have hb := (hP.armHolder.2.1 A z).2.2 y hy
      simpa [abs_of_nonneg hb.1] using hb.2
    have hh := hmul _ _ _ _ C_f 1 ((1 + C_f) * L * d) (L * d)
      hqa hmb (hq z) (hm A z) hC (by norm_num)
    exact hh.trans (by nlinarith [mul_nonneg hC (mul_nonneg hL hd)])
  have hq' (z : Bool) :
      |P.fS x * (if z then P.e x else 1 - P.e x) -
        P.fS y * (if z then P.e y else 1 - P.e y)| ≤
          3 * (1 + C_f) * L * d :=
    (hq z).trans (by nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + C_f) (mul_nonneg hL hd)])
  fin_cases i
  · exact ht.trans (by nlinarith [mul_nonneg hC (mul_nonneg hL hd), mul_nonneg hL hd])
  · exact hq' false
  · exact hq' true
  · exact hr true false
  · exact hr true true
  · exact hr false false
  · exact hr false true

/-- Splitting an error at an intermediate value costs at most the factor `2⁷` in its eighth power.  Under [the displayed assumptions and inputs](hyp:u,v,w), [the stated conclusion holds](goal). -/
-- @node: abs_sub_eighth_le
lemma abs_sub_eighth_le (u v w : ℝ) :
    |u - w| ^ (8 : ℕ) ≤ 2 ^ (7 : ℕ) * (|u - v| ^ (8 : ℕ) + |v - w| ^ (8 : ℕ)) := by
  calc
    _ ≤ (|u - v| + |v - w|) ^ (8 : ℕ) :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_sub_le u v w) 8
    _ ≤ _ := by simpa using add_pow_le (abs_nonneg (u - v)) (abs_nonneg (v - w)) 8

/-- The clipped pilot's eighth-power error splits into histogram fluctuation and deterministic bias.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,x,hx,i,center), [the stated conclusion holds](goal). -/
-- @node: pilot_error_eighth_split
lemma pilot_error_eighth_split (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (ω : TwoSample n n)
    (x : ℝ) (hx : x ∈ covariateSpace) (i : Fin 7) (center : ℝ) :
    |pilot c_f C_f ω x i - markedDensityVector c_f C_f L P n hP x i| ^ (8 : ℕ) ≤
      2 ^ (7 : ℕ) *
        (|markedHistogram ω i (pilotResolution n) 0 x - center| ^ (8 : ℕ) +
          |center - markedDensityVector c_f C_f L P n hP x i| ^ (8 : ℕ)) := by
  exact (pow_le_pow_left₀ (abs_nonneg _)
    (pilot_error_le_histogram_error c_f C_f L P n hn hP ω x hx i) 8).trans
      (abs_sub_eighth_le _ center _)

/-- Every centered bounded bin mark lies in the unit ball.  This controls
all multiplicities in the eighth-power index-pattern expansion.  Under [the displayed assumptions and inputs](hyp:Ω,f,hf,hb,x), [the stated conclusion holds](goal). -/
-- @node: centered_unit_mark_abs_le_one
lemma centered_unit_mark_abs_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hb : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (x : Ω) :
    |f x - ∫ y, f y ∂μ| ≤ 1 := by
  have hi : Integrable f μ := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    filter_upwards [] with y
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hb y).1] using (hb y).2
  have hmean0 : 0 ≤ ∫ y, f y ∂μ := integral_nonneg (fun y => (hb y).1)
  have hmean1 : (∫ y, f y ∂μ) ≤ 1 := by
    simpa using integral_mono hi (integrable_const (1 : ℝ)) (fun y => (hb y).2)
  rw [abs_le]
  constructor <;> linarith [(hb x).1, (hb x).2]

/-- Every multiplicity of at least two is controlled by the centered
second moment of a bounded bin mark.  Independence can then multiply
these bounds over the distinct indices in a surviving eighth-power term.  Under [the displayed assumptions and inputs](hyp:Ω,f,hf,hb,k,hk), [the stated conclusion holds](goal). -/
-- @node: centered_unit_mark_multiplicity_moment_le
lemma centered_unit_mark_multiplicity_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hb : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (hk : 2 ≤ k) :
    |∫ x, (f x - ∫ y, f y ∂μ) ^ k ∂μ| ≤
      ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := by
  have hunit := centered_unit_mark_abs_le_one μ f hf hb
  have hpoint (x : Ω) : |f x - ∫ y, f y ∂μ| ^ k ≤
      (f x - ∫ y, f y ∂μ) ^ 2 := by
    have hp : |f x - ∫ y, f y ∂μ| ^ (k - 2) ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) (hunit x)
    rw [show k = 2 + (k - 2) by omega, pow_add]
    simpa only [sq_abs, mul_one] using
      mul_le_mul_of_nonneg_left hp (sq_nonneg |f x - ∫ y, f y ∂μ|)
  have hi2 : Integrable (fun x => (f x - ∫ y, f y ∂μ) ^ 2) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
      pow_le_one₀ (abs_nonneg _) (hunit x) (n := 2)
  calc
    _ ≤ ∫ x, |(f x - ∫ y, f y ∂μ) ^ k| ∂μ := abs_integral_le_integral_abs
    _ ≤ _ := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun x => abs_nonneg _)) hi2
      (Filter.Eventually.of_forall (fun x => by simpa only [abs_pow] using hpoint x))

/-- Centering a bounded bin mark removes the singleton moment exactly.  Under [the displayed assumptions and inputs](hyp:Ω,f,hf,hb), [the stated conclusion holds](goal). -/
-- @node: integral_centered_unit_mark_eq_zero
lemma integral_centered_unit_mark_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hb : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, (f x - ∫ y, f y ∂μ) ∂μ) = 0 := by
  have hi : Integrable f μ := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hb x).1] using (hb x).2
  rw [integral_sub hi (integrable_const _)]
  simp

/-- In the product experiment, any monomial with a singleton sample index
has zero expectation.  This is the exact cancellation used before counting
the surviving eighth-power index patterns.  Under [the displayed assumptions and inputs](hyp:Ω,f,hf,hb,n,k,r,hr), [the stated conclusion holds](goal). -/
-- @node: iid_centered_unit_mark_singleton_monomial_zero
lemma iid_centered_unit_mark_singleton_monomial_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hb : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    {n : ℕ} (k : Fin n → ℕ) (r : Fin n) (hr : k r = 1) :
    (∫ x : Fin n → Ω, ∏ j, (f (x j) - ∫ y, f y ∂μ) ^ k j
      ∂Measure.pi (fun _ : Fin n => μ)) = 0 := by
  rw [integral_fintype_prod_eq_prod
    (fun j x => (f x - ∫ y, f y ∂μ) ^ k j)]
  apply Finset.prod_eq_zero (Finset.mem_univ r)
  rw [hr]
  simp only [pow_one]
  exact integral_centered_unit_mark_eq_zero μ f hf hb

/-- For a surviving monomial, independence bounds the product of the
multiplicity moments by one variance factor per distinct sample index.  Under [the displayed assumptions and inputs](hyp:Ω,f,hf,hb,m,k,hk), [the stated conclusion holds](goal). -/
-- @node: iid_centered_unit_mark_surviving_monomial_le
lemma iid_centered_unit_mark_surviving_monomial_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hb : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    {m : ℕ} (k : Fin m → ℕ) (hk : ∀ j, 2 ≤ k j) :
    |∫ x : Fin m → Ω, ∏ j, (f (x j) - ∫ y, f y ∂μ) ^ k j
      ∂Measure.pi (fun _ : Fin m => μ)| ≤
        (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) ^ m := by
  rw [integral_fintype_prod_eq_prod
    (fun j x => (f x - ∫ y, f y ∂μ) ^ k j), Finset.abs_prod]
  calc
    _ ≤ ∏ _j : Fin m, (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact abs_nonneg _
      · intro j hj
        exact centered_unit_mark_multiplicity_moment_le μ f hf hb (k j) (hk j)
    _ = _ := by simp
/-- [The pilot eighth constant object](goal) is defined from [the supplied inputs](hyp:C_f,L). -/

noncomputable def pilotEighthConstant (C_f L : ℝ) : ℝ :=
  let H := 3 * (1 + C_f) * L
  let V := 1 + C_f + C_f ^ 2
  2 ^ (7 : ℕ) * (Nat.factorial 8 : ℝ) *
    (V ^ 4 * 5 ^ ((4 : ℝ) / 5) + V * 5 ^ ((7 : ℝ) / 5)) +
    2 ^ (8 : ℕ) * H ^ 8 * 5 ^ ((4 : ℝ) / 5)

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

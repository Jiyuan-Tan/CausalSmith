module
public import Causalean.Mathlib.Probability.Certified.NormalCDF.Exponential
public import Causalean.Mathlib.Probability.Certified.NormalCDF.Normalization
public import Causalean.Mathlib.Probability.GaussianMoments

/-!
# Mills-ratio standard-normal tail certificates

For `x > 8`, the checker encloses the density using a finite rational
exponential certificate and a rational normalization certificate, then applies
the classical Mills bounds
`x φ(x)/(x²+1) ≤ 1-Φ(x) ≤ φ(x)/x`.  These are the normal-tail counterpart of
NIST DLMF §7.8 and avoid evaluating a nearly-one CDF by cancellation-prone
central quadrature.
-/

@[expose] public section

namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure

open Causalean.Mathlib.Analysis.IntervalArithmetic
open Causalean.Mathlib.Analysis.IntervalArithmetic.Contour
/-- The standard-normal density is strictly positive at every real argument. -/
theorem stdNormalPDF_pos (x : ℝ) :
    0 < Causalean.Mathlib.stdNormalPDF x := by
  simpa [Causalean.Mathlib.stdNormalPDF] using
    ProbabilityTheory.gaussianPDFReal_pos 0 1 x one_ne_zero

/-- The derivative of the standard-normal density is `-x · φ(x)`. -/
theorem hasDerivAt_stdNormalPDF (x : ℝ) :
    HasDerivAt Causalean.Mathlib.stdNormalPDF
      (-x * Causalean.Mathlib.stdNormalPDF x) x := by
  have hpdf : Causalean.Mathlib.stdNormalPDF =
      fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    funext y
    unfold Causalean.Mathlib.stdNormalPDF ProbabilityTheory.gaussianPDFReal
    congr 2
    · norm_num
    · norm_num
  rw [hpdf]
  have hpow : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    have h := ((hasDerivAt_pow 2 x).div_const 2).fun_neg
    simpa [neg_div, pow_one] using h.congr_deriv (by ring)
  have hcomp : HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / 2))
      (Real.exp (-x ^ 2 / 2) * (-x)) x :=
    (Real.hasDerivAt_exp _).comp x hpow
  simpa only [mul_assoc, mul_comm, mul_left_comm, neg_mul, mul_neg] using
    hcomp.const_mul (Real.sqrt (2 * Real.pi))⁻¹

/-- The standard-normal upper-tail probability equals the integral of its
density over the ray strictly above the endpoint. -/
theorem one_sub_stdNormalCDF_eq_integral_Ioi (x : ℝ) :
    1 - Causalean.Mathlib.stdNormalCDF x =
      ∫ t in Set.Ioi x, Causalean.Mathlib.stdNormalPDF t := by
  exact (Causalean.Mathlib.integral_Ioi_stdNormalPDF x).symm

/-- The classical upper Mills inequality bounds the standard-normal upper tail
by `φ(x)/x` at every positive argument. -/
theorem millsRatio_upper (x : ℝ) (hx : 0 < x) :
    1 - Causalean.Mathlib.stdNormalCDF x ≤
      Causalean.Mathlib.stdNormalPDF x / x := by
  have hcompare :
      (∫ t in Set.Ioi x, Causalean.Mathlib.stdNormalPDF t) ≤
        ∫ t in Set.Ioi x,
          (1 / x) * (t * Causalean.Mathlib.stdNormalPDF t) := by
    have hpdf : MeasureTheory.Integrable
        (fun t : ℝ => Causalean.Mathlib.stdNormalPDF t) := by
      change MeasureTheory.Integrable
        (ProbabilityTheory.gaussianPDFReal 0 1)
      exact ProbabilityTheory.integrable_gaussianPDFReal 0 1
    have hweighted : MeasureTheory.Integrable
        (fun t : ℝ => (1 / x) *
          (t * Causalean.Mathlib.stdNormalPDF t)) :=
      (Causalean.Mathlib.integrable_id_mul_stdNormalPDF).const_mul (1 / x)
    refine MeasureTheory.setIntegral_mono_on_ae hpdf.integrableOn
      hweighted.integrableOn measurableSet_Ioi ?_
    filter_upwards with t
    intro ht
    have hxt : x ≤ t := le_of_lt ht
    have hratio : 1 ≤ t / x := (le_div_iff₀ hx).2 (by simpa using hxt)
    calc
      Causalean.Mathlib.stdNormalPDF t
          = 1 * Causalean.Mathlib.stdNormalPDF t := by ring
      _ ≤ (t / x) * Causalean.Mathlib.stdNormalPDF t :=
        mul_le_mul_of_nonneg_right hratio (stdNormalPDF_pos t).le
      _ = (1 / x) * (t * Causalean.Mathlib.stdNormalPDF t) := by ring
  calc
    1 - Causalean.Mathlib.stdNormalCDF x
        = ∫ t in Set.Ioi x, Causalean.Mathlib.stdNormalPDF t :=
          one_sub_stdNormalCDF_eq_integral_Ioi x
    _ ≤ ∫ t in Set.Ioi x,
          (1 / x) * (t * Causalean.Mathlib.stdNormalPDF t) := hcompare
    _ = (1 / x) * ∫ t in Set.Ioi x,
          t * Causalean.Mathlib.stdNormalPDF t := by
          rw [MeasureTheory.integral_const_mul]
    _ = Causalean.Mathlib.stdNormalPDF x / x := by
          rw [Causalean.Mathlib.integral_Ioi_id_mul_stdNormalPDF]
          ring

/-- The classical lower Mills inequality bounds the standard-normal upper tail
below by `xφ(x)/(x²+1)` at every positive argument. -/
theorem millsRatio_lower (x : ℝ) (hx : 0 < x) :
    x / (x ^ 2 + 1) * Causalean.Mathlib.stdNormalPDF x ≤
      1 - Causalean.Mathlib.stdNormalCDF x := by
  have hpdf_int : MeasureTheory.Integrable
      Causalean.Mathlib.stdNormalPDF := by
    change MeasureTheory.Integrable (ProbabilityTheory.gaussianPDFReal 0 1)
    exact ProbabilityTheory.integrable_gaussianPDFReal 0 1
  have hpdf_cont : Continuous Causalean.Mathlib.stdNormalPDF := by
    exact continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_stdNormalPDF t).continuousAt
  have hrem_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => Causalean.Mathlib.stdNormalPDF t / t ^ 2) (Set.Ioi x) := by
    have hmajor : MeasureTheory.IntegrableOn
        (fun t : ℝ => (1 / x ^ 2) * Causalean.Mathlib.stdNormalPDF t) (Set.Ioi x) :=
      (hpdf_int.const_mul (1 / x ^ 2)).integrableOn
    refine hmajor.mono'
      ((hpdf_cont.continuousOn.div (continuous_id.pow 2).continuousOn
        (fun t ht => pow_ne_zero 2 (ne_of_gt (hx.trans ht)))).aestronglyMeasurable
          measurableSet_Ioi) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := hx.trans ht
    have hxt : x < t := ht
    have hsq : x ^ 2 ≤ t ^ 2 := by nlinarith
    have hinv : 1 / t ^ 2 ≤ 1 / x ^ 2 :=
      (div_le_div_iff₀ (pow_pos htpos 2) (pow_pos hx 2)).2 (by simpa using hsq)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (stdNormalPDF_pos t).le (sq_nonneg t))]
    calc
      Causalean.Mathlib.stdNormalPDF t / t ^ 2
          = (1 / t ^ 2) * Causalean.Mathlib.stdNormalPDF t := by ring
      _ ≤ (1 / x ^ 2) * Causalean.Mathlib.stdNormalPDF t :=
        mul_le_mul_of_nonneg_right hinv (stdNormalPDF_pos t).le
  have hpdf_tendsto : Filter.Tendsto Causalean.Mathlib.stdNormalPDF
      Filter.atTop (nhds 0) := by
    have hpdf : Causalean.Mathlib.stdNormalPDF =
      fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
      funext y
      simp [Causalean.Mathlib.stdNormalPDF, ProbabilityTheory.gaussianPDFReal]
    rw [hpdf]
    have hsq : Filter.Tendsto (fun t : ℝ => t ^ 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num)
    have hneg : Filter.Tendsto (fun t : ℝ => -t ^ 2 / 2)
        Filter.atTop Filter.atBot := by
      apply Filter.Tendsto.atBot_div_const (by norm_num)
      exact Filter.tendsto_neg_atBot_iff.mpr hsq
    simpa using (tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hneg))
  have hquot_tendsto : Filter.Tendsto
      (fun t : ℝ => -Causalean.Mathlib.stdNormalPDF t / t)
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (hpdf_tendsto.mul tendsto_inv_atTop_zero).neg
  have hderiv : ∀ t ∈ Set.Ici x,
      HasDerivAt (fun y : ℝ => -Causalean.Mathlib.stdNormalPDF y / y)
        (Causalean.Mathlib.stdNormalPDF t +
          Causalean.Mathlib.stdNormalPDF t / t ^ 2) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (hx.trans_le ht)
    change HasDerivAt
      ((fun y : ℝ => -Causalean.Mathlib.stdNormalPDF y) / id)
      (Causalean.Mathlib.stdNormalPDF t +
        Causalean.Mathlib.stdNormalPDF t / t ^ 2) t
    have h := (hasDerivAt_stdNormalPDF t).fun_neg.div (hasDerivAt_id t) ht0
    exact h.congr_deriv (by
      simp only [id_eq]
      field_simp [ht0]
      ring)
  have htail_int : MeasureTheory.IntegrableOn Causalean.Mathlib.stdNormalPDF
      (Set.Ioi x) := hpdf_int.integrableOn
  have hsum_eq :
      (∫ t in Set.Ioi x, Causalean.Mathlib.stdNormalPDF t +
        Causalean.Mathlib.stdNormalPDF t / t ^ 2) =
        Causalean.Mathlib.stdNormalPDF x / x := by
    have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (f := fun t : ℝ => -Causalean.Mathlib.stdNormalPDF t / t)
      (f' := fun t : ℝ => Causalean.Mathlib.stdNormalPDF t +
        Causalean.Mathlib.stdNormalPDF t / t ^ 2)
      (a := x) (m := 0) hderiv (htail_int.add hrem_int) hquot_tendsto
    simpa [hx.ne', neg_div] using h
  have hdecomp :
      Causalean.Mathlib.stdNormalPDF x / x =
        (∫ t in Set.Ioi x, Causalean.Mathlib.stdNormalPDF t) +
          ∫ t in Set.Ioi x, Causalean.Mathlib.stdNormalPDF t / t ^ 2 := by
    rw [← MeasureTheory.integral_add htail_int hrem_int]
    exact hsum_eq.symm
  have hrem_le :
      (∫ t in Set.Ioi x, Causalean.Mathlib.stdNormalPDF t / t ^ 2) ≤
        (1 / x ^ 2) * ∫ t in Set.Ioi x, Causalean.Mathlib.stdNormalPDF t := by
    calc
      (∫ t in Set.Ioi x, Causalean.Mathlib.stdNormalPDF t / t ^ 2)
          ≤ ∫ t in Set.Ioi x,
              (1 / x ^ 2) * Causalean.Mathlib.stdNormalPDF t := by
            refine MeasureTheory.setIntegral_mono_of_nonneg ?_ ?_
              ((hpdf_int.const_mul (1 / x ^ 2)).integrableOn)
            · intro t ht
              exact div_nonneg (stdNormalPDF_pos t).le (sq_nonneg t)
            · intro t ht
              have htpos : 0 < t := hx.trans ht
              have hxt : x < t := ht
              have hsq : x ^ 2 ≤ t ^ 2 := by nlinarith
              have hinv : 1 / t ^ 2 ≤ 1 / x ^ 2 :=
                (div_le_div_iff₀ (pow_pos htpos 2) (pow_pos hx 2)).2
                  (by simpa using hsq)
              calc
                Causalean.Mathlib.stdNormalPDF t / t ^ 2
                    = (1 / t ^ 2) * Causalean.Mathlib.stdNormalPDF t := by ring
                _ ≤ (1 / x ^ 2) * Causalean.Mathlib.stdNormalPDF t :=
                  mul_le_mul_of_nonneg_right hinv (stdNormalPDF_pos t).le
      _ = (1 / x ^ 2) * ∫ t in Set.Ioi x,
          Causalean.Mathlib.stdNormalPDF t := by
            rw [MeasureTheory.integral_const_mul]
  have hmain :
      Causalean.Mathlib.stdNormalPDF x / x ≤
        (∫ t in Set.Ioi x, Causalean.Mathlib.stdNormalPDF t) +
          (1 / x ^ 2) * ∫ t in Set.Ioi x,
            Causalean.Mathlib.stdNormalPDF t := by
    rw [hdecomp]
    exact add_le_add_right hrem_le _
  have hscaled := mul_le_mul_of_nonneg_right hmain (sq_nonneg x)
  field_simp [hx.ne'] at hscaled
  rw [one_sub_stdNormalCDF_eq_integral_Ioi]
  rw [div_mul_eq_mul_div, mul_comm x]
  apply (div_le_iff₀ (by positivity : 0 < x ^ 2 + 1)).2
  exact hscaled

/-- The classical two-sided Mills inequality for the standard-normal upper
tail at a positive real argument. -/
theorem millsRatio_bounds (x : ℝ) (hx : 0 < x) :
    x / (x ^ 2 + 1) * Causalean.Mathlib.stdNormalPDF x ≤
        1 - Causalean.Mathlib.stdNormalCDF x ∧
      1 - Causalean.Mathlib.stdNormalCDF x ≤
        Causalean.Mathlib.stdNormalPDF x / x := by
  exact ⟨millsRatio_lower x hx, millsRatio_upper x hx⟩

/-- A tail certificate combines rational normalization and exponential
certificates for the density at the absolute endpoint. -/
structure TailCertificate (q : ℚ) where
  /-- Certified normalization constant. -/
  normalization : NormalizationCertificate
  /-- Certified value of `exp (-|q|²/2)`. -/
  exponential : ExpCertificate (-|q| ^ 2 / 2)

/-- The certified rational interval for the density `φ(|q|)`. -/
def tailDensityInterval (q : ℚ) (c : TailCertificate q) : RatInterval :=
  c.normalization.enclosure.mul c.exponential.enclosure

/-- The product of the certified normalization and exponential intervals
contains the exact standard-normal density at the absolute endpoint. -/
theorem tailDensityInterval_sound (q : ℚ) (c : TailCertificate q)
    (hnormalization : normalizationCheck c.normalization = true)
    (hexponential : expCheck (-|q| ^ 2 / 2) c.exponential = true) :
    (tailDensityInterval q c).Contains
      (Causalean.Mathlib.stdNormalPDF (|q| : ℚ)) := by
  unfold tailDensityInterval
  have h := RatInterval.mul_sound (c.normalization.sound hnormalization)
    (c.exponential.sound hexponential)
  simpa [Causalean.Mathlib.stdNormalPDF,
    ProbabilityTheory.gaussianPDFReal] using h

/-- A rational Mills tail enclosure is the hull of the lower-factor product
and upper-factor product with the certified density interval, the factors being `x/(x²+1)` and
`1/x`. It encloses the upper tail only for positive `x`, as required by its soundness theorem; at
`x = 0` both factors are zero by the division convention. -/
def millsTailInterval (x : ℚ) (density : RatInterval) : RatInterval :=
  ((RatInterval.point (x / (x ^ 2 + 1))).mul density).hull
    ((RatInterval.point (1 / x)).mul density)

/-- A density enclosure and positivity of `x` imply that the rational Mills
interval contains the exact standard-normal upper-tail probability. -/
theorem millsTailInterval_sound (x : ℚ) (hx : 0 < x) (density : RatInterval)
    (hdensity : density.Contains (Causalean.Mathlib.stdNormalPDF (x : ℝ))) :
    (millsTailInterval x density).Contains
      (1 - Causalean.Mathlib.stdNormalCDF (x : ℝ)) := by
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hlower := RatInterval.mul_sound
    (RatInterval.point_sound (x / (x ^ 2 + 1))) hdensity
  have hupper := RatInterval.mul_sound
    (RatInterval.point_sound (1 / x)) hdensity
  have hmills := millsRatio_bounds (x : ℝ) hxR
  have hlowerLo := hlower.1
  have hupperHi := hupper.2
  constructor
  · simp only [millsTailInterval, RatInterval.hull, Rat.cast_min]
    refine (min_le_left _ _).trans (hlowerLo.trans ?_)
    simpa only [Rat.cast_div, Rat.cast_add, Rat.cast_pow, Rat.cast_one] using
      hmills.1
  · simp only [millsTailInterval, RatInterval.hull, Rat.cast_max]
    refine hmills.2.trans ?_
    calc
      Causalean.Mathlib.stdNormalPDF (x : ℝ) / (x : ℝ)
          = ((1 / x : ℚ) : ℝ) * Causalean.Mathlib.stdNormalPDF (x : ℝ) := by
            simp only [Rat.cast_div, Rat.cast_one]
            ring
      _ ≤ (((RatInterval.point (1 / x)).mul density).hi : ℚ) := hupperHi
      _ ≤ max
          (((RatInterval.point (x / (x ^ 2 + 1))).mul density).hi : ℝ)
          (((RatInterval.point (1 / x)).mul density).hi : ℝ) :=
        le_max_right _ _

/-- The signed tail evaluator returns the upper-tail interval directly for a
negative endpoint and reflects it for a nonnegative endpoint. -/
def tailInterval (q : ℚ) (c : TailCertificate q) : RatInterval :=
  let upperTail := millsTailInterval |q| (tailDensityInterval q c)
  if 0 ≤ q then reflectInterval upperTail else upperTail

/-- The tail checker validates normalization and exponential subcertificates,
the strict cutoff, and exact refinement into the caller-supplied interval. -/
def tailCheck (q : ℚ) (c : TailCertificate q) (reported : RatInterval) : Bool :=
  normalizationCheck c.normalization &&
    expCheck (-|q| ^ 2 / 2) c.exponential &&
    decide (centralCutoff < |q| ∧
      reported.lo ≤ (tailInterval q c).lo ∧
      (tailInterval q c).hi ≤ reported.hi)

/-- When [the Mills-tail checker accepts the supplied certificate and interval](hyp:hcheck), [that interval contains the standard-normal CDF at the rational endpoint](goal). -/
theorem tailCheck_sound {q : ℚ} {c : TailCertificate q} {reported : RatInterval}
    (hcheck : tailCheck q c reported = true) :
    reported.Contains (Causalean.Mathlib.stdNormalCDF (q : ℝ)) := by
  -- Decode the normalization, exponential, strict-cutoff, and refinement
  -- checks.  The strict cutoff makes `|q|` positive, so
  -- `tailDensityInterval_sound` and `millsTailInterval_sound` enclose the
  -- upper-tail probability at `|q|`.  Split on the sign of `q`: for positive
  -- `q`, reflect `1 - Φ(q)` once; for negative `q`, use `q = -|q|` and
  -- `stdNormalCDF_neg`.  First obtain containment in `tailInterval q c`, then
  -- finish by `RatInterval.Contains.mono` using the decoded refinement pair.
  unfold tailCheck at hcheck
  rw [Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨hcertificates, hconditions⟩
  rw [Bool.and_eq_true] at hcertificates
  rcases hcertificates with ⟨hnormalization, hexponential⟩
  have hconditions' :
      centralCutoff < |q| ∧
        reported.lo ≤ (tailInterval q c).lo ∧
        (tailInterval q c).hi ≤ reported.hi :=
    of_decide_eq_true hconditions
  rcases hconditions' with ⟨hcutoff, hlo, hhi⟩
  have habspos : 0 < |q| :=
    (by norm_num [centralCutoff] : (0 : ℚ) < centralCutoff).trans hcutoff
  have hdensity := tailDensityInterval_sound q c hnormalization hexponential
  have hupper := millsTailInterval_sound |q| habspos
    (tailDensityInterval q c) hdensity
  have htail :
      (tailInterval q c).Contains
        (Causalean.Mathlib.stdNormalCDF (q : ℝ)) := by
    by_cases hq : 0 ≤ q
    · simpa [tailInterval, hq, abs_of_nonneg hq] using
        (reflectInterval_sound hupper)
    · have hqneg : q < 0 := lt_of_not_ge hq
      have hqabs : q = -|q| := by simp [abs_of_neg hqneg]
      rw [tailInterval, if_neg hq]
      rw [show (q : ℝ) = -(((|q| : ℚ) : ℝ)) by exact_mod_cast hqabs,
        Causalean.Mathlib.stdNormalCDF_neg]
      exact hupper
  exact RatInterval.Contains.mono ⟨hlo, hhi⟩ htail

end Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure

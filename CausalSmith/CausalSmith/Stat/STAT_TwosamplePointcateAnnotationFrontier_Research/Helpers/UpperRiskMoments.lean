module

public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.UpperRiskPointwise
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! # Expected rectangular sampling deviations
Integrability and Cauchy–Schwarz bounds converting the rectangular second moments
into the mean error of the guarded estimator.
-/

public section

noncomputable section
set_option linter.style.longLine false
set_option linter.style.whitespace false
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- The square root of a nonnegative integrable function is integrable on a finite measure.  Given [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input hf0](hyp:hf0), [the upper integrable sqrt conclusion](goal) holds. -/
lemma upper_integrable_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ) (hf0 : ∀ w, 0 ≤ f w) :
    Integrable (fun w => Real.sqrt (f w)) μ := by
  apply (hf.add (integrable_const 1)).mono' (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  change Real.sqrt (f w) ≤ f w+1
  have hs := Real.sq_sqrt (hf0 w)
  nlinarith [Real.sqrt_nonneg (f w), sq_nonneg (Real.sqrt (f w)-1)]

/-- Cauchy–Schwarz in expectation bounds a mean square root by the square root of its mean.  Given [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input hf0](hyp:hf0), [the upper integral sqrt le conclusion](goal) holds. -/
lemma upper_integral_sqrt_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ) (hf0 : ∀ w, 0 ≤ f w) :
    (∫ w, Real.sqrt (f w) ∂μ) ≤ Real.sqrt (∫ w, f w ∂μ) := by
  have hs := upper_integrable_sqrt hf hf0
  have hj := Real.strictConcaveOn_sqrt.concaveOn.le_map_integral
    Real.continuous_sqrt.continuousOn isClosed_Ici
    (Filter.Eventually.of_forall hf0) hf hs
  simpa only [Function.comp_def] using hj

/-- The outcome moment's squared Euclidean deviation is integrable.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the r hat square deviation integrable conclusion](goal) holds. -/
lemma rHat_square_deviation_integrable (d n m : ℕ) (alpha beta gamma L eps : ℝ)
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (hn : 2 ≤ n) (h : ℝ) (J : ℕ) (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J) :
    Integrable (fun w : Sample d n m => ∑ u,
      (rHat w.1 h J u-rBar P n m h J u)^2) (experiment P n m) := by
  letI := experiment_probability d n m P
  apply integrable_finsetSum
  intro u hu
  exact (((rectangular_r_coordinate_bound (m := m) P hP hn h J hh hh' hJ u).1.sub
    (memLp_const _))).integrable_sq

/-- A failed guard is dominated by the Frobenius deviation itself.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input J](hyp:J), [the specified input hJ](hyp:hJ), [the specified input D](hyp:D), [the gram cutoff indicator le sqrt conclusion](goal) holds. -/
lemma gram_cutoff_indicator_le_sqrt (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps)
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (n m : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (J : ℕ) (hJ : 1 ≤ J) (D : Dataset d n m) :
    (if lambdaMin (qHat D h J) < gramGuard eps then (1:ℝ) else 0) ≤
      (gramGuard eps)⁻¹*Real.sqrt (∑ u, ∑ v, (qHat D h J u v-qPop P n m h J u v)^2) := by
  have hg : 0 < gramGuard eps := hdom.gramGuard_pos
  split_ifs with hbad
  · have hs := gram_cutoff_sq_deviation (qHat D h J) (qPop P n m h J) _ hg
      (fun v hv => by
        have hp := (population_positivity d alpha beta gamma L eps hdom P hP n m hn h hh hh' J hJ v).2
        have h2 : 2*gramGuard eps = eps*(1-eps) := by unfold gramGuard; ring
        rw [h2]
        simpa only [hv, mul_one] using hp) hbad
    have hnonneg : 0 ≤ ∑ u, ∑ v, (qHat D h J u v-qPop P n m h J u v)^2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hr := Real.sq_sqrt hnonneg
    have hr0 := Real.sqrt_nonneg (∑ u, ∑ v, (qHat D h J u v-qPop P n m h J u v)^2)
    have hsq : gramGuard eps ≤ Real.sqrt (∑ u, ∑ v, (qHat D h J u v-qPop P n m h J u v)^2) :=
      Real.le_sqrt_of_sq_le hs
    rw [← div_eq_inv_mul, le_div_iff₀ hg, one_mul]
    exact hsq
  · positivity

/-- Fixed-tuning risk is controlled by population approximation and the square root of the rectangular variance scale.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the rectangular risk sqrt variance conclusion](goal) holds. -/
lemma rectangular_risk_sqrt_variance (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (h : ℝ) (J : ℕ),
      2 ≤ n → 0 < h → h ≤ 1/2 → 1 ≤ J →
      ∃ hMeas : Measurable (fun w : Sample d n m => tHat eps h J w.1),
        ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
          risk ⟨fun w => tHat eps h J w.1, hMeas⟩ P hP ≤
            ENNReal.ofReal (C*(h^gamma+(h/J)^(alpha+beta)+
              Real.sqrt (1/((n:ℝ)*h^d)+(Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d /
                ((n:ℝ)*((n:ℝ)+m)*h^(2*d))))) := by
  obtain ⟨A, hA, hpoint⟩ := rectangular_pointwise_error_bound d alpha beta gamma L eps hdom
  obtain ⟨B, hB, hsampling⟩ := rectangular_sampling_bound d alpha beta gamma L eps hdom
  have hg : 0 < gramGuard eps := hdom.gramGuard_pos
  let K := A+(gramGuard eps)⁻¹
  refine ⟨K*(1+2*Real.sqrt B), by dsimp [K]; positivity, ?_⟩
  intro n m h J hn hh hh' hJ
  let hMeas := tHat_measurable d n m eps h J hn hh hh' hJ
  refine ⟨hMeas, ?_⟩
  intro P hP
  letI := experiment_probability d n m P
  let μ := experiment P n m
  let R : Sample d n m → ℝ := fun w => ∑ u, (rHat w.1 h J u-rBar P n m h J u)^2
  let Q : Sample d n m → ℝ := fun w => ∑ u, ∑ v, (qHat w.1 h J u v-qPop P n m h J u v)^2
  let V := 1/((n:ℝ)*h^d)+(Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d /
    ((n:ℝ)*((n:ℝ)+m)*h^(2*d))
  let b := h^gamma+(h/J)^(alpha+beta)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hR0 : ∀ w, 0 ≤ R w := fun w => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQ0 : ∀ w, 0 ≤ Q w := fun w =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hiR : Integrable R μ := rHat_square_deviation_integrable d n m alpha beta gamma L eps P hP hn h J hh hh' hJ
  have hiQ : Integrable Q μ := qHat_square_deviation_integrable d n m P h J hh hJ
  have hsR := upper_integrable_sqrt hiR hR0
  have hsQ := upper_integrable_sqrt hiQ hQ0
  have hsamp : (∫ w, R w ∂μ)+(∫ w, Q w ∂μ) ≤ B*V :=
    hsampling P hP n m h J hn hh hh' hJ
  have hmeanR : (∫ w, Real.sqrt (R w) ∂μ) ≤ Real.sqrt B*Real.sqrt V := by
    calc
      _ ≤ Real.sqrt (∫ w, R w ∂μ) := upper_integral_sqrt_le hiR hR0
      _ ≤ Real.sqrt (B*V) := Real.sqrt_le_sqrt (by linarith [integral_nonneg (f := Q) (fun w => hQ0 w) (μ := μ)])
      _ = _ := Real.sqrt_mul hB.le V
  have hmeanQ : (∫ w, Real.sqrt (Q w) ∂μ) ≤ Real.sqrt B*Real.sqrt V := by
    calc
      _ ≤ Real.sqrt (∫ w, Q w ∂μ) := upper_integral_sqrt_le hiQ hQ0
      _ ≤ Real.sqrt (B*V) := Real.sqrt_le_sqrt (by linarith [integral_nonneg (f := R) (fun w => hR0 w) (μ := μ)])
      _ = _ := Real.sqrt_mul hB.le V
  let f : Sample d n m → ℝ := fun w => |tHat eps h J w.1-tau P hP (x0 d)|
  have hif : Integrable f μ := by
    apply (integrable_const (2:ℝ)).mono' (by
      dsimp [f]
      exact (hMeas.sub measurable_const).abs.aestronglyMeasurable)
    filter_upwards [] with w
    simpa only [f, Real.norm_eq_abs, abs_abs] using tHat_absolute_error_le P hP w.1 h J
  have henv : Integrable (fun w => K*(b+Real.sqrt (R w)+Real.sqrt (Q w))) μ :=
    (((integrable_const b).add hsR).add hsQ).const_mul K
  have hpoint' : ∀ w, f w ≤ K*(b+Real.sqrt (R w)+Real.sqrt (Q w)) := by
    intro w
    have hp := hpoint P hP n m h J hn hh hh' hJ w.1
    have hg' := gram_cutoff_indicator_le_sqrt d alpha beta gamma L eps hdom P hP n m hn h hh hh' J hJ w.1
    change f w ≤ A*(b+Real.sqrt (R w)+Real.sqrt (Q w))+_ at hp
    change _ ≤ (gramGuard eps)⁻¹*Real.sqrt (Q w) at hg'
    dsimp only [K]
    have hgi : 0 ≤ (gramGuard eps)⁻¹ := inv_nonneg.mpr hg.le
    nlinarith [Real.sqrt_nonneg (R w), Real.sqrt_nonneg (Q w),
      mul_nonneg hgi (Real.sqrt_nonneg (R w)), mul_nonneg hgi hb]
  have hrisk : (∫ w, f w ∂μ) ≤ K*(1+2*Real.sqrt B)*(b+Real.sqrt V) := by
    calc
      _ ≤ ∫ w, K*(b+Real.sqrt (R w)+Real.sqrt (Q w)) ∂μ := integral_mono hif henv hpoint'
      _ = K*(b+(∫ w, Real.sqrt (R w) ∂μ)+(∫ w, Real.sqrt (Q w) ∂μ)) := by
        rw [integral_const_mul, integral_add (f := fun w => b+Real.sqrt (R w)) (g := fun w => Real.sqrt (Q w)) ((integrable_const b).add hsR) hsQ,
          integral_add (f := fun _ => b) (g := fun w => Real.sqrt (R w)) (integrable_const b) hsR]
        simp [μ]
      _ ≤ K*(b+2*(Real.sqrt B*Real.sqrt V)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by dsimp [K]; positivity)
      _ ≤ _ := by
        have hnonneg : 0 ≤ K*(2*Real.sqrt B)*b := by dsimp [K]; positivity
        have hnV : 0 ≤ K*Real.sqrt V := by dsimp [K]; positivity
        nlinarith
  change (∫⁻ w, ENNReal.ofReal (f w) ∂μ) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hif (Filter.Eventually.of_forall (fun w => abs_nonneg _))]
  exact ENNReal.ofReal_le_ofReal hrisk

/-- The squared inverse square-root rate is the reciprocal scale.  Given [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the upper inverse half sq conclusion](goal) holds. -/
lemma upper_inverse_half_sq (x : ℝ) (hx : 0 < x) :
    (x^(-(1/2:ℝ)))^2 = 1/x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num
  exact Real.rpow_neg_one x

/-- Rank and cell-side bookkeeping converts rectangular variance to the stated sampling rates.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input J](hyp:J), [the specified input h](hyp:h), [the specified input hn](hyp:hn), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the rectangular variance sqrt le rates conclusion](goal) holds. -/
lemma rectangular_variance_sqrt_le_rates (d n m J : ℕ) (h : ℝ)
    (hn : 2 ≤ n) (hh : 0 < h) (hJ : 1 ≤ J) :
    Real.sqrt (1/((n:ℝ)*h^d)+(Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d /
      ((n:ℝ)*((n:ℝ)+m)*h^(2*d))) ≤
    (1+Real.sqrt (Fintype.card (PolyIdx d)))*
      (((n:ℝ)*h^d)^(-(1/2:ℝ))+
        ((n:ℝ)*((n:ℝ)+m)*h^d*(h/J)^d)^(-(1/2:ℝ))) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hJpos : (0:ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  let a := ((n:ℝ)*h^d)^(-(1/2:ℝ))
  let b := ((n:ℝ)*((n:ℝ)+m)*h^d*(h/J)^d)^(-(1/2:ℝ))
  let q : ℝ := Fintype.card (PolyIdx d)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ha2 : a^2 = 1/((n:ℝ)*h^d) := upper_inverse_half_sq _ (by positivity)
  have hb2 : b^2 = 1/((n:ℝ)*((n:ℝ)+m)*h^d*(h/J)^d) := upper_inverse_half_sq _ (by positivity)
  have hid : 1/((n:ℝ)*h^d)+q*(J:ℝ)^d / ((n:ℝ)*((n:ℝ)+m)*h^(2*d)) =
      a^2+q*b^2 := by
    rw [ha2, hb2, div_pow, pow_mul]
    field_simp
    rw [← pow_mul, Nat.mul_comm 2 d, pow_mul]
    ring
  change Real.sqrt _ ≤ (1+Real.sqrt q)*(a+b)
  rw [hid]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hs := Real.sq_sqrt hq
  have hsq : a^2+q*b^2 ≤ (a+Real.sqrt q*b)^2 := by
    nlinarith [mul_nonneg ha (mul_nonneg (Real.sqrt_nonneg q) hb)]
  have hsum : a+Real.sqrt q*b ≤ (1+Real.sqrt q)*(a+b) := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg q) ha]
  exact hsq.trans (pow_le_pow_left₀ (by positivity) hsum 2)

/-- The clipped rectangular estimator attains the fixed-tuning risk envelope uniformly over the primitive class.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the rectangular fixed tuning risk conclusion](goal) holds. -/
lemma rectangular_fixed_tuning_risk (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (h : ℝ) (J : ℕ),
      2 ≤ n → 0 < h → h ≤ 1/2 → 1 ≤ J →
      ∃ hMeas : Measurable (fun w : Sample d n m => tHat eps h J w.1),
        ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
          risk ⟨fun w => tHat eps h J w.1, hMeas⟩ P hP ≤
            ENNReal.ofReal (C*min 1 (h^gamma+(h/J)^(alpha+beta)+
              ((n:ℝ)*h^d)^(-(1/2:ℝ))+
              ((n:ℝ)*((n:ℝ)+m)*h^d*(h/J)^d)^(-(1/2:ℝ)))) := by
  obtain ⟨A, hA, hmean⟩ := rectangular_risk_sqrt_variance d alpha beta gamma L eps hdom
  let K := 1+Real.sqrt (Fintype.card (PolyIdx d))
  let C := A*K+2
  have hK : 1 ≤ K := by dsimp [K]; linarith [Real.sqrt_nonneg (Fintype.card (PolyIdx d))]
  have hC : 0 < C := by dsimp [C, K]; positivity
  refine ⟨C, hC, ?_⟩
  intro n m h J hn hh hh' hJ
  obtain ⟨hMeas, hbound⟩ := hmean n m h J hn hh hh' hJ
  refine ⟨hMeas, ?_⟩
  intro P hP
  let b := h^gamma+(h/J)^(alpha+beta)
  let a := ((n:ℝ)*h^d)^(-(1/2:ℝ))+
    ((n:ℝ)*((n:ℝ)+m)*h^d*(h/J)^d)^(-(1/2:ℝ))
  let V := 1/((n:ℝ)*h^d)+(Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d /
    ((n:ℝ)*((n:ℝ)+m)*h^(2*d))
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hvar : Real.sqrt V ≤ K*a := rectangular_variance_sqrt_le_rates d n m J h hn hh hJ
  have hfull : risk ⟨fun w => tHat eps h J w.1, hMeas⟩ P hP ≤ ENNReal.ofReal (C*(b+a)) := by
    calc
      _ ≤ ENNReal.ofReal (A*(b+Real.sqrt V)) := hbound P hP
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hbase : b ≤ K*b := by nlinarith
        have hm := mul_le_mul_of_nonneg_left (add_le_add hbase hvar) hA.le
        dsimp [C]
        nlinarith
  rw [show h^gamma+(h/J)^(alpha+beta)+((n:ℝ)*h^d)^(-(1/2:ℝ))+
    ((n:ℝ)*((n:ℝ)+m)*h^d*(h/J)^d)^(-(1/2:ℝ)) = b+a by dsimp [b, a]; ring]
  by_cases hsmall : b+a ≤ 1
  · rw [min_eq_right hsmall]
    exact hfull
  · rw [min_eq_left (le_of_not_ge hsmall)]
    exact (tHat_risk_le_diameter P hP h J hMeas).trans
      (ENNReal.ofReal_le_ofReal (by dsimp [C, K]; nlinarith [Real.sqrt_nonneg (Fintype.card (PolyIdx d))]))

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

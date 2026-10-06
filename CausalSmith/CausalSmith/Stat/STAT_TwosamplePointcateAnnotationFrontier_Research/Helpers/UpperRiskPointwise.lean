module

public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.UpperRiskGeometry

/-! # Pointwise upper-risk assembly
Uniform deterministic error envelopes for the rectangular estimator, separating
the two sampling deviations, the population bias, and the failed guard.
-/

public section

noncomputable section
set_option linter.style.longLine false
set_option linter.style.whitespace false
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- The two arm-mean range conditions place the designated contrast in the clipping interval.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the tau mem clipping interval conclusion](goal) holds. -/
lemma tau_mem_clipping_interval {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (x : Cov d) (hx : x ∈ cube d) : tau P hP x ∈ Icc (-1) 1 := by
  have hspec := canonicalLaw_spec P hP
  have h0 := hspec.2.2.2.2.2.2.2.1 x hx
  have h1 := hspec.2.2.2.2.2.2.2.2 x hx
  simp only [tau, designatedTreated, designatedControl, if_pos hx, mem_Icc]
  constructor <;> linarith

/-- Clipping, including the zero fallback, always produces an output in the prescribed interval.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input D](hyp:D), [the specified input h](hyp:h), [the specified input J](hyp:J), [the overlap level eps](hyp:eps), [the t hat mem clipping interval conclusion](goal) holds. -/
lemma tHat_mem_clipping_interval {d n m : ℕ} (eps : ℝ) (D : Dataset d n m) (h : ℝ) (J : ℕ) :
    tHat eps h J D ∈ Icc (-1) 1 := by
  classical
  unfold tHat
  split_ifs
  · constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  · constructor <;> norm_num

/-- The absolute error is uniformly bounded by the diameter of the clipping interval.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input D](hyp:D), [the specified input h](hyp:h), [the specified input J](hyp:J), [the t hat absolute error le conclusion](goal) holds. -/
lemma tHat_absolute_error_le {d n m : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (D : Dataset d n m) (h : ℝ) (J : ℕ) :
    |tHat eps h J D-tau P hP (x0 d)| ≤ 2 := by
  have ht := tHat_mem_clipping_interval eps D h J
  have hy := tau_mem_clipping_interval P hP (x0 d) (x0_mem_cube d)
  exact abs_le.mpr ⟨by linarith [ht.1, hy.2], by linarith [ht.2, hy.1]⟩

/-- The localization center is in every positive-bandwidth box.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the x0 mem loc cube conclusion](goal) holds. -/
lemma x0_mem_locCube (d : ℕ) (h : ℝ) (hh : 0 ≤ h) : x0 d ∈ locCube d h := by
  intro i
  change (1/2:ℝ) ∈ Icc (1/2-h/2) (1/2+h/2)
  constructor <;> linarith

/-- Uniform pointwise assembly follows from the local polynomial approximation and the causal population-bias bridge. The failed-guard term is kept explicit for the probability bound.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the rectangular pointwise error bound conclusion](goal) holds. -/
lemma rectangular_pointwise_error_bound (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
      (n m : ℕ) (h : ℝ) (J : ℕ), 2 ≤ n → 0 < h → h ≤ 1/2 → 1 ≤ J →
      ∀ D : Dataset d n m,
        |tHat eps h J D-tau P hP (x0 d)| ≤
          C*(h^gamma+(h/J)^(alpha+beta) +
            Real.sqrt (∑ u, (rHat D h J u-rBar P n m h J u)^2) +
            Real.sqrt (∑ u, ∑ v, (qHat D h J u v-qPop P n m h J u v)^2)) +
          (if lambdaMin (qHat D h J) < gramGuard eps then (1:ℝ) else 0) := by
  classical
  obtain ⟨A, hA, hlocal⟩ := local_polynomial_projection_facts d alpha beta gamma L eps hdom
  let B := Real.sqrt (Fintype.card (PolyIdx d)) * (A^2+2*A)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg : 0 < gramGuard eps := hdom.gramGuard_pos
  let C := (gramGuard eps)⁻¹*A*(1+B+A)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro P hP n m h J hn hh hh' hJ D
  obtain ⟨⟨theta, herr, htheta, hcenter, htaylor⟩, hcoarse, hrow, htrace, he, hmu⟩ :=
    hlocal P hP h J hh hh' hJ
  have hbias : Real.sqrt (∑ u, (rBar P n m h J u-(qPop P n m h J).mulVec theta u)^2) ≤
      B*(h^gamma+(h/J)^(alpha+beta)) := by
    have hc := population_finite_norm_bound
      (fun u => rBar P n m h J u-(qPop P n m h J).mulVec theta u)
      ((A^2+2*A)*(h^gamma+(h/J)^(alpha+beta))) (by positivity)
      (population_bias_coordinate_bound P hP n m hn h hh hh' J hJ theta A hA herr he hmu)
    calc
      _ ≤ Real.sqrt (Fintype.card (PolyIdx d))*((A^2+2*A)*(h^gamma+(h/J)^(alpha+beta))) := hc
      _ = _ := by dsimp [B]; ring
  have hr0 : Real.sqrt (∑ u, (r0 d h u)^2) ≤ A :=
    hcoarse (x0 d) (x0_mem_locCube d h hh.le)
  have hbase : 0 ≤ h^gamma+(h/J)^(alpha+beta) := by positivity
  have hnoiseR : 0 ≤ Real.sqrt (∑ u, (rHat D h J u-rBar P n m h J u)^2) := Real.sqrt_nonneg _
  have hnoiseQ : 0 ≤ Real.sqrt (∑ u, ∑ v, (qHat D h J u v-qPop P n m h J u v)^2) := Real.sqrt_nonneg _
  by_cases hgood : gramGuard eps ≤ lambdaMin (qHat D h J)
  · have hp := tHat_good_branch_error hg D h J theta (rBar P n m h J) (qPop P n m h J)
      (tau P hP (x0 d)) (tau_mem_clipping_interval P hP (x0 d) (x0_mem_cube d)) hcenter hgood
    rw [if_neg (not_lt_of_ge hgood), add_zero]
    calc
      _ ≤ (gramGuard eps)⁻¹*Real.sqrt (∑ u, (r0 d h u)^2) *
          (Real.sqrt (∑ u, (rHat D h J u-rBar P n m h J u)^2) +
           Real.sqrt (∑ u, (rBar P n m h J u-(qPop P n m h J).mulVec theta u)^2) +
           Real.sqrt (∑ u, ∑ v, (qHat D h J u v-qPop P n m h J u v)^2)*Real.sqrt (∑ u, theta u^2)) := hp
      _ ≤ (gramGuard eps)⁻¹*A *
          (Real.sqrt (∑ u, (rHat D h J u-rBar P n m h J u)^2) +
           B*(h^gamma+(h/J)^(alpha+beta)) +
           Real.sqrt (∑ u, ∑ v, (qHat D h J u v-qPop P n m h J u v)^2)*A) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hr0 (inv_nonneg.mpr hg.le)
        · exact add_le_add (add_le_add (le_refl _) hbias) (mul_le_mul_of_nonneg_left htheta hnoiseQ)
        · positivity
        · positivity
      _ ≤ _ := by
        have hk : 0 ≤ (gramGuard eps)⁻¹*A := by positivity
        have hbr : 1 ≤ 1+B+A := by linarith
        have hbb : B ≤ 1+B+A := by linarith
        have hbq : A ≤ 1+B+A := by linarith
        have hsum : Real.sqrt (∑ u, (rHat D h J u-rBar P n m h J u)^2) +
            B*(h^gamma+(h/J)^(alpha+beta)) +
            Real.sqrt (∑ u, ∑ v, (qHat D h J u v-qPop P n m h J u v)^2)*A ≤
            (1+B+A)*((h^gamma+(h/J)^(alpha+beta)) +
            Real.sqrt (∑ u, (rHat D h J u-rBar P n m h J u)^2) +
            Real.sqrt (∑ u, ∑ v, (qHat D h J u v-qPop P n m h J u v)^2)) := by
          nlinarith [mul_le_mul_of_nonneg_right hbr hnoiseR,
            mul_le_mul_of_nonneg_right hbb hbase, mul_le_mul_of_nonneg_right hbq hnoiseQ]
        have hm := mul_le_mul_of_nonneg_left hsum hk
        dsimp [C]
        nlinarith
  · have hbad : lambdaMin (qHat D h J) < gramGuard eps := lt_of_not_ge hgood
    rw [if_pos hbad, tHat, if_neg hgood, zero_sub, abs_neg]
    have hy := tau_mem_clipping_interval P hP (x0 d) (x0_mem_cube d)
    have habs : |tau P hP (x0 d)| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
    have hnonneg : 0 ≤ C*(h^gamma+(h/J)^(alpha+beta) +
        Real.sqrt (∑ u, (rHat D h J u-rBar P n m h J u)^2) +
        Real.sqrt (∑ u, ∑ v, (qHat D h J u v-qPop P n m h J u v)^2)) := by positivity
    linarith

/-- The clipped estimator has finite absolute-loss risk on every primitive-class law.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hMeas](hyp:hMeas), [the t hat risk le diameter conclusion](goal) holds. -/
lemma tHat_risk_le_diameter {d n m : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) (h : ℝ) (J : ℕ)
    (hMeas : Measurable (fun w : Sample d n m => tHat eps h J w.1)) :
    risk ⟨fun w => tHat eps h J w.1, hMeas⟩ P hP ≤ ENNReal.ofReal (2:ℝ) := by
  let := experiment_probability d n m P
  unfold risk
  calc
    _ ≤ ∫⁻ _ : Sample d n m, ENNReal.ofReal (2:ℝ) ∂experiment P n m := by
      apply lintegral_mono
      intro w
      exact ENNReal.ofReal_le_ofReal (tHat_absolute_error_le P hP w.1 h J)
    _ = _ := by simp

/-- The pointwise assembly reduces fixed-tuning risk to the two mean Euclidean deviations and the failed-guard indicator, while retaining a finite uniform cap.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the rectangular risk envelope reduction conclusion](goal) holds. -/
lemma rectangular_risk_envelope_reduction (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
      (n m : ℕ) (h : ℝ) (J : ℕ), 2 ≤ n → 0 < h → h ≤ 1/2 → 1 ≤ J →
      ∃ hMeas : Measurable (fun w : Sample d n m => tHat eps h J w.1),
        risk ⟨fun w => tHat eps h J w.1, hMeas⟩ P hP ≤ ENNReal.ofReal (2:ℝ) ∧
        risk ⟨fun w => tHat eps h J w.1, hMeas⟩ P hP ≤
          ∫⁻ w, ENNReal.ofReal
            (C*(h^gamma+(h/J)^(alpha+beta) +
              Real.sqrt (∑ u, (rHat w.1 h J u-rBar P n m h J u)^2) +
              Real.sqrt (∑ u, ∑ v, (qHat w.1 h J u v-qPop P n m h J u v)^2)) +
            (if lambdaMin (qHat w.1 h J) < gramGuard eps then (1:ℝ) else 0))
            ∂experiment P n m := by
  obtain ⟨C, hC, hpoint⟩ := rectangular_pointwise_error_bound d alpha beta gamma L eps hdom
  refine ⟨C, hC, ?_⟩
  intro P hP n m h J hn hh hh' hJ
  let hMeas := tHat_measurable d n m eps h J hn hh hh' hJ
  refine ⟨hMeas, tHat_risk_le_diameter P hP h J hMeas, ?_⟩
  apply lintegral_mono
  intro w
  exact ENNReal.ofReal_le_ofReal (hpoint P hP n m h J hn hh hh' hJ w.1)

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

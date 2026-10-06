module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.OracleSmoother
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationOutcomeMoments

/-! # Oracle response identification
Bounded inverse-propensity tests identify the conditional effect, and uniform
design transports the oracle evaluation kernel to its local projection mean.
-/

public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Overlap bounds both inverse-propensity test functions on their cube support.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input he](hyp:he), [the specified input f](hyp:f), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hf](hyp:hf), [the specified input hs](hyp:hs), [the overlap level eps](hyp:eps), [the oracle inverse test bound conclusion](goal) holds. -/
lemma oracle_inverse_test_bound {d : ℕ} {eps : ℝ} (P : PrimitiveLaw d) (he : Overlap eps P)
    (f : Cov d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ x, ‖f x‖ ≤ B) (hs : ∀ x, x ∉ cube d → f x = 0) :
    (∀ x, ‖f x / P.e x‖ ≤ eps⁻¹*B) ∧
    (∀ x, ‖f x / (1-P.e x)‖ ≤ eps⁻¹*B) := by
  have heps : 0 < eps := he.1
  have hdiv (x : Cov d) (q : ℝ) (hq : eps ≤ q) : ‖f x / q‖ ≤ eps⁻¹*B := by
    have hq0 : 0 < q := by linarith
    rw [norm_div, Real.norm_eq_abs q, abs_of_pos hq0]
    apply (div_le_iff₀ hq0).2
    have h1 : 1 ≤ eps⁻¹ * q := by
      rw [← div_eq_inv_mul, le_div_iff₀ heps]; linarith
    calc ‖f x‖ ≤ B := hf x
      _ = 1 * B := (one_mul B).symm
      _ ≤ (eps⁻¹ * q) * B := mul_le_mul_of_nonneg_right h1 hB
      _ = _ := by ring
  have hepsi : 0 ≤ eps⁻¹ * B := mul_nonneg (inv_nonneg.mpr heps.le) hB
  constructor <;> intro x <;> by_cases hx : x ∈ cube d
  · exact hdiv x _ (he.2 x hx).1
  · simp [hs x hx, hepsi]
  · exact hdiv x _ (by linarith [(he.2 x hx).2])
  · simp [hs x hx, hepsi]

/-- The supplied inverse-propensity response has effect mean against every bounded
cube-supported Borel test, by cancellation in the two identified arm moments.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input hdesign](hyp:hdesign), [the specified input hex](hyp:hex), [the specified input he](hyp:he), [the specified input hm0](hyp:hm0), [the specified input hm1](hyp:hm1), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hfB](hyp:hfB), [the specified input hs](hyp:hs), [the overlap level eps](hyp:eps), [the oracle response test mean conclusion](goal) holds. -/
lemma oracle_response_test_mean {d : ℕ} {eps : ℝ} (P : PrimitiveLaw d)
    (hdesign : UniformDesign P) (hex : ConditionalExchangeability P) (he : Overlap eps P)
    (hm0 : ControlInterior P) (hm1 : TreatedInterior P)
    (f : Cov d → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hfB : ∀ x, ‖f x‖ ≤ B) (hs : ∀ x, x ∉ cube d → f x = 0) :
    (∫ w, f w.1 * (bit w.2.1 * bit w.2.2 / P.e w.1 -
      (1-bit w.2.1)*bit w.2.2 / (1-P.e w.1)) ∂obsLaw P) =
      ∫ x, f x * (P.mu1 x-P.mu0 x) ∂uniformLaw d := by
  letI := obsLaw_probability P
  have hPe := P.measurable_e
  have hb := oracle_inverse_test_bound P he f B hB hfB hs
  have heps : 0 < eps := he.1
  have hbits (a y : Bool) : ‖bit a * bit y‖ ≤ 1 ∧ ‖(1-bit a)*bit y‖ ≤ 1 := by
    cases a <;> cases y <;> norm_num [bit]
  have hi : Integrable (fun w : Cov d × Bool × Bool =>
      (f w.1/P.e w.1)*bit w.2.1*bit w.2.2) (obsLaw P) := by
    apply population_integrable_bounded _ _ (by fun_prop) (eps⁻¹*B)
    intro w
    rw [mul_assoc, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hbits _ _).1 (norm_nonneg _)).trans (by simpa using hb.1 w.1)
  have hj : Integrable (fun w : Cov d × Bool × Bool =>
      (f w.1/(1-P.e w.1))*(1-bit w.2.1)*bit w.2.2) (obsLaw P) := by
    apply population_integrable_bounded _ _ (by fun_prop) (eps⁻¹*B)
    intro w
    rw [mul_assoc, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hbits _ _).2 (norm_nonneg _)).trans (by simpa using hb.2 w.1)
  have ht := population_treated_outcome_moment P hdesign hex he hm1
    (fun x => f x/P.e x) (by fun_prop) (eps⁻¹*B) (by positivity) hb.1
    (by intro x hx; simp [hs x hx])
  have hc := population_control_outcome_moment P hdesign hex he hm0
    (fun x => f x/(1-P.e x)) (by fun_prop) (eps⁻¹*B) (by positivity) hb.2
    (by intro x hx; simp [hs x hx])
  have hut : (∫ x, (f x/P.e x)*P.e x*P.mu1 x ∂uniformLaw d) =
      ∫ x, f x*P.mu1 x ∂uniformLaw d := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet (cube d) from by
      unfold cube; simp only [setOf_forall]; exact MeasurableSet.iInter (fun i => measurableSet_Icc.preimage (by fun_prop)))] with x hx
    rw [div_mul_cancel₀ _ (by linarith [(he.2 x hx).1, he.1] : P.e x ≠ 0)]
  have huc : (∫ x, (f x/(1-P.e x))*(1-P.e x)*P.mu0 x ∂uniformLaw d) =
      ∫ x, f x*P.mu0 x ∂uniformLaw d := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet (cube d) from by
      unfold cube; simp only [setOf_forall]; exact MeasurableSet.iInter (fun i => measurableSet_Icc.preimage (by fun_prop)))] with x hx
    rw [div_mul_cancel₀ _ (by linarith [(he.2 x hx).2, he.1] : 1-P.e x ≠ 0)]
  have hu : IsProbabilityMeasure (uniformLaw d) := by
    rw [← hdesign]; exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI := hu
  have hmu (g : Cov d → ℝ) (hg : Measurable g)
      (hgB : ∀ x ∈ cube d, g x ∈ Icc 0 1) :
      Integrable (fun x => f x*g x) (uniformLaw d) := by
    apply population_integrable_bounded _ _ (by fun_prop) B
    intro x
    by_cases hx : x ∈ cube d
    · rw [norm_mul, Real.norm_eq_abs (g x), abs_of_nonneg (hgB x hx).1]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hgB x hx).2).trans (hfB x)
    · simp [hs x hx, hB]
  have hiu := hmu P.mu1 P.measurable_mu1 (by intro x hx; constructor <;> linarith [(hm1 x hx).1, (hm1 x hx).2])
  have hju := hmu P.mu0 P.measurable_mu0 (by intro x hx; constructor <;> linarith [(hm0 x hx).1, (hm0 x hx).2])
  have heq : (fun w : Cov d × Bool × Bool => f w.1 *
      (bit w.2.1 * bit w.2.2 / P.e w.1 - (1-bit w.2.1)*bit w.2.2/(1-P.e w.1))) =
      fun w => (f w.1/P.e w.1)*bit w.2.1*bit w.2.2 -
        (f w.1/(1-P.e w.1))*(1-bit w.2.1)*bit w.2.2 := by
    funext w; ring
  rw [heq, integral_sub hi hj, ht, hc, hut, huc, ← integral_sub hiu hju]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- The oracle kernel's record expectation is the known-design local projection
of the canonical effect, throughout the full admissible oracle bandwidth range.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the oracle summand mean conclusion](goal) holds. -/
lemma oracle_summand_mean {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1) :
    (∫ w, locWeight h w.1 *
      ((∑ u : PolyIdx d, r0 d h u * coarseBasis h w.1 u) *
        (bit w.2.1 * bit w.2.2 / designatedPropensity P hP w.1 -
          (1-bit w.2.1)*bit w.2.2 / (1-designatedPropensity P hP w.1))) ∂obsLaw P) =
      ∫ x, (∑ u : PolyIdx d, r0 d h u * coarseBasis h x u) * tau P hP x
        ∂locLaw d h := by
  let K := fun x : Cov d => ∑ u : PolyIdx d, r0 d h u * coarseBasis h x u
  let F := fun x : Cov d => locWeight h x * K x
  have hs := canonicalLaw_spec P hP
  have hobs : obsLaw P = obsLaw (canonicalLaw P hP) := by
    unfold obsLaw; rw [hs.1]
  have hFB : ∀ x, ‖F x‖ ≤ h^(-(d:ℝ))*
      ((Fintype.card (PolyIdx d):ℝ) * ((4:ℝ)^d)^2) := by
    apply locWeight_mul_norm_bound h hh K _ (by positivity)
    intro x hx
    simpa only [Real.norm_eq_abs] using oracle_evaluation_kernel_bound d h hh x hx
  have hFs : ∀ x, x ∉ cube d → F x = 0 := by
    intro x hx
    have hn : x ∉ locCube d h := fun hl => hx (oracle_locCube_subset_cube d h hh' hl)
    simp [F, locWeight, hn]
  have hm := oracle_response_test_mean (canonicalLaw P hP)
    hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.2
    F (by dsimp [F, K]; fun_prop) _ (by positivity) hFB hFs
  calc
    _ = ∫ w, F w.1 * (bit w.2.1 * bit w.2.2 / (canonicalLaw P hP).e w.1 -
        (1-bit w.2.1)*bit w.2.2 / (1-(canonicalLaw P hP).e w.1))
        ∂obsLaw (canonicalLaw P hP) := by
      rw [hobs]
      apply integral_congr_ae
      filter_upwards [] with w
      by_cases hx : w.1 ∈ locCube d h
      · simp only [designatedPropensity, if_pos (oracle_locCube_subset_cube d h hh' hx), F, K]
        ring
      · simp [F, locWeight, hx]
    _ = ∫ x, K x * ((canonicalLaw P hP).mu1 x-(canonicalLaw P hP).mu0 x)
        ∂locLaw d h := by
      rw [hm]
      dsimp only [F]
      simp only [mul_assoc]
      exact oracle_uniform_localization_integral d h hh hh' _
    _ = _ := by
      apply integral_congr_ae
      unfold locLaw
      apply Measure.ae_smul_measure
      filter_upwards [ae_restrict_mem (isClosed_locCube d h).measurableSet] with x hx
      simp only [tau, designatedTreated, designatedControl,
        if_pos (oracle_locCube_subset_cube d h hh' hx), K]

/-- Full-window coarse orthonormality normalizes the oracle localization law.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the oracle localization probability conclusion](goal) holds. -/
lemma oracle_localization_probability (d : ℕ) (h : ℝ) (hh : 0 < h) :
    IsProbabilityMeasure (locLaw d h) := by
  let z : PolyIdx d := ⟨fun _ => 0, by simp⟩
  have ho := oracle_coarse_orthonormal d h hh z z
  simp only [z, coarseBasis, legendre, ite_true, Finset.prod_const_one, one_mul] at ho
  apply isProbabilityMeasure_iff_real.mpr
  simpa only [integral_const, smul_eq_mul, mul_one] using ho

/-- The oracle evaluation kernel reproduces every coarse polynomial at the target.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input theta](hyp:theta), [the oracle polynomial reproduction conclusion](goal) holds. -/
lemma oracle_polynomial_reproduction (d : ℕ) (h : ℝ) (hh : 0 < h)
    (theta : PolyIdx d → ℝ) :
    (∫ x, (∑ u : PolyIdx d, r0 d h u * coarseBasis h x u) * pv h theta x
      ∂locLaw d h) = pv h theta (x0 d) := by
  have hi (u v : PolyIdx d) : Integrable
      (fun x => (r0 d h u * coarseBasis h x u) * (coarseBasis h x v * theta v))
      (locLaw d h) := by
    convert ((oracle_coarseBasis_memLp d h hh u).integrable_mul
      (oracle_coarseBasis_memLp d h hh v)).const_mul (r0 d h u * theta v) using 1
    ext x; simp only [Pi.mul_apply]; ring
  simp only [pv, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun v _ => integrable_finsetSum _ (fun u _ => hi u v))]
  simp_rw [integral_finsetSum _ (fun u _ => hi u _)]
  simp_rw [show ∀ (u v : PolyIdx d) x,
    (r0 d h u * coarseBasis h x u) * (coarseBasis h x v * theta v) =
      (r0 d h u * theta v) * (coarseBasis h x u * coarseBasis h x v) by intros; ring]
  simp_rw [integral_const_mul, oracle_coarse_orthonormal d h hh]
  simp [r0]

/-- Polynomial reproduction converts a uniform approximation remainder into an
oracle mean bias bound, with the explicit finite-dimensional kernel constant.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input theta](hyp:theta), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input herr](hyp:herr), [the specified input htarget](hyp:htarget), [the oracle projection bias bound conclusion](goal) holds. -/
lemma oracle_projection_bias_bound {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (hh : 0 < h) (theta : PolyIdx d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (herr : ∀ x ∈ locCube d h, |tau P hP x-pv h theta x| ≤ B)
    (htarget : pv h theta (x0 d) = tau P hP (x0 d)) :
    |(∫ x, (∑ u : PolyIdx d, r0 d h u * coarseBasis h x u) * tau P hP x
      ∂locLaw d h) - tau P hP (x0 d)| ≤
      ((Fintype.card (PolyIdx d):ℝ) * ((4:ℝ)^d)^2) * B := by
  letI := oracle_localization_probability d h hh
  let K := fun x : Cov d => ∑ u : PolyIdx d, r0 d h u * coarseBasis h x u
  have hae : ∀ᵐ x ∂locLaw d h, x ∈ locCube d h := by
    unfold locLaw; apply Measure.ae_smul_measure
    exact ae_restrict_mem (isClosed_locCube d h).measurableSet
  have hk : MemLp K 2 (locLaw d h) :=
    memLp_finsetSum _ (fun u _ => (oracle_coarseBasis_memLp d h hh u).const_mul _)
  have hp : MemLp (pv h theta) 2 (locLaw d h) := by
    unfold pv
    exact memLp_finsetSum _ (fun u _ => (oracle_coarseBasis_memLp d h hh u).mul_const _)
  have he : MemLp (fun x => tau P hP x-pv h theta x) 2 (locLaw d h) := by
    apply (memLp_top_of_bound ((measurable_tau P hP).sub (by unfold pv; fun_prop)).aestronglyMeasurable B ?_).mono_exponent (by simp)
    filter_upwards [hae] with x hx
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using herr x hx
  have ht : MemLp (tau P hP) 2 (locLaw d h) := by
    convert he.add hp using 1
    ext x; simp
  rw [← htarget, ← oracle_polynomial_reproduction d h hh theta,
    ← integral_sub (f := fun x => K x*tau P hP x) (g := fun x => K x*pv h theta x)
      (hk.integrable_mul ht) (hk.integrable_mul hp)]
  have hr : (fun x => K x*tau P hP x-K x*pv h theta x) =
      fun x => K x*(tau P hP x-pv h theta x) := by funext x; ring
  change |∫ x, K x*tau P hP x-K x*pv h theta x ∂locLaw d h| ≤ _
  rw [hr]
  apply (abs_integral_le_integral_abs).trans
  calc
    _ ≤ ∫ _x : Cov d, ((Fintype.card (PolyIdx d):ℝ) * ((4:ℝ)^d)^2)*B
        ∂locLaw d h := by
      apply integral_mono_ae (hk.integrable_mul he).abs (integrable_const _)
      filter_upwards [hae] with x hx
      simp only [Pi.mul_apply]
      rw [abs_mul]
      exact mul_le_mul (oracle_evaluation_kernel_bound d h hh x hx)
        (herr x hx) (abs_nonneg _) (by positivity)
    _ = _ := by simp

/-- Averaging all labeled oracle responses preserves their local projection mean;
auxiliary records and the independent randomizer integrate out exactly.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the oracle average mean conclusion](goal) holds. -/
lemma oracle_average_mean {d n m : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (hn : 0 < n) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1) :
    (∫ w : Sample d n m, (n:ℝ)⁻¹ * ∑ i : Fin n,
      locWeight h (w.1.1 i).1 *
        ((∑ u : PolyIdx d, r0 d h u * coarseBasis h (w.1.1 i).1 u) *
          (bit (w.1.1 i).2.1 * bit (w.1.1 i).2.2 / designatedPropensity P hP (w.1.1 i).1 -
            (1-bit (w.1.1 i).2.1)*bit (w.1.1 i).2.2 / (1-designatedPropensity P hP (w.1.1 i).1)))
      ∂experiment P n m) =
      ∫ x, (∑ u : PolyIdx d, r0 d h u * coarseBasis h x u) * tau P hP x
        ∂locLaw d h := by
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  letI := population_randomizer_probability
  letI := population_experiment_probability P n m
  let F := fun z : Cov d × Bool × Bool => locWeight h z.1 *
    ((∑ u : PolyIdx d, r0 d h u * coarseBasis h z.1 u) *
      (bit z.2.1 * bit z.2.2 / designatedPropensity P hP z.1 -
        (1-bit z.2.1)*bit z.2.2 / (1-designatedPropensity P hP z.1)))
  have hF := oracle_summand_memLp_top (obsLaw P) P hP h hh id measurable_id
  have hi (i : Fin n) : Integrable (fun w : Sample d n m => F (w.1.1 i))
      (experiment P n m) :=
    (oracle_summand_memLp_top (experiment P n m) P hP h hh
      (fun w => w.1.1 i) (by fun_prop)).integrable (by simp)
  have hmean (i : Fin n) : (∫ w : Sample d n m, F (w.1.1 i) ∂experiment P n m) =
      ∫ z, F z ∂obsLaw P := by
    rw [experiment_integral_dataset P (fun D : Dataset d n m => F (D.1 i)),
      integral_fun_fst (fun D : Fin n → Cov d × Bool × Bool => F (D i))]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    exact integral_comp_eval (μ := fun _ : Fin n => obsLaw P) (f := F) hF.aestronglyMeasurable
  change (∫ w : Sample d n m, (n:ℝ)⁻¹ * ∑ i : Fin n, F (w.1.1 i)
    ∂experiment P n m) = _
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [hmean]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hn.ne' : (n:ℝ) ≠ 0), one_mul]
  exact oracle_summand_mean P hP h hh hh'

/-- The untruncated oracle sample average inherits the polynomial approximation
bias without any loss from the auxiliary channel or randomization.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input theta](hyp:theta), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input herr](hyp:herr), [the specified input htarget](hyp:htarget), [the oracle average bias bound conclusion](goal) holds. -/
lemma oracle_average_bias_bound {d n m : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (hn : 0 < n) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1)
    (theta : PolyIdx d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (herr : ∀ x ∈ locCube d h, |tau P hP x-pv h theta x| ≤ B)
    (htarget : pv h theta (x0 d) = tau P hP (x0 d)) :
    |(∫ w : Sample d n m, (n:ℝ)⁻¹ * ∑ i : Fin n,
      locWeight h (w.1.1 i).1 *
        ((∑ u : PolyIdx d, r0 d h u * coarseBasis h (w.1.1 i).1 u) *
          (bit (w.1.1 i).2.1 * bit (w.1.1 i).2.2 / designatedPropensity P hP (w.1.1 i).1 -
            (1-bit (w.1.1 i).2.1)*bit (w.1.1 i).2.2 / (1-designatedPropensity P hP (w.1.1 i).1)))
      ∂experiment P n m) - tau P hP (x0 d)| ≤
      ((Fintype.card (PolyIdx d):ℝ) * ((4:ℝ)^d)^2) * B := by
  rw [oracle_average_mean P hP hn h hh hh']
  exact oracle_projection_bias_bound P hP h hh theta B hB herr htarget

/-- Full-window Taylor reproduction bounds the bias uniformly over the primitive class.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the oracle uniform average bias conclusion](goal) holds. -/
lemma oracle_uniform_average_bias (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 0 < n →
      ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
      ∀ (h : ℝ), 0 < h → h ≤ 1 →
    |(∫ w : Sample d n m, (n:ℝ)⁻¹ * ∑ i : Fin n,
      locWeight h (w.1.1 i).1 *
        ((∑ u : PolyIdx d, r0 d h u * coarseBasis h (w.1.1 i).1 u) *
          (bit (w.1.1 i).2.1 * bit (w.1.1 i).2.2 / designatedPropensity P hP (w.1.1 i).1 -
            (1-bit (w.1.1 i).2.1)*bit (w.1.1 i).2.2 / (1-designatedPropensity P hP (w.1.1 i).1)))
      ∂experiment P n m) - tau P hP (x0 d)| ≤ C*h^gamma := by
  obtain ⟨Ct, hCt, ht⟩ := oracle_taylor_approximation d alpha beta gamma L eps hdom
  let K : ℝ := (Fintype.card (PolyIdx d):ℝ) * ((4:ℝ)^d)^2
  have hcard : 0 < Fintype.card (PolyIdx d) := by
    have : Nonempty (PolyIdx d) := ⟨⟨fun _ => 0, by simp⟩⟩
    exact Fintype.card_pos
  have hK : 0 < K := mul_pos (by exact_mod_cast hcard) (by positivity)
  refine ⟨K*Ct, mul_pos hK hCt, ?_⟩
  intro n m hn P hP h hh hh'
  obtain ⟨theta, herr, htarget, _⟩ := ht P hP h hh hh'
  have hb := oracle_average_bias_bound (m := m) P hP hn h hh hh' theta
    (Ct*h^gamma) (by positivity) herr htarget
  simpa only [K, mul_assoc] using hb

/-- At the prescribed oracle bandwidth the uniform average bias has the oracle rate.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the oracle tuned average bias conclusion](goal) holds. -/
lemma oracle_tuned_average_bias (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 2 ≤ n →
      ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
    |(∫ w : Sample d n m, (n:ℝ)⁻¹ * ∑ i : Fin n,
      locWeight ((n:ℝ)^(-(1/(2*gamma+d)))) (w.1.1 i).1 *
        ((∑ u : PolyIdx d, r0 d ((n:ℝ)^(-(1/(2*gamma+d)))) u * coarseBasis ((n:ℝ)^(-(1/(2*gamma+d)))) (w.1.1 i).1 u) *
          (bit (w.1.1 i).2.1 * bit (w.1.1 i).2.2 / designatedPropensity P hP (w.1.1 i).1 -
            (1-bit (w.1.1 i).2.1)*bit (w.1.1 i).2.2 / (1-designatedPropensity P hP (w.1.1 i).1)))
      ∂experiment P n m) - tau P hP (x0 d)| ≤ C*oracleRate d gamma n := by
  obtain ⟨C, hC, hbound⟩ := oracle_uniform_average_bias d alpha beta gamma L eps hdom
  refine ⟨C, hC, ?_⟩
  intro n m hn P hP
  have hn0 : 0 < n := by omega
  obtain ⟨hh, hh'⟩ := oracle_bandwidth_bounds d n gamma hn hdom.2.2.2.2.2.1
  have hb := hbound n m hn0 P hP _ hh hh'
  rwa [oracle_bandwidth_bias_identity d n gamma hn0] at hb

/-- The original-record experiment preserves the iid variance reduction for any labeled statistic.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input hn](hyp:hn), [the specified input F](hyp:F), [the specified input hF](hyp:hF), [the oracle iid centered second moment conclusion](goal) holds. -/
lemma oracle_iid_centered_second_moment {d n m : ℕ} (P : PrimitiveLaw d)
    (hn : 0 < n) (F : Cov d × Bool × Bool → ℝ) (hF : MemLp F 2 (obsLaw P)) :
    (∫ w : Sample d n m,
      ((n:ℝ)⁻¹ * ∑ i : Fin n, F (w.1.1 i) - ∫ z, F z ∂obsLaw P)^2
        ∂experiment P n m) ≤ (n:ℝ)⁻¹ * ∫ z, (F z)^2 ∂obsLaw P := by
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  letI := population_randomizer_probability
  let A := fun s : Fin n → Cov d × Bool × Bool => (n:ℝ)⁻¹ * ∑ i, F (s i)
  let μ := Measure.pi (fun _ : Fin n => obsLaw P)
  have hA : MemLp A 2 μ :=
    (memLp_finsetSum _ (fun i _ => hF.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => obsLaw P) i))).const_mul _
  have hmean : (∫ s, A s ∂μ) = ∫ z, F z ∂obsLaw P :=
    Causalean.Mathlib.Probability.iid_average_integral (obsLaw P) n hn F
      (hF.integrable (by norm_num))
  have hv := Causalean.Mathlib.Probability.iid_average_variance (obsLaw P) n F hF
  have hvar : variance F (obsLaw P) ≤ ∫ z, (F z)^2 ∂obsLaw P := by
    rw [variance_eq_sub hF]
    exact sub_le_self _ (sq_nonneg _)
  calc
    _ = ∫ s, (A s - ∫ z, F z ∂obsLaw P)^2 ∂μ := by
      rw [experiment_integral_dataset P
        (fun D : Dataset d n m => (A D.1 - ∫ z, F z ∂obsLaw P)^2),
        integral_fun_fst (fun s => (A s - ∫ z, F z ∂obsLaw P)^2)]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      rfl
    _ = variance A μ := by
      rw [variance_eq_integral hA.aemeasurable, hmean]
    _ = (n:ℝ)⁻¹ * variance F (obsLaw P) := hv
    _ ≤ _ := mul_le_mul_of_nonneg_left hvar (by positivity)

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

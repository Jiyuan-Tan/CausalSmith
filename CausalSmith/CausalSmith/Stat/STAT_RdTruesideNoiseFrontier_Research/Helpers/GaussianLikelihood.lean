module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.MarkedConvolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Gaussian reference likelihood on the full proxy line

The midpoint denominator comparison and absolute integrability of the signed
Gaussian cross-kernel justify the Fubini step preceding the moment series ML.5.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- Dividing the global midpoint lower bound gives the pointwise ML.3 comparison. Given [the displayed inputs and assumptions](hyp:b,σ,m,hb,hσ,w), [the stated mathematical conclusion holds](goal). -/
lemma marked_square_midpoint_comparison (b σ : ℝ) (m : ℕ)
    (hb : b ∈ Ioc (0 : ℝ) 1) (hσ : 0 < σ) (w : ℝ) :
    markedConvolution b m σ w ^ 2 / treatedConvolution σ w ≤
      (Real.exp (b^2/(24*σ^2))/b) *
        (markedConvolution b m σ w ^ 2 / phi σ (w-b/2)) := by
  have hbp := hb.1
  have hp := phi_pos σ (w-b/2) hσ
  have hd := treatedConvolution_centered_lower b σ w ⟨hb.1.le, hb.2⟩
  calc
    _ ≤ markedConvolution b m σ w ^ 2 /
        (b * Real.exp (-b^2/(24*σ^2)) * phi σ (w-b/2)) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hd
    _ = _ := by
      rw [show -b^2/(24*σ^2) = -(b^2/(24*σ^2)) by ring, Real.exp_neg]
      field_simp

/-- The centered cross exponent stays below λ on the entire support square. Given [the displayed inputs and assumptions](hyp:b,σ,x,t,hb,hx,ht), [the stated mathematical conclusion holds](goal). -/
lemma centered_cross_exponent_le (b σ x t : ℝ) (hb : 0 ≤ b)
    (hx : x ∈ Icc (0 : ℝ) b) (ht : t ∈ Icc (0 : ℝ) b) :
    (x-b/2)*(t-b/2)/σ^2 ≤ likelihoodLambda b σ := by
  have hx' : |x-b/2| ≤ b/2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have ht' : |t-b/2| ≤ b/2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hh := mul_le_mul hx' ht' (abs_nonneg _) (by linarith : 0 ≤ b/2)
  have hp : (x-b/2)*(t-b/2) ≤ b^2/4 := by
    have ha := le_abs_self ((x-b/2)*(t-b/2))
    rw [abs_mul] at ha
    nlinarith only [ha, hh]
  unfold likelihoodLambda
  simpa only [div_div] using div_le_div_of_nonneg_right hp (sq_nonneg σ)

/-- The absolute signed cross-kernel has an explicit finite Gaussian integral (ML.4). Given [the displayed inputs and assumptions](hyp:b,σ,m,x,t,hσ), [the stated mathematical conclusion holds](goal). -/
lemma signed_gaussian_cross_norm_integral (b σ : ℝ) (m : ℕ) (x t : ℝ)
    (hσ : 0 < σ) :
    (∫ w, ‖block m (x/b) * block m (t/b) *
      (phi σ (w-x) * phi σ (w-t) / phi σ (w-b/2))‖) =
      |block m (x/b) * block m (t/b)| *
        Real.exp ((x-b/2)*(t-b/2)/σ^2) := by
  simp_rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (div_nonneg (mul_nonneg (phi_nonneg σ _) (phi_nonneg σ _))
      (phi_nonneg σ _))]
  rw [integral_const_mul, phi_product_div_integral σ x t (b/2) hσ]

/-- Absolute cross-kernel integrability justifies signed Fubini over both latent
coordinates and every real proxy value, with no discarded tails (ML.4--ML.5). Given [the displayed inputs and assumptions](hyp:hleg,b,σ,m,hb,hσ), [the stated mathematical conclusion holds](goal). -/
lemma signed_gaussian_cross_integrable (hleg : ClassicalLegendreFacts)
    (b σ : ℝ) (m : ℕ) (hb : 0 < b) (hσ : 0 < σ) :
    Integrable (fun z : (ℝ × ℝ) × ℝ =>
      block m (z.1.1/b) * block m (z.1.2/b) *
        (phi σ (z.2-z.1.1) * phi σ (z.2-z.1.2) / phi σ (z.2-b/2)))
      (((volume.restrict (Ioc (0 : ℝ) b)).prod
        (volume.restrict (Ioc (0 : ℝ) b))).prod volume) := by
  have hm : StronglyMeasurable (fun z : (ℝ × ℝ) × ℝ =>
      block m (z.1.1/b) * block m (z.1.2/b) *
        (phi σ (z.2-z.1.1) * phi σ (z.2-z.1.2) / phi σ (z.2-b/2))) := by
    unfold block legendreP
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun p =>
      (phi_product_div_integrable σ p.1 p.2 (b/2) hσ).const_mul
        (block m (p.1/b) * block m (p.2/b)))
  · simp_rw [signed_gaussian_cross_norm_integral b σ m _ _ hσ]
    apply (integrable_const (Real.exp (likelihoodLambda b σ))).mono'
    · have hc : StronglyMeasurable (fun p : ℝ × ℝ =>
          |block m (p.1/b) * block m (p.2/b)| *
            Real.exp ((p.1-b/2)*(p.2-b/2)/σ^2)) := by
        unfold block legendreP
        fun_prop
      exact hc.aestronglyMeasurable
    · rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
      rcases p with ⟨x, t⟩
      rcases hp with ⟨hx, ht⟩
      have hx' : x/b ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hx.1.le hb.le, (div_le_one hb).mpr hx.2⟩
      have ht' : t/b ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg ht.1.le hb.le, (div_le_one hb).mpr ht.2⟩
      have hblock : |block m (x/b) * block m (t/b)| ≤ 1 := by
        rw [abs_mul]
        simpa using mul_le_mul (block_abs_le_one hleg m _ hx')
          (block_abs_le_one hleg m _ ht') (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc
        _ ≤ Real.exp ((x-b/2)*(t-b/2)/σ^2) := by
          simpa using mul_le_mul_of_nonneg_right hblock (Real.exp_pos _).le
        _ ≤ _ := Real.exp_le_exp.mpr
          (centered_cross_exponent_le b σ x t hb.le ⟨hx.1.le, hx.2⟩ ⟨ht.1.le, ht.2⟩)

/-- Multiplying the two compact latent integrals gives the square of the marked
convolution, with the positive Gaussian reference denominator left outside. Given [the displayed inputs and assumptions](hyp:b,σ,m,hb,w), [the stated mathematical conclusion holds](goal). -/
lemma marked_square_as_cross_integral (b σ : ℝ) (m : ℕ) (hb : 0 ≤ b) (w : ℝ) :
    (∫ p : ℝ × ℝ, block m (p.1/b) * block m (p.2/b) *
      (phi σ (w-p.1) * phi σ (w-p.2) / phi σ (w-b/2))
      ∂(volume.restrict (Ioc (0 : ℝ) b)).prod (volume.restrict (Ioc (0 : ℝ) b))) =
      markedConvolution b m σ w ^ 2 / phi σ (w-b/2) := by
  have he : (fun p : ℝ × ℝ => block m (p.1/b) * block m (p.2/b) *
      (phi σ (w-p.1) * phi σ (w-p.2) / phi σ (w-b/2))) =
      (fun p : ℝ × ℝ =>
        ((block m (p.1/b) * phi σ (w-p.1)) *
          (block m (p.2/b) * phi σ (w-p.2))) / phi σ (w-b/2)) := by
    funext p
    ring
  rw [he, integral_div, integral_prod_mul
    (fun x : ℝ => block m (x/b) * phi σ (w-x))
    (fun t : ℝ => block m (t/b) * phi σ (w-t))]
  simp only [markedConvolution, intervalIntegral.integral_of_le hb, pow_two]

/-- The Gaussian-reference square is integrable on all real proxy values;
this follows from the signed three-variable absolute-integrability bound. Given [the displayed inputs and assumptions](hyp:hleg,b,σ,m,hb,hσ), [the stated mathematical conclusion holds](goal). -/
lemma marked_square_reference_integrable (hleg : ClassicalLegendreFacts)
    (b σ : ℝ) (m : ℕ) (hb : 0 < b) (hσ : 0 < σ) :
    Integrable (fun w => markedConvolution b m σ w ^ 2 / phi σ (w-b/2)) := by
  have hi := (signed_gaussian_cross_integrable hleg b σ m hb hσ).integral_prod_right
  simp_rw [marked_square_as_cross_integral b σ m hb.le] at hi
  exact hi

/-- Signed Fubini and the exact Gaussian cross-kernel give the compact double
integral in ML.5, retaining every real proxy value. Given [the displayed inputs and assumptions](hyp:hleg,b,σ,m,hb,hσ), [the stated mathematical conclusion holds](goal). -/
lemma marked_square_reference_integral (hleg : ClassicalLegendreFacts)
    (b σ : ℝ) (m : ℕ) (hb : 0 < b) (hσ : 0 < σ) :
    (∫ w, markedConvolution b m σ w ^ 2 / phi σ (w-b/2)) =
      ∫ x in (0 : ℝ)..b, ∫ t in (0 : ℝ)..b,
        block m (x/b) * block m (t/b) *
          Real.exp ((x-b/2)*(t-b/2)/σ^2) := by
  have hi := signed_gaussian_cross_integrable hleg b σ m hb hσ
  have hswap := integral_integral_swap (f := fun (p : ℝ × ℝ) (w : ℝ) =>
    block m (p.1/b) * block m (p.2/b) *
      (phi σ (w-p.1) * phi σ (w-p.2) / phi σ (w-b/2))) hi
  simp_rw [marked_square_as_cross_integral b σ m hb.le] at hswap
  rw [← hswap]
  simp_rw [integral_const_mul, phi_product_div_integral σ _ _ (b/2) hσ]
  have hc : Continuous (fun p : ℝ × ℝ => block m (p.1/b) * block m (p.2/b) *
      Real.exp ((p.1-b/2)*(p.2-b/2)/σ^2)) := by
    unfold block legendreP
    fun_prop
  have hcompact : Integrable (fun p : ℝ × ℝ => block m (p.1/b) * block m (p.2/b) *
      Real.exp ((p.1-b/2)*(p.2-b/2)/σ^2))
      ((volume.restrict (Ioc (0 : ℝ) b)).prod (volume.restrict (Ioc (0 : ℝ) b))) := by
    rw [Measure.prod_restrict]
    exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [integral_prod _ hcompact]
  simp only [intervalIntegral.integral_of_le hb.le]

/-- Integrating ML.3 reduces the actual likelihood square to the finite
Gaussian-reference square, using the just-proved full-domain integrability. Given [the displayed inputs and assumptions](hyp:hleg,b,σ,m,hb,hσ), [the stated mathematical conclusion holds](goal). -/
lemma marked_square_integral_midpoint_comparison (hleg : ClassicalLegendreFacts)
    (b σ : ℝ) (m : ℕ) (hb : b ∈ Ioc (0 : ℝ) 1) (hσ : 0 < σ) :
    (∫ w, markedConvolution b m σ w ^ 2 / treatedConvolution σ w) ≤
      (Real.exp (b^2/(24*σ^2))/b) *
        (∫ w, markedConvolution b m σ w ^ 2 / phi σ (w-b/2)) := by
  rw [← integral_const_mul]
  exact integral_mono (markedConvolution_square_div_integrable hleg b σ m hb hσ)
    ((marked_square_reference_integrable hleg b σ m hb.1 hσ).const_mul _)
    (marked_square_midpoint_comparison b σ m hb hσ)

/-- The absolute cross exponent is uniformly controlled on the support square,
so its exponential power series has a summable constant majorant. Given [the displayed inputs and assumptions](hyp:b,σ,x,t,hb,hx,ht), [the stated mathematical conclusion holds](goal). -/
lemma centered_cross_exponent_abs_le (b σ x t : ℝ) (hb : 0 ≤ b)
    (hx : x ∈ Icc (0 : ℝ) b) (ht : t ∈ Icc (0 : ℝ) b) :
    |(x-b/2)*(t-b/2)/σ^2| ≤ likelihoodLambda b σ := by
  have hx' : |x-b/2| ≤ b/2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have ht' : |t-b/2| ≤ b/2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hh := mul_le_mul hx' ht' (abs_nonneg _) (by linarith : 0 ≤ b/2)
  rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg σ)]
  unfold likelihoodLambda
  have hp : |x-b/2| * |t-b/2| ≤ b^2/4 := by nlinarith only [hh]
  simpa only [div_div] using div_le_div_of_nonneg_right hp (sq_nonneg σ)

/-- Expanding the compact cross-kernel and integrating its summable majorant
proves the exact centered-moment series ML.5. Given [the displayed inputs and assumptions](hyp:hleg,b,σ,m,hb,hσ), [the stated mathematical conclusion holds](goal). -/
lemma marked_square_reference_moment_series (hleg : ClassicalLegendreFacts)
    (b σ : ℝ) (m : ℕ) (hb : 0 < b) (hσ : 0 < σ) :
    (∫ w, markedConvolution b m σ w ^ 2 / phi σ (w-b/2)) =
      ∑' j : ℕ, (∫ x in (0 : ℝ)..b, block m (x/b) * (x-b/2)^j)^2 /
        (σ^(2*j) * (Nat.factorial j : ℝ)) := by
  let μ := (volume.restrict (Ioc (0 : ℝ) b)).prod (volume.restrict (Ioc (0 : ℝ) b))
  let F : ℕ → ℝ × ℝ → ℝ := fun j p => block m (p.1/b) * block m (p.2/b) *
    (((p.1-b/2)*(p.2-b/2)/σ^2)^j / (Nat.factorial j : ℝ))
  have hFi (j : ℕ) : Integrable (F j) μ := by
    have hc : Continuous (F j) := by
      dsimp [F]
      unfold block legendreP
      fun_prop
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hbound (j : ℕ) : ∀ᵐ p ∂μ,
      ‖F j p‖ ≤ likelihoodLambda b σ^j / (Nat.factorial j : ℝ) := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    have hx : p.1/b ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hp.1.1.le hb.le, (div_le_one hb).mpr hp.1.2⟩
    have ht : p.2/b ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hp.2.1.le hb.le, (div_le_one hb).mpr hp.2.2⟩
    have hg : |block m (p.1/b) * block m (p.2/b)| ≤ 1 := by
      rw [abs_mul]
      simpa using mul_le_mul (block_abs_le_one hleg m _ hx)
        (block_abs_le_one hleg m _ ht) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    dsimp [F]
    rw [abs_mul, abs_div, abs_pow,
      abs_of_nonneg (show 0 ≤ (Nat.factorial j : ℝ) by positivity)]
    calc
      _ ≤ 1 * (likelihoodLambda b σ^j / (Nat.factorial j : ℝ)) := by
        apply mul_le_mul hg
          (div_le_div_of_nonneg_right
            (pow_le_pow_left₀ (abs_nonneg _) (centered_cross_exponent_abs_le b σ p.1 p.2
              hb.le ⟨hp.1.1.le, hp.1.2⟩ ⟨hp.2.1.le, hp.2.2⟩) j) (by positivity))
          (by positivity) (by norm_num)
      _ = _ := one_mul _
  have hnorm : Summable (fun j : ℕ => ∫ p, ‖F j p‖ ∂μ) := by
    apply ((Real.summable_pow_div_factorial (likelihoodLambda b σ)).mul_left
      (μ.real univ)).of_nonneg_of_le (fun j => integral_nonneg (fun p => norm_nonneg _))
    intro j
    have hh := integral_mono_ae (hFi j).norm
      (integrable_const (likelihoodLambda b σ^j / (Nat.factorial j : ℝ))) (hbound j)
    simpa only [integral_const, smul_eq_mul] using hh
  have hseries := integral_tsum_of_summable_integral_norm hFi hnorm
  have hpoint (p : ℝ × ℝ) : (∑' j : ℕ, F j p) =
      block m (p.1/b) * block m (p.2/b) *
        Real.exp ((p.1-b/2)*(p.2-b/2)/σ^2) := by
    dsimp [F]
    rw [tsum_mul_left]
    congr 1
    have hs := NormedSpace.expSeries_div_hasSum_exp ((p.1-b/2)*(p.2-b/2)/σ^2)
    simpa only [← Real.exp_eq_exp_ℝ] using hs.tsum_eq
  have hterm (j : ℕ) : (∫ p, F j p ∂μ) =
      (∫ x in (0 : ℝ)..b, block m (x/b) * (x-b/2)^j)^2 /
        (σ^(2*j) * (Nat.factorial j : ℝ)) := by
    have he : F j = (fun p : ℝ × ℝ =>
        (block m (p.1/b) * (p.1-b/2)^j) *
        (block m (p.2/b) * (p.2-b/2)^j) /
          (σ^(2*j) * (Nat.factorial j : ℝ))) := by
      funext p
      dsimp [F]
      rw [div_pow, mul_pow, ← pow_mul]
      ring
    rw [he, integral_div]
    dsimp [μ]
    rw [integral_prod_mul (fun x : ℝ => block m (x/b) * (x-b/2)^j)
      (fun t : ℝ => block m (t/b) * (t-b/2)^j)]
    simp only [intervalIntegral.integral_of_le hb.le, pow_two]
  simp_rw [hterm, hpoint] at hseries
  rw [marked_square_reference_integral hleg b σ m hb hσ]
  have hi : Integrable (fun p : ℝ × ℝ => block m (p.1/b) * block m (p.2/b) *
      Real.exp ((p.1-b/2)*(p.2-b/2)/σ^2)) μ := by
    have hc : Continuous (fun p : ℝ × ℝ => block m (p.1/b) * block m (p.2/b) *
        Real.exp ((p.1-b/2)*(p.2-b/2)/σ^2)) := by
      unfold block legendreP
      fun_prop
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [integral_prod _ hi] at hseries
  simpa only [intervalIntegral.integral_of_le hb.le] using hseries.symm

/-- ML.3--ML.6 bound the full proxy-domain likelihood square by the retained
factorial tail; no observed-law identities are assumed in this analytic step. Given [the displayed inputs and assumptions](hyp:hleg,b,σ,m,hb,hσ,hm), [the stated mathematical conclusion holds](goal). -/
lemma marked_square_factorial_tail_bound (hleg : ClassicalLegendreFacts)
    (b σ : ℝ) (m : ℕ) (hb : b ∈ Ioc (0 : ℝ) 1) (hσ : 0 < σ) (hm : 2 ≤ m) :
    (∫ w, markedConvolution b m σ w ^ 2 / treatedConvolution σ w) ≤
      (b/blockNorm m) * Real.exp (b^2/(24*σ^2)) *
        ∑' j : ℕ, if m-1 ≤ j then
          likelihoodLambda b σ^j / (Nat.factorial j : ℝ) else 0 := by
  have hmoment := (centered_block_moment_series_bound hleg b σ m hb.1 hσ hm).2
  calc
    _ ≤ (Real.exp (b^2/(24*σ^2))/b) *
        (∫ w, markedConvolution b m σ w ^ 2 / phi σ (w-b/2)) :=
      marked_square_integral_midpoint_comparison hleg b σ m hb hσ
    _ = (Real.exp (b^2/(24*σ^2))/b) *
        (∑' j : ℕ, (∫ x in (0 : ℝ)..b, block m (x/b) * (x-b/2)^j)^2 /
          (σ^(2*j) * (Nat.factorial j : ℝ))) := by
      rw [marked_square_reference_moment_series hleg b σ m hb.1 hσ]
    _ ≤ (Real.exp (b^2/(24*σ^2))/b) * ((b^2/blockNorm m) *
        ∑' j : ℕ, if m-1 ≤ j then
          likelihoodLambda b σ^j / (Nat.factorial j : ℝ) else 0) :=
      mul_le_mul_of_nonneg_left hmoment (div_nonneg (Real.exp_pos _).le hb.1.le)
    _ = _ := by
      have hbp := hb.1.ne'
      field_simp

end CausalSmith.Stat.RdTruesideNoiseFrontier

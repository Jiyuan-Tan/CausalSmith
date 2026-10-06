module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.WitnessModel
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Full-domain integrability of the marked Gaussian likelihood

The first marked-likelihood step bounds the signed perturbation by the positive
Gaussian mixture on every real proxy value. Fubini and the normalized Gaussian
mass then make the density-square ratio integrable without trimming proxy tails.
Centered-moment cancellation and Cauchy--Schwarz bound the convergent moment
series by the factorial tail used in the second likelihood inequality.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- The paper density is the centered Mathlib Gaussian density at variance σ². Given [the displayed inputs and assumptions](hyp:σ,w), [the stated mathematical conclusion holds](goal). -/
lemma phi_eq_gaussianPDFReal (σ w : ℝ) :
    phi σ w = gaussianPDFReal 0 (NNReal.mk (σ^2) (sq_nonneg σ)) w := by
  simp [phi, gaussianPDFReal, NNReal.coe_mk, div_eq_mul_inv]

/-- Given the [Gaussian scale](hyp:σ), the density is [continuous in its real argument, including at zero scale](goal). -/
@[fun_prop] lemma phi_continuous (σ : ℝ) : Continuous (phi σ) := by
  unfold phi
  fun_prop

/-- Every value of the Gaussian density is nonnegative. Given [the displayed inputs and assumptions](hyp:σ,w), [the stated mathematical conclusion holds](goal). -/
lemma phi_nonneg (σ w : ℝ) : 0 ≤ phi σ w := by
  rw [phi_eq_gaussianPDFReal]
  exact gaussianPDFReal_nonneg _ _ _

/-- Positive noise gives a strictly positive Gaussian density everywhere. Given [the displayed inputs and assumptions](hyp:σ,w,hσ), [the stated mathematical conclusion holds](goal). -/
lemma phi_pos (σ w : ℝ) (hσ : 0 < σ) : 0 < phi σ w := by
  rw [phi_eq_gaussianPDFReal]
  apply gaussianPDFReal_pos
  intro hz
  have hs := congrArg NNReal.toReal hz
  simp only [NNReal.coe_mk, NNReal.coe_zero] at hs
  exact (ne_of_gt (sq_pos_of_pos hσ)) hs

/-- Every translated Gaussian density is integrable over the whole proxy line. Given [the displayed inputs and assumptions](hyp:σ,x), [the stated mathematical conclusion holds](goal). -/
lemma phi_translate_integrable (σ x : ℝ) : Integrable (fun w => phi σ (w-x)) := by
  simp_rw [phi_eq_gaussianPDFReal, gaussianPDFReal_sub, zero_add]
  exact integrable_gaussianPDFReal _ _

/-- A translated positive-scale Gaussian density has total mass one. Given [the displayed inputs and assumptions](hyp:σ,x,hσ), [the stated mathematical conclusion holds](goal). -/
lemma phi_translate_integral (σ x : ℝ) (hσ : 0 < σ) :
    (∫ w, phi σ (w-x)) = 1 := by
  simp_rw [phi_eq_gaussianPDFReal, gaussianPDFReal_sub, zero_add]
  apply integral_gaussianPDFReal_eq_one
  intro hz
  have hs := congrArg NNReal.toReal hz
  simp only [NNReal.coe_mk, NNReal.coe_zero] at hs
  exact (ne_of_gt (sq_pos_of_pos hσ)) hs

/-- The treated Gaussian mixture is positive at every real proxy value (ML.1). Given [the displayed inputs and assumptions](hyp:σ,w,hσ), [the stated mathematical conclusion holds](goal). -/
lemma treatedConvolution_pos (σ w : ℝ) (hσ : 0 < σ) :
    0 < treatedConvolution σ w := by
  apply intervalIntegral.integral_pos (by norm_num)
  · fun_prop
  · intro x hx
    exact (phi_pos σ _ hσ).le
  · exact ⟨0, by norm_num, phi_pos σ _ hσ⟩

/-- Fubini and Gaussian normalization give full-domain mixture integrability. Given [the displayed inputs and assumptions](hyp:σ,hσ), [the stated mathematical conclusion holds](goal). -/
lemma treatedConvolution_integrable (σ : ℝ) (hσ : 0 < σ) :
    Integrable (treatedConvolution σ) := by
  have hm : AEStronglyMeasurable (fun z : ℝ × ℝ => phi σ (z.2-z.1))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
    unfold phi
    fun_prop
  have hi : Integrable (fun z : ℝ × ℝ => phi σ (z.2-z.1))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
    apply (integrable_prod_iff hm).mpr
    constructor
    · exact ae_of_all _ (fun x => phi_translate_integrable σ x)
    · simp_rw [Real.norm_eq_abs, abs_of_nonneg (phi_nonneg σ _),
        phi_translate_integral σ _ hσ]
      exact integrable_const 1
  change Integrable (fun w => ∫ x in (0 : ℝ)..1, phi σ (w-x))
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact hi.integral_prod_right

/-- The legal block bound dominates the signed mixture by the treated mixture (ML.1). Given [the displayed inputs and assumptions](hyp:hleg,b,σ,m,hb,w), [the stated mathematical conclusion holds](goal). -/
lemma markedConvolution_abs_le (hleg : ClassicalLegendreFacts) (b σ : ℝ)
    (m : ℕ) (hb : b ∈ Ioc (0 : ℝ) 1) (w : ℝ) :
    |markedConvolution b m σ w| ≤ treatedConvolution σ w := by
  have hc : Continuous (fun x : ℝ => block m (x/b) * phi σ (w-x)) := by
    unfold block legendreP
    fun_prop
  have hp : Continuous (fun x : ℝ => phi σ (w-x)) := by
    unfold phi
    fun_prop
  calc
    _ ≤ ∫ x in (0 : ℝ)..b, |block m (x/b) * phi σ (w-x)| :=
      intervalIntegral.abs_integral_le_integral_abs hb.1.le
    _ ≤ ∫ x in (0 : ℝ)..b, phi σ (w-x) := by
      apply intervalIntegral.integral_mono_on hb.1.le
        (hc.abs.intervalIntegrable 0 b) (hp.intervalIntegrable 0 b)
      intro x hx
      have hx' : x/b ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hx.1 hb.1.le, (div_le_one hb.1).mpr hx.2⟩
      rw [abs_mul, abs_of_nonneg (phi_nonneg σ _)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (block_abs_le_one hleg m (x/b) hx') (phi_nonneg σ _)
    _ ≤ treatedConvolution σ w := by
      apply intervalIntegral.integral_mono_interval (by norm_num) hb.1.le hb.2
      · exact ae_of_all _ (fun x => phi_nonneg σ _)
      · exact hp.intervalIntegrable 0 1

/-- Given the [arm width, noise scale, and polynomial degree](hyp:b,σ,m), integrating the marked kernel over the fixed latent arm [preserves strong measurability](goal). -/
@[fun_prop] lemma markedConvolution_stronglyMeasurable (b σ : ℝ) (m : ℕ) :
    StronglyMeasurable (markedConvolution b m σ) := by
  have hm : StronglyMeasurable (fun z : ℝ × ℝ => block m (z.2/b) * phi σ (z.1-z.2)) := by
    unfold block legendreP
    fun_prop
  unfold markedConvolution intervalIntegral
  exact (hm.integral_prod_right' (ν := volume.restrict (Ioc 0 b))).sub
    (hm.integral_prod_right' (ν := volume.restrict (Ioc b 0)))

/-- Given the [noise scale](hyp:σ), integrating the Gaussian kernel over the treated arm [preserves strong measurability](goal). -/
@[fun_prop] lemma treatedConvolution_stronglyMeasurable (σ : ℝ) :
    StronglyMeasurable (treatedConvolution σ) := by
  have hm : StronglyMeasurable (fun z : ℝ × ℝ => phi σ (z.1-z.2)) := by
    unfold phi
    fun_prop
  unfold treatedConvolution intervalIntegral
  exact (hm.integral_prod_right' (ν := volume.restrict (Ioc 0 1))).sub
    (hm.integral_prod_right' (ν := volume.restrict (Ioc 1 0)))

/-- The domination |u| ≤ q gives u²/q ≤ q and full-domain integrability (ML.2). Given [the displayed inputs and assumptions](hyp:hleg,b,σ,m,hb,hσ), [the stated mathematical conclusion holds](goal). -/
lemma markedConvolution_square_div_integrable (hleg : ClassicalLegendreFacts)
    (b σ : ℝ) (m : ℕ) (hb : b ∈ Ioc (0 : ℝ) 1) (hσ : 0 < σ) :
    Integrable (fun w => markedConvolution b m σ w ^ 2 / treatedConvolution σ w) := by
  apply (treatedConvolution_integrable σ hσ).mono'
  · exact ((markedConvolution_stronglyMeasurable b σ m).measurable.pow_const 2).div
      (treatedConvolution_stronglyMeasurable σ).measurable |>.aestronglyMeasurable
  · apply ae_of_all
    intro w
    have hq := treatedConvolution_pos σ w hσ
    have hu := markedConvolution_abs_le hleg b σ m hb w
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hq.le)]
    apply (div_le_iff₀ hq).mpr
    calc
      _ = |markedConvolution b m σ w|^2 := (sq_abs _).symm
      _ ≤ (treatedConvolution σ w)^2 := pow_le_pow_left₀ (abs_nonneg _) hu 2
      _ = _ := by ring
/-- Both Bernoulli cells retain at least one eighth of the unmarked density (ML.1). Given [the displayed inputs and assumptions](hyp:q,u,a,hq,hu,ha), [the stated mathematical conclusion holds](goal). -/
lemma marked_cell_denominator_lower (q u a : ℝ) (hq : 0 ≤ q)
    (hu : |u| ≤ q) (ha : |a| ≤ 1/4) :
    q/8 ≤ q/4 - a*u/2 ∧ q/8 ≤ q/4 + a*u/2 := by
  have hp : |a*u| ≤ q/4 := by
    rw [abs_mul]
    have hh := mul_le_mul ha hu (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 1/4)
    nlinarith only [hh]
  have hh := abs_le.mp hp
  constructor <;> linarith [hh.1, hh.2]

/-- Adding the two outcome cells gives the factor sixteen in ML.2. Given [the displayed inputs and assumptions](hyp:q,u,a,hq,hu,ha), [the stated mathematical conclusion holds](goal). -/
lemma marked_two_cell_square_bound (q u a : ℝ) (hq : 0 < q)
    (hu : |u| ≤ q) (ha : |a| ≤ 1/4) :
    (a*u)^2 / (q/4-a*u/2) + (a*u)^2 / (q/4+a*u/2) ≤
      16*a^2*(u^2/q) := by
  have hd := marked_cell_denominator_lower q u a hq.le hu ha
  have hb (d : ℝ) (hd : q/8 ≤ d) : (a*u)^2/d ≤ 8*a^2*(u^2/q) := by
    calc
      _ ≤ (a*u)^2/(q/8) := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hd
      _ = _ := by field_simp
  have h₁ := hb _ hd.1
  have h₂ := hb _ hd.2
  linarith

/-- The full-domain treated-cell square ratio is integrable, without proxy truncation. Given [the displayed inputs and assumptions](hyp:hleg,b,σ,a,m,hb,hσ,ha), [the stated mathematical conclusion holds](goal). -/
lemma marked_two_cell_square_integrable (hleg : ClassicalLegendreFacts)
    (b σ a : ℝ) (m : ℕ) (hb : b ∈ Ioc (0 : ℝ) 1) (hσ : 0 < σ)
    (ha : |a| ≤ 1/4) :
    Integrable (fun w =>
      (a*markedConvolution b m σ w)^2 /
        (treatedConvolution σ w/4-a*markedConvolution b m σ w/2) +
      (a*markedConvolution b m σ w)^2 /
        (treatedConvolution σ w/4+a*markedConvolution b m σ w/2)) := by
  apply ((markedConvolution_square_div_integrable hleg b σ m hb hσ).const_mul
    (16*a^2)).mono'
  · have hu := (markedConvolution_stronglyMeasurable b σ m).measurable
    have hq := (treatedConvolution_stronglyMeasurable σ).measurable
    have hn := (hu.const_mul a).pow_const 2
    exact ((hn.div ((hq.div_const 4).sub ((hu.const_mul a).div_const 2))).add
      (hn.div ((hq.div_const 4).add ((hu.const_mul a).div_const 2)))).aestronglyMeasurable
  · apply ae_of_all
    intro w
    have hq := treatedConvolution_pos σ w hσ
    have hu := markedConvolution_abs_le hleg b σ m hb w
    have hd := marked_cell_denominator_lower _ _ a hq.le hu ha
    have hn : 0 ≤ (a*markedConvolution b m σ w)^2 /
        (treatedConvolution σ w/4-a*markedConvolution b m σ w/2) +
      (a*markedConvolution b m σ w)^2 /
        (treatedConvolution σ w/4+a*markedConvolution b m σ w/2) := by
      apply add_nonneg <;> apply div_nonneg (sq_nonneg _)
      · linarith [hd.1]
      · linarith [hd.2]
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact marked_two_cell_square_bound _ _ a hq hu ha

/-- Integrating both outcome-cell contributions gives the full-domain ML.2 bound. Given [the displayed inputs and assumptions](hyp:hleg,b,σ,a,m,hb,hσ,ha), [the stated mathematical conclusion holds](goal). -/
lemma marked_two_cell_integral_bound (hleg : ClassicalLegendreFacts)
    (b σ a : ℝ) (m : ℕ) (hb : b ∈ Ioc (0 : ℝ) 1) (hσ : 0 < σ)
    (ha : |a| ≤ 1/4) :
    (∫ w, (a*markedConvolution b m σ w)^2 /
        (treatedConvolution σ w/4-a*markedConvolution b m σ w/2) +
      (a*markedConvolution b m σ w)^2 /
        (treatedConvolution σ w/4+a*markedConvolution b m σ w/2)) ≤
      16*a^2 * ∫ w, markedConvolution b m σ w^2 / treatedConvolution σ w := by
  rw [← integral_const_mul]
  apply integral_mono
    (marked_two_cell_square_integrable hleg b σ a m hb hσ ha)
    ((markedConvolution_square_div_integrable hleg b σ m hb hσ).const_mul _)
  intro w
  exact marked_two_cell_square_bound _ _ a (treatedConvolution_pos σ w hσ)
    (markedConvolution_abs_le hleg b σ m hb w) ha

/-- The paper's perturbation amplitude satisfies the cell-denominator condition. Given [the displayed inputs and assumptions](hyp:β,b,m,hβ,hb,hm), [the stated mathematical conclusion holds](goal). -/
lemma marked_likelihood_amplitude_bound (β b : ℝ) (m : ℕ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) :
    |kappa * (b/(m : ℝ)^2)^β| ≤ 1/4 := by
  have hr := cancellationResolution_mem b m hb hm
  have hp := Real.rpow_le_one hr.1.le hr.2 hβ.1.le
  have hp0 := Real.rpow_nonneg hr.1.le β
  rw [abs_of_nonneg (mul_nonneg (by norm_num [kappa]) hp0)]
  unfold kappa
  linarith

/-- ML.2 for the actual witness amplitude, retaining both binary cells and all proxy values. Given [the displayed inputs and assumptions](hyp:hleg,β,b,σ,m,hβ,hb,hm,hσ), [the stated mathematical conclusion holds](goal). -/
lemma marked_likelihood_density_integral_bound (hleg : ClassicalLegendreFacts)
    (β b σ : ℝ) (m : ℕ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hb : b ∈ Ioc (0 : ℝ) 1) (hm : 2 ≤ m) (hσ : 0 < σ) :
    let a := kappa * (b/(m : ℝ)^2)^β
    (∫ w, (a*markedConvolution b m σ w)^2 /
        (treatedConvolution σ w/4-a*markedConvolution b m σ w/2) +
      (a*markedConvolution b m σ w)^2 /
        (treatedConvolution σ w/4+a*markedConvolution b m σ w/2)) ≤
      16*kappa^2*(b/(m : ℝ)^2)^(2*β) *
        ∫ w, markedConvolution b m σ w^2 / treatedConvolution σ w := by
  have hr := cancellationResolution_mem b m hb hm
  have he : ((b/(m : ℝ)^2)^β)^2 = (b/(m : ℝ)^2)^(2*β) := by
    rw [← Real.rpow_mul_natCast hr.1.le]
    congr 1
    ring
  simpa only [mul_pow, he, mul_assoc] using
    marked_two_cell_integral_bound hleg b σ (kappa * (b/(m : ℝ)^2)^β) m hb hσ
      (marked_likelihood_amplitude_bound β b m hβ hb hm)

/-- Every polynomial of the canceled degrees is orthogonal to the legal block. Given [the displayed inputs and assumptions](hyp:hleg,m,hm,p,hp), [the stated mathematical conclusion holds](goal). -/
lemma block_polynomial_moment_zero (hleg : ClassicalLegendreFacts) (m : ℕ)
    (hm : 2 ≤ m) (p : Polynomial ℝ) (hp : p.natDegree ≤ m-2) :
    (∫ t in (0 : ℝ)..1, p.eval t * block m t) = 0 := by
  simp_rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro k hk
    have hk' : k ≤ m-2 := (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hp
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul, block_moment_zero hleg m k hm hk', mul_zero]
  · intro k hk
    apply Continuous.intervalIntegrable
    unfold block legendreP
    fun_prop

/-- Changing scale preserves the canceled monomial moments on the full support. Given [the displayed inputs and assumptions](hyp:hleg,b,m,k,hb,hm,hk), [the stated mathematical conclusion holds](goal). -/
lemma scaled_block_moment_zero (hleg : ClassicalLegendreFacts) (b : ℝ) (m k : ℕ)
    (hb : 0 < b) (hm : 2 ≤ m) (hk : k ≤ m-2) :
    (∫ x in (0 : ℝ)..b, x^k * block m (x/b)) = 0 := by
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (fun x : ℝ => x^k * block m (x/b)) b
  simp only [mul_zero, mul_one, smul_eq_mul] at hs
  rw [← hs]
  simp_rw [mul_div_cancel_left₀ _ hb.ne', mul_pow, mul_assoc]
  rw [intervalIntegral.integral_const_mul, block_moment_zero hleg m k hm hk]
  simp

/-- Centering does not change the cancellation order (ML.5). Given [the displayed inputs and assumptions](hyp:hleg,b,c,m,j,hb,hm,hj), [the stated mathematical conclusion holds](goal). -/
lemma centered_block_moment_zero (hleg : ClassicalLegendreFacts) (b c : ℝ) (m j : ℕ)
    (hb : 0 < b) (hm : 2 ≤ m) (hj : j ≤ m-2) :
    (∫ x in (0 : ℝ)..b, block m (x/b) * (x-c)^j) = 0 := by
  let p : Polynomial ℝ := (Polynomial.C b * Polynomial.X - Polynomial.C c)^j
  have hp : p.natDegree ≤ j := by
    apply Polynomial.natDegree_pow_le.trans
    have hd : (Polynomial.C b * Polynomial.X - Polynomial.C c).natDegree ≤ 1 := by
      apply (Polynomial.natDegree_sub_le _ _).trans
      simp only [Polynomial.natDegree_C]
      exact max_le ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)) (by omega)
    exact (Nat.mul_le_mul_left j hd).trans (by omega)
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (fun x : ℝ => block m (x/b) * (x-c)^j) b
  simp only [mul_zero, mul_one, smul_eq_mul] at hs
  rw [← hs]
  simp_rw [mul_div_cancel_left₀ _ hb.ne']
  have he : (fun x : ℝ => block m x * (b*x-c)^j) = fun x => p.eval x * block m x := by
    funext x
    simp only [p, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    exact mul_comm _ _
  rw [he, block_polynomial_moment_zero hleg m hm p (hp.trans hj), mul_zero]

/-- Scaling the block's squared-mass bound gives its support-width factor (ML.6). Given [the displayed inputs and assumptions](hyp:hleg,b,m,hb), [the stated mathematical conclusion holds](goal). -/
lemma scaled_block_square_integral_le (hleg : ClassicalLegendreFacts) (b : ℝ) (m : ℕ)
    (hb : 0 < b) :
    (∫ x in (0 : ℝ)..b, (block m (x/b))^2) ≤ b / blockNorm m := by
  rw [intervalIntegral.integral_comp_div (fun t : ℝ => (block m t)^2) hb.ne']
  simp only [zero_div, div_self hb.ne', smul_eq_mul]
  simpa only [div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left (block_sq_integral_le hleg m) hb.le

/-- Every centered power has the compact-support squared-mass bound used in ML.6. Given [the displayed inputs and assumptions](hyp:b,j,hb), [the stated mathematical conclusion holds](goal). -/
lemma centered_power_square_integral_le (b : ℝ) (j : ℕ) (hb : 0 < b) :
    (∫ x in (0 : ℝ)..b, ((x-b/2)^j)^2) ≤ b * (b/2)^(2*j) := by
  calc
    _ ≤ ∫ x in (0 : ℝ)..b, (b/2)^(2*j) := by
      apply intervalIntegral.integral_mono_on hb.le
        (by apply Continuous.intervalIntegrable; fun_prop) (intervalIntegrable_const)
      intro x hx
      have ha : |x-b/2| ≤ b/2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
      calc
        _ = |x-b/2|^(2*j) := by rw [pow_mul, sq_abs, ← pow_mul, Nat.mul_comm j 2, pow_mul]
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) ha _
    _ = _ := by simp [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

/-- Cauchy--Schwarz on the complete latent support, with continuous integrands. Given [the displayed inputs and assumptions](hyp:b,hb,f,g,hf,hg), [the stated mathematical conclusion holds](goal). -/
lemma support_integral_mul_sq_le (b : ℝ) (hb : 0 < b) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ x in (0 : ℝ)..b, f x * g x)^2 ≤
      (∫ x in (0 : ℝ)..b, (f x)^2) * (∫ x in (0 : ℝ)..b, (g x)^2) := by
  have hf2 : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) b)) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (hf.pow 2 |>.intervalIntegrable 0 b).1
  have hg2 : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) b)) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (hg.pow 2 |>.intervalIntegrable 0 b).1
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf2) (by simpa using hg2)
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs] at hh
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  have ha : |∫ x in Ioc (0 : ℝ) b, f x * g x| ≤
      Real.sqrt (∫ x in Ioc (0 : ℝ) b, (f x)^2) *
        Real.sqrt (∫ x in Ioc (0 : ℝ) b, (g x)^2) := by
    exact (abs_integral_le_integral_abs).trans (by simpa only [abs_mul] using hh)
  have hs := pow_le_pow_left₀ (abs_nonneg _) ha 2
  rw [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _)),
    Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _))] at hs
  simpa only [intervalIntegral.integral_of_le hb.le] using hs

/-- The centered moments obey the squared-mass estimate ML.6 at every order. Given [the displayed inputs and assumptions](hyp:hleg,b,m,j,hb), [the stated mathematical conclusion holds](goal). -/
lemma centered_block_moment_square_le (hleg : ClassicalLegendreFacts) (b : ℝ)
    (m j : ℕ) (hb : 0 < b) :
    (∫ x in (0 : ℝ)..b, block m (x/b) * (x-b/2)^j)^2 ≤
      b^2 / blockNorm m * (b/2)^(2*j) := by
  have hc : Continuous (fun x : ℝ => block m (x/b)) := by
    unfold block legendreP
    fun_prop
  have hp : Continuous (fun x : ℝ => (x-b/2)^j) := by fun_prop
  calc
    _ ≤ (∫ x in (0 : ℝ)..b, (block m (x/b))^2) *
        (∫ x in (0 : ℝ)..b, ((x-b/2)^j)^2) :=
      support_integral_mul_sq_le b hb _ _ hc hp
    _ ≤ (b / blockNorm m) * (b * (b/2)^(2*j)) := by
      apply mul_le_mul (scaled_block_square_integral_le hleg b m hb)
        (centered_power_square_integral_le b j hb)
        (intervalIntegral.integral_nonneg hb.le (fun x hx => sq_nonneg _))
        (div_nonneg hb.le (blockNorm_pos m).le)
    _ = _ := by ring

/-- Normalizing ML.6 by the Gaussian variance and factorial gives each likelihood-series term. Given [the displayed inputs and assumptions](hyp:hleg,b,σ,m,j,hb,hσ), [the stated mathematical conclusion holds](goal). -/
lemma centered_block_normalized_moment_le (hleg : ClassicalLegendreFacts) (b σ : ℝ)
    (m j : ℕ) (hb : 0 < b) (hσ : 0 < σ) :
    (∫ x in (0 : ℝ)..b, block m (x/b) * (x-b/2)^j)^2 /
        (σ^(2*j) * (Nat.factorial j : ℝ)) ≤
      (b^2 / blockNorm m) * likelihoodLambda b σ^j / (Nat.factorial j : ℝ) := by
  have he : (b/2)^(2*j) / σ^(2*j) = likelihoodLambda b σ^j := by
    rw [← div_pow, pow_mul]
    congr 1
    unfold likelihoodLambda
    field_simp
    <;> ring
  calc
    _ ≤ (b^2 / blockNorm m * (b/2)^(2*j)) /
        (σ^(2*j) * (Nat.factorial j : ℝ)) :=
      div_le_div_of_nonneg_right (centered_block_moment_square_le hleg b m j hb)
        (by positivity)
    _ = _ := by rw [div_mul_eq_div_div, mul_div_assoc, he]

/-- Cancellation and ML.6 make the exact centered-moment series convergent and
bound it by the retained factorial tail, before the Gaussian identity ML.5 is inserted. Given [the displayed inputs and assumptions](hyp:hleg,b,σ,m,hb,hσ,hm), [the stated mathematical conclusion holds](goal). -/
lemma centered_block_moment_series_bound (hleg : ClassicalLegendreFacts) (b σ : ℝ)
    (m : ℕ) (hb : 0 < b) (hσ : 0 < σ) (hm : 2 ≤ m) :
    Summable (fun j : ℕ =>
      (∫ x in (0 : ℝ)..b, block m (x/b) * (x-b/2)^j)^2 /
        (σ^(2*j) * (Nat.factorial j : ℝ))) ∧
    (∑' j : ℕ, (∫ x in (0 : ℝ)..b, block m (x/b) * (x-b/2)^j)^2 /
        (σ^(2*j) * (Nat.factorial j : ℝ))) ≤
      (b^2 / blockNorm m) * ∑' j : ℕ,
        if m-1 ≤ j then likelihoodLambda b σ^j / (Nat.factorial j : ℝ) else 0 := by
  have hlam : 0 ≤ likelihoodLambda b σ := by unfold likelihoodLambda; positivity
  have htail : Summable (fun j : ℕ =>
      if m-1 ≤ j then likelihoodLambda b σ^j / (Nat.factorial j : ℝ) else 0) := by
    apply (Real.summable_pow_div_factorial (likelihoodLambda b σ)).of_nonneg_of_le
    · intro j
      split_ifs <;> positivity
    · intro j
      split_ifs <;> first | exact le_rfl | positivity
  have hmajor := htail.mul_left (b^2 / blockNorm m)
  have hterm (j : ℕ) :
      (∫ x in (0 : ℝ)..b, block m (x/b) * (x-b/2)^j)^2 /
          (σ^(2*j) * (Nat.factorial j : ℝ)) ≤
        (b^2 / blockNorm m) *
          (if m-1 ≤ j then likelihoodLambda b σ^j / (Nat.factorial j : ℝ) else 0) := by
    split_ifs with hj
    · simpa only [mul_div_assoc] using
        centered_block_normalized_moment_le hleg b σ m j hb hσ
    · rw [centered_block_moment_zero hleg b (b/2) m j hb hm (by omega)]
      simp
  have hs := hmajor.of_nonneg_of_le (fun j => by positivity) hterm
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' j : ℕ, (b^2 / blockNorm m) *
        (if m-1 ≤ j then likelihoodLambda b σ^j / (Nat.factorial j : ℝ) else 0) :=
      hs.tsum_le_tsum hterm hmajor
    _ = _ := tsum_mul_left

/-- Averaging the tangent inequality for the exponential gives a lower bound
when the exponent has zero interval mean (the elementary Jensen step in ML.3). Given [the displayed inputs and assumptions](hyp:b,hb,r,hr,hzero), [the stated mathematical conclusion holds](goal). -/
lemma interval_exp_lower_of_integral_zero (b : ℝ) (hb : 0 ≤ b)
    (r : ℝ → ℝ) (hr : Continuous r) (hzero : (∫ x in (0 : ℝ)..b, r x) = 0) :
    b ≤ ∫ x in (0 : ℝ)..b, Real.exp (r x) := by
  have hmono := intervalIntegral.integral_mono_on hb
    ((hr.add continuous_const).intervalIntegrable (μ := volume) 0 b)
    ((show Continuous (fun x => Real.exp (r x)) by fun_prop).intervalIntegrable (μ := volume) 0 b)
    (fun x _ => Real.add_one_le_exp (r x))
  simpa only [Pi.add_apply, intervalIntegral.integral_add (hr.intervalIntegrable 0 b)
    (continuous_const.intervalIntegrable 0 b), hzero, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul, mul_one, zero_add] using hmono

/-- The centered quadratic Gaussian log-ratio has zero mean on its support (ML.3). Given [the displayed inputs and assumptions](hyp:b,σ,w), [the stated mathematical conclusion holds](goal). -/
lemma gaussian_centered_exponent_integral_zero (b σ w : ℝ) :
    (∫ x in (0 : ℝ)..b,
      (-(w-x)^2 + (w-b/2)^2 + b^2/12) / (2*σ^2)) = 0 := by
  have he : (fun x : ℝ => (-(w-x)^2 + (w-b/2)^2 + b^2/12) / (2*σ^2)) =
      (fun x : ℝ => ((2*w)*x - x^2 + (-w*b + b^2/3)) / (2*σ^2)) := by
    funext x
    ring
  rw [he, intervalIntegral.integral_div]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, integral_id,
    integral_pow, intervalIntegral.integral_const]
  · simp only [sub_zero, zero_pow (by omega : 3 ≠ 0), smul_eq_mul]
    ring
  all_goals exact (by fun_prop : Continuous _).intervalIntegrable _ _

/-- Factoring at the local midpoint exposes the mean-zero exponent of ML.3. Given [the displayed inputs and assumptions](hyp:b,σ,w,x), [the stated mathematical conclusion holds](goal). -/
lemma phi_centered_exponent_factorization (b σ w x : ℝ) :
    phi σ (w-x) =
      (Real.exp (-b^2/(24*σ^2)) * phi σ (w-b/2)) *
        Real.exp ((-(w-x)^2 + (w-b/2)^2 + b^2/12) / (2*σ^2)) := by
  unfold phi
  rw [show Real.exp (-b^2/(24*σ^2)) *
      ((Real.sqrt (2*Real.pi*σ^2))⁻¹ * Real.exp (-(w-b/2)^2/(2*σ^2))) *
        Real.exp ((-(w-x)^2 + (w-b/2)^2 + b^2/12)/(2*σ^2)) =
      (Real.sqrt (2*Real.pi*σ^2))⁻¹ *
        (Real.exp (-b^2/(24*σ^2)) * Real.exp (-(w-b/2)^2/(2*σ^2)) *
          Real.exp ((-(w-x)^2 + (w-b/2)^2 + b^2/12)/(2*σ^2))) by ring]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

/-- The local Gaussian mixture is bounded below at every real proxy value (ML.3). Given [the displayed inputs and assumptions](hyp:b,σ,w,hb), [the stated mathematical conclusion holds](goal). -/
lemma local_gaussian_mixture_lower (b σ w : ℝ) (hb : 0 ≤ b) :
    b * Real.exp (-b^2/(24*σ^2)) * phi σ (w-b/2) ≤
      ∫ x in (0 : ℝ)..b, phi σ (w-x) := by
  rw [show (fun x => phi σ (w-x)) =
      (fun x => (Real.exp (-b^2/(24*σ^2)) * phi σ (w-b/2)) *
        Real.exp ((-(w-x)^2 + (w-b/2)^2 + b^2/12)/(2*σ^2))) by
      funext x; exact phi_centered_exponent_factorization b σ w x]
  rw [intervalIntegral.integral_const_mul]
  have hc : 0 ≤ Real.exp (-b^2/(24*σ^2)) * phi σ (w-b/2) :=
    mul_nonneg (Real.exp_pos _).le (phi_nonneg _ _)
  have hi := interval_exp_lower_of_integral_zero b hb
    (fun x => (-(w-x)^2 + (w-b/2)^2 + b^2/12)/(2*σ^2))
    (by fun_prop) (gaussian_centered_exponent_integral_zero b σ w)
  simpa only [mul_assoc, mul_comm b, mul_left_comm b] using
    mul_le_mul_of_nonneg_left hi hc

/-- Restricting the unit mixture to the local support proves the global denominator
bound, including the full real proxy line (ML.3). Given [the displayed inputs and assumptions](hyp:b,σ,w,hb), [the stated mathematical conclusion holds](goal). -/
lemma treatedConvolution_centered_lower (b σ w : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    b * Real.exp (-b^2/(24*σ^2)) * phi σ (w-b/2) ≤ treatedConvolution σ w := by
  apply (local_gaussian_mixture_lower b σ w hb.1).trans
  unfold treatedConvolution
  exact intervalIntegral.integral_mono_interval le_rfl hb.1 hb.2
    (ae_of_all _ (fun x => phi_nonneg σ (w-x)))
    ((show Continuous (fun x => phi σ (w-x)) by fun_prop).intervalIntegrable 0 1)

/-- Completing the square factors the product of two Gaussian translates (ML.4). Given [the displayed inputs and assumptions](hyp:σ,w,x,t,c), [the stated mathematical conclusion holds](goal). -/
lemma phi_product_square_completion (σ w x t c : ℝ) :
    phi σ (w-x) * phi σ (w-t) =
      (Real.exp ((x-c)*(t-c)/σ^2) * phi σ (w-(x+t-c))) * phi σ (w-c) := by
  unfold phi
  calc
    _ = (Real.sqrt (2*Real.pi*σ^2))⁻¹^2 *
        Real.exp (-(w-x)^2/(2*σ^2) + -(w-t)^2/(2*σ^2)) := by
      rw [Real.exp_add]
      ring
    _ = (Real.sqrt (2*Real.pi*σ^2))⁻¹^2 *
        Real.exp (((x-c)*(t-c)/σ^2 + -(w-(x+t-c))^2/(2*σ^2)) +
          -(w-c)^2/(2*σ^2)) := by
      congr 2
      ring
    _ = _ := by
      rw [Real.exp_add, Real.exp_add]
      ring

/-- The positive reference density cancels in the square-completion identity. Given [the displayed inputs and assumptions](hyp:σ,w,x,t,c,hσ), [the stated mathematical conclusion holds](goal). -/
lemma phi_product_div_centered (σ w x t c : ℝ) (hσ : 0 < σ) :
    phi σ (w-x) * phi σ (w-t) / phi σ (w-c) =
      Real.exp ((x-c)*(t-c)/σ^2) * phi σ (w-(x+t-c)) := by
  rw [phi_product_square_completion]
  exact mul_div_cancel_right₀ _ (ne_of_gt (phi_pos σ (w-c) hσ))

/-- The square-completed ratio is integrable on the entire proxy line (ML.4). Given [the displayed inputs and assumptions](hyp:σ,x,t,c,hσ), [the stated mathematical conclusion holds](goal). -/
lemma phi_product_div_integrable (σ x t c : ℝ) (hσ : 0 < σ) :
    Integrable (fun w => phi σ (w-x) * phi σ (w-t) / phi σ (w-c)) := by
  simp_rw [phi_product_div_centered σ _ x t c hσ]
  exact (phi_translate_integrable σ (x+t-c)).const_mul _

/-- Integrating the square completion gives the exact Gaussian cross-kernel (ML.4). Given [the displayed inputs and assumptions](hyp:σ,x,t,c,hσ), [the stated mathematical conclusion holds](goal). -/
lemma phi_product_div_integral (σ x t c : ℝ) (hσ : 0 < σ) :
    (∫ w, phi σ (w-x) * phi σ (w-t) / phi σ (w-c)) =
      Real.exp ((x-c)*(t-c)/σ^2) := by
  simp_rw [phi_product_div_centered σ _ x t c hσ]
  rw [integral_const_mul, phi_translate_integral σ (x+t-c) hσ, mul_one]
end CausalSmith.Stat.RdTruesideNoiseFrontier

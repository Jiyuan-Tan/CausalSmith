module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.MixtureOverlap
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.SignProduct
/-! Assembly of complete sign-family membership and the fixed-sample chi-square certificate. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace CausalSmith.Stat.PrivateCateRoughdesign
variable (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4)
include hhL
/-- The micro radius is positive and no larger than the macro radius.  [the asserted conclusion follows](goal). -/
-- @node: deltaL_pos_le_macro
lemma deltaL_pos_le_macro : 0 < deltaL hL ∧ deltaL hL ≤ hL := by
  have hp : 0 < hL^5 := pow_pos hhL.1 5
  have h1 : hL ≤ 1 := hhL.2.trans (by norm_num)
  have h4 : hL^4 ≤ 1 := pow_le_one₀ (le_of_lt hhL.1) h1
  constructor
  · exact hp
  · dsimp [deltaL]
    calc
      hL^5 = hL * hL^4 := by ring
      _ ≤ hL * 1 := mul_le_mul_of_nonneg_left h4 (le_of_lt hhL.1)
      _ = hL := mul_one _

/-- Active centers lie in the integer interval between the two macro endpoint roundings.  [the asserted conclusion follows](goal). -/
-- @node: activeSigns_subset_endpoint_interval
lemma activeSigns_subset_endpoint_interval :
    activeSigns hL ⊆ Finset.Icc ⌊(x0-hL)/deltaL hL⌋ ⌈(x0+hL)/deltaL hL⌉ := by
  intro j hj
  have hd := (deltaL_pos_le_macro hL hhL).1
  have hm := (mem_activeSigns hL hhL j).mp hj
  have hl : (x0-hL)/deltaL hL < (j : ℝ)+1 := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith [hm.2]
  have hu : (j : ℝ)-1 < (x0+hL)/deltaL hL := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith [hm.1]
  have hf := Int.floor_le ((x0-hL)/deltaL hL)
  have hc := Int.le_ceil ((x0+hL)/deltaL hL)
  have hf' : ⌊(x0-hL)/deltaL hL⌋ < j+1 := by exact_mod_cast (hf.trans_lt hl)
  have hc' : j-1 < ⌈(x0+hL)/deltaL hL⌉ := by exact_mod_cast (hu.trans_le hc)
  rw [Finset.mem_Icc]
  omega

/-- Counting the active centers costs at most the macro interval length plus three micro cells.  [the asserted conclusion follows](goal). -/
-- @node: activeSigns_card_le_length
lemma activeSigns_card_le_length :
    ((activeSigns hL).card : ℝ) ≤ 2*hL/deltaL hL+3 := by
  have hd := (deltaL_pos_le_macro hL hhL).1
  have he : (x0-hL)/deltaL hL ≤ (x0+hL)/deltaL hL := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hd)
    linarith [hhL.1]
  have hl := Int.floor_le ((x0-hL)/deltaL hL)
  have hu := Int.le_ceil ((x0+hL)/deltaL hL)
  have hround : ⌊(x0-hL)/deltaL hL⌋ ≤ ⌈(x0+hL)/deltaL hL⌉ := by
    exact_mod_cast (hl.trans (he.trans hu))
  have hc := Finset.card_le_card (activeSigns_subset_endpoint_interval hL hhL)
  have hcount := Int.card_Icc_of_le ⌊(x0-hL)/deltaL hL⌋ ⌈(x0+hL)/deltaL hL⌉ (by omega)
  have hcR : ((activeSigns hL).card : ℝ) ≤
      (⌈(x0+hL)/deltaL hL⌉ : ℝ)+1-(⌊(x0-hL)/deltaL hL⌋ : ℝ) := by
    exact_mod_cast (show ((activeSigns hL).card : ℤ) ≤
      ⌈(x0+hL)/deltaL hL⌉+1-⌊(x0-hL)/deltaL hL⌋ by
        rw [← hcount]; exact_mod_cast hc)
  have hf := Int.lt_floor_add_one ((x0-hL)/deltaL hL)
  have hce := Int.ceil_lt_add_one ((x0+hL)/deltaL hL)
  have hdiff : (x0+hL)/deltaL hL-(x0-hL)/deltaL hL = 2*hL/deltaL hL := by ring
  linarith

/-- The number of active signs is at most five times the macro-to-micro radius ratio.  [the asserted conclusion follows](goal). -/
-- @node: activeSigns_card_le_five_ratio
lemma activeSigns_card_le_five_ratio :
    ((activeSigns hL).card : ℝ) ≤ 5*hL/deltaL hL := by
  have hd := deltaL_pos_le_macro hL hhL
  have hr : 1 ≤ hL/deltaL hL := (le_div_iff₀ hd.1).mpr (by simpa using hd.2)
  have hc := activeSigns_card_le_length hL hhL
  have he : 5*hL/deltaL hL = 5*(hL/deltaL hL) := by ring
  have he' : 2*hL/deltaL hL = 2*(hL/deltaL hL) := by ring
  rw [he]
  rw [he'] at hc
  linarith

/-- Updating one latent sign changes only its localized frame contribution.  [the theorem's stated inputs and assumptions](hyp:b,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam,j). -/
-- @node: perturbation_update_difference
lemma perturbation_update_difference (lam : SignVector hL) (j : activeSigns hL)
    (b : Bool) (x : Covariate) :
    perturbation hL lam x - perturbation hL (Function.update lam j b) x =
      envelope hL x * (2*bit (lam j)-2*bit b) * frame hL j x := by
  classical
  have hs : (∑ i : activeSigns hL,
      ((2*bit (lam i)-1)*frame hL i x -
        (2*bit (Function.update lam j b i)-1)*frame hL i x)) =
      (2*bit (lam j)-2*bit b)*frame hL j x := by
    rw [Finset.sum_eq_single j]
    · simp only [Function.update_self]
      ring
    · intro i _ hij
      simp [Function.update_of_ne hij]
    · simp
  simp only [perturbation]
  rw [← mul_sub, ← Finset.sum_sub_distrib, hs]
  ring

/-- A sign update has pointwise oscillation at most twice its envelope-weighted frame.  [the theorem's stated inputs and assumptions](hyp:b,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam,j). -/
-- @node: perturbation_update_abs_le
lemma perturbation_update_abs_le (lam : SignVector hL) (j : activeSigns hL)
    (b : Bool) (x : Covariate) :
    |perturbation hL lam x - perturbation hL (Function.update lam j b) x| ≤
      2*envelope hL x*|frame hL j x| := by
  rw [perturbation_update_difference hL hhL, abs_mul, abs_mul,
    abs_of_nonneg (envelope_range hL x).1]
  have hb : |2*bit (lam j)-2*bit b| ≤ 2 := by
    cases h : lam j <;> cases b <;> norm_num [bit, h]
  simpa only [mul_comm (envelope hL x) 2] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (envelope_range hL x).1) (abs_nonneg (frame hL j x))

/-- Outside the updated frame's support the perturbation is unchanged.  [the theorem's stated inputs and assumptions](hyp:b,x,hx,x,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam). -/
-- @node: perturbation_update_eq_off_support
lemma perturbation_update_eq_off_support (lam : SignVector hL) (j : activeSigns hL)
    (b : Bool) (x : Covariate) (hx : deltaL hL ≤ |(x : ℝ)-(j : ℤ)*deltaL hL|) :
    perturbation hL lam x = perturbation hL (Function.update lam j b) x := by
  have he := perturbation_update_difference hL hhL lam j b x
  rw [frame_zero_of_radius_le hL hhL j x hx, mul_zero] at he
  exact sub_eq_zero.mp he

/-- The roadmap's coordinate oscillation constants have the required total squared budget. [The displayed conclusion](goal) follows. -/
-- @node: sign_coordinate_squared_budget
lemma sign_coordinate_squared_budget :
    (∑ j : activeSigns hL, (16*separation hL*deltaL hL)^2) ≤
      1280*(separation hL)^2*hL*deltaL hL := by
  classical
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hd := (deltaL_pos_le_macro hL hhL).1
  have hc := activeSigns_card_le_five_ratio hL hhL
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (16*separation hL*deltaL hL))
  calc
    _ ≤ (5*hL/deltaL hL)*(16*separation hL*deltaL hL)^2 := hm
    _ = _ := by field_simp; ring

/-- The Fourier overlap integrand is unchanged outside a replaced sign's frame support.  [the theorem's stated inputs and assumptions](hyp:j,b,x,hx,x,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam,lam'). -/
-- @node: signOverlapIntegrand_update_eq_off_support
lemma signOverlapIntegrand_update_eq_off_support (lam lam' : SignVector hL)
    (j : activeSigns hL) (b : Bool) (x : Covariate)
    (hx : deltaL hL ≤ |(x : ℝ)-(j : ℤ)*deltaL hL|) :
    signOverlapIntegrand hL lam lam' x =
      signOverlapIntegrand hL (Function.update lam j b) lam' x := by
  simp only [signOverlapIntegrand, perturbation_update_eq_off_support hL hhL lam j b x hx]

/-- The centered overlap stays in a fixed bounded interval after covariate integration.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam,lam'). -/
-- @node: signOverlap_range
lemma signOverlap_range (lam lam' : SignVector hL) : signOverlap hL lam lam' ∈ Icc (-1) 15 := by
  have hi := integrable_signOverlapIntegrand hL hhL lam lam'
  constructor
  · have hm := integral_mono (integrable_const (-1 : ℝ)) hi
      (fun x => (signOverlapIntegrand_range hL hhL lam lam' x).1)
    simpa [signOverlap] using hm
  · have hm := integral_mono hi (integrable_const (15 : ℝ))
      (fun x => (signOverlapIntegrand_range hL hhL lam lam' x).2)
    simpa [signOverlap] using hm

/-- The boundedness hypothesis of the bounded-differences gate holds for each fixed second sign.  [the theorem's stated inputs and assumptions](hyp:lam,lam'), and [the asserted conclusion follows](goal). -/
-- @node: signOverlap_abs_le_fifteen
lemma signOverlap_abs_le_fifteen (lam lam' : SignVector hL) :
    |signOverlap hL lam lam'| ≤ 15 := by
  have hr := signOverlap_range hL hhL lam lam'
  exact abs_le.mpr ⟨by linarith [hr.1], hr.2⟩

/-- A coordinate replacement in the overlap is exactly the integral of its localized change.  [the theorem's stated inputs and assumptions](hyp:j,b), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam,lam'). -/
-- @node: signOverlap_update_difference_integral
lemma signOverlap_update_difference_integral (lam lam' : SignVector hL)
    (j : activeSigns hL) (b : Bool) :
    signOverlap hL lam lam' - signOverlap hL (Function.update lam j b) lam' =
      ∫ x : Covariate, (signOverlapIntegrand hL lam lam' x -
        signOverlapIntegrand hL (Function.update lam j b) lam' x) := by
  exact (integral_sub (integrable_signOverlapIntegrand hL hhL lam lam')
    (integrable_signOverlapIntegrand hL hhL (Function.update lam j b) lam')).symm

/-- Only the two neighboring lattice frames can be nonzero, including at grid boundaries. [The displayed conclusion](goal) follows. -/
-- @node: frame_nonzero_card_le_two
lemma frame_nonzero_card_le_two (x : Covariate) :
    (Finset.univ.filter (fun j : activeSigns hL => frame hL j x ≠ 0)).card ≤ 2 := by
  classical
  let q : ℤ := ⌊(x : ℝ) / deltaL hL⌋
  have hd := (deltaL_pos_le_macro hL hhL).1
  have hl : (q : ℝ) * deltaL hL ≤ x := (le_div_iff₀ hd).mp (Int.floor_le _)
  have hu : (x : ℝ) ≤ (q + 1 : ℤ) * deltaL hL := by
    have hu := (div_lt_iff₀ hd).mp (Int.lt_floor_add_one ((x : ℝ) / deltaL hL))
    simpa [q] using hu.le
  have hc := Finset.card_le_card_of_injOn (fun j : activeSigns hL => (j : ℤ))
    (s := Finset.univ.filter (fun j : activeSigns hL => frame hL j x ≠ 0))
    (t := {q, q+1}) (by
      intro j hj
      have hn := (Finset.mem_filter.mp hj).2
      by_cases hj0 : (j : ℤ) = q
      · simp [hj0]
      · by_cases hj1 : (j : ℤ) = q+1
        · simp [hj1]
        · exact (hn (frame_zero_off_neighbors hL hhL q j x hl hu hj0 hj1)).elim)
    (by intro i hi j hj hij; exact Subtype.ext hij)
  exact hc.trans (Finset.card_le_two)

/-- The two-frame Cauchy-Schwarz bound keeps every squared perturbation below twice the bump.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam,x). -/
-- @node: perturbation_square_le_two_bump
lemma perturbation_square_le_two_bump (lam : SignVector hL) (x : Covariate) :
    (perturbation hL lam x)^2 ≤ 2*bump hL x := by
  classical
  let s := Finset.univ.filter (fun j : activeSigns hL => frame hL j x ≠ 0)
  have hsum : (∑ j ∈ s, (2*bit (lam j)-1)*frame hL j x) =
      ∑ j : activeSigns hL, (2*bit (lam j)-1)*frame hL j x := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hn
    have hz : frame hL j x = 0 := by simpa [s, hj] using hn
    simp [hz]
  have hsquares : (∑ j ∈ s, (frame hL j x)^2) =
      ∑ j : activeSigns hL, (frame hL j x)^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hn
    have hz : frame hL j x = 0 := by simpa [s, hj] using hn
    simp [hz]
  have hc : (s.card : ℝ) ≤ 2 := by exact_mod_cast frame_nonzero_card_le_two hL hhL x
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun j => 2*bit (lam j)-1) (fun j => frame hL j x)
  have hbitSq (b : Bool) : (2 * bit b - 1) ^ 2 = (1 : ℝ) := by
    cases b <;> norm_num [bit]
  simp only [hbitSq, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [hsum, hsquares] at hcs
  have ht := hcs.trans (mul_le_mul_of_nonneg_right hc
    (Finset.sum_nonneg (fun j _ => sq_nonneg (frame hL j x))))
  have hw := mul_le_mul_of_nonneg_left ht (sq_nonneg (envelope hL x))
  calc
    (perturbation hL lam x)^2 = bump hL x *
        (∑ j : activeSigns hL, (2*bit (lam j)-1)*frame hL j x)^2 := by
      simp only [perturbation, bump, mul_pow]
    _ ≤ bump hL x * (2 * ∑ j : activeSigns hL, (frame hL j x)^2) := hw
    _ = 2*bump hL x := by
      rw [← mul_assoc, mul_comm (bump hL x) 2, mul_assoc,
        weighted_frame_square_partition hL hhL]

/-- The centered quadratic Fourier coefficient is bounded by the local bump.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam,x). -/
-- @node: perturbation_square_residual_abs_le_bump
lemma perturbation_square_residual_abs_le_bump (lam : SignVector hL) (x : Covariate) :
    |bump hL x-(perturbation hL lam x)^2| ≤ bump hL x := by
  have hs := perturbation_square_le_two_bump hL hhL lam x
  exact abs_le.mpr ⟨by linarith, by linarith [sq_nonneg (perturbation hL lam x)]⟩

/-- Replacing one sign changes the squared perturbation by at most twice the bump.  [the theorem's stated inputs and assumptions](hyp:b,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam,j). -/
-- @node: perturbation_update_square_abs_le
lemma perturbation_update_square_abs_le (lam : SignVector hL) (j : activeSigns hL)
    (b : Bool) (x : Covariate) :
    |(perturbation hL lam x)^2-(perturbation hL (Function.update lam j b) x)^2| ≤
      2*bump hL x := by
  have hs := perturbation_square_le_two_bump hL hhL lam x
  have hu := perturbation_square_le_two_bump hL hhL (Function.update lam j b) x
  exact abs_le.mpr ⟨by linarith [sq_nonneg (perturbation hL lam x)],
    by linarith [sq_nonneg (perturbation hL (Function.update lam j b) x)]⟩

/-- The sharp square bound gives a convenient rational sup-norm envelope.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam,x). -/
-- @node: perturbation_abs_le_three_halves
lemma perturbation_abs_le_three_halves (lam : SignVector hL) (x : Covariate) :
    |perturbation hL lam x| ≤ 3/2 := by
  have hs := perturbation_square_le_two_bump hL hhL lam x
  have hq := (bump_range hL x).2
  have ha := sq_abs (perturbation hL lam x)
  nlinarith [abs_nonneg (perturbation hL lam x)]

/-- The effect amplitude lies between zero and one for every legal macro radius.  [the asserted conclusion follows](goal). -/
-- @node: separation_unit_range
lemma separation_unit_range : separation hL ∈ Icc 0 1 := by
  norm_num [separation, kappa] at *
  constructor <;> linarith [hhL.1, hhL.2]

/-- A coordinate replacement changes the Fourier overlap integrand by at most eight amplitudes.  [the theorem's stated inputs and assumptions](hyp:lam,lam',j,b,x), and [the asserted conclusion follows](goal). -/
-- @node: signOverlapIntegrand_update_abs_le
lemma signOverlapIntegrand_update_abs_le (lam lam' : SignVector hL)
    (j : activeSigns hL) (b : Bool) (x : Covariate) :
    |signOverlapIntegrand hL lam lam' x -
      signOverlapIntegrand hL (Function.update lam j b) lam' x| ≤ 8*separation hL := by
  have ht := separation_unit_range hL hhL
  have hq := bump_range hL x
  have hcoef : 0 ≤ 1+(separation hL*bump hL x-1)^2 ∧
      1+(separation hL*bump hL x-1)^2 ≤ 2 := by
    have hp := mul_nonneg ht.1 hq.1
    have hu := mul_le_one₀ ht.2 hq.1 hq.2
    constructor
    · positivity
    · nlinarith [mul_nonneg hp (sub_nonneg.mpr hu)]
  have hframe : |frame hL j x| ≤ 1 := by
    exact (frame_abs_le hL j x).trans (by split_ifs <;> norm_num)
  have hdiff : |perturbation hL lam x-perturbation hL (Function.update lam j b) x| ≤ 2 := by
    have hd := perturbation_update_abs_le hL hhL lam j b x
    have hf := mul_le_mul (envelope_range hL x).2 hframe
      (abs_nonneg (frame hL j x)) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hfirst : |separation hL*(1+(separation hL*bump hL x-1)^2)*
      (perturbation hL lam x-perturbation hL (Function.update lam j b) x)*
      perturbation hL lam' x| ≤ 6*separation hL := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ht.1, abs_of_nonneg hcoef.1]
    calc
      _ ≤ separation hL*2*2*(3/2) := by
        have ht0 := ht.1
        gcongr <;> first
          | positivity
          | exact hcoef.2
          | exact hdiff
          | exact perturbation_abs_le_three_halves hL hhL lam' x
      _ = _ := by ring
  have hsecond : |(separation hL)^2*
      ((perturbation hL (Function.update lam j b) x)^2-(perturbation hL lam x)^2)*
      (bump hL x-(perturbation hL lam' x)^2)| ≤ 2*(separation hL)^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_sub_comm
      ((perturbation hL (Function.update lam j b) x)^2)]
    have hd := (perturbation_update_square_abs_le hL hhL lam j b x).trans
      (mul_le_mul_of_nonneg_left hq.2 (by norm_num : (0 : ℝ) ≤ 2))
    have hr := (perturbation_square_residual_abs_le_bump hL hhL lam' x).trans hq.2
    calc
      _ ≤ (separation hL)^2*2*1 := by
        gcongr
        simpa using hd
      _ = _ := by ring
  have he : signOverlapIntegrand hL lam lam' x -
      signOverlapIntegrand hL (Function.update lam j b) lam' x =
      separation hL*(1+(separation hL*bump hL x-1)^2)*
        (perturbation hL lam x-perturbation hL (Function.update lam j b) x)*
        perturbation hL lam' x +
      (separation hL)^2*
        ((perturbation hL (Function.update lam j b) x)^2-(perturbation hL lam x)^2)*
        (bump hL x-(perturbation hL lam' x)^2) := by
    dsimp [signOverlapIntegrand]
    ring
  rw [he]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ 6*separation hL+2*(separation hL)^2 := add_le_add hfirst hsecond
    _ ≤ 8*separation hL := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]

/-- Restricting a micro support to the unit interval can only decrease its length. [The displayed conclusion](goal) follows. -/
-- @node: frame_open_support_volume_le
lemma frame_open_support_volume_le (j : ℤ) :
    (volume : Measure Covariate).real
      {x | |(x : ℝ)-j*deltaL hL| < deltaL hL} ≤ 2*deltaL hL := by
  have hd := (deltaL_pos_le_macro hL hhL).1
  have hsub : Subtype.val '' {x : Covariate | |(x : ℝ)-j*deltaL hL| < deltaL hL} ⊆
      Ioo ((j : ℝ)*deltaL hL-deltaL hL) ((j : ℝ)*deltaL hL+deltaL hL) := by
    rintro y ⟨x, hx, rfl⟩
    change |(x : ℝ)-j*deltaL hL| < deltaL hL at hx
    have hx' := abs_lt.mp hx
    constructor <;> linarith
  have hm : (volume : Measure ℝ) (Subtype.val '' {x : Covariate |
      |(x : ℝ)-j*deltaL hL| < deltaL hL}) ≤
      volume (Ioo ((j : ℝ)*deltaL hL-deltaL hL) ((j : ℝ)*deltaL hL+deltaL hL)) :=
    measure_mono hsub
  rw [← unitInterval.volume_apply, Real.volume_Ioo,
    show (j : ℝ)*deltaL hL+deltaL hL-((j : ℝ)*deltaL hL-deltaL hL) =
      2*deltaL hL by ring] at hm
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  simpa only [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*deltaL hL)] using hr

/-- Integrating the localized pointwise change gives the roadmap's sixteen-amplitude coordinate bound.  [the theorem's stated inputs and assumptions](hyp:j,b), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam,lam'). -/
-- @node: signOverlap_update_abs_le
lemma signOverlap_update_abs_le (lam lam' : SignVector hL)
    (j : activeSigns hL) (b : Bool) :
    |signOverlap hL lam lam'-signOverlap hL (Function.update lam j b) lam'| ≤
      16*separation hL*deltaL hL := by
  classical
  let s : Set Covariate := {x | |(x : ℝ)-(j : ℤ)*deltaL hL| < deltaL hL}
  have hs : MeasurableSet s := by
    apply measurableSet_lt
    · fun_prop
    · fun_prop
  have hi := (integrable_signOverlapIntegrand hL hhL lam lam').sub
    (integrable_signOverlapIntegrand hL hhL (Function.update lam j b) lam')
  have hbound (x : Covariate) :
      |signOverlapIntegrand hL lam lam' x-
        signOverlapIntegrand hL (Function.update lam j b) lam' x| ≤
      s.indicator (fun _ => 8*separation hL) x := by
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      exact signOverlapIntegrand_update_abs_le hL hhL lam lam' j b x
    · rw [Set.indicator_of_notMem hx]
      have hx' : deltaL hL ≤ |(x : ℝ)-(j : ℤ)*deltaL hL| := by
        exact le_of_not_gt hx
      rw [signOverlapIntegrand_update_eq_off_support hL hhL lam lam' j b x hx']
      simp
  rw [signOverlap_update_difference_integral hL hhL]
  calc
    _ ≤ ∫ x : Covariate, |signOverlapIntegrand hL lam lam' x-
        signOverlapIntegrand hL (Function.update lam j b) lam' x| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x : Covariate, s.indicator (fun _ => 8*separation hL) x :=
      integral_mono hi.abs ((integrable_const _).indicator hs) hbound
    _ = (volume : Measure Covariate).real s * (8*separation hL) := by
      rw [integral_indicator_const _ hs, smul_eq_mul]
    _ ≤ (2*deltaL hL)*(8*separation hL) :=
      mul_le_mul_of_nonneg_right (frame_open_support_volume_le hL hhL j)
        (mul_nonneg (by norm_num) (separation_unit_range hL hhL).1)
    _ = _ := by ring

/-- For a fixed second sign vector, the centered overlap obeys the roadmap's mgf bound.  [the theorem's stated inputs and assumptions](hyp:n,lam'), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:gate). -/
-- @node: signOverlap_exp_average_le
lemma signOverlap_exp_average_le (gate : BoundedDifferencesMGF)
    (n : ℕ) (lam' : SignVector hL) :
    (∑ lam : SignVector hL, Real.exp ((n : ℝ)*signOverlap hL lam lam')) /
      (Fintype.card (SignVector hL) : ℝ) ≤
      Real.exp (160*(n : ℝ)^2*(separation hL)^2*hL*deltaL hL) := by
  classical
  have hm := finite_sign_mgf_average gate (fun lam => signOverlap hL lam lam')
    (signOverlap_sign_sum hL hhL lam')
    ⟨15, fun lam => signOverlap_abs_le_fifteen hL hhL lam lam'⟩
    (fun _ => 16*separation hL*deltaL hL)
    (fun _ => mul_nonneg
      (mul_nonneg (by norm_num) (separation_unit_range hL hhL).1)
      (deltaL_pos_le_macro hL hhL).1.le)
    (fun j lam b => signOverlap_update_abs_le hL hhL lam lam' j b)
    (n : ℝ) (Nat.cast_nonneg n)
  apply hm.trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (n : ℝ)^2 / 8 * (1280*(separation hL)^2*hL*deltaL hL) :=
      mul_le_mul_of_nonneg_left (sign_coordinate_squared_budget hL hhL) (by positivity)
    _ = _ := by ring

/-- Averaging the fixed-second-sign mgf estimate gives the joint exponential bound. [The displayed conclusion](goal) follows. -/
-- @node: signOverlap_joint_exp_average_le
lemma signOverlap_joint_exp_average_le (gate : BoundedDifferencesMGF) (n : ℕ) :
    (∑ lam : SignVector hL, ∑ lam' : SignVector hL,
      Real.exp ((n : ℝ)*signOverlap hL lam lam')) /
        (Fintype.card (SignVector hL) : ℝ)^2 ≤
      Real.exp (160*(n : ℝ)^2*(separation hL)^2*hL*deltaL hL) := by
  classical
  have hc : 0 < (Fintype.card (SignVector hL) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hb (lam' : SignVector hL) :=
    (div_le_iff₀ hc).mp (signOverlap_exp_average_le hL hhL gate n lam')
  have hs := Finset.sum_le_sum (fun lam' (_ : lam' ∈ Finset.univ) => hb lam')
  rw [Finset.sum_comm] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  apply (div_le_iff₀ (sq_pos_of_pos hc)).mpr
  calc
    _ ≤ _ := hs
    _ = _ := by ring

/-- Frame moments, model membership, the Fourier likelihood and fixed-sample chi-square
certificate are conditional on the published bounded-differences mgf gate.
The certificate records absolute continuity and square-density integrability explicitly,
so its real-valued chi-square integral represents the finite divergence used in testing.  [the theorem's stated inputs and assumptions](hyp:n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:boundedDifferences_of_gate). -/
-- @node: lem:positive-family-certificate
lemma positive_family_certificate (boundedDifferences_of_gate : BoundedDifferencesMGF)
    (n : ℕ) :
    CompleteModel fairNull ∧ theta fairNull = 0 ∧
    (∀ lam : SignVector hL, CompleteModel (cosineFamily hL hhL lam) ∧
      theta (cosineFamily hL hhL lam) = separation hL) ∧
    (∀ lam x av yv,
      conditionalLikelihood hL lam x av yv =
        1 + (2*bit av-1)*Real.sqrt (separation hL)*perturbation hL lam x +
        (2*bit yv-1)*Real.sqrt (separation hL)*(separation hL*bump hL x-1)*
          perturbation hL lam x +
        (2*bit av-1)*(2*bit yv-1)*separation hL*
          (bump hL x-(perturbation hL lam x)^2)) ∧
    oneRecordMixture hL hhL = Pobs fairNull ∧
    Causalean.Stat.chiSqDiv (signMixture hL hhL n) (dataLaw n fairNull) ≤
      Real.exp (160*(n : ℝ)^2*(separation hL)^2*hL*deltaL hL)-1 ∧
    signMixture hL hhL n ≪ dataLaw n fairNull ∧
    Integrable (fun z => (((signMixture hL hhL n).rnDeriv
      (dataLaw n fairNull) z).toReal - 1)^2) (dataLaw n fairNull) := by
  have hchi :
      Causalean.Stat.chiSqDiv (signMixture hL hhL n) (dataLaw n fairNull) ≤
        Real.exp (160*(n : ℝ)^2*(separation hL)^2*hL*deltaL hL)-1 := by
    have hmgf :
        (∑ lam : SignVector hL, ∑ lam' : SignVector hL,
          Real.exp ((n : ℝ)*signOverlap hL lam lam')) /
            (Fintype.card (SignVector hL) : ℝ)^2 ≤
          Real.exp (160*(n : ℝ)^2*(separation hL)^2*hL*deltaL hL) := by
      exact signOverlap_joint_exp_average_le hL hhL boundedDifferences_of_gate n
    have hmoment := (signMixture_chiSq_le_fourier_exp_average hL hhL n).trans hmgf
    linarith
  have halt : ∀ lam : SignVector hL, CompleteModel (cosineFamily hL hhL lam) :=
    cosineFamily_completeModel hL hhL
  exact ⟨fairNull_completeModel, fairNull_target,
    fun lam => ⟨halt lam, cosineFamily_target hL hhL lam⟩,
    conditionalLikelihood_fourier hL hhL, oneRecordMixture_eq_fairNull hL hhL, hchi,
    signMixture_absolutelyContinuous hL hhL n,
    signMixture_square_density_integrable hL hhL n⟩


end CausalSmith.Stat.PrivateCateRoughdesign

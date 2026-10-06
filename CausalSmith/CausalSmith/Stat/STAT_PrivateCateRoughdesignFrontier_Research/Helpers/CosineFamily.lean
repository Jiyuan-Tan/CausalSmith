module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.BinaryExchangeability
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.FrameGeometry
public import Causalean.Stat.EmpiricalProcess.Countable.ScalarSigns
/-! Explicit uniform-design Bernoulli causal laws, overlapping cosine signs, and the
conditional published-mgf certificate for the fixed-sample alternative mixture. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign

open Causalean.Stat.EmpiricalProcess.Countable

variable (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
-- @realizes lambda(uniform probability on the finite sign-vector space)
/-- The latent sign law is uniform on all sign vectors. -/
def signLaw : Measure (SignVector hL) :=
  ENNReal.ofReal ((2 : ℝ)^(-((activeSigns hL).card : ℤ))) •
    ∑ lam : SignVector hL, Measure.dirac lam
-- @realizes S(signed nuisance perturbation)
/-- The nuisance perturbation multiplies the signed frame sum by the macro envelope. -/
def perturbation (lam : SignVector hL) (x : Covariate) : ℝ :=
  envelope hL x * ∑ j : activeSigns hL, (2*bit (lam j)-1)*frame hL j x

/-- A finite signed sum of Borel frames times the envelope is Borel measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_perturbation
@[fun_prop] lemma measurable_perturbation (lam : SignVector hL) :
    Measurable (perturbation hL lam) := by
  unfold perturbation
  fun_prop

/-- Fair independent signs cancel the nuisance perturbation pointwise, including boundaries. [The displayed conclusion](goal) follows. -/
-- @node: perturbation_sign_sum
lemma perturbation_sign_sum (x : Covariate) :
    (∑ lam : SignVector hL, perturbation hL lam x) = 0 := by
  classical
  have hsign (b : Bool) : 2 * bit b - 1 = if b then (1 : ℝ) else -1 := by
    cases b <;> norm_num [bit]
  simp only [perturbation, ← Finset.mul_sum]
  simp_rw [hsign]
  rw [show (∑ lam : SignVector hL,
      ∑ j : activeSigns hL, (if lam j then (1 : ℝ) else -1) * frame hL j x) = 0 by
    exact signLinear_sum (fun j : activeSigns hL => frame hL j x), mul_zero]

/-- Off-diagonal frame terms cancel in the exact finite-sign second moment.
The remaining geometric sum of squared frames is kept explicit. [The displayed conclusion](goal) follows. -/
-- @node: perturbation_sign_square_sum
lemma perturbation_sign_square_sum (x : Covariate) :
    (∑ lam : SignVector hL, (perturbation hL lam x)^2) =
      (Fintype.card (SignVector hL) : ℝ) *
        (bump hL x * ∑ j : activeSigns hL, (frame hL j x)^2) := by
  classical
  have hsign (b : Bool) : 2 * bit b - 1 = if b then (1 : ℝ) else -1 := by
    cases b <;> norm_num [bit]
  simp only [perturbation, mul_pow, ← Finset.mul_sum]
  simp_rw [hsign]
  rw [show (∑ lam : SignVector hL,
      (∑ j : activeSigns hL, (if lam j then (1 : ℝ) else -1) * frame hL j x) ^ 2) =
      (Fintype.card (SignVector hL) : ℝ) *
        ∑ j : activeSigns hL, (frame hL j x) ^ 2 by
    exact signLinear_sq_sum (fun j : activeSigns hL => frame hL j x)]
  unfold bump
  ring

/-- The alternative propensity is one half plus the specified shared-sign perturbation. -/
def altE (lam : SignVector hL) (x : Covariate) : ℝ :=
  (1 + Real.sqrt (separation hL)*perturbation hL lam x)/2
/-- The alternative control mean has the negative shared-sign term and negative effect bump. -/
def altMu0 (lam : SignVector hL) (x : Covariate) : ℝ :=
  (1 - Real.sqrt (separation hL)*perturbation hL lam x - separation hL*bump hL x)/2
/-- The alternative treated mean has the negative shared-sign term and positive effect bump. -/
def altMu1 (lam : SignVector hL) (x : Covariate) : ℝ :=
  (1 - Real.sqrt (separation hL)*perturbation hL lam x + separation hL*bump hL x)/2
/-- The shared-sign propensity is measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_altE
@[fun_prop] lemma measurable_altE (lam : SignVector hL) : Measurable (altE hL lam) := by
  unfold altE
  fun_prop
/-- The shared-sign control mean is measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_altMu0
@[fun_prop] lemma measurable_altMu0 (lam : SignVector hL) : Measurable (altMu0 hL lam) := by
  unfold altMu0
  fun_prop
/-- The shared-sign treated mean is measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_altMu1
@[fun_prop] lemma measurable_altMu1 (lam : SignVector hL) : Measurable (altMu1 hL lam) := by
  unfold altMu1
  fun_prop
/-- A localized frame has absolute value at most one, and is zero outside its support.  [the theorem's stated inputs and assumptions](hyp:x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:j). -/
-- @node: frame_abs_le
lemma frame_abs_le (j : ℤ) (x : Covariate) :
    |frame hL j x| ≤ if |(x : ℝ) - j * deltaL hL| ≤ deltaL hL then 1 else 0 := by
  classical
  unfold frame
  split
  · exact Real.abs_cos_le_one _
  · simp

include hhL in
/-- At most three closed frame supports cover a covariate, including support endpoints. [The displayed conclusion](goal) follows. -/
-- @node: frame_support_card_le
lemma frame_support_card_le (x : Covariate) :
    (Finset.univ.filter (fun j : activeSigns hL =>
      |(x : ℝ) - (j : ℤ) * deltaL hL| ≤ deltaL hL)).card ≤ 3 := by
  classical
  let q : ℤ := ⌊(x : ℝ) / deltaL hL⌋
  have hd : 0 < deltaL hL := pow_pos hhL.1 5
  have hq := Int.floor_le ((x : ℝ) / deltaL hL)
  have hq' := Int.lt_floor_add_one ((x : ℝ) / deltaL hL)
  have hc := Finset.card_le_card_of_injOn (fun j : activeSigns hL => (j : ℤ))
    (s := Finset.univ.filter (fun j : activeSigns hL =>
      |(x : ℝ) - (j : ℤ) * deltaL hL| ≤ deltaL hL))
    (t := Finset.Icc (q - 1) (q + 1)) (by
      intro j hj
      have hj' := abs_le.mp (Finset.mem_filter.mp hj).2
      rw [Finset.mem_coe, Finset.mem_Icc]
      have hl : (q : ℝ) - 1 ≤ (j : ℤ) := by
        have h := (le_div_iff₀ hd).mp hq
        change (q : ℝ) * deltaL hL ≤ (x : ℝ) at h
        nlinarith [hj'.2]
      have hu : (j : ℤ) < (q : ℝ) + 2 := by
        have h := (div_lt_iff₀ hd).mp hq'
        change (x : ℝ) < ((q : ℝ) + 1) * deltaL hL at h
        nlinarith [hj'.1]
      constructor
      · exact_mod_cast hl
      · change (j : ℤ) ≤ q + 1
        have : (j : ℤ) < q + 2 := by exact_mod_cast hu
        omega) (by
      intro i hi j hj hij
      exact Subtype.ext hij)
  have hcard : (Finset.Icc (q - 1) (q + 1)).card = 3 := by
    rw [Int.card_Icc]
    omega
  exact hc.trans (by rw [hcard])

include hhL in
/-- Closed-support counting gives a uniform bound on the signed perturbation, also at boundaries.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam,x). -/
-- @node: perturbation_abs_le_three
lemma perturbation_abs_le_three (lam : SignVector hL) (x : Covariate) :
    |perturbation hL lam x| ≤ 3 := by
  classical
  have hg := envelope_range hL x
  have hs : |∑ j : activeSigns hL, (2 * bit (lam j) - 1) * frame hL j x| ≤ 3 := by
    calc
      _ ≤ ∑ j : activeSigns hL, |(2 * bit (lam j) - 1) * frame hL j x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : activeSigns hL,
          if |(x : ℝ) - (j : ℤ) * deltaL hL| ≤ deltaL hL then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        have hb : |2 * bit (lam j) - 1| = 1 := by
          cases h : lam j <;> norm_num [bit, h]
        rw [abs_mul, hb, one_mul]
        exact frame_abs_le hL j x
      _ = ((Finset.univ.filter (fun j : activeSigns hL =>
          |(x : ℝ) - (j : ℤ) * deltaL hL| ≤ deltaL hL)).card : ℝ) := by
        simp [← Finset.sum_filter]
      _ ≤ 3 := by exact_mod_cast frame_support_card_le hL hhL x
  unfold perturbation
  rw [abs_mul, abs_of_nonneg hg.1]
  calc
    _ ≤ envelope hL x * 3 := mul_le_mul_of_nonneg_left hs hg.1
    _ ≤ 3 := by nlinarith [hg.2]

include hhL in
/-- Every legal macro radius gives valid binary probabilities for every sign vector.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam). -/
-- @node: alt_parameters_range
lemma alt_parameters_range (lam : SignVector hL) :
    ∀ x, altE hL lam x ∈ Icc 0 1 ∧ altMu0 hL lam x ∈ Icc 0 1 ∧
      altMu1 hL lam x ∈ Icc 0 1 := by
  intro x
  have hq := bump_range hL x
  have hs := abs_le.mp (perturbation_abs_le_three hL hhL lam x)
  have ht : 0 ≤ separation hL ∧ separation hL ≤ 1 / 16384 := by
    unfold separation kappa
    norm_num
    constructor <;> nlinarith [hhL.1, hhL.2]
  have hroot := Real.sqrt_nonneg (separation hL)
  have hsq := Real.sq_sqrt ht.1
  have hsmall : Real.sqrt (separation hL) ≤ 1 / 128 := by nlinarith
  have hprodlo := mul_le_mul_of_nonneg_left hs.1 hroot
  have hprodhi := mul_le_mul_of_nonneg_left hs.2 hroot
  have hbumplo := mul_nonneg ht.1 hq.1
  have hbumphi := mul_le_mul_of_nonneg_left hq.2 ht.1
  dsimp [altE, altMu0, altMu1]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

include hhL in
/-- The small public amplitude keeps every sign alternative inside the required overlap
interval, uniformly over covariates and signs.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam,x). -/
-- @node: altE_overlap
lemma altE_overlap (lam : SignVector hL) (x : Covariate) :
    1 / 4 ≤ altE hL lam x ∧ altE hL lam x ≤ 3 / 4 := by
  have hs := abs_le.mp (perturbation_abs_le_three hL hhL lam x)
  have ht : 0 ≤ separation hL ∧ separation hL ≤ 1 / 16384 := by
    unfold separation kappa
    norm_num
    constructor <;> nlinarith [hhL.1, hhL.2]
  have hroot := Real.sqrt_nonneg (separation hL)
  have hsq := Real.sq_sqrt ht.1
  have hsmall : Real.sqrt (separation hL) ≤ 1 / 128 := by nlinarith
  have hlo := mul_le_mul_of_nonneg_left hs.1 hroot
  have hhi := mul_le_mul_of_nonneg_left hs.2 hroot
  dsimp [altE]
  constructor <;> nlinarith

-- @node: def:cosine-family
-- @realizes Plambda(concrete Bernoulli shared-sign causal alternative)
/-- The concrete causal alternative has the specified shared-sign propensity and arm means,
independent binary potential outcomes given the covariate, and consistency. -/
def cosineFamily (lam : SignVector hL) : CausalLaw :=
  binaryCausalLaw (altE hL lam) (altMu0 hL lam) (altMu1 hL lam)
    (measurable_altE hL lam) (measurable_altMu0 hL lam) (measurable_altMu1 hL lam)
    (alt_parameters_range hL hhL lam)
/-- The fair Bernoulli parameters are valid probabilities. [The displayed conclusion](goal) follows. -/
-- @node: fair_parameters_range
lemma fair_parameters_range : ∀ x : Covariate,
    (1/2 : ℝ) ∈ Icc 0 1 ∧ (1/2 : ℝ) ∈ Icc 0 1 ∧ (1/2 : ℝ) ∈ Icc 0 1 := by
  intro x
  norm_num
-- @realizes P0(full-support fair causal null)
/-- The full-support null uses a uniform covariate and three conditionally independent fair binary
variables, followed by consistency. -/
def fairNull : CausalLaw := binaryCausalLaw (fun _ => 1/2) (fun _ => 1/2) (fun _ => 1/2)
  measurable_const measurable_const measurable_const fair_parameters_range
-- @realizes Qn(uniform sign mixture of observed n-record product laws)
/-- The fixed-sample alternative mixture averages the observed product laws uniformly over all
sign vectors. -/
def signMixture (n : ℕ) : Measure (Dataset n) :=
  (ENNReal.ofReal ((2 : ℝ)^(-(activeSigns hL).card : ℤ))) •
    ∑ lam : SignVector hL, dataLaw n (cosineFamily hL hhL lam)
/-- The one-record mixture averages the observed marginals uniformly over all sign vectors. -/
def oneRecordMixture : Measure O :=
  (ENNReal.ofReal ((2 : ℝ)^(-(activeSigns hL).card : ℤ))) •
    ∑ lam : SignVector hL, Pobs (cosineFamily hL hhL lam)
-- @realizes U(treatment Fourier mark)
/-- The treatment Fourier mark maps the binary treatment to minus one or one. -/
def U (z : O) : ℝ := 2*bit z.2.1-1
-- @realizes likelihood(actual four-cell conditional likelihood relative to fair marks)
/-- The conditional mark likelihood is the actual Bernoulli cell mass divided by the fair cell
mass. -/
def conditionalLikelihood (lam : SignVector hL) (x : Covariate) (av yv : Bool) : ℝ :=
  4 * bernoulliMass (altE hL lam x) av *
    bernoulliMass (if av then altMu1 hL lam x else altMu0 hL lam x) yv

/-- The effect bump equals one at the target covariate.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hh). -/
-- @node: bump_at_target
lemma bump_at_target (hh : 0 ≤ hL) : bump hL x0 = 1 := by
  simp [bump, envelope, hh]

/-- The shared nuisance terms cancel exactly in the alternative contrast.  [the theorem's stated inputs and assumptions](hyp:lam,x), and [the asserted conclusion follows](goal). -/
-- @node: cosineFamily_contrast
lemma cosineFamily_contrast (lam : SignVector hL) (x : Covariate) :
    tau (cosineFamily hL hhL lam) x = separation hL * bump hL x := by
  change altMu1 hL lam x - altMu0 hL lam x = _
  dsimp [altMu1, altMu0]
  ring

/-- Every sign alternative has the prescribed point target.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam). -/
-- @node: cosineFamily_target
lemma cosineFamily_target (lam : SignVector hL) :
    theta (cosineFamily hL hhL lam) = separation hL := by
  rw [theta, cosineFamily_contrast, bump_at_target hL hhL.1.le, mul_one]

/-- The fair null has zero contrast at the target. [The displayed conclusion](goal) follows. -/
-- @node: fairNull_target
lemma fairNull_target : theta fairNull = 0 := by
  change (1 / 2 : ℝ) - 1 / 2 = 0
  ring

/-- The fair null's treatment is independent of its potential outcomes given the covariate.  [the asserted conclusion follows](goal). -/
-- @node: fairNull_exchangeability
lemma fairNull_exchangeability : Exchangeability fairNull :=
  binaryCausalLaw_exchangeability _ _ _ measurable_const measurable_const measurable_const
    fair_parameters_range

/-- Each shared-sign law has conditionally independent treatment and potential outcomes. [The displayed conclusion](goal) follows. -/
-- @node: cosineFamily_exchangeability
lemma cosineFamily_exchangeability (lam : SignVector hL) :
    Exchangeability (cosineFamily hL hhL lam) :=
  binaryCausalLaw_exchangeability _ _ _
    (measurable_altE hL lam) (measurable_altMu0 hL lam) (measurable_altMu1 hL lam)
    (alt_parameters_range hL hhL lam)

/-- The fair null satisfies all conditions of the complete causal model. [The displayed conclusion](goal) follows. -/
-- @node: fairNull_completeModel
lemma fairNull_completeModel : CompleteModel fairNull := by
  apply binaryCausalLaw_completeModel (fun _ => 1/2) (fun _ => 1/2) (fun _ => 1/2)
    measurable_const measurable_const measurable_const fair_parameters_range fairNull_exchangeability
  · intro x
    norm_num
  · intro x y
    simp only [sub_self, abs_zero]
    exact mul_nonneg (by norm_num [L]) (Real.rpow_nonneg (abs_nonneg _) _)
  · intro x y
    simp only [sub_self, abs_zero]
    exact mul_nonneg (by norm_num [L]) (Real.rpow_nonneg (abs_nonneg _) _)
  · intro x y
    simp only [sub_self, abs_zero]
    exact mul_nonneg (by norm_num [L]) (abs_nonneg _)

include hhL in
/-- Expanding the four Bernoulli cells gives the Fourier likelihood relative to fair marks.  [the theorem's stated inputs and assumptions](hyp:av,yv), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:lam,x). -/
-- @node: conditionalLikelihood_fourier
lemma conditionalLikelihood_fourier (lam : SignVector hL) (x : Covariate)
    (av yv : Bool) :
    conditionalLikelihood hL lam x av yv =
      1 + (2*bit av-1)*Real.sqrt (separation hL)*perturbation hL lam x +
      (2*bit yv-1)*Real.sqrt (separation hL)*(separation hL*bump hL x-1)*
        perturbation hL lam x +
      (2*bit av-1)*(2*bit yv-1)*separation hL*
        (bump hL x-(perturbation hL lam x)^2) := by
  have ht : 0 ≤ separation hL := by
    unfold separation kappa
    exact mul_nonneg (by norm_num) hhL.1.le
  have hs := Real.sq_sqrt ht
  cases av <;> cases yv <;>
    simp only [conditionalLikelihood, bernoulliMass, bit, Bool.false_eq_true,
      if_false, if_true, altE, altMu0, altMu1] <;>
    nlinarith [hs]

include hhL in
/-- Averaging the actual Fourier likelihood cancels both linear sign terms;
its only remaining deviation from the fair likelihood is the squared-frame defect. [The displayed conclusion](goal) follows. -/
-- @node: conditionalLikelihood_sign_sum
lemma conditionalLikelihood_sign_sum (x : Covariate) (av yv : Bool) :
    (∑ lam : SignVector hL, conditionalLikelihood hL lam x av yv) =
      (Fintype.card (SignVector hL) : ℝ) *
        (1 + (2 * bit av - 1) * (2 * bit yv - 1) * separation hL *
          (bump hL x - bump hL x * ∑ j : activeSigns hL, (frame hL j x)^2)) := by
  classical
  simp_rw [conditionalLikelihood_fourier hL hhL]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    perturbation_sign_sum, perturbation_sign_square_sum, mul_zero,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_zero]
  ring

/-- The uniform sign weight times the number of binary sign vectors is one. The result uses [the stated assumptions](hyp:hL) and establishes [the displayed conclusion](goal). -/
-- @node: sign_weight_normalization
lemma sign_weight_normalization (hL : ℝ) :
    ENNReal.ofReal ((2 : ℝ)^(-((activeSigns hL).card : ℤ))) *
      (Fintype.card (SignVector hL) : ℝ≥0∞) = 1 := by
  classical
  have hcard : Fintype.card (SignVector hL) = 2 ^ (activeSigns hL).card := by
    simp [SignVector, Fintype.card_fun]
  rw [hcard, zpow_neg, zpow_natCast, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  norm_cast
  exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)

/-- The real-valued uniform sign weight normalizes the finite number of vectors. The result uses [the stated assumptions](hyp:hL) and establishes [the displayed conclusion](goal). -/
-- @node: sign_weight_real_normalization
lemma sign_weight_real_normalization (hL : ℝ) :
    (2 : ℝ)^(-((activeSigns hL).card : ℤ)) *
      (Fintype.card (SignVector hL) : ℝ) = 1 := by
  classical
  have h := congrArg ENNReal.toReal (sign_weight_normalization hL)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) _)),
    ENNReal.toReal_natCast, ENNReal.toReal_one] using h

/-- Integrating any real function against the sign law is its finite uniform average. [The displayed conclusion](goal) follows. -/
-- @node: integral_signLaw
lemma integral_signLaw (F : SignVector hL → ℝ) :
    (∫ lam, F lam ∂signLaw hL) =
      (2 : ℝ)^(-((activeSigns hL).card : ℤ)) * ∑ lam, F lam := by
  classical
  rw [signLaw, integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_ofReal (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) _)), smul_eq_mul]
  · intro lam _
    exact integrable_dirac (by finiteness)

/-- The nuisance perturbation has expectation zero under the actual sign probability law.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: perturbation_sign_mean
lemma perturbation_sign_mean (x : Covariate) :
    (∫ lam, perturbation hL lam x ∂signLaw hL) = 0 := by
  rw [integral_signLaw, perturbation_sign_sum, mul_zero]

/-- The actual sign-law second moment leaves only the squared-frame geometric factor.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: perturbation_sign_second_moment
lemma perturbation_sign_second_moment (x : Covariate) :
    (∫ lam, (perturbation hL lam x)^2 ∂signLaw hL) =
      bump hL x * ∑ j : activeSigns hL, (frame hL j x)^2 := by
  classical
  rw [integral_signLaw, perturbation_sign_square_sum, ← mul_assoc,
    sign_weight_real_normalization, one_mul]

include hhL in
/-- Under the actual sign law, the averaged likelihood has exactly the squared-frame defect. [The displayed conclusion](goal) follows. -/
-- @node: conditionalLikelihood_sign_mean
lemma conditionalLikelihood_sign_mean (x : Covariate) (av yv : Bool) :
    (∫ lam, conditionalLikelihood hL lam x av yv ∂signLaw hL) =
      1 + (2 * bit av - 1) * (2 * bit yv - 1) * separation hL *
        (bump hL x - bump hL x * ∑ j : activeSigns hL, (frame hL j x)^2) := by
  classical
  rw [integral_signLaw, conditionalLikelihood_sign_sum hL hhL,
    ← mul_assoc, sign_weight_real_normalization, one_mul]

include hhL in
/-- The exact localized frame partition makes the sign second moment equal to the effect bump.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: perturbation_sign_second_moment_exact
lemma perturbation_sign_second_moment_exact (x : Covariate) :
    (∫ lam, (perturbation hL lam x)^2 ∂signLaw hL) = bump hL x := by
  rw [perturbation_sign_second_moment, weighted_frame_square_partition hL hhL]

include hhL in
/-- The actual conditional likelihood has sign average one at every covariate and mark.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,av,yv). -/
-- @node: conditionalLikelihood_sign_mean_one
lemma conditionalLikelihood_sign_mean_one (x : Covariate) (av yv : Bool) :
    (∫ lam, conditionalLikelihood hL lam x av yv ∂signLaw hL) = 1 := by
  rw [conditionalLikelihood_sign_mean hL hhL, weighted_frame_square_partition hL hhL]
  ring

include hhL in
/-- Summing the four-cell likelihood over all signs gives exactly the number of sign vectors. [The displayed conclusion](goal) follows. -/
-- @node: conditionalLikelihood_sign_sum_exact
lemma conditionalLikelihood_sign_sum_exact (x : Covariate) (av yv : Bool) :
    (∑ lam : SignVector hL, conditionalLikelihood hL lam x av yv) =
      (Fintype.card (SignVector hL) : ℝ) := by
  rw [conditionalLikelihood_sign_sum hL hhL, weighted_frame_square_partition hL hhL]
  ring

include hhL in
/-- The uniform average of every actual conditional Bernoulli mark mass is the fair mass. [The displayed conclusion](goal) follows. -/
-- @node: conditional_mark_mass_sign_average
lemma conditional_mark_mass_sign_average (x : Covariate) (av yv : Bool) :
    ENNReal.ofReal ((2 : ℝ)^(-((activeSigns hL).card : ℤ))) *
      ∑ lam : SignVector hL,
        ENNReal.ofReal (bernoulliMass (altE hL lam x) av *
          bernoulliMass (if av then altMu1 hL lam x else altMu0 hL lam x) yv) =
      ENNReal.ofReal (1 / 4 : ℝ) := by
  classical
  let m : SignVector hL → ℝ := fun lam => bernoulliMass (altE hL lam x) av *
    bernoulliMass (if av then altMu1 hL lam x else altMu0 hL lam x) yv
  have hm (lam : SignVector hL) : 0 ≤ m lam := by
    apply mul_nonneg (bernoulliMass_nonneg (alt_parameters_range hL hhL lam x).1 av)
    cases av
    · exact bernoulliMass_nonneg (alt_parameters_range hL hhL lam x).2.1 yv
    · exact bernoulliMass_nonneg (alt_parameters_range hL hhL lam x).2.2 yv
  have hsum : (2 : ℝ)^(-((activeSigns hL).card : ℤ)) * ∑ lam, m lam = 1 / 4 := by
    have hs := conditionalLikelihood_sign_sum_exact hL hhL x av yv
    simp only [conditionalLikelihood, mul_assoc] at hs
    change (∑ lam, 4 * (m lam)) = (Fintype.card (SignVector hL) : ℝ) at hs
    rw [← Finset.mul_sum] at hs
    have hn := sign_weight_real_normalization hL
    calc
      _ = (2 : ℝ)^(-((activeSigns hL).card : ℤ)) *
          ((Fintype.card (SignVector hL) : ℝ) / 4) := by rw [← hs]; ring
      _ = 1 / 4 := by rw [← mul_div_assoc, hn]
  change ENNReal.ofReal ((2 : ℝ)^(-((activeSigns hL).card : ℤ))) *
    ∑ lam, ENNReal.ofReal (m lam) = _
  rw [← ENNReal.ofReal_sum_of_nonneg (fun lam _ => hm lam),
    ← ENNReal.ofReal_mul (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) _)), hsum]

include hhL in
/-- Averaging the observed one-record laws gives the fair null measure exactly.  [the asserted conclusion follows](goal). -/
-- @node: oneRecordMixture_eq_fairNull
lemma oneRecordMixture_eq_fairNull : oneRecordMixture hL hhL = Pobs fairNull := by
  classical
  ext s hs
  let w := ENNReal.ofReal ((2 : ℝ)^(-((activeSigns hL).card : ℤ)))
  let f := fun (lam : SignVector hL) (x : Covariate) =>
    ∑ z : Bool × Bool,
      ENNReal.ofReal (bernoulliMass (altE hL lam x) z.1 *
        bernoulliMass (if z.1 then altMu1 hL lam x else altMu0 hL lam x) z.2) *
      s.indicator (fun _ => (1 : ℝ≥0∞)) (x, z.1, z.2)
  have hfm (lam : SignVector hL) : Measurable (f lam) := by
    apply Finset.measurable_fun_sum
    intro z hz
    apply Measurable.mul
    · cases z.1 <;> cases z.2 <;> unfold bernoulliMass <;> simp only [if_true,
        Bool.false_eq_true, if_false] <;> fun_prop
    · exact (measurable_const.indicator hs).comp (by fun_prop)
  have hobs (lam : SignVector hL) : Pobs (cosineFamily hL hhL lam) s = ∫⁻ x, f lam x :=
    binaryCausalLaw_observed_apply _ _ _ (measurable_altE hL lam)
      (measurable_altMu0 hL lam) (measurable_altMu1 hL lam)
      (alt_parameters_range hL hhL lam) s hs
  have hnull : Pobs fairNull s = ∫⁻ x : Covariate, ∑ z : Bool × Bool,
      ENNReal.ofReal (1 / 4 : ℝ) * s.indicator (fun _ => (1 : ℝ≥0∞)) (x, z.1, z.2) := by
    rw [fairNull, binaryCausalLaw_observed_apply _ _ _ measurable_const measurable_const
      measurable_const fair_parameters_range s hs]
    apply lintegral_congr
    intro x
    apply Finset.sum_congr rfl
    intro z hz
    cases z.1 <;> cases z.2 <;> norm_num [bernoulliMass]
  simp only [oneRecordMixture, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  simp_rw [hobs]
  change w * (∑ lam, ∫⁻ x, f lam x) = _
  rw [← lintegral_finsetSum _ (fun lam _ => hfm lam),
    ← lintegral_const_mul' w _ ENNReal.ofReal_ne_top, hnull]
  apply lintegral_congr
  intro x
  dsimp [f]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.sum_mul, ← mul_assoc]
  exact congrArg (fun a => a * s.indicator (fun _ => (1 : ℝ≥0∞)) (x, z.1, z.2))
    (conditional_mark_mass_sign_average hL hhL x z.1 z.2)

/-- Each observed sign alternative is dominated by eight times the fair observed null.  [the theorem's stated inputs and assumptions](hyp:lam), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: cosineFamily_observed_domination
lemma cosineFamily_observed_domination (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4)
    (lam : SignVector hL) : Pobs (cosineFamily hL hhL lam) ≤ (8 : ℝ≥0∞) • Pobs fairNull := by
  have hm : Measurable observe := by unfold observe A Y; fun_prop
  have h := Measure.map_mono (binaryLaw_fair_domination
    (altE hL lam) (altMu0 hL lam) (altMu1 hL lam)
    (measurable_altE hL lam) (measurable_altMu0 hL lam) (measurable_altMu1 hL lam)
    (alt_parameters_range hL hhL lam)) hm
  simpa only [Pobs, cosineFamily, fairNull, binaryCausalLaw, Measure.map_smul] using h

/-- The finite sign mixture is dominated by eight to the sample-size power times the null dataset law. The result uses [the stated assumptions](hyp:hL,hhL) and establishes [the displayed conclusion](goal). -/
-- @node: signMixture_domination
lemma signMixture_domination (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4) (n : ℕ) :
    signMixture hL hhL n ≤ (8 : ℝ≥0∞)^n • dataLaw n fairNull := by
  classical
  have hm : Measurable observe := by unfold observe A Y; fun_prop
  letI : IsProbabilityMeasure (Pobs fairNull) := Measure.isProbabilityMeasure_map hm.aemeasurable
  letI : IsFiniteMeasure ((8 : ℝ≥0∞) • Pobs fairNull) := ⟨by simp⟩
  have hd (lam : SignVector hL) : dataLaw n (cosineFamily hL hhL lam) ≤
      (8 : ℝ≥0∞)^n • dataLaw n fairNull := by
    exact finite_product_measure_domination n _ _ 8 (cosineFamily_observed_domination hL hhL lam)
  apply Measure.le_iff.mpr
  intro s hs
  simp only [signMixture, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  calc
    _ ≤ ENNReal.ofReal ((2 : ℝ)^(-((activeSigns hL).card : ℤ))) *
        ∑ lam : SignVector hL, ((8 : ℝ≥0∞)^n • dataLaw n fairNull) s :=
      mul_le_mul' le_rfl (Finset.sum_le_sum (fun lam _ => hd lam s))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
      rw [sign_weight_normalization, one_mul, Measure.smul_apply, smul_eq_mul]

/-- The uniform finite sign law is a probability measure.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: signLaw_probability
lemma signLaw_probability (hL : ℝ) : IsProbabilityMeasure (signLaw hL) := by
  classical
  rw [isProbabilityMeasure_iff, signLaw]
  simp only [Measure.smul_apply, Measure.finsetSum_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact sign_weight_normalization hL

/-- The sign mixture of observed product laws is a probability measure.  [the theorem's stated inputs and assumptions](hyp:hL,hhL,n), and [the asserted conclusion follows](goal). -/
-- @node: signMixture_probability
lemma signMixture_probability (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4) (n : ℕ) :
    IsProbabilityMeasure (signMixture hL hhL n) := by
  classical
  have hm : Measurable observe := by unfold observe A Y; fun_prop
  letI (P : CausalLaw) : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  letI (P : CausalLaw) : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  rw [isProbabilityMeasure_iff, signMixture]
  simp only [Measure.smul_apply, Measure.finsetSum_apply, measure_univ, smul_eq_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact sign_weight_normalization hL

/-- The dataset sign mixture is absolutely continuous with respect to the fair null experiment.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL,n). -/
-- @node: signMixture_absolutelyContinuous
lemma signMixture_absolutelyContinuous (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4) (n : ℕ) :
    signMixture hL hhL n ≪ dataLaw n fairNull :=
  Measure.absolutelyContinuous_of_le_smul (signMixture_domination hL hhL n)

/-- The squared density deviation of the sign mixture is integrable under the fair null experiment. The result uses [the stated assumptions](hyp:hL,hhL) and establishes [the displayed conclusion](goal). -/
-- @node: signMixture_square_density_integrable
lemma signMixture_square_density_integrable (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1/4) (n : ℕ) :
    Integrable (fun z => (((signMixture hL hhL n).rnDeriv
      (dataLaw n fairNull) z).toReal - 1)^2) (dataLaw n fairNull) := by
  have hm : Measurable observe := by unfold observe A Y; fun_prop
  letI : IsProbabilityMeasure (Pobs fairNull) := Measure.isProbabilityMeasure_map hm.aemeasurable
  letI : IsProbabilityMeasure (dataLaw n fairNull) := by unfold dataLaw; infer_instance
  exact square_rnDeriv_integrable_of_domination _ _ ((8 : ℝ≥0∞)^n)
    (by positivity) (by finiteness) (signMixture_domination hL hhL n)

/-- The direct treated mean is one half plus the localized effect bump. -/
def directMu1 (x : Covariate) : ℝ := 1/2 + separation hL*bump hL x
/-- The direct treated mean is measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_directMu1
@[fun_prop] lemma measurable_directMu1 : Measurable (directMu1 hL) := by
  unfold directMu1
  fun_prop
include hhL in
/-- The direct alternative has valid binary parameters at every legal macro radius. [The displayed conclusion](goal) follows. -/
-- @node: direct_parameters_range
lemma direct_parameters_range : ∀ x : Covariate,
    (1/2 : ℝ) ∈ Icc 0 1 ∧ (1/2 : ℝ) ∈ Icc 0 1 ∧ directMu1 hL x ∈ Icc 0 1 := by
  intro x
  have hq := bump_range hL x
  have ht : 0 ≤ separation hL ∧ separation hL ≤ 1 / 2 := by
    unfold separation kappa
    norm_num at *
    constructor <;> nlinarith [hhL.1, hhL.2]
  have hp := mul_nonneg ht.1 hq.1
  have hu := mul_le_mul_of_nonneg_left hq.2 ht.1
  dsimp [directMu1]
  constructor
  · norm_num
  constructor
  · norm_num
  · constructor <;> nlinarith

-- @node: def:direct-family
-- @realizes P1(direct localized Bernoulli causal alternative)
/-- The direct localized causal law has fair treatment and control potential outcome and the
specified perturbed treated potential outcome, followed by consistency. -/
def directAlternative : CausalLaw :=
  binaryCausalLaw (fun _ => 1/2) (fun _ => 1/2) (directMu1 hL)
    measurable_const measurable_const (measurable_directMu1 hL)
    (direct_parameters_range hL hhL)
end CausalSmith.Stat.PrivateCateRoughdesign

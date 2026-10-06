module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.BumpIntegrals
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.TNonFlatSanity

/-!
Actual observed-law constructors and unchanged-model membership for the lower sign families.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Parameters needed by the explicit lower experiment. -/
def LowerParameters (theta : ℝ) (k j : ℕ) : Prop :=
  theta ∈ Set.Ioc 0 (1 / 4) ∧ Dyadic k ∧ Dyadic j ∧ (k : ℝ) ^ (1 / 10 : ℝ) ≤ j

/-- Dyadic ranks are at least one. -/
-- @node: lower_dyadic_one_le
lemma lower_dyadic_one_le {k : ℕ} (hk : Dyadic k) : 1 ≤ k := by
  obtain ⟨l, rfl⟩ := hk
  exact Nat.one_le_pow _ _ (by norm_num)

/-- The public propensity amplitude is nonnegative and at most one quarter. -/
-- @node: lowerTau_mem_Icc
lemma lowerTau_mem_Icc (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j) :
    lowerTau theta k ∈ Set.Icc 0 (1 / 4) := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast lower_dyadic_one_le hp.2.1
  have hr : (k : ℝ) ^ (-1 / 10 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hk (by norm_num)
  have hn : 0 ≤ (k : ℝ) ^ (-1 / 10 : ℝ) := Real.rpow_nonneg (by positivity) _
  unfold lowerTau
  constructor
  · exact mul_nonneg hp.1.1.le hn
  · nlinarith [hp.1.2]

/-- The public outcome amplitude is nonnegative and at most one quarter. -/
-- @node: lowerGamma_mem_Icc
lemma lowerGamma_mem_Icc (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j) :
    lowerGamma theta j ∈ Set.Icc 0 (1 / 4) := by
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast lower_dyadic_one_le hp.2.2.1
  have hjp : (0 : ℝ) < j := by linarith
  constructor
  · exact div_nonneg hp.1.1.le hjp.le
  · apply (div_le_iff₀ hjp).2
    nlinarith [hp.1.2]

/-- The denominator of every lower-experiment density stays at least three quarters. -/
-- @node: lower_denominator_ge
lemma lower_denominator_ge (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : Fin k → Bool) (x : ℝ) :
    3 / 4 ≤ 1 + lowerTau theta k * signedBumps k lambda x := by
  have ht := lowerTau_mem_Icc theta k j hp
  have hf := signedBumps_abs_le_one k lambda x
  rw [abs_le] at hf
  nlinarith [ht.1, ht.2, hf.1, hf.2]

/-- The complete signed density perturbation has absolute magnitude at most one third. -/
-- @node: lower_perturbation_abs_le
lemma lower_perturbation_abs_le (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) (x y : ℝ) :
    |lowerGamma theta j * signedBumps k lambda x /
      (1 + lowerTau theta k * signedBumps k lambda x) * signedBumps j omega y| ≤ 1 / 3 := by
  have hg := lowerGamma_mem_Icc theta k j hp
  have hd := lower_denominator_ge theta k j hp lambda x
  have hdp : 0 < 1 + lowerTau theta k * signedBumps k lambda x := by linarith
  have hf := signedBumps_abs_le_one k lambda x
  have ho := signedBumps_abs_le_one j omega y
  have hn : |lowerGamma theta j * signedBumps k lambda x| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_nonneg hg.1]
    calc
      lowerGamma theta j * |signedBumps k lambda x| ≤ lowerGamma theta j * 1 :=
        mul_le_mul_of_nonneg_left hf hg.1
      _ ≤ 1 / 4 := by simpa using hg.2
  rw [abs_mul, abs_div, abs_of_pos hdp]
  have hdiv : |lowerGamma theta j * signedBumps k lambda x| /
      (1 + lowerTau theta k * signedBumps k lambda x) ≤ 1 / 3 := by
    apply (div_le_iff₀ hdp).2
    linarith
  calc
    _ ≤ (1 / 3 : ℝ) * 1 :=
      mul_le_mul hdiv ho (abs_nonneg _) (by norm_num)
    _ = 1 / 3 := by norm_num

/-- The common cosine baseline is an everywhere positive normalized density. -/
-- @node: lower_baseline_valid
lemma lower_baseline_valid :
    Measurable baselineDensity ∧ (∀ y, 9 / 10 ≤ baselineDensity y) ∧
    Integrable baselineDensity unitVolume ∧ (∫ y, baselineDensity y ∂unitVolume) = 1 := by
  have hc : Integrable (fun y : ℝ => Real.cos (2 * Real.pi * y)) unitVolume := by
    apply ContinuousOn.integrableOn_Icc
    fun_prop
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold baselineDensity
    fun_prop
  · intro y
    dsimp [baselineDensity]
    linarith [Real.neg_one_le_cos (2 * Real.pi * y)]
  · exact (integrable_const (1 : ℝ)).add (hc.div_const 10)
  · unfold baselineDensity
    rw [integral_add (integrable_const (1 : ℝ)) (hc.div_const 10), integral_div,
      example_cos_integral]
    simp

/-- The specified lower-experiment nuisance functions are normalized and measurable. -/
-- @node: lower_nuisance_valid
lemma lower_nuisance_valid (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    NuisanceValid (lowerPropensity theta k lambda) lowerNullDensity ∧
    NuisanceValid (lowerPropensity theta k lambda)
      (lowerAlternativeDensity theta k j lambda omega) := by
  have hbase := lower_baseline_valid
  have he : Measurable (lowerPropensity theta k lambda) := by
    unfold lowerPropensity
    fun_prop
  have herange : ∀ x ∈ Set.Icc 0 1, lowerPropensity theta k lambda x ∈ Set.Icc 0 1 := by
    intro x hx
    have ht := lowerTau_mem_Icc theta k j hp
    have hf := signedBumps_abs_le_one k lambda x
    rw [abs_le] at hf
    constructor <;> dsimp [lowerPropensity] <;> nlinarith [ht.1, ht.2, hf.1, hf.2]
  have hint (a : Bool) (x : ℝ) :
      Integrable (lowerAlternativeDensity theta k j lambda omega a x) unitVolume := by
    cases a
    · change Integrable (fun y => baselineDensity y + 0) unitVolume
      simpa only [add_zero] using hbase.2.2.1
    · exact hbase.2.2.1.add ((signedBumps_integrable j omega).const_mul _)
  constructor
  · refine ⟨he, ?_, herange, ?_, ?_, ?_⟩
    · intro a
      exact hbase.1.comp measurable_snd
    · intro a x y hx hy
      exact (by norm_num : (0 : ℝ) ≤ 9 / 10).trans (hbase.2.1 y)
    · intro a x hx
      exact hbase.2.2.1
    · intro a x hx
      exact hbase.2.2.2
  · refine ⟨he, ?_, herange, ?_, ?_, ?_⟩
    · intro a
      unfold lowerAlternativeDensity
      cases a <;> simp only [Bool.false_eq_true, if_false, if_true, add_zero]
      · exact hbase.1.comp measurable_snd
      · have hm : Measurable (fun z : ℝ × ℝ => baselineDensity z.2) :=
          hbase.1.comp measurable_snd
        fun_prop
    · intro a x y hx hy
      have hb := hbase.2.1 y
      have hh := lower_perturbation_abs_le theta k j hp lambda omega x y
      rw [abs_le] at hh
      cases a <;> simp only [lowerAlternativeDensity, Bool.false_eq_true, if_false, if_true]
        <;> linarith [hh.1]
    · intro a x hx
      exact hint a x
    · intro a x hx
      cases a
      · simpa [lowerAlternativeDensity] using hbase.2.2.2
      · simp only [lowerAlternativeDensity, if_true]
        rw [integral_add hbase.2.2.1 ((signedBumps_integrable j omega).const_mul _),
          integral_const_mul, signedBumps_integral_zero, hbase.2.2.2]
        ring
/-- Constructed null law, with a redundant outcome sign for a shared index space. -/
def lowerNullLaw (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) : ObsLaw :=
  ObsLaw.ofNuisance (lowerPropensity theta k lambda) lowerNullDensity
    (lower_nuisance_valid theta k j hp lambda omega).1
/-- Constructed alternative law. -/
def lowerAlternativeLaw (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) : ObsLaw :=
  ObsLaw.ofNuisance (lowerPropensity theta k lambda)
    (lowerAlternativeDensity theta k j lambda omega)
    (lower_nuisance_valid theta k j hp lambda omega).2
/-- The two reciprocal rank powers cancel, as required by the Hölder amplitudes. -/
-- @node: lower_rank_power_cancel
lemma lower_rank_power_cancel (k : ℕ) (hk : Dyadic k) :
    (k : ℝ) ^ (-1 / 10 : ℝ) * (k : ℝ) ^ (1 / 10 : ℝ) = 1 := by
  have hp : (0 : ℝ) < k := by exact_mod_cast (lower_dyadic_one_le hk)
  rw [← Real.rpow_add hp]
  norm_num

/-- Both sign experiments obey the original propensity overlap envelope. -/
-- @node: lower_propensity_overlap
lemma lower_propensity_overlap (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : Fin k → Bool) (x : ℝ) :
    lowerPropensity theta k lambda x ∈ Set.Icc (1 / 4) (3 / 4) := by
  have ht := lowerTau_mem_Icc theta k j hp
  have hf := signedBumps_abs_le_one k lambda x
  rw [abs_le] at hf
  constructor <;> dsimp [lowerPropensity] <;> nlinarith [ht.1, ht.2, hf.1, hf.2]

/-- Rank-scaled Hölder regularity cancels the propensity amplitude's inverse rank power. -/
-- @node: lower_propensity_holder
lemma lower_propensity_holder (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : Fin k → Bool) (x xp : ℝ) :
    |lowerPropensity theta k lambda x - lowerPropensity theta k lambda xp| ≤
      10 * |x - xp| ^ (1 / 10 : ℝ) := by
  have ht := lowerTau_mem_Icc theta k j hp
  have hh := signedBumps_holder k lambda x xp
  have hc := lower_rank_power_cancel k hp.2.1
  have he : lowerPropensity theta k lambda x - lowerPropensity theta k lambda xp =
      lowerTau theta k * (signedBumps k lambda x - signedBumps k lambda xp) / 2 := by
    unfold lowerPropensity; ring
  rw [he, abs_div, abs_mul, abs_of_nonneg ht.1]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ lowerTau theta k * (4 * (k : ℝ) ^ (1 / 10 : ℝ) *
        |x - xp| ^ (1 / 10 : ℝ)) / 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh ht.1) (by norm_num)
    _ = 2 * theta * |x - xp| ^ (1 / 10 : ℝ) := by
      unfold lowerTau
      calc
        _ = 2 * theta * ((k : ℝ) ^ (-1 / 10 : ℝ) * (k : ℝ) ^ (1 / 10 : ℝ)) *
            |x - xp| ^ (1 / 10 : ℝ) := by ring
        _ = _ := by rw [hc]; ring
    _ ≤ _ := by nlinarith [Real.rpow_nonneg (abs_nonneg (x - xp)) (1 / 10 : ℝ), hp.1.2]

/-- The baseline's original density envelope and Lipschitz constant hold globally. -/
-- @node: lower_baseline_envelope_lipschitz
lemma lower_baseline_envelope_lipschitz :
    (∀ y, baselineDensity y ∈ Set.Icc (9 / 10) (11 / 10)) ∧
    (∀ y yp, |baselineDensity y - baselineDensity yp| ≤ (4 / 5) * |y - yp|) := by
  constructor
  · intro y
    have h := Real.abs_cos_le_one (2 * Real.pi * y)
    rw [abs_le] at h
    constructor <;> dsimp [baselineDensity] <;> linarith [h.1, h.2]
  · intro y yp
    have he : baselineDensity y - baselineDensity yp =
        (Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * yp)) / 10 := by
      unfold baselineDensity; ring
    rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 10)]
    linarith [example_cosine_lipschitz y yp]

/-- Every null-law arm has the exact common, non-flat marginal density. -/
-- @node: lower_null_marginal_density
lemma lower_null_marginal_density (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) (a : Bool) (y : ℝ) :
    marginalDensity (lowerNullLaw theta k j hp lambda omega) a y = baselineDensity y := by
  change (∫ x, baselineDensity y ∂unitVolume) = baselineDensity y
  simp [unitVolume]

/-- All six original model conditions hold for every actual null observed law. -/
-- @node: lower_null_model
lemma lower_null_model (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    NullModel (lowerNullLaw theta k j hp lambda omega) := by
  constructor
  · refine ⟨obsLaw_uniform_design _, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact lower_propensity_overlap theta k j hp lambda x
    · intro x hx xp hxp
      exact lower_propensity_holder theta k j hp lambda x xp
    · intro a x y hx hy
      have hb := lower_baseline_envelope_lipschitz.1 y
      change baselineDensity y ∈ Set.Icc (1 / 4) 4
      constructor <;> linarith [hb.1, hb.2]
    · intro a y hy x hx xp hxp
      change |baselineDensity y - baselineDensity y| ≤ _
      rw [sub_self, abs_zero]
      positivity
    · intro a x hx y hy yp hyp
      change |baselineDensity y - baselineDensity yp| ≤ _
      have hb := lower_baseline_envelope_lipschitz.2 y yp
      nlinarith [abs_nonneg (y - yp)]
  · intro y hy
    unfold delta
    rw [lower_null_marginal_density, lower_null_marginal_density, sub_self]

/-- Rank selection controls the covariate amplitude in the alternative density. -/
-- @node: lowerGamma_rank_bound
lemma lowerGamma_rank_bound (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j) :
    lowerGamma theta j * (k : ℝ) ^ (1 / 10 : ℝ) ≤ theta := by
  have hj : (0 : ℝ) < j := by exact_mod_cast (lower_dyadic_one_le hp.2.2.1)
  unfold lowerGamma
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hj).2
  exact mul_le_mul_of_nonneg_left hp.2.2.2 hp.1.1.le

/-- The rational propensity adjustment is Lipschitz on the legal bump range. -/
-- @node: lower_adjusted_bump_difference
lemma lower_adjusted_bump_difference (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : Fin k → Bool) (x xp : ℝ) :
    |signedBumps k lambda x / (1 + lowerTau theta k * signedBumps k lambda x) -
      signedBumps k lambda xp / (1 + lowerTau theta k * signedBumps k lambda xp)| ≤
      2 * |signedBumps k lambda x - signedBumps k lambda xp| := by
  have hd := lower_denominator_ge theta k j hp lambda x
  have he := lower_denominator_ge theta k j hp lambda xp
  have hn : 0 < 1 + lowerTau theta k * signedBumps k lambda x := by linarith
  have hm : 0 < 1 + lowerTau theta k * signedBumps k lambda xp := by linarith
  have hid : signedBumps k lambda x / (1 + lowerTau theta k * signedBumps k lambda x) -
      signedBumps k lambda xp / (1 + lowerTau theta k * signedBumps k lambda xp) =
      (signedBumps k lambda x - signedBumps k lambda xp) /
        ((1 + lowerTau theta k * signedBumps k lambda x) *
          (1 + lowerTau theta k * signedBumps k lambda xp)) := by
    rw [div_sub_div _ _ hn.ne' hm.ne']
    congr 1
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hn hm)]
  apply (div_le_iff₀ (mul_pos hn hm)).2
  have hpq : (3 / 4 : ℝ) * (3 / 4) ≤
      (1 + lowerTau theta k * signedBumps k lambda x) *
        (1 + lowerTau theta k * signedBumps k lambda xp) :=
    mul_le_mul hd he (by norm_num) hn.le
  calc
    _ ≤ (2 * |signedBumps k lambda x - signedBumps k lambda xp|) *
        ((3 / 4 : ℝ) * (3 / 4)) := by
      nlinarith [abs_nonneg (signedBumps k lambda x - signedBumps k lambda xp)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hpq (by positivity)

/-- The density perturbation coefficient is bounded by four-thirds of its amplitude. -/
-- @node: lower_adjusted_bump_amplitude
lemma lower_adjusted_bump_amplitude (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : Fin k → Bool) (x : ℝ) :
    |lowerGamma theta j * signedBumps k lambda x /
      (1 + lowerTau theta k * signedBumps k lambda x)| ≤ (4 / 3) * lowerGamma theta j := by
  have hg := lowerGamma_mem_Icc theta k j hp
  have hd := lower_denominator_ge theta k j hp lambda x
  have hdp : 0 < 1 + lowerTau theta k * signedBumps k lambda x := by linarith
  rw [abs_div, abs_mul, abs_of_nonneg hg.1, abs_of_pos hdp]
  apply (div_le_iff₀ hdp).2
  have hb := mul_le_mul_of_nonneg_left (signedBumps_abs_le_one k lambda x) hg.1
  have hc := mul_le_mul_of_nonneg_left hd hg.1
  nlinarith

/-- Every actual alternative observed law satisfies the unchanged six-atom model. -/
-- @node: lower_alternative_model
lemma lower_alternative_model (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    Model (lowerAlternativeLaw theta k j hp lambda omega) := by
  have hg := lowerGamma_mem_Icc theta k j hp
  refine ⟨obsLaw_uniform_design _, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact lower_propensity_overlap theta k j hp lambda x
  · intro x hx xp hxp
    exact lower_propensity_holder theta k j hp lambda x xp
  · intro a x y hx hy
    have hb := lower_baseline_envelope_lipschitz.1 y
    have hh := lower_perturbation_abs_le theta k j hp lambda omega x y
    rw [abs_le] at hh
    change lowerAlternativeDensity theta k j lambda omega a x y ∈ _
    cases a <;> constructor <;> dsimp [lowerAlternativeDensity]
      <;> linarith [hb.1, hb.2, hh.1, hh.2]
  · intro a y hy x hx xp hxp
    change |lowerAlternativeDensity theta k j lambda omega a x y -
      lowerAlternativeDensity theta k j lambda omega a xp y| ≤ _
    cases a
    · simp only [lowerAlternativeDensity, Bool.false_eq_true, if_false, add_zero,
        sub_self, abs_zero]
      positivity
    · have he : lowerAlternativeDensity theta k j lambda omega true x y -
          lowerAlternativeDensity theta k j lambda omega true xp y =
          lowerGamma theta j * (signedBumps k lambda x /
            (1 + lowerTau theta k * signedBumps k lambda x) - signedBumps k lambda xp /
            (1 + lowerTau theta k * signedBumps k lambda xp)) * signedBumps j omega y := by
        unfold lowerAlternativeDensity; simp only [if_true]; ring
      rw [he, abs_mul, abs_mul, abs_of_nonneg hg.1]
      calc
        _ ≤ lowerGamma theta j *
            (2 * |signedBumps k lambda x - signedBumps k lambda xp|) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left
            (lower_adjusted_bump_difference theta k j hp lambda x xp) hg.1)
            (signedBumps_abs_le_one j omega y) (abs_nonneg _) (mul_nonneg hg.1 (by positivity))
        _ ≤ lowerGamma theta j *
            (2 * (4 * (k : ℝ) ^ (1 / 10 : ℝ) * |x - xp| ^ (1 / 10 : ℝ))) := by
          simp only [mul_one]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (signedBumps_holder k lambda x xp) (by norm_num)) hg.1
        _ = 8 * (lowerGamma theta j * (k : ℝ) ^ (1 / 10 : ℝ)) *
            |x - xp| ^ (1 / 10 : ℝ) := by ring
        _ ≤ 8 * theta * |x - xp| ^ (1 / 10 : ℝ) := by
          gcongr
          exact lowerGamma_rank_bound theta k j hp
        _ ≤ _ := by nlinarith [hp.1.2, Real.rpow_nonneg (abs_nonneg (x - xp)) (1 / 10 : ℝ)]
  · intro a x hx y hy yp hyp
    change |lowerAlternativeDensity theta k j lambda omega a x y -
      lowerAlternativeDensity theta k j lambda omega a x yp| ≤ _
    cases a
    · simpa only [lowerAlternativeDensity, Bool.false_eq_true, if_false, add_zero] using
        (lower_baseline_envelope_lipschitz.2 y yp).trans (by nlinarith [abs_nonneg (y - yp)])
    · have he : lowerAlternativeDensity theta k j lambda omega true x y -
          lowerAlternativeDensity theta k j lambda omega true x yp =
          baselineDensity y - baselineDensity yp +
          (lowerGamma theta j * signedBumps k lambda x /
            (1 + lowerTau theta k * signedBumps k lambda x)) *
              (signedBumps j omega y - signedBumps j omega yp) := by
        unfold lowerAlternativeDensity; simp only [if_true]; ring
      rw [he]
      calc
        _ ≤ |baselineDensity y - baselineDensity yp| +
            |(lowerGamma theta j * signedBumps k lambda x /
              (1 + lowerTau theta k * signedBumps k lambda x)) *
                (signedBumps j omega y - signedBumps j omega yp)| := abs_add_le _ _
        _ ≤ (4 / 5) * |y - yp| +
            ((4 / 3) * lowerGamma theta j) * (4 * j * |y - yp|) := by
          rw [abs_mul]
          exact add_le_add (lower_baseline_envelope_lipschitz.2 y yp)
            (mul_le_mul (lower_adjusted_bump_amplitude theta k j hp lambda x)
              (signedBumps_lipschitz j omega y yp) (abs_nonneg _)
              (mul_nonneg (by norm_num) hg.1))
        _ = ((4 / 5) + (16 / 3) * theta) * |y - yp| := by
          have hj : (j : ℝ) ≠ 0 := by
            have : 0 < j := lower_dyadic_one_le hp.2.2.1
            exact_mod_cast this.ne'
          unfold lowerGamma
          field_simp
          ring
        _ ≤ _ := by nlinarith [hp.1.2, abs_nonneg (y - yp)]

/-- Antisymmetry identifies the alternative's marginal contrast for every sign vector. -/
-- @node: lower_alternative_delta
lemma lower_alternative_delta (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) (y : ℝ) :
    delta (lowerAlternativeLaw theta k j hp lambda omega) y =
      -lowerTau theta k * lowerGamma theta j * lowerCphi (lowerTau theta k) *
        signedBumps j omega y := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have ht := lowerTau_mem_Icc theta k j hp
  have hk : 0 < k := lower_dyadic_one_le hp.2.1
  have hi := signedBumps_ratio_integrable (lowerTau theta k) ht k lambda
  have he : (fun x => lowerAlternativeDensity theta k j lambda omega true x y) =
      fun x => baselineDensity y + (lowerGamma theta j * signedBumps j omega y) *
        (signedBumps k lambda x / (1 + lowerTau theta k * signedBumps k lambda x)) := by
    funext x
    simp only [lowerAlternativeDensity, if_true]
    ring
  unfold delta marginalDensity
  change (∫ x, lowerAlternativeDensity theta k j lambda omega true x y ∂unitVolume) -
    (∫ x, lowerAlternativeDensity theta k j lambda omega false x y ∂unitVolume) = _
  rw [he, integral_add (integrable_const _) (hi.const_mul _), integral_const_mul,
    signedBumps_ratio_integral (lowerTau theta k) ht k hk lambda]
  simp only [lowerAlternativeDensity, Bool.false_eq_true, if_false, add_zero,
    integral_const]
  ring

/-- The squared marginal contrast has the exact positive separation in the lower experiment. -/
-- @node: lower_alternative_energy
lemma lower_alternative_energy (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    Psi (lowerAlternativeLaw theta k j hp lambda omega) = lowerSeparation theta k j := by
  unfold Psi l2Squared
  simp_rw [lower_alternative_delta, mul_pow]
  rw [integral_const_mul, signedBumps_squared_integral j
    (lower_dyadic_one_le hp.2.2.1) omega]
  unfold lowerSeparation
  ring

/-- All support laws satisfy the six original atoms, and have their exact stated marginals. -/
-- @node: lower_membership
lemma lower_membership (theta : ℝ) (k j : ℕ) (hp : LowerParameters theta k j)
    (lambda : Fin k → Bool) (omega : Fin j → Bool) :
    NullModel (lowerNullLaw theta k j hp lambda omega) ∧
    (∀ a y, y ∈ Set.Icc 0 1 →
      marginalDensity (lowerNullLaw theta k j hp lambda omega) a y = baselineDensity y) ∧
    Model (lowerAlternativeLaw theta k j hp lambda omega) ∧
    Psi (lowerAlternativeLaw theta k j hp lambda omega) = lowerSeparation theta k j := by
  refine ⟨lower_null_model theta k j hp lambda omega, ?_,
    lower_alternative_model theta k j hp lambda omega, ?_⟩
  · exact fun a y _ => lower_null_marginal_density theta k j hp lambda omega a y
  · exact lower_alternative_energy theta k j hp lambda omega

end CausalSmith.Stat.DensityEffectRoughNull

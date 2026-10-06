module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawMembership

/-!
# A coupling range bound for bounded outcomes

This file isolates the analytic cell inequality used by the all-label
ambiguity calculation.  If the first marginal is supported on `[0,1]`, the
difference between product expectations under any two couplings is controlled
by the absolute deviation of the second marginal about every fixed center.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

open Causalean.Stat

/-- [This definition](goal) introduces the corresponding mathematical object. -/
def fairBernoulliLaw : Measure ℝ :=
  (1 / 2 : ENNReal) •
    (Measure.dirac 0 + Measure.dirac 1)
/-- [This definition](goal) introduces the corresponding mathematical object. -/
instance fairBernoulliLaw_isProbabilityMeasure :
    IsProbabilityMeasure fairBernoulliLaw := by
  refine ⟨?_⟩
  simp [fairBernoulliLaw, smul_eq_mul]
  exact ENNReal.inv_two_add_inv_two

private lemma fairBernoulliLaw_cdf_of_lt_zero (x : ℝ) (hx : x < 0) :
    cdf fairBernoulliLaw x = 0 := by
  rw [cdf_eq_real]
  have hx0 : ¬0 ≤ x := not_le.mpr hx
  have hx1 : ¬1 ≤ x := not_le.mpr (lt_trans hx (by norm_num))
  simp [fairBernoulliLaw, Measure.real, hx0, hx1]

private lemma fairBernoulliLaw_cdf_between (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    cdf fairBernoulliLaw x = 1 / 2 := by
  rw [cdf_eq_real]
  simp [fairBernoulliLaw, Measure.real, hx0, not_le.mpr hx1]

private lemma fairBernoulliLaw_cdf_one :
    cdf fairBernoulliLaw 1 = 1 := by
  rw [cdf_eq_real]
  simp [fairBernoulliLaw, Measure.real, ENNReal.inv_two_add_inv_two]

/-- Given [the stated mathematical inputs and assumptions](hyp:u,hu0,hu1), this result [establishes the stated mathematical conclusion](goal). -/
lemma fairBernoulliLaw_quantile (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    quantile fairBernoulliLaw u = if u ≤ 1 / 2 then 0 else 1 := by
  split_ifs with hu
  · apply le_antisymm
    · apply quantile_le_of_le_cdf hu0
      rw [fairBernoulliLaw_cdf_between 0 (le_refl 0) (by norm_num)]
      exact hu
    · by_contra hn
      have hneg : quantile fairBernoulliLaw u < 0 := lt_of_not_ge hn
      have hle := (quantile_le_iff hu0 hu1).mp
        (le_refl (quantile fairBernoulliLaw u))
      rw [fairBernoulliLaw_cdf_of_lt_zero _ hneg] at hle
      linarith
  · apply le_antisymm
    · apply quantile_le_of_le_cdf hu0
      rw [fairBernoulliLaw_cdf_one]
      exact hu1.le
    · by_contra hn
      have hlt : quantile fairBernoulliLaw u < 1 := lt_of_not_ge hn
      let x := (quantile fairBernoulliLaw u + 1) / 2
      have hqx : quantile fairBernoulliLaw u ≤ x := by
        dsimp [x]
        linarith
      have hx0 : 0 ≤ x := by
        have hq0 : 0 ≤ quantile fairBernoulliLaw u := by
          by_contra hn0
          have hqneg : quantile fairBernoulliLaw u < 0 := lt_of_not_ge hn0
          have hle := (quantile_le_iff hu0 hu1).mp
            (le_refl (quantile fairBernoulliLaw u))
          rw [fairBernoulliLaw_cdf_of_lt_zero _ hqneg] at hle
          linarith
        dsimp [x]
        linarith
      have hx1 : x < 1 := by dsimp [x]; linarith
      have hle := (quantile_le_iff hu0 hu1).mp hqx
      rw [fairBernoulliLaw_cdf_between x hx0 hx1] at hle
      exact hu hle

/-- Given [the stated mathematical inputs and assumptions](hyp:Y,W,πminus,πplus,hminus,hplus,hYsupport,hY2,hW2,c), this result [establishes the stated mathematical conclusion](goal). -/
lemma coupling_product_gap_le_absoluteDeviation
    {Y W : Measure ℝ} [IsProbabilityMeasure Y] [IsProbabilityMeasure W]
    {πminus πplus : Measure (ℝ × ℝ)}
    (hminus : IsCoupling πminus Y W) (hplus : IsCoupling πplus Y W)
    (hYsupport : Y (Icc (0 : ℝ) 1)ᶜ = 0)
    (hY2 : MemLp (fun y : ℝ => y) 2 Y)
    (hW2 : MemLp (fun w : ℝ => w) 2 W) (c : ℝ) :
    (∫ p, p.1 * p.2 ∂πplus) - (∫ p, p.1 * p.2 ∂πminus)
      ≤ ∫ w, |w - c| ∂W := by
  letI : IsProbabilityMeasure πminus := hminus.isProbabilityMeasure
  letI : IsProbabilityMeasure πplus := hplus.isProbabilityMeasure
  let pos : ℝ → ℝ := fun x => (x + |x|) / 2
  let neg : ℝ → ℝ := fun x => (-x + |x|) / 2
  have hYae (π : Measure (ℝ × ℝ)) (hπ : IsCoupling π Y W) :
      ∀ᵐ p ∂π, p.1 ∈ Icc (0 : ℝ) 1 := by
    have hh : ∀ᵐ y ∂Y, y ∈ Icc (0 : ℝ) 1 := by
      rw [ae_iff]
      exact hYsupport
    rw [← hπ.map_fst] at hh
    exact (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mp hh
  have hposInt : Integrable (fun w : ℝ => pos (w - c)) W := by
    apply Integrable.div_const
    apply Integrable.add
    · exact (hW2.integrable (by norm_num)).sub (integrable_const c)
    · exact ((hW2.integrable (by norm_num)).sub (integrable_const c)).abs
  have hnegInt : Integrable (fun w : ℝ => neg (w - c)) W := by
    apply Integrable.div_const
    apply Integrable.add
    · exact ((hW2.integrable (by norm_num)).sub (integrable_const c)).neg
    · exact ((hW2.integrable (by norm_num)).sub (integrable_const c)).abs
  have hposMap (π : Measure (ℝ × ℝ)) (hπ : IsCoupling π Y W) :
      (∫ p, pos (p.2 - c) ∂π) = ∫ w, pos (w - c) ∂W := by
    calc
      (∫ p, pos (p.2 - c) ∂π) =
          ∫ w, pos (w - c) ∂(π.map Prod.snd) := by
            rw [integral_map measurable_snd.aemeasurable]
            fun_prop
      _ = ∫ w, pos (w - c) ∂W := by rw [hπ.map_snd]
  have hnegMap (π : Measure (ℝ × ℝ)) (hπ : IsCoupling π Y W) :
      (∫ p, neg (p.2 - c) ∂π) = ∫ w, neg (w - c) ∂W := by
    calc
      (∫ p, neg (p.2 - c) ∂π) =
          ∫ w, neg (w - c) ∂(π.map Prod.snd) := by
            rw [integral_map measurable_snd.aemeasurable]
            fun_prop
      _ = ∫ w, neg (w - c) ∂W := by rw [hπ.map_snd]
  have hplusProd := coupling_integrable_mul hplus hY2 hW2
  have hminusProd := coupling_integrable_mul hminus hY2 hW2
  have hplusFst : Integrable (fun p : ℝ × ℝ => p.1) πplus :=
    (coupling_fst_memLp hplus hY2).integrable (by norm_num)
  have hminusFst : Integrable (fun p : ℝ × ℝ => p.1) πminus :=
    (coupling_fst_memLp hminus hY2).integrable (by norm_num)
  have hplusPos : Integrable (fun p : ℝ × ℝ => pos (p.2 - c)) πplus := by
    apply Integrable.div_const
    apply Integrable.add
    · exact ((coupling_snd_memLp hplus hW2).integrable (by norm_num)).sub
        (integrable_const c)
    · exact (((coupling_snd_memLp hplus hW2).integrable (by norm_num)).sub
        (integrable_const c)).abs
  have hminusNeg : Integrable (fun p : ℝ × ℝ => neg (p.2 - c)) πminus := by
    apply Integrable.div_const
    apply Integrable.add
    · exact (((coupling_snd_memLp hminus hW2).integrable (by norm_num)).sub
        (integrable_const c)).neg
    · exact (((coupling_snd_memLp hminus hW2).integrable (by norm_num)).sub
        (integrable_const c)).abs
  have hu :
      (∫ p, p.1 * p.2 ∂πplus) ≤
        c * (∫ y, y ∂Y) + ∫ w, pos (w - c) ∂W := by
    rw [← coupling_integral_fst hplus hY2, ← hposMap πplus hplus,
      ← integral_const_mul, ← integral_add (hplusFst.const_mul c) hplusPos]
    apply integral_mono_ae hplusProd ((hplusFst.const_mul c).add hplusPos)
    filter_upwards [hYae πplus hplus] with p hp
    dsimp [pos]
    have habs : -(p.2 - c) ≤ |p.2 - c| := neg_le_abs (p.2 - c)
    have habs' : p.2 - c ≤ |p.2 - c| := le_abs_self (p.2 - c)
    by_cases hw : 0 ≤ p.2 - c
    · rw [abs_of_nonneg hw]
      nlinarith [hp.2]
    · rw [abs_of_nonpos (le_of_not_ge hw)]
      nlinarith [hp.1]
  have hl :
      c * (∫ y, y ∂Y) - ∫ w, neg (w - c) ∂W ≤
        ∫ p, p.1 * p.2 ∂πminus := by
    rw [← coupling_integral_fst hminus hY2, ← hnegMap πminus hminus,
      ← integral_const_mul, ← integral_sub (hminusFst.const_mul c) hminusNeg]
    apply integral_mono_ae ((hminusFst.const_mul c).sub hminusNeg) hminusProd
    filter_upwards [hYae πminus hminus] with p hp
    dsimp [neg]
    by_cases hw : 0 ≤ p.2 - c
    · rw [abs_of_nonneg hw]
      nlinarith [hp.1]
    · rw [abs_of_nonpos (le_of_not_ge hw)]
      nlinarith [hp.2]
  have hsplit :
      (∫ w, pos (w - c) ∂W) + (∫ w, neg (w - c) ∂W) =
        ∫ w, |w - c| ∂W := by
    rw [← integral_add hposInt hnegInt]
    apply integral_congr_ae
    filter_upwards with w
    dsimp [pos, neg]
    ring
  linarith

/-- Given [the stated mathematical inputs and assumptions](hyp:Y,W,πminus,πplus,hminus,hplus,hY2,hW2,c,hupper,hlower), this result [establishes the stated mathematical conclusion](goal). -/
lemma coupling_product_gap_eq_absoluteDeviation
    {Y W : Measure ℝ} [IsProbabilityMeasure Y] [IsProbabilityMeasure W]
    {πminus πplus : Measure (ℝ × ℝ)}
    (hminus : IsCoupling πminus Y W) (hplus : IsCoupling πplus Y W)
    (hY2 : MemLp (fun y : ℝ => y) 2 Y)
    (hW2 : MemLp (fun w : ℝ => w) 2 W) (c : ℝ)
    (hupper : ∀ᵐ p ∂πplus,
      p.1 * p.2 = c * p.1 + ((p.2 - c) + |p.2 - c|) / 2)
    (hlower : ∀ᵐ p ∂πminus,
      p.1 * p.2 = c * p.1 - (-(p.2 - c) + |p.2 - c|) / 2) :
    (∫ p, p.1 * p.2 ∂πplus) - (∫ p, p.1 * p.2 ∂πminus)
      = ∫ w, |w - c| ∂W := by
  letI : IsProbabilityMeasure πminus := hminus.isProbabilityMeasure
  letI : IsProbabilityMeasure πplus := hplus.isProbabilityMeasure
  let pos : ℝ → ℝ := fun x => (x + |x|) / 2
  let neg : ℝ → ℝ := fun x => (-x + |x|) / 2
  have hposInt : Integrable (fun w : ℝ => pos (w - c)) W := by
    exact (((hW2.integrable (by norm_num)).sub (integrable_const c)).add
      ((hW2.integrable (by norm_num)).sub (integrable_const c)).abs).div_const 2
  have hnegInt : Integrable (fun w : ℝ => neg (w - c)) W := by
    exact ((((hW2.integrable (by norm_num)).sub (integrable_const c)).neg).add
      ((hW2.integrable (by norm_num)).sub (integrable_const c)).abs).div_const 2
  have hposMap :
      (∫ p, pos (p.2 - c) ∂πplus) = ∫ w, pos (w - c) ∂W := by
    calc
      _ = ∫ w, pos (w - c) ∂(πplus.map Prod.snd) := by
        rw [integral_map measurable_snd.aemeasurable]
        fun_prop
      _ = _ := by rw [hplus.map_snd]
  have hnegMap :
      (∫ p, neg (p.2 - c) ∂πminus) = ∫ w, neg (w - c) ∂W := by
    calc
      _ = ∫ w, neg (w - c) ∂(πminus.map Prod.snd) := by
        rw [integral_map measurable_snd.aemeasurable]
        fun_prop
      _ = _ := by rw [hminus.map_snd]
  have hplusFst : Integrable (fun p : ℝ × ℝ => p.1) πplus :=
    (coupling_fst_memLp hplus hY2).integrable (by norm_num)
  have hminusFst : Integrable (fun p : ℝ × ℝ => p.1) πminus :=
    (coupling_fst_memLp hminus hY2).integrable (by norm_num)
  have hplusPos : Integrable (fun p : ℝ × ℝ => pos (p.2 - c)) πplus := by
    apply Integrable.div_const
    apply Integrable.add
    · exact ((coupling_snd_memLp hplus hW2).integrable (by norm_num)).sub
        (integrable_const c)
    · exact (((coupling_snd_memLp hplus hW2).integrable (by norm_num)).sub
        (integrable_const c)).abs
  have hminusNeg : Integrable (fun p : ℝ × ℝ => neg (p.2 - c)) πminus := by
    apply Integrable.div_const
    apply Integrable.add
    · exact (((coupling_snd_memLp hminus hW2).integrable (by norm_num)).sub
        (integrable_const c)).neg
    · exact (((coupling_snd_memLp hminus hW2).integrable (by norm_num)).sub
        (integrable_const c)).abs
  have hu :
      (∫ p, p.1 * p.2 ∂πplus) =
        c * (∫ y, y ∂Y) + ∫ w, pos (w - c) ∂W := by
    rw [← coupling_integral_fst hplus hY2, ← hposMap,
      ← integral_const_mul, ← integral_add (hplusFst.const_mul c) hplusPos]
    exact integral_congr_ae (hupper.mono fun p hp => by simpa [pos] using hp)
  have hl :
      (∫ p, p.1 * p.2 ∂πminus) =
        c * (∫ y, y ∂Y) - ∫ w, neg (w - c) ∂W := by
    rw [← coupling_integral_fst hminus hY2, ← hnegMap,
      ← integral_const_mul, ← integral_sub (hminusFst.const_mul c) hminusNeg]
    exact integral_congr_ae (hlower.mono fun p hp => by simpa [neg] using hp)
  have hsplit :
      (∫ w, pos (w - c) ∂W) + (∫ w, neg (w - c) ∂W) =
        ∫ w, |w - c| ∂W := by
    rw [← integral_add hposInt hnegInt]
    apply integral_congr_ae
    filter_upwards with w
    dsimp [pos, neg]
    ring
  rw [hu, hl]
  linarith

/-- Given [the stated mathematical inputs and assumptions](hyp:W,hW2), this result [establishes the stated mathematical conclusion](goal). -/
lemma fairBernoulli_monotoneCoupling_gap_eq_medianAbsoluteDeviation
    (W : Measure ℝ) [IsProbabilityMeasure W]
    (hW2 : MemLp (fun w : ℝ => w) 2 W) :
    (∫ p, p.1 * p.2 ∂
        (Causalean.Stat.comonotoneCoupling fairBernoulliLaw W)) -
      (∫ p, p.1 * p.2 ∂
        (Causalean.Stat.countermonotoneCoupling fairBernoulliLaw W)) =
      ∫ w, |w - quantile W (1 / 2)| ∂W := by
  let m := quantile W (1 / 2)
  have hYae : ∀ᵐ y ∂fairBernoulliLaw, y ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    simp [fairBernoulliLaw]
  have hY2 : MemLp (fun y : ℝ => y) 2 fairBernoulliLaw := by
    apply memLp_of_bounded
    · filter_upwards [hYae] with y hy
      exact hy
    · fun_prop
  have hupper : ∀ᵐ p ∂(Causalean.Stat.comonotoneCoupling fairBernoulliLaw W),
      p.1 * p.2 =
        m * p.1 + ((p.2 - m) + |p.2 - m|) / 2 := by
    unfold Causalean.Stat.comonotoneCoupling
    let φ : ℝ → ℝ × ℝ :=
      fun u => (quantile fairBernoulliLaw u, quantile W u)
    have hφ : AEMeasurable φ Causalean.Stat.unifOI :=
      (Causalean.Stat.aemeasurable_quantile_unifOI fairBernoulliLaw).prodMk
        (Causalean.Stat.aemeasurable_quantile_unifOI W)
    apply (ae_map_iff hφ (by
      exact measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    change quantile fairBernoulliLaw u * quantile W u =
      m * quantile fairBernoulliLaw u +
        ((quantile W u - m) + |quantile W u - m|) / 2
    rw [fairBernoulliLaw_quantile u hu.1 hu.2]
    by_cases huh : u ≤ 1 / 2
    · have hqm : quantile W u ≤ m := by
        dsimp [m]
        exact quantile_mono hu.1 (by norm_num) huh
      norm_num [div_eq_mul_inv] at huh ⊢
      have hstep : u ≤ (2 : ℝ)⁻¹ := by
        convert huh using 1 <;> norm_num
      simp [hstep, abs_of_nonpos (sub_nonpos.mpr hqm)]
    · have hmq : m ≤ quantile W u := by
        dsimp [m]
        exact quantile_mono (by norm_num) hu.2 (le_of_not_ge huh)
      norm_num [div_eq_mul_inv] at huh ⊢
      have hstep : ¬u ≤ (1 / 2 : ℝ) := not_le_of_gt huh
      rw [if_neg hstep, if_neg hstep,
        abs_of_nonneg (sub_nonneg.mpr hmq)]
      ring
  have hlower :
      ∀ᵐ p ∂(Causalean.Stat.countermonotoneCoupling fairBernoulliLaw W),
      p.1 * p.2 =
        m * p.1 - (-(p.2 - m) + |p.2 - m|) / 2 := by
    unfold Causalean.Stat.countermonotoneCoupling
    let r : ℝ → ℝ := fun u => 1 - u
    have hr : Measurable r := by fun_prop
    have hWmap : AEMeasurable (quantile W)
        (Causalean.Stat.unifOI.map r) := by
      simpa [r, Causalean.Stat.map_one_sub_unifOI] using
        (Causalean.Stat.aemeasurable_quantile_unifOI W)
    have hWr : AEMeasurable (fun u : ℝ => quantile W (1 - u))
        Causalean.Stat.unifOI := by
      simpa [r, Function.comp_def] using hWmap.comp_measurable hr
    let φ : ℝ → ℝ × ℝ :=
      fun u => (quantile fairBernoulliLaw u, quantile W (1 - u))
    have hφ : AEMeasurable φ Causalean.Stat.unifOI :=
      (Causalean.Stat.aemeasurable_quantile_unifOI fairBernoulliLaw).prodMk hWr
    apply (ae_map_iff hφ (by
      exact measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hv0 : 0 < 1 - u := by linarith [hu.2]
    have hv1 : 1 - u < 1 := by linarith [hu.1]
    change quantile fairBernoulliLaw u * quantile W (1 - u) =
      m * quantile fairBernoulliLaw u -
        (-(quantile W (1 - u) - m) + |quantile W (1 - u) - m|) / 2
    rw [fairBernoulliLaw_quantile u hu.1 hu.2]
    by_cases huh : u ≤ 1 / 2
    · have hmq : m ≤ quantile W (1 - u) := by
        dsimp [m]
        apply quantile_mono (by norm_num) hv1
        linarith
      norm_num [div_eq_mul_inv] at huh ⊢
      have hstep : u ≤ (2 : ℝ)⁻¹ := by
        convert huh using 1 <;> norm_num
      simp [hstep, abs_of_nonneg (sub_nonneg.mpr hmq)]
    · have hqm : quantile W (1 - u) ≤ m := by
        dsimp [m]
        apply quantile_mono hv0 (by norm_num)
        linarith
      norm_num [div_eq_mul_inv] at huh ⊢
      have hstep : ¬u ≤ (1 / 2 : ℝ) := not_le_of_gt huh
      rw [if_neg hstep, if_neg hstep,
        abs_of_nonpos (sub_nonpos.mpr hqm)]
      ring
  simpa [m] using coupling_product_gap_eq_absoluteDeviation
    (Causalean.Stat.isCoupling_countermonotoneCoupling fairBernoulliLaw W)
    (Causalean.Stat.isCoupling_comonotoneCoupling fairBernoulliLaw W)
    hY2 hW2 m hupper hlower

/-- Given [the stated mathematical inputs and assumptions](hyp:W,hW2,C,hC,hmedian), this result [establishes the stated mathematical conclusion](goal). -/
lemma fairBernoulli_monotoneCoupling_gap_eq_sInf_absoluteDeviation
    (W : Measure ℝ) [IsProbabilityMeasure W]
    (hW2 : MemLp (fun w : ℝ => w) 2 W)
    (C : Set ℝ) (hC : C.Nonempty) (hmedian : quantile W (1 / 2) ∈ C) :
    (∫ p, p.1 * p.2 ∂
        (Causalean.Stat.comonotoneCoupling fairBernoulliLaw W)) -
      (∫ p, p.1 * p.2 ∂
        (Causalean.Stat.countermonotoneCoupling fairBernoulliLaw W)) =
      sInf {v : ℝ | ∃ c ∈ C, v = ∫ w, |w - c| ∂W} := by
  have hYsupport : fairBernoulliLaw (Icc (0 : ℝ) 1)ᶜ = 0 := by
    simp [fairBernoulliLaw]
  have hYae : ∀ᵐ y ∂fairBernoulliLaw, y ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact hYsupport
  have hY2 : MemLp (fun y : ℝ => y) 2 fairBernoulliLaw := by
    apply memLp_of_bounded
    · filter_upwards [hYae] with y hy
      exact hy
    · fun_prop
  have hle :
      (∫ p, p.1 * p.2 ∂
          (Causalean.Stat.comonotoneCoupling fairBernoulliLaw W)) -
        (∫ p, p.1 * p.2 ∂
          (Causalean.Stat.countermonotoneCoupling fairBernoulliLaw W)) ≤
        sInf {v : ℝ | ∃ c ∈ C, v = ∫ w, |w - c| ∂W} := by
    apply le_csInf
    · rcases hC with ⟨c, hc⟩
      exact ⟨∫ w, |w - c| ∂W, c, hc, rfl⟩
    · intro v hv
      rcases hv with ⟨c, hc, rfl⟩
      exact coupling_product_gap_le_absoluteDeviation
        (Causalean.Stat.isCoupling_countermonotoneCoupling fairBernoulliLaw W)
        (Causalean.Stat.isCoupling_comonotoneCoupling fairBernoulliLaw W)
        hYsupport hY2 hW2 c
  have heq :=
    fairBernoulli_monotoneCoupling_gap_eq_medianAbsoluteDeviation W hW2
  have hbelow : BddBelow {v : ℝ | ∃ c ∈ C, v = ∫ w, |w - c| ∂W} := by
    refine ⟨0, ?_⟩
    intro v hv
    rcases hv with ⟨c, hc, rfl⟩
    exact integral_nonneg fun w => abs_nonneg _
  have hinf :
      sInf {v : ℝ | ∃ c ∈ C, v = ∫ w, |w - c| ∂W} ≤
        ∫ w, |w - quantile W (1 / 2)| ∂W :=
    csInf_le hbelow ⟨quantile W (1 / 2), hmedian, rfl⟩
  exact le_antisymm hle (heq.symm ▸ hinf)

/-- Given [the stated mathematical inputs and assumptions](hyp:Y,W,hYsupport,hY2,hW2,C,hC), this result [establishes the stated mathematical conclusion](goal). -/
lemma monotoneCoupling_product_gap_le_sInf_absoluteDeviation
    (Y W : Measure ℝ) [IsProbabilityMeasure Y] [IsProbabilityMeasure W]
    (hYsupport : Y (Icc (0 : ℝ) 1)ᶜ = 0)
    (hY2 : MemLp (fun y : ℝ => y) 2 Y)
    (hW2 : MemLp (fun w : ℝ => w) 2 W)
    (C : Set ℝ) (hC : C.Nonempty) :
    (∫ p, p.1 * p.2 ∂(Causalean.Stat.comonotoneCoupling Y W)) -
        (∫ p, p.1 * p.2 ∂(Causalean.Stat.countermonotoneCoupling Y W))
      ≤ sInf {v : ℝ | ∃ c ∈ C, v = ∫ w, |w - c| ∂W} := by
  apply le_csInf
  · rcases hC with ⟨c, hc⟩
    exact ⟨∫ w, |w - c| ∂W, c, hc, rfl⟩
  · intro v hv
    rcases hv with ⟨c, hc, rfl⟩
    exact coupling_product_gap_le_absoluteDeviation
      (Causalean.Stat.isCoupling_countermonotoneCoupling Y W)
      (Causalean.Stat.isCoupling_comonotoneCoupling Y W)
      hYsupport hY2 hW2 c

end
end CausalSmith.PartialID.UnlinkedPropensityAte

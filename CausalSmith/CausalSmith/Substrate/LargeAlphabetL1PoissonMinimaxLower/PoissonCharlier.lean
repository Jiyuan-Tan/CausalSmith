import CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower.Basic
import Causalean.Stat.Minimax.MaximalCoupling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Charlier expansion for moment-matched Poisson mixtures

This file develops the elementary Charlier-polynomial and countable-measure
lemmas used by the scalar mixed-Poisson total-variation estimate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower

/-- The monic Charlier polynomial, evaluated on a natural number, in its
creation-operator recursion. -/
noncomputable def monicCharlier (a : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | k + 1, z => (z : ℝ) * monicCharlier a k (z - 1) - a * monicCharlier a k z

@[simp] lemma monicCharlier_succ (a : ℝ) (k z : ℕ) :
    monicCharlier a (k + 1) z =
      (z : ℝ) * monicCharlier a k (z - 1) - a * monicCharlier a k z := rfl

lemma monicCharlier_zero (a : ℝ) (k : ℕ) :
    monicCharlier a k 0 = (-a) ^ k := by
  induction k with
  | zero => simp [monicCharlier]
  | succ k ih => simp [monicCharlier, ih, pow_succ] <;> ring

/-- Forward differences lower the Charlier degree. -/
lemma monicCharlier_forwardDiff (a : ℝ) (k z : ℕ) :
    monicCharlier a (k + 1) (z + 1) - monicCharlier a (k + 1) z =
      (k + 1 : ℝ) * monicCharlier a k z := by
  induction k generalizing z with
  | zero => simp [monicCharlier]
  | succ k ih =>
      rw [monicCharlier_succ a (k + 1) (z + 1),
        monicCharlier_succ a (k + 1) z]
      cases z with
      | zero =>
          have h := ih 0
          have hzero : monicCharlier a (k + 1) 0 =
              -a * monicCharlier a k 0 := by
            rw [monicCharlier_succ]
            simp
          norm_num only [Nat.cast_zero, Nat.cast_one, Nat.zero_add, Nat.one_sub,
            one_mul, zero_mul, zero_sub] at ⊢
          push_cast at h ⊢
          have hone : monicCharlier a (k + 1) 1 =
              monicCharlier a (k + 1) 0 +
                (k + 1 : ℝ) * monicCharlier a k 0 := by linarith
          rw [hone, hzero]
          ring
      | succ w =>
          have hnext := ih (w + 1)
          have hprev := ih w
          have hrec : monicCharlier a (k + 1) (w + 1) =
              (w + 1 : ℝ) * monicCharlier a k w -
                a * monicCharlier a k (w + 1) := by
            rw [monicCharlier_succ]
            simp
          simp only [Nat.add_sub_cancel, Nat.succ_sub_one] at ⊢
          push_cast at hnext hprev hrec ⊢
          have hn : monicCharlier a (k + 1) (w + 1 + 1) =
              monicCharlier a (k + 1) (w + 1) +
                (k + 1 : ℝ) * monicCharlier a k (w + 1) := by linarith
          have hp : monicCharlier a (k + 1) w =
              monicCharlier a (k + 1) (w + 1) -
                (k + 1 : ℝ) * monicCharlier a k w := by linarith
          rw [hn, hp, hrec]
          ring

noncomputable def charlierTerm (a x : ℝ) (z k : ℕ) : ℝ :=
  monicCharlier a k z / (a ^ k * (k.factorial : ℝ)) * x ^ k

lemma charlierTerm_succ_rate {a : ℝ} (ha : a ≠ 0) (x : ℝ) (z k : ℕ) :
    charlierTerm a x (z + 1) (k + 1) =
      charlierTerm a x z (k + 1) +
        (x / a) * charlierTerm a x z k := by
  rw [charlierTerm, charlierTerm, charlierTerm]
  have hd := monicCharlier_forwardDiff a k z
  have he : monicCharlier a (k + 1) (z + 1) =
      monicCharlier a (k + 1) z +
        (k + 1 : ℝ) * monicCharlier a k z := by linarith
  rw [he]
  rw [pow_succ, pow_succ, Nat.factorial_succ]
  push_cast
  field_simp

private lemma charlierTerm_zero_degree (a x : ℝ) (z : ℕ) :
    charlierTerm a x z 0 = 1 := by simp [charlierTerm, monicCharlier]

/-- Exponential generating function of the monic Charlier polynomials. -/
lemma monicCharlier_hasSum {a : ℝ} (ha : a ≠ 0) (x : ℝ) (z : ℕ) :
    HasSum (charlierTerm a x z)
      (Real.exp (-x) * (1 + x / a) ^ z) := by
  induction z with
  | zero =>
      have h : HasSum (fun k : ℕ => (-x) ^ k / (k.factorial : ℝ))
          (Real.exp (-x)) := by
        simpa only [Real.exp_eq_exp_ℝ] using
          (NormedSpace.expSeries_div_hasSum_exp (-x : ℝ))
      convert h using 1
      · funext k
        rw [charlierTerm, monicCharlier_zero]
        field_simp [ha]
        ring
      · simp
  | succ z ih =>
      let q : ℕ → ℝ
        | 0 => 0
        | k + 1 => (x / a) * charlierTerm a x z k
      have hq : HasSum q ((x / a) *
          (Real.exp (-x) * (1 + x / a) ^ z)) := by
        have htail : HasSum (fun n => q (n + 1)) ((x / a) *
            (Real.exp (-x) * (1 + x / a) ^ z)) := by
          simpa [q] using ih.mul_left (x / a)
        simpa [q] using htail.zero_add
      convert ih.add hq using 1
      · funext k
        cases k with
        | zero => simp [q, charlierTerm_zero_degree]
        | succ k => simp only [q, charlierTerm_succ_rate ha]
      · ring

/-- The Charlier generating series is absolutely summable. -/
lemma summable_norm_charlierTerm {a : ℝ} (ha : a ≠ 0) (x : ℝ) (z : ℕ) :
    Summable (fun k => ‖charlierTerm a x z k‖) := by
  induction z with
  | zero =>
      have h := (NormedSpace.norm_expSeries_div_summable (-x : ℝ))
      apply h.congr
      intro k
      congr 1
      rw [charlierTerm, monicCharlier_zero]
      field_simp [ha]
      ring
  | succ z ih =>
      have hdegreeShift : Summable (fun k => ‖charlierTerm a x z (k + 1)‖) :=
        ih.comp_injective Nat.succ_injective
      have hshift : Summable (fun k => ‖(x / a) * charlierTerm a x z k‖) :=
        by simpa [norm_mul] using ih.mul_left ‖x / a‖
      rw [← summable_nat_add_iff 1]
      simp only [charlierTerm_succ_rate ha]
      apply Summable.of_nonneg_of_le
        (f := fun k => ‖charlierTerm a x z (k + 1)‖ +
          ‖(x / a) * charlierTerm a x z k‖)
      · exact fun _ => norm_nonneg _
      · exact fun k => norm_add_le _ _
      · exact hdegreeShift.add hshift

private lemma integrable_exp_natCast_poisson (a : ℝ≥0) (t : ℝ) :
    Integrable (fun z : ℕ => Real.exp (t * (z : ℝ))) (poissonMeasure a) := by
  rw [integrable_poissonMeasure_iff]
  have hs := Real.summable_pow_div_factorial ((a : ℝ) * Real.exp t)
  apply hs.mul_left (Real.exp (-(a : ℝ))) |>.congr
  intro z
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [show Real.exp (t * (z : ℝ)) = (Real.exp t) ^ z by
    calc
      Real.exp (t * (z : ℝ)) = Real.exp ((z : ℝ) * t) := by ring_nf
      _ = (Real.exp t) ^ z := Real.exp_nat_mul t z]
  push_cast
  ring

private lemma integrable_shifted_natCast_pow_poisson (a : ℝ≥0) (c : ℝ) (k : ℕ) :
    Integrable (fun z : ℕ => ((z : ℝ) + c) ^ k) (poissonMeasure a) := by
  apply ProbabilityTheory.integrable_pow_of_integrable_exp_mul
      (X := fun z : ℕ => (z : ℝ) + c) (t := 1)
  · norm_num
  · simpa [add_mul, Real.exp_add, mul_comm] using
      (integrable_exp_natCast_poisson a 1).mul_const (Real.exp c)
  · simpa [add_mul, Real.exp_add, mul_comm] using
      (integrable_exp_natCast_poisson a (-1)).mul_const (Real.exp (-c))

private lemma abs_monicCharlier_le (a : ℝ) (k z : ℕ) :
    |monicCharlier a k z| ≤ ((z : ℝ) + |a|) ^ k := by
  induction k generalizing z with
  | zero => simp [monicCharlier]
  | succ k ih =>
      rw [monicCharlier_succ, pow_succ]
      calc
        |(z : ℝ) * monicCharlier a k (z - 1) - a * monicCharlier a k z| ≤
            (z : ℝ) * |monicCharlier a k (z - 1)| +
              |a| * |monicCharlier a k z| := by
                calc
                  |_ - _| ≤ |(z : ℝ) * monicCharlier a k (z - 1)| +
                      |a * monicCharlier a k z| := abs_sub _ _
                  _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg z)]
        _ ≤ (z : ℝ) * (((z - 1 : ℕ) : ℝ) + |a|) ^ k +
              |a| * ((z : ℝ) + |a|) ^ k := by
                gcongr
                exact ih (z - 1)
                exact ih z
        _ ≤ (z : ℝ) * ((z : ℝ) + |a|) ^ k +
              |a| * ((z : ℝ) + |a|) ^ k := by
                have hzsub : (((z - 1 : ℕ) : ℝ) + |a|) ≤ (z : ℝ) + |a| := by
                  have hzcast : ((z - 1 : ℕ) : ℝ) ≤ (z : ℝ) := by
                    exact_mod_cast Nat.sub_le z 1
                  linarith
                gcongr
        _ = ((z : ℝ) + |a|) ^ (k + 1) := by ring

private lemma integrable_monicCharlier_mul (a : ℝ≥0) (k l : ℕ) :
    Integrable (fun z : ℕ => monicCharlier (a : ℝ) k z *
      monicCharlier (a : ℝ) l z) (poissonMeasure a) := by
  apply Integrable.mono'
      (integrable_shifted_natCast_pow_poisson a |(a : ℝ)| (k + l))
      (by fun_prop)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_mul, pow_add]
  exact mul_le_mul (abs_monicCharlier_le (a : ℝ) k z)
    (abs_monicCharlier_le (a : ℝ) l z) (abs_nonneg _) (by positivity)

private lemma poisson_creation_integral (a : ℝ≥0) (f : ℕ → ℝ)
    (hl : Integrable (fun z : ℕ => (z : ℝ) * f (z - 1)) (poissonMeasure a)) :
    (∫ z, (z : ℝ) * f (z - 1) ∂poissonMeasure a) =
      (a : ℝ) * ∫ z, f z ∂poissonMeasure a := by
  have hsum : Summable (fun n : ℕ =>
      (Real.exp (-(a : ℝ)) * (a : ℝ) ^ n / (n.factorial : ℝ)) •
        ((n : ℝ) * f (n - 1))) :=
    (hasSum_integral_poissonMeasure hl).summable
  rw [integral_poissonMeasure, integral_poissonMeasure]
  rw [hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, smul_zero, zero_add]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
    Nat.factorial_succ, Nat.cast_mul]
  rw [pow_succ]
  field_simp

private lemma integrable_monicCharlier_mul_succArg (a : ℝ≥0) (k l : ℕ) :
    Integrable (fun z : ℕ => monicCharlier (a : ℝ) k z *
      monicCharlier (a : ℝ) l (z + 1)) (poissonMeasure a) := by
  cases l with
  | zero => simpa [monicCharlier] using
      (integrable_monicCharlier_mul a k 0)
  | succ l =>
      have h := (integrable_monicCharlier_mul a k (l + 1)).add
        ((integrable_monicCharlier_mul a k l).mul_const (l + 1 : ℝ))
      apply h.congr
      filter_upwards with z
      rw [show monicCharlier (a : ℝ) (l + 1) (z + 1) =
        monicCharlier (a : ℝ) (l + 1) z +
          (l + 1 : ℝ) * monicCharlier (a : ℝ) l z by
          linarith [monicCharlier_forwardDiff (a : ℝ) l z]]
      simp only [Pi.add_apply]
      ring

/-- The Charlier creation operator is adjoint to `a` times forward difference
under the Poisson law of mean `a`. -/
lemma monicCharlier_adjoint (a : ℝ≥0) (k l : ℕ) :
    (∫ z, monicCharlier (a : ℝ) (k + 1) z *
        monicCharlier (a : ℝ) l z ∂poissonMeasure a) =
      (a : ℝ) * ∫ z, monicCharlier (a : ℝ) k z *
        (monicCharlier (a : ℝ) l (z + 1) -
          monicCharlier (a : ℝ) l z) ∂poissonMeasure a := by
  let f : ℕ → ℝ := fun z => monicCharlier (a : ℝ) k z *
    monicCharlier (a : ℝ) l (z + 1)
  have hf : Integrable f (poissonMeasure a) :=
    integrable_monicCharlier_mul_succArg a k l
  have hleft : Integrable (fun z : ℕ => (z : ℝ) * f (z - 1))
      (poissonMeasure a) := by
    have h := (integrable_monicCharlier_mul a (k + 1) l).add
      ((integrable_monicCharlier_mul a k l).mul_const (a : ℝ))
    apply h.congr
    filter_upwards with z
    dsimp [f]
    by_cases hz : z = 0
    · subst z
      simp <;> ring
    · have hz' : z - 1 + 1 = z := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hz)
      rw [hz']
      ring
  have hc := poisson_creation_integral a f hleft
  have hprod := integrable_monicCharlier_mul a k l
  have hsucc := integrable_monicCharlier_mul_succArg a k l
  calc
    (∫ z, monicCharlier (a : ℝ) (k + 1) z *
        monicCharlier (a : ℝ) l z ∂poissonMeasure a) =
        ∫ z, (z : ℝ) * f (z - 1) -
          (a : ℝ) * (monicCharlier (a : ℝ) k z *
            monicCharlier (a : ℝ) l z) ∂poissonMeasure a := by
          apply integral_congr_ae
          filter_upwards with z
          dsimp [f]
          by_cases hz : z = 0
          · subst z; simp <;> ring
          · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hz)]
            ring
    _ = (∫ z, (z : ℝ) * f (z - 1) ∂poissonMeasure a) -
        ∫ z, (a : ℝ) * (monicCharlier (a : ℝ) k z *
          monicCharlier (a : ℝ) l z) ∂poissonMeasure a := by
          rw [integral_sub hleft (hprod.const_mul _)]
    _ = (a : ℝ) * (∫ z, f z ∂poissonMeasure a) -
        (a : ℝ) * ∫ z, monicCharlier (a : ℝ) k z *
          monicCharlier (a : ℝ) l z ∂poissonMeasure a := by
          rw [hc, integral_const_mul]
    _ = (a : ℝ) * ∫ z, monicCharlier (a : ℝ) k z *
        (monicCharlier (a : ℝ) l (z + 1) -
          monicCharlier (a : ℝ) l z) ∂poissonMeasure a := by
          rw [← mul_sub, ← integral_sub hsucc hprod]
          congr 2
          funext z
          ring

/-- Exact squared norm of the monic Charlier polynomial under its Poisson
orthogonality measure. -/
lemma integral_monicCharlier_sq (a : ℝ≥0) (k : ℕ) :
    (∫ z, monicCharlier (a : ℝ) k z ^ 2 ∂poissonMeasure a) =
      (a : ℝ) ^ k * (k.factorial : ℝ) := by
  induction k with
  | zero => simp [monicCharlier]
  | succ k ih =>
      rw [show (fun z => monicCharlier (a : ℝ) (k + 1) z ^ 2) =
          fun z => monicCharlier (a : ℝ) (k + 1) z *
            monicCharlier (a : ℝ) (k + 1) z by funext z; ring]
      rw [monicCharlier_adjoint a k (k + 1)]
      have hd (z : ℕ) : monicCharlier (a : ℝ) (k + 1) (z + 1) -
          monicCharlier (a : ℝ) (k + 1) z =
            (k + 1 : ℝ) * monicCharlier (a : ℝ) k z :=
        monicCharlier_forwardDiff (a : ℝ) k z
      simp_rw [hd]
      rw [show (fun z => monicCharlier (a : ℝ) k z *
          ((k + 1 : ℝ) * monicCharlier (a : ℝ) k z)) =
            fun z => (k + 1 : ℝ) * monicCharlier (a : ℝ) k z ^ 2 by
          funext z; ring,
        integral_const_mul, ih, pow_succ, Nat.factorial_succ]
      push_cast
      ring

/-- Cauchy--Schwarz bound for the first absolute moment of a Charlier
polynomial. -/
lemma integral_abs_monicCharlier_le_sqrt (a : ℝ≥0) (k : ℕ) :
    (∫ z, |monicCharlier (a : ℝ) k z| ∂poissonMeasure a) ≤
      Real.sqrt ((a : ℝ) ^ k * (k.factorial : ℝ)) := by
  have hmeas : AEStronglyMeasurable
      (fun z : ℕ => monicCharlier (a : ℝ) k z) (poissonMeasure a) := by
    fun_prop
  have hsq : Integrable (fun z : ℕ =>
      ‖monicCharlier (a : ℝ) k z‖ ^ 2) (poissonMeasure a) := by
    convert integrable_monicCharlier_mul a k k using 1
    funext z
    rw [Real.norm_eq_abs, sq_abs, pow_two]
  have hLp : MemLp (fun z : ℕ => monicCharlier (a : ℝ) k z)
      (ENNReal.ofReal (2 : ℝ)) (poissonMeasure a) := by
    simpa using (memLp_two_iff_integrable_sq_norm hmeas).2 hsq
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    constructor <;> norm_num
  have hcs := integral_mul_norm_le_Lp_mul_Lq hholder hLp
    (memLp_const (μ := poissonMeasure a) (1 : ℝ))
  simp only [Real.norm_eq_abs, abs_one, mul_one, one_div] at hcs
  rw [show (∫ z : ℕ, |monicCharlier (a : ℝ) k z| ^ (2 : ℝ)
      ∂poissonMeasure a) = (a : ℝ) ^ k * (k.factorial : ℝ) by
        simp_rw [Real.rpow_two]
        simpa [sq_abs] using integral_monicCharlier_sq a k,
    show (∫ _z : ℕ, (1 : ℝ) ^ (2 : ℝ) ∂poissonMeasure a) = 1 by simp,
    ] at hcs
  simpa [Real.sqrt_eq_rpow] using hcs

private lemma hasSum_measureReal_singleton (μ : Measure ℕ)
    [IsProbabilityMeasure μ] : HasSum (fun n : ℕ => μ.real {n}) 1 := by
  let p := μ.toPMF
  have htop : ∑' n, p n ≠ ⊤ := by simp [PMF.tsum_coe]
  have hs := ENNReal.hasSum_toReal htop
  have hval : ∑' n, (p n).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq]
    · simp [PMF.tsum_coe]
    · intro n
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one p n)
  rw [hval] at hs
  convert hs using 1
  funext n
  rw [Measure.toPMF_apply]
  rfl

private lemma tsum_indicator_measureReal_singleton (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (A : Set ℕ) :
    ∑' n : ℕ, A.indicator (fun n => μ.real {n}) n = μ.real A := by
  have hENN := μ.tsum_indicator_apply_singleton A
    (MeasurableSet.of_discrete : MeasurableSet A)
  have hfinite (n : ℕ) : A.indicator (fun n => μ {n}) n ≠ ⊤ := by
    by_cases hn : n ∈ A <;> simp [Set.indicator, hn]
  have hreal := congrArg ENNReal.toReal hENN
  rw [ENNReal.tsum_toReal_eq hfinite] at hreal
  have hind : (fun n : ℕ => (A.indicator (fun n => μ {n}) n).toReal) =
      A.indicator (fun n => μ.real {n}) := by
    funext n
    by_cases hn : n ∈ A <;> simp [Set.indicator, hn, measureReal_def]
  rw [hind] at hreal
  exact hreal

/-- On a countable discrete space, total variation is at most one half of the
ℓ¹ distance between singleton masses. -/
lemma tvDist_le_half_tsum_abs_singleton (μ ν : Measure ℕ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Causalean.Stat.tvDist μ ν ≤
      (1 / 2 : ℝ) * ∑' n : ℕ, |μ.real {n} - ν.real {n}| := by
  let f : ℕ → ℝ := fun n => μ.real {n} - ν.real {n}
  have hμ := hasSum_measureReal_singleton μ
  have hν := hasSum_measureReal_singleton ν
  have hfSum : Summable f := hμ.summable.sub hν.summable
  have hf : Integrable f Measure.count := by
    rw [integrable_count_iff]
    exact hfSum.norm
  have hzero : ∫ n, f n ∂Measure.count = 0 := by
    rw [integral_countable hf]
    simp only [Measure.count_singleton, measureReal_def, ENNReal.toReal_one, one_smul]
    change (∑' n, (μ.real {n} - ν.real {n})) = 0
    simpa using (hμ.sub hν).tsum_eq
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  have hbound := Causalean.Stat.abs_setIntegral_le_half_integral_abs_of_integral_eq_zero
    hf hzero hA
  rw [← integral_indicator hA] at hbound
  rw [integral_countable (hf.indicator hA), integral_countable hf.abs] at hbound
  simp only [Measure.count_singleton, measureReal_def, ENNReal.toReal_one, one_smul] at hbound
  have hind : A.indicator f =
      A.indicator (fun n => μ.real {n}) - A.indicator (fun n => ν.real {n}) := by
    funext n
    by_cases hn : n ∈ A <;> simp [Set.indicator, hn, f]
  have hμA : Summable (A.indicator fun n => μ.real {n}) :=
    summable_subtype_iff_indicator.mp
      (hμ.summable.subtype (p := fun n => n ∈ A))
  have hνA : Summable (A.indicator fun n => ν.real {n}) :=
    summable_subtype_iff_indicator.mp
      (hν.summable.subtype (p := fun n => n ∈ A))
  have htsub : (∑' x, ((A.indicator (fun n => μ.real {n}) -
      A.indicator (fun n => ν.real {n})) x)) =
      (∑' x, A.indicator (fun n => μ.real {n}) x) -
        ∑' x, A.indicator (fun n => ν.real {n}) x :=
    (hμA.hasSum.sub hνA.hasSum).tsum_eq
  rw [hind, htsub,
    tsum_indicator_measureReal_singleton μ A,
    tsum_indicator_measureReal_singleton ν A] at hbound
  simpa [f] using hbound

private lemma measurable_poissonMeasure : Measurable poissonMeasure := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [poissonMeasure, Measure.sum_apply _ hs, Measure.smul_apply,
    Measure.dirac_apply' _ hs]
  fun_prop

private noncomputable def poissonKernelMass (u : ℝ≥0) (j : ℕ) : ℝ :=
  Real.exp (-(u : ℝ)) * (u : ℝ) ^ j / (j.factorial : ℝ)

private lemma bind_poisson_real_singleton (ν : Measure ℝ≥0) (j : ℕ) :
    (ν.bind poissonMeasure).real {j} = ∫ u, poissonKernelMass u j ∂ν := by
  rw [measureReal_def, Measure.bind_apply (MeasurableSet.singleton j)
    measurable_poissonMeasure.aemeasurable]
  simp_rw [poissonMeasure_singleton]
  rw [← integral_eq_lintegral_of_nonneg_ae]
  · rfl
  · exact Filter.Eventually.of_forall fun u => by
      dsimp [poissonKernelMass]
      positivity
  · fun_prop

private lemma ae_mem_Icc_of_mass_one {ν : Measure ℝ≥0}
    [IsProbabilityMeasure ν] {lo hi : ℝ≥0} (hs : ν (Set.Icc lo hi) = 1) :
    ∀ᵐ u ∂ν, u ∈ Set.Icc lo hi := by
  exact (ae_iff_prob_eq_one
    (MeasurableSet.mem (measurableSet_Icc : MeasurableSet (Set.Icc lo hi)))).2 hs

private lemma abs_sub_center_le_of_mem {a M u : ℝ≥0} (hM : M ≤ a)
    (hu : u ∈ Set.Icc (a - M) (a + M)) :
    |(u : ℝ) - (a : ℝ)| ≤ (M : ℝ) := by
  have hlo : (a : ℝ) - (M : ℝ) ≤ (u : ℝ) := by
    exact_mod_cast hu.1
  have hhi : (u : ℝ) ≤ (a : ℝ) + (M : ℝ) := by
    exact_mod_cast hu.2
  rw [abs_le]
  constructor <;> linarith

private lemma integrable_rate_pow_of_support {ν : Measure ℝ≥0}
    [IsProbabilityMeasure ν] {a M : ℝ≥0}
    (hs : ν (Set.Icc (a - M) (a + M)) = 1) (k : ℕ) :
    Integrable (fun u : ℝ≥0 => (u : ℝ) ^ k) ν := by
  refine Integrable.of_bound (by fun_prop) (((a : ℝ) + (M : ℝ)) ^ k) ?_
  filter_upwards [ae_mem_Icc_of_mass_one hs] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr
  exact_mod_cast hu.2

private lemma integrable_centered_pow_of_support {ν : Measure ℝ≥0}
    [IsProbabilityMeasure ν] {a M : ℝ≥0} (hM : M ≤ a)
    (hs : ν (Set.Icc (a - M) (a + M)) = 1) (k : ℕ) :
    Integrable (fun u : ℝ≥0 => ((u : ℝ) - (a : ℝ)) ^ k) ν := by
  refine Integrable.of_bound (by fun_prop) ((M : ℝ) ^ k) ?_
  filter_upwards [ae_mem_Icc_of_mass_one hs] with u hu
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (by positivity) (abs_sub_center_le_of_mem hM hu) k

private lemma centered_moments_eq {ν0 ν1 : Measure ℝ≥0}
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    {a M : ℝ≥0} {L : ℕ} (hM : M ≤ a)
    (hs0 : ν0 (Set.Icc (a - M) (a + M)) = 1)
    (hs1 : ν1 (Set.Icc (a - M) (a + M)) = 1)
    (hmom : ∀ k ≤ L, (∫ u, (u : ℝ) ^ k ∂ν0) = ∫ u, (u : ℝ) ^ k ∂ν1)
    {k : ℕ} (hk : k ≤ L) :
    (∫ u, ((u : ℝ) - (a : ℝ)) ^ k ∂ν0) =
      ∫ u, ((u : ℝ) - (a : ℝ)) ^ k ∂ν1 := by
  simp_rw [sub_eq_add_neg, add_pow]
  rw [integral_finsetSum, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_mul_const, integral_mul_const, integral_mul_const, integral_mul_const,
      hmom j (Nat.le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hk)]
  · intro j hj
    exact ((integrable_rate_pow_of_support hs1 j).mul_const _).mul_const _
  · intro j hj
    exact ((integrable_rate_pow_of_support hs0 j).mul_const _).mul_const _

private lemma centered_moment_gap_le {ν0 ν1 : Measure ℝ≥0}
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    {a M : ℝ≥0} (hM : M ≤ a)
    (hs0 : ν0 (Set.Icc (a - M) (a + M)) = 1)
    (hs1 : ν1 (Set.Icc (a - M) (a + M)) = 1) (k : ℕ) :
    |(∫ u, ((u : ℝ) - (a : ℝ)) ^ k ∂ν0) -
        ∫ u, ((u : ℝ) - (a : ℝ)) ^ k ∂ν1| ≤ 2 * (M : ℝ) ^ k := by
  have hbound (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
      (hs : ν (Set.Icc (a - M) (a + M)) = 1) :
      |∫ u, ((u : ℝ) - (a : ℝ)) ^ k ∂ν| ≤ (M : ℝ) ^ k := by
    calc
      abs (∫ u, ((u : ℝ) - (a : ℝ)) ^ k ∂ν) ≤
          ∫ u, |((u : ℝ) - (a : ℝ)) ^ k| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ _u, (M : ℝ) ^ k ∂ν := by
        apply integral_mono_ae
        · exact (integrable_centered_pow_of_support hM hs k).abs
        · fun_prop
        · filter_upwards [ae_mem_Icc_of_mass_one hs] with u hu
          rw [abs_pow]
          exact pow_le_pow_left₀ (by positivity) (abs_sub_center_le_of_mem hM hu) k
      _ = (M : ℝ) ^ k := by simp
  rw [show 2 * (M : ℝ) ^ k = (M : ℝ) ^ k + (M : ℝ) ^ k by ring]
  exact (abs_sub (∫ u, ((u : ℝ) - (a : ℝ)) ^ k ∂ν0)
    (∫ u, ((u : ℝ) - (a : ℝ)) ^ k ∂ν1)).trans
      (add_le_add (hbound ν0 hs0) (hbound ν1 hs1))

private noncomputable def poissonExpansionTerm
    (a u : ℝ≥0) (j k : ℕ) : ℝ :=
  poissonKernelMass a j *
    charlierTerm (a : ℝ) ((u : ℝ) - (a : ℝ)) j k

private lemma poissonExpansionTerm_hasSum {a : ℝ≥0} (ha : 0 < a)
    (u : ℝ≥0) (j : ℕ) :
    HasSum (poissonExpansionTerm a u j) (poissonKernelMass u j) := by
  change HasSum (fun k => Real.exp (-(a : ℝ)) * (a : ℝ) ^ j /
    (j.factorial : ℝ) * charlierTerm (a : ℝ) ((u : ℝ) - (a : ℝ)) j k) _
  have h := (monicCharlier_hasSum (show (a : ℝ) ≠ 0 by positivity)
    ((u : ℝ) - (a : ℝ)) j).mul_left
      (Real.exp (-(a : ℝ)) * (a : ℝ) ^ j / (j.factorial : ℝ))
  have hbase : 1 + ((u : ℝ) - (a : ℝ)) / (a : ℝ) =
      (u : ℝ) / (a : ℝ) := by
    field_simp
    ring
  have hexp : Real.exp (-(a : ℝ)) * Real.exp (-((u : ℝ) - (a : ℝ))) =
      Real.exp (-(u : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hkernel : Real.exp (-(u : ℝ)) * (u : ℝ) ^ j /
      (j.factorial : ℝ) =
      Real.exp (-(a : ℝ)) * (a : ℝ) ^ j / (j.factorial : ℝ) *
        (Real.exp (-((u : ℝ) - (a : ℝ))) *
          (1 + ((u : ℝ) - (a : ℝ)) / (a : ℝ)) ^ j) := by
    rw [hbase, div_pow, ← hexp]
    field_simp
  rw [poissonKernelMass, hkernel]
  exact h

private lemma integrable_poissonExpansionTerm {ν : Measure ℝ≥0}
    [IsProbabilityMeasure ν] {a M : ℝ≥0} (hM : M ≤ a)
    (hs : ν (Set.Icc (a - M) (a + M)) = 1) (j k : ℕ) :
    Integrable (poissonExpansionTerm a · j k) ν := by
  have h := (integrable_centered_pow_of_support hM hs k).const_mul
    (poissonKernelMass a j *
      (monicCharlier (a : ℝ) k j /
        ((a : ℝ) ^ k * (k.factorial : ℝ))))
  convert h using 1
  ext u
  simp only [poissonExpansionTerm, charlierTerm]
  ring

private lemma norm_poissonExpansionTerm_le {a M u : ℝ≥0} (hM : M ≤ a)
    (hu : u ∈ Set.Icc (a - M) (a + M)) (j k : ℕ) :
    ‖poissonExpansionTerm a u j k‖ ≤
      poissonKernelMass a j * ‖charlierTerm (a : ℝ) (M : ℝ) j k‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  simp only [poissonExpansionTerm, charlierTerm, abs_mul, abs_div, abs_pow]
  rw [abs_of_nonneg (show 0 ≤ poissonKernelMass a j by
    dsimp [poissonKernelMass]; positivity)]
  apply mul_le_mul_of_nonneg_left _ (by
    dsimp [poissonKernelMass]
    positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [abs_of_nonneg (by positivity : 0 ≤ (M : ℝ))]
  exact pow_le_pow_left₀ (by positivity) (abs_sub_center_le_of_mem hM hu) k

private lemma summable_integral_norm_poissonExpansionTerm {ν : Measure ℝ≥0}
    [IsProbabilityMeasure ν] {a M : ℝ≥0} (ha : 0 < a) (hM : M ≤ a)
    (hs : ν (Set.Icc (a - M) (a + M)) = 1) (j : ℕ) :
    Summable (fun k => ∫ u, ‖poissonExpansionTerm a u j k‖ ∂ν) := by
  have hsum : Summable (fun k => poissonKernelMass a j *
      ‖charlierTerm (a : ℝ) (M : ℝ) j k‖) :=
    (summable_norm_charlierTerm (show (a : ℝ) ≠ 0 by positivity) (M : ℝ) j).mul_left _
  apply Summable.of_nonneg_of_le
  · intro k
    positivity
  · intro k
    calc
      (∫ u, ‖poissonExpansionTerm a u j k‖ ∂ν) ≤
          ∫ _u, poissonKernelMass a j *
            ‖charlierTerm (a : ℝ) (M : ℝ) j k‖ ∂ν := by
        apply integral_mono_ae
        · exact (integrable_poissonExpansionTerm hM hs j k).norm
        · fun_prop
        · filter_upwards [ae_mem_Icc_of_mass_one hs] with u hu
          exact norm_poissonExpansionTerm_le hM hu j k
      _ = poissonKernelMass a j *
          ‖charlierTerm (a : ℝ) (M : ℝ) j k‖ := by simp
  · exact hsum

private lemma mixturePoint_hasSum {ν : Measure ℝ≥0}
    [IsProbabilityMeasure ν] {a M : ℝ≥0} (ha : 0 < a) (hM : M ≤ a)
    (hs : ν (Set.Icc (a - M) (a + M)) = 1) (j : ℕ) :
    HasSum (fun k => ∫ u, poissonExpansionTerm a u j k ∂ν)
      ((ν.bind poissonMeasure).real {j}) := by
  have h := hasSum_integral_of_summable_integral_norm
    (fun k => integrable_poissonExpansionTerm hM hs j k)
    (summable_integral_norm_poissonExpansionTerm ha hM hs j)
  rw [bind_poisson_real_singleton]
  have hpoint : (∫ u, ∑' k, poissonExpansionTerm a u j k ∂ν) =
      ∫ u, poissonKernelMass u j ∂ν := by
    apply integral_congr_ae
    filter_upwards [] with u
    exact (poissonExpansionTerm_hasSum ha u j).tsum_eq
  rw [← hpoint]
  exact h

private lemma integral_poissonExpansionTerm {ν : Measure ℝ≥0}
    [IsProbabilityMeasure ν] {a M : ℝ≥0} (hM : M ≤ a)
    (hs : ν (Set.Icc (a - M) (a + M)) = 1) (j k : ℕ) :
    (∫ u, poissonExpansionTerm a u j k ∂ν) =
      poissonKernelMass a j *
        (monicCharlier (a : ℝ) k j /
          ((a : ℝ) ^ k * (k.factorial : ℝ))) *
        ∫ u, ((u : ℝ) - (a : ℝ)) ^ k ∂ν := by
  rw [show (fun u => poissonExpansionTerm a u j k) =
      fun u : ℝ≥0 => (poissonKernelMass a j *
        (monicCharlier (a : ℝ) k j /
          ((a : ℝ) ^ k * (k.factorial : ℝ)))) *
            ((u : ℝ) - (a : ℝ)) ^ k by
    funext u
    simp only [poissonExpansionTerm, charlierTerm]
    ring]
  rw [integral_const_mul]

private lemma abs_integral_poissonExpansionTerm_sub_le
    {ν0 ν1 : Measure ℝ≥0}
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    {a M : ℝ≥0} (ha : 0 < a) (hM : M ≤ a)
    (hs0 : ν0 (Set.Icc (a - M) (a + M)) = 1)
    (hs1 : ν1 (Set.Icc (a - M) (a + M)) = 1) (j k : ℕ) :
    |(∫ u, poissonExpansionTerm a u j k ∂ν0) -
        ∫ u, poissonExpansionTerm a u j k ∂ν1| ≤
      2 * poissonKernelMass a j * |monicCharlier (a : ℝ) k j| /
          ((a : ℝ) ^ k * (k.factorial : ℝ)) * (M : ℝ) ^ k := by
  rw [integral_poissonExpansionTerm hM hs0,
    integral_poissonExpansionTerm hM hs1]
  rw [← mul_sub]
  rw [abs_mul]
  have hgap := centered_moment_gap_le hM hs0 hs1 k
  have hkernel : 0 ≤ poissonKernelMass a j := by
    dsimp [poissonKernelMass]
    positivity
  have hden : 0 < (a : ℝ) ^ k * (k.factorial : ℝ) := by positivity
  rw [abs_mul, abs_of_nonneg hkernel, abs_div, abs_of_pos hden]
  calc
    poissonKernelMass a j *
          (|monicCharlier (a : ℝ) k j| /
            ((a : ℝ) ^ k * (k.factorial : ℝ))) *
        |(∫ u, ((u : ℝ) - (a : ℝ)) ^ k ∂ν0) -
          ∫ u, ((u : ℝ) - (a : ℝ)) ^ k ∂ν1| ≤
        poissonKernelMass a j *
          (|monicCharlier (a : ℝ) k j| /
            ((a : ℝ) ^ k * (k.factorial : ℝ))) *
          (2 * (M : ℝ) ^ k) := by gcongr
    _ = 2 * poissonKernelMass a j * |monicCharlier (a : ℝ) k j| /
          ((a : ℝ) ^ k * (k.factorial : ℝ)) * (M : ℝ) ^ k := by ring

private lemma integral_poissonExpansionTerm_sub_eq_zero
    {ν0 ν1 : Measure ℝ≥0}
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    {a M : ℝ≥0} {L : ℕ} (hM : M ≤ a)
    (hs0 : ν0 (Set.Icc (a - M) (a + M)) = 1)
    (hs1 : ν1 (Set.Icc (a - M) (a + M)) = 1)
    (hmom : ∀ k ≤ L,
      (∫ u, (u : ℝ) ^ k ∂ν0) = ∫ u, (u : ℝ) ^ k ∂ν1)
    (j : ℕ) {k : ℕ} (hk : k ≤ L) :
    (∫ u, poissonExpansionTerm a u j k ∂ν0) -
        ∫ u, poissonExpansionTerm a u j k ∂ν1 = 0 := by
  rw [integral_poissonExpansionTerm hM hs0,
    integral_poissonExpansionTerm hM hs1, centered_moments_eq hM hs0 hs1 hmom hk]
  ring

private lemma abs_integral_poissonExpansionTerm_sub_le_normTerm
    {ν0 ν1 : Measure ℝ≥0}
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    {a M : ℝ≥0} (ha : 0 < a) (hM : M ≤ a)
    (hs0 : ν0 (Set.Icc (a - M) (a + M)) = 1)
    (hs1 : ν1 (Set.Icc (a - M) (a + M)) = 1) (j k : ℕ) :
    |(∫ u, poissonExpansionTerm a u j k ∂ν0) -
        ∫ u, poissonExpansionTerm a u j k ∂ν1| ≤
      2 * poissonKernelMass a j *
        ‖charlierTerm (a : ℝ) (M : ℝ) j k‖ := by
  have h := abs_integral_poissonExpansionTerm_sub_le ha hM hs0 hs1 j k
  rw [Real.norm_eq_abs, charlierTerm, abs_mul, abs_div, abs_pow]
  have hden : 0 < (a : ℝ) ^ k * (k.factorial : ℝ) := by positivity
  rw [abs_of_pos hden, abs_of_nonneg (by positivity : 0 ≤ (M : ℝ))]
  convert h using 1 <;> ring

private lemma pointMassDiff_le_tail
    {ν0 ν1 : Measure ℝ≥0}
    [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    {a M : ℝ≥0} {L : ℕ} (ha : 0 < a) (hM : M ≤ a)
    (hs0 : ν0 (Set.Icc (a - M) (a + M)) = 1)
    (hs1 : ν1 (Set.Icc (a - M) (a + M)) = 1)
    (hmom : ∀ k ≤ L,
      (∫ u, (u : ℝ) ^ k ∂ν0) = ∫ u, (u : ℝ) ^ k ∂ν1)
    (j : ℕ) :
    |(ν0.bind poissonMeasure).real {j} -
        (ν1.bind poissonMeasure).real {j}| ≤
      ∑' n, 2 * poissonKernelMass a j *
        ‖charlierTerm (a : ℝ) (M : ℝ) j (n + (L + 1))‖ := by
  let d : ℕ → ℝ := fun k =>
    (∫ u, poissonExpansionTerm a u j k ∂ν0) -
      ∫ u, poissonExpansionTerm a u j k ∂ν1
  let b : ℕ → ℝ := fun k => 2 * poissonKernelMass a j *
    ‖charlierTerm (a : ℝ) (M : ℝ) j k‖
  have hd : HasSum d ((ν0.bind poissonMeasure).real {j} -
      (ν1.bind poissonMeasure).real {j}) :=
    (mixturePoint_hasSum ha hM hs0 j).sub
      (mixturePoint_hasSum ha hM hs1 j)
  have hzero : ∀ k < L + 1, d k = 0 := by
    intro k hk
    exact integral_poissonExpansionTerm_sub_eq_zero hM hs0 hs1 hmom j
      (Nat.lt_succ_iff.mp hk)
  have hprefix : ∑ k ∈ Finset.range (L + 1), d k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact hzero k (Finset.mem_range.mp hk)
  have htail : HasSum (fun n => d (n + (L + 1)))
      ((ν0.bind poissonMeasure).real {j} -
        (ν1.bind poissonMeasure).real {j}) := by
    have h := (hasSum_nat_add_iff' (f := d) (L + 1)).2 hd
    simpa [hprefix] using h
  have hb : Summable b := by
    have h := ((summable_norm_charlierTerm (show (a : ℝ) ≠ 0 by positivity)
      (M : ℝ) j).mul_left (poissonKernelMass a j)).mul_left 2
    apply h.congr
    intro k
    dsimp [b]
    ring
  have hinj : Function.Injective (fun n : ℕ => n + (L + 1)) :=
    by intro x y hxy; exact Nat.add_right_cancel hxy
  have hbshift : Summable (fun n => b (n + (L + 1))) := by
    change Summable (b ∘ fun n => n + (L + 1))
    exact hb.comp_injective hinj
  have hdnorm : Summable (fun n => ‖d (n + (L + 1))‖) := by
    have hdshift : Summable (fun n => d (n + (L + 1))) := htail.summable
    exact hdshift.norm
  calc
    |(ν0.bind poissonMeasure).real {j} -
        (ν1.bind poissonMeasure).real {j}| =
        ‖∑' n, d (n + (L + 1))‖ := by
          rw [htail.tsum_eq, Real.norm_eq_abs]
    _ ≤ ∑' n, ‖d (n + (L + 1))‖ := norm_tsum_le_tsum_norm hdnorm
    _ ≤ ∑' n, b (n + (L + 1)) := by
      apply hdnorm.tsum_le_tsum
      · intro n
        exact abs_integral_poissonExpansionTerm_sub_le_normTerm
          ha hM hs0 hs1 j (n + (L + 1))
      · exact hbshift
    _ = ∑' n, 2 * poissonKernelMass a j *
        ‖charlierTerm (a : ℝ) (M : ℝ) j (n + (L + 1))‖ := rfl

private noncomputable def charlierLayer (a M : ℝ≥0) (k : ℕ) : ℝ :=
  ∑' j, poissonKernelMass a j *
    ‖charlierTerm (a : ℝ) (M : ℝ) j k‖

private lemma summable_poissonKernelMass_mul_abs_monicCharlier
    (a : ℝ≥0) (k : ℕ) :
    Summable (fun j => poissonKernelMass a j *
      |monicCharlier (a : ℝ) k j|) := by
  have hg : Integrable (fun j : ℕ => |monicCharlier (a : ℝ) k j|)
      (poissonMeasure a) := by
    have h := integrable_monicCharlier_mul a k 0
    simpa [monicCharlier, abs_mul] using h.abs
  have h := (hasSum_integral_poissonMeasure hg).summable
  apply h.congr
  intro j
  simp only [smul_eq_mul, poissonKernelMass]

private lemma charlierLayer_eq (a M : ℝ≥0) (k : ℕ) :
    charlierLayer a M k =
      (M : ℝ) ^ k / ((a : ℝ) ^ k * (k.factorial : ℝ)) *
        ∫ j, |monicCharlier (a : ℝ) k j| ∂poissonMeasure a := by
  let c : ℝ := (M : ℝ) ^ k /
    ((a : ℝ) ^ k * (k.factorial : ℝ))
  have hg : Integrable (fun j : ℕ => |monicCharlier (a : ℝ) k j|)
      (poissonMeasure a) := by
    have h := integrable_monicCharlier_mul a k 0
    simpa [monicCharlier, abs_mul] using h.abs
  rw [charlierLayer, integral_poissonMeasure, ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [Real.norm_eq_abs, charlierTerm, abs_mul, abs_div, abs_pow,
    abs_of_nonneg (by positivity : 0 ≤ (M : ℝ))]
  simp only [smul_eq_mul, poissonKernelMass]
  have hnonneg : 0 ≤ (a : ℝ) ^ k * (k.factorial : ℝ) := by positivity
  rw [abs_of_nonneg hnonneg]
  ring

private lemma charlierLayer_le_sqrt (a M : ℝ≥0) (k : ℕ) :
    charlierLayer a M k ≤
      (M : ℝ) ^ k / ((a : ℝ) ^ k * (k.factorial : ℝ)) *
        Real.sqrt ((a : ℝ) ^ k * (k.factorial : ℝ)) := by
  rw [charlierLayer_eq]
  gcongr
  exact integral_abs_monicCharlier_le_sqrt a k

private lemma sqrt_pow_nonneg (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    Real.sqrt (x ^ k) = Real.sqrt x ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hx k), ih, pow_succ]

private lemma pow_div_exp_le_factorial (k : ℕ) (hk : 1 ≤ k) :
    ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := by
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hkreal : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith [Real.pi_gt_three]
  exact (le_mul_of_one_le_left (by positivity) hsqrt).trans
    (Stirling.le_factorial_stirling k)

private lemma charlierLayer_le_exp_ratio_pow {a M : ℝ≥0} (ha : 0 < a)
    (k : ℕ) (hk : 1 ≤ k) :
    charlierLayer a M k ≤
      (Real.exp 1 * (M : ℝ) /
        Real.sqrt ((a : ℝ) * (k : ℝ))) ^ k := by
  apply (charlierLayer_le_sqrt a M k).trans
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hfactup : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
    exact_mod_cast Nat.factorial_le_pow k
  have hroot : Real.sqrt ((a : ℝ) ^ k * (k.factorial : ℝ)) ≤
      Real.sqrt ((a : ℝ) * (k : ℝ)) ^ k := by
    calc
      Real.sqrt ((a : ℝ) ^ k * (k.factorial : ℝ)) ≤
          Real.sqrt ((a : ℝ) ^ k * (k : ℝ) ^ k) := by gcongr
      _ = Real.sqrt (((a : ℝ) * (k : ℝ)) ^ k) := by congr 1; ring
      _ = _ := sqrt_pow_nonneg _ (by positivity) k
  calc
    (M : ℝ) ^ k / ((a : ℝ) ^ k * (k.factorial : ℝ)) *
        Real.sqrt ((a : ℝ) ^ k * (k.factorial : ℝ)) ≤
      (M : ℝ) ^ k / ((a : ℝ) ^ k * (k.factorial : ℝ)) *
        Real.sqrt ((a : ℝ) * (k : ℝ)) ^ k := by gcongr
    _ ≤ (Real.exp 1 * (M : ℝ) /
        Real.sqrt ((a : ℝ) * (k : ℝ))) ^ k := by
      rw [mul_div_assoc, mul_pow, div_pow]
      have hspos : 0 < Real.sqrt ((a : ℝ) * (k : ℝ)) :=
        Real.sqrt_pos.2 (by positivity)
      have hfact := pow_div_exp_le_factorial k hk
      rw [div_pow] at hfact
      have hepos : 0 < Real.exp 1 ^ k := by positivity
      have hcross : (k : ℝ) ^ k ≤
          (k.factorial : ℝ) * Real.exp 1 ^ k := by
        exact (div_le_iff₀ hepos).mp (by simpa [mul_comm] using hfact)
      have hsquare : Real.sqrt ((a : ℝ) * (k : ℝ)) ^ k *
          Real.sqrt ((a : ℝ) * (k : ℝ)) ^ k =
            (a : ℝ) ^ k * (k : ℝ) ^ k := by
        rw [← mul_pow, ← pow_two, Real.sq_sqrt (by positivity), mul_pow]
      field_simp
      nlinarith [mul_le_mul_of_nonneg_left hcross
        (pow_nonneg (show 0 ≤ (a : ℝ) by positivity) k),
        pow_nonneg (show 0 ≤ (M : ℝ) by positivity) k, hsquare]

private lemma charlierLayer_nonneg (a M : ℝ≥0) (k : ℕ) :
    0 ≤ charlierLayer a M k := by
  apply tsum_nonneg
  intro j
  exact mul_nonneg (by dsimp [poissonKernelMass]; positivity) (norm_nonneg _)

private lemma sum_charlierLayer_tail_le {a M : ℝ≥0} {L : ℕ}
    (ha : 0 < a)
    (hdegree : ((2 * Real.exp 1 * (M : ℝ)) ^ 2) / (a : ℝ) ≤
      (L + 1 : ℝ)) :
    (∑' n, charlierLayer a M (n + (L + 1))) ≤
      2 * ((Real.exp 1 * (M : ℝ)) /
        Real.sqrt ((a : ℝ) * (L + 1 : ℝ))) ^ (L + 1) := by
  let q : ℝ := (Real.exp 1 * (M : ℝ)) /
    Real.sqrt ((a : ℝ) * (L + 1 : ℝ))
  have hLpos : 0 < (L + 1 : ℝ) := by positivity
  have hspos : 0 < Real.sqrt ((a : ℝ) * (L + 1 : ℝ)) :=
    Real.sqrt_pos.2 (by positivity)
  have hqnonneg : 0 ≤ q := by dsimp [q]; positivity
  have hdegree' : (2 * Real.exp 1 * (M : ℝ)) ^ 2 ≤
      (L + 1 : ℝ) * (a : ℝ) :=
    (div_le_iff₀ (show 0 < (a : ℝ) by positivity)).mp hdegree
  have hsquare : Real.sqrt ((a : ℝ) * (L + 1 : ℝ)) ^ 2 =
      (a : ℝ) * (L + 1 : ℝ) := Real.sq_sqrt (by positivity)
  have hqhalf : q ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hspos).2
    nlinarith [hdegree']
  have hqone : q < 1 := lt_of_le_of_lt hqhalf (by norm_num)
  have hlayer (n : ℕ) : charlierLayer a M (n + (L + 1)) ≤
      q ^ (n + (L + 1)) := by
    apply (charlierLayer_le_exp_ratio_pow ha _ (by omega)).trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [q]
    gcongr
    have hnat : (L + 1 : ℕ) ≤ n + (L + 1) := by omega
    have hreal : (L + 1 : ℝ) ≤ (n + (L + 1) : ℕ) := by exact_mod_cast hnat
    exact hreal
  have hgeom : Summable (fun n : ℕ => q ^ (n + (L + 1))) := by
    have h := (summable_geometric_of_lt_one hqnonneg hqone).mul_left (q ^ (L + 1))
    apply h.congr
    intro n
    rw [pow_add]
    ring
  have hlayersum : Summable (fun n => charlierLayer a M (n + (L + 1))) := by
    apply Summable.of_nonneg_of_le
    · intro n
      exact charlierLayer_nonneg a M _
    · exact hlayer
    · exact hgeom
  calc
    (∑' n, charlierLayer a M (n + (L + 1))) ≤
        ∑' n, q ^ (n + (L + 1)) :=
      hlayersum.tsum_le_tsum hlayer hgeom
    _ = q ^ (L + 1) * (1 - q)⁻¹ := by
      rw [show (fun n : ℕ => q ^ (n + (L + 1))) =
          fun n => q ^ (L + 1) * q ^ n by
        funext n
        rw [pow_add]
        ring]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hqnonneg hqone]
    _ ≤ 2 * q ^ (L + 1) := by
      have hinv : (1 - q)⁻¹ ≤ (2 : ℝ) := by
        apply (inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 - q)).2
        nlinarith
      nlinarith [pow_nonneg hqnonneg (L + 1)]
    _ = 2 * ((Real.exp 1 * (M : ℝ)) /
        Real.sqrt ((a : ℝ) * (L + 1 : ℝ))) ^ (L + 1) := rfl

private lemma summable_charlierLayer_terms (a M : ℝ≥0) (k : ℕ) :
    Summable (fun j => poissonKernelMass a j *
      ‖charlierTerm (a : ℝ) (M : ℝ) j k‖) := by
  let c : ℝ := (M : ℝ) ^ k /
    ((a : ℝ) ^ k * (k.factorial : ℝ))
  have h := (summable_poissonKernelMass_mul_abs_monicCharlier a k).mul_left c
  apply h.congr
  intro j
  rw [Real.norm_eq_abs, charlierTerm, abs_mul, abs_div, abs_pow,
    abs_of_nonneg (by positivity : 0 ≤ (M : ℝ))]
  have hnonneg : 0 ≤ (a : ℝ) ^ k * (k.factorial : ℝ) := by positivity
  rw [abs_of_nonneg hnonneg]
  dsimp [c]
  ring

private lemma summable_charlierLayer_tail {a M : ℝ≥0} {L : ℕ}
    (ha : 0 < a)
    (hdegree : ((2 * Real.exp 1 * (M : ℝ)) ^ 2) / (a : ℝ) ≤
      (L + 1 : ℝ)) :
    Summable (fun n => charlierLayer a M (n + (L + 1))) := by
  let q : ℝ := (Real.exp 1 * (M : ℝ)) /
    Real.sqrt ((a : ℝ) * (L + 1 : ℝ))
  have hspos : 0 < Real.sqrt ((a : ℝ) * (L + 1 : ℝ)) :=
    Real.sqrt_pos.2 (by positivity)
  have hqnonneg : 0 ≤ q := by dsimp [q]; positivity
  have hdegree' : (2 * Real.exp 1 * (M : ℝ)) ^ 2 ≤
      (L + 1 : ℝ) * (a : ℝ) :=
    (div_le_iff₀ (show 0 < (a : ℝ) by positivity)).mp hdegree
  have hsquare : Real.sqrt ((a : ℝ) * (L + 1 : ℝ)) ^ 2 =
      (a : ℝ) * (L + 1 : ℝ) := Real.sq_sqrt (by positivity)
  have hqhalf : q ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hspos).2
    nlinarith [hdegree', hsquare]
  have hqone : q < 1 := lt_of_le_of_lt hqhalf (by norm_num)
  have hlayer (n : ℕ) : charlierLayer a M (n + (L + 1)) ≤
      q ^ (n + (L + 1)) := by
    apply (charlierLayer_le_exp_ratio_pow ha _ (by omega)).trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [q]
    gcongr
    have hnat : (L + 1 : ℕ) ≤ n + (L + 1) := by omega
    exact_mod_cast hnat
  have hgeom : Summable (fun n : ℕ => q ^ (n + (L + 1))) := by
    have h := (summable_geometric_of_lt_one hqnonneg hqone).mul_left (q ^ (L + 1))
    apply h.congr
    intro n
    rw [pow_add]
    ring
  exact Summable.of_nonneg_of_le
    (fun n => charlierLayer_nonneg a M _) hlayer hgeom

private theorem tvDist_bind_poisson_le_of_momentMatch_core
    {ν0 ν1 : Measure ℝ≥0} [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    {a M : ℝ≥0} {L : ℕ}
    (ha : 0 < a) (hM : M ≤ a)
    (hs0 : ν0 (Set.Icc (a - M) (a + M)) = 1)
    (hs1 : ν1 (Set.Icc (a - M) (a + M)) = 1)
    (hmom : ∀ k ≤ L,
      (∫ x, (x : ℝ) ^ k ∂ν0) = ∫ x, (x : ℝ) ^ k ∂ν1)
    (hdegree : ((2 * Real.exp 1 * (M : ℝ)) ^ 2) / (a : ℝ) ≤ (L + 1 : ℝ)) :
    Causalean.Stat.tvDist (ν0.bind poissonMeasure) (ν1.bind poissonMeasure) ≤
      2 * ((Real.exp 1 * (M : ℝ)) /
        Real.sqrt ((a : ℝ) * (L + 1 : ℝ))) ^ (L + 1) := by
  let F : ℕ → ℕ → ℝ := fun n j => poissonKernelMass a j *
    ‖charlierTerm (a : ℝ) (M : ℝ) j (n + (L + 1))‖
  have hFnonneg : ∀ p : ℕ × ℕ, 0 ≤ Function.uncurry F p := by
    intro p
    exact mul_nonneg (by dsimp [poissonKernelMass]; positivity) (norm_nonneg _)
  have hFrow : ∀ n, Summable (F n) := by
    intro n
    exact summable_charlierLayer_terms a M (n + (L + 1))
  have hrows : Summable (fun n => ∑' j, F n j) := by
    simpa only [F, charlierLayer] using
      summable_charlierLayer_tail ha hdegree
  have hFprod : Summable (Function.uncurry F) :=
    (summable_prod_of_nonneg hFnonneg).2 ⟨hFrow, hrows⟩
  have hFswap : Summable (Function.uncurry fun j n => F n j) := by
    have h := hFprod.comp_injective (Equiv.prodComm ℕ ℕ).injective
    apply h.congr
    rintro ⟨j, n⟩
    rfl
  have hcols : Summable (fun j => ∑' n, F n j) := hFswap.prod
  have hupp : Summable (fun j => ∑' n, 2 * F n j) := by
    have h := hcols.mul_left 2
    apply h.congr
    intro j
    change 2 * (∑' n, F n j) = ∑' n, 2 * F n j
    exact tsum_mul_left.symm
  have hpoint (j : ℕ) :
      |(ν0.bind poissonMeasure).real {j} -
        (ν1.bind poissonMeasure).real {j}| ≤ ∑' n, 2 * F n j := by
    simpa only [F, mul_assoc] using pointMassDiff_le_tail ha hM hs0 hs1 hmom j
  have hdiff : Summable (fun j => |(ν0.bind poissonMeasure).real {j} -
      (ν1.bind poissonMeasure).real {j}|) := by
    apply Summable.of_nonneg_of_le
    · exact fun _ => abs_nonneg _
    · exact hpoint
    · exact hupp
  letI : IsProbabilityMeasure (ν0.bind poissonMeasure) := by
    apply isProbabilityMeasure_bind measurable_poissonMeasure.aemeasurable
    exact Filter.Eventually.of_forall fun _ => inferInstance
  letI : IsProbabilityMeasure (ν1.bind poissonMeasure) := by
    apply isProbabilityMeasure_bind measurable_poissonMeasure.aemeasurable
    exact Filter.Eventually.of_forall fun _ => inferInstance
  apply (tvDist_le_half_tsum_abs_singleton
    (ν0.bind poissonMeasure) (ν1.bind poissonMeasure)).trans
  calc
    (1 / 2 : ℝ) * ∑' j, |(ν0.bind poissonMeasure).real {j} -
        (ν1.bind poissonMeasure).real {j}| ≤
        (1 / 2 : ℝ) * ∑' j, ∑' n, 2 * F n j := by
      exact mul_le_mul_of_nonneg_left
        (hdiff.tsum_le_tsum hpoint hupp) (by norm_num)
    _ = ∑' n, charlierLayer a M (n + (L + 1)) := by
      rw [show (fun j => ∑' n, 2 * F n j) =
          fun j => 2 * ∑' n, F n j by
        funext j
        rw [tsum_mul_left]]
      rw [tsum_mul_left]
      have hcancel : (1 / 2 : ℝ) *
          (2 * ∑' j, ∑' n, F n j) = ∑' j, ∑' n, F n j := by ring
      rw [hcancel, hFprod.tsum_comm]
      apply tsum_congr
      intro n
      rfl
    _ ≤ 2 * ((Real.exp 1 * (M : ℝ)) /
        Real.sqrt ((a : ℝ) * (L + 1 : ℝ))) ^ (L + 1) :=
      sum_charlierLayer_tail_le ha hdegree

/-- Total variation bound for moment-matched mixtures of Poisson laws. -/
theorem tvDist_bind_poisson_le_of_momentMatch
    {ν0 ν1 : Measure ℝ≥0} [IsProbabilityMeasure ν0] [IsProbabilityMeasure ν1]
    {a M : ℝ≥0} {L : ℕ}
    (ha : 0 < a) (hM : M ≤ a)
    (hs0 : ν0 (Set.Icc (a - M) (a + M)) = 1)
    (hs1 : ν1 (Set.Icc (a - M) (a + M)) = 1)
    (hmom : ∀ k ≤ L,
      (∫ x, (x : ℝ) ^ k ∂ν0) = ∫ x, (x : ℝ) ^ k ∂ν1)
    (hdegree : ((2 * Real.exp 1 * (M : ℝ)) ^ 2) / (a : ℝ) ≤ (L + 1 : ℝ)) :
    Causalean.Stat.tvDist (ν0.bind poissonMeasure) (ν1.bind poissonMeasure) ≤
      2 * ((Real.exp 1 * (M : ℝ)) /
        Real.sqrt ((a : ℝ) * (L + 1 : ℝ))) ^ (L + 1) := by
  by_cases hzero : M = 0
  · subst M
    exact tvDist_bind_poisson_le_of_momentMatch_core ha hM hs0 hs1 hmom hdegree
  · exact tvDist_bind_poisson_le_of_momentMatch_core ha hM hs0 hs1 hmom hdegree

end CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower

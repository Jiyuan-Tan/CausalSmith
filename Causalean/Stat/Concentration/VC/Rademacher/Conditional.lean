module
public import Causalean.Stat.Concentration.VC.Rademacher.EntropyIntegral

/-!
# Conditional Rademacher and empirical-radius bounds

This file connects absolute and signed empirical Rademacher complexities,
proves the conditional entropy-integral estimate used by the VC maximal
bound, and develops measurability and deterministic bounds for the empirical
`L²` radius. The entropy integration and final variance-adaptive theorem live
in the sibling files.
-/

@[expose] public section

namespace Causalean.Stat.Concentration

open MeasureTheory

universe u v

variable {𝒳 : Type u} [MeasurableSpace 𝒳] {ι : Type v}


/-- If [the class contains a zero function](hyp:hzero), [the envelope level is
nonnegative](hyp:hM0), and [every function is bounded in absolute value by the
envelope](hyp:hM), then [its empirical Rademacher complexity is bounded by the sum of the
unsigned-supremum complexities of the class and its negation](goal). -/
lemma empiricalRademacherComplexity_le_signed_add_neg_of_zero
    [Nonempty ι]
    (H : ι → 𝒳 → ℝ) (i₀ : ι) (hzero : ∀ x, H i₀ x = 0)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i x, |H i x| ≤ M)
    (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n H S ≤
      empiricalRademacherComplexity_without_abs n H S +
        empiricalRademacherComplexity_without_abs n (fun i x => -H i x) S := by
  classical
  unfold empiricalRademacherComplexity empiricalRademacherComplexity_without_abs
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ => ?_) (by positivity)
  let z : ι → ℝ := fun i =>
    (n : ℝ)⁻¹ * ∑ k : Fin n, (τ k : ℝ) * H i (S k)
  have hz0 : z i₀ = 0 := by simp [z, hzero]
  have hbddAbs : BddAbove (Set.range fun i => |z i|) := by
    simpa [z] using absInner_bddAbove H hM0 hM n S τ
  have hbdd : BddAbove (Set.range z) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact (le_abs_self _).trans (absInner_le_of_bound H hM0 hM n S τ i)
  have hbddNeg : BddAbove (Set.range fun i => -z i) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact (neg_le_abs _).trans (absInner_le_of_bound H hM0 hM n S τ i)
  have hsup0 : 0 ≤ ⨆ i, z i := by
    rw [← hz0]
    exact le_ciSup hbdd i₀
  have hsupNeg0 : 0 ≤ ⨆ i, -z i := by
    rw [← show -z i₀ = 0 by rw [hz0]; simp]
    exact le_ciSup hbddNeg i₀
  have hpoint : (⨆ i, |z i|) ≤ (⨆ i, z i) + (⨆ i, -z i) := by
    refine ciSup_le fun i => ?_
    by_cases hi : 0 ≤ z i
    · rw [abs_of_nonneg hi]
      linarith [le_ciSup hbdd i]
    · rw [abs_of_neg (lt_of_not_ge hi)]
      linarith [le_ciSup hbddNeg i]
  have hneg : (⨆ i, -z i) =
      ⨆ i, (n : ℝ)⁻¹ * ∑ k : Fin n, (τ k : ℝ) * (-H i (S k)) := by
    refine iSup_congr fun i => ?_
    calc
      -z i = (n : ℝ)⁻¹ * (-(∑ k : Fin n, (τ k : ℝ) * H i (S k))) := by
        simp only [z]
        ring
      _ = (n : ℝ)⁻¹ * ∑ k : Fin n, -((τ k : ℝ) * H i (S k)) := by
        rw [Finset.sum_neg_distrib]
      _ = (n : ℝ)⁻¹ * ∑ k : Fin n, (τ k : ℝ) * (-H i (S k)) := by
        congr 1
        refine Finset.sum_congr rfl fun k _ => by ring
  simpa [z, hneg] using hpoint

/-- If [the sample size is positive](hyp:hn), then [the empirical Rademacher complexity of a
constant-indexed function class is at most twice the function's empirical L2 norm divided by the
square root of the sample size](goal). -/
lemma constantClass_empiricalRademacher_le
    [Nonempty ι] (g : 𝒳 → ℝ) {n : ℕ} (hn : 0 < n) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (fun _i : ι => g) S ≤
      2 * empiricalNorm S g / Real.sqrt (n : ℝ) := by
  classical
  let H : Unit → 𝒳 → ℝ := fun _ => g
  have hradius : ∀ i ∈ (Finset.univ : Finset Unit),
      Real.sqrt (∑ k : Fin n, ((n : ℝ)⁻¹ * |H i (S k)|) ^ 2) ≤
        empiricalNorm S g / Real.sqrt (n : ℝ) := by
    intro i hi
    exact (sqrt_sum_inv_abs_sq_eq_empiricalNorm_div_sqrt hn S g).le
  have hmass := empiricalRademacher_withAbs_finiteClass_le hn H S
    (Finset.univ : Finset Unit) (by simp) (empiricalNorm S g / Real.sqrt (n : ℝ)) hradius
  rw [empiricalRademacherComplexity_F_on_univ_eq] at hmass
  have hlog2 : Real.sqrt (2 * Real.log (2 * ((Finset.univ : Finset Unit).card : ℝ))) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · simp only [Finset.card_univ, Fintype.card_unit, Nat.cast_one, mul_one]
      nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hnonneg : 0 ≤ empiricalNorm S g / Real.sqrt (n : ℝ) :=
    div_nonneg (by simp only [causal_defs_simps]; positivity) (Real.sqrt_nonneg _)
  have hunit : empiricalRademacherComplexity n H S =
      empiricalRademacherComplexity n (fun _i : ι => g) S := by
    simp only [causal_defs_simps]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp [H, hn.ne']
  rw [← hunit]
  exact hmass.trans (by
    calc
      _ ≤ (empiricalNorm S g / Real.sqrt (n : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left hlog2 hnonneg
      _ = _ := by ring)

/-- For [a measurable observation space, nonempty function index set, and function
class](hyp:𝒳,ι,F), [an envelope, entropy cutoff, covering constant, entropy exponent,
and empirical radius](hyp:U,σ,A,p,R), if [the cutoff is positive and below the
envelope](hyp:hσ,hσU), [the covering constant and exponent satisfy their lower
bounds](hyp:hA,hp), [every function is measurable](hyp:hmeas), [the envelope bounds every
function](hyp:henvelope), and [the class has polynomial empirical covering numbers](hyp:hcover),
then for [a positive sample size and realized sample](hyp:n,hn,S), [a uniform empirical-radius
bound](hyp:hR), [positive radius](hyp:hR0), and [radius below the envelope](hyp:hRU), [the
conditional empirical Rademacher complexity obeys the stated localized entropy bound](goal). -/
lemma empiricalRademacher_conditional_le
    [Nonempty ι]
    (F : ι → 𝒳 → ℝ) {U σ A p R : ℝ}
    (hσ : 0 < σ) (hσU : σ < U) (hA : Real.exp 1 ≤ A) (hp : 1 ≤ p)
    (hmeas : ∀ i, Measurable (F i))
    (henvelope : ∀ i x, |F i x| ≤ U)
    (hcover : HasPolynomialEmpiricalL2Cover F U A p)
    {n : ℕ} (hn : 0 < n) (S : Fin n → 𝒳)
    (hR : ∀ i, empiricalNorm S (F i) ≤ R) (hR0 : 0 < R) (hRU : R ≤ U) :
    empiricalRademacherComplexity n F S ≤
      26 / Real.sqrt (n : ℝ) * Real.sqrt (p * vcMaximalLog A U σ) * (R + σ) := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  let H := anchoredClass F i₀
  have hU : 0 < U := hσ.trans hσU
  have hU0 : 0 ≤ U := hU.le
  have hHmeas : ∀ i, Measurable (H i) := anchoredClass_measurable F i₀ hmeas
  have hHenv : ∀ i x, |H i x| ≤ 2 * U := by
    intro i x
    exact (abs_sub (F i x) (F i₀ x)).trans (by linarith [henvelope i x, henvelope i₀ x])
  have hHnorm : ∀ i, empiricalNorm S (H i) ≤ 2 * R :=
    empiricalNorm_anchored_le F i₀ S hR
  have hHcover : HasPolynomialEmpiricalL2Cover H U A p := by
    change HasPolynomialEmpiricalL2Cover (anchoredClass F i₀) U A p
    exact hcover.anchoredClass i₀ hmeas
  have htot := hHcover.totallyBounded hHmeas hU S hn
  have hnegCover : HasPolynomialEmpiricalL2Cover (fun i x => -H i x) U A p := by
    exact hHcover.neg hHmeas
  have hnegMeas : ∀ i, Measurable (fun x => -H i x) := fun i => (hHmeas i).neg
  have htotNeg := hnegCover.totallyBounded hnegMeas hU S hn
  have hHsigned :
      empiricalRademacherComplexity_without_abs n H S +
          empiricalRademacherComplexity_without_abs n (fun i x => -H i x) S ≤
        24 / Real.sqrt (n : ℝ) *
          (R * Real.sqrt (p * vcMaximalLog A U σ) + σ * Real.sqrt p) := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    let ε := min (R / 2) (δ / 8)
    have hε : 0 < ε := lt_min (by positivity) (by positivity)
    have hεR : ε ≤ R := (min_le_left _ _).trans (by linarith)
    have hεltR : ε < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hdudley := dudley_entropy_integral_bound (F := H) hε htot hn hHnorm (by
      simpa using hεltR)
    have hnegNorm : ∀ i, empiricalNorm S (fun x => -H i x) ≤ 2 * R := by
      intro i
      simpa [empiricalNorm] using hHnorm i
    have hdudleyNeg := dudley_entropy_integral_bound (F := fun i x => -H i x)
      hε htotNeg hn hnegNorm (by simpa using hεltR)
    have hdudley' := hdudley
    have hdudleyNeg' := hdudleyNeg
    simp only [show (2 * R) / 2 = R by ring] at hdudley' hdudleyNeg'
    have hint := polynomialCover_entropyIntegral_le hHcover hHmeas hU hσ hσU
      hA hp S hn hε hεR hRU
    have hintNeg := polynomialCover_entropyIntegral_le hnegCover hnegMeas hU hσ hσU
      hA hp S hn hε hεR hRU
    have hint' : (∫ x in ε..R,
        Real.sqrt (Real.log (coveringNumber' htot x))) ≤
          R * Real.sqrt (p * vcMaximalLog A U σ) + σ * Real.sqrt p := by
      simpa [htot] using hint
    have hintNeg' : (∫ x in ε..R,
        Real.sqrt (Real.log (coveringNumber' htotNeg x))) ≤
          R * Real.sqrt (p * vcMaximalLog A U σ) + σ * Real.sqrt p := by
      simpa [htotNeg] using hintNeg
    have hεsmall : 8 * ε ≤ δ := by
      dsimp [ε]
      have := min_le_right (R / 2) (δ / 8)
      linarith
    exact (add_le_add hdudley' hdudleyNeg').trans (by
        have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
        have hdiv0 : 0 ≤ 12 / Real.sqrt (n : ℝ) := div_nonneg (by norm_num) hsqrt0
        have hmul1 := mul_le_mul_of_nonneg_left hint' hdiv0
        have hmul2 := mul_le_mul_of_nonneg_left hintNeg' hdiv0
        have hcoef : 24 / Real.sqrt (n : ℝ) = 2 * (12 / Real.sqrt (n : ℝ)) := by ring
        calc
          (4 * ε + 12 / Real.sqrt (n : ℝ) *
                (∫ x in ε..R, Real.sqrt (Real.log (coveringNumber' htot x)))) +
              (4 * ε + 12 / Real.sqrt (n : ℝ) *
                (∫ x in ε..R, Real.sqrt (Real.log (coveringNumber' htotNeg x))))
              ≤ 8 * ε + 24 / Real.sqrt (n : ℝ) *
                (R * Real.sqrt (p * vcMaximalLog A U σ) + σ * Real.sqrt p) := by
                  rw [hcoef]
                  linarith
          _ ≤ 24 / Real.sqrt (n : ℝ) *
                (R * Real.sqrt (p * vcMaximalLog A U σ) + σ * Real.sqrt p) + δ := by
                  linarith)
  have hHzero : ∀ x, H i₀ x = 0 := by simp [H, anchoredClass]
  have hHabs := empiricalRademacherComplexity_le_signed_add_neg_of_zero
    H i₀ hHzero (mul_nonneg (by norm_num) hU0) hHenv n S
  have hdecomp : empiricalRademacherComplexity n F S ≤
      empiricalRademacherComplexity n H S +
        empiricalRademacherComplexity n (fun _i : ι => F i₀) S := by
    have hsub := empiricalRademacherComplexity_sub_le H (fun _i : ι => fun x => -F i₀ x)
      (mul_nonneg (by norm_num) hU0) hU0 hHenv
      (fun _ x => by simpa using henvelope i₀ x) n S
    have hcongr : empiricalRademacherComplexity n F S =
        empiricalRademacherComplexity n
          (fun i x => H i x - (-F i₀ x)) S := by
      apply empiricalRademacherComplexity_congr_sample
      intro i k
      simp [H, anchoredClass]
    rw [hcongr]
    have hnegConst : empiricalRademacherComplexity n (fun _i : ι => fun x => -F i₀ x) S =
        empiricalRademacherComplexity n (fun _i : ι => F i₀) S := by
      simpa using empiricalRademacherComplexity_smul_class
        (fun _i : ι => F i₀) (-1) n S
    rwa [hnegConst] at hsub
  have hanchor := constantClass_empiricalRademacher_le (ι := ι) (F i₀) hn S
  have hbasic : empiricalRademacherComplexity n F S ≤
      24 / Real.sqrt (n : ℝ) *
          (R * Real.sqrt (p * vcMaximalLog A U σ) + σ * Real.sqrt p) +
        2 * R / Real.sqrt (n : ℝ) := by
    have hanchorR : empiricalRademacherComplexity n (fun _i : ι => F i₀) S ≤
        2 * R / Real.sqrt (n : ℝ) := hanchor.trans (by
      gcongr
      exact hR i₀)
    exact hdecomp.trans (add_le_add (hHabs.trans hHsigned) hanchorR)
  have hratio : Real.exp 1 < A * U / σ := by
    have hUσ : 1 < U / σ := (one_lt_div₀ hσ).2 hσU
    calc
      Real.exp 1 ≤ A := hA
      _ < A * (U / σ) := by nlinarith [Real.exp_pos 1]
      _ = A * U / σ := by ring
  have hL1 : 1 ≤ vcMaximalLog A U σ := by
    rw [vcMaximalLog, max_eq_right hratio.le, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hratio.le
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hq1 : 1 ≤ Real.sqrt (p * vcMaximalLog A U σ) := by
    have hs := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ p * vcMaximalLog A U σ by nlinarith)
    simpa using hs
  have hsqrtp : Real.sqrt p ≤ Real.sqrt (p * vcMaximalLog A U σ) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hRnonneg : 0 ≤ R := hR0.le
  have hnroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  calc
    empiricalRademacherComplexity n F S ≤ _ := hbasic
    _ ≤ 26 / Real.sqrt (n : ℝ) * Real.sqrt (p * vcMaximalLog A U σ) * (R + σ) := by
      have h1 := mul_le_mul_of_nonneg_left hsqrtp hσ.le
      have h2 := mul_le_mul_of_nonneg_left hq1 hRnonneg
      field_simp
      nlinarith [Real.sqrt_nonneg (p * vcMaximalLog A U σ)]

/-- For [a countably indexed function class](hyp:F) whose [members are
measurable](hyp:hmeas) and [a fixed sample size](hyp:n), [the empirical
Rademacher complexity is measurable as a function of the sample](goal). -/
@[fun_prop]
lemma empiricalRademacherComplexity_measurable_countable
    [Countable ι] (F : ι → 𝒳 → ℝ) (hmeas : ∀ i, Measurable (F i)) (n : ℕ) :
    Measurable (fun S : Fin n → 𝒳 => empiricalRademacherComplexity n F S) := by
  simp only [causal_defs_simps]
  fun_prop

/-- If [the envelope level is nonnegative](hyp:hM0) and [every function is bounded in absolute
value by the envelope](hyp:hM), then [the empirical Rademacher complexity lies between zero and
the envelope level](goal). -/
lemma empiricalRademacherComplexity_mem_Icc
    [Nonempty ι]
    (F : ι → 𝒳 → ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i x, |F i x| ≤ M)
    (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n F S ∈ Set.Icc 0 M := by
  classical
  letI : Nonempty (Signs n) := ⟨fun _ => ⟨1, by simp⟩⟩
  simp only [causal_defs_simps]
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun τ _ => by
      let i₀ : ι := Classical.choice inferInstance
      exact (abs_nonneg _).trans (le_ciSup (absInner_bddAbove F hM0 hM n S τ) i₀))
  · calc
      (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ τ : Signs n, ⨆ i, |(n : ℝ)⁻¹ * ∑ k, (τ k : ℝ) * F i (S k)|
          ≤ (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ _τ : Signs n, M := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ => ?_) (by positivity)
            exact ciSup_le fun i => absInner_le_of_bound F hM0 hM n S τ i
      _ = M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hcNat : 0 < Fintype.card (Signs n) := Fintype.card_pos
        have hc : (Fintype.card (Signs n) : ℝ) ≠ 0 := by exact_mod_cast hcNat.ne'
        field_simp

/-- For [a function class](hyp:F) and [a finite sample](hyp:S), [the empirical
L² radius](goal) is the largest empirical L² norm among the functions in the
class. It summarizes the sample-specific scale used in variance-adaptive bounds. -/
noncomputable def empiricalL2Radius
    (F : ι → 𝒳 → ℝ) {n : ℕ} (S : Fin n → 𝒳) : ℝ :=
  ⨆ i, empiricalNorm S (F i)

/-- For [a countably indexed function class](hyp:F) whose [members are
measurable](hyp:hmeas) and [a fixed sample size](hyp:n), [the empirical L²
radius is measurable as a function of the sample](goal). -/
@[fun_prop]
lemma empiricalL2Radius_measurable
    [Countable ι] (F : ι → 𝒳 → ℝ) (hmeas : ∀ i, Measurable (F i)) (n : ℕ) :
    Measurable (fun S : Fin n → 𝒳 => empiricalL2Radius F S) := by
  unfold empiricalL2Radius empiricalNorm
  fun_prop

/-- If [the envelope level is nonnegative](hyp:hU0) and [every function is bounded in absolute
value by the envelope](hyp:henvelope), then [the empirical L2 radius lies between zero and the
envelope level](goal). -/
lemma empiricalL2Radius_mem_Icc
    [Nonempty ι]
    (F : ι → 𝒳 → ℝ) {U : ℝ} (hU0 : 0 ≤ U) (henvelope : ∀ i x, |F i x| ≤ U)
    {n : ℕ} (S : Fin n → 𝒳) : empiricalL2Radius F S ∈ Set.Icc 0 U := by
  have hbdd : BddAbove (Set.range fun i => empiricalNorm S (F i)) :=
    ⟨U, by rintro _ ⟨i, rfl⟩; exact empiricalNorm_le_of_envelope F hU0 henvelope S i⟩
  constructor
  · let i₀ : ι := Classical.choice inferInstance
    exact (by simp only [causal_defs_simps]; positivity : 0 ≤ empiricalNorm S (F i₀)) |>.trans
      (le_ciSup hbdd i₀)
  · exact ciSup_le fun i => empiricalNorm_le_of_envelope F hU0 henvelope S i

/-- If [the clipping radius is nonnegative](hyp:hU0), then [squaring after clipping to the
symmetric interval of that radius is Lipschitz at zero with constant twice the radius](goal). -/
lemma clippedSquare_lipschitzAt0 {U : ℝ} (hU0 : 0 ≤ U) :
    LipschitzAt0 (fun x => (Causalean.Mathlib.Analysis.clipIcc (-U) U x) ^ 2) (2 * U) := by
  open Causalean.Mathlib.Analysis in
  constructor
  · simp [clipIcc, hU0]
  · intro x y
    let a := clipIcc (-U) U x
    let b := clipIcc (-U) U y
    have ha : |a| ≤ U := abs_clipIcc_neg_le hU0 x
    have hb : |b| ≤ U := abs_clipIcc_neg_le hU0 y
    have hab : |a - b| ≤ |x - y| := abs_clipIcc_sub_clipIcc_le (-U) U x y
    have habsum : |a + b| ≤ 2 * U := by
      calc |a + b| ≤ |a| + |b| := abs_add_le _ _
        _ ≤ 2 * U := by linarith
    rw [sq_sub_sq, abs_mul]
    calc
      |a + b| * |a - b| ≤ (2 * U) * |x - y| :=
        mul_le_mul habsum hab (abs_nonneg _) (by positivity)

/-- If [the population L2 radius is positive](hyp:hσ), [it is smaller than the envelope
level](hyp:hσU), [all class functions are measurable](hyp:hmeas), [they are uniformly bounded
by the envelope](hyp:henvelope), [their population L2 distances from zero are at most the stated
radius](hyp:hL2), and [the sample size is positive](hyp:hn), then [the squared empirical L2 radius
is at most the squared population radius plus the uniform deviation of the squared class](goal). -/
lemma empiricalL2Radius_sq_le_uniformDeviation
    [Nonempty ι]
    (P : Measure 𝒳) [IsProbabilityMeasure P]
    (F : ι → 𝒳 → ℝ) {U σ : ℝ}
    (hσ : 0 < σ) (hσU : σ < U)
    (hmeas : ∀ i, Measurable (F i))
    (henvelope : ∀ i x, |F i x| ≤ U)
    (hL2 : ∀ i, measureL2Dist P (F i) (fun _ => 0) ≤ σ)
    {n : ℕ} (hn : 0 < n) (S : Fin n → 𝒳) :
    empiricalL2Radius F S ^ 2 ≤ σ ^ 2 +
      uniformDeviation n (fun i x => F i x ^ 2) P id S := by
  classical
  have hU : 0 < U := hσ.trans hσU
  have hpop : ∀ i, ∫ x, F i x ^ 2 ∂P ≤ σ ^ 2 := by
    intro i
    have hi0 : 0 ≤ ∫ x, F i x ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
    have hi := hL2 i
    unfold measureL2Dist at hi
    simp only [sub_zero] at hi
    calc
      (∫ x, F i x ^ 2 ∂P) = Real.sqrt (∫ x, F i x ^ 2 ∂P) ^ 2 :=
        (Real.sq_sqrt hi0).symm
      _ ≤ σ ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg _) hσ.le).2 hi
  have havg : ∀ i, 0 ≤ (n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) ^ 2 ∧
      (n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) ^ 2 ≤ U ^ 2 := by
    intro i
    constructor
    · positivity
    · calc
        (n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) ^ 2
            ≤ (n : ℝ)⁻¹ * ∑ _k : Fin n, U ^ 2 := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity)
              rw [sq_le_sq]
              simpa [abs_of_pos hU] using henvelope i (S k)
        _ = U ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
          simp only [Fintype.card_fin]
          field_simp
  have hdevBdd : BddAbove (Set.range fun i =>
      |(n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) ^ 2 - ∫ x, F i x ^ 2 ∂P|) := by
    refine ⟨2 * U ^ 2, ?_⟩
    rintro _ ⟨i, rfl⟩
    have hpop0 : 0 ≤ ∫ x, F i x ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
    have hσU2 : σ ^ 2 ≤ U ^ 2 := by nlinarith
    rw [abs_le]
    constructor <;> nlinarith [havg i, hpop i]
  let D := uniformDeviation n (fun i x => F i x ^ 2) P id S
  have hD0 : 0 ≤ D := by
    let i₀ : ι := Classical.choice inferInstance
    exact (abs_nonneg _).trans (le_ciSup hdevBdd i₀)
  have hnormsq : ∀ i, empiricalNorm S (F i) ^ 2 ≤ σ ^ 2 + D := by
    intro i
    have hdev : |(n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) ^ 2 - ∫ x, F i x ^ 2 ∂P| ≤ D :=
      le_ciSup hdevBdd i
    have heq : empiricalNorm S (F i) ^ 2 =
        (n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) ^ 2 := by
      simp only [causal_defs_simps]
      simpa [one_div] using Real.sq_sqrt (havg i |>.1)
    rw [heq]
    linarith [le_abs_self ((n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) ^ 2 -
      ∫ x, F i x ^ 2 ∂P), hpop i]
  have hrad := empiricalL2Radius_mem_Icc F hU.le henvelope S
  have hB0 : 0 ≤ σ ^ 2 + D := add_nonneg (sq_nonneg _) hD0
  have hradle : empiricalL2Radius F S ≤ Real.sqrt (σ ^ 2 + D) := by
    unfold empiricalL2Radius
    refine ciSup_le fun i => ?_
    have hs := Real.sqrt_le_sqrt (hnormsq i)
    have hnorm0 : 0 ≤ empiricalNorm S (F i) := by simp only [causal_defs_simps]; positivity
    rw [Real.sqrt_sq hnorm0] at hs
    exact hs
  change empiricalL2Radius F S ^ 2 ≤ σ ^ 2 + D
  nlinarith [Real.sq_sqrt hB0, hrad.1]



end Causalean.Stat.Concentration

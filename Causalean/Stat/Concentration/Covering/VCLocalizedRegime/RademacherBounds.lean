module
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.RademacherBridge

/-!
# Localized finite-VC Rademacher bounds

This file combines Boolean trace-cardinality control with a finite-class
Massart bound to prove samplewise linear bounds for the star-hull-zeroed class.
It lifts those bounds to population Rademacher envelopes and constructs the
`LocalizedRegime` packages consumed by localized uniform-deviation theorems.
-/

@[expose] public section

namespace Causalean
namespace Stat
namespace Concentration

open MeasureTheory ProbabilityTheory

universe u v

section RademacherBridge

variable {Ω : Type*} {ι : Type u} {𝒳 : Type v} [MeasurableSpace Ω]
variable [Nonempty ι] [Countable ι]

/-- For a positive sample size, the square root of the sum of squared
sample-normalized absolute function values equals the empirical norm divided by
the square root of the sample size. -/
lemma sqrt_sum_inv_abs_sq_eq_empiricalNorm_div_sqrt
    {𝒳 : Type*} {n : ℕ} (hn : 0 < n) (S : Fin n → 𝒳) (g : 𝒳 → ℝ) :
    Real.sqrt (∑ k : Fin n, ((n : ℝ)⁻¹ * |g (S k)|) ^ 2)
      = empiricalNorm S g / Real.sqrt (n : ℝ) := by
  classical
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum :
      (∑ k : Fin n, ((n : ℝ)⁻¹ * |g (S k)|) ^ 2)
        =
      (n : ℝ)⁻¹ * ((n : ℝ)⁻¹ * ∑ k : Fin n, (g (S k)) ^ 2) := by
    calc
      (∑ k : Fin n, ((n : ℝ)⁻¹ * |g (S k)|) ^ 2)
          = ∑ k : Fin n, ((n : ℝ)⁻¹) ^ 2 * (g (S k)) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [mul_pow, sq_abs]
      _ = ((n : ℝ)⁻¹) ^ 2 * ∑ k : Fin n, (g (S k)) ^ 2 := by
            rw [Finset.mul_sum]
      _ = (n : ℝ)⁻¹ * ((n : ℝ)⁻¹ * ∑ k : Fin n, (g (S k)) ^ 2) := by
            ring
  calc
    Real.sqrt (∑ k : Fin n, ((n : ℝ)⁻¹ * |g (S k)|) ^ 2)
        = Real.sqrt ((n : ℝ)⁻¹ *
            ((n : ℝ)⁻¹ * ∑ k : Fin n, (g (S k)) ^ 2)) := by
          rw [hsum]
    _ = Real.sqrt ((n : ℝ)⁻¹) *
          Real.sqrt ((n : ℝ)⁻¹ * ∑ k : Fin n, (g (S k)) ^ 2) := by
          rw [Real.sqrt_mul (inv_nonneg.mpr (le_of_lt hnR))]
    _ = (Real.sqrt (n : ℝ))⁻¹ *
          Real.sqrt ((n : ℝ)⁻¹ * ∑ k : Fin n, (g (S k)) ^ 2) := by
          rw [Real.sqrt_inv]
    _ = empiricalNorm S g / Real.sqrt (n : ℝ) := by
          unfold empiricalNorm
          ring

/-- Under the localized VC hypotheses, a function's localized scale coefficient
times its empirical norm over the sample is at most the localization radius. -/
lemma starHullZeroOutScaleCoeff_mul_empiricalNorm_le
    {ι 𝒳 : Type*} {n : ℕ}
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm)
    (S : Fin n → 𝒳) {r : ℝ} (hr : 0 ≤ r) (i : ι) :
    starHullZeroOutScaleCoeff F norm r i * empiricalNorm S (F i) ≤ r := by
  classical
  have hnorm_nonneg : 0 ≤ empiricalNorm S (F i) := by
    unfold empiricalNorm
    positivity
  have hmul :
      (⨆ a : Set.Icc (0 : ℝ) 1,
          (if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0) *
            empiricalNorm S (F i))
        =
      starHullZeroOutScaleCoeff F norm r i * empiricalNorm S (F i) := by
    rw [ciSup_mul_const_of_le_one
      (fun a : Set.Icc (0 : ℝ) 1 =>
        if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0)
      (empiricalNorm S (F i))
      hnorm_nonneg]
    rfl
  rw [← hmul]
  refine ciSup_le ?_
  intro a
  by_cases hactive : norm (starHullEval F (a, i)) ≤ r
  · have hnorm := Hloc.empirical_radius S hr (a, i)
    have heq :
        empiricalNorm S (starHullZeroOut F norm r (a, i))
          = (a : ℝ) * empiricalNorm S (F i) := by
      calc
        empiricalNorm S (starHullZeroOut F norm r (a, i))
            = empiricalNorm S (fun x => (a : ℝ) * F i x) := by
              congr
              funext x
              simp [starHullZeroOut, hactive, starHullEval]
        _ = (a : ℝ) * empiricalNorm S (F i) :=
              by simpa [abs_of_nonneg a.property.1] using
                empiricalNorm_const_mul S (a : ℝ) (F i)
    simpa [hactive, heq] using hnorm
  · calc
      (if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0) *
          empiricalNorm S (F i) = 0 := by
          simp [hactive]
      _ ≤ r := hr

private lemma starHullPatternCoeff_mul_empiricalNorm_rep_le
    {ι 𝒳 : Type*} {n : ℕ}
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm)
    (S : Fin n → 𝒳) {r : ℝ} (hr : 0 ≤ r)
    (A : {A // A ∈ growthFamily π S}) :
    starHullPatternCoeff F norm π S r A *
        empiricalNorm S (F (growthFamilyRep π S A)) ≤ r := by
  classical
  rcases hfactor S with ⟨φ, hφ⟩
  let repSub : {i : ι // restrictionPattern (π i) S = A.1} :=
    ⟨growthFamilyRep π S A, growthFamilyRep_spec π S A⟩
  haveI : Nonempty {i : ι // restrictionPattern (π i) S = A.1} := ⟨repSub⟩
  have hnorm_nonneg : 0 ≤ empiricalNorm S (F (growthFamilyRep π S A)) := by
    unfold empiricalNorm
    positivity
  have hmul :
      (⨆ i : {i : ι // restrictionPattern (π i) S = A.1},
          starHullZeroOutScaleCoeff F norm r i.1 *
            empiricalNorm S (F (growthFamilyRep π S A)))
        =
      starHullPatternCoeff F norm π S r A *
        empiricalNorm S (F (growthFamilyRep π S A)) := by
    rw [starHullPatternCoeff]
    rw [ciSup_mul_const_of_le_one
      (fun i : {i : ι // restrictionPattern (π i) S = A.1} =>
        starHullZeroOutScaleCoeff F norm r i.1)
      (empiricalNorm S (F (growthFamilyRep π S A)))
      hnorm_nonneg]
  rw [← hmul]
  refine ciSup_le ?_
  intro i
  have hnorm_eq :
      empiricalNorm S (F i.1) =
        empiricalNorm S (F (growthFamilyRep π S A)) := by
    have hpoint : ∀ k : Fin n,
        F i.1 (S k) = F (growthFamilyRep π S A) (S k) :=
      sample_eq_growthFamilyRep_of_pattern (F := F) (π := π) (S := S)
        (φ := φ) hφ A i.2
    simp [empiricalNorm, hpoint]
  simpa [hnorm_eq] using
    starHullZeroOutScaleCoeff_mul_empiricalNorm_le F norm Hloc S hr i.1

private lemma starHullPatternClass_radius_le
    {ι 𝒳 : Type*} {n : ℕ} (hn : 0 < n)
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm)
    (S : Fin n → 𝒳) {r : ℝ} (hr : 0 ≤ r)
    (A : {A // A ∈ growthFamily π S}) :
    Real.sqrt (∑ k : Fin n,
        ((n : ℝ)⁻¹ * |starHullPatternClass F norm π S r A (S k)|)^2)
      ≤ r / Real.sqrt (n : ℝ) := by
  classical
  rw [sqrt_sum_inv_abs_sq_eq_empiricalNorm_div_sqrt hn]
  have hnorm :
      empiricalNorm S (starHullPatternClass F norm π S r A)
        =
      starHullPatternCoeff F norm π S r A *
        empiricalNorm S (F (growthFamilyRep π S A)) := by
    have h :=
      empiricalNorm_const_mul S
        (starHullPatternCoeff F norm π S r A)
        (F (growthFamilyRep π S A))
    simp only [abs_of_nonneg (starHullPatternCoeff_nonneg F norm π S r A)] at h
    exact h
  rw [hnorm]
  exact div_le_div_of_nonneg_right
    (starHullPatternCoeff_mul_empiricalNorm_rep_le F norm π hfactor Hloc S hr A)
    (Real.sqrt_nonneg _)

omit [Nonempty ι] [Countable ι] in
/-- The empirical Rademacher complexity of a zero-augmented localized star hull
is bounded by its radius times a logarithmic factor determined by the number of
distinct Boolean patterns in the sample. -/
lemma starHullZeroOut_empirical_rademacher_le_growthFamily
    [Nonempty ι]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    {n : ℕ} (hn : 0 < n)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm)
    (S : Fin n → 𝒳) (r : ℝ) (hr : 0 ≤ r) :
    empiricalRademacherComplexity n (starHullZeroOut F norm r) S
      ≤ r * Real.sqrt
        ((2 * Real.log (2 * ((growthFamily π S).card : ℝ))) / (n : ℝ)) := by
  classical
  let W : {A // A ∈ growthFamily π S} → 𝒳 → ℝ :=
    starHullPatternClass F norm π S r
  have hgf_nonempty : (growthFamily π S).Nonempty := by
    let i0 : ι := Classical.arbitrary ι
    refine ⟨restrictionPattern (π i0) S, ?_⟩
    rw [mem_growthFamily_iff]
    exact ⟨i0, rfl⟩
  haveI : Nonempty {A // A ∈ growthFamily π S} := by
    rcases hgf_nonempty with ⟨A, hA⟩
    exact ⟨⟨A, hA⟩⟩
  have hcollapse :
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S
        ≤ empiricalRademacherComplexity n W S := by
    simpa [W] using
      starHullZeroOut_empirical_rademacher_le_patternClass F norm π hfactor S r
  have hfinite_on :
      empiricalRademacherComplexity n
          (F_on W (Finset.univ : Finset {A // A ∈ growthFamily π S})) S
        ≤
      (r / Real.sqrt (n : ℝ)) *
        Real.sqrt
          (2 * Real.log
            (2 * (((Finset.univ : Finset {A // A ∈ growthFamily π S}).card : ℝ)))) := by
    refine empiricalRademacher_withAbs_finiteClass_le
      (ι' := {A // A ∈ growthFamily π S}) (Z := 𝒳)
      hn W S (Finset.univ : Finset {A // A ∈ growthFamily π S})
      ?_ (r / Real.sqrt (n : ℝ)) ?_
    · simpa using
        (Finset.univ_nonempty :
          (Finset.univ : Finset {A // A ∈ growthFamily π S}).Nonempty)
    · intro A _hA
      simpa [W] using
        starHullPatternClass_radius_le hn F norm π hfactor Hloc S hr A
  have hfinite :
      empiricalRademacherComplexity n W S
        ≤
      (r / Real.sqrt (n : ℝ)) *
        Real.sqrt (2 * Real.log (2 * ((growthFamily π S).card : ℝ))) := by
    have hcard :
        (((Finset.univ : Finset {A // A ∈ growthFamily π S}).card : ℝ))
          = ((growthFamily π S).card : ℝ) := by
      simp
    have hfinite_univ := hfinite_on
    rw [empiricalRademacherComplexity_F_on_univ_eq W S] at hfinite_univ
    simpa [hcard] using hfinite_univ
  let L : ℝ := 2 * Real.log (2 * ((growthFamily π S).card : ℝ))
  have hcard_pos : 0 < (growthFamily π S).card := Finset.card_pos.mpr hgf_nonempty
  have hlog_nonneg : 0 ≤ Real.log (2 * ((growthFamily π S).card : ℝ)) := by
    have hcard_one : (1 : ℝ) ≤ ((growthFamily π S).card : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hcard_pos)
    have hone_le : (1 : ℝ) ≤ 2 * ((growthFamily π S).card : ℝ) := by
      nlinarith
    exact Real.log_nonneg hone_le
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg (by norm_num) hlog_nonneg
  calc
    empiricalRademacherComplexity n (starHullZeroOut F norm r) S
        ≤ empiricalRademacherComplexity n W S := hcollapse
    _ ≤ (r / Real.sqrt (n : ℝ)) * Real.sqrt L := by
        simpa [L] using hfinite
    _ = r * Real.sqrt (L / (n : ℝ)) := by
        rw [Real.sqrt_div hL_nonneg]
        ring
    _ = r * Real.sqrt
        ((2 * Real.log (2 * ((growthFamily π S).card : ℝ))) / (n : ℝ)) := by
        rfl

omit [Nonempty ι] [Countable ι] in
/-- Massart finite-realization bound for the localized star-hull zero-out
class under binary trace entropy control.

This is the genuine analytic substep: star-hull scale contraction, empirical
radius control, finite Boolean-pattern reduction, and Massart's lemma. -/
lemma starHullZeroOut_empirical_rademacher_massart_vc
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (d n : ℕ)
    (Htrace : BinaryTraceEntropyControl π d)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm) :
    ∀ (S : Fin n → 𝒳) (r : ℝ), 0 ≤ r →
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S
        ≤ r * Real.sqrt
          ((2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2) / (n : ℝ)) := by
  intro S r hr
  by_cases hn0 : n = 0
  · subst n
    simp [empiricalRademacherComplexity]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    by_cases hι : Nonempty ι
    · haveI : Nonempty ι := hι
      have hcard_pos : 0 < (growthFamily π S).card := by
        let i0 : ι := Classical.choice hι
        have hmem : restrictionPattern (π i0) S ∈ growthFamily π S := by
          rw [mem_growthFamily_iff]
          exact ⟨i0, rfl⟩
        exact Finset.card_pos.mpr ⟨_, hmem⟩
      have hcard :
          (growthFamily π S).card ≤ (n + 1) ^ d :=
        growthFamily_card_le_succ_pow_of_trace π d n Htrace S
      have hmass :=
        starHullZeroOut_empirical_rademacher_le_growthFamily
          F norm π hfactor hn Hloc S r hr
      have hlog :=
        log_two_growth_card_le π d n S hcard_pos hcard
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hsqrt :
          Real.sqrt
              ((2 * Real.log (2 * ((growthFamily π S).card : ℝ))) / (n : ℝ))
            ≤
          Real.sqrt
              ((2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2) / (n : ℝ)) := by
        exact Real.sqrt_le_sqrt
          (div_le_div_of_nonneg_right hlog (le_of_lt hnR))
      exact hmass.trans (mul_le_mul_of_nonneg_left hsqrt hr)
    · letI : IsEmpty ι := ⟨fun i => hι ⟨i⟩⟩
      have hzero :
          empiricalRademacherComplexity n (starHullZeroOut F norm r) S = 0 := by
        simp [empiricalRademacherComplexity, starHullParam]
      rw [hzero]
      exact mul_nonneg hr (Real.sqrt_nonneg _)

omit [Nonempty ι] [Countable ι] in
/-- Shared finite-pattern VC bound for the localized star-hull class.

This combines star-hull scale contraction, binary trace-cardinality control,
and the finite-realization Massart bound into the linear localized Rademacher
envelope used by the regime package. It does not invoke entropy chaining. -/
lemma absolute_dudley_vc_starHullZeroOut_linear_residual_shared
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (K : ℝ) (d n : ℕ) (hK : (1 : ℝ) ≤ K)
    (Htrace : BinaryTraceEntropyControl π d)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm) :
    ∀ (S : Fin n → 𝒳) (r : ℝ), 0 ≤ r →
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S
        ≤ vcLocalizedPsi K d n r := by
  intro S r hr
  have hmass :=
    starHullZeroOut_empirical_rademacher_massart_vc
      F norm π hfactor d n Htrace Hloc S r hr
  by_cases hn0 : n = 0
  · simpa [vcLocalizedPsi, vcLocalizedSlope, hn0] using hmass
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hK0 : 0 ≤ K := le_trans zero_le_one hK
    have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := by
      have hone_le : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        linarith [le_of_lt hnR]
      exact Real.log_nonneg hone_le
    have hD_nonneg : 0 ≤ (d : ℝ) * Real.log ((n : ℝ) + 1) :=
      mul_nonneg (Nat.cast_nonneg d) hlog
    have hKD :
        (d : ℝ) * Real.log ((n : ℝ) + 1)
          ≤ K * (d : ℝ) * Real.log ((n : ℝ) + 1) := by
      calc
        (d : ℝ) * Real.log ((n : ℝ) + 1)
            = 1 * ((d : ℝ) * Real.log ((n : ℝ) + 1)) := by ring
        _ ≤ K * ((d : ℝ) * Real.log ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hK hD_nonneg
        _ = K * (d : ℝ) * Real.log ((n : ℝ) + 1) := by ring
    have hnum :
        2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2
          ≤ 36 * (K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) := by
      nlinarith
    have hfrac :
        (2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2) / (n : ℝ)
          ≤ 36 *
            ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) := by
      have hdiv :=
        div_le_div_of_nonneg_right hnum (le_of_lt hnR)
      simpa [mul_div_assoc, mul_assoc] using hdiv
    have hsqrt :
        Real.sqrt
            ((2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2) / (n : ℝ))
          ≤
        6 * Real.sqrt
            ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) := by
      calc
        Real.sqrt
            ((2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2) / (n : ℝ))
            ≤ Real.sqrt
                (36 *
                  ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ))) :=
              Real.sqrt_le_sqrt hfrac
        _ = 6 * Real.sqrt
              ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) := by
              have hsqrt36 : Real.sqrt (36 : ℝ) = 6 := by
                have hsq : (Real.sqrt (36 : ℝ)) ^ 2 = (6 : ℝ) ^ 2 := by
                  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 36)]
                  norm_num
                rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
                · exact h
                · nlinarith [Real.sqrt_nonneg (36 : ℝ)]
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 36)]
              rw [hsqrt36]
    calc
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S
          ≤ r * Real.sqrt
              ((2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2) / (n : ℝ)) :=
            hmass
      _ ≤ r *
          (6 * Real.sqrt
            ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hsqrt hr
      _ = vcLocalizedPsi K d n r := by
            simp [vcLocalizedPsi, vcLocalizedSlope]
            ring

omit [Nonempty ι] [Countable ι] in
/-- The finite-VC sample-path bound for the localized star-hull class.

See `absolute_dudley_vc_starHullZeroOut_linear_residual_shared` for the shared
finite-pattern bound that feeds this specialization. -/
lemma vc_starHullZeroOut_empirical_rademacher_le_linear
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (K : ℝ) (d n : ℕ) (hK : (1 : ℝ) ≤ K)
    (Hvc : BinaryFactoredVCClass F d)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm) :
    ∀ (S : Fin n → 𝒳) (r : ℝ), 0 ≤ r →
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S
        ≤ vcLocalizedPsi K d n r :=
  absolute_dudley_vc_starHullZeroOut_linear_residual_shared
    F norm Hvc.π Hvc.factor K d n hK (Or.inl Hvc.vcDim_le) Hloc

omit [Nonempty ι] [Countable ι] in
/-- Cardinality-bound sample-path bridge for the localized star-hull class.
This is the direct growth-function analogue of
`vc_starHullZeroOut_empirical_rademacher_le_linear`. -/
lemma vc_starHullZeroOut_empirical_rademacher_le_linear_of_card
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (K : ℝ) (dPi n : ℕ) (hK : (1 : ℝ) ≤ K)
    (hcard : ∀ (m : ℕ) (S : Fin m → 𝒳),
      (growthFamily π S).card ≤ (m + 1) ^ dPi)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm) :
    ∀ (S : Fin n → 𝒳) (r : ℝ), 0 ≤ r →
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S
        ≤ vcLocalizedPsi K dPi n r :=
  absolute_dudley_vc_starHullZeroOut_linear_residual_shared
    F norm π hfactor K dPi n hK (Or.inr hcard) Hloc

omit [Nonempty ι] [Countable ι] in
/-- The finite-VC population Rademacher bound for the localized star-hull
class, obtained by integrating the finite-pattern samplewise estimate. -/
lemma vc_starHullZeroOut_population_rademacher_le_linear
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (K : ℝ) (d n : ℕ) (hK : (1 : ℝ) ≤ K)
    (Hvc : BinaryFactoredVCClass F d)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm) :
    ∀ r : ℝ, 0 ≤ r →
      rademacherComplexity n (starHullZeroOut F norm r) μ X
        ≤ vcLocalizedPsi K d n r := by
  intro r hr
  let C := vcLocalizedPsi K d n r
  have hpoint : ∀ S : Fin n → 𝒳,
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S ≤ C := by
    intro S
    exact vc_starHullZeroOut_empirical_rademacher_le_linear
      F norm K d n hK Hvc Hloc S r hr
  have h_abs : ∀ᵐ ω : Fin n → Ω ∂(Measure.pi fun _ : Fin n => μ),
      |empiricalRademacherComplexity n
          (starHullZeroOut F norm r) (X ∘ ω)| ≤ C := by
    exact Filter.Eventually.of_forall fun ω => by
      have hnonneg : 0 ≤ empiricalRademacherComplexity n
          (starHullZeroOut F norm r) (X ∘ ω) := by
        unfold empiricalRademacherComplexity
        refine mul_nonneg ?_ ?_
        · positivity
        · refine Finset.sum_nonneg ?_
          intro σ _
          refine Real.iSup_nonneg ?_
          intro p
          exact abs_nonneg _
      rw [abs_of_nonneg hnonneg]
      exact hpoint (X ∘ ω)
  unfold rademacherComplexity
  change ∫ ω : Fin n → Ω,
      empiricalRademacherComplexity n
        (starHullZeroOut F norm r) (X ∘ ω)
        ∂(Measure.pi fun _ : Fin n => μ) ≤ C
  exact le_trans (le_abs_self _)
    (abs_expectation_le_of_abs_le_const h_abs)

omit [Nonempty ι] [Countable ι] in
/-- Cardinality-bound population bridge for the localized star-hull class. -/
lemma vc_starHullZeroOut_population_rademacher_le_linear_of_card
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (K : ℝ) (dPi n : ℕ) (hK : (1 : ℝ) ≤ K)
    (hcard : ∀ (m : ℕ) (S : Fin m → 𝒳),
      (growthFamily π S).card ≤ (m + 1) ^ dPi)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm) :
    ∀ r : ℝ, 0 ≤ r →
      rademacherComplexity n (starHullZeroOut F norm r) μ X
        ≤ vcLocalizedPsi K dPi n r := by
  intro r hr
  let C := vcLocalizedPsi K dPi n r
  have hpoint : ∀ S : Fin n → 𝒳,
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S ≤ C := by
    intro S
    exact vc_starHullZeroOut_empirical_rademacher_le_linear_of_card
      F norm π hfactor K dPi n hK hcard Hloc S r hr
  have h_abs : ∀ᵐ ω : Fin n → Ω ∂(Measure.pi fun _ : Fin n => μ),
      |empiricalRademacherComplexity n
          (starHullZeroOut F norm r) (X ∘ ω)| ≤ C := by
    exact Filter.Eventually.of_forall fun ω => by
      have hnonneg : 0 ≤ empiricalRademacherComplexity n
          (starHullZeroOut F norm r) (X ∘ ω) := by
        unfold empiricalRademacherComplexity
        refine mul_nonneg ?_ ?_
        · positivity
        · refine Finset.sum_nonneg ?_
          intro σ _
          refine Real.iSup_nonneg ?_
          intro p
          exact abs_nonneg _
      rw [abs_of_nonneg hnonneg]
      exact hpoint (X ∘ ω)
  unfold rademacherComplexity
  change ∫ ω : Fin n → Ω,
      empiricalRademacherComplexity n
        (starHullZeroOut F norm r) (X ∘ ω)
        ∂(Measure.pi fun _ : Fin n => μ) ≤ C
  exact le_trans (le_abs_self _)
    (abs_expectation_le_of_abs_le_const h_abs)

omit [Nonempty ι] [Countable ι] in
/-- The finite-VC localized envelope upper-bounds population localized
Rademacher complexity. -/
theorem vcLocalizedRademacherUpperBound
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (K : ℝ) (d n : ℕ) (hK : (1 : ℝ) ≤ K)
    (Hvc : BinaryFactoredVCClass F d)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm) :
    RademacherUpperBound F norm μ X n (vcLocalizedPsi K d n) := by
  intro r hr
  exact vc_starHullZeroOut_population_rademacher_le_linear
    F norm μ X K d n hK Hvc Hloc r hr

omit [Nonempty ι] [Countable ι] in
/-- The growth-cardinality localized envelope upper-bounds population
localized Rademacher complexity. -/
theorem vcLocalizedRademacherUpperBound_of_card
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (K : ℝ) (dPi n : ℕ) (hK : (1 : ℝ) ≤ K)
    (hcard : ∀ (m : ℕ) (S : Fin m → 𝒳),
      (growthFamily π S).card ≤ (m + 1) ^ dPi)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm) :
    RademacherUpperBound F norm μ X n (vcLocalizedPsi K dPi n) := by
  intro r hr
  exact vc_starHullZeroOut_population_rademacher_le_linear_of_card
    F norm π μ X hfactor K dPi n hK hcard Hloc r hr

omit [Nonempty ι] [Countable ι] in
/-- For [a function class, localization norm, probability space, and observation
map](hyp:Ω,ι,𝒳,F,norm,μ,X), [a tuning constant, VC-dimension bound, and sample
size](hyp:K,d,n), [a tuning constant at least one](hyp:hK), [positive sample size](hyp:hn), [a
binary factorization with the stated VC bound](hyp:Hvc), and [the samplewise
localization certificate](hyp:Hloc), [the finite-VC envelope is star-shaped,
bounds the localized population Rademacher complexity, and yields both the
stated critical-radius and squared-rate bounds](goal).

Fixed-`n` samplewise-radius finite-VC localized envelope package: star-shaped envelope,
localized Rademacher upper bound, critical-radius bound by the slope, and
squared critical-radius rate. -/
theorem vcLocalizedEnvelope
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (K : ℝ) (d n : ℕ) (hK : (1 : ℝ) ≤ K) (hn : 0 < n)
    (Hvc : BinaryFactoredVCClass F d)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm) :
    IsStarShapedEnvelope (vcLocalizedPsi K d n) ∧
      RademacherUpperBound F norm μ X n (vcLocalizedPsi K d n) ∧
      criticalRadius (vcLocalizedPsi K d n) ≤ vcLocalizedSlope K d n ∧
      (criticalRadius (vcLocalizedPsi K d n)) ^ 2 ≤
        36 * ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) := by
  refine ⟨vcLocalizedPsi_isStarShapedEnvelope K d n, ?_, ?_, ?_⟩
  · exact vcLocalizedRademacherUpperBound F norm μ X K d n hK Hvc Hloc
  · exact criticalRadius_vcLocalizedPsi_le (le_trans zero_le_one hK) hn
  · exact criticalRadius_vcLocalizedPsi_sq_le_rate (le_trans zero_le_one hK) hn

omit [Nonempty ι] [Countable ι] in
/-- Given [a real-valued function class](hyp:F), [a function norm](hyp:norm),
[a probability measure](hyp:μ), [an observation map](hyp:X), [a uniform
bound](hyp:b) that is [nonnegative](hyp:hb) and [bounds every function value at
every observed point](hyp:hbound), [variance controlled by the squared
localization norm](hyp:hvariance), [a tuning constant](hyp:K), [a VC-dimension
bound](hyp:d), [a tuning constant at least one](hyp:hK), [a binary
factorization with VC dimension at most the stated bound](hyp:Hvc), and [the
samplewise localization certificate](hyp:Hloc), [the localized-regime
package](goal) consists of this bound and the finite-VC localized envelope with
its star-shaped-envelope and Rademacher upper-bound guarantees.

Build the `LocalizedRegime` bundle for the localized-deviation theorems
from a bounded finite-VC class and the finite-VC localized envelope. -/
noncomputable def vcLocalizedRegime
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ i ω, |F i (X ω)| ≤ b)
    (hvariance : ∀ i, variance (fun ω => F i (X ω)) μ ≤ norm (F i) ^ 2)
    (K : ℝ) (d : ℕ) (hK : (1 : ℝ) ≤ K)
    (Hvc : BinaryFactoredVCClass F d)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm) :
    LocalizedRegime Ω ι 𝒳 F norm μ X where
  b := b
  b_nonneg := hb
  bound := hbound
  variance_proxy := hvariance
  ψ := fun n => vcLocalizedPsi K d n
  ψ_isStarShapedEnvelope := fun n => vcLocalizedPsi_isStarShapedEnvelope K d n
  ψ_ub := fun n => vcLocalizedRademacherUpperBound F norm μ X K d n hK Hvc Hloc

omit [Nonempty ι] [Countable ι] in
/-- Given [a real-valued function class](hyp:F), [a function norm](hyp:norm),
[a Boolean factorization family](hyp:π), [a probability measure](hyp:μ), [an
observation map](hyp:X), [a uniform bound](hyp:b) that is
[nonnegative](hyp:hb) and [bounds every function value at every observed
point](hyp:hbound), [variance controlled by the squared localization
norm](hyp:hvariance), [a factorization of each finite-sample function value
through its Boolean label](hyp:hfactor), [a tuning constant](hyp:K), [a
trace-growth exponent](hyp:dPi), [a tuning constant at least one](hyp:hK), [a
polynomial bound on every finite-sample trace-family cardinality](hyp:hcard),
and [the samplewise localization certificate](hyp:Hloc), [the localized-regime
package](goal) consists of this bound and the localized envelope obtained from
the direct trace-cardinality bound.

Build the `LocalizedRegime` bundle from a direct growth-cardinality bound
on the binary trace family. -/
noncomputable def vcLocalizedRegime_of_card
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ i ω, |F i (X ω)| ≤ b)
    (hvariance : ∀ i, variance (fun ω => F i (X ω)) μ ≤ norm (F i) ^ 2)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (K : ℝ) (dPi : ℕ) (hK : (1 : ℝ) ≤ K)
    (hcard : ∀ (m : ℕ) (S : Fin m → 𝒳),
      (growthFamily π S).card ≤ (m + 1) ^ dPi)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm) :
    LocalizedRegime Ω ι 𝒳 F norm μ X where
  b := b
  b_nonneg := hb
  bound := hbound
  variance_proxy := hvariance
  ψ := fun n => vcLocalizedPsi K dPi n
  ψ_isStarShapedEnvelope := fun n => vcLocalizedPsi_isStarShapedEnvelope K dPi n
  ψ_ub := fun n =>
    vcLocalizedRademacherUpperBound_of_card
      F norm π μ X hfactor K dPi n hK hcard Hloc

end RademacherBridge


end Concentration
end Stat
end Causalean

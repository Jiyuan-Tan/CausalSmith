/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime
public import Causalean.Stat.Concentration.Localization.PeelingRates

/-!
Finite-VC localized uniform-deviation bounds under a universal samplewise
empirical-radius assumption, derived from the sharp localized empirical-process
theorem.

For a finite-VC binary-indexed function class, with high probability the localized empirical
process deviates from its mean by at most 10ρ * ‖f‖ + 5ρ² uniformly over members satisfying
`0 ≤ norm f ≤ b`, with critical radius ρ of order sqrt(d * log n / n) -- derived, under that
stronger samplewise assumption, by instantiating
`localized_uniform_deviation_sharp` with the finite-VC localized envelope.

This file is the samplewise-radius finite-VC specialization layer for the sharp
localized uniform-deviation theorem. The empirical-process content is supplied
by finite-pattern Massart bounds; the only rate arithmetic is supplied by
`vcLocalizedSlope_peelingCondition_eventually`.
It exports the VC-dimension event `vc_localized_deviation_event`, the direct
growth-cardinality variant `vc_localized_deviation_event_of_card`, and the
measurability/integrability bridges needed to instantiate the sharp theorem.
-/

public section

namespace Causalean
namespace Stat
namespace Concentration

open MeasureTheory ProbabilityTheory

universe u v

section Helpers

variable {ι : Type u} {𝒳 : Type v}

/-- The critical radius of a positive-slope linear envelope equals its slope,
giving the exact fixed-point scale for a localized empirical-process bound. -/
lemma criticalRadius_linear_eq {C : ℝ} (hC : 0 < C) :
    criticalRadius (fun r : ℝ => C * r) = C := by
  apply le_antisymm
  · exact criticalRadius_linear_le hC
  · rw [criticalRadius]
    apply le_csInf
    · exact ⟨C, hC, by rw [pow_two]⟩
    · rintro δ ⟨hδ_pos, hδ⟩
      have hδ' : C * δ ≤ δ * δ := by
        simpa [pow_two] using hδ
      nlinarith [hδ', hδ_pos]

/-- For the finite-VC localized envelope, its value at the critical radius is
no larger than the square of that radius. -/
lemma vcLocalizedPsi_criticalRadius_fp {K : ℝ} {d n : ℕ}
    (hK : 0 ≤ K) (hn : 0 < n) :
    vcLocalizedPsi K d n (criticalRadius (vcLocalizedPsi K d n))
      ≤ (criticalRadius (vcLocalizedPsi K d n)) ^ 2 := by
  let ρ := vcLocalizedSlope K d n
  have hρ_pos : 0 < ρ := vcLocalizedSlope_pos hK hn
  have hcrit_eq : criticalRadius (vcLocalizedPsi K d n) = ρ := by
    unfold vcLocalizedPsi
    exact criticalRadius_linear_eq hρ_pos
  rw [hcrit_eq]
  unfold vcLocalizedPsi ρ
  rw [pow_two]

/-- The bounded supremum of a real-valued quantity indexed by two choices is
unchanged when the two choices are optimized one after the other. -/
lemma ciSup_prod_eq_of_bddAbove {A B : Type*} [Nonempty A] [Nonempty B]
    (f : A → B → ℝ)
    (hb : BddAbove (Set.range fun p : A × B => f p.1 p.2)) :
    (⨆ p : A × B, f p.1 p.2) = ⨆ b : B, ⨆ a : A, f a b := by
  classical
  have hinner_bdd : ∀ b : B, BddAbove (Set.range fun a : A => f a b) := by
    intro b
    rcases hb with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact hM ⟨(a, b), rfl⟩
  have houter_bdd : BddAbove (Set.range fun b : B => ⨆ a : A, f a b) := by
    rcases hb with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    rintro _ ⟨b, rfl⟩
    exact ciSup_le fun a => hM ⟨(a, b), rfl⟩
  apply le_antisymm
  · refine ciSup_le ?_
    intro p
    exact le_trans (le_ciSup (hinner_bdd p.2) p.1) (le_ciSup houter_bdd p.2)
  · refine ciSup_le ?_
    intro b
    refine ciSup_le ?_
    intro a
    exact le_ciSup hb (a, b)

private lemma ciSup_mul_const_of_Icc {A : Type*} [Nonempty A]
    (c : A → ℝ) (b : ℝ) (hc_le : ∀ a, c a ≤ 1) (hb : 0 ≤ b) :
    (⨆ a : A, c a * b) = (⨆ a : A, c a) * b := by
  classical
  have hc_bdd : BddAbove (Set.range c) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact hc_le a
  have hcb_bdd : BddAbove (Set.range fun a : A => c a * b) := by
    refine ⟨b, ?_⟩
    rintro _ ⟨a, rfl⟩
    calc
      c a * b ≤ 1 * b := mul_le_mul_of_nonneg_right (hc_le a) hb
      _ = b := one_mul b
  apply le_antisymm
  · refine ciSup_le ?_
    intro a
    exact mul_le_mul_of_nonneg_right (le_ciSup hc_bdd a) hb
  · by_cases hb0 : b = 0
    · simp [hb0]
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hsup_le : (⨆ a : A, c a) ≤ (⨆ a : A, c a * b) / b := by
        refine ciSup_le ?_
        intro a
        exact (le_div_iff₀ hbpos).mpr (le_ciSup hcb_bdd a)
      exact (le_div_iff₀ hbpos).mp hsup_le

/-- Measurability bridge for the empirical Rademacher process of the finite-VC
localized star hull.

  The scale parameter in `starHullParam ι = Set.Icc 0 1 × ι` is uncountable.
  For measurability we first take its deterministic supremum, producing one
  constant coefficient for each countable `i : ι`, and then use the standard
  countable `Measurable.iSup` bridge. -/
  lemma vc_starHullZeroOut_empirical_rademacher_aemeasurable
      [MeasurableSpace 𝒳] [Nonempty ι] [Countable ι]
      (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
      (hF_meas : ∀ i, Measurable (F i))
      (μ : Measure 𝒳)
      (b r : ℝ) (hb : 0 ≤ b) (hbound : ∀ i x, |F i x| ≤ b)
      (n : ℕ) :
        AEMeasurable
          (fun ω : Fin n → 𝒳 =>
            empiricalRademacherComplexity n (starHullZeroOut F norm r) (id ∘ ω))
          (Measure.pi (fun _ => μ)) := by
    classical
    apply Measurable.aemeasurable
    unfold empiricalRademacherComplexity
    apply measurable_const.mul
    apply Finset.univ.measurable_sum
    intro σ _
    have hsup_eq :
        (fun ω : Fin n → 𝒳 =>
          ⨆ p : starHullParam ι,
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              starHullZeroOut F norm r p ((id ∘ ω) k)|) =
        fun ω : Fin n → 𝒳 =>
          ⨆ i : ι,
            starHullZeroOutScaleCoeff F norm r i *
              |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (ω k)| := by
      funext ω
      have hbdd :
          BddAbove (Set.range fun p : starHullParam ι =>
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              starHullZeroOut F norm r p ((id ∘ ω) k)|) := by
        simpa using
          starHullZeroOut_bddAbove_of_bound F norm hb n r (id ∘ ω)
            (fun i k => hbound i _) σ
      calc
        (⨆ p : starHullParam ι,
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              starHullZeroOut F norm r p ((id ∘ ω) k)|)
            = ⨆ i : ι, ⨆ a : Set.Icc (0 : ℝ) 1,
                |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
                  starHullZeroOut F norm r (a, i) (ω k)| := by
              unfold starHullParam
              simpa [Function.comp_def] using
                ciSup_prod_eq_of_bddAbove
                  (fun a : Set.Icc (0 : ℝ) 1 => fun i : ι =>
                    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
                      starHullZeroOut F norm r (a, i) (ω k)|)
                  hbdd
        _ = ⨆ i : ι,
              starHullZeroOutScaleCoeff F norm r i *
                |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (ω k)| := by
              congr
              ext i
              exact starHullZeroOut_inner_sup_eq F norm r ω σ i
    rw [hsup_eq]
    apply Measurable.iSup
    intro i
    apply measurable_const.mul
    apply Measurable.abs
    apply measurable_const.mul
    apply Finset.univ.measurable_sum
    intro k _
    apply measurable_const.mul
    exact (hF_meas i).comp (measurable_pi_apply k)

/-- Integrability of the finite-VC localized star-hull empirical Rademacher
process follows from the deterministic linear envelope once the residual
measurability bridge above is available. -/
  lemma vc_starHullZeroOut_empirical_rademacher_integrable
      [MeasurableSpace 𝒳] [Nonempty ι] [Countable ι]
      (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
      (μ : Measure 𝒳) [IsProbabilityMeasure μ]
      (hF_meas : ∀ i, Measurable (F i))
      (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ i x, |F i x| ≤ b)
      (K : ℝ) (d n : ℕ) (hK : (1 : ℝ) ≤ K) (hn : 0 < n)
      (Hvc : BinaryFactoredVCClass F d)
      (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm) :
    ∀ r : ℝ, vcLocalizedSlope K d n ≤ r →
      Integrable
        (fun ω : Fin n → 𝒳 =>
          empiricalRademacherComplexity n (starHullZeroOut F norm r) (id ∘ ω))
        (Measure.pi (fun _ => μ)) := by
  intro r hr
  let g : (Fin n → 𝒳) → ℝ :=
    fun ω => empiricalRademacherComplexity n (starHullZeroOut F norm r) (id ∘ ω)
  have hr_nonneg : 0 ≤ r :=
    le_trans (vcLocalizedSlope_nonneg K d n) hr
  have hg_meas :
      AEMeasurable g (Measure.pi (fun _ : Fin n => μ)) := by
      simpa [g] using
        vc_starHullZeroOut_empirical_rademacher_aemeasurable
          F norm hF_meas μ b r hb hbound n
  have hg_nonneg : ∀ᵐ ω : Fin n → 𝒳 ∂(Measure.pi (fun _ : Fin n => μ)),
      0 ≤ g ω := by
    exact Filter.Eventually.of_forall fun ω => by
      dsimp [g]
      unfold empiricalRademacherComplexity
      refine mul_nonneg ?_ ?_
      · positivity
      · refine Finset.sum_nonneg ?_
        intro σ _
        refine Real.iSup_nonneg ?_
        intro p
        exact abs_nonneg _
  have hg_upper : ∀ᵐ ω : Fin n → 𝒳 ∂(Measure.pi (fun _ : Fin n => μ)),
      g ω ≤ vcLocalizedPsi K d n r := by
    exact Filter.Eventually.of_forall fun ω => by
      dsimp [g]
      simpa using
        vc_starHullZeroOut_empirical_rademacher_le_linear
          F norm K d n hK Hvc Hloc (id ∘ ω) r hr_nonneg
  have hg_Icc : ∀ᵐ ω : Fin n → 𝒳 ∂(Measure.pi (fun _ : Fin n => μ)),
      g ω ∈ Set.Icc 0 (vcLocalizedPsi K d n r) := by
    filter_upwards [hg_nonneg, hg_upper] with ω h0 h1
    exact ⟨h0, h1⟩
  exact integrable_bounded 0 (vcLocalizedPsi K d n r) hg_meas hg_Icc

/-- Cardinality-bound variant of the integrability bridge for the localized
star-hull empirical Rademacher process. -/
  lemma vc_starHullZeroOut_empirical_rademacher_integrable_of_card
      [MeasurableSpace 𝒳] [Nonempty ι] [Countable ι]
      (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
      (π : ι → 𝒳 → Bool)
      (μ : Measure 𝒳) [IsProbabilityMeasure μ]
      (hF_meas : ∀ i, Measurable (F i))
      (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ i x, |F i x| ≤ b)
      (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
        ∀ i j, F i (S j) = φ j (π i (S j)))
      (K : ℝ) (dPi n : ℕ) (hK : (1 : ℝ) ≤ K) (hn : 0 < n)
      (hcard : ∀ (m : ℕ) (S : Fin m → 𝒳),
        (growthFamily π S).card ≤ (m + 1) ^ dPi)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm) :
    ∀ r : ℝ, vcLocalizedSlope K dPi n ≤ r →
      Integrable
        (fun ω : Fin n → 𝒳 =>
          empiricalRademacherComplexity n (starHullZeroOut F norm r) (id ∘ ω))
        (Measure.pi (fun _ => μ)) := by
  intro r hr
  let g : (Fin n → 𝒳) → ℝ :=
    fun ω => empiricalRademacherComplexity n (starHullZeroOut F norm r) (id ∘ ω)
  have hr_nonneg : 0 ≤ r :=
    le_trans (vcLocalizedSlope_nonneg K dPi n) hr
  have hg_meas :
      AEMeasurable g (Measure.pi (fun _ : Fin n => μ)) := by
      simpa [g] using
        vc_starHullZeroOut_empirical_rademacher_aemeasurable
          F norm hF_meas μ b r hb hbound n
  have hg_nonneg : ∀ᵐ ω : Fin n → 𝒳 ∂(Measure.pi (fun _ : Fin n => μ)),
      0 ≤ g ω := by
    exact Filter.Eventually.of_forall fun ω => by
      dsimp [g]
      unfold empiricalRademacherComplexity
      refine mul_nonneg ?_ ?_
      · positivity
      · refine Finset.sum_nonneg ?_
        intro σ _
        refine Real.iSup_nonneg ?_
        intro p
        exact abs_nonneg _
  have hg_upper : ∀ᵐ ω : Fin n → 𝒳 ∂(Measure.pi (fun _ : Fin n => μ)),
      g ω ≤ vcLocalizedPsi K dPi n r := by
    exact Filter.Eventually.of_forall fun ω => by
      dsimp [g]
      simpa using
        vc_starHullZeroOut_empirical_rademacher_le_linear_of_card
          F norm π hfactor K dPi n hK hcard Hloc (id ∘ ω) r hr_nonneg
  have hg_Icc : ∀ᵐ ω : Fin n → 𝒳 ∂(Measure.pi (fun _ : Fin n => μ)),
      g ω ∈ Set.Icc 0 (vcLocalizedPsi K dPi n r) := by
    filter_upwards [hg_nonneg, hg_upper] with ω h0 h1
    exact ⟨h0, h1⟩
  exact integrable_bounded 0 (vcLocalizedPsi K dPi n r) hg_meas hg_Icc

end Helpers

section Main

variable {ι : Type u} {𝒳 : Type v} [MeasurableSpace 𝒳]
variable [Nonempty 𝒳] [Nonempty ι] [Countable ι]

/-- **Finite-VC localized uniform deviation event.** For [a class of
measurable real-valued functions](hyp:hF_meas) [uniformly bounded in
absolute value by a nonnegative constant b](hyp:hb,hbound), with [a
nonnegative localization norm](hyp:hnorm_nonneg), [variance controlled by its
square](hyp:hvariance), [a localization constant K at least 1](hyp:hK) and [a
positive sample size n](hyp:hn), suppose [the class factors through a binary
Boolean family of VC dimension at most d](hyp:Hvc) and [has the samplewise
localization certificate](hyp:Hloc). For [a failure
probability δ in `(0,1]`](hyp:hδ,hδ'), writing ρ for the localized slope
`vcLocalizedSlope K d n`, if [ρ is at most b](hyp:hρ_le_b) and [the
peeling/log-domination side condition holds at one dyadic depth covering the class](hyp:hδ_dom),
then [there is a measurable event of probability at least `1 - δ` on which
every class member i with `0 ≤ norm (F i) ≤ b` satisfies the sharp
localized deviation bound `|n⁻¹ ∑ₖ F i(ωₖ) − 𝔼[F i]| ≤ 10ρ·norm(F i) +
5ρ²`](goal).

The arithmetic side condition `hδ_dom` is the peeling/log domination condition
from `localized_uniform_deviation_sharp`. -/
theorem vc_localized_deviation_event
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (hF_meas : ∀ i, Measurable (F i))
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ i x, |F i x| ≤ b)
    (hnorm_nonneg : ∀ i, 0 ≤ norm (F i))
    (hvariance : ∀ i, variance (F i) μ ≤ norm (F i) ^ 2)
    (K : ℝ) (d n : ℕ) (hK : (1 : ℝ) ≤ K) (hn : 0 < n)
    (Hvc : BinaryFactoredVCClass F d)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (hρ_le_b : vcLocalizedSlope K d n ≤ b)
    (hδ_dom : PeelingCondition b δ (vcLocalizedSlope K d n) n) :
    ∃ E : Set (Fin n → 𝒳), MeasurableSet E ∧
      Measure.pi (fun _ => μ) E ≥ 1 - ENNReal.ofReal δ ∧
      ∀ ω ∈ E, ∀ i : ι,
        0 ≤ norm (F i) →
        norm (F i) ≤ b →
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (ω k))
            - μ[fun x => F i x]|
          ≤ 10 * vcLocalizedSlope K d n * norm (F i)
            + 5 * (vcLocalizedSlope K d n) ^ 2 := by
  classical
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  let R : LocalizedRegime 𝒳 ι 𝒳 F norm μ id :=
    vcLocalizedRegime F norm μ id b hb (by simpa using hbound)
      (by simpa using hvariance) K d hK Hvc Hloc
  let ρ : ℝ := vcLocalizedSlope K d n
  have hρ_pos : 0 < ρ := vcLocalizedSlope_pos hK0 hn
  have hcrit_eq : criticalRadius (R.ψ n) = ρ := by
    dsimp [R, vcLocalizedRegime, vcLocalizedPsi, ρ]
    exact criticalRadius_linear_eq hρ_pos
  have hcrit_le_ρ : criticalRadius (R.ψ n) ≤ ρ := by
    rw [hcrit_eq]
  have hcrit_pos : 0 < criticalRadius (R.ψ n) := by
    rw [hcrit_eq]
    exact hρ_pos
  have hrad_bdd : ∀ r : ℝ, ρ ≤ r →
      ∀ S : Fin n → 𝒳, ∀ σ : Signs n,
        BddAbove (Set.range fun p : starHullParam ι =>
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            starHullZeroOut F norm r p (S k)|) := by
    intro r _hr
    exact fun S σ => starHullZeroOut_bddAbove_of_bound F norm hb n r S
      (fun i k => hbound i _) σ
  have hrad_int : ∀ r : ℝ, ρ ≤ r →
      Integrable
        (fun ω : Fin n → 𝒳 =>
          empiricalRademacherComplexity n (starHullZeroOut F norm r) (id ∘ ω))
        (Measure.pi (fun _ => μ)) := by
    intro r hr
    exact vc_starHullZeroOut_empirical_rademacher_integrable
      F norm μ hF_meas b hb hbound K d n hK hn Hvc Hloc r hr
  rcases localized_uniform_deviation_sharp
      F norm μ id measurable_id hF_meas hnorm_nonneg R hδ hδ' n hn
      (ρ := ρ) (Rmax := b)
      hcrit_le_ρ hρ_pos hcrit_pos hrad_bdd hrad_int
      (by simpa [PeelingCondition, R, ρ, vcLocalizedRegime] using hδ_dom) with
    ⟨E, hE_meas, hE_prob, hE_bound⟩
  refine ⟨E, hE_meas, hE_prob, ?_⟩
  intro ω hω i hi_nonneg hi_b
  simpa [R, ρ] using hE_bound ω hω i hi_nonneg hi_b

/-- **Growth-cardinality localized uniform deviation event.** For [a class of measurable
real-valued functions](hyp:hF_meas) [uniformly bounded in absolute value by a
nonnegative constant b](hyp:hb,hbound), with [a nonnegative localization
norm](hyp:hnorm_nonneg) and [variance controlled by its square](hyp:hvariance),
that [factors through a Boolean classifier π at every finite sample, for a
coordinate transform φ with `F i (S j) = φ j (π i (S j))`](hyp:hfactor), with
[a localization constant K at least 1](hyp:hK) and [a positive sample size
n](hyp:hn), suppose [the induced Boolean growth family satisfies the direct
cardinality bound `#growthFamily π S ≤ (m+1)^dPi` on every finite sample of size
m](hyp:hcard) and [the class has the samplewise localization
certificate](hyp:Hloc). For [a failure probability δ in
`(0,1]`](hyp:hδ,hδ'), writing ρ for the localized slope
`vcLocalizedSlope K dPi n`, if [ρ is at most b](hyp:hρ_le_b) and [the
peeling/log-domination side condition holds at one dyadic depth covering the
class](hyp:hδ_dom), then [there is a measurable event of probability at least
`1 - δ` on which every class member i with `0 ≤ norm (F i) ≤ b` satisfies the
sharp localized deviation bound
`|n⁻¹ ∑ₖ F i(ωₖ) − 𝔼[F i]| ≤ 10ρ·norm(F i) + 5ρ²`](goal).

This variant takes a direct cardinality bound on the binary trace family,
`#growthFamily π S ≤ (m + 1)^dPi`, matching finite policy trace bounds that
control growth functions without first packaging the class as a VC-dimension
bound. -/
theorem vc_localized_deviation_event_of_card
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (hF_meas : ∀ i, Measurable (F i))
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ i x, |F i x| ≤ b)
    (hnorm_nonneg : ∀ i, 0 ≤ norm (F i))
    (hvariance : ∀ i, variance (F i) μ ≤ norm (F i) ^ 2)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (K : ℝ) (dPi n : ℕ) (hK : (1 : ℝ) ≤ K) (hn : 0 < n)
    (hcard : ∀ (m : ℕ) (S : Fin m → 𝒳),
      (growthFamily π S).card ≤ (m + 1) ^ dPi)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (hρ_le_b : vcLocalizedSlope K dPi n ≤ b)
    (hδ_dom : PeelingCondition b δ (vcLocalizedSlope K dPi n) n) :
    ∃ E : Set (Fin n → 𝒳), MeasurableSet E ∧
      Measure.pi (fun _ => μ) E ≥ 1 - ENNReal.ofReal δ ∧
      ∀ ω ∈ E, ∀ i : ι,
        0 ≤ norm (F i) →
        norm (F i) ≤ b →
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (ω k))
            - μ[fun x => F i x]|
          ≤ 10 * vcLocalizedSlope K dPi n * norm (F i)
            + 5 * (vcLocalizedSlope K dPi n) ^ 2 := by
  classical
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  let R : LocalizedRegime 𝒳 ι 𝒳 F norm μ id :=
    vcLocalizedRegime_of_card
      F norm π μ id b hb (by simpa using hbound) (by simpa using hvariance)
      hfactor K dPi hK hcard Hloc
  let ρ : ℝ := vcLocalizedSlope K dPi n
  have hρ_pos : 0 < ρ := vcLocalizedSlope_pos hK0 hn
  have hcrit_eq : criticalRadius (R.ψ n) = ρ := by
    dsimp [R, vcLocalizedRegime_of_card, vcLocalizedPsi, ρ]
    exact criticalRadius_linear_eq hρ_pos
  have hcrit_le_ρ : criticalRadius (R.ψ n) ≤ ρ := by
    rw [hcrit_eq]
  have hcrit_pos : 0 < criticalRadius (R.ψ n) := by
    rw [hcrit_eq]
    exact hρ_pos
  have hrad_bdd : ∀ r : ℝ, ρ ≤ r →
      ∀ S : Fin n → 𝒳, ∀ σ : Signs n,
        BddAbove (Set.range fun p : starHullParam ι =>
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            starHullZeroOut F norm r p (S k)|) := by
    intro r _hr
    exact fun S σ => starHullZeroOut_bddAbove_of_bound F norm hb n r S
      (fun i k => hbound i _) σ
  have hrad_int : ∀ r : ℝ, ρ ≤ r →
      Integrable
        (fun ω : Fin n → 𝒳 =>
          empiricalRademacherComplexity n (starHullZeroOut F norm r) (id ∘ ω))
        (Measure.pi (fun _ => μ)) := by
    intro r hr
    exact vc_starHullZeroOut_empirical_rademacher_integrable_of_card
      F norm π μ hF_meas b hb hbound hfactor K dPi n hK hn hcard Hloc r hr
  rcases localized_uniform_deviation_sharp
      F norm μ id measurable_id hF_meas hnorm_nonneg R hδ hδ' n hn
      (ρ := ρ) (Rmax := b)
      hcrit_le_ρ hρ_pos hcrit_pos hrad_bdd hrad_int
      (by
        simpa [PeelingCondition, R, ρ, vcLocalizedRegime_of_card] using hδ_dom) with
    ⟨E, hE_meas, hE_prob, hE_bound⟩
  refine ⟨E, hE_meas, hE_prob, ?_⟩
  intro ω hω i hi_nonneg hi_b
  simpa [R, ρ] using hE_bound ω hω i hi_nonneg hi_b

/-- For [a measurable finite-VC function class](hyp:F,hF_meas,Hvc), [a nonnegative
localization norm](hyp:norm,hnorm_nonneg), [a probability law](hyp:μ), [a nonnegative
envelope and its uniform bound](hyp:b,hb,hbound), [the variance control](hyp:hvariance),
[a VC tuning constant](hyp:K,hK), [a positive VC dimension](hyp:d,hd), [the
samplewise localization certificate](hyp:Hloc), and [a confidence level in
`(0,1]`](hyp:δ,hδ,hδ'),
[eventually every logarithmic peeling depth covering the envelope yields the finite-VC
localized deviation event without a separate peeling-arithmetic hypothesis](goal). -/
theorem vc_localized_deviation_event_eventually
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (hF_meas : ∀ i, Measurable (F i))
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ i x, |F i x| ≤ b)
    (hnorm_nonneg : ∀ i, 0 ≤ norm (F i))
    (hvariance : ∀ i, variance (F i) μ ≤ norm (F i) ^ 2)
    (K : ℝ) (d : ℕ) (hK : (1 : ℝ) ≤ K) (hd : 0 < d)
    (Hvc : BinaryFactoredVCClass F d)
    (Hloc : SamplewiseLocalizedVCDudleyHypotheses F norm)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ L : ℕ,
      (L : ℝ) ≤ Real.log ((n : ℝ) + 1) →
      b ≤ vcLocalizedSlope K d n * (2 : ℝ) ^ L →
      vcLocalizedSlope K d n ≤ b →
      ∃ E : Set (Fin n → 𝒳), MeasurableSet E ∧
        Measure.pi (fun _ => μ) E ≥ 1 - ENNReal.ofReal δ ∧
        ∀ ω ∈ E, ∀ i : ι,
          0 ≤ norm (F i) →
          norm (F i) ≤ b →
          |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (ω k))
              - μ[fun x => F i x]|
            ≤ 10 * vcLocalizedSlope K d n * norm (F i)
              + 5 * (vcLocalizedSlope K d n) ^ 2 := by
  obtain ⟨n₀, hn₀⟩ := vcLocalizedSlope_peelingCondition_eventually hb hδ hδ' hK hd
  refine ⟨max n₀ 1, ?_⟩
  intro n hn L hL hcover hρ_le_b
  have hn₀n : n₀ ≤ n := (Nat.le_max_left n₀ 1).trans hn
  have hnpos : 0 < n :=
    Nat.zero_lt_one.trans_le ((Nat.le_max_right n₀ 1).trans hn)
  exact vc_localized_deviation_event F norm μ hF_meas b hb hbound
    hnorm_nonneg hvariance K d n hK hnpos Hvc Hloc hδ hδ' hρ_le_b
    (hn₀ n hn₀n L hL hcover)

end Main

end Concentration
end Stat
end Causalean

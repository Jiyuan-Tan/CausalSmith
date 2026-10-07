/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.RademacherBridge
public import Causalean.Stat.Concentration.Covering.VCUniformDeviation
public import Causalean.Stat.Concentration.Rademacher.LocalRademacher
public import Causalean.Stat.Concentration.VC.Rademacher.Conditional

/-!
# Countable reduction of population-localized star hulls

The star hull of a class F localized in population L² norm,
{a·f : f ∈ F, 0 ≤ a ≤ 1, ‖a·f‖_{L²(P)} ≤ r}, is indexed by an uncountable scalar even
when F is countable. This file replaces it by one function per member of F: the
multiple c_i·f_i with the largest admissible scalar c_i = min(1, r/‖f_i‖_{L²(P)})
(and c_i = 1 when ‖f_i‖_{L²(P)} = 0). The resulting family has the same empirical
Rademacher complexity and the same uniform deviation of squares as the full
localized star hull on every sample, so suprema over the localized star hull of
a countable class are measurable functions of the sample.

Localization uses `measureL2Dist P f 0`, the star hull is `starHullZeroOut`, and
the complexity is `localRademacherComplexity`.

## Main definitions

* `populationLocalizedRepresentative` — the family of largest admissible multiples.

## Main results

* `population_empiricalRademacher_eq_representative`,
  `population_squareDeviation_eq_representative` — the two samplewise equalities.
* `population_localizedRademacher_integrable` — measurability and integrability of the
  localized empirical Rademacher complexity.
* `population_localizedRademacher_isStarShapedEnvelope` — r ↦ R_n(r), the population-localized
  Rademacher complexity, is nonnegative, nondecreasing, and R_n(r)/r is nonincreasing.
-/

@[expose] public section

namespace Causalean.Stat.Concentration

open MeasureTheory

variable {𝒳 ι : Type*} [MeasurableSpace 𝒳]

/-- For [a measure P](hyp:P), [a real-valued function f](hyp:f) and [a real number a](hyp:a),
[the L²(P) norm is absolutely homogeneous: √(∫ (a·f)² dP) = |a| · √(∫ f² dP)](goal). -/
lemma measureL2Dist_zero_const_mul (P : Measure 𝒳) (f : 𝒳 → ℝ) (a : ℝ) :
    measureL2Dist P (fun x => a * f x) (fun _ => 0) =
      |a| * measureL2Dist P f (fun _ => 0) := by
  simp only [measureL2Dist, sub_zero, mul_pow]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

/-- For [a measure P](hyp:P), [a function class F](hyp:F), [a radius r ≥ 0](hyp:hr) and
[a member f_i of the class](hyp:i), [the largest scalar a between 0 and 1 with
‖a·f_i‖_{L²(P)} ≤ r equals 1 when ‖f_i‖_{L²(P)} = 0 and min(1, r / ‖f_i‖_{L²(P)})
otherwise](goal). -/
lemma population_scaleCoeff_eq (P : Measure 𝒳) (F : ι → 𝒳 → ℝ)
    {r : ℝ} (hr : 0 ≤ r) (i : ι) :
    starHullZeroOutScaleCoeff F (fun f => measureL2Dist P f (fun _ => 0)) r i =
      if measureL2Dist P (F i) (fun _ => 0) = 0 then 1
      else min 1 (r / measureL2Dist P (F i) (fun _ => 0)) := by
  classical
  have hhom (a : Set.Icc (0 : ℝ) 1) :
      measureL2Dist P (starHullEval F (a, i)) (fun _ => 0) =
        (a : ℝ) * measureL2Dist P (F i) (fun _ => 0) := by
    change measureL2Dist P (fun x => (a : ℝ) * F i x) (fun _ => 0) = _
    simpa only [abs_of_nonneg a.property.1] using
      measureL2Dist_zero_const_mul P (F i) (a : ℝ)
  simp only [starHullZeroOutScaleCoeff, hhom]
  by_cases hz : measureL2Dist P (F i) (fun _ => 0) = 0
  · simp only [hz, mul_zero, if_pos hr, if_true]
    apply le_antisymm
    · exact ciSup_le fun a => a.property.2
    · have hbdd : BddAbove (Set.range fun a : Set.Icc (0 : ℝ) 1 => (a : ℝ)) :=
        ⟨1, by rintro _ ⟨a, rfl⟩; exact a.property.2⟩
      exact le_ciSup hbdd (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1)
  · rw [if_neg hz]
    have hd : 0 < measureL2Dist P (F i) (fun _ => 0) :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    have hc : 0 ≤ min 1 (r / measureL2Dist P (F i) (fun _ => 0)) :=
      le_min (by norm_num) (div_nonneg hr hd.le)
    have hcm : min 1 (r / measureL2Dist P (F i) (fun _ => 0)) *
        measureL2Dist P (F i) (fun _ => 0) ≤ r :=
      (le_div_iff₀ hd).mp (min_le_right _ _)
    apply le_antisymm
    · apply ciSup_le
      intro a
      split_ifs with ha
      · exact le_min a.property.2 ((le_div_iff₀ hd).mpr ha)
      · exact hc
    · let a : Set.Icc (0 : ℝ) 1 := ⟨_, hc, min_le_left _ _⟩
      have hbdd : BddAbove (Set.range fun a : Set.Icc (0 : ℝ) 1 =>
          if (a : ℝ) * measureL2Dist P (F i) (fun _ => 0) ≤ r then (a : ℝ) else 0) := by
        refine ⟨1, ?_⟩
        rintro _ ⟨a, rfl⟩
        dsimp only
        split_ifs
        · exact a.property.2
        · norm_num
      simpa only [a, if_pos hcm] using le_ciSup hbdd a

/-- [The population-localized representative family](goal) of [a function class F](hyp:F)
under [a measure P](hyp:P) at [radius r](hyp:r) replaces each member f_i by c_i·f_i, where c_i
is the largest scalar between 0 and 1 with ‖c_i·f_i‖_{L²(P)} ≤ r.

It is indexed by the class itself, so it is countable whenever the class is, and it attains
the suprema of the full localized star hull.  When the radius is negative, no nonzero multiple
is admissible, so every representative is zero. -/
noncomputable def populationLocalizedRepresentative (P : Measure 𝒳)
    (F : ι → 𝒳 → ℝ) (r : ℝ) : ι → 𝒳 → ℝ :=
  fun i x =>
    starHullZeroOutScaleCoeff F (fun f => measureL2Dist P f (fun _ => 0)) r i * F i x

/-- For [a measure P](hyp:P), [a function class F](hyp:F) and [a radius r ≥ 0](hyp:hr),
[the representative of each member](hyp:i) has [L²(P) norm at most r](goal). -/
lemma populationLocalizedRepresentative_radius (P : Measure 𝒳)
    (F : ι → 𝒳 → ℝ) {r : ℝ} (hr : 0 ≤ r) (i : ι) :
    measureL2Dist P (populationLocalizedRepresentative P F r i) (fun _ => 0) ≤ r := by
  unfold populationLocalizedRepresentative
  rw [measureL2Dist_zero_const_mul,
    abs_of_nonneg (starHullZeroOutScaleCoeff_nonneg F _ r i),
    population_scaleCoeff_eq P F hr i]
  split_ifs with hz
  · simpa [hz] using hr
  · have hd : 0 < measureL2Dist P (F i) (fun _ => 0) :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    exact (le_div_iff₀ hd).mp (min_le_right _ _)

/-- For [a measure P](hyp:P) and [a function class F](hyp:F) whose [members are bounded in
absolute value by b](hyp:hbound), [every representative is bounded in absolute value by
b](goal). -/
lemma populationLocalizedRepresentative_bound (P : Measure 𝒳)
    (F : ι → 𝒳 → ℝ) {b r : ℝ} (hbound : ∀ i x, |F i x| ≤ b) :
    ∀ i x, |populationLocalizedRepresentative P F r i x| ≤ b := by
  intro i x
  rw [populationLocalizedRepresentative, abs_mul,
    abs_of_nonneg (starHullZeroOutScaleCoeff_nonneg F _ r i)]
  calc
    _ ≤ 1 * |F i x| := mul_le_mul_of_nonneg_right
      (starHullZeroOutScaleCoeff_le_one F _ r i) (abs_nonneg _)
    _ ≤ b := by simpa using hbound i x

/-- For [a measure P](hyp:P), [a function class F](hyp:F) with [measurable members](hyp:hmeas)
and [a radius r](hyp:r), [every representative is measurable](goal). -/
@[fun_prop]
lemma populationLocalizedRepresentative_measurable (P : Measure 𝒳)
    (F : ι → 𝒳 → ℝ) (hmeas : ∀ i, Measurable (F i)) (r : ℝ) :
    ∀ i, Measurable (populationLocalizedRepresentative P F r i) := by
  intro i
  exact measurable_const.mul (hmeas i)

/-- For [a measure P](hyp:P) and [a nonempty function class F](hyp:F) [bounded in absolute
value by b ≥ 0](hyp:hb,hbound), on [every sample](hyp:S) [the empirical Rademacher complexity
of the star hull localized to L²(P)-norm at most r equals that of the representative
family](goal). -/
lemma population_empiricalRademacher_eq_representative [Nonempty ι]
    (P : Measure 𝒳) (F : ι → 𝒳 → ℝ) {b r : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ i x, |F i x| ≤ b) {n : ℕ} (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n
        (starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r) S =
      empiricalRademacherComplexity n (populationLocalizedRepresentative P F r) S := by
  classical
  unfold empiricalRademacherComplexity
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  calc
    _ = ⨆ i : ι, ⨆ a : Set.Icc (0 : ℝ) 1,
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r (a, i) (S k)| := by
      exact ciSup_prod_eq_of_bddAbove
        (fun a : Set.Icc (0 : ℝ) 1 => fun i : ι =>
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r (a, i) (S k)|)
        (starHullZeroOut_bddAbove_of_bound F _ hb n r S (fun i k => hbound i _) σ)
    _ = _ := by
      simp_rw [starHullZeroOut_inner_sup_eq]
      congr 1
      ext i
      unfold populationLocalizedRepresentative
      have hsum :
          (∑ k : Fin n, (σ k : ℝ) *
            (starHullZeroOutScaleCoeff F (fun f => measureL2Dist P f (fun _ => 0)) r i *
              F i (S k))) =
          starHullZeroOutScaleCoeff F (fun f => measureL2Dist P f (fun _ => 0)) r i *
            ∑ k : Fin n, (σ k : ℝ) * F i (S k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hsum, mul_left_comm]
      simp only [abs_mul,
        abs_of_nonneg (starHullZeroOutScaleCoeff_nonneg F _ r i)]

/-- For [a probability law P](hyp:P), [a nonempty function class F](hyp:F) [bounded in
absolute value by b ≥ 0](hyp:hb,hbound) and [a radius r ≥ 0](hyp:hr), on [every sample
x₁,…,x_n](hyp:S) [the supremum of |(1/n) Σ_k g(x_k)² − ∫ g² dP| over the star hull localized
to L²(P)-norm at most r equals the same supremum over the representative family](goal). -/
lemma population_squareDeviation_eq_representative [Nonempty ι]
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    {b r : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ i x, |F i x| ≤ b) (hr : 0 ≤ r)
    {n : ℕ} (S : Fin n → 𝒳) :
    uniformDeviation n
        (fun p x => (starHullZeroOut F
          (fun f => measureL2Dist P f (fun _ => 0)) r p x) ^ 2) P id S =
      uniformDeviation n (fun i x => (populationLocalizedRepresentative P F r i x) ^ 2)
        P id S := by
  classical
  let d (f : 𝒳 → ℝ) : ℝ :=
    |(n : ℝ)⁻¹ * ∑ k : Fin n, (f (S k)) ^ 2 - ∫ x, (f x) ^ 2 ∂P|
  let c := starHullZeroOutScaleCoeff F (fun f => measureL2Dist P f (fun _ => 0)) r
  have hscale (a : ℝ) (f : 𝒳 → ℝ) :
      d (fun x => a * f x) = a ^ 2 * d f := by
    dsimp only [d]
    simp only [mul_pow, ← Finset.mul_sum, integral_const_mul]
    rw [mul_left_comm, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg a)]
  have hdbound (f : 𝒳 → ℝ) (hf : ∀ x, |f x| ≤ b) : d f ≤ 2 * b ^ 2 := by
    have hsq (x : 𝒳) : |f x ^ 2| ≤ b ^ 2 := by
      simpa only [abs_pow, sq_abs] using
        pow_le_pow_left₀ (abs_nonneg (f x)) (hf x) 2
    have havg : |(n : ℝ)⁻¹ * ∑ k : Fin n, f (S k) ^ 2| ≤ b ^ 2 := by
      simpa using absInner_le_of_bound (fun _ : Unit => fun x => f x ^ 2)
        (sq_nonneg b) (fun _ x => hsq x) n S (fun _ => ⟨1, by simp⟩) ()
    have hint : |∫ x, f x ^ 2 ∂P| ≤ b ^ 2 := by
      simpa [Real.norm_eq_abs, Measure.real] using
        (norm_integral_le_of_norm_le_const
          (Filter.Eventually.of_forall fun x => by
            simpa only [Real.norm_eq_abs] using hsq x) :
          ‖∫ x, f x ^ 2 ∂P‖ ≤ b ^ 2 * P.real Set.univ)
    exact (abs_sub _ _).trans (by linarith)
  have hrep (i : ι) : d (populationLocalizedRepresentative P F r i) =
      c i ^ 2 * d (F i) := hscale (c i) (F i)
  have hterm (p : starHullParam ι) :
      d (starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r p) ≤
        d (populationLocalizedRepresentative P F r p.2) := by
    rw [hrep]
    by_cases hp : measureL2Dist P (starHullEval F p) (fun _ => 0) ≤ r
    · have hcoeff : (p.1 : ℝ) ≤ c p.2 := by
        have hbcoeff : BddAbove (Set.range fun a : Set.Icc (0 : ℝ) 1 =>
            if measureL2Dist P (starHullEval F (a, p.2)) (fun _ => 0) ≤ r
            then (a : ℝ) else 0) := by
          refine ⟨1, ?_⟩
          rintro _ ⟨a, rfl⟩
          dsimp only
          split_ifs
          · exact a.property.2
          · norm_num
        have hp' : measureL2Dist P (starHullEval F (p.1, p.2)) (fun _ => 0) ≤ r := hp
        simpa only [c, starHullZeroOutScaleCoeff, if_pos hp'] using le_ciSup hbcoeff p.1
      have heq : d (starHullZeroOut F
          (fun f => measureL2Dist P f (fun _ => 0)) r p) =
          (p.1 : ℝ) ^ 2 * d (F p.2) := by
        have hf : starHullZeroOut F
            (fun f => measureL2Dist P f (fun _ => 0)) r p =
            fun x => (p.1 : ℝ) * F p.2 x := by
          funext x
          simp only [starHullZeroOut, if_pos hp, starHullEval]
        rw [hf]
        exact hscale (p.1 : ℝ) (F p.2)
      rw [heq]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ p.1.property.1 hcoeff 2) (abs_nonneg _)
    · simp only [starHullZeroOut, hp, if_false, d, zero_pow (by decide : 2 ≠ 0),
        Finset.sum_const_zero, mul_zero, integral_zero, sub_zero, abs_zero]
      exact mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have hfullbdd : BddAbove (Set.range fun p : starHullParam ι =>
      d (starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r p)) := by
    refine ⟨2 * b ^ 2, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact hdbound _ fun x => abs_starHullZeroOut_le_bound F _ hb (hbound p.2 x)
  have hrepbdd : BddAbove (Set.range fun i =>
      d (populationLocalizedRepresentative P F r i)) := by
    refine ⟨2 * b ^ 2, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hdbound _ (populationLocalizedRepresentative_bound P F hbound i)
  change (⨆ p : starHullParam ι, d (starHullZeroOut F
      (fun f => measureL2Dist P f (fun _ => 0)) r p)) =
    ⨆ i, d (populationLocalizedRepresentative P F r i)
  apply le_antisymm
  · exact ciSup_le fun p => (hterm p).trans (le_ciSup hrepbdd p.2)
  · apply ciSup_le
    intro i
    let a : Set.Icc (0 : ℝ) 1 := ⟨c i,
      starHullZeroOutScaleCoeff_nonneg F _ r i,
      starHullZeroOutScaleCoeff_le_one F _ r i⟩
    have ha : measureL2Dist P (starHullEval F (a, i)) (fun _ => 0) ≤ r :=
      populationLocalizedRepresentative_radius P F hr i
    have heq : starHullZeroOut F
        (fun f => measureL2Dist P f (fun _ => 0)) r (a, i) =
        populationLocalizedRepresentative P F r i := by
      funext x
      simp only [starHullZeroOut, if_pos ha]
      rfl
    simpa only [heq] using le_ciSup hfullbdd (a, i)

/-- For [a probability law P](hyp:P), [a nonempty countable class F](hyp:F) of [measurable
functions](hyp:hmeas) [bounded in absolute value by b ≥ 0](hyp:hb,hbound) and [a sample size
n](hyp:n), [the empirical Rademacher complexity of the star hull localized to L²(P)-norm at
most r is a measurable function of the sample and is integrable under n independent draws
from P](goal). -/
lemma population_localizedRademacher_integrable [Nonempty ι] [Countable ι]
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    (hmeas : ∀ i, Measurable (F i)) {b r : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ i x, |F i x| ≤ b) (n : ℕ) :
    Measurable (fun S : Fin n → 𝒳 => empiricalRademacherComplexity n
        (starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r) S) ∧
      Integrable (fun S : Fin n → 𝒳 => empiricalRademacherComplexity n
        (starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r) S)
        (Measure.pi (fun _ => P)) := by
  have heq : (fun S : Fin n → 𝒳 => empiricalRademacherComplexity n
      (starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r) S) =
      (fun S => empiricalRademacherComplexity n
        (populationLocalizedRepresentative P F r) S) := by
    funext S
    exact population_empiricalRademacher_eq_representative P F hb hbound S
  rw [heq]
  have hm := empiricalRademacherComplexity_measurable_countable
    (populationLocalizedRepresentative P F r)
    (populationLocalizedRepresentative_measurable P F hmeas r) n
  refine ⟨hm, Integrable.of_mem_Icc 0 b hm.aemeasurable ?_⟩
  exact Filter.Eventually.of_forall fun S =>
    empiricalRademacherComplexity_mem_Icc
      (populationLocalizedRepresentative P F r) hb
      (populationLocalizedRepresentative_bound P F hbound) n S

/-- For [a measure P](hyp:P) and [a nonempty function class F](hyp:F) [bounded in absolute
value by b ≥ 0](hyp:hb,hbound), [radii 0 < r₁ ≤ r₂](hyp:hr₁,hr) and [every sample](hyp:S),
[the empirical Rademacher complexities R̂(r) of the star hulls localized to L²(P)-norm at most
r satisfy r₁ · R̂(r₂) ≤ r₂ · R̂(r₁)](goal).

Equivalently R̂(r)/r is nonincreasing in r > 0. -/
lemma population_empiricalRademacher_rescale_le [Nonempty ι]
    (P : Measure 𝒳) (F : ι → 𝒳 → ℝ) {b r₁ r₂ : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ i x, |F i x| ≤ b) (hr₁ : 0 < r₁) (hr : r₁ ≤ r₂)
    {n : ℕ} (S : Fin n → 𝒳) :
    r₁ * empiricalRademacherComplexity n
        (starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r₂) S ≤
      r₂ * empiricalRademacherComplexity n
        (starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r₁) S := by
  classical
  have hr₂ : 0 ≤ r₂ := hr₁.le.trans hr
  let c := starHullZeroOutScaleCoeff F (fun f => measureL2Dist P f (fun _ => 0))
  have hc (i : ι) : r₁ * c r₂ i ≤ r₂ * c r₁ i := by
    dsimp only [c]
    rw [population_scaleCoeff_eq P F hr₂ i,
      population_scaleCoeff_eq P F hr₁.le i]
    split_ifs with hz
    · simpa using hr
    · rw [mul_min_of_nonneg _ _ hr₂, mul_one]
      apply le_min
      · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hr₁.le).trans
          (by simpa using hr)
      · calc
          r₁ * min 1 (r₂ / measureL2Dist P (F i) (fun _ => 0)) ≤
              r₁ * (r₂ / measureL2Dist P (F i) (fun _ => 0)) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hr₁.le
          _ = r₂ * (r₁ / measureL2Dist P (F i) (fun _ => 0)) := by ring
  have hfactor (r : ℝ) (σ : Signs n) (i : ι) :
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
        populationLocalizedRepresentative P F r i (S k)| =
      c r i * |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)| := by
    unfold populationLocalizedRepresentative
    have hsum : (∑ k : Fin n, (σ k : ℝ) * (c r i * F i (S k))) =
        c r i * ∑ k : Fin n, (σ k : ℝ) * F i (S k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    change |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c r i * F i (S k))| = _
    rw [hsum, mul_left_comm, abs_mul,
      abs_of_nonneg (starHullZeroOutScaleCoeff_nonneg F _ r i)]
  rw [population_empiricalRademacher_eq_representative P F hb hbound S,
    population_empiricalRademacher_eq_representative P F hb hbound S]
  unfold empiricalRademacherComplexity
  rw [mul_left_comm r₁, mul_left_comm r₂]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  rw [Real.mul_iSup_of_nonneg hr₁.le, Real.mul_iSup_of_nonneg hr₂]
  apply ciSup_mono
  · refine ⟨r₂ * b, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact mul_le_mul_of_nonneg_left
      (absInner_le_of_bound (populationLocalizedRepresentative P F r₁) hb
        (populationLocalizedRepresentative_bound P F hbound) n S σ i) hr₂
  · intro i
    rw [hfactor, hfactor, ← mul_assoc, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hc i) (abs_nonneg _)

/-- For [a probability law P](hyp:P), [a nonempty countable class F](hyp:F) of [measurable
functions](hyp:hmeas) [bounded in absolute value by b ≥ 0](hyp:hb,hbound) and [a sample size
n](hyp:n), [the map r ↦ R_n(r), the Rademacher complexity of the star hull localized to
L²(P)-norm at most r, is nonnegative and nondecreasing on r ≥ 0, and R_n(r)/r is
nonincreasing on r > 0](goal). -/
lemma population_localizedRademacher_isStarShapedEnvelope [Nonempty ι] [Countable ι]
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    (hmeas : ∀ i, Measurable (F i)) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ i x, |F i x| ≤ b) (n : ℕ) :
    IsStarShapedEnvelope
      (fun r => localRademacherComplexity F
        (fun f => measureL2Dist P f (fun _ => 0)) P id n r) := by
  refine ⟨fun r _ => localRademacherComplexity_nonneg F _ P id n r, ?_, ?_⟩
  · intro r₁ r₂ _ hr
    apply localRademacherComplexity_mono_r F _ P id n hr
    · intro S σ
      exact starHullZeroOut_bddAbove_of_bound F _ hb n r₂ S
        (fun i k => hbound i (S k)) σ
    · simpa only [Function.comp_id, Function.id_comp] using
        (population_localizedRademacher_integrable P F hmeas hb hbound n).2
  · intro r₁ r₂ hr₁ hr
    have hr₂ : 0 < r₂ := hr₁.trans_le hr
    apply (div_le_div_iff₀ hr₂ hr₁).2
    have hint₁ := (population_localizedRademacher_integrable
      P F hmeas (r := r₁) hb hbound n).2
    have hint₂ := (population_localizedRademacher_integrable
      P F hmeas (r := r₂) hb hbound n).2
    have hle := integral_mono (hint₂.const_mul r₁) (hint₁.const_mul r₂)
      (fun S => population_empiricalRademacher_rescale_le P F hb hbound hr₁ hr S)
    simp only [integral_const_mul] at hle
    simpa only [localRademacherComplexity, rademacherComplexity,
      Function.comp_id, Function.id_comp, mul_comm] using hle

end Causalean.Stat.Concentration

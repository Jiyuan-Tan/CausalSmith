/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.RademacherBounds
public import Causalean.Stat.Concentration.Localization.SquaredProcess

/-!
# Massart bound and self-bounding inequality under population localization

Let F be bounded by b and factor through Boolean labels of VC dimension at most d,
let G_r be its star hull localized to L²(P)-norm at most r, and q = (d·log(n+1) + 1)/n.

* On every sample, Massart's finite-class lemma applied to the at most (n+1)^d label
  patterns gives R̂_n(G_r) ≤ √(2q)·ρ_n, where ρ_n = sup over g ∈ G_r of ‖g‖_n is the
  empirical radius of the localized class. No bound on ρ_n is assumed.
* E ρ_n² ≤ r² + 8·b·R_n(r), by the expectation bound for the squared process.
* Combining the two, R_n(r)² ≤ 2q·(r² + 8·b·R_n(r)); solving this quadratic inequality
  gives R_n(r) ≤ 2·√q·r + 16·b·q at every radius r ≥ 0.

## Main results

* `population_massart_empirical_radius`, `population_empirical_radius_second_moment`
* `vcPopulation_localizedRademacher_le` — R_n(r) ≤ 2·√q·r + 16·b·q, the affine envelope
  `vcPopulationLocalizedPsi`.
-/

public section

namespace Causalean.Stat.Concentration

open MeasureTheory

variable {𝒳 ι : Type*} [MeasurableSpace 𝒳] [Nonempty ι] [Countable ι]

omit [Countable ι] in
/-- For [a law P](hyp:P), let [a nonempty class F](hyp:F) be [bounded in absolute value by
b ≥ 0](hyp:hb,hbound) and [factor through Boolean labels of VC dimension at most
d](hyp:d,Hvc), and let G_r be its star hull localized to L²(P)-norm at most r. For [n ≥ 1](hyp:n,hn)
and [every sample x₁,…,x_n](hyp:S), [the empirical Rademacher complexity of G_r is at most
√(2·(d·log(n+1) + 1)/n) · ρ_n, where ρ_n = sup over g ∈ G_r of the empirical L² norm
‖g‖_n](goal).

The supremum ρ_n is written over the representative family, which attains it. -/
lemma population_massart_empirical_radius
    (P : Measure 𝒳) (F : ι → 𝒳 → ℝ) {b r : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ i x, |F i x| ≤ b) (d n : ℕ) (hn : 0 < n)
    (Hvc : BinaryFactoredVCClass F d) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n
        (starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r) S ≤
      Real.sqrt (2 * (((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n)) *
        empiricalL2Radius (populationLocalizedRepresentative P F r) S := by
  classical
  let norm : (𝒳 → ℝ) → ℝ := fun f => measureL2Dist P f (fun _ => 0)
  let G := populationLocalizedRepresentative P F r
  let R := empiricalL2Radius G S
  let π := Hvc.π
  let W := starHullPatternClass F norm π S r
  have hGbound : ∀ i x, |G i x| ≤ b :=
    populationLocalizedRepresentative_bound P F hbound
  have hR : 0 ≤ R := (empiricalL2Radius_mem_Icc G hb hGbound S).1
  have hGbdd : BddAbove (Set.range fun i => empiricalNorm S (G i)) :=
    ⟨b, by rintro _ ⟨i, rfl⟩; exact empiricalNorm_le_of_envelope G hb hGbound S i⟩
  have hgf : (growthFamily π S).Nonempty := by
    refine ⟨restrictionPattern (π (Classical.arbitrary ι)) S, ?_⟩
    rw [mem_growthFamily_iff]
    exact ⟨_, rfl⟩
  have : Nonempty {A // A ∈ growthFamily π S} := by
    rcases hgf with ⟨A, hA⟩
    exact ⟨⟨A, hA⟩⟩
  have hWnorm (A : {A // A ∈ growthFamily π S}) :
      empiricalNorm S (W A) ≤ R := by
    rcases Hvc.factor S with ⟨φ, hφ⟩
    have : Nonempty {i : ι // restrictionPattern (π i) S = A.1} :=
      ⟨⟨growthFamilyRep π S A, growthFamilyRep_spec π S A⟩⟩
    have hnonneg : 0 ≤ empiricalNorm S (F (growthFamilyRep π S A)) :=
      Real.sqrt_nonneg _
    change empiricalNorm S
      (fun x => starHullPatternCoeff F norm π S r A * F (growthFamilyRep π S A) x) ≤ R
    rw [empiricalNorm_const_mul,
      abs_of_nonneg (starHullPatternCoeff_nonneg F norm π S r A)]
    unfold starHullPatternCoeff
    rw [← ciSup_mul_const_of_le_one _ _ hnonneg]
    apply ciSup_le
    intro i
    have heq : empiricalNorm S (F i.1) =
        empiricalNorm S (F (growthFamilyRep π S A)) := by
      have hp := sample_eq_growthFamilyRep_of_pattern (F := F) (π := π)
        (S := S) (φ := φ) hφ A i.2
      simp only [empiricalNorm, hp]
    rw [← heq]
    have hnorm : empiricalNorm S (G i.1) =
        starHullZeroOutScaleCoeff F norm r i.1 *
          empiricalNorm S (F i.1) := by
      exact (empiricalNorm_const_mul S _ (F i.1)).trans
        (by rw [abs_of_nonneg (starHullZeroOutScaleCoeff_nonneg F norm r i.1)])
    rw [← hnorm]
    exact le_ciSup hGbdd i.1
  have hfinite : empiricalRademacherComplexity n W S ≤
      (R / Real.sqrt (n : ℝ)) *
        Real.sqrt (2 * Real.log (2 * ((growthFamily π S).card : ℝ))) := by
    have h := empiricalRademacher_withAbs_finiteClass_le hn W S
      (Finset.univ : Finset {A // A ∈ growthFamily π S})
      Finset.univ_nonempty (R / Real.sqrt (n : ℝ)) (by
        intro A _
        rw [sqrt_sum_inv_abs_sq_eq_empiricalNorm_div_sqrt hn]
        exact div_le_div_of_nonneg_right (hWnorm A) (Real.sqrt_nonneg _))
    rw [empiricalRademacherComplexity_F_on_univ_eq W S] at h
    simpa using h
  have hcardpos := Finset.card_pos.mpr hgf
  have hcard := growthFamily_card_le_succ_pow_of_trace π d n (Or.inl Hvc.vcDim_le) S
  have hlog := log_two_growth_card_le π d n S hcardpos hcard
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hL : 0 ≤ 2 * Real.log (2 * ((growthFamily π S).card : ℝ)) := by
    have hone : (1 : ℝ) ≤ ((growthFamily π S).card : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hcardpos)
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  calc
    empiricalRademacherComplexity n (starHullZeroOut F norm r) S
        ≤ empiricalRademacherComplexity n W S :=
      starHullZeroOut_empirical_rademacher_le_patternClass F norm π Hvc.factor S r
    _ ≤ (R / Real.sqrt (n : ℝ)) *
        Real.sqrt (2 * Real.log (2 * ((growthFamily π S).card : ℝ))) := hfinite
    _ = Real.sqrt ((2 * Real.log (2 * ((growthFamily π S).card : ℝ))) / n) * R := by
      rw [Real.sqrt_div hL]
      ring
    _ ≤ Real.sqrt (2 * (((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n)) * R := by
      apply mul_le_mul_of_nonneg_right _ hR
      apply Real.sqrt_le_sqrt
      have h := div_le_div_of_nonneg_right hlog hnR.le
      convert h using 1 <;> (first | rfl | ring)

/-- Under [a probability law P](hyp:P), let [a nonempty countable class F](hyp:F) of
[measurable functions](hyp:hmeas) be [bounded in absolute value by b ≥ 0](hyp:hb,hbound), and
let G_r be its star hull localized to L²(P)-norm at most [r ≥ 0](hyp:hr). For [n ≥ 1](hyp:n,hn)
independent draws from P, [the empirical radius ρ_n = sup over g ∈ G_r of ‖g‖_n satisfies
E ρ_n² ≤ r² + 8·b·R_n(r), where R_n(r) is the Rademacher complexity of G_r](goal). -/
lemma population_empirical_radius_second_moment
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    (hmeas : ∀ i, Measurable (F i)) {b r : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ i x, |F i x| ≤ b) (hr : 0 ≤ r) (n : ℕ) (hn : 0 < n) :
    (∫ S, empiricalL2Radius (populationLocalizedRepresentative P F r) S ^ 2
        ∂Measure.pi (fun _ : Fin n => P)) ≤
      r ^ 2 + 8 * b * localRademacherComplexity F
        (fun f => measureL2Dist P f (fun _ => 0)) P id n r := by
  let G := populationLocalizedRepresentative P F r
  let μ := Measure.pi (fun _ : Fin n => P)
  have hGmeas := populationLocalizedRepresentative_measurable P F hmeas r
  have hGbound := populationLocalizedRepresentative_bound P F hbound (r := r)
  have hsqbound : ∀ i x, |G i x ^ 2| ≤ b ^ 2 := by
    intro i x
    simpa only [abs_pow, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (G i x)) (hGbound i x) 2
  have hpoint (S : Fin n → 𝒳) : empiricalL2Radius G S ^ 2 ≤
      r ^ 2 + uniformDeviation n (fun i x => G i x ^ 2) P id S := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let σ := Real.sqrt (r ^ 2 + ε)
    have hσ : 0 < σ := Real.sqrt_pos.2 (by positivity)
    have hσsq : σ ^ 2 = r ^ 2 + ε := Real.sq_sqrt (by positivity)
    have hrσ : r ≤ σ := by nlinarith [Real.sqrt_nonneg (r ^ 2 + ε)]
    have h := empiricalL2Radius_sq_le_uniformDeviation P G
      (U := b + σ + 1) hσ (by linarith)
      (fun i x => (hGbound i x).trans (by linarith))
      (fun i => (populationLocalizedRepresentative_radius P F hr i).trans hrσ) hn S
    rw [hσsq] at h
    linarith
  have hradInt : Integrable (fun S : Fin n → 𝒳 => empiricalL2Radius G S ^ 2) μ :=
    Integrable.of_mem_Icc 0 (b ^ 2)
      ((empiricalL2Radius_measurable G hGmeas n).pow_const 2).aemeasurable
      (ae_of_all _ fun S => ⟨sq_nonneg _, pow_le_pow_left₀
        (empiricalL2Radius_mem_Icc G hb hGbound S).1
        (empiricalL2Radius_mem_Icc G hb hGbound S).2 2⟩)
  have hdevInt : Integrable
      (fun S : Fin n → 𝒳 => uniformDeviation n (fun i x => G i x ^ 2) P id S) μ := by
    apply Integrable.of_mem_Icc 0 (2 * b ^ 2)
      (uniformDeviation_measurable id (fun i => (hGmeas i).pow_const 2)).aemeasurable
    apply ae_of_all
    intro S
    constructor
    · exact Real.iSup_nonneg fun i => abs_nonneg _
    · change (⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, G i (S k) ^ 2 -
          ∫ x, G i x ^ 2 ∂P|) ≤ 2 * b ^ 2
      apply ciSup_le
      intro i
      have havg : |(n : ℝ)⁻¹ * ∑ k : Fin n, G i (S k) ^ 2| ≤ b ^ 2 := by
        simpa using absInner_le_of_bound (fun _ : Unit => fun x => G i x ^ 2)
          (sq_nonneg b) (fun _ x => hsqbound i x) n S (fun _ => ⟨1, by simp⟩) ()
      have hint : |∫ x, G i x ^ 2 ∂P| ≤ b ^ 2 := by
        simpa [Real.norm_eq_abs, Measure.real] using
          (norm_integral_le_of_norm_le_const
            (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hsqbound i x) :
            ‖∫ x, G i x ^ 2 ∂P‖ ≤ b ^ 2 * P.real Set.univ)
      exact (abs_sub _ _).trans (by linarith)
  calc
    _ ≤ ∫ S, r ^ 2 + uniformDeviation n (fun i x => G i x ^ 2) P id S ∂μ :=
      integral_mono hradInt ((integrable_const _).add hdevInt) hpoint
    _ = r ^ 2 + ∫ S, uniformDeviation n (fun i x => G i x ^ 2) P id S ∂μ := by
      rw [integral_add (integrable_const _) hdevInt]
      simp [μ]
    _ ≤ _ := add_le_add le_rfl
      (population_squareDeviation_expectation_le P F hmeas hb hbound n hn)

/-- Under [a probability law P](hyp:P), let [a nonempty countable class F](hyp:F) of
[measurable functions](hyp:hmeas) be [bounded in absolute value by b ≥ 0](hyp:hb,hbound) and
[factor through Boolean labels of VC dimension at most d](hyp:d,Hvc). For [every radius
r ≥ 0](hyp:hr) and [sample size n ≥ 1](hyp:n,hn), [the Rademacher complexity R_n(r) of the star
hull of F localized to L²(P)-norm at most r satisfies R_n(r) ≤ 2·√q·r + 16·b·q, where
q = (d·log(n+1) + 1)/n](goal). -/
lemma vcPopulation_localizedRademacher_le
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    (hmeas : ∀ i, Measurable (F i)) {b r : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ i x, |F i x| ≤ b) (hr : 0 ≤ r) (d n : ℕ) (hn : 0 < n)
    (Hvc : BinaryFactoredVCClass F d) :
    localRademacherComplexity F (fun f => measureL2Dist P f (fun _ => 0)) P id n r ≤
      2 * Real.sqrt (((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n) * r +
        16 * b * (((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n) := by
  let μ := Measure.pi (fun _ : Fin n => P)
  let G := populationLocalizedRepresentative P F r
  let T : (Fin n → 𝒳) → ℝ := fun S => empiricalL2Radius G S
  let R := localRademacherComplexity F
    (fun f => measureL2Dist P f (fun _ => 0)) P id n r
  let q := (((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n)
  have hq : 0 ≤ q := by
    dsimp [q]
    apply div_nonneg _ (by positivity)
    have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    positivity
  have hR : 0 ≤ R := localRademacherComplexity_nonneg F _ P id n r
  have hGmeas := populationLocalizedRepresentative_measurable P F hmeas r
  have hGbound := populationLocalizedRepresentative_bound P F hbound (r := r)
  have hTmeas : Measurable T := empiricalL2Radius_measurable G hGmeas n
  have hTmem : ∀ S, T S ∈ Set.Icc 0 b :=
    fun S => empiricalL2Radius_mem_Icc G hb hGbound S
  have hTint : Integrable T μ := Integrable.of_mem_Icc 0 b hTmeas.aemeasurable
    (ae_of_all _ hTmem)
  have hTlp : MemLp T 2 μ := MemLp.of_bound hTmeas.aestronglyMeasurable b
    (ae_of_all _ fun S => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hTmem S).1] using (hTmem S).2)
  have hCS : (∫ S, T S ∂μ) ^ 2 ≤ ∫ S, T S ^ 2 ∂μ := by
    have hv := ProbabilityTheory.variance_nonneg T μ
    rw [ProbabilityTheory.variance_eq_sub hTlp] at hv
    simpa only [Pi.pow_apply] using (sub_nonneg.mp hv)
  have hmass : R ≤ Real.sqrt (2 * q) * ∫ S, T S ∂μ := by
    have hi := (population_localizedRademacher_integrable P F hmeas (r := r) hb hbound n).2
    have h := integral_mono hi (hTint.const_mul (Real.sqrt (2 * q)))
      (fun S => population_massart_empirical_radius P F hb hbound d n hn Hvc S)
    rw [integral_const_mul] at h
    simpa only [R, q, T, G, μ, localRademacherComplexity, rademacherComplexity,
      Function.id_comp] using h
  have hmassSq := pow_le_pow_left₀ hR hmass 2
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hq)] at hmassSq
  have hsecond : (∫ S, T S ^ 2 ∂μ) ≤ r ^ 2 + 8 * b * R :=
    population_empirical_radius_second_moment P F hmeas hb hbound hr n hn
  have hquad : R ^ 2 ≤ 2 * q * (r ^ 2 + 8 * b * R) :=
    hmassSq.trans (mul_le_mul_of_nonneg_left (hCS.trans hsecond) (by positivity))
  let A := 2 * Real.sqrt q * r
  let B := 16 * b * q
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hAsq : A ^ 2 = 4 * q * r ^ 2 := by
    dsimp [A]
    rw [mul_pow, mul_pow, Real.sq_sqrt hq]
    ring
  have hquad' : R ^ 2 ≤ A ^ 2 / 2 + B * R := by
    rw [hAsq]
    dsimp [B]
    nlinarith only [hquad]
  change R ≤ A + B
  by_contra h
  have hlt : A + B < R := lt_of_not_ge h
  have hprod := mul_pos (by linarith : 0 < R - B - A) (by linarith : 0 < R + A)
  nlinarith [mul_nonneg hB hA]

end Causalean.Stat.Concentration

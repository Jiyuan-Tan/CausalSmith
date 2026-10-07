/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Concentration.Localization.CountableReduction
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.LipschitzParametric.Scalar

/-!
# Population-localized classes of VC dimension zero

A class that factors through Boolean labels of VC dimension zero consists of a
single function, so its population-localized star hull reduces to one rescaled
function. For a single function g the Rademacher complexity is at most
‖g‖_{L²(P)} / √n: the second moment of a Rademacher sum is the sum of squares,
and Jensen's inequality passes from the empirical to the population norm.

## Main results

* `vcPopulation_dim_zero_eq` — all members of a class of VC dimension zero coincide.
* `constantClass_empiricalRademacher_le_empiricalNorm_div_sqrt`,
  `population_singletonRademacher_le` — the empirical and population bounds for one function.
* `vcPopulation_localizedRademacher_dim_zero` — the population-localized Rademacher
  complexity of a class of VC dimension zero is at most r / √n.
-/

public section

namespace Causalean.Stat.Concentration

open MeasureTheory

variable {𝒳 ι : Type*} [MeasurableSpace 𝒳]

omit [MeasurableSpace 𝒳] in
/-- If [a function class factors through Boolean labels of VC dimension zero](hyp:F,Hvc),
then [any two of its members](hyp:i,j) are [the same function](goal). -/
lemma vcPopulation_dim_zero_eq (F : ι → 𝒳 → ℝ)
    (Hvc : BinaryFactoredVCClass F 0) (i j : ι) : F i = F j := by
  classical
  funext x
  let S : Fin 1 → 𝒳 := fun _ => x
  have hcard : (growthFamily Hvc.π S).card ≤ 1 := by
    simpa using growthFamily_card_le_succ_pow_of_trace Hvc.π 0 1
      (Or.inl Hvc.vcDim_le) S
  have hpattern : restrictionPattern (Hvc.π i) S =
      restrictionPattern (Hvc.π j) S :=
    Finset.card_le_one.mp hcard _ (mem_growthFamily_iff.mpr ⟨i, rfl⟩)
      _ (mem_growthFamily_iff.mpr ⟨j, rfl⟩)
  have hlabel : Hvc.π i x = Hvc.π j x := by
    apply Bool.eq_iff_iff.mpr
    change Hvc.π i (S 0) = true ↔ Hvc.π j (S 0) = true
    rw [← restrictionPattern_mem_iff, hpattern, restrictionPattern_mem_iff]
  obtain ⟨φ, hφ⟩ := Hvc.factor S
  calc
    F i x = φ 0 (Hvc.π i x) := hφ i 0
    _ = φ 0 (Hvc.π j x) := by rw [hlabel]
    _ = F j x := (hφ j 0).symm

omit [MeasurableSpace 𝒳] in
/-- For [a positive sample size](hyp:hn) and [a sample](hyp:S), [the empirical Rademacher
complexity of the class whose every member is one fixed function g](hyp:g) satisfies
[R̂_n({g}) ≤ ‖g‖_n / √n, where ‖g‖_n is the empirical L² norm of g on the sample](goal). -/
lemma constantClass_empiricalRademacher_le_empiricalNorm_div_sqrt
    [Nonempty ι] (g : 𝒳 → ℝ) {n : ℕ} (hn : 0 < n) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (fun _ : ι => g) S ≤
      empiricalNorm S g / Real.sqrt (n : ℝ) := by
  classical
  let : Nonempty (Signs n) := ⟨fun _ => ⟨1, by simp⟩⟩
  have hc : 0 < (Fintype.card (Signs n) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Signs n)
  let v : Fin n → ℝ := fun k => (n : ℝ)⁻¹ * g (S k)
  let Z : Signs n → ℝ := fun σ => ∑ k : Fin n, (σ k : ℝ) * v k
  have hpair : ∀ k l : Fin n,
      (∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ)) =
        if k = l then (Fintype.card (Signs n) : ℝ) else 0 := by
    intro k l
    by_cases hkl : k = l
    · subst l
      have hdiag : ∀ σ : Signs n, (σ k : ℝ) * (σ k : ℝ) = 1 := by
        intro σ
        nlinarith [abs_sigma (σ k), sq_abs (σ k : ℝ)]
      simp [hdiag]
    · simp [hkl, rademacher_orthogonality n k l hkl]
  have hsecond : (∑ σ : Signs n, Z σ ^ 2) =
      (Fintype.card (Signs n) : ℝ) * ∑ k : Fin n, v k ^ 2 := by
    calc
      _ = ∑ σ : Signs n, ∑ k : Fin n, ∑ l : Fin n,
          ((σ k : ℝ) * (σ l : ℝ)) * (v k * v l) := by
        apply Finset.sum_congr rfl
        intro σ _
        simp only [Z, pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = ∑ k : Fin n, ∑ l : Fin n,
          (∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ)) * (v k * v l) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = _ := by
        simp [hpair, Finset.mul_sum, pow_two]
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Signs n))
    (fun σ => |Z σ|) (fun _ => (1 : ℝ))
  have habs : (∑ σ : Signs n, |Z σ|) ≤
      (Fintype.card (Signs n) : ℝ) * Real.sqrt (∑ k : Fin n, v k ^ 2) := by
    simpa only [mul_one, sq_abs, Finset.sum_const, one_pow, Finset.card_univ,
      nsmul_eq_mul, hsecond, Real.sqrt_mul hc.le, mul_one,
      mul_right_comm (Real.sqrt (Fintype.card (Signs n))),
      ← mul_assoc, Real.mul_self_sqrt hc.le] using hCS
  calc
    _ = (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, |Z σ| := by
      simp only [empiricalRademacherComplexity, ciSup_const]
      congr 1
      apply Finset.sum_congr rfl
      intro σ _
      congr 1
      simp only [Z, v, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ Real.sqrt (∑ k : Fin n, v k ^ 2) := by
      calc
        _ ≤ (Fintype.card (Signs n) : ℝ)⁻¹ *
            ((Fintype.card (Signs n) : ℝ) * Real.sqrt (∑ k : Fin n, v k ^ 2)) :=
          mul_le_mul_of_nonneg_left habs (inv_nonneg.mpr hc.le)
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    _ = empiricalNorm S g / Real.sqrt (n : ℝ) := by
      rw [← sqrt_sum_inv_abs_sq_eq_empiricalNorm_div_sqrt hn S g]
      simp only [v, mul_pow, sq_abs]

/-- Under [a probability law P](hyp:P), for [a measurable function g](hyp:g,hmeas)
[bounded in absolute value by b ≥ 0](hyp:hb,hbound) and [a positive sample size n](hyp:n,hn),
[the Rademacher complexity of the one-function class {g} over n independent draws from P is
at most ‖g‖_{L²(P)} / √n](goal). -/
lemma population_singletonRademacher_le
    (P : Measure 𝒳) [IsProbabilityMeasure P] (g : 𝒳 → ℝ)
    (hmeas : Measurable g) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ x, |g x| ≤ b) (n : ℕ) (hn : 0 < n) :
    rademacherComplexity n (fun _ : Unit => g) P id ≤
      measureL2Dist P g (fun _ => 0) / Real.sqrt (n : ℝ) := by
  let μ := Measure.pi (fun _ : Fin n => P)
  have hTmeas : Measurable (fun S : Fin n → 𝒳 => empiricalNorm S g) := by
    unfold empiricalNorm
    fun_prop
  have hTint : Integrable (fun S : Fin n → 𝒳 => empiricalNorm S g) μ :=
    Integrable.of_mem_Icc 0 b hTmeas.aemeasurable
      (ae_of_all _ fun S => ⟨Real.sqrt_nonneg _,
        empiricalNorm_le_of_envelope (fun _ : Unit => g) hb (fun _ => hbound) S ()⟩)
  have hsqInt : Integrable (fun x => g x ^ 2) P :=
    Integrable.of_mem_Icc 0 (b ^ 2) (hmeas.pow_const 2).aemeasurable
      (ae_of_all _ fun x => ⟨sq_nonneg _, by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (g x)) (hbound x) 2⟩)
  have hmean : (∫ S, empiricalNorm S g ∂μ) ≤ measureL2Dist P g (fun _ => 0) := by
    simpa only [measureL2Dist, sub_zero] using
      Causalean.Stat.expected_empiricalNorm_le P hn g hmeas hsqInt
  have hRint : Integrable
      (fun S => empiricalRademacherComplexity n (fun _ : Unit => g) S) μ :=
    Integrable.of_mem_Icc 0 b
      (empiricalRademacherComplexity_measurable_countable (fun _ : Unit => g)
        (fun _ => hmeas) n).aemeasurable
      (ae_of_all _ fun S => empiricalRademacherComplexity_mem_Icc
        (fun _ : Unit => g) hb (fun _ => hbound) n S)
  calc
    _ ≤ ∫ S, empiricalNorm S g / Real.sqrt (n : ℝ) ∂μ := by
      simpa only [rademacherComplexity, Function.id_comp, μ] using
        integral_mono hRint (hTint.div_const _)
          (constantClass_empiricalRademacher_le_empiricalNorm_div_sqrt g hn)
    _ = (∫ S, empiricalNorm S g ∂μ) / Real.sqrt (n : ℝ) := integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right hmean (Real.sqrt_nonneg _)

/-- Under [a probability law P](hyp:P), let [a nonempty class of measurable
functions](hyp:F,hmeas) be [bounded in absolute value by b ≥ 0](hyp:hb,hbound) and
[factor through Boolean labels of VC dimension zero](hyp:Hvc). Then for [every radius
r ≥ 0](hyp:hr) and [positive sample size n](hyp:n,hn), [the Rademacher complexity of the star
hull localized to L²(P)-norm at most r is at most r / √n](goal). -/
lemma vcPopulation_localizedRademacher_dim_zero [Nonempty ι]
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    (hmeas : ∀ i, Measurable (F i)) {b r : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ i x, |F i x| ≤ b) (hr : 0 ≤ r) (n : ℕ) (hn : 0 < n)
    (Hvc : BinaryFactoredVCClass F 0) :
    localRademacherComplexity F (fun f => measureL2Dist P f (fun _ => 0)) P id n r ≤
      r / Real.sqrt (n : ℝ) := by
  classical
  let i₀ : ι := Classical.arbitrary ι
  let g := populationLocalizedRepresentative P F r i₀
  have hF : F = fun _ => F i₀ := by
    funext i
    exact vcPopulation_dim_zero_eq F Hvc i i₀
  have hG : populationLocalizedRepresentative P F r = fun _ => g := by
    rw [hF]
    rfl
  have heq : localRademacherComplexity F
      (fun f => measureL2Dist P f (fun _ => 0)) P id n r =
      rademacherComplexity n (fun _ : Unit => g) P id := by
    unfold localRademacherComplexity rademacherComplexity
    simp only [Function.id_comp]
    apply integral_congr_ae
    apply ae_of_all
    intro S
    rw [population_empiricalRademacher_eq_representative P F hb hbound S, hG]
    simp [empiricalRademacherComplexity]
  rw [heq]
  exact (population_singletonRademacher_le P g
    (populationLocalizedRepresentative_measurable P F hmeas r i₀) hb
    (populationLocalizedRepresentative_bound P F hbound i₀) n hn).trans
    (div_le_div_of_nonneg_right (populationLocalizedRepresentative_radius P F hr i₀)
      (Real.sqrt_nonneg _))

end Causalean.Stat.Concentration

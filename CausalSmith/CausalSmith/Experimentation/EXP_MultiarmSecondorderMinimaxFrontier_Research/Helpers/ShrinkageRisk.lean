import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.ScoreDesign
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.FirstOrderUpper
import Causalean.Experimentation.DesignBased.ProductMeasure
import Causalean.Experimentation.DesignBased.InProb
import Mathlib.Probability.Moments.SubGaussian

/-! Finite-sample risk improvement of the clipped contrast-score shrinkage rule. -/

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

variable {K n : ℕ}

-- @node: normalizedUpperUnitScore
/-- The normalized upper unit score rescales a unit’s contrast-weighted inverse-probability score by the contrast norm. -/
noncomputable def normalizedUpperUnitScore (c : Contrast ℝ K) (t : RespType K)
    (a : Arm K) : ℝ := upperUnitScore c t a / (Lc c / 2)

-- @node: normalizedTypeScore
/-- The normalized response-type score is the conditional mean of the normalized upper unit score over its treatment assignment. -/
noncomputable def normalizedTypeScore (c : Contrast ℝ K) (t : RespType K) : ℝ :=
  (∑ a, c a * if t a then 1 else 0) / (Lc c / 2)

-- @node: normalizedUpperUnitScore_mem_Icc
/-- [the normalized upper unit score belongs to closed interval](goal). -/
lemma normalizedUpperUnitScore_mem_Icc (c : Contrast ℝ K) (t : RespType K)
    (a : Arm K) : normalizedUpperUnitScore c t a ∈ Set.Icc (-1) 1 := by
  classical
  by_cases hc : c a = 0
  · simp [normalizedUpperUnitScore, upperUnitScore, qStar, hc]
  · have hq : qStar c a ≠ 0 :=
      div_ne_zero (abs_ne_zero.mpr hc) (ne_of_gt (Lc_pos c))
    have habs : |normalizedUpperUnitScore c t a| = 1 := by
      simp only [normalizedUpperUnitScore, upperUnitScore, hq, if_false]
      simp_rw [abs_div, abs_mul]
      have hhalf : |(if t a then (1 : ℝ) else 0) - 1 / 2| = 1 / 2 := by
        by_cases ht : t a <;> simp [ht] <;> norm_num
      rw [hhalf]
      simp only [qStar, abs_div, abs_abs, abs_of_pos (Lc_pos c)]
      norm_num
      field_simp [abs_ne_zero.mpr hc, ne_of_gt (Lc_pos c)]
    exact abs_le.mp habs.le

-- @node: normalizedUpperUnitScore_mean
/-- [the normalized upper unit score mean property holds](goal). -/
lemma normalizedUpperUnitScore_mean (c : Contrast ℝ K) (t : RespType K) :
    (qStarDesign c).E (normalizedUpperUnitScore c t) = normalizedTypeScore c t := by
  rw [show normalizedUpperUnitScore c t = fun a => (Lc c / 2)⁻¹ * upperUnitScore c t a by
    funext a; simp [normalizedUpperUnitScore, div_eq_mul_inv, mul_comm]]
  rw [Causalean.Experimentation.DesignBased.FiniteDesign.E_const_mul,
    upperUnitScore_mean]
  simp [normalizedTypeScore, div_eq_mul_inv, mul_comm]

-- @node: normalizedUpperUnitScore_secondMoment
/-- [the normalized upper unit score second moment property holds](goal). -/
lemma normalizedUpperUnitScore_secondMoment (c : Contrast ℝ K) (t : RespType K) :
    (qStarDesign c).E (fun a => normalizedUpperUnitScore c t a ^ 2) = 1 := by
  have hh : Lc c / 2 ≠ 0 := by positivity [Lc_pos c]
  rw [show (fun a => normalizedUpperUnitScore c t a ^ 2) =
      fun a => (Lc c / 2)⁻¹ ^ 2 * upperUnitScore c t a ^ 2 by
    funext a; simp [normalizedUpperUnitScore, div_eq_mul_inv]; ring]
  rw [Causalean.Experimentation.DesignBased.FiniteDesign.E_const_mul,
    upperUnitScore_secondMoment]
  unfold C0
  field_simp [ne_of_gt (Lc_pos c)]
  norm_num

-- @node: lambdaC_le_abs_normalizedTypeScore
/-- [the stated side condition holds](hyp:ht), [the lambda c is at most abs normalized type score](goal). -/
lemma lambdaC_le_abs_normalizedTypeScore (c : Contrast ℝ K) (t : RespType K)
    (ht : normalizedTypeScore c t ≠ 0) :
    lambdaC c ≤ |normalizedTypeScore c t| := by
  let s := ∑ a, c a * if t a then 1 else 0
  have hs : s ≠ 0 := by
    intro h
    apply ht
    rw [show normalizedTypeScore c t = s / (Lc c / 2) by rfl, h]
    norm_num
  unfold lambdaC
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨u, hu, rfl⟩
    exact div_nonneg (abs_nonneg _) (by positivity [Lc_pos c])
  · refine ⟨t, hs, ?_⟩
    have hhpos : 0 < Lc c / 2 := by positivity [Lc_pos c]
    rw [show normalizedTypeScore c t = s / (Lc c / 2) by rfl, abs_div,
      abs_of_pos hhpos]

-- @node: normalizedTypeScore_sq_lower
/-- [the normalized type score squared lower property holds](goal). -/
lemma normalizedTypeScore_sq_lower (c : Contrast ℝ K) (t : RespType K) :
    lambdaC c * |normalizedTypeScore c t| ≤ normalizedTypeScore c t ^ 2 := by
  by_cases ht : normalizedTypeScore c t = 0
  · simp [ht]
  · calc
      lambdaC c * |normalizedTypeScore c t| ≤
          |normalizedTypeScore c t| * |normalizedTypeScore c t| :=
        mul_le_mul_of_nonneg_right (lambdaC_le_abs_normalizedTypeScore c t ht)
          (abs_nonneg _)
      _ = normalizedTypeScore c t ^ 2 := by rw [← sq_abs, pow_two]

-- @node: normalizedScore_tail_bound
/-- [the population size is positive](hyp:hn), [the stated side condition holds](hyp:hu), [the normalized score tail bound property holds](goal). -/
lemma normalizedScore_tail_bound (c : Contrast ℝ K) (z : Schedule K n)
    (hn : 0 < n) (u : ℝ) (hu : 0 ≤ u) :
    let D := Causalean.Experimentation.DesignBased.prodDesign
      (fun _ : Unit n => qStarDesign c)
    let X : Assign K n → ℝ := fun A => (n : ℝ)⁻¹ *
      ∑ i, normalizedUpperUnitScore c (z i) (A i)
    let θ := (n : ℝ)⁻¹ * ∑ i, normalizedTypeScore c (z i)
    D.Pr (fun A => |X A - θ| ≥ u) ≤ 2 * Real.exp (-(n : ℝ) * u ^ 2 / 2) := by
  classical
  dsimp only
  let D := Causalean.Experimentation.DesignBased.prodDesign
    (fun _ : Unit n => qStarDesign c)
  let η : Unit n → ℝ := fun i => normalizedTypeScore c (z i)
  let Y : Unit n → Assign K n → ℝ :=
    fun i A => normalizedUpperUnitScore c (z i) (A i) - η i
  have hindep : iIndepFun Y D.toMeasure := by
    have h := Causalean.Experimentation.DesignBased.iIndepFun_prodDesign_eval
      (fun _ : Unit n => qStarDesign c)
    exact h.comp (fun i a => normalizedUpperUnitScore c (z i) a - η i)
      (fun _ => measurable_of_finite _)
  have hsubG : ∀ i : Unit n,
      HasSubgaussianMGF (Y i) 1 D.toMeasure := by
    intro i
    have hg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (X := Y i) (a := -1 - η i) (b := 1 - η i)
      (D.aemeasurable_toMeasure _)
      (by
        filter_upwards [] with A
        rcases normalizedUpperUnitScore_mem_Icc c (z i) (A i) with ⟨hl, hr⟩
        exact ⟨by dsimp [Y]; linarith, by dsimp [Y]; linarith⟩)
      (by
        rw [← D.E_eq_integral]
        dsimp [Y, η]
        rw [D.E_sub, D.E_const,
          Causalean.Experimentation.DesignBased.FiniteDesign.E_prod_apply,
          normalizedUpperUnitScore_mean]
        ring)
    convert hg using 1 <;> norm_num
  have hsumG : HasSubgaussianMGF (fun A => ∑ i, Y i A)
      (∑ _i : Unit n, 1) D.toMeasure := by
    exact ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun hindep
      (c := fun _ => 1) (s := (Finset.univ : Finset (Unit n)))
      (fun i _ => hsubG i)
  have hsum_pos := hsumG.measure_ge_le (ε := (n : ℝ) * u)
    (mul_nonneg (Nat.cast_nonneg n) hu)
  have hsum_neg := hsumG.neg.measure_ge_le (ε := (n : ℝ) * u)
    (mul_nonneg (Nat.cast_nonneg n) hu)
  have hpos : D.Pr (fun A => u ≤
      (n : ℝ)⁻¹ * ∑ i, normalizedUpperUnitScore c (z i) (A i) -
        (n : ℝ)⁻¹ * ∑ i, normalizedTypeScore c (z i)) ≤
      Real.exp (-(n : ℝ) * u ^ 2 / 2) := by
    rw [D.Pr_eq_measureReal]
    convert hsum_pos using 1
    · congr 1
      ext A
      simp only [Y, η, Finset.sum_sub_distrib]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp [hnR]
    · congr 1
      norm_num
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp [hnR]
  have hneg : D.Pr (fun A => u ≤ -((n : ℝ)⁻¹ *
      ∑ i, normalizedUpperUnitScore c (z i) (A i) -
        (n : ℝ)⁻¹ * ∑ i, normalizedTypeScore c (z i))) ≤
      Real.exp (-(n : ℝ) * u ^ 2 / 2) := by
    rw [D.Pr_eq_measureReal]
    convert hsum_neg using 1
    · congr 1
      ext A
      simp only [Y, η, Finset.sum_sub_distrib, Pi.neg_apply]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp [hnR]
    · congr 1
      norm_num
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp [hnR]
  calc
    D.Pr (fun A => |(n : ℝ)⁻¹ * ∑ i, normalizedUpperUnitScore c (z i) (A i) -
        (n : ℝ)⁻¹ * ∑ i, normalizedTypeScore c (z i)| ≥ u) ≤
        D.Pr (fun A => u ≤ (n : ℝ)⁻¹ * ∑ i, normalizedUpperUnitScore c (z i) (A i) -
          (n : ℝ)⁻¹ * ∑ i, normalizedTypeScore c (z i)) +
        D.Pr (fun A => u ≤ -((n : ℝ)⁻¹ * ∑ i, normalizedUpperUnitScore c (z i) (A i) -
          (n : ℝ)⁻¹ * ∑ i, normalizedTypeScore c (z i))) := by
      simp only [le_abs]
      exact D.Pr_or_le _ _
    _ ≤ 2 * Real.exp (-(n : ℝ) * u ^ 2 / 2) := by linarith

-- @node: finiteDesign_cov_monotone_comp_nonneg
/-- [the stated side condition holds](hyp:hg), [the finite design cov monotone comp is nonnegative](goal). -/
lemma finiteDesign_cov_monotone_comp_nonneg {Ω : Type*} [Fintype Ω]
    (D : Causalean.Experimentation.DesignBased.FiniteDesign Ω)
    (X : Ω → ℝ) (g : ℝ → ℝ) (hg : Monotone g) :
    0 ≤ D.Cov X (fun ω => g (X ω)) := by
  classical
  have hpair : 0 ≤ ∑ a, ∑ b,
      D.p a * D.p b * ((X a - X b) * (g (X a) - g (X b))) := by
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    apply mul_nonneg (mul_nonneg (D.p_nonneg a) (D.p_nonneg b))
    rcases le_total (X a) (X b) with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h) (sub_nonpos.mpr (hg h))
    · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (hg h))
  have hid : (∑ a, ∑ b,
      D.p a * D.p b * ((X a - X b) * (g (X a) - g (X b)))) =
      2 * D.Cov X (fun ω => g (X ω)) := by
    rw [D.Cov_eq]
    unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
    have hdiag : (∑ a, ∑ b, D.p a * D.p b * (X a * g (X a))) =
        ∑ a, D.p a * (X a * g (X a)) := by
      calc
        _ = ∑ a, (D.p a * (X a * g (X a))) * ∑ b, D.p b := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := by rw [D.p_sum]; simp
    have hcross₂ : (∑ a, ∑ b, D.p a * D.p b * (X a * g (X b))) =
        (∑ a, D.p a * X a) * ∑ b, D.p b * g (X b) := by
      calc
        _ = ∑ a, (D.p a * X a) * ∑ b, D.p b * g (X b) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := by rw [Finset.sum_mul]
    have hcross₁ : (∑ a, ∑ b, D.p a * D.p b * (X b * g (X a))) =
        (∑ b, D.p b * X b) * ∑ a, D.p a * g (X a) := by
      rw [Finset.sum_comm]
      simpa [mul_comm] using hcross₂
    have hdiag' : (∑ a, ∑ b, D.p a * D.p b * (X b * g (X b))) =
        ∑ b, D.p b * (X b * g (X b)) := by
      rw [Finset.sum_comm]
      simpa [mul_comm] using hdiag
    rw [show (∑ a, ∑ b, D.p a * D.p b *
        ((X a - X b) * (g (X a) - g (X b)))) =
        2 * ((∑ a, D.p a * (X a * g (X a))) -
          (∑ a, D.p a * X a) * ∑ b, D.p b * g (X b)) by
      simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
      rw [hdiag, hcross₁, hcross₂, hdiag']
      ring]
  rw [hid] at hpair
  linarith

-- @node: finiteDesign_cov_perturbation_lower
/-- [the stated side condition holds](hyp:hmean), [the stated side condition holds](hyp:hcenter), [the stated side condition holds](hyp:hH), [the finite design cov perturbation lower property holds](goal). -/
lemma finiteDesign_cov_perturbation_lower {Ω : Type*} [Fintype Ω]
    (D : Causalean.Experimentation.DesignBased.FiniteDesign Ω)
    (X H : Ω → ℝ) (m δ : ℝ)
    (hmean : D.E X = m) (hcenter : ∀ ω, |X ω - m| ≤ 2)
    (hH : ∀ ω, |H ω| ≤ Causalean.Experimentation.DesignBased.FiniteDesign.ind
      (fun ω => δ ≤ |X ω - m|) ω) :
    D.Var X - 2 * D.Pr (fun ω => δ ≤ |X ω - m|) ≤
      D.Cov X (fun ω => X ω + H ω) := by
  classical
  have hEH : |D.E (fun ω => (X ω - m) * H ω)| ≤
      2 * D.Pr (fun ω => δ ≤ |X ω - m|) := by
    rw [show D.E (fun ω => (X ω - m) * H ω) =
        ∑ ω, D.p ω * ((X ω - m) * H ω) by rfl]
    calc
      |∑ ω, D.p ω * ((X ω - m) * H ω)| ≤
          ∑ ω, |D.p ω * ((X ω - m) * H ω)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω, D.p ω * (2 * Causalean.Experimentation.DesignBased.FiniteDesign.ind
          (fun ω => δ ≤ |X ω - m|) ω) := by
        apply Finset.sum_le_sum
        intro ω _
        rw [abs_mul, abs_of_nonneg (D.p_nonneg ω), abs_mul]
        apply mul_le_mul_of_nonneg_left _ (D.p_nonneg ω)
        exact mul_le_mul (hcenter ω) (hH ω)
          (abs_nonneg _) (by norm_num)
      _ = 2 * D.Pr (fun ω => δ ≤ |X ω - m|) := by
        unfold Causalean.Experimentation.DesignBased.FiniteDesign.Pr
          Causalean.Experimentation.DesignBased.FiniteDesign.E
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        ring
  have hdecomp : D.Cov X (fun ω => X ω + H ω) =
      D.Var X + D.E (fun ω => (X ω - m) * H ω) := by
    rw [← D.Cov_self, D.Cov_eq, D.Cov_eq, hmean, D.E_add]
    rw [show D.E (fun z => X z * (X z + H z)) =
        D.E (fun z => X z * X z) + D.E (fun z => X z * H z) by
      rw [← D.E_add]
      apply D.E_congr
      intro z
      ring]
    rw [show D.E (fun ω => (X ω - m) * H ω) = D.E (fun ω => X ω * H ω) - m * D.E H by
      rw [← D.E_const_mul, ← D.E_sub]
      apply D.E_congr
      intro z
      ring]
    rw [hmean]
    ring
  rw [hdecomp]
  linarith [neg_abs_le (D.E (fun ω => (X ω - m) * H ω))]

-- @node: normalizedTypeScore_mem_Icc
/-- [the normalized type score belongs to closed interval](goal). -/
lemma normalizedTypeScore_mem_Icc (c : Contrast ℝ K) (t : RespType K) :
    normalizedTypeScore c t ∈ Set.Icc (-1) 1 := by
  classical
  rw [← normalizedUpperUnitScore_mean]
  constructor
  · calc
      -1 = (qStarDesign c).E (fun _ => (-1 : ℝ)) := by simp
      _ ≤ (qStarDesign c).E (normalizedUpperUnitScore c t) := by
        unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left
          (normalizedUpperUnitScore_mem_Icc c t a).1 ((qStarDesign c).p_nonneg a)
  · calc
      (qStarDesign c).E (normalizedUpperUnitScore c t) ≤
          (qStarDesign c).E (fun _ => (1 : ℝ)) := by
        unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left
          (normalizedUpperUnitScore_mem_Icc c t a).2 ((qStarDesign c).p_nonneg a)
      _ = 1 := by simp

-- @node: clippedScore_monotone
/-- [the clipped score monotone property holds](goal). -/
lemma clippedScore_monotone (b : ℝ) : Monotone (fun x : ℝ => max (-b) (min x b)) := by
  intro x y hxy
  exact max_le_max (le_refl _) (min_le_min hxy (le_refl _))

-- @node: clippedScore_abs_le
/-- [the stated side condition holds](hyp:hb), [the clipped score abs is at most property holds](goal). -/
lemma clippedScore_abs_le {b x : ℝ} (hb : 0 ≤ b) : |max (-b) (min x b)| ≤ b := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (neg_le_self hb) (min_le_right _ _)⟩

-- @node: clippedScore_eq_self
/-- [the observed count satisfies its stated condition](hyp:hx), [the clipped score equals self](goal). -/
lemma clippedScore_eq_self {b x : ℝ} (hx : |x| ≤ b) : max (-b) (min x b) = x := by
  rw [abs_le] at hx
  rw [min_eq_left hx.2, max_eq_right hx.1]

-- @node: clippedScore_sub_abs_le
/-- [the stated side condition holds](hyp:hb), [the observed count satisfies its stated condition](hyp:hx), [the stated side condition holds](hyp:hb1), [the clipped score sub abs is at most property holds](goal). -/
lemma clippedScore_sub_abs_le {b x : ℝ} (hb : 0 ≤ b) (hx : |x| ≤ 1) (hb1 : b ≤ 1) :
    |max (-b) (min x b) - x| ≤ 1 := by
  by_cases hl : x < -b
  · rw [min_eq_left (by linarith), max_eq_left hl.le,
      abs_of_nonneg (by linarith : 0 ≤ -b - x)]
    rw [abs_le] at hx
    linarith
  · by_cases hr : b < x
    · rw [min_eq_right hr.le, max_eq_right (by linarith),
        abs_of_nonpos (sub_nonpos.mpr hr.le)]
      rw [abs_le] at hx
      linarith
    · rw [clippedScore_eq_self (by rw [abs_le]; exact ⟨le_of_not_gt hl, le_of_not_gt hr⟩)]
      simp

-- @node: normalizedScore_mean_variance
/-- [the population size is positive](hyp:hn), [the normalized score mean variance property holds](goal). -/
lemma normalizedScore_mean_variance (c : Contrast ℝ K) (z : Schedule K n)
    (hn : 0 < n) :
    let D := Causalean.Experimentation.DesignBased.prodDesign
      (fun _ : Unit n => qStarDesign c)
    let X : Assign K n → ℝ := fun A => (n : ℝ)⁻¹ *
      ∑ i, normalizedUpperUnitScore c (z i) (A i)
    let θ := (n : ℝ)⁻¹ * ∑ i, normalizedTypeScore c (z i)
    D.E X = θ ∧
      D.Var X = (n : ℝ)⁻¹ - (n : ℝ)⁻¹ ^ 2 *
        ∑ i, normalizedTypeScore c (z i) ^ 2 := by
  classical
  dsimp only
  let D := Causalean.Experimentation.DesignBased.prodDesign
    (fun _ : Unit n => qStarDesign c)
  let X : Assign K n → ℝ := fun A => (n : ℝ)⁻¹ *
    ∑ i, normalizedUpperUnitScore c (z i) (A i)
  have hmean : D.E X = (n : ℝ)⁻¹ * ∑ i, normalizedTypeScore c (z i) := by
    dsimp [X, D]
    rw [Causalean.Experimentation.DesignBased.FiniteDesign.E_const_mul,
      Causalean.Experimentation.DesignBased.FiniteDesign.E_sum]
    simp_rw [Causalean.Experimentation.DesignBased.FiniteDesign.E_prod_apply,
      normalizedUpperUnitScore_mean]
  refine ⟨hmean, ?_⟩
  change D.Var X = _
  rw [show X = fun A => ∑ i, (n : ℝ)⁻¹ *
      normalizedUpperUnitScore c (z i) (A i) by
    funext A
    simp only [X]
    rw [Finset.mul_sum],
    Causalean.Experimentation.DesignBased.FiniteDesign.Var_prod_linear_comb]
  simp_rw [Causalean.Experimentation.DesignBased.FiniteDesign.Var_eq,
    normalizedUpperUnitScore_secondMoment,
    normalizedUpperUnitScore_mean]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    (∑ i, (n : ℝ)⁻¹ ^ 2 * (1 - normalizedTypeScore c (z i) ^ 2)) =
        (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) - ∑ i, normalizedTypeScore c (z i) ^ 2) := by
      rw [show (n : ℝ) = ∑ _i : Unit n, (1 : ℝ) by simp,
        ← Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by
      field_simp [hnR]

-- @node: normalizedScore_bounds
/-- [the population size is positive](hyp:hn), [the normalized score bounds property holds](goal). -/
lemma normalizedScore_bounds (c : Contrast ℝ K) (z : Schedule K n) (hn : 0 < n) :
    let X : Assign K n → ℝ := fun A => (n : ℝ)⁻¹ *
      ∑ i, normalizedUpperUnitScore c (z i) (A i)
    let θ := (n : ℝ)⁻¹ * ∑ i, normalizedTypeScore c (z i)
    (∀ A, |X A| ≤ 1) ∧ |θ| ≤ 1 := by
  classical
  dsimp only
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro A
    rw [abs_le]
    constructor
    · calc
        -1 = (n : ℝ)⁻¹ * ∑ _i : Unit n, (-1 : ℝ) := by
          simp [hnR.ne']
        _ ≤ (n : ℝ)⁻¹ * ∑ i, normalizedUpperUnitScore c (z i) (A i) := by
          gcongr
          exact (normalizedUpperUnitScore_mem_Icc c (z _) (A _)).1
    · calc
        (n : ℝ)⁻¹ * ∑ i, normalizedUpperUnitScore c (z i) (A i) ≤
            (n : ℝ)⁻¹ * ∑ _i : Unit n, (1 : ℝ) := by
          gcongr
          exact (normalizedUpperUnitScore_mem_Icc c (z _) (A _)).2
        _ = 1 := by simp [hnR.ne']
  · rw [abs_le]
    constructor
    · calc
        -1 = (n : ℝ)⁻¹ * ∑ _i : Unit n, (-1 : ℝ) := by
          simp [hnR.ne']
        _ ≤ (n : ℝ)⁻¹ * ∑ i, normalizedTypeScore c (z i) := by
          gcongr
          exact (normalizedTypeScore_mem_Icc c (z _)).1
    · calc
        (n : ℝ)⁻¹ * ∑ i, normalizedTypeScore c (z i) ≤
            (n : ℝ)⁻¹ * ∑ _i : Unit n, (1 : ℝ) := by
          gcongr
          exact (normalizedTypeScore_mem_Icc c (z _)).2
        _ = 1 := by simp [hnR.ne']

-- @node: finiteDesign_mse_shrinkage_upper
/-- [the stated side condition holds](hyp:hmean), [the stated side condition holds](hyp:heps), [the stated side condition holds](hyp:hg), [the finite design mse shrinkage upper property holds](goal). -/
lemma finiteDesign_mse_shrinkage_upper {Ω : Type*} [Fintype Ω]
    (D : Causalean.Experimentation.DesignBased.FiniteDesign Ω)
    (X : Ω → ℝ) (g : ℝ → ℝ) (θ eps b : ℝ)
    (hmean : D.E X = θ) (heps : 0 ≤ eps) (hg : ∀ x, |g x| ≤ b) :
    D.mse (fun ω => X ω - eps * g (X ω)) θ ≤
      D.Var X - 2 * eps * D.Cov X (fun ω => g (X ω)) + eps ^ 2 * b ^ 2 := by
  classical
  have hEg : D.E (fun ω => g (X ω) ^ 2) ≤ b ^ 2 := by
    calc
      D.E (fun ω => g (X ω) ^ 2) ≤ D.E (fun _ => b ^ 2) := by
        unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (D.p_nonneg ω)
        have hb : 0 ≤ b := (abs_nonneg (g (X ω))).trans (hg (X ω))
        calc
          g (X ω) ^ 2 = |g (X ω)| ^ 2 := (sq_abs _).symm
          _ ≤ b ^ 2 := (sq_le_sq₀ (abs_nonneg _) hb).2 (hg (X ω))
      _ = b ^ 2 := by simp
  rw [Causalean.Experimentation.DesignBased.FiniteDesign.mse,
    Causalean.Experimentation.DesignBased.FiniteDesign.Var_eq,
    Causalean.Experimentation.DesignBased.FiniteDesign.Cov_eq, hmean]
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hmean' : (∑ ω, D.p ω * X ω) = θ := hmean
  have hid : (∑ ω, D.p ω * ((X ω - eps * g (X ω) - θ) ^ 2)) =
      (∑ ω, D.p ω * X ω ^ 2) - 2 * eps * (∑ ω, D.p ω * (X ω * g (X ω))) +
        2 * eps * θ * (∑ ω, D.p ω * g (X ω)) +
        eps ^ 2 * (∑ ω, D.p ω * g (X ω) ^ 2) - θ ^ 2 := by
    calc
      (∑ ω, D.p ω * ((X ω - eps * g (X ω) - θ) ^ 2)) =
        ∑ ω, (D.p ω * X ω ^ 2 - 2 * eps * (D.p ω * (X ω * g (X ω))) +
          -2 * θ * (D.p ω * X ω) + 2 * eps * θ * (D.p ω * g (X ω)) +
          eps ^ 2 * (D.p ω * g (X ω) ^ 2) + D.p ω * θ ^ 2) := by
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        have hcross : (∑ x, 2 * eps * (D.p x * (X x * g (X x)))) =
            2 * eps * ∑ x, D.p x * (X x * g (X x)) := by
          rw [Finset.mul_sum]
        have hmeanSum : (∑ x, -2 * θ * (D.p x * X x)) =
            -2 * θ * ∑ x, D.p x * X x := by
          rw [Finset.mul_sum]
        have hgSum : (∑ x, 2 * eps * θ * (D.p x * g (X x))) =
            2 * eps * θ * ∑ x, D.p x * g (X x) := by
          rw [show 2 * eps * θ = (2 * eps) * θ by ring, Finset.mul_sum]
        have hg2Sum : (∑ x, eps ^ 2 * (D.p x * g (X x) ^ 2)) =
            eps ^ 2 * ∑ x, D.p x * g (X x) ^ 2 := by
          rw [Finset.mul_sum]
        have hconst : (∑ ω, D.p ω * θ ^ 2) = θ ^ 2 := by
          rw [← Finset.sum_mul, D.p_sum, one_mul]
        rw [hcross, hmeanSum, hgSum, hg2Sum, hmean', hconst]
        ring
  rw [hid]
  have hscaled := mul_le_mul_of_nonneg_left hEg (sq_nonneg eps)
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E at hscaled
  nlinarith

-- @node: shrunkenClippedScore_abs_le_one
/-- [the stated side condition holds](hyp:hb), [the stated side condition holds](hyp:hb1), [the stated side condition holds](hyp:heps), [the stated side condition holds](hyp:heps1), [the observed count satisfies its stated condition](hyp:hx), [the shrunken clipped score abs is at most one](goal). -/
lemma shrunkenClippedScore_abs_le_one {b eps x : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hx : |x| ≤ 1) :
    |x - eps * max (-b) (min x b)| ≤ 1 := by
  rw [abs_le] at hx ⊢
  have heb : eps * b ≤ 1 := calc
    eps * b ≤ 1 * b := mul_le_mul_of_nonneg_right heps1 hb
    _ = b := one_mul b
    _ ≤ 1 := hb1
  by_cases hl : x < -b
  · rw [min_eq_left (by linarith), max_eq_left hl.le]
    constructor <;> nlinarith [mul_nonneg heps hb]
  · by_cases hr : b < x
    · rw [min_eq_right hr.le, max_eq_right (by linarith)]
      constructor <;> nlinarith [mul_nonneg heps hb]
    · rw [clippedScore_eq_self (by rw [abs_le]; exact ⟨le_of_not_gt hl, le_of_not_gt hr⟩)]
      by_cases hx0 : 0 ≤ x
      · constructor <;> nlinarith [mul_nonneg heps hx0,
          mul_nonneg (sub_nonneg.mpr heps1) hx0]
      · have hnx : 0 ≤ -x := by linarith
        constructor <;> nlinarith [mul_nonneg heps hnx,
          mul_nonneg (sub_nonneg.mpr heps1) hnx]

-- @node: shrinkagePowerIdentities
/-- [the population size is positive](hyp:hn), [the shrinkage power identities property holds](goal). -/
lemma shrinkagePowerIdentities (n : ℕ) (hn : 0 < n) :
    let b := (n : ℝ) ^ (-(1 / 3 : ℝ))
    b / n = (n : ℝ) ^ (-(4 / 3 : ℝ)) ∧
      b ^ 4 = (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
  dsimp only
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    rw [← Real.rpow_add hnR]
    congr 1
    norm_num
  · rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hnR.le]
    congr 1
    norm_num

-- @node: shrinkageProcedure_risk_bound_of_tail
set_option maxHeartbeats 800000 in
/-- [the population size is positive](hyp:hn), [the stated side condition holds](hyp:htail), [the shrinkage procedure risk bound when tail property holds](goal). -/
lemma shrinkageProcedure_risk_bound_of_tail (K n : ℕ) (c : Contrast ℝ K)
    (hn : 0 < n)
    (htail : 4 * Real.sqrt (lambdaC c) * (n : ℝ) *
      Real.exp (-(n : ℝ) ^ (1 / 3 : ℝ) / 8) ≤
        Real.sqrt (lambdaC c) / 2 - lambdaC c / 16) :
    Causalean.Stat.worstCaseRisk
      (fun (p : Procedure K n c) (z : Schedule K n) => labeledRisk c p z)
      (shrinkageProcedure K n c) ≤
        C0 c * ((n : ℝ)⁻¹ - kappaC c * (n : ℝ) ^ (-(4 / 3 : ℝ))) := by
  classical
  let D := Causalean.Experimentation.DesignBased.prodDesign
    (fun _ : Unit n => qStarDesign c)
  let b : ℝ := (n : ℝ) ^ (-(1 / 3 : ℝ))
  let eps : ℝ := Real.sqrt (lambdaC c) / 4 * b
  let g : ℝ → ℝ := fun x => max (-b) (min x b)
  have hlambda := (lambdaC_pos_le_one c).1
  have hlambda_le := (lambdaC_pos_le_one c).2
  have hsqrt0 : 0 ≤ Real.sqrt (lambdaC c) := Real.sqrt_nonneg _
  have hsqrt_le : Real.sqrt (lambdaC c) ≤ 1 := by
    nlinarith [Real.sq_sqrt hlambda.le]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb0 : 0 ≤ b := Real.rpow_nonneg hnR.le _
  have hb1 : b ≤ 1 := by
    dsimp [b]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast hn
    · norm_num
  have heps0 : 0 ≤ eps := mul_nonneg (div_nonneg hsqrt0 (by norm_num)) hb0
  have heps1 : eps ≤ 1 / 4 := by
    dsimp [eps]
    have hmul : Real.sqrt (lambdaC c) * b ≤ 1 := calc
      Real.sqrt (lambdaC c) * b ≤ 1 * b :=
        mul_le_mul_of_nonneg_right hsqrt_le hb0
      _ = b := one_mul b
      _ ≤ 1 := hb1
    nlinarith
  have hsqrt_sq : Real.sqrt (lambdaC c) ^ 2 = lambdaC c :=
    Real.sq_sqrt hlambda.le
  rcases shrinkagePowerIdentities n hn with ⟨hbdiv, hb4⟩
  apply Causalean.Stat.worstCaseRisk_le
  intro z
  let X : Assign K n → ℝ := fun A => (n : ℝ)⁻¹ *
    ∑ i, normalizedUpperUnitScore c (z i) (A i)
  let θ : ℝ := (n : ℝ)⁻¹ * ∑ i, normalizedTypeScore c (z i)
  let Q : ℝ := ∑ i, normalizedTypeScore c (z i) ^ 2
  have hmv := normalizedScore_mean_variance c z hn
  change D.E X = θ ∧ D.Var X = (n : ℝ)⁻¹ - (n : ℝ)⁻¹ ^ 2 * Q at hmv
  rcases hmv with ⟨hmean, hvar⟩
  have hbounds := normalizedScore_bounds c z hn
  change (∀ A, |X A| ≤ 1) ∧ |θ| ≤ 1 at hbounds
  rcases hbounds with ⟨hX, htheta⟩
  have hQ : lambdaC c * (n : ℝ) * |θ| ≤ Q := by
    calc
      lambdaC c * (n : ℝ) * |θ| =
          lambdaC c * |∑ i, normalizedTypeScore c (z i)| := by
        dsimp [θ]
        rw [abs_mul, abs_inv, abs_of_pos hnR]
        field_simp [hnR.ne']
      _ ≤ lambdaC c * ∑ i, |normalizedTypeScore c (z i)| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, lambdaC c * |normalizedTypeScore c (z i)| := by
        rw [Finset.mul_sum]
      _ ≤ Q := by
        dsimp [Q]
        exact Finset.sum_le_sum fun i _ => normalizedTypeScore_sq_lower c (z i)
  have hcov0 : 0 ≤ D.Cov X (fun A => g (X A)) :=
    finiteDesign_cov_monotone_comp_nonneg D X g (clippedScore_monotone b)
  have hmse := finiteDesign_mse_shrinkage_upper D X g θ eps b hmean heps0
    (fun x => clippedScore_abs_le hb0)
  have himprovement : D.mse (fun A => X A - eps * g (X A)) θ ≤
      (n : ℝ)⁻¹ - kappaC c * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
    rw [hvar] at hmse
    by_cases hlocal : |θ| ≤ b / 2
    · have htailprob := normalizedScore_tail_bound c z hn (b / 2)
          (div_nonneg hb0 (by norm_num))
      change D.Pr (fun A => |X A - θ| ≥ b / 2) ≤ _ at htailprob
      have hexp : Real.exp (-(n : ℝ) * (b / 2) ^ 2 / 2) =
          Real.exp (-(n : ℝ) ^ (1 / 3 : ℝ) / 8) := by
        congr 1
        have hb2 : b ^ 2 = (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
          dsimp [b]
          rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
          congr 1
          norm_num
        have hpow : (n : ℝ) * b ^ 2 = (n : ℝ) ^ (1 / 3 : ℝ) := by
          calc
            (n : ℝ) * b ^ 2 = (n : ℝ) ^ (1 : ℝ) *
                (n : ℝ) ^ (-(2 / 3 : ℝ)) := by rw [hb2, Real.rpow_one]
            _ = (n : ℝ) ^ ((1 : ℝ) + -(2 / 3 : ℝ)) :=
              (Real.rpow_add hnR _ _).symm
            _ = _ := by congr 1; norm_num
        rw [div_pow]
        nlinarith
      rw [hexp] at htailprob
      have hH : ∀ A, |g (X A) - X A| ≤
          Causalean.Experimentation.DesignBased.FiniteDesign.ind
            (fun A => b / 2 ≤ |X A - θ|) A := by
        intro A
        by_cases hfar : b / 2 ≤ |X A - θ|
        · simp [Causalean.Experimentation.DesignBased.FiniteDesign.ind, hfar]
          exact clippedScore_sub_abs_le hb0 (hX A) hb1
        · have hxlocal : |X A| ≤ b := by
            calc
              |X A| ≤ |X A - θ| + |θ| := by
                simpa only [sub_add_cancel] using (abs_add_le (X A - θ) θ)
              _ ≤ b := by linarith
          simp [Causalean.Experimentation.DesignBased.FiniteDesign.ind, hfar,
            g, clippedScore_eq_self hxlocal]
      have hcov := finiteDesign_cov_perturbation_lower D X
        (fun A => g (X A) - X A) θ (b / 2) hmean
        (fun A => by
          calc
            |X A - θ| ≤ |X A| + |θ| := abs_sub _ _
            _ ≤ 2 := by linarith [hX A, htheta]) hH
      have hcov : D.Var X - 2 * D.Pr (fun A => b / 2 ≤ |X A - θ|) ≤
          D.Cov X (fun A => g (X A)) := by
        convert hcov using 1
        congr 2
        funext A
        ring
      have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hcoef : 0 ≤ 1 - 2 * eps := by linarith
      have hApos : 0 < Real.sqrt (lambdaC c) / 2 - lambdaC c / 16 := by
        nlinarith [hsqrt_sq]
      have htailScaled :
          2 * Real.sqrt (lambdaC c) * b *
              Real.exp (-(n : ℝ) ^ (1 / 3 : ℝ) / 8) ≤
            (Real.sqrt (lambdaC c) / 2 - lambdaC c / 16) / 2 *
              (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
        rw [← hbdiv]
        have := mul_le_mul_of_nonneg_left htail
          (div_nonneg hb0 (by positivity : (0 : ℝ) ≤ 2 * n))
        field_simp [hnR.ne'] at this ⊢
        nlinarith
      have hAhalf : kappaC c ≤
          (Real.sqrt (lambdaC c) / 2 - lambdaC c / 16) / 2 := by
        dsimp [kappaC]
        exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      have hpows : (Real.sqrt (lambdaC c) / 4 * b) ^ 2 * b ^ 2 =
          lambdaC c / 16 * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
        calc
          (Real.sqrt (lambdaC c) / 4 * b) ^ 2 * b ^ 2 =
              Real.sqrt (lambdaC c) ^ 2 / 16 * b ^ 4 := by ring
          _ = _ := by rw [hsqrt_sq]; simpa [b] using
            (congrArg (fun x => lambdaC c / 16 * x) hb4)
      dsimp [eps] at hmse
      rw [hpows] at hmse
      have hcov' : (n : ℝ)⁻¹ - (n : ℝ)⁻¹ ^ 2 * Q -
          4 * Real.exp (-(n : ℝ) ^ (1 / 3 : ℝ) / 8) ≤
          D.Cov X (fun A => g (X A)) := by linarith
      have hbase :
          D.mse (fun A => X A - eps * g (X A)) θ ≤
            (n : ℝ)⁻¹ -
              (Real.sqrt (lambdaC c) / 2 - lambdaC c / 16) *
                (n : ℝ) ^ (-(4 / 3 : ℝ)) +
              2 * Real.sqrt (lambdaC c) * b *
                Real.exp (-(n : ℝ) ^ (1 / 3 : ℝ) / 8) := by
        have hcovmul :
            -2 * (Real.sqrt (lambdaC c) / 4 * b) * D.Cov X (fun A => g (X A)) ≤
              -2 * (Real.sqrt (lambdaC c) / 4 * b) *
                ((n : ℝ)⁻¹ - (n : ℝ)⁻¹ ^ 2 * Q -
                  4 * Real.exp (-(n : ℝ) ^ (1 / 3 : ℝ) / 8)) :=
          mul_le_mul_of_nonpos_left hcov'
            (by nlinarith [mul_nonneg hsqrt0 hb0])
        have hdrop : 0 ≤ (1 - 2 * (Real.sqrt (lambdaC c) / 4 * b)) *
            ((n : ℝ)⁻¹ ^ 2 * Q) := by
          apply mul_nonneg
          · simpa [eps] using hcoef
          · positivity
        have hstep :
            D.mse (fun A => X A - eps * g (X A)) θ ≤
              (n : ℝ)⁻¹ - Real.sqrt (lambdaC c) / 2 * (b / n) +
                2 * Real.sqrt (lambdaC c) * b *
                  Real.exp (-(n : ℝ) ^ (1 / 3 : ℝ) / 8) +
                lambdaC c / 16 * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
          dsimp [eps] at hcovmul hdrop hmse ⊢
          calc
            _ ≤ (n : ℝ)⁻¹ - (n : ℝ)⁻¹ ^ 2 * Q -
                2 * (Real.sqrt (lambdaC c) / 4 * b) *
                  D.Cov X (fun A => g (X A)) +
                lambdaC c / 16 * (n : ℝ) ^ (-(4 / 3 : ℝ)) := hmse
            _ ≤ _ := by
              ring_nf at hcovmul hdrop ⊢
              linarith
        rw [hbdiv] at hstep
        convert hstep using 1 <;> ring
      calc
        _ ≤ _ := hbase
        _ ≤ (n : ℝ)⁻¹ - kappaC c * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
          have hrpow0 : 0 ≤ (n : ℝ) ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hnR.le _
          nlinarith [mul_le_mul_of_nonneg_right hAhalf hrpow0]
    · have hthetaLarge : b / 2 < |θ| := lt_of_not_ge hlocal
      have hQscaled : lambdaC c / 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) ≤
          (n : ℝ)⁻¹ ^ 2 * Q := by
        rw [← hbdiv]
        have h := mul_le_mul_of_nonneg_left hthetaLarge.le
          (mul_nonneg hlambda.le hnR.le)
        have hraw : lambdaC c * (n : ℝ) * b / 2 ≤ Q := by
          nlinarith [hQ]
        calc
          lambdaC c / 2 * (b / (n : ℝ)) =
              (lambdaC c * (n : ℝ) * b / 2) / (n : ℝ) ^ 2 := by
            field_simp [hnR.ne']
          _ ≤ Q / (n : ℝ) ^ 2 := by
            gcongr
          _ = (n : ℝ)⁻¹ ^ 2 * Q := by
            field_simp [hnR.ne']
      have hB : kappaC c ≤ 7 * lambdaC c / 16 := by
        dsimp [kappaC]
        calc min _ _ / 2 ≤ (7 * lambdaC c / 16) / 2 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        _ ≤ 7 * lambdaC c / 16 := by nlinarith [hlambda]
      have hpows : (Real.sqrt (lambdaC c) / 4 * b) ^ 2 * b ^ 2 =
          lambdaC c / 16 * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
        calc
          (Real.sqrt (lambdaC c) / 4 * b) ^ 2 * b ^ 2 =
              Real.sqrt (lambdaC c) ^ 2 / 16 * b ^ 4 := by ring
          _ = _ := by rw [hsqrt_sq]; simpa [b] using
            (congrArg (fun x => lambdaC c / 16 * x) hb4)
      dsimp [eps] at hmse
      rw [hpows] at hmse
      have hrpow0 : 0 ≤ (n : ℝ) ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hnR.le _
      have hBk := mul_le_mul_of_nonneg_right hB hrpow0
      have hec := mul_nonneg heps0 hcov0
      have hec' : 0 ≤ (Real.sqrt (lambdaC c) / 4 * b) *
          D.Cov X (fun A => g (X A)) := by simpa [eps] using hec
      change D.mse (fun A => X A - (Real.sqrt (lambdaC c) / 4 * b) * g (X A)) θ ≤ _
      calc
        _ ≤ (n : ℝ)⁻¹ - (n : ℝ)⁻¹ ^ 2 * Q -
            2 * (Real.sqrt (lambdaC c) / 4 * b) * D.Cov X (fun A => g (X A)) +
            lambdaC c / 16 * (n : ℝ) ^ (-(4 / 3 : ℝ)) := hmse
        _ ≤ (n : ℝ)⁻¹ - 7 * lambdaC c / 16 *
            (n : ℝ) ^ (-(4 / 3 : ℝ)) := by nlinarith
        _ ≤ _ := by nlinarith
  have hunclipped (A : Assign K n) :
      (Lc c / 2) * (X A - eps * g (X A)) ∈
        Set.Icc (-Lc c / 2) (Lc c / 2) := by
    have hh : 0 ≤ Lc c / 2 := by positivity [Lc_pos c]
    have hnorm := shrunkenClippedScore_abs_le_one hb0 hb1 heps0
      (by linarith : eps ≤ 1) (hX A)
    rw [abs_le] at hnorm
    constructor <;> nlinarith
  have hnormalized (A : Assign K n) :
      centeredContrastScore c A (obsOutcome z A) / (Lc c / 2) = X A := by
    have hh : Lc c / 2 ≠ 0 := by positivity [Lc_pos c]
    change ((n : ℝ)⁻¹ * ∑ i, upperUnitScore c (z i) (A i)) / (Lc c / 2) =
      (n : ℝ)⁻¹ * ∑ i, upperUnitScore c (z i) (A i) / (Lc c / 2)
    rw [← Finset.sum_div]
    ring
  unfold labeledRisk
  simp only [shrinkageProcedure, contrastWeightedProcedure]
  change D.mse (fun A => clip c ((Lc c / 2) *
    (centeredContrastScore c A (obsOutcome z A) / (Lc c / 2) - eps *
      max (-b) (min (centeredContrastScore c A (obsOutcome z A) / (Lc c / 2)) b))))
      (tauC c z) ≤ _
  simp_rw [hnormalized]
  change D.mse (fun A => clip c ((Lc c / 2) * (X A - eps * g (X A)))) (tauC c z) ≤ _
  have htau : tauC c z = (Lc c / 2) * θ := by
    have hh : Lc c / 2 ≠ 0 := by positivity [Lc_pos c]
    change (n : ℝ)⁻¹ * ∑ i, ∑ a, c a * (if z i a then (1 : ℝ) else 0) =
      (Lc c / 2) * ((n : ℝ)⁻¹ *
        ∑ i, (∑ a, c a * (if z i a then (1 : ℝ) else 0)) / (Lc c / 2))
    rw [← Finset.sum_div]
    field_simp [hh]
    field_simp [ne_of_gt (Lc_pos c)]
  rw [htau]
  have hclip : ∀ A, clip c ((Lc c / 2) * (X A - eps * g (X A))) =
      (Lc c / 2) * (X A - eps * g (X A)) := by
    intro A
    rcases hunclipped A with ⟨hl, hr⟩
    unfold clip
    rw [min_eq_right hr, max_eq_right hl]
  simp_rw [hclip]
  calc
    D.mse (fun A => (Lc c / 2) * (X A - eps * g (X A))) ((Lc c / 2) * θ) =
        (Lc c / 2) ^ 2 * D.mse (fun A => X A - eps * g (X A)) θ := by
      unfold Causalean.Experimentation.DesignBased.FiniteDesign.mse
        Causalean.Experimentation.DesignBased.FiniteDesign.E
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      ring
    _ ≤ (Lc c / 2) ^ 2 * ((n : ℝ)⁻¹ - kappaC c *
        (n : ℝ) ^ (-(4 / 3 : ℝ))) := by
      gcongr
    _ = C0 c * ((n : ℝ)⁻¹ - kappaC c *
        (n : ℝ) ^ (-(4 / 3 : ℝ))) := by
      unfold C0
      ring

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

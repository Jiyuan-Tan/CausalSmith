module
public import Causalean.Stat.UStatistic.LocalizedVariance.Coordinates

/-!
# Localized covariance bounds

This module bounds the mean, pair variance, and overlapping pair covariance using the
two distinct localization scales. Symmetry handles every orientation of a shared index.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.UStatistic.LocalizedVariance

variable {X : Type*} [MeasurableSpace X]
  (P : Measure X) [IsProbabilityMeasure P]
  {H W : X → X → ℝ} {M : ℝ} (h : LocalizedKernel H W M)

-- Keep the localization hypotheses in every theorem's public signature, including
-- the declarations whose scaffold bodies do not yet refer to `h`.
include h

/-- A [probability law and localization certificate](hyp:P,h) and [sample pair](hyp:p) give
[a pair kernel value with finite second moment](goal) under the independent product law. -/
theorem pairValue_memLp_two {n : ℕ} (p : Fin n × Fin n) :
    MemLp (pairValue H p) 2 (iidLaw P n) := by
  have : IsProbabilityMeasure (iidLaw P n) := by unfold iidLaw; infer_instance
  have hm : Measurable (pairValue H p) := by
    change Measurable (fun ω : Fin n → X => H (ω p.1) (ω p.2))
    have hpair : Measurable (fun ω : Fin n → X => (ω p.1, ω p.2)) := by fun_prop
    exact h.measurable_kernel.comp hpair
  apply MemLp.of_bound hm.aestronglyMeasurable M
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  exact (h.envelope (ω p.1) (ω p.2)).trans
    (mul_le_of_le_one_right h.envelope_nonneg (h.weight_le_one _ _))

/-- A [probability law and localized-kernel certificate](hyp:P,h) give [a population kernel
mean whose square is controlled by the squared row mass](goal). -/
theorem kernel_mean_sq_le_rowMassSq :
    (∫ x, ∫ y, H x y ∂P ∂P) ^ 2 ≤ M ^ 2 * rowMassSq P W := by
  have hH (x : X) : Integrable (H x) P :=
    Integrable.of_bound
      (h.measurable_kernel.comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs]
        exact (h.envelope x y).trans
          (mul_le_of_le_one_right h.envelope_nonneg (h.weight_le_one x y))))
  have hW (x : X) : Integrable (W x) P :=
    Integrable.of_bound
      (h.measurable_weight.comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h.weight_nonneg x y)]
        exact h.weight_le_one x y))
  have hrow (x : X) : |∫ y, H x y ∂P| ≤ M * ∫ y, W x y ∂P := by
    calc
      _ ≤ ∫ y, |H x y| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ y, M * W x y ∂P :=
        integral_mono (hH x).abs ((hW x).const_mul M) (h.envelope x)
      _ = _ := by rw [integral_const_mul]
  have hHprod : Integrable (fun z : X × X => H z.1 z.2) (P.prod P) :=
    Integrable.of_bound h.measurable_kernel.aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]
        exact (h.envelope z.1 z.2).trans
          (mul_le_of_le_one_right h.envelope_nonneg (h.weight_le_one _ _))))
  have hWprod : Integrable (fun z : X × X => W z.1 z.2) (P.prod P) :=
    Integrable.of_bound h.measurable_weight.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h.weight_nonneg _ _)]
        exact h.weight_le_one _ _))
  have hHout : Integrable (fun x => ∫ y, H x y ∂P) P := hHprod.integral_prod_left
  have hWout : Integrable (fun x => ∫ y, W x y ∂P) P := hWprod.integral_prod_left
  have hWmeas : Measurable (fun x => ∫ y, W x y ∂P) :=
    (h.measurable_weight.stronglyMeasurable.integral_prod_right'
      (ν := P)).measurable
  have hWbound (x : X) : |∫ y, W x y ∂P| ≤ 1 := by
    calc
      _ ≤ ∫ y, |W x y| ∂P := abs_integral_le_integral_abs
      _ = ∫ y, W x y ∂P := by congr 1; funext y; rw [abs_of_nonneg (h.weight_nonneg x y)]
      _ ≤ 1 := by
        simpa using integral_mono (hW x) (integrable_const (1 : ℝ)) (h.weight_le_one x)
  have hWsq : Integrable (fun x => (∫ y, W x y ∂P) ^ 2) P :=
    Integrable.of_bound (hWmeas.pow_const 2).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [mul_nonneg (sub_nonneg.mpr (hWbound x))
          (add_nonneg (abs_nonneg (∫ y, W x y ∂P)) (by norm_num : (0 : ℝ) ≤ 1)),
          sq_abs (∫ y, W x y ∂P)]))
  have hglobal : |∫ x, ∫ y, H x y ∂P ∂P| ≤ M * ∫ x, ∫ y, W x y ∂P ∂P := by
    calc
      _ ≤ ∫ x, |∫ y, H x y ∂P| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ x, M * ∫ y, W x y ∂P ∂P :=
        integral_mono hHout.abs (hWout.const_mul M) hrow
      _ = _ := by rw [integral_const_mul]
  have hjs : (∫ x, ∫ y, W x y ∂P ∂P) ^ 2 ≤ rowMassSq P W := by
    have hvar := variance_nonneg (fun x => ∫ y, W x y ∂P) P
    rw [variance_eq_sub ((memLp_two_iff_integrable_sq hWmeas.aestronglyMeasurable).2 hWsq)] at hvar
    simp only [Pi.pow_apply] at hvar
    unfold rowMassSq
    linarith
  have hsq : (∫ x, ∫ y, H x y ∂P ∂P) ^ 2 ≤
      M ^ 2 * (∫ x, ∫ y, W x y ∂P ∂P) ^ 2 := by
    have hw : 0 ≤ ∫ x, ∫ y, W x y ∂P ∂P :=
      integral_nonneg (fun x => integral_nonneg (h.weight_nonneg x))
    have ha := (sq_le_sq₀ (abs_nonneg (∫ x, ∫ y, H x y ∂P ∂P))
      (mul_nonneg h.envelope_nonneg hw)).2 hglobal
    nlinarith [ha, sq_abs (∫ x, ∫ y, H x y ∂P ∂P)]
  nlinarith [mul_le_mul_of_nonneg_left hjs (sq_nonneg M)]

/-- A [probability law and localized-kernel certificate](hyp:P,h) and [unordered sample
pair](hyp:hp) give [a pair-value second moment bounded by the pair mass](goal). -/
theorem pairValue_second_moment_le_pairMass {n : ℕ}
    {p : Fin n × Fin n} (hp : p ∈ pairIndices n) :
    (∫ ω, (pairValue H p ω) ^ 2 ∂iidLaw P n) ≤ M ^ 2 * pairMass P W := by
  have hij : p.1 ≠ p.2 := ne_of_lt (Finset.mem_filter.mp hp).2
  have hsq (x y : X) : H x y ^ 2 ≤ M ^ 2 * W x y := by
    have hw0 := h.weight_nonneg x y
    have hw1 := h.weight_le_one x y
    have he := h.envelope x y
    have hm := h.envelope_nonneg
    have ha : H x y ^ 2 ≤ (M * W x y) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr he)
        (add_nonneg (abs_nonneg (H x y)) (mul_nonneg hm hw0)), sq_abs (H x y)]
    have hb : (W x y) ^ 2 ≤ W x y := by
      nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hw1)]
    nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg M)]
  have hmeas : Measurable (fun z : X × X => H z.1 z.2 ^ 2) :=
    h.measurable_kernel.pow_const 2
  have hbound (x y : X) : |H x y ^ 2| ≤ M ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have := hsq x y
    exact this.trans (mul_le_of_le_one_right (sq_nonneg M) (h.weight_le_one x y))
  have hH (x : X) : Integrable (fun y => H x y ^ 2) P :=
    Integrable.of_bound
      (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (M ^ 2) (Filter.Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs] using hbound x y))
  have hW (x : X) : Integrable (fun y => M ^ 2 * W x y) P := by
    have hwm : Measurable (fun y => M ^ 2 * W x y) :=
      (h.measurable_weight.comp
        (measurable_const.prodMk measurable_id)).const_mul _
    exact Integrable.of_bound hwm.aestronglyMeasurable
      (M ^ 2) (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (h.weight_nonneg _ _))]
        exact mul_le_of_le_one_right (sq_nonneg _) (h.weight_le_one _ _)))
  have hinner (x : X) : (∫ y, H x y ^ 2 ∂P) ≤ M ^ 2 * ∫ y, W x y ∂P := by
    calc
      _ ≤ ∫ y, M ^ 2 * W x y ∂P := integral_mono (hH x) (hW x) (hsq x)
      _ = _ := by rw [integral_const_mul]
  have houtH : Integrable (fun x => ∫ y, H x y ^ 2 ∂P) P := by
    have hp : Integrable (fun z : X × X => H z.1 z.2 ^ 2) (P.prod P) :=
      Integrable.of_bound hmeas.aestronglyMeasurable (M ^ 2)
        (Filter.Eventually.of_forall (fun z => by
          simpa only [Real.norm_eq_abs] using hbound z.1 z.2))
    exact hp.integral_prod_left
  have houtW : Integrable (fun x => M ^ 2 * ∫ y, W x y ∂P) P := by
    have hw : Integrable (fun z : X × X => W z.1 z.2) (P.prod P) :=
      Integrable.of_bound h.measurable_weight.aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (h.weight_nonneg _ _)]
          exact h.weight_le_one _ _))
    exact hw.integral_prod_left.const_mul _
  calc
    _ = ∫ x, ∫ y, H x y ^ 2 ∂P ∂P := by
      change (∫ ω, H (ω p.1) (ω p.2) ^ 2 ∂iidLaw P n) = _
      exact integral_two_coordinates P hij (fun x y => H x y ^ 2) hmeas
        (M ^ 2) hbound
    _ ≤ ∫ x, M ^ 2 * ∫ y, W x y ∂P ∂P :=
      integral_mono houtH houtW hinner
    _ = M ^ 2 * pairMass P W := by rw [integral_const_mul]; rfl

/-- A [probability law and localized-kernel certificate](hyp:P,h) and [unordered sample
pair](hyp:hp) give [the independent-pair population mean](goal). -/
theorem pairValue_integral_eq_kernel_mean {n : ℕ}
    {p : Fin n × Fin n} (hp : p ∈ pairIndices n) :
    (∫ ω, pairValue H p ω ∂iidLaw P n) = ∫ x, ∫ y, H x y ∂P ∂P := by
  have hij : p.1 ≠ p.2 := ne_of_lt (Finset.mem_filter.mp hp).2
  have hbound (x y : X) : |H x y| ≤ M :=
    (h.envelope x y).trans
      (mul_le_of_le_one_right h.envelope_nonneg (h.weight_le_one x y))
  change (∫ ω, H (ω p.1) (ω p.2) ∂iidLaw P n) = _
  exact integral_two_coordinates P hij H h.measurable_kernel M hbound

/-- A [probability law and localized-kernel certificate](hyp:P,h), [two unordered sample
pairs](hyp:hp,hq), and [their disjointness](hyp:hpq) give [zero covariance](goal) under the
finite independent product law. -/
theorem covariance_disjoint_pairs_eq_zero {n : ℕ}
    {p q : Fin n × Fin n} (hp : p ∈ pairIndices n) (hq : q ∈ pairIndices n)
    (hpq : ¬ SharesIndex p q) :
    covariance (pairValue H p) (pairValue H q) (iidLaw P n) = 0 := by
  -- The two coordinate pairs are independent by `iIndepFun_pi` and the four
  -- cross-inequalities from `¬ SharesIndex`; apply `IndepFun.covariance_eq_zero`.
  haveI : IsProbabilityMeasure (iidLaw P n) := by unfold iidLaw; infer_instance
  have hcross : p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 := by
    simp only [SharesIndex, not_or] at hpq
    exact hpq
  have hcoord : iIndepFun (fun i : Fin n => fun ω : Fin n → X => ω i) (iidLaw P n) := by
    unfold iidLaw
    simpa using (iIndepFun_pi (μ := fun _ : Fin n => P)
      (X := fun _ : Fin n => id) (fun _ => aemeasurable_id))
  have hind : pairValue H p ⟂ᵢ[iidLaw P n] pairValue H q := by
    have hpairs := hcoord.indepFun_prodMk_prodMk
      (fun i => measurable_pi_apply i) p.1 p.2 q.1 q.2
      hcross.1 hcross.2.1 hcross.2.2.1 hcross.2.2.2
    have hc := hpairs.comp h.measurable_kernel h.measurable_kernel
    change (fun ω => H (ω p.1) (ω p.2)) ⟂ᵢ[iidLaw P n]
      (fun ω => H (ω q.1) (ω q.2))
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using hc
  exact hind.covariance_eq_zero (pairValue_memLp_two P h p) (pairValue_memLp_two P h q)

/-- A [probability law and localized-kernel certificate](hyp:P,h) give [a shared-first-draw
product moment bounded by the squared row mass](goal). -/
theorem shared_triple_integral_abs_le_rowMassSq :
    |∫ x, ∫ y, ∫ z, H x y * H x z ∂P ∂P ∂P| ≤
      M ^ 2 * rowMassSq P W := by
  have hH (x : X) : Integrable (H x) P :=
    Integrable.of_bound
      (h.measurable_kernel.comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs]
        exact (h.envelope x y).trans
          (mul_le_of_le_one_right h.envelope_nonneg (h.weight_le_one x y))))
  have hW (x : X) : Integrable (W x) P :=
    Integrable.of_bound
      (h.measurable_weight.comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h.weight_nonneg x y)]
        exact h.weight_le_one x y))
  have hrow (x : X) : |∫ y, H x y ∂P| ≤ M * ∫ y, W x y ∂P := by
    calc
      _ ≤ ∫ y, |H x y| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ y, M * W x y ∂P :=
        integral_mono (hH x).abs ((hW x).const_mul M) (h.envelope x)
      _ = _ := by rw [integral_const_mul]
  have hWrow_nonneg (x : X) : 0 ≤ ∫ y, W x y ∂P :=
    integral_nonneg (h.weight_nonneg x)
  have hWrow_le_one (x : X) : ∫ y, W x y ∂P ≤ 1 := by
    simpa using integral_mono (hW x) (integrable_const (1 : ℝ)) (h.weight_le_one x)
  have hWmeas : Measurable (fun x => ∫ y, W x y ∂P) :=
    (h.measurable_weight.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have hHmeas : Measurable (fun x => ∫ y, H x y ∂P) :=
    (h.measurable_kernel.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have hWsq : Integrable (fun x => (∫ y, W x y ∂P) ^ 2) P :=
    Integrable.of_bound (hWmeas.pow_const 2).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [hWrow_nonneg x, hWrow_le_one x]))
  have hHsq : Integrable (fun x => (∫ y, H x y ∂P) ^ 2) P :=
    Integrable.of_bound (hHmeas.pow_const 2).aestronglyMeasurable (M ^ 2)
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hx : |∫ y, H x y ∂P| ≤ M :=
          (hrow x).trans (mul_le_of_le_one_right h.envelope_nonneg (hWrow_le_one x))
        nlinarith [(sq_le_sq₀ (abs_nonneg (∫ y, H x y ∂P))
          h.envelope_nonneg).2 hx, sq_abs (∫ y, H x y ∂P)]))
  have hsq (x : X) : (∫ y, H x y ∂P) ^ 2 ≤
      M ^ 2 * (∫ y, W x y ∂P) ^ 2 := by
    have hx := hrow x
    have hy := hWrow_nonneg x
    nlinarith [(sq_le_sq₀ (abs_nonneg (∫ y, H x y ∂P))
      (mul_nonneg h.envelope_nonneg hy)).2 hx,
      sq_abs (∫ y, H x y ∂P)]
  have hid (x : X) : (∫ y, ∫ z, H x y * H x z ∂P ∂P) =
      (∫ y, H x y ∂P) ^ 2 := by
    simp_rw [integral_const_mul, integral_mul_const]
    ring
  calc
    _ = |∫ x, (∫ y, H x y ∂P) ^ 2 ∂P| := by simp_rw [hid]
    _ = ∫ x, (∫ y, H x y ∂P) ^ 2 ∂P := by
      rw [abs_of_nonneg (integral_nonneg (fun x => sq_nonneg _))]
    _ ≤ ∫ x, M ^ 2 * (∫ y, W x y ∂P) ^ 2 ∂P :=
      integral_mono hHsq (hWsq.const_mul _) hsq
    _ = M ^ 2 * rowMassSq P W := by rw [integral_const_mul]; rfl

/-- A [probability law and localized-kernel certificate](hyp:P,h) and [three pairwise
distinct sample coordinates](hyp:hij,hik,hjk) give [a shared-coordinate product moment
bounded by the squared row mass](goal). -/
theorem shared_first_coordinate_product_integral_abs_le_rowMassSq {n : ℕ}
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    |∫ ω, H (ω i) (ω j) * H (ω i) (ω k) ∂iidLaw P n| ≤
      M ^ 2 * rowMassSq P W := by
  have hmeas : Measurable (fun t : (X × X) × X =>
      H t.1.1 t.1.2 * H t.1.1 t.2) := by
    have hleft : Measurable (fun t : (X × X) × X => (t.1.1, t.1.2)) := by fun_prop
    have hright : Measurable (fun t : (X × X) × X => (t.1.1, t.2)) := by fun_prop
    exact (h.measurable_kernel.comp hleft).mul (h.measurable_kernel.comp hright)
  have hbound (x y z : X) : |H x y * H x z| ≤ M ^ 2 := by
    have hxy : |H x y| ≤ M :=
      (h.envelope x y).trans
        (mul_le_of_le_one_right h.envelope_nonneg (h.weight_le_one x y))
    have hxz : |H x z| ≤ M :=
      (h.envelope x z).trans
        (mul_le_of_le_one_right h.envelope_nonneg (h.weight_le_one x z))
    calc
      |H x y * H x z| = |H x y| * |H x z| := abs_mul _ _
      _ ≤ M * M := mul_le_mul hxy hxz (abs_nonneg _) h.envelope_nonneg
      _ = M ^ 2 := by ring
  rw [integral_three_coordinates P hij hik hjk
    (fun x y z => H x y * H x z) hmeas (M ^ 2) hbound]
  exact shared_triple_integral_abs_le_rowMassSq P h

/-- A [probability law and localized-kernel certificate](hyp:P,h), [two unordered sample
pairs](hyp:hp,hq), [their inequality](hyp:hne), and [their shared index](hyp:hpq) give [an
absolute product expectation bounded by the squared row mass](goal). -/
theorem shared_pairs_product_integral_abs_le_rowMassSq {n : ℕ}
    {p q : Fin n × Fin n} (hp : p ∈ pairIndices n) (hq : q ∈ pairIndices n)
    (hne : p ≠ q) (hpq : SharesIndex p q) :
    |∫ ω, pairValue H p ω * pairValue H q ω ∂iidLaw P n| ≤
      M ^ 2 * rowMassSq P W := by
  have hpord : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  have hqord : q.1 < q.2 := (Finset.mem_filter.mp hq).2
  rcases hpq with h11 | h12 | h21 | h22
  · have hjk : p.2 ≠ q.2 := by
      intro e
      exact hne (Prod.ext h11 e)
    have hb := shared_first_coordinate_product_integral_abs_le_rowMassSq P h
      (ne_of_lt hpord) (by omega : p.1 ≠ q.2) hjk
    convert hb using 1
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ω
    simp only [pairValue, h11]
  · have hjk : p.2 ≠ q.1 := by omega
    have hb := shared_first_coordinate_product_integral_abs_le_rowMassSq P h
      (ne_of_lt hpord) (by omega : p.1 ≠ q.1) hjk
    convert hb using 1
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ω
    simp only [pairValue]
    rw [h.symmetric_kernel (ω q.1) (ω q.2), ← h12]
  · have hjk : p.1 ≠ q.2 := by omega
    have hb := shared_first_coordinate_product_integral_abs_le_rowMassSq P h
      (by omega : p.2 ≠ p.1) (by omega : p.2 ≠ q.2) hjk
    convert hb using 1
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ω
    simp only [pairValue]
    rw [h.symmetric_kernel (ω p.1) (ω p.2), h21]
  · have hjk : p.1 ≠ q.1 := by
      intro e
      exact hne (Prod.ext e h22)
    have hb := shared_first_coordinate_product_integral_abs_le_rowMassSq P h
      (by omega : p.2 ≠ p.1) (by omega : p.2 ≠ q.1) hjk
    convert hb using 1
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ω
    simp only [pairValue]
    rw [h.symmetric_kernel (ω p.1) (ω p.2),
      h.symmetric_kernel (ω q.1) (ω q.2), h22]

/-- A [probability law and localized-kernel certificate](hyp:P,h), [two unordered sample
pairs](hyp:hp,hq), [their inequality](hyp:hne), and [their shared index](hyp:hpq) give [a
covariance bounded by twice the scaled squared row mass](goal). -/
theorem covariance_shared_pairs_le_rowMassSq {n : ℕ}
    {p q : Fin n × Fin n} (hp : p ∈ pairIndices n) (hq : q ∈ pairIndices n)
    (hne : p ≠ q) (hpq : SharesIndex p q) :
    covariance (pairValue H p) (pairValue H q) (iidLaw P n) ≤
      2 * M ^ 2 * rowMassSq P W := by
  haveI : IsProbabilityMeasure (iidLaw P n) := by unfold iidLaw; infer_instance
  rw [covariance_eq_sub (pairValue_memLp_two P h p) (pairValue_memLp_two P h q),
    pairValue_integral_eq_kernel_mean P h hp,
    pairValue_integral_eq_kernel_mean P h hq]
  have hb := shared_pairs_product_integral_abs_le_rowMassSq P h hp hq hne hpq
  have hs : 0 ≤ M ^ 2 * rowMassSq P W := by
    apply mul_nonneg (sq_nonneg M)
    unfold rowMassSq
    exact integral_nonneg (fun x => sq_nonneg _)
  have hm : 0 ≤ (∫ x, ∫ y, H x y ∂P ∂P) *
      (∫ x, ∫ y, H x y ∂P ∂P) := mul_self_nonneg _
  have hi : (∫ ω, pairValue H p ω * pairValue H q ω ∂iidLaw P n) ≤
      M ^ 2 * rowMassSq P W := le_trans (le_abs_self _) hb
  simp only [Pi.mul_apply]
  linarith

/-- A [probability law and localized-kernel certificate](hyp:P,h) and [unordered sample
pair](hyp:hp) give [a self-covariance bounded by the scaled pair mass](goal). -/
theorem covariance_identical_pair_le_pairMass {n : ℕ}
    {p : Fin n × Fin n} (hp : p ∈ pairIndices n) :
    covariance (pairValue H p) (pairValue H p) (iidLaw P n) ≤
      M ^ 2 * pairMass P W := by
  -- Use `variance_le_expectation_sq` or `covariance_self`, then the localized
  -- second-moment estimate above.
  haveI : IsProbabilityMeasure (iidLaw P n) := by unfold iidLaw; infer_instance
  have hm := pairValue_memLp_two P h p
  calc
    covariance (pairValue H p) (pairValue H p) (iidLaw P n)
        = variance (pairValue H p) (iidLaw P n) := covariance_self hm.aemeasurable
    _ ≤ ∫ ω, (pairValue H p ω) ^ 2 ∂iidLaw P n :=
      variance_le_expectation_sq hm.aestronglyMeasurable
    _ ≤ M ^ 2 * pairMass P W := pairValue_second_moment_le_pairMass P h hp

end Causalean.Stat.UStatistic.LocalizedVariance

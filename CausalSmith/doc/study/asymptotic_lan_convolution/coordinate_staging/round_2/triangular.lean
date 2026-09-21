/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Estimation.Efficiency.AsymptoticLanConvolution.Basic
import Causalean.Stat.Concentration.Matrix.IidSums
import Mathlib.Probability.Independence.InfinitePi

/-!
# Triangular-array estimates for i.i.d. LAN expansions

This module isolates the generic probability estimates behind the quadratic log-likelihood
Taylor expansion.  The rows may change with `n`, but the coordinates within each row have one
common law.  These results contain no statistical-model or density-specific definitions.
-/

namespace Causalean.Estimation.Efficiency.AsymptoticLanConvolution

open Filter MeasureTheory ProbabilityTheory Topology

variable {X : Type*} [MeasurableSpace X]

/-- An `L²` approximation of a triangular row by `S / sqrt n` transfers the fixed `L²` tail
condition of `S` to the Lindeberg tail condition for the row. -/
theorem scaledL2Approx_lindeberg
    (P : Measure X) [IsProbabilityMeasure P]
    (W : ℕ → X → ℝ) (S : X → ℝ)
    (hW : ∀ n, Measurable (W n)) (hW2 : ∀ n, MemLp (W n) 2 P)
    (hS : MemLp S 2 P)
    (happrox : Tendsto (fun n : ℕ => (n : ℝ) * ∫ x,
      (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 ∂P) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (n : ℝ) *
      ∫ x in {x | ε ≤ |W n x|}, W n x ^ 2 ∂P) atTop (𝓝 0) := by
  intro ε hε
  classical
  let A : ℕ → Set X := fun n => {x | ε ≤ |W n x|}
  let good : ℕ → Prop := fun n => Integrable (fun x => W n x ^ 2) P
  let B : ℕ → Set X := fun n => if good n then A n else ∅
  have hS2 : Integrable (fun x => S x ^ 2) P := hS.integrable_sq
  have hBmeas : ∀ n, MeasurableSet (B n) := by
    intro n
    simp only [B]
    split_ifs
    · exact measurableSet_Ici.preimage (hW n).abs
    · exact MeasurableSet.empty
  have hBmeasure_real : Tendsto (fun n => P.real (B n)) atTop (𝓝 0) := by
    apply squeeze_zero (g := fun (n : ℕ) => (ε ^ 2)⁻¹ *
      (2 * ∫ x, (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 ∂P +
        2 * ((Real.sqrt (n : ℝ))⁻¹) ^ 2 * ∫ x, S x ^ 2 ∂P))
    · intro n; positivity
    · intro n
      by_cases hn : good n
      · have hW2n : Integrable (fun x => W n x ^ 2) P := hn
        have hmarkov := mul_meas_ge_le_integral_of_nonneg
          (μ := P) (f := fun x => W n x ^ 2) (ae_of_all P fun x => sq_nonneg (W n x)) hW2n
          (ε ^ 2)
        have hset : {x | ε ^ 2 ≤ W n x ^ 2} = A n := by
          ext x
          simp only [A, Set.mem_ofPred_eq]
          rw [← sq_abs (W n x), sq_le_sq₀ hε.le (abs_nonneg _)]
        rw [hset] at hmarkov
        simp only [B, if_pos hn]
        calc
          P.real (A n) ≤ (ε ^ 2)⁻¹ * ∫ x, W n x ^ 2 ∂P := by
            calc
              P.real (A n) = (ε ^ 2)⁻¹ * ((ε ^ 2) * P.real (A n)) := by
                field_simp
              _ ≤ _ := mul_le_mul_of_nonneg_left hmarkov (inv_nonneg.2 (sq_nonneg ε))
          _ ≤ (ε ^ 2)⁻¹ * (2 * ∫ x,
                (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 ∂P +
              2 * ((Real.sqrt (n : ℝ))⁻¹) ^ 2 * ∫ x, S x ^ 2 ∂P) := by
            have hWmem : MemLp (W n) 2 P :=
              (memLp_two_iff_integrable_sq (hW n).aestronglyMeasurable).2 hW2n
            have hSmem : MemLp (fun x => (Real.sqrt (n : ℝ))⁻¹ * S x) 2 P :=
              hS.const_mul _
            have herrn : Integrable (fun x =>
                (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2) P :=
              (hWmem.sub hSmem).integrable_sq
            have hIntBound : ∫ x, W n x ^ 2 ∂P ≤
                2 * ∫ x, (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 ∂P +
                  2 * ((Real.sqrt (n : ℝ))⁻¹) ^ 2 * ∫ x, S x ^ 2 ∂P := by
              calc
                ∫ x, W n x ^ 2 ∂P ≤ ∫ x,
                    2 * (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 +
                      (2 * ((Real.sqrt (n : ℝ))⁻¹) ^ 2) * S x ^ 2 ∂P := by
                  apply integral_mono hW2n
                    ((herrn.const_mul 2).add (hS2.const_mul _))
                  intro x
                  dsimp only [Pi.add_apply]
                  nlinarith [sq_nonneg (W n x - 2 * (Real.sqrt (n : ℝ))⁻¹ * S x)]
                _ = _ := by
                  rw [integral_add (herrn.const_mul 2) (hS2.const_mul _),
                    integral_const_mul, integral_const_mul]
            exact mul_le_mul_of_nonneg_left hIntBound (inv_nonneg.2 (sq_nonneg ε))
      · simp only [B, if_neg hn, measureReal_empty]
        positivity
    · have herr : Tendsto (fun n : ℕ => ∫ x,
          (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 ∂P) atTop (𝓝 0) := by
        apply squeeze_zero' (g := fun (n : ℕ) => (n : ℝ) * ∫ x,
          (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 ∂P)
        · exact Eventually.of_forall fun n =>
            integral_nonneg (μ := P) (fun x => sq_nonneg _)
        · filter_upwards [eventually_ge_atTop 1] with n hn
          have hi : 0 ≤ ∫ x, (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 ∂P :=
            integral_nonneg (μ := P) (fun x => sq_nonneg _)
          have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          nlinarith
        · exact happrox
      have hsqrt : Tendsto (fun n : ℕ => ((Real.sqrt (n : ℝ))⁻¹) ^ 2) atTop (𝓝 0) := by
        have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
          tendsto_natCast_atTop_atTop.inv_tendsto_atTop
        apply hinv.congr'
        exact Eventually.of_forall fun n => by
          change ((n : ℝ))⁻¹ = ((Real.sqrt (n : ℝ))⁻¹) ^ 2
          rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      have ht := ((herr.const_mul 2).add
        (hsqrt.const_mul (2 * ∫ x, S x ^ 2 ∂P))).const_mul ((ε ^ 2)⁻¹)
      convert ht using 1
      · funext n
        ring
      · norm_num
  have hBmeasure : Tendsto (fun n => P (B n)) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top P (B n))).1 hBmeasure_real
  have hsmall : Tendsto (fun n => ∫ x in B n, S x ^ 2 ∂P) atTop (𝓝 0) :=
    hS2.tendsto_setIntegral_nhds_zero hBmeasure
  apply squeeze_zero (g := fun (n : ℕ) => 2 * ((n : ℝ) * ∫ x,
      (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 ∂P) +
    2 * ∫ x in B n, S x ^ 2 ∂P)
  · intro n
    exact mul_nonneg (Nat.cast_nonneg n) (integral_nonneg fun x => sq_nonneg _)
  · intro n
    by_cases hn : good n
    · have hW2n : Integrable (fun x => W n x ^ 2) P := hn
      have herrn : Integrable (fun x =>
          (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2) P := by
        have hWmem : MemLp (W n) 2 P :=
          (memLp_two_iff_integrable_sq (hW n).aestronglyMeasurable).2 hW2n
        exact (hWmem.sub (hS.const_mul _)).integrable_sq
      have hpoint : ∀ x, W n x ^ 2 ≤
          2 * (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 +
            2 * ((Real.sqrt (n : ℝ))⁻¹) ^ 2 * S x ^ 2 := by
        intro x
        nlinarith [sq_nonneg (W n x - 2 * (Real.sqrt (n : ℝ))⁻¹ * S x)]
      have hBA : B n = A n := by simp [B, hn]
      calc
        (n : ℝ) * ∫ x in A n, W n x ^ 2 ∂P ≤
            (n : ℝ) * ∫ x in A n,
              (2 * (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 +
                2 * ((Real.sqrt (n : ℝ))⁻¹) ^ 2 * S x ^ 2) ∂P := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
          exact setIntegral_mono_on hW2n.integrableOn
              ((herrn.const_mul 2).add (hS2.const_mul _)).integrableOn
              (hBA ▸ hBmeas n) fun x _ => by
                exact hpoint x
        _ ≤ 2 * ((n : ℝ) * ∫ x,
              (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 ∂P) +
            2 * ∫ x in B n, S x ^ 2 ∂P := by
          rw [hBA]
          rw [integral_add (herrn.const_mul 2 |>.integrableOn)
            (hS2.const_mul _ |>.integrableOn), integral_const_mul, integral_const_mul]
          have hemono : ∫ x in A n,
              (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 ∂P ≤
              ∫ x, (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 ∂P :=
            integral_mono_measure P.restrict_le_self (ae_of_all _ fun x => sq_nonneg _) herrn
          have hsqrtn : (n : ℝ) * ((Real.sqrt (n : ℝ))⁻¹) ^ 2 ≤ 1 := by
            by_cases hn0 : n = 0
            · simp [hn0]
            · rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
              field_simp
              norm_num
          have hSint : 0 ≤ ∫ x in A n, S x ^ 2 ∂P :=
            integral_nonneg (μ := P.restrict (A n)) (fun x => sq_nonneg (S x))
          nlinarith
    · rw [integral_undef]
      · simp only [mul_zero]
        have hBn : B n = ∅ := by simp [B, hn]
        rw [hBn, setIntegral_empty]
        have herr_nonneg : 0 ≤ (n : ℝ) * ∫ x,
            (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 ∂P :=
          mul_nonneg (Nat.cast_nonneg n)
            (integral_nonneg (μ := P) (fun x => sq_nonneg _))
        positivity
      · intro htail
        apply hn
        have hcomp : IntegrableOn (fun x => W n x ^ 2) (A n)ᶜ P := by
          apply (integrable_const (μ := P.restrict (A n)ᶜ) (c := ε ^ 2)).mono'
          · exact (hW n).pow_const 2 |>.aestronglyMeasurable.restrict
          · filter_upwards [ae_restrict_mem
                ((measurableSet_Ici.preimage (hW n).abs).compl)] with x hx
            simp only [A, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            have hs := (sq_lt_sq₀ (abs_nonneg (W n x)) hε.le).2 hx
            rw [sq_abs] at hs
            exact hs.le
        change Integrable (fun x => W n x ^ 2) P
        rw [← integrableOn_univ, ← Set.union_compl_self (A n), integrableOn_union]
        exact ⟨htail, hcomp⟩
  · simpa using (happrox.const_mul 2).add (hsmall.const_mul 2)

/-- For an i.i.d. product row, a centered sum of errors converges in probability to zero when
the row error has total second moment tending to zero.  A convergent scaled row mean supplies
the stated deterministic limit. -/
theorem iid_sum_approx_tendstoInProbability
    (P : Measure X) [IsProbabilityMeasure P]
    (W : ℕ → X → ℝ) (S : X → ℝ) (m : ℝ)
    (hW : ∀ n, Measurable (W n)) (hW2 : ∀ n, MemLp (W n) 2 P)
    (hS : MemLp S 2 P)
    (hSmean : ∫ x, S x ∂P = 0)
    (happrox : Tendsto (fun n : ℕ => (n : ℝ) * ∫ x,
      (W n x - (Real.sqrt (n : ℝ))⁻¹ * S x) ^ 2 ∂P) atTop (𝓝 0))
    (hmean : Tendsto (fun n : ℕ => (n : ℝ) * ∫ x, W n x ∂P) atTop (𝓝 m)) :
    TendstoInProbability (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n x => (∑ i, W n (x i)) -
        (Real.sqrt (n : ℝ))⁻¹ * ∑ i, S (x i)) m := by
  -- Apply Chebyshev to the sum of the independent coordinate errors.  Its variance is at most
  -- `n` times the one-coordinate second moment, while its expectation tends to `m`.  Rowwise
  -- `MemLp` is explicit because a bare Bochner square integral does not imply integrability.
  let g : ℕ → X → ℝ := fun n x =>
    W n x - (Real.sqrt (n : ℝ))⁻¹ * S x
  have hg : ∀ n, MemLp (g n) 2 P := by
    intro n
    change MemLp (W n - fun x => (Real.sqrt (n : ℝ))⁻¹ * S x) 2 P
    exact (hW2 n).sub (hS.const_mul (Real.sqrt (n : ℝ))⁻¹)
  have hgmean : ∀ n, ∫ x, g n x ∂P = ∫ x, W n x ∂P := by
    intro n
    simp only [g]
    rw [integral_sub ((hW2 n).integrable (by norm_num))
      ((hS.const_mul _).integrable (by norm_num)), integral_const_mul, hSmean]
    ring
  have hcenter : Tendsto (fun n : ℕ => (n : ℝ) * ∫ x, g n x ∂P)
      atTop (𝓝 m) := by
    simpa only [hgmean] using hmean
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hcenter_close : ∀ᶠ n : ℕ in atTop,
      |(n : ℝ) * ∫ x, g n x ∂P - m| < ε / 2 := by
    rw [Metric.tendsto_atTop] at hcenter
    obtain ⟨N, hN⟩ := hcenter (ε / 2) hhalf
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa [Real.dist_eq] using hN n hn
  have hbound_tend : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (((n : ℝ) * ∫ x, (g n x) ^ 2 ∂P) / (ε / 2) ^ 2))
      atTop (𝓝 0) := by
    have ht := ENNReal.tendsto_ofReal (happrox.div_const ((ε / 2) ^ 2))
    simpa [g] using ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (f := fun n => Measure.pi (fun _ : Fin n => P)
        {x | ε ≤ |((∑ i, W n (x i)) -
          (Real.sqrt (n : ℝ))⁻¹ * ∑ i, S (x i)) - m|})
      (g := fun _ => 0)
      (h := fun n => ENNReal.ofReal
        (((n : ℝ) * ∫ x, (g n x) ^ 2 ∂P) / (ε / 2) ^ 2))
      tendsto_const_nhds hbound_tend
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [hcenter_close] with n hn
    have hcheb := Causalean.Stat.Concentration.iid_sum_chebyshev
      (N := n) P (g n) (hg n) hhalf
    calc
      Measure.pi (fun _ : Fin n => P)
          {x | ε ≤ |((∑ i, W n (x i)) -
            (Real.sqrt (n : ℝ))⁻¹ * ∑ i, S (x i)) - m|}
        ≤ Measure.pi (fun _ : Fin n => P)
          {x | ε / 2 ≤ |(∑ i, g n (x i)) -
            (n : ℝ) * ∫ y, g n y ∂P|} := by
          apply measure_mono
          intro x hx
          change ε ≤ |((∑ i, W n (x i)) -
            (Real.sqrt (n : ℝ))⁻¹ * ∑ i, S (x i)) - m| at hx
          change ε / 2 ≤ |(∑ i, g n (x i)) -
            (n : ℝ) * ∫ y, g n y ∂P|
          have hsum : (∑ i, W n (x i)) -
              (Real.sqrt (n : ℝ))⁻¹ * ∑ i, S (x i) =
              ∑ i, g n (x i) := by
            simp only [g, Finset.sum_sub_distrib]
            rw [Finset.mul_sum]
          rw [hsum] at hx
          have htri := abs_sub_le (∑ i, g n (x i))
            ((n : ℝ) * ∫ y, g n y ∂P) m
          nlinarith
      _ ≤ ENNReal.ofReal
          ((n : ℝ) * Var[g n; P] / (ε / 2) ^ 2) := hcheb
      _ ≤ ENNReal.ofReal
          (((n : ℝ) * ∫ x, (g n x) ^ 2 ∂P) / (ε / 2) ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left
          (variance_le_expectation_sq (hg n).aestronglyMeasurable)
          (Nat.cast_nonneg n)

/-- For one square-integrable row, the probability that at least one i.i.d. coordinate exceeds
`δ` is bounded by `n / δ²` times the second moment on the tail `|W| ≥ δ`. -/
theorem iid_large_coordinate_measureReal_le
    (P : Measure X) [IsProbabilityMeasure P]
    (W : X → ℝ) (hW : Measurable W) (hW2 : MemLp W 2 P)
    (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (Measure.pi (fun _ : Fin n => P)).real
        {x | ∃ i, δ ≤ |W (x i)|} ≤
      (n : ℝ) * (δ ^ 2)⁻¹ * ∫ x in {x | δ ≤ |W x|}, W x ^ 2 ∂P := by
  -- Rewrite the event as a finite union, use `measureReal_iUnion_fintype_le`, identify every
  -- coordinate marginal by `measurePreserving_eval`, and apply Markov to `W²` on the tail.
  let A : Set X := {x | δ ≤ |W x|}
  have hA : MeasurableSet A := measurableSet_Ici.preimage hW.abs
  have hsingle : P.real A ≤ (δ ^ 2)⁻¹ * ∫ x in A, W x ^ 2 ∂P := by
    let f : X → ℝ := A.indicator (fun x => W x ^ 2)
    have hfint : Integrable f P := hW2.integrable_sq.indicator hA
    have hfnonneg : ∀ᵐ x ∂P, 0 ≤ f x :=
      ae_of_all P fun x => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (μ := P) hfnonneg hfint (δ ^ 2)
    have hset : {x | δ ^ 2 ≤ f x} = A := by
      ext x
      by_cases hx : x ∈ A
      · simp only [f, Set.indicator_of_mem hx, Set.mem_ofPred_eq, hx, iff_true]
        have habs : δ ≤ |W x| := hx
        simpa [sq_abs] using (sq_le_sq₀ hδ.le (abs_nonneg _)).2 habs
      · simp only [f, Set.indicator_of_notMem hx, Set.mem_ofPred_eq, hx, iff_false]
        exact not_le_of_gt (sq_pos_of_pos hδ)
    rw [hset, integral_indicator hA] at hmarkov
    calc
      P.real A = (δ ^ 2)⁻¹ * ((δ ^ 2) * P.real A) := by field_simp
      _ ≤ (δ ^ 2)⁻¹ * ∫ x in A, W x ^ 2 ∂P :=
        mul_le_mul_of_nonneg_left hmarkov (inv_nonneg.2 (sq_nonneg δ))
  have hevent : {x : Fin n → X | ∃ i, δ ≤ |W (x i)|} =
      ⋃ i : Fin n, (Function.eval i) ⁻¹' A := by
    ext x
    simp [A]
  rw [hevent]
  calc
    (Measure.pi (fun _ : Fin n => P)).real
        (⋃ i : Fin n, (Function.eval i) ⁻¹' A)
      ≤ ∑ i : Fin n, (Measure.pi (fun _ : Fin n => P)).real
          ((Function.eval i) ⁻¹' A) :=
        measureReal_iUnion_fintype_le _
    _ = ∑ _i : Fin n, P.real A := by
      apply Finset.sum_congr rfl
      intro i _
      exact (measurePreserving_eval (fun _ : Fin n => P) i).measureReal_preimage
        hA.nullMeasurableSet
    _ ≤ ∑ _i : Fin n, ((δ ^ 2)⁻¹ * ∫ x in A, W x ^ 2 ∂P) :=
      Finset.sum_le_sum fun _ _ => hsingle
    _ = (n : ℝ) * (δ ^ 2)⁻¹ * ∫ x in A, W x ^ 2 ∂P := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [Finset.card_univ, Fintype.card_fin]
      ring

/-- The centered sum of the truncated squares `W² 1{|W|<δ}` under an i.i.d. product law obeys
a Chebyshev bound controlled by `n δ² E[W²]`. -/
theorem iid_truncated_sq_deviation_le
    (P : Measure X) [IsProbabilityMeasure P]
    (W : X → ℝ) (hW : Measurable W) (hW2 : MemLp W 2 P)
    (n : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    Measure.pi (fun _ : Fin n => P)
        {x | ε ≤ |(∑ i, if |W (x i)| < δ then W (x i) ^ 2 else 0) -
          (n : ℝ) * ∫ y, (if |W y| < δ then W y ^ 2 else 0) ∂P|} ≤
      ENNReal.ofReal (((n : ℝ) * δ ^ 2 * ∫ y, W y ^ 2 ∂P) / ε ^ 2) := by
  -- Apply `Causalean.Stat.Concentration.iid_sum_chebyshev` to the bounded truncation.  Bound its
  -- variance by its second moment and use `(W² 1{|W|<δ})² ≤ δ² W²` under the base law.
  let g : X → ℝ := fun x => if |W x| < δ then W x ^ 2 else 0
  have hgmeas : Measurable g := by
    exact (hW.pow_const 2).ite (measurableSet_Iio.preimage hW.abs) measurable_const
  have hgbound : ∀ x, ‖g x‖ ≤ δ ^ 2 := by
    intro x
    simp only [g]
    split_ifs with hx
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hs := (sq_lt_sq₀ (abs_nonneg (W x)) hδ.le).2 hx
      simpa [sq_abs] using hs.le
    · simp only [norm_zero]
      exact sq_nonneg δ
  have hg : MemLp g 2 P :=
    MemLp.of_bound hgmeas.aestronglyMeasurable (δ ^ 2) (ae_of_all P hgbound)
  have hvar : Var[g; P] ≤ δ ^ 2 * ∫ y, W y ^ 2 ∂P := by
    calc
      Var[g; P] ≤ ∫ y, g y ^ 2 ∂P :=
        variance_le_expectation_sq hg.aestronglyMeasurable
      _ ≤ ∫ y, δ ^ 2 * W y ^ 2 ∂P := by
        apply integral_mono hg.integrable_sq (hW2.integrable_sq.const_mul _)
        intro y
        simp only [g]
        split_ifs with hy
        · have hs := (sq_lt_sq₀ (abs_nonneg (W y)) hδ.le).2 hy
          rw [sq_abs] at hs
          nlinarith [sq_nonneg (W y)]
        · simpa using mul_nonneg (sq_nonneg δ) (sq_nonneg (W y))
      _ = δ ^ 2 * ∫ y, W y ^ 2 ∂P := by rw [integral_const_mul]
  have hcheb := Causalean.Stat.Concentration.iid_sum_chebyshev (N := n) P g hg hε
  change Measure.pi (fun _ : Fin n => P)
        {x | ε ≤ |(∑ i, g (x i)) - (n : ℝ) * ∫ y, g y ∂P|} ≤ _
  refine hcheb.trans ?_
  apply ENNReal.ofReal_le_ofReal
  calc
    (n : ℝ) * Var[g; P] / ε ^ 2 ≤
        (n : ℝ) * (δ ^ 2 * ∫ y, W y ^ 2 ∂P) / ε ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg ε)
      exact mul_le_mul_of_nonneg_left hvar (Nat.cast_nonneg n)
    _ = ((n : ℝ) * δ ^ 2 * ∫ y, W y ^ 2 ∂P) / ε ^ 2 := by ring

/-- The sum of squares in an infinitesimal i.i.d. triangular row obeys a weak law when its
scaled second moment converges and its Lindeberg tail vanishes. -/
theorem iid_sum_sq_tendstoInProbability_of_lindeberg
    (P : Measure X) [IsProbabilityMeasure P]
    (W : ℕ → X → ℝ) (q : ℝ)
    (hW : ∀ n, Measurable (W n)) (hW2 : ∀ n, MemLp (W n) 2 P)
    (hsecond : Tendsto (fun n : ℕ => (n : ℝ) * ∫ x, W n x ^ 2 ∂P)
      atTop (𝓝 q))
    (hlindeberg : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (n : ℝ) *
      ∫ x in {x | ε ≤ |W n x|}, W n x ^ 2 ∂P) atTop (𝓝 0)) :
    TendstoInProbability (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n x => (∑ i, W n (x i) ^ 2)) q := by
  -- Truncate `W²` at a fixed level, apply Chebyshev to the bounded independent summands, and
  -- remove the truncation with `hlindeberg`; then send the truncation level to zero.
  intro ε hε
  have hreal : Tendsto (fun n => (Measure.pi (fun _ : Fin n => P)).real
      {x | ε ≤ |(∑ i, W n (x i) ^ 2) - q|}) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    let ρ : ℝ := min η 1
    have hρ : 0 < ρ := lt_min hη zero_lt_one
    have hρη : ρ ≤ η := min_le_left _ _
    have hρ1 : ρ ≤ 1 := min_le_right _ _
    let t : ℝ := ε / 2
    have ht : 0 < t := half_pos hε
    let C : ℝ := |q| + 1
    have hC : 0 < C := by positivity
    have hC1 : 1 ≤ C := by simp [C]
    let δ : ℝ := ρ * t / (4 * C)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    let a : ℕ → ℝ := fun n => (n : ℝ) *
      ∫ x, (if |W n x| < δ then W n x ^ 2 else 0) ∂P
    let b : ℕ → ℝ := fun n => (n : ℝ) * ∫ x, W n x ^ 2 ∂P
    let r : ℕ → ℝ := fun n => (n : ℝ) *
      ∫ x in {x | δ ≤ |W n x|}, W n x ^ 2 ∂P
    have hsplit : ∀ n, b n = a n + r n := by
      intro n
      have hA : MeasurableSet {x | δ ≤ |W n x|} :=
        measurableSet_Ici.preimage (hW n).abs
      have hsint : Integrable (fun x => W n x ^ 2) P := (hW2 n).integrable_sq
      have htint : Integrable (fun x =>
          if |W n x| < δ then W n x ^ 2 else 0) P := by
        apply hsint.mono'
        · exact ((hW n).pow_const 2).ite
            (measurableSet_Iio.preimage (hW n).abs) measurable_const
            |>.aestronglyMeasurable
        · exact ae_of_all P fun x => by
            split_ifs <;> simp [sq_nonneg]
      have hrint : Integrable
          ({x | δ ≤ |W n x|}.indicator (fun x => W n x ^ 2)) P :=
        hsint.indicator hA
      dsimp [a, b, r]
      rw [← integral_indicator hA, ← mul_add, ← integral_add htint hrint]
      congr 1
      apply integral_congr_ae
      exact ae_of_all P fun x => by
        change W n x ^ 2 = (if |W n x| < δ then W n x ^ 2 else 0) +
          {x | δ ≤ |W n x|}.indicator (fun x => W n x ^ 2) x
        by_cases hx : δ ≤ |W n x|
        · simp [hx, not_lt_of_ge hx]
        · simp [hx, lt_of_not_ge hx]
    have ha : Tendsto a atTop (𝓝 q) := by
      have hbr : Tendsto (fun n => b n - r n) atTop (𝓝 q) := by
        simpa [b, r] using hsecond.sub (hlindeberg δ hδ)
      apply hbr.congr'
      exact Eventually.of_forall fun n => by
        change b n - r n = a n
        rw [hsplit n]
        ring
    have hlarge_tend : Tendsto (fun n => (δ ^ 2)⁻¹ * r n) atTop (𝓝 0) := by
      simpa [r] using (hlindeberg δ hδ).const_mul ((δ ^ 2)⁻¹)
    have hlarge_small : ∀ᶠ n in atTop, (δ ^ 2)⁻¹ * r n < ρ / 4 := by
      have hm := Metric.tendsto_atTop.mp hlarge_tend (ρ / 4) (by positivity)
      obtain ⟨N, hN⟩ := hm
      filter_upwards [eventually_ge_atTop N] with n hn
      have hh := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hh
      · exact hh
      · exact mul_nonneg (inv_nonneg.2 (sq_nonneg δ))
          (mul_nonneg (Nat.cast_nonneg n)
            (integral_nonneg (μ := P.restrict {x | δ ≤ |W n x|})
              (fun x => sq_nonneg _)))
    have habias : ∀ᶠ n in atTop, |a n - q| < t := by
      have hm := Metric.tendsto_atTop.mp ha t ht
      obtain ⟨N, hN⟩ := hm
      filter_upwards [eventually_ge_atTop N] with n hn
      simpa [Real.dist_eq] using hN n hn
    have hbC : ∀ᶠ n in atTop, b n < C := by
      have hm := Metric.tendsto_atTop.mp
        (show Tendsto b atTop (𝓝 q) by simpa [b] using hsecond) 1 zero_lt_one
      obtain ⟨N, hN⟩ := hm
      filter_upwards [eventually_ge_atTop N] with n hn
      have hh := hN n hn
      rw [Real.dist_eq] at hh
      dsimp [C]
      have hsub : b n - q ≤ |b n - q| := le_abs_self _
      linarith [le_abs_self q]
    rw [← eventually_atTop]
    filter_upwards [hlarge_small, habias, hbC] with n hnlarge hnbias hnb
    let μn : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => P)
    let L : Set (Fin n → X) := {x | ∃ i, δ ≤ |W n (x i)|}
    let D : Set (Fin n → X) := {x | t ≤
      |(∑ i, if |W n (x i)| < δ then W n (x i) ^ 2 else 0) - a n|}
    have hsubset :
        {x | ε ≤ |(∑ i, W n (x i) ^ 2) - q|} ⊆ L ∪ D := by
      intro x hx
      by_cases hxL : x ∈ L
      · exact Set.mem_union_left _ hxL
      · apply Set.mem_union_right
        change t ≤ |(∑ i, if |W n (x i)| < δ then W n (x i) ^ 2 else 0) - a n|
        have hall : ∀ i, |W n (x i)| < δ := by
          intro i
          exact lt_of_not_ge fun hi => hxL ⟨i, hi⟩
        have hsum : (∑ i, if |W n (x i)| < δ then W n (x i) ^ 2 else 0) =
            ∑ i, W n (x i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          simp [hall i]
        rw [hsum]
        have htri := abs_sub_le (∑ i, W n (x i) ^ 2) (a n) q
        change ε ≤ |(∑ i, W n (x i) ^ 2) - q| at hx
        dsimp [t] at *
        nlinarith
    have hL : μn.real L ≤ (δ ^ 2)⁻¹ * r n := by
      dsimp [μn, L]
      calc
        (Measure.pi (fun _ : Fin n => P)).real
            {x | ∃ i, δ ≤ |W n (x i)|}
          ≤ (n : ℝ) * (δ ^ 2)⁻¹ *
              ∫ x in {x | δ ≤ |W n x|}, W n x ^ 2 ∂P :=
            iid_large_coordinate_measureReal_le P (W n) (hW n) (hW2 n) n hδ
        _ = (δ ^ 2)⁻¹ * r n := by dsimp [r]; ring
    have hD_enn := iid_truncated_sq_deviation_le
      P (W n) (hW n) (hW2 n) n hδ ht
    have hD : μn.real D ≤ (b n * δ ^ 2) / t ^ 2 := by
      change (μn D).toReal ≤ (b n * δ ^ 2) / t ^ 2
      have hh := (ENNReal.toReal_le_toReal
        (measure_ne_top μn D) ENNReal.ofReal_ne_top).2 hD_enn
      rw [ENNReal.toReal_ofReal] at hh
      · calc
          (μn D).toReal ≤ ((n : ℝ) * δ ^ 2 * ∫ y, W n y ^ 2 ∂P) / t ^ 2 := hh
          _ = (b n * δ ^ 2) / t ^ 2 := by dsimp [b]; ring
      · positivity
    have hdevsmall : (b n * δ ^ 2) / t ^ 2 < ρ / 4 := by
      have hnonneg : 0 ≤ b n := by
        dsimp [b]
        positivity
      dsimp [δ]
      field_simp
      nlinarith [sq_nonneg ρ, mul_nonneg hnonneg (sq_nonneg ρ)]
    have htotal : μn.real
        {x | ε ≤ |(∑ i, W n (x i) ^ 2) - q|} < η := by
      calc
        μn.real {x | ε ≤ |(∑ i, W n (x i) ^ 2) - q|}
          ≤ μn.real (L ∪ D) := measureReal_mono hsubset
        _ ≤ μn.real L + μn.real D := measureReal_union_le _ _
        _ ≤ (δ ^ 2)⁻¹ * r n + (b n * δ ^ 2) / t ^ 2 :=
          add_le_add hL hD
        _ < ρ / 4 + ρ / 4 := add_lt_add hnlarge hdevsmall
        _ ≤ η := by linarith
    simpa [μn, Real.dist_eq, abs_of_nonneg measureReal_nonneg] using htotal
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun n => measure_ne_top (Measure.pi (fun _ : Fin n => P))
      {x | ε ≤ |(∑ i, W n (x i) ^ 2) - q|})).1 hreal

/-- For an i.i.d. triangular row with [measurable coordinates](hyp:hW), [finite second moments](hyp:hW2), and [a Lindeberg tail condition](hyp:hlindeberg), [the probability that its largest absolute coordinate exceeds any positive threshold vanishes](goal). -/
theorem iid_max_tendsto_zero_of_lindeberg
    (P : Measure X) [IsProbabilityMeasure P]
    (W : ℕ → X → ℝ)
    (hW : ∀ n, Measurable (W n)) (hW2 : ∀ n, MemLp (W n) 2 P)
    (hlindeberg : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (n : ℝ) *
      ∫ x in {x | ε ≤ |W n x|}, W n x ^ 2 ∂P) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => Measure.pi (fun _ : Fin n => P)
      {x | ∃ i, ε ≤ |W n (x i)|}) atTop (𝓝 0) := by
  -- Use the finite union bound and Markov on `W² 1_{|W|≥ε}`.  The explicit
  -- `MemLp` premise is logically necessary with Mathlib's Bochner integral convention:
  -- the integral of a non-integrable real function is definitionally zero, so the displayed
  -- Lindeberg limit alone cannot rule out non-square-integrable rows.
  intro ε hε
  have hreal : Tendsto (fun n => (Measure.pi (fun _ : Fin n => P)).real
      {x | ∃ i, ε ≤ |W n (x i)|}) atTop (𝓝 0) := by
    apply squeeze_zero (g := fun n : ℕ => (ε ^ 2)⁻¹ *
      ((n : ℝ) * ∫ x in {x | ε ≤ |W n x|}, W n x ^ 2 ∂P))
    · exact fun n => measureReal_nonneg
    · intro n
      calc
        (Measure.pi (fun _ : Fin n => P)).real
            {x | ∃ i, ε ≤ |W n (x i)|}
          ≤ (n : ℝ) * (ε ^ 2)⁻¹ *
              ∫ x in {x | ε ≤ |W n x|}, W n x ^ 2 ∂P :=
            iid_large_coordinate_measureReal_le P (W n) (hW n) (hW2 n) n hε
        _ = (ε ^ 2)⁻¹ *
              ((n : ℝ) * ∫ x in {x | ε ≤ |W n x|}, W n x ^ 2 ∂P) := by ring
    · simpa using (hlindeberg ε hε).const_mul ((ε ^ 2)⁻¹)
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun n => measure_ne_top (Measure.pi (fun _ : Fin n => P))
      {x | ∃ i, ε ≤ |W n (x i)|})).1 hreal

end Causalean.Estimation.Efficiency.AsymptoticLanConvolution

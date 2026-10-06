module
public import Causalean.Stat.Concentration.BoundedVariation.Variation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Weighted integrals of bounded-variation paths

An integral of continuous paths against a bounded scalar weight remains a continuous path.
Its supremum norm plus total variation is bounded by the common path-size envelope times the
weight bound. This is the analytic step for integral coefficient extraction.
-/

public section

open MeasureTheory
open Causalean.Stat.Concentration.BoundedVariation

namespace Causalean.Stat.Concentration.BoundedVariation

/-- [A probability measure](hyp:μ), [a family of continuous paths and a scalar weight](hyp:f,w), [nonnegative path-size and weight bounds](hyp:B,M,hB,hM), [integrability of each weighted time section](hyp:hInt), [a pointwise weight bound](hyp:hweight), [finite variation of every input path](hyp:hBV), and [a common path-size bound](hyp:hsize) give [a continuous bounded-variation weighted integral path with the stated size bound](goal).

Integrating a family of continuous bounded-variation paths against a uniformly bounded
weight produces a continuous bounded-variation path. If each input path has size at most `B`
and the weight has absolute value at most `M`, the integral path has size at most `M * B`.

Use dominated convergence for continuity. For each finite time partition, integrate the
pointwise supremum norm plus increment sum before taking the variation supremum; this keeps
the sharp factor `M` rather than separately bounding the two terms by `M * B`.
-/
theorem weightedPathIntegral_size_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → Path) (w : α → ℝ) (B M : ℝ)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hInt : ∀ t : Time, Integrable (fun x => w x * f x t) μ)
    (hweight : ∀ x, |w x| ≤ M)
    (hBV : ∀ x, eVariationOn (f x) Set.univ < ⊤)
    (hsize : ∀ x, pathSize (f x) ≤ B) :
    ∃ g : Path,
      (∀ t : Time, g t = ∫ x, w x * f x t ∂μ) ∧
      eVariationOn g Set.univ < ⊤ ∧
      pathSize g ≤ M * B := by
  let F : Time → α → ℝ := fun t x => w x * f x t
  have hF_bound (t : Time) (x : α) : ‖F t x‖ ≤ M * B := by
    have hf : ‖f x t‖ ≤ B := by
      calc
        ‖f x t‖ ≤ ‖f x‖ := ContinuousMap.norm_coe_le_norm (f x) t
        _ ≤ pathSize (f x) := by simp [pathSize, pathTV_nonneg]
        _ ≤ B := hsize x
    calc
      ‖F t x‖ = |w x| * ‖f x t‖ := by simp [F, norm_mul, Real.norm_eq_abs]
      _ ≤ M * B := mul_le_mul (hweight x) hf (norm_nonneg _) hM
  have hF_cont : Continuous (fun t : Time => ∫ x, F t x ∂μ) := by
    apply continuous_of_dominated (bound := fun _ => M * B)
    · intro t
      exact (hInt t).aestronglyMeasurable
    · intro t
      exact Filter.Eventually.of_forall (fun x => hF_bound t x)
    · exact integrable_const (M * B)
    · exact Filter.Eventually.of_forall (fun x => (continuous_const.mul (f x).continuous))
  let g : Path := ⟨fun t => ∫ x, F t x ∂μ, hF_cont⟩
  have hg (t : Time) : g t = ∫ x, w x * f x t ∂μ := rfl
  have hpart (t : Time) (n : ℕ) (u : ℕ → Time) (hu : Monotone u) :
      ‖g t‖ + ∑ i ∈ Finset.range n, ‖g (u (i + 1)) - g (u i)‖ ≤ M * B := by
    have hpoint (x : α) : ‖F t x‖ +
        ∑ i ∈ Finset.range n, ‖F (u (i + 1)) x - F (u i) x‖ ≤ M * B := by
      have hinc : (∑ i ∈ Finset.range n,
          ‖f x (u (i + 1)) - f x (u i)‖) ≤ pathTV (f x) := by
        have hs := eVariationOn.sum_le (f := f x) (n := n) hu
          (fun i => Set.mem_univ (u i))
        have hs' := ENNReal.toReal_mono (ne_of_lt (hBV x)) hs
        rw [ENNReal.toReal_sum] at hs'
        · simp_rw [← dist_edist, Real.dist_eq] at hs'
          simpa [pathTV, Real.norm_eq_abs] using hs'
        · intro i hi
          exact ne_of_lt (edist_lt_top _ _)
      have hbase : ‖f x t‖ +
          ∑ i ∈ Finset.range n, ‖f x (u (i + 1)) - f x (u i)‖ ≤ B := by
        have ht := ContinuousMap.norm_coe_le_norm (f x) t
        have hz := hsize x
        dsimp [pathSize] at hz
        linarith
      have hw : 0 ≤ |w x| := abs_nonneg _
      calc
        ‖F t x‖ + ∑ i ∈ Finset.range n, ‖F (u (i + 1)) x - F (u i) x‖ =
            |w x| * (‖f x t‖ + ∑ i ∈ Finset.range n,
              ‖f x (u (i + 1)) - f x (u i)‖) := by
                simp [F, ← mul_sub, norm_mul, Real.norm_eq_abs, Finset.mul_sum, mul_add]
        _ ≤ |w x| * B := mul_le_mul_of_nonneg_left hbase hw
        _ ≤ M * B := mul_le_mul_of_nonneg_right (hweight x) hB
    let D (i : ℕ) (x : α) := F (u (i + 1)) x - F (u i) x
    have hDInt (i : ℕ) : Integrable (D i) μ := (hInt (u (i + 1))).sub (hInt (u i))
    have hDNormInt (i : ℕ) : Integrable (fun x => ‖D i x‖) μ := (hDInt i).norm
    have hFNormInt : Integrable (fun x => ‖F t x‖) μ := (hInt t).norm
    have hsumInt : Integrable (fun x => ∑ i ∈ Finset.range n, ‖D i x‖) μ :=
      integrable_finsetSum _ (fun i hi => hDNormInt i)
    have hD_eq (i : ℕ) : g (u (i + 1)) - g (u i) = ∫ x, D i x ∂μ := by
      rw [hg, hg, ← integral_sub (hInt (u (i + 1))) (hInt (u i))]
    calc
      ‖g t‖ + ∑ i ∈ Finset.range n, ‖g (u (i + 1)) - g (u i)‖ ≤
          (∫ x, ‖F t x‖ ∂μ) + ∑ i ∈ Finset.range n, ∫ x, ‖D i x‖ ∂μ := by
            apply add_le_add
            · simpa [g] using (norm_integral_le_integral_norm (fun x => F t x) (μ := μ))
            · apply Finset.sum_le_sum
              intro i hi
              rw [hD_eq i]
              exact norm_integral_le_integral_norm (D i)
      _ = ∫ x, (‖F t x‖ + ∑ i ∈ Finset.range n, ‖D i x‖) ∂μ := by
            rw [integral_add hFNormInt hsumInt]
            rw [integral_finsetSum (Finset.range n) (fun i hi => hDNormInt i)]
      _ ≤ ∫ x, (M * B) ∂μ := by
            apply integral_mono (hFNormInt.add hsumInt) (integrable_const _)
            intro x
            exact hpoint x
      _ = M * B := by simp
  have hnorm : ‖g‖ ≤ M * B := by
    apply (ContinuousMap.norm_le g (mul_nonneg hM hB)).2
    intro t
    simpa using hpart t 0 (fun _ => t) monotone_const
  have hvar : eVariationOn g Set.univ ≤ ENNReal.ofReal (M * B - ‖g‖) := by
    apply iSup_le
    rintro ⟨n, ⟨u, hu, hus⟩⟩
    have hs : (∑ i ∈ Finset.range n, ‖g (u (i + 1)) - g (u i)‖) ≤
        M * B - ‖g‖ := by
      have hc : 0 ≤ M * B - ∑ i ∈ Finset.range n,
          ‖g (u (i + 1)) - g (u i)‖ := by
        have hp := hpart timeZero n u hu
        have ht := norm_nonneg (g timeZero)
        linarith
      have hn : ‖g‖ ≤ M * B - ∑ i ∈ Finset.range n,
          ‖g (u (i + 1)) - g (u i)‖ := by
        apply (ContinuousMap.norm_le g hc).2
        intro t
        have hp := hpart t n u hu
        linarith
      linarith
    calc
      (∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i))) =
          ENNReal.ofReal (∑ i ∈ Finset.range n, ‖g (u (i + 1)) - g (u i)‖) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            · simp [edist_dist, Real.dist_eq, abs_sub_comm]
            · intro i hi
              exact norm_nonneg _
      _ ≤ ENNReal.ofReal (M * B - ‖g‖) := ENNReal.ofReal_le_ofReal hs
  have hfinite : eVariationOn g Set.univ < ⊤ :=
    lt_of_le_of_lt hvar ENNReal.ofReal_lt_top
  refine ⟨g, hg, hfinite, ?_⟩
  have hnonneg : 0 ≤ M * B - ‖g‖ := sub_nonneg.mpr hnorm
  have htv : pathTV g ≤ M * B - ‖g‖ := by
    simpa [pathTV, ENNReal.toReal_ofReal hnonneg] using
      (ENNReal.toReal_mono (ne_of_lt (ENNReal.ofReal_lt_top)) hvar)
  dsimp [pathSize]
  linarith

end Causalean.Stat.Concentration.BoundedVariation


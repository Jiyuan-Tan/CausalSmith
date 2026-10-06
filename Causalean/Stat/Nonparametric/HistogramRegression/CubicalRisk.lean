module
public import Causalean.Stat.Nonparametric.HistogramRegression.Geometry
public import Causalean.Stat.Nonparametric.HistogramRegression.Risk

/-!
# Hölder cubical histogram risk and optimized rate

For any observation law with unit-cube covariates and bounded responses whose
conditional mean is Hölder, the ceiling-mesh histogram has squared bias of
order `b^(2β)` and variance of order `1/(m*b^d)`. The optimized bandwidth gives
the explicit rate `m^(-2β/(2β+d))`. Constants depend only on dimension and the
Hölder constant/exponent, and all cube boundary points and empty cells are kept.

The integrated marginal loss and zero-empty-cell convention are classical:
Andrew Nobel, "Histogram Regression Estimation Using Data-dependent Partitions"
(1995), introduction and equation (2),
https://nobel.web.unc.edu/wp-content/uploads/sites/13591/2017/01/histreg.pdf.
Here the default is generalized to any fixed point of the unit interval;
the finite-sample rate is derived from the closed occupancy and mesh lemmas.
-/

public section

open MeasureTheory

namespace Causalean.Stat.Nonparametric.HistogramRegression

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- [Measurable cube covariates, responses, and regression function](hyp:hX,hY,hg),
[bounded responses and default](hyp:hbound,ha), [the conditional mean identity](hyp:hmean),
[positive smoothness and a nonnegative Hölder constant](hyp:hβ,hC),
[a Hölder bound](hyp:hholder), and [a bandwidth in `(0,1]`](hyp:hb,hb1)
imply [the explicit bias-plus-cell-count histogram risk bound](goal). -/
theorem cubical_histogram_risk_le {d m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Cube d)
    (Y : Ω → ℝ) (g : Cube d → ℝ) (a β C b : ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hg : Measurable g)
    (hbound : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hmean : ConditionalMean μ X Y g)
    (hβ : 0 < β) (hC : 0 ≤ C) (hb : 0 < b) (hb1 : b ≤ 1)
    (hholder : ∀ x y, |g x - g y| ≤ C * (dist x y) ^ β) :
    risk μ (Measure.pi (fun _ : Fin m => μ)) (cubeLabel b) X Y a g ≤
      2 * C ^ 2 * (Real.sqrt (d : ℝ)) ^ (2 * β) * b ^ (2 * β) +
        6 * (meshCount b : ℝ) ^ d / (m + 1 : ℝ) := by
  -- The constant oscillation envelope sums against cell masses totaling one.
  -- Count only positive-mass cells before comparing with the full label type.
  -- Nonnegative-base rpow identities retain the zero-dimensional cube case.
  let D : ℝ := C * (Real.sqrt (d : ℝ)) ^ β * b ^ β
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hosc : ∀ k x y, cubeLabel b x = k → cubeLabel b y = k →
      |g x - g y| ≤ D := by
    intro k x y hx hy
    exact cube_holder_oscillation g β C b hβ hC hb hb1 hholder x y (hx.trans hy.symm)
  have hr := histogram_risk_le (m := m) μ (cubeLabel b) X Y g a (fun _ => D)
    (measurable_cubeLabel d b) hX hY hg hbound ha hmean (fun _ => hD) hosc
  have hmass := sum_positiveCells_mass μ (cubeLabel b) X (measurable_cubeLabel d b) hX
  have hsum : (∑ k ∈ positiveCells μ (cubeLabel b) X,
      cellMass μ (cubeLabel b) X k * D ^ 2) = D ^ 2 := by
    rw [← Finset.sum_mul, hmass, one_mul]
  have hcard : ((positiveCells μ (cubeLabel b) X).card : ℝ) ≤
      (meshCount b : ℝ) ^ d := by
    have hn := Finset.card_le_univ (positiveCells μ (cubeLabel b) X)
    rw [cube_label_card d b] at hn
    exact_mod_cast hn
  have hsqrt : ((Real.sqrt (d : ℝ)) ^ β) ^ (2 : ℕ) =
      (Real.sqrt (d : ℝ)) ^ (2 * β) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (Real.sqrt_nonneg _)]
    congr 1
    ring
  have hbpow : (b ^ β) ^ (2 : ℕ) = b ^ (2 * β) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hb.le]
    congr 1
    ring
  have hDsquare : D ^ 2 = C ^ 2 * (Real.sqrt (d : ℝ)) ^ (2 * β) * b ^ (2 * β) := by
    dsimp [D]
    rw [mul_pow, mul_pow, hsqrt, hbpow]
  rw [hsum, hDsquare] at hr
  calc
    _ ≤ 2 * (C ^ 2 * (Real.sqrt (d : ℝ)) ^ (2 * β) * b ^ (2 * β)) +
        6 * ((positiveCells μ (cubeLabel b) X).card : ℝ) / (m + 1 : ℝ) := hr
    _ ≤ 2 * (C ^ 2 * (Real.sqrt (d : ℝ)) ^ (2 * β) * b ^ (2 * β)) +
        6 * (meshCount b : ℝ) ^ d / (m + 1 : ℝ) := by
      apply add_le_add le_rfl
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcard (by norm_num)) (by positivity)
    _ = _ := by ring

/-- [Measurable regression inputs](hyp:hX,hY,hg), [bounded responses and
default](hyp:hbound,ha), [the conditional mean identity](hyp:hmean),
[positive Hölder smoothness and a nonnegative constant](hyp:hβ,hC),
[a Hölder bound](hyp:hholder), [a bandwidth in `(0,1]`](hyp:hb,hb1), and
[at least one observation](hyp:hm) imply [the bias-plus-inverse-effective-sample-size
risk bound](goal). -/
theorem cubical_histogram_bandwidth_risk_le {d m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Cube d)
    (Y : Ω → ℝ) (g : Cube d → ℝ) (a β C b : ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hg : Measurable g)
    (hbound : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hmean : ConditionalMean μ X Y g)
    (hβ : 0 < β) (hC : 0 ≤ C) (hb : 0 < b) (hb1 : b ≤ 1) (hm : 1 ≤ m)
    (hholder : ∀ x y, |g x - g y| ≤ C * (dist x y) ^ β) :
    risk μ (Measure.pi (fun _ : Fin m => μ)) (cubeLabel b) X Y a g ≤
      2 * C ^ 2 * (Real.sqrt (d : ℝ)) ^ (2 * β) * b ^ (2 * β) +
        (6 * (2 : ℝ) ^ d) / ((m : ℝ) * b ^ d) := by
  -- First bound the ceiling cell count by (2/b)^d; then replace m+1 by m.
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  refine (cubical_histogram_risk_le μ X Y g a β C b
    hX hY hg hbound ha hmean hβ hC hb hb1 hholder).trans ?_
  apply add_le_add le_rfl
  calc
    6 * (meshCount b : ℝ) ^ d / (m + 1 : ℝ) ≤
        6 * ((2 : ℝ) ^ d / b ^ d) / (m + 1 : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mesh_count_pow_le d b hb hb1) (by norm_num))
        (by positivity)
    _ ≤ 6 * ((2 : ℝ) ^ d / b ^ d) / (m : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hmpos (by linarith)
    _ = _ := by ring

/-- [Measurable regression inputs](hyp:hX,hY,hg), [bounded responses and
default](hyp:hbound,ha), [the conditional mean identity](hyp:hmean),
[positive Hölder smoothness and nonnegative constant](hyp:hβ,hC),
[a Hölder bound](hyp:hholder), and [at least one observation](hyp:hm)
give [the exact optimized exponent for the ceiling-mesh histogram](goal). -/
theorem optimized_cubical_histogram_risk_le {d m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Cube d)
    (Y : Ω → ℝ) (g : Cube d → ℝ) (a β C : ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hg : Measurable g)
    (hbound : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hmean : ConditionalMean μ X Y g)
    (hβ : 0 < β) (hC : 0 ≤ C) (hm : 1 ≤ m)
    (hholder : ∀ x y, |g x - g y| ≤ C * (dist x y) ^ β) :
    risk μ (Measure.pi (fun _ : Fin m => μ))
        (cubeLabel (optimizedBandwidth d β m)) X Y a g ≤
      (2 * C ^ 2 * (Real.sqrt (d : ℝ)) ^ (2 * β) + 6 * (2 : ℝ) ^ d) *
        (m : ℝ) ^ (-(2 * β / (2 * β + d))) := by
  -- Use the closed balancing identity for bias and the optimized ceiling-count
  -- comparison for variance, then factor their common sample-size power.
  obtain ⟨hb, hb1⟩ := optimizedBandwidth_mem d β m hβ hm
  have hr := cubical_histogram_risk_le (m := m) μ X Y g a β C (optimizedBandwidth d β m)
    hX hY hg hbound ha hmean hβ hC hb hb1 hholder
  rw [(optimized_power_identities d β m hβ hm).1] at hr
  refine hr.trans ?_
  have hv := mul_le_mul_of_nonneg_left (optimized_mesh_variance_le d β m hβ hm)
    (by norm_num : (0 : ℝ) ≤ 6)
  calc
    _ ≤ 2 * C ^ 2 * (Real.sqrt (d : ℝ)) ^ (2 * β) *
          (m : ℝ) ^ (-(2 * β / (2 * β + d))) +
        6 * ((2 : ℝ) ^ d * (m : ℝ) ^ (-(2 * β / (2 * β + d)))) := by
      apply add_le_add le_rfl
      simpa only [mul_div_assoc] using hv
    _ = _ := by ring

end

end Causalean.Stat.Nonparametric.HistogramRegression

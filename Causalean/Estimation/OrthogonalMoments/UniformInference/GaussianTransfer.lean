module
public import Causalean.Estimation.OrthogonalMoments.UniformInference.Basic

/-! # Uniform CDF transfer under a negligible perturbation

This probability inequality transfers class-uniform Gaussian convergence
from one statistic to another when their difference vanishes uniformly in
probability. It is independent of cross-fitting and variance estimation.
-/

public section

namespace Causalean.Estimation.OrthogonalMoments.UniformInference

open MeasureTheory ProbabilityTheory Filter Topology

variable {ι Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  {K : ℕ} (F : Family ι Ω Z K)

namespace Family

private theorem gaussian_cdf_increment_le {a b : ℝ} (hab : a ≤ b) :
    ((gaussianReal 0 1) (Set.Iic b)).toReal -
      ((gaussianReal 0 1) (Set.Iic a)).toReal ≤ b - a := by
  have hpdf : ∀ x : ℝ, gaussianPDFReal 0 1 x ≤ 1 := by
    intro x
    have hroot : 1 ≤ Real.sqrt (2 * Real.pi) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity),
        Real.one_le_pi_div_two, Real.sqrt_nonneg (2 * Real.pi)]
    have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hroot
    have he : Real.exp (-(x ^ 2 / 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    have hmul := (mul_le_mul hinv he (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans
        (by norm_num : (1 : ℝ) * 1 ≤ 1)
    rw [gaussianPDFReal_def]
    simpa only [NNReal.coe_one, sub_zero, mul_one, one_mul, div_one,
      neg_div, neg_mul, one_div, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hmono : (gaussianReal 0 1) (Set.Ioc a b) ≤ ENNReal.ofReal (b - a) := by
    rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
    apply ENNReal.ofReal_le_ofReal
    calc
      ∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x
          ≤ ∫ _x in Set.Ioc a b, (1 : ℝ) := by
            apply MeasureTheory.setIntegral_mono_on
              ((integrable_gaussianPDFReal 0 1).integrableOn)
              (MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc]))
              measurableSet_Ioc
            exact fun x _ => hpdf x
      _ = b - a := by simp [hab]
  have hcdf : (gaussianReal 0 1) (Set.Ioc a b) =
      ENNReal.ofReal (((gaussianReal 0 1) (Set.Iic b)).toReal -
        ((gaussianReal 0 1) (Set.Iic a)).toReal) := by
    calc
      (gaussianReal 0 1) (Set.Ioc a b)
          = ENNReal.ofReal (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) := by
              conv_lhs => rw [← measure_cdf (gaussianReal 0 1)]
              exact StieltjesFunction.measure_Ioc _ a b
      _ = _ := by simp only [cdf_eq_real, measureReal_def]
  have hdiff : 0 ≤ ((gaussianReal 0 1) (Set.Iic b)).toReal -
      ((gaussianReal 0 1) (Set.Iic a)).toReal := by
    exact sub_nonneg.mpr (measureReal_mono (Set.Iic_subset_Iic.mpr hab))
  rw [hcdf] at hmono
  exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hab)).mp hmono

/-- For [a cross-fitting family](hyp:F), if [a statistic X converges to the standard Gaussian in
Kolmogorov distance uniformly over the law class](hyp:X,hX) and [a second statistic Y differs from
X by an amount vanishing in probability uniformly over the law class](hyp:Y,hDiff), then [Y also
converges to the standard Gaussian in Kolmogorov distance uniformly over the law class](goal). -/
theorem uniformGaussian_of_uniformOP_difference
    (X Y : ℕ → ι → Ω → ℝ)
    (hX : F.UniformGaussian X)
    (hDiff : F.UniformOP (fun n p ω => Y n p ω - X n p ω)) :
    F.UniformGaussian Y := by
  rw [UniformGaussian, ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · subst ε
    exact Filter.Eventually.of_forall (fun _ => le_top)
  let δ : ℝ := ε.toReal / 4
  have hεfin : ε ≠ ⊤ := htop
  have hεpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεfin
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hXev := (ENNReal.tendsto_nhds_zero.mp hX) (ENNReal.ofReal δ)
    (ENNReal.ofReal_pos.mpr hδ)
  have hDev := (ENNReal.tendsto_nhds_zero.mp (hDiff δ hδ)) (ENNReal.ofReal δ)
    (ENNReal.ofReal_pos.mpr hδ)
  filter_upwards [hXev, hDev] with n hXn hDn
  refine (iSup_le fun p => iSup_le fun hp => iSup_le fun x => ?_)
  have : IsProbabilityMeasure (F.sampleLaw p) :=
    (F.sample p).indep.isProbabilityMeasure
  let μ := F.sampleLaw p
  let G : ℝ → ℝ := fun t => ((gaussianReal 0 1) (Set.Iic t)).toReal
  let A : ℝ → ℝ := fun t => (μ {ω | X n p ω ≤ t}).toReal
  let B : ℝ → ℝ := fun t => (μ {ω | Y n p ω ≤ t}).toReal
  let D : ENNReal := μ {ω | δ ≤ |Y n p ω - X n p ω|}
  have htail : D.toReal ≤ δ := by
    have hDle : D ≤ ENNReal.ofReal δ :=
      (le_iSup_of_le p (le_iSup (fun hp : p ∈ F.lawClass n =>
        μ {ω | δ ≤ |Y n p ω - X n p ω|}) hp)).trans hDn
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hDle).trans_eq
      (ENNReal.toReal_ofReal hδ.le)
  have herror (t : ℝ) : |A t - G t| ≤ δ := by
    have hle : ENNReal.ofReal |A t - G t| ≤ ENNReal.ofReal δ :=
      (le_iSup_of_le p (le_iSup_of_le hp
        (le_iSup (fun x : ℝ => ENNReal.ofReal
          |(μ {ω | X n p ω ≤ x}).toReal - G x|) t))).trans hXn
    exact (ENNReal.ofReal_le_ofReal_iff hδ.le).mp hle
  have hupper : B x ≤ A (x + δ) + D.toReal := by
    change μ.real {ω | Y n p ω ≤ x} ≤
      μ.real {ω | X n p ω ≤ x + δ} + μ.real {ω | δ ≤ |Y n p ω - X n p ω|}
    refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
    intro ω hy
    by_cases ht : δ ≤ |Y n p ω - X n p ω|
    · exact Or.inr ht
    · left
      simp only [Set.mem_ofPred_eq] at hy ⊢
      have hlow := (abs_lt.mp (lt_of_not_ge ht)).1
      linarith
  have hlower : A (x - δ) ≤ B x + D.toReal := by
    change μ.real {ω | X n p ω ≤ x - δ} ≤
      μ.real {ω | Y n p ω ≤ x} + μ.real {ω | δ ≤ |Y n p ω - X n p ω|}
    refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
    intro ω hx
    by_cases ht : δ ≤ |Y n p ω - X n p ω|
    · exact Or.inr ht
    · left
      simp only [Set.mem_ofPred_eq] at hx ⊢
      have hup := (abs_lt.mp (lt_of_not_ge ht)).2
      linarith
  have hGplus : G (x + δ) - G x ≤ δ := by
    simpa [G] using gaussian_cdf_increment_le (a := x) (b := x + δ) (by linarith)
  have hGminus : G x - G (x - δ) ≤ δ := by
    simpa [G] using gaussian_cdf_increment_le (a := x - δ) (b := x) (by linarith)
  have hbound : |B x - G x| ≤ 3 * δ := by
    rw [abs_le] at ⊢
    have hp := herror (x + δ)
    have hm := herror (x - δ)
    rw [abs_le] at hp hm
    constructor <;> linarith
  have hreal : 3 * δ ≤ ε.toReal := by dsimp [δ]; linarith
  exact (ENNReal.ofReal_le_ofReal hbound).trans
    ((ENNReal.ofReal_le_ofReal hreal).trans (ENNReal.ofReal_toReal hεfin).le)

end Family
end Causalean.Estimation.OrthogonalMoments.UniformInference

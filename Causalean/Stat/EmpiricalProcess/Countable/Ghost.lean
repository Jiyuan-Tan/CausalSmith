module
public import Causalean.Stat.EmpiricalProcess.Countable.FiniteAverage
public import Causalean.Stat.EmpiricalProcess.Countable.ProcessMeasurability
public import Causalean.Stat.EmpiricalProcess.Countable.ProductSwap
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul

/-!
# Fourth-moment ghost and Rademacher symmetrization

The conditional Jensen comparison has constant one; coordinatewise exchange
of two iid copies introduces independent signs without changing the product
integral. The fourth-power triangle inequality then gives constant sixteen.
Reference: Moulinath Banerjee, "Empirical Processes: Symmetrization",
October 12, 2010, Lemma 1.1 (the nondecreasing convex moment comparison):
https://dept.stat.lsa.umich.edu/~moulib/emp-proc-notes-symmetrization.pdf
FoML's first-moment symmetrization does not prove these fourth-moment claims.
-/

public section

open MeasureTheory
open scoped BigOperators
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- Under a probability law, if [a real function g](hyp:g) is
[integrable](hyp:hg) and [has an integrable fourth power](hyp:hg4), then
[the fourth power of the integral of g is at most the integral of its
fourth power](goal), by Jensen's inequality. -/
theorem integral_fourth_jensen {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (g : S → ℝ)
    (hg : Integrable g ν) (hg4 : Integrable (fun s => g s ^ 4) ν) :
    (∫ s, g s ∂ν)^4 ≤ ∫ s, g s ^ 4 ∂ν := by
  have hc : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 4) :=
    (show Even (4 : ℕ) from ⟨2, rfl⟩).convexOn_pow
  exact hc.map_integral_le (continuous_id.pow 4).continuousOn isClosed_univ
    (ae_of_all _ fun _ => Set.mem_univ _) hg hg4

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [Nonempty ι]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (F : BoundedClass Ω ι)

/-- For [a positive sample size n](hyp:n,hn), [any sample x](hyp:x), and
[any function of the class](hyp:i), [the population-centered empirical
average of that function equals the expectation, over an independent ghost
sample y drawn from μ, of (1/n) Σ_j (f(x_j) − f(y_j))](goal). -/
theorem centeredAverage_eq_ghost_integral (n : ℕ) (hn : 0 < n)
    (x : Fin n → Ω) (i : ι) :
    Causalean.Stat.Concentration.centeredEmpiricalAverage μ x (F.f i) =
      ∫ y : Fin n → Ω, (n : ℝ)⁻¹ * ∑ j, (F.f i (x j) - F.f i (y j))
        ∂Measure.pi (fun _ : Fin n => μ) := by
  -- BoundedClass.integrable and the probability pi evaluation map make
  -- every summand integrable. Use integral_finsetSum, integral_sub,
  -- integral_const_mul, and integral_comp_eval. The n equal population
  -- integrals cancel the inverse sample-size normalization using hn.
  -- This is an identity for one function, not a supremum exchange.
  have hj (j : Fin n) : Integrable (fun y : Fin n → Ω =>
      F.f i (x j) - F.f i (y j)) (Measure.pi (fun _ : Fin n => μ)) :=
    (integrable_const _).sub (integrable_comp_eval (F.integrable μ i))
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => hj j)]
  have he (j : Fin n) : (∫ y : Fin n → Ω, F.f i (x j) - F.f i (y j)
      ∂Measure.pi (fun _ : Fin n => μ)) = F.f i (x j) - ∫ z, F.f i z ∂μ := by
    rw [integral_sub (integrable_const _)
      (integrable_comp_eval (μ := fun _ : Fin n => μ) (i := j) (F.integrable μ i)),
      integral_const, integral_comp_eval (F.measurable i).aestronglyMeasurable]
    simp
  simp_rw [he]
  unfold Causalean.Stat.Concentration.centeredEmpiricalAverage
  rw [Finset.sum_sub_distrib]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp [Finset.sum_const, hn', mul_sub]

/-- For [a positive sample size n](hyp:n,hn) and [any fixed sample
x](hyp:x), [the fourth power of the centered supremum at x is at most the
expected fourth power of the ghost supremum of x against an independent
ghost sample drawn from μ](goal). -/
theorem centeredSup_fourth_le_ghost (n : ℕ) (hn : 0 < n) (x : Fin n → Ω) :
    centeredSup μ F.f x ^ 4 ≤
      ∫ y, ghostSup F.f x y ^ 4 ∂Measure.pi (fun _ : Fin n => μ) := by
  -- For each index use centeredAverage_eq_ghost_integral,
  -- apply scalar Jensen, dominate by the ghost supremum, then take the
  -- bounded real supremum. No interchange of sup and expectation is asserted.
  let ν := Measure.pi (fun _ : Fin n => μ)
  let g (i : ι) (y : Fin n → Ω) : ℝ :=
    (n : ℝ)⁻¹ * ∑ j, (F.f i (x j) - F.f i (y j))
  have hb (y : Fin n → Ω) : BddAbove (Set.range (fun i => |g i y|)) := by
    refine ⟨|(n : ℝ)⁻¹| * ∑ _ : Fin n, (2 * F.bound), ?_⟩
    rintro _ ⟨i, rfl⟩
    dsimp [g]
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro j _
    exact (abs_sub _ _).trans (by
      have hx := F.bounded i (x j)
      have hy := F.bounded i (y j)
      linarith)
  have hle (i : ι) (y : Fin n → Ω) : |g i y| ≤ ghostSup F.f x y :=
    le_ciSup (hb y) i
  have hm : Measurable (fun y : Fin n → Ω => ghostSup F.f x y) := by
    have hmap : Measurable (fun y : Fin n → Ω => (x, y)) :=
      measurable_const.prodMk measurable_id
    simpa only [Function.comp_def] using (ghostSup_legal μ F n).1.comp hmap
  have hG : Integrable (fun y => ghostSup F.f x y ^ 4) ν := by
    apply Integrable.of_bound (hm.pow_const 4).aestronglyMeasurable ((2 * F.bound) ^ 4)
    apply ae_of_all
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ((ghostSup_legal μ F n).2.1 x y).1 4)]
    exact pow_le_pow_left₀ ((ghostSup_legal μ F n).2.1 x y).1
      ((ghostSup_legal μ F n).2.1 x y).2 4
  unfold centeredSup
  rw [Real.iSup_pow (fun i => abs_nonneg _) 4]
  apply ciSup_le
  intro i
  have hg : Integrable (g i) ν := by
    apply Integrable.const_mul
    exact integrable_finsetSum _ fun j _ =>
      (integrable_const _).sub (integrable_comp_eval (F.integrable μ i))
  have hgm : Measurable (g i) := by
    dsimp [g]
    exact measurable_const.mul (Finset.measurable_sum _ fun j _ =>
      measurable_const.sub ((F.measurable i).comp (measurable_pi_apply j)))
  have hp (y : Fin n → Ω) : g i y ^ 4 ≤ ghostSup F.f x y ^ 4 := by
    calc
      g i y ^ 4 = |g i y| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      _ ≤ ghostSup F.f x y ^ 4 := pow_le_pow_left₀ (abs_nonneg _) (hle i y) 4
  have hg4 : Integrable (fun y => g i y ^ 4) ν :=
    hG.mono' (hgm.pow_const 4).aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hp y)
  calc
    |Causalean.Stat.Concentration.centeredEmpiricalAverage μ x (F.f i)| ^ 4 =
        (∫ y, g i y ∂ν) ^ 4 := by
      rw [centeredAverage_eq_ghost_integral μ F n hn x i, ← abs_pow,
        abs_of_nonneg (by positivity)]
    _ ≤ ∫ y, g i y ^ 4 ∂ν := integral_fourth_jensen ν (g i) hg hg4
    _ ≤ ∫ y, ghostSup F.f x y ^ 4 ∂ν := integral_mono hg4 hG hp

/-- For two independent samples of [size n](hyp:n) drawn from μ and [any
fixed sign vector σ](hyp:σ), [the expected fourth power of the ghost
supremum equals the expected fourth power of the σ-signed ghost
supremum](goal), since swapping paired iid coordinates preserves the joint
law. -/
theorem ghost_fourth_eq_signedGhost (n : ℕ) (σ : Fin n → Bool) :
    (∫ p : (Fin n → Ω) × (Fin n → Ω), ghostSup F.f p.1 p.2 ^ 4
      ∂((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ)))) =
    ∫ p : (Fin n → Ω) × (Fin n → Ω), signedGhostSup F.f p.1 p.2 σ ^ 4
      ∂((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ))) := by
  have h := (pairedSampleSwap_measurePreserving μ σ).integral_comp'
    (fun p : (Fin n → Ω) × (Fin n → Ω) => ghostSup F.f p.1 p.2 ^ 4)
  simpa only [ghostSup_pairedSampleSwap] using h.symm

/-- For [a positive sample size n](hyp:n,hn), [the expected fourth power
of the centered supremum over an iid sample from μ is at most the expected
fourth power of the ghost supremum over two independent iid
samples](goal), with constant one. -/
theorem centered_fourth_le_ghost_integral (n : ℕ) (hn : 0 < n) :
    (∫ x, centeredSup μ F.f x ^ 4 ∂Measure.pi (fun _ : Fin n => μ)) ≤
    ∫ p : (Fin n → Ω) × (Fin n → Ω), ghostSup F.f p.1 p.2 ^ 4
      ∂((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ))) := by
  have hG := (ghostSup_legal μ F n).2.2
  rw [integral_prod _ hG]
  exact integral_mono (centeredSup_legal μ F n).2.2 hG.integral_prod_left
    (fun x => centeredSup_fourth_le_ghost μ F n hn x)

/-- For [any sample size n](hyp:n), [the expected fourth power of the
ghost supremum over two independent iid samples from μ is at most sixteen
times the expected sign-average fourth power of the signed supremum of the
class on one iid sample](goal). -/
theorem ghost_fourth_le_rademacher (n : ℕ) :
    (∫ p : (Fin n → Ω) × (Fin n → Ω), ghostSup F.f p.1 p.2 ^ 4
      ∂((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ)))) ≤
    16 * ∫ x, signAverage (fun σ => signedSup F.f x σ ^ 4)
      ∂Measure.pi (fun _ : Fin n => μ) := by
  classical
  let ν := Measure.pi (fun _ : Fin n => μ)
  have hs := signedSup_legal μ F n
  have hb (x : Fin n → Ω) (σ : Fin n → Bool) :
      BddAbove (Set.range (fun i =>
        |(n : ℝ)⁻¹ * ∑ j, (if σ j then (1 : ℝ) else -1) * F.f i (x j)|)) := by
    refine ⟨|(n : ℝ)⁻¹| * ∑ _ : Fin n, F.bound, ?_⟩
    rintro _ ⟨i, rfl⟩
    dsimp only
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro j _
    have he : |(if σ j then (1 : ℝ) else -1) * F.f i (x j)| =
        |F.f i (x j)| := by cases σ j <;> simp
    rw [he]
    exact F.bounded i (x j)
  -- Compare each normalized signed difference before taking the supremum.
  have htriangle (x y : Fin n → Ω) (σ : Fin n → Bool) :
      signedGhostSup F.f x y σ ≤ signedSup F.f x σ + signedSup F.f y σ := by
    apply ciSup_le
    intro i
    have he : (n : ℝ)⁻¹ * ∑ j,
        (if σ j then (1 : ℝ) else -1) * (F.f i (x j) - F.f i (y j)) =
        (n : ℝ)⁻¹ * ∑ j, (if σ j then (1 : ℝ) else -1) * F.f i (x j) -
        (n : ℝ)⁻¹ * ∑ j, (if σ j then (1 : ℝ) else -1) * F.f i (y j) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    rw [he]
    exact (abs_sub _ _).trans (add_le_add (le_ciSup (hb x σ) i) (le_ciSup (hb y σ) i))
  have hfourth (x y : Fin n → Ω) (σ : Fin n → Bool) :
      signedGhostSup F.f x y σ ^ 4 ≤
        8 * (signedSup F.f x σ ^ 4 + signedSup F.f y σ ^ 4) := by
    have hnonneg : 0 ≤ signedGhostSup F.f x y σ := by
      rw [← ghostSup_pairedSampleSwap F.f σ (x, y)]
      exact ((ghostSup_legal μ F n).2.1 _ _).1
    exact (pow_le_pow_left₀ hnonneg (htriangle x y σ) 4).trans
      (by convert add_pow_le (hs.2.1 x σ).1 (hs.2.1 y σ).1 4 using 1; norm_num)
  have hi (σ : Fin n → Bool) :
      Integrable (fun x : Fin n → Ω => signedSup F.f x σ ^ 4) ν := by
    apply Integrable.of_bound ((hs.1 σ).pow_const 4).aestronglyMeasurable (F.bound ^ 4)
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hs.2.1 x σ).1 4)]
    exact pow_le_pow_left₀ (hs.2.1 x σ).1 (hs.2.1 x σ).2 4
  have hfixed (σ : Fin n → Bool) :
      (∫ p : (Fin n → Ω) × (Fin n → Ω), ghostSup F.f p.1 p.2 ^ 4 ∂ν.prod ν) ≤
        16 * ∫ x, signedSup F.f x σ ^ 4 ∂ν := by
    rw [ghost_fourth_eq_signedGhost μ F n σ]
    calc
      _ ≤ ∫ p : (Fin n → Ω) × (Fin n → Ω),
          8 * (signedSup F.f p.1 σ ^ 4 + signedSup F.f p.2 σ ^ 4) ∂ν.prod ν :=
        integral_mono (signedGhostSup_legal μ F n σ).2.1
          ((((hi σ).comp_fst ν).add ((hi σ).comp_snd ν)).const_mul 8)
          (fun p => hfourth p.1 p.2 σ)
      _ = 16 * ∫ x, signedSup F.f x σ ^ 4 ∂ν := by
        rw [integral_const_mul, integral_add ((hi σ).comp_fst ν) ((hi σ).comp_snd ν),
          integral_fun_fst (fun x => signedSup F.f x σ ^ 4),
          integral_fun_snd (fun x => signedSup F.f x σ ^ 4)]
        simp only [probReal_univ, one_smul]
        ring
  -- Average the swap comparisons, then commute the finite sum with the integral.
  have havg := signAverage_mono
    (fun _ : Fin n → Bool => ∫ p : (Fin n → Ω) × (Fin n → Ω),
      ghostSup F.f p.1 p.2 ^ 4 ∂ν.prod ν)
    (fun σ => 16 * ∫ x, signedSup F.f x σ ^ 4 ∂ν) hfixed
  have hconst (c : ℝ) : signAverage (fun _ : Fin n → Bool => c) = c := by
    simp [signAverage, Fintype.card_fin, Fintype.card_bool]
  have hlin : signAverage (fun σ => 16 * ∫ x, signedSup F.f x σ ^ 4 ∂ν) =
      16 * ∫ x, signAverage (fun σ => signedSup F.f x σ ^ 4) ∂ν := by
    unfold signAverage
    rw [integral_div, integral_finsetSum _ (fun σ _ => hi σ)]
    rw [← Finset.mul_sum]
    ring
  rw [hconst, hlin] at havg
  exact havg

/-- For [a uniformly bounded measurable class](hyp:F) with a nonempty
countable index set, [a probability measure μ](hyp:μ), and [a
positive sample size n](hyp:n,hn), [the expected fourth power of the
centered supremum over an iid sample from μ is at most sixteen times the
expected sign-average fourth power of the signed supremum](goal): the
fourth-moment Rademacher symmetrization inequality. -/
theorem centered_fourth_le_rademacher (n : ℕ) (hn : 0 < n) :
    (∫ x, centeredSup μ F.f x ^ 4 ∂Measure.pi (fun _ : Fin n => μ)) ≤
    16 * ∫ x, signAverage (fun σ => signedSup F.f x σ ^ 4)
      ∂Measure.pi (fun _ : Fin n => μ) := by
  exact (centered_fourth_le_ghost_integral μ F n hn).trans
    (ghost_fourth_le_rademacher μ F n)

end Causalean.Stat.EmpiricalProcess.Countable

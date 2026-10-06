module
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Basic
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.FixedCount
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Integrability
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Mixture
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Moments
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Series

/-!
# Exact second moment for two independent finite Poisson samples

The bilinear statistic over two independent streams splits into the four
index-coincidence patterns. Separate count laws supply the two rate factors.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

namespace Causalean.Mathlib.Probability.Poisson.PairSecondMoment

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Given [two probability laws](hyp:P,Q), [their nonnegative Poisson
rates](hyp:rateA,rateB), [a measurable real kernel](hyp:K,hK), and [an
integrable kernel square](hyp:hK2), [the squared bilinear finite-Poisson sum
is integrable](goal). -/
theorem integrable_pairSum_sq
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (rateA rateB : ℝ≥0) (K : X → Y → ℝ)
    (hK : Measurable (Function.uncurry K))
    (hK2 : Integrable (fun p : X × Y => K p.1 p.2 ^ 2) (P.prod Q)) :
    Integrable (fun p : FiniteSample X × FiniteSample Y =>
      pairSum K p.1 p.2 ^ 2)
      ((finitePoissonSampleLaw P rateA).prod
        (finitePoissonSampleLaw Q rateB)) := by
  -- Use `measurable_pairSum` for the measurability part of integrability.
  -- `lintegral_pairSum_sq_lt_top` supplies finite absolute integral because
  -- a real square is nonnegative.
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_pairSum K hK).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => sq_nonneg (pairSum K p.1 p.2))).mp
  exact (lintegral_pairSum_sq_lt_top P Q rateA rateB K hK hK2).ne

private lemma summable_poisson_pair_product
    (rateA rateB : ℝ≥0) (f g : ℕ → ℝ) (c : ℝ)
    (hf : Integrable f (poissonMeasure rateA))
    (hg : Integrable g (poissonMeasure rateB)) :
    Summable (fun p : ℕ × ℕ =>
      ((poissonMeasure rateA) ({p.1} : Set ℕ)).toReal *
        ((poissonMeasure rateB) ({p.2} : Set ℕ)).toReal *
          (f p.1 * g p.2 * c)) := by
  let a (m : ℕ) : ℝ := ((poissonMeasure rateA) ({m} : Set ℕ)).toReal * f m
  let b (n : ℕ) : ℝ := ((poissonMeasure rateB) ({n} : Set ℕ)).toReal * g n
  have ha : Summable (fun m => ‖a m‖) := by
    have hdirac : Integrable f
        (Measure.sum fun m : ℕ =>
          (poissonMeasure rateA) ({m} : Set ℕ) • Measure.dirac m) := by
      simpa only [Measure.sum_smul_dirac] using hf
    simpa only [a, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg] using hdirac.summable_of_dirac
  have hb : Summable (fun n => ‖b n‖) := by
    have hdirac : Integrable g
        (Measure.sum fun n : ℕ =>
          (poissonMeasure rateB) ({n} : Set ℕ) • Measure.dirac n) := by
      simpa only [Measure.sum_smul_dirac] using hg
    simpa only [b, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg] using hdirac.summable_of_dirac
  have hab : Summable (fun p : ℕ × ℕ => a p.1 * b p.2) :=
    summable_mul_of_summable_norm ha hb
  have heq :
      (fun p : ℕ × ℕ =>
        ((poissonMeasure rateA) ({p.1} : Set ℕ)).toReal *
          ((poissonMeasure rateB) ({p.2} : Set ℕ)).toReal *
            (f p.1 * g p.2 * c)) =
        (fun p : ℕ × ℕ => a p.1 * b p.2 * c) := by
    funext p
    dsimp [a, b]
    ring
  rw [heq]
  exact hab.mul_right c

/-- Given [two probability laws](hyp:P,Q), [their nonnegative Poisson
rates](hyp:rateA,rateB), [a measurable real kernel](hyp:K,hK), and [an
integrable kernel square](hyp:hK2), [the squared bilinear finite-Poisson sum
equals its four exact index-coincidence contributions](goal). -/
theorem integral_pairSum_sq
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (rateA rateB : ℝ≥0) (K : X → Y → ℝ)
    (hK : Measurable (Function.uncurry K))
    (hK2 : Integrable (fun p : X × Y => K p.1 p.2 ^ 2) (P.prod Q)) :
    (∫ p : FiniteSample X × FiniteSample Y,
      pairSum K p.1 p.2 ^ 2
      ∂((finitePoissonSampleLaw P rateA).prod
        (finitePoissonSampleLaw Q rateB))) =
      (rateA : ℝ) * (rateB : ℝ) *
        (∫ x, ∫ y, K x y * K x y ∂Q ∂P) +
      (rateA : ℝ) * (rateB : ℝ) ^ 2 *
        (∫ x, ∫ y, ∫ y', K x y * K x y' ∂Q ∂Q ∂P) +
      (rateA : ℝ) ^ 2 * (rateB : ℝ) *
        (∫ x, ∫ x', ∫ y, K x y * K x' y ∂Q ∂P ∂P) +
      (rateA : ℝ) ^ 2 * (rateB : ℝ) ^ 2 *
        (∫ x, ∫ x', ∫ y, ∫ y', K x y * K x' y' ∂Q ∂Q ∂P ∂P) := by
  let f (m : ℕ) : ℝ := m
  let g (m : ℕ) : ℝ := (m : ℝ) * ((m : ℝ) - 1)
  let c₀ : ℝ := ∫ x, ∫ y, K x y * K x y ∂Q ∂P
  let c₁ : ℝ := ∫ x, ∫ y, ∫ y', K x y * K x y' ∂Q ∂Q ∂P
  let c₂ : ℝ := ∫ x, ∫ x', ∫ y, K x y * K x' y ∂Q ∂P ∂P
  let c₃ : ℝ := ∫ x, ∫ x', ∫ y, ∫ y', K x y * K x' y' ∂Q ∂Q ∂P ∂P
  let wA (m : ℕ) : ℝ := ((poissonMeasure rateA) ({m} : Set ℕ)).toReal
  let wB (n : ℕ) : ℝ := ((poissonMeasure rateB) ({n} : Set ℕ)).toReal
  let term (u v : ℕ → ℝ) (c : ℝ) (p : ℕ × ℕ) : ℝ :=
    wA p.1 * wB p.2 * (u p.1 * v p.2 * c)
  have hfA : Integrable f (poissonMeasure rateA) :=
    (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two rateA).integrable
      (by norm_num)
  have hfB : Integrable f (poissonMeasure rateB) :=
    (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two rateB).integrable
      (by norm_num)
  have hgA : Integrable g (poissonMeasure rateA) :=
    integrable_poisson_ordered_pairs rateA
  have hgB : Integrable g (poissonMeasure rateB) :=
    integrable_poisson_ordered_pairs rateB
  have h₀ : Summable (term f f c₀) :=
    summable_poisson_pair_product rateA rateB f f c₀ hfA hfB
  have h₁ : Summable (term f g c₁) :=
    summable_poisson_pair_product rateA rateB f g c₁ hfA hgB
  have h₂ : Summable (term g f c₂) :=
    summable_poisson_pair_product rateA rateB g f c₂ hgA hfB
  have h₃ : Summable (term g g c₃) :=
    summable_poisson_pair_product rateA rateB g g c₃ hgA hgB
  rw [integral_pair_count_mixture P Q rateA rateB _
    (integrable_pairSum_sq P Q rateA rateB K hK hK2)]
  have hfixed (m n : ℕ) :
      (∫ p : (Fin m → X) × (Fin n → Y),
        pairSum K ⟨m, p.1⟩ ⟨n, p.2⟩ ^ 2
        ∂((Measure.pi fun _ : Fin m => P).prod
          (Measure.pi fun _ : Fin n => Q))) =
        f m * f n * c₀ + f m * g n * c₁ +
          g m * f n * c₂ + g m * g n * c₃ := by
    simpa only [pairSum, f, g, c₀, c₁, c₂, c₃] using
      integral_fixedCount_pairSum_sq P Q K m n hK hK2
  simp_rw [hfixed]
  have hsum : Summable (fun p => term f f c₀ p + term f g c₁ p +
      term g f c₂ p + term g g c₃ p) :=
    ((h₀.add h₁).add h₂).add h₃
  calc
    (∑' m : ℕ, ∑' n : ℕ,
      wA m * wB n *
        (f m * f n * c₀ + f m * g n * c₁ +
          g m * f n * c₂ + g m * g n * c₃)) =
        ∑' p : ℕ × ℕ,
          (term f f c₀ p + term f g c₁ p +
            term g f c₂ p + term g g c₃ p) := by
      rw [hsum.tsum_prod]
      congr 1
      funext m
      congr 1
      funext n
      dsimp [term]
      ring
    _ = (∑' p : ℕ × ℕ, term f f c₀ p) +
        (∑' p : ℕ × ℕ, term f g c₁ p) +
        (∑' p : ℕ × ℕ, term g f c₂ p) +
        (∑' p : ℕ × ℕ, term g g c₃ p) := by
      rw [(h₀.add h₁).add h₂ |>.tsum_add h₃,
        (h₀.add h₁).tsum_add h₂, h₀.tsum_add h₁]
    _ = _ := by
      have hfactor (u v : ℕ → ℝ) (c : ℝ)
          (hu : Integrable u (poissonMeasure rateA))
          (hv : Integrable v (poissonMeasure rateB))
          (_hs : Summable (term u v c)) :
          (∑' p : ℕ × ℕ, term u v c p) =
            (∫ m : ℕ, u m ∂poissonMeasure rateA) *
              (∫ n : ℕ, v n ∂poissonMeasure rateB) * c := by
        have hsbase := summable_poisson_pair_product rateA rateB u v 1 hu hv
        have h := poisson_pair_weighted_tsum_mul rateA rateB u v hu hv
        calc
          _ = (∑' p : ℕ × ℕ, term u v 1 p) * c := by
            rw [← hsbase.tsum_mul_right c]
            congr 1
            funext p
            dsimp [term]
            ring
          _ = (∑' m : ℕ, ∑' n : ℕ,
              wA m * wB n * (u m * v n)) * c := by
            rw [hsbase.tsum_prod]
            simp only [wA, wB, mul_one]
          _ = _ := by simpa only [wA, wB] using congrArg (· * c) h
      rw [hfactor f f c₀ hfA hfB h₀,
        hfactor f g c₁ hfA hgB h₁,
        hfactor g f c₂ hgA hfB h₂,
        hfactor g g c₃ hgA hgB h₃]
      simp only [f, g, c₀, c₁, c₂, c₃,
        poisson_count_first_moment, poisson_ordered_pairs_second_moment]

end Causalean.Mathlib.Probability.Poisson.PairSecondMoment

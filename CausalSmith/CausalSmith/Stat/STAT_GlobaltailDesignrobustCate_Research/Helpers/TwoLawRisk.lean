module
public import Causalean.Stat.Minimax.LeCam
public import Causalean.Stat.Minimax.Pinsker
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # Two-law expected metric risk bound -/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory InformationTheory
open scoped ENNReal

-- @node: lem:two-law-metric-risk
/-- Expected metric loss under at least one of two laws is bounded below by
separation and the finite Kullback–Leibler divergence. -/
lemma two_law_metric_risk {Ω Θ : Type} [MeasurableSpace Ω] [MetricSpace Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    (Q₀ Q₁ : Measure Ω) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁]
    (θ₀ θ₁ : Θ) (T : {T : Ω → Θ // Measurable T})
    (hΔ : 0 < dist θ₀ θ₁) (hKL : klDiv Q₀ Q₁ ≠ ⊤) :
    ENNReal.ofReal ((dist θ₀ θ₁ / 4) *
      (1 - Real.sqrt ((klDiv Q₀ Q₁).toReal))) ≤
      max (∫⁻ ω, ENNReal.ofReal (dist (T.1 ω) θ₀) ∂Q₀)
        (∫⁻ ω, ENNReal.ofReal (dist (T.1 ω) θ₁) ∂Q₁) := by
  let Δ := dist θ₀ θ₁
  let s := Δ / 2
  let K := (klDiv Q₀ Q₁).toReal
  have hac : Q₀ ≪ Q₁ := (klDiv_ne_top_iff.mp hKL).1
  have hsep : 2 * s ≤ dist θ₀ θ₁ := by dsimp [s, Δ]; linarith
  have hprob := Causalean.Stat.klForm_two_point_lower_bound hac hKL T.2 hsep
  have hKnonneg : 0 ≤ K := ENNReal.toReal_nonneg
  have hsnonneg : 0 ≤ s := by dsimp [s, Δ]; positivity
  have hsqrtle : Real.sqrt (K / 2) ≤ Real.sqrt K :=
    Real.sqrt_le_sqrt (by dsimp [K]; nlinarith)
  have hprobWeak : (1 - Real.sqrt K) / 2 ≤
      max (Q₀.real {ω | s ≤ dist (T.1 ω) θ₀})
        (Q₁.real {ω | s ≤ dist (T.1 ω) θ₁}) := by
    exact (by nlinarith : (1 - Real.sqrt K) / 2 ≤
      (1 - Real.sqrt (K / 2)) / 2).trans hprob
  have hevent (Q : Measure Ω) [IsProbabilityMeasure Q] (θ : Θ) :
      ENNReal.ofReal s * Q {ω | s ≤ dist (T.1 ω) θ} ≤
        ∫⁻ ω, ENNReal.ofReal (dist (T.1 ω) θ) ∂Q := by
    have hset : MeasurableSet {ω : Ω | s ≤ dist (T.1 ω) θ} :=
      Causalean.Stat.measurableSet_error T.2 θ s
    calc
      ENNReal.ofReal s * Q {ω | s ≤ dist (T.1 ω) θ} =
          ∫⁻ _ω in {ω | s ≤ dist (T.1 ω) θ}, ENNReal.ofReal s ∂Q :=
        (setLIntegral_const _ _).symm
      _ = ∫⁻ ω, {ω | s ≤ dist (T.1 ω) θ}.indicator
          (fun _ => ENNReal.ofReal s) ω ∂Q := (lintegral_indicator hset _).symm
      _ ≤ ∫⁻ ω, ENNReal.ofReal (dist (T.1 ω) θ) ∂Q := by
        apply lintegral_mono
        intro ω
        by_cases hω : s ≤ dist (T.1 ω) θ
        · rw [Set.indicator_of_mem (show ω ∈ {ω | s ≤ dist (T.1 ω) θ} from hω)]
          exact ENNReal.ofReal_le_ofReal hω
        · rw [Set.indicator_of_notMem (show ω ∉ {ω | s ≤ dist (T.1 ω) θ} from hω)]
          exact bot_le
  have hmax : ENNReal.ofReal s *
      max (Q₀ {ω | s ≤ dist (T.1 ω) θ₀})
        (Q₁ {ω | s ≤ dist (T.1 ω) θ₁}) ≤
      max (∫⁻ ω, ENNReal.ofReal (dist (T.1 ω) θ₀) ∂Q₀)
        (∫⁻ ω, ENNReal.ofReal (dist (T.1 ω) θ₁) ∂Q₁) := by
    rw [mul_max]
    exact max_le_max (hevent Q₀ θ₀) (hevent Q₁ θ₁)
  have hprobEN : ENNReal.ofReal ((1 - Real.sqrt K) / 2) ≤
      max (Q₀ {ω | s ≤ dist (T.1 ω) θ₀})
        (Q₁ {ω | s ≤ dist (T.1 ω) θ₁}) := by
    have h := ENNReal.ofReal_le_ofReal hprobWeak
    simpa [ENNReal.ofReal_max, Measure.real] using h
  calc
    ENNReal.ofReal ((Δ / 4) * (1 - Real.sqrt K)) =
        ENNReal.ofReal s * ENNReal.ofReal ((1 - Real.sqrt K) / 2) := by
      rw [← ENNReal.ofReal_mul hsnonneg]
      congr 1
      dsimp [s]
      ring
    _ ≤ ENNReal.ofReal s *
        max (Q₀ {ω | s ≤ dist (T.1 ω) θ₀})
          (Q₁ {ω | s ≤ dist (T.1 ω) θ₁}) := by gcongr
    _ ≤ _ := hmax

end CausalSmith.Stat.GlobalTailDesignRobustCate

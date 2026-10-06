module
public import Causalean.PO.Bridge.FiniteCellTwoDraw
public import Causalean.Stat.UStatistic.LocalizedVariance.Mean


/-!
# Mean of an unordered order-two U-statistic

For a measurable integrable symmetric pair kernel, each distinct finite-product
coordinate pair has the independent two-draw expectation. Averaging over
unordered pairs preserves that mean. The observed finite-cell law can be used
as the common marginal, including for localized arm kernels.
-/

public section

open MeasureTheory ProbabilityTheory
open Causalean.PO.Bridge
open Causalean.Stat.UStatistic.LocalizedVariance

namespace Causalean.PO.Bridge


variable {Ω γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (D : FiniteCellData Ω γ μ)

/-- A [finite-cell observed table](hyp:D), [sample size](hyp:n) with [at least
two observations](hyp:hn), [treatment arm](hyp:d), and [symmetric measurable
integrable covariate-pair weight](hyp:W,hSym,hW,hInt) give [the localized
treatment-cell U-statistic mean through finite-cell treatment probabilities](goal). -/
theorem integral_uStatistic_arm (n : ℕ) (hn : 2 ≤ n) (d : Bool)
    (W : γ → γ → ℝ) (hSym : ∀ x y, W x y = W y x)
    (hW : Measurable fun p : γ × γ => W p.1 p.2)
    (hInt : Integrable (fun p : γ × γ => W p.1 p.2)
      ((μ.map D.X).prod (μ.map D.X))) :
    ∫ ω, uStatistic n
        (fun z z' : γ × Bool × Bool =>
          W z.1 z'.1 * armIndicator d z.2.1 * armIndicator d z'.2.1)
        ω ∂iidLaw D.observedLaw n =
      ∫ p : γ × γ,
        W p.1 p.2 * D.armProb d p.1 * D.armProb d p.2
          ∂((μ.map D.X).prod (μ.map D.X)) := by
  letI : IsProbabilityMeasure D.observedLaw := observedLaw_isProbability D
  let H : (γ × Bool × Bool) → (γ × Bool × Bool) → ℝ :=
    fun z z' => W z.1 z'.1 * armIndicator d z.2.1 * armIndicator d z'.2.1
  have hSymH : ∀ z z', H z z' = H z' z := by
    intro z z'
    dsimp [H]
    rw [hSym]
    ring
  have hA : Measurable (fun z : γ × Bool × Bool => armIndicator d z.2.1) := by
    unfold armIndicator
    exact Measurable.ite
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
      measurable_const measurable_const
  have hH : Measurable (fun p : (γ × Bool × Bool) × (γ × Bool × Bool) =>
      H p.1 p.2) := by
    dsimp [H]
    exact (hW.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd))).mul
        (hA.comp measurable_fst) |>.mul (hA.comp measurable_snd)
  have hAb (z : γ × Bool × Bool) : ‖armIndicator d z.2.1‖ ≤ 1 := by
    simp only [armIndicator]
    split_ifs <;> simp
  have hbase : Integrable (fun p : (γ × Bool × Bool) × (γ × Bool × Bool) =>
      W p.1.1 p.2.1) (D.observedLaw.prod D.observedLaw) := by
    rw [← pair_covariate_map D] at hInt
    exact (integrable_map_measure hW.aestronglyMeasurable
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd)).aemeasurable).1 hInt
  have hIntH : Integrable (fun p : (γ × Bool × Bool) × (γ × Bool × Bool) =>
      H p.1 p.2) (D.observedLaw.prod D.observedLaw) := by
    have h₁ := hbase.mul_bdd (hA.comp measurable_fst).aestronglyMeasurable
      (ae_of_all _ fun p => hAb p.1)
    exact h₁.mul_bdd (hA.comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ fun p => hAb p.2)
  calc
    _ = ∫ p : (γ × Bool × Bool) × (γ × Bool × Bool),
        H p.1 p.2 ∂(D.observedLaw.prod D.observedLaw) :=
      integral_uStatistic_eq_pair D.observedLaw n hn H hSymH hH hIntH
    _ = _ := integral_pair_arm D d d W hW hInt

end Causalean.PO.Bridge

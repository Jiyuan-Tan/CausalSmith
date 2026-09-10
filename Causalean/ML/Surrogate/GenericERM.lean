/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Proper binary losses and population risk

This file defines `ProperBinaryLoss` and `StrictProperBinaryLoss` for losses
`L q b`, where `q` is a predicted probability and `b` is a binary label.  A
proper loss is minimized pointwise at the true probability `η`; a strictly proper
loss has `η` as its unique `[0,1]` minimizer.

The theorem `properLoss_population_risk_le` integrates the pointwise proper-loss
inequality, showing that predicting `η` has no larger conditional-risk integral
than any measurable `[0,1]`-valued comparator.  The theorem
`properLoss_population_minimizer_recovers_eta` proves the corresponding
identification statement for strictly proper losses: any population minimizer
equals the true conditional probability almost everywhere.
-/

namespace Causalean.ML

open MeasureTheory

/-- For [a real-valued loss of a predicted probability and a binary outcome](hyp:L), the [property of being a proper binary loss](goal) means that, for every true probability $\eta$ in $[0,1]$ and every candidate probability $q$ in $[0,1]$, the conditional expected loss at $\eta$ is no greater than that at $q$: $\eta L(\eta,1)+(1-\eta)L(\eta,0) \le \eta L(q,1)+(1-\eta)L(q,0)$.

Equivalently, the conditional expected loss is minimized over $[0,1]$ by reporting the true probability. -/
def ProperBinaryLoss (L : ℝ → Bool → ℝ) : Prop :=
  ∀ η ∈ Set.Icc (0 : ℝ) 1,
    IsMinOn (fun q => η * L q true + (1 - η) * L q false) (Set.Icc (0 : ℝ) 1) η

/-- For [a real-valued loss of a predicted probability and a binary outcome](hyp:L), the [property of being a strictly proper binary loss](goal) means both that [the loss is proper](step:1) and that, for every true probability $\eta$ and every candidate probability $q$ in $[0,1]$, [equality between their conditional expected losses implies $q=\eta$](step:2).

Thus truthful reporting is the unique minimizer of conditional expected loss on the unit interval. -/
def StrictProperBinaryLoss (L : ℝ → Bool → ℝ) : Prop :=
  ProperBinaryLoss L ∧
    ∀ η ∈ Set.Icc (0 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      η * L q true + (1 - η) * L q false =
        η * L η true + (1 - η) * L η false → q = η

variable {X : Type*} [MeasurableSpace X]

/-- **Proper-loss integrated risk inequality.** For a proper binary loss, the
integral of the conditional risk obtained by predicting the true conditional
probability is no larger than the corresponding integral for any pointwise
`[0,1]`-valued comparator.  The hypotheses keep both conditional-risk integrands
integrable. -/
theorem properLoss_population_risk_le
    {L : ℝ → Bool → ℝ} (hproper : ProperBinaryLoss L)
    {PX : Measure X} (η : X → ℝ) (hη : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (q : X → ℝ) (hq : ∀ x, q x ∈ Set.Icc (0 : ℝ) 1)
    (hint_η : Integrable (fun x => η x * L (η x) true + (1 - η x) * L (η x) false) PX)
    (hint_q : Integrable (fun x => η x * L (q x) true + (1 - η x) * L (q x) false) PX) :
    ∫ x, (η x * L (η x) true + (1 - η x) * L (η x) false) ∂PX
      ≤ ∫ x, (η x * L (q x) true + (1 - η x) * L (q x) false) ∂PX := by
  exact integral_mono hint_η hint_q (fun x => by
    exact (hproper (η x) (hη x)) (hq x))

/-- **Strictly proper population minimizers recover the regression function.** For [a strictly
proper binary loss `L`](hyp:hstrict) on a measure space `PX`, with [the true conditional
probability `η` taking values in `[0,1]`](hyp:hη) and [a candidate prediction rule `q` also
taking values in `[0,1]`](hyp:hq), if [`q` minimizes the population conditional risk over every
`[0,1]`-valued prediction rule](hyp:hmin) and [the conditional risks of `η` and `q` are both
integrable](hyp:hint_η,hint_q), then [`q` equals `η` almost everywhere](goal). -/
theorem properLoss_population_minimizer_recovers_eta
    {L : ℝ → Bool → ℝ} (hstrict : StrictProperBinaryLoss L)
    {PX : Measure X} (η : X → ℝ) (hη : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (q : X → ℝ) (hq : ∀ x, q x ∈ Set.Icc (0 : ℝ) 1)
    (hmin :
      IsMinOn
        (fun r : X → ℝ =>
          ∫ x, (η x * L (r x) true + (1 - η x) * L (r x) false) ∂PX)
        {r : X → ℝ | ∀ x, r x ∈ Set.Icc (0 : ℝ) 1} q)
    (hint_η : Integrable (fun x => η x * L (η x) true + (1 - η x) * L (η x) false) PX)
    (hint_q : Integrable (fun x => η x * L (q x) true + (1 - η x) * L (q x) false) PX) :
    q =ᵐ[PX] η := by
  have hη_le_q :
      ∫ x, (η x * L (η x) true + (1 - η x) * L (η x) false) ∂PX
        ≤ ∫ x, (η x * L (q x) true + (1 - η x) * L (q x) false) ∂PX :=
    properLoss_population_risk_le hstrict.1 η hη q hq hint_η hint_q
  have hq_le_η :
      ∫ x, (η x * L (q x) true + (1 - η x) * L (q x) false) ∂PX
        ≤ ∫ x, (η x * L (η x) true + (1 - η x) * L (η x) false) ∂PX :=
    (isMinOn_iff.mp hmin) η hη
  have hintegral_eq :
      ∫ x, (η x * L (η x) true + (1 - η x) * L (η x) false) ∂PX
        = ∫ x, (η x * L (q x) true + (1 - η x) * L (q x) false) ∂PX :=
    le_antisymm hη_le_q hq_le_η
  have hrisk_le :
      (fun x => η x * L (η x) true + (1 - η x) * L (η x) false)
        ≤ᵐ[PX] fun x => η x * L (q x) true + (1 - η x) * L (q x) false :=
    Filter.Eventually.of_forall fun x => (hstrict.1 (η x) (hη x)) (hq x)
  have hrisk_eq :
      (fun x => η x * L (η x) true + (1 - η x) * L (η x) false)
        =ᵐ[PX] fun x => η x * L (q x) true + (1 - η x) * L (q x) false :=
    (integral_eq_iff_of_ae_le hint_η hint_q hrisk_le).1 hintegral_eq
  exact hrisk_eq.mono fun x hx => by
    exact hstrict.2 (η x) (hη x) (q x) (hq x) hx.symm

end Causalean.ML

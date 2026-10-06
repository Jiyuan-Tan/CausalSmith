/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.ML.Core
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

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

Gneiting--Raftery (2007), equation (1), uses the opposite convention of scores that
are maximized; the definitions here reorient those scores as losses to minimize.
Proper and strictly proper binary losses follow Reid--Williamson (2010), Section 3.1.
Log loss requires the conditional probability to lie in the open interval `(0,1)` when finite
real-valued risk, rather than an extended endpoint convention, is needed.
-/

@[expose] public section

namespace Causalean.ML

open MeasureTheory

/-- [A proper binary loss](goal) makes truthful probability reports optimal:
[truth weakly minimizes conditional risk on the unit interval](step:1). The criterion applies
to [a real-valued binary probability loss](hyp:L).

Equivalently, the conditional expected loss is minimized over `[0,1]` by reporting the true
probability. -/
def ProperBinaryLoss (L : ℝ → Bool → ℝ) : Prop :=
  ∀ η ∈ Set.Icc (0 : ℝ) 1,
    IsMinOn (fun q => η * L q true + (1 - η) * L q false) (Set.Icc (0 : ℝ) 1) η

/-- [A strictly proper binary loss](goal) makes truthful probability reporting uniquely optimal:
[the loss is proper](step:1), and [equal conditional risk forces truth](step:2). It applies to
[a real-valued binary probability loss](hyp:L).

Thus truthful reporting is the unique minimizer of conditional expected loss on the unit
interval. -/
def StrictProperBinaryLoss (L : ℝ → Bool → ℝ) : Prop :=
  ProperBinaryLoss L ∧
    ∀ η ∈ Set.Icc (0 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      η * L q true + (1 - η) * L q false =
        η * L η true + (1 - η) * L η false → q = η

variable {X : Type*} [MeasurableSpace X]

/-- **Proper-loss integrated risk inequality.** For [a proper binary loss](hyp:hproper) under
[a population law](hyp:PX), let [the true conditional probability](hyp:η) and [a
comparator](hyp:q) be [`[0,1]`-valued almost everywhere](hyp:hη,hq), with [integrable truthful
and comparator conditional risks](hyp:hint_η,hint_q). Then [truthful prediction has no larger
integrated risk than the comparator](goal). -/
theorem properLoss_population_risk_le
    {L : ℝ → Bool → ℝ} (hproper : ProperBinaryLoss L)
    {PX : Measure X} (η : X → ℝ) (hη : ∀ᵐ x ∂PX, η x ∈ Set.Icc (0 : ℝ) 1)
    (q : X → ℝ) (hq : ∀ᵐ x ∂PX, q x ∈ Set.Icc (0 : ℝ) 1)
    (hint_η : Integrable (fun x => η x * L (η x) true + (1 - η x) * L (η x) false) PX)
    (hint_q : Integrable (fun x => η x * L (q x) true + (1 - η x) * L (q x) false) PX) :
    ∫ x, (η x * L (η x) true + (1 - η x) * L (η x) false) ∂PX
      ≤ ∫ x, (η x * L (q x) true + (1 - η x) * L (q x) false) ∂PX := by
  exact integral_mono_ae hint_η hint_q <| by
    filter_upwards [hη, hq] with x hηx hqx
    exact (hproper (η x) hηx) hqx

/-- **Strictly proper population minimizers recover the regression function.** For [a strictly
proper binary loss](hyp:hstrict) under [a population law](hyp:PX), suppose [the true conditional
probability](hyp:η) is [measurable](hyp:hη_meas), [`[0,1]`-valued almost everywhere](hyp:hη), and
has [integrable conditional risk](hyp:hint_η), while [the candidate](hyp:q) is
[measurable](hyp:hq_meas), [`[0,1]`-valued almost everywhere](hyp:hq), and has [integrable
risk](hyp:hint_q). If [the candidate minimizes over admissible competitors](hyp:hmin), then [it
equals the truth almost everywhere](goal). -/
theorem properLoss_population_minimizer_recovers_eta
    {L : ℝ → Bool → ℝ} (hstrict : StrictProperBinaryLoss L)
    {PX : Measure X} (η : X → ℝ) (hη_meas : Measurable η)
    (hη : ∀ᵐ x ∂PX, η x ∈ Set.Icc (0 : ℝ) 1)
    (q : X → ℝ) (hq_meas : Measurable q)
    (hq : ∀ᵐ x ∂PX, q x ∈ Set.Icc (0 : ℝ) 1)
    (hint_q : Integrable
      (fun x => η x * L (q x) true + (1 - η x) * L (q x) false) PX)
    (hmin :
      IsMinOn
        (fun r : X → ℝ =>
          ∫ x, (η x * L (r x) true + (1 - η x) * L (r x) false) ∂PX)
        {r : X → ℝ |
          Measurable r ∧
          (∀ᵐ x ∂PX, r x ∈ Set.Icc (0 : ℝ) 1) ∧
          Integrable
            (fun x => η x * L (r x) true + (1 - η x) * L (r x) false) PX} q)
    (hint_η : Integrable (fun x => η x * L (η x) true + (1 - η x) * L (η x) false) PX) :
    q =ᵐ[PX] η := by
  have hq_admissible : q ∈ {r : X → ℝ |
      Measurable r ∧
      (∀ᵐ x ∂PX, r x ∈ Set.Icc (0 : ℝ) 1) ∧
      Integrable
        (fun x => η x * L (r x) true + (1 - η x) * L (r x) false) PX} :=
    ⟨hq_meas, hq, hint_q⟩
  have hη_le_q :
      ∫ x, (η x * L (η x) true + (1 - η x) * L (η x) false) ∂PX
        ≤ ∫ x, (η x * L (q x) true + (1 - η x) * L (q x) false) ∂PX :=
    properLoss_population_risk_le hstrict.1 η hη q hq_admissible.2.1
      hint_η hq_admissible.2.2
  have hq_le_η :
      ∫ x, (η x * L (q x) true + (1 - η x) * L (q x) false) ∂PX
        ≤ ∫ x, (η x * L (η x) true + (1 - η x) * L (η x) false) ∂PX :=
    (isMinOn_iff.mp hmin) η ⟨hη_meas, hη, hint_η⟩
  have hintegral_eq :
      ∫ x, (η x * L (η x) true + (1 - η x) * L (η x) false) ∂PX
        = ∫ x, (η x * L (q x) true + (1 - η x) * L (q x) false) ∂PX :=
    le_antisymm hη_le_q hq_le_η
  have hrisk_le :
      (fun x => η x * L (η x) true + (1 - η x) * L (η x) false)
        ≤ᵐ[PX] fun x => η x * L (q x) true + (1 - η x) * L (q x) false := by
    filter_upwards [hη, hq] with x hηx hqx
    exact (hstrict.1 (η x) hηx) hqx
  have hrisk_eq :
      (fun x => η x * L (η x) true + (1 - η x) * L (η x) false)
        =ᵐ[PX] fun x => η x * L (q x) true + (1 - η x) * L (q x) false :=
    (integral_eq_iff_of_ae_le hint_η hint_q hrisk_le).1 hintegral_eq
  filter_upwards [hrisk_eq, hη, hq] with x hx hηx hqx
  exact hstrict.2 (η x) hηx (q x) hqx hx.symm

end Causalean.ML

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.Risk

/-!
# Generic finite-population variance quantities for two-arm designs

This module contains the paper-independent finite-population arm variances, unit-effect variance,
and observed separate-arm variance estimator used by Neyman's complete-randomization formula.
They live in the design-based layer so interference models can import them without reversing the
library's dependency direction.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

section Group

variable {n : ℕ}

/-- For [a population of `n` units](hyp:n) and [a unit](hyp:j), the [treatment indicator](goal)
is one when the Boolean assignment treats that unit and zero otherwise. -/
noncomputable def T (j : Fin n) : (Fin n → Bool) → ℝ :=
  FiniteDesign.ind (fun w => w j = true)

/-- For [a population of `n` units](hyp:n) and [a real quantity for every unit](hyp:x), the
[finite-population mean](goal) is the unit sum divided by `n`. -/
noncomputable def popMeanV (x : Fin n → ℝ) : ℝ := (∑ j, x j) / n

/-- For [a population of `n` units](hyp:n) and [treated potential outcomes](hyp:a), the
[treated finite-population sample variance](goal) uses denominator `n-1`. -/
noncomputable def S1 (a : Fin n → ℝ) : ℝ :=
  (∑ j, (a j - popMeanV a) ^ 2) / (n - 1 : ℝ)

/-- For [a population of `n` units](hyp:n) and [control potential outcomes](hyp:b), the
[control finite-population sample variance](goal) uses denominator `n-1`. -/
noncomputable def S0 (b : Fin n → ℝ) : ℝ :=
  (∑ j, (b j - popMeanV b) ^ 2) / (n - 1 : ℝ)

/-- For [a population of `n` units](hyp:n), [treated potential outcomes](hyp:a), and [control
potential outcomes](hyp:b), the [finite-population sample variance of unit treatment
effects](goal) uses denominator `n-1`. -/
noncomputable def Stau (a b : Fin n → ℝ) : ℝ :=
  (∑ j, ((a j - b j) - (popMeanV a - popMeanV b)) ^ 2) / (n - 1 : ℝ)

variable (K : ℕ) (a b : Fin n → ℝ)

/-- For [a treated count](hyp:K), [treated outcomes](hyp:a), and [a Boolean assignment](hyp:w),
the [observed treated-arm mean](goal) averages treated outcomes over the treated count. -/
noncomputable def obsMeanTreated (w : Fin n → Bool) : ℝ :=
  (∑ j, T j w * a j) / K

/-- For [a treated count](hyp:K), [control outcomes](hyp:b), and [a Boolean assignment](hyp:w),
the [observed control-arm mean](goal) averages control outcomes over the control count. -/
noncomputable def obsMeanControl (w : Fin n → Bool) : ℝ :=
  (∑ j, (1 - T j w) * b j) / (n - K : ℝ)

/-- For [a treated count](hyp:K), [treated outcomes](hyp:a), and [a Boolean assignment](hyp:w),
the [observed treated-arm sample variance](goal) uses denominator `K-1`. -/
noncomputable def ShatTreated (w : Fin n → Bool) : ℝ :=
  (∑ j, T j w * (a j - obsMeanTreated K a w) ^ 2) / (K - 1 : ℝ)

/-- For [a treated count](hyp:K), [control outcomes](hyp:b), and [a Boolean assignment](hyp:w),
the [observed control-arm sample variance](goal) uses denominator `n-K-1`. -/
noncomputable def ShatControl (w : Fin n → Bool) : ℝ :=
  (∑ j, (1 - T j w) * (b j - obsMeanControl K b w) ^ 2) / (n - K - 1 : ℝ)

/-- For [a treated count](hyp:K), [treated and control outcomes](hyp:a,b), and [a Boolean
assignment](hyp:w), the [usual conservative variance estimator](goal) is the sum of the observed
arm sample variances divided by their arm sizes. -/
noncomputable def varHat (w : Fin n → Bool) : ℝ :=
  ShatTreated K a w / K + ShatControl K b w / (n - K : ℝ)

end Group

end DesignBased
end Experimentation
end Causalean

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Mathlib.Probability.Kernel.BernoulliMark
public import Causalean.Mathlib.Probability.Kernel.CompProdAssembly
public import Causalean.Mathlib.Probability.Kernel.CondDistrib
public import Causalean.Mathlib.Probability.Kernel.CondDistribWitness
public import Causalean.Mathlib.Probability.Kernel.GraphMapProd
public import Causalean.Mathlib.Probability.Kernel.ParameterizedKernelQuantileRealization
public import Causalean.Mathlib.Probability.Kernel.ProductCondDistrib
public import Causalean.Mathlib.Probability.Kernel.TwoStateMarkov

/-!
Probability-kernel constructions for conditional distributions, product composition, graph-based
maps, Bernoulli marks, and quantile realizations. These tools build and compare stochastic
mechanisms with explicit conditioning structure.
-/

public section

namespace Causalean.Mathlib.Probability

/-- For [measurable spaces](hyp:α,β), [a Markov kernel `κ`](hyp:κ), and
[a source point `a`](hyp:a), [the kernel slice has total mass one](goal). -/
theorem kernel_apply_univ {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : ProbabilityTheory.Kernel α β) [ProbabilityTheory.IsMarkovKernel κ] (a : α) :
    κ a Set.univ = 1 :=
  MeasureTheory.measure_univ

end Causalean.Mathlib.Probability

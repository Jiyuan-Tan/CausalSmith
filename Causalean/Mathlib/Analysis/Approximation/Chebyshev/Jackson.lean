/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.AffineFour
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CoefficientEnvelopeFour
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Center
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.CenterMass
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Coefficients
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Derivative
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Fourier
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.FourierBridge
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Localization
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Reciprocal
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Support
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.TorusGeometry
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Variation
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Kernel
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Tensor
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TensorExtraction
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TrigExtraction

/-!
Jackson-style approximation bounds assembled from Chebyshev kernels, tensor constructions, coefficient envelopes, and extraction lemmas. Use these results to bound approximation error by smoothness.
-/

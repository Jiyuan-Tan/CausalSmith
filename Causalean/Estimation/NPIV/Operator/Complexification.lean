/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Operator.Complexification_Part2
/-! # Real functional calculus by complexification

This facade exports the real-to-complex `L²` maps, the complex lift of a real
continuous linear operator, and the real functional calculus obtained by
applying complex CFC and restricting back to the real subspace.  The NPIV
spectral layer uses this compatibility API for the real normal operator
`T†T`; the declarations themselves are generic measured-space operator facts.
-/

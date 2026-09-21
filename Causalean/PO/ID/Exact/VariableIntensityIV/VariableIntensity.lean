/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Variable-intensity instrumental variables

A directed-pair Wald specialization of the Angrist--Imbens causal-response
algebra for finite ordered treatment intensities: one directed instrument
contrast identifies an average causal response over the treatment-intensity
margins crossed by that contrast. The exported 2SLS objects remain interfaces;
this barrel does not claim the paper's general population 2SLS theorem.
-/

module
public import Causalean.PO.ID.Exact.VariableIntensityIV.VariableIntensity.Basic
public import Causalean.PO.ID.Exact.VariableIntensityIV.VariableIntensity.Identification
public import Causalean.PO.ID.Exact.VariableIntensityIV.VariableIntensity.SpecialCases

/-! # Variable-Intensity Instrumental Variables

This barrel exports the ordered-treatment potential-outcome setup, the
directed-pair Wald identification theorem, and its binary-treatment,
constant-response, and population-score specializations. -/

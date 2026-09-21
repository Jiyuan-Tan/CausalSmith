/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Primal.RateSequence

/-! # Fixed-sample TRAE primal rate

This public facade exports the NPIV Tikhonov rate at one sample-size index and
one confidence level, with a sample-size-dependent regularization sequence.
The fixed-confidence construction avoids a countable union bound over sample
sizes, and the bias certificate uses one constant uniformly over every
positive regularization level.
-/

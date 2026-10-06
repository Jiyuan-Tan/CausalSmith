/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.MomentProblems.AtomicLaw
public import Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.Attainment
public import Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.Bounds
public import Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.Defs
public import Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.Envelope
public import Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope.QuarticRoot
public import Causalean.Stat.MomentProblems.Cumulant
public import Causalean.Stat.MomentProblems.GaussianPerturbation
public import Causalean.Stat.MomentProblems.MomentCumulantInversion
public import Causalean.Stat.MomentProblems.RawMoment
public import Causalean.Stat.MomentProblems.ResidualQuadratic
public import Causalean.Stat.MomentProblems.ScoreProgram
public import Causalean.Stat.MomentProblems.SymmetricAtomSolve
public import Causalean.Stat.MomentProblems.TruncatedCumulantInterior

/-!
The classical moment problem: which sequences of raw moments come from a probability law, and what
the moments pin down about the law. Raw-moment and cumulant algebra with the inversion between
them, atomic and symmetric-atom solutions, sharp envelopes for a bounded outcome, Gaussian
perturbations under a Carleman condition, and constrained score programs with their L² projection
residuals.
-/

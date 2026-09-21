/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.EmpiricalProcess.Basic
public import Causalean.Stat.EmpiricalProcess.CrossFitRate
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.LipschitzParametric.Sample
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.LipschitzZEstimatorSampleFn
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.Modulus
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.Process
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.SecondMoment
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.StochEquicont
public import Causalean.Stat.EmpiricalProcess.GlivenkoCantelli
public import Causalean.Stat.EmpiricalProcess.MEstimatorConsistency

/-!
Empirical-process foundations for uniform stochastic deviations. They provide the machinery for controlling an estimator simultaneously over a function class.
-/

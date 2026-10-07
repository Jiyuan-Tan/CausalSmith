/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.GraphicalThms.IDAlgorithmRec.Soundness

/-! # Soundness of the recursive ID algorithm

Soundness of the Tian–Shpitser ID algorithm in its recursive form, for structural causal models
with finitely many values per variable and positive observational probabilities. The acceptance
certificate requires each district of the post-intervention ancestral graph to be reachable from
a c-component of the original graph by the IDENTIFY recursion (alternately restricting to
ancestors and extracting a district). When the certificate holds for treatment set X and outcome
set Y, any two models on the same graph with the same observational law have the same law of Y
under do(X): the causal effect is identified. Only soundness is proved; completeness of the
algorithm is not.

## Main definitions

* `identifyMassRecObserved`, `recoveredFactorRec` — the recursive identification functional on
  observational masses, and the district factor it returns.

## Main results

* `doAncestralDistrictDensity_recovered_from_obs_rec` — each recursively reachable district
  density of the post-intervention law is computed from the observational law.
* `doKernelY_eq_cfactor_decomposition_rec` — two dominated, positive models on the same graph
  with equal observational kernels have equal post-intervention outcome kernels.
* `id_sound_rec`, `id_sound_rec_discrete` — identifiability of the query within a nonempty
  class of compatible positive models, for a general faithful reference family and for the
  counting reference.
-/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.LiNGAM.Identifiability
public import Causalean.Discovery.LiNGAM.Kurtosis
public import Causalean.Discovery.LiNGAM.LiNGAMKurtosis

/-!
# LiNGAM identification

Identifiability of the linear non-Gaussian acyclic model x = B·x + e (Shimizu et al. 2006) under
a fourth-cumulant assumption. Suppose two models x = A·e and x = A'·e' with invertible mixing
matrices generate the same law of the observed vector, both coefficient matrices A⁻¹ = I − B and
A'⁻¹ = I − B' have unit diagonal, A⁻¹ is acyclic in some causal order, and both disturbance
vectors have independent coordinates. If the coordinates of e are centered with finite fourth
moments and fourth cumulants that are all strictly positive or all strictly negative, then
B = B'. The argument uses a fourth-cumulant identity in place of the Darmois–Skitovich theorem,
so it covers the all-super-Gaussian and all-sub-Gaussian cases, not general non-Gaussian noise.

## Contents

* `Kurtosis` — `cross_fourth_cumulant_eq_sum`, the fourth cross-cumulant of two linear mixtures
  of independent sources, and `colSupport_of_kurtosis`: two independent mixtures of same-sign
  kurtotic sources cannot both load on the same source.
* `Identifiability` — `lingam_identifiable`: if I − B' equals I − B after a row permutation and a
  nonzero row scaling, with both diagonals zero and B acyclic, then B = B'.
* `LiNGAMKurtosis` — `ica_genPerm_relation` (the two unmixing matrices differ by a permutation and
  nonzero scaling) and the identification theorem `lingam_identifiability_kurtosis`.
-/

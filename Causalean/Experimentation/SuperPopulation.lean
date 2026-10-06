/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.SuperPopulation.Basic
public import Causalean.Experimentation.SuperPopulation.CLT
public import Causalean.Experimentation.SuperPopulation.HAC
public import Causalean.Experimentation.SuperPopulation.Network

/-!
# Super-population experimentation

Super-population modules collect network-dependent sampling CLTs and HAC variance tools.

This roll-up imports the basic `NetworkDependence` setup, the network-sum CLT
`networkSum_clt`, the network-HAC estimator `NetworkDependence.netHACVarEst` and its unbiasedness
identity, the HAC consistency theorems, and the mean-CLT bridge.  Together these modules cover
locally dependent network fields, standard-normal limits for network sums and means, and
network-HAC variance estimation for the same super-population asymptotic regime.
-/

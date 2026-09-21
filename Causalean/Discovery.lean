/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Discovery.InvariantPrediction
public import Causalean.Discovery.LiNGAM
public import Causalean.Discovery.LinearDisentanglement
/-!
# Causal-discovery interfaces

This directory collects three identification mechanisms: invariant prediction
across environments, non-Gaussian linear structural models via LiNGAM, and
linear latent disentanglement from intervention-indexed precision matrices.
Each subdirectory exposes its own model assumptions and recovery guarantee.
-/

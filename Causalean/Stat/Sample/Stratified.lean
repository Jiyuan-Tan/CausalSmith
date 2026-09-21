/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Sample.Stratified.Basic
public import Causalean.Stat.Sample.Stratified.CenteredNoiseBound
public import Causalean.Stat.Sample.Stratified.Main
public import Causalean.Stat.Sample.Stratified.MissingBound
public import Causalean.Stat.Sample.Stratified.MissingMoments
public import Causalean.Stat.Sample.Stratified.NestedCountBound
public import Causalean.Stat.Sample.Stratified.Basic
public import Causalean.Stat.Sample.Stratified.CenteredNoiseBound
public import Causalean.Stat.Sample.Stratified.Main
public import Causalean.Stat.Sample.Stratified.MissingBound
public import Causalean.Stat.Sample.Stratified.MissingMoments
public import Causalean.Stat.Sample.Stratified.NestedCountBound

/-!
# Fixed finite-stratum marked ratio mean-squared error

This module collects totalized finite-stratum arm means, their fixed-set
population targets and missing-arm decompositions, exact missing-count moments,
and boundary-safe mean-squared-error bounds for real square-integrable marks.
-/

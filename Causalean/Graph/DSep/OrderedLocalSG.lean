/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Graph.DSep.OrderedLocalSG.Defs
public import Causalean.Graph.DSep.OrderedLocalSG.PathSurgery
public import Causalean.Graph.DSep.OrderedLocalSG.PathJoining
public import Causalean.Graph.DSep.OrderedLocalSG.Closure

/-! # Ordered-local semi-graphoid closure

This interface exports the ordered-local derivation rules, the active-walk surgery and
joining lemmas used by the peel induction, and the theorem that d-separation yields an
ordered-local semi-graphoid derivation.
-/

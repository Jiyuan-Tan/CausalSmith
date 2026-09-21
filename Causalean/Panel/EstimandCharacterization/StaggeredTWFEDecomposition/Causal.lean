/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon (2021): TWFE decomposition under staggered timing — Layer C

**Role in the folder.** *Causal layer (support for the causal headline).*
Provides the potential-outcome corollaries consumed by the fused headline
`CausalDecomposition.lean`. See `StaggeredTWFEDecomposition.lean` for the folder
layer-map.

Layer C — causal characterization of the three 2x2 contrasts. Promotes the
algebraic objects `Δ_TN, Δ_EL, Δ_LE` from Layer A to causal statements about
window-specific ATTs under a two-state potential-outcome simplification.

**Two-state simplification (audit gap G2 / review item A6).**
The paper (Goodman-Bacon 2021, Assumption 1) uses a full adoption-date-indexed
potential-outcome family `Y_{gt}(a)` where `a` ranges over `𝒯 ∪ {∞}`.  Each
cohort `g` has its own path `Y_g(A_g)` for every possible adoption date `a`, and
consistency is stated as `Y_{gt} = Y_{gt}(A_g)`.

This Lean layer flattens that family to two maps:
- `Y0 : 𝒢 → Fin T → ℝ` representing `Y(∞)` (the never-treated path), and
- `Y1 : 𝒢 → Fin T → ℝ` representing `Y(A_g)` (each cohort's own adoption-date path).

This simplification is **sufficient** for the three causal corollaries proved
here (`Δ_TN_eq_ATT`, `Δ_EL_eq_ATT`, `Δ_LE_eq_bad_comparison`). The TN and EL
identification results require a nonempty pre-treatment window; separate
`_totalized` lemmas retain the algebraic equalities used by the decomposition
when a zero-weight comparison has an empty baseline. The full
adoption-date-indexed family `Y_{gt}(a)` is needed only for more general
heterogeneous-treatment comparisons across cohorts with different adoption
dates, which are outside the scope of Cor 5.

In particular, the LE bad-comparison result — showing that `Δ_LE` is contaminated
by `ATT_e(S1_LE) − ATT_e(S0_LE)` when early-treated cohorts serve as controls — is
fully captured by the two-state simplification.  To lift this to the paper's general
`Y_{gt}(a)` family one would introduce a type
`Y_full : 𝒢 → Fin T → WithTop (Fin T) → ℝ` and derive `Y0 g t = Y_full g t ⊤`
and `Y1 g t = Y_full g t (P.A g)` as special slices. The shared
`Causalean.Panel.AdoptionPath` module supplies the date predicates, but not this
potential-outcome family.

`Y0` denotes the never-treated path `Y(∞)`, while `Y1` denotes each cohort's
own adoption-date path `Y(A_g)`. This is sufficient for the LE bad-comparison
corollary proved here; it is not the full adoption-date-indexed family
`Y_gt(a)`.

* consistency `Y_{gt} = Y_{gt}(A_g)`,
* no anticipation `t < A_g → Y_{gt}(A_g) = Y_{gt}(∞)`,
* pairwise untreated parallel trends.

The three corollaries (NL doc A6 / LaTeX
`cor:po-estimand-goodman-bacon-causal-characterization`):

* `Δ_TN_eq_ATT` — `Δ_TN P g u = ATT_window Y0 Y1 g (S1_TN P g)`.
* `Δ_EL_eq_ATT` — `Δ_EL P e ℓ = ATT_window Y0 Y1 e (S1_EL P e ℓ)`.
* `Δ_LE_eq_bad_comparison` —
  `Δ_LE P e ℓ = ATT_window Y0 Y1 ℓ (S1_LE P e ℓ)
                  − (ATT_window Y0 Y1 e (S1_LE P e ℓ)
                      − ATT_window Y0 Y1 e (S0_LE P e ℓ))`.

Pure cell-level algebra: window means commute with sums, parallel trends
cancels untreated trends, and consistency reduces factual window means to
potential-outcome window means. No anticipation records the intended two-path
causal model but is not used by these proofs. **No** dependence on
`prop:po-did-att`; the proofs are stated directly in terms of the window mean
operator `Ybar0` (the never-treated potential-outcome window mean).

NL artifact:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.md`.
Source LaTeX:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.tex`.
-/

module
public import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.FinitePanel
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Goodman-Bacon Causal Characterization

This file gives the causal layer of the Goodman-Bacon staggered-timing
decomposition. Under two-state potential-outcome assumptions, consistency, no
anticipation, and pairwise untreated parallel trends, it identifies the
treated-versus-never and early-versus-late contrasts with window-specific
average treatment effects and expresses the late-versus-early contrast with its
bad-comparison adjustment. -/

@[expose] public section

namespace Causalean
namespace Panel.EstimandCharacterization
namespace StaggeredTWFEDecomposition

open Finset

variable {𝒢 : Type*} [Fintype 𝒢] [DecidableEq 𝒢] {T : ℕ}

/-- The [never-treated mean outcome over a period window](goal) averages
[a cohort's](hyp:g) [never-treated potential outcomes](hyp:Y0) across
[the selected periods](hyp:S) and is zero for an empty window. -/
noncomputable def Ybar0 (Y0 : 𝒢 → Fin T → ℝ) (g : 𝒢) (S : Finset (Fin T)) : ℝ :=
  (S.card : ℝ)⁻¹ * ∑ t ∈ S, Y0 g t

/-- The [window-specific average treatment effect on the treated](goal) averages the difference
between [own-adoption potential outcomes](hyp:Y1) and
[never-treated potential outcomes](hyp:Y0) for [a cohort](hyp:g) across
[the selected periods](hyp:S), and is zero for an empty window. -/
noncomputable def ATT_window (Y0 Y1 : 𝒢 → Fin T → ℝ) (g : 𝒢)
    (S : Finset (Fin T)) : ℝ :=
  (S.card : ℝ)⁻¹ * ∑ t ∈ S, (Y1 g t - Y0 g t)

/-- The causal model for [a cohort panel](hyp:P),
[never-treated potential outcomes](hyp:Y0), and
[own-adoption potential outcomes](hyp:Y1) combines
[consistency after adoption](hyp:consistencyTreated),
[consistency with never treatment before adoption](hyp:consistencyUntreated),
[no anticipation across the two potential-outcome paths](hyp:noAnticipation), and untreated
parallel trends for [treated-versus-never comparisons](hyp:parallelTrends_TN),
[early-versus-late comparisons](hyp:parallelTrends_EL), and
[late-versus-early comparisons](hyp:parallelTrends_LE).

**Two-state simplification (gap G2).** The paper uses a full adoption-date-indexed
family `Y_{gt}(a)`.  Here we use only two maps `Y0 = Y(∞)` and `Y1 = Y(A_g)`,
which suffices for Cor 5 (TN/EL ATT identification and the LE bad-comparison
corollary).  See the file header for a full discussion.

**Redundancy note.** `consistencyTreated` and `consistencyUntreated` together
with `noAnticipation` are slightly over-strong relative to the paper's single
consistency axiom `Y_{gt} = Y_{gt}(A_g)`: on pre-adoption cells,
`consistencyUntreated` gives `Y_{gt} = Y0 g t`, while `noAnticipation` gives
`Y1 g t = Y0 g t`. The current corollaries use `consistencyUntreated` directly
and do not consume `noAnticipation`; that field remains part of the assumption
package to record the intended two-path causal model. -/
structure CausalAssumptions (P : CohortPanel 𝒢 T) (Y0 Y1 : 𝒢 → Fin T → ℝ) :
    Prop where
  /-- Consistency on treated cells: when `A_g ≤ t`, the factual outcome
  equals the post-adoption potential outcome. -/
  consistencyTreated :
    ∀ g t, AdoptionPath.le (P.A g) t → P.Y g t = Y1 g t
  /-- Consistency on untreated cells: when `t < A_g`, the factual outcome
  equals the never-treated potential outcome. -/
  consistencyUntreated :
    ∀ g t, AdoptionPath.lt (P.A g) t → P.Y g t = Y0 g t
  /-- No anticipation: pre-adoption potential outcomes coincide. -/
  noAnticipation :
    ∀ g t, AdoptionPath.lt (P.A g) t → Y1 g t = Y0 g t
  /-- Pairwise untreated parallel trends for treated-vs-never (TN). -/
  parallelTrends_TN :
    ∀ g u, AdoptionPath.isFinite (P.A g) → AdoptionPath.isInfinite (P.A u) →
      Ybar0 Y0 g (S1_TN P g) - Ybar0 Y0 g (S0_TN P g)
        = Ybar0 Y0 u (S1_TN P g) - Ybar0 Y0 u (S0_TN P g)
  /-- Pairwise untreated parallel trends for early-vs-late before late (EL). -/
  parallelTrends_EL :
    ∀ e ℓ, P.A e < P.A ℓ → AdoptionPath.isFinite (P.A ℓ) →
      Ybar0 Y0 e (S1_EL P e ℓ) - Ybar0 Y0 e (S0_EL P e)
        = Ybar0 Y0 ℓ (S1_EL P e ℓ) - Ybar0 Y0 ℓ (S0_EL P e)
  /-- Pairwise untreated parallel trends for late-vs-early after early (LE). -/
  parallelTrends_LE :
    ∀ e ℓ, P.A e < P.A ℓ → AdoptionPath.isFinite (P.A ℓ) →
      Ybar0 Y0 e (S1_LE P ℓ) - Ybar0 Y0 e (S0_LE P e ℓ)
        = Ybar0 Y0 ℓ (S1_LE P ℓ) - Ybar0 Y0 ℓ (S0_LE P e ℓ)

namespace CausalAssumptions

variable {P : CohortPanel 𝒢 T} {Y0 Y1 : 𝒢 → Fin T → ℝ}

omit [DecidableEq 𝒢] in
/-- On the untreated window `S0_TN P g = {t : t < A_g}`, the factual `Ybar`
of cohort `g` equals the never-treated `Ybar0`: by `consistencyUntreated`
on each cell. -/
theorem Ybar_eq_Ybar0_on_S0_TN
    (hConsistency : ∀ g t, AdoptionPath.lt (P.A g) t → P.Y g t = Y0 g t) (g : 𝒢) :
    Ybar P g (S0_TN P g) = Ybar0 Y0 g (S0_TN P g) := by
  classical
  unfold Ybar Ybar0
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t ht
  have htlt : AdoptionPath.lt (P.A g) t := by
    simpa only [S0_TN, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] using ht
  exact hConsistency g t htlt

omit [DecidableEq 𝒢] in
/-- On any window `S` where every period is untreated for cohort `u`, the
factual `Ybar` equals the never-treated `Ybar0`. -/
theorem Ybar_eq_Ybar0_of_inf
    (hConsistency : ∀ g t, AdoptionPath.lt (P.A g) t → P.Y g t = Y0 g t)
    {u : 𝒢} (S : Finset (Fin T))
    (hS : ∀ t ∈ S, AdoptionPath.lt (P.A u) t) :
    Ybar P u S = Ybar0 Y0 u S := by
  classical
  unfold Ybar Ybar0
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t ht
  exact hConsistency u t (hS t ht)

omit [DecidableEq 𝒢] in
/-- On a window where every cell is treated for cohort `g`, the factual
`Ybar` decomposes as the never-treated mean plus the window ATT. -/
theorem Ybar_eq_Ybar0_add_ATT_of_treated
    (hConsistency : ∀ g t, AdoptionPath.le (P.A g) t → P.Y g t = Y1 g t)
    (g : 𝒢) (S : Finset (Fin T))
    (hS : ∀ t ∈ S, AdoptionPath.le (P.A g) t) :
    Ybar P g S = Ybar0 Y0 g S + ATT_window Y0 Y1 g S := by
  classical
  unfold Ybar Ybar0 ATT_window
  rw [← mul_add]
  congr 1
  calc
    ∑ t ∈ S, P.Y g t = ∑ t ∈ S, Y1 g t := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      exact hConsistency g t (hS t ht)
    _ = ∑ t ∈ S, (Y0 g t + (Y1 g t - Y0 g t)) := by
      refine Finset.sum_congr rfl ?_
      intro t _
      ring
    _ = ∑ t ∈ S, Y0 g t + ∑ t ∈ S, (Y1 g t - Y0 g t) := by
      exact Finset.sum_add_distrib

omit [DecidableEq 𝒢] in
/-- On the early-cohort untreated window `S0_EL P e = {t : t < A_e}`, the
factual `Ybar` of cohort `e` equals the never-treated `Ybar0`. -/
theorem Ybar_eq_Ybar0_on_S0_EL
    (hConsistency : ∀ g t, AdoptionPath.lt (P.A g) t → P.Y g t = Y0 g t) (e : 𝒢) :
    Ybar P e (S0_EL P e) = Ybar0 Y0 e (S0_EL P e) := by
  classical
  unfold Ybar Ybar0
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t ht
  have htlt : AdoptionPath.lt (P.A e) t := by
    simpa only [S0_EL, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] using ht
  exact hConsistency e t htlt

omit [DecidableEq 𝒢] in
/-- The late-cohort factual `Ybar` on `S1_EL P e ℓ = {A_e ≤ t < A_ℓ}` equals
the never-treated `Ybar0`: each cell satisfies `t < A_ℓ`. -/
theorem Ybar_eq_Ybar0_late_on_S1_EL
    (hConsistency : ∀ g t, AdoptionPath.lt (P.A g) t → P.Y g t = Y0 g t) (e ℓ : 𝒢) :
    Ybar P ℓ (S1_EL P e ℓ) = Ybar0 Y0 ℓ (S1_EL P e ℓ) := by
  classical
  unfold Ybar Ybar0
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t ht
  have htmem : AdoptionPath.le (P.A e) t ∧ AdoptionPath.lt (P.A ℓ) t := by
    simpa only [S1_EL, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] using ht
  exact hConsistency ℓ t htmem.2

omit [DecidableEq 𝒢] in
/-- The late-cohort factual `Ybar` on `S0_EL P e = {t : t < A_e}` equals
the never-treated `Ybar0` when `A_e < A_ℓ`. -/
theorem Ybar_eq_Ybar0_late_on_S0_EL
    (hConsistency : ∀ g t, AdoptionPath.lt (P.A g) t → P.Y g t = Y0 g t)
    (e ℓ : 𝒢) (h_lt : P.A e < P.A ℓ) :
    Ybar P ℓ (S0_EL P e) = Ybar0 Y0 ℓ (S0_EL P e) := by
  classical
  unfold Ybar Ybar0
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t ht
  have htlt : (t : WithTop (Fin T)) < P.A e := by
    have h0 : AdoptionPath.lt (P.A e) t := by
      simpa only [S0_EL, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] using ht
    exact h0
  exact hConsistency ℓ t (by
    simpa [AdoptionPath.lt] using lt_trans htlt h_lt)

omit [DecidableEq 𝒢] in
/-- The late-cohort factual `Ybar` on `S0_LE P e ℓ = {A_e ≤ t < A_ℓ}` equals
the never-treated `Ybar0`. -/
theorem Ybar_eq_Ybar0_late_on_S0_LE
    (hConsistency : ∀ g t, AdoptionPath.lt (P.A g) t → P.Y g t = Y0 g t) (e ℓ : 𝒢) :
    Ybar P ℓ (S0_LE P e ℓ) = Ybar0 Y0 ℓ (S0_LE P e ℓ) := by
  classical
  unfold Ybar Ybar0
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t ht
  have htmem : AdoptionPath.le (P.A e) t ∧ AdoptionPath.lt (P.A ℓ) t := by
    simpa only [S0_LE, S1_EL, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] using ht
  exact hConsistency ℓ t htmem.2

end CausalAssumptions

omit [DecidableEq 𝒢] in
/-- Under [the packaged causal assumptions](hyp:hA) linking [a cohort panel](hyp:P) to
[never-treated and own-adoption potential-outcome paths](hyp:Y0,Y1), the totalized comparison
of [a treated and a never-treated cohort](hyp:g,u) [equals the treated cohort's totalized
post-adoption window effect](goal) when their adoption dates are respectively
[finite](hyp:h_g_fin) and [infinite](hyp:h_u_inf).

This equality also covers an empty pre-treatment window because `Ybar` is defined as zero
there. In that case it is an algebraic bookkeeping identity, not a standalone DID
identification claim.

    Δ_TN P g u = ATT_window Y0 Y1 g (S1_TN P g).

Proof outline:
1. Replace `Ybar P u (S1_TN P g)` and `Ybar P u (S0_TN P g)` by `Ybar0 Y0 u …`
   via `Ybar_eq_Ybar0_of_inf` (cohort `u` is never treated).
2. Replace `Ybar P g (S0_TN P g)` by `Ybar0 Y0 g (S0_TN P g)` via
   `Ybar_eq_Ybar0_on_S0_TN` (untreated-cell consistency).
3. Apply `parallelTrends_TN` to cancel `(Ybar0 Y0 g S1) - (Ybar0 Y0 g S0)`
   against `(Ybar0 Y0 u S1) - (Ybar0 Y0 u S0)`.
4. The remainder reduces to `Ybar P g (S1_TN P g) - Ybar0 Y0 g (S1_TN P g)`,
   which by consistency on `S1_TN` (treated cells) and the `ATT_window`
   definition equals `ATT_window Y0 Y1 g (S1_TN P g)`. -/
theorem Δ_TN_eq_ATT_totalized (P : CohortPanel 𝒢 T) (Y0 Y1 : 𝒢 → Fin T → ℝ)
    (hA : CausalAssumptions P Y0 Y1) (g u : 𝒢)
    (h_g_fin : AdoptionPath.isFinite (P.A g))
    (h_u_inf : AdoptionPath.isInfinite (P.A u)) :
    Δ_TN P g u = ATT_window Y0 Y1 g (S1_TN P g) := by
  classical
  have h_treated :
      Ybar P g (S1_TN P g) =
        Ybar0 Y0 g (S1_TN P g) + ATT_window Y0 Y1 g (S1_TN P g) := by
    exact CausalAssumptions.Ybar_eq_Ybar0_add_ATT_of_treated hA.consistencyTreated g (S1_TN P g) (by
      intro t ht
      simpa only [S1_TN, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] using ht)
  have h_g0 := CausalAssumptions.Ybar_eq_Ybar0_on_S0_TN hA.consistencyUntreated g
  have h_u1 := CausalAssumptions.Ybar_eq_Ybar0_of_inf hA.consistencyUntreated
    (S1_TN P g) (fun _ _ => AdoptionPath.lt_of_isInfinite h_u_inf)
  have h_u0 := CausalAssumptions.Ybar_eq_Ybar0_of_inf hA.consistencyUntreated
    (S0_TN P g) (fun _ _ => AdoptionPath.lt_of_isInfinite h_u_inf)
  have hPT := hA.parallelTrends_TN g u h_g_fin h_u_inf
  unfold Δ_TN
  rw [h_treated, h_g0, h_u1, h_u0]
  linarith

omit [DecidableEq 𝒢] in
/-- Under [the packaged causal assumptions](hyp:hA) linking [a cohort panel](hyp:P) to
[never-treated and own-adoption potential-outcome paths](hyp:Y0,Y1), the DID comparison of
[a treated and a never-treated cohort](hyp:g,u) [identifies the treated cohort's post-adoption
window effect](goal) when their adoption dates are respectively [finite](hyp:h_g_fin) and
[infinite](hyp:h_u_inf), and [the treated cohort has a pre-treatment period](hyp:h_pre).

The nonempty baseline rules out the first-period-adoption case, where the totalized equality
above remains valid but does not represent a before/after DID design. -/
theorem Δ_TN_eq_ATT (P : CohortPanel 𝒢 T) (Y0 Y1 : 𝒢 → Fin T → ℝ)
    (hA : CausalAssumptions P Y0 Y1) (g u : 𝒢)
    (h_g_fin : AdoptionPath.isFinite (P.A g))
    (h_u_inf : AdoptionPath.isInfinite (P.A u))
    (h_pre : (S0_TN P g).Nonempty) :
    Δ_TN P g u = ATT_window Y0 Y1 g (S1_TN P g) := by
  exact (fun _ : (S0_TN P g).Nonempty =>
    Δ_TN_eq_ATT_totalized P Y0 Y1 hA g u h_g_fin h_u_inf) h_pre

omit [DecidableEq 𝒢] in
/-- Under [the packaged causal assumptions](hyp:hA) linking [a cohort panel](hyp:P) to
[never-treated and own-adoption potential-outcome paths](hyp:Y0,Y1), the totalized comparison
of [an early and a late cohort](hyp:e,ℓ) [equals the early cohort's totalized effect over the
between-adoption window](goal) when [the early cohort adopts first](hyp:h_lt) and
[the late cohort eventually adopts](hyp:h_ℓ_fin).

This equality also covers an empty pre-treatment window because `Ybar` is defined as zero
there. In that case it is an algebraic bookkeeping identity, not a standalone DID
identification claim.

    Δ_EL P e ℓ = ATT_window Y0 Y1 e (S1_EL P e ℓ).

Proof outline:
1. Replace `Ybar P ℓ (S1_EL P e ℓ)` and `Ybar P ℓ (S0_EL P e ℓ)` by
   `Ybar0 Y0 ℓ …` (late cohort is untreated on both EL windows since they
   sit before `A_ℓ`).
2. Replace `Ybar P e (S0_EL P e ℓ)` by `Ybar0 Y0 e …` via
   `Ybar_eq_Ybar0_on_S0_EL`.
3. Apply `parallelTrends_EL` to cancel the late-cohort contribution.
4. The remainder is `Ybar P e (S1_EL P e ℓ) - Ybar0 Y0 e (S1_EL P e ℓ) =
   ATT_window Y0 Y1 e (S1_EL P e ℓ)` by consistency on the treated window. -/
theorem Δ_EL_eq_ATT_totalized (P : CohortPanel 𝒢 T) (Y0 Y1 : 𝒢 → Fin T → ℝ)
    (hA : CausalAssumptions P Y0 Y1) (e ℓ : 𝒢)
    (h_lt : P.A e < P.A ℓ) (h_ℓ_fin : AdoptionPath.isFinite (P.A ℓ)) :
    Δ_EL P e ℓ = ATT_window Y0 Y1 e (S1_EL P e ℓ) := by
  classical
  have h_e1 :
      Ybar P e (S1_EL P e ℓ) =
        Ybar0 Y0 e (S1_EL P e ℓ) + ATT_window Y0 Y1 e (S1_EL P e ℓ) := by
    exact CausalAssumptions.Ybar_eq_Ybar0_add_ATT_of_treated hA.consistencyTreated e
      (S1_EL P e ℓ) (by
      intro t ht
      have htmem :
          AdoptionPath.le (P.A e) t ∧ AdoptionPath.lt (P.A ℓ) t := by
        simpa only [S1_EL, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq] using ht
      exact htmem.1)
  have h_e0 := CausalAssumptions.Ybar_eq_Ybar0_on_S0_EL hA.consistencyUntreated e
  have h_l1 := CausalAssumptions.Ybar_eq_Ybar0_late_on_S1_EL hA.consistencyUntreated e ℓ
  have h_l0 := CausalAssumptions.Ybar_eq_Ybar0_late_on_S0_EL hA.consistencyUntreated e ℓ h_lt
  have hPT := hA.parallelTrends_EL e ℓ h_lt h_ℓ_fin
  unfold Δ_EL
  rw [h_e1, h_e0, h_l1, h_l0]
  linarith

omit [DecidableEq 𝒢] in
/-- Under [the packaged causal assumptions](hyp:hA) linking [a cohort panel](hyp:P) to
[never-treated and own-adoption potential-outcome paths](hyp:Y0,Y1), the DID comparison of
[an early and a late cohort](hyp:e,ℓ) [identifies the early cohort's effect over the
between-adoption window](goal) when [the early cohort adopts first](hyp:h_lt),
[the late cohort eventually adopts](hyp:h_ℓ_fin), and
[the early cohort has a pre-treatment period](hyp:h_pre).

The nonempty baseline rules out first-period adoption by the early cohort. -/
theorem Δ_EL_eq_ATT (P : CohortPanel 𝒢 T) (Y0 Y1 : 𝒢 → Fin T → ℝ)
    (hA : CausalAssumptions P Y0 Y1) (e ℓ : 𝒢)
    (h_lt : P.A e < P.A ℓ) (h_ℓ_fin : AdoptionPath.isFinite (P.A ℓ))
    (h_pre : (S0_EL P e).Nonempty) :
    Δ_EL P e ℓ = ATT_window Y0 Y1 e (S1_EL P e ℓ) := by
  exact (fun _ : (S0_EL P e).Nonempty =>
    Δ_EL_eq_ATT_totalized P Y0 Y1 hA e ℓ h_lt h_ℓ_fin) h_pre

omit [DecidableEq 𝒢] in
/-- **Layer C corollary 3 — LE has a bad-comparison term.** Fix a cohort panel `P` and
potential-outcome maps `Y0`, `Y1`, and assume [consistency on treated and untreated cells, no
anticipation, and pairwise untreated parallel trends across the three comparison
types](hyp:hA). For [an early cohort `e` whose adoption date strictly precedes that of a late
cohort `ℓ`](hyp:h_lt), with [`ℓ`'s adoption date finite](hyp:h_ℓ_fin), [the late-versus-early
contrast `Δ_LE` equals `ℓ`'s window-specific average treatment effect on the treated over its
post-adoption window, minus the "bad-comparison" gap between `e`'s own treatment effects on the
two comparison windows](goal):

    Δ_LE P e ℓ
      = ATT_window Y0 Y1 ℓ (S1_LE P ℓ)
        − (ATT_window Y0 Y1 e (S1_LE P ℓ)
            − ATT_window Y0 Y1 e (S0_LE P e ℓ)).

Proof outline:
1. The late cohort `ℓ` is untreated on `S0_LE P e ℓ = {A_e ≤ t < A_ℓ}` so
   `Ybar P ℓ (S0_LE P e ℓ) = Ybar0 Y0 ℓ …`.
2. On `S1_LE P ℓ = {A_ℓ ≤ t}`, `ℓ` is treated, so consistency gives
   `Ybar P ℓ (S1_LE P ℓ) = Ybar0 Y0 ℓ … + ATT_window Y0 Y1 ℓ …`.
3. Cohort `e` is treated on both `S0_LE` and `S1_LE` (since `A_e < A_ℓ`
   means `A_e ≤ t` whenever `t ∈ S0_LE` or `t ∈ S1_LE`); decompose
   `Ybar P e S = Ybar0 Y0 e S + ATT_window Y0 Y1 e S` for each window.
4. Apply `parallelTrends_LE` to cancel `Ybar0 Y0 ℓ` differences against
   `Ybar0 Y0 e` differences; the residual ATT terms produce the
   bad-comparison expression. -/
theorem Δ_LE_eq_bad_comparison (P : CohortPanel 𝒢 T) (Y0 Y1 : 𝒢 → Fin T → ℝ)
    (hA : CausalAssumptions P Y0 Y1) (e ℓ : 𝒢)
    (h_lt : P.A e < P.A ℓ) (h_ℓ_fin : AdoptionPath.isFinite (P.A ℓ)) :
    Δ_LE P e ℓ
      = ATT_window Y0 Y1 ℓ (S1_LE P ℓ)
        - (ATT_window Y0 Y1 e (S1_LE P ℓ)
            - ATT_window Y0 Y1 e (S0_LE P e ℓ)) := by
  classical
  have h_l1 :
      Ybar P ℓ (S1_LE P ℓ) =
        Ybar0 Y0 ℓ (S1_LE P ℓ) + ATT_window Y0 Y1 ℓ (S1_LE P ℓ) := by
    exact CausalAssumptions.Ybar_eq_Ybar0_add_ATT_of_treated hA.consistencyTreated ℓ (S1_LE P ℓ) (by
      intro t ht
      simpa only [S1_LE, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] using ht)
  have h_l0 := CausalAssumptions.Ybar_eq_Ybar0_late_on_S0_LE hA.consistencyUntreated e ℓ
  have h_e0 :
      Ybar P e (S0_LE P e ℓ) =
        Ybar0 Y0 e (S0_LE P e ℓ) + ATT_window Y0 Y1 e (S0_LE P e ℓ) := by
    exact CausalAssumptions.Ybar_eq_Ybar0_add_ATT_of_treated hA.consistencyTreated e
      (S0_LE P e ℓ) (by
      intro t ht
      have htmem :
          AdoptionPath.le (P.A e) t ∧ AdoptionPath.lt (P.A ℓ) t := by
        simpa only [S0_LE, S1_EL, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq] using ht
      exact htmem.1)
  have h_e1 :
      Ybar P e (S1_LE P ℓ) =
        Ybar0 Y0 e (S1_LE P ℓ) + ATT_window Y0 Y1 e (S1_LE P ℓ) := by
    exact CausalAssumptions.Ybar_eq_Ybar0_add_ATT_of_treated hA.consistencyTreated e (S1_LE P ℓ) (by
      intro t ht
      have hle : AdoptionPath.le (P.A ℓ) t := by
        simpa only [S1_LE, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq] using ht
      exact le_of_lt (lt_of_lt_of_le h_lt hle))
  have hPT := hA.parallelTrends_LE e ℓ h_lt h_ℓ_fin
  unfold Δ_LE
  rw [h_l1, h_l0, h_e1, h_e0]
  linarith

end StaggeredTWFEDecomposition
end Panel.EstimandCharacterization
end Causalean

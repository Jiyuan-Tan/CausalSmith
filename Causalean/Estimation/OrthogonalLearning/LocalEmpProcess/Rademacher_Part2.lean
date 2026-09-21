/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bridge: bounded loss + Rademacher complexity ⇒ `LocalEmpProcessModulus`

This bridge discharges the `LocalEmpProcessModulus` hypothesis used by
`OrthogonalLearning/OracleInequality.lean` from concrete data-generating
assumptions. No upstream code lives here; this file consumes the
`Causalean.Stat.Concentration.{Rademacher, BoundedDifference, McDiarmid,
Symmetrization, Separable}` headlines together with the orthogonal
statistical-learning oracle-inequality predicate.

## Output

Under
* a uniform bound `|ℓ z θ g| ≤ b` for `θ ∈ Θ_set`,
* a population Rademacher-complexity bound `R_n` for the centred loss
  class `{z ↦ ℓ z θ g − ℓ z θ₀ g : θ ∈ Θ_set}` measured on the estimation
  fold,
* countability / separability of `Θ_set` (handled via
  `Causalean.Stat.Concentration.Separable`),

we conclude `LocalEmpProcessModulus S S_iid split ρ δ g` with
`ρ n := √(2 R_n + 2b * Real.sqrt (2 * Real.log (1 / δ) / |B(n)|))`
when the estimation fold is nonempty, and the boundary value
`ρ n := √(2b)` when `|B(n)| = 0`.

Only the constant slot `(ρ n)^2` is filled — the `ρ n * ‖θ − θ₀‖` slot
of the modulus inequality is satisfied by the trivial monotonicity
`ρ n * ‖θ − θ₀‖ ≥ 0`.  This is a deliberate, non-localized realisation:
sharper localized rates (Foster–Syrgkanis Lemma 14) live in the sibling
file `OrthogonalLearning/LocalEmpProcess/Localized.lean`.

## Headline schema

```
theorem localEmpProcessModulus_of_bounded_rademacher
    (S : LearningSystem Ω μ Z P_Z Θ G) (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid) {b : ℝ} (hb : 0 ≤ b)
    (g : G) (hg_bdd : ∀ z, ∀ θ ∈ S.Θ_set, |S.ℓ z θ g| ≤ b)
    (R : ℕ → ℝ) (hR : RademacherBound S S_iid split g R)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    LocalEmpProcessModulus S S_iid split
      (fun n => Real.sqrt
        (if (split.foldB n).card = 0 then 2 * b
         else 2 * R n + 2 * b *
          Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) δ g
```
-/

module
public import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Rademacher_Part1

/-! # Global Rademacher Modulus

This second part proves `localEmpProcessModulus_of_bounded_rademacher`, the main
everywhere-bounded bridge from a population Rademacher-complexity bound to a local
empirical-process modulus. The shared definitions are in `Rademacher_Part1.lean`; the
almost-everywhere and singleton forms are in `Rademacher_Part3.lean`.
-/

public section

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Causalean.Stat
  Causalean.Stat.Concentration

/-! ## Imported helpers

Part 1 supplies the public fold-B joint-law alias and the predicates used below. -/
variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]
/-- **Bounded-loss Rademacher bridge theorem.** Assume [`b` is nonnegative](hyp:hb), that
[the loss magnitude is uniformly bounded by `b` over the parameter set](hyp:hg_bdd), and
that [the loss is continuous in the parameter on the parameter set](hyp:hg_cont). Given
[a sequence `R n` that is nonnegative and upper-bounds the population Rademacher
complexity of the centred loss class on the fold-B sample at every sample
size](hyp:hR), then for any confidence level [`0 < δ ≤ 1`](hyp:hδ,hδ') [the local
empirical-process modulus condition holds, with rate `ρ n := √(2 · b)` when the fold-B
sample is empty and `ρ n := √(2 · R n + 2 · b · √(2 · log(1/δ) / |foldB n|))`
otherwise](goal).

Under uniform boundedness of the loss and a Rademacher-complexity bound
on the centred loss class, `LocalEmpProcessModulus` holds with
the textbook nonempty-fold rate
`ρ n := √(2 R n + 2b · √(2 log(1/δ) / |B(n)|))`, with the empty-fold
boundary branch `ρ n := √(2b)`.

The proof chains:

1. `BoundedDifference.uniformDeviation_bounded_difference` ⇒ the centred
   sup is bounded-difference with constant `c_i = 2b / n`.
2. `McDiarmid.mcdiarmid_inequality_pos'` ⇒ the centred sup is concentrated
   around its mean: `‖Pₙ − P‖_F ≤ 𝔼‖Pₙ − P‖_F + b√(2 log(1/δ)/n)` w.p.
   `≥ 1 − δ`.
3. `Symmetrization.expectation_le_rademacher` ⇒ `𝔼‖Pₙ − P‖_F ≤ 2 R_n(F)`
   in the population Rademacher sense.
4. The bound on the centred *excess* risk
   `[L θ g − L θ₀ g] − [Lₙ θ g − Lₙ θ₀ g]`
   follows by applying the uniform deviation bound to the centred loss
   class.

The `ρ n * ‖θ − θ₀‖` slot of the modulus inequality is satisfied
trivially since the right-hand side `(ρ n)^2` already dominates.

**Rate form.** The modulus only uses the constant `ρ²` slot, with the
`ρ‖θ−θ₀‖` slot set to 0, so the realised
modulus must be a `ρ_{n,δ}` whose square dominates the uniform deviation
of the centred loss class.  The centred class
`{z ↦ ℓ z θ g − ℓ z θ₀ g : θ ∈ Θ_set}` is bounded by `2b` (triangle
inequality), so:

* `expectation_le_rademacher` ⇒ `𝔼[sup_θ |Lₙ_centred − L_centred|] ≤ 2 R n`,
* `uniformDeviation_bounded_difference` (with class bound `2b`) gives
  bounded-difference constants `c_i = 4b/m` where `m = |B(n)|`,
* `mcdiarmid_inequality_pos'` ⇒ deviation around the mean by
  `2b · √(2 log(1/δ) / m)` w.p. ≥ `1 − δ`.

We therefore set

    ρ_{n,δ} := if |B(n)| = 0 then √(2b)
      else Real.sqrt (2 · R n + 2 · b · √(2 · log(1/δ) / |B(n)|))

so that `ρ²` itself dominates `2 R n + 2b · √(2 log(1/δ) / |B(n)|)` and
the slack term `ρ · ‖θ − θ₀‖` adds non-negative excess.

**Hypotheses.** `[IsProbabilityMeasure μ]` is needed for
`μ E ≥ 1 - ENNReal.ofReal δ`; `[SeparableSpace S.Θ_set]` and
`[Nonempty S.Θ_set]` carry the countable-dense substrate, while
`LossContinuousOnΘset` provides the continuity needed by
`separableSpaceSup_eq_real` to lift FoML's `ℕ`-indexed sup conclusion to
a sup over `↥S.Θ_set`.

**Why not `[Countable S.Θ_set]`?** Combined with `S.Θ_convex`, countability
forces `S.Θ_set.Subsingleton` (a non-trivial convex subset of a real
vector space contains a line segment, which is uncountable).  The
`[SeparableSpace]` form admits genuinely infinite convex `Θ_set`.
The user must supply `idx_dense` as the explicit separability witness —
`S.Θ_set` is not assumed to carry a `[SeparableSpace]` instance a priori;
the bridge constructs that instance from `idx_dense` internally.

**Bridge.** The re-indexing from FoML's `μⁿ`-on-`Fin m → Ω` form to the
fold-B sum on `μ` uses `Causalean.Stat.oneShot_iid` (joint-law identification) plus the
order-isomorphism `Fin (split.foldB n).card ≃o split.foldB n`.  The
final sup-over-`↥S.Θ_set` step uses `separableSpaceSup_eq_real`
specialised to the deviation map. -/
theorem localEmpProcessModulus_of_bounded_rademacher
    (S : LearningSystem Ω μ Z P_Z Θ G)
    [IsProbabilityMeasure μ]
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    {b : ℝ} (hb : 0 ≤ b) (g : G)
    (hg_bdd : UniformlyBoundedLoss S g b)
    (hg_cont : LossContinuousOnΘset S g)
    (idx : ℕ → S.Θ_set)
    (idx_dense : DenseRange idx)
    (R : ℕ → ℝ)
    (hR : RademacherBound S S_iid split g idx R)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    LocalEmpProcessModulus S S_iid split
      (fun n => Real.sqrt
        (if (split.foldB n).card = 0 then 2 * b
         else 2 * R n + 2 * b *
          Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) δ g := by
  intro n
  classical
  haveI : IsProbabilityMeasure P_Z := by
    rw [← S_iid.law]
    exact Measure.isProbabilityMeasure_map (S_iid.meas 0).aemeasurable
  have hR_nonneg : 0 ≤ R n := (hR n).1
  by_cases hm0 : (split.foldB n).card = 0
  · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · rw [measure_univ]
      exact tsub_le_self
    · intro ω _ θ hθ
      have hfold_empty : split.foldB n = ∅ := Finset.card_eq_zero.mp hm0
      have hpop : S.L θ g - S.L S.θ₀ g ≤ 2 * b :=
        populationRisk_sub_le_two_mul_bound S hb hg_bdd hθ
      have hρsq :
          (Real.sqrt
            (if (split.foldB n).card = 0 then 2 * b
             else 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2
            = 2 * b := by
        rw [Real.sq_sqrt]
        · simp [hm0]
        · have : 0 ≤ 2 * b := by nlinarith
          simpa [hm0] using this
      have hρ_nonneg :
          0 ≤ Real.sqrt
            (if (split.foldB n).card = 0 then 2 * b
             else 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) :=
        Real.sqrt_nonneg _
      have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
      calc
        (S.L θ g - S.L S.θ₀ g)
            - (empRiskFoldB S S_iid split n ω θ g
                - empRiskFoldB S S_iid split n ω S.θ₀ g)
            = S.L θ g - S.L S.θ₀ g := by
                simp [empRiskFoldB, hfold_empty]
        _ ≤ 2 * b := hpop
        _ = (Real.sqrt
            (if (split.foldB n).card = 0 then 2 * b
             else 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := hρsq.symm
        _ ≤ Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) * ‖θ - S.θ₀‖
              + (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := by
            nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg]
  · have hm_pos_nat : 0 < (split.foldB n).card := Nat.pos_of_ne_zero hm0
    have hm_pos : 0 < ((split.foldB n).card : ℝ) := Nat.cast_pos.mpr hm_pos_nat
    by_cases hb0 : b = 0
    · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
      · rw [measure_univ]
        exact tsub_le_self
      · intro ω _ θ hθ
        have hloss_zero : ∀ z θ', θ' ∈ S.Θ_set → S.ℓ z θ' g = 0 := by
          intro z θ' hθ'
          have habs : |S.ℓ z θ' g| = 0 := by
            apply le_antisymm
            · simpa [hb0] using hg_bdd z θ' hθ'
            · exact abs_nonneg _
          exact abs_eq_zero.mp habs
        have hLθ : S.L θ g = 0 := by
          have habs := populationRisk_abs_le_of_uniform S hb hg_bdd hθ
          exact abs_eq_zero.mp (le_antisymm (by simpa [hb0] using habs) (abs_nonneg _))
        have hL0 : S.L S.θ₀ g = 0 := by
          have habs := populationRisk_abs_le_of_uniform S hb hg_bdd S.θ₀_mem
          exact abs_eq_zero.mp (le_antisymm (by simpa [hb0] using habs) (abs_nonneg _))
        have hempθ : empRiskFoldB S S_iid split n ω θ g = 0 := by
          simp [empRiskFoldB, hloss_zero, hθ]
        have hemp0 : empRiskFoldB S S_iid split n ω S.θ₀ g = 0 := by
          simp [empRiskFoldB, hloss_zero, S.θ₀_mem]
        have hρ_nonneg :
            0 ≤ Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) :=
          Real.sqrt_nonneg _
        have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
        have hρsq_nonneg :
            0 ≤ (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := sq_nonneg _
        calc
          (S.L θ g - S.L S.θ₀ g)
              - (empRiskFoldB S S_iid split n ω θ g
                  - empRiskFoldB S S_iid split n ω S.θ₀ g) = 0 := by
                simp [hLθ, hL0, hempθ, hemp0]
          _ ≤ Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) * ‖θ - S.θ₀‖
              + (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := by
            nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg, hρsq_nonneg]
    · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      let m : ℕ := (split.foldB n).card
      let fθ : S.Θ_set → Z → ℝ := fun θ z => S.ℓ z θ.val g - S.ℓ z S.θ₀ g
      haveI : Nonempty Z := nonempty_of_isProbabilityMeasure P_Z
      haveI : Nonempty S.Θ_set := ⟨⟨S.θ₀, S.θ₀_mem⟩⟩
      haveI : SeparableSpace S.Θ_set := by
        exact ⟨⟨Set.range idx, Set.countable_range idx, idx_dense⟩⟩
      have hf_meas : ∀ θ : S.Θ_set, Measurable (fθ θ) := by
        intro θ
        exact (S.ℓ_meas θ.val g).sub (S.ℓ_meas S.θ₀ g)
      have hf_bdd : ∀ θ : S.Θ_set, ∀ z : Z, |fθ θ z| ≤ 2 * b := by
        intro θ z
        have h1 : |S.ℓ z θ.val g| ≤ b := hg_bdd z θ.val θ.property
        have h2 : |S.ℓ z S.θ₀ g| ≤ b := hg_bdd z S.θ₀ S.θ₀_mem
        have h := abs_sub (S.ℓ z θ.val g) (S.ℓ z S.θ₀ g)
        dsimp [fθ]
        linarith
      have hf_cont : ∀ z : Z, Continuous fun θ : S.Θ_set => fθ θ z := by
        intro z
        exact (hg_cont z).sub continuous_const
      let ε : ℝ := 2 * b * Real.sqrt (2 * Real.log (1 / δ) / m)
      let τ : ℝ := 2 * R n + ε
      have hε_nonneg : 0 ≤ ε := by
        dsimp [ε]
        positivity
      have htail := uniform_deviation_tail_bound_separable_of_pos
        (μ := P_Z) (n := m) (f := fθ) hf_meas (X := id) measurable_id
        (b := 2 * b) (by linarith) hf_bdd hf_cont (ε := ε) hε_nonneg
      have hrad_full_le : rademacherComplexity m fθ P_Z id ≤ R n := by
        have hfull_dense :
            rademacherComplexity m fθ P_Z id =
              rademacherComplexity m (fθ ∘ idx) P_Z id :=
          rademacherComplexity_eq_denseRange idx_dense m fθ hf_cont P_Z id
        have hmap :
            rademacherComplexity m (fθ ∘ idx) P_Z id =
              rademacherComplexity m (fθ ∘ idx) μ (S_iid.Z 0) := by
          have hmap' :
              rademacherComplexity m (fθ ∘ idx) (μ.map (S_iid.Z 0)) id =
                rademacherComplexity m (fθ ∘ idx) μ (S_iid.Z 0) :=
            rademacherComplexity_map_id m (fθ ∘ idx)
            (by
              intro k
              exact (hf_meas (idx k))) μ (S_iid.Z 0) (S_iid.meas 0)
          simpa [S_iid.law] using hmap'
        calc
          rademacherComplexity m fθ P_Z id
              = rademacherComplexity m (fθ ∘ idx) P_Z id := hfull_dense
          _ = rademacherComplexity m (fθ ∘ idx) μ (S_iid.Z 0) := hmap
          _ ≤ R n := (hR n).2
      let badZ : Set (Fin m → Z) :=
        {s | 2 • rademacherComplexity m fθ P_Z id + ε ≤
          uniformDeviation m fθ P_Z id (id ∘ s)}
      let EZ : Set (Fin m → Z) := badZᶜ
      have hbad_meas : MeasurableSet badZ := by
        have hUD_eq :
            uniformDeviation m fθ P_Z id =
              uniformDeviation m (fθ ∘ denseSeq S.Θ_set) P_Z id :=
          uniformDeviation_eq (n := m) (f := fθ) hf_meas id measurable_id
            (b := 2 * b) hf_bdd hf_cont P_Z
        have hbad_eq :
            badZ =
              {s | 2 • rademacherComplexity m fθ P_Z id + ε ≤
                uniformDeviation m (fθ ∘ denseSeq S.Θ_set) P_Z id (id ∘ s)} := by
          ext s
          simp [badZ, hUD_eq]
        rw [hbad_eq]
        exact measurableSet_le measurable_const
          ((uniformDeviation_measurable (n := m) (f := fθ ∘ denseSeq S.Θ_set)
            (μ := P_Z) id (by intro k; exact hf_meas (denseSeq S.Θ_set k))).comp measurable_id)
      have hEZ_meas : MeasurableSet EZ := hbad_meas.compl
      have hbad_le_delta : Measure.pi (fun _ : Fin m => P_Z) badZ ≤ ENNReal.ofReal δ := by
        have hbad_toReal : (Measure.pi (fun _ : Fin m => P_Z) badZ).toReal ≤ δ := by
          have hle_exp := htail
          have hexp_le : Real.exp (-ε ^ 2 * m / (2 * (2 * b) ^ 2)) ≤ δ := by
            have hδ_nonneg : 0 ≤ δ := le_of_lt hδ
            have hlog_nonneg : 0 ≤ Real.log (1 / δ) := by
              apply Real.log_nonneg
              have : (1 : ℝ) ≤ 1 / δ := by
                rw [le_div_iff₀ hδ]
                simpa using hδ'
              exact this
            have hsqrt_sq : (Real.sqrt (2 * Real.log (1 / δ) / m)) ^ 2 =
                2 * Real.log (1 / δ) / m := by
              rw [Real.sq_sqrt]
              positivity
            have hcalc : -ε ^ 2 * m / (2 * (2 * b) ^ 2) = Real.log δ := by
              dsimp [ε]
              rw [mul_pow, hsqrt_sq]
              field_simp [hb_pos.ne', hm_pos.ne']
              ring_nf
              rw [Real.log_inv δ]
              rw [mul_assoc, mul_inv_cancel₀ hm_pos.ne', mul_one]
              ring
            rw [hcalc, Real.exp_log hδ]
          exact hle_exp.trans hexp_le
        rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (le_of_lt hδ)]
        exact hbad_toReal
      have hEZ_prob : Measure.pi (fun _ : Fin m => P_Z) EZ ≥ 1 - ENNReal.ofReal δ := by
        dsimp [EZ]
        rw [measure_compl hbad_meas (measure_ne_top _ _), measure_univ]
        exact tsub_le_tsub_left hbad_le_delta 1
      let e : Fin m ≃o split.foldB n := (split.foldB n).orderIsoOfFin rfl
      let Y : Ω → Fin m → Z := fun ω j => S_iid.Z (e j).val ω
      have hY_meas : Measurable Y := by
        apply measurable_pi_lambda
        intro j
        exact S_iid.meas (e j).val
      have hY_law : μ.map Y = Measure.pi (fun _ : Fin m => P_Z) := by
        let YB : Ω → split.foldB n → Z := fun ω i => S_iid.Z i.val ω
        let T : (split.foldB n → Z) ≃ᵐ (Fin m → Z) :=
          MeasurableEquiv.piCongrLeft (fun _ : Fin m => Z) e.symm.toEquiv
        have hY_eq : Y = T ∘ YB := by
          funext ω j
          simpa [Y, YB, T] using
            (MeasurableEquiv.piCongrLeft_apply_apply (e := e.symm.toEquiv)
              (β := fun _ : Fin m => Z)
              (x := fun i : split.foldB n => S_iid.Z i.val ω) (i := e j)).symm
        rw [hY_eq, ← Measure.map_map T.measurable
          (measurable_pi_lambda YB fun i => S_iid.meas i.val)]
        · rw [Causalean.Stat.oneShot_iid S_iid split n]
          simpa [T] using Measure.pi_map_piCongrLeft (e := e.symm.toEquiv)
            (β := fun _ : Fin m => Z) (μ := fun _ : Fin m => P_Z)
      refine ⟨Y ⁻¹' EZ, hEZ_meas.preimage hY_meas, ?_, ?_⟩
      · rw [← Measure.map_apply hY_meas hEZ_meas, hY_law]
        exact hEZ_prob
      · intro ω hω θ hθ
        let θs : S.Θ_set := ⟨θ, hθ⟩
        have hgood : ¬ (2 • rademacherComplexity m fθ P_Z id + ε ≤
            uniformDeviation m fθ P_Z id (id ∘ Y ω)) := by
          simpa [EZ, badZ] using hω
        have hdev_lt : uniformDeviation m fθ P_Z id (Y ω) < 2 * R n + ε := by
          have hnot : uniformDeviation m fθ P_Z id (Y ω) <
              2 • rademacherComplexity m fθ P_Z id + ε := by
            rw [not_le] at hgood
            simpa using hgood
          have hrad_two : 2 • rademacherComplexity m fθ P_Z id + ε ≤ 2 * R n + ε := by
            simpa [two_nsmul] using
              add_le_add_right
                (mul_le_mul_of_nonneg_left hrad_full_le (by norm_num : (0 : ℝ) ≤ 2)) ε
          exact hnot.trans_le hrad_two
        have hpoint_le_dev :
            |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => fθ θs (Y ω k))
              - P_Z[fun z => fθ θs (id z)]|
              ≤ uniformDeviation m fθ P_Z id (Y ω) := by
          dsimp [uniformDeviation]
          apply le_ciSup (f := fun i : S.Θ_set =>
            |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => fθ i (Y ω k))
              - P_Z[fun z => fθ i (id z)]|)
          rw [bddAbove_def]
          use 4 * b
          intro y hy
          rcases hy with ⟨θ', rfl⟩
          have hsample :
              |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => fθ θ' (Y ω k))| ≤
                2 * b := by
            calc
              _ = (m : ℝ)⁻¹ * |Finset.univ.sum fun k : Fin m => fθ θ' (Y ω k)| := by
                rw [abs_mul, abs_of_nonneg]
                exact inv_nonneg.mpr (Nat.cast_nonneg _)
              _ ≤ (m : ℝ)⁻¹ * (Finset.univ.sum fun _ : Fin m => 2 * b) := by
                apply mul_le_mul_of_nonneg_left
                · exact Finset.abs_sum_le_sum_abs _ _ |>.trans
                    (Finset.sum_le_sum fun k _ => hf_bdd θ' (Y ω k))
                · positivity
              _ = 2 * b := by
                simp [m]
                field_simp [hm_pos.ne']
          have hmean : |P_Z[fun z => fθ θ' (id z)]| ≤ 2 * b := by
            calc
              _ ≤ ∫ z, |fθ θ' z| ∂P_Z := abs_integral_le_integral_abs
              _ ≤ ∫ _z, 2 * b ∂P_Z := by
                apply integral_mono
                · exact Integrable.of_bound ((hf_meas θ').abs.aestronglyMeasurable) (2 * b)
                    (by
                      filter_upwards with z
                      simpa [Real.norm_eq_abs] using hf_bdd θ' z)
                · exact integrable_const (2 * b)
                · intro z
                  exact hf_bdd θ' z
              _ = 2 * b := by simp
          calc
            |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => fθ θ' (Y ω k))
                - P_Z[fun z => fθ θ' (id z)]|
                ≤ |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => fθ θ' (Y ω k))|
                    + |P_Z[fun z => fθ θ' (id z)]| := abs_sub _ _
            _ ≤ 4 * b := by linarith
        have hcenter_abs :
            |(empRiskFoldB S S_iid split n ω θ g
                - empRiskFoldB S S_iid split n ω S.θ₀ g)
              - (S.L θ g - S.L S.θ₀ g)| ≤ 2 * R n + ε := by
          have hsum_reindex :
              (Finset.univ.sum fun k : Fin m => fθ θs (Y ω k)) =
                ∑ i ∈ split.foldB n,
                  (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g) := by
            have hsum_subtype :
                (Finset.univ.sum fun k : Fin m => fθ θs (Y ω k)) =
                  ∑ i : split.foldB n,
                    (S.ℓ (S_iid.Z i.val ω) θ g - S.ℓ (S_iid.Z i.val ω) S.θ₀ g) :=
              Fintype.sum_equiv e.toEquiv (fun k => fθ θs (Y ω k))
                (fun i : split.foldB n =>
                  S.ℓ (S_iid.Z i.val ω) θ g - S.ℓ (S_iid.Z i.val ω) S.θ₀ g)
                (by intro k; rfl)
            have hsum_attach :
                (∑ i : split.foldB n,
                    (S.ℓ (S_iid.Z i.val ω) θ g - S.ℓ (S_iid.Z i.val ω) S.θ₀ g)) =
                  ∑ i ∈ split.foldB n,
                    (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g) := by
              simpa using Finset.sum_attach (s := split.foldB n)
                (f := fun i =>
                  S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g)
            exact hsum_subtype.trans hsum_attach
          have hmean_eq : (∫ z, fθ θs z ∂P_Z) = S.L θ g - S.L S.θ₀ g := by
            have hintθ : Integrable (fun z => S.ℓ z θ g) P_Z :=
              Integrable.of_bound (S.ℓ_meas θ g).aestronglyMeasurable b
                (by
                  filter_upwards with z
                  simpa [Real.norm_eq_abs] using hg_bdd z θ hθ)
            have hint0 : Integrable (fun z => S.ℓ z S.θ₀ g) P_Z :=
              Integrable.of_bound (S.ℓ_meas S.θ₀ g).aestronglyMeasurable b
                (by
                  filter_upwards with z
                  simpa [Real.norm_eq_abs] using hg_bdd z S.θ₀ S.θ₀_mem)
            change (∫ z, S.ℓ z θ g - S.ℓ z S.θ₀ g ∂P_Z) =
              S.L θ g - S.L S.θ₀ g
            change (∫ z, S.ℓ z θ g - S.ℓ z S.θ₀ g ∂P_Z) =
              (∫ z, S.ℓ z θ g ∂P_Z) - (∫ z, S.ℓ z S.θ₀ g ∂P_Z)
            exact integral_sub hintθ hint0
          have hpoint := hpoint_le_dev.trans (le_of_lt hdev_lt)
          have hpoint' :
              |(m : ℝ)⁻¹ *
                    (∑ i ∈ split.foldB n,
                      (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g))
                  - (S.L θ g - S.L S.θ₀ g)| ≤ 2 * R n + ε := by
            simpa [hmean_eq, hsum_reindex] using hpoint
          convert hpoint' using 1
          simp [empRiskFoldB, m]
          ring_nf
        have hmain :
            (S.L θ g - S.L S.θ₀ g)
              - (empRiskFoldB S S_iid split n ω θ g
                  - empRiskFoldB S S_iid split n ω S.θ₀ g)
              ≤ 2 * R n + ε := by
          have := neg_le_abs ((empRiskFoldB S S_iid split n ω θ g
                - empRiskFoldB S S_iid split n ω S.θ₀ g)
              - (S.L θ g - S.L S.θ₀ g))
          linarith
        have hρsq_eq :
            (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 =
              2 * R n + ε := by
          have hradicand :
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                 Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))
                = 2 * R n + 2 * b *
                    Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card) := by
            rw [if_neg hm0]
          have hnonneg :
              0 ≤ (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                 Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) := by
            have : 0 ≤ 2 * R n + ε := by
              nlinarith [hε_nonneg, hR_nonneg]
            rw [hradicand]
            simpa [ε, m] using this
          rw [Real.sq_sqrt hnonneg]
          rw [hradicand]
        have hρ_nonneg :
            0 ≤ Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) :=
          Real.sqrt_nonneg _
        have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
        calc
          (S.L θ g - S.L S.θ₀ g)
              - (empRiskFoldB S S_iid split n ω θ g
                  - empRiskFoldB S S_iid split n ω S.θ₀ g)
              ≤ 2 * R n + ε := hmain
          _ = (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := hρsq_eq.symm
          _ ≤ Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) * ‖θ - S.θ₀‖
              + (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := by
            nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg]

end OrthogonalLearning
end Estimation
end Causalean

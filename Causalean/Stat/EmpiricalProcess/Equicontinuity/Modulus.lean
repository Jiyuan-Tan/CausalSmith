/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Class-level asymptotic equicontinuity and the `StochEquicontAt` reduction

`Causalean.Stat.StochEquicontAt` (`Equicontinuity/StochEquicont.lean`) is the
empirical-process hypothesis fed to the `Z`-estimator / GMM CLTs.  As literally
stated it is an *estimator-indexed* property: it conditions on the random event
`{‖θn − θ₀‖ < δ}` and asks the centered gap `R_n` evaluated **at the random
estimator** `θn` to vanish in probability.  That statement is only true when
`θn →_p θ₀`; it bundles together two genuinely separate ingredients:

* a **class-level** Donsker / asymptotic-equicontinuity property of the score
  family `{ψ(θ,·) − ψ(θ₀,·) : ‖θ − θ₀‖ < δ}`, which does **not** depend on `θn`
  (here: `AsymptoticEquicont`);
* **consistency** `θn →_p θ₀`.

This file isolates the first ingredient as `AsymptoticEquicont` and proves the
reduction

    AsymptoticEquicont  +  consistency  ⟹  StochEquicontAt.

This is the empirical-process step of van der Vaart (1998), Lemma 19.24: the
class-level property is separated from the elementary union-bound argument
that evaluates it at a consistent estimator.  The deterministic-curve special
case `empProcVec_isLittleOp_of_L2` is proved here from a second-moment bound.
The sibling `LipschitzParametric.lean` supplies a continuum finite-dimensional
Lipschitz instance using covering entropy, Dudley chaining, symmetrization, and
truncation.  A general bracketing-entropy provider remains outside this file.

References: van der Vaart (1998), §19.4, Lemma 19.24; Theorem 5.41.
-/

module
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.Process
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.SecondMoment
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.StochEquicont
public import Causalean.Stat.Limit.Convergence

/-! # Asymptotic Equicontinuity Modulus

This file separates class-level asymptotic equicontinuity of an empirical
process from consistency of a random estimator.  It defines
`AsymptoticEquicont`, proves `empProcVec_atEstimator_tendsto_zero`, packages the
reduction `stochEquicontAt_of_asymptoticEquicont`, and supplies the deterministic
curve witness `empProcVec_isLittleOp_of_L2` from second-moment control.
`LipschitzParametric.lean` supplies the concrete continuum Lipschitz provider;
this file does not develop a general bracketing-entropy criterion. -/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {Θ V : Type*} [NormedAddCommGroup Θ]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- [Class-level asymptotic equicontinuity](goal) means that every fixed
empirical-process tolerance is met uniformly on a sufficiently small parameter
ball, with arbitrarily small eventual sampling measure.  It concerns [a score
family](hyp:ψ) around [a reference parameter](hyp:θ₀), sampled by [an i.i.d.
sequence](hyp:S) under [population and sample-space
measures](hyp:P,μ).

For every `ε > 0` and positive measure tolerance `η` there is a ball radius
`δ > 0` such that, eventually in `n`, the sampling measure of the event that the centered
empirical process `Gₙ(ψ(θ,·) − ψ(θ₀,·))` exceeds `ε` for **some** `θ` in the
`δ`-ball is at most `η`:

    ∀ ε > 0, ∀ η > 0, ∃ δ > 0, ∀ᶠ n,
      μ {ω | ∃ θ, ‖θ − θ₀‖ < δ ∧ ε < ‖Gₙ(ψ(θ,·) − ψ(θ₀,·))(ω)‖} ≤ η.

When both measures are probability measures, this is the standard double-limit
asymptotic equicontinuity
`lim_{δ→0} limsup_n P*(sup_{‖θ−θ₀‖<δ} |Gₙ| > ε) = 0` (van der Vaart 1998,
§19.2), phrased with an existential over `θ` rather than a (possibly
non-measurable) supremum so that the outer-measure bookkeeping is automatic.
Unlike `StochEquicontAt`, it makes no reference to an estimator sequence: it is
a property of the function class and the sample alone, and it is what
bracketing-entropy / Donsker theorems actually establish. -/
def AsymptoticEquicont (ψ : Θ → X → V) (θ₀ : Θ) (P : Measure X)
    (μ : Measure Ω) (S : IIDSample Ω X μ P) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ n in atTop,
      μ {ω | ∃ θ : Θ, ‖θ - θ₀‖ < δ ∧
          ε < ‖S.empProcVec (fun z => ψ θ z - ψ θ₀ z) n ω‖}
        ≤ ENNReal.ofReal η

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Empirical process at the estimator vanishes.** If [the score family `ψ` is asymptotically
equicontinuous at `θ₀` along the i.i.d. sample `S`](hyp:hAEC) and [`θn` is a sequence of
estimators consistent for `θ₀`](hyp:hConsistent), then for [any fixed tolerance `ε > 0`](hyp:hε),
[the centered empirical process of the score gap `ψ(θn,·) − ψ(θ₀,·)`, evaluated at the random
estimator `θn`, namely `Gₙ(ψ(θn,·) − ψ(θ₀,·))`, exceeds `ε` on an
event whose sampling measure tends to zero, without restricting the estimator
to a shrinking neighborhood of `θ₀`](goal).

This is the substantive conclusion; `StochEquicontAt` is an immediate corollary.
The proof is the textbook union bound: split on `{‖θn − θ₀‖ ≥ δ}` (small by
consistency) and `{‖θn − θ₀‖ < δ}` (on which the gap is witnessed by `θ = θn`,
so the event sits inside the equicontinuity event). -/
theorem empProcVec_atEstimator_tendsto_zero
    (ψ : Θ → X → V) (θ₀ : Θ)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → Θ)
    (hAEC : AsymptoticEquicont ψ θ₀ P μ S)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun n =>
        μ {ω | ε < ‖S.empProcVec (fun z => ψ (θn n ω) z - ψ θ₀ z) n ω‖})
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro γ hγ
  by_cases hγtop : γ = ⊤
  · filter_upwards with n; simp [hγtop]
  have hγpos : 0 < γ.toReal := ENNReal.toReal_pos (ne_of_gt hγ) hγtop
  set η : ℝ := γ.toReal / 2 with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨δ, hδpos, hAEC_event⟩ := hAEC ε hε η hηpos
  have hδhalf : 0 < δ / 2 := by positivity
  have hCons_event :=
    (ENNReal.tendsto_nhds_zero.mp (hConsistent (δ / 2) hδhalf))
      (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hηpos)
  have hsum_le : ENNReal.ofReal η + ENNReal.ofReal η ≤ γ := by
    rw [← ENNReal.ofReal_add hηpos.le hηpos.le]
    have : η + η = γ.toReal := by rw [hη]; ring
    rw [this, ENNReal.ofReal_toReal hγtop]
  filter_upwards [hAEC_event, hCons_event] with n hAEC_n hCons_n
  -- `{ε < ‖R_n‖} ⊆ {δ/2 < ‖θn − θ₀‖} ∪ {∃ θ, ‖θ − θ₀‖ < δ ∧ ε < ‖Gₙ‖}`
  have hsub :
      {ω | ε < ‖S.empProcVec (fun z => ψ (θn n ω) z - ψ θ₀ z) n ω‖}
        ⊆ {ω | δ / 2 < ‖θn n ω - θ₀‖}
          ∪ {ω | ∃ θ : Θ, ‖θ - θ₀‖ < δ ∧
              ε < ‖S.empProcVec (fun z => ψ θ z - ψ θ₀ z) n ω‖} := by
    intro ω hω
    by_cases hθ : ‖θn n ω - θ₀‖ < δ
    · exact Or.inr ⟨θn n ω, hθ, hω⟩
    · refine Or.inl ?_
      have hδle : δ ≤ ‖θn n ω - θ₀‖ := not_lt.mp hθ
      change δ / 2 < ‖θn n ω - θ₀‖
      linarith
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  exact le_trans (add_le_add hCons_n hAEC_n) hsum_le

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Reduction: `StochEquicontAt` from class-level equicontinuity + consistency.** If [the
score family `ψ` is asymptotically equicontinuous at `θ₀` along the i.i.d. sample
`S`](hyp:hAEC) and [`θn` is a sequence of estimators consistent for `θ₀`](hyp:hConsistent),
then [the pair `(ψ, θ₀)` satisfies the stochastic-equicontinuity-at-the-estimator condition
`StochEquicontAt` along `S` and `θn`](goal).

The Z-estimator and GMM CLTs (`zEstimator_asymLinear`, `oracleGMM_asymLinear`)
take `StochEquicontAt` as a hypothesis.  This theorem discharges it from the
two clean ingredients it actually decomposes into: the Donsker / asymptotic-
equicontinuity property of the score family (`AsymptoticEquicont`, independent
of `θn`) and consistency of `θn` in sampling measure. Any `δ` works since
`empProcVec_atEstimator_tendsto_zero` already gives the *unconditional* vanishing
of the gap. -/
theorem stochEquicontAt_of_asymptoticEquicont
    (ψ : Θ → X → V) (θ₀ : Θ)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → Θ)
    (hAEC : AsymptoticEquicont ψ θ₀ P μ S)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0)) :
    StochEquicontAt ψ θ₀ P μ S θn := by
  intro ε hε
  refine ⟨1, one_pos, ?_⟩
  have hgap := empProcVec_atEstimator_tendsto_zero ψ θ₀ S θn hAEC hConsistent ε hε
  refine ENNReal.tendsto_nhds_zero.mpr ?_
  intro γ hγ
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hgap) γ hγ] with n hn
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  exact hω.2

omit [NormedAddCommGroup Θ] in
/-- **Deterministic-curve equicontinuity (non-vacuousness witness).** Suppose that for every
parameter value `θ`, [the score gap `ψ(θ,·) − ψ(θ₀,·)` is measurable and square-integrable
under `P`](hyp:hψ_meas,hψ_L2). Along a deterministic parameter sequence `θn` whose score
perturbation [shrinks in `L²(P)`: $\int\|\psi(\theta_n,\cdot)-\psi(\theta_0,\cdot)\|^2\,dP \to
0$](hyp:hmod), [the centered empirical-process gap `Gₙ(ψ(θn,·) − ψ(θ₀,·))` is $o_p(1)$](goal),
with no chaining and no consistency hypothesis: it is a direct consequence of the
uniform-in-`n` Chebyshev bound `empProcVec_chebyshev`.

This is the base case of asymptotic equicontinuity (the parameter is moved along
a fixed curve rather than over a whole ball) and certifies that the
`AsymptoticEquicont` machinery is satisfiable.  The genuinely uniform
(sup-over-ball) statement is what requires bracketing-entropy / chaining. -/
theorem empProcVec_isLittleOp_of_L2 [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (ψ : Θ → X → V) (θ₀ : Θ) (θn : ℕ → Θ)
    (S : IIDSample Ω X μ P)
    (hψ_meas : ∀ θ, Measurable (fun x => ψ θ x - ψ θ₀ x))
    (hψ_L2 : ∀ θ, MemLp (fun x => ψ θ x - ψ θ₀ x) 2 P)
    (hmod : Tendsto (fun n => ∫ x, ‖ψ (θn n) x - ψ θ₀ x‖ ^ 2 ∂P) atTop (𝓝 0)) :
    IsLittleOp
      (fun n ω => ‖S.empProcVec (fun z => ψ (θn n) z - ψ θ₀ z) n ω‖)
      (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  have hhalfsq : (0 : ℝ) < (ε / 2) ^ 2 := by positivity
  have hbound : ∀ n,
      μ {ω | ε ≤ ‖S.empProcVec (fun z => ψ (θn n) z - ψ θ₀ z) n ω‖}
        ≤ ENNReal.ofReal (∫ x, ‖ψ (θn n) x - ψ θ₀ x‖ ^ 2 ∂P) /
            ENNReal.ofReal ((ε / 2) ^ 2) := by
    intro n
    refine (measure_mono ?_).trans
      (empProcVec_chebyshev S (fun z => ψ (θn n) z - ψ θ₀ z)
        (hψ_meas (θn n)) (hψ_L2 (θn n)) n hhalf)
    intro ω hω
    change ε ≤ ‖S.empProcVec (fun z => ψ (θn n) z - ψ θ₀ z) n ω‖ at hω
    change ε / 2 < ‖S.empProcVec (fun z => ψ (θn n) z - ψ θ₀ z) n ω‖
    linarith
  have hdiv : Tendsto (fun n => ENNReal.ofReal (∫ x, ‖ψ (θn n) x - ψ θ₀ x‖ ^ 2 ∂P)
      / ENNReal.ofReal ((ε / 2) ^ 2)) atTop (𝓝 0) := by
    have hreal : Tendsto
        (fun n => (∫ x, ‖ψ (θn n) x - ψ θ₀ x‖ ^ 2 ∂P) / (ε / 2) ^ 2)
        atTop (𝓝 0) := by
      simpa using hmod.div_const ((ε / 2) ^ 2)
    have heq : ∀ n, ENNReal.ofReal (∫ x, ‖ψ (θn n) x - ψ θ₀ x‖ ^ 2 ∂P)
        / ENNReal.ofReal ((ε / 2) ^ 2) =
          ENNReal.ofReal
            ((∫ x, ‖ψ (θn n) x - ψ θ₀ x‖ ^ 2 ∂P) / (ε / 2) ^ 2) := fun n =>
      (ENNReal.ofReal_div_of_pos hhalfsq).symm
    simp_rw [heq]
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
    (fun _ => zero_le) (fun n => by simpa only [mul_one, norm_norm] using hbound n)

end Causalean.Stat

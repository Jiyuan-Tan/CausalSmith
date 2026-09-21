/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.PO.Assumptions.ConsistencyLemmas
public import Causalean.PO.Analysis.Regression
public import Causalean.PO.ID.Exact.RDD.RDDLimits

/-! # Sharp Regression Discontinuity

This file formalizes sharp regression-discontinuity identification in the
potential-outcome framework. Under consistency, the deterministic cutoff rule,
local support of the running variable on both sides of the cutoff, and
continuity of the treatment-specific regressions, the cutoff effect equals the
difference between the right and left limits of the observed outcome regression.

The proof reduces the sharp cutoff to half-line agreement between observable
and potential-outcome regressions, then invokes the shared one-sided limit
engine for regression-discontinuity designs. -/

@[expose] public section

namespace Causalean
namespace PO

open Filter MeasureTheory
open scoped Topology

/-- **Data layout for sharp regression discontinuity.** The system records [a real-valued
running variable](hyp:Xvar), [a binary treatment](hyp:Dvar), [a real outcome](hyp:Yvar), and
[a cutoff](hyp:c), with [distinct outcome and treatment nodes](hyp:hYD). The deterministic
assignment rule and continuity and support conditions that make the design sharp are imposed
separately by `Assumptions`; they are not properties of this bare variable bundle. -/
structure POSharpRDDSystem (P : POSystem) where
  /-- Running (forcing) variable `X`. -/
  Xvar : POVar P ℝ
  /-- Binary treatment `D` (deterministic given `X` at the cutoff). -/
  Dvar : POVar P Bool
  /-- Real outcome `Y`. -/
  Yvar : POVar P ℝ
  /-- Cutoff value of the running variable. -/
  c : ℝ
  hYD : Yvar.v ≠ Dvar.v

namespace POSharpRDDSystem

variable {P : POSystem} (S : POSharpRDDSystem P)

/-- The [observed running variable](goal) in [a sharp regression-discontinuity
design](hyp:S) [records each unit's realized forcing score](step:1), whose position around
the cutoff determines treatment. -/
noncomputable def factualX : P.Ω → ℝ := S.Xvar.factual

/-- The [observed treatment](goal) in [a sharp regression-discontinuity design](hyp:S)
[records each unit's realized side-of-cutoff assignment](step:1). -/
noncomputable def factualD : P.Ω → Bool := S.Dvar.factual

/-- The [observed outcome](goal) in [a sharp regression-discontinuity design](hyp:S)
[records each unit's realized real-valued response](step:1). -/
noncomputable def factualY : P.Ω → ℝ := S.Yvar.factual

/-- The [treatment-specific potential outcome](goal) in [a sharp
regression-discontinuity design](hyp:S) [records each unit's response if assigned the
selected treatment](step:1), with [that treatment level](hyp:d) defining one side of the
cutoff effect. -/
noncomputable def YofD (d : Bool) : P.Ω → ℝ := S.Yvar.cfUnder S.Dvar d

/-- [The running variable in a sharp regression-discontinuity design](hyp:S) is
[measurable, so cutoff neighborhoods and the running-variable law are valid](goal). -/
@[fun_prop]
lemma measurable_factualX : Measurable S.factualX := S.Xvar.measurable_factual
/-- [Treatment in a sharp regression-discontinuity design](hyp:S) is [measurable, so
the two cutoff-assigned groups define valid events](goal). -/
@[fun_prop]
lemma measurable_factualD : Measurable S.factualD := S.Dvar.measurable_factual
/-- [The outcome in a sharp regression-discontinuity design](hyp:S) is [measurable,
so its regression on the running variable is well-defined](goal). -/
@[fun_prop]
lemma measurable_factualY : Measurable S.factualY := S.Yvar.measurable_factual
/-- In [a sharp regression-discontinuity design](hyp:S), [the potential outcome under
a treatment level](hyp:d) is [measurable, so its cutoff regression is well-defined](goal). -/
@[fun_prop]
lemma measurable_YofD (d : Bool) : Measurable (S.YofD d) :=
  S.Yvar.measurable_cfUnder S.Dvar d

/-- The [observed treatment group](goal) in [a sharp regression-discontinuity
design](hyp:S) [collects units assigned the selected treatment level](step:1), with
[that level](hyp:d) distinguishing the two cutoff sides. -/
def dEvent (d : Bool) : Set P.Ω := S.Dvar.event d

/-- In [a sharp regression-discontinuity design](hyp:S), [an observed treatment
level](hyp:d) defines [a measurable event suitable for consistency arguments](goal). -/
lemma measurableSet_dEvent (d : Bool) : MeasurableSet (S.dEvent d) :=
  by simpa [dEvent] using S.Dvar.measurableSet_event d

/-- **Sharp RDD assumption bundle** (`def:po-sharp-rdd-assumptions`). For a sharp
regression-discontinuity system, this packages [consistency (SUTVA)](hyp:consistency) and [the
deterministic cutoff rule: the treatment indicator agrees almost surely with whether the running
variable has reached the cutoff](hyp:sharpCutoff). It supplies treatment-specific latent
regression representatives `mu` and an observable outcome regression representative `nu`, each
[certified as a genuine regression function of the corresponding response on the running
variable](hyp:mu_isReg,nu_isReg), with the latent representatives [continuous at the
cutoff](hyp:mu_continuousAt); it also assumes [the running variable has positive local
probability mass on both sides of the cutoff](hyp:support_right,support_left) and [the observable
outcome regression has well-defined one-sided limits at the
cutoff](hyp:nu_right_limit_exists,nu_left_limit_exists).

The continuity clause is asserted on the treatment-specific regression
representatives `μ_d` at the cutoff, matching the textbook statement.  Two-sided
local support is encoded by demanding that every one-sided open neighborhood
of `c` carries positive `(P.μ.map X)`-mass; this is the formal counterpart of
"`X` has support on both sides of the cutoff arbitrarily close to `c`". -/
structure Assumptions (S : POSharpRDDSystem P) where
  consistency : P.Consistency
  sharpCutoff : ∀ᵐ ω ∂P.μ, S.factualD ω ↔ S.c ≤ S.factualX ω
  mu : Bool → ℝ → ℝ
  nu : ℝ → ℝ
  mu_isReg : ∀ d, IsRegressionFunction P.μ S.factualX (S.YofD d) (mu d)
  nu_isReg : IsRegressionFunction P.μ S.factualX S.factualY nu
  mu_continuousAt : ∀ d, ContinuousAt (mu d) S.c
  support_right : ∀ ε > (0 : ℝ),
    (P.μ.map S.factualX) (Set.Ioo S.c (S.c + ε)) ≠ 0
  support_left : ∀ ε > (0 : ℝ),
    (P.μ.map S.factualX) (Set.Ioo (S.c - ε) S.c) ≠ 0
  nu_right_limit_exists : ∃ L : ℝ, Tendsto nu (𝓝[>] S.c) (𝓝 L)
  nu_left_limit_exists : ∃ L : ℝ, Tendsto nu (𝓝[<] S.c) (𝓝 L)

/-- The [cutoff-local treatment effect](goal) for [a sharp regression-discontinuity
design](hyp:S) under [the sharp-RDD assumptions](hyp:hA) [contrasts the treated and
untreated potential-outcome regression representatives at the cutoff](step:1).

By definition it is the difference of the treatment-specific regression representatives at
the cutoff. In the standard reading of `μ_d c = E[Y(d) | X = c]`, this is
`E[Y(1) - Y(0) | X = c]`. -/
noncomputable def tau_RDD (hA : S.Assumptions) : ℝ :=
  hA.mu true S.c - hA.mu false S.c

/-- The [observable outcome regression's right-hand cutoff limit](goal) for [a sharp
regression-discontinuity design](hyp:S) under [the sharp-RDD assumptions](hyp:hA) [selects
the limiting outcome level approached from above the cutoff](step:1).

The right-hand limit `lim_{x ↓ c} ν(x)` chosen from the existence witness
of `Assumptions`. -/
noncomputable def nu_right_limit (hA : S.Assumptions) : ℝ :=
  Classical.choose hA.nu_right_limit_exists

/-- The [observable outcome regression's left-hand cutoff limit](goal) for [a sharp
regression-discontinuity design](hyp:S) under [the sharp-RDD assumptions](hyp:hA) [selects
the limiting outcome level approached from below the cutoff](step:1).

The left-hand limit `lim_{x ↑ c} ν(x)` chosen from the existence witness
of `Assumptions`. -/
noncomputable def nu_left_limit (hA : S.Assumptions) : ℝ :=
  Classical.choose hA.nu_left_limit_exists

/-- Under [the sharp-RDD assumptions](hyp:hA), [the selected right-hand limit for the
design](hyp:S) [is attained by the observable outcome regression as the running variable
approaches the cutoff from above](goal). -/
lemma tendsto_nu_right_limit (hA : S.Assumptions) :
    Tendsto hA.nu (𝓝[>] S.c) (𝓝 (S.nu_right_limit hA)) :=
  Classical.choose_spec hA.nu_right_limit_exists

/-- Under [the sharp-RDD assumptions](hyp:hA), [the selected left-hand limit for the
design](hyp:S) [is attained by the observable outcome regression as the running variable
approaches the cutoff from below](goal). -/
lemma tendsto_nu_left_limit (hA : S.Assumptions) :
    Tendsto hA.nu (𝓝[<] S.c) (𝓝 (S.nu_left_limit hA)) :=
  Classical.choose_spec hA.nu_left_limit_exists

/-! ### Bridge from sharp cutoff + consistency to slice-level identities -/

private lemma factualY_eq_YofD_on_dEvent
    (hC : P.Consistency) (d : Bool) :
    ∀ ω ∈ S.dEvent d, S.factualY ω = S.YofD d ω := by
  intro ω hω
  exact (POVar.cf_eq_factual_on_event hC S.Yvar S.Dvar d S.hYD hω).symm

private lemma factualY_eq_YofD_true_ae_restrict_Ici
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    S.factualY =ᵐ[P.μ.restrict (S.factualX ⁻¹' A)] S.YofD true := by
  have hslice : MeasurableSet (S.factualX ⁻¹' A) :=
    S.measurable_factualX hAmeas
  filter_upwards [ae_restrict_of_ae hA.sharpCutoff, self_mem_ae_restrict hslice]
    with ω hsharp hωA
  have hx : S.c ≤ S.factualX ω := hAsub hωA
  have hDprop : S.factualD ω := hsharp.mpr hx
  have hD : S.factualD ω = true := by
    cases hDω : S.factualD ω <;> simp_all
  exact S.factualY_eq_YofD_on_dEvent hA.consistency true ω hD

private lemma factualY_eq_YofD_false_ae_restrict_Iio
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    S.factualY =ᵐ[P.μ.restrict (S.factualX ⁻¹' A)] S.YofD false := by
  have hslice : MeasurableSet (S.factualX ⁻¹' A) :=
    S.measurable_factualX hAmeas
  filter_upwards [ae_restrict_of_ae hA.sharpCutoff, self_mem_ae_restrict hslice]
    with ω hsharp hωA
  have hx : S.factualX ω < S.c := hAsub hωA
  have hnotD : ¬ S.factualD ω := by
    intro hD
    exact (not_le_of_gt hx) (hsharp.mp hD)
  have hD : S.factualD ω = false := by
    cases hDω : S.factualD ω <;> simp_all
  exact S.factualY_eq_YofD_on_dEvent hA.consistency false ω hD

/-! ### Slice-level integral bridges between `ν` and `μ_d` -/

/-- Under [the sharp-RDD assumptions](hyp:hA), [the observed and treated latent outcome
regressions have the same population integral on a right-side slice](goal) for [the
design](hyp:S), provided [the slice lies weakly above the cutoff](hyp:hAsub) and [is
measurable](hyp:hAmeas). -/
private lemma regression_integral_bridge_right
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, hA.nu (S.factualX ω) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, hA.mu true (S.factualX ω) ∂P.μ := by
  calc
    (∫ ω in S.factualX ⁻¹' A, hA.nu (S.factualX ω) ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' A, S.factualY ω ∂P.μ :=
          (hA.nu_isReg.integral_preimage_eq A hAmeas).symm
    _ = ∫ ω in S.factualX ⁻¹' A, S.YofD true ω ∂P.μ :=
          integral_congr_ae
            (S.factualY_eq_YofD_true_ae_restrict_Ici hA hAsub hAmeas)
    _ = ∫ ω in S.factualX ⁻¹' A, hA.mu true (S.factualX ω) ∂P.μ :=
          (hA.mu_isReg true).integral_preimage_eq A hAmeas

/-- Under [the sharp-RDD assumptions](hyp:hA), [the observed and untreated latent outcome
regressions have the same population integral on a left-side slice](goal) for [the
design](hyp:S), provided [the slice lies below the cutoff](hyp:hAsub) and [is
measurable](hyp:hAmeas). -/
private lemma regression_integral_bridge_left
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, hA.nu (S.factualX ω) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, hA.mu false (S.factualX ω) ∂P.μ := by
  calc
    (∫ ω in S.factualX ⁻¹' A, hA.nu (S.factualX ω) ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' A, S.factualY ω ∂P.μ :=
          (hA.nu_isReg.integral_preimage_eq A hAmeas).symm
    _ = ∫ ω in S.factualX ⁻¹' A, S.YofD false ω ∂P.μ :=
          integral_congr_ae
            (S.factualY_eq_YofD_false_ae_restrict_Iio hA hAsub hAmeas)
    _ = ∫ ω in S.factualX ⁻¹' A, hA.mu false (S.factualX ω) ∂P.μ :=
          (hA.mu_isReg false).integral_preimage_eq A hAmeas

/-! ### Pushforward integrability and integral identity -/

/-- [The running variable in a sharp regression-discontinuity design](hyp:S) is
[almost-everywhere measurable under the population law](goal), allowing regressions to
be pushed forward to its marginal distribution. -/
@[fun_prop]
lemma aemeasurable_factualX (S : POSharpRDDSystem P) :
    AEMeasurable S.factualX P.μ := S.measurable_factualX.aemeasurable

/-- Under [the sharp-RDD assumptions](hyp:hA), [the observed and treated latent
regressions have equal integrals under the running-variable law](goal) for [the
design](hyp:S), on [a slice weakly above the cutoff](hyp:hAsub) that [is
measurable](hyp:hAmeas). -/
private lemma setIntegral_pushforward_eq_right
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    (∫ x in A, hA.nu x ∂(P.μ.map S.factualX))
      = ∫ x in A, hA.mu true x ∂(P.μ.map S.factualX) := by
  have hnu :=
    setIntegral_map (μ := P.μ) (g := S.factualX) (f := hA.nu) hAmeas
      hA.nu_isReg.measurable.aestronglyMeasurable S.aemeasurable_factualX
  have hmu :=
    setIntegral_map (μ := P.μ) (g := S.factualX) (f := hA.mu true) hAmeas
      (hA.mu_isReg true).measurable.aestronglyMeasurable S.aemeasurable_factualX
  rw [hnu, hmu]
  exact S.regression_integral_bridge_right hA hAsub hAmeas

/-- Under [the sharp-RDD assumptions](hyp:hA), [the observed and untreated latent
regressions have equal integrals under the running-variable law](goal) for [the
design](hyp:S), on [a slice below the cutoff](hyp:hAsub) that [is
measurable](hyp:hAmeas). -/
private lemma setIntegral_pushforward_eq_left
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    (∫ x in A, hA.nu x ∂(P.μ.map S.factualX))
      = ∫ x in A, hA.mu false x ∂(P.μ.map S.factualX) := by
  have hnu :=
    setIntegral_map (μ := P.μ) (g := S.factualX) (f := hA.nu) hAmeas
      hA.nu_isReg.measurable.aestronglyMeasurable S.aemeasurable_factualX
  have hmu :=
    setIntegral_map (μ := P.μ) (g := S.factualX) (f := hA.mu false) hAmeas
      (hA.mu_isReg false).measurable.aestronglyMeasurable S.aemeasurable_factualX
  rw [hnu, hmu]
  exact S.regression_integral_bridge_left hA hAsub hAmeas

/-! ### A.e. agreement of `ν` and `μ_d` on the half-lines -/

/-- `ν` and `μ_1` agree `(P.μ.map X)`-almost everywhere on `Ici c`. -/
private lemma nu_eq_mu_true_ae_restrict_Ici (hA : S.Assumptions) :
    hA.nu =ᵐ[(P.μ.map S.factualX).restrict (Set.Ici S.c)] hA.mu true := by
  set π := P.μ.map S.factualX
  refine MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq
    hA.nu (hA.mu true)
    (hA.nu_isReg.integrable_pushforward).restrict
    ((hA.mu_isReg true).integrable_pushforward).restrict
    ?_
  intro s hs _
  simp_rw [Measure.restrict_restrict (μ := π) hs]
  exact S.setIntegral_pushforward_eq_right hA Set.inter_subset_right
    (hs.inter measurableSet_Ici)

/-- `ν` and `μ_0` agree `(P.μ.map X)`-almost everywhere on `Iio c`. -/
private lemma nu_eq_mu_false_ae_restrict_Iio (hA : S.Assumptions) :
    hA.nu =ᵐ[(P.μ.map S.factualX).restrict (Set.Iio S.c)] hA.mu false := by
  set π := P.μ.map S.factualX
  refine MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq
    hA.nu (hA.mu false)
    (hA.nu_isReg.integrable_pushforward).restrict
    ((hA.mu_isReg false).integrable_pushforward).restrict
    ?_
  intro s hs _
  simp_rw [Measure.restrict_restrict (μ := π) hs]
  exact S.setIntegral_pushforward_eq_left hA Set.inter_subset_right
    (hs.inter measurableSet_Iio)

/-! ### Limits of `ν` at the cutoff coincide with `μ_d c`

Thin wrappers around the generic `RDDLimits.oneSidedLimit_eq_*` engine. -/

/-- Any right-limit of `ν` at `c` coincides with `μ_1 c`. -/
theorem nu_right_limit_eq (hA : S.Assumptions) {L : ℝ}
    (h : Tendsto hA.nu (𝓝[>] S.c) (𝓝 L)) :
    L = hA.mu true S.c :=
  RDDLimits.oneSidedLimit_eq_right
    (S.nu_eq_mu_true_ae_restrict_Ici hA)
    (hA.mu_continuousAt true)
    hA.support_right
    h

/-- Any left-limit of `ν` at `c` coincides with `μ_0 c`. -/
theorem nu_left_limit_eq (hA : S.Assumptions) {L : ℝ}
    (h : Tendsto hA.nu (𝓝[<] S.c) (𝓝 L)) :
    L = hA.mu false S.c :=
  RDDLimits.oneSidedLimit_eq_left
    (S.nu_eq_mu_false_ae_restrict_Iio hA)
    (hA.mu_continuousAt false)
    hA.support_left
    h

/-! ### Sharp RDD identification — prop:po-sharp-rdd -/

/-- **Sharp RDD identification at the cutoff** (textbook form). For [a sharp-RDD
design](hyp:S), under [the sharp-RDD
assumption bundle — SUTVA consistency, deterministic treatment assignment `D = 1{X ≥ c}`
almost surely, regression-function representatives for the potential and observed outcomes,
continuity of the potential-outcome regression functions at the cutoff, positive local mass
of the running variable on each side of `c`, and existence of both one-sided limits of the
observed-outcome regression function at `c`](hyp:hA), [the cutoff-local treatment effect
equals the difference of the right- and left-hand limits of the observed-outcome regression
function at the cutoff](goal):

    τ_RDD(c) = lim_{x ↓ c} ν(x) - lim_{x ↑ c} ν(x).

The existence of both side limits is part of the `Assumptions` bundle. -/
theorem rdd_identification (hA : S.Assumptions) :
    S.tau_RDD hA = S.nu_right_limit hA - S.nu_left_limit hA := by
  rw [show S.nu_right_limit hA = hA.mu true S.c from
        S.nu_right_limit_eq hA (S.tendsto_nu_right_limit hA),
      show S.nu_left_limit hA = hA.mu false S.c from
        S.nu_left_limit_eq hA (S.tendsto_nu_left_limit hA)]
  rfl

end POSharpRDDSystem

end PO
end Causalean

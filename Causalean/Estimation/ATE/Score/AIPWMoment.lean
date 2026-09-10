/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW moment, influence function, and overlap-bounded nuisance space

* `aipwMoment z μ_fn e_fn θ`             — `m_AIPW` from `def:est-aipw-moment`.
* `ψ_AIPW S z`                           — influence function at the truth.
* `NuisanceVec γ`                        — pair `(μ_fn, e_fn)` with measurability,
                                           equipped with componentwise `AddCommGroup`
                                           and `Module ℝ` instances so it can be fed
                                           to `NeymanOrthogonal`.
* `H_ε ε`                                — legacy pointwise overlap-bounded realization set.
* `H_ε_aeL2 S ε`                         — source-shaped a.e./L² nuisance set.
* `aipwMomentFunctional`                 — `m_AIPW` viewed as `NuisanceVec γ → … → ℝ`.
-/

import Causalean.Estimation.ATE.Setup
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Causalean.Tactic.Attr

/-!
Defines the AIPW score objects used throughout the back-door ATE estimation
theory.

The main declarations are the observed-data projections `projX`, `projA`,
`projY`, the treatment indicator `indA`, the AIPW moment `aipwMoment`, the
truth influence function `ψ_AIPW`, and the nuisance vector space
`NuisanceVec`.  The file also defines the truth nuisance `η₀`, the legacy
pointwise overlap class `H_ε`, the source-shaped a.e./L² nuisance class
`H_ε_aeL2`, transport lemmas for its a.e. overlap condition, and
`aipwMomentFunctional` for use in orthogonality and DML theorems.
-/

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

namespace BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-! ## AIPW moment and influence function -/

/-- For a [covariate space](hyp:γ), the [covariate projection](goal) maps every observed triple $(x,a,y)$ to its covariate component $x$. -/
def projX : γ × Bool × ℝ → γ := fun z => z.1

/-- For a [covariate space](hyp:γ), the [treatment projection](goal) maps every observed triple $(x,a,y)$ to its binary treatment component $a$. -/
def projA : γ × Bool × ℝ → Bool := fun z => z.2.1

/-- For a [covariate space](hyp:γ), the [outcome projection](goal) maps every observed triple $(x,a,y)$ to its real-valued outcome component $y$. -/
def projY : γ × Bool × ℝ → ℝ := fun z => z.2.2

/-- The covariate projection of an observed data triple returns its covariate component. -/
@[causal_defs_simps]
lemma projX_apply (z : γ × Bool × ℝ) : projX z = z.1 := rfl

/-- The treatment projection of an observed data triple returns its treatment component. -/
@[causal_defs_simps]
lemma projA_apply (z : γ × Bool × ℝ) : projA z = z.2.1 := rfl

/-- The outcome projection of an observed data triple returns its outcome component. -/
@[causal_defs_simps]
lemma projY_apply (z : γ × Bool × ℝ) : projY z = z.2.2 := rfl

/-- For a [covariate space](hyp:γ) and [an observed covariate--treatment--outcome triple](hyp:z), the [real-valued treatment indicator](goal) equals one when the treatment is true and zero when it is false. -/
noncomputable def indA (z : γ × Bool × ℝ) : ℝ :=
  if projA z = true then 1 else 0

/-- For a [covariate space](hyp:γ), [an observed triple](hyp:z), [two treatment-specific outcome-regression functions](hyp:μ_fn), [a propensity-score function](hyp:e_fn), and [a real target value](hyp:θ), the [augmented inverse-probability-weighting moment](goal) is the outcome-regression contrast plus the treated inverse-propensity-weighted residual minus the control inverse-propensity-weighted residual, less the target value.

The AIPW moment `m_AIPW(η, z, θ)` from `def:est-aipw-moment`:

    μ(1,x) − μ(0,x) + (a/e(x))(y − μ(1,x)) − ((1−a)/(1−e(x)))(y − μ(0,x)) − θ. -/
noncomputable def aipwMoment
    (z : γ × Bool × ℝ) (μ_fn : Bool → γ → ℝ) (e_fn : γ → ℝ) (θ : ℝ) : ℝ :=
  (μ_fn true (projX z) - μ_fn false (projX z))
    + (indA z / e_fn (projX z)) * (projY z - μ_fn true (projX z))
    - ((1 - indA z) / (1 - e_fn (projX z))) * (projY z - μ_fn false (projX z))
    - θ

/-- The augmented inverse-probability-weighting moment at a data point, a nuisance pair, and a
parameter value is the contrast of the two outcome regressions at the covariate, plus the
treated inverse-propensity-weighted outcome residual, minus the control inverse-propensity-weighted
outcome residual, minus the parameter value. -/
@[causal_defs_simps]
lemma aipwMoment_eq
    (z : γ × Bool × ℝ) (μ_fn : Bool → γ → ℝ) (e_fn : γ → ℝ) (θ : ℝ) :
    aipwMoment z μ_fn e_fn θ =
      (μ_fn true (projX z) - μ_fn false (projX z))
        + (indA z / e_fn (projX z)) * (projY z - μ_fn true (projX z))
        - ((1 - indA z) / (1 - e_fn (projX z))) * (projY z - μ_fn false (projX z))
        - θ :=
  rfl

/-- For a [potential-outcome system](hyp:P) with a standard-Borel sample space and finite probability measure, a [measurable covariate space](hyp:γ), [a back-door estimation system](hyp:S), and [an observed triple](hyp:z), the [AIPW influence function at the system's true nuisance functions and average treatment effect](goal) is its AIPW moment evaluated at that triple. -/
noncomputable def ψ_AIPW (S : BackdoorEstimationSystem P γ)
    (z : γ × Bool × ℝ) : ℝ :=
  aipwMoment z S.μ_val S.e_val (S.θ₀)

/-! ## Overlap-bounded nuisance space `H_ε`

We package nuisance pairs `(μ_fn, e_fn)` together with their measurability as
`NuisanceVec`, with vector-space operations defined componentwise.  The
`AddCommGroup` and `Module ℝ` instances are wired to the underlying
function-valued operations from `Pi.instAddCommGroup` / `Pi.module`. -/

end BackdoorEstimationSystem

/-- **A pair of value-space AIPW nuisance functions**, used as the abstract nuisance space
for the AIPW moment functional: [a treatment-arm-indexed outcome regression](hyp:μ_fn) and
[a propensity score](hyp:e_fn), together with [their measurability](hyp:μ_meas,e_meas). -/
structure NuisanceVec (γ : Type*) [MeasurableSpace γ] where
  μ_fn : Bool → γ → ℝ
  e_fn : γ → ℝ
  μ_meas : ∀ b, Measurable (μ_fn b)
  e_meas : Measurable e_fn

attribute [fun_prop] NuisanceVec.μ_meas NuisanceVec.e_meas

namespace NuisanceVec

variable {γ : Type*} [MeasurableSpace γ]

/-- For [a measurable covariate space](hyp:γ), the [zero operation on AIPW nuisance vectors](goal)
sets [both treatment-specific outcome regressions and the propensity score to zero](step:1). -/
instance : Zero (NuisanceVec γ) where
  zero := ⟨fun _ _ => 0, fun _ => 0,
           fun _ => measurable_const, measurable_const⟩

/-- For [a measurable covariate space](hyp:γ), the [addition operation on AIPW nuisance vectors](goal)
is [componentwise addition of the treatment-specific outcome regressions and propensity score](step:1). -/
instance : Add (NuisanceVec γ) where
  add η η' :=
    ⟨fun b x => η.μ_fn b x + η'.μ_fn b x,
     fun x => η.e_fn x + η'.e_fn x,
     fun b => (η.μ_meas b).add (η'.μ_meas b),
     η.e_meas.add η'.e_meas⟩

/-- For [a measurable covariate space](hyp:γ), the [negation operation on AIPW nuisance vectors](goal)
[negates each treatment-specific outcome regression and the propensity score](step:1). -/
instance : Neg (NuisanceVec γ) where
  neg η :=
    ⟨fun b x => -η.μ_fn b x, fun x => -η.e_fn x,
     fun b => (η.μ_meas b).neg, η.e_meas.neg⟩

/-- For [a measurable covariate space](hyp:γ), the [subtraction operation on AIPW nuisance vectors](goal)
is [componentwise subtraction of the treatment-specific outcome regressions and propensity score](step:1). -/
instance : Sub (NuisanceVec γ) where
  sub η η' :=
    ⟨fun b x => η.μ_fn b x - η'.μ_fn b x,
     fun x => η.e_fn x - η'.e_fn x,
     fun b => (η.μ_meas b).sub (η'.μ_meas b),
     η.e_meas.sub η'.e_meas⟩

/-- For [a measurable covariate space](hyp:γ), the [real scalar-multiplication operation on AIPW nuisance vectors](goal)
[scales each treatment-specific outcome regression and the propensity score](step:1). -/
instance : SMul ℝ (NuisanceVec γ) where
  smul t η :=
    ⟨fun b x => t * η.μ_fn b x, fun x => t * η.e_fn x,
     fun b => measurable_const.mul (η.μ_meas b),
     measurable_const.mul η.e_meas⟩

/-- Two AIPW nuisance vectors are equal when their outcome regressions and
propensity functions agree everywhere. -/
@[ext]
theorem ext {η η' : NuisanceVec γ}
    (hμ : ∀ b x, η.μ_fn b x = η'.μ_fn b x)
    (he : ∀ x, η.e_fn x = η'.e_fn x) : η = η' := by
  cases η
  cases η'
  simp only at hμ he
  congr
  · funext b x
    exact hμ b x
  · funext x
    exact he x

/-- For [a measurable covariate space](hyp:γ), the [additive commutative group structure on AIPW nuisance vectors](goal)
uses [the zero vector](step:1), [componentwise addition](step:2), [componentwise negation](step:3),
[componentwise subtraction](step:4), [natural-number scalar multiplication](step:5), and [integer scalar multiplication](step:6),
and satisfies [the natural-zero rule](step:7), [the natural-successor rule](step:8), [the integer-zero rule](step:9), [the positive-integer-successor rule](step:10), [the negative-integer-successor rule](step:11), [subtraction as addition of an inverse](step:12), [associativity](step:13), [the left-zero law](step:14), [the right-zero law](step:15), [inverse cancellation](step:16), and [commutativity](step:17). -/
instance : AddCommGroup (NuisanceVec γ) where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  sub := Sub.sub
  nsmul := nsmulRec
  zsmul := zsmulRec
  nsmul_zero η := by
    rfl
  nsmul_succ n η := by
    rfl
  zsmul_zero' η := by
    rfl
  zsmul_succ' n η := by
    rfl
  zsmul_neg' n η := by
    rfl
  sub_eq_add_neg η η' := by
    apply ext <;> intro b
    · intro x
      exact sub_eq_add_neg (η.μ_fn b x) (η'.μ_fn b x)
    · exact sub_eq_add_neg (η.e_fn b) (η'.e_fn b)
  add_assoc η η' η'' := by
    apply ext <;> intro b
    · intro x
      exact add_assoc (η.μ_fn b x) (η'.μ_fn b x) (η''.μ_fn b x)
    · exact add_assoc (η.e_fn b) (η'.e_fn b) (η''.e_fn b)
  zero_add η := by
    apply ext <;> intro b
    · intro x
      exact zero_add (η.μ_fn b x)
    · exact zero_add (η.e_fn b)
  add_zero η := by
    apply ext <;> intro b
    · intro x
      exact add_zero (η.μ_fn b x)
    · exact add_zero (η.e_fn b)
  neg_add_cancel η := by
    apply ext <;> intro b
    · intro x
      exact neg_add_cancel (η.μ_fn b x)
    · exact neg_add_cancel (η.e_fn b)
  add_comm η η' := by
    apply ext <;> intro b
    · intro x
      exact add_comm (η.μ_fn b x) (η'.μ_fn b x)
    · exact add_comm (η.e_fn b) (η'.e_fn b)

/-- For [a measurable covariate space](hyp:γ), the [real vector-space structure on AIPW nuisance vectors](goal)
uses [componentwise scalar multiplication](step:1) and satisfies [multiplication by one](step:2), [compatibility of successive scalar multiplications](step:3), [multiplication of zero vectors](step:4), [distribution over vector addition](step:5), [distribution over scalar addition](step:6), and [multiplication by the zero scalar](step:7). -/
instance : Module ℝ (NuisanceVec γ) where
  smul := (· • ·)
  one_smul η := by
    apply ext <;> intro b
    · intro x
      change (1 : ℝ) * η.μ_fn b x = η.μ_fn b x
      exact one_mul _
    · change (1 : ℝ) * η.e_fn b = η.e_fn b
      exact one_mul _
  mul_smul t u η := by
    apply ext <;> intro b
    · intro x
      change (t * u) * η.μ_fn b x = t * (u * η.μ_fn b x)
      ring
    · change (t * u) * η.e_fn b = t * (u * η.e_fn b)
      ring
  smul_zero t := by
    apply ext <;> intro b
    · intro x
      change t * (0 : ℝ) = 0
      exact mul_zero t
    · change t * (0 : ℝ) = 0
      exact mul_zero t
  smul_add t η η' := by
    apply ext <;> intro b
    · intro x
      change t * (η.μ_fn b x + η'.μ_fn b x) =
        t * η.μ_fn b x + t * η'.μ_fn b x
      ring
    · change t * (η.e_fn b + η'.e_fn b) = t * η.e_fn b + t * η'.e_fn b
      ring
  add_smul t u η := by
    apply ext <;> intro b
    · intro x
      change (t + u) * η.μ_fn b x = t * η.μ_fn b x + u * η.μ_fn b x
      ring
    · change (t + u) * η.e_fn b = t * η.e_fn b + u * η.e_fn b
      ring
  zero_smul η := by
    apply ext <;> intro b
    · intro x
      change (0 : ℝ) * η.μ_fn b x = 0
      exact zero_mul _
    · change (0 : ℝ) * η.e_fn b = 0
      exact zero_mul _

end NuisanceVec

namespace BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- For a [potential-outcome system](hyp:P) with a standard-Borel sample space and finite probability measure, a [measurable covariate space](hyp:γ), and [a back-door estimation system](hyp:S), the [true nuisance vector](goal) consists of the system's treatment-specific outcome regressions and propensity score. -/
noncomputable def η₀ (S : BackdoorEstimationSystem P γ) : NuisanceVec γ :=
  ⟨S.μ_val, S.e_val, S.μ_meas, S.e_meas⟩

/-- For a [measurable covariate space](hyp:γ) and [a real overlap level](hyp:ε), the [pointwise overlap-bounded nuisance class](goal) is the set of all nuisance vectors whose propensity score lies between $ε$ and $1-ε$ at every covariate value.

This pointwise version remains for existing denominator-bound proofs that have
not yet been migrated to a.e. overlap. -/
def H_ε (ε : ℝ) : Set (NuisanceVec γ) :=
  { η | ∀ x, ε ≤ η.e_fn x ∧ η.e_fn x ≤ 1 - ε }

/-- For a [potential-outcome system](hyp:P) with a standard-Borel sample space and finite probability measure, a [measurable covariate space](hyp:γ), [a back-door estimation system](hyp:S), and [a real overlap level](hyp:ε), the [almost-everywhere $L^2$ AIPW nuisance class](goal) is the set of nuisance vectors whose propensity score lies between $ε$ and $1-ε$ almost everywhere under the covariate law, whose two outcome regressions are square-integrable under that law, and whose propensity score is essentially bounded under that law.

This is the econometric nuisance-space structure used in standard AIPW/DML
statements: overlap is a support condition, while the regression and propensity
components live in the corresponding `L²` and `L∞` spaces. -/
def H_ε_aeL2 (S : BackdoorEstimationSystem P γ) (ε : ℝ) :
    Set (NuisanceVec γ) :=
  { η | (∀ᵐ x ∂S.P_X, ε ≤ η.e_fn x ∧ η.e_fn x ≤ 1 - ε) ∧
      (∀ d : Bool, MemLp (η.μ_fn d) 2 S.P_X) ∧
      MemLp η.e_fn ⊤ S.P_X }

/-- Membership in `H_ε_aeL2` transports its a.e. overlap condition from the
covariate law to the original probability space along the observed covariate. -/
lemma H_ε_aeL2_overlap_factualX
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    {η : NuisanceVec γ} (hη : η ∈ H_ε_aeL2 S ε) :
    ∀ᵐ ω ∂P.μ,
      ε ≤ η.e_fn (S.toPOBackdoorSystem.factualX ω) ∧
        η.e_fn (S.toPOBackdoorSystem.factualX ω) ≤ 1 - ε := by
  have hset : MeasurableSet {x : γ | ε ≤ η.e_fn x ∧ η.e_fn x ≤ 1 - ε} := by
    exact measurableSet_Icc.preimage η.e_meas
  have hx : ∀ᵐ x ∂S.P_X, ε ≤ η.e_fn x ∧ η.e_fn x ≤ 1 - ε := hη.1
  unfold BackdoorEstimationSystem.P_X at hx
  exact (MeasureTheory.ae_map_iff
    S.toPOBackdoorSystem.measurable_factualX.aemeasurable hset).mp hx

/-- Membership in `H_ε_aeL2` transports its a.e. overlap condition from the
covariate law to the observed-data law along the covariate projection. -/
lemma H_ε_aeL2_overlap_P_Z
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    {η : NuisanceVec γ} (hη : η ∈ H_ε_aeL2 S ε) :
    ∀ᵐ z ∂S.P_Z,
      ε ≤ η.e_fn (projX z) ∧ η.e_fn (projX z) ≤ 1 - ε := by
  have hset : MeasurableSet {x : γ | ε ≤ η.e_fn x ∧ η.e_fn x ≤ 1 - ε} := by
    exact measurableSet_Icc.preimage η.e_meas
  have hx : ∀ᵐ x ∂S.P_X, ε ≤ η.e_fn x ∧ η.e_fn x ≤ 1 - ε := hη.1
  rw [← BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] at hx
  have hproj : Measurable (fun z : γ × Bool × ℝ => projX z) := by
    simpa [projX] using (measurable_fst : Measurable (fun z : γ × Bool × ℝ => z.1))
  exact (MeasureTheory.ae_map_iff hproj.aemeasurable hset).mp hx

/-- For an estimation system `S`, overlap level `ε`, and treatment arm `d`, if
[`η` is a member of the `ε`-overlap `L²` nuisance class `H_ε_aeL2`](hyp:hη),
then [`η`'s outcome-regression component at arm `d` lies in `L²(P_X)`](goal). -/
lemma H_ε_aeL2_mu_memLp
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    {η : NuisanceVec γ} (hη : η ∈ H_ε_aeL2 S ε) (d : Bool) :
    MemLp (η.μ_fn d) 2 S.P_X :=
  hη.2.1 d

/-- The propensity component of an `H_ε_aeL2` nuisance is in `L∞(P_X)`. -/
lemma H_ε_aeL2_e_memLp_top
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    {η : NuisanceVec γ} (hη : η ∈ H_ε_aeL2 S ε) :
    MemLp η.e_fn ⊤ S.P_X :=
  hη.2.2

/-- For a [measurable covariate space](hyp:γ), the [AIPW moment functional](goal) maps a nuisance vector, an observed covariate--treatment--outcome triple, and a real target value to the corresponding AIPW moment. -/
noncomputable def aipwMomentFunctional :
    NuisanceVec γ → (γ × Bool × ℝ) → ℝ → ℝ :=
  fun η z θ => aipwMoment z η.μ_fn η.e_fn θ

end BackdoorEstimationSystem

end ATE
end Estimation
end Causalean

import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Classes
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.EReal.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-! # Generic divergence and legality classes -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set

/-- Mutual absolute continuity for two measures. -/
def MutuallyAC {Y : Type*} [MeasurableSpace Y] (P Q : Measure Y) : Prop :=
  P.AbsolutelyContinuous Q ∧ Q.AbsolutelyContinuous P

/-- The paper's extended-valued general `f`-divergence. Nonintegrable pairs
have divergence `⊤`, rather than inheriting the Bochner integral's default zero. -/
noncomputable def fDiv {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (P Q : Measure Y) : EReal := by
  classical
  exact if Integrable (fun x => f ((P.rnDeriv Q x).toReal)) Q then
      ((∫ x, f ((P.rnDeriv Q x).toReal) ∂Q : ℝ) : EReal)
    else ⊤
  -- @realizes D_f(P\|Q)(integral of f(dP/dQ) under Q)

/-- The propensity-calibrated divergence radius. -/
noncomputable def divRadius (f : ℝ → ℝ) (e : ℝ) : ℝ :=
  e * f (1 / e) + (1 - e) * f 0
  -- @realizes B_f(e)(e*f(1/e)+(1-e)*f(0))

/-- Finite continuous convex normalized divergence generators. -/
def AdmissibleGenerator (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧ ConvexOn ℝ (Set.Ici 0) f ∧ f 1 = 0
  -- @realizes \(f\)(finite continuous convex function on [0,∞), normalized at 1)

/-- Domain conditions under which the real integral is the finite nonnegative
`f`-divergence of probability laws. -/
-- keep: same-scope domain and nonnegativity constraints for the core symbol D_f(P\|Q)
def FDivDomain {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (P Q : Measure Y) : Prop :=
  AdmissibleGenerator f ∧ IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
    P.AbsolutelyContinuous Q ∧
    Integrable (fun x => f ((P.rnDeriv Q x).toReal)) Q
  -- @realizes D_f(P\|Q)(admissible finite probability-law divergence in [0,∞))

/-- Domain conditions making the calibrated radius nonnegative. -/
-- keep: same-scope domain and nonnegativity constraints for the core symbol B_f(e)
def DivRadiusDomain (f : ℝ → ℝ) (e : ℝ) : Prop :=
  AdmissibleGenerator f ∧ StrictPositivity e
  -- @realizes B_f(e)(admissible generator and 0<e<1 imply nonnegative radius)

/-- The propensity-induced cap. -/
def PropensityCap (e c : ℝ) : Prop :=
  StrictPositivity e ∧ c = 1 / e ∧ 1 < c
  -- @realizes c(c=1/e in (1,∞))

/-- The KL generator with the `0 log 0 = 0` convention. -/
-- keep: explicit paper-named generator realizing the core symbol f_KL for public reuse
noncomputable def klGenerator (t : ℝ) : ℝ :=
  if t = 0 then 0 else t * Real.log t
  -- @realizes f_{\mathrm{KL}}(t log t with 0 log 0 = 0)

/-- The cap-hinge generator. -/
-- keep: explicit paper-named generator realizing the core symbol f_c for public reuse
def capHinge (c t : ℝ) : ℝ := max (t - c) 0
  -- @realizes f_c((t-c)_+)

/-- The mutual-support Jung--Kang ball membership predicate. -/
-- @node: def:jk-ball
structure JKBall {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) (P Q : Measure Y) : Prop where
  positivity : StrictPositivity e
  admissible : AdmissibleGenerator f
  observed_probability : IsProbabilityMeasure P
  candidate_probability : IsProbabilityMeasure Q
  mutual_ac : MutuallyAC Q P
  divergence_le : fDiv f P Q ≤ (divRadius f e : EReal)

/-- The mutual-support divergence ambiguity set. -/
noncomputable def jkBallSet {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) (P : Measure Y) : Set (Measure Y) :=
  {Q | JKBall f e P Q}
  -- @realizes \mathfrak B_{f,e}(P)(mutual-AC f-divergence ball)

/-- The one-sided Jung--Kang ball membership predicate. -/
-- @node: def:jk-ball-one-sided
structure JKBallOneSided {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) (P Q : Measure Y) : Prop where
  positivity : StrictPositivity e
  admissible : AdmissibleGenerator f
  observed_probability : IsProbabilityMeasure P
  candidate_probability : IsProbabilityMeasure Q
  forward_support : P.AbsolutelyContinuous Q
  divergence_le : fDiv f P Q ≤ (divRadius f e : EReal)

/-- The one-sided divergence ambiguity set. -/
noncomputable def jkBallOneSidedSet {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) (P : Measure Y) : Set (Measure Y) :=
  {Q | JKBallOneSided f e P Q}
  -- @realizes \mathfrak B^{\to}_{f,e}(P)(one-sided f-divergence ball)

/-- The fixed-cap affine-equivalence frontier membership predicate. -/
-- @node: def:hinge-class
structure HingeClass (c : ℝ) (f : ℝ → ℝ) : Prop where
  positivity : StrictPositivity (1 / c)
  admissible : AdmissibleGenerator f
  affine_hinge : ∃ b : ℝ,
    (∀ t, 0 ≤ t → t ≤ c → f t - b * (t - 1) = 0) ∧
    (∀ t, c < t → 0 < f t - b * (t - 1))

/-- Generators affine-equivalent to the cap hinge. -/
def hingeClassSet (c : ℝ) : Set (ℝ → ℝ) :=
  {f | HingeClass c f}
  -- @realizes \mathfrak H_c(affine-equivalence class of cap hinges)

/-- The mutual-support legality-correction membership predicate. -/
-- @node: def:lawful-correction
structure LawfulCorrection {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) (P Q : Measure Y) : Prop where
  positivity : StrictPositivity e
  divergence_member : Q ∈ jkBallSet f e P
  mixture_member : Q ∈ mixtureClassSet e P

/-- Intersection of the mutual divergence ball and exact mixture class. -/
noncomputable def lawfulCorrectionSet {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) (P : Measure Y) : Set (Measure Y) :=
  jkBallSet f e P ∩ mixtureClassSet e P
  -- @realizes \mathfrak B^{\mathrm{law}}_{f,e}(P)(lawful mutual intersection)

/-- The one-sided legality-correction membership predicate. -/
-- @node: def:lawful-correction-one-sided
structure LawfulCorrectionOneSided {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) (P Q : Measure Y) : Prop where
  positivity : StrictPositivity e
  divergence_member : Q ∈ jkBallOneSidedSet f e P
  mixture_member : Q ∈ mixtureClassOneSidedSet e P

/-- Intersection of the one-sided divergence ball and exact mixture class. -/
noncomputable def lawfulCorrectionOneSidedSet {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) (P : Measure Y) : Set (Measure Y) :=
  jkBallOneSidedSet f e P ∩ mixtureClassOneSidedSet e P
  -- @realizes \mathfrak B^{\mathrm{law},\to}_{f,e}(P)(lawful one-sided intersection)

/-- The propensity-adaptive hinge. -/
noncomputable def adaptiveHinge (e t : ℝ) : ℝ := max (t - 1 / e) 0
  -- @realizes f_e(propensity-adaptive hinge)
  -- @realizes f_{a,x}(adaptive hinge after substituting e_a(x))

end CausalSmith.SCM.PropensityLvSharpnessFrontier

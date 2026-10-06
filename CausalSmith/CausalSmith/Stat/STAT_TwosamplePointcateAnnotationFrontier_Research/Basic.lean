module
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Basic

Two-channel point-CATE annotation frontier: Basic
constructions and obligations.
-/

@[expose] public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


/-- Euclidean covariates, with coordinatewise cube support.  Given [the specified input d](hyp:d), [cov](goal) is the corresponding construction. -/
abbrev Cov (d : ℕ) := EuclideanSpace ℝ (Fin d)
/-- Closed design cube.  Given [the specified input d](hyp:d), [cube](goal) is the corresponding construction. -/
def cube (d : ℕ) : Set (Cov d) := {x | ∀ i, x i ∈ Icc 0 1} -- @realizes x(cube carrier) @realizes xp(cube carrier) @realizes X(cube support)
/-- Given [the specified input d](hyp:d), [x0](goal) is the corresponding construction. -/
def x0 (d : ℕ) : Cov d := WithLp.toLp 2 (fun _ => 1 / 2) -- @realizes x0(interior centre)
/-- Given [the specified input d](hyp:d), [uniform law](goal) is the corresponding construction. -/
def uniformLaw (d : ℕ) : Measure (Cov d) := volume.restrict (cube d)
/-- Given [the specified input d](hyp:d), [full record](goal) is the corresponding construction. -/
abbrev FullRecord (d : ℕ) := Cov d × Bool × Bool × Bool
-- @realizes A(binary second coordinate) @realizes Yzero(binary third coordinate) @realizes Yone(binary fourth coordinate)
/-- Given [the specified input a](hyp:a), [bit](goal) is the corresponding construction. -/
def bit (a : Bool) : ℝ := if a then 1 else 0
/-- Given [the specified input d](hyp:d), [the specified input w](hyp:w), [observed](goal) is the corresponding construction. -/
def observed {d : ℕ} (w : FullRecord d) : Cov d × Bool × Bool :=
  (w.1, w.2.1, if w.2.1 then w.2.2.2 else w.2.2.1) -- @realizes Y(consistency selection)
/-- Given [the specified input p](hyp:p), [bern](goal) is the corresponding construction. -/
def bern (p : ℝ) : Measure Bool :=
  ENNReal.ofReal (1-p) • Measure.dirac false + ENNReal.ofReal p • Measure.dirac true
/-- Given [the specified input p](hyp:p), [the specified input hp](hyp:hp), [the measurable bern conclusion](goal) holds. -/
@[fun_prop] lemma measurable_bern {Ω : Type*} [MeasurableSpace Ω] (p : Ω → ℝ)
    (hp : Measurable p) : Measurable (fun x => bern (p x)) := by
  unfold bern
  fun_prop
/-- Given [the specified input p](hyp:p), [the specified input hp](hyp:hp), [bern kernel](goal) is the corresponding construction. -/
def bernKernel {Ω : Type*} [MeasurableSpace Ω] (p : Ω → ℝ) (hp : Measurable p) : Kernel Ω Bool :=
  ⟨fun x => bern (p x), measurable_bern p hp⟩
/-- A probability law with raw measurable conditional versions. Class membership below
quantifies over admissible replacements with the same underlying measure. -/
structure PrimitiveLaw (d : ℕ) where
  law : Measure (FullRecord d) -- @realizes P(Borel full-record law)
  probability : IsProbabilityMeasure law
  supported : law {w | w.1 ∈ cube d} = 1 -- @realizes X(cube supported)
  e : Cov d → ℝ
  mu0 : Cov d → ℝ
  mu1 : Cov d → ℝ
  measurable_e : Measurable e
  measurable_mu0 : Measurable mu0
  measurable_mu1 : Measurable mu1
  margin_e : law.map (fun w => (w.1,w.2.1)) = (law.map Prod.fst) ⊗ₘ bernKernel e measurable_e
  margin_mu0 : law.map (fun w => (w.1,w.2.2.1)) = (law.map Prod.fst) ⊗ₘ bernKernel mu0 measurable_mu0
  margin_mu1 : law.map (fun w => (w.1,w.2.2.2)) = (law.map Prod.fst) ⊗ₘ bernKernel mu1 measurable_mu1
attribute [instance] PrimitiveLaw.probability
/-- Given [the specified input d](hyp:d), [the specified input P](hyp:P), [obs law](goal) is the corresponding construction. -/
def obsLaw {d : ℕ} (P : PrimitiveLaw d) : Measure (Cov d × Bool × Bool) := P.law.map observed -- @realizes Po(observed pushforward)
/-- Given [the specified input d](hyp:d), [the specified input P](hyp:P), [xa law](goal) is the corresponding construction. -/
def xaLaw {d : ℕ} (P : PrimitiveLaw d) : Measure (Cov d × Bool) := P.law.map (fun w => (w.1,w.2.1)) -- @realizes PXA(treatment marginal)
/-- Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input x](hyp:x), [raw contrast](goal) is the corresponding construction. -/
def rawContrast {d : ℕ} (P : PrimitiveLaw d) (x : Cov d) : ℝ := P.mu1 x - P.mu0 x
-- @env: S1
variable {d : ℕ} (alpha beta gamma L eps : ℝ)
/-- [The public parameter domain](goal): [the covariate dimension d](hyp:d) is at least one, [the propensity smoothness alpha](hyp:alpha) and [the control-mean smoothness beta](hyp:beta) lie in (0, 1], [the effect smoothness gamma](hyp:gamma) lies in [1, 3], [the Hölder radius L](hyp:L) exceeds one half, and [the overlap level eps](hyp:eps) lies strictly between 0 and one half. All constants in the results may depend on these parameters. -/
def PublicDomain (d : ℕ) (alpha beta gamma L eps : ℝ) : Prop :=
  1 ≤ d ∧ -- @realizes d(positive integer)
  0 < alpha ∧ alpha ≤ 1 ∧ -- @realizes alpha(public interval)
  0 < beta ∧ beta ≤ 1 ∧ -- @realizes beta(public interval)
  1 ≤ gamma ∧ gamma ≤ 3 ∧ -- @realizes gamma(public interval)
  1/2 < L ∧ -- @realizes L(public radius)
  0 < eps ∧ eps < 1/2 -- @realizes eps(overlap level)
/-- [multi order](goal) is the corresponding construction. -/
def multiOrder (κ : Fin d → ℕ) : ℕ := ∑ i, κ i -- @realizes kappa(natural multi-index)
/-- Given [the specified input k](hyp:k), [coordinate directions](goal) is the corresponding construction. -/
def coordinateDirections (κ : Fin d → ℕ) (k : Fin (multiOrder κ)) : Cov d :=
  ∑ i, if (∑ j ∈ Finset.univ.filter (fun j => j < i), κ j) ≤ k.val ∧
    k.val < (∑ j ∈ Finset.univ.filter (fun j => j < i), κ j) + κ i
    then EuclideanSpace.single i 1 else 0
/-- Given [the specified input f](hyp:f), [the specified input x](hyp:x), [coordinate partial](goal) is the corresponding construction. -/
def coordinatePartial (f : Cov d → ℝ) (κ : Fin d → ℕ) (x : Cov d) : ℝ :=
  iteratedFDerivWithin ℝ (multiOrder κ) f (cube d) x (coordinateDirections κ)
-- @node: def:holder-norm
/-- Exact coordinate-partial Hölder norm, infinite when the required continuous derivatives do not exist.  Given [the specified input f](hyp:f), [the specified input s](hyp:s), [holder norm](goal) is the corresponding construction. -/
def holderNorm (f : Cov d → ℝ) (s : ℝ) : ℝ≥0∞ :=
  if ContDiffOn ℝ (Nat.ceil s - 1 : ℕ) f (cube d) then
    max (⨆ (κ : Fin d → ℕ) (_ : multiOrder κ ≤ Nat.ceil s - 1) (x : Cov d) (_ : x ∈ cube d),
      ENNReal.ofReal |coordinatePartial f κ x|)
      (⨆ (κ : Fin d → ℕ) (_ : multiOrder κ = Nat.ceil s - 1)
        (x : Cov d) (_ : x ∈ cube d) (xp : Cov d) (_ : xp ∈ cube d) (_ : x ≠ xp),
        ENNReal.ofReal (|coordinatePartial f κ x - coordinatePartial f κ xp| /
          dist x xp ^ (s - (Nat.ceil s - 1 : ℕ))))
  else ⊤ -- @realizes normH(exact extended norm) @realizes f(function carrier) @realizes s(regularity argument)
/-- Given [the specified input f](hyp:f), [the specified input s](hyp:s), [the specified input L](hyp:L), [the specified input hL](hyp:hL), [the holder norm le iff conclusion](goal) holds. -/
lemma holderNorm_le_iff (f : Cov d → ℝ) (s L : ℝ) (hL : 0 ≤ L) :
    holderNorm f s ≤ ENNReal.ofReal L ↔
      ContDiffOn ℝ (Nat.ceil s - 1 : ℕ) f (cube d) ∧
      (∀ κ, multiOrder κ ≤ Nat.ceil s - 1 → ∀ x ∈ cube d, |coordinatePartial f κ x| ≤ L) ∧
      (∀ κ, multiOrder κ = Nat.ceil s - 1 → ∀ x ∈ cube d, ∀ xp ∈ cube d, x ≠ xp →
        |coordinatePartial f κ x - coordinatePartial f κ xp| ≤ L * dist x xp ^ (s - (Nat.ceil s - 1 : ℕ))) := by
  unfold holderNorm
  by_cases hf : ContDiffOn ℝ (Nat.ceil s - 1 : ℕ) f (cube d)
  · rw [if_pos hf]
    simp only [max_le_iff, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff hL]
    constructor
    · rintro ⟨hderiv, hseminorm⟩
      refine ⟨hf, hderiv, ?_⟩
      intro κ hκ x hx xp hxp hne
      exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hne) _)).mp
        (hseminorm κ hκ x hx xp hxp hne)
    · rintro ⟨_, hderiv, hseminorm⟩
      refine ⟨hderiv, ?_⟩
      intro κ hκ x hx xp hxp hne
      exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hne) _)).mpr
        (hseminorm κ hκ x hx xp hxp hne)
  · rw [if_neg hf]
    simp only [top_le_iff, ENNReal.ofReal_ne_top, false_iff]
    exact fun h => hf h.1
/-- The cube has a nonempty open interior, so within-cube derivatives are unique.  Given [the specified input d](hyp:d), [the unique diff on cube conclusion](goal) holds. -/
lemma uniqueDiffOn_cube (d : ℕ) : UniqueDiffOn ℝ (cube d) := by
  apply uniqueDiffOn_convex
  · intro x hx y hy a b ha hb hab
    intro i
    change 0 ≤ a * x i + b * y i ∧ a * x i + b * y i ≤ 1
    constructor
    · exact add_nonneg (mul_nonneg ha (hx i).1) (mul_nonneg hb (hy i).1)
    · calc
        a * x i + b * y i ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hx i).2 ha)
            (mul_le_mul_of_nonneg_left (hy i).2 hb)
        _ = 1 := by nlinarith
  · let U : Set (Cov d) := ⋂ i : Fin d, {x | x i ∈ Ioo (0 : ℝ) 1}
    have hU : IsOpen U := by
      apply isOpen_iInter_of_finite
      intro i
      exact isOpen_Ioo.preimage (by fun_prop)
    have hsub : U ⊆ cube d := by
      intro x hx i
      have hi := Set.mem_iInter.mp hx i
      exact ⟨hi.1.le, hi.2.le⟩
    refine ⟨x0 d, interior_mono hsub ?_⟩
    rw [hU.interior_eq]
    norm_num [U, x0]

/-- Coordinate partials of smooth functions add on the closed cube.  Given [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input N](hyp:N), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the multi-index](hyp:κ), [its order bound](hyp:hκ), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the coordinate partial add conclusion](goal) holds. -/
lemma coordinatePartial_add (f g : Cov d → ℝ) (N : ℕ)
    (hf : ContDiffOn ℝ N f (cube d)) (hg : ContDiffOn ℝ N g (cube d))
    (κ : Fin d → ℕ) (hκ : multiOrder κ ≤ N) (x : Cov d) (hx : x ∈ cube d) :
    coordinatePartial (fun x => f x + g x) κ x =
      coordinatePartial f κ x + coordinatePartial g κ x := by
  unfold coordinatePartial
  rw [fun_iteratedFDerivWithin_add_apply
    ((hf.of_le (by exact_mod_cast hκ)) x hx)
    ((hg.of_le (by exact_mod_cast hκ)) x hx) (uniqueDiffOn_cube d) hx]
  rfl

/-- The exact extended Hölder norm obeys the triangle inequality.  Given [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input s](hyp:s), [the holder norm add le conclusion](goal) holds. -/
lemma holderNorm_add_le (f g : Cov d → ℝ) (s : ℝ) :
    holderNorm (fun x => f x + g x) s ≤ holderNorm f s + holderNorm g s := by
  by_cases hfTop : holderNorm f s = ⊤
  · simp [hfTop]
  by_cases hgTop : holderNorm g s = ⊤
  · simp [hgTop]
  let A := (holderNorm f s).toReal
  let B := (holderNorm g s).toReal
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hf := (holderNorm_le_iff f s A hA).mp
    (le_of_eq (ENNReal.ofReal_toReal hfTop).symm)
  have hg := (holderNorm_le_iff g s B hB).mp
    (le_of_eq (ENNReal.ofReal_toReal hgTop).symm)
  have hbound : holderNorm (fun x => f x + g x) s ≤ ENNReal.ofReal (A + B) := by
    apply (holderNorm_le_iff _ s (A + B) (add_nonneg hA hB)).mpr
    refine ⟨hf.1.add hg.1, ?_, ?_⟩
    · intro κ hκ x hx
      rw [coordinatePartial_add f g _ hf.1 hg.1 κ hκ x hx]
      exact (abs_add_le _ _).trans (add_le_add (hf.2.1 κ hκ x hx) (hg.2.1 κ hκ x hx))
    · intro κ hκ x hx xp hxp hne
      rw [coordinatePartial_add f g _ hf.1 hg.1 κ hκ.le x hx,
        coordinatePartial_add f g _ hf.1 hg.1 κ hκ.le xp hxp]
      calc
        |coordinatePartial f κ x + coordinatePartial g κ x -
            (coordinatePartial f κ xp + coordinatePartial g κ xp)| =
            |(coordinatePartial f κ x - coordinatePartial f κ xp) +
              (coordinatePartial g κ x - coordinatePartial g κ xp)| := by congr 1; ring
        _ ≤ |coordinatePartial f κ x - coordinatePartial f κ xp| +
            |coordinatePartial g κ x - coordinatePartial g κ xp| := abs_add_le _ _
        _ ≤ A * dist x xp ^ (s - (Nat.ceil s - 1 : ℕ)) +
            B * dist x xp ^ (s - (Nat.ceil s - 1 : ℕ)) :=
          add_le_add (hf.2.2 κ hκ x hx xp hxp hne) (hg.2.2 κ hκ x hx xp hxp hne)
        _ = (A + B) * dist x xp ^ (s - (Nat.ceil s - 1 : ℕ)) := by ring
  rw [ENNReal.ofReal_add hA hB] at hbound
  dsimp only [A, B] at hbound
  simpa only [ENNReal.ofReal_toReal hfTop, ENNReal.ofReal_toReal hgTop] using hbound
-- @node: ass:uniform-design
/-- Given [the specified input P](hyp:P), [uniform design](goal) is the corresponding construction. -/
def UniformDesign (P : PrimitiveLaw d) : Prop := P.law.map Prod.fst = uniformLaw d
-- @node: ass:exchangeability
/-- Given [the specified input P](hyp:P), [conditional exchangeability](goal) is the corresponding construction. -/
def ConditionalExchangeability (P : PrimitiveLaw d) : Prop :=
  ∃ Γ : Kernel (Cov d) (Bool × Bool), IsMarkovKernel Γ ∧
    P.law.map (fun w => ((w.1,(w.2.2.1,w.2.2.2)),w.2.1)) =
      (P.law.map Prod.fst ⊗ₘ Γ) ⊗ₘ
        bernKernel (fun w : Cov d × (Bool × Bool) => P.e w.1) (P.measurable_e.comp measurable_fst)
-- @node: ass:overlap
/-- [The overlap condition at level eps](goal): [the overlap level eps](hyp:eps) is positive and, on the design cube, [the law P](hyp:P) has a propensity between eps and 1 − eps. -/
def Overlap (eps : ℝ) (P : PrimitiveLaw d) : Prop :=
  0 < eps ∧ ∀ x ∈ cube d, eps ≤ P.e x ∧ P.e x ≤ 1 - eps -- @realizes e(overlap band)

/-- Under [overlap](hyp:h) at [the overlap level eps](hyp:eps), [the propensity of the law P is a probability on the design cube](goal). -/
lemma Overlap.unit {eps : ℝ} {P : PrimitiveLaw d} (h : Overlap eps P) :
    ∀ x ∈ cube d, 0 ≤ P.e x ∧ P.e x ≤ 1 := by
  intro x hx
  have hb := h.2 x hx
  constructor <;> linarith [h.1, hb.1, hb.2]
-- @node: ass:propensity-holder
/-- Witness-level propensity smoothness, applied by `PrimitiveClass` to its admissible `W`.  Given [the specified input alpha](hyp:alpha), [the specified input L](hyp:L), [the specified input W](hyp:W), [propensity holder](goal) is the corresponding construction. -/
def PropensityHolder (alpha L : ℝ) (W : PrimitiveLaw d) : Prop := holderNorm W.e alpha ≤ ENNReal.ofReal L -- @realizes e(propensity smoothness)
-- @node: ass:control-holder
/-- Witness-level control-mean smoothness, applied by `PrimitiveClass` to its admissible `W`.  Given [the specified input beta](hyp:beta), [the specified input L](hyp:L), [the specified input W](hyp:W), [control holder](goal) is the corresponding construction. -/
def ControlHolder (beta L : ℝ) (W : PrimitiveLaw d) : Prop := holderNorm W.mu0 beta ≤ ENNReal.ofReal L -- @realizes mu0(control smoothness)
-- @node: ass:effect-holder
/-- Witness-level effect smoothness. After `W` is selected, `rawContrast W` agrees
with the canonical `tau` on the cube.  Given [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the specified input W](hyp:W), [effect holder](goal) is the corresponding construction. -/
def EffectHolder (gamma L : ℝ) (W : PrimitiveLaw d) : Prop := holderNorm (rawContrast W) gamma ≤ ENNReal.ofReal L -- @realizes tau(effect smoothness)
-- @node: ass:control-interior
/-- [The control-arm mean range condition](goal): on the design cube, [the admissible version W](hyp:W) has a control mean that is a probability, between 0 and 1. -/
def ControlInterior (W : PrimitiveLaw d) : Prop := ∀ x ∈ cube d, 0 ≤ W.mu0 x ∧ W.mu0 x ≤ 1 -- @realizes mu0(probability range)
-- @node: ass:treated-interior
/-- [The treated-arm mean range condition](goal): on the design cube, [the admissible version W](hyp:W) has a treated mean that is a probability, between 0 and 1. -/
def TreatedInterior (W : PrimitiveLaw d) : Prop := ∀ x ∈ cube d, 0 ≤ W.mu1 x ∧ W.mu1 x ≤ 1 -- @realizes mu1(probability range)
-- @node: def:primitive-class
/-- Membership is existential over conditional-margin witnesses of the underlying law.
The carrier's raw versions do not enter this predicate. -/
structure PrimitiveClass (alpha beta gamma L eps : ℝ) (P : PrimitiveLaw d) : Prop where
  versions : ∃ W : PrimitiveLaw d, W.law = P.law ∧
    UniformDesign W ∧ ConditionalExchangeability W ∧
    Overlap eps W ∧ PropensityHolder alpha L W ∧ ControlHolder beta L W ∧
    EffectHolder gamma L W ∧ ControlInterior W ∧ TreatedInterior W
-- @realizes M(existential eight-atom class of underlying laws)

/-- Designated admissible versions are selected from membership, never from the raw carrier.  Given [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [canonical law](goal) is the corresponding construction. -/
def canonicalLaw {alpha beta gamma L eps : ℝ} (P : PrimitiveLaw d)
    (hP : PrimitiveClass alpha beta gamma L eps P) : PrimitiveLaw d :=
  Classical.choose hP.versions

/-- Given [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the canonical law spec conclusion](goal) holds. -/
lemma canonicalLaw_spec {alpha beta gamma L eps : ℝ} (P : PrimitiveLaw d)
    (hP : PrimitiveClass alpha beta gamma L eps P) :
    (canonicalLaw P hP).law = P.law ∧
    UniformDesign (canonicalLaw P hP) ∧ ConditionalExchangeability (canonicalLaw P hP) ∧
    Overlap eps (canonicalLaw P hP) ∧ PropensityHolder alpha L (canonicalLaw P hP) ∧
    ControlHolder beta L (canonicalLaw P hP) ∧ EffectHolder gamma L (canonicalLaw P hP) ∧
    ControlInterior (canonicalLaw P hP) ∧ TreatedInterior (canonicalLaw P hP) := by
  exact Classical.choose_spec hP.versions

/-- For [a law P in the model class](hyp:hP), [the overlap level eps](hyp:eps) [is positive](goal). -/
lemma PrimitiveClass.eps_pos {alpha beta gamma L eps : ℝ} {P : PrimitiveLaw d}
    (hP : PrimitiveClass alpha beta gamma L eps P) : 0 < eps :=
  (canonicalLaw_spec P hP).2.2.2.1.1

/-- For [a law P in the model class](hyp:hP), [the overlap level eps](hyp:eps) [is at most one half](goal), since the propensity at the cube centre lies between eps and 1 − eps. -/
lemma PrimitiveClass.eps_le_half {alpha beta gamma L eps : ℝ} {P : PrimitiveLaw d}
    (hP : PrimitiveClass alpha beta gamma L eps P) : eps ≤ 1/2 := by
  have hx : x0 d ∈ cube d := by intro i; norm_num [x0, cube]
  have hb := (canonicalLaw_spec P hP).2.2.2.1.2 (x0 d) hx
  linarith [hb.1, hb.2]

/-- The supplied propensity and arm means are admissible conditional-margin witnesses.  Given [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [designated propensity](goal) is the corresponding construction. -/
def designatedPropensity {alpha beta gamma L eps : ℝ} (P : PrimitiveLaw d)
    (hP : PrimitiveClass alpha beta gamma L eps P) : Cov d → ℝ :=
  fun x => if x ∈ cube d then (canonicalLaw P hP).e x else 0 -- @realizes e(admissible Borel conditional-margin witness)
/-- Given [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [designated control](goal) is the corresponding construction. -/
def designatedControl {alpha beta gamma L eps : ℝ} (P : PrimitiveLaw d)
    (hP : PrimitiveClass alpha beta gamma L eps P) : Cov d → ℝ :=
  fun x => if x ∈ cube d then (canonicalLaw P hP).mu0 x else 0 -- @realizes mu0(admissible Borel conditional-margin witness)
/-- Given [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [designated treated](goal) is the corresponding construction. -/
def designatedTreated {alpha beta gamma L eps : ℝ} (P : PrimitiveLaw d)
    (hP : PrimitiveClass alpha beta gamma L eps P) : Cov d → ℝ :=
  fun x => if x ∈ cube d then (canonicalLaw P hP).mu1 x else 0 -- @realizes mu1(admissible Borel conditional-margin witness)
/-- Canonical continuous contrast on the cube, obtained from admissible witnesses.  Given [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input x](hyp:x), [tau](goal) is the corresponding construction. -/
def tau {alpha beta gamma L eps : ℝ} (P : PrimitiveLaw d)
    (hP : PrimitiveClass alpha beta gamma L eps P) (x : Cov d) : ℝ :=
  designatedTreated P hP x - designatedControl P hP x -- @realizes tau(canonical admissible contrast)

/-- The closed cube has dense interior, including in dimension zero.  Given [the specified input d](hyp:d), [the cube subset closure interior conclusion](goal) holds. -/
lemma cube_subset_closure_interior (d : ℕ) : cube d ⊆ closure (interior (cube d)) := by
  let H := PiLp.homeomorph 2 (fun _ : Fin d => ℝ)
  have hc : cube d = H ⁻¹' Set.pi Set.univ (fun _ => Icc (0 : ℝ) 1) := by
    ext x; simp [cube, H, PiLp.homeomorph, Pi.le_def, forall_and]
  rw [hc, ← H.preimage_interior, ← H.preimage_closure]
  apply Set.preimage_mono
  rw [interior_pi_set Set.finite_univ, closure_pi_set]
  exact Set.pi_mono fun i _ => (closure_interior_Icc (by norm_num : (0 : ℝ) ≠ 1)).symm.subset

/-- Uniform-design almost-everywhere equality determines continuous versions on the cube.  Given [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input hfg](hyp:hfg), [the uniform law continuous versions conclusion](goal) holds. -/
lemma uniformLaw_continuous_versions (f g : Cov d → ℝ)
    (hf : ContinuousOn f (cube d)) (hg : ContinuousOn g (cube d))
    (hfg : f =ᵐ[uniformLaw d] g) : Set.EqOn f g (cube d) := by
  exact MeasureTheory.Measure.eqOn_of_ae_eq hfg hf hg (cube_subset_closure_interior d)

/-- Finite Hölder norm supplies continuity on the entire closed cube.  Given [the specified input f](hyp:f), [the specified input s](hyp:s), [the specified input L](hyp:L), [the specified input h](hyp:h), [the holder norm continuous on conclusion](goal) holds. -/
lemma holderNorm_continuousOn (f : Cov d → ℝ) (s L : ℝ)
    (h : holderNorm f s ≤ ENNReal.ofReal L) : ContinuousOn f (cube d) := by
  have hc : ContDiffOn ℝ (Nat.ceil s - 1 : ℕ) f (cube d) := by
    by_contra hn
    simp only [holderNorm, if_neg hn] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h)
  exact hc.continuousOn

/-- Clamp a raw version only outside its probability range.  Given [the specified input p](hyp:p), [version clip](goal) is the corresponding construction. -/
def versionClip (p : ℝ) : ℝ := max 0 (min 1 p)

/-- Given [the specified input p](hyp:p), [the version clip mem conclusion](goal) holds. -/
lemma versionClip_mem (p : ℝ) : versionClip p ∈ Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Given [the specified input p](hyp:p), [the specified input hp](hyp:hp), [the version clip eq conclusion](goal) holds. -/
lemma versionClip_eq (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) : versionClip p = p := by
  simp only [versionClip, min_eq_right hp.2, max_eq_right hp.1]

/-- [the measurable version clip conclusion](goal) holds. -/
@[fun_prop] lemma measurable_versionClip : Measurable versionClip := by
  unfold versionClip
  fun_prop

/-- Clipped Bernoulli kernels are Markov kernels even when raw versions are unbounded.  Given [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the bern kernel version clip markov conclusion](goal) holds. -/
lemma bernKernel_versionClip_markov (f : Cov d → ℝ) (hf : Measurable f) :
    IsMarkovKernel (bernKernel (fun x => versionClip (f x)) (by fun_prop)) := by
  constructor
  intro x
  constructor
  have hp := versionClip_mem (f x)
  simp only [bernKernel, Kernel.coe_mk, bern, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hp.2) hp.1]
  norm_num

/-- A probability marginal rules out the zero fallback in composition-product.  Given [the specified input P](hyp:P), [the specified input j](hyp:j), [the specified input hj](hyp:hj), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input hm](hyp:hm), [the bern kernel sfinite of margin conclusion](goal) holds. -/
lemma bernKernel_sfinite_of_margin (P : PrimitiveLaw d) (j : FullRecord d → Bool)
    (hj : Measurable j) (f : Cov d → ℝ) (hf : Measurable f)
    (hm : P.law.map (fun w => (w.1, j w)) =
      (P.law.map Prod.fst) ⊗ₘ bernKernel f hf) : IsSFiniteKernel (bernKernel f hf) := by
  by_contra hn
  have hz : P.law.map (fun w => (w.1, j w)) = 0 :=
    hm.trans (Measure.compProd_of_not_isSFiniteKernel _ _ hn)
  have hu := congrArg (fun μ : Measure (Cov d × Bool) => μ Set.univ) hz
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ] at hu
  simp at hu

/-- Conditional Bernoulli margins identify admissible continuous probability versions.  Given [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the specified input hfcont](hyp:hfcont), [the specified input hgcont](hyp:hgcont), [the specified input hfprob](hyp:hfprob), [the specified input hgprob](hyp:hgprob), [the specified input hm](hyp:hm), [the bern margin versions unique conclusion](goal) holds. -/
lemma bern_margin_versions_unique (f g : Cov d → ℝ) (hf : Measurable f) (hg : Measurable g)
    [IsFiniteMeasure (uniformLaw d)]
    [IsSFiniteKernel (bernKernel f hf)] [IsSFiniteKernel (bernKernel g hg)]
    (hfcont : ContinuousOn f (cube d)) (hgcont : ContinuousOn g (cube d))
    (hfprob : ∀ x ∈ cube d, f x ∈ Icc (0 : ℝ) 1)
    (hgprob : ∀ x ∈ cube d, g x ∈ Icc (0 : ℝ) 1)
    (hm : (uniformLaw d) ⊗ₘ bernKernel f hf = (uniformLaw d) ⊗ₘ bernKernel g hg) :
    Set.EqOn f g (cube d) := by
  have hcube : MeasurableSet (cube d) := by
    have heq : cube d = ⋂ i : Fin d, (fun x : Cov d => x i) ⁻¹' Icc (0 : ℝ) 1 := by
      ext x; simp [cube]
    rw [heq]
    exact MeasurableSet.iInter fun i => measurableSet_Icc.preimage (by fun_prop)
  let fc := bernKernel (fun x => versionClip (f x)) (by fun_prop)
  let gc := bernKernel (fun x => versionClip (g x)) (by fun_prop)
  let : IsMarkovKernel fc := bernKernel_versionClip_markov f hf
  let : IsMarkovKernel gc := bernKernel_versionClip_markov g hg
  have hfc : bernKernel f hf =ᵐ[uniformLaw d] fc := by
    filter_upwards [ae_restrict_mem hcube] with x hx
    change bern (f x) = bern (versionClip (f x))
    rw [versionClip_eq _ (hfprob x hx)]
  have hgc : bernKernel g hg =ᵐ[uniformLaw d] gc := by
    filter_upwards [ae_restrict_mem hcube] with x hx
    change bern (g x) = bern (versionClip (g x))
    rw [versionClip_eq _ (hgprob x hx)]
  have heq : fc =ᵐ[uniformLaw d] gc := Kernel.ae_eq_of_compProd_eq
    ((Measure.compProd_congr hfc).symm.trans (hm.trans (Measure.compProd_congr hgc)))
  apply uniformLaw_continuous_versions f g hfcont hgcont
  filter_upwards [hfc, hgc, heq, ae_restrict_mem hcube] with x hfx hgx hx hxc
  have hb : bern (f x) = bern (g x) := hfx.trans (hx.trans hgx.symm)
  have ht := congrArg (fun μ : Measure Bool => μ {true}) hb
  simp [bern] at ht
  exact (ENNReal.ofReal_eq_ofReal_iff (hfprob x hxc).1 (hgprob x hxc).1).mp ht

/-- Full support of the uniform design and continuity make admissible versions unique
on the closed cube, including its boundary.  Given [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input Q](hyp:Q), [the specified input hP](hyp:hP), [the specified input hQ](hyp:hQ), [the specified input hlaw](hyp:hlaw), [the admissible versions unique conclusion](goal) holds. -/
lemma admissible_versions_unique {alpha beta gamma L eps : ℝ} (P Q : PrimitiveLaw d)
    (hP : PrimitiveClass alpha beta gamma L eps P) (hQ : PrimitiveClass alpha beta gamma L eps Q)
    (hlaw : P.law = Q.law) :
    ∀ x ∈ cube d, designatedPropensity P hP x = designatedPropensity Q hQ x ∧
      designatedControl P hP x = designatedControl Q hQ x ∧
      designatedTreated P hP x = designatedTreated Q hQ x ∧ tau P hP x = tau Q hQ x := by
  let W := canonicalLaw P hP
  let V := canonicalLaw Q hQ
  have hW := canonicalLaw_spec P hP
  have hV := canonicalLaw_spec Q hQ
  have hWV : W.law = V.law := hW.1.trans (hlaw.trans hV.1.symm)
  have hWu : W.law.map Prod.fst = uniformLaw d := hW.2.1
  have hVu : V.law.map Prod.fst = uniformLaw d := hV.2.1
  let : IsFiniteMeasure (uniformLaw d) := by
    rw [← hWu]
    infer_instance
  let := bernKernel_sfinite_of_margin W (fun w => w.2.1) (by fun_prop) W.e W.measurable_e W.margin_e
  let := bernKernel_sfinite_of_margin V (fun w => w.2.1) (by fun_prop) V.e V.measurable_e V.margin_e
  let := bernKernel_sfinite_of_margin W (fun w => w.2.2.1) (by fun_prop) W.mu0 W.measurable_mu0 W.margin_mu0
  let := bernKernel_sfinite_of_margin V (fun w => w.2.2.1) (by fun_prop) V.mu0 V.measurable_mu0 V.margin_mu0
  let := bernKernel_sfinite_of_margin W (fun w => w.2.2.2) (by fun_prop) W.mu1 W.measurable_mu1 W.margin_mu1
  let := bernKernel_sfinite_of_margin V (fun w => w.2.2.2) (by fun_prop) V.mu1 V.measurable_mu1 V.margin_mu1
  have hWe : ContinuousOn W.e (cube d) := holderNorm_continuousOn _ _ _ hW.2.2.2.2.1
  have hVe : ContinuousOn V.e (cube d) := holderNorm_continuousOn _ _ _ hV.2.2.2.2.1
  have hW0 : ContinuousOn W.mu0 (cube d) := holderNorm_continuousOn _ _ _ hW.2.2.2.2.2.1
  have hV0 : ContinuousOn V.mu0 (cube d) := holderNorm_continuousOn _ _ _ hV.2.2.2.2.2.1
  have hW1 : ContinuousOn W.mu1 (cube d) := by
    have hc := (holderNorm_continuousOn _ _ _ hW.2.2.2.2.2.2.1).add hW0
    change ContinuousOn (fun x => (W.mu1 x - W.mu0 x) + W.mu0 x) (cube d) at hc
    simpa only [Pi.add_apply, rawContrast, sub_add_cancel] using hc
  have hV1 : ContinuousOn V.mu1 (cube d) := by
    have hc := (holderNorm_continuousOn _ _ _ hV.2.2.2.2.2.2.1).add hV0
    change ContinuousOn (fun x => (V.mu1 x - V.mu0 x) + V.mu0 x) (cube d) at hc
    simpa only [Pi.add_apply, rawContrast, sub_add_cancel] using hc
  have he : Set.EqOn W.e V.e (cube d) := by
    apply bern_margin_versions_unique _ _ W.measurable_e V.measurable_e hWe hVe
    · exact hW.2.2.2.1.unit
    · exact hV.2.2.2.1.unit
    · rw [← hWu, ← W.margin_e, hWV, V.margin_e, hVu]
  have h0 : Set.EqOn W.mu0 V.mu0 (cube d) := by
    apply bern_margin_versions_unique _ _ W.measurable_mu0 V.measurable_mu0 hW0 hV0
    · intro x hx; have hb := hW.2.2.2.2.2.2.2.1 x hx; constructor <;> linarith [hb.1, hb.2]
    · intro x hx; have hb := hV.2.2.2.2.2.2.2.1 x hx; constructor <;> linarith [hb.1, hb.2]
    · rw [← hWu, ← W.margin_mu0, hWV, V.margin_mu0, hVu]
  have h1 : Set.EqOn W.mu1 V.mu1 (cube d) := by
    apply bern_margin_versions_unique _ _ W.measurable_mu1 V.measurable_mu1 hW1 hV1
    · intro x hx; have hb := hW.2.2.2.2.2.2.2.2 x hx; constructor <;> linarith [hb.1, hb.2]
    · intro x hx; have hb := hV.2.2.2.2.2.2.2.2 x hx; constructor <;> linarith [hb.1, hb.2]
    · rw [← hWu, ← W.margin_mu1, hWV, V.margin_mu1, hVu]
  intro x hx
  have hex := he hx
  have h0x := h0 hx
  have h1x := h1 hx
  simpa only [designatedPropensity, designatedControl, designatedTreated, tau, if_pos hx]
    using (show W.e x = V.e x ∧ W.mu0 x = V.mu0 x ∧ W.mu1 x = V.mu1 x ∧
      W.mu1 x - W.mu0 x = V.mu1 x - V.mu0 x from
        ⟨hex, h0x, h1x, congrArg₂ (fun a b : ℝ => a - b) h1x h0x⟩)

/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [big delta](goal) is the corresponding construction. -/
def bigDelta (d : ℕ) (alpha beta gamma : ℝ) : ℝ := 2*gamma + d + gamma*d/(alpha+beta) -- @realizes Delta(tuning denominator)
/-- Given [the specified input d](hyp:d), [the specified input gamma](hyp:gamma), [s crit](goal) is the corresponding construction. -/
def sCrit (d : ℕ) (gamma : ℝ) : ℝ := gamma*d/(2*gamma+d) -- @realizes Scrit(smoothness cutoff)
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [q star](goal) is the corresponding construction. -/
def qStar (d : ℕ) (alpha beta gamma : ℝ) : ℝ := gamma*d/((alpha+beta)*(2*gamma+d)) -- @realizes qstar(record exponent)
/-- Given [the specified input d](hyp:d), [the specified input gamma](hyp:gamma), [the specified input n](hyp:n), [oracle rate](goal) is the corresponding construction. -/
def oracleRate (d : ℕ) (gamma : ℝ) (n : ℕ) : ℝ := (n:ℝ)^(-(gamma/(2*gamma+d))) -- @realizes ro(oracle order)
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input n](hyp:n), [the specified input m](hyp:m), [upper rate](goal) is the corresponding construction. -/
def upperRate (d : ℕ) (alpha beta gamma : ℝ) (n m : ℕ) : ℝ :=
  max (oracleRate d gamma n) (((n:ℝ)*((n:ℝ)+m))^(-(gamma/bigDelta d alpha beta gamma))) -- @realizes rup(upper rate)
-- @node: def:sharp-rate
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input n](hyp:n), [the specified input m](hyp:m), [sharp rate](goal) is the corresponding construction. -/
def sharpRate (d : ℕ) (alpha beta gamma : ℝ) (n m : ℕ) : ℝ :=
  max ((n:ℝ)^(-(gamma/(2*gamma+d))))
    (((n:ℝ)*((n:ℝ)+m))^(-(gamma/(2*gamma+d+gamma*d/(alpha+beta))))) -- @realizes rstar(sharp closed form)
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input n](hyp:n), [the specified input m](hyp:m), [the sharp rate eq upper rate conclusion](goal) holds. -/
lemma sharpRate_eq_upperRate (d : ℕ) (alpha beta gamma : ℝ) (n m : ℕ) :
    sharpRate d alpha beta gamma n m = upperRate d alpha beta gamma n m := by
  rfl
-- @node: def:annotation-region
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input zeta](hyp:zeta), [annotation region](goal) is the corresponding construction. -/
def annotationRegion (d : ℕ) (alpha beta gamma zeta : ℝ) : Set (ℕ × ℕ) :=
  {p | 2 ≤ p.1 ∧ sharpRate d alpha beta gamma p.1 p.2 ≤ zeta * oracleRate d gamma p.1} -- @realizes Bstar(oracle-attainment region) @realizes zeta(tolerance input)

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

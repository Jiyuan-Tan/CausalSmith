module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Basic
public import Causalean.Stat.Minimax.MinimaxValue
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Experiment

Two-channel point-CATE annotation frontier: Experiment
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


-- @env: S2
variable {d n m : ℕ}
/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [dataset](goal) is the corresponding construction. -/
abbrev Dataset (d n m : ℕ) := (Fin n → Cov d × Bool × Bool) × (Fin m → Cov d × Bool) -- @realizes D(two original record blocks)
/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [sample](goal) is the corresponding construction. -/
abbrev Sample (d n m : ℕ) := Dataset d n m × ℝ -- @realizes U(randomizer coordinate)
/-- Given [the specified input P](hyp:P), [the specified input n](hyp:n), [the specified input m](hyp:m), [experiment](goal) is the corresponding construction. -/
def experiment (P : PrimitiveLaw d) (n m : ℕ) : Measure (Sample d n m) :=
  ((Measure.pi fun _ : Fin n => obsLaw P).prod (Measure.pi fun _ : Fin m => xaLaw P)).prod
    (volume.restrict (Icc 0 1)) -- @realizes E(independent two-block experiment) @realizes U(uniform independent randomizer)
/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [decision](goal) is the corresponding construction. -/
abbrev Decision (d n m : ℕ) := {T : Sample d n m → ℝ // Measurable T} -- @realizes T(Borel decisions)
/-- Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [oracle decision](goal) is the corresponding construction. -/
abbrev OracleDecision (d n m : ℕ) :=
  {T : Sample d n m → (Cov d → ℝ) → ℝ // ∀ e, Measurable (fun w => T w e)} -- @realizes Te(Borel with supplied propensity)
-- @node: ass:sample-law
/-- Given [the specified input P](hyp:P), [the specified input n](hyp:n), [the specified input m](hyp:m), [sample law](goal) is the corresponding construction. -/
def SampleLaw (P : PrimitiveLaw d) (n m : ℕ) (μ : Measure (Sample d n m)) : Prop := μ = experiment P n m
-- @node: def:risk
/-- Given [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input T](hyp:T), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [risk](goal) is the corresponding construction. -/
def risk {alpha beta gamma L eps : ℝ} (T : Decision d n m) (P : PrimitiveLaw d)
    (hP : PrimitiveClass alpha beta gamma L eps P) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal |T.1 w - tau P hP (x0 d)| ∂experiment P n m -- @realizes risk(extended absolute loss)
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input T](hyp:T), [the specified input P](hyp:P), [class risk](goal) is the corresponding construction. -/
def classRisk (d : ℕ) (alpha beta gamma L eps : ℝ) (n m : ℕ) (T : Decision d n m)
    (P : {P : PrimitiveLaw d // PrimitiveClass alpha beta gamma L eps P}) : ℝ≥0∞ := risk T P.1 P.2
-- @node: def:minimax
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input n](hyp:n), [the specified input m](hyp:m), [minimax risk](goal) is the corresponding construction. -/
def minimaxRisk (d : ℕ) (alpha beta gamma L eps : ℝ) (n m : ℕ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal (classRisk d alpha beta gamma L eps n m) -- @realizes R(minimax value)
-- @node: def:oracle-risk
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input n](hyp:n), [the specified input m](hyp:m), [oracle risk](goal) is the corresponding construction. -/
def oracleRisk (d : ℕ) (alpha beta gamma L eps : ℝ) (n m : ℕ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal
    (fun (T : OracleDecision d n m) (P : {P : PrimitiveLaw d // PrimitiveClass alpha beta gamma L eps P}) =>
      ∫⁻ w, ENNReal.ofReal |T.1 w (designatedPropensity P.1 P.2) - tau P.1 P.2 (x0 d)| ∂experiment P.1 n m) -- @realizes Re(supplied-propensity minimax)

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

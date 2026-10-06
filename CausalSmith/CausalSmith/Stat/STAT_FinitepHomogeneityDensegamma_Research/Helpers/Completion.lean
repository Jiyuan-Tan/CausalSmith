module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Basic
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.Kernel.Composition.Prod

/-! Finite-moment homogeneity testing: Helpers/Completion. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Bernmeasure: the displayed mathematical construction or bound. This statement assumes [the e parameter](hyp:e), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def bernMeasure (e : Nuisance) (x : unitInterval) : Measure Bool :=
  ENNReal.ofReal (e x) • Measure.dirac true+ENNReal.ofReal (1-e x) • Measure.dirac false
/-- The explicit bernMeasure construction is Borel measurable. [This is the stated conclusion](goal). -/
-- @node: measurable_bernMeasure
@[fun_prop] lemma measurable_bernMeasure (e : Nuisance) : Measurable (bernMeasure e) := by
  unfold bernMeasure
  fun_prop
/-- Bernkernel: the displayed mathematical construction or bound. This statement assumes [the law parameter](hyp:law). [This is the stated defined object](goal). -/
def bernKernel (law : ObservedLaw) : Kernel unitInterval Bool := ⟨bernMeasure law.e,measurable_bernMeasure law.e⟩
/-- Causalrecord: the displayed mathematical construction or bound. [This is the stated defined object](goal). -/
abbrev CausalRecord := unitInterval × Bool × ℝ × ℝ
/-- [Conditional independent-arm causal realization](goal). \(\mathbb Q_P(dx,dy_0,dy_1,da)=\lambda(dx)Q_{0,P}(dy_0\mid x)Q_{1,P}(dy_1\mid x)e_P(x)^a(1-e_P(x))^{1-a},\quad Y=(1-A)Y(0)+AY(1)\). Kernel changes on \(\lambda\)-null sets leave \(\mathbb Q_P\) unchanged. This statement assumes [the law parameter](hyp:law). -/
-- @node: def:causal-completion
def causalCompletion (law : ObservedLaw) : Measure CausalRecord :=
  design ⊗ₘ ((bernKernel law).prod ((law.Q false).prod (law.Q true))) -- @realizes Causal(conditionally independent-arm completion)
/-- Completion probability: the displayed mathematical construction or bound.  [the parameters and conditions in the statement](hyp:law), [the asserted mathematical result holds](goal). -/
-- @node: completion_probability
lemma completion_probability (law : ObservedLaw) : IsProbabilityMeasure (causalCompletion law) := by
  have hbern : IsMarkovKernel (bernKernel law) := by
    constructor
    intro x
    constructor
    change bernMeasure law.e x Set.univ = 1
    simp only [bernMeasure, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem, Set.mem_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (law.e_range x).1 (sub_nonneg.mpr (law.e_range x).2)]
    norm_num
  let : IsMarkovKernel (bernKernel law) := hbern
  let : IsProbabilityMeasure design := by
    change IsProbabilityMeasure (volume : Measure unitInterval)
    infer_instance
  unfold causalCompletion
  infer_instance
/-- The bundled carrier supplies its declared mathematical structure. This statement assumes [the law parameter](hyp:law). [This is the stated defined object](goal). -/
instance (law : ObservedLaw) : IsProbabilityMeasure (causalCompletion law) := completion_probability law
/-- Completionx: the displayed mathematical construction or bound. This statement assumes [the r parameter](hyp:r). [This is the stated defined object](goal). -/
def completionX (r : CausalRecord) : unitInterval := r.1
/-- Completiona: the displayed mathematical construction or bound. This statement assumes [the r parameter](hyp:r). [This is the stated defined object](goal). -/
def completionA (r : CausalRecord) : Bool := r.2.1
/-- Y0: the displayed mathematical construction or bound. This statement assumes [the r parameter](hyp:r). [This is the stated defined object](goal). -/
def Y0 (r : CausalRecord) : ℝ := r.2.2.1 -- @realizes Yzero(control potential outcome)
/-- Y1: the displayed mathematical construction or bound. This statement assumes [the r parameter](hyp:r). [This is the stated defined object](goal). -/
def Y1 (r : CausalRecord) : ℝ := r.2.2.2 -- @realizes Yone(treated potential outcome)
/-- Observe: the displayed mathematical construction or bound. This statement assumes [the r parameter](hyp:r). [This is the stated defined object](goal). -/
def observe (r : CausalRecord) : Record := (completionX r,completionA r,if completionA r then Y1 r else Y0 r)
/-- The explicit completionX construction is Borel measurable. [This is the stated conclusion](goal). -/
-- @node: measurable_completionX
@[fun_prop] lemma measurable_completionX : Measurable completionX := by
  unfold completionX
  fun_prop

end CausalSmith.Stat.FinitepHomogeneityDensegamma

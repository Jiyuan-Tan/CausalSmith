module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Basic
public import Causalean.Stat.Minimax.TotalVariation

/-! Finite-moment homogeneity testing: Helpers/Testing. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Standing sample-size domain of the public experiment. This statement assumes [the n parameter](hyp:n). [This is the stated defined object](goal). -/
def SampleSizeDomain (n : ℕ) : Prop := 2 ≤ n -- @realizes n(standing domain n≥2)
/-- Standing domain of the positive separation argument. This statement assumes [the r parameter](hyp:r). [This is the stated defined object](goal). -/
def SeparationDomain (r : ℝ) : Prop := 0 < r -- @realizes r(standing positive separation)
-- @env: S2
variable (n : ℕ) (v : Params) (r : ℝ) -- @realizes n(natural carrier; range via SampleSizeDomain) @realizes r(real carrier; range via SeparationDomain)
variable (hn : SampleSizeDomain n) (hr : SeparationDomain r)
/-- Jointly Borel randomized rejection maps. This statement assumes [the n parameter](hyp:n). [This is the stated defined object](goal). -/
def Test := {φ : Experiment n → ℝ // Measurable φ ∧ ∀ z, 0 ≤ φ z ∧ φ z ≤ 1} -- @realizes phi(measurable [0,1]-valued map)
/-- The rejection expectation integrates the test against the iid law and independent seed. This statement assumes [the n parameter](hyp:n), [the P parameter](hyp:P), [the φ parameter](hyp:φ). [This is the stated defined object](goal). -/
def rejectProb (P : Measure Record) (φ : Test n) : ℝ := ∫ z, φ.1 z ∂expLaw n P -- @realizes Risk(rejection expectation)
/-- A test has level at most one tenth on every law in the composite null. This statement assumes [the n parameter](hyp:n), [the Null parameter](hyp:Null), [the φ parameter](hyp:φ). [This is the stated defined object](goal). -/
def LevelValid (Null : Set ObservedLaw) (φ : Test n) : Prop := ∀ law ∈ Null, rejectProb n law.P φ ≤ 1/10
/-- Minimize worst-alternative type-II error over all tests satisfying the whole-null level constraint. This statement assumes [the n parameter](hyp:n), [the r parameter](hyp:r), [the Null parameter](hyp:Null), [the Alt parameter](hyp:Alt). [This is the stated defined object](goal). -/
def testingRiskOn (Null Alt : Set ObservedLaw) : ℝ :=
  ⨅ φ : {φ : Test n // LevelValid n Null φ},
  ⨆ law : {law : ObservedLaw // law ∈ Alt ∧ r ≤ hetDist law}, 1-rejectProb n law.1.P φ.1
/-- [Full original-record testing decision problem](goal). \(B_n(v,r)=\inf_{\phi:\ \sup_{P\in H_0(v)}\mathsf R_n(P,\phi)\le1/10}\ \sup_{P\in\mathcal M_v:\ d(P)\ge r}\{1-\mathsf R_n(P,\phi)\},\quad n\ge2,\ v\in\mathcal V,\ 0<r<D_v\). This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the r parameter](hyp:r). -/
-- @node: def:testing-risk
def testingRisk : ℝ := testingRiskOn n r {law | InNull v law} {law | InModel v law} -- @realizes B(composite-null infimum supremum)
/-- Take the infimum of successful positive separations together with the model-maximum sentinel. This statement assumes [the D parameter](hyp:D), [the B parameter](hyp:B). [This is the stated defined object](goal). -/
def cappedRadius (D : ℝ) (B : ℝ → ℝ) : ℝ := sInf ({r | 0 < r ∧ r < D ∧ B r ≤ 1/10} ∪ {D})
/-- [Capped critical radius with sentinel](goal). \(r_n^*(v)=\inf\bigl(\{r\in(0,D_v):B_n(v,r)\le1/10\}\cup\{D_v\}\bigr)\). This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). -/
-- @node: def:critical-radius
def criticalRadius : ℝ := cappedRadius (maxDist v) (testingRisk n v) -- @realizes rstar(capped infimum)
/-- [Bounded full-record decision problem](goal). \(B_n^{\mathrm b}(w,r)=\inf_{\phi:\sup_{P\in H_0^{\mathrm b}(w)}\mathsf R_n(P,\phi)\le1/10}\sup_{P\in\mathcal M^{\mathrm b}_w:d(P)\ge r}\{1-\mathsf R_n(P,\phi)\},\quad n\ge2,\ w\in\mathcal W,\ 0<r<D_w^{\mathrm b}\). This statement assumes [the n parameter](hyp:n), [the w parameter](hyp:w), [the r parameter](hyp:r). -/
-- @node: def:bounded-risk
def boundedTestingRisk (n : ℕ) (w : Smooth3) (r : ℝ) : ℝ := testingRiskOn n r {law | InBoundedNull w law} {law | InBoundedModel w law} -- @realizes Bbound(bounded risk)
/-- [Signed-binary full-record decision problem](goal). \(B_n^{\mathrm{bin}}(w,r)=\inf_{\phi:\sup_{P\in H_0^{\mathrm{bin}}(w)}\mathsf R_n(P,\phi)\le1/10}\sup_{P\in\mathcal M^{\mathrm{bin}}_w:d(P)\ge r}\{1-\mathsf R_n(P,\phi)\},\quad n\ge2,\ w\in\mathcal W,\ 0<r<D_w^{\mathrm{bin}}\). This statement assumes [the n parameter](hyp:n), [the w parameter](hyp:w), [the r parameter](hyp:r). -/
-- @node: def:binary-risk
def binaryTestingRisk (n : ℕ) (w : Smooth3) (r : ℝ) : ℝ := testingRiskOn n r {law | InBinaryNull w law} {law | InBinaryModel w law} -- @realizes Bbin(binary risk)
/-- [Capped bounded critical radius](goal). \(r_n^{*,\mathrm b}(w)=\inf(\{r\in(0,D_w^{\mathrm b}):B_n^{\mathrm b}(w,r)\le1/10\}\cup\{D_w^{\mathrm b}\})\). This statement assumes [the n parameter](hyp:n), [the w parameter](hyp:w). -/
-- @node: def:bounded-radius
def boundedCriticalRadius (w : Smooth3) : ℝ := cappedRadius (maxDistBounded w) (boundedTestingRisk n w) -- @realizes rstarbound(bounded capped radius)
/-- [Capped signed-binary critical radius](goal). \(r_n^{*,\mathrm{bin}}(w)=\inf(\{r\in(0,D_w^{\mathrm{bin}}):B_n^{\mathrm{bin}}(w,r)\le1/10\}\cup\{D_w^{\mathrm{bin}}\})\). This statement assumes [the n parameter](hyp:n), [the w parameter](hyp:w). -/
-- @node: def:binary-radius
def binaryCriticalRadius (w : Smooth3) : ℝ := cappedRadius (maxDistBinary w) (binaryTestingRisk n w) -- @realizes rstarbin(binary capped radius)
/-- Supplied-propensity tests are joint Borel maps of a continuous function, original dataset and public seed. This statement assumes [the n parameter](hyp:n). [This is the stated defined object](goal). -/
def OracleTest := {φ : Nuisance × Experiment n → ℝ // Measurable φ ∧ ∀ z, 0 ≤ φ z ∧ φ z ≤ 1} -- @realizes phior(joint Borel map with supplied function)
/-- Evaluate the supplied-propensity test at the entire true continuous propensity before integrating. This statement assumes [the n parameter](hyp:n), [the law parameter](hyp:law), [the φ parameter](hyp:φ). [This is the stated defined object](goal). -/
def oracleRejectProb (law : ObservedLaw) (φ : OracleTest n) : ℝ := ∫ z, φ.1 (law.e,z) ∂expLaw n law.P -- @realizes Riskor(supplied-propensity expectation)
/-- [Same-class supplied-propensity experiment](goal). \(B_n^{\mathrm e}(v,r)=\inf_{\phi^{\mathrm e}:\ \sup_{P\in H_0(v)}\mathsf R_n^{\mathrm e}(P,\phi^{\mathrm e})\le1/10}\ \sup_{P\in\mathcal M_v:\ d(P)\ge r}\{1-\mathsf R_n^{\mathrm e}(P,\phi^{\mathrm e})\},\quad n\ge2,\ v\in\mathcal V,\ 0<r<D_v\). This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the r parameter](hyp:r). -/
-- @node: def:oracle-risk
def oracleTestingRisk : ℝ :=
  ⨅ φ : {φ : OracleTest n // ∀ law, InNull v law → oracleRejectProb n law φ ≤ 1/10},
  ⨆ law : {law : ObservedLaw // InModel v law ∧ r ≤ hetDist law}, 1-oracleRejectProb n law.1 φ.1 -- @realizes Bor(same-class supplied-propensity risk)
/-- [Supplied-propensity capped radius](goal). \(r_n^{*,\mathrm e}(v)=\inf\bigl(\{r\in(0,D_v):B_n^{\mathrm e}(v,r)\le1/10\}\cup\{D_v\}\bigr)\). This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). -/
-- @node: def:oracle-radius
def oracleCriticalRadius : ℝ := cappedRadius (maxDist v) (oracleTestingRisk n v) -- @realizes rstaror(oracle capped radius)
/-- [Broader oracle risk with the unchanged supplied-function interface](goal). For n >= 2 and 0 < r < maxDistOracle v, minimize the worst separated-alternative type-II error over the existing jointly Borel OracleTest maps with level at most 1/10 on InOracleNull. Evaluation still supplies law.e to the original iid sample and public seed. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the r parameter](hyp:r). -/
-- @node: def:oracle-broad-risk
def oracleBroadTestingRisk : ℝ :=
  ⨅ φ : {φ : OracleTest n // ∀ law, InOracleNull v law → oracleRejectProb n law φ ≤ 1/10},
  ⨆ law : {law : ObservedLaw // InOracleModel v law ∧ r ≤ hetDist law},
    1-oracleRejectProb n law.1 φ.1 -- @realizes BoracleBroad(level-constrained infimum of broader-alternative errors)
/-- [Broader oracle capped critical radius](goal). The infimum of successful separations in (0,maxDistOracle v), together with the same model-maximum saturation sentinel as the existing capped radius. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). -/
-- @node: def:oracle-broad-radius
def oracleBroadCriticalRadius : ℝ :=
  cappedRadius (maxDistOracle v) (oracleBroadTestingRisk n v) -- @realizes rstaroracleBroad(broader-model capped infimum)
/-- [Matched heavy-tail versus bounded phase handle](goal). The defined object is exactly the capped-radius ratio \[\Delta_n(v)=\frac{r_n^*(v)}{r_n^{*,\mathrm b}(w)},\qquad w=(\alpha,\beta,\gamma).\] Both numerator and denominator are the capped critical radii of the original-record experiments in Definition \(\mathrm{def:testing\mbox{-}risk}\) and its bounded analogue, at the same sample size and matched smoothness tuple. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). -/
-- @node: def:comparison-handle
def radiusRatio : ℝ := criticalRadius n v / boundedCriticalRadius n v.toSmooth3 -- @realizes Delta(matched radius ratio)
/-- [Strict conditional-tail enlargement set](goal).
\(\mathcal T=\{v\in\mathcal V:p<2,\ \lim_{n\to\infty}\Delta_n(v)=\infty\}\).
-/
-- @node: def:tail-region
def tailRegion : Set Params := {v | v.Valid ∧ v.p < 2 ∧ Filter.Tendsto (fun n : ℕ => radiusRatio n v) Filter.atTop Filter.atTop} -- @realizes TailRegion(strict enlargement)
/-- [Bounded-order retention set](goal).
\(\mathcal E=\{v\in\mathcal V:\sup_{n\ge2}\Delta_n(v)<\infty\}\).
-/
-- @node: def:equality-region
def equalityRegion : Set Params := {v | v.Valid ∧ BddAbove ((fun n : ℕ => radiusRatio n v) '' {n | 2 ≤ n})} -- @realizes EqualityRegion(bounded ratios)
/-- [Order-preservation set](goal).
\(\mathcal R=\{v\in\mathcal V:\ \sup_{n\ge2}r_n^*(v)/r_n^{*,\mathrm e}(v)<\infty\}\).
-/
-- @node: def:preservation-region
def preservationRegion : Set Params := {v | v.Valid ∧ BddAbove ((fun n : ℕ => criticalRadius n v / oracleCriticalRadius n v) '' {n | 2 ≤ n})} -- @realizes Region(oracle-order preservation)
/-- Reuse the substrate supremum of measurable-event probability gaps. This statement assumes [the μ parameter](hyp:μ), [the ν parameter](hyp:ν). [This is the stated defined object](goal). -/
abbrev totalVariation {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) : ℝ := Causalean.Stat.tvDist μ ν -- @realizes TV(supremum measurable-event mass gap)

end CausalSmith.Stat.FinitepHomogeneityDensegamma

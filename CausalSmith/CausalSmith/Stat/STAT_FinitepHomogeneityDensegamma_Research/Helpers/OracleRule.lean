module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Scales
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ProjectionGeometry

/-! Finite-moment homogeneity testing: Helpers/OracleRule. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Extend the supplied-function rule by clipping its values into the fixed overlap envelope. This statement assumes [the f parameter](hyp:f), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def clipProp (f : Nuisance) (x : unitInterval) : ℝ := max (1/4) (min (f x) (3/4))
/-- The clipped inverse-propensity score uses the two observed treatment arms. This statement assumes [the f parameter](hyp:f), [the T parameter](hyp:T), [the o parameter](hyp:o). [This is the stated defined object](goal). -/
def ipwScore (f : Nuisance) (T : ℝ) (o : Record) : ℝ :=
  treatment o*clipY T (Y o)/clipProp f (X o)-(1-treatment o)*clipY T (Y o)/(1-clipProp f (X o))
/-- The untruncated inverse-propensity score targets the original conditional mean effect. This statement assumes [the f parameter](hyp:f), [the o parameter](hyp:o). [This is the stated defined object](goal). -/
def ipwUntruncated (f : Nuisance) (o : Record) : ℝ :=
  treatment o*Y o/clipProp f (X o)-(1-treatment o)*Y o/(1-clipProp f (X o))
/-- Subtract the constant-coordinate projection of a histogram vector. This statement assumes [the z parameter](hyp:z). [This is the stated defined object](goal). -/
def centerVec {J : ℕ} (z : Vec J) : Vec J :=
  z-((∑ j : Fin J, z j)/(J:ℝ)) • WithLp.toLp 2 (fun _ : Fin J => (1:ℝ))
/-- The oracle block scale uses the pure tail testing exponent. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def oracleA (n : ℕ) (v : Params) : ℝ := (blockSize n:ℝ)^(-E0 v)
/-- The oracle outcome cutoff rounds the pure tail bias target upward dyadically. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def oracleT (n : ℕ) (v : Params) : ℝ := dyadUp (oracleA n v^(-1/(v.p-1)))
/-- The oracle rank rounds the effect approximation target upward dyadically. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def oracleJ (n : ℕ) (v : Params) : ℕ := leastPow2Ge (oracleA n v^(-1/v.γ))
/-- Average centered histogram features weighted by the clipped observed inverse-propensity score. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the f parameter](hyp:f), [the b parameter](hyp:b), [the data parameter](hyp:data). [This is the stated defined object](goal). -/
def oracleBlockVec (n : ℕ) (v : Params) (f : Nuisance) (b : Bool) (data : Dataset n) : Vec (oracleJ n v) :=
  (blockSize n:ℝ)⁻¹ • ∑ i ∈ evalBlock n b,
    ipwScore f (oracleT n v) (data i) • centerVec (featureMap (oracleJ n v) (X (data i)))
/-- The oracle clipping bias budget is twenty times cutoff to the one-minus-moment power. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def oracleBias (n : ℕ) (v : Params) : ℝ := 20*oracleT n v^(1-v.p)
/-- The oracle covariance budget is eighty times clipped second-moment scale divided by block size. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def oracleCov (n : ℕ) (v : Params) : ℝ := 80*oracleT n v^(2-v.p)/(blockSize n:ℝ)
/-- Reject when the independent oracle-block inner product exceeds the public bias and covariance cutoff. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the z parameter](hyp:z). [This is the stated defined object](goal). -/
def oracleRule (n : ℕ) (v : Params) (z : Nuisance × Experiment n) : ℝ :=
  if 2*oracleBias n v^2+1024*Real.sqrt (oracleJ n v)*oracleCov n v <
    inner ℝ (oracleBlockVec n v z.1 false z.2.1) (oracleBlockVec n v z.1 true z.2.1) then 1 else 0
/-- Centering is a continuous linear operation on histogram coordinates. [This is the stated conclusion](goal). -/
-- @node: continuous_centerVec
@[fun_prop] lemma continuous_centerVec (J : ℕ) : Continuous (@centerVec J) := by
  unfold centerVec
  fun_prop

/-- The oracle score is jointly measurable in the supplied propensity and original record. [This is the stated conclusion](goal). -/
-- @node: measurable_ipwScore
@[fun_prop] lemma measurable_ipwScore (T : ℝ) :
    Measurable (fun z : Nuisance × Record => ipwScore z.1 T z.2) := by
  have ht : Measurable treatment := by
    unfold treatment A
    exact (measurable_of_countable (fun b : Bool => if b then (1:ℝ) else 0)).comp
      (measurable_fst.comp measurable_snd)
  unfold ipwScore clipProp clipY X Y
  fun_prop

/-- A finite oracle block average is jointly measurable in the supplied function and data. [This is the stated conclusion](goal). -/
-- @node: measurable_oracleBlockVec
@[fun_prop] lemma measurable_oracleBlockVec (n : ℕ) (v : Params) (b : Bool) :
    Measurable (fun z : Nuisance × Experiment n => oracleBlockVec n v z.1 b z.2.1) := by
  unfold oracleBlockVec X
  fun_prop

/-- The explicit rejection rule is Borel measurable and takes values between zero and one.  [the parameters and conditions in the statement](hyp:n,v), [the asserted mathematical result holds](goal). -/
-- @node: oracleRule_test
lemma oracleRule_test (n : ℕ) (v : Params) : Measurable (oracleRule n v) ∧ ∀ z, 0 ≤ oracleRule n v z ∧ oracleRule n v z ≤ 1  := by
  constructor
  · unfold oracleRule
    apply Measurable.ite
    · apply measurableSet_lt <;> fun_prop
    · fun_prop
    · fun_prop
  · intro z
    unfold oracleRule
    split <;> norm_num
/-- [Supplied-propensity comparison handle](goal). The public supplied-propensity test uses s = floor(n/2), a = s^(−E0), T = 2^ceil(log₂(a^(−1/(p−1)))) and J = leastPow2Ge(a^(−1/γ)). Clip the supplied function into [1/4,3/4], center the histogram features, and form the two block averages of the clipped original inverse-propensity score. Reject exactly when their inner product exceeds 2 b² + 1024 √J Λ, with b = 20 T^(1−p) and Λ = 80 T^(2−p)/s. This is the specified dyadic rate-balancing selection on valid tuples and n ≥ 2. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). -/
-- @node: def:oracle-handle
def oracleTest (n : ℕ) (v : Params) : OracleTest n := ⟨oracleRule n v,oracleRule_test n v⟩ -- @realizes phistaror(explicit supplied-propensity rule)

end CausalSmith.Stat.FinitepHomogeneityDensegamma

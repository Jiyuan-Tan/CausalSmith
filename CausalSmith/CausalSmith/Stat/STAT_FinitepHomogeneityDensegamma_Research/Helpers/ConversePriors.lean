module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PairedTent

/-! Finite-moment homogeneity testing: Helpers/ConversePriors. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Use the rough copula channel only when it determines the phase and the public lower threshold has been reached. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def roughBranch (n : ℕ) (v : Params) : Prop := Fphase v < 1 ∧ Nlow v ≤ n
/-- The rough fine rank dyadically rounds the large fixed resolution multiplier times the sample power. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def roughK (n : ℕ) (v : Params) : ℕ := leastPow2Ge (Hfine*(n:ℝ)^(2/Dp v))
/-- The rough coarse rank rounds its smoothness target downward dyadically. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def roughM (n : ℕ) (v : Params) : ℕ := 2^(Nat.floor (Real.logb 2 ((roughK n v:ℝ)^(sumReg v/v.γ)/16)))
/-- Select the explicit rough-channel or paired-tent rare-mark probability. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def rarity (n : ℕ) (v : Params) : ℝ :=
  if roughBranch n v then (16:ℝ)^(-1/qExp v)*(roughK n v:ℝ)^(-v.β/qExp v) else tentRarity n v -- @realizes rarity(branchwise derived mark probability)
/-- Select the moment-normalized rough mark size or the paired-tent mark size. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def magnitude (n : ℕ) (v : Params) : ℝ :=
  if roughBranch n v then rarity n v^(-1/v.p) else tentMagnitude n v -- @realizes magnitude(branchwise derived mark size)
/-- [Tail-essential normalized full-record converse handle](goal). Select the explicit priors for valid tuples and n ≥ 2. When Fphase < 1 and n ≥ Nlow, use K = leastPow2Ge(Hfine n^(2/Dp)), M = 2^floor(log₂(K^(S/γ)/16)), a = K^(−α)/16, u = 1/16, ε = 16^(−1/q) K^(−β/q) and L = ε^(−1/p). Otherwise use the paired-tent priors with N = 2 ceil(n^(2q/(2γ+q))), h = 1/N, ε = h^(γ/q) and L = h^(−γ/(p−1)), control kernel δ₀, and treated masses ε(1 ± νκgσ)/2 at ±L and 1 − ε at zero. Mix the entire iid record laws. Legality, separation, mixture distance and divergence are proved by the converse theorem. This statement assumes [the ν parameter](hyp:ν), [the n parameter](hyp:n), [the v parameter](hyp:v). -/
-- @node: def:converse-handle
def conversePrior (ν : Bool) (n : ℕ) (v : Params) : FinitePrior :=
  if roughBranch n v then copulaPrior ν v (roughK n v) (roughM n v)
    ((roughK n v:ℝ)^(-v.α)/16) (1/16) (rarity n v) (magnitude n v)
  else tentPrior ν n v -- @realizes piNull(null branch at nu=0) @realizes piAlt(alternative branch at nu=1)
/-- Mix the complete iid records under the branchwise converse prior. This statement assumes [the ν parameter](hyp:ν), [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def converseMixture (ν : Bool) (n : ℕ) (v : Params) : Measure (Dataset n) :=
  priorMixture n (conversePrior ν n v) -- @realizes MixNull(null iid mixture) @realizes MixAlt(alternative iid mixture)
/-- Use the separate bounded copula tuning or signed-binary paired-tent family. This statement assumes [the ν parameter](hyp:ν), [the n parameter](hyp:n), [the w parameter](hyp:w). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. -/
def boundedConversePrior (ν : Bool) (n : ℕ) (w : Smooth3) : FinitePrior :=
  let v := Params.ofBounded w
  if roughBranch n v then copulaPrior ν v (roughK n v) (roughM n v)
    ((roughK n v:ℝ)^(-v.α)/16) (2*(roughK n v:ℝ)^(-v.β)/256) (1/2) 1
  else binaryTentPrior ν n w
/-- Mix the full iid laws from the bounded converse family. This statement assumes [the ν parameter](hyp:ν), [the n parameter](hyp:n), [the w parameter](hyp:w). [This is the stated defined object](goal). -/
def boundedConverseMixture (ν : Bool) (n : ℕ) (w : Smooth3) : Measure (Dataset n) := priorMixture n (boundedConversePrior ν n w)

end CausalSmith.Stat.FinitepHomogeneityDensegamma

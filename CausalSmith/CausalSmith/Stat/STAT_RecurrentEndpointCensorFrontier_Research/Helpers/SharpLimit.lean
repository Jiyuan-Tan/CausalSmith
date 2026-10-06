module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.LowerDirections

/-!
# Open sharp-limit question

The payloads preserve the proposed procedure and unresolved alternatives
without asserting that an exact limit experiment or constant exists.
-/

@[expose] public section

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

-- @node: def:sharp-limit-handle
def sharpLimitHandle : _root_.String :=
  "Localize the complete observed-history Poisson experiment along smooth " ++
  "endpoint intensity directions δλ_h and δλ_n^crit; compute its modulus " ++
  "for the causal count contrast θ; calibrate a bias-aware interval by the " ++
  "resulting limit experiment. This is an informal proposed procedure and " ++
  "asserts no output or existence theorem."
  -- @realizes H_sharp(proposed sharp-limit procedure)

-- @node: oeq:sharp-limit-experiment
def sharpLimitExperimentQuestion : _root_.String :=
  "Using H_sharp, the proposed sharp-limit procedure encoded by " ++
  "sharpLimitHandle — " ++ sharpLimitHandle ++ " — address the question " ++
  "for κ = 1 (critical logarithmic regime) and κ > 1 " ++
  "(supercritical regime): either characterize the local asymptotic " ++
  "experiment of the complete censored Poisson-history model and the exact " ++
  "minimax squared-risk and honest-length constants over P_{β,κ}, or prove " ++
  "that no single Gaussian-shift reduction is uniform over P_{β,κ}. " ++
  "The fixed-baseline tangent quadratic form is " ++
  "p₁ ∫₀¹ S₁(t) G₁(t) v(t)²/λ₁(t) dt and the target derivative is " ++
  "∫₀¹ S₁(t) v(t) dt. Neither alternative, exact constant, uniform " ++
  "equivalence, nor interval procedure is asserted here."

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

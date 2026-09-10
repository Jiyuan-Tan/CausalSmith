import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Basic

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-! Nonassertive carriers for the unresolved sharp-constant route and question. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

-- @node: def:constant-handle
/-- For [the specified overlap level](hyp:epsilon), the [sharp-constant handle is the three-step research program of local Poisson rescaling, sharp polynomial bias-variance optimization, and dual moment-matching](goal). -/
def sharpConstantHandle (epsilon : ℝ) : _root_.List _root_.String :=
  ["rescale the pilot-local four-cell rectangles by their Poisson noise geometry",
   "optimize the tensor-polynomial bias-variance functional for the globally Lipschitz cell extension at the fixed overlap constant",
   "dualize the approximation constraint into moment-matched observed laws in the overlap class for the optimal-regression target"]
  -- @realizes \(\mathscr H_\epsilon^{\mathrm{const}}\)(three-step open derivation route)

-- @node: oeq:sharp-overlap-constant
/-- For [the specified overlap level](hyp:epsilon), the [sharp-overlap-constant question asks whether the normalized nonsaturated minimax risk converges to a positive finite limit and whether the sharp-constant program yields an attaining estimator](goal). -/
def sharpOverlapConstantQuestion (epsilon : ℝ) : _root_.String :=
  "Along nonsaturated sequences d tending to infinity with d/(n log(ed)) tending to zero, does (n log(ed)/d) times the minimax risk converge to a finite positive limit, and is an estimator attaining it derivable through the sharp-constant handle? The matched frontier proves only positive finite liminf/limsup bounds; it asserts neither convergence, a cone-dependent optimal leading constant, nor an attaining estimator."

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreLedger

/-! Finite-moment homogeneity testing: Helpers/Scales. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


-- @env: S3
variable (n : ℕ) (v : Params)
/-- [Explicit matched scales, multipliers and public thresholds](goal). For \(v\in\mathcal V\), put \[ q=(p-1)/p,\quad S=\alpha+\beta,\quad D_p=1+2\alpha+\beta/q+S/(2\gamma),\quad E_0(p)=\frac{2\gamma q}{2\gamma+q},\quad E_4(p)=\frac{2S}{D_p}, \quad F(p)=\frac{2\alpha}{p-1}+\frac\beta q+\frac S{2\gamma}, \quad E(p)=\min\{E_0(p),E_4(p)\}. \] Here arguments \(p\) in \(E_0,E_4,F,E\) retain the same \((\alpha,\beta,\gamma)\). Define \[ H_{\mathrm{fine}}=2^{40},\quad N_{\mathrm{low}}(v)=\left\lceil\max\{2,32^{D_p\gamma/(2S)}\}\right\rceil, \quad k_v=2^{-17}(2H_{\mathrm{fine}})^{-S},\quad c_0^{\mathrm e}=4^{-\gamma}/(16\sqrt3). \] The sharp scales and lower multipliers are \[ \rho_n(v)=n^{-E(p)},\qquad \rho_n^{\mathrm b}(w)=n^{-E(2)},\qquad c_v=\begin{cases} c_0^{\mathrm e},&F(p)\ge1,\\ \min\{k_v,c_0^{\mathrm e}N_{\mathrm{low}}(v)^{-(E_0(p)-E_4(p))}\},&F(p)<1, \end{cases} \qquad c_w^{\mathrm b}=c_{(2,w)}. \] Take \(C_v=C^{\mathrm{att}}_v\), \(N_v=N^{\mathrm{att}}_v\) with the fully evaluable formulas of Theorem \(\mathrm{thm:original\mbox{-}record\mbox{-}attainable\mbox{-}rate}\); take \(C_w^{\mathrm b}=C^{\mathrm{att}}_{(2,w)}\), \(N_w^{\mathrm b}=N^{\mathrm{att}}_{(2,w)}\). The rule \(\phi^*_{n,v}\) is exactly the total original-record rule of Definition \(\mathrm{def:explicit\mbox{-}score\mbox{-}ledger}\); \(\phi^{*,\mathrm b}_{n,w}\) is the same rule at tuple \((2,w)\). These definitions name scales and rules; their sharpness is a conclusion of the full-record lower and attainment proofs. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). -/
-- @node: def:sharp-frontier-scales
def rho : ℝ := (n:ℝ)^(-Eexp v) -- @realizes rho(unknown-propensity pure power)
/-- Evaluate the entire-class scale at moment exponent two. This statement assumes [the n parameter](hyp:n), [the w parameter](hyp:w). [This is the stated defined object](goal). -/
def rhoBounded (n : ℕ) (w : Smooth3) : ℝ := rho n (Params.ofBounded w) -- @realizes rhobound(matched bounded power)
/-- The supplied-propensity scale uses the pure tail exponent. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def rhoOracle (n : ℕ) (v : Params) : ℝ := (n:ℝ)^(-E0 v) -- @realizes rhoor(oracle power)
/-- The fixed fine-resolution multiplier is two to the fortieth power. [This is the stated defined object](goal). -/
def Hfine : ℝ := 2^40
/-- The public lower threshold rounds the rough-channel geometric feasibility target upward. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def Nlow (v : Params) : ℕ := Nat.ceil (max 2 ((32:ℝ)^(Dp v*v.γ/(2*sumReg v))))
/-- The rough lower multiplier includes the fixed fine-resolution inflation. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def kLow (v : Params) : ℝ := (2:ℝ)^(-17:ℤ)*(2*Hfine)^(-sumReg v)
/-- The paired-tent separation multiplier depends only on effect smoothness. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def cOracle (v : Params) : ℝ := (4:ℝ)^(-v.γ)/(16*Real.sqrt 3)
/-- Use the pure tail multiplier or the minimum of rough and small-sample bridge multipliers. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def cLower (v : Params) : ℝ := if 1 ≤ Fphase v then cOracle v else min (kLow v) (cOracle v*(Nlow v:ℝ)^(-(E0 v-E4 v))) -- @realizes clower(sharp lower multiplier)
/-- The bounded lower multiplier is the matched moment-two multiplier. This statement assumes [the w parameter](hyp:w). [This is the stated defined object](goal). -/
def cLowerBounded (w : Smooth3) : ℝ := cLower (Params.ofBounded w) -- @realizes clowerbound(bounded multiplier)
/-- The smallest primitive smoothness controls the geometric singleton ledger.  [the parameters and conditions in the statement](hyp:v), [the asserted mathematical result holds](goal). -/
-- @node: s0
def s0 (v : Params) : ℝ := min v.α (min v.β v.γ)
/-- The variance inflation exponent is the second-minus-moment ratio. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def tExp (v : Params) : ℝ := (2-v.p)/(v.p-1)
/-- The canonical increment decay is an explicit positive function of the moment exponent. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def eta0 (v : Params) : ℝ := (v.p-1)*(v.p+6)/(4*v.p)
/-- The geometric-series multiplier is the reciprocal of one minus two to the negative decay exponent. This statement assumes [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def Ageo (x : ℝ) : ℝ := (1-(2:ℝ)^(-x))⁻¹
/-- The explicit bias attainment constant includes both propensity and increment geometric sums. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def Bstar (v : Params) : ℝ := 420+800*(Ageo v.α+Ageo (lam0 v))
/-- The explicit logarithmic interpolation constant depends on interaction smoothness. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def Dstar (v : Params) : ℝ := 1+(Real.exp 1*sumReg v*Real.log 2)⁻¹
/-- The singleton attainment constant retains every geometric contribution. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def Lstar (v : Params) : ℝ := 16+880*Ageo (s0 v)+160*Dstar v+960*Ageo v.α
/-- The canonical attainment constant retains both variance inflation and increment decay. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def Gstar (v : Params) : ℝ := Real.sqrt 64*((2:ℝ)^(tExp v/2)*Ageo (1/2)+Ageo (eta0 v/2))
/-- The quadratic covariance attainment constant combines singleton and canonical bounds. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def Astar (v : Params) : ℝ := Real.sqrt 2*(24576+64*Lstar v^2+16384+256*Gstar v^2)
/-- The public attainment multiplier combines approximation, bias and covariance constants. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def CAtt (v : Params) : ℝ := 16*(16+5*Bstar v+1024*Real.sqrt (Astar v)) -- @realizes Cupper(explicit attainment constant)
/-- Round the public nonempty-power threshold upward from the matched pure-power target. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def NAtt (v : Params) : ℕ := Nat.ceil (max 4 ((2*CAtt v/d0)^(1/Eexp v))) -- @realizes Npublic(public nonempty-power threshold)
/-- Use the explicit moment-two attainment multiplier for the bounded class. This statement assumes [the w parameter](hyp:w). [This is the stated defined object](goal). -/
def CAttBounded (w : Smooth3) : ℝ := CAtt (Params.ofBounded w) -- @realizes Cupperbound(bounded attainment)
/-- Use the moment-two public nonempty-power threshold. This statement assumes [the w parameter](hyp:w). [This is the stated defined object](goal). -/
def NAttBounded (w : Smooth3) : ℕ := NAtt (Params.ofBounded w) -- @realizes Npublicbound(bounded threshold)
/-- The attaining original-record rule is exactly the explicit ledger test. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def phistar (n : ℕ) (v : Params) : Test n := ledgerTest n v -- @realizes phistar(attaining rule)
/-- The bounded attaining rule is the same ledger test at moment exponent two. This statement assumes [the n parameter](hyp:n), [the w parameter](hyp:w). [This is the stated defined object](goal). -/
def phistarBounded (n : ℕ) (w : Smooth3) : Test n := ledgerTest n (Params.ofBounded w) -- @realizes phistarbound(bounded rule)
/-- The oracle upper multiplier is the fixed explicit bias-and-variance constant. [This is the stated defined object](goal). -/
def COr : ℝ := 3*(120+128*Real.sqrt (160*Real.sqrt 2))
/-- Round the public oracle nonempty-power threshold upward. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def NOr (v : Params) : ℕ := Nat.ceil (max 2 ((2*COr/d0)^(1/E0 v)))
/-- The preservation gap is the nonnegative difference of the pure-tail and rough exponents. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def gapExp (v : Params) : ℝ := max 0 (E0 v-E4 v)
/-- The calibrated separation combines coarse approximation, coefficient bias and profiled covariance. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def Ratt (n : ℕ) (v : Params) : ℝ := (16/3)*(16*(ledgerM n v:ℝ)^(-v.γ)+5*ledgerBias n v+1024*(ledgerM n v:ℝ)^(1/4:ℝ)*Real.sqrt (ledgerCov n v))

end CausalSmith.Stat.FinitepHomogeneityDensegamma

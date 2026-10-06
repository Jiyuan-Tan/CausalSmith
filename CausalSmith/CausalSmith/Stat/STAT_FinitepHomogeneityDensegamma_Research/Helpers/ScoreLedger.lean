module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Scores
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ProjectionGeometry
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Testing
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Finite-moment homogeneity testing: Helpers/ScoreLedger. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- The tail exponent is the moment exponent minus one, divided by the moment exponent. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def qExp (v : Params) : ℝ := (v.p-1)/v.p
/-- The interaction smoothness is the sum of propensity and baseline smoothness. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def sumReg (v : Params) : ℝ := v.α+v.β
/-- The rough-channel denominator combines the dimension, primitive smoothness and effect smoothness budgets. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def Dp (v : Params) : ℝ := 1+2*v.α+v.β/qExp v+sumReg v/(2*v.γ)
/-- The pure tail testing exponent balances effect approximation against finite-moment noise. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def E0 (v : Params) : ℝ := 2*v.γ*qExp v/(2*v.γ+qExp v)
/-- The rough testing exponent is twice interaction smoothness divided by the rough-channel denominator. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def E4 (v : Params) : ℝ := 2*sumReg v/Dp v
/-- The entire-class exponent is the minimum of the two independently derived channels. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def Eexp (v : Params) : ℝ := min (E0 v) (E4 v)
/-- The phase functional determines which channel gives the smaller exponent. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def Fphase (v : Params) : ℝ := 2*v.α/(v.p-1)+v.β/qExp v+sumReg v/(2*v.γ)
/-- Dyadic rounding retains negative integer exponents for general positive inputs. This statement assumes [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def dyadUp (x : ℝ) : ℝ := (2:ℝ) ^ (Int.ceil (Real.logb 2 x))
/-- Round a positive target upward to the least nonnegative power of two above it. This statement assumes [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def leastPow2Ge (x : ℝ) : ℕ := 2 ^ (Nat.ceil (Real.logb 2 x))
/-- The target block scale raises the deterministic block size to the negative entire-class exponent. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def ledgerA (n : ℕ) (v : Params) : ℝ := (blockSize n:ℝ) ^ (-Eexp v)
/-- The coarse histogram rank is the dyadic rounding of the effect approximation target. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def ledgerM (n : ℕ) (v : Params) : ℕ := if n < 4 then 1 else leastPow2Ge (ledgerA n v ^ (-1/v.γ)) -- @realizes Jcoarse(public power of two)
/-- The fine histogram rank also resolves the interaction smoothness target. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def ledgerK (n : ℕ) (v : Params) : ℕ := if n < 4 then 1 else leastPow2Ge (max (ledgerM n v:ℝ) (ledgerA n v ^ (-1/sumReg v))) -- @realizes Jfine(public power of two ≥coarse)
/-- The main outcome cutoff is the public dyadic rounding of the tail bias target. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def ledgerT0 (n : ℕ) (v : Params) : ℝ := if n < 4 then 1 else max 1 (dyadUp (ledgerA n v ^ (-1/(v.p-1)))) -- @realizes T(main cutoff with enforced lower bound 1)
/-- The clipping construction enforces its standing lower bound for every input tuple. [This is the stated conclusion](goal). -/
lemma ledgerT0_ge_one (n : ℕ) (v : Params) : 1 ≤ ledgerT0 n v := by
  unfold ledgerT0
  split
  · exact le_rfl
  · exact le_max_left 1 _
/-- The main clipped moment budget is thirty-two times the cutoff to the second-minus-moment power. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def ledgerV0 (n : ℕ) (v : Params) : ℝ := 32*ledgerT0 n v ^ (2-v.p)
/-- A single common cutoff suffices when interaction smoothness exceeds effect smoothness or propensity smoothness exceeds the tail exponent. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def singleBranch (v : Params) : Prop := sumReg v ≥ v.γ ∨ v.α ≥ qExp v
/-- The increment decay parameter is the squared moment excess divided by four times the moment exponent. This statement assumes [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def lam0 (v : Params) : ℝ := (v.p-1)^2/(4*v.p)
/-- The number of correction increments is the binary logarithm of the dyadic rank ratio. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def ledgerL (n : ℕ) (v : Params) : ℕ := Nat.log 2 (ledgerK n v / ledgerM n v)
/-- Increment ranks double deterministically from the coarse rank. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the j parameter](hyp:j). [This is the stated defined object](goal). -/
def ledgerR (n : ℕ) (v : Params) (j : ℕ) : ℕ := 2^j*ledgerM n v
/-- Each increment cutoff is dyadically rounded after truncation to the public admissible interval. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the j parameter](hyp:j). [This is the stated defined object](goal). -/
def ledgerT (n : ℕ) (v : Params) (j : ℕ) : ℝ :=
  if n < 4 then 1 else dyadUp (max 1 (min (ledgerA n v ^ (-1/(v.p-1)))
    (((ledgerR n v j:ℝ)^(-v.α)/(ledgerA n v*((ledgerR n v j:ℝ)/ledgerK n v)^lam0 v))^(1/(v.p-1)))))
/-- Each increment has its own clipped second-moment budget. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the j parameter](hyp:j). [This is the stated defined object](goal). -/
def ledgerV (n : ℕ) (v : Params) (j : ℕ) : ℝ := 32*ledgerT n v j^(2-v.p)
/-- The propensity approximation budget uses the preceding dyadic rank. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the j parameter](hyp:j). [This is the stated defined object](goal). -/
def aLev (n : ℕ) (v : Params) (j : ℕ) : ℝ := 40*(ledgerR n v (j-1):ℝ)^(-v.α)
/-- The increment singleton budget combines primitive approximation and clipping remainder. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the j parameter](hyp:j). [This is the stated defined object](goal). -/
def dLev (n : ℕ) (v : Params) (j : ℕ) : ℝ :=
  110*(ledgerR n v (j-1):ℝ)^(-min v.α (min v.β v.γ))+20*ledgerT n v j^(1-v.p)
/-- The bias ledger retains interaction approximation, main tail bias and every increment tail contribution. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def ledgerBias (n : ℕ) (v : Params) : ℝ :=
  if n < 4 then 0 else 400*(ledgerK n v:ℝ)^(-sumReg v)+20*ledgerT0 n v^(1-v.p)+
  if singleBranch v then 0 else 10*∑ j : Fin (ledgerL n v), aLev n v (j.val+1)*ledgerT n v (j.val+1)^(1-v.p) -- @realizes Bias(public bias ledger)
/-- The linear covariance ledger sums the main and all increment singleton contributions. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def ledgerL1 (n : ℕ) (v : Params) : ℝ :=
  if n < 4 then 0 else 16*Real.sqrt (ledgerV0 n v)+
  if singleBranch v then 0 else 8*∑ j : Fin (ledgerL n v), (dLev n v (j.val+1)+aLev n v (j.val+1)*Real.sqrt (ledgerV n v (j.val+1)))
/-- The canonical covariance ledger sums the rank-weighted clipped pair contributions. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def ledgerL2 (n : ℕ) (v : Params) : ℝ :=
  if n < 4 then 0 else if singleBranch v then 4*Real.sqrt (ledgerK n v*ledgerV0 n v) else
  4*(Real.sqrt (ledgerM n v*ledgerV0 n v)+∑ j : Fin (ledgerL n v), Real.sqrt (ledgerR n v (j.val+1)*ledgerV n v (j.val+1)))
/-- The total covariance budget combines the linear and canonical ledgers with their exact block normalizations. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def ledgerCov (n : ℕ) (v : Params) : ℝ :=
  if n < 4 then 0 else ledgerL1 n v^2/(blockSize n:ℝ)+2*ledgerL2 n v^2/((blockSize n:ℝ)*((blockSize n:ℝ)-1)) -- @realizes Covbound(public covariance ledger)
/-- Dyadically round twice the squared bias plus the dimension-weighted covariance cutoff. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def ledgerCutoff (n : ℕ) (v : Params) : ℝ :=
  if n < 4 then 0 else dyadUp (2*ledgerBias n v^2+2^16*Real.sqrt (ledgerM n v)*ledgerCov n v) -- @realizes Cutoff(rounded rejection threshold)
/-- Subtract the initial correction and every level-specific correction from the observed single-record score. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the b parameter](hyp:b), [the c parameter](hyp:c), [the data parameter](hyp:data). [This is the stated defined object](goal). -/
def ledgerScore (n : ℕ) (v : Params) (b : Bool) (c : ℝ) (data : Dataset n) : Vec (ledgerM n v) :=
  if n < 4 then 0 else if singleBranch v then
    hScore n b (ledgerM n v) (ledgerT0 n v) c data-uScore n b (ledgerM n v) (projKernel (ledgerK n v)) (ledgerT0 n v) c data
  else multiresScore n b (ledgerM n v) (ledgerL n v) (ledgerT0 n v) (fun j => ledgerT n v (j.val+1)) c data -- @realizes Zscore(explicit multiresolution score)
/-- The quadratic statistic pairs the two disjoint evaluation-block scores. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the c parameter](hyp:c), [the data parameter](hyp:data). [This is the stated defined object](goal). -/
def ledgerW (n : ℕ) (v : Params) (c : ℝ) (data : Dataset n) : ℝ := quadStat (ledgerScore n v) c data -- @realizes Wscore(independent-block inner product)
/-- Reject when the finite profiled minimum strictly exceeds the public cutoff; the small-sample branch returns zero. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the z parameter](hyp:z). [This is the stated defined object](goal). -/
def ledgerRule (n : ℕ) (v : Params) (z : Experiment n) : ℝ :=
  if n < 4 then 0 else if ledgerCutoff n v < profiledMin (ledgerScore n v) z.1 then 1 else 0
/-- Every branch of the public score is a measurable finite sum of original-record features. [This is the stated conclusion](goal). -/
-- @node: measurable_ledgerScore
@[fun_prop] lemma measurable_ledgerScore (n : ℕ) (v : Params) (b : Bool) (c : ℝ) :
    Measurable (ledgerScore n v b c) := by
  have ht : Measurable treatment := by
    unfold treatment A
    exact (measurable_of_countable (fun b : Bool => if b then (1:ℝ) else 0)).comp
      (measurable_fst.comp measurable_snd)
  unfold ledgerScore
  split
  · fun_prop
  · split
    all_goals
      simp only [multiresScore, hScore, uScore, hIntercept, hTreatment, uIntercept, uTreatment]
      split_ifs
      simp only [clipY, X, Y, diffKernel, projKernel]
      fun_prop

/-- The finite endpoint and vertex profile is a Borel function of its three coefficients. [This is the stated conclusion](goal). -/
-- @node: measurable_quadraticMin
@[fun_prop] lemma measurable_quadraticMin :
    Measurable (fun z : ℝ × ℝ × ℝ => quadraticMin z.1 z.2.1 z.2.2) := by
  unfold quadraticMin
  apply Measurable.ite
  · apply MeasurableSet.inter
    · exact measurableSet_lt measurable_const measurable_snd.snd
    · apply MeasurableSet.inter
      · change MeasurableSet {z : ℝ × ℝ × ℝ | (-1/2:ℝ) ≤ -z.2.1/(2*z.2.2)}
        apply measurableSet_le <;> fun_prop
      · change MeasurableSet {z : ℝ × ℝ × ℝ | -z.2.1/(2*z.2.2) ≤ (1/2:ℝ)}
        apply measurableSet_le <;> fun_prop
  · fun_prop
  · fun_prop

/-- Profiling the two affine block scores uses only measurable arithmetic and finite comparisons. [This is the stated conclusion](goal). -/
-- @node: measurable_ledgerProfile
@[fun_prop] lemma measurable_ledgerProfile (n : ℕ) (v : Params) :
    Measurable (profiledMin (ledgerScore n v)) := by
  unfold profiledMin
  fun_prop

/-- The explicit rejection rule is Borel measurable and takes values between zero and one. [This is the stated conclusion](goal). -/
-- @node: ledgerRule_test
lemma ledgerRule_test (n : ℕ) (v : Params) : Measurable (ledgerRule n v) ∧ ∀ z, 0 ≤ ledgerRule n v z ∧ ledgerRule n v z ≤ 1  := by
  constructor
  · unfold ledgerRule
    split
    · fun_prop
    · apply Measurable.ite
      · apply measurableSet_lt <;> fun_prop
      · fun_prop
      · fun_prop
  · intro z
    unfold ledgerRule
    split
    · norm_num
    · split <;> norm_num
/-- [Total public dyadic score and deterministic ledgers](goal). This is a specified member of Definition \(\mathrm{def:calibration\mbox{-}handle}\), constructed from the original records only. For the public tuple put \[ q=\frac{p-1}{p},\quad S=\alpha+\beta,\quad t=\frac{2-p}{p-1},\quad E_0=\frac{2\gamma q}{2\gamma+q},\quad E_4=\frac{2S}{1+2\alpha+\beta/q+S/(2\gamma)},\quad E=\min\{E_0,E_4\}. \] For \(n=2,3\), set \(J_{\mathrm c}=J_{\mathrm f}=1\), all cutoffs equal to one, \(Z_b(c)=0\), \(\mathfrak b_{n,v}=\Lambda_{n,v}=h_{n,v}=0\), and the rejection rule equal to zero. For \(n\ge4\), let \(s=s_n\), \(a=s^{-E}\), and let \(M=J_{\mathrm c}\) be the least power of two at least \(a^{-1/\gamma}\). Let \(K=J_{\mathrm f}\) be the least power of two at least \(\max\{M,a^{-1/S}\}\). For \(x>0\) put \(\mathcal R(x)=2^{\lceil\log_2 x\rceil}\). Put \(T_0=\mathcal R(a^{-1/(p-1)})\) and \(V_0=32T_0^{2-p}\). If \(S\ge\gamma\) or \(\alpha\ge q\), define \[ Z_b(c)=H_{b,T_0}(c)-U_{b,\Pi_K,T_0}(c),\quad B=400K^{-S}+20T_0^{1-p},\quad L_1=16\sqrt{V_0},\quad L_2=4\sqrt{KV_0}. \] Otherwise let \(\lambda_0=(p-1)^2/(4p)\), \(L=\log_2(K/M)\), \(R_j=2^jM\), \(D_j=\Pi_{R_j}-\Pi_{R_{j-1}}\), and \[ T_j=\mathcal R\left(\max\left\{1,\min\left\{a^{-1/(p-1)}, \left[\frac{R_j^{-\alpha}}{a(R_j/K)^{\lambda_0}}\right]^{1/(p-1)}\right\}\right\}\right), \qquad 1\le j\le L. \] For each defined increment cutoff set \(V_j=32T_j^{2-p}\). Here \(L\) is an integer and an empty sum has value zero. In this branch set \[ \begin{split} Z_b(c)&=H_{b,T_0}(c)-U_{b,\Pi_M,T_0}(c) -\sum_{j=1}^L U_{b,D_j,T_j}(c),\\ a_j&=40R_{j-1}^{-\alpha},\quad d_j=110R_{j-1}^{-\min\{\alpha,\beta,\gamma\}}+20T_j^{1-p},\\ B&=400K^{-S}+20T_0^{1-p}+10\sum_{j=1}^L a_jT_j^{1-p},\\ L_1&=16\sqrt{V_0}+8\sum_{j=1}^L(d_j+a_j\sqrt{V_j}),\\ L_2&=4\left(\sqrt{MV_0}+\sum_{j=1}^L\sqrt{R_jV_j}\right). \end{split} \] In both branches define the public numbers \[ \mathfrak b_{n,v}=B,\quad \Lambda_{n,v}=\frac{L_1^2}{s}+\frac{2L_2^2}{s(s-1)},\quad h_{n,v}=\mathcal R(2B^2+2^{16}\sqrt M\Lambda_{n,v}). \] Use \(W(c)=\langle Z_1(c),Z_2(c)\rangle\) and reject exactly when \(\min_{|c|\le1/2}W(c)>h_{n,v}\). Compute this minimum from the two endpoints and, only for a positive quadratic coefficient and an interior vertex, the vertex. For public grid bookkeeping use the rank grid \(\{2^j:0\le j\le\lceil\log_2(2s^2)\rceil\}\) and the outcome grid \(\{2^j:0\le j\le\lceil\log_2(2s)\rceil\}\). The cutoff is the upper endpoint of the public two-point dyadic grid bracketing its unrounded formula. Every sum is finite. The definitions of the histogram and ordered-pair scores supply the values at bin endpoints, and there is no division by an observed cell count. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). -/
-- @node: def:explicit-score-ledger
def ledgerTest (n : ℕ) (v : Params) : Test n := ⟨ledgerRule n v,ledgerRule_test n v⟩

/-- Both ledger branches and the zero branch retain affine dependence on the candidate constant. [This is the stated conclusion](goal). -/
-- @node: ledgerScore_affine
lemma ledgerScore_affine (n : ℕ) (v : Params) (b : Bool) (c : ℝ) (data : Dataset n) :
    ledgerScore n v b c data = ledgerScore n v b 0 data-c •
      (ledgerScore n v b 0 data-ledgerScore n v b 1 data) := by
  unfold ledgerScore
  split
  · simp
  · split
    · rw [hScore_affine n _ b _ c data, uScore_affine n _ b _ _ c data]
      module
    · exact multiresScore_affine n _ _ b _ _ c data

/-- Ledger profiledmin: the displayed mathematical construction or bound. [This is the stated conclusion](goal). -/
-- @node: ledger_profiledMin
lemma ledger_profiledMin (n : ℕ) (v : Params) (data : Dataset n) :
    profiledMin (ledgerScore n v) data =
      ⨅ c : {c : ℝ // |c| ≤ 1/2}, ledgerW n v c.1 data := by
  apply profiledMin_eq_iInf_of_affine
  intro b c
  exact ledgerScore_affine n v b c data

/-- The finite public grid containing the two histogram ranks. This statement assumes [the n parameter](hyp:n). [This is the stated defined object](goal). -/
def publicRankGrid (n : ℕ) : Finset ℕ :=
  (Finset.range (Nat.ceil (Real.logb 2 (2*(blockSize n:ℝ)^2))+1)).image (fun j => 2^j)
/-- The finite public grid containing every outcome cutoff. This statement assumes [the n parameter](hyp:n). [This is the stated defined object](goal). -/
def publicOutcomeGrid (n : ℕ) : Finset ℝ :=
  (Finset.range (Nat.ceil (Real.logb 2 (2*(blockSize n:ℝ)))+1)).image (fun j => (2:ℝ)^j)
/-- The two public dyadic endpoints bracketing the unrounded rejection cutoff. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. -/
def publicCutoffGrid (n : ℕ) (v : Params) : Finset ℝ :=
  if n < 4 then {0} else
    let x := 2*ledgerBias n v^2+2^16*Real.sqrt (ledgerM n v)*ledgerCov n v
    {(2:ℝ)^(Int.floor (Real.logb 2 x)),dyadUp x}

/-- The complete calibration handle selects the specified dyadic ranks and separate cutoffs, assembles the branchwise affine score, its bias and covariance ledgers, the rounded threshold, the finite endpoint-and-vertex profile and the rejection test, together with their public grids. Its deterministic selection is exactly `ledgerM`, `ledgerK`, `ledgerT0` and `ledgerT`; its covariance is L₁²/s + 2 L₂²/[s(s−1)] and its cutoff is the upper dyadic rounding of 2 B² + 2¹⁶ √M Λ. The score subtracts both the initial and all increment corrections. All ledgers and the test use the stipulated zero branch for sample sizes two and three. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
-- @node: def:calibration-handle
def calibrationHandle (n : ℕ) (v : Params) :
    (ℕ × ℕ × ℝ × (Fin (ledgerL n v) → ℝ)) ×
    (Bool → ℝ → Dataset n → Vec (ledgerM n v)) ×
    (Bool → Bool → Dataset n → Vec (ledgerM n v)) ×
    (ℝ × ℝ × ℝ) × (Dataset n → ℝ) × Test n ×
    (Finset ℕ × Finset ℝ × Finset ℝ) :=
  ((ledgerM n v, ledgerK n v, ledgerT0 n v, fun j => ledgerT n v (j.val+1)),
   ledgerScore n v,
   (fun b r data => if r then ledgerScore n v b 0 data-ledgerScore n v b 1 data
     else ledgerScore n v b 0 data),
   (ledgerBias n v, ledgerCov n v, ledgerCutoff n v),
   profiledMin (ledgerScore n v), ledgerTest n v,
   (publicRankGrid n, publicOutcomeGrid n, publicCutoffGrid n v))

end CausalSmith.Stat.FinitepHomogeneityDensegamma

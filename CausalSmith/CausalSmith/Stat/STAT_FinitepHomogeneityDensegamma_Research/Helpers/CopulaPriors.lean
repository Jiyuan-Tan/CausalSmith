module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Frame

/-! Finite-moment homogeneity testing: Helpers/CopulaPriors. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- The latent index retains every coarse sign and every fine coefficient pair. This statement assumes [the K parameter](hyp:K), [the M parameter](hyp:M). [This is the stated defined object](goal). -/
abbrev CopulaIndex (K M : ℕ) := (Fin (M/2) → Bool) × (Fin (K+1) → Bool × Bool)
/-- The sign-copula coupling constant is one sixteenth. [This is the stated defined object](goal). -/
def kappa0 : ℝ := 1/16
/-- The tent rises linearly to one and falls linearly to zero on the unit interval. This statement assumes [the t parameter](hyp:t). [This is the stated defined object](goal). -/
def tentBase (t : ℝ) : ℝ := if 0 ≤ t ∧ t ≤ 1 then 2*min t (1-t) else 0
/-- Paired adjacent coarse tents carry opposite values of the same fair coarse sign. This statement assumes [the M parameter](hyp:M), [the σ parameter](hyp:σ), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def coarseTent (M : ℕ) (σ : Fin (M/2) → Bool) (x : ℝ) : ℝ :=
  ∑ j : Fin (M/2), signVal (σ j)*(tentBase ((M:ℝ)*x-2*j.val)-tentBase ((M:ℝ)*x-(2*j.val+1)))
/-- Interpolate the coarse tent values through squared smooth-frame coordinates. This statement assumes [the K parameter](hyp:K), [the M parameter](hyp:M), [the σ parameter](hyp:σ), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def smoothedTent (K M : ℕ) (σ : Fin (M/2) → Bool) (x : ℝ) : ℝ :=
  ∑ i : Fin (K+1), coarseTent M σ ((i:ℝ)/K)*frameCoord K i x^2
/-- A coefficient-pair probability is its sign-copula tilt of the fair four-point law. This statement assumes [the ν parameter](hyp:ν), [the g parameter](hyp:g), [the l parameter](hyp:l), [the h parameter](hyp:h). [This is the stated defined object](goal). -/
def pairWeight (ν : Bool) (g : ℝ) (l h : Bool) : ℝ := (1+(if ν then 1 else 0)*kappa0*g*signVal l*signVal h)/4
/-- Combine fair coarse signs with the conditionally independent sign-copula coefficient draws. This statement assumes [the ν parameter](hyp:ν), [the K parameter](hyp:K), [the M parameter](hyp:M), [the idx parameter](hyp:idx). [This is the stated defined object](goal). -/
def copulaWeight (ν : Bool) (K M : ℕ) (idx : CopulaIndex K M) : ℝ :=
  (1/2:ℝ)^(M/2)*∏ i : Fin (K+1), pairWeight ν (coarseTent M idx.1 ((i:ℝ)/K)) (idx.2 i).1 (idx.2 i).2
/-- The propensity coordinate is its amplitude times the signed smooth-frame field. This statement assumes [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the idx parameter](hyp:idx), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def copulaXi (K M : ℕ) (a : ℝ) (idx : CopulaIndex K M) (x : unitInterval) : ℝ := a*frameField K (fun i => signVal (idx.2 i).1) x
/-- The outcome coordinate is its amplitude times the second signed smooth-frame field. This statement assumes [the K parameter](hyp:K), [the M parameter](hyp:M), [the u parameter](hyp:u), [the idx parameter](hyp:idx), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def copulaUpsilon (K M : ℕ) (u : ℝ) (idx : CopulaIndex K M) (x : unitInterval) : ℝ := u*frameField K (fun i => signVal (idx.2 i).2) x
/-- The correction cancels the singleton sign-copula interaction through the squared-frame interpolated tent. This statement assumes [the ν parameter](hyp:ν), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the idx parameter](hyp:idx), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def copulaT (ν : Bool) (K M : ℕ) (a u : ℝ) (idx : CopulaIndex K M) (x : unitInterval) : ℝ :=
  -(if ν then 1 else 0)*a*u*kappa0/(1-a^2)*smoothedTent K M idx.1 x
/-- The table interaction combines the coordinate product and the corrected deterministic effect term. This statement assumes [the ν parameter](hyp:ν), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the idx parameter](hyp:idx), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def copulaZeta (ν : Bool) (K M : ℕ) (a u : ℝ) (idx : CopulaIndex K M) (x : unitInterval) : ℝ :=
  copulaXi K M a idx x*copulaUpsilon K M u idx x+copulaT ν K M a u idx x*(1-copulaXi K M a idx x^2)
/-- Insert every finite coefficient draw into the complete-record table construction. This statement assumes [the ν parameter](hyp:ν), [the v parameter](hyp:v), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the ε parameter](hyp:ε), [the L parameter](hyp:L), [the idx parameter](hyp:idx). [This is the stated defined object](goal). -/
def copulaLaw (ν : Bool) (v : Params) (K M : ℕ) (a u ε L : ℝ) (idx : CopulaIndex K M) : ObservedLaw :=
  tableObservedLaw (copulaXi K M a idx) (copulaUpsilon K M u idx) (copulaZeta ν K M a u idx) ε L
/-- [Explicit finite smooth sign-copula priors](goal). Inputs are \(v\), dyadic integers \(K=J_{\mathrm f}\), \(M=J_{\mathrm c}\ge2\) with \(K\ge16M\), amplitudes \(0<a,u\le1/16\), and \(0<\varepsilon<1\), \(L>0\). Put \(\kappa=1/16\), and let \(b_\triangle(t)=2\min(t,1-t)\) on \([0,1]\). For independent uniform signs \(\sigma_j\), \(1\le j\le M/2\), define \(g_\sigma\) to be \(\sigma_j b_\triangle\) rescaled onto coarse cell \(2j-1\), and its negative rescaled onto cell \(2j\), with zero at cell boundaries. Let \(f_i\), \(0\le i\le K\), be the continuous frame: on \([i/K,(i+1)/K]\) its two nonzero coordinates are \(f_i(x)=\cos(\pi(Kx-i)/2)\), \(f_{i+1}(x)=\sin(\pi(Kx-i)/2)\). Put \[ \widetilde g_\sigma(x)=\sum_{i=0}^K g_\sigma(i/K)f_i(x)^2. \] For \(\nu=0,1\), conditionally on \(\sigma\), independently draw coefficient pairs with \[ \Pr_\nu(\lambda_i=l,\eta_i=h\mid\sigma) =\frac{1+\nu\kappa g_\sigma(i/K)lh}{4},\qquad l,h\in\{-1,1\}. \] For each draw name a record law by uniform \(X\) and the normalized table in Definition \(\mathrm{def:marked\mbox{-}table}\), using \[ \xi(x)=a\sum_i f_i(x)\lambda_i,\quad \upsilon(x)=u\sum_i f_i(x)\eta_i,\quad t_\nu(x)=-\frac{\nu a u\kappa}{1-a^2}\widetilde g_\sigma(x),\quad \zeta(x)=\xi(x)\upsilon(x)+t_\nu(x)(1-\xi(x)^2). \] The pushforward of these finite coefficient draws is \(\pi^{K,M}_{\nu;v,a,u,\varepsilon,L}\). This definition names tables and mixing laws; normalization, model membership, separation and mixture-distance properties are proved in the consuming lemmas. This statement assumes [the ν parameter](hyp:ν), [the v parameter](hyp:v), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the ε parameter](hyp:ε), [the L parameter](hyp:L). -/
-- @node: def:copula-frame-priors
def copulaPrior (ν : Bool) (v : Params) (K M : ℕ) (a u ε L : ℝ) : FinitePrior :=
  finitePriorOf (copulaWeight ν K M) (copulaLaw ν v K M a u ε L) -- @realizes copulaPrior(finite sign-copula family)
/-- Mix every sign-copula support law at the original sample size. This statement assumes [the ν parameter](hyp:ν), [the n parameter](hyp:n), [the v parameter](hyp:v), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the ε parameter](hyp:ε), [the L parameter](hyp:L). [This is the stated defined object](goal). -/
def copulaMixture (ν : Bool) (n : ℕ) (v : Params) (K M : ℕ) (a u ε L : ℝ) : Measure (Dataset n) :=
  priorMixture n (copulaPrior ν v K M a u ε L)
/-- Public copula inputs have dyadic refining ranks, bounded positive amplitudes, interior rarity and positive magnitude. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the ε parameter](hyp:ε), [the L parameter](hyp:L). [This is the stated defined object](goal). -/
def CopulaDomain (n K M : ℕ) (a u ε L : ℝ) : Prop :=
  2 ≤ n ∧
  (∃ k, K = 2^k) ∧ -- @realizes Jfine(dyadic fine rank)
  (∃ m, M = 2^m) ∧ -- @realizes Jcoarse(dyadic coarse rank)
  16*M ≤ K ∧ 2 ≤ M ∧ -- @realizes Jfine(fine rank refines coarse rank)
  (0 < a ∧ a ≤ 1/16) ∧ -- @realizes aamp(0<a≤1/16)
  (0 < u ∧ u ≤ 1/16) ∧ -- @realizes uamp(0<u≤1/16)
  (0 < ε ∧ ε < 1) ∧ 0 < L

end CausalSmith.Stat.FinitepHomogeneityDensegamma

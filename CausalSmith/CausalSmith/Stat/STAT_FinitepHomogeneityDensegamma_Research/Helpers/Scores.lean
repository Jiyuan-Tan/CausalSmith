module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Projections
public import Mathlib.MeasureTheory.Integral.Prod

/-! Finite-moment homogeneity testing: Helpers/Scores. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Each evaluation block contains the integer part of half the sample size. This statement assumes [the n parameter](hyp:n). [This is the stated defined object](goal). -/
def blockSize (n : ℕ) : ℕ := n/2 -- @realizes bsize(floor n/2)
/-- [Deterministic block indexing](goal). \(\mathcal I_1=\{1,\ldots,s_n\},\quad\mathcal I_2=\{s_n+1,\ldots,2s_n\},\quad s_n=\lfloor n/2\rfloor\). This statement assumes [the n parameter](hyp:n), [the b parameter](hyp:b). -/
-- @node: def:blocks
def evalBlock (n : ℕ) (b : Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => if b then blockSize n ≤ i.val ∧ i.val < 2*blockSize n else i.val < blockSize n) -- @realizes blocks(two deterministic disjoint blocks)
/-- Clip the original outcome to the symmetric public cutoff interval. This statement assumes [the T parameter](hyp:T), [the y parameter](hyp:y). [This is the stated defined object](goal). -/
def clipY (T y : ℝ) : ℝ := max (-T) (min y T) -- @realizes clip(clipping at T)
/-- Encode the original binary treatment label as zero or one. This statement assumes [the o parameter](hyp:o). [This is the stated defined object](goal). -/
def treatment (o : Record) : ℝ := if A o then 1 else 0
/-- Average the clipped treated single-record feature vectors within the selected deterministic block. This statement assumes [the n parameter](hyp:n), [the b parameter](hyp:b), [the J parameter](hyp:J), [the T parameter](hyp:T), [the data parameter](hyp:data). [This is the stated defined object](goal). -/
def hIntercept (n : ℕ) (b : Bool) (J : ℕ) (T : ℝ) (data : Dataset n) : Vec J :=
  if n < 4 then 0 else (blockSize n : ℝ)⁻¹ • ∑ i ∈ evalBlock n b,
    (treatment (data i)*clipY T (Y (data i))) • featureMap J (X (data i))
/-- Average the treatment-weighted feature vectors within the selected block. This statement assumes [the n parameter](hyp:n), [the b parameter](hyp:b), [the J parameter](hyp:J), [the data parameter](hyp:data). [This is the stated defined object](goal). -/
def hTreatment (n : ℕ) (b : Bool) (J : ℕ) (data : Dataset n) : Vec J :=
  if n < 4 then 0 else (blockSize n : ℝ)⁻¹ • ∑ i ∈ evalBlock n b,
    treatment (data i) • featureMap J (X (data i))
/-- [Observable original-outcome covariance-score primitives](goal). For \(n\ge4\), \[H_{b,T}(c)=s_n^{-1}\sum_{i\in\mathcal I_b}F_{J_{\mathrm c}}(X_i)A_i\{\ell_T(Y_i)-c\},\qquad U_{b,G,T}(c)=\{s_n(s_n-1)\}^{-1}\sum_{i\ne j\in\mathcal I_b}F_{J_{\mathrm c}}(X_i)A_iG(X_i,X_j)\{\ell_T(Y_j)-cA_j\}.\] Set both vectors to zero for \(n=2,3\). This statement assumes [the n parameter](hyp:n), [the b parameter](hyp:b), [the J parameter](hyp:J), [the T parameter](hyp:T), [the c parameter](hyp:c), [the data parameter](hyp:data). -/
-- @node: def:score-family
def hScore (n : ℕ) (b : Bool) (J : ℕ) (T c : ℝ) (data : Dataset n) : Vec J :=
  hIntercept n b J T data-c • hTreatment n b J data -- @realizes Hscore(single-record affine vector)
/-- Average the ordered distinct-record correction pairs using clipped outcomes. This statement assumes [the n parameter](hyp:n), [the b parameter](hyp:b), [the J parameter](hyp:J), [the G parameter](hyp:G), [the T parameter](hyp:T), [the data parameter](hyp:data). [This is the stated defined object](goal). -/
def uIntercept (n : ℕ) (b : Bool) (J : ℕ) (G : unitInterval → unitInterval → ℝ) -- @realizes G(correction-kernel carrier)
    (T : ℝ) (data : Dataset n) : Vec J :=
  if n < 4 then 0 else ((blockSize n:ℝ)*((blockSize n:ℝ)-1))⁻¹ •
    ∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i,
    (treatment (data i)*G (X (data i)) (X (data j))*clipY T (Y (data j))) • featureMap J (X (data i))
/-- Average the ordered distinct-record correction pairs using both treatment labels. This statement assumes [the n parameter](hyp:n), [the b parameter](hyp:b), [the J parameter](hyp:J), [the G parameter](hyp:G), [the data parameter](hyp:data). [This is the stated defined object](goal). -/
def uTreatment (n : ℕ) (b : Bool) (J : ℕ) (G : unitInterval → unitInterval → ℝ)
    (data : Dataset n) : Vec J :=
  if n < 4 then 0 else ((blockSize n:ℝ)*((blockSize n:ℝ)-1))⁻¹ •
    ∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i,
    (treatment (data i)*G (X (data i)) (X (data j))*treatment (data j)) • featureMap J (X (data i))
/-- The ordered-pair score is affine in the candidate null constant. This statement assumes [the n parameter](hyp:n), [the b parameter](hyp:b), [the J parameter](hyp:J), [the G parameter](hyp:G), [the T parameter](hyp:T), [the c parameter](hyp:c), [the data parameter](hyp:data). [This is the stated defined object](goal). -/
def uScore (n : ℕ) (b : Bool) (J : ℕ) (G : unitInterval → unitInterval → ℝ)
    (T c : ℝ) (data : Dataset n) : Vec J :=
  uIntercept n b J G T data-c • uTreatment n b J G data -- @realizes Uscore(ordered-pair affine vector)
/-- Subtract the initial histogram correction and every nested dyadic increment, each with its own cutoff. The complete calibrated public handle is `calibrationHandle` in `Helpers/ScoreLedger.lean`. This statement assumes [the n parameter](hyp:n), [the b parameter](hyp:b), [the J parameter](hyp:J), [the L parameter](hyp:L), [the T0 parameter](hyp:T0), [the T parameter](hyp:T), [the c parameter](hyp:c), [the data parameter](hyp:data). [This is the stated defined object](goal). -/
def multiresScore (n : ℕ) (b : Bool) (J L : ℕ) (T0 : ℝ) (T : Fin L → ℝ)
    (c : ℝ) (data : Dataset n) : Vec J :=
  hScore n b J T0 c data-uScore n b J (projKernel J) T0 c data-
    ∑ j : Fin L, uScore n b J (diffKernel (2^j.val*J)) (T j) c data
/-- Multiply the two independent block vectors by their Euclidean inner product. This statement assumes [the score parameter](hyp:score), [the c parameter](hyp:c), [the data parameter](hyp:data). [This is the stated defined object](goal). -/
def quadStat {n J : ℕ} (score : Bool → ℝ → Dataset n → Vec J) (c : ℝ) (data : Dataset n) : ℝ :=
  inner ℝ (score false c data) (score true c data)
/-- A quadratic on the null interval is minimized at an endpoint or an admissible positive-curvature vertex. This statement assumes [the q0 parameter](hyp:q0), [the q1 parameter](hyp:q1), [the q2 parameter](hyp:q2). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. [Defining clause 3](step:3) is used. -/
def quadraticMin (q0 q1 q2 : ℝ) : ℝ :=
  let ends := min (q0-q1/2+q2/4) (q0+q1/2+q2/4)
  let vertex := -q1/(2*q2)
  if 0 < q2 ∧ -1/2 ≤ vertex ∧ vertex ≤ 1/2 then min ends (q0-q1^2/(4*q2)) else ends
/-- Compute the finite endpoint-and-vertex minimum from the two affine score coefficients. This statement assumes [the score parameter](hyp:score), [the data parameter](hyp:data). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. [Defining clause 3](step:3) is used. [Defining clause 4](step:4) is used. [Defining clause 5](step:5) is used. -/
def profiledMin {n J : ℕ} (score : Bool → ℝ → Dataset n → Vec J) (data : Dataset n) : ℝ :=
  let z0 := score false 0 data
  let z1 := score true 0 data
  let a0 := z0-score false 1 data
  let a1 := z1-score true 1 data
  quadraticMin (inner ℝ z0 z1) (-(inner ℝ a0 z1+inner ℝ z0 a1)) (inner ℝ a0 a1)
/-- [Original-mean remainder and true-law projection handle](goal). For an untruncated telescoping member of the score family compute \[\int_0^1F_{J_{\mathrm c}}(x)\{e_P(x)(1-(\Pi_{J_{\mathrm f}}e_P)(x))(\tau_P(x)-c)+(e_P(x)-(\Pi_{J_{\mathrm f}}e_P)(x))m_{0,P}(x)\}\,dx.\] For each truncated member, add its exact tail remainder; decompose its two affine coefficients into the true-law singleton projection and canonical pair projection. Multiply independent-block vectors and retain every resulting two-, three- and four-record contraction. This statement assumes [the law parameter](hyp:law), [the J parameter](hyp:J), [the K parameter](hyp:K), [the c parameter](hyp:c). -/
def origMeanVector (law : ObservedLaw) (J K : ℕ) (c : ℝ) : Vec J :=
  ∫ x, (law.e x*(1-projOp K law.e x)*(law.tau x-c)+
    (law.e x-projOp K law.e x)*law.m0 x) • featureMap J x ∂design
/-- The true-law mean integrates the score against the original iid record law. This statement assumes [the law parameter](hyp:law), [the score parameter](hyp:score), [the c parameter](hyp:c). [This is the stated defined object](goal). -/
def thetaVec {n J : ℕ} (law : ObservedLaw) (score : ℝ → Dataset n → Vec J) (c : ℝ) : Vec J :=
  ∫ data, score c data ∂Measure.pi (fun _ : Fin n => law.P) -- @realizes theta(true-law score mean)
/-- Retain both exact armwise clipping remainders with their propensity weights. This statement assumes [the law parameter](hyp:law), [the T parameter](hyp:T), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def tailRemainder (law : ObservedLaw) (T : ℝ) (x : unitInterval) : ℝ :=
  law.e x*(∫ y, y-clipY T y ∂law.Q true x)+(1-law.e x)*(∫ y, y-clipY T y ∂law.Q false x)

/-- Exact treated-arm mean discarded by clipping, without a smoothness approximation. This statement assumes [the law parameter](hyp:law), [the T parameter](hyp:T), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def treatedTailRemainder (law : ObservedLaw) (T : ℝ) (x : unitInterval) : ℝ :=
  ∫ y, y-clipY T y ∂law.Q true x
/-- Exact tail correction: subtract the main discarded tail and add the tails of all subtracted pair scores. This statement assumes [the law parameter](hyp:law), [the J parameter](hyp:J), [the L parameter](hyp:L), [the T0 parameter](hyp:T0), [the T parameter](hyp:T). [This is the stated defined object](goal). -/
def multiresMeanTail (law : ObservedLaw) (J L : ℕ) (T0 : ℝ) (T : Fin L → ℝ) : Vec J :=
  -(∫ x, (law.e x*treatedTailRemainder law T0 x) • featureMap J x ∂design)+
  (∫ x, (law.e x*projOp J (tailRemainder law T0) x) • featureMap J x ∂design)+
  ∑ j : Fin L, ∫ x, (law.e x*(∫ z, diffKernel (2^j.val*J) x z*tailRemainder law (T j) z ∂design)) • featureMap J x ∂design
/-- The two single-record coefficient kernels, with true denoting the treatment coefficient. This statement assumes [the J parameter](hyp:J), [the T0 parameter](hyp:T0), [the r parameter](hyp:r), [the o parameter](hyp:o). [This is the stated defined object](goal). -/
def multiresSingleKernel (J : ℕ) (T0 : ℝ) (r : Bool) (o : Record) : Vec J :=
  (treatment o*(if r then 1 else clipY T0 (Y o))) • featureMap J (X o)
/-- Symmetrize the complete signed pair correction, retaining the initial and all increment cutoffs. This statement assumes [the J parameter](hyp:J), [the L parameter](hyp:L), [the T0 parameter](hyp:T0), [the T parameter](hyp:T), [the r parameter](hyp:r), [the o parameter](hyp:o), [the z parameter](hyp:z). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. [Defining clause 3](step:3) is used. -/
def multiresPairKernel (J L : ℕ) (T0 : ℝ) (T : Fin L → ℝ) (r : Bool) (o z : Record) : Vec J :=
  let leg := fun (G : unitInterval → unitInterval → ℝ) (t : ℝ) (o z : Record) =>
    (treatment o*G (X o) (X z)*(if r then treatment z else clipY t (Y z))) • featureMap J (X o)
  let ordered := fun o z => -leg (projKernel J) T0 o z-
    ∑ j : Fin L, leg (diffKernel (2^j.val*J)) (T j) o z
  (1/2:ℝ) • (ordered o z+ordered z o)
/-- Mean of a vector-valued symmetric pair kernel under the true record law. This statement assumes [the law parameter](hyp:law), [the g parameter](hyp:g). [This is the stated defined object](goal). -/
def vectorPairMean {J : ℕ} (law : ObservedLaw) (g : Record → Record → Vec J) : Vec J :=
  ∫ z : Record × Record, g z.1 z.2 ∂law.P.prod law.P
/-- True-law singleton projection of a symmetric vector-valued pair kernel. This statement assumes [the law parameter](hyp:law), [the g parameter](hyp:g), [the o parameter](hyp:o). [This is the stated defined object](goal). -/
def vectorSingleton {J : ℕ} (law : ObservedLaw) (g : Record → Record → Vec J) (o : Record) : Vec J :=
  (∫ z, g o z ∂law.P)-vectorPairMean law g
/-- Canonical pair projection removes the mean and both singleton terms. This statement assumes [the law parameter](hyp:law), [the g parameter](hyp:g), [the o parameter](hyp:o), [the z parameter](hyp:z). [This is the stated defined object](goal). -/
def vectorCanonical {J : ℕ} (law : ObservedLaw) (g : Record → Record → Vec J) (o z : Record) : Vec J :=
  g o z-vectorPairMean law g-vectorSingleton law g o-vectorSingleton law g z
/-- Every independent-block two-, three- and four-record contraction of two coefficient kernels. This statement assumes [the law parameter](hyp:law), [the h parameter](hyp:h), [the h' parameter](hyp:h'), [the g parameter](hyp:g), [the g' parameter](hyp:g'). [This is the stated defined object](goal). -/
def independentContractions {J : ℕ} (law : ObservedLaw)
    (h h' : Record → Vec J) (g g' : Record → Record → Vec J) : ℝ × ℝ × ℝ × ℝ :=
  ((∫ o, ∫ z, inner ℝ (h o) (h' z) ∂law.P ∂law.P),
   (∫ o, ∫ z, ∫ w, inner ℝ (h o) (g' z w) ∂law.P ∂law.P ∂law.P),
   (∫ o, ∫ z, ∫ w, inner ℝ (g o z) (h' w) ∂law.P ∂law.P ∂law.P),
   (∫ o, ∫ z, ∫ w, ∫ t, inner ℝ (g o z) (g' w t) ∂law.P ∂law.P ∂law.P ∂law.P))
/-- Assemble all two-, three- and four-record terms of the product of two block averages. This statement assumes [the n parameter](hyp:n), [the h parameter](hyp:h), [the g parameter](hyp:g), [the data parameter](hyp:data). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. [Defining clause 3](step:3) is used. [Defining clause 4](step:4) is used. -/
def kernelContractionStatistic {J : ℕ} (n : ℕ) (h : Record → Vec J)
    (g : Record → Record → Vec J) (data : Dataset n) : ℝ :=
  if n < 4 then 0 else
  let s := (blockSize n:ℝ)
  let B0 := evalBlock n false
  let B1 := evalBlock n true
  (s^2)⁻¹*(∑ i ∈ B0, ∑ j ∈ B1, inner ℝ (h (data i)) (h (data j)))+
  (s^2*(s-1))⁻¹*(∑ i ∈ B0, ∑ j ∈ B1, ∑ k ∈ B1.erase j,
    inner ℝ (h (data i)) (g (data j) (data k)))+
  (s^2*(s-1))⁻¹*(∑ i ∈ B0, ∑ j ∈ B0.erase i, ∑ k ∈ B1,
    inner ℝ (g (data i) (data j)) (h (data k)))+
  (s^2*(s-1)^2)⁻¹*(∑ i ∈ B0, ∑ j ∈ B0.erase i, ∑ k ∈ B1, ∑ l ∈ B1.erase k,
    inner ℝ (g (data i) (data j)) (g (data k) (data l)))
/-- The complete multiresolution quadratic expansion uses both affine coefficients in every contraction. This statement assumes [the n parameter](hyp:n), [the J parameter](hyp:J), [the L parameter](hyp:L), [the T0 parameter](hyp:T0), [the T parameter](hyp:T), [the c parameter](hyp:c), [the data parameter](hyp:data). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. [Defining clause 3](step:3) is used. -/
def multiresContractionStatistic (n J L : ℕ) (T0 : ℝ) (T : Fin L → ℝ)
    (c : ℝ) (data : Dataset n) : ℝ :=
  let h := multiresSingleKernel J T0
  let g := multiresPairKernel J L T0 T
  kernelContractionStatistic n (fun o => h false o-c • h true o)
    (fun o z => g false o z-c • g true o z) data
/-- Swapping two distinct indices preserves the complete ordered-pair sum. [This is the stated conclusion](goal). -/
-- @node: score_pair_sum_swap
lemma score_pair_sum_swap {ι E : Type*} [DecidableEq ι] [AddCommMonoid E]
    (B : Finset ι) (g : ι → ι → E) :
    (∑ i ∈ B, ∑ j ∈ B.erase i, g j i) = ∑ i ∈ B, ∑ j ∈ B.erase i, g i j := by
  have he (i : ι) : B.erase i = B.filter (fun j => j ≠ i) := by
    ext j
    simp [Finset.mem_erase, and_comm]
  simp only [he, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [ne_comm]

/-- Averaging a pair kernel with its transpose preserves its ordered-pair sum. [This is the stated conclusion](goal). -/
-- @node: score_pair_sum_symmetrize
lemma score_pair_sum_symmetrize {ι : Type*} [DecidableEq ι] {J : ℕ}
    (B : Finset ι) (g : ι → ι → Vec J) :
    (∑ i ∈ B, ∑ j ∈ B.erase i, (1/2:ℝ) • (g i j+g j i)) =
    ∑ i ∈ B, ∑ j ∈ B.erase i, g i j := by
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [score_pair_sum_swap]
  module

/-- The normalized contraction ledger is the product of the two block kernel averages. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: kernelContractionStatistic_expand
lemma kernelContractionStatistic_expand {n J : ℕ} (h : Record → Vec J) (g : Record → Record → Vec J)
    (data : Dataset n) (hn : 4 ≤ n) :
    kernelContractionStatistic n h g data =
    inner ℝ
      ((blockSize n:ℝ)⁻¹ • ∑ i ∈ evalBlock n false, h (data i)+
       ((blockSize n:ℝ)*((blockSize n:ℝ)-1))⁻¹ • ∑ i ∈ evalBlock n false, ∑ j ∈ (evalBlock n false).erase i, g (data i) (data j))
      ((blockSize n:ℝ)⁻¹ • ∑ i ∈ evalBlock n true, h (data i)+
       ((blockSize n:ℝ)*((blockSize n:ℝ)-1))⁻¹ • ∑ i ∈ evalBlock n true, ∑ j ∈ (evalBlock n true).erase i, g (data i) (data j)) := by
  unfold kernelContractionStatistic
  rw [if_neg (by omega)]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [sum_inner]
  simp only [inner_sum]
  simp only [mul_inv_rev, ← inv_pow]
  ring

/-- The symmetrized affine kernels average to the observed multiresolution score. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: multiresScore_kernel_average
lemma multiresScore_kernel_average (n J L : ℕ) (T0 : ℝ) (T : Fin L → ℝ) (c : ℝ)
    (data : Dataset n) (b : Bool) (hn : 4 ≤ n) :
    (blockSize n:ℝ)⁻¹ • ∑ i ∈ evalBlock n b,
        (multiresSingleKernel J T0 false (data i)-c • multiresSingleKernel J T0 true (data i))+
      ((blockSize n:ℝ)*((blockSize n:ℝ)-1))⁻¹ • ∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i,
        (multiresPairKernel J L T0 T false (data i) (data j)-c • multiresPairKernel J L T0 T true (data i) (data j)) =
    multiresScore n b J L T0 T c data := by
  let leg := fun (G : unitInterval → unitInterval → ℝ) (t : ℝ) (o z : Record) =>
    (treatment o*G (X o) (X z)*clipY t (Y z)) • featureMap J (X o)-
      c • ((treatment o*G (X o) (X z)*treatment z) • featureMap J (X o))
  let ordered := fun o z => -leg (projKernel J) T0 o z-
    ∑ j : Fin L, leg (diffKernel (2^j.val*J)) (T j) o z
  have hp (o z : Record) : multiresPairKernel J L T0 T false o z-c • multiresPairKernel J L T0 T true o z =
      (1/2:ℝ) • (ordered o z+ordered z o) := by
    simp only [multiresPairKernel, Bool.false_eq_true, ↓reduceIte]
    dsimp [ordered, leg]
    simp only [Finset.sum_sub_distrib, ← Finset.smul_sum]
    module
  simp_rw [hp]
  rw [score_pair_sum_symmetrize]
  dsimp [ordered, leg]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.smul_sum]
  have hs (f : Fin L → Fin n → Fin n → Vec J) :
      (∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i, ∑ k : Fin L, f k i j) =
      ∑ k : Fin L, ∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i, f k i j := by
    simp_rw [Finset.sum_comm (s := (evalBlock n b).erase _)]
    rw [Finset.sum_comm]
  rw [hs, hs]
  simp only [multiresSingleKernel, Bool.false_eq_true, ↓reduceIte, multiresScore, hScore, uScore,
    hIntercept, hTreatment, uIntercept, uTreatment, if_neg (by omega : ¬n < 4)]
  simp only [Finset.sum_sub_distrib, ← Finset.smul_sum, mul_one]
  module

/-- Expansion into the retained record contractions is exactly the original block statistic. [This is the stated conclusion](goal). -/
-- @node: multiresContractions_exact
lemma multiresContractions_exact (n J L : ℕ) (T0 : ℝ) (T : Fin L → ℝ) (c : ℝ) (data : Dataset n) :
    multiresContractionStatistic n J L T0 T c data =
      quadStat (fun b c => multiresScore n b J L T0 T c) c data := by
  by_cases hn : n < 4
  · simp [multiresContractionStatistic, kernelContractionStatistic, quadStat, multiresScore,
      hScore, uScore, hIntercept, hTreatment, uIntercept, uTreatment, hn]
  · unfold multiresContractionStatistic
    rw [kernelContractionStatistic_expand _ _ data (by omega), multiresScore_kernel_average n J L T0 T c data false (by omega),
      multiresScore_kernel_average n J L T0 T c data true (by omega)]
    rfl

/-- The public mean handle assembles the untruncated mean, exact clipped correction, both coefficient means, singleton and canonical projections, and every cross-coefficient independent-block contraction. This statement assumes [the law parameter](hyp:law), [the J parameter](hyp:J), [the L parameter](hyp:L), [the T0 parameter](hyp:T0), [the T parameter](hyp:T). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. [Defining clause 3](step:3) is used. [Defining clause 4](step:4) is used. [Defining clause 5](step:5) is used. -/
def multiresMeanHandle (law : ObservedLaw) (J L : ℕ) (T0 : ℝ) (T : Fin L → ℝ) :
    (ℝ → Vec J) × (Bool → Vec J) × (Bool → Record → Vec J) ×
    (Bool → Record → Record → Vec J) × (Bool → Bool → ℝ × ℝ × ℝ × ℝ) ×
    (∀ n : ℕ, ℝ → Dataset n → ℝ) :=
  let h := multiresSingleKernel J T0
  let g := multiresPairKernel J L T0 T
  let means := fun r => (∫ o, h r o ∂law.P)+vectorPairMean law (g r)
  let singles := fun r o => h r o-(∫ z, h r z ∂law.P)+(2:ℝ) • vectorSingleton law (g r) o
  (fun c => origMeanVector law J (2^L*J) c+multiresMeanTail law J L T0 T,
   means, singles, fun r => vectorCanonical law (g r),
   (fun r r' => independentContractions law (h r) (h r') (g r) (g r')),
   fun n => multiresContractionStatistic n J L T0 T)
/-- Exact tail correction for the single-correction member with fine rank K. This statement assumes [the law parameter](hyp:law), [the J parameter](hyp:J), [the K parameter](hyp:K), [the T0 parameter](hyp:T0). [This is the stated defined object](goal). -/
def singleMeanTail (law : ObservedLaw) (J K : ℕ) (T0 : ℝ) : Vec J :=
  -(∫ x, (law.e x*treatedTailRemainder law T0 x) • featureMap J x ∂design)+
  (∫ x, (law.e x*projOp K (tailRemainder law T0) x) • featureMap J x ∂design)
/-- Symmetrized negative fine-rank correction for either affine coefficient. This statement assumes [the J parameter](hyp:J), [the K parameter](hyp:K), [the T0 parameter](hyp:T0), [the r parameter](hyp:r), [the o parameter](hyp:o), [the z parameter](hyp:z). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. -/
def singlePairKernel (J K : ℕ) (T0 : ℝ) (r : Bool) (o z : Record) : Vec J :=
  let leg := fun o z =>
    (treatment o*projKernel K (X o) (X z)*(if r then treatment z else clipY T0 (Y z))) • featureMap J (X o)
  (-1/2:ℝ) • (leg o z+leg z o)
/-- Mean, singleton, canonical and contraction data for the single-correction branch. This statement assumes [the law parameter](hyp:law), [the J parameter](hyp:J), [the K parameter](hyp:K), [the T0 parameter](hyp:T0). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. [Defining clause 3](step:3) is used. [Defining clause 4](step:4) is used. [Defining clause 5](step:5) is used. -/
def singleMeanHandle (law : ObservedLaw) (J K : ℕ) (T0 : ℝ) :
    (ℝ → Vec J) × (Bool → Vec J) × (Bool → Record → Vec J) ×
    (Bool → Record → Record → Vec J) × (Bool → Bool → ℝ × ℝ × ℝ × ℝ) ×
    (∀ n : ℕ, ℝ → Dataset n → ℝ) :=
  let h := multiresSingleKernel J T0
  let g := singlePairKernel J K T0
  let means := fun r => (∫ o, h r o ∂law.P)+vectorPairMean law (g r)
  let singles := fun r o => h r o-(∫ z, h r z ∂law.P)+(2:ℝ) • vectorSingleton law (g r) o
  (fun c => origMeanVector law J K c+singleMeanTail law J K T0,
   means, singles, fun r => vectorCanonical law (g r),
   (fun r r' => independentContractions law (h r) (h r') (g r) (g r')),
   fun n c => kernelContractionStatistic n (fun o => h false o-c • h true o)
     (fun o z => g false o z-c • g true o z))
/-- [Original-mean remainder and true-law projection handle](goal). Use exactly the two score members of Definition \(\mathrm{def:calibration\mbox{-}handle}\). For the multiresolution member take coarse rank \(J_{\mathrm c}=J\), fine rank \(J_{\mathrm f}=2^LJ\), main cutoff \(T_0\), and increment cutoffs \(T_j\), \(j\in\operatorname{Fin}(L)\); for the single- correction member take coarse rank \(J_{\mathrm c}=J\), fine rank \(J_{\mathrm f}=K\), and cutoff \(T_0\). In either branch compute the population original mean \[\int_0^1F_{J_{\mathrm c}}(x)\{e_P(x)(1-(\Pi_{J_{\mathrm f}}e_P)(x))(\tau_P(x)-c)+(e_P(x)-(\Pi_{J_{\mathrm f}}e_P)(x))m_{0,P}(x)\}\,dx,\] and add respectively the exact multiresolution or single-correction clipping-tail remainder. For each affine coefficient \(r\in\{0,1\}\), let \(h_r\) be the branch's raw single-record kernel and \(g_r\) its raw symmetric pair kernel. Retain their population coefficient means \(\mathbb E h_r+\mathbb E g_r\), singleton projections \(h_r-\mathbb E h_r+2g_{r,1}\), and canonical pair projections \(g_r-\mathbb E g_r-g_{r,1}(o)-g_{r,1}(z)\). For every pair \(r,r'\), retain the four population raw-kernel contractions \(h_r\!\times h_{r'}\), \(h_r\!\times g_{r'}\), \(g_r\!\times h_{r'}\), and \(g_r\!\times g_{r'}\), where each contraction is the expectation of a Euclidean inner product over the displayed independent records. For each \(c\), put \(h_c=h_0-c h_1\) and \(g_c=g_0-c g_1\). The sample object is the single \(c\)-indexed normalized two-block statistic \(W(c)=\langle Z_0(c),Z_1(c)\rangle\), expanded as the total of its two-, three-, and four-record sums of Euclidean inner products over independent blocks and distinct within-block indices. Its two mixed affine-coefficient contributions are retained through their sum, rather than as separate sample outputs. The existing Lean branches are multiresMeanHandle and singleMeanHandle; their raw kernels are multiresSingleKernel with multiresPairKernel or singlePairKernel. Their normalized sample assembly is kernelContractionStatistic, evaluated on the affine kernels, and the existing multiresContractions_exact and singleContractions_exact proofs identify it with the inner product of the two block vectors. This statement assumes [the law parameter](hyp:law), [the J parameter](hyp:J), [the K parameter](hyp:K), [the L parameter](hyp:L), [the T0 parameter](hyp:T0), [the T parameter](hyp:T). -/
-- @node: def:mean-handle
def origMeanHandle (law : ObservedLaw) (J K L : ℕ) (T0 : ℝ) (T : Fin L → ℝ) :
    ((ℝ → Vec J) × (Bool → Vec J) × (Bool → Record → Vec J) ×
      (Bool → Record → Record → Vec J) × (Bool → Bool → ℝ × ℝ × ℝ × ℝ) ×
      (∀ n : ℕ, ℝ → Dataset n → ℝ)) ×
    ((ℝ → Vec J) × (Bool → Vec J) × (Bool → Record → Vec J) ×
      (Bool → Record → Record → Vec J) × (Bool → Bool → ℝ × ℝ × ℝ × ℝ) ×
      (∀ n : ℕ, ℝ → Dataset n → ℝ)) :=
  (multiresMeanHandle law J L T0 T, singleMeanHandle law J K T0)
/-- The symmetrized affine kernels average to the observed single-correction score. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: singleScore_kernel_average
lemma singleScore_kernel_average (n J K : ℕ) (T c : ℝ) (data : Dataset n) (b : Bool) (hn : 4 ≤ n) :
    (blockSize n:ℝ)⁻¹ • ∑ i ∈ evalBlock n b,
        (multiresSingleKernel J T false (data i)-c • multiresSingleKernel J T true (data i))+
      ((blockSize n:ℝ)*((blockSize n:ℝ)-1))⁻¹ • ∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i,
        (singlePairKernel J K T false (data i) (data j)-c • singlePairKernel J K T true (data i) (data j)) =
    hScore n b J T c data-uScore n b J (projKernel K) T c data := by
  let leg := fun o z : Record =>
    (treatment o*projKernel K (X o) (X z)*clipY T (Y z)) • featureMap J (X o)-
      c • ((treatment o*projKernel K (X o) (X z)*treatment z) • featureMap J (X o))
  have hp (o z : Record) : singlePairKernel J K T false o z-c • singlePairKernel J K T true o z =
      -(1/2:ℝ) • (leg o z+leg z o) := by
    simp only [singlePairKernel, Bool.false_eq_true, ↓reduceIte]
    dsimp [leg]
    module
  simp_rw [hp]
  simp only [neg_smul, Finset.sum_neg_distrib]
  rw [score_pair_sum_symmetrize]
  simp only [multiresSingleKernel, Bool.false_eq_true, ↓reduceIte, hScore, uScore,
    hIntercept, hTreatment, uIntercept, uTreatment, if_neg (by omega : ¬n < 4)]
  dsimp [leg]
  simp only [Finset.sum_sub_distrib, ← Finset.smul_sum, mul_one]
  module

/-- The single-correction contraction assembly equals the observed independent-block statistic. [This is the stated conclusion](goal). -/
-- @node: singleContractions_exact
lemma singleContractions_exact (n J K : ℕ) (T0 c : ℝ) (data : Dataset n) :
    kernelContractionStatistic n
      (fun o => multiresSingleKernel J T0 false o-c • multiresSingleKernel J T0 true o)
      (fun o z => singlePairKernel J K T0 false o z-c • singlePairKernel J K T0 true o z) data =
    quadStat (fun b c data => hScore n b J T0 c data-uScore n b J (projKernel K) T0 c data) c data := by
  by_cases hn : n < 4
  · simp [kernelContractionStatistic, quadStat, hScore, uScore,
      hIntercept, hTreatment, uIntercept, uTreatment, hn]
  · rw [kernelContractionStatistic_expand _ _ data (by omega), singleScore_kernel_average n J K T0 c data false (by omega),
      singleScore_kernel_average n J K T0 c data true (by omega)]
    rfl

/-- The endpoint-and-vertex formula is a lower bound on the entire null interval. This statement assumes [the hx condition](hyp:hx). [This is the stated conclusion](goal). -/
-- @node: quadraticMin_le
lemma quadraticMin_le (q0 q1 q2 x : ℝ) (hx : |x| ≤ 1/2) :
    quadraticMin q0 q1 q2 ≤ q0+q1*x+q2*x^2 := by
  have hx' := abs_le.mp hx
  unfold quadraticMin
  dsimp only
  split
  · rename_i hv
    apply (min_le_right _ _).trans
    have hq : q2 ≠ 0 := ne_of_gt hv.1
    have heq : q0+q1*x+q2*x^2-(q0-q1^2/(4*q2)) =
        q2*(x+q1/(2*q2))^2 := by field_simp; ring
    have hp := mul_nonneg hv.1.le (sq_nonneg (x+q1/(2*q2)))
    linarith
  · rename_i hv
    by_cases hq : 0 < q2
    · have heq : 2*q2*(-q1/(2*q2)) = -q1 := by field_simp
      have hout : -q1/(2*q2) < -1/2 ∨ 1/2 < -q1/(2*q2) := by
        by_cases hl : -1/2 ≤ -q1/(2*q2)
        · exact Or.inr (lt_of_not_ge (fun hr => hv ⟨hq,hl,hr⟩))
        · exact Or.inl (lt_of_not_ge hl)
      rcases hout with hl | hr
      · have hlin : q2 ≤ q1 := by nlinarith
        have hp := mul_nonneg (by linarith : 0 ≤ x+1/2)
          (by nlinarith : 0 ≤ q1+q2*(x-1/2))
        apply (min_le_left _ _).trans
        nlinarith
      · have hlin : q1 ≤ -q2 := by nlinarith
        have hp := mul_nonneg (by linarith : 0 ≤ 1/2-x)
          (by nlinarith : 0 ≤ -q1-q2*(x+1/2))
        apply (min_le_right _ _).trans
        nlinarith
    · have hs : x^2 ≤ 1/4 := by nlinarith [sq_nonneg (x+1/2), sq_nonneg (x-1/2)]
      have hp := mul_nonneg (by linarith : 0 ≤ -q2) (by linarith : 0 ≤ 1/4-x^2)
      by_cases hl : 0 ≤ q1
      · apply (min_le_left _ _).trans
        nlinarith [mul_nonneg hl (by linarith : 0 ≤ x+1/2)]
      · apply (min_le_right _ _).trans
        nlinarith [mul_nonneg (by linarith : 0 ≤ -q1) (by linarith : 0 ≤ 1/2-x)]

/-- A public endpoint or an admissible vertex attains the finite quadratic minimum. [This is the stated conclusion](goal). -/
-- @node: quadraticMin_attained
lemma quadraticMin_attained (q0 q1 q2 : ℝ) :
    ∃ x : ℝ, |x| ≤ 1/2 ∧ q0+q1*x+q2*x^2 = quadraticMin q0 q1 q2 := by
  have hend : ∃ x : ℝ, |x| ≤ 1/2 ∧ q0+q1*x+q2*x^2 =
      min (q0-q1/2+q2/4) (q0+q1/2+q2/4) := by
    by_cases h : q0-q1/2+q2/4 ≤ q0+q1/2+q2/4
    · refine ⟨-1/2, by norm_num, ?_⟩
      rw [min_eq_left h]; ring
    · refine ⟨1/2, by norm_num, ?_⟩
      rw [min_eq_right (le_of_not_ge h)]; ring
  unfold quadraticMin
  dsimp only
  split
  · rename_i hv
    by_cases he : min (q0-q1/2+q2/4) (q0+q1/2+q2/4) ≤ q0-q1^2/(4*q2)
    · rw [min_eq_left he]
      exact hend
    · rw [min_eq_right (le_of_not_ge he)]
      refine ⟨-q1/(2*q2), abs_le.mpr ⟨by linarith [hv.2.1], hv.2.2⟩, ?_⟩
      have hq : q2 ≠ 0 := ne_of_gt hv.1
      field_simp; ring
  · exact hend

/-- The finite quadratic minimum agrees with the infimum over every admissible null constant. [This is the stated conclusion](goal). -/
-- @node: quadraticMin_eq_iInf
lemma quadraticMin_eq_iInf (q0 q1 q2 : ℝ) :
    quadraticMin q0 q1 q2 = ⨅ c : {c : ℝ // |c| ≤ 1/2}, q0+q1*c.1+q2*c.1^2 := by
  have hb : BddBelow (Set.range (fun c : {c : ℝ // |c| ≤ 1/2} => q0+q1*c.1+q2*c.1^2)) := by
    refine ⟨quadraticMin q0 q1 q2, ?_⟩
    rintro _ ⟨c, rfl⟩
    exact quadraticMin_le q0 q1 q2 c.1 c.2
  have : Nonempty {c : ℝ // |c| ≤ 1/2} := ⟨⟨0, by norm_num⟩⟩
  apply le_antisymm
  · exact le_ciInf (fun c => quadraticMin_le q0 q1 q2 c.1 c.2)
  · obtain ⟨x,hx,he⟩ := quadraticMin_attained q0 q1 q2
    exact (ciInf_le hb ⟨x,hx⟩).trans he.le

/-- An affine vector score has the quadratic coefficients used by the finite profile. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: profiledMin_eq_iInf_of_affine
lemma profiledMin_eq_iInf_of_affine {n J : ℕ}
    (score : Bool → ℝ → Dataset n → Vec J) (data : Dataset n)
    (ha : ∀ b c, score b c data = score b 0 data-c • (score b 0 data-score b 1 data)) :
    profiledMin score data = ⨅ c : {c : ℝ // |c| ≤ 1/2}, quadStat score c.1 data := by
  unfold profiledMin
  rw [quadraticMin_eq_iInf]
  congr 1
  funext c
  rw [quadStat, ha false c.1, ha true c.1]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The single-record score is affine in the candidate constant. [This is the stated conclusion](goal). -/
-- @node: hScore_affine
lemma hScore_affine (n J : ℕ) (b : Bool) (T c : ℝ) (data : Dataset n) :
    hScore n b J T c data = hScore n b J T 0 data-c •
      (hScore n b J T 0 data-hScore n b J T 1 data) := by
  simp only [hScore, zero_smul, one_smul, sub_zero]
  module

/-- The correction score is affine in the candidate constant. [This is the stated conclusion](goal). -/
-- @node: uScore_affine
lemma uScore_affine (n J : ℕ) (b : Bool) (G : unitInterval → unitInterval → ℝ)
    (T c : ℝ) (data : Dataset n) :
    uScore n b J G T c data = uScore n b J G T 0 data-c •
      (uScore n b J G T 0 data-uScore n b J G T 1 data) := by
  simp only [uScore, zero_smul, one_smul, sub_zero]
  module

/-- All dyadic corrections retain the same affine dependence on the null constant. [This is the stated conclusion](goal). -/
-- @node: multiresScore_affine
lemma multiresScore_affine (n J L : ℕ) (b : Bool) (T0 : ℝ) (T : Fin L → ℝ)
    (c : ℝ) (data : Dataset n) :
    multiresScore n b J L T0 T c data = multiresScore n b J L T0 T 0 data-c •
      (multiresScore n b J L T0 T 0 data-multiresScore n b J L T0 T 1 data) := by
  simp only [multiresScore, hScore, uScore, zero_smul, one_smul, sub_zero,
    Finset.sum_sub_distrib, ← Finset.smul_sum]
  module

/-- Multiresscore profiledmin: the displayed mathematical construction or bound. [This is the stated conclusion](goal). -/
-- @node: multiresScore_profiledMin
lemma multiresScore_profiledMin (n J L : ℕ) (T0 : ℝ) (T : Fin L → ℝ) (data : Dataset n) :
    profiledMin (fun b c => multiresScore n b J L T0 T c) data =
      ⨅ c : {c : ℝ // |c| ≤ 1/2}, quadStat (fun b c => multiresScore n b J L T0 T c) c.1 data := by
  apply profiledMin_eq_iInf_of_affine
  intro b c
  exact multiresScore_affine n J L b T0 T c data

end CausalSmith.Stat.FinitepHomogeneityDensegamma

module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ProjectionGeometry
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreConditionalProjection
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreLedgerEnergy
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreIntegrability
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TruncationMoments
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TreatmentCoefficient
public import Causalean.Mathlib.Probability.CovarianceCauchySchwarz
public import Mathlib.Probability.Moments.Covariance

/-! Finite-moment homogeneity testing: TOriginalScoreCovarianceLedger. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Ledgercoeff: the displayed mathematical construction or bound. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the b parameter](hyp:b), [the r parameter](hyp:r), [the data parameter](hyp:data). [This is the stated defined object](goal). -/
def ledgerCoeff (n : ℕ) (v : Params) (b r : Bool) (data : Dataset n) : Vec (ledgerM n v) :=
  if r then ledgerScore n v b 0 data-ledgerScore n v b 1 data else ledgerScore n v b 0 data
/-- Covarianceledger: the displayed mathematical construction or bound. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the law parameter](hyp:law). [This is the stated defined object](goal). -/
def CovarianceLedger (n : ℕ) (v : Params) (law : ObservedLaw) : Prop :=
  (∀ b r u, MemLp (fun data => inner ℝ u (ledgerCoeff n v b r data)) 2 (Measure.pi fun _ : Fin n => law.P) ∧
    variance (fun data => inner ℝ u (ledgerCoeff n v b r data)) (Measure.pi fun _ : Fin n => law.P) ≤ ledgerCov n v*‖u‖^2) ∧
  ∀ b u z, |covariance (fun data => inner ℝ u (ledgerCoeff n v b false data))
    (fun data => inner ℝ z (ledgerCoeff n v b true data)) (Measure.pi fun _ : Fin n => law.P)| ≤ ledgerCov n v*‖u‖*‖z‖

/-- The stipulated small-sample branch sets both coefficients identically to zero. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: ledgerCoeff_small_sample
lemma ledgerCoeff_small_sample (n : ℕ) (v : Params) (b r : Bool)
    (hn : n < 4) (data : Dataset n) : ledgerCoeff n v b r data = 0 := by
  cases r <;> simp [ledgerCoeff, ledgerScore, hn]

/-- The small-sample covariance ledger holds exactly, including cross-coefficient covariance. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: covarianceLedger_small_sample
lemma covarianceLedger_small_sample (n : ℕ) (v : Params) (law : ObservedLaw)
    (hn : n < 4) : CovarianceLedger n v law := by
  have hz (b r : Bool) : ledgerCoeff n v b r = fun _ => 0 :=
    funext (ledgerCoeff_small_sample n v b r hn)
  constructor
  · intro b r u
    rw [hz]
    simp [ledgerCov, hn, variance, evariance]
  · intro b u z
    rw [hz b false, hz b true]
    simp [ledgerCov, hn]

/-- In the single-cutoff branch the treatment coefficient contains only treatment labels. This statement assumes [the hn condition](hyp:hn), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledgerCoeff_treatment_single
lemma ledgerCoeff_treatment_single (n : ℕ) (v : Params) (b : Bool) (hn : 4 ≤ n)
    (hb : singleBranch v) (data : Dataset n) :
    ledgerCoeff n v b true data = hTreatment n b (ledgerM n v) data-
      uTreatment n b (ledgerM n v) (projKernel (ledgerK n v)) data := by
  simp only [ledgerCoeff, if_true, ledgerScore, if_neg (by omega : ¬n < 4), if_pos hb]
  have hh := hScore_treatment_coefficient n (ledgerM n v) b (ledgerT0 n v) data
  have hu := uScore_treatment_coefficient n (ledgerM n v) b
    (projKernel (ledgerK n v)) (ledgerT0 n v) data
  calc
    _ = (hScore n b (ledgerM n v) (ledgerT0 n v) 0 data-
          hScore n b (ledgerM n v) (ledgerT0 n v) 1 data)-
        (uScore n b (ledgerM n v) (projKernel (ledgerK n v)) (ledgerT0 n v) 0 data-
          uScore n b (ledgerM n v) (projKernel (ledgerK n v)) (ledgerT0 n v) 1 data) := by module
    _ = _ := by rw [hh, hu]

/-- All level-specific outcome cutoffs cancel from the multilevel treatment coefficient. This statement assumes [the hn condition](hyp:hn), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: ledgerCoeff_treatment_multilevel
lemma ledgerCoeff_treatment_multilevel (n : ℕ) (v : Params) (b : Bool) (hn : 4 ≤ n)
    (hb : ¬singleBranch v) (data : Dataset n) :
    ledgerCoeff n v b true data = hTreatment n b (ledgerM n v) data-
      uTreatment n b (ledgerM n v) (projKernel (2^ledgerL n v*ledgerM n v)) data := by
  simp only [ledgerCoeff, if_true, ledgerScore, if_neg (by omega : ¬n < 4), if_neg hb]
  exact multiresScore_treatment_coefficient n (ledgerM n v) (ledgerL n v) b
    (ledgerT0 n v) (fun j => ledgerT n v (j.val+1)) data

/-- Both affine score coefficients are square integrable under every original sampling law. [This is the stated conclusion](goal). -/
-- @node: ledgerCoeff_memLp
lemma ledgerCoeff_memLp (n : ℕ) (v : Params) (b r : Bool) (law : ObservedLaw) :
    MemLp (ledgerCoeff n v b r) 2 (Measure.pi fun _ : Fin n => law.P) := by
  unfold ledgerCoeff
  split
  · exact (ledgerScore_memLp n v b 0 _ 2).sub (ledgerScore_memLp n v b 1 _ 2)
  · exact ledgerScore_memLp n v b 0 _ 2

/-- Every scalar contrast of an affine coefficient has the required second moment. [This is the stated conclusion](goal). -/
-- @node: ledgerCoeff_inner_memLp
lemma ledgerCoeff_inner_memLp (n : ℕ) (v : Params) (b r : Bool) (law : ObservedLaw)
    (u : Vec (ledgerM n v)) :
    MemLp (fun data => inner ℝ u (ledgerCoeff n v b r data)) 2
      (Measure.pi fun _ : Fin n => law.P) :=
  (ledgerCoeff_memLp n v b r law).const_inner u

/-- Every scalar affine coefficient is the pair average of its selected packaged kernel. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
lemma ledgerScalarKernel_average (n : ℕ) (v : Params) (hn : 4 ≤ n)
    (b r : Bool) (u : Vec (ledgerM n v)) (data : Dataset n) :
    evalBlockPairAverage n b (ledgerScalarKernel n v r u) data =
      inner ℝ u (ledgerCoeff n v b r data) := by
  by_cases hb : singleBranch v
  · rw [ledgerScalarKernel, if_pos hb,
      singleScalarKernel_average n _ _ hn b r (ledgerT0 n v) u data]
    unfold ledgerCoeff ledgerScore
    simp only [if_neg (by omega : ¬n < 4), if_pos hb]
  · rw [ledgerScalarKernel, if_neg hb,
      multiresScalarKernel_average n _ _ hn b r (ledgerT0 n v)
        (fun j => ledgerT n v (j.val+1)) u data]
    unfold ledgerCoeff ledgerScore
    simp only [if_neg (by omega : ¬n < 4), if_neg hb]

/-- The two coefficient variance bounds imply their cross-covariance bound by Cauchy--Schwarz. This statement assumes [the hvar condition](hyp:hvar). [This is the stated conclusion](goal). -/
-- @node: ledger_cross_covariance_of_variance
lemma ledger_cross_covariance_of_variance (n : ℕ) (v : Params) (law : ObservedLaw)
    (hvar : ∀ b r u,
      variance (fun data => inner ℝ u (ledgerCoeff n v b r data))
        (Measure.pi fun _ : Fin n => law.P) ≤ ledgerCov n v*‖u‖^2) :
    ∀ b u z, |covariance (fun data => inner ℝ u (ledgerCoeff n v b false data))
      (fun data => inner ℝ z (ledgerCoeff n v b true data))
        (Measure.pi fun _ : Fin n => law.P)| ≤ ledgerCov n v*‖u‖*‖z‖ := by
  intro b u z
  have hcov : 0 ≤ ledgerCov n v := by
    by_cases hn : n < 4
    · simp [ledgerCov, hn]
    · have hs : (2 : ℝ) ≤ blockSize n := by
        have : 2 ≤ blockSize n := by unfold blockSize; omega
        exact_mod_cast this
      have hspos : (0 : ℝ) < blockSize n := by linarith
      have hsm : (0 : ℝ) < (blockSize n : ℝ)-1 := by linarith
      simp only [ledgerCov, if_neg hn]
      positivity
  calc
    _ ≤ Real.sqrt (variance (fun data => inner ℝ u (ledgerCoeff n v b false data))
          (Measure.pi fun _ : Fin n => law.P))*
        Real.sqrt (variance (fun data => inner ℝ z (ledgerCoeff n v b true data))
          (Measure.pi fun _ : Fin n => law.P)) :=
      Causalean.Mathlib.abs_covariance_le_sqrt_mul
        (ledgerCoeff_inner_memLp n v b false law u) (ledgerCoeff_inner_memLp n v b true law z)
    _ ≤ Real.sqrt (ledgerCov n v*‖u‖^2)*Real.sqrt (ledgerCov n v*‖z‖^2) := by
      gcongr <;> apply hvar
    _ = ledgerCov n v*‖u‖*‖z‖ := by
      rw [Real.sqrt_mul hcov, Real.sqrt_mul hcov,
        Real.sqrt_sq (norm_nonneg u), Real.sqrt_sq (norm_nonneg z)]
      calc
        _ = (Real.sqrt (ledgerCov n v))^2*‖u‖*‖z‖ := by ring
        _ = _ := by rw [Real.sq_sqrt hcov]

/-- [Original score covariance ledger](goal). Write the explicit score as \(Z_b(c)=Z_{b,0}-cZ_{b,A}\). For every \(P\in\mathcal M_v\), both coefficients are square integrable and \[ \operatorname{Cov}_P(Z_{b,0})\preceq\Lambda_{n,v}I_M, \qquad \operatorname{Cov}_P(Z_{b,A})\preceq\Lambda_{n,v}I_M. \] In particular \(|u^T\operatorname{Cov}_P(Z_{b,0},Z_{b,A})z|\le\Lambda_{n,v}\|u\|_2\|z\|_2\). These bounds include every cross-level covariance and hold without any bound on \(K/n\). This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn), [the hm condition](hyp:hm). -/
-- @node: lem:original-score-covariance-ledger
lemma original_score_covariance_ledger (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (law : ObservedLaw) (hm : InModel v law) : CovarianceLedger n v law := by
  by_cases hsmall : n < 4
  · exact covarianceLedger_small_sample n v law hsmall
  have hlarge : 4 ≤ n := by omega
  have hvar : ∀ b r u,
      variance (fun data => inner ℝ u (ledgerCoeff n v b r data))
        (Measure.pi fun _ : Fin n => law.P) ≤ ledgerCov n v*‖u‖^2 := by
    intro b r u
    have hb := evalBlockPairAverage_variance_le n hlarge b law
      (ledgerScalarKernel n v r u) (ledgerScalarKernel_measurable n v r u)
      (ledgerScalarKernel_symmetric n v r u) (ledgerScalarKernel_memLp n v r law u)
      (ledgerL1 n v) (ledgerL2 n v) (‖u‖^2)
      (ledgerScalarKernel_singleton_variance_le v hv n hlarge law hm r u)
      (ledgerScalarKernel_canonical_energy_le v hv n hlarge law hm r u)
    have he : (fun data => inner ℝ u (ledgerCoeff n v b r data)) =
        evalBlockPairAverage n b (ledgerScalarKernel n v r u) := by
      funext data
      exact (ledgerScalarKernel_average n v hlarge b r u data).symm
    rw [he]
    simpa only [ledgerCov, if_neg hsmall] using hb
  exact ⟨fun b r u => ⟨ledgerCoeff_inner_memLp n v b r law u, hvar b r u⟩,
    ledger_cross_covariance_of_variance n v law hvar⟩

end CausalSmith.Stat.FinitepHomogeneityDensegamma

import CausalSmith.Substrate.CollisionSafeSpectralLaw.Measurability
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.StructuredLatticeNonempty
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TSummaryRepairTotalBorel
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-! # Borel measurability of the hard-threshold lattice criterion -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable local instance {rows cols : ℕ} : MeasurableSpace (RectMatrix rows cols) := borel _
local instance {rows cols : ℕ} : BorelSpace (RectMatrix rows cols) := ⟨rfl⟩
local instance {rows cols : ℕ} : OpensMeasurableSpace (RectMatrix rows cols) := ⟨le_rfl⟩

private lemma matrixCLM_isometry {rows cols : ℕ} : Isometry (@matrixCLM rows cols) := by
  intro A B
  rw [edist_dist, edist_dist,
    ENNReal.ofReal_eq_ofReal_iff (dist_nonneg) (dist_nonneg), dist_eq_norm, dist_eq_norm]
  change ‖matrixCLM A - matrixCLM B‖ = ‖A - B‖
  have heq : matrixCLM A - matrixCLM B = matrixCLM (A - B) := by
    ext x i
    simp [matrixCLM, Matrix.toEuclideanLin_apply]
  rw [heq]
  rfl

local instance {rows cols : ℕ} : SecondCountableTopology (RectMatrix rows cols) :=
  matrixCLM_isometry.isUniformInducing.isInducing.secondCountableTopology

private noncomputable def normalizedThresholdCoefficient (tau sigma : ℝ) (n : ℕ) : ℝ :=
  let q := n + 2
  if sigma = 0 then 0
  else if tau ≤ sigma then
    sigma⁻¹ / (1 + (tau / sigma) ^ (2 * q) / (q : ℝ))
  else
    sigma⁻¹ * (((q : ℝ) * (sigma / tau) ^ (2 * q)) /
      (1 + (q : ℝ) * (sigma / tau) ^ (2 * q)))

private lemma normalizedThresholdCoefficient_tendsto {tau sigma : ℝ}
    (htau : 0 < tau) (hsigma : 0 ≤ sigma) :
    Tendsto (normalizedThresholdCoefficient tau sigma) atTop
      (nhds (if tau ≤ sigma then sigma⁻¹ else 0)) := by
  by_cases hsigma0 : sigma = 0
  · subst sigma
    rw [if_neg (not_le_of_gt htau)]
    change Tendsto (fun n : ℕ => normalizedThresholdCoefficient tau 0 n) atTop (nhds 0)
    simpa [normalizedThresholdCoefficient] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hsigmaPos : 0 < sigma := lt_of_le_of_ne hsigma (Ne.symm hsigma0)
  by_cases hkeep : tau ≤ sigma
  · rw [if_pos hkeep]
    have hsmall : Tendsto (fun n : ℕ =>
        (tau / sigma) ^ (2 * (n + 2)) / (((n + 2 : ℕ) : ℝ))) atTop (nhds 0) := by
      by_cases heq : tau = sigma
      · subst tau
        have hi : Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ))⁻¹)
            atTop (nhds 0) := by
          have hc : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
            tendsto_natCast_atTop_atTop
          have hc2 : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ)) atTop atTop :=
            hc.comp (tendsto_add_atTop_nat 2)
          exact tendsto_inv_atTop_zero.comp hc2
        simpa [hsigma0] using hi
      · have hr0 : 0 ≤ tau / sigma := div_nonneg htau.le hsigma
        have hr1 : tau / sigma < 1 :=
          (div_lt_one hsigmaPos).mpr (lt_of_le_of_ne hkeep heq)
        have hnorm : ‖(tau / sigma) ^ 2‖ < 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          nlinarith
        have hp := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
        have hp' : Tendsto (fun n : ℕ => (tau / sigma) ^ (2 * (n + 2)))
            atTop (nhds 0) := by
          convert hp.comp (tendsto_add_atTop_nat 2) using 1
          funext n
          simp only [Function.comp_apply]
          rw [pow_mul]
        have hi : Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
          tendsto_inv_atTop_zero.comp
            (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
        simpa [div_eq_mul_inv] using hp'.mul hi
    have hden : Tendsto (fun n : ℕ => 1 +
        (tau / sigma) ^ (2 * (n + 2)) / (((n + 2 : ℕ) : ℝ))) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add hsmall
    have hout : Tendsto (fun n : ℕ => sigma⁻¹ /
        (1 + (tau / sigma) ^ (2 * (n + 2)) / (((n + 2 : ℕ) : ℝ))))
        atTop (nhds sigma⁻¹) := by
      convert tendsto_const_nhds.div hden one_ne_zero using 1
      · funext n
        rfl
      · simp
    convert hout using 1
    funext n
    simp [normalizedThresholdCoefficient, hsigma0, hkeep]
  · rw [if_neg hkeep]
    have hlt : sigma < tau := lt_of_not_ge hkeep
    have hr0 : 0 ≤ sigma / tau := div_nonneg hsigma htau.le
    have hr1 : sigma / tau < 1 := (div_lt_one htau).mpr hlt
    have hr2 : 0 ≤ (sigma / tau) ^ 2 := sq_nonneg _
    have hr2lt : (sigma / tau) ^ 2 < 1 := by nlinarith
    have ht0 : Tendsto (fun q : ℕ => (q : ℝ) * ((sigma / tau) ^ 2) ^ q)
        atTop (nhds 0) := tendsto_self_mul_const_pow_of_lt_one hr2 hr2lt
    have ht : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ) *
        (sigma / tau) ^ (2 * (n + 2))) atTop (nhds 0) := by
      convert ht0.comp (tendsto_add_atTop_nat 2) using 1
      funext n
      simp only [Function.comp_apply]
      rw [pow_mul]
    have hden : Tendsto (fun n : ℕ => 1 + ((n + 2 : ℕ) : ℝ) *
        (sigma / tau) ^ (2 * (n + 2))) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add ht
    have hquot : Tendsto (fun n : ℕ =>
        (((n + 2 : ℕ) : ℝ) * (sigma / tau) ^ (2 * (n + 2))) /
          (1 + ((n + 2 : ℕ) : ℝ) * (sigma / tau) ^ (2 * (n + 2))))
        atTop (nhds 0) := by
      convert ht.div hden one_ne_zero using 1
      · funext n
        rfl
      · simp
    have hout : Tendsto (fun n : ℕ => sigma⁻¹ *
        ((((n + 2 : ℕ) : ℝ) * (sigma / tau) ^ (2 * (n + 2))) /
          (1 + ((n + 2 : ℕ) : ℝ) * (sigma / tau) ^ (2 * (n + 2)))))
        atTop (nhds 0) := by simpa using tendsto_const_nhds.mul hquot
    convert hout using 1
    funext n
    simp [normalizedThresholdCoefficient, hsigma0, hkeep]

private noncomputable def rawThresholdCoefficient (tau sigma : ℝ) (n : ℕ) : ℝ :=
  let q := n + 2
  sigma ^ (2 * q - 1) / (sigma ^ (2 * q) + tau ^ (2 * q) / (q : ℝ))

private lemma rawThresholdCoefficient_eq_normalized {tau sigma : ℝ}
    (htau : 0 < tau) (hsigma : 0 ≤ sigma) (n : ℕ) :
    rawThresholdCoefficient tau sigma n = normalizedThresholdCoefficient tau sigma n := by
  have hq : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  by_cases hsigma0 : sigma = 0
  · subst sigma
    simp [rawThresholdCoefficient, normalizedThresholdCoefficient,
      show 2 * (n + 2) - 1 ≠ 0 by omega]
  have hsigmaPos : 0 < sigma := lt_of_le_of_ne hsigma (Ne.symm hsigma0)
  have hexp : 2 * (n + 2) - 1 = 2 * n + 3 := by omega
  by_cases hkeep : tau ≤ sigma
  · simp only [rawThresholdCoefficient, normalizedThresholdCoefficient, hsigma0, if_false,
      hkeep, if_true]
    rw [hexp]
    simp only [div_pow]
    field_simp [hsigma0]
    ring
  · simp only [rawThresholdCoefficient, normalizedThresholdCoefficient, hsigma0, if_false,
      hkeep]
    rw [hexp]
    simp only [div_pow]
    field_simp [hsigma0, ne_of_gt htau]
    ring

private lemma rawThresholdCoefficient_tendsto {tau sigma : ℝ}
    (htau : 0 < tau) (hsigma : 0 ≤ sigma) :
    Tendsto (rawThresholdCoefficient tau sigma) atTop
      (nhds (if tau ≤ sigma then sigma⁻¹ else 0)) := by
  apply (normalizedThresholdCoefficient_tendsto htau hsigma).congr'
  filter_upwards [] with n
  exact (rawThresholdCoefficient_eq_normalized htau hsigma n).symm

private lemma gram_mulVec_right {rows cols : ℕ} (A : RectMatrix rows cols)
    (r : Fin cols) :
    (A.transpose * A).mulVec ((singularSystem A).right r) =
      ((singularSystem A).sigma r) ^ 2 • (singularSystem A).right r := by
  classical
  let S := singularSystem A
  ext i
  simp only [Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply, Pi.smul_apply,
    smul_eq_mul]
  calc
    ∑ j : Fin cols, (∑ l : Fin rows, A l i * A l j) * S.right r j =
        ∑ l : Fin rows, A l i * (∑ j : Fin cols, A l j * S.right r j) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ l : Fin rows, A l i * (S.sigma r * S.left r l) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [S.apply_right]
    _ = S.sigma r * (∑ l : Fin rows, A l i * S.left r l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = S.sigma r * (S.sigma r * S.right r i) := by rw [S.apply_left_transpose]
    _ = S.sigma r ^ 2 * S.right r i := by ring

private lemma gram_pow_mulVec_right {rows cols : ℕ} (A : RectMatrix rows cols)
    (r : Fin cols) (m : ℕ) :
    ((A.transpose * A) ^ m).mulVec ((singularSystem A).right r) =
      (((singularSystem A).sigma r) ^ 2) ^ m • (singularSystem A).right r := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, gram_mulVec_right, Matrix.mulVec_smul, ih]
      rw [smul_smul]
      congr 1
      exact (pow_succ' _ _).symm

private noncomputable def rationalDenominator {rows cols : ℕ} (tau : ℝ) (m : ℕ)
    (A : RectMatrix rows cols) : RectMatrix cols cols :=
  (A.transpose * A) ^ (m + 1) +
    (tau ^ (2 * (m + 1)) / ((m + 1 : ℕ) : ℝ)) • 1

private lemma rationalDenominator_posDef {rows cols : ℕ} {tau : ℝ} (htau : 0 < tau)
    (m : ℕ) (A : RectMatrix rows cols) : (rationalDenominator tau m A).PosDef := by
  have hG : (A.transpose * A).PosSemidef := by
    have heq : A.conjTranspose = A.transpose := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    rw [← heq]
    exact Matrix.posSemidef_conjTranspose_mul_self A
  have ha : 0 < tau ^ (2 * (m + 1)) / ((m + 1 : ℕ) : ℝ) := by positivity
  exact Matrix.PosDef.posSemidef_add (hG.pow (m + 1)) (Matrix.PosDef.one.smul ha)

private lemma rationalDenominator_mulVec_right {rows cols : ℕ} (tau : ℝ) (m : ℕ)
    (A : RectMatrix rows cols) (r : Fin cols) :
    (rationalDenominator tau m A).mulVec ((singularSystem A).right r) =
      ((((singularSystem A).sigma r) ^ 2) ^ (m + 1) +
        tau ^ (2 * (m + 1)) / ((m + 1 : ℕ) : ℝ)) •
          (singularSystem A).right r := by
  unfold rationalDenominator
  rw [Matrix.add_mulVec, gram_pow_mulVec_right]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  exact (add_smul _ _ _).symm

private lemma rationalDenominator_inv_mulVec_right {rows cols : ℕ} {tau : ℝ}
    (htau : 0 < tau) (m : ℕ) (A : RectMatrix rows cols) (r : Fin cols) :
    (rationalDenominator tau m A)⁻¹.mulVec ((singularSystem A).right r) =
      ((((singularSystem A).sigma r) ^ 2) ^ (m + 1) +
        tau ^ (2 * (m + 1)) / ((m + 1 : ℕ) : ℝ))⁻¹ •
          (singularSystem A).right r := by
  let lambda : ℝ := (((singularSystem A).sigma r) ^ 2) ^ (m + 1) +
    tau ^ (2 * (m + 1)) / ((m + 1 : ℕ) : ℝ)
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    positivity
  have hunit : IsUnit (rationalDenominator tau m A).det :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (rationalDenominator_posDef htau m A).isUnit)
  have hcancel := congrArg
    (fun M : RectMatrix cols cols => M.mulVec ((singularSystem A).right r))
    (Matrix.nonsing_inv_mul (rationalDenominator tau m A) hunit)
  have heigen : (rationalDenominator tau m A).mulVec ((singularSystem A).right r) =
      lambda • (singularSystem A).right r := by
    exact rationalDenominator_mulVec_right tau m A r
  rw [← Matrix.mulVec_mulVec, heigen, Matrix.mulVec_smul, Matrix.one_mulVec] at hcancel
  change (rationalDenominator tau m A)⁻¹.mulVec ((singularSystem A).right r) =
    lambda⁻¹ • (singularSystem A).right r
  calc
    (rationalDenominator tau m A)⁻¹.mulVec ((singularSystem A).right r) =
        1 • (rationalDenominator tau m A)⁻¹.mulVec ((singularSystem A).right r) :=
      (one_smul ℝ _).symm
    _ = (lambda⁻¹ * lambda) •
        (rationalDenominator tau m A)⁻¹.mulVec ((singularSystem A).right r) := by
      rw [inv_mul_cancel₀ (ne_of_gt hlambda)]
    _ = lambda⁻¹ • (lambda •
        (rationalDenominator tau m A)⁻¹.mulVec ((singularSystem A).right r)) := by
      rw [smul_smul]
    _ = lambda⁻¹ • (singularSystem A).right r := by rw [hcancel]

private lemma rationalLeftFactor_mulVec_right {rows cols : ℕ} {tau : ℝ}
    (htau : 0 < tau) (n : ℕ) (A : RectMatrix rows cols) (r : Fin cols) :
    (((A.transpose * A) ^ (n + 1)) * (rationalDenominator tau (n + 1) A)⁻¹).mulVec
        ((singularSystem A).right r) =
      ((((singularSystem A).sigma r) ^ 2) ^ (n + 1) *
        ((((singularSystem A).sigma r) ^ 2) ^ (n + 2) +
          tau ^ (2 * (n + 2)) / ((n + 2 : ℕ) : ℝ))⁻¹) •
            (singularSystem A).right r := by
  rw [← Matrix.mulVec_mulVec, rationalDenominator_inv_mulVec_right htau,
    Matrix.mulVec_smul, gram_pow_mulVec_right, smul_smul]
  simp only [Nat.reduceAdd, Nat.add_assoc]
  rw [mul_comm]

private lemma rationalThresholdApprox_entry_eq_sum {rows cols : ℕ} {tau : ℝ}
    (htau : 0 < tau) (n : ℕ) (A : RectMatrix rows cols) (i : Fin cols)
    (j : Fin rows) :
    CausalSmith.Substrate.CollisionSafeSpectralLaw.rationalThresholdApprox tau (n + 1) A i j =
      ∑ r : Fin cols, rawThresholdCoefficient tau ((singularSystem A).sigma r) n *
        (singularSystem A).right r i * (singularSystem A).left r j := by
  classical
  let S := singularSystem A
  let M := ((A.transpose * A) ^ (n + 1)) * (rationalDenominator tau (n + 1) A)⁻¹
  have hM (r : Fin cols) : M.mulVec (S.right r) =
      (((S.sigma r) ^ 2) ^ (n + 1) *
        (((S.sigma r) ^ 2) ^ (n + 2) +
          tau ^ (2 * (n + 2)) / ((n + 2 : ℕ) : ℝ))⁻¹) • S.right r := by
    exact rationalLeftFactor_mulVec_right htau n A r
  have hexpand : (fun p : Fin cols => A j p) =
      ∑ r : Fin cols, (S.sigma r * S.left r j) • S.right r := by
    funext p
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      A j p = ∑ r : Fin cols, S.sigma r * S.left r j * S.right r p := S.expansion j p
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r _
        ring
  change (M * A.transpose) i j =
    ∑ r : Fin cols, rawThresholdCoefficient tau (S.sigma r) n *
      S.right r i * S.left r j
  rw [Matrix.mul_apply]
  change M.mulVec (fun p => A j p) i = _
  rw [hexpand, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, hM, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r _
  unfold rawThresholdCoefficient
  dsimp only
  have hsigma : 0 ≤ S.sigma r := S.sigma_nonneg r
  have hexp : 2 * (n + 2) - 1 = 2 * n + 3 := by omega
  by_cases hsigma0 : S.sigma r = 0
  · simp [hsigma0, hexp]
  have hdenpos : 0 < (S.sigma r ^ 2) ^ (n + 2) +
      tau ^ (2 * (n + 2)) / ((n + 2 : ℕ) : ℝ) := by positivity
  rw [hexp, inv_eq_one_div]
  simp only [pow_two, mul_pow]
  field_simp [hsigma0, ne_of_gt hdenpos]
  ring

private lemma rationalThresholdApprox_succ_tendsto {rows cols : ℕ} {tau : ℝ}
    (htau : 0 < tau) (A : RectMatrix rows cols) :
    Tendsto (fun n =>
      CausalSmith.Substrate.CollisionSafeSpectralLaw.rationalThresholdApprox tau (n + 1) A)
      atTop (nhds (thresholdedPenroseInverse tau A)) := by
  let S := singularSystem A
  let limitCoeff : Fin cols → ℝ := fun r => if tau ≤ S.sigma r then (S.sigma r)⁻¹ else 0
  let assemble : (Fin cols → ℝ) → RectMatrix cols rows := fun c i j =>
    ∑ r : Fin cols, c r * S.right r i * S.left r j
  have hcoeff : Tendsto (fun n r => rawThresholdCoefficient tau (S.sigma r) n)
      atTop (nhds limitCoeff) := by
    rw [tendsto_pi_nhds]
    intro r
    exact rawThresholdCoefficient_tendsto htau (S.sigma_nonneg r)
  have hassemble : Continuous assemble := by
    apply continuous_matrix
    intro i j
    apply continuous_finsetSum
    intro r _
    fun_prop
  have hout : Tendsto
      (fun n => assemble (fun r => rawThresholdCoefficient tau (S.sigma r) n))
      atTop (nhds (assemble limitCoeff)) :=
    Filter.Tendsto.comp hassemble.continuousAt hcoeff
  have hseq (n : ℕ) :
      CausalSmith.Substrate.CollisionSafeSpectralLaw.rationalThresholdApprox tau (n + 1) A =
        assemble (fun r => rawThresholdCoefficient tau (S.sigma r) n) := by
    ext i j
    exact rationalThresholdApprox_entry_eq_sum htau n A i j
  have htarget : assemble limitCoeff = thresholdedPenroseInverse tau A := by
    ext i j
    simp only [assemble, limitCoeff, thresholdedPenroseInverse]
    apply Finset.sum_congr rfl
    intro r _
    rw [S.sigma_eq]
    by_cases hr : tau ≤ singularValue A r <;> simp [hr, S]
  rw [← htarget]
  apply hout.congr'
  filter_upwards [] with n
  exact (hseq n).symm

/-- The genuine SVD hard-thresholded Moore--Penrose inverse is Borel measurable, including at
the equality stratum of the convention `tau ≤ sigma`. -/
lemma thresholdedPenroseInverse_measurable {rows cols : ℕ} {tau : ℝ} (htau : 0 < tau) :
    Measurable (thresholdedPenroseInverse (rows := rows) (cols := cols) tau) := by
  apply CausalSmith.Substrate.CollisionSafeSpectralLaw.measurable_of_rationalThresholdApprox_tendsto
    htau
  intro A
  apply (tendsto_add_atTop_iff_nat (f := fun m =>
    CausalSmith.Substrate.CollisionSafeSpectralLaw.rationalThresholdApprox tau m A)
    (l := nhds (thresholdedPenroseInverse tau A)) 1).mp
  simpa only [Nat.add_comm] using rationalThresholdApprox_succ_tendsto htau A

private lemma summary_M0_continuous {dx dz : ℕ} :
    Continuous (fun s : SummarySpace dx dz => s.M0) := by
  have hcoord : Continuous (@SummarySpace.toCoordinates dx dz) := continuous_induced_dom
  simpa [Function.comp_def, SummarySpace.toCoordinates] using continuous_fst.comp hcoord

private lemma summary_M1_continuous {dx dz : ℕ} :
    Continuous (fun s : SummarySpace dx dz => s.M1) := by
  have hcoord : Continuous (@SummarySpace.toCoordinates dx dz) := continuous_induced_dom
  simpa [Function.comp_def, SummarySpace.toCoordinates] using
    (continuous_fst.comp continuous_snd).comp hcoord

private lemma summary_N0_continuous {dx dz : ℕ} :
    Continuous (fun s : SummarySpace dx dz => s.N0) := by
  have hcoord : Continuous (@SummarySpace.toCoordinates dx dz) := continuous_induced_dom
  simpa [Function.comp_def, SummarySpace.toCoordinates] using
    (continuous_fst.comp (continuous_snd.comp continuous_snd)).comp hcoord

private lemma summary_N1_continuous {dx dz : ℕ} :
    Continuous (fun s : SummarySpace dx dz => s.N1) := by
  have hcoord : Continuous (@SummarySpace.toCoordinates dx dz) := continuous_induced_dom
  simpa [Function.comp_def, SummarySpace.toCoordinates] using
    (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).comp hcoord

private lemma summary_mX_continuous {dx dz : ℕ} :
    Continuous (fun s : SummarySpace dx dz => s.mX) := by
  have hcoord : Continuous (@SummarySpace.toCoordinates dx dz) := continuous_induced_dom
  simpa [Function.comp_def, SummarySpace.toCoordinates] using
    (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).comp hcoord

lemma empiricalCompressedOperator_measurable {dx dz : ℕ} {tau : ℝ} (htau : 0 < tau) :
    Measurable (empiricalCompressedOperator (dx := dx) (dz := dz) tau) := by
  have hpinv1 : Measurable (fun s : SummarySpace dx dz =>
      thresholdedPenroseInverse tau s.M1) :=
    (thresholdedPenroseInverse_measurable htau).comp summary_M1_continuous.measurable
  have hpinv0 : Measurable (fun s : SummarySpace dx dz =>
      thresholdedPenroseInverse tau s.M0) :=
    (thresholdedPenroseInverse_measurable htau).comp summary_M0_continuous.measurable
  have hmul : Continuous
      (fun p : RectMatrix dx dz × RectMatrix dz dx => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hterm1 : Measurable (fun s : SummarySpace dx dz =>
      thresholdedPenroseInverse tau s.M1 * s.N1) :=
    hmul.measurable2 hpinv1 summary_N1_continuous.measurable
  have hterm0 : Measurable (fun s : SummarySpace dx dz =>
      thresholdedPenroseInverse tau s.M0 * s.N0) :=
    hmul.measurable2 hpinv0 summary_N0_continuous.measurable
  have hsub : Continuous
      (fun p : RectMatrix dx dx × RectMatrix dx dx => p.1 - p.2) :=
    continuous_fst.sub continuous_snd
  exact hsub.measurable2 hterm1 hterm0

lemma structuredLatticeCriterion_measurable {k dx dz : ℕ} {radius tau : ℝ}
    (htau : 0 < tau) (theta : StructuredLatticePoint k dx radius) :
    Measurable (fun s : SummarySpace dx dz => structuredLatticeCriterion tau s theta) := by
  have hop : Measurable (fun s : SummarySpace dx dz =>
      ‖matrixCLM (structuredCandidateOperator theta - empiricalCompressedOperator tau s)‖) := by
    have hsub : Continuous
        (fun B : RectMatrix dx dx => structuredCandidateOperator theta - B) := by fun_prop
    exact (continuous_norm.comp (matrixCLM_continuous.comp hsub)).measurable.comp
      (empiricalCompressedOperator_measurable htau)
  have hmean : Continuous (fun s : SummarySpace dx dz =>
      Real.sqrt (∑ i, ((∑ u, theta.V i u * (∑ v, theta.R v u * theta.weight v)) -
        s.mX i) ^ 2)) := by
    have hm := summary_mX_continuous (dx := dx) (dz := dz)
    fun_prop
  have hconstant : Measurable (fun _s : SummarySpace dx dz =>
      Real.sqrt (∑ u, ((∑ v, theta.R u v *
        (∑ i, theta.V i v * firstBasis dx i)) - 1) ^ 2)) := measurable_const
  exact (hop.add hmean.measurable).add hconstant

/-- A finite score family with measurable coordinates has a measurable smallest-index minimizer. -/
lemma finite_first_minimizer_measurable_exists {α : Type*} [MeasurableSpace α]
    {m : ℕ} (hm : 0 < m) (score : α → Fin m → ℝ)
    (hscore : ∀ i, Measurable fun x => score x i) :
    ∃ first : α → Fin m,
      Measurable first ∧
      (∀ x i, score x (first x) ≤ score x i) ∧
      ∀ x i, score x (first x) = score x i → first x ≤ i := by
  classical
  obtain ⟨first, hmin, htie⟩ := finite_first_minimizer_exists hm score
  have hfiber (j : Fin m) : MeasurableSet {x : α | first x = j} := by
    have hchar : {x : α | first x = j} =
        {x : α | ∀ i, score x j ≤ score x i} ∩
          {x : α | ∀ i, score x j = score x i → j ≤ i} := by
      ext x
      constructor
      · intro hx
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
        subst j
        exact ⟨hmin x, htie x⟩
      · rintro ⟨hjmin, hjtie⟩
        apply le_antisymm
        · exact htie x j (le_antisymm (hmin x j) (hjmin (first x)))
        · exact hjtie (first x) (le_antisymm (hjmin (first x)) (hmin x j))
    rw [hchar]
    apply MeasurableSet.inter
    · have hInter : MeasurableSet (⋂ i, {x : α | score x j ≤ score x i}) :=
        MeasurableSet.iInter fun i => measurableSet_le (hscore j) (hscore i)
      simpa [Set.setOf_forall] using hInter
    · have hInter : MeasurableSet
          (⋂ i, {x : α | score x j = score x i → j ≤ i}) := by
        apply MeasurableSet.iInter
        intro i
        by_cases hji : j ≤ i
        · simp [hji]
        · rw [show {x : α | score x j = score x i → j ≤ i} =
              {x : α | score x j = score x i}ᶜ by ext x; simp [hji]]
          exact (measurableSet_eq_fun (hscore j) (hscore i)).compl
      simpa [Set.setOf_forall] using hInter
  refine ⟨first, ?_, hmin, htie⟩
  intro t _ht
  rw [show first ⁻¹' t = ⋃ j : t, {x : α | first x = j.1} by ext x; simp]
  exact MeasurableSet.iUnion fun j => hfiber j

/-- The paper's exhaustive family admits a Borel, lexicographically first criterion minimizer on
the five-block summary space. -/
theorem structuredLatticeMeasurableSelector_exists
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    ∃ (m : ℕ) (candidate : Fin m →
        StructuredLatticePoint k dx (effectRadius dz L sigma0))
      (first : SummarySpace dx dz → Fin m),
      0 < m ∧
      (∀ i, (candidate i).WellFormed (dz := dz) (n := n) (L := L)
        (pi0 := pi0) (sigma0 := sigma0)) ∧
      (∀ θ : StructuredLatticePoint k dx (effectRadius dz L sigma0),
        θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0) →
          ∃ i, (candidate i).V = θ.V ∧ (candidate i).R = θ.R ∧
            (candidate i).weight = θ.weight ∧ (candidate i).effect = θ.effect) ∧
      (∀ i j, (candidate i).V = (candidate j).V →
        (candidate i).R = (candidate j).R →
        (candidate i).weight = (candidate j).weight →
        (candidate i).effect = (candidate j).effect → i = j) ∧
      (∀ i j, i ≤ j ↔ StructuredLatticePoint.LexLE (candidate i) (candidate j)) ∧
      Measurable first ∧
      (∀ s i, structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) s
        (candidate (first s)) ≤
          structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) s (candidate i)) ∧
      ∀ s i, structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) s
        (candidate (first s)) =
          structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) s (candidate i) →
        first s ≤ i := by
  classical
  obtain ⟨m, candidate, _sampleFirst, hm, hwf, hcomplete, hinj, horder, _hmin, _htie⟩ :=
    structuredLatticeSearch_exists hk hkx hkz hL hpi hpiMax hsigma hsigmaMax
  let tau := pi0 * sigma0 ^ 2 / 2
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  let score : SummarySpace dx dz → Fin m → ℝ := fun s i =>
    structuredLatticeCriterion tau s (candidate i)
  have hscore : ∀ i, Measurable fun s => score s i := by
    intro i
    exact structuredLatticeCriterion_measurable htau (candidate i)
  obtain ⟨first, hfirst, hfirstMin, hfirstTie⟩ :=
    finite_first_minimizer_measurable_exists hm score hscore
  exact ⟨m, candidate, first, hm, hwf, hcomplete, hinj, horder, hfirst, hfirstMin,
    hfirstTie⟩

/-- The total empirical five-block summary is measurable, including the empty-arm branch. -/
lemma structuredLattice_empSummary_measurable {n dx dz : ℕ} :
    Measurable (@empSummary n dx dz) := by
  have hc (t : Bool) : Measurable (@armCount n dx dz t) := by
    unfold armCount
    simp_rw [Finset.card_filter]
    apply Finset.measurable_sum
    intro i _hi
    exact Measurable.ite
      (measurableSet_eq_fun
        (measurable_obs_T.comp (measurable_pi_apply i)) measurable_const)
      measurable_const measurable_const
  have hm (weighted t : Bool) (a : Fin dz) (b : Fin dx) :
      Measurable (fun sample : Fin n → Obs dx dz =>
        empiricalArmMatrix weighted t sample a b) := by
    unfold empiricalArmMatrix
    apply Measurable.mul
    · exact (measurable_const.max
        ((measurable_from_nat : Measurable fun q : ℕ => (q : ℝ)).comp (hc t))).inv
    · apply Finset.measurable_sum
      intro i _hi
      exact Measurable.ite
        (measurableSet_eq_fun
          (measurable_obs_T.comp (measurable_pi_apply i)) measurable_const)
        (by
          have hX : Measurable (fun sample : Fin n → Obs dx dz => (sample i).X b) :=
            ((measurable_pi_apply b).comp measurable_obs_X).comp (measurable_pi_apply i)
          have hZ : Measurable (fun sample : Fin n → Obs dx dz => (sample i).Z a) :=
            ((measurable_pi_apply a).comp measurable_obs_Z).comp (measurable_pi_apply i)
          have hY : Measurable (fun sample : Fin n → Obs dx dz => (sample i).Y) :=
            measurable_obs_Y.comp (measurable_pi_apply i)
          cases weighted
          · convert hZ.mul hX using 1 <;> ext sample <;> simp
          · exact (hY.mul hZ).mul hX)
        measurable_const
  let e := summaryRepairSpaceHomeomorph dx dz
  have he : Measurable (fun sample : Fin n → Obs dx dz => e (empSummary sample)) := by
    change Measurable (fun sample : Fin n → Obs dx dz =>
      summaryRepairToEuc (empSummary sample))
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_lambda
    intro i
    rcases i with ⟨b, a, j⟩ | j
    · fin_cases b
      · exact hm false false a j
      · exact hm false true a j
      · exact hm true false a j
      · exact hm true true a j
    · apply Measurable.mul measurable_const
      apply Finset.measurable_sum
      intro i _hi
      exact ((measurable_pi_apply j).comp measurable_obs_X).comp (measurable_pi_apply i)
  convert e.symm.continuous.measurable.comp he using 1
  ext sample
  exact e.symm_apply_apply (empSummary sample)

private lemma atomFloor_of_measureEquivalent {k : ℕ} {radius floor : ℝ}
    {a b : AtomicLaw.ProbabilityLaw k radius}
    (hab : a.MeasureEquivalent b) (hb : AtomicLaw.AtomFloor floor b.1) :
    AtomicLaw.AtomFloor floor a.1 := by
  classical
  intro x hx
  have hagg := hab.aggregate_weight x
  have hapos : 0 < ∑ i with a.1.atom i = x, a.1.weight i := by
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hi' := (Finset.mem_filter.mp hi).2
    exact lt_of_lt_of_le hi' (Finset.single_le_sum
      (fun j _ => a.2.1 j) (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩))
  have hbpos : 0 < ∑ i with b.1.atom i = x, b.1.weight i := by
    rwa [hagg] at hapos
  obtain ⟨i, hi, hipos⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun i _ => b.2.1 i)).mp hbpos
  rw [hagg]
  apply hb x
  exact Finset.mem_image.mpr
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hipos⟩,
      (Finset.mem_filter.mp hi).2⟩

private lemma structuredLatticePoint_atomFloor
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ} (hk : 2 ≤ k)
    (theta : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (htheta : theta.WellFormed (dz := dz) (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0)) :
    AtomicLaw.AtomFloor pi0 theta.effectLaw.representative.1 := by
  classical
  let H := latticeHeight k dx n pi0 sigma0
  have hH : 0 < H := by
    have : 2 * k ≤ H := by dsimp [H, latticeHeight]; omega
    omega
  obtain ⟨_hgrid, _hpolar, _horth, _hRgrid, _hRmin, _hRmax,
      ⟨a, ha, _hasum⟩, _heffect⟩ := htheta
  have hweight (u : Fin k) : pi0 ≤ theta.weight u := by
    rw [(ha u).2]
    apply (le_div_iff₀ (by exact_mod_cast hH : (0 : ℝ) < H)).2
    calc
      pi0 * (H : ℝ) ≤ (⌈pi0 * H⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (a u : ℝ) := by exact_mod_cast (ha u).1
  let raw : AtomicLaw.ProbabilityLaw k (effectRadius dz L sigma0) :=
    ⟨⟨theta.weight, theta.effect⟩, theta.lawValid⟩
  have hraw : AtomicLaw.AtomFloor pi0 raw.1 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
    calc
      pi0 ≤ theta.weight u := hweight u
      _ ≤ ∑ i with raw.1.atom i = raw.1.atom u, raw.1.weight i :=
        Finset.single_le_sum (fun i _ => raw.2.1 i)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ u, rfl⟩)
  have hrep : theta.effectLaw.representative.MeasureEquivalent raw := by
    change (AtomicLaw.probabilityLawSetoid k (effectRadius dz L sigma0)).r
      theta.effectLaw.representative raw
    exact (Quotient.eq_mk_iff_out (x := theta.effectLaw) (y := raw)).mp rfl
  exact atomFloor_of_measureEquivalent hrep hraw

/-- The measurable structured search packages into the estimator interface, with the prescribed
atom floor and exact exhaustive-search certificate. -/
theorem structuredLatticeEstimator_exists
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    ∃ A : LatticeEstimator k dx dz n (effectRadius dz L sigma0),
      IsPrescribedStructuredLattice (L := L) (pi0 := pi0) (sigma0 := sigma0) A ∧
      A.atomFloor = pi0 ∧ Measurable A.summaryRule ∧
      (A.estimate = fun sample => A.summaryRule (empSummary sample)) ∧
      ∀ sample, AtomicLaw.AtomFloor pi0 (A.estimate sample).representative.1 := by
  classical
  obtain ⟨m, candidate, first, hm, hwf, hcomplete, hinj, horder, hfirst,
      hmin, htie⟩ := structuredLatticeMeasurableSelector_exists
        hk hkx hkz hL hpi hpiMax hsigma hsigmaMax
  let summaryRule : SummarySpace dx dz →
      AtomicLaw.LawModulo k (effectRadius dz L sigma0) := fun s =>
    (candidate (first s)).effectLaw
  have hsummaryRule : Measurable summaryRule :=
    (measurable_of_finite (fun i : Fin m => (candidate i).effectLaw)).comp hfirst
  let estimate : (Fin n → Obs dx dz) →
      AtomicLaw.LawModulo k (effectRadius dz L sigma0) := fun sample =>
    summaryRule (empSummary sample)
  have hestimate : Measurable estimate :=
    hsummaryRule.comp structuredLattice_empSummary_measurable
  let A : LatticeEstimator k dx dz n (effectRadius dz L sigma0) :=
    { summaryRule := summaryRule
      summaryRule_measurable := hsummaryRule
      estimate := estimate
      measurable := hestimate
      atomFloor := pi0
      atomFloor_valid := fun sample => structuredLatticePoint_atomFloor hk
        (candidate (first (empSummary sample))) (hwf _)
      estimate_eq := rfl
      candidateCount := m }
  refine ⟨A, ?_, rfl, hsummaryRule, rfl, ?_⟩
  · refine ⟨candidate, fun sample => first (empSummary sample), hwf, hcomplete, hinj,
      horder, ?_, ?_, rfl⟩
    · exact fun sample => hmin (empSummary sample)
    · exact fun sample => htie (empSummary sample)
  · exact A.atomFloor_valid

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionFeasible
import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionPointwise
import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionLocalInverse

/-!
# Embedding retained confidence witnesses in the contraction compactification
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open Set
open scoped Matrix.Norms.L2Operator
open Causalean.Discovery.LinearDisentanglement.Quantitative
open Causalean.Discovery.LinearDisentanglement.Quantitative.PairwiseAffine

noncomputable section

/-- Zero extension of the true and selected variables from a retained environment set. -/
def retainedUniformContractionAmbient {p m c : ℕ} (W : BackshiftSystem p m c)
    {V : InferenceWorld p m} {A : RealMatrix p}
    (X : ConfidenceCandidateWitness (c := c) V A) (S : Finset (Environment m)) :
    UniformContractionAmbient p m :=
  ((W.structural, (W.structural⁻¹, (W.invariantNoise,
      (fun e ↦ if e ∈ S then W.covariance e else 0,
       fun e ↦ if e ∈ S then W.shifts e else 0)))),
   (A, (A⁻¹, (fun e ↦ if e ∈ S then X.covariance e else 0,
      (X.invariantNoise, fun e ↦ if e ∈ S then X.shifts e else 0)))))

/-- A common radius large enough for all ten retained witness components. -/
def contractionEmbeddingRadius (p : ℕ) (κ M : ℝ) : ℝ :=
  max κ (max (contractionL0 p κ)
    (max (M + 1) (contractionL0 p κ ^ 2 * (M + 1))))

private lemma norm_le_of_unitDiagonal_condition {p : ℕ} {κ : ℝ}
    (B : RealMatrix p) (hp : 0 < p) (hκ : 1 ≤ κ)
    (hB : B ∈ admissibleSet p) (hcond : matrixConditionNumber B ≤ κ) :
    ‖B‖ ≤ contractionL0 p κ := by
  apply opNorm_le_conditionRoot B hp hκ hB.2.1
  exact ⟨hB.1, abs_det_le_factorial_of_mem_admissibleSet hB, hcond⟩

private lemma norm_inv_le_of_unitDiagonal_condition {p : ℕ} {κ : ℝ}
    (B : RealMatrix p) (hp : 0 < p) (hB : B ∈ admissibleSet p)
    (hcond : matrixConditionNumber B ≤ κ) : ‖B⁻¹‖ ≤ κ := by
  let i : Fin p := ⟨0, hp⟩
  have hone : 1 ≤ ‖B‖ := by
    have hentry := abs_entry_le_opNorm B i i
    simpa [hB.2.1 i] using hentry
  unfold matrixConditionNumber at hcond
  nlinarith [norm_nonneg B⁻¹]

private lemma true_noise_norm_le_scale {p m : ℕ} (H : Finset (Environment m))
    (Omega : RealMatrix p) (Sigma : Environment m → RealMatrix p)
    (s : Environment m → Fin p → ℝ) {M : ℝ}
    (hscale : matrixScaleBound H Omega Sigma s ≤ M) : ‖Omega‖ ≤ M := by
  unfold matrixScaleBound at hscale
  have hSigma : 0 ≤ finsetMaxNorm H Sigma := by
    unfold finsetMaxNorm
    exact (Finset.le_fold_max 0).mpr (Or.inl le_rfl)
  have hs : 0 ≤ finsetMaxNorm H (fun e ↦ Matrix.diagonal (s e)) := by
    unfold finsetMaxNorm
    exact (Finset.le_fold_max 0).mpr (Or.inl le_rfl)
  nlinarith [norm_nonneg Omega]

private lemma true_covariance_norm_le_scale {p m : ℕ} (H : Finset (Environment m))
    (Omega : RealMatrix p) (Sigma : Environment m → RealMatrix p)
    (s : Environment m → Fin p → ℝ) {M : ℝ}
    (hscale : matrixScaleBound H Omega Sigma s ≤ M)
    {e : Environment m} (he : e ∈ H) : ‖Sigma e‖ ≤ M := by
  have hemax : ‖Sigma e‖ ≤ finsetMaxNorm H Sigma := by
    unfold finsetMaxNorm
    exact (Finset.le_fold_max (c := ‖Sigma e‖)).mpr (Or.inr ⟨e, he, le_rfl⟩)
  unfold matrixScaleBound at hscale
  have hs : 0 ≤ finsetMaxNorm H (fun a ↦ Matrix.diagonal (s a)) := by
    unfold finsetMaxNorm
    exact (Finset.le_fold_max 0).mpr (Or.inl le_rfl)
  nlinarith [norm_nonneg Omega]

private lemma true_shift_norm_le_scale {p m : ℕ} (H : Finset (Environment m))
    (Omega : RealMatrix p) (Sigma : Environment m → RealMatrix p)
    (s : Environment m → Fin p → ℝ) {M : ℝ}
    (hscale : matrixScaleBound H Omega Sigma s ≤ M)
    {e : Environment m} (he : e ∈ H) : ‖s e‖ ≤ M := by
  rw [← Matrix.l2_opNorm_diagonal]
  have hemax : ‖Matrix.diagonal (s e)‖ ≤
      finsetMaxNorm H (fun a ↦ Matrix.diagonal (s a)) := by
    unfold finsetMaxNorm
    exact (Finset.le_fold_max (c := ‖Matrix.diagonal (s e)‖)).mpr
      (Or.inr ⟨e, he, le_rfl⟩)
  unfold matrixScaleBound at hscale
  have hSigma : 0 ≤ finsetMaxNorm H Sigma := by
    unfold finsetMaxNorm
    exact (Finset.le_fold_max 0).mpr (Or.inl le_rfl)
  nlinarith [norm_nonneg Omega]

private lemma transformed_honest {p m c : ℕ} (W : BackshiftSystem p m c)
    (hmodel : HonestCovarianceModel W) {e : Environment m} (he : e ∈ W.honest) :
    W.structural * W.covariance e * W.structural.transpose =
      W.invariantNoise + Matrix.diagonal (W.shifts e) := by
  have hleft : W.structural * W.structural⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ W.structural_invertible
  have hright : W.structural⁻¹.transpose * W.structural.transpose = 1 := by
    rw [← Matrix.transpose_mul, hleft, Matrix.transpose_one]
  rw [hmodel e he]
  calc
    W.structural *
        (W.structural⁻¹ * (W.invariantNoise + Matrix.diagonal (W.shifts e)) *
          W.structural⁻¹.transpose) * W.structural.transpose =
        (W.structural * W.structural⁻¹) *
          (W.invariantNoise + Matrix.diagonal (W.shifts e)) *
            (W.structural⁻¹.transpose * W.structural.transpose) := by noncomm_ring
    _ = _ := by rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]

private lemma pairwise_max_of_separated {p m : ℕ} (S : Finset (Environment m))
    [Nonempty {e // e ∈ S}] (s : ContractionShifts p m) {γ : ℝ}
    (hsep : PairwiseAffineSeparated (fun e : {e // e ∈ S} ↦ s e.1) γ) :
    ∀ i j : Fin p, i ≠ j → γ ≤ maxPairAffineDet S s i j := by
  intro i j hij
  obtain ⟨a, b, d, habd⟩ := hsep i j hij
  unfold maxPairAffineDet
  exact habd.trans (Finset.le_sup' (fun q ↦
    |pairAffineDet (fun e : {e // e ∈ S} ↦ s e.1) i j q.1 q.2.1 q.2.2|)
      (by simp : (a, b, d) ∈ (Finset.univ :
        Finset ({e // e ∈ S} × {e // e ∈ S} × {e // e ∈ S}))))

/-- The zero-extended true/candidate witness satisfies every closed fixed-support constraint. [Under the stated hypotheses](hyp:hp,hWnorm,hnonneg,hmodel,hOmega,hslack,hWcond,hAcond,hscale,hSH,hSX,hSep) [this conclusion](goal) applies. -/
lemma retainedUniformContractionAmbient_constraints
    {p m c : ℕ} (hp : 2 ≤ p) (W : BackshiftSystem p m c)
    {V : InferenceWorld p m} {A : RealMatrix p}
    (X : ConfidenceCandidateWitness (c := c) V A) (S : Finset (Environment m))
    [Nonempty {e // e ∈ S}] {ζ κ M γ : ℝ}
    (hWnorm : BackshiftNormalization W) (hnonneg : NonnegativeShifts W)
    (hmodel : HonestCovarianceModel W) (hOmega : W.invariantNoise.PosSemidef)
    (hslack : ζ ≤ normalizationSlack W.structural)
    (hWcond : matrixConditionNumber W.structural ≤ κ)
    (hAcond : matrixConditionNumber A ≤ κ)
    (hscale : matrixScaleBound W.honest W.invariantNoise W.covariance W.shifts ≤ M)
    (hSH : S ⊆ W.honest) (hSX : S ⊆ X.fitted)
    (hSep : PairwiseAffineSeparated (fun e : {e // e ∈ S} ↦ W.shifts e.1) γ) :
    UniformContractionConstraints S ζ κ M γ
      (retainedUniformContractionAmbient W X S) := by
  classical
  unfold UniformContractionConstraints
  dsimp [retainedUniformContractionAmbient]
  refine ⟨Matrix.mul_nonsing_inv _ W.structural_invertible,
    Matrix.nonsing_inv_mul _ W.structural_invertible,
    Matrix.mul_nonsing_inv _ X.admissible.1,
    Matrix.nonsing_inv_mul _ X.admissible.1, hWnorm.2.1, X.admissible.2.1, ?_⟩
  refine ⟨by unfold normalizationSlack at hslack; linarith,
    le_of_lt X.admissible.2.2, hWcond, hAcond, ⟨hOmega⟩, ⟨X.invariantNoise_psd⟩, ?_⟩
  refine ⟨fun e ↦ ?_, ?_⟩
  · change ContractionPSD (if e ∈ S then W.covariance e else 0)
    constructor
    split
    · exact W.covariance_psd e
    · exact Matrix.PosSemidef.zero
  refine ⟨fun e ↦ ?_, ?_⟩
  · change ContractionPSD (if e ∈ S then X.covariance e else 0)
    constructor
    split
    · exact V.regions_psd V.sampleSize e (X.covariance e) (X.covariance_mem e)
    · exact Matrix.PosSemidef.zero
  refine ⟨?_, ?_, ?_⟩
  · intro e he i
    change 0 ≤ (if e ∈ S then W.shifts e else 0) i
    simp only [if_pos he]
    exact hnonneg e (hSH he) i
  · intro e he i
    change 0 ≤ (if e ∈ S then X.shifts e else 0) i
    simp only [if_pos he]
    exact X.shifts_nonnegative e (hSX he) i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    change (if e ∈ S then W.covariance e else 0) = 0
    simp [he]
  · intro e he
    change (if e ∈ S then X.covariance e else 0) = 0
    simp [he]
  · intro e he
    change (if e ∈ S then W.shifts e else 0) = 0
    simp [he]
  · intro e he
    change (if e ∈ S then X.shifts e else 0) = 0
    simp [he]
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    change W.structural * (if e ∈ S then W.covariance e else 0) *
      W.structural.transpose = W.invariantNoise +
        Matrix.diagonal (if e ∈ S then W.shifts e else 0)
    simpa [he] using transformed_honest W hmodel (hSH he)
  · intro e he
    change A * (if e ∈ S then X.covariance e else 0) * A.transpose =
      X.invariantNoise + Matrix.diagonal (if e ∈ S then X.shifts e else 0)
    simpa [he] using X.transformed_eq e (hSX he)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    change ‖if e ∈ S then W.covariance e else 0‖ ≤ M
    simpa [he] using
      true_covariance_norm_le_scale W.honest W.invariantNoise W.covariance W.shifts
        hscale (hSH he)
  · exact true_noise_norm_le_scale W.honest W.invariantNoise W.covariance W.shifts hscale
  · intro e he
    change ‖Matrix.diagonal (if e ∈ S then W.shifts e else 0)‖ ≤ M
    rw [if_pos he]
    rw [Matrix.l2_opNorm_diagonal]
    exact true_shift_norm_le_scale W.honest W.invariantNoise W.covariance W.shifts
      hscale (hSH he)
  · change ∀ i j : Fin p, i ≠ j → γ ≤
      maxPairAffineDet S (fun e ↦ if e ∈ S then W.shifts e else 0) i j
    exact pairwise_max_of_separated S (fun e ↦ if e ∈ S then W.shifts e else 0) (by
      simpa using hSep)

private lemma selected_covariance_norm_le {p m c : ℕ} (W : BackshiftSystem p m c)
    {V : InferenceWorld p m} {A : RealMatrix p}
    (X : ConfidenceCandidateWitness (c := c) V A) (S : Finset (Environment m))
    {M r : ℝ}
    (hscale : matrixScaleBound W.honest W.invariantNoise W.covariance W.shifts ≤ M)
    (hSH : S ⊆ W.honest)
    (herr : ∀ e ∈ S, ‖X.covariance e - W.covariance e‖ ≤ r)
    (hr : r ≤ 1) {e : Environment m} (he : e ∈ S) :
    ‖X.covariance e‖ ≤ M + 1 := by
  calc
    ‖X.covariance e‖ =
        ‖(X.covariance e - W.covariance e) + W.covariance e‖ := by congr 1 <;> abel
    _ ≤ ‖X.covariance e - W.covariance e‖ + ‖W.covariance e‖ := norm_add_le _ _
    _ ≤ r + M := add_le_add (herr e he)
      (true_covariance_norm_le_scale W.honest W.invariantNoise W.covariance W.shifts
        hscale (hSH he))
    _ ≤ M + 1 := by linarith

private lemma candidate_total_norm_le {p m c : ℕ} (W : BackshiftSystem p m c)
    {V : InferenceWorld p m} {A : RealMatrix p}
    (X : ConfidenceCandidateWitness (c := c) V A) (S : Finset (Environment m))
    {κ M r : ℝ} (hp : 0 < p) (hκ : 1 ≤ κ)
    (hAcond : matrixConditionNumber A ≤ κ)
    (hscale : matrixScaleBound W.honest W.invariantNoise W.covariance W.shifts ≤ M)
    (hSH : S ⊆ W.honest)
    (herr : ∀ e ∈ S, ‖X.covariance e - W.covariance e‖ ≤ r)
    (hr : r ≤ 1) {e : Environment m} (he : e ∈ S) :
    ‖A * X.covariance e * A.transpose‖ ≤ contractionL0 p κ ^ 2 * (M + 1) := by
  have hA := norm_le_of_unitDiagonal_condition A hp hκ X.admissible hAcond
  have hGamma := selected_covariance_norm_le W X S hscale hSH herr hr he
  have hL0 : 0 ≤ contractionL0 p κ := (norm_nonneg A).trans hA
  have hM1 : 0 ≤ M + 1 := (norm_nonneg (X.covariance e)).trans hGamma
  have htrans : ‖A.transpose‖ = ‖A‖ := by
    change ‖star A‖ = ‖A‖
    exact norm_star A
  calc
    ‖A * X.covariance e * A.transpose‖ ≤
        ‖A‖ * ‖X.covariance e‖ * ‖A.transpose‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
        (norm_nonneg _))
    _ ≤ contractionL0 p κ * (M + 1) * contractionL0 p κ := by
      rw [htrans]
      exact mul_le_mul (mul_le_mul hA hGamma (norm_nonneg _) hL0) hA
        (norm_nonneg _) (mul_nonneg hL0 hM1)
    _ = contractionL0 p κ ^ 2 * (M + 1) := by ring

private lemma candidate_noise_norm_le {p m c : ℕ} (W : BackshiftSystem p m c)
    {V : InferenceWorld p m} {A : RealMatrix p}
    (X : ConfidenceCandidateWitness (c := c) V A) (S : Finset (Environment m))
    {κ M r : ℝ} (hp : 0 < p) (hκ : 1 ≤ κ)
    (hAcond : matrixConditionNumber A ≤ κ)
    (hscale : matrixScaleBound W.honest W.invariantNoise W.covariance W.shifts ≤ M)
    (hSH : S ⊆ W.honest) (hSX : S ⊆ X.fitted)
    (herr : ∀ e ∈ S, ‖X.covariance e - W.covariance e‖ ≤ r)
    (hr : r ≤ 1) (e0 : {e // e ∈ S}) :
    ‖X.invariantNoise‖ ≤ contractionL0 p κ ^ 2 * (M + 1) := by
  have hdiag : (Matrix.diagonal (X.shifts e0.1)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i ↦ X.shifts_nonnegative e0.1 (hSX e0.2) i)
  calc
    ‖X.invariantNoise‖ ≤
        ‖X.invariantNoise + Matrix.diagonal (X.shifts e0.1)‖ :=
      opNorm_le_opNorm_add_of_posSemidef X.invariantNoise_psd hdiag
    _ = ‖A * X.covariance e0.1 * A.transpose‖ :=
      congrArg norm (X.transformed_eq e0.1 (hSX e0.2)).symm
    _ ≤ _ := candidate_total_norm_le W X S hp hκ hAcond hscale hSH herr hr e0.2

private lemma candidate_shift_norm_le {p m c : ℕ} (W : BackshiftSystem p m c)
    {V : InferenceWorld p m} {A : RealMatrix p}
    (X : ConfidenceCandidateWitness (c := c) V A) (S : Finset (Environment m))
    {κ M r : ℝ} (hp : 0 < p) (hκ : 1 ≤ κ)
    (hAcond : matrixConditionNumber A ≤ κ)
    (hscale : matrixScaleBound W.honest W.invariantNoise W.covariance W.shifts ≤ M)
    (hSH : S ⊆ W.honest) (hSX : S ⊆ X.fitted)
    (herr : ∀ e ∈ S, ‖X.covariance e - W.covariance e‖ ≤ r)
    (hr : r ≤ 1) {e : Environment m} (he : e ∈ S) :
    ‖X.shifts e‖ ≤ contractionL0 p κ ^ 2 * (M + 1) := by
  rw [← Matrix.l2_opNorm_diagonal]
  have hdiag : (Matrix.diagonal (X.shifts e)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i ↦ X.shifts_nonnegative e (hSX he) i)
  calc
    ‖Matrix.diagonal (X.shifts e)‖ ≤
        ‖Matrix.diagonal (X.shifts e) + X.invariantNoise‖ :=
      opNorm_le_opNorm_add_of_posSemidef hdiag X.invariantNoise_psd
    _ = ‖A * X.covariance e * A.transpose‖ := by
      rw [add_comm]
      exact congrArg norm (X.transformed_eq e (hSX he)).symm
    _ ≤ _ := candidate_total_norm_le W X S hp hκ hAcond hscale hSH herr hr he

/-- Every component of the retained witness lies in the explicit common-radius ambient box. [Under the stated hypotheses](hyp:hp,hκ,hWnorm,hWcond,hAcond,hscale,hSH,hSX,herr,hr0,hr1) [this conclusion](goal) applies. -/
lemma retainedUniformContractionAmbient_mem_box
    {p m c : ℕ} (hp : 2 ≤ p) (W : BackshiftSystem p m c)
    {V : InferenceWorld p m} {A : RealMatrix p}
    (X : ConfidenceCandidateWitness (c := c) V A) (S : Finset (Environment m))
    [Nonempty {e // e ∈ S}] {κ M r : ℝ} (hκ : 1 ≤ κ)
    (hWnorm : BackshiftNormalization W)
    (hWcond : matrixConditionNumber W.structural ≤ κ)
    (hAcond : matrixConditionNumber A ≤ κ)
    (hscale : matrixScaleBound W.honest W.invariantNoise W.covariance W.shifts ≤ M)
    (hSH : S ⊆ W.honest) (hSX : S ⊆ X.fitted)
    (herr : ∀ e ∈ S, ‖X.covariance e - W.covariance e‖ ≤ r)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    retainedUniformContractionAmbient W X S ∈
      uniformContractionBox p m (contractionEmbeddingRadius p κ M) := by
  classical
  let L := contractionL0 p κ
  let Q := L ^ 2 * (M + 1)
  let R := contractionEmbeddingRadius p κ M
  have hp0 : 0 < p := by omega
  have hM0 : 0 ≤ M := by
    have := true_noise_norm_le_scale W.honest W.invariantNoise W.covariance W.shifts hscale
    exact (norm_nonneg W.invariantNoise).trans this
  have hRκ : κ ≤ R := by simp [R, contractionEmbeddingRadius]
  have hRL : L ≤ R := by simp [R, L, contractionEmbeddingRadius]
  have hRM : M ≤ R := le_trans (by linarith : M ≤ M + 1)
    (by simp [R, contractionEmbeddingRadius])
  have hRM1 : M + 1 ≤ R := by simp [R, contractionEmbeddingRadius]
  have hRQ : Q ≤ R := by simp [R, Q, L, contractionEmbeddingRadius]
  have hD := norm_le_of_unitDiagonal_condition W.structural hp0 hκ hWnorm hWcond
  have hDi := norm_inv_le_of_unitDiagonal_condition W.structural hp0 hWnorm hWcond
  have hA := norm_le_of_unitDiagonal_condition A hp0 hκ X.admissible hAcond
  have hAi := norm_inv_le_of_unitDiagonal_condition A hp0 X.admissible hAcond
  have hOmegaR := (true_noise_norm_le_scale W.honest W.invariantNoise
    W.covariance W.shifts hscale).trans hRM
  have hSigmaR : ‖fun e ↦ if e ∈ S then W.covariance e else 0‖ ≤ R := by
    rw [pi_norm_le_iff_of_nonneg (le_trans (by linarith : 0 ≤ M) hRM)]
    intro e
    by_cases he : e ∈ S
    · simpa [he] using (true_covariance_norm_le_scale W.honest W.invariantNoise
        W.covariance W.shifts hscale (hSH he)).trans hRM
    · simp [he, le_trans (by linarith : 0 ≤ M) hRM]
  have hsR : ‖fun e ↦ if e ∈ S then W.shifts e else 0‖ ≤ R := by
    rw [pi_norm_le_iff_of_nonneg (le_trans (by linarith : 0 ≤ M) hRM)]
    intro e
    by_cases he : e ∈ S
    · simpa [he] using (true_shift_norm_le_scale W.honest W.invariantNoise
        W.covariance W.shifts hscale (hSH he)).trans hRM
    · simp [he, le_trans (by linarith : 0 ≤ M) hRM]
  have hGammaR : ‖fun e ↦ if e ∈ S then X.covariance e else 0‖ ≤ R := by
    rw [pi_norm_le_iff_of_nonneg (le_trans (by linarith : 0 ≤ M + 1) hRM1)]
    intro e
    by_cases he : e ∈ S
    · simpa [he] using (selected_covariance_norm_le W X S hscale hSH herr hr1 he).trans hRM1
    · simp [he, le_trans (by linarith : 0 ≤ M + 1) hRM1]
  let e0 : {e // e ∈ S} := Classical.choice inferInstance
  have hPsiR := (candidate_noise_norm_le W X S hp0 hκ hAcond hscale hSH hSX
    herr hr1 e0).trans hRQ
  have htR : ‖fun e ↦ if e ∈ S then X.shifts e else 0‖ ≤ R := by
    rw [pi_norm_le_iff_of_nonneg (le_trans (by positivity : 0 ≤ Q) hRQ)]
    intro e
    by_cases he : e ∈ S
    · simpa [he] using (candidate_shift_norm_le W X S hp0 hκ hAcond hscale hSH
        hSX herr hr1 he).trans hRQ
    · simp [he, le_trans (by positivity : 0 ≤ Q) hRQ]
  unfold uniformContractionBox retainedUniformContractionAmbient
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Metric.mem_closedBall] using hD.trans hRL
  · simpa [Metric.mem_closedBall] using hDi.trans hRκ
  · simpa [Metric.mem_closedBall] using hOmegaR
  · simpa [Metric.mem_closedBall] using hSigmaR
  · simpa [Metric.mem_closedBall] using hsR
  · simpa [Metric.mem_closedBall] using hA.trans hRL
  · simpa [Metric.mem_closedBall] using hAi.trans hRκ
  · simpa [Metric.mem_closedBall] using hGammaR
  · simpa [Metric.mem_closedBall] using hPsiR
  · simpa [Metric.mem_closedBall] using htR

/-- A retained confidence witness embeds in the explicit compact feasible set. [Under the stated hypotheses](hyp:hp,hκ,hWnorm,hnonneg,hmodel,hOmega,hslack,hWcond,hAcond,hscale,hSH,hSX,hSep,herr,hr0,hr1) [this conclusion](goal) applies. -/
lemma retainedUniformContractionAmbient_mem_feasible
    {p m c : ℕ} (hp : 2 ≤ p) (W : BackshiftSystem p m c)
    {V : InferenceWorld p m} {A : RealMatrix p}
    (X : ConfidenceCandidateWitness (c := c) V A) (S : Finset (Environment m))
    [Nonempty {e // e ∈ S}] {ζ κ M γ r : ℝ} (hκ : 1 ≤ κ)
    (hWnorm : BackshiftNormalization W) (hnonneg : NonnegativeShifts W)
    (hmodel : HonestCovarianceModel W) (hOmega : W.invariantNoise.PosSemidef)
    (hslack : ζ ≤ normalizationSlack W.structural)
    (hWcond : matrixConditionNumber W.structural ≤ κ)
    (hAcond : matrixConditionNumber A ≤ κ)
    (hscale : matrixScaleBound W.honest W.invariantNoise W.covariance W.shifts ≤ M)
    (hSH : S ⊆ W.honest) (hSX : S ⊆ X.fitted)
    (hSep : PairwiseAffineSeparated (fun e : {e // e ∈ S} ↦ W.shifts e.1) γ)
    (herr : ∀ e ∈ S, ‖X.covariance e - W.covariance e‖ ≤ r)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    retainedUniformContractionAmbient W X S ∈
      uniformContractionFeasible S ζ κ M γ (contractionEmbeddingRadius p κ M) := by
  exact ⟨retainedUniformContractionAmbient_mem_box hp W X S hκ hWnorm hWcond hAcond
      hscale hSH hSX herr hr0 hr1,
    retainedUniformContractionAmbient_constraints hp W X S hWnorm hnonneg hmodel hOmega
      hslack hWcond hAcond hscale hSH hSX hSep⟩

/-- The paper's worst-retained-subset affine margin supplies the separation hypothesis required
by the embedding theorem. [Under the stated hypotheses](hyp:hp,hκ,hγ,hWnorm,hnonneg,hmodel,hOmega,hslack,hWcond,hAcond,hscale,hAffine,hS,hSX,herr,hr0,hr1) [this conclusion](goal) applies. -/
lemma retainedUniformContractionAmbient_mem_feasible_of_affineSeparation
    {p m c : ℕ} (hp : 2 ≤ p) (W : BackshiftSystem p m c)
    {V : InferenceWorld p m} {A : RealMatrix p}
    (X : ConfidenceCandidateWitness (c := c) V A) (S : Finset (Environment m))
    [Nonempty {e // e ∈ S}] {ζ κ M γ r : ℝ} (hκ : 1 ≤ κ) (hγ : 0 < γ)
    (hWnorm : BackshiftNormalization W) (hnonneg : NonnegativeShifts W)
    (hmodel : HonestCovarianceModel W) (hOmega : W.invariantNoise.PosSemidef)
    (hslack : ζ ≤ normalizationSlack W.structural)
    (hWcond : matrixConditionNumber W.structural ≤ κ)
    (hAcond : matrixConditionNumber A ≤ κ)
    (hscale : matrixScaleBound W.honest W.invariantNoise W.covariance W.shifts ≤ M)
    (hAffine : γ ≤ affineSeparation hp W.honest W.honest_card W.shifts hnonneg)
    (hS : S ∈ W.honest.powersetCard (W.honest.card - c))
    (hSX : S ⊆ X.fitted)
    (herr : ∀ e ∈ S, ‖X.covariance e - W.covariance e‖ ≤ r)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    retainedUniformContractionAmbient W X S ∈
      uniformContractionFeasible S ζ κ M γ (contractionEmbeddingRadius p κ M) := by
  have hSH : S ⊆ W.honest := (Finset.mem_powersetCard.mp hS).1
  have hSep := pairwiseAffineSeparated_restrict_of_le_affineSeparation hp W.honest S
    W.honest_card W.shifts hnonneg hγ hAffine hS
  exact retainedUniformContractionAmbient_mem_feasible hp W X S hκ hWnorm hnonneg hmodel
    hOmega hslack hWcond hAcond hscale hSH hSX hSep herr hr0 hr1

/-- Pointwise retained covariance errors bound the compactification's summed residual. [Under the stated hypotheses](hyp:herr) [this conclusion](goal) applies. -/
lemma uniformContractionResidual_retained_le_card_mul
    {p m c : ℕ} (W : BackshiftSystem p m c)
    {V : InferenceWorld p m} {A : RealMatrix p}
    (X : ConfidenceCandidateWitness (c := c) V A) (S : Finset (Environment m))
    {r : ℝ} (herr : ∀ e ∈ S, ‖X.covariance e - W.covariance e‖ ≤ r) :
    uniformContractionResidual S (retainedUniformContractionAmbient W X S) ≤ S.card * r := by
  classical
  unfold uniformContractionResidual
  simp only [retainedUniformContractionAmbient]
  calc
    ∑ e ∈ S,
        ‖(if e ∈ S then X.covariance e else 0) -
          (if e ∈ S then W.covariance e else 0)‖ ≤ ∑ _e ∈ S, r := by
      exact Finset.sum_le_sum fun e he ↦ by simpa [he] using herr e he
    _ = S.card * r := by simp

end

end CausalSmith.ExactID.RobustBackshiftUniformDistance

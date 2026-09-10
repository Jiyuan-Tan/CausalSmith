import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionCompactness
import Causalean.Discovery.LinearDisentanglement.Quantitative.PairwiseAffine.Stability

/-!
# Confidence-union candidate witnesses

This file extracts a fixed-cardinality transformed BACKSHIFT explanation from membership in the
confidence union and records the elementary honest-region distance bound used by contraction
arguments.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open Set
open scoped Matrix.Norms.L2Operator ENNReal

open Causalean.Discovery.LinearDisentanglement.Quantitative
open Causalean.Discovery.LinearDisentanglement.Quantitative.PairwiseAffine

/-- The pre-weakening form of local pairwise-affine stability.  The reusable theorem deliberately
weakens this coefficient to `16 K L³`; covariance-region errors are themselves amplified by
`L²`, so the paper needs the sharper `4 K L` coefficient before that conversion. [Under the stated hypotheses](hyp:hp,hM,hδ,hL,hscale,hsep,hunit,hexact,hdiag₀,hdiag,hnorm,hε,happrox,hbranch) [this conclusion](goal) applies. -/
lemma opNorm_sub_le_of_pairwise_affine_in_identity_branch_sharp
    {p : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (A : E → SqMatrix p) (s : E → Fin p → ℝ) (B₀ B : SqMatrix p)
    {M δ L ε : ℝ}
    (hp : 0 < p) (hM : 0 < M) (hδ : 0 < δ) (hL : 1 ≤ L)
    (hscale : ShiftScaleBound s M) (hsep : PairwiseAffineSeparated s δ)
    (hunit : IsUnit B₀.det) (hexact : ExactCongruence A s B₀)
    (hdiag₀ : UnitDiagonal B₀) (hdiag : UnitDiagonal B)
    (hnorm : PairMatrixNormBound L B₀ B)
    (hε : 0 ≤ ε) (happrox : OffDiagonalApproximateCongruence A B ε)
    (hbranch : InIdentityBranch M δ L B₀ B) :
    ‖B - B₀‖ ≤ 4 * pairwiseAggregateFactor p M δ L * L * ε := by
  let R := transitionError B₀ B
  let K := pairwiseAggregateFactor p M δ L
  have hK0 : 0 ≤ K := by
    dsimp [K, pairwiseAggregateFactor, pairwiseSolveFactor]
    positivity
  have hu0 : 0 ≤ entryL2 R := by
    dsimp [entryL2]
    positivity
  have hc0 : 0 ≤ pairwiseSolveFactor M δ *
      (2 * M * entryL2 R ^ 2 + 2 * ε) := by
    unfold pairwiseSolveFactor
    positivity
  have hoff : ∀ i j, i ≠ j →
      |R i j| ≤ pairwiseSolveFactor M δ *
        (2 * M * entryL2 R ^ 2 + 2 * ε) := by
    simpa [R] using pairwise_offDiagonal_control A s B₀ B hM.le hδ hε
      hscale hsep hunit hexact happrox
  have hu := entryL2_transitionError_le B₀ B hp (le_trans (by norm_num) hL) hc0
    hunit hdiag₀ hdiag hnorm.1 hoff
  have huK : entryL2 R ≤ K * (2 * M * entryL2 R ^ 2 + 2 * ε) := by
    change entryL2 R ≤ pairwiseSolveFactor M δ *
      (2 * M * entryL2 R ^ 2 + 2 * ε) *
        Real.sqrt ((p : ℝ) * (p - 1 : ℕ) * (1 + L ^ 2)) at hu
    calc
      entryL2 R ≤ pairwiseSolveFactor M δ *
          (2 * M * entryL2 R ^ 2 + 2 * ε) *
            Real.sqrt ((p : ℝ) * (p - 1 : ℕ) * (1 + L ^ 2)) := hu
      _ = K * (2 * M * entryL2 R ^ 2 + 2 * ε) := by
        dsimp [K, pairwiseAggregateFactor]
        ring
  have hbranch' : 2 * K * M * entryL2 R ≤ 1 / 2 := by
    simpa [R, K, InIdentityBranch] using hbranch.2
  have hquad : K * (2 * M * entryL2 R ^ 2) ≤ entryL2 R / 2 := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hbranch')]
  have huLinear : entryL2 R ≤ 4 * K * ε := by
    nlinarith
  rw [sub_eq_transitionError_mul B₀ B hunit]
  calc
    ‖transitionError B₀ B * B₀‖ ≤ ‖transitionError B₀ B‖ * ‖B₀‖ := norm_mul_le _ _
    _ ≤ entryL2 R * L := by
      exact mul_le_mul (by simpa [R] using opNorm_le_entryL2 R) hnorm.1
        (norm_nonneg _) hu0
    _ ≤ (4 * K * ε) * L := by gcongr
    _ = 4 * pairwiseAggregateFactor p M δ L * L * ε := by
      dsimp [K]
      ring

/-- Data witnessing that a matrix in a confidence union exactly fits `m-c` selected covariance
matrices, in congruence-transformed form. -/
structure ConfidenceCandidateWitness {p m c : ℕ} (V : InferenceWorld p m)
    (A : RealMatrix p) where
  covariance : Environment m → RealMatrix p
  covariance_mem : ∀ e, covariance e ∈ V.currentRegions e
  fitted : Finset (Environment m)
  fitted_card : fitted.card = honestCount m c
  admissible : A ∈ admissibleSet p
  invariantNoise : RealMatrix p
  invariantNoise_psd : invariantNoise.PosSemidef
  shifts : Environment m → Fin p → ℝ
  shifts_nonnegative : ∀ e ∈ fitted, ∀ j, 0 ≤ shifts e j
  transformed_eq : ∀ e ∈ fitted,
    A * covariance e * A.transpose =
      invariantNoise + Matrix.diagonal (shifts e)

/-- Membership in the confidence union supplies an exact transformed explanation on exactly
`m-c` environments. [Under the stated hypotheses](hyp:hA) [this conclusion](goal) applies. -/
lemma exists_confidenceCandidateWitness {p m c : ℕ} (V : InferenceWorld p m)
    {A : RealMatrix p} (hA : A ∈ confidenceUnion c V) :
    Nonempty (ConfidenceCandidateWitness (c := c) V A) := by
  classical
  simp only [confidenceUnion, Set.mem_iUnion] at hA
  obtain ⟨Gamma, hGamma, hcompat⟩ := hA
  rw [compatibleSet_transformed_iff] at hcompat
  obtain ⟨hAdm, K, hKcard, Psi, hPsi, t, ht, heq⟩ := hcompat
  obtain ⟨K', hK'sub, hK'card⟩ := Finset.exists_subset_card_eq hKcard
  exact ⟨{
    covariance := Gamma
    covariance_mem := hGamma
    fitted := K'
    fitted_card := hK'card
    admissible := hAdm
    invariantNoise := Psi
    invariantNoise_psd := hPsi
    shifts := t
    shifts_nonnegative := fun e he j => ht e (hK'sub he) j
    transformed_eq := fun e he => heq e (hK'sub he)
  }⟩

/-- The candidate-side condition assumption bounds every confidence-union candidate's condition
number. [Under the stated hypotheses](hyp:hcondition,hA) [this conclusion](goal) applies. -/
lemma matrixConditionNumber_le_of_mem_confidenceUnion {p m c : ℕ}
    (V : InferenceWorld p m) {κ : ℝ}
    (hcondition : CandidateConditionBound (c := c) V.currentRegions κ)
    {A : RealMatrix p} (hA : A ∈ confidenceUnion c V) :
    matrixConditionNumber A ≤ κ := by
  obtain ⟨X⟩ := exists_confidenceCandidateWitness (c := c) V hA
  exact hcondition X.fitted X.fitted_card A X.admissible X.invariantNoise
    X.invariantNoise_psd X.shifts X.shifts_nonnegative X.covariance
    (fun e _ => X.covariance_mem e) X.transformed_eq

/-- Every selected matrix on an honest environment is no farther from the true covariance than
the honest-region radius. [Under the stated hypotheses](hyp:he,hGamma) [this conclusion](goal) applies. -/
lemma edist_le_honestRegionRadius {p m : ℕ} (V : InferenceWorld p m)
    (H : Finset (Environment m)) (Sigma : PSDCovarianceFamily p m)
    {e : Environment m} (he : e ∈ H) {Gamma : RealMatrix p}
    (hGamma : Gamma ∈ V.currentRegions e) :
    edist Gamma (Sigma.1 e) ≤ honestRegionRadius V H Sigma := by
  unfold honestRegionRadius
  exact le_iSup_of_le e <| le_iSup_of_le he <|
    le_iSup_of_le Gamma <| le_iSup_of_le hGamma le_rfl

/-- A lower bound on the paper's worst retained-subset separation gives the reusable pairwise
affine-separation predicate on each retained subset. [Under the stated hypotheses](hyp:hp,hH,hs,hγ,hsep,hS) [this conclusion](goal) applies. -/
lemma pairwiseAffineSeparated_restrict_of_le_affineSeparation
    {p m c : ℕ} (hp : 2 ≤ p) (H S : Finset (Environment m))
    (hH : H.card = honestCount m c) (s : Environment m → Fin p → ℝ)
    (hs : ∀ e ∈ H, ∀ k, 0 ≤ s e k) {γ : ℝ} (hγ : 0 < γ)
    (hsep : γ ≤ affineSeparation hp H hH s hs)
    (hS : S ∈ H.powersetCard (H.card - c)) :
    PairwiseAffineSeparated (fun e : {e // e ∈ S} => s e.1) γ := by
  classical
  have hcard : ¬ H.card - c < 3 := by
    intro hsmall
    unfold affineSeparation at hsep
    rw [if_pos hsmall] at hsep
    linarith
  unfold affineSeparation at hsep
  rw [if_neg hcard] at hsep
  intro i j hij
  have horient : i < j ∨ j < i := lt_or_gt_of_ne hij
  rcases horient with hijlt | hjilt
  · let value := maxAffineMinor S s i j
    have hvalue_mem : value ∈
        {x : ℝ | ∃ kl ∈ offDiagPairs p,
          ∃ T ∈ H.powersetCard (H.card - c), x = maxAffineMinor T s kl.1 kl.2} := by
      exact ⟨(i, j), by simp [offDiagPairs, hijlt], S, hS, rfl⟩
    have hbdd : BddBelow {x : ℝ | ∃ kl ∈ offDiagPairs p,
        ∃ T ∈ H.powersetCard (H.card - c), x = maxAffineMinor T s kl.1 kl.2} := by
      refine ⟨0, ?_⟩
      rintro x ⟨kl, _, T, _, rfl⟩
      exact (Finset.le_fold_max 0).mpr (Or.inl le_rfl)
    have hinf : sInf {x : ℝ | ∃ kl ∈ offDiagPairs p,
        ∃ T ∈ H.powersetCard (H.card - c), x = maxAffineMinor T s kl.1 kl.2} ≤ value :=
      csInf_le hbdd hvalue_mem
    have hγvalue : γ ≤ value := hsep.trans hinf
    change γ ≤ Finset.fold max 0
      (fun efg ↦ |affineMinor s i j efg.1 efg.2.1 efg.2.2|) (indexTriples S) at hγvalue
    rw [Finset.le_fold_max] at hγvalue
    rcases hγvalue with hγzero | ⟨efg, hefg, hminor⟩
    · linarith
    · rcases Finset.mem_filter.mp hefg with ⟨hefgS, _⟩
      rcases Finset.mem_product.mp hefgS with ⟨heS, hfgS⟩
      rcases Finset.mem_product.mp hfgS with ⟨hfS, hgS⟩
      refine ⟨⟨efg.1, heS⟩, ⟨efg.2.1, hfS⟩, ⟨efg.2.2, hgS⟩, ?_⟩
      have heq : pairAffineDet s i j efg.1 efg.2.1 efg.2.2 =
          affineMinor s i j efg.1 efg.2.1 efg.2.2 := by
        unfold pairAffineDet affineMinor
        ring
      change γ ≤ |pairAffineDet s i j efg.1 efg.2.1 efg.2.2|
      rw [heq]
      exact hminor
  · let value := maxAffineMinor S s j i
    have hvalue_mem : value ∈
        {x : ℝ | ∃ kl ∈ offDiagPairs p,
          ∃ T ∈ H.powersetCard (H.card - c), x = maxAffineMinor T s kl.1 kl.2} := by
      exact ⟨(j, i), by simp [offDiagPairs, hjilt], S, hS, rfl⟩
    have hbdd : BddBelow {x : ℝ | ∃ kl ∈ offDiagPairs p,
        ∃ T ∈ H.powersetCard (H.card - c), x = maxAffineMinor T s kl.1 kl.2} := by
      refine ⟨0, ?_⟩
      rintro x ⟨kl, _, T, _, rfl⟩
      exact (Finset.le_fold_max 0).mpr (Or.inl le_rfl)
    have hinf : sInf {x : ℝ | ∃ kl ∈ offDiagPairs p,
        ∃ T ∈ H.powersetCard (H.card - c), x = maxAffineMinor T s kl.1 kl.2} ≤ value :=
      csInf_le hbdd hvalue_mem
    have hγvalue : γ ≤ value := hsep.trans hinf
    change γ ≤ Finset.fold max 0
      (fun efg ↦ |affineMinor s j i efg.1 efg.2.1 efg.2.2|) (indexTriples S) at hγvalue
    rw [Finset.le_fold_max] at hγvalue
    rcases hγvalue with hγzero | ⟨efg, hefg, hminor⟩
    · linarith
    · rcases Finset.mem_filter.mp hefg with ⟨hefgS, _⟩
      rcases Finset.mem_product.mp hefgS with ⟨heS, hfgS⟩
      rcases Finset.mem_product.mp hfgS with ⟨hfS, hgS⟩
      refine ⟨⟨efg.1, heS⟩, ⟨efg.2.1, hfS⟩, ⟨efg.2.2, hgS⟩, ?_⟩
      have heq : pairAffineDet s i j efg.1 efg.2.1 efg.2.2 =
          -(affineMinor s j i efg.1 efg.2.1 efg.2.2) := by
        unfold pairAffineDet affineMinor
        ring
      change γ ≤ |pairAffineDet s i j efg.1 efg.2.1 efg.2.2|
      rw [heq, abs_neg]
      exact hminor

end CausalSmith.ExactID.RobustBackshiftUniformDistance

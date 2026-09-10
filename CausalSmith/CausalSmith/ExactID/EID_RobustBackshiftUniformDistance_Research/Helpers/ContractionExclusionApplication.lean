import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionPointwise
import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionFeasible
import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionLocalInverse
import Causalean.Discovery.LinearDisentanglement.Quantitative.CompactExclusion

/-!
# Uniform exclusion for compactified BACKSHIFT witnesses

This module applies the reusable compact-correspondence exclusion principle to one retained
environment set.  Its zero-residual argument uses weak-boundary overlap uniqueness.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open Set
open scoped Matrix.Norms.L2Operator ENNReal BigOperators
open Causalean.Discovery.LinearDisentanglement.Quantitative
open Causalean.Discovery.LinearDisentanglement.Quantitative.PairwiseAffine

/-- A feasible compactified witness with zero covariance residual has the reference structural
matrix as its candidate. [Under the stated hypotheses](hyp:hp,hc,hScard,hζ,hγ,hz,hzero) [this conclusion](goal) applies. -/
lemma candidate_eq_structural_of_uniformContractionResidual_eq_zero
    {p m c : ℕ} (hp : 2 ≤ p) (hc : c < m)
    (S : Finset (Environment m)) [Nonempty {e // e ∈ S}]
    (hScard : S.card = m - 2 * c) {ζ κ M γ : ℝ} (hζ : 0 < ζ) (hγ : 0 < γ)
    (z : UniformContractionAmbient p m)
    (hz : UniformContractionConstraints S ζ κ M γ z)
    (hzero : uniformContractionResidual S z = 0) :
    z.candidate = z.structural := by
  classical
  have hsep : PairwiseAffineSeparated
      (fun e : {e // e ∈ S} ↦ z.trueShifts e.1) γ :=
    pairwiseAffineSeparated_of_max S z.trueShifts γ hz.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hnoncollinear : ∀ k l : Fin p, k < l →
      ¬ CollinearPairs z.trueShifts k l S := by
    intro k l hkl hcol
    obtain ⟨a, b, d, habd⟩ := hsep k l (ne_of_lt hkl)
    have hdet0 : pairAffineDet (fun e : {e // e ∈ S} ↦ z.trueShifts e.1)
        k l a b d = 0 := by
      have := hcol a.1 a.2 b.1 b.2 d.1 d.2
      unfold pairAffineDet affineMinor at *
      linarith
    rw [hdet0, abs_zero] at habd
    linarith
  let k0 : Fin p := ⟨0, by omega⟩
  let k1 : Fin p := ⟨1, by omega⟩
  have hk01 : k0 < k1 := Fin.mk_lt_mk.mpr (by omega)
  have hSthree : 3 ≤ S.card :=
    noncollinear_card_at_least_three (hnoncollinear k0 k1 hk01)
  have htwoc : 2 * c < m := by omega
  have hunitD : IsUnit z.structural.det :=
    Matrix.isUnit_det_of_right_inverse hz.1
  have hunitB : IsUnit z.candidate.det :=
    Matrix.isUnit_det_of_right_inverse hz.2.2.1
  let first : WeakBackshiftExplanation p m (2 * c) z.trueCovariance := {
    fitted := S
    fitted_card := by simp [honestCount, hScard]
    structural := z.structural
    structural_invertible := hunitD
    structural_unit_diagonal := hz.2.2.2.2.1
    cycle_bound := (hz.2.2.2.2.2.2.1).trans (by linarith)
    invariantNoise := z.invariantNoise
    invariantNoise_psd := hz.2.2.2.2.2.2.2.2.2.2.1.out
    shifts := z.trueShifts
    shifts_nonnegative := hz.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    covariance_eq := fun e he ↦ covariance_eq_of_transformed z.structural
      (z.trueCovariance e) z.invariantNoise (z.trueShifts e) hunitD
        (hz.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he)
  }
  let second : WeakBackshiftExplanation p m (2 * c) z.trueCovariance := {
    fitted := S
    fitted_card := by simp [honestCount, hScard]
    structural := z.candidate
    structural_invertible := hunitB
    structural_unit_diagonal := hz.2.2.2.2.2.1
    cycle_bound := hz.2.2.2.2.2.2.2.1
    invariantNoise := z.candidateNoise
    invariantNoise_psd := hz.2.2.2.2.2.2.2.2.2.2.2.1.out
    shifts := z.candidateShifts
    shifts_nonnegative := hz.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    covariance_eq := fun e he ↦ covariance_eq_of_transformed z.candidate
      (z.trueCovariance e) z.candidateNoise (z.candidateShifts e) hunitB (by
        rw [← selected_eq_true_of_residual_eq_zero S z hzero he]
        exact hz.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he)
  }
  have hstrict : cycleProduct (1 - first.structural) < 1 := by
    dsimp [first]
    exact lt_of_le_of_lt hz.2.2.2.2.2.2.1 (by linarith)
  have hnc : ∀ k l : Fin p, k < l →
      ¬ CollinearPairs first.shifts k l (first.fitted ∩ second.fitted) := by
    simpa [first, second] using hnoncollinear
  exact (weak_boundary_overlap_uniqueness hp htwoc z.trueCovariance
    (fun e ↦ (hz.2.2.2.2.2.2.2.2.2.2.2.2.1 e).out) first second hstrict).2 hnc |>.symm

private lemma retainedSet_nonempty {m n : ℕ} (hn : 0 < n)
    (S : Finset (Environment m))
    (hS : S ∈ (Finset.univ : Finset (Environment m)).powersetCard n) :
    Nonempty {e // e ∈ S} := by
  have hcard : S.card = n := (Finset.mem_powersetCard.mp hS).2
  exact Finset.nonempty_coe_sort.mpr (Finset.card_pos.mp (by omega))

/-- Across all retained subsets of cardinality `m - 2c`, one positive covariance-residual
tolerance places every compactified candidate in the same prescribed local chart. [Under the stated hypotheses](hyp:hp,hc,hcount,hζ,hγ,hρ) [this conclusion](goal) applies. -/
lemma exists_uniformContractionLocalTolerance
    {p m c : ℕ} (hp : 2 ≤ p) (hc : c < m) (hcount : 3 ≤ m - 2 * c)
    {ζ κ M γ R ρ : ℝ} (hζ : 0 < ζ) (hγ : 0 < γ) (hρ : 0 < ρ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (S : Finset (Environment m)) (z : UniformContractionAmbient p m),
        ∀ hS : S ∈ (Finset.univ : Finset (Environment m)).powersetCard (m - 2 * c),
        z ∈ @uniformContractionFeasible p m S
          (retainedSet_nonempty (by omega) S hS) ζ κ M γ R →
        uniformContractionResidual S z ≤ ε₀ →
        InReferenceNeighborhood ρ z.structural z.candidate := by
  classical
  let family := (Finset.univ : Finset (Environment m)).powersetCard (m - 2 * c)
  have hnonempty (S : Finset (Environment m)) (hS : S ∈ family) :
      Nonempty {e // e ∈ S} := by
    exact retainedSet_nonempty (by omega) S hS
  let T := {S // S ∈ family}
  letI : TopologicalSpace T := ⊥
  letI : DiscreteTopology T := ⟨rfl⟩
  let feasible (S : T) : Set (UniformContractionAmbient p m) :=
    @uniformContractionFeasible p m S.1 (hnonempty S.1 S.2) ζ κ M γ R
  let embed (S : T) (z : UniformContractionAmbient p m) :=
    ((S, z), entryL2 (z.candidate - z.structural))
  let K : Set ((T × UniformContractionAmbient p m) × ℝ) :=
    ⋃ S : T, embed S '' feasible S
  have hK : IsCompact K := by
    dsimp [K]
    apply isCompact_iUnion
    intro S
    apply IsCompact.image
    · dsimp [feasible]
      exact @isCompact_uniformContractionFeasible p m S.1 (hnonempty S.1 S.2)
        ζ κ M γ R
    · dsimp [embed]
      exact (continuous_const.prodMk continuous_id).prodMk
        continuous_uniformContractionEntryDistance
  let x₀ : T × UniformContractionAmbient p m → ℝ := fun _ => 0
  let residual : (T × UniformContractionAmbient p m) × ℝ → ℝ :=
    fun q => uniformContractionResidual q.1.1.1 q.1.2
  let radius : T × UniformContractionAmbient p m → ℝ := fun _ => ρ
  have hresidual : Continuous residual := by
    dsimp [residual]
    have hg : Continuous (fun q : T × UniformContractionAmbient p m =>
        uniformContractionResidual q.1.1 q.2) :=
      continuous_prod_of_discrete_left.mpr fun S =>
        continuous_uniformContractionResidual S.1
    exact hg.comp continuous_fst
  obtain ⟨ε₀, hε₀, hlocal⟩ := exists_uniformExclusionTolerance_le K x₀ residual radius
    hK (by fun_prop) hresidual (by fun_prop) (fun _ => hρ)
    (by
      rintro ⟨⟨S, z⟩, x⟩ hx
      exact uniformContractionResidual_nonneg S z)
    (by
      intro q x hqx hzero
      simp only [K, Set.mem_iUnion] at hqx
      obtain ⟨S, z, hz, hembed⟩ := hqx
      rw [← hembed] at hzero
      have hScard : S.1.card = m - 2 * c := (Finset.mem_powersetCard.mp S.2).2
      haveI : Nonempty {e // e ∈ S.1} := hnonempty S.1 S.2
      have hz' : UniformContractionConstraints S.1 ζ κ M γ z := hz.2
      have heq := candidate_eq_structural_of_uniformContractionResidual_eq_zero
        hp hc S.1 hScard hζ hγ z hz' hzero
      calc
        x = entryL2 (z.candidate - z.structural) :=
          (congrArg Prod.snd hembed).symm
        _ = 0 := by simp [heq, entryL2]
        _ = x₀ q := rfl)
  refine ⟨ε₀, hε₀, ?_⟩
  intro S z hS hz hres
  haveI : Nonempty {e // e ∈ S} := hnonempty S hS
  let St : T := ⟨S, hS⟩
  have hzFeasible : z ∈ feasible St := by
    simpa only [feasible] using hz
  have hmem : embed St z ∈ K := by
    exact Set.mem_iUnion_of_mem St ⟨z, hzFeasible, rfl⟩
  have hd := hlocal (St, z) (entryL2 (z.candidate - z.structural)) hmem hres
  dsimp [x₀, radius] at hd
  rw [Real.dist_eq] at hd
  simp only [sub_zero] at hd
  change |entryL2 (z.candidate - z.structural)| < ρ at hd
  exact (le_abs_self _).trans hd.le

/-- Pointwise real operator bounds yield the corresponding extended-valued outer-radius bound. [Under the stated hypotheses](hyp:hA,r,hr,hC,hbound) [this conclusion](goal) applies. -/
lemma opOuterRadius_le_of_forall_opNorm
    {p : ℕ} (A : Set (RealMatrix p)) (hA : A.Nonempty) (D : RealMatrix p)
    (C : ℝ) (r : ℝ≥0∞) (hr : r ≠ ⊤) (hC : 0 ≤ C)
    (hbound : ∀ B ∈ A, ‖B - D‖ ≤ C * r.toReal) :
    opOuterRadius A hA D ≤ ENNReal.ofReal C * r := by
  unfold opOuterRadius
  apply iSup_le
  intro B
  apply iSup_le
  intro hB
  rw [edist_dist, dist_eq_norm]
  calc
    ENNReal.ofReal ‖B - D‖ ≤ ENNReal.ofReal (C * r.toReal) :=
      ENNReal.ofReal_le_ofReal (hbound B hB)
    _ = ENNReal.ofReal C * ENNReal.ofReal r.toReal := ENNReal.ofReal_mul hC
    _ = ENNReal.ofReal C * r := by rw [ENNReal.ofReal_toReal hr]

/-- The paper-specific bridges and the sharp identity-branch estimate give the advertised
contraction coefficient for one retained confidence witness. [Under the stated hypotheses](hyp:hp,hSH,hSX,hSpower,hnorm,hmodel,hnonnegative,hγ,hM,hκ,hr,hsep,hscale,hWcond,hAcond,herr,hsmall,hlocal) [this conclusion](goal) applies. -/
lemma opNorm_candidate_sub_structural_le_contractionC0
    {p m c : ℕ} {V : InferenceWorld p m} {A : RealMatrix p}
    (hp : 2 ≤ p) (W : BackshiftSystem p m c)
    (X : ConfidenceCandidateWitness (c := c) V A)
    (S : Finset (Environment m)) [Nonempty {e // e ∈ S}]
    (hSH : S ⊆ W.honest) (hSX : S ⊆ X.fitted)
    (hSpower : S ∈ W.honest.powersetCard (W.honest.card - c))
    (hnorm : BackshiftNormalization W) (hmodel : HonestCovarianceModel W)
    (hnonnegative : NonnegativeShifts W)
    {γ M κ r : ℝ} (hγ : 0 < γ) (hM : 0 < M) (hκ : 1 ≤ κ) (hr : 0 ≤ r)
    (hsep : γ ≤ affineSeparation W.dimension_at_least_two W.honest
      W.honest_card W.shifts hnonnegative)
    (hscale : matrixScaleBound W.honest W.invariantNoise W.covariance W.shifts ≤ M)
    (hWcond : matrixConditionNumber W.structural ≤ κ)
    (hAcond : matrixConditionNumber A ≤ κ)
    (herr : ∀ e ∈ S, ‖X.covariance e - W.covariance e‖ ≤ r)
    (hsmall : 2 * contractionL0 p κ ^ 2 * r ≤
      pairwiseResidualRadius p M γ (contractionL0 p κ))
    (hlocal : InReferenceNeighborhood
      (pairwiseLocalRadius p M γ (contractionL0 p κ) κ) W.structural A) :
    ‖A - W.structural‖ ≤ contractionC0 p γ M κ * r := by
  let e0 : {e // e ∈ S} := Classical.choice inferInstance
  have hp0 : 0 < p := by omega
  have hL : 1 ≤ contractionL0 p κ := by
    exact one_le_conditionRoot hp0 hκ
  have hshift := centered_shiftScaleBound_of_matrixScaleBound W.honest S hSH
    W.invariantNoise W.covariance W.shifts hnonnegative hscale e0
  have hsepS := pairwiseAffineSeparated_restrict_of_le_affineSeparation hp W.honest S
    W.honest_card W.shifts hnonnegative hγ hsep hSpower
  have hsepCentered := pairwiseAffineSeparated_centered S W.shifts hsepS e0
  have hexact := exactCongruence_centered_of_honestCovarianceModel W hmodel S hSH e0
  have hcond := pairDetConditionEnvelope_of_admissible W.structural A hnorm X.admissible
    hWcond hAcond
  have happrox := offDiagonalApproximateCongruence_centered S W.covariance X.covariance
    A X.invariantNoise X.shifts e0 (zero_le_one.trans hL) hr
    (pairMatrixNormBound_conditionRoot W.structural A hp0 hκ hnorm.2.1
      X.admissible.2.1 hcond).2
    (fun e he => X.transformed_eq e (hSX he)) herr
  have hbranch := inIdentityBranch_of_small_residual
    (fun e : {e // e ∈ S} => W.covariance e.1 - W.covariance e0.1)
    (fun e : {e // e ∈ S} => fun i => W.shifts e.1 i - W.shifts e0.1 i)
    W.structural A hp0 hM hγ hL (lt_of_lt_of_le zero_lt_one hκ)
    hshift hsepCentered W.structural_invertible hexact hnorm.2.1 X.admissible.2.1
    (pairMatrixNormBound_conditionRoot W.structural A hp0 hκ hnorm.2.1
      X.admissible.2.1 hcond)
    (invOpNorm_le_conditionEnvelope W.structural hp0 hnorm.2.1 hcond.1)
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hr) hsmall happrox hlocal
  have hsharp := opNorm_sub_le_of_pairwise_affine_in_identity_branch_sharp
    (fun e : {e // e ∈ S} => W.covariance e.1 - W.covariance e0.1)
    (fun e : {e // e ∈ S} => fun i => W.shifts e.1 i - W.shifts e0.1 i)
    W.structural A hp0 hM hγ hL hshift hsepCentered W.structural_invertible hexact
    hnorm.2.1 X.admissible.2.1
    (pairMatrixNormBound_conditionRoot W.structural A hp0 hκ hnorm.2.1
      X.admissible.2.1 hcond)
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hr) happrox hbranch
  have hK : 0 ≤ contractionK0 p γ M κ := by
    unfold contractionK0
    positivity
  calc
    ‖A - W.structural‖ ≤
        4 * pairwiseAggregateFactor p M γ (contractionL0 p κ) *
          contractionL0 p κ * (2 * contractionL0 p κ ^ 2 * r) := hsharp
    _ = 8 * contractionK0 p γ M κ * contractionL0 p κ ^ 3 * r := by
      unfold contractionK0 pairwiseAggregateFactor pairwiseSolveFactor
      ring
    _ ≤ 16 * contractionK0 p γ M κ * contractionL0 p κ ^ 3 * r := by
      have hprod : 0 ≤ contractionK0 p γ M κ * contractionL0 p κ ^ 3 * r :=
        mul_nonneg (mul_nonneg hK (pow_nonneg (le_trans (by norm_num) hL) _)) hr
      nlinarith
    _ = contractionC0 p γ M κ * r := by rfl

end CausalSmith.ExactID.RobustBackshiftUniformDistance

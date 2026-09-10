import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionTopology
import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionResidual

/-!
# Closed feasible tuples for uniform contraction

This module records the closed compactification of true and candidate BACKSHIFT explanations on
one fixed retained environment set.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open Set
open scoped Matrix.Norms.L2Operator

/-- Wrapper preventing conjunction normalization from splitting PSD constraints. -/
structure ContractionPSD {p : ℕ} (A : RealMatrix p) : Prop where
  out : A.PosSemidef

/-- Closed feasibility constraints on a common retained set.  Coordinates outside the retained
set are set to zero so that no irrelevant, unbounded variables enter the compactification. -/
def UniformContractionConstraints {p m : ℕ} (S : Finset (Environment m))
    [Nonempty {e // e ∈ S}] (ζ κ M γ : ℝ) (z : UniformContractionAmbient p m) : Prop :=
  z.structural * z.structuralInv = 1 ∧
  z.structuralInv * z.structural = 1 ∧
  z.candidate * z.candidateInv = 1 ∧
  z.candidateInv * z.candidate = 1 ∧
  (∀ i, z.structural i i = 1) ∧
  (∀ i, z.candidate i i = 1) ∧
  cycleProduct (1 - z.structural) ≤ 1 - ζ ∧
  cycleProduct (1 - z.candidate) ≤ 1 ∧
  ‖z.structural‖ * ‖z.structuralInv‖ ≤ κ ∧
  ‖z.candidate‖ * ‖z.candidateInv‖ ≤ κ ∧
  ContractionPSD z.invariantNoise ∧
  ContractionPSD z.candidateNoise ∧
  (∀ e, ContractionPSD (z.trueCovariance e)) ∧
  (∀ e, ContractionPSD (z.selectedCovariance e)) ∧
  (∀ e ∈ S, ∀ i, 0 ≤ z.trueShifts e i) ∧
  (∀ e ∈ S, ∀ i, 0 ≤ z.candidateShifts e i) ∧
  (∀ e ∉ S, z.trueCovariance e = 0) ∧
  (∀ e ∉ S, z.selectedCovariance e = 0) ∧
  (∀ e ∉ S, z.trueShifts e = 0) ∧
  (∀ e ∉ S, z.candidateShifts e = 0) ∧
  (∀ e ∈ S, z.structural * z.trueCovariance e * z.structural.transpose =
    z.invariantNoise + Matrix.diagonal (z.trueShifts e)) ∧
  (∀ e ∈ S, z.candidate * z.selectedCovariance e * z.candidate.transpose =
    z.candidateNoise + Matrix.diagonal (z.candidateShifts e)) ∧
  (∀ e ∈ S, ‖z.trueCovariance e‖ ≤ M) ∧
  ‖z.invariantNoise‖ ≤ M ∧
  (∀ e ∈ S, ‖Matrix.diagonal (z.trueShifts e)‖ ≤ M) ∧
  (∀ i j : Fin p, i ≠ j → γ ≤ maxPairAffineDet S z.trueShifts i j)

/-- The feasible portion of a common-radius ambient box. -/
def uniformContractionFeasible {p m : ℕ} (S : Finset (Environment m))
    [Nonempty {e // e ∈ S}] (ζ κ M γ R : ℝ) : Set (UniformContractionAmbient p m) :=
  uniformContractionBox p m R ∩ {z | UniformContractionConstraints S ζ κ M γ z}

private lemma isClosed_unitDiagonal_structural {p m : ℕ} :
    IsClosed {z : UniformContractionAmbient p m | ∀ i, z.structural i i = 1} := by
  simp only [show {z : UniformContractionAmbient p m | ∀ i, z.structural i i = 1} =
      ⋂ i, {z | z.structural i i = 1} by ext z; simp]
  apply isClosed_iInter
  intro i
  exact isClosed_eq (by fun_prop) continuous_const

private lemma isClosed_unitDiagonal_candidate {p m : ℕ} :
    IsClosed {z : UniformContractionAmbient p m | ∀ i, z.candidate i i = 1} := by
  simp only [show {z : UniformContractionAmbient p m | ∀ i, z.candidate i i = 1} =
      ⋂ i, {z | z.candidate i i = 1} by ext z; simp]
  apply isClosed_iInter
  intro i
  exact isClosed_eq (by fun_prop) continuous_const

private lemma isClosed_psd_projection {p m : ℕ}
    (f : UniformContractionAmbient p m → RealMatrix p) (hf : Continuous f) :
    IsClosed {z | ContractionPSD (f z)} := by
  rw [show {z | ContractionPSD (f z)} = {z | (f z).PosSemidef} by
    ext z
    constructor
    · exact fun h => ContractionPSD.out h
    · exact fun h => ⟨h⟩]
  exact (isClosed_posSemidef_realMatrix p).preimage hf

private lemma isClosed_all_psd_projection {p m : ℕ}
    (f : UniformContractionAmbient p m → Environment m → RealMatrix p)
    (hf : ∀ e, Continuous (fun z => f z e)) :
    IsClosed {z | ∀ e, ContractionPSD (f z e)} := by
  simp only [show {z | ∀ e, ContractionPSD (f z e)} =
      ⋂ e, {z | ContractionPSD (f z e)} by ext z; simp]
  apply isClosed_iInter
  intro e
  exact isClosed_psd_projection (fun z => f z e) (hf e)

private lemma isClosed_nonnegative_on {p m : ℕ} (S : Finset (Environment m))
    (f : UniformContractionAmbient p m → ContractionShifts p m)
    (hf : ∀ e i, Continuous (fun z => f z e i)) :
    IsClosed {z | ∀ e ∈ S, ∀ i, 0 ≤ f z e i} := by
  simp only [show {z | ∀ e ∈ S, ∀ i, 0 ≤ f z e i} =
      ⋂ e, ⋂ (_ : e ∈ S), ⋂ i, {z | 0 ≤ f z e i} by ext z; simp]
  apply isClosed_iInter; intro e
  apply isClosed_iInter; intro he
  apply isClosed_iInter; intro i
  exact isClosed_le continuous_const (hf e i)

private lemma isClosed_zero_off_set {p m : ℕ} {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] (S : Finset (Environment m))
    (f : UniformContractionAmbient p m → Environment m → Y)
    (hf : ∀ e, Continuous (fun z => f z e)) [Zero Y] :
    IsClosed {z | ∀ e ∉ S, f z e = 0} := by
  simp only [show {z | ∀ e ∉ S, f z e = 0} =
      ⋂ e, ⋂ (_ : e ∉ S), {z | f z e = 0} by ext z; simp]
  apply isClosed_iInter; intro e
  apply isClosed_iInter; intro he
  exact isClosed_eq (hf e) continuous_const

private lemma isClosed_transformed_equations {p m : ℕ} (S : Finset (Environment m))
    (B : UniformContractionAmbient p m → RealMatrix p)
    (A : UniformContractionAmbient p m → Environment m → RealMatrix p)
    (Ω : UniformContractionAmbient p m → RealMatrix p)
    (s : UniformContractionAmbient p m → ContractionShifts p m)
    (hB : Continuous B) (hA : ∀ e, Continuous (fun z => A z e))
    (hΩ : Continuous Ω) (hs : ∀ e, Continuous (fun z => s z e)) :
    IsClosed {z | ∀ e ∈ S, B z * A z e * (B z).transpose =
      Ω z + Matrix.diagonal (s z e)} := by
  simp only [show {z | ∀ e ∈ S, B z * A z e * (B z).transpose =
      Ω z + Matrix.diagonal (s z e)} = ⋂ e, ⋂ (_ : e ∈ S),
        {z | B z * A z e * (B z).transpose = Ω z + Matrix.diagonal (s z e)} by
          ext z; simp]
  apply isClosed_iInter; intro e
  apply isClosed_iInter; intro he
  apply isClosed_eq
  · exact ((hB.mul (hA e)).mul hB.matrix_transpose)
  · have hse := hs e
    fun_prop

private lemma isClosed_norm_on {p m : ℕ} (S : Finset (Environment m))
    (f : UniformContractionAmbient p m → Environment m → RealMatrix p) (M : ℝ)
    (hf : ∀ e, Continuous (fun z => f z e)) :
    IsClosed {z | ∀ e ∈ S, ‖f z e‖ ≤ M} := by
  simp only [show {z | ∀ e ∈ S, ‖f z e‖ ≤ M} =
      ⋂ e, ⋂ (_ : e ∈ S), {z | ‖f z e‖ ≤ M} by ext z; simp]
  apply isClosed_iInter; intro e
  apply isClosed_iInter; intro he
  exact isClosed_le (hf e).norm continuous_const

/-- The closed feasibility constraints form a closed subset of the ambient product. [This is the asserted conclusion](goal). -/
lemma isClosed_uniformContractionConstraints {p m : ℕ} (S : Finset (Environment m))
    [Nonempty {e // e ∈ S}] (ζ κ M γ : ℝ) :
    IsClosed {z : UniformContractionAmbient p m |
      UniformContractionConstraints S ζ κ M γ z} := by
  unfold UniformContractionConstraints
  simp only [setOf_and]
  repeat' apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_unitDiagonal_structural
  · exact isClosed_unitDiagonal_candidate
  · exact isClosed_le (continuous_cycleProduct.comp (by fun_prop)) (by fun_prop)
  · exact isClosed_le (continuous_cycleProduct.comp (by fun_prop)) continuous_const
  · exact isClosed_le (by fun_prop) continuous_const
  · exact isClosed_le (by fun_prop) continuous_const
  · exact isClosed_psd_projection (fun z => z.invariantNoise) (by fun_prop)
  · exact isClosed_psd_projection (fun z => z.candidateNoise) (by fun_prop)
  · exact isClosed_all_psd_projection (fun z => z.trueCovariance) (fun _ => by fun_prop)
  · exact isClosed_all_psd_projection (fun z => z.selectedCovariance) (fun _ => by fun_prop)
  · exact isClosed_nonnegative_on S (fun z => z.trueShifts) (fun _ _ => by fun_prop)
  · exact isClosed_nonnegative_on S (fun z => z.candidateShifts) (fun _ _ => by fun_prop)
  · exact isClosed_zero_off_set S (fun z => z.trueCovariance) (fun _ => by fun_prop)
  · exact isClosed_zero_off_set S (fun z => z.selectedCovariance) (fun _ => by fun_prop)
  · exact isClosed_zero_off_set S (fun z => z.trueShifts) (fun _ => by fun_prop)
  · exact isClosed_zero_off_set S (fun z => z.candidateShifts) (fun _ => by fun_prop)
  · exact isClosed_transformed_equations S (fun z => z.structural)
      (fun z => z.trueCovariance) (fun z => z.invariantNoise) (fun z => z.trueShifts)
      (by fun_prop) (fun _ => by fun_prop) (by fun_prop) (fun _ => by fun_prop)
  · exact isClosed_transformed_equations S (fun z => z.candidate)
      (fun z => z.selectedCovariance) (fun z => z.candidateNoise) (fun z => z.candidateShifts)
      (by fun_prop) (fun _ => by fun_prop) (by fun_prop) (fun _ => by fun_prop)
  · exact isClosed_norm_on S (fun z => z.trueCovariance) M (fun _ => by fun_prop)
  · exact isClosed_le (by fun_prop) continuous_const
  · exact isClosed_norm_on S (fun z e => Matrix.diagonal (z.trueShifts e)) M
      (fun _ => by fun_prop)
  · exact (isClosed_pairwiseAffineMaxSeparated S γ).preimage
      (show Continuous (fun z : UniformContractionAmbient p m => z.trueShifts) by fun_prop)

/-- The fixed-retained-set feasible compactification is compact. [This is the asserted conclusion](goal). -/
lemma isCompact_uniformContractionFeasible {p m : ℕ} (S : Finset (Environment m))
    [Nonempty {e // e ∈ S}] (ζ κ M γ R : ℝ) :
    IsCompact (uniformContractionFeasible (p := p) S ζ κ M γ R) := by
  exact (isCompact_uniformContractionBox p m R).inter_right
    (isClosed_uniformContractionConstraints S ζ κ M γ)

end CausalSmith.ExactID.RobustBackshiftUniformDistance

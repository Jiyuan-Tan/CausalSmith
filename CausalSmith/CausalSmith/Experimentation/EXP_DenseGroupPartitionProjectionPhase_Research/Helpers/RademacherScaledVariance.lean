import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.RademacherDegreeOne
import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.TExactPameVariance

/-!
# Exact scaled variance for additive Rademacher schedules

This file supplies the rowwise spectral identities used to assemble the two
Rademacher-prior variance limits.
-/

open scoped Topology
open Filter

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.FinitePopulationMoments

-- @node: FiniteDesign.TendstoInProb.congr_eventually
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,X,Y,a,hXY,hY), [the congr eventually result holds](goal). -/
lemma FiniteDesign.TendstoInProb.congr_eventually
    {Ω : ℕ → Type*} [∀ r, Fintype (Ω r)] {D : ∀ r, FiniteDesign (Ω r)}
    {X Y : ∀ r, Ω r → ℝ} {a : ℕ → ℝ}
    (hXY : ∀ᶠ r in atTop, ∀ w, X r w = Y r w)
    (hY : FiniteDesign.TendstoInProb D Y a) :
    FiniteDesign.TendstoInProb D X a := by
  intro ε hε
  apply Tendsto.congr' _ (hY ε hε)
  filter_upwards [hXY] with r hr
  apply (D r).Pr_congr
  intro w
  rw [hr w]

-- @node: probability_ge_tendsto_one_of_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,X,c,t,hX,ht), [the indicated sequence converges to its stated limit](goal). -/
lemma probability_ge_tendsto_one_of_tendstoInProb
    {Ω : ℕ → Type*} [∀ r, Fintype (Ω r)] {D : ∀ r, FiniteDesign (Ω r)}
    {X : ∀ r, Ω r → ℝ} {c t : ℝ}
    (hX : FiniteDesign.TendstoInProb D X (fun _ => c)) (ht : t < c) :
    Tendsto (fun r => (D r).Pr (fun w => t ≤ X r w)) atTop (nhds 1) := by
  have hbad : Tendsto (fun r => (D r).Pr (fun w => X r w < t)) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun r => (D r).Pr_nonneg _) _
      (hX (c - t) (sub_pos.mpr ht))
    exact Eventually.of_forall fun r => by
      apply (D r).Pr_mono
      intro w hw
      have : c - t < c - X r w := by linarith
      exact this.le.trans (by simpa using neg_le_abs (X r w - c))
  apply Tendsto.congr' _ (by simpa using
    (tendsto_const_nhds.sub hbad : Tendsto (fun r => 1 -
      (D r).Pr (fun w => X r w < t)) atTop (nhds (1 - 0))))
  filter_upwards [] with r
  unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
  calc
    1 - ∑ z, (D r).p z * (if X r z < t then 1 else 0) =
        (∑ z, (D r).p z) -
          ∑ z, (D r).p z * (if X r z < t then 1 else 0) := by
      rw [(D r).p_sum]
    _ = ∑ z, ((D r).p z -
          (D r).p z * (if X r z < t then 1 else 0)) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ z, (D r).p z * (if t ≤ X r z then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : t ≤ X r z
      · simp [hz, not_lt_of_ge hz]
      · simp [hz, lt_of_not_ge hz]

-- @node: kneserEigenvalue_one
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMtwo,h2M), [the kneser eigenvalue one result holds](goal). -/
lemma kneserEigenvalue_one {n M : ℕ} (hMtwo : 2 ≤ M) (h2M : 2 * M ≤ n) :
    kneserEigenvalue n M ⟨1, by omega⟩ =
      -(M : ℝ) / ((n : ℝ) - M) := by
  unfold kneserEigenvalue
  simp only [Nat.descFactorial, Nat.sub_zero, pow_one, neg_mul, mul_one]
  rw [Nat.cast_sub (by omega : M ≤ n)]
  ring

-- @node: crossCov_eq_kneserEigenvalue_mul_armVar_of_sampleMean
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMtwo,h2M,hMn,J,hJohnson,hKneser,Y,z,x,htable), [the stated variance result holds](goal). -/
lemma crossCov_eq_kneserEigenvalue_mul_armVar_of_sampleMean
    {n M : ℕ} (hMtwo : 2 ≤ M) (h2M : 2 * M ≤ n) (hMn : M ≤ n)
    (J : JohnsonProjections n M)
    (hJohnson : JohnsonOrthogonalDecomposition n M J)
    (hKneser : KneserAdjacencySpectrum n M) (Y : PotentialOutcome n M)
    (z : Arm) (x : Fin n → ℝ)
    (htable : armTable n M Y z = sampleMean M x) :
    crossCov n M hMn Y z z =
      kneserEigenvalue n M ⟨1, by omega⟩ * armVar n M hMn Y z := by
  let f : Omega n M → ℝ := sampleMean M x
  let fc : Omega n M → ℝ :=
    fun S => f S - (slice n M hMn).E f
  have hproj : J.proj ⟨1, by omega⟩ f = fc := by
    simpa [f, fc] using johnsonProj_sampleMean_eq_centered (by omega) h2M J hJohnson x
  have heigen := (exact_kneser_identity n M hMtwo h2M J Y hJohnson hKneser).1
    ⟨1, by omega⟩ f
  rw [hproj] at heigen
  unfold crossCov armTableCentered armVar
  rw [htable]
  change sliceInner n M hMn fc (kneserOp n M fc) =
    kneserEigenvalue n M ⟨1, by omega⟩ * (slice n M hMn).Var f
  rw [heigen, sliceInner_const_mul_right]
  rw [(slice n M hMn).Var_eq]
  unfold sliceInner fc
  rw [show (fun A => (f A - (slice n M hMn).E f) *
      (f A - (slice n M hMn).E f)) =
      fun A => f A ^ 2 - 2 * (slice n M hMn).E f * f A +
        ((slice n M hMn).E f) ^ 2 by funext A; ring,
    (slice n M hMn).E_add, (slice n M hMn).E_sub,
    (slice n M hMn).E_const_mul, (slice n M hMn).E_const]
  ring

-- @node: crossCovContrast_eq_kneserEigenvalue_mul_degreeOne_of_sampleMean
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMtwo,h2M,hMn,J,hJohnson,hKneser,Y,x,htable), [the stated equality holds](goal). -/
lemma crossCovContrast_eq_kneserEigenvalue_mul_degreeOne_of_sampleMean
    {n M : ℕ} (hMtwo : 2 ≤ M) (h2M : 2 * M ≤ n) (hMn : M ≤ n)
    (J : JohnsonProjections n M)
    (hJohnson : JohnsonOrthogonalDecomposition n M J)
    (hKneser : KneserAdjacencySpectrum n M) (Y : PotentialOutcome n M)
    (x : Fin n → ℝ)
    (htable : (fun S => armTable n M Y true S - armTable n M Y false S) =
      sampleMean M x) :
    crossCovContrast n M hMn Y =
      kneserEigenvalue n M ⟨1, by omega⟩ * degreeOneEnergy n M (by omega) hMn J Y := by
  let f : Omega n M → ℝ := sampleMean M x
  let fc : Omega n M → ℝ :=
    fun S => f S - (slice n M hMn).E f
  have hproj : J.proj ⟨1, by omega⟩ f = fc := by
    simpa [f, fc] using johnsonProj_sampleMean_eq_centered (by omega) h2M J hJohnson x
  have heigen := (exact_kneser_identity n M hMtwo h2M J Y hJohnson hKneser).1
    ⟨1, by omega⟩ f
  rw [hproj] at heigen
  unfold degreeOneEnergy
  rw [htable, hproj]
  unfold crossCovContrast crossCov armTableCentered
  rw [← disjointCov_sub_self n M h2M hMn]
  rw [htable]
  have hcentered : (fun S => armTable n M Y true S - armTable n M Y false S -
      (slice n M hMn).E (sampleMean M x)) = fc := by
    funext S
    rw [show armTable n M Y true S - armTable n M Y false S =
      sampleMean M x S from congrFun htable S]
  rw [hcentered]
  change sliceInner n M hMn fc (kneserOp n M fc) =
    kneserEigenvalue n M ⟨1, by omega⟩ * sliceNorm n M hMn fc ^ 2
  rw [heigen, sliceInner_const_mul_right]
  unfold sliceNorm sliceNormSq
  rw [Real.sq_sqrt (sliceInner_self_nonneg hMn fc)]

-- @node: scaledSigmaSq_eq_of_additive_armTables
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,hMtwo,hMG,hG1two,hG0two,hG1pos,hG1lt,hMn,h2M,J,hJohnson,hKneser,Y,x1,x0,xd,htable1,htable0,htabled), [the stated equality holds](goal). -/
lemma scaledSigmaSq_eq_of_additive_armTables
    {n M G G1 : ℕ} (hMtwo : 2 ≤ M) (hMG : M * G ≤ n)
    (hG1two : 2 ≤ G1) (hG0two : 2 ≤ G - G1)
    (hG1pos : 0 < G1) (hG1lt : G1 < G) (hMn : M ≤ n) (h2M : 2 * M ≤ n)
    (J : JohnsonProjections n M)
    (hJohnson : JohnsonOrthogonalDecomposition n M J)
    (hKneser : KneserAdjacencySpectrum n M) (Y : PotentialOutcome n M)
    (x1 x0 xd : Fin n → ℝ)
    (htable1 : armTable n M Y true = sampleMean M x1)
    (htable0 : armTable n M Y false = sampleMean M x0)
    (htabled : (fun S => armTable n M Y true S - armTable n M Y false S) =
      sampleMean M xd) :
    (G : ℝ) * sigmaSq Y hMG hG1pos hG1lt =
      (1 - kneserEigenvalue n M ⟨1, by omega⟩) *
        indepGroupVar n M G G1 hMn hG1pos hG1lt Y +
      (G : ℝ) * kneserEigenvalue n M ⟨1, by omega⟩ *
        degreeOneEnergy n M (by omega) hMn J Y := by
  have hv := (exact_pame_variance n M G G1 hMG hMtwo hG1two hG0two Y).2.1
  have hc1 := crossCov_eq_kneserEigenvalue_mul_armVar_of_sampleMean
    hMtwo h2M hMn J hJohnson hKneser Y true x1 htable1
  have hc0 := crossCov_eq_kneserEigenvalue_mul_armVar_of_sampleMean
    hMtwo h2M hMn J hJohnson hKneser Y false x0 htable0
  have hct := crossCovContrast_eq_kneserEigenvalue_mul_degreeOne_of_sampleMean
    hMtwo h2M hMn J hJohnson hKneser Y xd htabled
  rw [hv, hc1, hc0, hct]
  unfold indepGroupVar pFrac
  have hGne : (G : ℝ) ≠ 0 := by exact_mod_cast (by omega : G ≠ 0)
  have hG1ne : (G1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : G1 ≠ 0)
  have hG0ne : ((G - G1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : G - G1 ≠ 0)
  rw [Nat.cast_sub hG1lt.le]
  field_simp
  ring

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

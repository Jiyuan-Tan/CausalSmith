import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.Estimator
import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.TExactKneserIdentity
import Causalean.Experimentation.DesignBased.CompoundVariance
import Causalean.Experimentation.TwoStageInterference.VarianceConservative

/-! # Exchangeable moments for the exact two-stage variance calculation -/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.TwoStageInterference

-- @node: finiteDesign_ext_p
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,D',h), [the finite design ext p result holds](goal). -/
lemma finiteDesign_ext_p {Ω : Type*} [Fintype Ω] (D D' : FiniteDesign Ω)
    (h : D.p = D'.p) : D = D' := by
  cases D with
  | mk p hp hs =>
    cases D' with
    | mk p' hp' hs' =>
      simp only at h
      subst p'
      rfl

-- @node: randomPartitionDesign_eq_compoundCore
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,hMG,hG1), [the stated equality holds](goal). -/
lemma randomPartitionDesign_eq_compoundCore (n M G G1 : ℕ)
    (hMG : M * G ≤ n) (hG1 : G1 ≤ G) :
    randomPartitionDesign n M G G1 hMG hG1 =
      compoundCore (uniformPartitionTuple n M G hMG)
        (fun _ => completeRandomization G1 (by simpa using hG1)) := by
  classical
  let D := randomPartitionDesign n M G G1 hMG hG1
  let D' := compoundCore (uniformPartitionTuple n M G hMG)
    (fun _ : PartitionTuple n M G =>
      completeRandomization (V := Fin G) G1 (by simpa using hG1))
  change D = D'
  apply finiteDesign_ext_p D D'
  funext w
  simp only [D, D', randomPartitionDesign, FiniteDesign.map_p, compoundCore]
  calc
    (∑ x, @ite ℝ ((twoStagePairEquiv n M G G1) x = w)
        (Classical.propDecidable _)
        ((prodDesign (twoStageDesigns n M G G1 hMG hG1)).p x) 0) =
        ∑ y, (@ite ℝ (y = w) (Classical.propDecidable _)
          ((prodDesign (twoStageDesigns n M G G1 hMG hG1)).p
            ((twoStagePairEquiv n M G G1).symm y)) 0) := by
          exact Fintype.sum_equiv (twoStagePairEquiv n M G G1) _ _ (fun _ => rfl)
    _ = _ := by
      rw [Finset.sum_eq_single w]
      · simp [twoStageDesigns, prodDesign_p, twoStagePairEquiv]
        exact mul_comm _ _
      · intro y _ hy
        simp [hy]
      · simp

-- @node: finiteDesign_E_compoundCore_tower
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:F), [the stated expectation identity holds](goal). -/
lemma finiteDesign_E_compoundCore_tower {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (D₁ : FiniteDesign Ω₁) (D₂ : Ω₁ → FiniteDesign Ω₂) (F : Ω₁ × Ω₂ → ℝ) :
    (compoundCore D₁ D₂).E F = D₁.E (fun s => (D₂ s).E (fun w => F (s, w))) := by
  unfold FiniteDesign.E compoundCore
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

-- @node: finiteDesign_Var_compoundCore_tower
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:X), [the stated variance result holds](goal). -/
lemma finiteDesign_Var_compoundCore_tower {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (D₁ : FiniteDesign Ω₁) (D₂ : Ω₁ → FiniteDesign Ω₂) (X : Ω₁ × Ω₂ → ℝ) :
    (compoundCore D₁ D₂).Var X =
      D₁.E (fun s => (D₂ s).Var (fun w => X (s, w))) +
        D₁.Var (fun s => (D₂ s).E (fun w => X (s, w))) := by
  rw [FiniteDesign.Var_eq, finiteDesign_E_compoundCore_tower,
    finiteDesign_E_compoundCore_tower]
  have hsq : (fun s => (D₂ s).E (fun w => X (s, w) ^ 2)) =
      fun s => (D₂ s).Var (fun w => X (s, w)) +
        ((D₂ s).E (fun w => X (s, w))) ^ 2 := by
    funext s
    rw [FiniteDesign.Var_eq]
    ring
  rw [hsq, FiniteDesign.E_add, FiniteDesign.Var_eq]
  ring

-- @node: finiteDesign_Var_map
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,f,X), [the stated variance result holds](goal). -/
lemma finiteDesign_Var_map {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (D : FiniteDesign Ω) (f : Ω → Ω') (X : Ω' → ℝ) :
    (D.map f).Var X = D.Var (fun w => X (f w)) := by
  rw [FiniteDesign.Var_eq, FiniteDesign.Var_eq, FiniteDesign.E_map,
    FiniteDesign.E_map]

-- @node: randomPartition_E_partition
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,hMG,hG1,F), [the stated expectation identity holds](goal). -/
lemma randomPartition_E_partition (n M G G1 : ℕ)
    (hMG : M * G ≤ n) (hG1 : G1 ≤ G) (F : PartitionTuple n M G → ℝ) :
    (randomPartitionDesign n M G G1 hMG hG1).E (fun w => F w.1) =
      (uniformPartitionTuple n M G hMG).E F := by
  rw [randomPartitionDesign, FiniteDesign.E_map]
  exact FiniteDesign.E_prod_apply (twoStageDesigns n M G G1 hMG hG1) false F

-- @node: expectedSampleVariance_exchangeable
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,G,hG,X,q,r,hsq,hpair), [the stated variance result holds](goal). -/
lemma expectedSampleVariance_exchangeable {Ω : Type*} [Fintype Ω]
    (D : FiniteDesign Ω) (G : ℕ) (hG : 2 ≤ G) (X : Fin G → Ω → ℝ) (q r : ℝ)
    (hsq : ∀ i, D.E (fun w => X i w ^ 2) = q)
    (hpair : ∀ i j, i ≠ j → D.E (fun w => X i w * X j w) = r) :
    D.E (fun w => S1 (fun i => X i w)) = q - r := by
  have hGpos : 0 < G := by omega
  have hGr : (G : ℝ) ≠ 0 := by exact_mod_cast hGpos.ne'
  have hG1r : (G : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < G := by exact_mod_cast hG
    linarith
  unfold S1 popMeanV
  simp_rw [sum_sub_mean_sq hGpos]
  rw [show (fun w => ((∑ j, X j w ^ 2) - (∑ i, X i w) ^ 2 / (G : ℝ)) /
      ((G : ℝ) - 1)) = fun w =>
        ((∑ j, X j w ^ 2) - (1 / (G : ℝ)) * (∑ i, X i w) ^ 2) *
          (1 / ((G : ℝ) - 1)) by funext w; ring]
  rw [FiniteDesign.E_mul_const, FiniteDesign.E_sub, FiniteDesign.E_sum]
  simp_rw [hsq]
  have hsqsum : D.E (fun w => (∑ i, X i w) ^ 2) =
      ∑ i : Fin G, ∑ j : Fin G, if i = j then q else r := by
    have hpoint : (fun w => (∑ i, X i w) ^ 2) =
        fun w => ∑ i, ∑ j, X i w * X j w := by
      funext w
      rw [sq, Finset.sum_mul_sum]
    rw [hpoint, FiniteDesign.E_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [FiniteDesign.E_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · subst j
      simpa [pow_two] using hsq i
    · simp [hij, hpair i j hij]
  rw [D.E_const_mul (1 / (G : ℝ)) (fun w => (∑ i, X i w) ^ 2), hsqsum]
  have hcollapse : (∑ i : Fin G, ∑ j : Fin G, if i = j then q else r) =
      r * (∑ _i : Fin G, (1 : ℝ)) ^ 2 +
        (q - r) * ∑ _i : Fin G, (1 : ℝ) ^ 2 := by
    simpa only [one_mul] using
      (sum_sum_ite_quadratic Finset.univ (fun _ : Fin G => (1 : ℝ)) q r)
  rw [hcollapse]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    one_pow, mul_one]
  field_simp
  ring

-- @node: partition_expected_sample_variance
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,hMG,hG,hG1,f), [the stated variance result holds](goal). -/
lemma partition_expected_sample_variance (n M G G1 : ℕ)
    (hMG : M * G ≤ n) (hG : 2 ≤ G) (hG1 : G1 ≤ G)
    (f : Omega n M → ℝ) :
    (uniformPartitionTuple n M G hMG).E
        (fun T => S1 (fun g => f (T.1 g))) =
      (slice n M (by
        exact le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)).Var f -
        sliceInner n M (by
          exact le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)
          (fun A => f A - (slice n M (by
            exact le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)).E f)
          (kneserOp n M (fun A => f A - (slice n M (by
            exact le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)).E f)) := by
  let hM : M ≤ n := le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG
  have h2MG : 2 * M ≤ M * G := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left M hG
  have h2M : 2 * M ≤ n := le_trans h2MG hMG
  let D := uniformPartitionTuple n M G hMG
  let q := (slice n M hM).E (fun A => f A ^ 2)
  let r := (orderedDisjointPairDesign n M h2M).E (fun P => f P.1.1 * f P.1.2)
  have hsq (g : Fin G) : D.E (fun T => f (T.1 g) ^ 2) = q := by
    rw [← randomPartition_E_partition n M G G1 hMG hG1]
    exact marginal_uniform_coord n M G G1 hMG (by omega) hG1 g (fun A => f A ^ 2)
  have hpair (g g' : Fin G) (hgg' : g ≠ g') :
      D.E (fun T => f (T.1 g) * f (T.1 g')) = r := by
    rw [← randomPartition_E_partition n M G G1 hMG hG1]
    simpa only [groupAt] using
      (marginal_uniform_ordered_disjoint_pair n M G G1 hMG hG1 h2M g g' hgg'
        (fun P => f P.1.1 * f P.1.2))
  rw [expectedSampleVariance_exchangeable D G hG (fun g T => f (T.1 g)) q r hsq hpair]
  let mu := (slice n M hM).E f
  have hcenterPair :
      (orderedDisjointPairDesign n M h2M).E
          (fun P => (f P.1.1 - mu) * (f P.1.2 - mu)) = r - mu ^ 2 := by
    have hpoint : (fun P : OrderedDisjointPair n M =>
        (f P.1.1 - mu) * (f P.1.2 - mu)) =
        (fun P => f P.1.1 * f P.1.2 - mu * f P.1.1 - mu * f P.1.2 + mu ^ 2) := by
      funext P
      ring
    rw [hpoint]
    rw [FiniteDesign.E_add, FiniteDesign.E_sub, FiniteDesign.E_sub,
      FiniteDesign.E_const_mul, FiniteDesign.E_const_mul,
      orderedDisjointPair_first_E_eq_slice h2M,
      orderedDisjointPair_second_E_eq_slice h2M, FiniteDesign.E_const]
    change r - mu * mu - mu * mu + mu ^ 2 = r - mu ^ 2
    ring
  rw [show sliceInner n M hM (fun A => f A - (slice n M hM).E f)
      (kneserOp n M (fun A => f A - (slice n M hM).E f)) =
      (orderedDisjointPairDesign n M h2M).E
        (fun P => (f P.1.1 - mu) * (f P.1.2 - mu)) by
          symm
          simpa only [mu] using
            (orderedDisjointPair_E_eq n M h2M
              (fun A => f A - (slice n M hM).E f)
              (fun A => f A - (slice n M hM).E f))]
  rw [hcenterPair, FiniteDesign.Var_eq]
  change q - r = (q - mu ^ 2) - (r - mu ^ 2)
  ring

-- @node: pameHat_eq_diffInMeans
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,Y,hG1pos,hG1lt,T,S), [the stated equality holds](goal). -/
lemma pameHat_eq_diffInMeans {n M G G1 : ℕ} (Y : PotentialOutcome n M)
    (hG1pos : 0 < G1) (hG1lt : G1 < G)
    (T : PartitionTuple n M G) (S : TreatmentSpace G G1) :
    pameHat Y hG1pos hG1lt (T, S) =
      diffInMeans G1 (fun g => armTable n M Y true (T.1 g))
        (fun g => armTable n M Y false (T.1 g)) S := by
  classical
  simp [pameHat, diffInMeans, treatedMean, controlMean, Finset.sum_filter]

-- @node: cr2Var_eq_varHat
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,Y,hG1,hG0,T,S), [the stated variance result holds](goal). -/
lemma cr2Var_eq_varHat {n M G G1 : ℕ} (Y : PotentialOutcome n M)
    (hG1 : 2 ≤ G1) (hG0 : 2 ≤ G - G1)
    (T : PartitionTuple n M G) (S : TreatmentSpace G G1) :
    cr2Var Y hG1 hG0 (T, S) =
      varHat G1 (fun g => armTable n M Y true (T.1 g))
        (fun g => armTable n M Y false (T.1 g))
        (crdToBoolOn G1 S) := by
  classical
  let a : Fin G → ℝ := fun g => armTable n M Y true (T.1 g)
  let b : Fin G → ℝ := fun g => armTable n M Y false (T.1 g)
  let z := crdToBoolOn G1 S
  have hsum (f : Fin G → ℝ) :
      (∑ x ∈ S.1, f x) = ∑ x, if x ∈ S.1 then f x else 0 := by
    rw [← Finset.sum_filter]
    simp
  have hObsT : armObsMean Y (T, S) true = obsMeanTreated G1 a z := by
    simp [armObsMean, obsMeanTreated, realizedArmSet, armCount, obsGroupMean,
      a, z, Causalean.Experimentation.TwoStageInterference.T,
      crdToBoolOn, FiniteDesign.ind]
    congr 1
    apply Finset.sum_congr rfl
    intro g hg
    simp [hg]
  have hObsC : armObsMean Y (T, S) false = obsMeanControl G1 b z := by
    simp [armObsMean, obsMeanControl, realizedArmSet, armCount, obsGroupMean,
      b, z, Causalean.Experimentation.TwoStageInterference.T,
      crdToBoolOn, FiniteDesign.ind, Nat.cast_sub (by omega : G1 ≤ G)]
    congr 1
    rw [hsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro g _
    by_cases hg : g ∈ S.1 <;> simp [hg]
  have hVarT : armSampleVar Y (T, S) true (by simpa [armCount] using hG1) =
      ShatTreated G1 a z := by
    simp [armSampleVar, ShatTreated, realizedArmSet, armCount, hObsT,
      obsGroupMean, a, z, Causalean.Experimentation.TwoStageInterference.T,
      crdToBoolOn, FiniteDesign.ind,
      Nat.cast_sub (by omega : 1 ≤ G1)]
    congr 1
    apply Finset.sum_congr rfl
    intro g hg
    simp [hg]
  have hVarC : armSampleVar Y (T, S) false (by simpa [armCount] using hG0) =
      ShatControl G1 b z := by
    simp [armSampleVar, ShatControl, realizedArmSet, armCount, hObsC,
      obsGroupMean, b, z, Causalean.Experimentation.TwoStageInterference.T,
      crdToBoolOn, FiniteDesign.ind,
      Nat.cast_sub (by omega : 1 ≤ G - G1), Nat.cast_sub (by omega : G1 ≤ G)]
    congr 1
    rw [hsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro g _
    by_cases hg : g ∈ S.1 <;> simp [hg]
  unfold cr2Var varHat
  rw [hVarT, hVarC, Nat.cast_sub (by omega : G1 ≤ G)]

-- @node: conditional_E_pameHat
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,Y,hG1pos,hG1lt,T), [the stated expectation identity holds](goal). -/
lemma conditional_E_pameHat {n M G G1 : ℕ} (Y : PotentialOutcome n M)
    (hG1pos : 0 < G1) (hG1lt : G1 < G) (T : PartitionTuple n M G) :
    (completeRandomization (V := Fin G) G1 (by simpa using hG1lt.le)).E
        (fun S => pameHat Y hG1pos hG1lt (T, S)) =
      (∑ g, (armTable n M Y true (T.1 g) -
        armTable n M Y false (T.1 g))) / (G : ℝ) := by
  rw [(completeRandomization (V := Fin G) G1 (by simpa using hG1lt.le)).E_congr
    (fun S => pameHat_eq_diffInMeans Y hG1pos hG1lt T S)]
  rw [E_diffInMeans_eq_sate G1 hG1pos (by simpa using hG1lt)]
  simp [sateEstimand]

-- @node: conditional_Var_pameHat
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,Y,hG1pos,hG1lt,T), [the stated variance result holds](goal). -/
lemma conditional_Var_pameHat {n M G G1 : ℕ} (Y : PotentialOutcome n M)
    (hG1pos : 0 < G1) (hG1lt : G1 < G) (T : PartitionTuple n M G) :
    (completeRandomization (V := Fin G) G1 (by simpa using hG1lt.le)).Var
        (fun S => pameHat Y hG1pos hG1lt (T, S)) =
      S1 (fun g => armTable n M Y true (T.1 g)) / (G1 : ℝ) +
      S0 (fun g => armTable n M Y false (T.1 g)) / ((G : ℝ) - G1) -
      Stau (fun g => armTable n M Y true (T.1 g))
        (fun g => armTable n M Y false (T.1 g)) / (G : ℝ) := by
  let a := fun g : Fin G => armTable n M Y true (T.1 g)
  let b := fun g : Fin G => armTable n M Y false (T.1 g)
  have hp : (fun S => pameHat Y hG1pos hG1lt (T, S)) = diffInMeans G1 a b := by
    funext S
    exact pameHat_eq_diffInMeans Y hG1pos hG1lt T S
  rw [hp]
  have hneg : diffInMeans G1 a b = fun S => -tauHat G1 a b (crdToBoolOn G1 S) := by
    funext S
    have ht : (∑ x, a x * Causalean.Experimentation.TwoStageInterference.T x
        (crdToBoolOn G1 S)) = ∑ x, if x ∈ S.1 then a x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ S.1 <;> simp [Causalean.Experimentation.TwoStageInterference.T,
        crdToBoolOn, FiniteDesign.ind, hx]
    have hc : (∑ x, b x * (1 - Causalean.Experimentation.TwoStageInterference.T x
        (crdToBoolOn G1 S))) = ∑ x, if x ∈ S.1 then 0 else b x := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ S.1 <;> simp [Causalean.Experimentation.TwoStageInterference.T,
        crdToBoolOn, FiniteDesign.ind, hx]
    rw [diffInMeans, treatedMean, controlMean, tauHat, ht, hc]
    rw [Fintype.card_fin, Nat.cast_sub hG1lt.le]
    ring
  rw [hneg]
  have hminus : (fun S => -tauHat G1 a b (crdToBoolOn G1 S)) =
      fun S => (-1 : ℝ) * tauHat G1 a b (crdToBoolOn G1 S) := by
    funext S
    ring
  rw [hminus, FiniteDesign.Var_const_mul]
  norm_num
  rw [← finiteDesign_Var_map
    (completeRandomization (V := Fin G) G1 (by simpa using hG1lt.le))
    (crdToBoolOn G1) (tauHat G1 a b)]
  change (crd G1 hG1lt.le).Var (tauHat G1 a b) = _
  exact Var_tauHat_CRD G1 a b hG1pos hG1lt

-- @node: conditional_E_cr2Var
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,Y,hG1,hG0,T), [the stated variance result holds](goal). -/
lemma conditional_E_cr2Var {n M G G1 : ℕ} (Y : PotentialOutcome n M)
    (hG1 : 2 ≤ G1) (hG0 : 2 ≤ G - G1) (T : PartitionTuple n M G) :
    (completeRandomization (V := Fin G) G1
        (by simpa using (by omega : G1 ≤ G))).E
      (fun S => cr2Var Y hG1 hG0 (T, S)) =
      S1 (fun g => armTable n M Y true (T.1 g)) / (G1 : ℝ) +
      S0 (fun g => armTable n M Y false (T.1 g)) / ((G - G1 : ℕ) : ℝ) := by
  let a := fun g : Fin G => armTable n M Y true (T.1 g)
  let b := fun g : Fin G => armTable n M Y false (T.1 g)
  rw [(completeRandomization (V := Fin G) G1
    (by simpa using (by omega : G1 ≤ G))).E_congr
      (fun S => cr2Var_eq_varHat Y hG1 hG0 T S)]
  rw [show (completeRandomization (V := Fin G) G1
      (by simpa using (by omega : G1 ≤ G))).E
      (fun S => varHat G1 a b (crdToBoolOn G1 S)) =
      (crd G1 (by omega : G1 ≤ G)).E (varHat G1 a b) by
        rw [crd, crdOn, FiniteDesign.E_map]]
  unfold varHat
  rw [FiniteDesign.E_add]
  rw [show (fun w => ShatTreated G1 a w / (G1 : ℝ)) =
      fun w => (G1 : ℝ)⁻¹ * ShatTreated G1 a w by funext w; ring,
    show (fun w => ShatControl G1 b w / ((G : ℝ) - G1)) =
      fun w => ((G : ℝ) - G1)⁻¹ * ShatControl G1 b w by funext w; ring,
    FiniteDesign.E_const_mul, FiniteDesign.E_const_mul]
  rw [E_ShatTreated G1 a (crd G1 (by omega)) hG1 (by omega)
      (fun j => crd_mean G1 (by omega) j)
      (fun j k h => crd_pair G1 (by omega) j k h)
      (fun w hw => crd_supp G1 (by omega) w hw)]
  rw [E_ShatControl G1 b (crd G1 (by omega)) hG1 (by omega)
      (fun j => crd_mean G1 (by omega) j)
      (fun j k h => crd_pair G1 (by omega) j k h)
      (fun w hw => crd_supp G1 (by omega) w hw)]
  rw [Nat.cast_sub (by omega : G1 ≤ G)]
  ring

-- @node: partition_E_mean
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,hMG,hG,hG1,f), [the stated expectation identity holds](goal). -/
lemma partition_E_mean (n M G G1 : ℕ) (hMG : M * G ≤ n) (hG : 0 < G)
    (hG1 : G1 ≤ G) (f : Omega n M → ℝ) :
    (uniformPartitionTuple n M G hMG).E (fun T => (∑ g, f (T.1 g)) / (G : ℝ)) =
      (slice n M (le_trans (Nat.le_mul_of_pos_right M hG) hMG)).E f := by
  rw [← randomPartition_E_partition n M G G1 hMG hG1]
  change (randomPartitionDesign n M G G1 hMG hG1).E
    (fun w => (∑ g, f (groupAt n M G G1 w g)) / (G : ℝ)) = _
  calc
    _ = (randomPartitionDesign n M G G1 hMG hG1).E
        (fun w => (G : ℝ)⁻¹ * ∑ g, f (groupAt n M G G1 w g)) := by
          apply (randomPartitionDesign n M G G1 hMG hG1).E_congr
          intro w
          ring
    _ = _ := by
      rw [FiniteDesign.E_const_mul, FiniteDesign.E_sum]
      simp_rw [marginal_uniform_coord n M G G1 hMG hG hG1]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hGr : (G : ℝ) ≠ 0 := by exact_mod_cast hG.ne'
      field_simp

-- @node: Stau_eq_S1_sub
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:G,a,b), [the stated equality holds](goal). -/
lemma Stau_eq_S1_sub {G : ℕ} (a b : Fin G → ℝ) :
    Stau a b = S1 (fun g => a g - b g) := by
  unfold Stau S1 popMeanV
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [Finset.sum_sub_distrib]
  ring

-- @node: orderedDisjointPair_E_mul_comm
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,h2M,f,g), [the stated expectation identity holds](goal). -/
lemma orderedDisjointPair_E_mul_comm {n M : ℕ} (h2M : 2 * M ≤ n)
    (f g : Omega n M → ℝ) :
    (orderedDisjointPairDesign n M h2M).E (fun P => f P.1.1 * g P.1.2) =
      (orderedDisjointPairDesign n M h2M).E (fun P => g P.1.1 * f P.1.2) := by
  classical
  unfold FiniteDesign.E orderedDisjointPairDesign uniformFiniteDesign
  calc
    (∑ x : OrderedDisjointPair n M, (1 / (Fintype.card (OrderedDisjointPair n M) : ℝ)) *
        (f x.1.1 * g x.1.2)) =
      ∑ x : OrderedDisjointPair n M, (1 / (Fintype.card (OrderedDisjointPair n M) : ℝ)) *
        (f (orderedDisjointPairSwap x).1.1 * g (orderedDisjointPairSwap x).1.2) := by
          exact Fintype.sum_equiv orderedDisjointPairSwap _ _ (fun _ => rfl)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      change _ * (f x.1.2 * g x.1.1) = _
      ring

-- @node: disjointCov_sub_self
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,h2M,hM,f,g), [the disjoint cov sub self result holds](goal). -/
lemma disjointCov_sub_self (n M : ℕ) (h2M : 2 * M ≤ n) (hM : M ≤ n)
    (f g : Omega n M → ℝ) :
    sliceInner n M hM
        (fun A => (f A - g A) - (slice n M hM).E (fun A => f A - g A))
        (kneserOp n M
          (fun A => (f A - g A) - (slice n M hM).E (fun A => f A - g A))) =
      sliceInner n M hM (fun A => f A - (slice n M hM).E f)
          (kneserOp n M (fun A => f A - (slice n M hM).E f)) +
      sliceInner n M hM (fun A => g A - (slice n M hM).E g)
          (kneserOp n M (fun A => g A - (slice n M hM).E g)) -
      2 * sliceInner n M hM (fun A => f A - (slice n M hM).E f)
          (kneserOp n M (fun A => g A - (slice n M hM).E g)) := by
  rw [FiniteDesign.E_sub]
  have hc : (fun A => (f A - g A) - ((slice n M hM).E f - (slice n M hM).E g)) =
      fun A => (f A - (slice n M hM).E f) - (g A - (slice n M hM).E g) := by
    funext A
    ring
  rw [hc]
  rw [← orderedDisjointPair_E_eq n M h2M,
    ← orderedDisjointPair_E_eq n M h2M,
    ← orderedDisjointPair_E_eq n M h2M,
    ← orderedDisjointPair_E_eq n M h2M]
  have hp : (fun P : OrderedDisjointPair n M =>
      ((f P.1.1 - (slice n M hM).E f) - (g P.1.1 - (slice n M hM).E g)) *
       ((f P.1.2 - (slice n M hM).E f) - (g P.1.2 - (slice n M hM).E g))) =
      fun P =>
        (f P.1.1 - (slice n M hM).E f) * (f P.1.2 - (slice n M hM).E f) -
        (f P.1.1 - (slice n M hM).E f) * (g P.1.2 - (slice n M hM).E g) -
        (g P.1.1 - (slice n M hM).E g) * (f P.1.2 - (slice n M hM).E f) +
        (g P.1.1 - (slice n M hM).E g) * (g P.1.2 - (slice n M hM).E g) := by
    funext P
    ring
  rw [hp,
    FiniteDesign.E_add, FiniteDesign.E_sub, FiniteDesign.E_sub]
  have hsym : (orderedDisjointPairDesign n M h2M).E
      (fun P => (g P.1.1 - (slice n M hM).E g) *
        (f P.1.2 - (slice n M hM).E f)) =
      (orderedDisjointPairDesign n M h2M).E
      (fun P => (f P.1.1 - (slice n M hM).E f) *
        (g P.1.2 - (slice n M hM).E g)) :=
    orderedDisjointPair_E_mul_comm h2M
      (fun A => g A - (slice n M hM).E g)
      (fun A => f A - (slice n M hM).E f)
  rw [hsym]
  ring

-- @node: varianceMean_exchangeable
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,G,hG,X,v,c,hvar,hcov), [the stated variance result holds](goal). -/
lemma varianceMean_exchangeable {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω)
    (G : ℕ) (hG : 0 < G) (X : Fin G → Ω → ℝ) (v c : ℝ)
    (hvar : ∀ i, D.Var (X i) = v)
    (hcov : ∀ i j, i ≠ j → D.Cov (X i) (X j) = c) :
    D.Var (fun w => (∑ i, X i w) / (G : ℝ)) =
      (v + ((G : ℝ) - 1) * c) / (G : ℝ) := by
  have hGr : (G : ℝ) ≠ 0 := by exact_mod_cast hG.ne'
  have hform : (fun w => (∑ i, X i w) / (G : ℝ)) =
      fun w => ∑ i, (1 / (G : ℝ)) * X i w := by
    funext w
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [D.Var_congr (congrFun hform), FiniteDesign.Var_linear_comb]
  have hterms : (∑ i : Fin G, ∑ j : Fin G,
      (1 / (G : ℝ)) * (1 / (G : ℝ)) * D.Cov (X i) (X j)) =
      ∑ i : Fin G, ∑ j : Fin G,
        (1 / (G : ℝ)) * (1 / (G : ℝ)) * if i = j then v else c := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · subst j
      rw [FiniteDesign.Cov_self, hvar i]
      simp
    · simp [hij, hcov i j hij]
  rw [hterms, sum_sum_ite_quadratic Finset.univ
    (fun _ : Fin G => 1 / (G : ℝ)) v c]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

-- @node: partition_mean_variance
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,hMG,hG,hG1,f), [the stated variance result holds](goal). -/
lemma partition_mean_variance (n M G G1 : ℕ) (hMG : M * G ≤ n)
    (hG : 2 ≤ G) (hG1 : G1 ≤ G) (f : Omega n M → ℝ) :
    (uniformPartitionTuple n M G hMG).Var
        (fun T => (∑ g, f (T.1 g)) / (G : ℝ)) =
      ((slice n M (by
        exact le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)).Var f +
        ((G : ℝ) - 1) *
          sliceInner n M (by
            exact le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)
            (fun A => f A - (slice n M (by
              exact le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)).E f)
            (kneserOp n M (fun A => f A - (slice n M (by
              exact le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)).E f))) /
        (G : ℝ) := by
  let hM : M ≤ n := le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG
  have h2MG : 2 * M ≤ M * G := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left M hG
  have h2M : 2 * M ≤ n := le_trans h2MG hMG
  let D := uniformPartitionTuple n M G hMG
  let v := (slice n M hM).Var f
  let c := sliceInner n M hM (fun A => f A - (slice n M hM).E f)
    (kneserOp n M (fun A => f A - (slice n M hM).E f))
  have hvar (g : Fin G) : D.Var (fun T => f (T.1 g)) = v := by
    change D.Var (fun T => f (T.1 g)) = (slice n M hM).Var f
    rw [FiniteDesign.Var_eq, FiniteDesign.Var_eq]
    rw [← randomPartition_E_partition n M G G1 hMG hG1]
    have hsq := marginal_uniform_coord n M G G1 hMG (by omega) hG1 g
      (fun A => f A ^ 2)
    rw [show (randomPartitionDesign n M G G1 hMG hG1).E
        (fun w => f (w.1.1 g) ^ 2) = (slice n M hM).E (fun A => f A ^ 2) by
      simpa only [groupAt] using hsq]
    rw [← randomPartition_E_partition n M G G1 hMG hG1]
    have hm := marginal_uniform_coord n M G G1 hMG (by omega) hG1 g f
    rw [show (randomPartitionDesign n M G G1 hMG hG1).E
        (fun w => f (w.1.1 g)) = (slice n M hM).E f by
      simpa only [groupAt] using hm]
  have hcov (g g' : Fin G) (hgg' : g ≠ g') :
      D.Cov (fun T => f (T.1 g)) (fun T => f (T.1 g')) = c := by
    rw [FiniteDesign.Cov_eq]
    rw [← randomPartition_E_partition n M G G1 hMG hG1]
    have hp := marginal_uniform_ordered_disjoint_pair n M G G1 hMG hG1 h2M
      g g' hgg' (fun P => f P.1.1 * f P.1.2)
    rw [show (randomPartitionDesign n M G G1 hMG hG1).E
        (fun w => f (w.1.1 g) * f (w.1.1 g')) =
        (orderedDisjointPairDesign n M h2M).E
          (fun P => f P.1.1 * f P.1.2) by simpa only [groupAt] using hp]
    rw [← randomPartition_E_partition n M G G1 hMG hG1]
    have hmg := marginal_uniform_coord n M G G1 hMG (by omega) hG1 g f
    rw [show (randomPartitionDesign n M G G1 hMG hG1).E
        (fun w => f (w.1.1 g)) = (slice n M hM).E f by
      simpa only [groupAt] using hmg]
    rw [← randomPartition_E_partition n M G G1 hMG hG1]
    have hmg' := marginal_uniform_coord n M G G1 hMG (by omega) hG1 g' f
    rw [show (randomPartitionDesign n M G G1 hMG hG1).E
        (fun w => f (w.1.1 g')) = (slice n M hM).E f by
      simpa only [groupAt] using hmg']
    let mu := (slice n M hM).E f
    have hcenter : (orderedDisjointPairDesign n M h2M).E
        (fun P => (f P.1.1 - mu) * (f P.1.2 - mu)) =
        (orderedDisjointPairDesign n M h2M).E
          (fun P => f P.1.1 * f P.1.2) - mu ^ 2 := by
      have hp : (fun P : OrderedDisjointPair n M =>
          (f P.1.1 - mu) * (f P.1.2 - mu)) =
          fun P => f P.1.1 * f P.1.2 - mu * f P.1.1 - mu * f P.1.2 + mu ^ 2 := by
        funext P
        ring
      rw [hp, FiniteDesign.E_add, FiniteDesign.E_sub, FiniteDesign.E_sub,
        FiniteDesign.E_const_mul, FiniteDesign.E_const_mul,
        orderedDisjointPair_first_E_eq_slice h2M,
        orderedDisjointPair_second_E_eq_slice h2M, FiniteDesign.E_const]
      change _ - mu * mu - mu * mu + mu ^ 2 = _ - mu ^ 2
      ring
    have hc : (orderedDisjointPairDesign n M h2M).E
        (fun P => (f P.1.1 - mu) * (f P.1.2 - mu)) = c := by
      change _ = sliceInner n M hM (fun A => f A - (slice n M hM).E f)
        (kneserOp n M (fun A => f A - (slice n M hM).E f))
      simpa only [mu] using
        (orderedDisjointPair_E_eq n M h2M
          (fun A => f A - (slice n M hM).E f)
          (fun A => f A - (slice n M hM).E f))
    rw [hcenter] at hc
    simpa [mu, pow_two] using hc
  exact varianceMean_exchangeable D G (by omega) (fun g T => f (T.1 g)) v c hvar hcov

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

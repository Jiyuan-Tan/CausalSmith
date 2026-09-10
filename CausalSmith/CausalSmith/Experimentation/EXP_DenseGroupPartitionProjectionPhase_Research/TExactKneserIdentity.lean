import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.Kneser

/-!
# Exact Kneser spectral identity

The paper's exact identity is stated conditionally on the two cited Johnson/Kneser
logical gates.  Stage 3 supplies the Lean proof of the conditional result.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased

-- @node: sliceInner_sum_left
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hM,s,f,g), [the slice inner sum left result holds](goal). -/
lemma sliceInner_sum_left {n M : ℕ} (hM : M ≤ n) {ι : Type*}
    (s : Finset ι) (f : ι → Omega n M → ℝ) (g : Omega n M → ℝ) :
    sliceInner n M hM (fun A => ∑ i ∈ s, f i A) g =
      ∑ i ∈ s, sliceInner n M hM (f i) g := by
  unfold sliceInner
  rw [← (slice n M hM).E_sum s (fun i A => f i A * g A)]
  apply (slice n M hM).E_congr
  intro A
  rw [Finset.sum_mul]

-- @node: sliceInner_sum_right
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hM,s,f,g), [the slice inner sum right result holds](goal). -/
lemma sliceInner_sum_right {n M : ℕ} (hM : M ≤ n) {ι : Type*}
    (s : Finset ι) (f : Omega n M → ℝ) (g : ι → Omega n M → ℝ) :
    sliceInner n M hM f (fun A => ∑ i ∈ s, g i A) =
      ∑ i ∈ s, sliceInner n M hM f (g i) := by
  unfold sliceInner
  rw [← (slice n M hM).E_sum s (fun i A => f A * g i A)]
  apply (slice n M hM).E_congr
  intro A
  rw [Finset.mul_sum]

-- @node: sliceInner_const_mul_right
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hM,c,f,g), [the slice inner const mul right result holds](goal). -/
lemma sliceInner_const_mul_right {n M : ℕ} (hM : M ≤ n) (c : ℝ)
    (f g : Omega n M → ℝ) :
    sliceInner n M hM f (fun A => c * g A) = c * sliceInner n M hM f g := by
  unfold sliceInner
  rw [← (slice n M hM).E_const_mul c (fun A => f A * g A)]
  apply (slice n M hM).E_congr
  intro A
  ring

-- @node: sliceInner_self_eq_zero
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hM,f,hzero), [the stated equality holds](goal). -/
lemma sliceInner_self_eq_zero {n M : ℕ} (hM : M ≤ n) (f : Omega n M → ℝ)
    (hzero : sliceInner n M hM f f = 0) : f = 0 := by
  classical
  funext A
  have hc : 0 < (n.choose M : ℝ) := by
    exact_mod_cast Nat.choose_pos hM
  have hterm : 0 ≤ (1 / (n.choose M : ℝ)) * (f A * f A) :=
    mul_nonneg (one_div_nonneg.mpr hc.le) (mul_self_nonneg _)
  have hle : (1 / (n.choose M : ℝ)) * (f A * f A) ≤
      ∑ B : Omega n M, (1 / (n.choose M : ℝ)) * (f B * f B) := by
    apply Finset.single_le_sum
      (fun B _ => mul_nonneg (one_div_nonneg.mpr hc.le) (mul_self_nonneg _))
      (Finset.mem_univ A)
  have hsum : (∑ B : Omega n M,
      (1 / (n.choose M : ℝ)) * (f B * f B)) = 0 := by
    simpa [sliceInner, slice, completeRandomization, FiniteDesign.E] using hzero
  rw [hsum] at hle
  have htermzero : (1 / (n.choose M : ℝ)) * (f A * f A) = 0 :=
    le_antisymm hle hterm
  rcases mul_eq_zero.mp htermzero with hweight | hsq
  · exact False.elim ((one_div_ne_zero (ne_of_gt hc)) hweight)
  · simpa using mul_self_eq_zero.mp hsq

-- @node: sliceInner_self_nonneg
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hM,f), [the stated nonnegativity result holds](goal). -/
lemma sliceInner_self_nonneg {n M : ℕ} (hM : M ≤ n) (f : Omega n M → ℝ) :
    0 ≤ sliceInner n M hM f f := by
  unfold sliceInner FiniteDesign.E
  exact Finset.sum_nonneg fun A _ =>
    mul_nonneg ((slice n M hM).p_nonneg A) (mul_self_nonneg _)

-- @node: sliceInner_sub_self
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hM,f,g), [the slice inner sub self result holds](goal). -/
lemma sliceInner_sub_self {n M : ℕ} (hM : M ≤ n) (f g : Omega n M → ℝ) :
    sliceInner n M hM (fun A => f A - g A) (fun A => f A - g A) =
      sliceInner n M hM f f + sliceInner n M hM g g -
        2 * sliceInner n M hM f g := by
  unfold sliceInner
  rw [show (fun A => (f A - g A) * (f A - g A)) =
      (fun A => f A * f A + g A * g A - 2 * (f A * g A)) by
        funext A; ring,
    (slice n M hM).E_sub, (slice n M hM).E_add,
    (slice n M hM).E_const_mul]

-- @node: kneserOp_sum
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,s,f), [the kneser op sum result holds](goal). -/
lemma kneserOp_sum {n M : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Omega n M → ℝ) :
    kneserOp n M (fun A => ∑ i ∈ s, f i A) =
      fun A => ∑ i ∈ s, kneserOp n M (f i) A := by
  classical
  funext A
  unfold kneserOp kneserAdjacency
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.sum_mul]

-- @node: orderedDisjointPair_first_E_eq_slice
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,h2M,f), [the stated expectation identity holds](goal). -/
lemma orderedDisjointPair_first_E_eq_slice {n M : ℕ} (h2M : 2 * M ≤ n)
    (f : Omega n M → ℝ) :
    (orderedDisjointPairDesign n M h2M).E (fun P => f P.1.1) =
      (slice n M (by omega)).E f := by
  calc
    (orderedDisjointPairDesign n M h2M).E (fun P => f P.1.1) =
        (orderedDisjointPairDesign n M h2M).E
          (fun P => f P.1.1 * (fun _ : Omega n M => (1 : ℝ)) P.1.2) := by
            apply (orderedDisjointPairDesign n M h2M).E_congr
            simp
    _ = sliceInner n M (by omega) f (kneserOp n M (fun _ => 1)) :=
      orderedDisjointPair_E_eq n M h2M f (fun _ => 1)
    _ = (slice n M (by omega)).E f := by
      unfold sliceInner
      apply (slice n M (by omega)).E_congr
      intro A
      have hd : ((n - M).choose M : ℝ) ≠ 0 := by
        exact_mod_cast Nat.choose_ne_zero (by omega : M ≤ n - M)
      simp [kneserOp, kneserAdjacency, kneserDegree n M h2M A, hd]

-- @node: orderedDisjointPair_swap
/-- For [the stated inputs](hyp:n,M), [ordered disjoint pair swap](goal) is defined by the formula below. -/
def orderedDisjointPairSwap {n M : ℕ} : OrderedDisjointPair n M ≃ OrderedDisjointPair n M where
  toFun P := ⟨(P.1.2, P.1.1), P.2.symm⟩
  invFun P := ⟨(P.1.2, P.1.1), P.2.symm⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

-- @node: orderedDisjointPair_second_E_eq_slice
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,h2M,f), [the stated expectation identity holds](goal). -/
lemma orderedDisjointPair_second_E_eq_slice {n M : ℕ} (h2M : 2 * M ≤ n)
    (f : Omega n M → ℝ) :
    (orderedDisjointPairDesign n M h2M).E (fun P => f P.1.2) =
      (slice n M (by omega)).E f := by
  classical
  calc
    (orderedDisjointPairDesign n M h2M).E (fun P => f P.1.2) =
        (orderedDisjointPairDesign n M h2M).E (fun P => f P.1.1) := by
      unfold FiniteDesign.E orderedDisjointPairDesign uniformFiniteDesign
      exact Fintype.sum_equiv orderedDisjointPairSwap _ _ (fun _ => rfl)
    _ = (slice n M (by omega)).E f :=
      orderedDisjointPair_first_E_eq_slice h2M f

-- @node: johnson_proj_const_eq_zero
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,h2M,J,hJohnson,k,hk,c), [the stated equality holds](goal). -/
lemma johnson_proj_const_eq_zero {n M : ℕ} (h2M : 2 * M ≤ n)
    (J : JohnsonProjections n M) (hJohnson : JohnsonOrthogonalDecomposition n M J)
    (k : Fin (M + 1)) (hk : 0 < k.1) (c : ℝ) :
    J.proj k (fun _ => c) = 0 := by
  classical
  let s := Finset.univ.filter fun l : Fin (M + 1) => 0 < l.1
  have hkMem : k ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
  have hsum : (fun A => ∑ l ∈ s, J.proj l (fun _ => c) A) = 0 := by
    funext A
    change (∑ l ∈ s, J.proj l (fun _ => c) A) = (0 : ℝ)
    simpa only [s, FiniteDesign.E_const, sub_self] using (hJohnson h2M).1 (fun _ => c) A
  have hinner : sliceInner n M (by omega) (J.proj k (fun _ => c))
      (J.proj k (fun _ => c)) = 0 := by
    have hz : sliceInner n M (by omega) (fun A => ∑ l ∈ s, J.proj l (fun _ => c) A)
        (J.proj k (fun _ => c)) = 0 := by rw [hsum]; simp [sliceInner]
    rw [sliceInner_sum_left] at hz
    rw [Finset.sum_eq_single k] at hz
    · exact hz
    · intro l hl hlk
      rw [(hJohnson h2M).2 l k (fun _ => c) (fun _ => c) hlk]
    · exact fun hk' => (hk' hkMem).elim
  exact sliceInner_self_eq_zero (by omega) _ hinner

-- @node: johnson_proj_centered_eq
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,h2M,J,hJohnson,k,hk,f), [the stated equality holds](goal). -/
lemma johnson_proj_centered_eq {n M : ℕ} (h2M : 2 * M ≤ n)
    (J : JohnsonProjections n M) (hJohnson : JohnsonOrthogonalDecomposition n M J)
    (k : Fin (M + 1)) (hk : 0 < k.1) (f : Omega n M → ℝ) :
    J.proj k (fun A => f A - (slice n M (by omega)).E f) = J.proj k f := by
  let m := (slice n M (by omega)).E f
  calc
    J.proj k (fun A => f A - (slice n M (by omega)).E f) =
        J.proj k (fun A => f A + (-m) * (fun _ => (1 : ℝ)) A) := by
          congr 1
          funext A
          dsimp [m]
          ring
    _ = fun A => J.proj k f A + J.proj k (fun A => (-m) * (fun _ => (1 : ℝ)) A) A :=
      J.map_add k f _
    _ = fun A => J.proj k f A + (-m) * J.proj k (fun _ => (1 : ℝ)) A := by
      rw [J.map_smul]
    _ = J.proj k f := by
      rw [johnson_proj_const_eq_zero h2M J hJohnson k hk 1]
      simp

-- @node: thm:exact-kneser-identity
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hM,h2M,J,Y,hJohnsonOrthogonalDecomposition_of_gate,hKneserAdjacencySpectrum_of_gate), [the stated equality holds](goal). -/
theorem exact_kneser_identity (n M : ℕ) (hM : 2 ≤ M) (h2M : 2 * M ≤ n)
    (J : JohnsonProjections n M) (Y : PotentialOutcome n M)
    (hJohnsonOrthogonalDecomposition_of_gate : JohnsonOrthogonalDecomposition n M J)
    (hKneserAdjacencySpectrum_of_gate : KneserAdjacencySpectrum n M) :
    (∀ (k : Fin (M + 1)) (f : Omega n M → ℝ),
      kneserOp n M (J.proj k f) =
        fun A => kneserEigenvalue n M k * J.proj k f A) ∧
    (∀ (f g : Omega n M → ℝ),
      (slice n M (by omega)).E f = 0 →
      (slice n M (by omega)).E g = 0 →
      (orderedDisjointPairDesign n M h2M).Cov
          (fun P => f P.1.1) (fun P => g P.1.2) =
        ∑ k ∈ (Finset.univ.filter fun k : Fin (M + 1) => 0 < k.1),
          kneserEigenvalue n M k *
            sliceInner n M (by omega) (J.proj k f) (J.proj k g)) ∧
    crossCovContrast n M (by omega) Y =
      ∑ k ∈ (Finset.univ.filter fun k : Fin (M + 1) => 0 < k.1),
        kneserEigenvalue n M k *
          sliceNorm n M (by omega)
            (J.proj k (fun A => armTable n M Y true A - armTable n M Y false A)) ^ 2 := by
  classical
  have hEigen : ∀ (k : Fin (M + 1)) (f : Omega n M → ℝ),
      kneserOp n M (J.proj k f) =
        fun A => kneserEigenvalue n M k * J.proj k f A := by
    intro k f
    unfold kneserOp
    rw [hKneserAdjacencySpectrum_of_gate h2M k (J.proj k f)]
    · funext A
      simp only [kneserEigenvalue]
      calc
        (-1 : ℝ) ^ k.1 * ((n - M - k.1).choose (M - k.1) : ℝ) *
              J.proj k f A / ((n - M).choose M : ℝ) =
            (-1 : ℝ) ^ k.1 *
              (((n - M - k.1).choose (M - k.1) : ℝ) /
                ((n - M).choose M : ℝ)) * J.proj k f A := by ring
        _ = (-1 : ℝ) ^ k.1 *
              ((M.descFactorial k.1 : ℝ) / ((n - M).descFactorial k.1 : ℝ)) *
                J.proj k f A := by
              rw [kneserChooseRatio_eq_descFactorialRatio n M h2M k]
        _ = ((-1 : ℝ) ^ k.1 * (M.descFactorial k.1 : ℝ) /
              ((n - M).descFactorial k.1 : ℝ)) * J.proj k f A := by ring
    · rw [← J.range_eq k]
      exact ⟨f, rfl⟩
  have hCov : ∀ (f g : Omega n M → ℝ),
      (slice n M (by omega)).E f = 0 →
      (slice n M (by omega)).E g = 0 →
      (orderedDisjointPairDesign n M h2M).Cov
          (fun P => f P.1.1) (fun P => g P.1.2) =
        ∑ k ∈ (Finset.univ.filter fun k : Fin (M + 1) => 0 < k.1),
          kneserEigenvalue n M k *
            sliceInner n M (by omega) (J.proj k f) (J.proj k g) := by
    intro f g hf hg
    let s := Finset.univ.filter fun k : Fin (M + 1) => 0 < k.1
    have hfSum : (fun A => ∑ k ∈ s, J.proj k f A) = f := by
      funext A
      simpa only [s, hf, sub_zero] using
        (hJohnsonOrthogonalDecomposition_of_gate h2M).1 f A
    have hgSum : (fun A => ∑ k ∈ s, J.proj k g A) = g := by
      funext A
      simpa only [s, hg, sub_zero] using
        (hJohnsonOrthogonalDecomposition_of_gate h2M).1 g A
    rw [(orderedDisjointPairDesign n M h2M).Cov_eq,
      orderedDisjointPair_first_E_eq_slice h2M,
      orderedDisjointPair_second_E_eq_slice h2M, hf, hg]
    simp only [zero_mul, sub_zero]
    rw [orderedDisjointPair_E_eq n M h2M]
    calc
      sliceInner n M (by omega) f (kneserOp n M g) =
          sliceInner n M (by omega) (fun A => ∑ k ∈ s, J.proj k f A)
            (kneserOp n M (fun A => ∑ k ∈ s, J.proj k g A)) := by
              rw [hfSum, hgSum]
      _ = ∑ k ∈ s, kneserEigenvalue n M k *
            sliceInner n M (by omega) (J.proj k f) (J.proj k g) := by
        rw [kneserOp_sum, sliceInner_sum_left]
        simp_rw [hEigen, sliceInner_sum_right, sliceInner_const_mul_right]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_eq_single k]
        · intro l hl hkl
          rw [(hJohnsonOrthogonalDecomposition_of_gate h2M).2 k l f g hkl.symm]
          simp
        · exact fun hk' => (hk' hk).elim
  refine ⟨hEigen, hCov, ?_⟩
  let h₁ := armTable n M Y true
  let h₀ := armTable n M Y false
  let h₁c := armTableCentered n M (by omega) Y true
  let h₀c := armTableCentered n M (by omega) Y false
  have hCentered (z : Arm) :
      (slice n M (by omega)).E (armTableCentered n M (by omega) Y z) = 0 := by
    unfold armTableCentered
    rw [(slice n M (by omega)).E_sub]
    simp
  have hCross (a b : Arm) :
      crossCov n M (by omega) Y a b =
        (orderedDisjointPairDesign n M h2M).Cov
          (fun P => armTableCentered n M (by omega) Y a P.1.1)
          (fun P => armTableCentered n M (by omega) Y b P.1.2) := by
    rw [(orderedDisjointPairDesign n M h2M).Cov_eq,
      orderedDisjointPair_first_E_eq_slice h2M,
      orderedDisjointPair_second_E_eq_slice h2M, hCentered, hCentered]
    simp only [zero_mul, sub_zero]
    rw [orderedDisjointPair_E_eq n M h2M]
    rfl
  have hProjSub (k : Fin (M + 1)) :
      J.proj k (fun A => h₁ A - h₀ A) =
        fun A => J.proj k h₁ A - J.proj k h₀ A := by
    calc
      J.proj k (fun A => h₁ A - h₀ A) =
          J.proj k (fun A => h₁ A + (-1 : ℝ) * h₀ A) := by
            congr 1
            funext A
            ring
      _ = fun A => J.proj k h₁ A + J.proj k (fun A => (-1 : ℝ) * h₀ A) A :=
        J.map_add k h₁ _
      _ = fun A => J.proj k h₁ A + (-1 : ℝ) * J.proj k h₀ A := by
        rw [J.map_smul]
      _ = fun A => J.proj k h₁ A - J.proj k h₀ A := by
        funext A
        ring
  rw [crossCovContrast, hCross, hCross, hCross,
    hCov h₁c h₁c (hCentered true) (hCentered true),
    hCov h₀c h₀c (hCentered false) (hCentered false),
    hCov h₁c h₀c (hCentered true) (hCentered false)]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < k.1 := (Finset.mem_filter.mp hk).2
  rw [show h₁c = (fun A => h₁ A - (slice n M (by omega)).E h₁) by rfl,
    show h₀c = (fun A => h₀ A - (slice n M (by omega)).E h₀) by rfl,
    johnson_proj_centered_eq h2M J hJohnsonOrthogonalDecomposition_of_gate k hkpos h₁,
    johnson_proj_centered_eq h2M J hJohnsonOrthogonalDecomposition_of_gate k hkpos h₀,
    hProjSub]
  rw [show sliceNorm n M (by omega)
        (fun A => J.proj k h₁ A - J.proj k h₀ A) ^ 2 =
      sliceInner n M (by omega)
        (fun A => J.proj k h₁ A - J.proj k h₀ A)
        (fun A => J.proj k h₁ A - J.proj k h₀ A) by
      unfold sliceNorm sliceNormSq
      exact Real.sq_sqrt (sliceInner_self_nonneg (by omega) _),
    sliceInner_sub_self]
  ring

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

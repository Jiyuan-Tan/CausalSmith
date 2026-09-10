import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.Asymptotics
import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.TExactPameVariance

/-!
# Dense projection expansion

The deterministic group-scaled variance expansion is stated for bounded schedule
arrays without a scaled-variance nondegeneracy premise.
-/

open scoped BigOperators Topology
open Filter Finset

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased

/-- The pooled Johnson degrees at least two, at the group-count scale. -/
noncomputable def higherDegreeContribution {M : ℕ} (A : ScheduleArray M)
    (J : ∀ r, JohnsonProjections (A.popSize r) M) (r : ℕ) : ℝ :=
  (A.groups r : ℝ) *
    ∑ k ∈ (Finset.univ.filter fun k : Fin (M + 1) => 2 ≤ k.1),
      kneserEigenvalue (A.popSize r) M k *
        sliceNorm (A.popSize r) M (A.groupSize_le r)
          ((J r).proj k (fun S =>
            armTable (A.popSize r) M (A.schedule r) true S -
            armTable (A.popSize r) M (A.schedule r) false S)) ^ 2

-- @node: armTable_abs_le_of_boundedSchedule
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,A,B,hBounded,r,z,S), [the stated bound holds](goal). -/
lemma armTable_abs_le_of_boundedSchedule {M : ℕ} (A : ScheduleArray M) (B : ℝ)
    (hBounded : BoundedSchedule A B) (r : ℕ) (z : Arm)
    (S : Omega (A.popSize r) M) :
    |armTable (A.popSize r) M (A.schedule r) z S| ≤ B := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast A.groupSize_ge_two.trans' (by omega)
  rw [armTable, abs_div, abs_of_pos hMpos]
  apply (div_le_iff₀ hMpos).2
  calc
    |∑ i ∈ S.1.attach, A.schedule r S i z| ≤
        ∑ i ∈ S.1.attach, |A.schedule r S i z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S.1.attach, B := by
      gcongr with i hi
      exact hBounded.2 r S i z
    _ = B * M := by simp [S.2]; ring

-- @node: sliceInner_self_le_sq_of_abs_le
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMn,f,K,hf), [the stated bound holds](goal). -/
lemma sliceInner_self_le_sq_of_abs_le {n M : ℕ} (hMn : M ≤ n)
    (f : Omega n M → ℝ) (K : ℝ) (hf : ∀ S, |f S| ≤ K) :
    sliceInner n M hMn f f ≤ K ^ 2 := by
  unfold sliceInner FiniteDesign.E
  calc
    (∑ S, (slice n M hMn).p S * (f S * f S)) ≤
        ∑ S, (slice n M hMn).p S * K ^ 2 := by
      apply Finset.sum_le_sum
      intro S _
      have hK : 0 ≤ K := (abs_nonneg (f S)).trans (hf S)
      apply mul_le_mul_of_nonneg_left _ ((slice n M hMn).p_nonneg S)
      simpa [pow_two] using (sq_le_sq₀ (abs_nonneg (f S)) hK).2 (hf S)
    _ = K ^ 2 := by
      rw [← Finset.sum_mul]
      simp [(slice n M hMn).p_sum]

-- @node: johnsonProjection_energy_le_of_abs_le
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,h2M,J,k,f,K,hf), [the stated bound holds](goal). -/
lemma johnsonProjection_energy_le_of_abs_le {n M : ℕ} (h2M : 2 * M ≤ n)
    (J : JohnsonProjections n M)
    (k : Fin (M + 1)) (f : Omega n M → ℝ) (K : ℝ)
    (hf : ∀ S, |f S| ≤ K) :
    sliceNorm n M (by omega) (J.proj k f) ^ 2 ≤ K ^ 2 := by
  let P := J.proj k f
  let R : Omega n M → ℝ := fun S => f S - P S
  have hP : P ∈ johnsonHarmonicSpace n M J.slice_nonempty k := by
    rw [← J.range_eq k]
    exact ⟨f, rfl⟩
  have hOrth : sliceInner n M J.slice_nonempty R P = 0 :=
    J.residual_orthogonal k f P hP
  have hdecomp : sliceInner n M J.slice_nonempty f f =
      sliceInner n M J.slice_nonempty R R + sliceInner n M J.slice_nonempty P P := by
    have hpoint : (fun S => f S * f S) = fun S =>
        R S * R S + P S * P S + 2 * (R S * P S) := by
      funext S
      dsimp [R, P]
      ring
    unfold sliceInner at hOrth ⊢
    rw [hpoint, (slice n M J.slice_nonempty).E_add,
      (slice n M J.slice_nonempty).E_add,
      (slice n M J.slice_nonempty).E_const_mul, hOrth]
    ring
  have hproj : sliceInner n M J.slice_nonempty P P ≤
      sliceInner n M J.slice_nonempty f f := by
    rw [hdecomp]
    exact le_add_of_nonneg_left (sliceInner_self_nonneg J.slice_nonempty R)
  rw [show sliceNorm n M (by omega) P ^ 2 = sliceInner n M (by omega) P P by
    unfold sliceNorm sliceNormSq
    exact Real.sq_sqrt (sliceInner_self_nonneg (by omega) P)]
  simpa only [P, Subsingleton.elim J.slice_nonempty (by omega : M ≤ n)] using
    hproj.trans (sliceInner_self_le_sq_of_abs_le J.slice_nonempty f K hf)

-- @node: kneserEigenvalue_abs_le_one
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,h2M,k), [the stated bound holds](goal). -/
lemma kneserEigenvalue_abs_le_one {n M : ℕ} (h2M : 2 * M ≤ n)
    (k : Fin (M + 1)) : |kneserEigenvalue n M k| ≤ 1 := by
  have hkM : k.1 ≤ M := by omega
  have hbase : M ≤ n - M := by omega
  have hden : 0 < (n - M).descFactorial k.1 :=
    Nat.descFactorial_pos.mpr (hkM.trans hbase)
  have hnumden : M.descFactorial k.1 ≤ (n - M).descFactorial k.1 :=
    Nat.descFactorial_le k.1 hbase
  simp only [kneserEigenvalue, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow]
  rw [abs_of_nonneg (by positivity : 0 ≤ (M.descFactorial k.1 : ℝ)),
    abs_of_nonneg (by positivity : 0 ≤ ((n - M).descFactorial k.1 : ℝ))]
  simp only [one_mul]
  exact (div_le_one (by exact_mod_cast hden)).2 (by exact_mod_cast hnumden)

-- @node: kneserEigenvalue_abs_le_ge_four
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMpos,h4M,k), [the stated bound holds](goal). -/
lemma kneserEigenvalue_abs_le_ge_four {n M : ℕ} (hMpos : 0 < M)
    (h4M : 4 * M ≤ n)
    (k : Fin (M + 1)) :
    |kneserEigenvalue n M k| ≤ ((2 * M : ℕ) : ℝ) ^ k.1 / (n : ℝ) ^ k.1 := by
  have hkM : k.1 ≤ M := by omega
  have hMn : M ≤ n - M := by omega
  have hkden : k.1 ≤ n - M := hkM.trans hMn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdenpos : (0 : ℝ) < (n - M).descFactorial k.1 := by
    exact_mod_cast Nat.descFactorial_pos.mpr hkden
  have hnum : ((M.descFactorial k.1 : ℕ) : ℝ) ≤ (M : ℝ) ^ k.1 := by
    exact_mod_cast Nat.descFactorial_le_pow M k.1
  have hbaseNat : n ≤ 2 * (n - M + 1 - k.1) := by omega
  have hbase : (n : ℝ) / 2 ≤ (n - M + 1 - k.1 : ℕ) := by
    have hbaseR : (n : ℝ) ≤ 2 * ((n - M + 1 - k.1 : ℕ) : ℝ) := by
      exact_mod_cast hbaseNat
    linarith
  have hden : ((n : ℝ) / 2) ^ k.1 ≤
      ((n - M).descFactorial k.1 : ℕ) := by
    calc
      ((n : ℝ) / 2) ^ k.1 ≤ ((n - M + 1 - k.1 : ℕ) : ℝ) ^ k.1 :=
        pow_le_pow_left₀ (by positivity) hbase _
      _ ≤ ((n - M).descFactorial k.1 : ℕ) := by
        exact_mod_cast Nat.pow_sub_le_descFactorial (n - M) k.1
  simp only [kneserEigenvalue, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow]
  rw [abs_of_nonneg (by positivity : 0 ≤ (M.descFactorial k.1 : ℝ)),
    abs_of_nonneg (by positivity : 0 ≤ ((n - M).descFactorial k.1 : ℝ))]
  simp only [one_mul]
  calc
    (M.descFactorial k.1 : ℝ) / ((n - M).descFactorial k.1 : ℝ) ≤
        (M : ℝ) ^ k.1 / ((n : ℝ) / 2) ^ k.1 := by
      gcongr
    _ = ((2 * M : ℕ) : ℝ) ^ k.1 / (n : ℝ) ^ k.1 := by
      push_cast
      rw [mul_pow, div_pow]
      field_simp

-- @node: johnsonSpectralSum_abs_le
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,d,hMpos,h4M,J,s,hs,f,K,hf), [the stated bound holds](goal). -/
lemma johnsonSpectralSum_abs_le {n M d : ℕ} (hMpos : 0 < M) (h4M : 4 * M ≤ n)
    (J : JohnsonProjections n M) (s : Finset (Fin (M + 1)))
    (hs : ∀ k ∈ s, d ≤ k.1) (f : Omega n M → ℝ) (K : ℝ)
    (hf : ∀ S, |f S| ≤ K) :
    |∑ k ∈ s, kneserEigenvalue n M k *
        sliceNorm n M (by omega) (J.proj k f) ^ 2| ≤
      (s.card : ℝ) * (((2 * M : ℕ) : ℝ) / (n : ℝ)) ^ d * K ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hq0 : 0 ≤ (((2 * M : ℕ) : ℝ) / (n : ℝ)) := by positivity
  have hq1 : (((2 * M : ℕ) : ℝ) / (n : ℝ)) ≤ 1 := by
    apply (div_le_one hnpos).2
    exact_mod_cast (by omega : 2 * M ≤ n)
  calc
    |∑ k ∈ s, kneserEigenvalue n M k *
        sliceNorm n M (by omega) (J.proj k f) ^ 2| ≤
        ∑ k ∈ s, |kneserEigenvalue n M k *
          sliceNorm n M (by omega) (J.proj k f) ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ s, ((((2 * M : ℕ) : ℝ) / (n : ℝ)) ^ d * K ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      have hsqabs : |sliceNorm n M (by omega) (J.proj k f) ^ 2| =
          sliceNorm n M (by omega) (J.proj k f) ^ 2 := abs_of_nonneg (sq_nonneg _)
      rw [hsqabs]
      have heig : |kneserEigenvalue n M k| ≤
          (((2 * M : ℕ) : ℝ) / (n : ℝ)) ^ d := by
        calc
          |kneserEigenvalue n M k| ≤
              ((2 * M : ℕ) : ℝ) ^ k.1 / (n : ℝ) ^ k.1 :=
            kneserEigenvalue_abs_le_ge_four hMpos h4M k
          _ = (((2 * M : ℕ) : ℝ) / (n : ℝ)) ^ k.1 := by rw [div_pow]
          _ ≤ (((2 * M : ℕ) : ℝ) / (n : ℝ)) ^ d :=
            pow_le_pow_of_le_one hq0 hq1 (hs k hk)
      exact mul_le_mul heig
        (johnsonProjection_energy_le_of_abs_le (by omega) J k f K hf)
        (sq_nonneg _) (pow_nonneg hq0 _)
    _ = (s.card : ℝ) * (((2 * M : ℕ) : ℝ) / (n : ℝ)) ^ d * K ^ 2 := by
      simp
      ring

-- @node: higherDegreeContribution_uniform_bound
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,A,J,B,hBounded,r), [the higher degree contribution uniform bound result holds](goal). -/
lemma higherDegreeContribution_uniform_bound {M : ℕ} (hM : 2 ≤ M)
    (A : ScheduleArray M) (J : ∀ r, JohnsonProjections (A.popSize r) M)
    (B : ℝ) (hBounded : BoundedSchedule A B) (r : ℕ) :
    |higherDegreeContribution A J r| ≤
      (64 * (M : ℝ) ^ 2 * (M + 1 : ℝ) * B ^ 2) / (A.popSize r : ℝ) := by
  let n := A.popSize r
  let s := Finset.univ.filter fun k : Fin (M + 1) => 2 ≤ k.1
  let f : Omega n M → ℝ := fun S =>
    armTable n M (A.schedule r) true S - armTable n M (A.schedule r) false S
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast lt_of_lt_of_le (Nat.mul_pos (by omega) (A.groups_pos r)) (A.grouped_le r)
  have hGle : (A.groups r : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast le_trans (Nat.le_mul_of_pos_left (A.groups r) (by omega)) (A.grouped_le r)
  have hcard : (s.card : ℝ) ≤ (M + 1 : ℝ) := by
    exact_mod_cast (calc
      s.card ≤ (Finset.univ : Finset (Fin (M + 1))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = M + 1 := by simp)
  have hf : ∀ S, |f S| ≤ 2 * B := by
    intro S
    dsimp [f, n]
    calc
      |armTable (A.popSize r) M (A.schedule r) true S -
          armTable (A.popSize r) M (A.schedule r) false S| ≤
          |armTable (A.popSize r) M (A.schedule r) true S| +
            |armTable (A.popSize r) M (A.schedule r) false S| := abs_sub _ _
      _ ≤ B + B := add_le_add
        (armTable_abs_le_of_boundedSchedule A B hBounded r true S)
        (armTable_abs_le_of_boundedSchedule A B hBounded r false S)
      _ = 2 * B := by ring
  have h2M : 2 * M ≤ n := by
    have htpos := A.treated_pos r
    have htlt := A.treated_lt r
    exact le_trans (by
      have : 2 ≤ A.groups r := by omega
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left M this) (by simpa [n] using A.grouped_le r)
  have hraw : |higherDegreeContribution A J r| =
      (A.groups r : ℝ) * |∑ k ∈ s, kneserEigenvalue n M k *
        sliceNorm n M (by omega) ((J r).proj k f) ^ 2| := by
    unfold higherDegreeContribution
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (A.groups r : ℝ))]
  rw [hraw]
  by_cases hlarge : 4 * M ≤ n
  · have hspectral := johnsonSpectralSum_abs_le (by omega : 0 < M) hlarge
      (J r) s (fun k hk => (Finset.mem_filter.mp hk).2) f (2 * B) hf
    calc
      (A.groups r : ℝ) * |∑ k ∈ s, kneserEigenvalue n M k *
          sliceNorm n M (by omega) ((J r).proj k f) ^ 2| ≤
          (n : ℝ) * ((M + 1 : ℝ) * (((2 * M : ℕ) : ℝ) / (n : ℝ)) ^ 2 *
            (2 * B) ^ 2) := by
        apply mul_le_mul hGle
        · exact hspectral.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcard (sq_nonneg _)) (sq_nonneg _))
        · positivity
        · positivity
      _ ≤ (64 * (M : ℝ) ^ 2 * (M + 1 : ℝ) * B ^ 2) / (n : ℝ) := by
        push_cast
        field_simp
        nlinarith [sq_nonneg B]
  · have hspectral : |∑ k ∈ s, kneserEigenvalue n M k *
          sliceNorm n M (by omega) ((J r).proj k f) ^ 2| ≤
          (s.card : ℝ) * (2 * B) ^ 2 := by
      calc
        |∑ k ∈ s, kneserEigenvalue n M k *
            sliceNorm n M (by omega) ((J r).proj k f) ^ 2| ≤
            ∑ k ∈ s, |kneserEigenvalue n M k *
              sliceNorm n M (by omega) ((J r).proj k f) ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ s, (2 * B) ^ 2 := by
          apply Finset.sum_le_sum
          intro k hk
          rw [abs_mul]
          have hsqabs : |sliceNorm n M (by omega) ((J r).proj k f) ^ 2| =
              sliceNorm n M (by omega) ((J r).proj k f) ^ 2 :=
            abs_of_nonneg (sq_nonneg _)
          rw [hsqabs]
          calc
            |kneserEigenvalue n M k| *
                sliceNorm n M (by omega) ((J r).proj k f) ^ 2 ≤
                1 * sliceNorm n M (by omega) ((J r).proj k f) ^ 2 :=
              mul_le_mul_of_nonneg_right (kneserEigenvalue_abs_le_one h2M k)
                (sq_nonneg _)
            _ ≤ 1 * (2 * B) ^ 2 := mul_le_mul_of_nonneg_left
              (johnsonProjection_energy_le_of_abs_le h2M (J r) k f (2 * B) hf)
              zero_le_one
            _ = (2 * B) ^ 2 := one_mul _
        _ = (s.card : ℝ) * (2 * B) ^ 2 := by simp
    have hnupper : (n : ℝ) ≤ 4 * M := by exact_mod_cast (by omega : n ≤ 4 * M)
    calc
      (A.groups r : ℝ) * |∑ k ∈ s, kneserEigenvalue n M k *
          sliceNorm n M (by omega) ((J r).proj k f) ^ 2| ≤
          (n : ℝ) * ((M + 1 : ℝ) * (2 * B) ^ 2) := by
        apply mul_le_mul hGle
        · exact hspectral.trans (mul_le_mul_of_nonneg_right hcard (sq_nonneg _))
        · positivity
        · positivity
      _ ≤ (64 * (M : ℝ) ^ 2 * (M + 1 : ℝ) * B ^ 2) / (n : ℝ) := by
        apply (le_div_iff₀ hnpos).2
        have hsqn : (n : ℝ) ^ 2 ≤ (4 * (M : ℝ)) ^ 2 :=
          (sq_le_sq₀ (by positivity) (by positivity)).2 hnupper
        have hcore : 4 * (n : ℝ) ^ 2 ≤ 64 * (M : ℝ) ^ 2 := by nlinarith
        calc
          (n : ℝ) * ((M + 1 : ℝ) * (2 * B) ^ 2) * (n : ℝ) =
              (4 * (n : ℝ) ^ 2) * ((M + 1 : ℝ) * B ^ 2) := by ring
          _ ≤ (64 * (M : ℝ) ^ 2) * ((M + 1 : ℝ) * B ^ 2) :=
            mul_le_mul_of_nonneg_right hcore (mul_nonneg (by positivity) (sq_nonneg B))
          _ = 64 * (M : ℝ) ^ 2 * (M + 1 : ℝ) * B ^ 2 := by ring

-- @node: scaledContrastCrossCov_decomposition
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,A,J,r,hJohnson,hKneser), [the scaled contrast cross cov decomposition result holds](goal). -/
lemma scaledContrastCrossCov_decomposition {M : ℕ} (hM : 2 ≤ M)
    (A : ScheduleArray M) (J : ∀ r, JohnsonProjections (A.popSize r) M) (r : ℕ)
    (hJohnson : JohnsonOrthogonalDecomposition (A.popSize r) M (J r))
    (hKneser : KneserAdjacencySpectrum (A.popSize r) M) :
    (A.groups r : ℝ) * A.contrastCrossCov r =
      -((M : ℝ) * (A.groups r : ℝ) / ((A.popSize r : ℝ) - M)) *
        A.degreeOne (by omega) J r + higherDegreeContribution A J r := by
  let one : Fin (M + 1) := ⟨1, by omega⟩
  let high := Finset.univ.filter fun k : Fin (M + 1) => 2 ≤ k.1
  let positive := Finset.univ.filter fun k : Fin (M + 1) => 0 < k.1
  have hgroups : 2 ≤ A.groups r := by
    have htpos := A.treated_pos r
    have htlt := A.treated_lt r
    omega
  have h2M : 2 * M ≤ A.popSize r := by
    exact le_trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left M hgroups)
      (A.grouped_le r)
  have hsplit : positive = insert one high := by
    ext k
    simp only [positive, high, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hk
      by_cases hk1 : k.1 = 1
      · left
        exact Fin.ext hk1
      · right
        omega
    · rintro (rfl | hk)
      · simp [one]
      · omega
  have honeNot : one ∉ high := by simp [one, high]
  have hexact := (exact_kneser_identity (A.popSize r) M hM h2M (J r)
    (A.schedule r) hJohnson hKneser).2.2
  change A.contrastCrossCov r = ∑ k ∈ positive,
    kneserEigenvalue (A.popSize r) M k *
      sliceNorm (A.popSize r) M (A.groupSize_le r)
        ((J r).proj k (fun S => armTable (A.popSize r) M (A.schedule r) true S -
          armTable (A.popSize r) M (A.schedule r) false S)) ^ 2 at hexact
  rw [hsplit, Finset.sum_insert honeNot] at hexact
  rw [hexact]
  unfold higherDegreeContribution ScheduleArray.degreeOne degreeOneEnergy
  simp only [high, one, kneserEigenvalue, Nat.descFactorial, Nat.sub_zero, neg_mul]
  simp only [pow_one, mul_one]
  rw [Nat.cast_sub (by omega : M ≤ A.popSize r)]
  have hden : (A.popSize r : ℝ) - M ≠ 0 := by
    have : (M : ℝ) < A.popSize r := by exact_mod_cast (by omega : M < A.popSize r)
    linarith
  field_simp

-- @node: sliceExpectation_abs_le_of_abs_le
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMn,f,K,hf), [the stated expectation identity holds](goal). -/
lemma sliceExpectation_abs_le_of_abs_le {n M : ℕ} (hMn : M ≤ n)
    (f : Omega n M → ℝ) (K : ℝ) (hf : ∀ S, |f S| ≤ K) :
    |(slice n M hMn).E f| ≤ K := by
  calc
    |(slice n M hMn).E f| ≤ (slice n M hMn).E (fun S => |f S|) := by
      unfold FiniteDesign.E
      calc
        |∑ S, (slice n M hMn).p S * f S| ≤
            ∑ S, |(slice n M hMn).p S * f S| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ S, (slice n M hMn).p S * |f S| := by
          apply Finset.sum_congr rfl
          intro S _
          rw [abs_mul, abs_of_nonneg ((slice n M hMn).p_nonneg S)]
    _ ≤ (slice n M hMn).E (fun _ => K) := by
      unfold FiniteDesign.E
      apply Finset.sum_le_sum
      intro S _
      exact mul_le_mul_of_nonneg_left (hf S) ((slice n M hMn).p_nonneg S)
    _ = K := (slice n M hMn).E_const K

-- @node: armCrossCov_abs_le_ge_four
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,A,J,B,hBounded,r,h4M,hJohnson,hKneser,z), [the stated bound holds](goal). -/
lemma armCrossCov_abs_le_ge_four {M : ℕ} (hM : 2 ≤ M) (A : ScheduleArray M)
    (J : ∀ r, JohnsonProjections (A.popSize r) M) (B : ℝ)
    (hBounded : BoundedSchedule A B) (r : ℕ) (h4M : 4 * M ≤ A.popSize r)
    (hJohnson : JohnsonOrthogonalDecomposition (A.popSize r) M (J r))
    (hKneser : KneserAdjacencySpectrum (A.popSize r) M) (z : Arm) :
    |A.armCrossCov r z z| ≤
      (M + 1 : ℝ) * (((2 * M : ℕ) : ℝ) / (A.popSize r : ℝ)) * (2 * B) ^ 2 := by
  let n := A.popSize r
  let f := armTable n M (A.schedule r) z
  let fc := armTableCentered n M (A.groupSize_le r) (A.schedule r) z
  let positive := Finset.univ.filter fun k : Fin (M + 1) => 0 < k.1
  have h2M : 2 * M ≤ n := by omega
  have hf : ∀ S, |f S| ≤ B := by
    intro S
    exact armTable_abs_le_of_boundedSchedule A B hBounded r z S
  have hfc : ∀ S, |fc S| ≤ 2 * B := by
    intro S
    dsimp [fc, armTableCentered]
    calc
      |f S - (slice n M (A.groupSize_le r)).E f| ≤
          |f S| + |(slice n M (A.groupSize_le r)).E f| := abs_sub _ _
      _ ≤ B + B := add_le_add (hf S)
        (sliceExpectation_abs_le_of_abs_le (A.groupSize_le r) f B hf)
      _ = 2 * B := by ring
  have hcenter : (slice n M (A.groupSize_le r)).E fc = 0 := by
    change (slice n M (A.groupSize_le r)).E
      (fun S => f S - (slice n M (A.groupSize_le r)).E f) = 0
    rw [(slice n M (A.groupSize_le r)).E_sub]
    simp
  have hcov := (exact_kneser_identity n M hM h2M (J r) (A.schedule r)
    hJohnson hKneser).2.1 fc fc hcenter hcenter
  have hcross : A.armCrossCov r z z =
      (orderedDisjointPairDesign n M h2M).Cov
        (fun P => fc P.1.1) (fun P => fc P.1.2) := by
    change sliceInner n M (A.groupSize_le r) fc (kneserOp n M fc) = _
    rw [(orderedDisjointPairDesign n M h2M).Cov_eq,
      orderedDisjointPair_first_E_eq_slice h2M,
      orderedDisjointPair_second_E_eq_slice h2M]
    have hc : (slice n M (by omega)).E fc = 0 := by simpa only using hcenter
    rw [hc]
    simp only [zero_mul, sub_zero]
    symm
    simpa only using orderedDisjointPair_E_eq n M h2M fc fc
  rw [hcross, hcov]
  have hnorm (k : Fin (M + 1)) :
      sliceInner n M (by omega) ((J r).proj k fc) ((J r).proj k fc) =
        sliceNorm n M (by omega) ((J r).proj k fc) ^ 2 := by
    unfold sliceNorm sliceNormSq
    symm
    exact Real.sq_sqrt (sliceInner_self_nonneg (by omega) _)
  simp_rw [hnorm]
  have hspectral := johnsonSpectralSum_abs_le (by omega : 0 < M) h4M (J r) positive
    (fun k hk => (Finset.mem_filter.mp hk).2) fc (2 * B) hfc
  rw [pow_one] at hspectral
  exact hspectral.trans (by
      have hcard : (positive.card : ℝ) ≤ (M + 1 : ℝ) := by
        exact_mod_cast (calc
          positive.card ≤ (Finset.univ : Finset (Fin (M + 1))).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          _ = M + 1 := by simp)
      have hq : 0 ≤ (((2 * M : ℕ) : ℝ) / (A.popSize r : ℝ)) := by positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard hq) (sq_nonneg _))

-- @node: thm:dense-projection-limit
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,p,rho,B), [the dense projection limit result holds](goal). -/
theorem dense_projection_limit {M : ℕ} (hM : 2 ≤ M) (p rho B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ScheduleArray M)
      (J : ∀ r, JohnsonProjections (A.popSize r) M),
      GroupCountGrowth A →
      StableTreatmentFraction A p →
      SamplingFractionLimit A rho →
      BoundedSchedule A B →
      ∀ (hJohnsonOrthogonalDecomposition_of_gate :
        ∀ r, JohnsonOrthogonalDecomposition (A.popSize r) M (J r))
        (hKneserAdjacencySpectrum_of_gate :
        ∀ r, KneserAdjacencySpectrum (A.popSize r) M),
      Tendsto (fun r =>
        (A.groups r : ℝ) * A.variance r -
          (A.leadingVariance r - rho * A.degreeOne (by omega) J r))
        atTop (nhds 0) ∧
      Tendsto (fun r =>
        (A.groups r : ℝ) * A.contrastCrossCov r + rho * A.degreeOne (by omega) J r)
        atTop (nhds 0) ∧
      Tendsto (fun r =>
        A.armCrossCov r true true / A.treatmentFraction r +
          A.armCrossCov r false false / (1 - A.treatmentFraction r))
        atTop (nhds 0) ∧
      ∀ r, |higherDegreeContribution A J r| ≤ C / (A.popSize r : ℝ) := by
  let C := 64 * (M : ℝ) ^ 2 * (M + 1 : ℝ) * B ^ 2 + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro A J hGrowth hFraction hSampling hBounded hJohnson hKneser
  have hMpos : 0 < M := by omega
  have hpop : Tendsto A.popSize atTop atTop := by
    apply tendsto_atTop_mono (fun r => ?_) hGrowth
    exact le_trans (Nat.le_mul_of_pos_left (A.groups r) hMpos) (A.grouped_le r)
  have hpopR : Tendsto (fun r => (A.popSize r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpop
  have hinv : Tendsto (fun r => ((A.popSize r : ℝ))⁻¹) atTop (nhds 0) :=
    hpopR.inv_tendsto_atTop
  have hMratio : Tendsto (fun r => (M : ℝ) / (A.popSize r : ℝ))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv :
      Tendsto (fun r => (M : ℝ) * ((A.popSize r : ℝ))⁻¹) atTop (nhds (M * 0)))
  have hden : Tendsto (fun r => 1 - (M : ℝ) / (A.popSize r : ℝ))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hMratio :
      Tendsto (fun r => 1 - (M : ℝ) / (A.popSize r : ℝ)) atTop (nhds (1 - 0)))
  let coeff : ℕ → ℝ := fun r =>
    (M : ℝ) * (A.groups r : ℝ) / ((A.popSize r : ℝ) - M)
  have hcoeff : Tendsto coeff atTop (nhds rho) := by
    have hquot := hSampling.2.2.div hden (by norm_num : (1 : ℝ) ≠ 0)
    convert hquot using 1
    · funext r
      dsimp [coeff, ScheduleArray.grouped]
      have hnpos : (A.popSize r : ℝ) ≠ 0 := by
        exact_mod_cast (lt_of_lt_of_le (Nat.mul_pos hMpos (A.groups_pos r))
          (A.grouped_le r)).ne'
      field_simp
      push_cast
      rfl
    · norm_num
  have henergyBound (r : ℕ) :
      A.degreeOne (by omega) J r ≤ (2 * B) ^ 2 := by
    apply johnsonProjection_energy_le_of_abs_le
      (le_trans (by
        have htpos := A.treated_pos r
        have htlt := A.treated_lt r
        have hg : 2 ≤ A.groups r := by omega
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left M hg) (A.grouped_le r))
    intro S
    calc
      |armTable (A.popSize r) M (A.schedule r) true S -
          armTable (A.popSize r) M (A.schedule r) false S| ≤
          |armTable (A.popSize r) M (A.schedule r) true S| +
            |armTable (A.popSize r) M (A.schedule r) false S| := abs_sub _ _
      _ ≤ B + B := add_le_add
        (armTable_abs_le_of_boundedSchedule A B hBounded r true S)
        (armTable_abs_le_of_boundedSchedule A B hBounded r false S)
      _ = 2 * B := by ring
  have henergyNonneg (r : ℕ) : 0 ≤ A.degreeOne (by omega) J r := by
    unfold ScheduleArray.degreeOne degreeOneEnergy
    exact sq_nonneg _
  have hhigher : Tendsto (higherDegreeContribution A J) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun r => abs_nonneg _)
      (fun r => higherDegreeContribution_uniform_bound hM A J B hBounded r) ?_
    · have hc : Tendsto (fun _ : ℕ =>
          64 * (M : ℝ) ^ 2 * (M + 1 : ℝ) * B ^ 2) atTop
          (nhds (64 * (M : ℝ) ^ 2 * (M + 1 : ℝ) * B ^ 2)) := tendsto_const_nhds
      convert hc.mul hinv using 1 <;> simp [div_eq_mul_inv]
  have hcoeffEnergy : Tendsto (fun r => (rho - coeff r) *
      A.degreeOne (by omega) J r) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun r => abs_nonneg _)
      (fun r => show |(rho - coeff r) * A.degreeOne (by omega) J r| ≤
          |rho - coeff r| * (2 * B) ^ 2 by
        rw [abs_mul, abs_of_nonneg (henergyNonneg r)]
        exact mul_le_mul_of_nonneg_left (henergyBound r) (abs_nonneg _)) ?_
    · have hdif : Tendsto (fun r => |rho - coeff r|) atTop (nhds 0) := by
        have hrho : Tendsto (fun _ : ℕ => rho) atTop (nhds rho) := tendsto_const_nhds
        have hzero : Tendsto (fun r => rho - coeff r) atTop (nhds 0) := by
          simpa using hrho.sub hcoeff
        exact (tendsto_zero_iff_abs_tendsto_zero _).1 hzero
      simpa using hdif.mul_const ((2 * B) ^ 2)
  have hcontrast : Tendsto (fun r =>
      (A.groups r : ℝ) * A.contrastCrossCov r +
        rho * A.degreeOne (by omega) J r) atTop (nhds 0) := by
    have heq : (fun r => (A.groups r : ℝ) * A.contrastCrossCov r +
        rho * A.degreeOne (by omega) J r) =
        fun r => (rho - coeff r) * A.degreeOne (by omega) J r +
          higherDegreeContribution A J r := by
      funext r
      rw [scaledContrastCrossCov_decomposition hM A J r (hJohnson r) (hKneser r)]
      dsimp [coeff]
      ring
    rw [heq]
    simpa using hcoeffEnergy.add hhigher
  have hcross (z : Arm) : Tendsto (fun r => A.armCrossCov r z z)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    have h4 : ∀ᶠ r in atTop, 4 * M ≤ A.popSize r :=
      (tendsto_atTop.1 hpop) (4 * M)
    refine squeeze_zero' (Filter.Eventually.of_forall fun r => abs_nonneg _)
      (h4.mono fun r hr => armCrossCov_abs_le_ge_four hM A J B hBounded r hr
        (hJohnson r) (hKneser r) z) ?_
    · have hconst : Tendsto (fun r =>
          (M + 1 : ℝ) * (((2 * M : ℕ) : ℝ) / (A.popSize r : ℝ)) *
            (2 * B) ^ 2) atTop (nhds 0) := by
        have hc : Tendsto (fun _ : ℕ =>
            (M + 1 : ℝ) * ((2 * M : ℕ) : ℝ)) atTop
            (nhds ((M + 1 : ℝ) * ((2 * M : ℕ) : ℝ))) := tendsto_const_nhds
        convert (hc.mul hinv).mul_const ((2 * B) ^ 2) using 1
        · funext r
          push_cast
          simp only [div_eq_mul_inv]
          ring
        · norm_num
      exact hconst
  have harmSum : Tendsto (fun r =>
      A.armCrossCov r true true / A.treatmentFraction r +
        A.armCrossCov r false false / (1 - A.treatmentFraction r))
      atTop (nhds 0) := by
    have hpne : p ≠ 0 := ne_of_gt hFraction.1
    have hqne : 1 - p ≠ 0 := by linarith [hFraction.2.1]
    have htrue := (hcross true).div hFraction.2.2 hpne
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have hcontrolDen : Tendsto (fun r => 1 - A.treatmentFraction r)
        atTop (nhds (1 - p)) := hone.sub hFraction.2.2
    have hfalse := (hcross false).div hcontrolDen hqne
    simpa using htrue.add hfalse
  have hvariance : Tendsto (fun r =>
      (A.groups r : ℝ) * A.variance r -
        (A.leadingVariance r - rho * A.degreeOne (by omega) J r))
      atTop (nhds 0) := by
    have htreated : ∀ᶠ r in atTop, 2 ≤ A.treated r := by
      have hlower := (tendsto_order.1 hFraction.2.2).1 (p / 2) (by linarith [hFraction.1])
      have hGreal : Tendsto (fun r => (A.groups r : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hGrowth
      have hGlarge := hGreal.eventually_gt_atTop (4 / p)
      filter_upwards [hlower, hGlarge] with r hfr hGr
      by_contra ht
      have htpos := A.treated_pos r
      have htone : A.treated r = 1 := by omega
      have hGposR : (0 : ℝ) < A.groups r := by exact_mod_cast A.groups_pos r
      unfold ScheduleArray.treatmentFraction pFrac at hfr
      rw [htone] at hfr
      norm_num at hfr
      have hpG : 4 < p * (A.groups r : ℝ) := by
        simpa [mul_comm] using (div_lt_iff₀ hFraction.1).1 hGr
      have : p * (A.groups r : ℝ) < 2 := by
        have hh : (p / 2) * (A.groups r : ℝ) < 1 := by
          apply (lt_div_iff₀ hGposR).1
          simpa [one_div] using hfr
        linarith
      linarith
    have hcontrols : ∀ᶠ r in atTop, 2 ≤ A.controls r := by
      have hupper := (tendsto_order.1 hFraction.2.2).2 ((1 + p) / 2)
        (by linarith [hFraction.2.1])
      have hGreal : Tendsto (fun r => (A.groups r : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hGrowth
      have hGlarge := hGreal.eventually_gt_atTop (4 / (1 - p))
      filter_upwards [hupper, hGlarge] with r hfr hGr
      by_contra hc
      have hcpos : 0 < A.controls r := by
        unfold ScheduleArray.controls
        have htlt := A.treated_lt r
        omega
      have hcone : A.controls r = 1 := by
        omega
      have hGposR : (0 : ℝ) < A.groups r := by exact_mod_cast A.groups_pos r
      have hcast : (A.treated r : ℝ) = (A.groups r : ℝ) - 1 := by
        have htNat : A.treated r = A.groups r - 1 := by
          unfold ScheduleArray.controls at hcone
          omega
        rw [htNat, Nat.cast_sub (A.groups_pos r)]
        norm_num
      unfold ScheduleArray.treatmentFraction pFrac at hfr
      rw [hcast] at hfr
      have hqG : 4 < (1 - p) * (A.groups r : ℝ) := by
        simpa [mul_comm] using
          (div_lt_iff₀ (by linarith [hFraction.2.1] : 0 < 1 - p)).1 hGr
      have : (1 - p) * (A.groups r : ℝ) < 2 := by
        have hh := (div_lt_iff₀ hGposR).1 hfr
        field_simp at hh
        linarith
      linarith
    have htarget : Tendsto (fun r =>
        ((A.groups r : ℝ) * A.contrastCrossCov r +
          rho * A.degreeOne (by omega) J r) -
        (A.armCrossCov r true true / A.treatmentFraction r +
          A.armCrossCov r false false / (1 - A.treatmentFraction r)))
        atTop (nhds 0) := by
      simpa using hcontrast.sub harmSum
    apply Tendsto.congr' _ htarget
    filter_upwards [htreated, hcontrols] with r ht hc
    have hex := (exact_pame_variance (A.popSize r) M (A.groups r) (A.treated r)
      (A.grouped_le r) hM ht (by simpa [ScheduleArray.controls] using hc)
      (A.schedule r)).2.1
    change A.variance r = _ at hex
    rw [hex]
    unfold ScheduleArray.leadingVariance ScheduleArray.treatmentFraction
      ScheduleArray.armCrossCov ScheduleArray.contrastCrossCov
    have hGr : (A.groups r : ℝ) ≠ 0 := by exact_mod_cast (A.groups_pos r).ne'
    have htR : (A.treated r : ℝ) ≠ 0 := by exact_mod_cast (A.treated_pos r).ne'
    have hcR : ((A.groups r - A.treated r : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (by
        simpa [ScheduleArray.controls] using (show A.controls r ≠ 0 by omega))
    rw [Nat.cast_sub (A.treated_le r)]
    dsimp [pFrac]
    field_simp
    ring
  refine ⟨hvariance, hcontrast, harmSum, ?_⟩
  intro r
  exact (higherDegreeContribution_uniform_bound hM A J B hBounded r).trans (by
    have hnpos : (0 : ℝ) < A.popSize r := by
      exact_mod_cast lt_of_lt_of_le (Nat.mul_pos hMpos (A.groups_pos r)) (A.grouped_le r)
    apply (div_le_div_iff_of_pos_right hnpos).2
    dsimp [C]
    linarith)

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

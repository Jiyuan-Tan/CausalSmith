import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.TDenseProjectionLimit

open scoped BigOperators Topology
open Filter Finset

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased

-- @node: tableSchedule
/-- For [the stated inputs](hyp:n,M,z,f), [table schedule](goal) is defined by the formula below. -/
def tableSchedule {n M : ℕ} (z : Arm) (f : Omega n M → ℝ) : PotentialOutcome n M :=
  fun S _ a => if a = z then f S else 0

-- @node: armTable_tableSchedule_same
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hM,z,f,S), [the arm table table schedule same result holds](goal). -/
lemma armTable_tableSchedule_same {n M : ℕ} (hM : 0 < M) (z : Arm)
    (f : Omega n M → ℝ) (S : Omega n M) :
    armTable n M (tableSchedule z f) z S = f S := by
  unfold armTable tableSchedule
  simp [S.2, Nat.cast_ne_zero.mpr hM.ne']

-- @node: armTable_tableSchedule_ne
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,z,a,hza,f,S), [the arm table table schedule ne result holds](goal). -/
lemma armTable_tableSchedule_ne {n M : ℕ} (z a : Arm) (hza : a ≠ z)
    (f : Omega n M → ℝ) (S : Omega n M) :
    armTable n M (tableSchedule z f) a S = 0 := by
  unfold armTable tableSchedule
  simp [hza]

-- @node: selectedMean
/-- For [the stated inputs](hyp:n,M,G,G1,f,w,z), [selected mean](goal) is defined by the formula below. -/
noncomputable def selectedMean {n M G G1 : ℕ} (f : Omega n M → ℝ)
    (w : PartitionTuple n M G × TreatmentSpace G G1) (z : Arm) : ℝ :=
  if z then (∑ g ∈ w.2.1, f (w.1.1 g)) / (G1 : ℝ)
  else (∑ g ∈ (Finset.univ.filter fun g : Fin G => g ∉ w.2.1), f (w.1.1 g)) /
    ((G - G1 : ℕ) : ℝ)

-- @node: pameHat_tableSchedule_true
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,hM,hG1pos,hG1lt,f,w), [the pame hat table schedule true result holds](goal). -/
lemma pameHat_tableSchedule_true {n M G G1 : ℕ} (hM : 0 < M)
    (hG1pos : 0 < G1) (hG1lt : G1 < G) (f : Omega n M → ℝ)
    (w : PartitionTuple n M G × TreatmentSpace G G1) :
    pameHat (tableSchedule true f) hG1pos hG1lt w = selectedMean f w true := by
  simp [pameHat, selectedMean,
    armTable_tableSchedule_same hM, armTable_tableSchedule_ne]

-- @node: pameHat_tableSchedule_false
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,hM,hG1pos,hG1lt,f,w), [the pame hat table schedule false result holds](goal). -/
lemma pameHat_tableSchedule_false {n M G G1 : ℕ} (hM : 0 < M)
    (hG1pos : 0 < G1) (hG1lt : G1 < G) (f : Omega n M → ℝ)
    (w : PartitionTuple n M G × TreatmentSpace G G1) :
    pameHat (tableSchedule false f) hG1pos hG1lt w = -selectedMean f w false := by
  simp [pameHat, selectedMean,
    armTable_tableSchedule_same hM, armTable_tableSchedule_ne]

-- @node: pame_tableSchedule_true
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMpos,hMn,f), [the pame table schedule true result holds](goal). -/
lemma pame_tableSchedule_true {n M : ℕ} (hMpos : 0 < M) (hMn : M ≤ n)
    (f : Omega n M → ℝ) :
    pame n M hMn (tableSchedule true f) = (slice n M hMn).E f := by
  unfold pame
  rw [show armTable n M (tableSchedule true f) true = f by
        funext S; exact armTable_tableSchedule_same hMpos true f S,
    show armTable n M (tableSchedule true f) false = fun _ => 0 by
        funext S; exact armTable_tableSchedule_ne true false (by decide) f S]
  simp

-- @node: pame_tableSchedule_false
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMpos,hMn,f), [the pame table schedule false result holds](goal). -/
lemma pame_tableSchedule_false {n M : ℕ} (hMpos : 0 < M) (hMn : M ≤ n)
    (f : Omega n M → ℝ) :
    pame n M hMn (tableSchedule false f) = -(slice n M hMn).E f := by
  unfold pame
  rw [show armTable n M (tableSchedule false f) true = fun _ => 0 by
        funext S; exact armTable_tableSchedule_ne false true (by decide) f S,
    show armTable n M (tableSchedule false f) false = f by
        funext S; exact armTable_tableSchedule_same hMpos false f S]
  simp

-- @node: armVar_tableSchedule_same
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMpos,hMn,z,f), [the stated variance result holds](goal). -/
lemma armVar_tableSchedule_same {n M : ℕ} (hMpos : 0 < M) (hMn : M ≤ n)
    (z : Arm) (f : Omega n M → ℝ) :
    armVar n M hMn (tableSchedule z f) z = (slice n M hMn).Var f := by
  unfold armVar
  apply (slice n M hMn).Var_congr
  exact armTable_tableSchedule_same hMpos z f

-- @node: armVar_tableSchedule_ne
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMn,z,a,hza,f), [the stated variance result holds](goal). -/
lemma armVar_tableSchedule_ne {n M : ℕ} (hMn : M ≤ n)
    (z a : Arm) (hza : a ≠ z) (f : Omega n M → ℝ) :
    armVar n M hMn (tableSchedule z f) a = 0 := by
  unfold armVar
  rw [show armTable n M (tableSchedule z f) a = fun _ => 0 by
    funext S; exact armTable_tableSchedule_ne z a hza f S]
  simp [FiniteDesign.Var_eq]

-- @node: crossCov_tableSchedule_same
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMpos,hMn,z,f), [the cross cov table schedule same result holds](goal). -/
lemma crossCov_tableSchedule_same {n M : ℕ} (hMpos : 0 < M) (hMn : M ≤ n)
    (z : Arm) (f : Omega n M → ℝ) :
    crossCov n M hMn (tableSchedule z f) z z =
      sliceInner n M hMn (fun S => f S - (slice n M hMn).E f)
        (kneserOp n M (fun S => f S - (slice n M hMn).E f)) := by
  unfold crossCov armTableCentered
  rw [show armTable n M (tableSchedule z f) z = f by
    funext S; exact armTable_tableSchedule_same hMpos z f S]

-- @node: crossCov_tableSchedule_left_ne
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMn,z,a,b,haz,f), [the cross cov table schedule left ne result holds](goal). -/
lemma crossCov_tableSchedule_left_ne {n M : ℕ} (hMn : M ≤ n)
    (z a b : Arm) (haz : a ≠ z) (f : Omega n M → ℝ) :
    crossCov n M hMn (tableSchedule z f) a b = 0 := by
  unfold crossCov armTableCentered
  rw [show armTable n M (tableSchedule z f) a = fun _ => 0 by
    funext S; exact armTable_tableSchedule_ne z a haz f S]
  simp [sliceInner, FiniteDesign.E]

-- @node: crossCov_tableSchedule_right_ne
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMn,z,a,b,hbz,f), [the cross cov table schedule right ne result holds](goal). -/
lemma crossCov_tableSchedule_right_ne {n M : ℕ} (hMn : M ≤ n)
    (z a b : Arm) (hbz : b ≠ z) (f : Omega n M → ℝ) :
    crossCov n M hMn (tableSchedule z f) a b = 0 := by
  unfold crossCov armTableCentered
  rw [show armTable n M (tableSchedule z f) b = fun _ => 0 by
    funext S; exact armTable_tableSchedule_ne z b hbz f S]
  simp [kneserOp, kneserAdjacency, sliceInner, FiniteDesign.E]

-- @node: selectedMean_variance_true
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,hMG,hM,hG1,hG0,f), [the stated variance result holds](goal). -/
lemma selectedMean_variance_true {n M G G1 : ℕ} (hMG : M * G ≤ n)
    (hM : 2 ≤ M) (hG1 : 2 ≤ G1) (hG0 : 2 ≤ G - G1)
    (f : Omega n M → ℝ) :
    (randomPartitionDesign n M G G1 hMG (by omega)).Var
        (fun w => selectedMean f w true) =
      (slice n M (le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)).Var f / (G1 : ℝ) +
        (1 - 1 / (G1 : ℝ)) *
          sliceInner n M (le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)
            (fun S => f S -
              (slice n M (le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)).E f)
            (kneserOp n M (fun S => f S -
              (slice n M (le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)).E f)) := by
  let hG1pos : 0 < G1 := by omega
  let hG1lt : G1 < G := by omega
  let hMn : M ≤ n := le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG
  let C := sliceInner n M hMn (fun S => f S - (slice n M hMn).E f)
    (kneserOp n M (fun S => f S - (slice n M hMn).E f))
  have hex := (exact_pame_variance n M G G1 hMG hM hG1 hG0
    (tableSchedule true f)).2.1
  have hv : (randomPartitionDesign n M G G1 hMG (by omega)).Var
      (pameHat (tableSchedule true f) hG1pos hG1lt) =
      indepGroupVar n M G G1 hMn hG1pos hG1lt (tableSchedule true f) / (G : ℝ) +
        crossCovContrast n M hMn (tableSchedule true f) -
        crossCov n M hMn (tableSchedule true f) true true / (G1 : ℝ) -
        crossCov n M hMn (tableSchedule true f) false false / ((G - G1 : ℕ) : ℝ) := by
    simpa [sigmaSq] using hex
  rw [show (randomPartitionDesign n M G G1 hMG (by omega)).Var
      (fun w => selectedMean f w true) =
      (randomPartitionDesign n M G G1 hMG (by omega)).Var
        (pameHat (tableSchedule true f) hG1pos hG1lt) by
      apply (randomPartitionDesign n M G G1 hMG (by omega)).Var_congr
      intro w
      exact (pameHat_tableSchedule_true (by omega) hG1pos hG1lt f w).symm,
    hv]
  unfold indepGroupVar crossCovContrast pFrac
  rw [armVar_tableSchedule_same (by omega) hMn,
    armVar_tableSchedule_ne hMn true false (by decide),
    crossCov_tableSchedule_same (by omega) hMn,
    crossCov_tableSchedule_left_ne hMn true false false (by decide),
    crossCov_tableSchedule_right_ne hMn true true false (by decide)]
  have hGr : (G : ℝ) ≠ 0 := by exact_mod_cast (by omega : G ≠ 0)
  have hG1r : (G1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : G1 ≠ 0)
  field_simp
  ring

-- @node: selectedMean_variance_false
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,hMG,hM,hG1,hG0,f), [the stated variance result holds](goal). -/
lemma selectedMean_variance_false {n M G G1 : ℕ} (hMG : M * G ≤ n)
    (hM : 2 ≤ M) (hG1 : 2 ≤ G1) (hG0 : 2 ≤ G - G1)
    (f : Omega n M → ℝ) :
    (randomPartitionDesign n M G G1 hMG (by omega)).Var
        (fun w => selectedMean f w false) =
      (slice n M (le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)).Var f /
          ((G - G1 : ℕ) : ℝ) +
        (1 - 1 / ((G - G1 : ℕ) : ℝ)) *
          sliceInner n M (le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)
            (fun S => f S -
              (slice n M (le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)).E f)
            (kneserOp n M (fun S => f S -
              (slice n M (le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)).E f)) := by
  let hG1pos : 0 < G1 := by omega
  let hG1lt : G1 < G := by omega
  let hMn : M ≤ n := le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG
  have hex := (exact_pame_variance n M G G1 hMG hM hG1 hG0
    (tableSchedule false f)).2.1
  have hv : (randomPartitionDesign n M G G1 hMG (by omega)).Var
      (pameHat (tableSchedule false f) hG1pos hG1lt) =
      indepGroupVar n M G G1 hMn hG1pos hG1lt (tableSchedule false f) / (G : ℝ) +
        crossCovContrast n M hMn (tableSchedule false f) -
        crossCov n M hMn (tableSchedule false f) true true / (G1 : ℝ) -
        crossCov n M hMn (tableSchedule false f) false false / ((G - G1 : ℕ) : ℝ) := by
    simpa [sigmaSq] using hex
  rw [show (randomPartitionDesign n M G G1 hMG (by omega)).Var
      (fun w => selectedMean f w false) =
      (randomPartitionDesign n M G G1 hMG (by omega)).Var
        (pameHat (tableSchedule false f) hG1pos hG1lt) by
      rw [FiniteDesign.Var_eq, FiniteDesign.Var_eq]
      have hp : pameHat (tableSchedule false f) hG1pos hG1lt =
          fun w => -selectedMean f w false := by
        funext w
        exact pameHat_tableSchedule_false (by omega) hG1pos hG1lt f w
      rw [hp, (randomPartitionDesign n M G G1 hMG (by omega)).E_neg]
      congr 1
      · apply (randomPartitionDesign n M G G1 hMG (by omega)).E_congr
        intro w
        ring
      · ring,
    hv]
  unfold indepGroupVar crossCovContrast pFrac
  rw [armVar_tableSchedule_same (by omega) hMn,
    armVar_tableSchedule_ne hMn false true (by decide),
    crossCov_tableSchedule_same (by omega) hMn,
    crossCov_tableSchedule_left_ne hMn false true true (by decide),
    crossCov_tableSchedule_left_ne hMn false true false (by decide)]
  have hGr : (G : ℝ) ≠ 0 := by exact_mod_cast (by omega : G ≠ 0)
  have hG0r : ((G - G1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : G - G1 ≠ 0)
  rw [Nat.cast_sub (by omega : G1 ≤ G)]
  field_simp
  ring

-- @node: treated_tendsto_atTop
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,A,p,hGrowth,hFraction), [the indicated sequence converges to its stated limit](goal). -/
lemma treated_tendsto_atTop {M : ℕ} (A : ScheduleArray M) (p : ℝ)
    (hGrowth : GroupCountGrowth A) (hFraction : StableTreatmentFraction A p) :
    Tendsto A.treated atTop atTop := by
  rw [← tendsto_natCast_atTop_iff (R := ℝ)]
  have hG : Tendsto (fun r => (A.groups r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hGrowth
  have hprod := hFraction.2.2.pos_mul_atTop hFraction.1 hG
  apply Tendsto.congr' _ hprod
  filter_upwards [] with r
  unfold ScheduleArray.treatmentFraction pFrac
  have hGr : (A.groups r : ℝ) ≠ 0 := by exact_mod_cast (A.groups_pos r).ne'
  field_simp

-- @node: controls_tendsto_atTop
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,A,p,hGrowth,hFraction), [the indicated sequence converges to its stated limit](goal). -/
lemma controls_tendsto_atTop {M : ℕ} (A : ScheduleArray M) (p : ℝ)
    (hGrowth : GroupCountGrowth A) (hFraction : StableTreatmentFraction A p) :
    Tendsto A.controls atTop atTop := by
  rw [← tendsto_natCast_atTop_iff (R := ℝ)]
  have hG : Tendsto (fun r => (A.groups r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hGrowth
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hden : Tendsto (fun r => 1 - A.treatmentFraction r) atTop (nhds (1 - p)) :=
    hone.sub hFraction.2.2
  have hprod := hden.pos_mul_atTop (by linarith [hFraction.2.1]) hG
  apply Tendsto.congr' _ hprod
  filter_upwards [] with r
  unfold ScheduleArray.controls ScheduleArray.treatmentFraction pFrac
  rw [Nat.cast_sub (A.treated_le r)]
  have hGr : (A.groups r : ℝ) ≠ 0 := by exact_mod_cast (A.groups_pos r).ne'
  field_simp

-- @node: ScheduleArray.withTable
/-- For [the stated inputs](hyp:M,A,z,f), [with table](goal) is defined by the formula below. -/
def ScheduleArray.withTable {M : ℕ} (A : ScheduleArray M) (z : Arm)
    (f : ∀ r, Omega (A.popSize r) M → ℝ) : ScheduleArray M where
  groupSize_ge_two := A.groupSize_ge_two
  popSize := A.popSize
  groups := A.groups
  treated := A.treated
  groups_pos := A.groups_pos
  grouped_le := A.grouped_le
  treated_pos := A.treated_pos
  treated_lt := A.treated_lt
  treated_le := A.treated_le
  schedule := fun r => tableSchedule z (f r)

-- @node: withTable_bounded
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,A,z,f,K,hK,hf), [the with table bounded result holds](goal). -/
lemma withTable_bounded {M : ℕ} (A : ScheduleArray M) (z : Arm)
    (f : ∀ r, Omega (A.popSize r) M → ℝ) (K : ℝ) (hK : 0 < K)
    (hf : ∀ r S, |f r S| ≤ K) : BoundedSchedule (A.withTable z f) K := by
  refine ⟨hK, ?_⟩
  intro r S i a
  change |if a = z then f r S else 0| ≤ K
  split_ifs
  · exact hf r S
  · simpa using hK.le

-- @node: sliceVar_le_sq_of_abs_le
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,hMn,f,K,hf), [the stated variance result holds](goal). -/
lemma sliceVar_le_sq_of_abs_le {n M : ℕ} (hMn : M ≤ n)
    (f : Omega n M → ℝ) (K : ℝ) (hf : ∀ S, |f S| ≤ K) :
    (slice n M hMn).Var f ≤ K ^ 2 := by
  rw [FiniteDesign.Var_eq]
  calc
    (slice n M hMn).E (fun S => f S ^ 2) - ((slice n M hMn).E f) ^ 2 ≤
        (slice n M hMn).E (fun S => f S ^ 2) := sub_le_self _ (sq_nonneg _)
    _ = sliceInner n M hMn f f := by
      unfold sliceInner
      apply (slice n M hMn).E_congr
      intro S
      ring
    _ ≤ K ^ 2 := sliceInner_self_le_sq_of_abs_le hMn f K hf

-- @node: selectedMean_expectation_true
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,hMG,hM,hG1,hG0,f), [the stated expectation identity holds](goal). -/
lemma selectedMean_expectation_true {n M G G1 : ℕ} (hMG : M * G ≤ n)
    (hM : 2 ≤ M) (hG1 : 2 ≤ G1) (hG0 : 2 ≤ G - G1)
    (f : Omega n M → ℝ) :
    (randomPartitionDesign n M G G1 hMG (by omega)).E
      (fun w => selectedMean f w true) =
        (slice n M (le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)).E f := by
  let hG1pos : 0 < G1 := by omega
  let hG1lt : G1 < G := by omega
  have hex := (exact_pame_variance n M G G1 hMG hM hG1 hG0
    (tableSchedule true f)).1
  rw [show (fun w => selectedMean f w true) =
      pameHat (tableSchedule true f) hG1pos hG1lt by
        funext w; exact (pameHat_tableSchedule_true (by omega) hG1pos hG1lt f w).symm,
    hex]
  exact pame_tableSchedule_true (by omega)
    (le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG) f

-- @node: selectedMean_expectation_false
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,hMG,hM,hG1,hG0,f), [the stated expectation identity holds](goal). -/
lemma selectedMean_expectation_false {n M G G1 : ℕ} (hMG : M * G ≤ n)
    (hM : 2 ≤ M) (hG1 : 2 ≤ G1) (hG0 : 2 ≤ G - G1)
    (f : Omega n M → ℝ) :
    (randomPartitionDesign n M G G1 hMG (by omega)).E
      (fun w => selectedMean f w false) =
        (slice n M (le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG)).E f := by
  let hG1pos : 0 < G1 := by omega
  let hG1lt : G1 < G := by omega
  have hex := (exact_pame_variance n M G G1 hMG hM hG1 hG0
    (tableSchedule false f)).1
  rw [pame_tableSchedule_false (by omega)
      (le_trans (Nat.le_mul_of_pos_right M (by omega)) hMG) f] at hex
  have hp : pameHat (tableSchedule false f) hG1pos hG1lt =
      fun w => -selectedMean f w false := by
    funext w
    exact pameHat_tableSchedule_false (by omega) hG1pos hG1lt f w
  rw [hp, (randomPartitionDesign n M G G1 hMG (by omega)).E_neg] at hex
  linarith

-- @node: selectedMean_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,A,p,J,hGrowth,hFraction,hJohnson,hKneser,z,f,K,hK,hf), [the indicated sequence converges to its stated limit](goal). -/
lemma selectedMean_tendstoInProb {M : ℕ} (hM : 2 ≤ M) (A : ScheduleArray M)
    (p : ℝ) (J : ∀ r, JohnsonProjections (A.popSize r) M)
    (hGrowth : GroupCountGrowth A) (hFraction : StableTreatmentFraction A p)
    (hJohnson : ∀ r, JohnsonOrthogonalDecomposition (A.popSize r) M (J r))
    (hKneser : ∀ r, KneserAdjacencySpectrum (A.popSize r) M)
    (z : Arm) (f : ∀ r, Omega (A.popSize r) M → ℝ) (K : ℝ) (hK : 0 < K)
    (hf : ∀ r S, |f r S| ≤ K) :
    FiniteDesign.TendstoInProb A.design
      (fun r w => selectedMean (f r) w z)
      (fun r => (slice (A.popSize r) M (A.groupSize_le r)).E (f r)) := by
  have hpop : Tendsto A.popSize atTop atTop := by
    apply tendsto_atTop_mono (fun r => ?_) hGrowth
    exact le_trans (Nat.le_mul_of_pos_left (A.groups r) (by omega : 0 < M))
      (A.grouped_le r)
  have hpopR : Tendsto (fun r => (A.popSize r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpop
  have hinvPop : Tendsto (fun r => ((A.popSize r : ℝ))⁻¹) atTop (nhds 0) :=
    hpopR.inv_tendsto_atTop
  have h4 : ∀ᶠ r in atTop, 4 * M ≤ A.popSize r :=
    (tendsto_atTop.1 hpop) (4 * M)
  let A' := A.withTable z f
  have hA'bounded : BoundedSchedule A' K := withTable_bounded A z f K hK hf
  have hcross : Tendsto (fun r =>
      sliceInner (A.popSize r) M (A.groupSize_le r)
        (fun S => f r S - (slice (A.popSize r) M (A.groupSize_le r)).E (f r))
        (kneserOp (A.popSize r) M
          (fun S => f r S - (slice (A.popSize r) M (A.groupSize_le r)).E (f r))))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (g := fun r =>
      (M + 1 : ℝ) * (((2 * M : ℕ) : ℝ) / (A.popSize r : ℝ)) * (2 * K) ^ 2)
      (Filter.Eventually.of_forall fun r => abs_nonneg _) ?_ ?_
    · filter_upwards [h4] with r hr
      have hb := armCrossCov_abs_le_ge_four hM A' J K hA'bounded r hr
        (hJohnson r) (hKneser r) z
      dsimp [A', ScheduleArray.withTable, ScheduleArray.armCrossCov] at hb
      rw [crossCov_tableSchedule_same (by omega) (A.groupSize_le r)] at hb
      exact hb
    · have hc : Tendsto (fun _ : ℕ =>
          (M + 1 : ℝ) * ((2 * M : ℕ) : ℝ) * (2 * K) ^ 2) atTop
          (nhds ((M + 1 : ℝ) * ((2 * M : ℕ) : ℝ) * (2 * K) ^ 2)) :=
        tendsto_const_nhds
      convert hc.mul hinvPop using 1
      · funext r
        simp only [div_eq_mul_inv]
        ring
      · norm_num
  have htreat := treated_tendsto_atTop A p hGrowth hFraction
  have hcontrol := controls_tendsto_atTop A p hGrowth hFraction
  have htreatInv : Tendsto (fun r => ((A.treated r : ℝ))⁻¹) atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop.comp htreat).inv_tendsto_atTop
  have hcontrolInv : Tendsto (fun r => ((A.controls r : ℝ))⁻¹) atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop.comp hcontrol).inv_tendsto_atTop
  have hboth : ∀ᶠ r in atTop, 2 ≤ A.treated r ∧ 2 ≤ A.controls r := by
    filter_upwards [(tendsto_atTop.1 htreat) 2, (tendsto_atTop.1 hcontrol) 2] with r ht hc
    exact ⟨ht, hc⟩
  have hvar : Tendsto (fun r => (A.design r).Var
      (fun w => selectedMean (f r) w z)) atTop (nhds 0) := by
    have harmInv : Tendsto (fun r => ((armCount (A.groups r) (A.treated r) z : ℕ) : ℝ)⁻¹)
        atTop (nhds 0) := by
      cases z <;> simp only [armCount]
      · simpa [ScheduleArray.controls] using hcontrolInv
      · exact htreatInv
    have hvarPart : Tendsto (fun r =>
        (slice (A.popSize r) M (A.groupSize_le r)).Var (f r) /
          (armCount (A.groups r) (A.treated r) z : ℝ)) atTop (nhds 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero (g := fun r => K ^ 2 *
        ((armCount (A.groups r) (A.treated r) z : ℝ))⁻¹)
        (fun r => abs_nonneg _) (fun r => ?_) ?_
      · have hcount : 0 < armCount (A.groups r) (A.treated r) z := by
          cases z
          · change 0 < A.groups r - A.treated r
            exact Nat.sub_pos_of_lt (A.treated_lt r)
          · simp [armCount, A.treated_pos r]
        change |(slice (A.popSize r) M (A.groupSize_le r)).Var (f r) /
          (armCount (A.groups r) (A.treated r) z : ℝ)| ≤ _
        rw [abs_of_nonneg (div_nonneg ((slice (A.popSize r) M
          (A.groupSize_le r)).Var_nonneg _) (by positivity)), div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right
          (sliceVar_le_sq_of_abs_le (A.groupSize_le r) (f r) K (hf r)) (by positivity)
      · have hc : Tendsto (fun _ : ℕ => K ^ 2) atTop (nhds (K ^ 2)) :=
          tendsto_const_nhds
        simpa using hc.mul harmInv
    have hfactor : Tendsto (fun r =>
        1 - 1 / (armCount (A.groups r) (A.treated r) z : ℝ)) atTop (nhds 1) := by
      simpa [div_eq_mul_inv] using tendsto_const_nhds.sub harmInv
    have hformula : ∀ᶠ r in atTop,
        (A.design r).Var (fun w => selectedMean (f r) w z) =
          (slice (A.popSize r) M (A.groupSize_le r)).Var (f r) /
              (armCount (A.groups r) (A.treated r) z : ℝ) +
            (1 - 1 / (armCount (A.groups r) (A.treated r) z : ℝ)) *
              sliceInner (A.popSize r) M (A.groupSize_le r)
                (fun S => f r S - (slice (A.popSize r) M (A.groupSize_le r)).E (f r))
                (kneserOp (A.popSize r) M
                  (fun S => f r S -
                    (slice (A.popSize r) M (A.groupSize_le r)).E (f r))) := by
      filter_upwards [hboth] with r hr
      unfold ScheduleArray.design
      cases z
      · exact selectedMean_variance_false (A.grouped_le r) hM hr.1
          (by simpa [ScheduleArray.controls] using hr.2) (f r)
      · exact selectedMean_variance_true (A.grouped_le r) hM hr.1
          (by simpa [ScheduleArray.controls] using hr.2) (f r)
    apply Tendsto.congr' (hformula.mono fun _ hr => hr.symm)
    simpa using hvarPart.add (hfactor.mul hcross)
  have hbase := FiniteDesign.tendstoInProb_of_var A.design
    (fun r w => selectedMean (f r) w z) hvar
  intro ε hε
  have htail := hbase ε hε
  apply Tendsto.congr' _ htail
  filter_upwards [hboth] with r hr
  apply (A.design r).Pr_congr
  intro w
  cases z
  · simp only [show (A.design r).E (fun w => selectedMean (f r) w false) =
        (slice (A.popSize r) M (A.groupSize_le r)).E (f r) by
      exact selectedMean_expectation_false (A.grouped_le r) hM hr.1
        (by simpa [ScheduleArray.controls] using hr.2) (f r)]
  · simp only [show (A.design r).E (fun w => selectedMean (f r) w true) =
        (slice (A.popSize r) M (A.groupSize_le r)).E (f r) by
      exact selectedMean_expectation_true (A.grouped_le r) hM hr.1
        (by simpa [ScheduleArray.controls] using hr.2) (f r)]

-- @node: sampleVariance_finset_eq
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:s,m,hcard,hm,x), [the stated variance result holds](goal). -/
lemma sampleVariance_finset_eq {α : Type*} [Fintype α] (s : Finset α) (m : ℕ)
    (hcard : s.card = m) (hm : 2 ≤ m) (x : α → ℝ) :
    (∑ i ∈ s, (x i - (∑ j ∈ s, x j) / (m : ℝ)) ^ 2) / ((m - 1 : ℕ) : ℝ) =
      (m : ℝ) / ((m - 1 : ℕ) : ℝ) *
        ((∑ i ∈ s, x i ^ 2) / (m : ℝ) - ((∑ j ∈ s, x j) / (m : ℝ)) ^ 2) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm1R : ((m - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : m - 1 ≠ 0)
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hlin : (∑ i ∈ s, 2 * x i * ((∑ j ∈ s, x j) / (m : ℝ))) =
      2 * (∑ i ∈ s, x i) * ((∑ j ∈ s, x j) / (m : ℝ)) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [hlin]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  field_simp
  ring

-- @node: realizedArmSet_card
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,w,z), [the stated cardinality formula holds](goal). -/
lemma realizedArmSet_card {n M G G1 : ℕ}
    (w : PartitionTuple n M G × TreatmentSpace G G1) (z : Arm) :
    (realizedArmSet w z).card = armCount G G1 z := by
  cases z
  · change (Finset.univ \ w.2.1).card = G - G1
    rw [Finset.card_sdiff]
    simp [w.2.2]
  · exact w.2.2

-- @node: selectedMean_eq_realized
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,f,w,z), [the stated equality holds](goal). -/
lemma selectedMean_eq_realized {n M G G1 : ℕ} (f : Omega n M → ℝ)
    (w : PartitionTuple n M G × TreatmentSpace G G1) (z : Arm) :
    selectedMean f w z =
      (∑ i ∈ realizedArmSet w z, f (w.1.1 i)) / (armCount G G1 z : ℝ) := by
  cases z
  · unfold selectedMean realizedArmSet armCount
    simp only [Bool.false_eq_true, ↓reduceIte]
    congr 1
    apply Finset.sum_congr
    · ext i
      simp
    · intro i hi
      rfl
  · rfl

-- @node: selectedMean_abs_le
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,f,w,z,K,hf,hcount), [the stated bound holds](goal). -/
lemma selectedMean_abs_le {n M G G1 : ℕ} (f : Omega n M → ℝ)
    (w : PartitionTuple n M G × TreatmentSpace G G1) (z : Arm)
    (K : ℝ) (hf : ∀ S, |f S| ≤ K) (hcount : 0 < armCount G G1 z) :
    |selectedMean f w z| ≤ K := by
  rw [selectedMean_eq_realized, abs_div, abs_of_nonneg (by positivity :
    0 ≤ (armCount G G1 z : ℝ))]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < armCount G G1 z)).2
  calc
    |∑ i ∈ realizedArmSet w z, f (w.1.1 i)| ≤
        ∑ i ∈ realizedArmSet w z, |f (w.1.1 i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ realizedArmSet w z, K := by
      gcongr with i hi
      exact hf _
    _ = (armCount G G1 z : ℝ) * K := by
      rw [Finset.sum_const, nsmul_eq_mul, realizedArmSet_card]
    _ = K * (armCount G G1 z : ℝ) := by ring

-- @node: armSampleVar_eq_selectedMoments
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:n,M,G,G1,Y,w,z,hArm), [the stated variance result holds](goal). -/
lemma armSampleVar_eq_selectedMoments {n M G G1 : ℕ} (Y : PotentialOutcome n M)
    (w : PartitionTuple n M G × TreatmentSpace G G1) (z : Arm)
    (hArm : 2 ≤ armCount G G1 z) :
    armSampleVar Y w z hArm =
      (armCount G G1 z : ℝ) / ((armCount G G1 z - 1 : ℕ) : ℝ) *
        (selectedMean (fun S => armTable n M Y z S ^ 2) w z -
          selectedMean (armTable n M Y z) w z ^ 2) := by
  have hselected (g : Omega n M → ℝ) : selectedMean g w z =
      (∑ i ∈ realizedArmSet w z, g (w.1.1 i)) / (armCount G G1 z : ℝ) :=
    selectedMean_eq_realized g w z
  have hobs (g : Fin G) (hg : g ∈ realizedArmSet w z) :
      obsGroupMean Y w g = armTable n M Y z (w.1.1 g) := by
    cases z
    · simp only [realizedArmSet, Bool.false_eq_true, ↓reduceIte,
        Finset.mem_sdiff, Finset.mem_univ, true_and] at hg
      simp [obsGroupMean, hg]
    · simp only [realizedArmSet, ↓reduceIte] at hg
      simp [obsGroupMean, hg]
  have hmean : armObsMean Y w z = selectedMean (armTable n M Y z) w z := by
    unfold armObsMean
    rw [hselected]
    congr 1
    apply Finset.sum_congr rfl
    intro g hg
    exact hobs g hg
  unfold armSampleVar
  rw [hmean]
  have hcard := realizedArmSet_card w z
  have halg := sampleVariance_finset_eq (realizedArmSet w z) (armCount G G1 z)
    hcard hArm (fun g => armTable n M Y z (w.1.1 g))
  have hsum : (∑ g ∈ realizedArmSet w z,
      (obsGroupMean Y w g - selectedMean (armTable n M Y z) w z) ^ 2) =
      ∑ g ∈ realizedArmSet w z,
        (armTable n M Y z (w.1.1 g) -
          (∑ i ∈ realizedArmSet w z, armTable n M Y z (w.1.1 i)) /
            (armCount G G1 z : ℝ)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro g hg
    rw [hobs g hg, hselected]
  rw [hsum, halg, hselected, hselected]

-- @node: boundedInProb_of_pointwise_bound
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,X,K,hX), [the bounded in prob of pointwise bound result holds](goal). -/
lemma boundedInProb_of_pointwise_bound {Ω : ℕ → Type*} [∀ r, Fintype (Ω r)]
    (D : ∀ r, FiniteDesign (Ω r)) (X : ∀ r, Ω r → ℝ) (K : ℝ)
    (hX : ∀ r w, |X r w| ≤ K) : FiniteDesign.BoundedInProb D X := by
  intro η hη
  refine ⟨K + 1, ?_⟩
  filter_upwards [] with r
  have hz : (D r).Pr (fun w => K + 1 ≤ |X r w|) = 0 := by
    unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
    apply Finset.sum_eq_zero
    intro w hw
    simp [not_le.mpr (lt_of_le_of_lt (hX r w) (lt_add_one K))]
  rw [hz]
  exact hη.le

-- @node: FiniteDesign.TendstoInProb.square_of_bounded
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,X,a,K,hXbound,habound,hX), [the square of bounded result holds](goal). -/
lemma FiniteDesign.TendstoInProb.square_of_bounded
    {Ω : ℕ → Type*} [∀ r, Fintype (Ω r)]
    {D : ∀ r, FiniteDesign (Ω r)} {X : ∀ r, Ω r → ℝ} {a : ℕ → ℝ}
    (K : ℝ) (hXbound : ∀ r w, |X r w| ≤ K) (habound : ∀ r, |a r| ≤ K)
    (hX : FiniteDesign.TendstoInProb D X a) :
    FiniteDesign.TendstoInProb D (fun r w => X r w ^ 2) (fun r => a r ^ 2) := by
  have hcenter : FiniteDesign.TendstoInProb D (fun r w => X r w - a r) (fun _ => 0) := by
    intro ε hε
    simpa only [sub_zero, sub_zero] using hX ε hε
  have hsumBound : ∀ r w, |X r w + a r| ≤ 2 * K := by
    intro r w
    calc
      |X r w + a r| ≤ |X r w| + |a r| := abs_add_le _ _
      _ ≤ K + K := add_le_add (hXbound r w) (habound r)
      _ = 2 * K := by ring
  have hbounded := boundedInProb_of_pointwise_bound D (fun r w => X r w + a r)
    (2 * K) hsumBound
  have hprod := hcenter.mul_boundedInProb hbounded
  intro ε hε
  have ht := hprod ε hε
  change Tendsto (fun m => (D m).Pr (fun z => ε ≤ |X m z ^ 2 - a m ^ 2|))
    atTop (nhds 0)
  apply Tendsto.congr' _ ht
  filter_upwards [] with m
  apply (D m).Pr_congr
  intro w
  constructor <;> intro hh
  · convert hh using 1; ring
  · convert hh using 1; ring

-- @node: FiniteDesign.TendstoInProb.scale_tendsto_one_of_bounded
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,X,a,c,K,hXbound,hX,hc), [the indicated sequence converges to its stated limit](goal). -/
lemma FiniteDesign.TendstoInProb.scale_tendsto_one_of_bounded
    {Ω : ℕ → Type*} [∀ r, Fintype (Ω r)]
    {D : ∀ r, FiniteDesign (Ω r)} {X : ∀ r, Ω r → ℝ} {a c : ℕ → ℝ}
    (K : ℝ) (hXbound : ∀ r w, |X r w| ≤ K)
    (hX : FiniteDesign.TendstoInProb D X a) (hc : Tendsto c atTop (nhds 1)) :
    FiniteDesign.TendstoInProb D (fun r w => c r * X r w) a := by
  have hcenter : FiniteDesign.TendstoInProb D (fun r w => X r w - a r) (fun _ => 0) := by
    intro ε hε
    simpa only [sub_zero, sub_zero] using hX ε hε
  have hcProb := FiniteDesign.deterministic_tendstoInProb D c 1 hc
  have hc0 : FiniteDesign.TendstoInProb D (fun r _ => c r - 1) (fun _ => 0) := by
    intro ε hε
    simpa only [sub_zero, sub_zero] using hcProb ε hε
  have hbounded := boundedInProb_of_pointwise_bound D X K hXbound
  have hprod := hc0.mul_boundedInProb hbounded
  have hadd := hprod.add hcenter
  intro ε hε
  have ht := hadd ε hε
  change Tendsto (fun m => (D m).Pr (fun z => ε ≤ |c m * X m z - a m|))
    atTop (nhds 0)
  apply Tendsto.congr' _ ht
  filter_upwards [] with m
  apply (D m).Pr_congr
  intro w
  constructor <;> intro hh
  · convert hh using 1; ring
  · convert hh using 1; ring

-- @node: armSampleVar_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,A,p,B,J,hGrowth,hFraction,hBounded,hJohnson,hKneser,z), [the indicated sequence converges to its stated limit](goal). -/
lemma armSampleVar_tendstoInProb {M : ℕ} (hM : 2 ≤ M) (A : ScheduleArray M)
    (p B : ℝ) (J : ∀ r, JohnsonProjections (A.popSize r) M)
    (hGrowth : GroupCountGrowth A) (hFraction : StableTreatmentFraction A p)
    (hBounded : BoundedSchedule A B)
    (hJohnson : ∀ r, JohnsonOrthogonalDecomposition (A.popSize r) M (J r))
    (hKneser : ∀ r, KneserAdjacencySpectrum (A.popSize r) M) (z : Arm) :
    FiniteDesign.TendstoInProb A.design
      (fun r w => if h : 2 ≤ armCount (A.groups r) (A.treated r) z then
        armSampleVar (A.schedule r) w z h else 0)
      (fun r => A.armVariance r z) := by
  let f : ∀ r, Omega (A.popSize r) M → ℝ := fun r S =>
    armTable (A.popSize r) M (A.schedule r) z S
  have hB : 0 < B := hBounded.1
  have hf : ∀ r S, |f r S| ≤ B := fun r S =>
    armTable_abs_le_of_boundedSchedule A B hBounded r z S
  have hfsq : ∀ r S, |(f r S) ^ 2| ≤ B ^ 2 := by
    intro r S
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hf r S) 2
  let μ : ℕ → ℝ := fun r => (slice (A.popSize r) M (A.groupSize_le r)).E (f r)
  let μ2 : ℕ → ℝ := fun r =>
    (slice (A.popSize r) M (A.groupSize_le r)).E (fun S => (f r S) ^ 2)
  have hmean := selectedMean_tendstoInProb hM A p J hGrowth hFraction hJohnson hKneser
    z f B hB hf
  have hsecond := selectedMean_tendstoInProb hM A p J hGrowth hFraction hJohnson hKneser
    z (fun r S => (f r S) ^ 2) (B ^ 2) (sq_pos_of_pos hB) hfsq
  have hcount : ∀ r, 0 < armCount (A.groups r) (A.treated r) z := by
    intro r
    cases z
    · change 0 < A.groups r - A.treated r
      exact Nat.sub_pos_of_lt (A.treated_lt r)
    · simpa [armCount] using A.treated_pos r
  have hmeanBound : ∀ r w, |selectedMean (f r) w z| ≤ B := fun r w =>
    selectedMean_abs_le (f r) w z B (hf r) (hcount r)
  have hμBound : ∀ r, |μ r| ≤ B := fun r =>
    sliceExpectation_abs_le_of_abs_le (A.groupSize_le r) (f r) B (hf r)
  have hmeanSq := FiniteDesign.TendstoInProb.square_of_bounded B hmeanBound hμBound hmean
  have hbracket := hsecond.sub hmeanSq
  have hbracketBound : ∀ r
      (w : PartitionTuple (A.popSize r) M (A.groups r) ×
        TreatmentSpace (A.groups r) (A.treated r)),
      |selectedMean (fun S => (f r S) ^ 2) w z - selectedMean (f r) w z ^ 2| ≤
        2 * B ^ 2 := by
    intro r w
    have h2 := selectedMean_abs_le (fun S => (f r S) ^ 2) w z (B ^ 2)
      (hfsq r) (hcount r)
    have h1 := hmeanBound r w
    calc
      |selectedMean (fun S => (f r S) ^ 2) w z - selectedMean (f r) w z ^ 2| ≤
          |selectedMean (fun S => (f r S) ^ 2) w z| +
            |selectedMean (f r) w z ^ 2| := abs_sub _ _
      _ ≤ B ^ 2 + B ^ 2 := by
        gcongr
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = 2 * B ^ 2 := by ring
  have harm : Tendsto (fun r => armCount (A.groups r) (A.treated r) z) atTop atTop := by
    cases z
    · change Tendsto A.controls atTop atTop
      exact controls_tendsto_atTop A p hGrowth hFraction
    · simpa [armCount] using treated_tendsto_atTop A p hGrowth hFraction
  have harmInv : Tendsto (fun r => ((armCount (A.groups r) (A.treated r) z : ℕ) : ℝ)⁻¹)
      atTop (nhds 0) := (tendsto_natCast_atTop_atTop.comp harm).inv_tendsto_atTop
  have hfactor : Tendsto (fun r =>
      (armCount (A.groups r) (A.treated r) z : ℝ) /
        ((armCount (A.groups r) (A.treated r) z - 1 : ℕ) : ℝ)) atTop (nhds 1) := by
    have hden : Tendsto (fun r => 1 -
        ((armCount (A.groups r) (A.treated r) z : ℝ))⁻¹) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub harmInv
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have hquot := hone.div hden (by norm_num : (1 : ℝ) ≠ 0)
    have hlarge : ∀ᶠ r in atTop, 2 ≤ armCount (A.groups r) (A.treated r) z :=
      (tendsto_atTop.1 harm) 2
    have heq : ∀ᶠ r in atTop,
        (armCount (A.groups r) (A.treated r) z : ℝ) /
            ((armCount (A.groups r) (A.treated r) z - 1 : ℕ) : ℝ) =
          1 / (1 - ((armCount (A.groups r) (A.treated r) z : ℝ))⁻¹) := by
      filter_upwards [hlarge] with r hr
      rw [Nat.cast_sub (by omega : 1 ≤ armCount (A.groups r) (A.treated r) z)]
      have hm : (armCount (A.groups r) (A.treated r) z : ℝ) ≠ 0 := by positivity
      field_simp
      norm_num
    simpa using Tendsto.congr' (heq.mono fun _ hh => hh.symm) hquot
  have hscaled := FiniteDesign.TendstoInProb.scale_tendsto_one_of_bounded
    (2 * B ^ 2) hbracketBound hbracket hfactor
  have hlarge : ∀ᶠ r in atTop, 2 ≤ armCount (A.groups r) (A.treated r) z :=
    (tendsto_atTop.1 harm) 2
  intro ε hε
  have ht := hscaled ε hε
  apply Tendsto.congr' _ ht
  filter_upwards [hlarge] with r hr
  apply (A.design r).Pr_congr
  intro w
  have hsample := armSampleVar_eq_selectedMoments (A.schedule r) w z hr
  have htarget : A.armVariance r z = μ2 r - μ r ^ 2 := by
    unfold ScheduleArray.armVariance armVar μ2 μ f
    rw [FiniteDesign.Var_eq]
  simp only [dif_pos hr]
  rw [hsample, htarget]

-- @node: boundedInProb_deterministic_of_tendsto
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,a,c,ha), [the indicated sequence converges to its stated limit](goal). -/
lemma boundedInProb_deterministic_of_tendsto {Ω : ℕ → Type*} [∀ r, Fintype (Ω r)]
    (D : ∀ r, FiniteDesign (Ω r)) (a : ℕ → ℝ) (c : ℝ)
    (ha : Tendsto a atTop (nhds c)) :
    FiniteDesign.BoundedInProb D (fun r _ => a r) := by
  intro η hη
  refine ⟨|c| + 2, ?_⟩
  have hev : ∀ᶠ r in atTop, |a r| < |c| + 1 := by
    have hopen : Set.Iio (|c| + 1) ∈ nhds |c| := Iio_mem_nhds (lt_add_one _)
    exact (ha.norm.eventually hopen)
  filter_upwards [hev] with r hr
  have hz : (D r).Pr (fun _ => |c| + 2 ≤ |a r|) = 0 := by
    unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
    apply Finset.sum_eq_zero
    intro w hw
    rw [if_neg, mul_zero]
    exact not_le.mpr (hr.trans (by linarith))
  rw [hz]
  exact hη.le

-- @node: cr2_centered_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,A,p,B,J,hGrowth,hFraction,hBounded,hJohnson,hKneser), [the indicated sequence converges to its stated limit](goal). -/
lemma cr2_centered_tendstoInProb {M : ℕ} (hM : 2 ≤ M) (A : ScheduleArray M)
    (p B : ℝ) (J : ∀ r, JohnsonProjections (A.popSize r) M)
    (hGrowth : GroupCountGrowth A) (hFraction : StableTreatmentFraction A p)
    (hBounded : BoundedSchedule A B)
    (hJohnson : ∀ r, JohnsonOrthogonalDecomposition (A.popSize r) M (J r))
    (hKneser : ∀ r, KneserAdjacencySpectrum (A.popSize r) M) :
    FiniteDesign.TendstoInProb A.design
      (fun r w => (A.groups r : ℝ) * A.cr2 r w - A.leadingVariance r)
      (fun _ => 0) := by
  let s : Arm → ∀ r,
      PartitionTuple (A.popSize r) M (A.groups r) ×
        TreatmentSpace (A.groups r) (A.treated r) → ℝ := fun z r w =>
    if h : 2 ≤ armCount (A.groups r) (A.treated r) z then
      armSampleVar (A.schedule r) w z h else 0
  have hs1 := armSampleVar_tendstoInProb hM A p B J hGrowth hFraction hBounded
    hJohnson hKneser true
  have hs0 := armSampleVar_tendstoInProb hM A p B J hGrowth hFraction hBounded
    hJohnson hKneser false
  have he1 : FiniteDesign.TendstoInProb A.design
      (fun r w => s true r w - A.armVariance r true) (fun _ => 0) := by
    intro ε hε
    simpa only [s, sub_zero] using hs1 ε hε
  have he0 : FiniteDesign.TendstoInProb A.design
      (fun r w => s false r w - A.armVariance r false) (fun _ => 0) := by
    intro ε hε
    simpa only [s, sub_zero] using hs0 ε hε
  have hpInv : Tendsto (fun r => (A.treatmentFraction r)⁻¹) atTop (nhds p⁻¹) :=
    hFraction.2.2.inv₀ hFraction.1.ne'
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hq : Tendsto (fun r => 1 - A.treatmentFraction r) atTop (nhds (1 - p)) :=
    hone.sub hFraction.2.2
  have hqInv : Tendsto (fun r => (1 - A.treatmentFraction r)⁻¹) atTop
      (nhds (1 - p)⁻¹) := hq.inv₀ (by linarith [hFraction.2.1])
  have hb1 := boundedInProb_deterministic_of_tendsto A.design
    (fun r => (A.treatmentFraction r)⁻¹) p⁻¹ hpInv
  have hb0 := boundedInProb_deterministic_of_tendsto A.design
    (fun r => (1 - A.treatmentFraction r)⁻¹) (1 - p)⁻¹ hqInv
  have hprod1 := he1.mul_boundedInProb hb1
  have hprod0 := he0.mul_boundedInProb hb0
  have hadd := hprod1.add hprod0
  intro ε hε
  have ht := hadd ε hε
  have htreat := treated_tendsto_atTop A p hGrowth hFraction
  have hcontrol := controls_tendsto_atTop A p hGrowth hFraction
  have hboth : ∀ᶠ r in atTop, 2 ≤ A.treated r ∧ 2 ≤ A.controls r := by
    filter_upwards [(tendsto_atTop.1 htreat) 2, (tendsto_atTop.1 hcontrol) 2] with r h1 h0
    exact ⟨h1, h0⟩
  apply Tendsto.congr' _ ht
  filter_upwards [hboth] with r hr
  apply (A.design r).Pr_congr
  intro w
  have hp : A.treatmentFraction r = (A.treated r : ℝ) / (A.groups r : ℝ) := rfl
  have hGr : (A.groups r : ℝ) ≠ 0 := by exact_mod_cast (A.groups_pos r).ne'
  have htr : (A.treated r : ℝ) ≠ 0 := by exact_mod_cast (A.treated_pos r).ne'
  have hcr : ((A.controls r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : A.controls r ≠ 0)
  have h0 : 2 ≤ armCount (A.groups r) (A.treated r) false := by
    simpa [armCount, ScheduleArray.controls] using hr.2
  have h1 : 2 ≤ armCount (A.groups r) (A.treated r) true := by
    simpa [armCount] using hr.1
  have hcNat : 2 ≤ A.groups r - A.treated r := by
    simpa [ScheduleArray.controls] using hr.2
  have hs1eq : s true r w = armSampleVar (A.schedule r) w true h1 := by
    simp only [s, dif_pos h1]
  have hs0eq : s false r w = armSampleVar (A.schedule r) w false
      h0 := by
    simp only [s, dif_pos h0]
  have hcr2eq : A.cr2 r w = cr2Var (A.schedule r) hr.1 hcNat w := by
    unfold ScheduleArray.cr2
    rw [dif_pos hr]
  have halg : (A.groups r : ℝ) * A.cr2 r w - A.leadingVariance r =
      (s true r w - A.armVariance r true) * (A.treatmentFraction r)⁻¹ +
        (s false r w - A.armVariance r false) *
          (1 - A.treatmentFraction r)⁻¹ := by
    rw [hcr2eq, hs1eq, hs0eq]
    unfold cr2Var ScheduleArray.leadingVariance indepGroupVar
      ScheduleArray.armVariance ScheduleArray.treatmentFraction pFrac
    rw [Nat.cast_sub (A.treated_le r)]
    field_simp [ScheduleArray.controls]
    ring
  rw [halg]
  simp

-- @node: cr2_variance_gap_tendstoInProb
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,A,p,rho,B,J,hGrowth,hFraction,hSampling,hBounded,hJohnson,hKneser), [the indicated sequence converges to its stated limit](goal). -/
lemma cr2_variance_gap_tendstoInProb {M : ℕ} (hM : 2 ≤ M) (A : ScheduleArray M)
    (p rho B : ℝ) (J : ∀ r, JohnsonProjections (A.popSize r) M)
    (hGrowth : GroupCountGrowth A) (hFraction : StableTreatmentFraction A p)
    (hSampling : SamplingFractionLimit A rho) (hBounded : BoundedSchedule A B)
    (hJohnson : ∀ r, JohnsonOrthogonalDecomposition (A.popSize r) M (J r))
    (hKneser : ∀ r, KneserAdjacencySpectrum (A.popSize r) M) :
    FiniteDesign.TendstoInProb A.design
      (fun r w => (A.groups r : ℝ) * (A.cr2 r w - A.variance r) -
        rho * A.degreeOne (by omega) J r) (fun _ => 0) := by
  have hcr2 := cr2_centered_tendstoInProb hM A p B J hGrowth hFraction hBounded
    hJohnson hKneser
  obtain ⟨C, hC, hdense⟩ := dense_projection_limit hM p rho B
  have hv := (hdense A J hGrowth hFraction hSampling hBounded hJohnson hKneser).1
  have hvProb := FiniteDesign.deterministic_tendstoInProb A.design
    (fun r => (A.groups r : ℝ) * A.variance r -
      (A.leadingVariance r - rho * A.degreeOne (by omega) J r)) 0 hv
  have hsub := hcr2.sub hvProb
  intro ε hε
  have ht := hsub ε hε
  apply Tendsto.congr' _ ht
  filter_upwards [] with r
  apply (A.design r).Pr_congr
  intro w
  constructor <;> intro hh
  · convert hh using 1; ring
  · convert hh using 1; ring

-- @node: scaledVariance_eventually_lower
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,A,cSigma,hNondeg), [the stated variance result holds](goal). -/
lemma scaledVariance_eventually_lower {M : ℕ} (A : ScheduleArray M) (cSigma : ℝ)
    (hNondeg : ScaledVarianceNondegenerate A cSigma) :
    ∀ᶠ r in atTop, cSigma / 2 < (A.groups r : ℝ) * A.variance r := by
  have hlt : ((cSigma / 2 : ℝ) : EReal) < Filter.liminf (fun r =>
      (((A.groups r : ℝ) * A.variance r : ℝ) : EReal)) atTop := by
    apply lt_of_lt_of_le _ hNondeg.2
    exact EReal.coe_lt_coe_iff.mpr (by linarith [hNondeg.1] : cSigma / 2 < cSigma)
  have hev := eventually_lt_of_lt_liminf hlt (by isBoundedDefault)
  filter_upwards [hev] with r hr
  exact EReal.coe_lt_coe_iff.mp hr

-- @node: exists_global_abs_bound_of_eventually
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:a,C,hC), [the stated bound holds](goal). -/
lemma exists_global_abs_bound_of_eventually (a : ℕ → ℝ) (C : ℝ)
    (hC : ∀ᶠ r in atTop, |a r| ≤ C) : ∃ K : ℝ, ∀ r, |a r| ≤ K := by
  rw [eventually_atTop] at hC
  obtain ⟨N, hN⟩ := hC
  let K := |C| + ∑ r ∈ Finset.range N, |a r|
  refine ⟨K, ?_⟩
  intro r
  by_cases hr : N ≤ r
  · calc
      |a r| ≤ C := hN r hr
      _ ≤ |C| := le_abs_self C
      _ ≤ K := by
        dsimp [K]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  · have hrmem : r ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hr)
    calc
      |a r| ≤ ∑ i ∈ Finset.range N, |a i| := Finset.single_le_sum
        (fun i _ => abs_nonneg (a i)) hrmem
      _ ≤ K := by dsimp [K]; linarith [abs_nonneg C]

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

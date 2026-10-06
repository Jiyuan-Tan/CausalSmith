module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BaselineTranslationAffinity
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockSupport
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.DesignBridge
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ReverseTestMoments
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.TwoPriorRisk

/-!
# Complete-block construction, support, and response moments
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The fixed complete directed blocks of augmented degree d plus one. -/
-- @node: completeBlockEdge
def completeBlockEdge (n d : ℕ) (j i : Fin n) : Prop :=
  (j.val < (n / (d + 1)) * (d + 1) ∧ i.val < (n / (d + 1)) * (d + 1) ∧
    j.val / (d + 1) = i.val / (d + 1)) ∧ j ≠ i

/-- Complete block edges exclude all diagonal arrows.  [For the stated data and conditions](hyp:n,d), [the stated conclusion holds](goal). -/
-- @node: completeBlockEdge_irrefl
lemma completeBlockEdge_irrefl (n d : ℕ) : ∀ i, ¬ completeBlockEdge n d i i := by
  intro i h
  exact h.2 rfl

/-- Complete directed blocks of size d+1, sharing one fixed graph under both prior signs. -/
-- @node: completeBlockSchedule
def completeBlockSchedule (n d : ℕ) (σ : Bool) (h : ℝ) (U : Fin (n / (d + 1)) → ℝ) :
    Schedule (Fin n) where
  edge := completeBlockEdge n d
  decEdge := Classical.decRel _
  irrefl := completeBlockEdge_irrefl n d
  a := fun i => ∑ v : Fin (n / (d + 1)),
    if i.val / (d + 1) = v.val then U v - signOf σ * h / 2 else 0
  t := fun i => if i.val < (n / (d + 1)) * (d + 1) then signOf σ * h / (d + 1) else 0
  b := fun _ _ => signOf σ * h / (d + 1)

/-- The labeled members of one complete block, including its own coordinate. -/
-- @node: completeBlockMembers
def completeBlockMembers (n d : ℕ) (v : Fin (n / (d + 1))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val / (d + 1) = v.val)

/-- Each full block has exactly d+1 members.  [For the stated data and conditions](hyp:n,d,v), [the stated conclusion holds](goal). -/
-- @node: completeBlockMembers_card
lemma completeBlockMembers_card (n d : ℕ) (v : Fin (n / (d + 1))) :
    (completeBlockMembers n d v).card = d + 1 := by
  let f : Fin (d + 1) → Fin n := fun j => ⟨v.val * (d + 1) + j.val, by
    have hv := Nat.mul_le_mul_right (d + 1) (show v.val + 1 ≤ n / (d + 1) by omega)
    have hn := Nat.div_mul_le_self n (d + 1)
    have hj := j.isLt
    rw [Nat.add_mul] at hv
    omega⟩
  have hf (j : Fin (d + 1)) : (f j).val / (d + 1) = v.val := by
    dsimp [f]
    rw [Nat.mul_comm v.val (d + 1), Nat.mul_add_div (by omega : 0 < d + 1), Nat.div_eq_of_lt j.isLt, add_zero]
  have he : completeBlockMembers n d v = Finset.univ.image f := by
    ext i
    simp only [completeBlockMembers, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hi
      refine ⟨⟨i.val % (d + 1), Nat.mod_lt _ (by omega)⟩, ?_⟩
      apply Fin.ext
      dsimp [f]
      rw [← hi, Nat.mul_comm, Nat.div_add_mod]
    · rintro ⟨j, _, rfl⟩
      exact hf j
  rw [he, Finset.card_image_of_injective]
  · simp
  · intro j k hjk
    apply Fin.ext
    have hv := congrArg Fin.val hjk
    dsimp [f] at hv
    omega

/-- Quotients index a full block precisely for nonpadding labels.  [For the stated data and conditions](hyp:n,d,i), [the stated conclusion holds](goal). -/
-- @node: completeBlock_active_iff
lemma completeBlock_active_iff (n d : ℕ) (i : Fin n) :
    i.val < (n / (d + 1)) * (d + 1) ↔ i.val / (d + 1) < n / (d + 1) := by
  exact (Nat.div_lt_iff_lt_mul (by omega : 0 < d + 1)).symm

/-- A nonpadding label's incoming neighborhood is its block with itself removed.  [For the stated data and conditions](hyp:n,d,σ,h,U,i,hi), [the stated conclusion holds](goal). -/
-- @node: completeBlockSchedule_inNbhd
lemma completeBlockSchedule_inNbhd (n d : ℕ) (σ : Bool) (h : ℝ)
    (U : Fin (n / (d + 1)) → ℝ) (i : Fin n)
    (hi : i.val < (n / (d + 1)) * (d + 1)) :
    inNbhd (completeBlockSchedule n d σ h U) i =
      (completeBlockMembers n d ⟨i.val / (d + 1),
        (completeBlock_active_iff n d i).mp hi⟩).erase i := by
  ext j
  change (j ∈ Finset.univ.filter (fun j => completeBlockEdge n d j i)) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  simp only [completeBlockMembers, Finset.mem_filter, Finset.mem_univ, true_and]
  change completeBlockEdge n d j i ↔ j ≠ i ∧ j.val / (d + 1) = i.val / (d + 1)
  unfold completeBlockEdge
  constructor
  · rintro ⟨⟨hj, _, he⟩, hne⟩
    exact ⟨hne, he⟩
  · rintro ⟨hne, he⟩
    have hj : j.val < (n / (d + 1)) * (d + 1) :=
      (completeBlock_active_iff n d j).mpr (he ▸ (completeBlock_active_iff n d i).mp hi)
    exact ⟨⟨hj, hi, he⟩, hne⟩

/-- Padding labels have no incoming arrows.  [For the stated data and conditions](hyp:n,d,σ,h,U,i,hi), [the stated conclusion holds](goal). -/
-- @node: completeBlockSchedule_inNbhd_padding
lemma completeBlockSchedule_inNbhd_padding (n d : ℕ) (σ : Bool) (h : ℝ)
    (U : Fin (n / (d + 1)) → ℝ) (i : Fin n)
    (hi : ¬ i.val < (n / (d + 1)) * (d + 1)) :
    inNbhd (completeBlockSchedule n d σ h U) i = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro j hj
  exact hi (Finset.mem_filter.mp hj).2.1.2.1

/-- Full block rows have off-diagonal degree d; padding rows have degree zero.  [For the stated data and conditions](hyp:n,d,σ,h,U,i), [the stated conclusion holds](goal). -/
-- @node: completeBlockSchedule_inNbhd_card
lemma completeBlockSchedule_inNbhd_card (n d : ℕ) (σ : Bool) (h : ℝ)
    (U : Fin (n / (d + 1)) → ℝ) (i : Fin n) :
    (inNbhd (completeBlockSchedule n d σ h U) i).card =
      if i.val < (n / (d + 1)) * (d + 1) then d else 0 := by
  by_cases hi : i.val < (n / (d + 1)) * (d + 1)
  · rw [if_pos hi, completeBlockSchedule_inNbhd n d σ h U i hi,
      Finset.card_erase_of_mem (by simp [completeBlockMembers]), completeBlockMembers_card]
    omega
  · rw [if_neg hi, completeBlockSchedule_inNbhd_padding n d σ h U i hi,
      Finset.card_empty]

/-- Complete directed block edges are symmetric, so outgoing degrees equal incoming degrees.  [For the stated data and conditions](hyp:n,d,j,i), [the stated conclusion holds](goal). -/
-- @node: completeBlockEdge_symm
lemma completeBlockEdge_symm (n d : ℕ) (j i : Fin n) :
    completeBlockEdge n d j i ↔ completeBlockEdge n d i j := by
  constructor <;> rintro ⟨⟨hj, hi, he⟩, hne⟩
  · exact ⟨⟨hi, hj, he.symm⟩, Ne.symm hne⟩
  · exact ⟨⟨hi, hj, he.symm⟩, Ne.symm hne⟩

/-- A full block row uses exactly its own baseline.  [For the stated data and conditions](hyp:n,d,σ,h,U,i,hi), [the stated conclusion holds](goal). -/
-- @node: completeBlockSchedule_baseline
lemma completeBlockSchedule_baseline (n d : ℕ) (σ : Bool) (h : ℝ)
    (U : Fin (n / (d + 1)) → ℝ) (i : Fin n)
    (hi : i.val < (n / (d + 1)) * (d + 1)) :
    (completeBlockSchedule n d σ h U).a i =
      U ⟨i.val / (d + 1), (completeBlock_active_iff n d i).mp hi⟩ - signOf σ * h / 2 := by
  let v : Fin (n / (d + 1)) := ⟨i.val / (d + 1), (completeBlock_active_iff n d i).mp hi⟩
  change (∑ w, if i.val / (d + 1) = w.val then U w - signOf σ * h / 2 else 0) = _
  rw [Finset.sum_eq_single v]
  · simp [v]
  · intro w _ hw
    apply if_neg
    intro he
    exact hw (Fin.ext he.symm)
  · simp

/-- Padding rows have zero baseline as well as zero treatment effects.  [For the stated data and conditions](hyp:n,d,σ,h,U,i,hi), [the stated conclusion holds](goal). -/
-- @node: completeBlockSchedule_baseline_padding
lemma completeBlockSchedule_baseline_padding (n d : ℕ) (σ : Bool) (h : ℝ)
    (U : Fin (n / (d + 1)) → ℝ) (i : Fin n)
    (hi : ¬ i.val < (n / (d + 1)) * (d + 1)) :
    (completeBlockSchedule n d σ h U).a i = 0 := by
  change (∑ w, if i.val / (d + 1) = w.val then U w - signOf σ * h / 2 else 0) = 0
  apply Finset.sum_eq_zero
  intro w _
  apply if_neg
  intro he
  exact hi ((completeBlock_active_iff n d i).mpr (he ▸ w.isLt))

/-- Baselines and amplitudes in the declared support produce admissible complete-block schedules.  [For the stated data and conditions](hyp:n,d,σ,h,U,hh,hU), [the stated conclusion holds](goal). -/
-- @node: completeBlockSchedule_mem_class
lemma completeBlockSchedule_mem_class (n d : ℕ) (σ : Bool) (h : ℝ)
    (U : Fin (n / (d + 1)) → ℝ) (hh : h ∈ Set.Icc 0 (1 / 4))
    (hU : ∀ v, |U v| ≤ 1 / 4) : ScheduleClass (completeBlockSchedule n d σ h U) d := by
  have hk : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hs : |signOf σ| = 1 := by cases σ <;> norm_num [signOf]
  have habs : |signOf σ * h / (d + 1)| = h / (d + 1) := by
    rw [abs_div, abs_mul, hs, abs_of_nonneg hh.1, abs_of_pos hk, one_mul]
  constructor
  · intro i
    rw [completeBlockSchedule_inNbhd_card]
    split <;> omega
  · intro j
    have he : Finset.univ.filter (fun i => j ∈ inNbhd (completeBlockSchedule n d σ h U) i) =
        inNbhd (completeBlockSchedule n d σ h U) j := by
      ext i
      change (i ∈ Finset.univ.filter (fun i => j ∈ Finset.univ.filter
        (fun j => completeBlockEdge n d j i))) ↔
        (i ∈ Finset.univ.filter (fun i => completeBlockEdge n d i j))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, completeBlockEdge_symm]
    rw [he, completeBlockSchedule_inNbhd_card]
    split <;> omega
  · intro i
    by_cases hi : i.val < (n / (d + 1)) * (d + 1)
    · have ha := completeBlockSchedule_baseline n d σ h U i hi
      change |(completeBlockSchedule n d σ h U).a i| +
        |if i.val < (n / (d + 1)) * (d + 1) then signOf σ * h / (d + 1) else 0| +
        (∑ j ∈ inNbhd (completeBlockSchedule n d σ h U) i, |signOf σ * h / (d + 1)|) ≤ 1
      rw [ha, if_pos hi]
      simp only [habs, Finset.sum_const, nsmul_eq_mul,
        completeBlockSchedule_inNbhd_card, if_pos hi, Nat.cast_add, Nat.cast_one]
      have hm : h / ((d : ℝ) + 1) + d * (h / (d + 1)) = h := by field_simp; ring
      rw [add_assoc, hm]
      have ht : |signOf σ * h / 2| = h / 2 := by
        rw [abs_div, abs_mul, hs, abs_of_nonneg hh.1]
        norm_num
      have hb := abs_sub (U ⟨i.val / (d + 1), (completeBlock_active_iff n d i).mp hi⟩)
        (signOf σ * h / 2)
      rw [ht] at hb
      linarith [hU ⟨i.val / (d + 1), (completeBlock_active_iff n d i).mp hi⟩, hh.2]
    · change |(completeBlockSchedule n d σ h U).a i| +
        |if i.val < (n / (d + 1)) * (d + 1) then signOf σ * h / (d + 1) else 0| +
        (∑ j ∈ inNbhd (completeBlockSchedule n d σ h U) i, |signOf σ * h / (d + 1)|) ≤ 1
      rw [completeBlockSchedule_baseline_padding n d σ h U i hi, if_neg hi,
        completeBlockSchedule_inNbhd_padding n d σ h U i hi]
      norm_num

/-- The number of nonpadding labels is the number of full blocks times their size.  [For the stated data and conditions](hyp:n,d), [the stated conclusion holds](goal). -/
-- @node: completeBlock_active_card
lemma completeBlock_active_card (n d : ℕ) :
    (Finset.univ.filter (fun i : Fin n => i.val < (n / (d + 1)) * (d + 1))).card =
      (n / (d + 1)) * (d + 1) := by
  let m := (n / (d + 1)) * (d + 1)
  have hmn : m ≤ n := Nat.div_mul_le_self n (d + 1)
  change (Finset.univ.filter (fun i : Fin n => i.val < m)).card = m
  by_cases he : m = n
  · have hall : ∀ i : Fin n, i.val < m := fun i => by have hi := i.isLt; omega
    simp [hall, he]
  · have hm : m < n := by omega
    have hset : Finset.univ.filter (fun i : Fin n => i.val < m) =
        Finset.Iio (⟨m, hm⟩ : Fin n) := by
      ext i
      simp [Fin.lt_def]
    change (Finset.univ.filter (fun i : Fin n => i.val < m)).card = m
    rw [hset, Fin.card_Iio]

/-- A complete-block response is its baseline plus the translated centered block sign sum.  [For the stated data and conditions](hyp:n,d,σ,h,U,i,z,hi), [the stated conclusion holds](goal). -/
-- @node: completeBlockSchedule_response
lemma completeBlockSchedule_response (n d : ℕ) (σ : Bool) (h : ℝ)
    (U : Fin (n / (d + 1)) → ℝ) (i : Fin n) (z : Assign (Fin n))
    (hi : i.val < (n / (d + 1)) * (d + 1)) :
    potentialOutcome (completeBlockSchedule n d σ h U) i z =
      U ⟨i.val / (d + 1), (completeBlock_active_iff n d i).mp hi⟩ +
        signOf σ * h / (2 * (d + 1)) *
          ∑ j ∈ completeBlockMembers n d
            ⟨i.val / (d + 1), (completeBlock_active_iff n d i).mp hi⟩, signOf (z j) := by
  let v : Fin (n / (d + 1)) := ⟨i.val / (d + 1), (completeBlock_active_iff n d i).mp hi⟩
  let C := completeBlockMembers n d v
  have hmem : i ∈ C := by simp [C, completeBlockMembers, v]
  have hsum := Finset.sum_erase_add C (fun j => treatment (z j)) hmem
  have hcenter : (∑ j ∈ C, signOf (z j)) =
      2 * (∑ j ∈ C, treatment (z j)) - (d + 1) := by
    have hsign (j : Fin n) : signOf (z j) = 2 * treatment (z j) - 1 := by
      cases z j <;> norm_num [signOf, treatment]
    simp_rw [hsign]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [C, completeBlockMembers_card]
  unfold potentialOutcome
  rw [completeBlockSchedule_baseline n d σ h U i hi,
    completeBlockSchedule_inNbhd n d σ h U i hi]
  change U v - signOf σ * h / 2 +
    (if i.val < (n / (d + 1)) * (d + 1) then signOf σ * h / (d + 1) else 0) *
      treatment (z i) +
      (∑ j ∈ C.erase i, signOf σ * h / (d + 1) * treatment (z j)) =
    U v + signOf σ * h / (2 * (d + 1)) * ∑ j ∈ C, signOf (z j)
  rw [if_pos hi, ← Finset.mul_sum, hcenter, ← hsum]
  field_simp
  <;> ring

/-- Each nonpadding row has total-treatment contrast sigma*h, and padding rows have zero contrast.  [For the stated data and conditions](hyp:n,d,σ,h,U,i), [the stated conclusion holds](goal). -/
-- @node: completeBlockSchedule_row_contrast
lemma completeBlockSchedule_row_contrast (n d : ℕ) (σ : Bool) (h : ℝ)
    (U : Fin (n / (d + 1)) → ℝ) (i : Fin n) :
    potentialOutcome (completeBlockSchedule n d σ h U) i (fun _ => true) -
      potentialOutcome (completeBlockSchedule n d σ h U) i (fun _ => false) =
      if i.val < (n / (d + 1)) * (d + 1) then signOf σ * h else 0 := by
  simp only [potentialOutcome, treatment, ite_true, Bool.false_eq_true, ite_false,
    mul_one, mul_zero, Finset.sum_const_zero, add_zero, add_assoc, add_sub_cancel_left]
  change (if i.val < (n / (d + 1)) * (d + 1) then signOf σ * h / (d + 1) else 0) +
    (∑ j ∈ inNbhd (completeBlockSchedule n d σ h U) i, signOf σ * h / (d + 1)) = _
  simp only [Finset.sum_const, nsmul_eq_mul, completeBlockSchedule_inNbhd_card]
  by_cases hi : i.val < (n / (d + 1)) * (d + 1)
  · rw [if_pos hi, if_pos hi, if_pos hi]
    push_cast
    field_simp
    <;> ring
  · simp [hi]

/-- The complete-block construction has its constant signed target on every baseline draw.  [For the stated data and conditions](hyp:n,d,σ,h,U), [the stated conclusion holds](goal). -/
-- @node: completeBlockSchedule_tte
lemma completeBlockSchedule_tte (n d : ℕ) (σ : Bool) (h : ℝ)
    (U : Fin (n / (d + 1)) → ℝ) :
    tte (completeBlockSchedule n d σ h U) =
      signOf σ * ((n / (d + 1)) * (d + 1) : ℕ) * h / n := by
  simp only [tte, Fintype.card_fin, completeBlockSchedule_row_contrast]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, completeBlock_active_card]
  ring

/-- The independent compactly supported baselines put the complete-block prior in the model class.  [For the stated data and conditions](hyp:n,d,σ,h,hh), [the stated conclusion holds](goal). -/
-- @node: completeBlock_support
lemma completeBlock_support (n d : ℕ) (σ : Bool) (h : ℝ)
    (hh : h ∈ Set.Icc 0 (1 / 4)) :
    ∀ᵐ U ∂(blockBaselineLaw (n / (d + 1))),
      ScheduleClass (completeBlockSchedule n d σ h U) d ∧
        tte (completeBlockSchedule n d σ h U) =
          signOf σ * ((n / (d + 1)) * (d + 1) : ℕ) * h / n := by
  filter_upwards [blockBaselineLaw_ae_support (n / (d + 1))] with U hU
  exact ⟨completeBlockSchedule_mem_class n d σ h U hh hU,
    completeBlockSchedule_tte n d σ h U⟩

/-- At least one complete block fits for every admissible degree.  [For the stated data and conditions](hyp:n,d,hn,hdu), [the stated conclusion holds](goal). -/
-- @node: completeBlock_count_pos
lemma completeBlock_count_pos (n d : ℕ) (hn : 4 ≤ n) (hdu : d ≤ n - 1) :
    1 ≤ n / (d + 1) := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < d + 1)).mpr
  omega

/-- The full blocks cover at least half the population, as required by the testing separation.  [For the stated data and conditions](hyp:n,d,hn,hdu), [the stated conclusion holds](goal). -/
-- @node: completeBlock_coverage_ge_half
lemma completeBlock_coverage_ge_half (n d : ℕ) (hn : 4 ≤ n) (hdu : d ≤ n - 1) :
    (1 / 2 : ℝ) ≤ (((n / (d + 1)) * (d + 1) : ℕ) : ℝ) / n := by
  have hr := completeBlock_count_pos n d hn hdu
  have hk : d + 1 ≤ (n / (d + 1)) * (d + 1) := by
    simpa using Nat.mul_le_mul_right (d + 1) hr
  have hrem := Nat.mod_lt n (by omega : 0 < d + 1)
  have hdiv := Nat.div_add_mod n (d + 1)
  have htwice : n ≤ 2 * ((n / (d + 1)) * (d + 1)) := by
    rw [Nat.mul_comm (d + 1)] at hdiv
    omega
  have htwiceR : (n : ℝ) ≤ 2 * (((n / (d + 1)) * (d + 1) : ℕ) : ℝ) := by
    exact_mod_cast htwice
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply (le_div_iff₀ hnR).mpr
  linarith

/-- The centered sign sum in a full labeled block has second moment equal to its size.  [For the stated data and conditions](hyp:n,d,v), [the stated conclusion holds](goal). -/
-- @node: completeBlock_sign_second_moment
lemma completeBlock_sign_second_moment (n d : ℕ) (v : Fin (n / (d + 1))) :
    (∫ z, (∑ j ∈ completeBlockMembers n d v, signOf (z j)) ^ 2
      ∂halfBernoulli (Fin n)) = (d : ℝ) + 1 := by
  rw [reverse_revealed_second_moment, completeBlockMembers_card]
  simp

/-- The actual design has the same block sign moment, with all audit coordinates retained.  [For the stated data and conditions](hyp:n,d,D,ha,v), [the stated conclusion holds](goal). -/
-- @node: completeBlock_design_second_moment
lemma completeBlock_design_second_moment (n d : ℕ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) (ha : AssignmentLaw D)
    (v : Fin (n / (d + 1))) :
    (∫ ω, (∑ j ∈ completeBlockMembers n d v, signOf (ω.1 j)) ^ 2 ∂D) =
      (d : ℝ) + 1 := by
  rw [← integral_map measurable_fst.aemeasurable
    (show AEStronglyMeasurable (fun z : Assign (Fin n) =>
      (∑ j ∈ completeBlockMembers n d v, signOf (z j)) ^ 2) (D.map Prod.fst) from
      (measurable_of_finite _).aestronglyMeasurable), ha]
  exact completeBlock_sign_second_moment n d v

/-- The baseline translation in a complete block retains every member's observed sign. -/
-- @node: completeBlockShift
def completeBlockShift (n d : ℕ) (σ : Bool) (h : ℝ) (z : Assign (Fin n))
    (v : Fin (n / (d + 1))) : ℝ :=
  signOf σ * h / (2 * (d + 1)) * ∑ j ∈ completeBlockMembers n d v, signOf (z j)

/-- The squared separation of opposite-sign translations has its exact design expectation.  [For the stated data and conditions](hyp:n,d,h,D,ha,v), [the stated conclusion holds](goal). -/
-- @node: completeBlock_shift_separation_moment
lemma completeBlock_shift_separation_moment (n d : ℕ) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) (ha : AssignmentLaw D)
    (v : Fin (n / (d + 1))) :
    (∫ ω, (completeBlockShift n d true h ω.1 v -
      completeBlockShift n d false h ω.1 v) ^ 2 ∂D) = h ^ 2 / (d + 1) := by
  have he (z : Assign (Fin n)) :
      (completeBlockShift n d true h z v - completeBlockShift n d false h z v) ^ 2 =
        (h / (d + 1)) ^ 2 * (∑ j ∈ completeBlockMembers n d v, signOf (z j)) ^ 2 := by
    simp only [completeBlockShift, signOf, Bool.true_eq, Bool.false_eq_true,
      ite_true, ite_false]
    field_simp
    <;> ring
  simp_rw [he]
  rw [integral_const_mul, completeBlock_design_second_moment n d D ha v]
  have hk : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Product of the baseline densities translated by the observed complete-block sign sums. -/
-- @node: completeBlockResponseDensity
def completeBlockResponseDensity (n d : ℕ) (σ : Bool) (h : ℝ)
    (z : Assign (Fin n)) (y : Fin (n / (d + 1)) → ℝ) : ℝ :=
  ∏ v, cosSqDensity (y v - completeBlockShift n d σ h z v)

/-- Tensorized baseline translation bounds the distinct-response energy for every assignment.  [For the stated data and conditions](hyp:n,d,h,z), [the stated conclusion holds](goal). -/
-- @node: completeBlock_response_energy_le
lemma completeBlock_response_energy_le (n d : ℕ) (h : ℝ) (z : Assign (Fin n)) :
    hellingerEnergy volume (completeBlockResponseDensity n d true h z)
      (completeBlockResponseDensity n d false h z) ≤
    ∑ v : Fin (n / (d + 1)), 4 * Real.pi ^ 2 *
      (completeBlockShift n d true h z v - completeBlockShift n d false h z v) ^ 2 := by
  exact baseline_translation_affinity.2.2.2.1 (n / (d + 1))
    (completeBlockShift n d true h z) (completeBlockShift n d false h z)

/-- Averaging over the full assignment-audit design gives the sharp complete-block energy bound.  [For the stated data and conditions](hyp:n,d,h,D,ha), [the stated conclusion holds](goal). -/
-- @node: completeBlock_response_energy_mean_le
lemma completeBlock_response_energy_mean_le (n d : ℕ) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) (ha : AssignmentLaw D) :
    (∫ ω, hellingerEnergy volume (completeBlockResponseDensity n d true h ω.1)
      (completeBlockResponseDensity n d false h ω.1) ∂D) ≤
        4 * Real.pi ^ 2 * h ^ 2 * (n / (d + 1) : ℕ) / (d + 1) := by
  let := halfBernoulli_probability (V := Fin n)
  have hp : IsProbabilityMeasure (D.map Prod.fst) := by rw [ha]; infer_instance
  let := hp
  let : IsProbabilityMeasure D := Measure.isProbabilityMeasure_of_map Prod.fst
  calc
    _ ≤ ∫ ω, ∑ v : Fin (n / (d + 1)), 4 * Real.pi ^ 2 *
        (completeBlockShift n d true h ω.1 v -
          completeBlockShift n d false h ω.1 v) ^ 2 ∂D :=
      integral_mono Integrable.of_finite Integrable.of_finite
        (fun ω => completeBlock_response_energy_le n d h ω.1)
    _ = _ := by
      rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
      simp_rw [integral_const_mul, completeBlock_shift_separation_moment n d h D ha]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- [The complete-block response density is jointly measurable in the full design and responses.](goal) -/
-- @node: completeBlockResponseDensity_measurable
@[fun_prop]
lemma completeBlockResponseDensity_measurable (n d : ℕ) (σ : Bool) (h : ℝ) :
    Measurable (fun x : (Assign (Fin n) × Audit (Fin n)) ×
      (Fin (n / (d + 1)) → ℝ) => completeBlockResponseDensity n d σ h x.1.1 x.2) := by
  apply measurable_from_prod_countable_right
  intro ω
  unfold completeBlockResponseDensity cosSqDensity
  apply Finset.measurable_prod
  intro v _
  apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const) <;> fun_prop

/-- Every conditional complete-block density is nonnegative.  [For the stated data and conditions](hyp:n,d,σ,h,z,y), [the stated conclusion holds](goal). -/
-- @node: completeBlockResponseDensity_nonneg
lemma completeBlockResponseDensity_nonneg (n d : ℕ) (σ : Bool) (h : ℝ)
    (z : Assign (Fin n)) (y : Fin (n / (d + 1)) → ℝ) :
    0 ≤ completeBlockResponseDensity n d σ h z y := by
  exact Finset.prod_nonneg (fun _ _ => cosSqDensity_nonneg _)

/-- Independent translated baselines give an integrable, normalized product density.  [For the stated data and conditions](hyp:n,d,σ,h,z), [the stated conclusion holds](goal). -/
-- @node: completeBlockResponseDensity_integrable_normalized
lemma completeBlockResponseDensity_integrable_normalized (n d : ℕ) (σ : Bool) (h : ℝ)
    (z : Assign (Fin n)) :
    Integrable (completeBlockResponseDensity n d σ h z) ∧
      (∫ y, completeBlockResponseDensity n d σ h z y) = 1 := by
  constructor
  · exact Integrable.fintype_prod (fun v =>
      (translated_cosSqDensity_integrable_normalized (completeBlockShift n d σ h z v)).1)
  · change (∫ y : Fin (n / (d + 1)) → ℝ,
      ∏ v, cosSqDensity (y v - completeBlockShift n d σ h z v)
        ∂Measure.pi (fun _ => volume)) = 1
    rw [integral_fintype_prod_eq_prod
      (fun v w => cosSqDensity (w - completeBlockShift n d σ h z v))]
    simp only [(translated_cosSqDensity_integrable_normalized _).2, Finset.prod_const_one]

/-- Each conditional product response law is a probability law.  [For the stated data and conditions](hyp:n,d,σ,h,z), [the stated conclusion holds](goal). -/
-- @node: completeBlockResponseDensity_probability
lemma completeBlockResponseDensity_probability (n d : ℕ) (σ : Bool) (h : ℝ)
    (z : Assign (Fin n)) :
    IsProbabilityMeasure (volume.withDensity
      (fun y => ENNReal.ofReal (completeBlockResponseDensity n d σ h z y))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (completeBlockResponseDensity_integrable_normalized n d σ h z).1
      (Filter.Eventually.of_forall (completeBlockResponseDensity_nonneg n d σ h z)),
    (completeBlockResponseDensity_integrable_normalized n d σ h z).2]
  simp

/-- The averaged complete-block response energy is at most the population-scale envelope.  [For the stated data and conditions](hyp:n,d,h,D,ha), [the stated conclusion holds](goal). -/
-- @node: completeBlock_response_energy_population_le
lemma completeBlock_response_energy_population_le (n d : ℕ) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) (ha : AssignmentLaw D) :
    (∫ ω, hellingerEnergy volume (completeBlockResponseDensity n d true h ω.1)
      (completeBlockResponseDensity n d false h ω.1) ∂D) ≤
        4 * Real.pi ^ 2 * h ^ 2 * n / ((d : ℝ) + 1) ^ 2 := by
  refine (completeBlock_response_energy_mean_le n d h D ha).trans ?_
  have hk : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hr : (n / (d + 1) : ℕ) * ((d : ℝ) + 1) ≤ n := by
    exact_mod_cast Nat.div_mul_le_self n (d + 1)
  apply (div_le_div_iff₀ hk (sq_pos_of_pos hk)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hr (show 0 ≤ 4 * Real.pi ^ 2 * h ^ 2 by positivity)]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

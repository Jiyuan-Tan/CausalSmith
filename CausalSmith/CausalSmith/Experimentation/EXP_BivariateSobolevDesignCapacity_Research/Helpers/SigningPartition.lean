module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.SigningCrossExpectation

/-! # Reindexing the random signing partition

The selected rows and their complement are independent product samples after
reindexing. Their cross maximum is controlled by the independent-group bound, and
partition averaging completes the expected minimum-signing lower bound.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ An indicator sum is exactly the sum on its selected subtype.](goal) -/
-- @node: signing_sum_select_eq
lemma signing_sum_select_eq {ι E : Type} [Fintype ι] [AddCommMonoid E]
    (p : ι → Prop) [DecidablePred p] (f : ι → E) :
    (∑ i, if p i then f i else 0) = ∑ i : Subtype p, f i := by
  have h := Fintype.sum_subtype_add_sum_subtype p (fun i => if p i then f i else 0)
  have hy (i : Subtype p) : p i := i.property
  have hn (i : {i // ¬p i}) : ¬p i := i.property
  simpa only [hy, hn, ite_true, ite_false, Finset.sum_const_zero, add_zero] using h.symm

/-- [ Selected and complementary arrays, each indexed by its own finite cardinality. -/
-- @node: signingPartitionReindex
def signingPartitionReindex (n r : ℕ) (η : Signs n) :
    (Fin n → EuclideanSpace ℝ (Fin r)) ≃ᵐ
      (Fin (Fintype.card {i : Fin n // η i = true}) → EuclideanSpace ℝ (Fin r)) ×
      (Fin (Fintype.card {i : Fin n // ¬η i = true}) → EuclideanSpace ℝ (Fin r)) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => EuclideanSpace ℝ (Fin r))
    (fun i => η i = true)).trans
    ((MeasurableEquiv.piCongrLeft (fun _ => EuclideanSpace ℝ (Fin r))
      (Fintype.equivFin {i : Fin n // η i = true})).prodCongr
    (MeasurableEquiv.piCongrLeft (fun _ => EuclideanSpace ℝ (Fin r))
      (Fintype.equivFin {i : Fin n // ¬η i = true})))

/-- Partition reindexing preserves the product law, proving independence of the groups.](goal) This uses [the stated conclusion](goal). -/
-- @node: signingPartitionReindex_measurePreserving
lemma signingPartitionReindex_measurePreserving (n r : ℕ) (η : Signs n)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P] :
    MeasurePreserving (signingPartitionReindex n r η) (Measure.pi (fun _ : Fin n => P))
      ((Measure.pi (fun _ : Fin (Fintype.card {i : Fin n // η i = true}) => P)).prod
        (Measure.pi (fun _ : Fin (Fintype.card {i : Fin n // ¬η i = true}) => P))) := by
  exact ((measurePreserving_piCongrLeft (fun _ => P)
    (Fintype.equivFin {i : Fin n // η i = true})).prod
    (measurePreserving_piCongrLeft (fun _ => P)
      (Fintype.equivFin {i : Fin n // ¬η i = true}))).comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => P) (fun i => η i = true))

/-- [ A realized partition's cross maximum is bounded by the independent-group
projection maximum after reindexing, including either empty group.](goal) -/
-- @node: signingPartitionCrossMax_le_reindexed
lemma signingPartitionCrossMax_le_reindexed (n r : ℕ) (η : Signs n)
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) :
    signingPartitionCrossMax vs η ≤
      twoGroupCrossMax (signingPartitionReindex n r η vs).1
        (signingPartitionReindex n r η vs).2 := by
  classical
  let I := {i : Fin n // η i = true}
  let J := {i : Fin n // ¬η i = true}
  let eI := Fintype.equivFin I
  let eJ := Fintype.equivFin J
  let x : Fin (Fintype.card I) → EuclideanSpace ℝ (Fin r) := fun i => vs (eI.symm i)
  let y : Fin (Fintype.card J) → EuclideanSpace ℝ (Fin r) := fun j => vs (eJ.symm j)
  simp only [signingPartitionReindex, MeasurableEquiv.trans_apply,
    MeasurableEquiv.prodCongr, MeasurableEquiv.coe_mk,
    Equiv.prodCongr_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply,
    Prod.map_apply, MeasurableEquiv.piCongrLeft]
  have hx : (Equiv.piCongrLeft (fun _ => EuclideanSpace ℝ (Fin r)) eI)
      (fun i : I => vs i) = x := by
    funext i
    simp [Equiv.piCongrLeft_apply, x]
  have hy : (Equiv.piCongrLeft (fun _ => EuclideanSpace ℝ (Fin r)) eJ)
      (fun j : J => vs j) = y := by
    funext j
    simp [Equiv.piCongrLeft_apply, y]
  change signingPartitionCrossMax vs η ≤ twoGroupCrossMax
    ((Equiv.piCongrLeft (fun _ => EuclideanSpace ℝ (Fin r)) eI) (fun i : I => vs i))
    ((Equiv.piCongrLeft (fun _ => EuclideanSpace ℝ (Fin r)) eJ) (fun j : J => vs j))
  rw [hx, hy]
  unfold signingPartitionCrossMax
  apply ciSup_le
  intro z
  let w : Signs (Fintype.card J) := fun j => z (eJ.symm j)
  have hI : (∑ i, if η i = true then sgn (z i) • vs i else 0) =
      ∑ i : Fin (Fintype.card I), sgn (z (eI.symm i)) • x i := by
    rw [signing_sum_select_eq]
    exact (eI.symm.sum_comp (fun i : I => sgn (z i) • vs i)).symm
  have hJ : (∑ j, if η j = false then sgn (z j) • vs j else 0) =
      ∑ j, sgn (w j) • y j := by
    have he (j : Fin n) : (η j = false) ↔ ¬η j = true := by cases η j <;> simp
    simp_rw [he]
    rw [signing_sum_select_eq]
    exact (eJ.symm.sum_comp (fun j : J => sgn (z j) • vs j)).symm
  rw [signingPartitionCross_eq_inner, hI, hJ, sum_inner]
  have hpoint (i : Fin (Fintype.card I)) :
      |inner ℝ (sgn (z (eI.symm i)) • x i) (∑ j, sgn (w j) • y j)| =
        |inner ℝ (∑ j, sgn (w j) • y j) (x i)| := by
    rw [real_inner_smul_left, real_inner_comm]
    cases z (eI.symm i) <;> simp [sgn]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simp_rw [hpoint]
  exact le_ciSup (Finite.bddAbove_range (fun w : Signs (Fintype.card J) =>
    ∑ i, |inner ℝ (∑ j, sgn (w j) • y j) (x i)|)) w

/-- The explicit cross-group error is bounded uniformly over all partitions of n rows. Under [the stated conditions](hyp:hab), [the asserted mathematical result follows](goal). -/
-- @node: signing_group_error_le
lemma signing_group_error_le (a b n r : ℕ) (hab : a + b = n) :
    (a : ℝ) * b + 4 * a * Real.sqrt ((b : ℝ) * r) +
      4 * b * Real.sqrt ((a : ℝ) * r) ≤
        (n : ℝ) ^ 2 / 4 + 4 * n * Real.sqrt ((n : ℝ) * r) := by
  have habR : (a : ℝ) + b = n := by exact_mod_cast hab
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hsa : Real.sqrt ((a : ℝ) * r) ≤ Real.sqrt ((n : ℝ) * r) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (by linarith) hr)
  have hsb : Real.sqrt ((b : ℝ) * r) ≤ Real.sqrt ((n : ℝ) * r) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (by linarith) hr)
  have hm1 := mul_le_mul_of_nonneg_left hsb (by positivity : 0 ≤ 4 * (a : ℝ))
  have hm2 := mul_le_mul_of_nonneg_left hsa (by positivity : 0 ≤ 4 * (b : ℝ))
  have hprod : (a : ℝ) * b ≤ (n : ℝ) ^ 2 / 4 := by nlinarith [sq_nonneg ((a : ℝ) - b)]
  calc
    _ ≤ (a : ℝ) * b + 4 * a * Real.sqrt ((n : ℝ) * r) +
        4 * b * Real.sqrt ((n : ℝ) * r) :=
      add_le_add (add_le_add (le_refl _) hm1) hm2
    _ = (a : ℝ) * b + 4 * n * Real.sqrt ((n : ℝ) * r) := by rw [← habR]; ring
    _ ≤ _ := by linarith [hprod]

/-- [ Each fixed selector satisfies the independent-group cross bound under the
original row law. Reindexing supplies the independence required by the roadmap.](goal) Under [the stated conditions](hyp:hContraction,hmom,hiso). -/
-- @node: signingPartitionCrossMax_integral_le
lemma signingPartitionCrossMax_integral_le (hContraction : ClassicalRademacherContraction)
    (n r : ℕ) (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P)
    (hiso : ∀ h k, (∫ v, v h * v k ∂P) = if h = k then 1 else 0)
    (η : Signs n) :
    (∫ vs : Fin n → EuclideanSpace ℝ (Fin r), signingPartitionCrossMax vs η
      ∂Measure.pi (fun _ : Fin n => P)) ≤
        (n : ℝ) ^ 2 / 4 + 4 * n * Real.sqrt ((n : ℝ) * r) := by
  let a := Fintype.card {i : Fin n // η i = true}
  let b := Fintype.card {i : Fin n // ¬η i = true}
  have hmp := signingPartitionReindex_measurePreserving n r η P
  have hi : Integrable (fun p : (Fin a → EuclideanSpace ℝ (Fin r)) ×
      (Fin b → EuclideanSpace ℝ (Fin r)) => twoGroupCrossMax p.1 p.2)
      ((Measure.pi (fun _ : Fin a => P)).prod (Measure.pi (fun _ : Fin b => P))) :=
    (twoGroupCrossMax_joint_integrable a b r P hmom).swap
  have hmono := integral_mono (signingPartitionCrossMax_integrable n r P hmom η)
    (hmp.integrable_comp_of_integrable hi) (signingPartitionCrossMax_le_reindexed n r η)
  simp only [Function.comp_apply] at hmono
  rw [hmp.integral_comp' (fun p => twoGroupCrossMax p.1 p.2)] at hmono
  rw [integral_prod_symm _ hi] at hmono
  have hcross := independent_group_cross_integral_le_explicit hContraction a b r P hmom hiso
  have hab : a + b = n := by
    dsimp [a, b]
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have hle := Fintype.card_subtype_le (fun i : Fin n => η i = true)
    simp only [Fintype.card_fin] at hle
    omega
  exact hmono.trans (hcross.trans (signing_group_error_le a b n r hab))

/-- [ Averaging the uniform cross bound over fair selectors closes the random-partition
step, with the exact factor four from the ordered-pair selection probability.](goal) Under [the stated conditions](hyp:hContraction,hmom,hiso). -/
-- @node: signingPartitionCross_average_le
lemma signingPartitionCross_average_le (hContraction : ClassicalRademacherContraction)
    (n r : ℕ) (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ h, MemLp (fun v => v h) 2 P)
    (hiso : ∀ h k, (∫ v, v h * v k ∂P) = if h = k then 1 else 0) :
    4 * (∫ vs : Fin n → EuclideanSpace ℝ (Fin r),
      ∫ η, signingPartitionCrossMax vs η ∂fairSigns n
        ∂Measure.pi (fun _ : Fin n => P)) ≤
          (n : ℝ) ^ 2 + 16 * n * Real.sqrt ((n : ℝ) * r) := by
  let := fairSigns_probability n
  have hswap : (∫ vs : Fin n → EuclideanSpace ℝ (Fin r),
      ∫ η, signingPartitionCrossMax vs η ∂fairSigns n
        ∂Measure.pi (fun _ : Fin n => P)) =
      ∫ η, ∫ vs : Fin n → EuclideanSpace ℝ (Fin r), signingPartitionCrossMax vs η
        ∂Measure.pi (fun _ : Fin n => P) ∂fairSigns n := by
    simp_rw [integral_fintype (μ := fairSigns n) (Integrable.of_finite), smul_eq_mul]
    rw [integral_finsetSum _ (fun η _ =>
      (signingPartitionCrossMax_integrable n r P hmom η).const_mul _)]
    simp_rw [integral_const_mul]
  rw [hswap]
  have hbound := integral_mono (μ := fairSigns n) (Integrable.of_finite)
    (integrable_const ((n : ℝ) ^ 2 / 4 + 4 * n * Real.sqrt ((n : ℝ) * r)))
    (signingPartitionCrossMax_integral_le hContraction n r P hmom hiso)
  rw [integral_const] at hbound
  simp only [probReal_univ, one_smul] at hbound
  linarith

/-- [ Independent isotropic rows have the stated expected minimum-signing lower bound.](goal) Under [the stated conditions](hyp:hContraction_of_gate,hr,hmom,hiso). -/
-- @node: lem:isotropic-row-signing
lemma isotropic_row_signing (hContraction_of_gate : ClassicalRademacherContraction)
    (r0 n : ℕ) (hr : 0 < r0) (P : Measure (EuclideanSpace ℝ (Fin r0)))
    [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0) :
    let I := ∫ vs : Fin n → EuclideanSpace ℝ (Fin r0),
      ⨅ z : Signs n, ‖∑ i, sgn (z i) • vs i‖ ^ 2 ∂Measure.pi (fun _ : Fin n => P)
    (n : ℝ) * r0 - (n : ℝ) ^ 2 - 16 * n * Real.sqrt ((n : ℝ) * r0) ≤ I ∧
    (4096 * n ≤ r0 → (n : ℝ) * r0 / 2 ≤ I) := by
  dsimp only
  have hgeneral : (n : ℝ) * r0 - (n : ℝ) ^ 2 -
      16 * n * Real.sqrt ((n : ℝ) * r0) ≤
      ∫ vs : Fin n → EuclideanSpace ℝ (Fin r0),
        ⨅ z : Signs n, ‖∑ i, sgn (z i) • vs i‖ ^ 2
          ∂Measure.pi (fun _ : Fin n => P) := by
    by_cases hn : n ≤ 256
    · exact isotropic_small_sample_signing_lower n r0 hn P hmom hiso
    ·
      have hfluctuation :
          (∫ vs : Fin n → EuclideanSpace ℝ (Fin r0), signingOffDiagonalMax vs
            ∂Measure.pi (fun _ : Fin n => P)) ≤
            (n : ℝ) ^ 2 + 16 * n * Real.sqrt ((n : ℝ) * r0) := by
        have hcross :
            4 * (∫ vs : Fin n → EuclideanSpace ℝ (Fin r0),
              ∫ η, signingPartitionCrossMax vs η ∂fairSigns n
                ∂Measure.pi (fun _ : Fin n => P)) ≤
              (n : ℝ) ^ 2 + 16 * n * Real.sqrt ((n : ℝ) * r0) := by
          exact signingPartitionCross_average_le hContraction_of_gate n r0 P hmom hiso
        exact (signingOffDiagonal_integral_le_partition_average n r0 P hmom).trans hcross
      have hdiagonal := isotropic_signing_lower_of_offDiagonal n r0 P hmom hiso
      linarith
  refine ⟨hgeneral, ?_⟩
  intro hlarge
  have herr := isotropic_signing_error_le_half n r0 hlarge
  linarith


end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

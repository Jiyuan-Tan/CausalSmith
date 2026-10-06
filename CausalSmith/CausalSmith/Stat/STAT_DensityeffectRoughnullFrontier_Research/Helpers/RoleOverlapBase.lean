module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Histogram

/-!
Exact shared-role variance decomposition for rectangular cross averages of a square-integrable
kernel.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Rectangular role-wise cross average. -/
def roleAverage {E : Type*} (d m : ℕ) (h : (Fin d → E) → ℝ)
    (obs : Fin d → Fin m → E) : ℝ :=
  (m : ℝ) ^ (-(d : ℤ)) * ∑ indices : Fin d → Fin m, h (fun r => obs r (indices r))
/-- Integrate out roles outside S, using an independent canonical product. -/
def partialRoleKernel {E : Type*} [MeasurableSpace E] (P : Measure E)
    (d : ℕ) (S : Finset (Fin d)) (h : (Fin d → E) → ℝ) (obs : Fin d → E) : ℝ :=
  ∫ z, h (fun r => if r ∈ S then obs r else z r) ∂Measure.pi (fun _ => P)

/-- Splicing independent coordinate vectors along a fixed role set preserves the kernel law. -/
-- @node: role_splice_measurePreserving
lemma role_splice_measurePreserving {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ) (S : Finset (Fin d)) :
    MeasurePreserving
      (fun oz : (Fin d → E) × (Fin d → E) =>
        fun r => if r ∈ S then oz.1 r else oz.2 r)
      ((Measure.pi (fun _ : Fin d => P)).prod (Measure.pi (fun _ : Fin d => P)))
      (Measure.pi (fun _ : Fin d => P)) := by
  classical
  have hcoord (r : Fin d) :
      MeasurePreserving (fun z : E × E => if r ∈ S then z.1 else z.2)
        (P.prod P) P := by
    by_cases hr : r ∈ S
    · simpa [hr] using (measurePreserving_fst (μ := P) (ν := P))
    · simpa [hr] using (measurePreserving_snd (μ := P) (ν := P))
  exact (measurePreserving_pi _ _ hcoord).comp
    ((measurePreserving_arrowProdEquivProdArrow E E (Fin d) (fun _ => P)
      (fun _ => P)).symm _)

/-- The spliced kernel is integrable by transport from its original product law. -/
-- @node: role_spliced_kernel_integrable
lemma role_spliced_kernel_integrable {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ) (S : Finset (Fin d))
    (h : (Fin d → E) → ℝ) (hi : Integrable h (Measure.pi (fun _ : Fin d => P))) :
    Integrable (fun oz : (Fin d → E) × (Fin d → E) =>
      h (fun r => if r ∈ S then oz.1 r else oz.2 r))
      ((Measure.pi (fun _ : Fin d => P)).prod (Measure.pi (fun _ : Fin d => P))) := by
  exact (role_splice_measurePreserving P d S).integrable_comp_of_integrable hi

/-- Partial integration is integrable without a separate regularity premise. -/
-- @node: partial_role_kernel_integrable
lemma partial_role_kernel_integrable {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ) (S : Finset (Fin d))
    (h : (Fin d → E) → ℝ) (hi : Integrable h (Measure.pi (fun _ : Fin d => P))) :
    Integrable (partialRoleKernel P d S h) (Measure.pi (fun _ : Fin d => P)) := by
  exact (role_spliced_kernel_integrable P d S h hi).integral_prod_left

/-- Fubini and the spliced product law identify the common mean in the overlap proof. -/
-- @node: partial_role_kernel_mean
lemma partial_role_kernel_mean {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ) (S : Finset (Fin d))
    (h : (Fin d → E) → ℝ) (hi : Integrable h (Measure.pi (fun _ : Fin d => P))) :
    (∫ obs, partialRoleKernel P d S h obs ∂Measure.pi (fun _ : Fin d => P)) =
      ∫ obs, h obs ∂Measure.pi (fun _ : Fin d => P) := by
  unfold partialRoleKernel
  rw [integral_integral (role_spliced_kernel_integrable P d S h hi)]
  have hp := role_splice_measurePreserving P d S
  have heq := integral_map hp.aemeasurable (hp.map_eq.symm ▸ hi.aestronglyMeasurable)
  rw [hp.map_eq] at heq
  exact heq.symm

/-- The square of a partial expectation is bounded by the partial second moment almost surely. -/
-- @node: partial_role_kernel_sq_le
lemma partial_role_kernel_sq_le {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ) (S : Finset (Fin d))
    (h : (Fin d → E) → ℝ) (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin d => P))) :
    ∀ᵐ obs ∂Measure.pi (fun _ : Fin d => P),
      (partialRoleKernel P d S h obs) ^ 2 ≤
        partialRoleKernel P d S (fun z => (h z) ^ 2) obs := by
  have hi := role_spliced_kernel_integrable P d S h (hL2.integrable (by norm_num))
  have hi2 := role_spliced_kernel_integrable P d S (fun z => (h z) ^ 2)
    hL2.integrable_sq
  filter_upwards [hi.prod_right_ae, hi2.prod_right_ae] with obs hobs hobs2
  have hs : MemLp (fun z => h (fun r => if r ∈ S then obs r else z r)) 2
      (Measure.pi (fun _ : Fin d => P)) :=
    (memLp_two_iff_integrable_sq hobs.aestronglyMeasurable).2 hobs2
  have hv := variance_nonneg (fun z => h (fun r => if r ∈ S then obs r else z r))
    (Measure.pi (fun _ : Fin d => P))
  rw [variance_eq_sub hs] at hv
  exact sub_nonneg.mp hv

/-- Partial expectations of square-integrable kernels remain square integrable. -/
-- @node: partial_role_kernel_memLp
lemma partial_role_kernel_memLp {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ) (S : Finset (Fin d))
    (h : (Fin d → E) → ℝ) (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin d => P))) :
    MemLp (partialRoleKernel P d S h) 2 (Measure.pi (fun _ : Fin d => P)) := by
  have hi := partial_role_kernel_integrable P d S h (hL2.integrable (by norm_num))
  apply (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).2
  apply (partial_role_kernel_integrable P d S (fun z => (h z) ^ 2)
    hL2.integrable_sq).mono' (hi.aestronglyMeasurable.pow 2)
  filter_upwards [partial_role_kernel_sq_le P d S h hL2] with obs hobs
  change ‖(partialRoleKernel P d S h obs) ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hobs

/-- Integrating the partial second-moment bound preserves the original second-moment budget. -/
-- @node: partial_role_kernel_second_moment_le
lemma partial_role_kernel_second_moment_le {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ) (S : Finset (Fin d))
    (h : (Fin d → E) → ℝ) (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin d => P))) :
    (∫ obs, (partialRoleKernel P d S h obs) ^ 2 ∂Measure.pi (fun _ : Fin d => P)) ≤
      ∫ obs, (h obs) ^ 2 ∂Measure.pi (fun _ : Fin d => P) := by
  calc
    _ ≤ ∫ obs, partialRoleKernel P d S (fun z => (h z) ^ 2) obs
        ∂Measure.pi (fun _ : Fin d => P) :=
      integral_mono_ae (partial_role_kernel_memLp P d S h hL2).integrable_sq
        (partial_role_kernel_integrable P d S _ hL2.integrable_sq)
        (partial_role_kernel_sq_le P d S h hL2)
    _ = _ := partial_role_kernel_mean P d S _ hL2.integrable_sq

/-- The common-mean identity turns second-moment contraction into variance contraction. -/
-- @node: partial_role_kernel_variance_le
lemma partial_role_kernel_variance_le {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ) (S : Finset (Fin d))
    (h : (Fin d → E) → ℝ) (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin d => P))) :
    variance (partialRoleKernel P d S h) (Measure.pi (fun _ : Fin d => P)) ≤
      variance h (Measure.pi (fun _ : Fin d => P)) := by
  rw [variance_eq_sub (partial_role_kernel_memLp P d S h hL2), variance_eq_sub hL2]
  rw [partial_role_kernel_mean P d S h (hL2.integrable (by norm_num))]
  exact sub_le_sub_right (partial_role_kernel_second_moment_le P d S h hL2) _

/-- A partial kernel depends only on the roles retained in its conditioning set. -/
-- @node: partial_role_kernel_congr_shared
lemma partial_role_kernel_congr_shared {E : Type*} [MeasurableSpace E]
    (P : Measure E) (d : ℕ) (S : Finset (Fin d)) (h : (Fin d → E) → ℝ)
    (obs obs' : Fin d → E) (heq : ∀ r ∈ S, obs r = obs' r) :
    partialRoleKernel P d S h obs = partialRoleKernel P d S h obs' := by
  classical
  unfold partialRoleKernel
  congr 1
  funext z
  congr 1
  funext r
  by_cases hr : r ∈ S
  · simp [hr, heq r hr]
  · simp [hr]

/-- Retaining every role leaves the kernel itself under a probability product. -/
-- @node: partial_role_kernel_univ
lemma partial_role_kernel_univ {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ) (h : (Fin d → E) → ℝ) :
    partialRoleKernel P d Finset.univ h = h := by
  classical
  funext obs
  simp [partialRoleKernel]

/-- Selecting one observation in each independent role has the canonical product law. -/
-- @node: role_selection_measurePreserving
lemma role_selection_measurePreserving {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d m : ℕ) (indices : Fin d → Fin m) :
    MeasurePreserving (fun obs : Fin d → Fin m → E => fun r => obs r (indices r))
      (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => P)))
      (Measure.pi (fun _ : Fin d => P)) := by
  exact measurePreserving_pi _ _ (fun r => measurePreserving_eval _ (indices r))

/-- Every selected tuple has the original kernel variance. -/
-- @node: role_selected_kernel_variance
lemma role_selected_kernel_variance {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d m : ℕ)
    (h : (Fin d → E) → ℝ) (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin d => P)))
    (indices : Fin d → Fin m) :
    variance (fun obs : Fin d → Fin m → E => h (fun r => obs r (indices r)))
      (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => P))) =
      variance h (Measure.pi (fun _ : Fin d => P)) := by
  exact (role_selection_measurePreserving P d m indices).variance_fun_comp hL2.aemeasurable

/-- Square integrability survives selection of one record per independent role. -/
-- @node: role_selected_kernel_memLp
lemma role_selected_kernel_memLp {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d m : ℕ)
    (h : (Fin d → E) → ℝ) (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin d => P)))
    (indices : Fin d → Fin m) :
    MemLp (fun obs : Fin d → Fin m → E => h (fun r => obs r (indices r))) 2
      (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => P))) := by
  exact hL2.comp_measurePreserving (role_selection_measurePreserving P d m indices)

/-- The variance of a rectangular average is its normalization squared times the sum
of pairwise kernel covariances, the first step of the exact-overlap argument. -/
-- @node: role_average_variance_expansion
lemma role_average_variance_expansion {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d m : ℕ)
    (h : (Fin d → E) → ℝ) (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin d => P))) :
    variance (roleAverage d m h)
      (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => P))) =
    ((m : ℝ) ^ (-(d : ℤ))) ^ 2 *
      ∑ i : Fin d → Fin m, ∑ j : Fin d → Fin m,
        covariance (fun obs => h (fun r => obs r (i r)))
          (fun obs => h (fun r => obs r (j r)))
          (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => P))) := by
  unfold roleAverage
  rw [variance_const_mul, variance_fun_sum]
  intro i
  exact role_selected_kernel_memLp P d m h hL2 i

/-- After fixing the first tuple, exactly the roles in S are forced; all other roles
have m minus one choices. This includes the empty-product case m = 1. -/
-- @node: exact_overlap_configuration_count
lemma exact_overlap_configuration_count (d m : ℕ) (i : Fin d → Fin m)
    (S : Finset (Fin d)) :
    Fintype.card {j : Fin d → Fin m //
      ∀ r, if r ∈ S then j r = i r else j r ≠ i r} = (m - 1) ^ (d - S.card) := by
  classical
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi (β := fun _ : Fin d => Fin m)
    (p := fun r v => if r ∈ S then v = i r else v ≠ i r)), Fintype.card_pi]
  have coordinate_count (r : Fin d) :
      Fintype.card {v : Fin m // if r ∈ S then v = i r else v ≠ i r} =
        if r ∈ S then 1 else m - 1 := by
    by_cases hr : r ∈ S
    · simp [hr]
    · simp [hr, Fintype.card_subtype_compl]
  simp_rw [coordinate_count]
  rw [Finset.prod_ite]
  rw [← Finset.sdiff_eq_filter]
  simp [Finset.card_sdiff]

/-- The exact set of roles for which two index tuples use the same observation. -/
-- @node: sharedRoleSet
def sharedRoleSet (d m : ℕ) (i j : Fin d → Fin m) : Finset (Fin d) :=
  Finset.univ.filter (fun r => j r = i r)

/-- A tuple paired with itself shares all roles. -/
-- @node: shared_role_set_self
lemma shared_role_set_self (d m : ℕ) (i : Fin d → Fin m) :
    sharedRoleSet d m i i = Finset.univ := by
  classical
  simp [sharedRoleSet]

/-- The completely shared covariance is the original variance, and its partial kernel is h. -/
-- @node: fully_shared_role_covariance
lemma fully_shared_role_covariance {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d m : ℕ)
    (h : (Fin d → E) → ℝ) (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin d => P)))
    (i : Fin d → Fin m) :
    covariance (fun obs => h (fun r => obs r (i r)))
      (fun obs => h (fun r => obs r (i r)))
      (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => P))) =
    variance (partialRoleKernel P d (sharedRoleSet d m i i) h)
      (Measure.pi (fun _ : Fin d => P)) := by
  rw [shared_role_set_self, partial_role_kernel_univ,
    covariance_self (role_selected_kernel_memLp P d m h hL2 i).aemeasurable]
  exact role_selected_kernel_variance P d m h hL2 i

/-- Equality to an overlap pattern is the coordinatewise forced-or-distinct constraint. -/
-- @node: sharedRoleSet_eq_iff
lemma sharedRoleSet_eq_iff (d m : ℕ) (i j : Fin d → Fin m) (S : Finset (Fin d)) :
    sharedRoleSet d m i j = S ↔
      ∀ r, if r ∈ S then j r = i r else j r ≠ i r := by
  classical
  constructor
  · intro hs r
    have hr : j r = i r ↔ r ∈ S := by
      simpa [sharedRoleSet] using (Finset.ext_iff.mp hs r)
    split <;> simp_all
  · intro hs
    ext r
    simp only [sharedRoleSet, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hr : r ∈ S
    · exact iff_of_true (by simpa [hr] using hs r) hr
    · exact iff_of_false (by simpa [hr] using hs r) hr

/-- Each exact-overlap fiber has the configuration count from the roadmap. -/
-- @node: shared_role_fiber_card
lemma shared_role_fiber_card (d m : ℕ) (i : Fin d → Fin m) (S : Finset (Fin d)) :
    (Finset.univ.filter (fun j => sharedRoleSet d m i j = S)).card =
      (m - 1) ^ (d - S.card) := by
  classical
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun j => sharedRoleSet_eq_iff d m i j S))]
  exact exact_overlap_configuration_count d m i S

/-- Grouping the second tuple by its shared roles multiplies each pattern value by
its exact number of configurations. -/
-- @node: shared_role_sum_count
lemma shared_role_sum_count (d m : ℕ) (i : Fin d → Fin m)
    (f : Finset (Fin d) → ℝ) :
    ∑ j : Fin d → Fin m, f (sharedRoleSet d m i j) =
      ∑ S : Finset (Fin d), ((m - 1) ^ (d - S.card) : ℕ) * f S := by
  classical
  rw [← Finset.sum_fiberwise' Finset.univ (sharedRoleSet d m i) f]
  simp only [Finset.sum_const, nsmul_eq_mul, shared_role_fiber_card]

/-- Integrating out every role gives the constant kernel mean. -/
-- @node: partial_role_kernel_empty
lemma partial_role_kernel_empty {E : Type*} [MeasurableSpace E]
    (P : Measure E) (d : ℕ) (h : (Fin d → E) → ℝ) :
    partialRoleKernel P d ∅ h = fun _ => ∫ z, h z ∂Measure.pi (fun _ : Fin d => P) := by
  funext obs
  simp [partialRoleKernel]

/-- The empty overlap pattern has zero variance, so it drops out of the expansion. -/
-- @node: partial_role_kernel_empty_variance
lemma partial_role_kernel_empty_variance {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ) (h : (Fin d → E) → ℝ) :
    variance (partialRoleKernel P d ∅ h) (Measure.pi (fun _ : Fin d => P)) = 0 := by
  rw [partial_role_kernel_empty]
  simp [variance, evariance]

/-- Counting both tuples and applying the squared averaging normalization gives exactly
the nonempty-pattern weights in the variance identity. -/
-- @node: normalized_shared_role_sum
lemma normalized_shared_role_sum (d m : ℕ) (hm : 1 ≤ m)
    (f : Finset (Fin d) → ℝ) (hf : f ∅ = 0) :
    ((m : ℝ) ^ (-(d : ℤ))) ^ 2 *
      (∑ i : Fin d → Fin m, ∑ j : Fin d → Fin m, f (sharedRoleSet d m i j)) =
    ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.erase ∅,
      ((m - 1 : ℕ) : ℝ) ^ (d - S.card) / (m : ℝ) ^ d * f S := by
  classical
  simp_rw [shared_role_sum_count]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, Nat.cast_pow]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hp : (Finset.univ : Finset (Fin d)).powerset = Finset.univ := by
    ext S
    simp
  rw [hp]
  have hfull :
      ∑ S : Finset (Fin d), ((m - 1 : ℕ) : ℝ) ^ (d - S.card) / (m : ℝ) ^ d * f S =
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
        ((m - 1 : ℕ) : ℝ) ^ (d - S.card) / (m : ℝ) ^ d * f S := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ ∅)]
    simp [hf]
  rw [← hfull, ← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [Nat.cast_pow, zpow_neg, zpow_natCast]
  field_simp

/-- Two tuples with no shared coordinates have independent canonical kernel arguments. -/
-- @node: disjoint_role_pair_measurePreserving
lemma disjoint_role_pair_measurePreserving {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d m : ℕ) (i j : Fin d → Fin m)
    (hne : ∀ r, i r ≠ j r) :
    MeasurePreserving
      (fun obs : Fin d → Fin m → E =>
        ((fun r => obs r (i r)), (fun r => obs r (j r))))
      (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => P)))
      ((Measure.pi (fun _ : Fin d => P)).prod (Measure.pi (fun _ : Fin d => P))) := by
  have hcoord (r : Fin d) :
      MeasurePreserving (fun obs : Fin m → E => (obs (i r), obs (j r)))
        (Measure.pi (fun _ : Fin m => P)) (P.prod P) := by
    refine ⟨by fun_prop, ?_⟩
    have hi : iIndepFun (fun k : Fin m => fun obs : Fin m → E => obs k)
        (Measure.pi (fun _ : Fin m => P)) :=
      iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
    have hij := (hi.indepFun (hne r)).map_prod_eq_prod_map_map
      (measurePreserving_eval (fun _ : Fin m => P) (i r)).aemeasurable
      (measurePreserving_eval (fun _ : Fin m => P) (j r)).aemeasurable
    simpa only [(measurePreserving_eval (fun _ : Fin m => P) (i r)).map_eq,
      (measurePreserving_eval (fun _ : Fin m => P) (j r)).map_eq] using hij
  exact (measurePreserving_arrowProdEquivProdArrow E E (Fin d) (fun _ => P)
    (fun _ => P)).comp (measurePreserving_pi _ _ hcoord)

/-- No shared observations means zero covariance, exactly the empty-pattern contribution. -/
-- @node: disjoint_role_covariance
lemma disjoint_role_covariance {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d m : ℕ)
    (h : (Fin d → E) → ℝ) (hMeas : Measurable h)
    (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin d => P)))
    (i j : Fin d → Fin m) (hne : ∀ r, i r ≠ j r) :
    covariance (fun obs => h (fun r => obs r (i r)))
      (fun obs => h (fun r => obs r (j r)))
      (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => P))) = 0 := by
  have hind : IndepFun (fun obs : Fin d → Fin m → E => fun r => obs r (i r))
      (fun obs : Fin d → Fin m → E => fun r => obs r (j r))
      (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => P))) := by
    apply (indepFun_iff_map_prod_eq_prod_map_map
      (role_selection_measurePreserving P d m i).aemeasurable
      (role_selection_measurePreserving P d m j).aemeasurable).2
    rw [(role_selection_measurePreserving P d m i).map_eq,
      (role_selection_measurePreserving P d m j).map_eq]
    exact (disjoint_role_pair_measurePreserving P d m i j hne).map_eq
  exact (hind.comp hMeas hMeas).covariance_eq_zero
    (role_selected_kernel_memLp P d m h hL2 i) (role_selected_kernel_memLp P d m h hL2 j)

/-- With one observation per role every pair of tuples is identical; the exact identity
therefore holds, including its zero-exponent empty-product convention. -/
-- @node: exact_role_overlap_variance_one_sample
lemma exact_role_overlap_variance_one_sample {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ)
    (h : (Fin d → E) → ℝ) (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin d => P))) :
    variance (roleAverage d 1 h)
      (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin 1 => P))) =
    ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.erase ∅,
      ((1 - 1 : ℕ) : ℝ) ^ (d - S.card) / (1 : ℝ) ^ d *
        variance (partialRoleKernel P d S h) (Measure.pi (fun _ : Fin d => P)) := by
  classical
  rw [role_average_variance_expansion P d 1 h hL2]
  have heq (i j : Fin d → Fin 1) : j = i := Subsingleton.elim _ _
  have hcov (i j : Fin d → Fin 1) :
      covariance (fun obs => h (fun r => obs r (i r)))
        (fun obs => h (fun r => obs r (j r)))
        (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin 1 => P))) =
      variance (partialRoleKernel P d (sharedRoleSet d 1 i j) h)
        (Measure.pi (fun _ : Fin d => P)) := by
    rw [heq i j]
    exact fully_shared_role_covariance P d 1 h hL2 i
  simp_rw [hcov]
  simpa only [Nat.cast_one] using normalized_shared_role_sum d 1 (by norm_num)
    (fun S => variance (partialRoleKernel P d S h) (Measure.pi (fun _ : Fin d => P)))
    (partial_role_kernel_empty_variance P d h)

end CausalSmith.Stat.DensityEffectRoughNull

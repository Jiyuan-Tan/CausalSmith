module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RoleOverlapBase

/-!
Cross moments of kernels with shared observations and independent remaining roles. Transport
both sampled tuples and canonical splices to the same coordinatewise pair law; Fubini then
identifies their covariance with the variance of the partial-role kernel.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The left spliced argument has the original product law. -/
-- @node: shared_role_left_splice_measurePreserving
lemma shared_role_left_splice_measurePreserving {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ) (S : Finset (Fin d)) :
    MeasurePreserving
      (fun oz : (Fin d → E) × ((Fin d → E) × (Fin d → E)) =>
        fun r => if r ∈ S then oz.1 r else oz.2.1 r)
      ((Measure.pi (fun _ : Fin d => P)).prod
        ((Measure.pi (fun _ : Fin d => P)).prod (Measure.pi (fun _ : Fin d => P))))
      (Measure.pi (fun _ : Fin d => P)) := by
  exact (role_splice_measurePreserving P d S).comp
    ((MeasurePreserving.id _).prod (measurePreserving_fst (μ := Measure.pi (fun _ : Fin d => P))
      (ν := Measure.pi (fun _ : Fin d => P))))

/-- The right spliced argument has the original product law. -/
-- @node: shared_role_right_splice_measurePreserving
lemma shared_role_right_splice_measurePreserving {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ) (S : Finset (Fin d)) :
    MeasurePreserving
      (fun oz : (Fin d → E) × ((Fin d → E) × (Fin d → E)) =>
        fun r => if r ∈ S then oz.1 r else oz.2.2 r)
      ((Measure.pi (fun _ : Fin d => P)).prod
        ((Measure.pi (fun _ : Fin d => P)).prod (Measure.pi (fun _ : Fin d => P))))
      (Measure.pi (fun _ : Fin d => P)) := by
  exact (role_splice_measurePreserving P d S).comp
    ((MeasurePreserving.id _).prod (measurePreserving_snd (μ := Measure.pi (fun _ : Fin d => P))
      (ν := Measure.pi (fun _ : Fin d => P))))

/-- Square integrability justifies the shared-role cross moment without an extra assumption. -/
-- @node: shared_role_spliced_product_integrable
lemma shared_role_spliced_product_integrable {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ) (S : Finset (Fin d))
    (h : (Fin d → E) → ℝ) (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin d => P))) :
    Integrable
      (fun oz : (Fin d → E) × ((Fin d → E) × (Fin d → E)) =>
        h (fun r => if r ∈ S then oz.1 r else oz.2.1 r) *
          h (fun r => if r ∈ S then oz.1 r else oz.2.2 r))
      ((Measure.pi (fun _ : Fin d => P)).prod
        ((Measure.pi (fun _ : Fin d => P)).prod (Measure.pi (fun _ : Fin d => P)))) := by
  exact (hL2.comp_measurePreserving
    (shared_role_left_splice_measurePreserving P d S)).integrable_mul
    (hL2.comp_measurePreserving (shared_role_right_splice_measurePreserving P d S))

/-- Holding the shared roles fixed, the unshared arguments integrate independently. -/
-- @node: shared_role_spliced_product_moment
lemma shared_role_spliced_product_moment {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ) (S : Finset (Fin d))
    (h : (Fin d → E) → ℝ) (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin d => P))) :
    (∫ oz : (Fin d → E) × ((Fin d → E) × (Fin d → E)),
        h (fun r => if r ∈ S then oz.1 r else oz.2.1 r) *
          h (fun r => if r ∈ S then oz.1 r else oz.2.2 r)
      ∂(Measure.pi (fun _ : Fin d => P)).prod
        ((Measure.pi (fun _ : Fin d => P)).prod (Measure.pi (fun _ : Fin d => P)))) =
      ∫ obs, (partialRoleKernel P d S h obs) ^ 2 ∂Measure.pi (fun _ : Fin d => P) := by
  rw [integral_prod _ (shared_role_spliced_product_integrable P d S h hL2)]
  apply integral_congr_ae
  filter_upwards [] with obs
  simpa only [partialRoleKernel, pow_two] using
    (integral_prod_mul (μ := Measure.pi (fun _ : Fin d => P))
      (ν := Measure.pi (fun _ : Fin d => P))
      (fun z => h (fun r => if r ∈ S then obs r else z r))
      (fun z => h (fun r => if r ∈ S then obs r else z r)))

/-- The covariance of two conditionally independent splices is the partial-kernel variance. -/
-- @node: shared_role_spliced_covariance
lemma shared_role_spliced_covariance {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d : ℕ) (S : Finset (Fin d))
    (h : (Fin d → E) → ℝ) (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin d => P))) :
    covariance
      (fun oz : (Fin d → E) × ((Fin d → E) × (Fin d → E)) =>
        h (fun r => if r ∈ S then oz.1 r else oz.2.1 r))
      (fun oz : (Fin d → E) × ((Fin d → E) × (Fin d → E)) =>
        h (fun r => if r ∈ S then oz.1 r else oz.2.2 r))
      ((Measure.pi (fun _ : Fin d => P)).prod
        ((Measure.pi (fun _ : Fin d => P)).prod (Measure.pi (fun _ : Fin d => P)))) =
      variance (partialRoleKernel P d S h) (Measure.pi (fun _ : Fin d => P)) := by
  have hl2 : MemLp
      (fun oz : (Fin d → E) × ((Fin d → E) × (Fin d → E)) =>
        h (fun r => if r ∈ S then oz.1 r else oz.2.1 r)) 2 _ :=
    hL2.comp_measurePreserving (shared_role_left_splice_measurePreserving P d S)
  have hr2 : MemLp
      (fun oz : (Fin d → E) × ((Fin d → E) × (Fin d → E)) =>
        h (fun r => if r ∈ S then oz.1 r else oz.2.2 r)) 2 _ :=
    hL2.comp_measurePreserving (shared_role_right_splice_measurePreserving P d S)
  rw [covariance_eq_sub hl2 hr2,
    variance_eq_sub (partial_role_kernel_memLp P d S h hL2)]
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [shared_role_spliced_product_moment P d S h hL2,
    partial_role_kernel_mean P d S h (hL2.integrable (by norm_num))]
  have hl := shared_role_left_splice_measurePreserving P d S
  have hr := shared_role_right_splice_measurePreserving P d S
  have hml := integral_map hl.aemeasurable (hl.map_eq.symm ▸ hL2.aestronglyMeasurable)
  have hmr := integral_map hr.aemeasurable (hr.map_eq.symm ▸ hL2.aestronglyMeasurable)
  rw [hl.map_eq] at hml
  rw [hr.map_eq] at hmr
  rw [← hml, ← hmr, pow_two]


/-- Each role contributes a diagonal law when its two indices agree, otherwise a product law. -/
-- @node: rolePairLaw
def rolePairLaw {E : Type*} [MeasurableSpace E] (P : Measure E)
    (d m : ℕ) (i j : Fin d → Fin m) : Measure (Fin d → E × E) :=
  Measure.pi (fun r => if i r = j r then P.map (fun x => (x, x)) else P.prod P)

/-- A pair of evaluations in one role has its diagonal or independent product law. -/
-- @node: role_pair_coordinate_measurePreserving
lemma role_pair_coordinate_measurePreserving {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (m : ℕ) (i j : Fin m) :
    MeasurePreserving (fun obs : Fin m → E => (obs i, obs j))
      (Measure.pi (fun _ : Fin m => P))
      (if i = j then P.map (fun x => (x, x)) else P.prod P) := by
  classical
  by_cases hij : i = j
  · subst j
    simpa only [if_pos rfl, ↓reduceIte, Function.comp_def, Function.eval] using
      (show MeasurePreserving (fun x : E => (x, x)) P
      (P.map (fun x => (x, x))) from ⟨by fun_prop, rfl⟩).comp
      (measurePreserving_eval (fun _ : Fin m => P) i)
  · simp only [hij, ↓reduceIte]
    refine ⟨by fun_prop, ?_⟩
    have hi : iIndepFun (fun k : Fin m => fun obs : Fin m → E => obs k)
        (Measure.pi (fun _ : Fin m => P)) :=
      iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
    have heq := (hi.indepFun hij).map_prod_eq_prod_map_map
      (measurePreserving_eval (fun _ : Fin m => P) i).aemeasurable
      (measurePreserving_eval (fun _ : Fin m => P) j).aemeasurable
    simpa only [(measurePreserving_eval (fun _ : Fin m => P) i).map_eq,
      (measurePreserving_eval (fun _ : Fin m => P) j).map_eq] using heq

/-- Independence across roles assembles the pair laws into their finite product. -/
-- @node: role_pair_measurePreserving
lemma role_pair_measurePreserving {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d m : ℕ) (i j : Fin d → Fin m) :
    MeasurePreserving (fun obs : Fin d → Fin m → E => fun r => (obs r (i r), obs r (j r)))
      (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => P)))
      (rolePairLaw P d m i j) := by
  classical
  have (r : Fin d) : IsProbabilityMeasure
      (if i r = j r then P.map (fun x => (x, x)) else P.prod P) := by
    split_ifs
    · exact Measure.isProbabilityMeasure_map (by fun_prop)
    · infer_instance
  exact measurePreserving_pi _ _ (fun r => role_pair_coordinate_measurePreserving P m (i r) (j r))

/-- Independent canonical vectors reproduce exactly the same shared-role pair law. -/
-- @node: shared_role_pair_measurePreserving
lemma shared_role_pair_measurePreserving {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d m : ℕ) (i j : Fin d → Fin m) :
    MeasurePreserving
      (fun oz : (Fin d → E) × ((Fin d → E) × (Fin d → E)) => fun r =>
        (if r ∈ sharedRoleSet d m i j then oz.1 r else oz.2.1 r,
         if r ∈ sharedRoleSet d m i j then oz.1 r else oz.2.2 r))
      ((Measure.pi (fun _ : Fin d => P)).prod
        ((Measure.pi (fun _ : Fin d => P)).prod (Measure.pi (fun _ : Fin d => P))))
      (rolePairLaw P d m i j) := by
  classical
  have hc (r : Fin d) : MeasurePreserving
      (fun z : E × (E × E) =>
        (if r ∈ sharedRoleSet d m i j then z.1 else z.2.1,
         if r ∈ sharedRoleSet d m i j then z.1 else z.2.2))
      (P.prod (P.prod P)) (if i r = j r then P.map (fun x => (x, x)) else P.prod P) := by
    by_cases hij : i r = j r
    · have hmem : r ∈ sharedRoleSet d m i j := by simp [sharedRoleSet, hij.symm]
      simpa only [hmem, ↓reduceIte, hij, Function.comp_def] using
        (show MeasurePreserving (fun x : E => (x, x)) P
          (P.map (fun x => (x, x))) from ⟨by fun_prop, rfl⟩).comp
          (measurePreserving_fst (μ := P) (ν := P.prod P))
    · have hmem : r ∉ sharedRoleSet d m i j := by simp [sharedRoleSet, Ne.symm hij]
      simpa only [hmem, ↓reduceIte, hij, Function.comp_def] using
        (measurePreserving_snd (μ := P) (ν := P.prod P))
  have (r : Fin d) : IsProbabilityMeasure
      (if i r = j r then P.map (fun x => (x, x)) else P.prod P) := by
    split_ifs
    · exact Measure.isProbabilityMeasure_map (by fun_prop)
    · infer_instance
  exact (measurePreserving_pi _ _ hc).comp
    (((measurePreserving_arrowProdEquivProdArrow E (E × E) (Fin d)
      (fun _ => P) (fun _ => P.prod P)).symm _).comp
      ((MeasurePreserving.id _).prod
        ((measurePreserving_arrowProdEquivProdArrow E E (Fin d)
          (fun _ => P) (fun _ => P)).symm _)))

/-- Transport to the common pair law reduces sampled overlap covariance to the spliced moment. -/
-- @node: partial_overlap_role_covariance
lemma partial_overlap_role_covariance {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (d m : ℕ)
    (h : (Fin d → E) → ℝ) (hMeas : Measurable h)
    (hL2 : MemLp h 2 (Measure.pi (fun _ : Fin d => P)))
    (i j : Fin d → Fin m) :
    covariance (fun obs => h (fun r => obs r (i r)))
      (fun obs => h (fun r => obs r (j r)))
      (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => P))) =
    variance (partialRoleKernel P d (sharedRoleSet d m i j) h)
      (Measure.pi (fun _ : Fin d => P)) := by
  let f : (Fin d → E × E) → ℝ := fun z => h (fun r => (z r).1)
  let g : (Fin d → E × E) → ℝ := fun z => h (fun r => (z r).2)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hs := role_pair_measurePreserving P d m i j
  have ht := shared_role_pair_measurePreserving P d m i j
  have hsample := covariance_map_fun (hf.aestronglyMeasurable (μ := _))
    (hg.aestronglyMeasurable (μ := _)) hs.aemeasurable
  have hsplice := covariance_map_fun (hf.aestronglyMeasurable (μ := _))
    (hg.aestronglyMeasurable (μ := _)) ht.aemeasurable
  rw [hs.map_eq] at hsample
  rw [ht.map_eq] at hsplice
  change covariance (fun obs : Fin d → Fin m → E => f (fun r => (obs r (i r), obs r (j r))))
    (fun obs => g (fun r => (obs r (i r), obs r (j r)))) _ = _
  rw [← hsample, hsplice]
  exact shared_role_spliced_covariance P d (sharedRoleSet d m i j) h hL2

end CausalSmith.Stat.DensityEffectRoughNull

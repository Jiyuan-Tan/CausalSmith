module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.RectangularRoleTransport

/-! # Joint law of the original-record roles
An iid full-observation representation projects the auxiliary records to treatment
records. Selecting disjoint index blocks then gives exactly the independent role
product law needed by the rectangular variance calculation.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Disjoint injective selections from an iid sequence have the independent block law.  Given [the specified input N](hyp:N), [the specified input t](hyp:t), [the specified input ell](hyp:ell), [the specified input i](hyp:i), [the specified input j](hyp:j), [the specified input hi](hyp:hi), [the specified input hj](hyp:hj), [the specified input hij](hyp:hij), [the rectangular iid block law conclusion](goal) holds. -/
lemma rectangular_iid_block_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N t ell : ℕ)
    (i : Fin t → Fin N) (j : Fin ell → Fin N)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hij : ∀ a b, i a ≠ j b) :
    MeasurePreserving (fun D : Fin N → Ω => ((fun a => D (i a)), (fun b => D (j b))))
      (Measure.pi (fun _ : Fin N => μ))
      ((Measure.pi (fun _ : Fin t => μ)).prod (Measure.pi (fun _ : Fin ell => μ))) := by
  classical
  let s : Fin t ⊕ Fin ell → Fin N := Sum.elim i j
  have hs : Function.Injective s := by
    intro a b hab
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg Sum.inl (hi hab)
      | inr b => exact False.elim (hij a b hab)
    | inr a => cases b with
      | inl b => exact False.elim (hij b a hab.symm)
      | inr b => exact congrArg Sum.inr (hj hab)
  have hind := (iIndepFun_pi (μ := fun _ : Fin N => μ)
    (X := fun _ => id) (fun _ => aemeasurable_id)).precomp hs
  have hm := (iIndepFun_iff_map_fun_eq_pi_map
    (fun a : Fin t ⊕ Fin ell => (measurable_pi_apply (s a)).aemeasurable)).mp hind
  simp only [(measurePreserving_eval (fun _ : Fin N => μ) _).map_eq] at hm
  have hsel : MeasurePreserving (fun D : Fin N → Ω => fun a => D (s a))
      (Measure.pi (fun _ : Fin N => μ)) (Measure.pi (fun _ : Fin t ⊕ Fin ell => μ)) :=
    ⟨by fun_prop, hm⟩
  exact (measurePreserving_sumPiEquivProdPi (fun _ : Fin t ⊕ Fin ell => μ)).comp hsel

/-- Projecting outcome-free records from a longer iid observation sequence realizes the dataset law.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the rectangular iid dataset law conclusion](goal) holds. -/
lemma rectangular_iid_dataset_law {d n m : ℕ} (P : PrimitiveLaw d) :
    MeasurePreserving
      (fun D : Fin (n+m) → Cov d × Bool × Bool =>
        ((fun i : Fin n => D (Fin.castAdd m i)),
         (fun j : Fin m => ((D (Fin.natAdd n j)).1, (D (Fin.natAdd n j)).2.1))))
      (Measure.pi (fun _ : Fin (n+m) => obsLaw P))
      ((Measure.pi (fun _ : Fin n => obsLaw P)).prod (Measure.pi (fun _ : Fin m => xaLaw P))) := by
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  have hsplit := rectangular_iid_block_law (obsLaw P) (n+m) n m
    (Fin.castAdd m) (Fin.natAdd n) (Fin.castAdd_injective n m) (Fin.natAdd_injective m n)
    (fun i j he => by have := congrArg Fin.val he; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega)
  have hproj : MeasurePreserving (fun z : Cov d × Bool × Bool => (z.1,z.2.1))
      (obsLaw P) (xaLaw P) := ⟨by fun_prop, obsLaw_map_treatment P⟩
  exact (MeasurePreserving.prod (MeasurePreserving.id _)
    (measurePreserving_pi _ _ (fun _ : Fin m => hproj))).comp hsplit

/-- Enumerating both prescribed roles preserves their independent treatment/outcome product law.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the specified input i](hyp:i), [the specified input j](hyp:j), [the specified input hi](hyp:hi), [the specified input hj](hyp:hj), [the specified input hit](hyp:hit), [the specified input hjl](hyp:hjl), [the rectangular dataset block law conclusion](goal) holds. -/
lemma rectangular_dataset_block_law {d n m : ℕ} (P : PrimitiveLaw d)
    (i : Fin (treatmentCount n m) → Fin (n+m))
    (j : Fin (outcomeCount n) → Fin n)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hit : ∀ a, i a ∈ (roleSplit n m).2) (hjl : ∀ b, j b ∈ (roleSplit n m).1)
    : MeasurePreserving
      (fun D : Dataset d n m => ((fun a => treatmentRecords D (i a)), (fun b => D.1 (j b))))
      ((Measure.pi (fun _ : Fin n => obsLaw P)).prod (Measure.pi (fun _ : Fin m => xaLaw P)))
      ((Measure.pi (fun _ : Fin (treatmentCount n m) => xaLaw P)).prod
        (Measure.pi (fun _ : Fin (outcomeCount n) => obsLaw P))) := by
  letI := obsLaw_probability P
  letI := xaLaw_probability P
  have hsplit := rectangular_iid_block_law (obsLaw P) (n+m)
    (treatmentCount n m) (outcomeCount n) i (fun b => Fin.castAdd m (j b)) hi
    ((Fin.castAdd_injective n m).comp hj) (fun a b he => by
      have ht := (Finset.mem_filter.mp (hit a)).2
      have hl := (Finset.mem_filter.mp (hjl b)).2
      have := congrArg Fin.val he
      simp only [Fin.val_castAdd] at this
      omega)
  have hproj : MeasurePreserving (fun z : Cov d × Bool × Bool => (z.1,z.2.1))
      (obsLaw P) (xaLaw P) := ⟨by fun_prop, obsLaw_map_treatment P⟩
  have hroles := (MeasurePreserving.prod
    (measurePreserving_pi _ _ (fun _ : Fin (treatmentCount n m) => hproj))
    (MeasurePreserving.id _)).comp hsplit
  have hd := rectangular_iid_dataset_law (n := n) (m := m) P
  have he (D : Fin (n+m) → Cov d × Bool × Bool) (a : Fin (n+m)) :
      treatmentRecords ((fun k => D (Fin.castAdd m k)),
        (fun k => ((D (Fin.natAdd n k)).1, (D (Fin.natAdd n k)).2.1))) a =
        ((D a).1, (D a).2.1) := by
    refine Fin.addCases (fun k => ?_) (fun k => ?_) a <;>
      simp only [treatmentRecords, Fin.addCases_left, Fin.addCases_right]
  refine ⟨by fun_prop, ?_⟩
  rw [← hd.map_eq, Measure.map_map (by fun_prop) hd.measurable]
  convert hroles.map_eq using 1
  congr 1
  funext D
  apply Prod.ext
  · funext a
    exact he D (i a)
  · rfl

/-- An enumeration of the treatment role by its prescribed count.  Given [the specified input n](hyp:n), [the specified input m](hyp:m), [rectangular treatment enumeration](goal) is the corresponding construction. -/
def rectangularTreatmentEnumeration (n m : ℕ) : Fin (treatmentCount n m) ≃ (roleSplit n m).2 :=
  (Fintype.equivFinOfCardEq (by simpa using (population_role_cardinalities n m).2)).symm

/-- An enumeration of the outcome role by its prescribed count.  Given [the specified input n](hyp:n), [the specified input m](hyp:m), [rectangular outcome enumeration](goal) is the corresponding construction. -/
def rectangularOutcomeEnumeration (n m : ℕ) : Fin (outcomeCount n) ≃ (roleSplit n m).1 :=
  (Fintype.equivFinOfCardEq (by simpa using (population_role_cardinalities n m).1)).symm

/-- The selected records in the two roles, including their deterministic enumeration.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input w](hyp:w), [rectangular role data](goal) is the corresponding construction. -/
def rectangularRoleData {d n m : ℕ} (w : Sample d n m) :
    (Fin (treatmentCount n m) → Cov d × Bool) × (Fin (outcomeCount n) → Cov d × Bool × Bool) :=
  ((fun a => treatmentRecords w.1 (rectangularTreatmentEnumeration n m a)),
   (fun b => w.1.1 (rectangularOutcomeEnumeration n m b)))

/-- The original-record role vector has precisely the independent role product law.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input P](hyp:P), [the rectangular role data law conclusion](goal) holds. -/
lemma rectangular_role_data_law {d n m : ℕ} (P : PrimitiveLaw d) :
    MeasurePreserving (rectangularRoleData (d := d) (n := n) (m := m)) (experiment P n m)
      ((Measure.pi (fun _ : Fin (treatmentCount n m) => xaLaw P)).prod
        (Measure.pi (fun _ : Fin (outcomeCount n) => obsLaw P))) := by
  letI := population_randomizer_probability
  have h := rectangular_dataset_block_law P
    (fun a => (rectangularTreatmentEnumeration n m a).val)
    (fun b => (rectangularOutcomeEnumeration n m b).val)
    (Subtype.val_injective.comp (rectangularTreatmentEnumeration n m).injective)
    (Subtype.val_injective.comp (rectangularOutcomeEnumeration n m).injective)
    (fun a => (rectangularTreatmentEnumeration n m a).property)
    (fun b => (rectangularOutcomeEnumeration n m b).property)
  exact h.comp measurePreserving_fst

/-- The rectangular role sum equals the ordinary finite sum over the enumerated role vector.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input w](hyp:w), [the specified input H](hyp:H), [the rectangular role sum enumeration conclusion](goal) holds. -/
lemma rectangular_role_sum_enumeration {d n m : ℕ} (w : Sample d n m)
    (H : (Cov d × Bool) × (Cov d × Bool × Bool) → ℝ) :
    (∑ i ∈ (roleSplit n m).2, ∑ j ∈ (roleSplit n m).1,
      H (treatmentRecords w.1 i, w.1.1 j)) =
      ∑ a : Fin (treatmentCount n m), ∑ b : Fin (outcomeCount n),
        H ((rectangularRoleData w).1 a, (rectangularRoleData w).2 b) := by
  classical
  rw [← Finset.sum_coe_sort (roleSplit n m).2]
  simp_rw [← Finset.sum_coe_sort (roleSplit n m).1]
  rw [← (rectangularTreatmentEnumeration n m).sum_comp]
  simp_rw [← (rectangularOutcomeEnumeration n m).sum_comp]
  rfl

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.BaselinePoolEncoding

/-!
Exact iid laws for splitting the complete-record array and concatenating its
remaining treatment--covariate projections with the auxiliary array.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory

/-- Under the stated inputs and conditions, Splitting an iid array into its first and last blocks gives independent iid pools.  This gives [the stated result](goal). -/
-- @node: baseline_split_iid_law
lemma baseline_split_iid_law {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (h k : Nat) :
    MeasurePreserving
      (fun s : Fin (h + k) → X =>
        (fun i : Fin h => s (Fin.castAdd k i), fun i : Fin k => s (Fin.natAdd h i)))
      (Measure.pi (fun _ : Fin (h + k) => P))
      ((Measure.pi (fun _ : Fin h => P)).prod (Measure.pi (fun _ : Fin k => P))) := by
  have hr := (measurePreserving_piCongrLeft
    (fun _ : Fin (h + k) => P) (finSumFinEquiv : Fin h ⊕ Fin k ≃ Fin (h + k))).symm
  have hs := measurePreserving_sumPiEquivProdPi (fun _ : Fin h ⊕ Fin k => P)
  convert hs.comp hr using 1
  funext s
  apply Prod.ext <;> funext i <;> rfl

/-- [Under the stated hypotheses](hyp:hn), The split law also holds when the total capacity is expressed by an equal index.  This gives [the stated result](goal). -/
-- @node: baseline_split_iid_law_of_eq
lemma baseline_split_iid_law_of_eq {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (h k n : Nat) (hn : n = h + k) :
    MeasurePreserving
      (fun s : Fin n → X =>
        (fun i : Fin h => s ⟨i.val, by omega⟩,
         fun i : Fin k => s ⟨h + i.val, by omega⟩))
      (Measure.pi (fun _ : Fin n => P))
      ((Measure.pi (fun _ : Fin h => P)).prod (Measure.pi (fun _ : Fin k => P))) := by
  subst n
  exact baseline_split_iid_law P h k

/-- Under the stated inputs and conditions, Concatenating independent iid arrays of the same law gives one iid array.  This gives [the stated result](goal). -/
-- @node: baseline_append_iid_law
lemma baseline_append_iid_law {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (h k : Nat) :
    MeasurePreserving (fun s : (Fin h → X) × (Fin k → X) => Fin.append s.1 s.2)
      ((Measure.pi (fun _ : Fin h => P)).prod (Measure.pi (fun _ : Fin k => P)))
      (Measure.pi (fun _ : Fin (h + k) => P)) := by
  have hr := measurePreserving_piCongrLeft
    (fun _ : Fin (h + k) => P) (finSumFinEquiv : Fin h ⊕ Fin k ≃ Fin (h + k))
  have hs := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin h ⊕ Fin k => P)
  convert hr.comp hs using 1
  funext s i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']
    rfl
  · intro j
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']
    rfl

/-- Under the stated inputs and conditions, Dropping the outcome from an iid complete-record block gives the iid marginal block.  This gives [the stated result](goal). -/
-- @node: baseline_project_iid_law
lemma baseline_project_iid_law {d : Nat} (P : DiscreteLaw d) (k : Nat) :
    MeasurePreserving (fun s : Fin k → Obs d => fun i => ((s i).1, (s i).2.1))
      (labeledProductLaw P k) (auxProductLaw P k) := by
  unfold labeledProductLaw auxProductLaw
  apply measurePreserving_pi (fun _ : Fin k => obsLaw P)
    (fun _ => (auxMarginal P).toMeasure)
    (f := fun _ z => (z.1, z.2.1))
  intro i
  refine ⟨by fun_prop, ?_⟩
  exact PMF.toMeasure_map (fun z : Obs d => (z.1, z.2.1)) P.pmf (by fun_prop)

/-- The baseline pools preserve the original order: the first block is complete,
and the second block concatenates the remaining projections and auxiliary records. -/
-- @node: baselineFixedPools
def baselineFixedPools {n m d : Nat} (s : Sample n m d) :
    (Fin (n / 2) → Obs d) × (Fin (n - n / 2 + m) → AuxObs d) :=
  (fun i => s.1 ⟨i.val, by omega⟩,
    Fin.append (fun i : Fin (n - n / 2) =>
      let z := s.1 ⟨n / 2 + i.val, by omega⟩
      (z.1, z.2.1)) s.2)

/-- Extracting the two disjoint baseline pools is measurable. This gives [the stated conclusion](goal). -/
@[fun_prop]
-- @node: baselineFixedPools_measurable
lemma baselineFixedPools_measurable (n m d : Nat) :
    Measurable (baselineFixedPools (n := n) (m := m) (d := d)) := by
  unfold baselineFixedPools
  apply Measurable.prodMk
  · fun_prop
  · apply measurable_pi_lambda
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [Fin.append_left]
      fun_prop
    · intro j
      simp only [Fin.append_right]
      fun_prop

/-- [Under the stated inputs and conditions](hyp:P,n,m,d), Under the original two-channel experiment, the extracted pools are independent
with exactly the complete-record and treatment--covariate iid laws.  This gives [the stated result](goal).-/
-- @node: baseline_fixed_pools_law
lemma baseline_fixed_pools_law {n m d : Nat} (P : DiscreteLaw d) :
    MeasurePreserving (baselineFixedPools (n := n) (m := m) (d := d))
      (annotationLaw P n m)
      ((labeledProductLaw P (n / 2)).prod (auxProductLaw P (n - n / 2 + m))) := by
  have hsplit : MeasurePreserving
      (fun s : Fin n → Obs d =>
        (fun i : Fin (n / 2) => s ⟨i.val, by omega⟩,
         fun i : Fin (n - n / 2) => s ⟨n / 2 + i.val, by omega⟩))
      (labeledProductLaw P n)
      ((labeledProductLaw P (n / 2)).prod (labeledProductLaw P (n - n / 2))) := by
    exact baseline_split_iid_law_of_eq (obsLaw P) (n / 2) (n - n / 2) n (by omega)
  have hproj := baseline_project_iid_law P (n - n / 2)
  have happ := baseline_append_iid_law (auxMarginal P).toMeasure (n - n / 2) m
  have hfirst := hsplit.prod (MeasurePreserving.id (auxProductLaw P m))
  have hassoc := measurePreserving_prodAssoc
    (labeledProductLaw P (n / 2)) (labeledProductLaw P (n - n / 2)) (auxProductLaw P m)
  have hlast := (MeasurePreserving.id (labeledProductLaw P (n / 2))).prod
    (happ.comp (hproj.prod (MeasurePreserving.id (auxProductLaw P m))))
  convert hlast.comp (hassoc.comp hfirst) using 1
  · funext s
    rfl
  · rfl
  · rfl

/-- [Under the stated inputs and conditions](hyp:P,T,hT,theta,n,m,d), Squared risk of a measurable statistic of the extracted baseline pools is
exactly its risk in the independent fixed-pool experiment.  This gives [the stated result](goal).-/
-- @node: baseline_fixed_pools_sqRisk
lemma baseline_fixed_pools_sqRisk {n m d : Nat} (P : DiscreteLaw d)
    (T : ((Fin (n / 2) → Obs d) × (Fin (n - n / 2 + m) → AuxObs d)) → Real)
    (hT : Measurable T) (theta : Real) :
    Causalean.Stat.sqRisk (annotationLaw P n m) (T ∘ baselineFixedPools) theta =
      Causalean.Stat.sqRisk
        ((labeledProductLaw P (n / 2)).prod (auxProductLaw P (n - n / 2 + m)))
        T theta := by
  unfold Causalean.Stat.sqRisk
  rw [← (baseline_fixed_pools_law P).map_eq]
  exact (integral_map (baselineFixedPools_measurable n m d).aemeasurable
    ((hT.sub measurable_const).pow_const 2).aestronglyMeasurable).symm

end CausalSmith.Stat.AnnotationRarearmFrontier

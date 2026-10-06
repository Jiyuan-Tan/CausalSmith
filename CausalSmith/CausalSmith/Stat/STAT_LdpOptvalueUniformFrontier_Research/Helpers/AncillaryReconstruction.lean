module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Bridge.Identification

/-!
# Ancillary reconstruction of symmetric samples

The signed input and assignment bit factor as a product law. Coordinatewise
reconstruction consequently recovers the full iid observed sample.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- [The ancillary assignment has the parameter-independent fair law](goal). -/
-- @node: ancillaryBitLaw
def ancillaryBitLaw : Measure Bool := atomLaw (fun _ => (1/2 : ℝ))

/-- [Each assignment has probability one half](goal). -/
-- @node: ancillaryBitLaw_singleton
lemma ancillaryBitLaw_singleton (a : Bool) :
    ancillaryBitLaw {a} = ENNReal.ofReal (1/2 : ℝ) := by
  simp [ancillaryBitLaw, atomLaw, Measure.dirac_apply']
  cases a <;> simp

/-- [The ancillary bit law is a probability measure](goal). -/
-- @node: ancillaryBitLaw_probability
instance ancillaryBitLaw_probability : IsProbabilityMeasure ancillaryBitLaw := by
  constructor
  simp only [ancillaryBitLaw, atomLaw, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem, Set.mem_univ, smul_eq_mul, mul_one,
    Fintype.sum_bool]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [Splitting an observed record produces a paired input and an independent fair assignment](goal). -/
-- @node: symmetricLaw_signed_assignment_law
lemma symmetricLaw_signed_assignment_law (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (hd : 0 < d) :
    (observedLaw (symmetricLaw theta)).map (fun o => (signedObserve o, o.2.1)) =
      (pairedLaw theta).prod ancillaryBitLaw := by
  have := symmetricLaw_probability theta htheta hd
  have : IsProbabilityMeasure (pairedLaw theta) :=
    pairedFamily_subset_simplex hd (Set.mem_image_of_mem pairedLaw htheta)
  apply Measure.ext_of_singleton
  intro w
  rcases w with ⟨v,a⟩
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton _)]
  have hpre : (fun o : ObsRecord d => (signedObserve o, o.2.1)) ⁻¹' {(v,a)} =
      {recoverObs v a} := by
    ext o
    constructor
    · intro ho
      have heq : (signedObserve o, o.2.1) = (v,a) := ho
      have hv := congrArg Prod.fst heq
      have ha := congrArg Prod.snd heq
      change signedObserve o = v at hv
      change o.2.1 = a at ha
      simpa [hv, ha] using (recoverObs_signedObserve o).symm
    · intro ho
      have heq : o = recoverObs v a := ho
      subst o
      change (signedObserve (recoverObs v a), a) = (v,a)
      rw [signedObserve_recoverObs]
  rw [hpre, symmetricLaw_observed_singleton theta htheta hd,
    signedObserve_recoverObs]
  have hprod : ((pairedLaw theta).prod ancillaryBitLaw) {(v,a)} =
      pairedLaw theta {v} * ancillaryBitLaw {a} := by
    rw [show ({(v,a)} : Set (PairedSymbol d × Bool)) = {v} ×ˢ {a} from
      Set.singleton_prod_singleton.symm, Measure.prod_prod]
  rw [hprod, ancillaryBitLaw_singleton, mul_comm]

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [Reattaching the fair bit recovers exactly the original observed law](goal). -/
-- @node: symmetricLaw_reconstruction_law
lemma symmetricLaw_reconstruction_law (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (hd : 0 < d) :
    ((pairedLaw theta).prod ancillaryBitLaw).map (fun w => recoverObs w.1 w.2) =
      observedLaw (symmetricLaw theta) := by
  rw [← symmetricLaw_signed_assignment_law theta htheta hd,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hf : (fun w : PairedSymbol d × Bool => recoverObs w.1 w.2) ∘
      (fun o : ObsRecord d => (signedObserve o, o.2.1)) = id := by
    funext o
    exact recoverObs_signedObserve o
  rw [hf, Measure.map_id]

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [Splitting every participant preserves iid sampling and separates all ancillary bits](goal). -/
-- @node: symmetricLaw_iid_signed_assignment_law
lemma symmetricLaw_iid_signed_assignment_law (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (hd : 0 < d) :
    (Measure.pi (fun _ : Fin n => observedLaw (symmetricLaw theta))).map
      (fun o i => (signedObserve (o i), (o i).2.1)) =
      Measure.pi (fun _ : Fin n => (pairedLaw theta).prod ancillaryBitLaw) := by
  have := symmetricLaw_probability theta htheta hd
  have : IsProbabilityMeasure (observedLaw (symmetricLaw theta)) :=
    Measure.isProbabilityMeasure_map (show Measurable observe by fun_prop).aemeasurable
  have : IsProbabilityMeasure ((observedLaw (symmetricLaw theta)).map
      (fun o => (signedObserve o, o.2.1))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [Measure.pi_map_pi (fun _ => (show Measurable
    (fun o : ObsRecord d => (signedObserve o, o.2.1)) by fun_prop).aemeasurable)]
  simp only [symmetricLaw_signed_assignment_law theta htheta hd]

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [Reconstructing every participant recovers the full iid observed experiment](goal). -/
-- @node: symmetricLaw_iid_reconstruction_law
lemma symmetricLaw_iid_reconstruction_law (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (hd : 0 < d) :
    (Measure.pi (fun _ : Fin n => (pairedLaw theta).prod ancillaryBitLaw)).map
      (fun w i => recoverObs (w i).1 (w i).2) =
      Measure.pi (fun _ : Fin n => observedLaw (symmetricLaw theta)) := by
  have := symmetricLaw_probability theta htheta hd
  have : IsProbabilityMeasure (pairedLaw theta) :=
    pairedFamily_subset_simplex hd (Set.mem_image_of_mem pairedLaw htheta)
  have : IsProbabilityMeasure (((pairedLaw theta).prod ancillaryBitLaw).map
      (fun w => recoverObs w.1 w.2)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [Measure.pi_map_pi (fun _ => (show Measurable
    (fun w : PairedSymbol d × Bool => recoverObs w.1 w.2) by fun_prop).aemeasurable)]
  simp only [symmetricLaw_reconstruction_law theta htheta hd]

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [All signed inputs are independent of the entire vector of ancillary assignments](goal). -/
-- @node: symmetricLaw_iid_ancillary_product
lemma symmetricLaw_iid_ancillary_product (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (hd : 0 < d) :
    (Measure.pi (fun _ : Fin n => observedLaw (symmetricLaw theta))).map
      (fun o => ((fun i => signedObserve (o i)), (fun i => (o i).2.1))) =
      (Measure.pi (fun _ : Fin n => pairedLaw theta)).prod
        (Measure.pi (fun _ : Fin n => ancillaryBitLaw)) := by
  have : IsProbabilityMeasure (pairedLaw theta) :=
    pairedFamily_subset_simplex hd (Set.mem_image_of_mem pairedLaw htheta)
  have hsplit := symmetricLaw_iid_signed_assignment_law (n := n) theta htheta hd
  have hprod := (measurePreserving_arrowProdEquivProdArrow
    (PairedSymbol d) Bool (Fin n) (fun _ => pairedLaw theta)
      (fun _ => ancillaryBitLaw)).map_eq
  rw [← hsplit, Measure.map_map (by fun_prop) (by fun_prop)] at hprod
  exact hprod

end CausalSmith.Stat.LdpOptvalueUniformFrontier

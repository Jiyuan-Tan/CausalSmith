module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.AncillaryReconstruction

/-!
# Independent ancillary assignments for the entire sample

The signed sample and the assignment vector factor into independent product laws.
Reconstruction therefore works simultaneously for all participants, before any
adaptive transcript is generated.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [Reconstructing the complete observed sample from the independent signed sample and fair assignment vector recovers its iid law](goal). -/
-- @node: symmetricLaw_iid_reconstruction
lemma symmetricLaw_iid_reconstruction (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (hd : 0 < d) :
    ((Measure.pi (fun _ : Fin n => pairedLaw theta)).prod
      (Measure.pi (fun _ : Fin n => ancillaryBitLaw))).map
      (fun w => fun i => recoverObs (w.1 i) (w.2 i)) =
      Measure.pi (fun _ : Fin n => observedLaw (symmetricLaw theta)) := by
  rw [← symmetricLaw_iid_ancillary_product theta htheta hd,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hid : (fun o : Fin n → ObsRecord d =>
      fun i => recoverObs (signedObserve (o i)) (o i).2.1) = id := by
    funext o i
    exact recoverObs_signedObserve (o i)
  change (Measure.pi (fun _ : Fin n => observedLaw (symmetricLaw theta))).map
    (fun o => fun i => recoverObs (signedObserve (o i)) (o i).2.1) = _
  rw [hid, Measure.map_id]

/-- Assume [the stated htheta condition](hyp:htheta), [positive dimension](hyp:hd), and [measurability of f](hyp:hf). [The iid experiment identity also holds after arbitrary measurable processing of the complete original sample](goal). -/
-- @node: symmetricLaw_iid_reconstruction_map
lemma symmetricLaw_iid_reconstruction_map {Ω : Type} [MeasurableSpace Ω]
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (hd : 0 < d)
    (f : (Fin n → ObsRecord d) → Ω) (hf : Measurable f) :
    ((Measure.pi (fun _ : Fin n => pairedLaw theta)).prod
      (Measure.pi (fun _ : Fin n => ancillaryBitLaw))).map
      (fun w => f (fun i => recoverObs (w.1 i) (w.2 i))) =
      (Measure.pi (fun _ : Fin n => observedLaw (symmetricLaw theta))).map f := by
  rw [← symmetricLaw_iid_reconstruction theta htheta hd,
    Measure.map_map hf (by fun_prop)]
  rfl

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), [positive dimension](hyp:hd), and [the stated htheta condition](hyp:htheta). [Before any adaptive messages are generated, the original decision experiment can be represented by independent paired inputs, fair ancillary bits, and public coins](goal). -/
-- @node: symmetricLaw_reconstructed_decisionLaw
lemma symmetricLaw_reconstructed_decisionLaw (S : SamplingScheme n d)
    (hIID : IidPeople S) (hRandom : IndependentRandomness S) (hd : 0 < d)
    (Q : LocalProtocol n (ObsRecord d)) (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) :
    decisionLaw S Q (symmetricLaw theta) =
      (((Measure.pi (fun _ : Fin n => pairedLaw theta)).prod
        (Measure.pi (fun _ : Fin n => ancillaryBitLaw))).prod
        (Q.seedLaw.prod uniform01)).bind (fun w =>
          (fixedTranscriptLaw Q (fun i => recoverObs (w.1.1 i) (w.1.2 i)) w.2.1).map
            (fun z => (z,w.2.1,w.2.2))) := by
  haveI := symmetricLaw_probability theta htheta hd
  haveI : IsProbabilityMeasure uniform01 := ⟨by
    simp [uniform01, Measure.restrict_apply, Real.volume_Icc]⟩
  have hmodel := symmetricLaw_causalModel theta htheta hd
  haveI : IsProbabilityMeasure (pairedLaw theta) :=
    pairedFamily_subset_simplex hd (Set.mem_image_of_mem pairedLaw htheta)
  let f : (((Fin n → PairedSymbol d) × (Fin n → Bool)) × Q.Seed × ℝ) →
      ((Fin n → ObsRecord d) × Q.Seed × ℝ) :=
    fun w => (fun i => recoverObs (w.1.1 i) (w.1.2 i),w.2)
  have hf : Measurable f := by fun_prop
  have hinput : (((Measure.pi (fun _ : Fin n => pairedLaw theta)).prod
      (Measure.pi (fun _ : Fin n => ancillaryBitLaw))).prod
      (Q.seedLaw.prod uniform01)).map f =
      (Measure.pi (fun _ : Fin n => observedLaw (symmetricLaw theta))).prod
        (Q.seedLaw.prod uniform01) := by
    have hmap := (Measure.map_prod_map
      ((Measure.pi (fun _ : Fin n => pairedLaw theta)).prod
        (Measure.pi (fun _ : Fin n => ancillaryBitLaw)))
      (Q.seedLaw.prod uniform01)
      (show Measurable (fun w : (Fin n → PairedSymbol d) × (Fin n → Bool) =>
        fun i => recoverObs (w.1 i) (w.2 i)) by fun_prop)
      (measurable_id : Measurable (id : Q.Seed × ℝ → Q.Seed × ℝ))).symm
    rw [symmetricLaw_iid_reconstruction theta htheta hd, Measure.map_id] at hmap
    exact hmap
  unfold decisionLaw
  rw [hRandom Q.Seed Q.seedLaw (symmetricLaw theta) hmodel,
    hIID Q.Seed Q.seedLaw (symmetricLaw theta) hmodel, ← hinput]
  unfold Measure.bind
  rw [Measure.map_map (measurable_protocol_decisionRows Q) hf]
  rfl

end CausalSmith.Stat.LdpOptvalueUniformFrontier

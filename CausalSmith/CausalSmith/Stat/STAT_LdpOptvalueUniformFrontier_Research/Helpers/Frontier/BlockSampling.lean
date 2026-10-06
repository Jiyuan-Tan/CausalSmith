module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.Sampling

/-!
# Vector blocks extracted from the attaining transcript

Selecting distinct vector-release rows recovers the iid vector experiment used
by the finite moment calibration.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Assume [the stated hn condition](hyp:hn) and [the stated hi condition](hyp:hi). [A vector-release row has exactly the signed-vector marginal](goal). -/
-- @node: frontierKernel_vector_marginal
lemma frontierKernel_vector_marginal (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (i : Fin n) (hi : (frontierResources n d eps).m0 ≤ i.val) (o : ObsRecord d) :
    (frontierKernel n d eps i o).map Prod.snd = vectorKernel d eps o := by
  classical
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply measurable_snd hE]
  change atomLaw (frontierMass n d eps i o) (Prod.snd ⁻¹' E) =
    atomLaw (vectorMass eps o) E
  simp only [frontierMass, hn, not_lt.mpr hi, ↓reduceIte, atomLaw,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurable_snd hE),
    Measure.dirac_apply' _ hE]
  rw [Fintype.sum_prod_type]
  simp [Set.indicator, Set.mem_preimage]

/-- Assume [the stated hn condition](hyp:hn) and [the stated hi condition](hyp:hi). [Averaging inputs preserves the vector marginal of every vector-release row](goal). -/
-- @node: frontier_averaged_vector_marginal
lemma frontier_averaged_vector_marginal (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (i : Fin n) (hi : (frontierResources n d eps).m0 ≤ i.val)
    (P : Measure (FullRecord d)) :
    ((observedLaw P).bind (frontierKernel n d eps i)).map Prod.snd =
      vectorMessageLaw P eps := by
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply measurable_snd hE]
  unfold vectorMessageLaw
  rw [Measure.bind_apply (measurable_snd hE) (Kernel.measurable _).aemeasurable,
    Measure.bind_apply hE (Kernel.measurable _).aemeasurable]
  apply lintegral_congr
  intro o
  have h := congrArg (fun L => L E) (frontierKernel_vector_marginal n d eps hn i hi o)
  rw [Measure.map_apply measurable_snd hE] at h
  exact h

/-- Assume [the stated hn condition](hyp:hn), [the stated hg condition](hyp:hg), and [the stated hvec condition](hyp:hvec). [Selecting distinct vector-release rows yields independent vector messages](goal). -/
-- @node: frontier_vector_selection_law
lemma frontier_vector_selection_law {n d k : ℕ} (eps : ℝ) (hn : n ≠ 2)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (g : Fin k → Fin n) (hg : Function.Injective g)
    (hvec : ∀ i, (frontierResources n d eps).m0 ≤ (g i).val) :
    (Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))).map
      (fun z i => (z (g i)).2) = vectorBlockLaw P eps k := by
  have : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map (show Measurable observe by fun_prop).aemeasurable
  have : ∀ i, IsMarkovKernel (frontierKernel n d eps i) := by
    intro i
    exact ⟨fun o => (frontierStage_markov n d eps i).isProbabilityMeasure
      ((o,(0 : Fin 1)), fun _ => (false,fun _ => false))⟩
  have : ∀ i, IsProbabilityMeasure ((observedLaw P).bind (frontierKernel n d eps i)) :=
    fun i => isProbabilityMeasure_bind (Kernel.measurable _).aemeasurable
      (Filter.Eventually.of_forall (fun _ => inferInstance))
  have hind := (iIndepFun_pi
    (μ := fun i => (observedLaw P).bind (frontierKernel n d eps i))
    (X := fun (_ : Fin n) (z : FrontierMessage d) => z.2)
    (fun _ => measurable_snd.aemeasurable)).precomp hg
  have hlaw := hind.map_fun_eq_pi_map
    (fun i => (measurable_snd.comp (measurable_pi_apply (g i))).aemeasurable)
  refine hlaw.trans ?_
  unfold vectorBlockLaw
  congr 1
  funext i
  have hmap := (measurePreserving_eval
    (fun i => (observedLaw P).bind (frontierKernel n d eps i)) (g i)).map_eq
  rw [← Measure.map_map measurable_snd (measurable_pi_apply (g i)), hmap]
  exact frontier_averaged_vector_marginal n d eps hn (g i) (hvec i) P

/-- Assume [the stated hn condition](hyp:hn), [the stated hstart condition](hyp:hstart), and [the stated hend condition](hyp:hend). [Any in-horizon contiguous vector block has the calibrated iid block law](goal). -/
-- @node: frontierBlock_law
lemma frontierBlock_law (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (offset : ℕ) (hstart : (frontierResources n d eps).m0 ≤ offset)
    (hend : offset + n / 3 ≤ n) :
    (Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))).map
      (frontierBlock n d eps offset) = vectorBlockLaw P eps (n / 3) := by
  let g : Fin (n / 3) → Fin n := fun i => ⟨offset + i.val, by omega⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply Fin.ext
    have := congrArg Fin.val hij
    dsimp [g] at this
    omega
  have hfun : frontierBlock n d eps offset =
      (fun z i => (z (g i)).2) := by
    funext z i
    simp only [frontierBlock, messageAt, show offset + i.val < n by omega, ↓reduceDIte]
    rfl
  rw [hfun]
  exact frontier_vector_selection_law eps hn P g hg (fun i => by dsimp [g]; omega)

/-- Assume [the stated hn condition](hyp:hn), [the stated hstart condition](hyp:hstart), and [the stated hend condition](hyp:hend). [Expectations of extracted vector-block statistics equal their calibration expectations](goal). -/
-- @node: frontierBlock_integral
lemma frontierBlock_integral (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (offset : ℕ) (hstart : (frontierResources n d eps).m0 ≤ offset)
    (hend : offset + n / 3 ≤ n) (f : (Fin (n / 3) → Fin d → Bool) → ℝ) :
    (∫ z, f (frontierBlock n d eps offset z)
      ∂Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))) =
        blockMean P eps f := by
  unfold blockMean
  rw [← frontierBlock_law n d eps hn P offset hstart hend]
  exact (integral_map (by fun_prop) (by fun_prop)).symm

end CausalSmith.Stat.LdpOptvalueUniformFrontier

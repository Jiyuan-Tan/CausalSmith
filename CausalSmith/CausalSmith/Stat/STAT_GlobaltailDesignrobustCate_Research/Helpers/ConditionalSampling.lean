module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CountLaplace
public import Causalean.Stat.Minimax.MarkovKernelTransport
public import Mathlib.Probability.Kernel.CondDistrib

/-! # Identification of the independent conditional-outcome mixture

The recorded-design outcome kernel reconstructs the observed law. Its finite
product therefore reconstructs the actual iid sample, retaining empty subcells.
This supplies the measure identity needed to average roadmap equation (14).
-/
@[expose] public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- The outcome kernel retains the conditioning covariate and treatment in
its output triple. -/
-- @node: conditionalObservationKernel
noncomputable def conditionalObservationKernel {d : ℕ} (P : Law d)
    [IsProbabilityMeasure P.full] :
    Kernel ((Fin d → ℝ) × Bool) (Obs d) :=
  (Kernel.id ×ₖ condDistrib
    (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
    (fun u : Full d => (u.1, u.2.1)) P.full).map
      (fun p => (p.1.1, p.1.2, p.2))

/-- Every reconstructed observation fiber is a probability law. -/
-- @node: conditionalObservationKernel_isMarkov
instance conditionalObservationKernel_isMarkov {d : ℕ} (P : Law d)
    [IsProbabilityMeasure P.full] : IsMarkovKernel (conditionalObservationKernel P) := by
  unfold conditionalObservationKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- On a fixed design the reconstructed observation is exactly the outcome
conditional law with that design recorded. -/
-- @node: conditionalObservationKernel_apply
lemma conditionalObservationKernel_apply {d : ℕ} (P : Law d)
    [IsProbabilityMeasure P.full] (xa : (Fin d → ℝ) × Bool) :
    conditionalObservationKernel P xa =
      (condDistrib (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
        (fun u : Full d => (u.1, u.2.1)) P.full xa).map
          (fun y => (xa.1, xa.2, y)) := by
  rw [conditionalObservationKernel, Kernel.map_apply _ (by fun_prop),
    Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Averaging the reconstructed observation kernel over the actual design
marginal yields the consistent observed law. -/
-- @node: conditionalObservationKernel_comp_design
lemma conditionalObservationKernel_comp_design {d : ℕ} (P : Law d)
    [IsProbabilityMeasure P.full]
    (hiid : IidSampling P) (hcons : Consistency P) :
    conditionalObservationKernel P ∘ₘ
      P.full.map (fun u : Full d => (u.1, u.2.1)) = P.obs := by
  let : IsProbabilityMeasure P.full := hiid.1
  have hY : Measurable (fun u : Full d =>
      if u.2.1 then u.2.2.2 else u.2.2.1) := by
    exact Measurable.ite
      ((measurableSet_singleton true).preimage (by fun_prop))
      (by fun_prop) (by fun_prop)
  rw [conditionalObservationKernel, ← Measure.map_comp _ _ (by fun_prop),
    ← Measure.compProd_eq_comp_prod, compProd_map_condDistrib hY.aemeasurable,
    Measure.map_map (by fun_prop) (by fun_prop), hcons.2]
  apply Measure.map_congr
  filter_upwards [hcons.1] with u hu
  exact hu.symm

/-- The independent finite product of the reconstructed observation kernels
is the actual observed sample law after averaging over all designs. -/
-- @node: sample_eq_conditionalObservation_mixture
lemma sample_eq_conditionalObservation_mixture {d n : ℕ} (P : Law d)
    [IsProbabilityMeasure P.full]
    (hiid : IidSampling P) (hcons : Consistency P) (hn : 0 < n) :
    P.sample n = Causalean.Stat.finProductKernel n (conditionalObservationKernel P) ∘ₘ
      Measure.pi (fun _ : Fin n =>
        P.full.map (fun u : Full d => (u.1, u.2.1))) := by
  let : IsProbabilityMeasure P.full := hiid.1
  let : IsProbabilityMeasure (P.full.map (fun u : Full d => (u.1, u.2.1))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [Causalean.Stat.finProductKernel_comp_pi,
    conditionalObservationKernel_comp_design P hiid hcons,
    sample_eq_pi_obs P hiid hcons hn]

/-- The finite observation kernel agrees with the product of independent
outcome fibers, followed by recording the complete design. -/
-- @node: conditionalObservation_product_apply
lemma conditionalObservation_product_apply {d n : ℕ} (P : Law d)
    [IsProbabilityMeasure P.full] (design : Fin n → (Fin d → ℝ) × Bool) :
    Causalean.Stat.finProductKernel n (conditionalObservationKernel P) design =
      (Measure.pi (fun i : Fin n => condDistrib
        (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
        (fun u : Full d => (u.1, u.2.1)) P.full (design i))).map
          (fun y i => ((design i).1, (design i).2, y i)) := by
  rw [Causalean.Stat.finProductKernel_apply]
  simp_rw [conditionalObservationKernel_apply]
  exact (Measure.pi_map_pi (fun _ => by fun_prop)).symm

/-- A measurable sample event is the average of its probabilities under the
independent conditional outcome fibers, with the complete design recorded. -/
-- @node: sample_event_eq_conditionalFiber_lintegral
lemma sample_event_eq_conditionalFiber_lintegral {d n : ℕ} (P : Law d)
    [IsProbabilityMeasure P.full] (hiid : IidSampling P)
    (hcons : Consistency P) (hn : 0 < n)
    (E : Set (Fin n → Obs d)) (hE : MeasurableSet E) :
    P.sample n E = ∫⁻ design,
      (Measure.pi (fun i : Fin n => condDistrib
        (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
        (fun u : Full d => (u.1, u.2.1)) P.full (design i)))
          {y | (fun i => ((design i).1, (design i).2, y i)) ∈ E}
      ∂Measure.pi (fun _ : Fin n =>
        P.full.map (fun u : Full d => (u.1, u.2.1))) := by
  rw [sample_eq_conditionalObservation_mixture P hiid hcons hn,
    Measure.bind_apply hE (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro design
  rw [conditionalObservation_product_apply, Measure.map_apply (by fun_prop) hE]
  rfl

/-- The complete design marginal of the actual sample is the independent
product of the latent single-observation design marginal. -/
-- @node: sample_map_design_eq_pi
lemma sample_map_design_eq_pi {d n : ℕ} (P : Law d)
    (hiid : IidSampling P) (hcons : Consistency P) (hn : 0 < n) :
    (P.sample n).map (fun sample i => ((sample i).1, (sample i).2.1)) =
      Measure.pi (fun _ : Fin n =>
        P.full.map (fun u : Full d => (u.1, u.2.1))) := by
  let : IsProbabilityMeasure P.full := hiid.1
  let : IsProbabilityMeasure P.obs := obs_isProbabilityMeasure P hiid hcons
  let : IsProbabilityMeasure (P.obs.map (fun o : Obs d => (o.1, o.2.1))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [sample_eq_pi_obs P hiid hcons hn,
    Measure.pi_map_pi (f := fun (_ : Fin n) (o : Obs d) => (o.1, o.2.1))
      (fun _ => by fun_prop)]
  congr 1
  funext i
  rw [hcons.2]
  rw [Measure.map_congr (show P.observedRecord =ᵐ[P.full] observe from hcons.1),
    Measure.map_map (by fun_prop) (by
      unfold observe
      apply Measurable.prodMk (by fun_prop)
      apply Measurable.prodMk (by fun_prop)
      exact Measurable.ite
        ((measurableSet_singleton true).preimage (by fun_prop))
        (by fun_prop) (by fun_prop))]
  rfl

/-- Real probabilities of sample events can be averaged without losing the
zero-count design fibers. -/
-- @node: sample_real_event_eq_conditionalKernel_integral
lemma sample_real_event_eq_conditionalKernel_integral {d n : ℕ} (P : Law d)
    [IsProbabilityMeasure P.full] (hiid : IidSampling P)
    (hcons : Consistency P) (hn : 0 < n)
    (E : Set (Fin n → Obs d)) (hE : MeasurableSet E) :
    (P.sample n).real E = ∫ design,
      (Causalean.Stat.finProductKernel n (conditionalObservationKernel P) design).real E
      ∂Measure.pi (fun _ : Fin n =>
        P.full.map (fun u : Full d => (u.1, u.2.1))) := by
  rw [Measure.real, sample_eq_conditionalObservation_mixture P hiid hcons hn,
    Measure.bind_apply hE (Kernel.aemeasurable _)]
  exact (integral_toReal (Kernel.measurable_coe _ hE).aemeasurable
    (Filter.Eventually.of_forall (fun design => measure_lt_top _ _))).symm

/-- An integrable bound on the independent conditional outcome event
probabilities gives the unconditional sample bound by averaging over designs. -/
-- @node: sample_real_event_le_conditionalFiber_integral
lemma sample_real_event_le_conditionalFiber_integral {d n : ℕ} (P : Law d)
    [IsProbabilityMeasure P.full] (hiid : IidSampling P)
    (hcons : Consistency P) (hn : 0 < n)
    (E : Set (Fin n → Obs d)) (hE : MeasurableSet E)
    (g : (Fin n → (Fin d → ℝ) × Bool) → ℝ)
    (hg : Integrable g (Measure.pi (fun _ : Fin n =>
      P.full.map (fun u : Full d => (u.1, u.2.1)))))
    (hbound : ∀ᵐ design ∂Measure.pi (fun _ : Fin n =>
        P.full.map (fun u : Full d => (u.1, u.2.1))),
      (Measure.pi (fun i : Fin n => condDistrib
        (fun u : Full d => if u.2.1 then u.2.2.2 else u.2.2.1)
        (fun u : Full d => (u.1, u.2.1)) P.full (design i))).real
          {y | (fun i => ((design i).1, (design i).2, y i)) ∈ E} ≤ g design) :
    (P.sample n).real E ≤ ∫ design, g design
      ∂Measure.pi (fun _ : Fin n =>
        P.full.map (fun u : Full d => (u.1, u.2.1))) := by
  let : IsProbabilityMeasure (P.full.map (fun u : Full d => (u.1, u.2.1))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let K := Causalean.Stat.finProductKernel n (conditionalObservationKernel P)
  have hmeas : Measurable (fun design => (K design).real E) := by
    exact (Kernel.measurable_coe K hE).ennreal_toReal
  have hint : Integrable (fun design => (K design).real E)
      (Measure.pi (fun _ : Fin n =>
        P.full.map (fun u : Full d => (u.1, u.2.1)))) := by
    apply Integrable.of_mem_Icc 0 1 hmeas.aemeasurable
    exact Filter.Eventually.of_forall (fun design =>
      ⟨measureReal_nonneg, measureReal_le_one⟩)
  rw [sample_real_event_eq_conditionalKernel_integral P hiid hcons hn E hE]
  apply integral_mono_ae hint hg
  filter_upwards [hbound] with design hd
  change (K design).real E ≤ g design
  dsimp only [K]
  rw [conditionalObservation_product_apply, Measure.real,
    Measure.map_apply (by fun_prop) hE]
  exact hd

/-- Any measurable statistic of the complete design has the same expectation
under the design product marginal and the actual sample law. -/
-- @node: sample_design_integral_eq
lemma sample_design_integral_eq {d n : ℕ} (P : Law d)
    (hiid : IidSampling P) (hcons : Consistency P) (hn : 0 < n)
    (f : (Fin n → (Fin d → ℝ) × Bool) → ℝ) (hf : Measurable f) :
    (∫ design, f design ∂Measure.pi (fun _ : Fin n =>
      P.full.map (fun u : Full d => (u.1, u.2.1)))) =
      ∫ sample, f (fun i => ((sample i).1, (sample i).2.1)) ∂P.sample n := by
  rw [← sample_map_design_eq_pi P hiid hcons hn]
  exact integral_map (by fun_prop) hf.aestronglyMeasurable

/-- The minimum-count Laplace statistic transports exactly from design
fibers to the sample; this also retains every zero-count fiber. -/
-- @node: minimumCellCount_design_integral_eq
lemma minimumCellCount_design_integral_eq {d n : ℕ} (P : Law d)
    (hiid : IidSampling P) (hcons : Consistency P) (hn : 0 < n)
    (arm : Bool) (j m : ℕ) (ε s : ℝ) (Q : Fin d → Fin (2 ^ j)) :
    (∫ design, Real.exp (-s * (minimumCellCount
        (fun i => ((design i).1, (design i).2, (0 : ℝ))) arm j m ε Q : ℝ))
      ∂Measure.pi (fun _ : Fin n =>
        P.full.map (fun u : Full d => (u.1, u.2.1)))) =
      ∫ sample, Real.exp (-s * (minimumCellCount sample arm j m ε Q : ℝ))
        ∂P.sample n := by
  rw [sample_design_integral_eq P hiid hcons hn _ (by fun_prop)]
  rfl

end CausalSmith.Stat.GlobalTailDesignRobustCate

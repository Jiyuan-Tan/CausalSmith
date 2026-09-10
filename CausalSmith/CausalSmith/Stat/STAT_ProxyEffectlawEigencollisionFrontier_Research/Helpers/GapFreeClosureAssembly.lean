import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.GapFreeModulusBridge
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.SummaryMetric
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

/-! Dense extension while preserving the paper's explicit `dS` control function. -/

namespace GapFreeClosureAssembly

-- @node: gapFreeClosureAssembly_atomicLawBorelSpace
noncomputable instance atomicLawBorelSpace (k : ℕ) (radius : ℝ) :
    BorelSpace (AtomicLaw k radius) := by
  constructor
  rw [borel_comap, ← BorelSpace.measurable_eq]
  rfl

-- @node: gapFreeClosureAssembly_atomicLawPolishSpace
noncomputable instance atomicLawPolishSpace (k : ℕ) (radius : ℝ) :
    PolishSpace (AtomicLaw k radius) :=
  (AtomicLaw.coordinateHomeomorph k radius).toEquiv.polishSpace_induced

-- @node: gapFreeClosureAssembly_probabilityLawPolishSpace
noncomputable instance probabilityLawPolishSpace (k : ℕ) (radius : ℝ) :
    PolishSpace (AtomicLaw.ProbabilityLaw k radius) :=
  (AtomicLaw.valid_isCompact k radius).isClosed.polishSpace

-- @node: gapFreeClosureAssembly_lawModuloOpensMeasurableSpace
noncomputable instance lawModuloOpensMeasurableSpace (k : ℕ) (radius : ℝ) :
    OpensMeasurableSpace (AtomicLaw.LawModulo k radius) := by
  constructor
  intro U hU
  change MeasurableSet (AtomicLaw.LawModulo.ofProbabilityLaw ⁻¹' U)
  have hpre : @MeasurableSet (AtomicLaw.ProbabilityLaw k radius)
      (borel (AtomicLaw.ProbabilityLaw k radius))
      (AtomicLaw.LawModulo.ofProbabilityLaw ⁻¹' U) :=
    hU.preimage continuous_coinduced_rng.borel_measurable
  change @MeasurableSet (AtomicLaw.ProbabilityLaw k radius) inferInstance
    (AtomicLaw.LawModulo.ofProbabilityLaw ⁻¹' U)
  rw [show (inferInstance : MeasurableSpace (AtomicLaw.ProbabilityLaw k radius)) =
    borel (AtomicLaw.ProbabilityLaw k radius) from BorelSpace.measurable_eq]
  exact hpre

-- @node: gapFreeClosureAssembly_lawModuloBorelSpace
noncomputable instance lawModuloBorelSpace (k : ℕ) (radius : ℝ) :
    BorelSpace (AtomicLaw.LawModulo k radius) := by
  apply Measurable.borelSpace_codomain
      (f := @AtomicLaw.LawModulo.ofProbabilityLaw k radius)
  · exact Measurable.of_comap_le MeasurableSpace.comap_map_le
  · intro q
    exact ⟨q.out, Quotient.out_eq q⟩

-- @node: gapFreeClosureAssembly_exists_unique_extension_with_control
theorem exists_unique_extension_with_control
    {α : Type*} [PseudoMetricSpace α] {k : ℕ} {radius : ℝ}
    (s : Set α) (f : s → AtomicLaw.LawModulo k radius)
    (control : α → α → ℝ) {Kmetric : NNReal} {C : ℝ}
    (hfmetric : LipschitzWith Kmetric f)
    (hcontrol : Continuous (Function.uncurry control))
    (hfcontrol : ∀ x y : s, dist (f x) (f y) ≤ C * control x.1 y.1) :
    ∃ F : closure s → AtomicLaw.LawModulo k radius,
      Continuous F ∧
      (∀ q q', dist (F q) (F q') ≤ C * control q.1 q'.1) ∧
      (∀ x : s, F ⟨x, subset_closure x.property⟩ = f x) ∧
      ∀ G : closure s → AtomicLaw.LawModulo k radius, Continuous G →
        (∀ x : s, G ⟨x, subset_closure x.property⟩ = f x) → ∀ q, G q = F q := by
  obtain ⟨F, hFlip, hFext, hFunique⟩ :=
    GapFreeModulusBridge.exists_unique_lipschitz_extension s f hfmetric
  refine ⟨F, hFlip.continuous, ?_, hFext, hFunique⟩
  intro q q'
  obtain ⟨x, hxs, hx⟩ := (mem_closure_iff_seq_limit.mp q.property)
  obtain ⟨y, hys, hy⟩ := (mem_closure_iff_seq_limit.mp q'.property)
  let xc : ℕ → closure s := fun n => ⟨x n, subset_closure (hxs n)⟩
  let yc : ℕ → closure s := fun n => ⟨y n, subset_closure (hys n)⟩
  have hxc : Filter.Tendsto xc Filter.atTop (nhds q) := by
    rw [tendsto_subtype_rng]
    exact hx
  have hyc : Filter.Tendsto yc Filter.atTop (nhds q') := by
    rw [tendsto_subtype_rng]
    exact hy
  have hleft : Filter.Tendsto (fun n => dist (F (xc n)) (F (yc n))) Filter.atTop
      (nhds (dist (F q) (F q'))) :=
    (hFlip.continuous.continuousAt.tendsto.comp hxc).dist
      (hFlip.continuous.continuousAt.tendsto.comp hyc)
  have hright : Filter.Tendsto (fun n => C * control (x n) (y n)) Filter.atTop
      (nhds (C * control q.1 q'.1)) := by
    apply tendsto_const_nhds.mul
    exact hcontrol.continuousAt.tendsto.comp (hx.prodMk_nhds hy)
  apply le_of_tendsto_of_tendsto' hleft hright
  intro n
  change dist (F ⟨x n, subset_closure (hxs n)⟩)
      (F ⟨y n, subset_closure (hys n)⟩) ≤ C * control (x n) (y n)
  rw [hFext ⟨x n, hxs n⟩, hFext ⟨y n, hys n⟩]
  exact hfcontrol ⟨x n, hxs n⟩ ⟨y n, hys n⟩

end GapFreeClosureAssembly

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

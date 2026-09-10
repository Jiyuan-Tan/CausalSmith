import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.SummaryClosure
import CausalSmith.Substrate.CollisionSafeSpectralLaw.Composition
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
Paper-local bridges from the radius-indexed quotient-law carrier to the neutral
collision-safe finite-atomic Wasserstein substrate.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

namespace GapFreeModulusBridge

/-- Forget the support-radius index while retaining the labelled atomic law. -/
-- @node: gapFreeModulusBridge_asNeutral
def asNeutral {k : ℕ} {radius : ℝ} (mu : AtomicLaw k radius) :
    CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw (Fin k) :=
  ⟨mu.weight, mu.atom⟩

/-- Local validity supplies the positivity and normalization required by the neutral carrier. -/
-- @node: gapFreeModulusBridge_asNeutral_valid
lemma asNeutral_valid {k : ℕ} {radius : ℝ} {mu : AtomicLaw k radius}
    (hmu : AtomicLaw.Valid mu) :
    CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.Valid (asNeutral mu) :=
  ⟨hmu.1, hmu.2.1⟩

private def planToNeutral {k : ℕ} {radius : ℝ} {mu nu : AtomicLaw k radius}
    (pi : AtomicLaw.TransportPlan mu nu) :
    CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.TransportPlan
      (asNeutral mu) (asNeutral nu) where
  mass := pi.mass
  nonneg := pi.nonneg
  fst_marginal := pi.fst_marginal
  snd_marginal := pi.snd_marginal

private def planFromNeutral {k : ℕ} {radius : ℝ} {mu nu : AtomicLaw k radius}
    (pi : CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.TransportPlan
      (asNeutral mu) (asNeutral nu)) :
    AtomicLaw.TransportPlan mu nu where
  mass := pi.mass
  nonneg := pi.nonneg
  fst_marginal := pi.fst_marginal
  snd_marginal := pi.snd_marginal

private lemma cost_toNeutral {k : ℕ} {radius : ℝ} {mu nu : AtomicLaw k radius}
    (pi : AtomicLaw.TransportPlan mu nu) :
    CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.transportCost
      (planToNeutral pi) = AtomicLaw.transportCost pi := by
  rfl

private lemma cost_fromNeutral {k : ℕ} {radius : ℝ} {mu nu : AtomicLaw k radius}
    (pi : CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.TransportPlan
      (asNeutral mu) (asNeutral nu)) :
    AtomicLaw.transportCost (planFromNeutral pi) =
      CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.transportCost pi := by
  rfl

/-- The paper-local and neutral finite transport formulations compute exactly the same cost. -/
-- @node: gapFreeModulusBridge_wass1_eq_neutralW1
lemma wass1_eq_neutralW1 {k : ℕ} {radius : ℝ} {mu nu : AtomicLaw k radius}
    (hmu : AtomicLaw.Valid mu) (hnu : AtomicLaw.Valid nu) :
    AtomicLaw.wass1 mu nu =
      CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.w1
        (asNeutral mu) (asNeutral nu) := by
  apply le_antisymm
  · obtain ⟨pi, hpi⟩ :=
      CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.exists_optimalTransportPlan
      (asNeutral mu) (asNeutral nu) (asNeutral_valid hmu) (asNeutral_valid hnu)
    calc
      AtomicLaw.wass1 mu nu ≤ AtomicLaw.transportCost (planFromNeutral pi) :=
        AtomicLaw.wass1_le_of_plan _
      _ = CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.transportCost pi :=
        cost_fromNeutral pi
      _ = CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.w1
          (asNeutral mu) (asNeutral nu) := hpi
  · obtain ⟨pi, hpi⟩ := AtomicLaw.wass1_optimal_plan hmu hnu
    calc
      CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.w1
          (asNeutral mu) (asNeutral nu) ≤
          CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.transportCost
            (planToNeutral pi) :=
        CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.w1_le_transportCost _
      _ = AtomicLaw.transportCost pi := cost_toNeutral pi
      _ = AtomicLaw.wass1 mu nu := hpi

/-- Quotient Wasserstein distance can be evaluated by the neutral substrate on any chosen
representatives. -/
-- @node: gapFreeModulusBridge_lawModulo_wass1_eq_neutralW1
lemma lawModulo_wass1_eq_neutralW1 {k : ℕ} {radius : ℝ}
    (mu nu : AtomicLaw.LawModulo k radius) :
    mu.wass1 nu = CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.w1
      (asNeutral mu.representative.1) (asNeutral nu.representative.1) := by
  exact wass1_eq_neutralW1 mu.representative.2 nu.representative.2

/-- A Lipschitz map into the complete quotient-law space extends uniquely from a set to its
closure.  This packages the final completion step of the modulus argument independently of the
model-specific operator construction. -/
-- @node: gapFreeModulusBridge_exists_unique_lipschitz_extension
theorem exists_unique_lipschitz_extension
    {α : Type*} [PseudoMetricSpace α] {k : ℕ} {radius : ℝ}
    (s : Set α) (f : s → AtomicLaw.LawModulo k radius) {K : NNReal}
    (hf : LipschitzWith K f) :
    ∃ F : closure s → AtomicLaw.LawModulo k radius,
      LipschitzWith K F ∧
      (∀ x : s, F ⟨x, subset_closure x.property⟩ = f x) ∧
      ∀ G : closure s → AtomicLaw.LawModulo k radius, Continuous G →
        (∀ x : s, G ⟨x, subset_closure x.property⟩ = f x) → ∀ q, G q = F q := by
  let t : Set (closure s) := {x | (x : α) ∈ s}
  have ht : Dense t := by
    rw [Subtype.dense_iff]
    intro x hx
    change x ∈ closure (Subtype.val '' t)
    have himage : Subtype.val '' t = s := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨⟨y, subset_closure hy⟩, hy, rfl⟩
    simpa [himage] using hx
  let f' : t → AtomicLaw.LawModulo k radius := fun x => f ⟨x.1.1, x.2⟩
  have hf' : LipschitzWith K f' := by
    intro x y
    exact hf ⟨x.1.1, x.2⟩ ⟨y.1.1, y.2⟩
  let F : closure s → AtomicLaw.LawModulo k radius := ht.extend f'
  refine ⟨F, ht.lipschitzWith_extend hf', ?_, ?_⟩
  · intro x
    exact ht.extend_eq hf'.continuous ⟨⟨x, subset_closure x.property⟩, x.property⟩
  · intro G hG hGext q
    have hEq : G = F := by
      apply (ht.extend_unique (f := f') (g := G) _ hG).symm
      intro x
      exact hGext ⟨x.1.1, x.2⟩
    exact congrFun hEq q

end GapFreeModulusBridge

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

import Causalean.Graph.FiniteDensity.OrderedLocalMarkov.Main
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Constructions

/-!
# Positive compact-domain DAG product densities: foundations

This module defines compact positive finite-DAG product-density mechanisms and proves the
conditional-law formula identifying a node's normalized local factor as its law conditional on
its parents.  The edge characterization and stable witnesses are in the companion modules.
-/

open scoped ENNReal BigOperators
open Set Function MeasureTheory ProbabilityTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

open Causalean Causalean.Graph.FiniteDensity

universe uV uX

variable {V : Type uV} [Fintype V] [DecidableEq V]
variable {X : V → Type uX} [∀ i, MeasurableSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
variable {G : DAG V}

/-- A [normalized finite-DAG density factorization](hyp:B), [node](hyp:i), [parent-coordinate
test](hyp:h), [node-value test](hyp:g), and [measurability of those two tests](hyp:hh,hg) ensure
that [integrating their product under the observational law equals integrating the parent test
against the node's local conditional density](goal). -/
theorem Factorization.lintegral_node_given_parents
    (B : Factorization G X μ) (i : V)
    (h : (∀ k : G.parents i, X k) → ℝ≥0∞) (g : X i → ℝ≥0∞)
    (hh : Measurable h) (hg : Measurable g) :
    (∫⁻ x, h (coordinateProjection (X := X) (G.parents i) x) * g (x i)
        ∂B.observationalMeasure) =
      ∫⁻ x, h (coordinateProjection (X := X) (G.parents i) x) *
          (∫⁻ z, g z * B.factor i (Function.update x i z) ∂μ i)
        ∂B.observationalMeasure := by
  /- Use the existing reverse-topological elimination identities to compute the joint marginal
  of `i ∪ parents i`, then apply Tonelli twice and `B.normalized_factor`. -/
  classical
  let τ := canonicalTopologicalRanking G
  let P := predecessors τ i
  let A := insert i P
  let T := Finset.univ \ A
  let q₁ : (∀ k, X k) → ℝ≥0∞ := fun x ↦
    h (coordinateProjection (X := X) (G.parents i) x) * g (x i)
  let r : (∀ k, X k) → ℝ≥0∞ := fun x ↦
    ∫⁻ z, g z * B.factor i (Function.update x i z) ∂μ i
  let q₂ : (∀ k, X k) → ℝ≥0∞ := fun x ↦
    h (coordinateProjection (X := X) (G.parents i) x) * r x
  have hparentsP : G.parents i ⊆ P := parents_subset_predecessors τ i
  have hiParents : i ∉ G.parents i := by
    simpa [Causalean.DAG.mem_parents] using G.irrefl i
  have hAclosed : ParentClosed G A := by
    intro j hj k hk
    rcases Finset.mem_insert.mp hj with rfl | hjP
    · exact Finset.mem_insert_of_mem (hparentsP hk)
    · exact Finset.mem_insert_of_mem (parentClosed_predecessors τ i hjP hk)
  have hiP : i ∉ P := not_mem_predecessors τ i
  have hleaf : IsLeafIn G i A := by
    refine ⟨Finset.mem_insert_self i P, ?_⟩
    intro j hj hji hij
    have hjP : j ∈ P := (Finset.mem_insert.mp hj).resolve_left hji
    have hjlt : τ.rank j < τ.rank i := by
      simpa [P, predecessors] using hjP
    exact (not_lt_of_ge (Nat.le_of_lt hjlt)) (τ.edge_lt hij)
  have hq₁ : Measurable q₁ := by
    unfold q₁
    fun_prop
  have hr : Measurable r := by
    unfold r
    apply Measurable.lintegral_prod_right
    exact (hg.comp measurable_snd).mul
      ((B.measurable_factor i).comp measurable_update')
  have hq₂ : Measurable q₂ := by
    unfold q₂
    fun_prop
  have hq₁_dep : DependsOn A q₁ := by
    intro x y hxy
    unfold q₁
    congr 1
    · congr 1
      funext k
      exact hxy k (Finset.mem_insert_of_mem (hparentsP k.property))
    · exact congrArg g (hxy i (Finset.mem_insert_self i P))
  have hr_dep : DependsOn A r := by
    intro x y hxy
    unfold r
    apply lintegral_congr
    intro z
    congr 1
    apply B.local_factor i
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simp
    · have hki : k ≠ i := fun hki ↦ hiParents (by simpa [hki] using hk)
      rw [Function.update_of_ne hki, Function.update_of_ne hki]
      exact hxy k (Finset.mem_insert_of_mem (hparentsP hk))
  have hq₂_dep : DependsOn A q₂ := by
    intro x y hxy
    unfold q₂
    congr 1
    · congr 1
      funext k
      exact hxy k (Finset.mem_insert_of_mem (hparentsP k.property))
    · exact hr_dep hxy
  have hmarginal_mul (q : (∀ k, X k) → ℝ≥0∞) (hq : Measurable q)
      (hq_dep : DependsOn A q) :
      (∫⋯∫⁻_T, fun x ↦ B.observationalDensity x * q x ∂μ) =
        fun x ↦ B.partialDensity A x * q x := by
    funext x
    simp only [MeasureTheory.lmarginal]
    calc
      (∫⁻ y, B.observationalDensity (Function.updateFinset x T y) *
          q (Function.updateFinset x T y)
          ∂Measure.pi fun j : T ↦ μ j) =
          ∫⁻ y, B.observationalDensity (Function.updateFinset x T y) * q x
            ∂Measure.pi fun j : T ↦ μ j := by
        apply lintegral_congr
        intro y
        rw [hq_dep (fun k hk ↦ by
          simp only [Function.updateFinset]
          rw [dif_neg]
          simpa [T] using hk)]
      _ = (∫⁻ y, B.observationalDensity (Function.updateFinset x T y)
            ∂Measure.pi fun j : T ↦ μ j) * q x := by
        rw [lintegral_mul_const]
        exact B.measurable_observationalDensity.comp measurable_updateFinset
      _ = B.partialDensity A x * q x := by
        rw [show (∫⁻ y, B.observationalDensity (Function.updateFinset x T y)
              ∂Measure.pi fun j : T ↦ μ j) =
            (∫⋯∫⁻_T, B.observationalDensity ∂μ) x by rfl]
        exact congrArg (· * q x)
          (congrFun (B.lmarginal_compl_observationalDensity_eq hAclosed) x)
  have hsingle :
      (∫⋯∫⁻_{i}, fun x ↦ B.partialDensity A x * q₁ x ∂μ) =
        (∫⋯∫⁻_{i}, fun x ↦ B.partialDensity A x * q₂ x ∂μ) := by
    rw [MeasureTheory.lmarginal_singleton, MeasureTheory.lmarginal_singleton]
    funext x
    unfold q₁ q₂ r
    simp only [Function.update_self]
    calc
      (∫⁻ z, B.partialDensity A (Function.update x i z) *
          (h (fun k ↦ Function.update x i z k) * g z) ∂μ i) =
          B.partialDensity (A.erase i) x *
            h (coordinateProjection (X := X) (G.parents i) x) *
              (∫⁻ z, g z * B.factor i (Function.update x i z) ∂μ i) := by
        simp_rw [show ∀ z, B.partialDensity A (Function.update x i z) =
            B.factor i (Function.update x i z) * B.partialDensity (A.erase i) x by
          intro z
          calc
            B.partialDensity A (Function.update x i z) =
                B.factor i (Function.update x i z) *
                  B.partialDensity (A.erase i) (Function.update x i z) := by
              unfold Factorization.partialDensity
              exact (Finset.mul_prod_erase A
                (fun j ↦ B.factor j (Function.update x i z)) hleaf.1).symm
            _ = _ := by rw [B.partialDensity_erase_update_leaf hleaf]]
        simp_rw [show ∀ (z : X i),
            h (fun k : G.parents i ↦ Function.update x i z k) =
              h (coordinateProjection (X := X) (G.parents i) x) by
          intro z
          congr 1
          funext k
          exact Function.update_of_ne
            (fun hki ↦ hiParents (by simpa [hki] using k.property)) _ _]
        rw [← lintegral_const_mul]
        · congr 1
          funext z
          simp only [mul_assoc, mul_left_comm, mul_comm]
        · exact hg.mul ((B.measurable_factor i).comp (measurable_update x))
      _ = ∫⁻ z, B.partialDensity A (Function.update x i z) *
          (h (fun k ↦ Function.update x i z k) *
            ∫⁻ w, g w * B.factor i (Function.update (Function.update x i z) i w) ∂μ i)
          ∂μ i := by
        simp_rw [Function.update_idem]
        simp_rw [show ∀ (z : X i),
            h (fun k : G.parents i ↦ Function.update x i z k) =
              h (coordinateProjection (X := X) (G.parents i) x) by
          intro z
          congr 1
          funext k
          exact Function.update_of_ne
            (fun hki ↦ hiParents (by simpa [hki] using k.property)) _ _]
        rw [lintegral_mul_const]
        · rw [B.lintegral_partialDensity_leaf hleaf x]
          simp only [mul_assoc, mul_left_comm, mul_comm]
        · exact (B.measurable_partialDensity A).comp (measurable_update x)
  have hweighted :
      ∫⁻ x, B.observationalDensity x * q₁ x ∂Measure.pi μ =
        ∫⁻ x, B.observationalDensity x * q₂ x ∂Measure.pi μ := by
    apply MeasureTheory.lintegral_eq_of_lmarginal_eq (T ∪ {i})
      (B.measurable_observationalDensity.mul hq₁)
      (B.measurable_observationalDensity.mul hq₂)
    rw [MeasureTheory.lmarginal_union' μ _
        (B.measurable_observationalDensity.mul hq₁)
        (Finset.disjoint_singleton_right.mpr (by simp [T, A])),
      MeasureTheory.lmarginal_union' μ _
        (B.measurable_observationalDensity.mul hq₂)
        (Finset.disjoint_singleton_right.mpr (by simp [T, A]))]
    change (∫⋯∫⁻_{i}, ∫⋯∫⁻_T,
        (fun x ↦ B.observationalDensity x * q₁ x) ∂μ ∂μ) =
      (∫⋯∫⁻_{i}, ∫⋯∫⁻_T,
        (fun x ↦ B.observationalDensity x * q₂ x) ∂μ ∂μ)
    rw [hmarginal_mul q₁ hq₁ hq₁_dep, hmarginal_mul q₂ hq₂ hq₂_dep]
    exact hsingle
  change (∫⁻ x, q₁ x ∂B.observationalMeasure) =
    ∫⁻ x, q₂ x ∂B.observationalMeasure
  rw [Factorization.observationalMeasure,
    lintegral_withDensity_eq_lintegral_mul _ B.measurable_observationalDensity hq₁,
    lintegral_withDensity_eq_lintegral_mul _ B.measurable_observationalDensity hq₂]
  exact hweighted

variable [∀ i, TopologicalSpace (X i)] [∀ i, BorelSpace (X i)]
variable [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
variable [∀ i, StandardBorelSpace (X i)] [∀ i, (μ i).IsOpenPosMeasure]

/-- A compact positive DAG density is a normalized parent-local factorization whose local
densities are finite and continuous and all share one explicit strictly positive lower bound. -/
structure CompactPositiveFactorization (G : DAG V) (X : V → Type uX)
    [∀ i, MeasurableSpace (X i)] [∀ i, TopologicalSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] where
  /-- The underlying normalized measurable parent-local DAG factorization. -/
  toFactorization : Factorization G X μ
  /-- The common pointwise lower bound for every local density. -/
  lower : ℝ
  /-- The common lower bound is strictly positive. -/
  lower_pos : 0 < lower
  /-- Every extended-nonnegative local density is finite at every point. -/
  factor_ne_top : ∀ i x, toFactorization.factor i x ≠ ∞
  /-- The real value of each local density is continuous on the compact product domain. -/
  factor_continuous : ∀ i,
    Continuous (fun x : ∀ k, X k ↦ (toFactorization.factor i x).toReal)
  /-- Every local density is bounded below by the displayed common positive margin. -/
  lower_le_factor : ∀ i x, lower ≤ (toFactorization.factor i x).toReal

namespace CompactPositiveFactorization

variable (M : CompactPositiveFactorization G X μ)

/-- The observational law of a compact positive factorization is the product reference measure
weighted by the product of its local densities. -/
abbrev observationalMeasure : Measure (∀ i, X i) := M.toFactorization.observationalMeasure

/-- Coordinate `i` is conditionally independent of coordinate `j` given `C` under the
observational product-density law. -/
def CondIndepCoordinates (i j : V) (C : Finset V) : Prop :=
  CondIndepFun
    (MeasurableSpace.comap (coordinateProjection (X := X) C) inferInstance)
    (coordinateConditioning_comap_le (X := X) C)
    (fun x : ∀ k, X k ↦ x i) (fun x : ∀ k, X k ↦ x j)
    M.observationalMeasure

/-- A child's local conditional density is independent of coordinate `j` when updating only that
coordinate leaves the factor unchanged at every point of the compact product domain. -/
def FactorIndependentOf (i j : V) : Prop :=
  ∀ (x : ∀ k, X k) (xj : X j),
    M.toFactorization.factor i (Function.update x j xj) = M.toFactorization.factor i x

/-- A child's local factor is almost-everywhere independent of coordinate `j` when the update
identity holds for product-reference-almost every assignment and parent value. -/
def AEFactorIndependentOf (i j : V) : Prop :=
  ∀ᵐ x ∂Measure.pi μ, ∀ᵐ xj ∂μ j,
    M.toFactorization.factor i (Function.update x j xj) = M.toFactorization.factor i x

/-- A [compact positive factorization](hyp:M) and [node](hyp:i) have [a regular conditional law
of that node given its parents equal to the reference measure weighted by the node's normalized
local factor](goal). -/
theorem condDistrib_child_given_parents (i : V) :
    let P := G.parents i
    let x₀ : ∀ k, X k := Classical.choice inferInstance
    let d : (∀ k : P, X k) → X i → ℝ≥0∞ := fun p z ↦
      M.toFactorization.factor i
        (Function.update (coordinateExtension P x₀ p) i z)
    condDistrib (fun x : ∀ k, X k ↦ x i)
        (coordinateProjection (X := X) P) M.observationalMeasure
      =ᵐ[Measure.map (coordinateProjection (X := X) P) M.observationalMeasure]
        Kernel.withDensity (Kernel.const (∀ k : P, X k) (μ i)) d := by
  classical
  dsimp only
  let P := G.parents i
  let x₀ : ∀ k, X k := Classical.choice inferInstance
  let d : (∀ k : P, X k) → X i → ℝ≥0∞ := fun p z ↦
    M.toFactorization.factor i
      (Function.update (coordinateExtension P x₀ p) i z)
  have hd : Measurable (Function.uncurry d) := by
    unfold d
    exact (M.toFactorization.measurable_factor i).comp
      (measurable_update'.comp
        (((measurable_coordinateExtension P x₀).comp measurable_fst).prodMk measurable_snd))
  let κ : Kernel (∀ k : P, X k) (X i) :=
    Kernel.withDensity (Kernel.const (∀ k : P, X k) (μ i)) d
  have hκ_apply (p : ∀ k : P, X k) :
      κ p = (μ i).withDensity (d p) := by
    dsimp [κ]
    rw [Kernel.withDensity_apply _ hd, Kernel.const_apply]
  have hd_eq (x : ∀ k, X k) (z : X i) :
      d (coordinateProjection (X := X) P x) z =
        M.toFactorization.factor i (Function.update x i z) := by
    unfold d
    apply M.toFactorization.local_factor i
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simp
    · have hki : k ≠ i := by
        intro hki
        subst k
        exact G.irrefl i (G.mem_parents.mp hk)
      have hkP : k ∈ P := by simpa [P] using hk
      simp [coordinateExtension, coordinateProjection, hkP, hki]
  letI : IsFiniteKernel κ := ⟨1, ENNReal.one_lt_top, fun p ↦ by
    rw [hκ_apply, withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    change ∫⁻ z, M.toFactorization.factor i
      (Function.update (coordinateExtension P x₀ p) i z) ∂μ i ≤ 1
    rw [M.toFactorization.normalized_factor]⟩
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (measurable_coordinateProjection P) (measurable_pi_apply i)
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (by fun_prop) (hs.prod ht), Measure.compProd_apply_prod hs ht]
  rw [← lintegral_indicator_one ((hs.prod ht).preimage
    ((measurable_coordinateProjection P).prodMk (measurable_pi_apply i)))]
  rw [← lintegral_indicator hs]
  rw [lintegral_map
    ((Kernel.measurable_coe κ ht).indicator hs) (measurable_coordinateProjection P)]
  simp_rw [hκ_apply, withDensity_apply _ ht]
  calc
    (∫⁻ a, ((fun x : ∀ k, X k ↦
        (coordinateProjection (X := X) P x, x i)) ⁻¹' (s ×ˢ t)).indicator 1 a
        ∂M.observationalMeasure) =
        ∫⁻ x, s.indicator 1 (coordinateProjection (X := X) P x) *
          t.indicator 1 (x i) ∂M.observationalMeasure := by
      apply lintegral_congr
      intro x
      by_cases hp : coordinateProjection (X := X) P x ∈ s <;>
        by_cases hi : x i ∈ t <;> simp [Set.indicator, hp, hi]
    _ = ∫⁻ x, s.indicator 1 (coordinateProjection (X := X) P x) *
          (∫⁻ z, t.indicator 1 z *
            M.toFactorization.factor i (Function.update x i z) ∂μ i)
          ∂M.observationalMeasure :=
      _root_.Causalean.Graph.FiniteDensity.Factorization.lintegral_node_given_parents
        M.toFactorization i (s.indicator 1) (t.indicator 1)
          (measurable_const.indicator hs) (measurable_const.indicator ht)
    _ = ∫⁻ a, s.indicator (fun p ↦ ∫⁻ z in t, d p z ∂μ i)
          (coordinateProjection (X := X) P a) ∂M.observationalMeasure := by
      apply lintegral_congr
      intro x
      by_cases hp : coordinateProjection (X := X) P x ∈ s
      · simp only [Set.indicator_of_mem hp, Pi.one_apply, one_mul]
        rw [← lintegral_indicator ht]
        apply lintegral_congr
        intro z
        by_cases hz : z ∈ t <;> simp [Set.indicator, hz, hd_eq]
      · simp [Set.indicator, hp]

end CompactPositiveFactorization

end Causalean.Graph.FiniteDensity

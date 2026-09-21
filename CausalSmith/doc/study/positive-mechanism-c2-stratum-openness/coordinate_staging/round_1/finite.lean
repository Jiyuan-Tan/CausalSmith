import Causalean.Graph.DAG
import Causalean.Graph.FiniteDensity.Coordinate
import Causalean.Graph.FiniteDensity.Positive.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Pi

/-!
# Positive finite-state DAG mechanisms

This module gives a pointwise finite-state interface for strictly positive Bayesian-network
mechanisms.  It defines cylinder marginals and conditional masses directly from the product
density, and characterizes a redundant directed edge by independence of the child's local factor.
Stable witnesses are in `Positive.FiniteWitness`.
-/

open scoped ENNReal BigOperators

noncomputable section

namespace Causalean.Graph.FiniteDensity

open Causalean Causalean.Graph.FiniteDensity MeasureTheory

universe uV uX

variable {V : Type uV} [Fintype V] [DecidableEq V]
variable {X : V → Type uX} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)]

/-- A positive finite-state DAG mechanism consists of normalized, strictly positive local
factors, each depending only on its own coordinate and its graph parents. -/
structure PositiveFiniteDAGMechanism (G : DAG V) (X : V → Type uX)
    [∀ i, Fintype (X i)] where
  /-- The local conditional mass factor at each vertex. -/
  factor : ∀ i, (∀ k, X k) → ℝ
  /-- Every local factor is strictly positive. -/
  factor_pos : ∀ i x, 0 < factor i x
  /-- Each local factor sums to one in its own coordinate for every fixed context. -/
  factor_normalized : ∀ i x, ∑ z : X i, factor i (Function.update x i z) = 1
  /-- A local factor depends only on its vertex and its parents. -/
  factor_local : ∀ i, DependsOn (X := X) (insert i (G.parents i)) (factor i)

namespace PositiveFiniteDAGMechanism

variable {G : DAG V} (M : PositiveFiniteDAGMechanism G X)

/-- The joint mass of an assignment is the product of all local factors. -/
def jointMass (x : ∀ i, X i) : ℝ := ∏ i, M.factor i x

/-- The mass of the cylinder fixing the coordinates in `S` to their values in `x` is obtained
by summing the joint product mass over all compatible full assignments. -/
def marginalMass (S : Finset V) (x : ∀ i, X i) : ℝ :=
  ∑ y : ∀ i, X i,
    if coordinateProjection (X := X) S y = coordinateProjection (X := X) S x
    then M.jointMass y else 0

/-- The pointwise conditional mass of coordinate `i`, given coordinates `C`, is the ratio of the
corresponding cylinder masses. -/
def conditionalMass (i : V) (C : Finset V) (x : ∀ i, X i) (z : X i) : ℝ :=
  M.marginalMass (insert i C) (Function.update x i z) / M.marginalMass C x

/-- The product density of a normalized positive finite DAG mechanism has total mass one. -/
theorem sum_jointMass : ∑ x : ∀ i, X i, M.jointMass x = 1 := by
  letI : ∀ i, MeasurableSpace (X i) := fun _ => ⊤
  let μ : ∀ i, Measure (X i) := fun _ => Measure.count
  haveI : ∀ i, MeasureTheory.SigmaFinite (μ i) := fun _ => inferInstance
  let B : Factorization G X μ := {
    factor := fun i x => ENNReal.ofReal (M.factor i x)
    measurable_factor := by
      intro i
      exact measurable_of_countable _
    local_factor := by
      intro i x y hxy
      exact congrArg ENNReal.ofReal (M.factor_local i hxy)
    normalized_factor := by
      intro i x
      rw [MeasureTheory.lintegral_count, tsum_fintype,
        ← ENNReal.ofReal_sum_of_nonneg]
      · rw [M.factor_normalized]
        simp
      · intro z _
        exact (M.factor_pos i _).le }
  have hpi : Measure.pi μ = (Measure.count : Measure (∀ i, X i)) := by
    apply Measure.ext_of_singleton
    intro x
    rw [Measure.pi_singleton, Measure.count_singleton]
    dsimp [μ]
    simp
  have hobs (x : ∀ i, X i) :
      B.observationalDensity x = ENNReal.ofReal (M.jointMass x) := by
    change (∏ i ∈ Finset.univ, ENNReal.ofReal (M.factor i x)) =
      ENNReal.ofReal (∏ i ∈ Finset.univ, M.factor i x)
    rw [ENNReal.ofReal_prod_of_nonneg]
    intro i _
    exact (M.factor_pos i x).le
  let x₀ : ∀ i, X i := fun i => Classical.choice (inferInstance : Nonempty (X i))
  have hmarg := B.lmarginal_compl_observationalDensity_eq (A := ∅) (by
    intro i hi
    simp at hi)
  have hint :
      ∫⁻ x, B.observationalDensity x ∂Measure.pi μ = 1 := by
    rw [MeasureTheory.lintegral_eq_lmarginal_univ x₀]
    simpa [Factorization.partialDensity] using congrFun hmarg x₀
  rw [hpi, MeasureTheory.lintegral_count, tsum_fintype] at hint
  simp_rw [hobs] at hint
  rw [← ENNReal.ofReal_sum_of_nonneg] at hint
  · exact ENNReal.ofReal_eq_one.mp hint
  · intro x _
    exact (Finset.prod_pos fun i _ => M.factor_pos i x).le

/-- Every cylinder marginal of a positive finite DAG mechanism is strictly positive. -/
theorem marginalMass_pos (S : Finset V) (x : ∀ i, X i) :
    0 < M.marginalMass S x := by
  unfold marginalMass
  apply Finset.sum_pos'
  · intro y _
    split_ifs
    · exact (Finset.prod_pos fun i _ => M.factor_pos i y).le
    · exact le_rfl
  · refine ⟨x, Finset.mem_univ x, ?_⟩
    simp only [ite_true]
    exact Finset.prod_pos fun i _ => M.factor_pos i x

private theorem projection_insert_update_iff (i : V) (x y : ∀ i, X i) (z : X i) :
    coordinateProjection (X := X) (insert i (G.parents i)) y =
        coordinateProjection (X := X) (insert i (G.parents i))
          (Function.update x i z) ↔
      coordinateProjection (X := X) (G.parents i) y =
          coordinateProjection (X := X) (G.parents i) x ∧ y i = z := by
  have hi : i ∉ G.parents i := by
    simpa [DAG.mem_parents] using G.irrefl i
  constructor
  · intro h
    constructor
    · funext k
      have hk := congrFun h
        (⟨k, Finset.mem_insert_of_mem k.property⟩ : ↥(insert i (G.parents i)))
      have hne : (k : V) ≠ i := by
        intro hki
        apply hi
        simpa [hki] using k.property
      simpa [coordinateProjection, Function.update_of_ne hne] using hk
    · have hi' := congrFun h
        (⟨i, Finset.mem_insert_self i _⟩ : ↥(insert i (G.parents i)))
      simpa [coordinateProjection] using hi'
  · rintro ⟨hp, hiz⟩
    funext k
    by_cases hki : (k : V) = i
    · rcases k with ⟨k, hk⟩
      dsimp at hki ⊢
      subst k
      change y i = Function.update x i z i
      simpa using hiz
    · have hkpar : (k : V) ∈ G.parents i :=
        (Finset.mem_insert.mp k.property).resolve_left hki
      have hk := congrFun hp (⟨k, hkpar⟩ : G.parents i)
      simpa [coordinateProjection, Function.update_of_ne hki] using hk

private theorem factor_update_eq_of_projection_eq (i : V) (x y : ∀ i, X i) (z : X i)
    (hxy : coordinateProjection (X := X) (G.parents i) y =
      coordinateProjection (X := X) (G.parents i) x) :
    M.factor i (Function.update y i z) = M.factor i (Function.update x i z) := by
  apply M.factor_local i
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl | hk
  · simp
  · have hki : k ≠ i := by
      intro h
      subst k
      exact G.irrefl i (G.mem_parents.mp hk)
    have h := congrFun hxy (⟨k, hk⟩ : G.parents i)
    simpa [coordinateProjection, Function.update_of_ne hki] using h

/-- Conditioning a node on all of its parents recovers exactly its normalized local factor. -/
theorem conditionalMass_given_parents (i : V) (x : ∀ i, X i) (z : X i) :
    M.conditionalMass i (G.parents i) x z = M.factor i (Function.update x i z) := by
  letI : ∀ i, MeasurableSpace (X i) := fun _ => ⊤
  let μ : ∀ i, Measure (X i) := fun _ => Measure.count
  haveI : ∀ i, SigmaFinite (μ i) := fun _ => inferInstance
  let B : Factorization G X μ := {
    factor := fun i x => ENNReal.ofReal (M.factor i x)
    measurable_factor := by
      intro i
      exact measurable_of_countable _
    local_factor := by
      intro i x y hxy
      exact congrArg ENNReal.ofReal (M.factor_local i hxy)
    normalized_factor := by
      intro i x
      rw [lintegral_count, tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg]
      · rw [M.factor_normalized]
        simp
      · intro w _
        exact (M.factor_pos i _).le }
  have hpi : Measure.pi μ = (Measure.count : Measure (∀ i, X i)) := by
    apply Measure.ext_of_singleton
    intro y
    rw [Measure.pi_singleton, Measure.count_singleton]
    dsimp [μ]
    simp
  have hobs (y : ∀ i, X i) :
      B.observationalDensity y = ENNReal.ofReal (M.jointMass y) := by
    change (∏ i ∈ Finset.univ, ENNReal.ofReal (M.factor i y)) =
      ENNReal.ofReal (∏ i ∈ Finset.univ, M.factor i y)
    rw [ENNReal.ofReal_prod_of_nonneg]
    intro j _
    exact (M.factor_pos j y).le
  have hcyl (S : Finset V) (a : ∀ i, X i) :
      ENNReal.ofReal (M.marginalMass S a) =
        ∫⁻ y, (if coordinateProjection (X := X) S y =
          coordinateProjection (X := X) S a then 1 else 0)
          ∂B.observationalMeasure := by
    rw [Factorization.observationalMeasure,
      lintegral_withDensity_eq_lintegral_mul _ B.measurable_observationalDensity
        (measurable_of_countable _)]
    rw [hpi, lintegral_count, tsum_fintype]
    unfold marginalMass
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro y _
      change ENNReal.ofReal
          (if coordinateProjection (X := X) S y = coordinateProjection (X := X) S a
            then M.jointMass y else 0) =
        B.observationalDensity y *
          (if coordinateProjection (X := X) S y = coordinateProjection (X := X) S a
            then 1 else 0)
      rw [hobs]
      by_cases hy : coordinateProjection (X := X) S y = coordinateProjection (X := X) S a
      · simp [hy]
      · simp [hy]
    · intro y _
      by_cases hy : coordinateProjection (X := X) S y = coordinateProjection (X := X) S a
      · simp [hy]
        exact (Finset.prod_pos fun j _ => M.factor_pos j y).le
      · simp [hy]
  let h : (∀ k : G.parents i, X k) → ℝ≥0∞ := fun p =>
    if p = coordinateProjection (X := X) (G.parents i) x then 1 else 0
  let g : X i → ℝ≥0∞ := fun w => if w = z then 1 else 0
  have hnode :=
    _root_.Causalean.Graph.FiniteDensity.Factorization.lintegral_node_given_parents
      B i h g (measurable_of_countable _) (measurable_of_countable _)
  have hinner (y : ∀ i, X i) :
      (∫⁻ w, g w * B.factor i (Function.update y i w) ∂μ i) =
        B.factor i (Function.update y i z) := by
    rw [lintegral_count, tsum_fintype]
    simp [g]
  have hmeasure :
      ENNReal.ofReal
          (M.marginalMass (insert i (G.parents i)) (Function.update x i z)) =
        ENNReal.ofReal (M.factor i (Function.update x i z)) *
          ENNReal.ofReal (M.marginalMass (G.parents i) x) := by
    rw [hcyl, hcyl]
    calc
      (∫⁻ y, (if coordinateProjection (X := X) (insert i (G.parents i)) y =
          coordinateProjection (X := X) (insert i (G.parents i))
            (Function.update x i z) then 1 else 0) ∂B.observationalMeasure) =
          ∫⁻ y, h (coordinateProjection (X := X) (G.parents i) y) * g (y i)
            ∂B.observationalMeasure := by
              apply lintegral_congr
              intro y
              by_cases hyi : y i = z <;>
                by_cases hyp : coordinateProjection (X := X) (G.parents i) y =
                  coordinateProjection (X := X) (G.parents i) x <;>
                simp [h, g, projection_insert_update_iff, hyi, hyp]
      _ = ∫⁻ y, h (coordinateProjection (X := X) (G.parents i) y) *
          (∫⁻ w, g w * B.factor i (Function.update y i w) ∂μ i)
          ∂B.observationalMeasure := hnode
      _ = ∫⁻ y, ENNReal.ofReal (M.factor i (Function.update x i z)) *
          h (coordinateProjection (X := X) (G.parents i) y)
          ∂B.observationalMeasure := by
            apply lintegral_congr
            intro y
            rw [hinner]
            by_cases hy : coordinateProjection (X := X) (G.parents i) y =
              coordinateProjection (X := X) (G.parents i) x
            · change h _ * ENNReal.ofReal (M.factor i (Function.update y i z)) = _
              rw [factor_update_eq_of_projection_eq M i x y z hy]
              simp [h, hy]
            · simp [h, hy]
      _ = ENNReal.ofReal (M.factor i (Function.update x i z)) *
          ∫⁻ y, h (coordinateProjection (X := X) (G.parents i) y)
            ∂B.observationalMeasure := by
              rw [lintegral_const_mul]
              exact measurable_of_countable _
      _ = ENNReal.ofReal (M.factor i (Function.update x i z)) *
          ∫⁻ y, (if coordinateProjection (X := X) (G.parents i) y =
            coordinateProjection (X := X) (G.parents i) x then 1 else 0)
            ∂B.observationalMeasure := by rfl
  have hreal :
      M.marginalMass (insert i (G.parents i)) (Function.update x i z) =
        M.factor i (Function.update x i z) * M.marginalMass (G.parents i) x := by
    rw [← ENNReal.ofReal_eq_ofReal_iff]
    · rw [ENNReal.ofReal_mul (M.factor_pos i _).le]
      exact hmeasure
    · exact (M.marginalMass_pos _ _).le
    · exact mul_nonneg (M.factor_pos i _).le (M.marginalMass_pos _ _).le
  unfold conditionalMass
  rw [hreal]
  exact mul_div_cancel_right₀ _ (ne_of_gt (M.marginalMass_pos (G.parents i) x))

/-- Two coordinates are conditionally independent given `C` when every four relevant cylinder
masses satisfy the usual cross-multiplied finite conditional-probability identity. -/
def CondIndepCoordinates (i j : V) (C : Finset V) : Prop :=
  ∀ (x : ∀ k, X k) (xi : X i) (xj : X j),
    M.marginalMass (insert i (insert j C))
        (Function.update (Function.update x i xi) j xj) * M.marginalMass C x =
      M.marginalMass (insert i C) (Function.update x i xi) *
        M.marginalMass (insert j C) (Function.update x j xj)

/-- A local factor is independent of coordinate `j` when changing only that coordinate never
changes the factor. -/
def FactorIndependentOf (i j : V) : Prop :=
  ∀ (x : ∀ k, X k) (xj : X j), M.factor i (Function.update x j xj) = M.factor i x

/-- The four-point local contrast compares the two-by-two cross products of a child's factor as
its own value and one candidate parent value vary, with all other coordinates held fixed. -/
def localContrast (i j : V) (x : ∀ k, X k)
    (xi xi' : X i) (xj xj' : X j) : ℝ :=
  M.factor i (Function.update (Function.update x i xi) j xj) *
      M.factor i (Function.update (Function.update x i xi') j xj') -
    M.factor i (Function.update (Function.update x i xi) j xj') *
      M.factor i (Function.update (Function.update x i xi') j xj)

private theorem projection_insert_update_iff_of_not_mem (S : Finset V) (j : V)
    (hj : j ∉ S) (x y : ∀ i, X i) (z : X j) :
    coordinateProjection (X := X) (insert j S) y =
        coordinateProjection (X := X) (insert j S) (Function.update x j z) ↔
      coordinateProjection (X := X) S y = coordinateProjection (X := X) S x ∧
        y j = z := by
  constructor
  · intro h
    constructor
    · funext k
      have hk := congrFun h
        (⟨k, Finset.mem_insert_of_mem k.property⟩ : ↥(insert j S))
      have hne : (k : V) ≠ j := by
        intro hkj
        apply hj
        simpa [hkj] using k.property
      simpa [coordinateProjection, Function.update_of_ne hne] using hk
    · have hj' := congrFun h
        (⟨j, Finset.mem_insert_self j S⟩ : ↥(insert j S))
      simpa [coordinateProjection] using hj'
  · rintro ⟨hS, hjz⟩
    funext k
    by_cases hkj : (k : V) = j
    · rcases k with ⟨k, hk⟩
      dsimp at hkj ⊢
      subst k
      simpa [coordinateProjection] using hjz
    · have hkS : (k : V) ∈ S :=
        (Finset.mem_insert.mp k.property).resolve_left hkj
      have hk := congrFun hS (⟨k, hkS⟩ : S)
      simpa [coordinateProjection, Function.update_of_ne hkj] using hk

private theorem sum_marginalMass_insert (S : Finset V) (j : V) (hj : j ∉ S)
    (x : ∀ i, X i) :
    ∑ z : X j, M.marginalMass (insert j S) (Function.update x j z) =
      M.marginalMass S x := by
  unfold marginalMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hS : coordinateProjection (X := X) S y = coordinateProjection (X := X) S x
  · simp [projection_insert_update_iff_of_not_mem S j hj, hS]
  · simp [projection_insert_update_iff_of_not_mem S j hj, hS]

private theorem marginalMass_insert_parents_eq_factor_mul (i : V)
    (x : ∀ k, X k) (z : X i) :
    M.marginalMass (insert i (G.parents i)) (Function.update x i z) =
      M.factor i (Function.update x i z) * M.marginalMass (G.parents i) x := by
  apply (div_eq_iff (ne_of_gt (M.marginalMass_pos (G.parents i) x))).mp
  simpa [conditionalMass] using M.conditionalMass_given_parents i x z

private theorem marginalMass_insert_child_eq_factor_mul_of_independent
    {i j : V} (hji : G.edge j i) (hind : M.FactorIndependentOf i j)
    (x : ∀ k, X k) (xi : X i) :
    M.marginalMass (insert i ((G.parents i).erase j)) (Function.update x i xi) =
      M.factor i (Function.update x i xi) *
        M.marginalMass ((G.parents i).erase j) x := by
  let C := (G.parents i).erase j
  have hij : i ≠ j := by
    intro hij
    subst j
    exact G.irrefl i hji
  have hjC : j ∉ C := by simp [C]
  have hjinsert : j ∉ insert i C := by simp [hij.symm, hjC]
  have hparents : insert j C = G.parents i := by
    exact Finset.insert_erase (G.mem_parents.mpr hji)
  calc
    M.marginalMass (insert i C) (Function.update x i xi) =
        ∑ z : X j, M.marginalMass (insert j (insert i C))
          (Function.update (Function.update x i xi) j z) := by
            symm
            exact sum_marginalMass_insert M (insert i C) j hjinsert
              (Function.update x i xi)
    _ = ∑ z : X j, M.marginalMass (insert i (G.parents i))
          (Function.update (Function.update x i xi) j z) := by
            congr 1
            rw [Finset.insert_comm, hparents]
    _ = ∑ z : X j, M.factor i (Function.update (Function.update x i xi) j z) *
          M.marginalMass (G.parents i) (Function.update x j z) := by
            apply Finset.sum_congr rfl
            intro z hz
            simpa [Function.update_comm hij] using
              marginalMass_insert_parents_eq_factor_mul M i
                (Function.update x j z) xi
    _ = ∑ z : X j, M.factor i (Function.update x i xi) *
          M.marginalMass (G.parents i) (Function.update x j z) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [hind (Function.update x i xi) z]
    _ = M.factor i (Function.update x i xi) *
          ∑ z : X j, M.marginalMass (G.parents i) (Function.update x j z) := by
            rw [Finset.mul_sum]
    _ = M.factor i (Function.update x i xi) * M.marginalMass C x := by
            rw [← hparents]
            rw [sum_marginalMass_insert M C j hjC x]

/-- For a directed edge `j → i`, conditional independence of its endpoints given the other
parents is equivalent to pointwise independence of the child's local factor from `j`. -/
theorem edge_condIndep_iff_factorIndependent {i j : V} (hji : G.edge j i) :
    M.CondIndepCoordinates i j ((G.parents i).erase j) ↔ M.FactorIndependentOf i j := by
  classical
  let C := (G.parents i).erase j
  have hij : i ≠ j := by
    intro hij
    subst j
    exact G.irrefl i hji
  have hparents : insert j C = G.parents i :=
    Finset.insert_erase (G.mem_parents.mpr hji)
  constructor
  · intro hCI x xj
    have heq (z : X j) :
        M.factor i (Function.update x j z) * M.marginalMass C x =
          M.marginalMass (insert i C) x := by
      have h := hCI x (x i) z
      rw [show (G.parents i).erase j = C from rfl, hparents] at h
      have hnum :
          M.marginalMass (insert i (G.parents i))
              (Function.update (Function.update x i (x i)) j z) =
            M.factor i (Function.update x j z) *
              M.marginalMass (G.parents i) (Function.update x j z) := by
        have hcoord : Function.update x j z i = x i :=
          Function.update_of_ne hij z x
        have hidem : Function.update (Function.update x j z) i (x i) =
            Function.update x j z := by
          rw [← hcoord, Function.update_eq_self]
        simpa [hidem] using
          marginalMass_insert_parents_eq_factor_mul M i
            (Function.update x j z) (x i)
      rw [hnum] at h
      simp only [Function.update_eq_self] at h
      apply (mul_right_cancel₀
        (ne_of_gt (M.marginalMass_pos (G.parents i) (Function.update x j z))))
      ring_nf at h ⊢
      exact h
    have hnew := heq xj
    have hold := heq (x j)
    simp only [Function.update_eq_self] at hold
    apply (mul_right_cancel₀ (ne_of_gt (M.marginalMass_pos C x)))
    exact hnew.trans hold.symm
  · intro hind x xi xj
    rw [show (G.parents i).erase j = C from rfl, hparents]
    have hnum :
        M.marginalMass (insert i (G.parents i))
            (Function.update (Function.update x i xi) j xj) =
          M.factor i (Function.update (Function.update x i xi) j xj) *
            M.marginalMass (G.parents i) (Function.update x j xj) := by
      simpa [Function.update_comm hij] using
        marginalMass_insert_parents_eq_factor_mul M i
          (Function.update x j xj) xi
    rw [hnum, marginalMass_insert_child_eq_factor_mul_of_independent M hji hind]
    rw [hind (Function.update x i xi) xj]
    ring

/-- For a directed edge `j → i`, independence of the child's factor from `j` is equivalent to
vanishing of every local four-point cross-product contrast. -/
theorem factorIndependent_iff_localContrast_zero {i j : V} (hji : G.edge j i) :
    M.FactorIndependentOf i j ↔
      ∀ (x : ∀ k, X k) (xi xi' : X i) (xj xj' : X j),
        M.localContrast i j x xi xi' xj xj' = 0 := by
  constructor
  · intro hind x xi xi' xj xj'
    have hij : i ≠ j := by
      intro hij
      subst j
      exact G.irrefl i hji
    unfold localContrast
    rw [hind (Function.update x i xi) xj,
      hind (Function.update x i xi') xj',
      hind (Function.update x i xi) xj',
      hind (Function.update x i xi') xj]
    ring
  · intro hzero x xj
    have hij : i ≠ j := by
      intro hij
      subst j
      exact G.irrefl i hji
    have hcross (z w : X i) :
        M.factor i (Function.update (Function.update x j xj) i z) *
            M.factor i (Function.update x i w) =
          M.factor i (Function.update x i z) *
            M.factor i (Function.update (Function.update x j xj) i w) := by
      apply sub_eq_zero.mp
      simpa [localContrast, Function.update_comm hij] using
        hzero x z w xj (x j)
    have hsum (z : X i) :
        M.factor i (Function.update (Function.update x j xj) i z) =
          M.factor i (Function.update x i z) := by
      have hs := Finset.sum_congr rfl (fun w (_ : w ∈ Finset.univ) ↦ hcross z w)
      calc
        M.factor i (Function.update (Function.update x j xj) i z) =
            M.factor i (Function.update (Function.update x j xj) i z) * 1 := by ring
        _ = M.factor i (Function.update (Function.update x j xj) i z) *
            ∑ w : X i, M.factor i (Function.update x i w) := by
              rw [M.factor_normalized]
        _ = ∑ w : X i,
            M.factor i (Function.update (Function.update x j xj) i z) *
              M.factor i (Function.update x i w) := Finset.mul_sum _ _ _
        _ = ∑ w : X i, M.factor i (Function.update x i z) *
            M.factor i (Function.update (Function.update x j xj) i w) := hs
        _ = M.factor i (Function.update x i z) *
            ∑ w : X i,
              M.factor i (Function.update (Function.update x j xj) i w) :=
                (Finset.mul_sum _ _ _).symm
        _ = M.factor i (Function.update x i z) := by
              rw [M.factor_normalized]
              ring
    have hz := hsum (x i)
    have hcoord : Function.update x j xj i = x i :=
      Function.update_of_ne hij xj x
    have hidem : Function.update (Function.update x j xj) i (x i) =
        Function.update x j xj := by
      rw [← hcoord, Function.update_eq_self]
    simpa [hidem] using hz

/-- A [positive finite-state DAG mechanism](hyp:M) and [directed edge](hyp:hji) have
[conditional independence of the endpoints given the other parents exactly when every local
four-point factor contrast vanishes](goal). -/
theorem edge_condIndep_iff_localContrast_zero {i j : V} (hji : G.edge j i) :
    M.CondIndepCoordinates i j ((G.parents i).erase j) ↔
      ∀ (x : ∀ k, X k) (xi xi' : X i) (xj xj' : X j),
        M.localContrast i j x xi xi' xj xj' = 0 := by
  exact (M.edge_condIndep_iff_factorIndependent hji).trans
    (M.factorIndependent_iff_localContrast_zero hji)

end PositiveFiniteDAGMechanism

end Causalean.Graph.FiniteDensity

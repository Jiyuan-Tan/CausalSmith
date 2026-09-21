import Causalean.Graph.DAG
import Causalean.Graph.FiniteDensity.Coordinate

/-!
# Finite DAG density factorizations

This module packages a family of measurable normalized conditional densities on a finite DAG.
Each factor is an `ℝ≥0∞`-valued function of its node and parent coordinates.  It also defines the
single-node replacement by a normalized parent-independent intervention density.
-/

open scoped ENNReal
open Set Function
open MeasureTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {X : V → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]

/-- A [finite DAG](hyp:G), [coordinate value spaces](hyp:X), and [coordinate reference measures](hyp:μ)
determine [a factorization interface of measurable, parent-local conditional densities normalized in
their own coordinates](hyp:factor,measurable_factor,local_factor,normalized_factor). -/
structure Factorization (G : Causalean.DAG V) (X : V → Type*)
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) where
  /-- The conditional density factor belonging to a node. -/
  factor : ∀ i, (∀ k, X k) → ℝ≥0∞
  /-- Every conditional density factor is measurable on the full product. -/
  measurable_factor : ∀ i, Measurable (factor i)
  /-- A node factor is local to the node and its graph parents. -/
  local_factor : ∀ i, DependsOn (insert i (G.parents i)) (factor i)
  /-- Integrating a node factor in its own coordinate gives one for every fixed context. -/
  normalized_factor : ∀ i (v : ∀ k, X k),
    ∫⁻ x, factor i (Function.update v i x) ∂μ i = 1

/-- A [DAG factorization](hyp:B), a [finite node set](hyp:S), and a [full assignment](hyp:v)
determine [the product density over that node set](goal). -/
def Factorization.partialDensity {G : Causalean.DAG V}
    (B : Factorization G X μ) (S : Finset V) (v : ∀ i, X i) : ℝ≥0∞ :=
  ∏ i ∈ S, B.factor i v

/-- A [DAG factorization](hyp:B) and a [full assignment](hyp:v) determine [the observational
product density over all nodes](goal). -/
def Factorization.observationalDensity {G : Causalean.DAG V}
    (B : Factorization G X μ) (v : ∀ i, X i) : ℝ≥0∞ :=
  B.partialDensity Finset.univ v

/-- A [DAG factorization](hyp:B) and a [finite node set](hyp:S) [have a measurable partial
product density](goal). -/
@[fun_prop]
theorem Factorization.measurable_partialDensity {G : Causalean.DAG V}
    (B : Factorization G X μ) (S : Finset V) :
    Measurable (B.partialDensity S) := by
  change Measurable (fun v ↦ ∏ i ∈ S, B.factor i v)
  exact Finset.measurable_prod S (fun i _ ↦ B.measurable_factor i)

/-- A [DAG factorization](hyp:B) [has a measurable observational product density](goal). -/
@[fun_prop]
theorem Factorization.measurable_observationalDensity {G : Causalean.DAG V}
    (B : Factorization G X μ) : Measurable B.observationalDensity := by
  change Measurable (B.partialDensity Finset.univ)
  exact B.measurable_partialDensity Finset.univ

/-- A [DAG factorization](hyp:B), a [target node](hyp:i), and a [numerator depending on that
node's value](hyp:numerator) [give a density ratio determined only by the target and its parents](goal). -/
theorem Factorization.targetRatio_dependsOn {G : Causalean.DAG V}
    (B : Factorization G X μ) (i : V) (numerator : X i → ℝ≥0∞) :
    DependsOn (insert i (G.parents i))
      (fun v ↦ numerator (v i) / B.factor i v) := by
  intro x y hxy
  exact congrArg₂ (· / ·)
    (congrArg numerator (hxy i (Finset.mem_insert_self i _)))
    (B.local_factor i hxy)

/-- An [intervention target](hyp:j), [coordinate value spaces](hyp:X), and [coordinate reference
measures](hyp:μ) determine [a measurable unit-mass replacement density for that target](hyp:density,measurable_density,normalized_density). -/
structure InterventionDensity (j : V) (X : V → Type*) [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) where
  /-- The replacement density on the intervention target coordinate. -/
  density : X j → ℝ≥0∞
  /-- The replacement density is measurable. -/
  measurable_density : Measurable density
  /-- The replacement density has unit mass. -/
  normalized_density : ∫⁻ x, density x ∂μ j = 1

/-- A [DAG factorization](hyp:B), [intervention target](hyp:j), and [normalized replacement
density](hyp:q) determine [the factorization obtained by replacing that target's factor](goal). -/
def Factorization.intervene {G : Causalean.DAG V} (B : Factorization G X μ)
    (j : V) (q : InterventionDensity j X μ) : Factorization G X μ where
  factor i v := if i = j then q.density (v j) else B.factor i v
  measurable_factor := by
    intro i
    by_cases h : i = j
    · subst i
      simp only [↓reduceIte]
      exact q.measurable_density.comp (measurable_pi_apply j)
    · simp only [h, ↓reduceIte]
      exact B.measurable_factor i
  local_factor := by
    intro i
    by_cases h : i = j
    · subst i
      simp only [↓reduceIte]
      intro x y hxy
      exact congrArg q.density (hxy j (Finset.mem_insert_self j _))
    · simp only [h, ↓reduceIte]
      exact B.local_factor i
  normalized_factor := by
    intro i v
    by_cases h : i = j
    · subst i
      simp only [↓reduceIte]
      simpa using q.normalized_density
    · simp only [h, ↓reduceIte]
      exact B.normalized_factor i v

/-- A [DAG factorization](hyp:B), [intervention target](hyp:j), [replacement density](hyp:q), and
[full assignment](hyp:v) determine [the truncated product density for that intervention](goal). -/
def Factorization.interventionDensity {G : Causalean.DAG V}
    (B : Factorization G X μ) (j : V) (q : InterventionDensity j X μ)
    (v : ∀ i, X i) : ℝ≥0∞ :=
  q.density (v j) * B.partialDensity (Finset.univ.erase j) v

/-- A [DAG factorization](hyp:B), [intervention target](hyp:j), and [replacement density](hyp:q)
[give the same product density whether intervention is represented by factor replacement or by
the explicit truncated product](goal). -/
theorem Factorization.observationalDensity_intervene {G : Causalean.DAG V}
    (B : Factorization G X μ) (j : V) (q : InterventionDensity j X μ) :
    (B.intervene j q).observationalDensity = B.interventionDensity j q := by
  funext v
  change (∏ i ∈ Finset.univ,
      if i = j then q.density (v j) else B.factor i v) =
    q.density (v j) * ∏ i ∈ Finset.univ.erase j, B.factor i v
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  have hprod :
      (∏ i ∈ Finset.univ.erase j,
        if i = j then q.density (v j) else B.factor i v) =
        ∏ i ∈ Finset.univ.erase j, B.factor i v := by
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    simp only [hij, ↓reduceIte]
  rw [hprod]
  simp only [↓reduceIte]
  exact mul_comm _ _

/-- A [DAG factorization](hyp:B), [intervention target](hyp:j), and [replacement density](hyp:q)
[give a measurable truncated intervention density](goal). -/
@[fun_prop]
theorem Factorization.measurable_interventionDensity {G : Causalean.DAG V}
    (B : Factorization G X μ) (j : V) (q : InterventionDensity j X μ) :
    Measurable (B.interventionDensity j q) := by
  change Measurable
    (fun v ↦ q.density (v j) * B.partialDensity (Finset.univ.erase j) v)
  exact (q.measurable_density.comp (measurable_pi_apply j)).mul
    (B.measurable_partialDensity (Finset.univ.erase j))

end Causalean.Graph.FiniteDensity

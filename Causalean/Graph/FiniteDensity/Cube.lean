import Causalean.Graph.FiniteDensity.Main
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic



/-!
# Finite unit-cube specialization

This module specializes the general finite-product theorem to real coordinates equipped with
Lebesgue measure restricted to `[0,1]`.  The resulting product reference measure is concentrated
on `Set.pi Set.univ (fun _ ↦ Set.Icc 0 1)`, the finite product cube in the requirement.
-/

open scoped ENNReal
open Set Function
open MeasureTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

variable (V : Type*) [DecidableEq V] [Fintype V]

/-- A [finite vertex population](hyp:V) determines [the ambient finite unit cube of real
assignments](goal). -/
def unitCube : Set (V → ℝ) :=
  Set.pi Set.univ (fun _ ↦ Set.Icc (0 : ℝ) 1)

/-- [The one-coordinate reference measure on the unit interval](goal) is Lebesgue measure
restricted to the closed interval from zero to one. -/
def unitIntervalReference : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- A [finite vertex population](hyp:V) determines [the product reference measure on its unit
cube](goal). -/
def unitCubeReference : Measure (V → ℝ) :=
  Measure.pi (fun _ : V ↦ unitIntervalReference)

/-- A [finite vertex population](hyp:V) [has a unit-cube product reference measure concentrated
on the ambient finite unit cube](goal). -/
theorem unitCubeReference_compl (V : Type*) [DecidableEq V] [Fintype V] :
    unitCubeReference V (unitCube V)ᶜ = 0 := by
  -- Rewrite `Set.pi Set.univ` as an intersection of coordinate preimages, take complements,
  -- and use `measure_iUnion_null` with `Measure.pi_eval_preimage_null`.  Unfold
  -- `unitIntervalReference` when synthesizing the `SigmaFinite` instance for the restricted
  -- Lebesgue measure; the definition is intentionally not an abbreviation.
  classical
  have hσ : ∀ _ : V, SigmaFinite unitIntervalReference := fun _ ↦ by
    unfold unitIntervalReference
    infer_instance
  rw [unitCubeReference, unitCube, univ_pi_eq_iInter, compl_iInter]
  apply measure_iUnion_null
  intro i
  rw [← preimage_compl]
  exact @Measure.pi_eval_preimage_null V (fun _ : V ↦ ℝ) _ _
    (fun _ : V ↦ unitIntervalReference) hσ i (Set.Icc 0 1)ᶜ
    (by simp [unitIntervalReference])

/-- A [finite DAG](hyp:G) determines [the factorization interface whose coordinates use
unit-interval-restricted Lebesgue reference measure](goal). -/
abbrev UnitCubeFactorization (G : Causalean.DAG V) :=
  Factorization G (fun _ : V ↦ ℝ) (fun _ : V ↦ unitIntervalReference)

/-- A [unit-cube DAG factorization](hyp:B), [distinct intervention and queried nodes](hyp:hji),
evidence that [the intervention target is not an ancestor of the queried node](hyp:hnotAncestor),
and a [normalized replacement density](hyp:q) [give identical observational and interventional
laws on the queried node's ancestral closure](goal). -/
theorem UnitCubeFactorization.ancestralMarginal_eq
    {G : Causalean.DAG V} (B : UnitCubeFactorization V G) {i j : V}
    (hji : j ≠ i) (hnotAncestor : ¬ G.isAncestor j i)
    (q : InterventionDensity j (fun _ : V ↦ ℝ) (fun _ : V ↦ unitIntervalReference)) :
    Measure.map
        (coordinateProjection (X := fun _ : V ↦ ℝ) (nodeAncestralClosure G i))
        B.observationalMeasure =
      Measure.map
        (coordinateProjection (X := fun _ : V ↦ ℝ) (nodeAncestralClosure G i))
        (B.interventionMeasure j q) := by
  -- Establish the coordinatewise `SigmaFinite` family by unfolding `unitIntervalReference`,
  -- then apply `Factorization.ancestralMarginal_eq` without changing the measures or projection.
  have hσ : ∀ _ : V, SigmaFinite unitIntervalReference := fun _ ↦ by
    unfold unitIntervalReference
    infer_instance
  exact @Factorization.ancestralMarginal_eq V _ _ (fun _ : V ↦ ℝ) _
    (fun _ : V ↦ unitIntervalReference) hσ G B i j hji hnotAncestor q

end Causalean.Graph.FiniteDensity
/-! ## Coordinatewise retraction onto a finite unit cube -/

open Set Function MeasureTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

variable (V : Type*) [DecidableEq V] [Fintype V]

/-- A [finite coordinate type](hyp:V) and [a real assignment](hyp:v) determine [the
coordinatewise clamp to the closed unit cube](goal), [by clamping each coordinate between zero
and one](step:1). -/
def clampCube (v : V → ℝ) : V → ℝ :=
  fun i ↦ max 0 (min 1 (v i))

/-- The [coordinatewise clamp for a finite coordinate type](hyp:V) [is measurable](goal). -/
@[fun_prop]
theorem measurable_clampCube : Measurable (clampCube V) := by
  -- Prove each coordinate measurable from `measurable_pi_iff`, using measurability of `min` and
  -- `max` on the real line.
  refine measurable_pi_iff.mpr fun i ↦ ?_
  exact measurable_const.max (measurable_const.min (measurable_pi_apply i))

/-- Every [real assignment](hyp:v) over [a finite coordinate type](hyp:V) is [sent by the
coordinatewise clamp into the finite unit cube](goal). -/
theorem clampCube_mem (v : V → ℝ) :
    clampCube V v ∈ Causalean.Graph.FiniteDensity.unitCube V := by
  -- Unfold membership in `Set.pi`; the scalar expression is between zero and one by the linear
  -- order laws for `min` and `max`.
  rw [Causalean.Graph.FiniteDensity.unitCube]
  intro i _
  constructor
  · exact le_max_left _ _
  · exact max_le zero_le_one (min_le_left _ _)

/-- A [finite coordinate type](hyp:V) and [a point in its unit cube](hyp:hv) are such that [the
coordinatewise clamp fixes that point](goal). -/
@[simp]
theorem clampCube_eq_self {v : V → ℝ}
    (hv : v ∈ Causalean.Graph.FiniteDensity.unitCube V) :
    clampCube V v = v := by
  -- Extensionality reduces this to `max_eq_right` and `min_eq_right`, using the two coordinate
  -- inequalities extracted from `hv`.
  ext i
  have hi : v i ∈ Set.Icc (0 : ℝ) 1 := hv i (Set.mem_univ i)
  simp [clampCube, min_eq_right hi.2, max_eq_right hi.1]

/-- [An assignment](hyp:v), [a coordinate](hyp:i), and [a replacement value](hyp:x) satisfy
[the update-and-clamp identity](goal). -/
theorem clampCube_update (v : V → ℝ) (i : V) (x : ℝ) :
    clampCube V (Function.update v i x) =
      Function.update (clampCube V v) i (max 0 (min 1 x)) := by
  -- Use function extensionality and split on whether the inspected coordinate is `i`.
  ext j
  by_cases h : j = i
  · simp [clampCube, h]
  · simp [clampCube, h]

/-- [An assignment](hyp:v), [a coordinate](hyp:i), and [a replacement value in the unit
interval](hyp:hx) satisfy [the update identity in which only the unchanged context is
clamped](goal). -/
theorem clampCube_update_of_mem (v : V → ℝ) (i : V) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    clampCube V (Function.update v i x) =
      Function.update (clampCube V v) i x := by
  -- Rewrite with `clampCube_update` and simplify the scalar clamp from `hx`.
  rw [clampCube_update]
  simp [min_eq_right hx.2, max_eq_right hx.1]

end Causalean.Graph.FiniteDensity

/-! ## Unit-cube reference measure -/

open Set MeasureTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

/-- For a [finite coordinate type](hyp:V), [the product of unit-interval Lebesgue restrictions is
Lebesgue volume restricted to the finite unit cube](goal). -/
theorem unitCubeReference_eq_volume_restrict
    (V : Type*) [DecidableEq V] [Fintype V] :
    Causalean.Graph.FiniteDensity.unitCubeReference V =
      volume.restrict (Causalean.Graph.FiniteDensity.unitCube V) := by
  -- Unfold both Causalean definitions.  Rewrite product volume with `volume_pi`, then apply
  -- `Measure.restrict_pi_pi` to the constant family `Set.Icc 0 1`.
  rw [Causalean.Graph.FiniteDensity.unitCubeReference,
    Causalean.Graph.FiniteDensity.unitIntervalReference,
    Causalean.Graph.FiniteDensity.unitCube, volume_pi, Measure.restrict_pi_pi]

end Causalean.Graph.FiniteDensity

/-! ## Unit-cube factorization constructors -/

open scoped BigOperators ENNReal
open Set Function MeasureTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

variable {V : Type*} [DecidableEq V] [Fintype V]

private theorem measurableSet_unitCube :
    MeasurableSet (Causalean.Graph.FiniteDensity.unitCube V) := by
  rw [Causalean.Graph.FiniteDensity.unitCube]
  exact MeasurableSet.pi Set.countable_univ (fun _ _ ↦ measurableSet_Icc)

/-- A [function](hyp:f) and [a set](hyp:S) determine [the proposition that the function is
measurable on that set](goal), [by testing the restriction to the set's subtype](step:1). -/
def MeasurableOnSet {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (S : Set X) : Prop :=
  Measurable (fun x : S ↦ f x)

/-- A [node set](hyp:A) and [an extended-nonnegative function](hyp:f) determine [cube-local
dependence](goal), [by requiring agreement on those coordinates to determine the function value
at any two cube points](step:1). -/
def CubeDependsOn (A : Finset V) (f : (V → ℝ) → ℝ≥0∞) : Prop :=
  ∀ {v w : V → ℝ},
    v ∈ Causalean.Graph.FiniteDensity.unitCube V →
    w ∈ Causalean.Graph.FiniteDensity.unitCube V →
    (∀ i ∈ A, v i = w i) → f v = f w

/-- A [cube-local extended-nonnegative function](hyp:p) determines [its globally defined clamped
extension](goal), [by evaluating it after coordinatewise clamping](step:1). -/
def clampedFactor (p : (V → ℝ) → ℝ≥0∞) : (V → ℝ) → ℝ≥0∞ :=
  fun v ↦ p (clampCube V v)

/-- A [cube-local real function](hyp:p) determines [its globally defined nonnegative clamped
extension](goal), [by applying the nonnegative-real conversion after coordinatewise
clamping](step:1). -/
def clampedOfRealFactor (p : (V → ℝ) → ℝ) : (V → ℝ) → ℝ≥0∞ :=
  fun v ↦ ENNReal.ofReal (p (clampCube V v))

/-- [A cube-local extended-nonnegative function](hyp:p) with [cube-local measurability](hyp:hp)
has [a globally measurable clamped extension](goal). -/
@[fun_prop]
theorem measurable_clampedFactor {p : (V → ℝ) → ℝ≥0∞}
    (hp : MeasurableOnSet p (Causalean.Graph.FiniteDensity.unitCube V)) :
    Measurable (clampedFactor p) := by
  -- Regard `clampCube` as a measurable map into the cube subtype using `clampCube_mem`, then
  -- compose it with `hp`.
  exact hp.comp ((measurable_clampCube V).subtype_mk (h := clampCube_mem V))

/-- [A cube-local real function](hyp:p) with [cube-local measurability](hyp:hp) has [a globally
measurable nonnegative clamped extension](goal). -/
@[fun_prop]
theorem measurable_clampedOfRealFactor {p : (V → ℝ) → ℝ}
    (hp : MeasurableOnSet p (Causalean.Graph.FiniteDensity.unitCube V)) :
    Measurable (clampedOfRealFactor p) := by
  -- Compose the subtype-valued clamp with `hp`, then with `ENNReal.measurable_ofReal`.
  exact ENNReal.measurable_ofReal.comp
    (hp.comp ((measurable_clampCube V).subtype_mk (h := clampCube_mem V)))

/-- [Cube-local extended-nonnegative factors](hyp:p) that are [measurable on the cube](hyp:hmeas),
[local to each node and its parents on the cube](hyp:hlocal), and [normalized in their own
coordinates on the cube](hyp:hnorm) determine [a global unit-cube DAG factorization](goal), [by
using their clamped extensions as factors](step:1). -/
def unitCubeFactorizationOfCubeFactors
    {G : Causalean.DAG V} (p : ∀ i : V, (V → ℝ) → ℝ≥0∞)
    (hmeas : ∀ i : V, MeasurableOnSet (p i) (Causalean.Graph.FiniteDensity.unitCube V))
    (hlocal : ∀ i : V, CubeDependsOn (insert i (G.parents i)) (p i))
    (hnorm : ∀ i : V, ∀ v : V → ℝ,
      v ∈ Causalean.Graph.FiniteDensity.unitCube V →
      ∫⁻ x in Set.Icc (0 : ℝ) 1, p i (Function.update v i x) ∂volume = 1) :
    Causalean.Graph.FiniteDensity.UnitCubeFactorization V G := by
  -- Set `factor i := clampedFactor (p i)`.  Measurability is the preceding lemma; locality follows
  -- because clamping preserves equality coordinatewise; normalization rewrites
  -- `clampCube (update v i x)` on `Icc` and unfolds `unitIntervalReference`.
  refine
    { factor := fun i ↦ clampedFactor (p i)
      measurable_factor := fun i ↦ measurable_clampedFactor (hmeas i)
      local_factor := ?_
      normalized_factor := ?_ }
  · intro i v w hvw
    apply hlocal i (clampCube_mem V v) (clampCube_mem V w)
    intro k hk
    simp only [clampCube]
    rw [hvw k hk]
  · intro i v
    unfold Causalean.Graph.FiniteDensity.unitIntervalReference
    change ∫⁻ x in Set.Icc (0 : ℝ) 1,
      p i (clampCube V (Function.update v i x)) ∂volume = 1
    rw [setLIntegral_congr_fun measurableSet_Icc
      (fun x hx ↦ congrArg (p i) (clampCube_update_of_mem V v i hx))]
    exact hnorm i (clampCube V v) (clampCube_mem V v)

/-- [Cube-local factors](hyp:p) with [cube measurability](hyp:hmeas), [node-and-parent
locality](hyp:hlocal), and [coordinate-wise normalization](hyp:hnorm), evaluated at [a node](hyp:i)
and [a cube point](hyp:hv), give [a constructed factor equal to the original factor](goal). -/
theorem unitCubeFactorizationOfCubeFactors_factor_eq
    {G : Causalean.DAG V} (p : ∀ i : V, (V → ℝ) → ℝ≥0∞)
    (hmeas : ∀ i : V, MeasurableOnSet (p i) (Causalean.Graph.FiniteDensity.unitCube V))
    (hlocal : ∀ i : V, CubeDependsOn (insert i (G.parents i)) (p i))
    (hnorm : ∀ i : V, ∀ v : V → ℝ,
      v ∈ Causalean.Graph.FiniteDensity.unitCube V →
      ∫⁻ x in Set.Icc (0 : ℝ) 1, p i (Function.update v i x) ∂volume = 1)
    (i : V) {v : V → ℝ} (hv : v ∈ Causalean.Graph.FiniteDensity.unitCube V) :
    (unitCubeFactorizationOfCubeFactors p hmeas hlocal hnorm).factor i v = p i v := by
  -- Unfold the constructor and rewrite `clampCube V v` with `clampCube_eq_self hv`.
  simp [unitCubeFactorizationOfCubeFactors, clampedFactor, clampCube_eq_self V hv]

/-- [Cube-local extended-nonnegative factors](hyp:p) determine [the corresponding cube-restricted
observational product-density measure](goal), [by weighting restricted Lebesgue volume with their
joint product](step:1). -/
def cubeProductDensityMeasure (p : ∀ i : V, (V → ℝ) → ℝ≥0∞) : Measure (V → ℝ) :=
  (volume.restrict (Causalean.Graph.FiniteDensity.unitCube V)).withDensity
    (fun v ↦ ∏ i, p i v)

/-- [Cube-local extended-nonnegative factors](hyp:p), [a target coordinate](hyp:j), and [a
replacement density](hyp:q) determine [the corresponding cube-restricted single-target
product-density measure](goal), [by replacing that coordinate's factor in the joint product](step:1). -/
def cubeInterventionDensityMeasure (p : ∀ i : V, (V → ℝ) → ℝ≥0∞)
    (j : V) (q : ℝ → ℝ≥0∞) : Measure (V → ℝ) :=
  (volume.restrict (Causalean.Graph.FiniteDensity.unitCube V)).withDensity
    (fun v ↦ q (v j) * ∏ i ∈ Finset.univ.erase j, p i v)

/-- [Cube-local factors](hyp:p) with [cube measurability](hyp:hmeas), [node-and-parent
locality](hyp:hlocal), and [coordinate-wise normalization](hyp:hnorm) give [an observational law
of the clamped factorization equal to the cube-restricted product-density measure](goal). -/
theorem observationalMeasure_unitCubeFactorizationOfCubeFactors
    {G : Causalean.DAG V} (p : ∀ i : V, (V → ℝ) → ℝ≥0∞)
    (hmeas : ∀ i : V, MeasurableOnSet (p i) (Causalean.Graph.FiniteDensity.unitCube V))
    (hlocal : ∀ i : V, CubeDependsOn (insert i (G.parents i)) (p i))
    (hnorm : ∀ i : V, ∀ v : V → ℝ,
      v ∈ Causalean.Graph.FiniteDensity.unitCube V →
      ∫⁻ x in Set.Icc (0 : ℝ) 1, p i (Function.update v i x) ∂volume = 1) :
    (unitCubeFactorizationOfCubeFactors p hmeas hlocal hnorm).observationalMeasure =
      cubeProductDensityMeasure p := by
  -- Rewrite the reference measure with `unitCubeReference_eq_volume_restrict`; then apply
  -- `Measure.withDensity_congr_ae`, using the factor-on-cube lemma under the restricted measure.
  rw [Causalean.Graph.FiniteDensity.Factorization.observationalMeasure]
  change (Causalean.Graph.FiniteDensity.unitCubeReference V).withDensity _ = _
  rw [unitCubeReference_eq_volume_restrict]
  unfold cubeProductDensityMeasure
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_unitCube] with v hv
  unfold Causalean.Graph.FiniteDensity.Factorization.observationalDensity
    Causalean.Graph.FiniteDensity.Factorization.partialDensity
  apply Finset.prod_congr rfl
  intro i hi
  exact unitCubeFactorizationOfCubeFactors_factor_eq p hmeas hlocal hnorm i hv

/-- [A target coordinate](hyp:j) and [a cube-local replacement density](hyp:q) that is
[measurable on the interval](hyp:hqmeas) and [normalized there](hyp:hqnorm) determine [a global
intervention density](goal), [by scalar clamping](step:1). -/
def interventionDensityOfCube
    (j : V) (q : ℝ → ℝ≥0∞)
    (hqmeas : MeasurableOnSet q (Set.Icc (0 : ℝ) 1))
    (hqnorm : ∫⁻ x in Set.Icc (0 : ℝ) 1, q x ∂volume = 1) :
    Causalean.Graph.FiniteDensity.InterventionDensity j (fun _ : V ↦ ℝ)
      (fun _ : V ↦ Causalean.Graph.FiniteDensity.unitIntervalReference) := by
  -- Clamp the scalar input to `[0,1]`; its measurability and normalization are the one-dimensional
  -- versions of the factor-constructor arguments.
  refine
    { density := fun x ↦ q (max 0 (min 1 x))
      measurable_density := ?_
      normalized_density := ?_ }
  · exact hqmeas.comp
      ((measurable_const.max (measurable_const.min measurable_id)).subtype_mk (h := fun x ↦ by
        exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩))
  · unfold Causalean.Graph.FiniteDensity.unitIntervalReference
    change ∫⁻ x in Set.Icc (0 : ℝ) 1, q (max 0 (min 1 x)) ∂volume = 1
    rw [setLIntegral_congr_fun measurableSet_Icc]
    · exact hqnorm
    · intro x hx
      simp [min_eq_right hx.2, max_eq_right hx.1]

/-- [Cube-local factors](hyp:p) with [cube measurability](hyp:hmeas), [node-and-parent
locality](hyp:hlocal), and [coordinate-wise normalization](hyp:hnorm), together with [a target
coordinate](hyp:j), [a replacement density](hyp:q), [its interval measurability](hyp:hqmeas), and
[its normalization](hyp:hqnorm), give [an intervention law equal to the cube-restricted
replacement product-density measure](goal). -/
theorem interventionMeasure_unitCubeFactorizationOfCubeFactors
    {G : Causalean.DAG V} (p : ∀ i : V, (V → ℝ) → ℝ≥0∞)
    (hmeas : ∀ i : V, MeasurableOnSet (p i) (Causalean.Graph.FiniteDensity.unitCube V))
    (hlocal : ∀ i : V, CubeDependsOn (insert i (G.parents i)) (p i))
    (hnorm : ∀ i : V, ∀ v : V → ℝ,
      v ∈ Causalean.Graph.FiniteDensity.unitCube V →
      ∫⁻ x in Set.Icc (0 : ℝ) 1, p i (Function.update v i x) ∂volume = 1)
    (j : V) (q : ℝ → ℝ≥0∞)
    (hqmeas : MeasurableOnSet q (Set.Icc (0 : ℝ) 1))
    (hqnorm : ∫⁻ x in Set.Icc (0 : ℝ) 1, q x ∂volume = 1) :
    (unitCubeFactorizationOfCubeFactors p hmeas hlocal hnorm).interventionMeasure j
        (interventionDensityOfCube j q hqmeas hqnorm) =
      cubeInterventionDensityMeasure p j q := by
  -- Rewrite the reference measure, use with-density a.e. congruence on the cube, and simplify both
  -- the replacement density and every retained factor by their identity-on-cube lemmas.
  rw [Causalean.Graph.FiniteDensity.Factorization.interventionMeasure]
  change (Causalean.Graph.FiniteDensity.unitCubeReference V).withDensity _ = _
  rw [unitCubeReference_eq_volume_restrict]
  unfold cubeInterventionDensityMeasure
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_unitCube] with v hv
  unfold Causalean.Graph.FiniteDensity.Factorization.interventionDensity
  congr 1
  · simp [interventionDensityOfCube]
    have hj := hv j (Set.mem_univ j)
    simp [min_eq_right hj.2, max_eq_right hj.1]
  · apply Finset.prod_congr rfl
    intro i hi
    exact unitCubeFactorizationOfCubeFactors_factor_eq p hmeas hlocal hnorm i hv

/-- [Real-valued cube factors](hyp:p) that are [measurable on the cube](hyp:hmeas),
[nonnegative there](hyp:hnonneg), [local to each node and its parents](hyp:hlocal), and
[normalized by Lebesgue integration in their own coordinate](hyp:hnorm) determine [a global
unit-cube DAG factorization](goal), [by conversion to extended nonnegative factors](step:1). -/
def unitCubeFactorizationOfRealCubeFactors
    {G : Causalean.DAG V} (p : ∀ i : V, (V → ℝ) → ℝ)
    (hmeas : ∀ i : V, MeasurableOnSet (p i) (Causalean.Graph.FiniteDensity.unitCube V))
    (hnonneg : ∀ i : V, ∀ v, v ∈ Causalean.Graph.FiniteDensity.unitCube V → 0 ≤ p i v)
    (hlocal : ∀ i : V, ∀ {v w : V → ℝ},
      v ∈ Causalean.Graph.FiniteDensity.unitCube V →
      w ∈ Causalean.Graph.FiniteDensity.unitCube V →
      (∀ k ∈ insert i (G.parents i), v k = w k) → p i v = p i w)
    (hnorm : ∀ i : V, ∀ v : V → ℝ,
      v ∈ Causalean.Graph.FiniteDensity.unitCube V →
      ∫ x in Set.Icc (0 : ℝ) 1, p i (Function.update v i x) ∂volume = 1) :
    Causalean.Graph.FiniteDensity.UnitCubeFactorization V G := by
  -- Apply the ENNReal constructor to `fun i v ↦ ENNReal.ofReal (p i v)`.  Convert ordinary
  -- integrals of nonnegative measurable functions to lintegrals, and transfer parent locality
  -- through `ENNReal.ofReal`.
  apply unitCubeFactorizationOfCubeFactors (fun i v ↦ ENNReal.ofReal (p i v))
  · intro i
    exact ENNReal.measurable_ofReal.comp (hmeas i)
  · intro i v w hv hw hvw
    exact congrArg ENNReal.ofReal (hlocal i hv hw hvw)
  · intro i v hv
    have hvi : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        Function.update v i x ∈ Causalean.Graph.FiniteDensity.unitCube V := by
      intro x hx k hk
      by_cases hki : k = i
      · subst k
        simpa using hx
      · simpa [Function.update, hki] using hv k hk
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
        (fun x ↦ p i (Function.update v i x)) :=
      ae_restrict_of_forall_mem measurableSet_Icc fun x hx ↦ hnonneg i _ (hvi x hx)
    have hint : Integrable (fun x ↦ p i (Function.update v i x))
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      integrable_of_integral_eq_one (hnorm i v hv)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hnorm i v hv, ENNReal.ofReal_one]

/-- [Real cube factors](hyp:p) with [cube measurability](hyp:hmeas), [nonnegativity](hyp:hnonneg),
[node-and-parent locality](hyp:hlocal), and [coordinate-wise normalization](hyp:hnorm), evaluated
at [a node](hyp:i) and [a cube point](hyp:hv), give [a constructed factor equal to the
nonnegative-real conversion of the original factor](goal). -/
theorem unitCubeFactorizationOfRealCubeFactors_factor_eq
    {G : Causalean.DAG V} (p : ∀ i : V, (V → ℝ) → ℝ)
    (hmeas : ∀ i : V, MeasurableOnSet (p i) (Causalean.Graph.FiniteDensity.unitCube V))
    (hnonneg : ∀ i : V, ∀ v, v ∈ Causalean.Graph.FiniteDensity.unitCube V → 0 ≤ p i v)
    (hlocal : ∀ i : V, ∀ {v w : V → ℝ},
      v ∈ Causalean.Graph.FiniteDensity.unitCube V →
      w ∈ Causalean.Graph.FiniteDensity.unitCube V →
      (∀ k ∈ insert i (G.parents i), v k = w k) → p i v = p i w)
    (hnorm : ∀ i : V, ∀ v : V → ℝ,
      v ∈ Causalean.Graph.FiniteDensity.unitCube V →
      ∫ x in Set.Icc (0 : ℝ) 1, p i (Function.update v i x) ∂volume = 1)
    (i : V) {v : V → ℝ} (hv : v ∈ Causalean.Graph.FiniteDensity.unitCube V) :
    (unitCubeFactorizationOfRealCubeFactors p hmeas hnonneg hlocal hnorm).factor i v =
      ENNReal.ofReal (p i v) := by
  -- Reduce to the ENNReal factor-on-cube theorem used by the real constructor.
  simp [unitCubeFactorizationOfRealCubeFactors,
    unitCubeFactorizationOfCubeFactors, clampedFactor, clampCube_eq_self V hv]

/-- [Nonnegative real-valued cube factors](hyp:p) determine [their cube-restricted observational
product-density measure](goal), [by converting their joint real product to an extended
nonnegative density](step:1). -/
def realCubeProductDensityMeasure (p : ∀ i : V, (V → ℝ) → ℝ) : Measure (V → ℝ) :=
  (volume.restrict (Causalean.Graph.FiniteDensity.unitCube V)).withDensity
    (fun v ↦ ENNReal.ofReal (∏ i, p i v))

/-- [Nonnegative real-valued cube factors](hyp:p), [a target coordinate](hyp:j), and [a real
replacement density](hyp:q) determine [their cube-restricted single-target product-density
measure](goal), [by replacing the target factor before converting the product](step:1). -/
def realCubeInterventionDensityMeasure (p : ∀ i : V, (V → ℝ) → ℝ)
    (j : V) (q : ℝ → ℝ) : Measure (V → ℝ) :=
  (volume.restrict (Causalean.Graph.FiniteDensity.unitCube V)).withDensity
    (fun v ↦ ENNReal.ofReal (q (v j) * ∏ i ∈ Finset.univ.erase j, p i v))

/-- [Real cube factors](hyp:p) with [cube measurability](hyp:hmeas), [nonnegativity](hyp:hnonneg),
[node-and-parent locality](hyp:hlocal), and [coordinate-wise normalization](hyp:hnorm) give [an
observational law equal to the usual cube-restricted real product-density measure](goal). -/
theorem observationalMeasure_unitCubeFactorizationOfRealCubeFactors
    {G : Causalean.DAG V} (p : ∀ i : V, (V → ℝ) → ℝ)
    (hmeas : ∀ i : V, MeasurableOnSet (p i) (Causalean.Graph.FiniteDensity.unitCube V))
    (hnonneg : ∀ i : V, ∀ v, v ∈ Causalean.Graph.FiniteDensity.unitCube V → 0 ≤ p i v)
    (hlocal : ∀ i : V, ∀ {v w : V → ℝ},
      v ∈ Causalean.Graph.FiniteDensity.unitCube V →
      w ∈ Causalean.Graph.FiniteDensity.unitCube V →
      (∀ k ∈ insert i (G.parents i), v k = w k) → p i v = p i w)
    (hnorm : ∀ i : V, ∀ v : V → ℝ,
      v ∈ Causalean.Graph.FiniteDensity.unitCube V →
      ∫ x in Set.Icc (0 : ℝ) 1, p i (Function.update v i x) ∂volume = 1) :
    (unitCubeFactorizationOfRealCubeFactors p hmeas hnonneg hlocal hnorm).observationalMeasure =
      realCubeProductDensityMeasure p := by
  -- Start from the ENNReal observational identity and rewrite the finite product of `ofReal`
  -- factors as `ofReal` of the real product, using cube nonnegativity.
  rw [Causalean.Graph.FiniteDensity.Factorization.observationalMeasure]
  change (Causalean.Graph.FiniteDensity.unitCubeReference V).withDensity _ = _
  rw [unitCubeReference_eq_volume_restrict]
  unfold realCubeProductDensityMeasure
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_unitCube] with v hv
  unfold Causalean.Graph.FiniteDensity.Factorization.observationalDensity
    Causalean.Graph.FiniteDensity.Factorization.partialDensity
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hnonneg i v hv)]
  apply Finset.prod_congr rfl
  intro i hi
  exact unitCubeFactorizationOfRealCubeFactors_factor_eq
    p hmeas hnonneg hlocal hnorm i hv

/-- [A target coordinate](hyp:j) and [a real replacement density](hyp:q) that is [measurable on
the unit interval](hyp:hqmeas), [nonnegative there](hyp:hqnonneg), and
[Lebesgue-normalized](hyp:hqnorm) determine [a global intervention density](goal), [by
nonnegative-real conversion followed by scalar clamping](step:1). -/
def interventionDensityOfRealCube
    (j : V) (q : ℝ → ℝ)
    (hqmeas : MeasurableOnSet q (Set.Icc (0 : ℝ) 1))
    (hqnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ q x)
    (hqnorm : ∫ x in Set.Icc (0 : ℝ) 1, q x ∂volume = 1) :
    Causalean.Graph.FiniteDensity.InterventionDensity j (fun _ : V ↦ ℝ)
      (fun _ : V ↦ Causalean.Graph.FiniteDensity.unitIntervalReference) := by
  -- Apply `interventionDensityOfCube` to `ENNReal.ofReal ∘ q`, converting the normalized
  -- nonnegative ordinary integral to the required lintegral.
  apply interventionDensityOfCube j (fun x ↦ ENNReal.ofReal (q x))
  · exact ENNReal.measurable_ofReal.comp hqmeas
  · have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] q :=
      ae_restrict_of_forall_mem measurableSet_Icc hqnonneg
    have hint : Integrable q (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      integrable_of_integral_eq_one hqnorm
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hqnorm, ENNReal.ofReal_one]

/-- [Real cube factors](hyp:p) with [cube measurability](hyp:hmeas), [nonnegativity](hyp:hnonneg),
[node-and-parent locality](hyp:hlocal), and [coordinate-wise normalization](hyp:hnorm), together
with [a target coordinate](hyp:j), [a real replacement density](hyp:q), [its interval
measurability](hyp:hqmeas), [its nonnegativity](hyp:hqnonneg), and [its normalization](hyp:hqnorm),
give [an intervention law equal to the usual cube-restricted real replacement product-density
measure](goal). -/
theorem interventionMeasure_unitCubeFactorizationOfRealCubeFactors
    {G : Causalean.DAG V} (p : ∀ i : V, (V → ℝ) → ℝ)
    (hmeas : ∀ i : V, MeasurableOnSet (p i) (Causalean.Graph.FiniteDensity.unitCube V))
    (hnonneg : ∀ i : V, ∀ v, v ∈ Causalean.Graph.FiniteDensity.unitCube V → 0 ≤ p i v)
    (hlocal : ∀ i : V, ∀ {v w : V → ℝ},
      v ∈ Causalean.Graph.FiniteDensity.unitCube V →
      w ∈ Causalean.Graph.FiniteDensity.unitCube V →
      (∀ k ∈ insert i (G.parents i), v k = w k) → p i v = p i w)
    (hnorm : ∀ i : V, ∀ v : V → ℝ,
      v ∈ Causalean.Graph.FiniteDensity.unitCube V →
      ∫ x in Set.Icc (0 : ℝ) 1, p i (Function.update v i x) ∂volume = 1)
    (j : V) (q : ℝ → ℝ)
    (hqmeas : MeasurableOnSet q (Set.Icc (0 : ℝ) 1))
    (hqnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ q x)
    (hqnorm : ∫ x in Set.Icc (0 : ℝ) 1, q x ∂volume = 1) :
    (unitCubeFactorizationOfRealCubeFactors p hmeas hnonneg hlocal hnorm).interventionMeasure j
        (interventionDensityOfRealCube j q hqmeas hqnonneg hqnorm) =
      realCubeInterventionDensityMeasure p j q := by
  -- Use the ENNReal intervention identity and combine `ofReal` over the nonnegative replacement
  -- and retained-factor product on the cube.
  rw [Causalean.Graph.FiniteDensity.Factorization.interventionMeasure]
  change (Causalean.Graph.FiniteDensity.unitCubeReference V).withDensity _ = _
  rw [unitCubeReference_eq_volume_restrict]
  unfold realCubeInterventionDensityMeasure
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_unitCube] with v hv
  rw [ENNReal.ofReal_mul (hqnonneg (v j) (hv j (Set.mem_univ j))),
    ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hnonneg i v hv)]
  unfold Causalean.Graph.FiniteDensity.Factorization.interventionDensity
  congr 1
  · simp [interventionDensityOfRealCube, interventionDensityOfCube]
    have hj := hv j (Set.mem_univ j)
    simp [min_eq_right hj.2, max_eq_right hj.1]
  · apply Finset.prod_congr rfl
    intro i hi
    exact unitCubeFactorizationOfRealCubeFactors_factor_eq
      p hmeas hnonneg hlocal hnorm i hv

/-- [Real cube factors](hyp:p) with [continuity on the finite unit cube](hyp:hcont) have [the
cube-local measurability required by the real-valued factorization constructor](goal). -/
theorem measurableOnSet_of_continuousOn_cube
    (p : ∀ i : V, (V → ℝ) → ℝ)
    (hcont : ∀ i : V, ContinuousOn (p i) (Causalean.Graph.FiniteDensity.unitCube V)) :
    ∀ i : V, MeasurableOnSet (p i) (Causalean.Graph.FiniteDensity.unitCube V) := by
  -- A continuous map on a set is continuous as a map from the subtype; continuous maps between
  -- these Borel spaces are measurable.
  intro i
  exact (hcont i).domRestrict.measurable

end Causalean.Graph.FiniteDensity







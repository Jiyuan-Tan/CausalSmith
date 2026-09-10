import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Explicit sparse, cancellation, and affine-path mechanisms

This file contains the elementary compact-cube mechanisms used by the
genericity and cancellation arguments.
-/

open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- Reflection of a coordinate when its prescribed sign is negative. -/
def reflect (σ z : ℝ) : ℝ := if σ = 1 then z else 1 - z

/-- The centered affine function `2z-1`. -/
def centeredCoordinate (z : ℝ) : ℝ := 2 * z - 1

/-- The normalized exponential intervention density. -/
def exponentialInterventionDensity (z : ℝ) : ℝ :=
  4 * Real.exp (4 * z) / (Real.exp 4 - 1)

/-- The cancellation primitive `H`. -/
def cancellationPrimitive (x : ℝ) : ℝ :=
  (Real.exp (4 * x) - 1) / (Real.exp 4 - 1) - x

/-- The three-node graph `0 → 1` with node `2` isolated. -/
def threeNodeEdge (i j : Fin 3) : Prop := i = 0 ∧ j = 1

lemma threeNodeEdge_acyclic (v : Fin 3) : ¬ Relation.TransGen threeNodeEdge v v := by
  intro h
  have path_shape : ∀ {a b : Fin 3}, Relation.TransGen threeNodeEdge a b →
      a = 0 ∧ b = 1 := by
    intro a b hab
    induction hab with
    | single hab => exact hab
    | tail hab hbc ih => exact ⟨ih.1, hbc.2⟩
  rcases path_shape h with ⟨hv0, hv1⟩
  simp_all

/-- The fixed three-node witness DAG. -/
def threeNodeDAG : Causalean.DAG (Fin 3) where
  edge := threeNodeEdge
  decEdge := fun i j => by unfold threeNodeEdge; infer_instance
  acyclic := threeNodeEdge_acyclic

/-- Reflected coordinate selected by a sign vector. -/
def reflectedCoordinate {n : ℕ} (s : SignVector n) (i : Fin n) (z : ℝ) : ℝ :=
  reflect (s.value i) z

/-- Sparse witness observational conditional mechanism. -/
def sparseP (s : SignVector 3) (i : Fin 3) (v : LatentState 3) : ℝ :=
  if i = 1 then
    1 + (1 / 10 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
      centeredCoordinate (reflectedCoordinate s 1 (v 1))
  else 1

/-- Sparse witness intervention mechanism. -/
def sparseQ (s : SignVector 3) (i : Fin 3) (z : ℝ) : ℝ :=
  exponentialInterventionDensity (reflectedCoordinate s i z)

lemma sparseP_parent_local (s : SignVector 3) :
    ∀ i v w, v i = w i →
      (∀ j ∈ threeNodeDAG.parents i, v j = w j) → sparseP s i v = sparseP s i w := by
  intro i v w hi hp
  simp only [sparseP]
  split
  · rename_i h_i
    have h0 : v 0 = w 0 := hp 0 (by simp [threeNodeDAG, Causalean.DAG.parents,
      threeNodeEdge, h_i])
    have h1 : v 1 = w 1 := by simpa [h_i] using hi
    rw [h0, h1]
  · rfl

-- @node: def:sparse-witness
/-- The explicit reflected sparse witness on `0 → 1` plus an isolated node. -/
def sparseWitness (s : SignVector 3) : Mechanism 3 threeNodeDAG where
  p := sparseP s -- @realizes \(\theta^{\mathrm{sp}}\)(p_2 = 1 + 0.1 h(x)h(y); others 1)
  q := sparseQ s -- @realizes \(\theta^{\mathrm{sp}}\)(q_i normalized exponential tilt)
  parent_local := sparseP_parent_local s

/-- Cancellation witness observational conditional mechanism. -/
def cancellationP (s : SignVector 3) (i : Fin 3) (v : LatentState 3) : ℝ :=
  if i = 1 then
    1 + (1 / 10 : ℝ) * cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
      centeredCoordinate (reflectedCoordinate s 1 (v 1))
  else 1

lemma cancellationP_parent_local (s : SignVector 3) :
    ∀ i v w, v i = w i →
      (∀ j ∈ threeNodeDAG.parents i, v j = w j) →
        cancellationP s i v = cancellationP s i w := by
  intro i v w hi hp
  simp only [cancellationP]
  split
  · rename_i h_i
    have h0 : v 0 = w 0 := hp 0 (by simp [threeNodeDAG, Causalean.DAG.parents,
      threeNodeEdge, h_i])
    have h1 : v 1 = w 1 := by simpa [h_i] using hi
    rw [h0, h1]
  · rfl

-- @node: def:cancellation-witness
/-- The explicit reflected faithful cancellation mechanism. -/
def cancellationWitness (s : SignVector 3) : Mechanism 3 threeNodeDAG where
  p := cancellationP s -- @realizes \(\theta^{\mathrm{can}}\)(p_2 = 1 + 0.1 H(x)h(y))
  q := sparseQ s -- @realizes \(\theta^{\mathrm{can}}\)(same normalized intervention tilts)
  parent_local := cancellationP_parent_local s

/-- Edge-specific sparse endpoint embedded in an arbitrary DAG. -/
def embeddedSparseP {n : ℕ} (s : SignVector n)
    (j i : Fin n) (l : Fin n) (v : LatentState n) : ℝ :=
  if l = i then
    1 + (1 / 10 : ℝ) * centeredCoordinate (reflectedCoordinate s j (v j)) *
      centeredCoordinate (reflectedCoordinate s i (v i))
  else 1

lemma embeddedSparseP_parent_local {n : ℕ} {G : Causalean.DAG (Fin n)}
    (s : SignVector n) {j i : Fin n} (hji : G.edge j i) :
    ∀ l v w, v l = w l → (∀ k ∈ G.parents l, v k = w k) →
      embeddedSparseP s j i l v = embeddedSparseP s j i l w := by
  intro l v w hl hp
  simp only [embeddedSparseP]
  split
  · rename_i hli
    have hj : v j = w j := hp j (by simpa [Causalean.DAG.parents, hli] using hji)
    have hi : v i = w i := by simpa [hli] using hl
    rw [hj, hi]
  · rfl

/-- The edge-specific sparse endpoint used by the affine perturbation. -/
def embeddedSparseWitness {n : ℕ} {G : Causalean.DAG (Fin n)}
    (s : SignVector n) {j i : Fin n} (hji : G.edge j i) : Mechanism n G where
  p := embeddedSparseP s j i
  q := fun l z => exponentialInterventionDensity (reflectedCoordinate s l z)
  parent_local := embeddedSparseP_parent_local s hji

lemma affinePath_parent_local {n : ℕ} {G : Causalean.DAG (Fin n)}
    (θ endpoint : Mechanism n G) (t : ℝ) :
    ∀ i v w, v i = w i → (∀ j ∈ G.parents i, v j = w j) →
      ((1 - t) * θ.p i v + t * endpoint.p i v) =
        ((1 - t) * θ.p i w + t * endpoint.p i w) := by
  intro i v w hi hp
  rw [θ.parent_local i v w hi hp, endpoint.parent_local i v w hi hp]

/-! The unrestricted extension is used only to state analyticity on a neighborhood of the
closed unit interval. The paper's mechanism path itself is the restricted wrapper below. -/
def affinePathExtension {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) (t : ℝ) : Mechanism n G where
  p := fun l v => (1 - t) * θ.1.p l v + t * (embeddedSparseWitness s hji).p l v
  q := fun l z => (1 - t) * θ.1.q l z + t * (embeddedSparseWitness s hji).q l z
  parent_local := affinePath_parent_local θ.1 (embeddedSparseWitness s hji) t

-- @node: def:affine-path
/-- Nodewise normalized affine interpolation, indexed exactly by `t ∈ [0,1]`. -/
def affinePath {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    (t : Set.Icc (0 : ℝ) 1) : Mechanism n G :=
  affinePathExtension s θ hji t.1
  -- @realizes \(\theta^t\)(p_l^t and q_l^t are affine; t is indexed by [0,1])

lemma exponentialInterventionDensity_integral :
    ∫ z in Set.Icc (0 : ℝ) 1, exponentialInterventionDensity z = 1 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  unfold exponentialInterventionDensity
  have hfun : (fun z : ℝ => 4 * Real.exp (4 * z) / (Real.exp 4 - 1)) =
      fun z => (Real.exp 4 - 1)⁻¹ * (4 * Real.exp (4 * z)) := by
    funext z
    field_simp
  rw [hfun, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left Real.exp (by norm_num : (4 : ℝ) ≠ 0)]
  rw [integral_exp]
  have hden : Real.exp 4 - 1 ≠ 0 := by
    have h : 1 < Real.exp 4 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  simp only [mul_zero, mul_one, Real.exp_zero, inv_eq_one_div, smul_eq_mul]
  field_simp

lemma centeredCoordinate_integral :
    ∫ z in Set.Icc (0 : ℝ) 1, centeredCoordinate z = 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  unfold centeredCoordinate
  rw [intervalIntegral.integral_sub
      (intervalIntegral.intervalIntegrable_id.const_mul 2)
      intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id, integral_one]
  norm_num

-- @node: integral_reflectedCoordinate
/-- Reflection about the midpoint preserves integrals over the unit interval. -/
lemma integral_reflectedCoordinate {n : ℕ} (s : SignVector n) (i : Fin n)
    (f : ℝ → ℝ) :
    ∫ z in Set.Icc (0 : ℝ) 1, f (reflectedCoordinate s i z) =
      ∫ z in Set.Icc (0 : ℝ) 1, f z := by
  rcases s.signed i with hi | hi
  · have hne : (-1 : ℝ) ≠ 1 := by norm_num
    simp only [reflectedCoordinate, reflect, hi, if_neg hne]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simpa using intervalIntegral.integral_comp_sub_left f (1 : ℝ)
  · simp [reflectedCoordinate, reflect, hi]

-- @node: sparseQ_normalized
/-- Every reflected exponential intervention density is normalized. -/
lemma sparseQ_normalized (s : SignVector 3) (i : Fin 3) :
    ∫ z in Set.Icc (0 : ℝ) 1, sparseQ s i z = 1 := by
  unfold sparseQ
  rw [integral_reflectedCoordinate]
  exact exponentialInterventionDensity_integral

-- @node: centeredCoordinate_reflected_integral
/-- Every reflected centered coordinate has zero integral. -/
lemma centeredCoordinate_reflected_integral (s : SignVector 3) (i : Fin 3) :
    ∫ z in Set.Icc (0 : ℝ) 1,
      centeredCoordinate (reflectedCoordinate s i z) = 0 := by
  rw [integral_reflectedCoordinate]
  exact centeredCoordinate_integral

-- @node: sparseP_normalized
/-- Every sparse observational conditional is normalized in its own coordinate. -/
lemma sparseP_normalized (s : SignVector 3) (i : Fin 3) (v : LatentState 3) :
    ∫ z in Set.Icc (0 : ℝ) 1, sparseP s i (Function.update v i z) = 1 := by
  by_cases hi : i = 1
  · subst i
    simp only [sparseP, if_true, Function.update_self]
    simp only [Function.update, dif_neg (by decide : ¬(0 : Fin 3) = 1)]
    rw [integral_add]
    · simp only [integral_const, Measure.restrict_apply_univ,
        Measure.real, measureReal_def, Real.volume_Icc, sub_zero, ENNReal.toReal_one,
        one_smul]
      rw [show (∫ a in Set.Icc (0 : ℝ) 1,
          (1 / 10 * centeredCoordinate (reflectedCoordinate s 0 (v 0))) *
            centeredCoordinate (reflectedCoordinate s 1 a)) =
          (1 / 10 * centeredCoordinate (reflectedCoordinate s 0 (v 0))) *
            ∫ a in Set.Icc (0 : ℝ) 1,
              centeredCoordinate (reflectedCoordinate s 1 a) by
          rw [integral_const_mul]]
      rw [centeredCoordinate_reflected_integral]
      ring
      norm_num
    · exact integrableOn_const (ne_of_lt measure_Icc_lt_top)
    · have hc : Continuous (fun z : ℝ =>
          1 / 10 * centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (reflectedCoordinate s 1 z)) := by
          rcases s.signed 1 with hs | hs
          · simp only [centeredCoordinate, reflectedCoordinate, reflect, hs,
              if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
            fun_prop
          · simp only [centeredCoordinate, reflectedCoordinate, reflect, hs]
            simp only [if_true]
            fun_prop
      exact hc.integrableOn_Icc
  · simp [sparseP, hi]

-- @node: cancellationP_normalized
/-- Every cancellation observational conditional is normalized in its own coordinate. -/
lemma cancellationP_normalized (s : SignVector 3) (i : Fin 3) (v : LatentState 3) :
    ∫ z in Set.Icc (0 : ℝ) 1, cancellationP s i (Function.update v i z) = 1 := by
  by_cases hi : i = 1
  · subst i
    simp only [cancellationP, if_true, Function.update_self]
    simp only [Function.update, dif_neg (by decide : ¬(0 : Fin 3) = 1)]
    rw [integral_add]
    · simp only [integral_const, Measure.restrict_apply_univ,
        Measure.real, measureReal_def, Real.volume_Icc, sub_zero, ENNReal.toReal_one,
        one_smul]
      rw [show (∫ a in Set.Icc (0 : ℝ) 1,
          (1 / 10 * cancellationPrimitive (reflectedCoordinate s 0 (v 0))) *
            centeredCoordinate (reflectedCoordinate s 1 a)) =
          (1 / 10 * cancellationPrimitive (reflectedCoordinate s 0 (v 0))) *
            ∫ a in Set.Icc (0 : ℝ) 1,
              centeredCoordinate (reflectedCoordinate s 1 a) by
          rw [integral_const_mul]]
      rw [centeredCoordinate_reflected_integral]
      ring
      norm_num
    · exact integrableOn_const (ne_of_lt measure_Icc_lt_top)
    · have hc : Continuous (fun z : ℝ =>
          1 / 10 * cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (reflectedCoordinate s 1 z)) := by
          rcases s.signed 1 with hs | hs
          · simp only [centeredCoordinate, reflectedCoordinate, reflect, hs,
              if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
            fun_prop
          · simp only [centeredCoordinate, reflectedCoordinate, reflect, hs]
            simp only [if_true]
            fun_prop
      exact hc.integrableOn_Icc
  · simp [cancellationP, hi]

lemma cancellationPrimitive_zero :
    cancellationPrimitive 0 = 0 ∧ cancellationPrimitive 1 = 0 := by
  constructor
  · simp [cancellationPrimitive]
  · unfold cancellationPrimitive
    have h : Real.exp 4 - 1 ≠ 0 := by
      have : 1 < Real.exp 4 := Real.one_lt_exp_iff.mpr (by norm_num)
      linarith
    field_simp
    norm_num

lemma cancellationPrimitive_deriv (x : ℝ) :
    deriv cancellationPrimitive x = exponentialInterventionDensity x - 1 := by
  change deriv (fun y : ℝ => (Real.exp (4 * y) - 1) / (Real.exp 4 - 1) - y) x =
    exponentialInterventionDensity x - 1
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (4 * y))
      (4 * Real.exp (4 * x)) x := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (4 * x)).comp x (hasDerivAt_const_mul (x := x) 4)
  have hF : HasDerivAt
      (fun y : ℝ => (Real.exp (4 * y) - 1) / (Real.exp 4 - 1))
      (exponentialInterventionDensity x) x := by
    simpa [exponentialInterventionDensity] using
      (hexp.sub_const 1).div_const (Real.exp 4 - 1)
  exact (hF.sub (hasDerivAt_id x)).deriv

-- @node: cancellationPrimitive_nonconstant
/-- The cancellation primitive genuinely varies, as witnessed by its nonzero derivative at zero. -/
lemma cancellationPrimitive_nonconstant :
    ∃ x, cancellationPrimitive x ≠ cancellationPrimitive 0 := by
  by_contra hconst
  push Not at hconst
  have hd0 : deriv cancellationPrimitive 0 = 0 := by
    rw [show cancellationPrimitive = fun _ => cancellationPrimitive 0 by
      funext x
      exact hconst x]
    simp
  rw [cancellationPrimitive_deriv] at hd0
  have hexp : 5 < Real.exp 4 := by
    nlinarith [Real.add_one_lt_exp (by norm_num : (4 : ℝ) ≠ 0)]
  have hden : 0 < Real.exp 4 - 1 := by linarith
  have hq0 : exponentialInterventionDensity 0 < 1 := by
    simp only [exponentialInterventionDensity, mul_zero, Real.exp_zero]
    apply (div_lt_one hden).2
    linarith
  linarith

-- @node: cancellationPrimitive_mem_unitInterval_sub
/-- On the unit interval the cancellation primitive lies between minus one and one. -/
lemma cancellationPrimitive_mem_unitInterval_sub {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    cancellationPrimitive x ∈ Set.Icc (-1 : ℝ) 1 := by
  have hden : 0 < Real.exp 4 - 1 := by
    have h := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 4)
    linarith
  have hexp0 : 1 ≤ Real.exp (4 * x) := by
    simpa using Real.one_le_exp (by nlinarith [hx.1] : 0 ≤ 4 * x)
  have hexp4 : Real.exp (4 * x) ≤ Real.exp 4 := by
    apply Real.exp_le_exp.mpr
    nlinarith [hx.2]
  have hfrac0 : 0 ≤ (Real.exp (4 * x) - 1) / (Real.exp 4 - 1) := div_nonneg (by linarith) hden.le
  have hfrac1 : (Real.exp (4 * x) - 1) / (Real.exp 4 - 1) ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  unfold cancellationPrimitive
  constructor <;> linarith [hx.1, hx.2]

/-- A prescribed coordinate reflection preserves the closed unit interval. -/
-- @node: reflectedCoordinate_mem_unitInterval
lemma reflectedCoordinate_mem_unitInterval {n : ℕ} (s : SignVector n) (i : Fin n)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    reflectedCoordinate s i z ∈ Set.Icc (0 : ℝ) 1 := by
  rcases s.signed i with hi | hi
  · simp only [reflectedCoordinate, reflect, hi, if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
    constructor <;> linarith [hz.1, hz.2]
  · rw [reflectedCoordinate, reflect, hi, if_pos rfl]
    exact hz

/-- The centered coordinate has absolute value at most one on the unit interval. -/
-- @node: abs_centeredCoordinate_le_one
lemma abs_centeredCoordinate_le_one {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    |centeredCoordinate z| ≤ 1 := by
  rw [abs_le]
  constructor <;> simp only [centeredCoordinate] <;> linarith [hz.1, hz.2]

/-- The normalized exponential intervention density is strictly positive. -/
-- @node: exponentialInterventionDensity_pos
lemma exponentialInterventionDensity_pos (z : ℝ) :
    0 < exponentialInterventionDensity z := by
  unfold exponentialInterventionDensity
  have hden : 0 < Real.exp 4 - 1 := by
    have := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 4)
    linarith
  positivity

/-- Every sparse observational mechanism is strictly positive on the latent cube. -/
-- @node: sparseP_pos
lemma sparseP_pos (s : SignVector 3) (i : Fin 3) (v : LatentState 3)
    (hv : v ∈ latentCube 3) : 0 < sparseP s i v := by
  by_cases hi : i = 1
  · subst i
    have hv0 : v 0 ∈ Set.Icc (0 : ℝ) 1 := hv 0 (Set.mem_univ 0)
    have hv1 : v 1 ∈ Set.Icc (0 : ℝ) 1 := hv 1 (Set.mem_univ 1)
    have h0 := abs_centeredCoordinate_le_one
      (reflectedCoordinate_mem_unitInterval s 0 hv0)
    have h1 := abs_centeredCoordinate_le_one
      (reflectedCoordinate_mem_unitInterval s 1 hv1)
    have hprod : -1 ≤ centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
        centeredCoordinate (reflectedCoordinate s 1 (v 1)) := by
      rw [abs_le] at h0 h1
      nlinarith
    simp only [sparseP, if_true]
    nlinarith
  · simp [sparseP, hi]

/-- The sparse witness is positive, normalized, and `C³` on every mechanism domain. -/
-- @node: sparseWitness_positive_normalized_smooth
lemma sparseWitness_positive_normalized_smooth (s : SignVector 3) :
    PositiveNormalizedSmoothMechanisms threeNodeDAG (sparseWitness s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i v hv
    exact sparseP_pos s i v hv
  · intro i z hz
    exact exponentialInterventionDensity_pos _
  · intro i
    by_cases hi : i = 1
    · subst i
      change ContDiffOn ℝ 3 (fun v : LatentState 3 =>
        1 + (1 / 10 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
          centeredCoordinate (reflectedCoordinate s 1 (v 1))) (latentCube 3)
      rcases s.signed 0 with h0 | h0 <;> rcases s.signed 1 with h1 | h1 <;>
        simp [reflectedCoordinate, reflect, h0, h1, centeredCoordinate,
          show (-1 : ℝ) ≠ 1 by norm_num] <;> fun_prop
    · change ContDiffOn ℝ 3 (sparseP s i) (latentCube 3)
      rw [show sparseP s i = fun _ => (1 : ℝ) by
        funext v
        simp [sparseP, hi]]
      fun_prop
  · intro i
    change ContDiffOn ℝ 3 (fun z : ℝ =>
      exponentialInterventionDensity (reflectedCoordinate s i z)) (Set.Icc 0 1)
    unfold exponentialInterventionDensity
    rcases s.signed i with hi | hi
    · simp [reflectedCoordinate, reflect, hi, show (-1 : ℝ) ≠ 1 by norm_num]
      fun_prop
    · simp [reflectedCoordinate, reflect, hi]
      fun_prop
  · intro i v hv
    exact sparseP_normalized s i v
  · intro i
    exact sparseQ_normalized s i

-- @node: cancellationP_pos
/-- Every cancellation observational mechanism is strictly positive on the latent cube. -/
lemma cancellationP_pos (s : SignVector 3) (i : Fin 3) (v : LatentState 3)
    (hv : v ∈ latentCube 3) : 0 < cancellationP s i v := by
  by_cases hi : i = 1
  · subst i
    have hv0 : v 0 ∈ Set.Icc (0 : ℝ) 1 := hv 0 (Set.mem_univ 0)
    have hv1 : v 1 ∈ Set.Icc (0 : ℝ) 1 := hv 1 (Set.mem_univ 1)
    have h0 := cancellationPrimitive_mem_unitInterval_sub
      (reflectedCoordinate_mem_unitInterval s 0 hv0)
    have h1 := abs_centeredCoordinate_le_one
      (reflectedCoordinate_mem_unitInterval s 1 hv1)
    rw [abs_le] at h1
    simp only [cancellationP, if_true]
    nlinarith [h0.1, h0.2]
  · simp [cancellationP, hi]

-- @node: cancellationWitness_positive_normalized_smooth
/-- The cancellation witness is positive, normalized, and `C³` on every mechanism domain. -/
lemma cancellationWitness_positive_normalized_smooth (s : SignVector 3) :
    PositiveNormalizedSmoothMechanisms threeNodeDAG (cancellationWitness s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i v hv
    exact cancellationP_pos s i v hv
  · intro i z hz
    exact exponentialInterventionDensity_pos _
  · intro i
    by_cases hi : i = 1
    · subst i
      change ContDiffOn ℝ 3 (fun v : LatentState 3 =>
        1 + (1 / 10 : ℝ) * cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
          centeredCoordinate (reflectedCoordinate s 1 (v 1))) (latentCube 3)
      rcases s.signed 0 with h0 | h0 <;> rcases s.signed 1 with h1 | h1 <;>
        simp [cancellationPrimitive, reflectedCoordinate, reflect, h0, h1, centeredCoordinate,
          show (-1 : ℝ) ≠ 1 by norm_num] <;> fun_prop
    · change ContDiffOn ℝ 3 (cancellationP s i) (latentCube 3)
      rw [show cancellationP s i = fun _ => (1 : ℝ) by
        funext v
        simp [cancellationP, hi]]
      fun_prop
  · intro i
    change ContDiffOn ℝ 3 (fun z : ℝ =>
      exponentialInterventionDensity (reflectedCoordinate s i z)) (Set.Icc 0 1)
    unfold exponentialInterventionDensity
    rcases s.signed i with hi | hi
    · simp [reflectedCoordinate, reflect, hi, show (-1 : ℝ) ≠ 1 by norm_num]
      fun_prop
    · simp [reflectedCoordinate, reflect, hi]
      fun_prop
  · intro i v hv
    exact cancellationP_normalized s i v
  · intro i
    exact sparseQ_normalized s i

-- @node: sparseWitness_contDiff_all
/-- Every sparse-witness mechanism component is smooth to every finite order. -/
lemma sparseWitness_contDiff_all (s : SignVector 3) :
    (∀ k i, ContDiffOn ℝ k ((sparseWitness s).p i) (latentCube 3)) ∧
    ∀ k i, ContDiffOn ℝ k ((sparseWitness s).q i) (Set.Icc (0 : ℝ) 1) := by
  constructor
  · intro k i
    by_cases hi : i = 1
    · subst i
      change ContDiffOn ℝ k (fun v : LatentState 3 =>
        1 + (1 / 10 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
          centeredCoordinate (reflectedCoordinate s 1 (v 1))) (latentCube 3)
      rcases s.signed 0 with h0 | h0 <;> rcases s.signed 1 with h1 | h1 <;>
        simp [reflectedCoordinate, reflect, h0, h1, centeredCoordinate,
          show (-1 : ℝ) ≠ 1 by norm_num] <;> fun_prop
    · change ContDiffOn ℝ k (sparseP s i) (latentCube 3)
      rw [show sparseP s i = fun _ => (1 : ℝ) by
        funext v
        simp [sparseP, hi]]
      fun_prop
  · intro k i
    change ContDiffOn ℝ k (fun z : ℝ =>
      exponentialInterventionDensity (reflectedCoordinate s i z)) (Set.Icc 0 1)
    unfold exponentialInterventionDensity
    rcases s.signed i with hi | hi
    · simp [reflectedCoordinate, reflect, hi, show (-1 : ℝ) ≠ 1 by norm_num]
      fun_prop
    · simp [reflectedCoordinate, reflect, hi]
      fun_prop

-- @node: cancellationWitness_contDiff_all
/-- Every cancellation-witness mechanism component is smooth to every finite order. -/
lemma cancellationWitness_contDiff_all (s : SignVector 3) :
    (∀ k i, ContDiffOn ℝ k ((cancellationWitness s).p i) (latentCube 3)) ∧
    ∀ k i, ContDiffOn ℝ k ((cancellationWitness s).q i) (Set.Icc (0 : ℝ) 1) := by
  constructor
  · intro k i
    by_cases hi : i = 1
    · subst i
      change ContDiffOn ℝ k (fun v : LatentState 3 =>
        1 + (1 / 10 : ℝ) * cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
          centeredCoordinate (reflectedCoordinate s 1 (v 1))) (latentCube 3)
      rcases s.signed 0 with h0 | h0 <;> rcases s.signed 1 with h1 | h1 <;>
        simp [cancellationPrimitive, reflectedCoordinate, reflect, h0, h1, centeredCoordinate,
          show (-1 : ℝ) ≠ 1 by norm_num] <;> fun_prop
    · change ContDiffOn ℝ k (cancellationP s i) (latentCube 3)
      rw [show cancellationP s i = fun _ => (1 : ℝ) by
        funext v
        simp [cancellationP, hi]]
      fun_prop
  · intro k i
    change ContDiffOn ℝ k (fun z : ℝ =>
      exponentialInterventionDensity (reflectedCoordinate s i z)) (Set.Icc 0 1)
    unfold exponentialInterventionDensity
    rcases s.signed i with hi | hi
    · simp [reflectedCoordinate, reflect, hi, show (-1 : ℝ) ≠ 1 by norm_num]
      fun_prop
    · simp [reflectedCoordinate, reflect, hi]
      fun_prop

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

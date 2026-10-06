module
public import Causalean.Mathlib.Analysis.RealInterpolation.Basic

/-!
# Embedded endpoint norms and decomposition infima

These order-theoretic lemmas identify the extended ambient norm and translate
ambient decompositions to endpoint decompositions. Positivity of the scale is
essential when eliminating an infinite endpoint cost. The final lemma is the
rescaled K-functional estimate, before integrating in the scale.
-/

public section
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace Causalean.Mathlib.Analysis.RealInterpolation

/-- An [injective embedding](hyp:i,hi) gives [the original endpoint norm](goal)
at [an embedded vector](hyp:e). -/
theorem embeddedNorm_apply {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (i : E →L[ℝ] V)
    (hi : Function.Injective i) (e : E) :
    embeddedNorm i (i e) = ENNReal.ofReal ‖e‖ := by
  unfold embeddedNorm
  apply le_antisymm
  · exact iInf_le_of_le e (iInf_le_of_le rfl le_rfl)
  · refine le_iInf fun e' => le_iInf fun h => ?_
    rw [hi h]

/-- [A vector outside the range](hyp:v,hv) of [an embedding](hyp:i) has
[infinite extended endpoint norm](goal). -/
theorem embeddedNorm_eq_top {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (i : E →L[ℝ] V)
    (v : V) (hv : v ∉ Set.range i) : embeddedNorm i v = ⊤ := by
  unfold embeddedNorm
  refine iInf_eq_top.mpr fun e => iInf_eq_top.mpr fun h => ?_
  exact (hv ⟨e, h⟩).elim

/-- [An injective embedding](hyp:i,hi) gives [a finite extended norm exactly on
its range](goal), at [any ambient vector](hyp:v). -/
theorem embeddedNorm_lt_top_iff {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (i : E →L[ℝ] V)
    (hi : Function.Injective i) (v : V) :
    embeddedNorm i v < ⊤ ↔ ∃ e, i e = v := by
  constructor
  · intro h
    by_contra hn
    have hv : v ∉ Set.range i := hn
    rw [embeddedNorm_eq_top i v hv] at h
    exact (lt_irrefl _ h)
  · rintro ⟨e, rfl⟩
    rw [embeddedNorm_apply i hi e]
    exact ENNReal.ofReal_lt_top

/-- [Injective endpoint embeddings](hyp:i0,i1,hi0,hi1) identify [the ambient
quadratic K-functional with the endpoint decomposition infimum](goal), at
[a positive scale](hyp:t,ht) and [an ambient vector](hyp:v).

Prove both inequalities by indexing each infimum. Outside endpoint ranges the
ambient cost is infinity; positive scale prevents zero times infinity on endpoint 1. -/
theorem kFunctionalSq_embedded {E0 E1 V : Type*}
    [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i0 : E0 →L[ℝ] V) (i1 : E1 →L[ℝ] V)
    (hi0 : Function.Injective i0) (hi1 : Function.Injective i1)
    (t : ℝ) (ht : 0 < t) (v : V) :
    kFunctionalSq (embeddedNorm i0) (embeddedNorm i1) t v =
      ⨅ (e0 : E0) (e1 : E1) (_ : v = i0 e0 + i1 e1),
        ENNReal.ofReal ‖e0‖ ^ 2 + ENNReal.ofReal (t ^ 2) * ENNReal.ofReal ‖e1‖ ^ 2 := by
  classical
  unfold kFunctionalSq
  apply le_antisymm
  · refine le_iInf fun e0 => le_iInf fun e1 => le_iInf fun h => ?_
    refine (iInf_le_of_le (i0 e0) (iInf_le_of_le (i1 e1)
      (iInf_le_of_le h le_rfl))).trans ?_
    rw [embeddedNorm_apply i0 hi0, embeddedNorm_apply i1 hi1]
  · refine le_iInf fun v0 => le_iInf fun v1 => le_iInf fun h => ?_
    by_cases h0 : v0 ∈ Set.range i0
    · obtain ⟨e0, rfl⟩ := h0
      by_cases h1 : v1 ∈ Set.range i1
      · obtain ⟨e1, rfl⟩ := h1
        rw [embeddedNorm_apply i0 hi0, embeddedNorm_apply i1 hi1]
        exact iInf_le_of_le e0 (iInf_le_of_le e1 (iInf_le_of_le h le_rfl))
      · rw [embeddedNorm_eq_top i1 v1 h1]
        have ht' : ENNReal.ofReal (t ^ 2) ≠ 0 :=
          ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos ht))
        simp [ENNReal.mul_top, ht']
    · rw [embeddedNorm_eq_top i0 v0 h0]
      simp

/-- [An additive operator](hyp:D) with [positive finite endpoint bounds](hyp:A0,A1,hA0,hA1,h0,h1)
satisfies [the rescaled squared K-functional estimate](goal), for
[endpoint gauges](hyp:n0,n1,m0,m1), [a positive scale](hyp:t,ht), and [a vector](hyp:v).

Map each admissible decomposition using additivity, square the endpoint bounds,
and factor out A0² through the infimum. No completeness or attainment is needed. -/
theorem kFunctionalSq_map_le {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (n0 n1 : V → ℝ≥0∞) (m0 m1 : W → ℝ≥0∞) (D : V →+ W)
    (A0 A1 : ℝ≥0∞) (hA0 : 0 < A0 ∧ A0 < ⊤) (hA1 : 0 < A1 ∧ A1 < ⊤)
    (h0 : ∀ v, m0 (D v) ≤ A0 * n0 v) (h1 : ∀ v, m1 (D v) ≤ A1 * n1 v)
    (t : ℝ) (ht : 0 < t) (v : V) :
    kFunctionalSq m0 m1 t (D v) ≤
      A0 ^ 2 * kFunctionalSq n0 n1 (t * (A1.toReal / A0.toReal)) v := by
  have hA0z : A0 ≠ 0 := ne_of_gt hA0.1
  have hA0t : A0 ≠ ⊤ := ne_of_lt hA0.2
  have hA1t : A1 ≠ ⊤ := ne_of_lt hA1.2
  have ha0 : 0 < A0.toReal := ENNReal.toReal_pos_iff.mpr hA0
  have ha1 : 0 < A1.toReal := ENNReal.toReal_pos_iff.mpr hA1
  have hscale : A0 ^ 2 * ENNReal.ofReal ((t * (A1.toReal / A0.toReal)) ^ 2) =
      ENNReal.ofReal (t ^ 2) * A1 ^ 2 := by
    rw [mul_pow, ENNReal.ofReal_mul (le_of_lt (sq_pos_of_pos ht)),
      ENNReal.ofReal_pow (div_nonneg ha1.le ha0.le),
      ENNReal.ofReal_div_of_pos ha0, ENNReal.ofReal_toReal hA1t,
      ENNReal.ofReal_toReal hA0t, div_eq_mul_inv,
      mul_pow, ← ENNReal.inv_pow, ← div_eq_mul_inv]
    calc
      A0 ^ 2 * (ENNReal.ofReal (t ^ 2) * (A1 ^ 2 / A0 ^ 2)) =
          ENNReal.ofReal (t ^ 2) * (A0 ^ 2 * (A1 ^ 2 / A0 ^ 2)) := by ac_rfl
      _ = _ := by
        rw [ENNReal.mul_div_cancel (ENNReal.pow_ne_zero hA0z 2)
          (ENNReal.pow_ne_top hA0t)]
  unfold kFunctionalSq
  rw [ENNReal.mul_iInf_of_ne (ENNReal.pow_ne_zero hA0z 2)
    (ENNReal.pow_ne_top hA0t)]
  refine le_iInf fun v0 => ?_
  rw [ENNReal.mul_iInf_of_ne (ENNReal.pow_ne_zero hA0z 2)
    (ENNReal.pow_ne_top hA0t)]
  refine le_iInf fun v1 => ?_
  rw [ENNReal.mul_iInf_of_ne (ENNReal.pow_ne_zero hA0z 2)
    (ENNReal.pow_ne_top hA0t)]
  refine le_iInf fun h => ?_
  have hD : D v = D v0 + D v1 := by rw [h, map_add]
  refine (iInf_le_of_le (D v0) (iInf_le_of_le (D v1)
    (iInf_le_of_le hD le_rfl))).trans ?_
  calc
    m0 (D v0) ^ 2 + ENNReal.ofReal (t ^ 2) * m1 (D v1) ^ 2 ≤
        (A0 * n0 v0) ^ 2 + ENNReal.ofReal (t ^ 2) * (A1 * n1 v1) ^ 2 :=
      add_le_add (pow_le_pow_left' (h0 v0) 2)
        (mul_le_mul_right (pow_le_pow_left' (h1 v1) 2) _)
    _ = A0 ^ 2 * (n0 v0 ^ 2 +
        ENNReal.ofReal ((t * (A1.toReal / A0.toReal)) ^ 2) * n1 v1 ^ 2) := by
      rw [mul_add, mul_pow, mul_pow, ← mul_assoc,
        ← hscale, mul_assoc]

end Causalean.Mathlib.Analysis.RealInterpolation

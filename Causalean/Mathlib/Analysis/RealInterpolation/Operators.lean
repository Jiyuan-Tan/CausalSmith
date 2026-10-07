module
public import Causalean.Mathlib.Analysis.RealInterpolation.Endpoint
public import Causalean.Mathlib.Analysis.RealInterpolation.ScaleIntegral
public import Causalean.Mathlib.Analysis.RealInterpolation.ScaleMeasurability
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Exact quadratic operator interpolation

Positive endpoint bounds follow by rescaling the K-functional and integrating.
Arbitrary finite nonnegative bounds follow by a limit of positive bounds, using
the finite input interpolation norm. The main theorem retains complete endpoint
spaces and injective continuous embeddings, matching compatible Banach pairs.
No continuity of the ambient linear map beyond the endpoint bounds is required.

Reference: Chandler-Wilde, Hewett, Moiola (2015), Theorem 2.2(i), arXiv:1404.3599v4.
-/

public section
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace Causalean.Mathlib.Analysis.RealInterpolation

/-- [An additive map](hyp:D) with [positive finite endpoint bounds](hyp:A0,A1,hA0,hA1,h0,h1)
has [the exact exponent interpolation bound](goal) for [endpoint gauges](hyp:n0,n1,m0,m1),
[an interior exponent](hyp:θ,hθ), and [any vector](hyp:v).

Integrate kFunctionalSq_map_le and use lintegral_weighted_dilation with
c=A1.toReal/A0.toReal. Convert the resulting A0²*c^(2*θ) to geometric powers. -/
theorem kNormSq_map_le_of_pos {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (n0 n1 : V → ℝ≥0∞) (m0 m1 : W → ℝ≥0∞) (D : V →+ W)
    (A0 A1 : ℝ≥0∞) (hA0 : 0 < A0 ∧ A0 < ⊤) (hA1 : 0 < A1 ∧ A1 < ⊤)
    (h0 : ∀ v, m0 (D v) ≤ A0 * n0 v) (h1 : ∀ v, m1 (D v) ≤ A1 * n1 v)
    (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) 1) (v : V) :
    kNormSq m0 m1 θ (D v) ≤
      (ENNReal.rpow A0 (1 - θ) * ENNReal.rpow A1 θ) ^ 2 * kNormSq n0 n1 θ v := by
  have ha0 : 0 < A0.toReal := ENNReal.toReal_pos_iff.mpr hA0
  have ha1 : 0 < A1.toReal := ENNReal.toReal_pos_iff.mpr hA1
  have hc : 0 < A1.toReal / A0.toReal := div_pos ha1 ha0
  have hcoef : A0 ^ 2 * ENNReal.ofReal ((A1.toReal / A0.toReal) ^ (2 * θ)) =
      (ENNReal.rpow A0 (1 - θ) * ENNReal.rpow A1 θ) ^ 2 := by
    simp only [ENNReal.rpow_eq_pow]
    rw [← ENNReal.ofReal_rpow_of_pos hc, ENNReal.ofReal_div_of_pos ha0,
      ENNReal.ofReal_toReal (ne_of_lt hA1.2),
      ENNReal.ofReal_toReal (ne_of_lt hA0.2),
      ENNReal.div_rpow_of_nonneg A1 A0 (by linarith [hθ.1])]
    calc
      A0 ^ 2 * (A1 ^ (2 * θ) / A0 ^ (2 * θ)) =
          (A0 ^ 2 / A0 ^ (2 * θ)) * A1 ^ (2 * θ) := by
        simp only [div_eq_mul_inv]
        ac_rfl
      _ = A0 ^ (2 - 2 * θ) * A1 ^ (2 * θ) := by
        rw [← ENNReal.rpow_two, ← ENNReal.rpow_sub 2 (2 * θ)
          (ne_of_gt hA0.1) (ne_of_lt hA0.2)]
      _ = _ := by
        rw [mul_pow, ← ENNReal.rpow_two (A0 ^ (1 - θ)),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_two (A1 ^ θ), ← ENNReal.rpow_mul]
        congr 1 <;> congr 1 <;> ring
  unfold kNormSq
  calc
    _ ≤ normalizationSq θ * ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (-1 - 2 * θ)) *
          (A0 ^ 2 * kFunctionalSq n0 n1 (t * (A1.toReal / A0.toReal)) v) := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      exact mul_le_mul' le_rfl (kFunctionalSq_map_le n0 n1 m0 m1 D A0 A1
        hA0 hA1 h0 h1 t ht v)
    _ = normalizationSq θ * (A0 ^ 2 *
        (ENNReal.ofReal ((A1.toReal / A0.toReal) ^ (2 * θ)) *
          ∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (-1 - 2 * θ)) * kFunctionalSq n0 n1 t v)) := by
      simp_rw [mul_left_comm (ENNReal.ofReal _) (A0 ^ 2)]
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ne_of_lt hA0.2)),
        lintegral_weighted_dilation _ (measurable_kFunctionalSq_indicator n0 n1 v)
          _ hc θ]
    _ = _ := by rw [← hcoef]; ac_rfl

/-- [An endpoint estimate on embedded vectors](hyp:h)
extends to [the whole ambient space](goal) for [an injective embedding](hyp:i,hi),
[a positive bound](hyp:A,hA), and [an ambient map and target gauge](hyp:D,m).
Outside the source endpoint the right side is infinity because A is positive. -/
theorem embeddedNorm_endpoint_bound_of_pos {E V W : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : E →L[ℝ] V) (hi : Function.Injective i) (D : V → W) (m : W → ℝ≥0∞)
    (A : ℝ≥0∞) (hA : 0 < A)
    (h : ∀ e, m (D (i e)) ≤ A * ENNReal.ofReal ‖e‖) :
    ∀ v, m (D v) ≤ A * embeddedNorm i v := by
  intro v
  by_cases hv : v ∈ Set.range i
  · obtain ⟨e, rfl⟩ := hv
    simpa only [embeddedNorm_apply i hi] using h e
  · rw [embeddedNorm_eq_top i v hv]
    simp [ENNReal.mul_top, ne_of_gt hA]

/-- [Bounds for every strictly larger positive finite endpoint constant](hyp:h)
imply [the bound at the original finite nonnegative constants](goal), for
[a finite input energy](hyp:K,hK), [a target energy](hyp:L),
[finite endpoint constants](hyp:A0,A1,hA0,hA1), and [an interior exponent](hyp:θ,hθ).

Take B0=A0+ofReal ε and B1=A1+ofReal ε as ε tends to zero from above. Continuity
of positive ENNReal powers at zero is needed. Finiteness of K prevents a discontinuous
zero-times-infinity limit; do not remove it or impose positivity of A0 or A1. -/
theorem le_geometric_of_forall_gt (L K A0 A1 : ℝ≥0∞)
    (hK : K < ⊤) (hA0 : A0 < ⊤) (hA1 : A1 < ⊤)
    (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (h : ∀ B0 B1 : ℝ≥0∞, A0 < B0 → B0 < ⊤ → A1 < B1 → B1 < ⊤ →
      L ≤ (ENNReal.rpow B0 (1 - θ) * ENNReal.rpow B1 θ) ^ 2 * K) :
    L ≤ (ENNReal.rpow A0 (1 - θ) * ENNReal.rpow A1 θ) ^ 2 * K := by
  have hB (A : ℝ≥0∞) :
      Tendsto (fun ε : ℝ => A + ENNReal.ofReal ε) (𝓝[>] (0 : ℝ)) (𝓝 A) := by
    have ht : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := A)).add (ENNReal.tendsto_ofReal ht)
  have hp0 := (ENNReal.continuous_rpow_const (y := 1 - θ)).tendsto A0 |>.comp (hB A0)
  have hp1 := (ENNReal.continuous_rpow_const (y := θ)).tendsto A1 |>.comp (hB A1)
  have hp : Filter.Tendsto (fun ε : ℝ =>
      ((A0 + ENNReal.ofReal ε) ^ (1 - θ) * (A1 + ENNReal.ofReal ε) ^ θ) ^ 2 * K)
      (𝓝[>] (0 : ℝ)) (𝓝 ((A0 ^ (1 - θ) * A1 ^ θ) ^ 2 * K)) :=
    ENNReal.Tendsto.mul_const
      ((ENNReal.continuous_pow 2).tendsto _ |>.comp
        (ENNReal.Tendsto.mul hp0
          (Or.inr (ENNReal.rpow_ne_top_of_nonneg hθ.1.le (ne_of_lt hA1))) hp1
          (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by linarith [hθ.2])
            (ne_of_lt hA0))))) (Or.inr (ne_of_lt hK))
  simp only [ENNReal.rpow_eq_pow] at h ⊢
  apply ge_of_tendsto hp
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact h _ _
    (ENNReal.lt_add_right (ne_of_lt hA0) (ne_of_gt (ENNReal.ofReal_pos.mpr hε)))
    (ENNReal.add_lt_top.mpr ⟨hA0, ENNReal.ofReal_lt_top⟩)
    (ENNReal.lt_add_right (ne_of_lt hA1) (ne_of_gt (ENNReal.ofReal_pos.mpr hε)))
    (ENNReal.add_lt_top.mpr ⟨hA1, ENNReal.ofReal_lt_top⟩)

/-- [A common real linear operator](hyp:D) from
[a compatible embedded Banach source pair](hyp:i0,i1,hi0,hi1) to
[an embedded Banach target pair](hyp:j0,j1), with
[finite nonnegative endpoint bounds](hyp:A0,A1,hA0,hA1,h0,h1),
satisfies [the exact interpolation estimate: the normalized squared interpolation norm of
its image in the target pair is at most (A0^(1−θ)·A1^θ)² times the normalized squared
interpolation norm of the vector in the source pair](goal), for
[an interior exponent](hyp:θ,hθ) and
[a vector with finite interpolation energy](hyp:v,hvfin).

This is the full embedded-pair operator contract, with no interpolation theorem
as a hypothesis. Apply the positive-gauge theorem with slightly larger bounds,
then le_geometric_of_forall_gt. Completeness remains explicit at all four endpoints.
Reference: https://arxiv.org/html/1404.3599v4, Theorem 2.2(i), (8)--(9). -/
theorem exact_interpolation_operators
    (E0 E1 G0 G1 V W : Type*)
    [NormedAddCommGroup E0] [NormedSpace ℝ E0] [CompleteSpace E0]
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [CompleteSpace E1]
    [NormedAddCommGroup G0] [NormedSpace ℝ G0] [CompleteSpace G0]
    [NormedAddCommGroup G1] [NormedSpace ℝ G1] [CompleteSpace G1]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (i0 : E0 →L[ℝ] V) (i1 : E1 →L[ℝ] V)
    (j0 : G0 →L[ℝ] W) (j1 : G1 →L[ℝ] W)
    (hi0 : Function.Injective i0) (hi1 : Function.Injective i1)
    (D : V →ₗ[ℝ] W) (A0 A1 : ℝ≥0∞) (hA0 : A0 < ⊤) (hA1 : A1 < ⊤)
    (h0 : ∀ e, embeddedNorm j0 (D (i0 e)) ≤ A0 * ENNReal.ofReal ‖e‖)
    (h1 : ∀ e, embeddedNorm j1 (D (i1 e)) ≤ A1 * ENNReal.ofReal ‖e‖)
    (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) 1) (v : V)
    (hvfin : kNormSq (embeddedNorm i0) (embeddedNorm i1) θ v < ⊤) :
    kNormSq (embeddedNorm j0) (embeddedNorm j1) θ (D v) ≤
      (ENNReal.rpow A0 (1 - θ) * ENNReal.rpow A1 θ) ^ 2 *
        kNormSq (embeddedNorm i0) (embeddedNorm i1) θ v := by
  apply le_geometric_of_forall_gt _ _ A0 A1 hvfin hA0 hA1 θ hθ
  intro B0 B1 hB0 hB0fin hB1 hB1fin
  have hB0pos : 0 < B0 := lt_of_le_of_lt zero_le hB0
  have hB1pos : 0 < B1 := lt_of_le_of_lt zero_le hB1
  apply kNormSq_map_le_of_pos _ _ _ _ D.toAddMonoidHom B0 B1
    ⟨hB0pos, hB0fin⟩ ⟨hB1pos, hB1fin⟩ _ _ θ hθ v
  · apply embeddedNorm_endpoint_bound_of_pos i0 hi0 D (embeddedNorm j0) B0 hB0pos
    intro e
    exact (h0 e).trans (mul_le_mul' hB0.le le_rfl)
  · apply embeddedNorm_endpoint_bound_of_pos i1 hi1 D (embeddedNorm j1) B1 hB1pos
    intro e
    exact (h1 e).trans (mul_le_mul' hB1.le le_rfl)

end Causalean.Mathlib.Analysis.RealInterpolation

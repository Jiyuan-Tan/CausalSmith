module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.SigningRademacher

/-! # Unit-ball projections for isotropic signing

Norm duality and a countable dense direction class supply the unit-ball
specialization of the cited contraction interface in the row-signing roadmap.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Every real Euclidean vector has a unit-ball direction attaining its norm.](goal) -/
-- @node: euclidean_unit_direction
lemma euclidean_unit_direction {r : ℕ} (v : EuclideanSpace ℝ (Fin r)) :
    ∃ u : EuclideanSpace ℝ (Fin r), ‖u‖ ≤ 1 ∧ inner ℝ u v = ‖v‖ := by
  by_cases hv : v = 0
  · exact ⟨0, by simp, by simp [hv]⟩
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · simp [norm_smul, hn]
  · rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp

/-- [ The signed norm maximum equals the supremum of absolute projections summed
over the rows; this is the deterministic duality step in the roadmap.](goal) -/
-- @node: signingNormMax_eq_unit_projection_sum
lemma signingNormMax_eq_unit_projection_sum {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) :
    signingNormMax vs =
      ⨆ u : {u : EuclideanSpace ℝ (Fin r) // ‖u‖ ≤ 1},
        ∑ i, |inner ℝ u.val (vs i)| := by
  have hb : BddAbove (range (fun u : {u : EuclideanSpace ℝ (Fin r) // ‖u‖ ≤ 1} =>
      ∑ i, |inner ℝ u.val (vs i)|)) := by
    refine ⟨∑ i, ‖vs i‖, ?_⟩
    rintro _ ⟨u, rfl⟩
    apply Finset.sum_le_sum
    intro i _
    exact (abs_real_inner_le_norm _ _).trans (by
      nlinarith [u.property, norm_nonneg (vs i)])
  let : Nonempty {u : EuclideanSpace ℝ (Fin r) // ‖u‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
  apply le_antisymm
  · apply ciSup_le
    intro z
    obtain ⟨u, hu, he⟩ := euclidean_unit_direction (∑ i, sgn (z i) • vs i)
    calc
      ‖∑ i, sgn (z i) • vs i‖ = |inner ℝ u (∑ i, sgn (z i) • vs i)| := by
        rw [he, abs_of_nonneg (norm_nonneg _)]
      _ ≤ ∑ i, |inner ℝ u (vs i)| := by
        rw [← signing_projection_max_eq_sum_abs]
        exact le_ciSup (Finite.bddAbove_range
          (fun z : Signs n => |inner ℝ u (∑ i, sgn (z i) • vs i)|)) z
      _ ≤ _ := le_ciSup hb ⟨u, hu⟩
  · apply ciSup_le
    intro u
    rw [← signing_projection_max_eq_sum_abs]
    apply ciSup_le
    intro z
    exact ((abs_real_inner_le_norm _ _).trans (by
      nlinarith [u.property, norm_nonneg (∑ i, sgn (z i) • vs i)])).trans
        (signing_norm_le_max vs z)

/-- [ A separable Euclidean direction set gives a countable class that simultaneously
approximates every finite evaluation set of its linear projections.](goal) -/
-- @node: euclidean_projection_pointwiseSeparable
lemma euclidean_projection_pointwiseSeparable {r : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin r))) :
    PointwiseSeparable (range (fun u : U => fun v => inner ℝ u.val v)) := by
  classical
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense U
  let f := fun u : U => fun v : EuclideanSpace ℝ (Fin r) => inner ℝ u.val v
  refine ⟨f '' D, hD.image f, image_subset_range _ _, ?_⟩
  rintro g ⟨u, rfl⟩ xs ε hε
  let R : ℝ := 1 + ∑ x ∈ xs, ‖x‖
  have hR : 0 < R := by
    dsimp [R]
    positivity
  obtain ⟨u0, hu0, hdist⟩ := hdense.exists_dist_lt u (div_pos hε hR)
  refine ⟨f u0, mem_image_of_mem f hu0, ?_⟩
  intro x hx
  have hxR : ‖x‖ ≤ R := by
    have hxsum := Finset.single_le_sum (fun y _ => norm_nonneg y) hx
    dsimp [R]
    linarith
  have hd : ‖u0.val - u.val‖ < ε / R := by
    simpa only [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hdist
  calc
    |f u0 x - f u x| = |inner ℝ (u0.val - u.val) x| := by rw [inner_sub_left]
    _ ≤ ‖u0.val - u.val‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u0.val - u.val‖ * R := mul_le_mul_of_nonneg_left hxR (norm_nonneg _)
    _ < (ε / R) * R := mul_lt_mul_of_pos_right hd hR
    _ = ε := div_mul_cancel₀ ε hR.ne'

/-- The unit-ball projection class satisfies factor-two contraction, with no
extra separability assumption on its callers. Under [the stated conditions](hyp:hContraction,hmom,hiso), [the asserted mathematical result follows](goal). -/
-- @node: unit_projection_abs_contraction
lemma unit_projection_abs_contraction (hContraction : ClassicalRademacherContraction)
    (n r : ℕ) (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0) :
    radAverage P n (range (fun u : {u : EuclideanSpace ℝ (Fin r) // ‖u‖ ≤ 1} =>
      fun v => inner ℝ u.val v)) abs ≤ 2 * ENNReal.ofReal (Real.sqrt ((n : ℝ) * r)) := by
  let U := {u : EuclideanSpace ℝ (Fin r) | ‖u‖ ≤ 1}
  let f := fun u : U => fun v => inner ℝ u.val v
  have hnorm : Integrable (fun v : EuclideanSpace ℝ (Fin r) => ‖v‖) P :=
    ((memLp_two_iff_integrable_sq (by fun_prop)).mpr
      (isotropic_norm_sq_integrable r P hmom)).integrable (by norm_num)
  have hgate := hContraction (EuclideanSpace ℝ (Fin r)) P inferInstance n (range f)
    (euclidean_projection_pointwiseSeparable U)
    (by rintro g ⟨u, rfl⟩; fun_prop)
    ⟨fun v => ‖v‖, hnorm, Filter.Eventually.of_forall (by
      rintro v g ⟨u, rfl⟩
      have hu : ‖u.val‖ ≤ 1 := u.property
      exact (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg v]))⟩
    abs (by
      convert (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)) using 1 <;> rfl)
    abs_zero
  have hlinear := projection_radAverage_id_le n r P hmom hiso
    (fun u : U => u.val) (R := 1) (by norm_num) (fun u => u.property)
  simpa only [one_mul, f, U] using! hgate.trans (mul_le_mul_right hlinear 2)

/-- Unit-ball projections recover the length of each Rademacher sum exactly. [The asserted mathematical result follows](goal). -/
-- @node: unit_projection_rademacher_sup_eq_norm
lemma unit_projection_rademacher_sup_eq_norm {n r : ℕ}
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) (z : Signs n) :
    (⨆ g : range (fun u : {u : EuclideanSpace ℝ (Fin r) // ‖u‖ ≤ 1} =>
        fun v => inner ℝ u.val v),
      ENNReal.ofReal |∑ i, sgn (z i) * id (g.val (vs i))|) =
      ENNReal.ofReal ‖∑ i, sgn (z i) • vs i‖ := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨g, u, rfl⟩
    simp only [id_eq, ← real_inner_smul_right, ← inner_sum]
    apply ENNReal.ofReal_le_ofReal
    exact (abs_real_inner_le_norm _ _).trans (by
      nlinarith [u.property, norm_nonneg (∑ i, sgn (z i) • vs i)])
  · obtain ⟨u, hu, he⟩ := euclidean_unit_direction (∑ i, sgn (z i) • vs i)
    let g : range (fun u : {u : EuclideanSpace ℝ (Fin r) // ‖u‖ ≤ 1} =>
        fun v => inner ℝ u.val v) :=
      ⟨fun v => inner ℝ u v, ⟨⟨u, hu⟩, rfl⟩⟩
    have h := le_iSup (fun g : range (fun u :
        {u : EuclideanSpace ℝ (Fin r) // ‖u‖ ≤ 1} => fun v => inner ℝ u.val v) =>
      ENNReal.ofReal |∑ i, sgn (z i) * id (g.val (vs i))|) g
    simpa only [g, id_eq, ← real_inner_smul_right, ← inner_sum, he,
      abs_of_nonneg (norm_nonneg _)] using h

/-- The unit-ball linear Rademacher average is exactly the expected signed norm,
so no slack is introduced by the projection representation. Under [the stated conditions](hyp:hmom), [the asserted mathematical result follows](goal). -/
-- @node: unit_projection_radAverage_id_eq
lemma unit_projection_radAverage_id_eq (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P) :
    radAverage P n (range (fun u : {u : EuclideanSpace ℝ (Fin r) // ‖u‖ ≤ 1} =>
      fun v => inner ℝ u.val v)) id =
      ENNReal.ofReal (∫ vs : Fin n → EuclideanSpace ℝ (Fin r),
        ∫ z : Signs n, ‖∑ i, sgn (z i) • vs i‖ ∂fairSigns n
          ∂Measure.pi (fun _ : Fin n => P)) := by
  let := fairSigns_probability n
  let Q := (Measure.pi (fun _ : Fin n => P)).prod (fairSigns n)
  let f := fun ω : (Fin n → EuclideanSpace ℝ (Fin r)) × Signs n =>
    ‖∑ i, sgn (ω.2 i) • ω.1 i‖
  have hp : MemLp f 2 Q := (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    (isotropic_rademacher_norm_sq_integrable n r P hmom)
  have hf : Integrable f Q := hp.integrable (by norm_num)
  unfold radAverage
  simp_rw [unit_projection_rademacher_sup_eq_norm]
  rw [← lintegral_prod (fun ω : (Fin n → EuclideanSpace ℝ (Fin r)) × Signs n =>
      ENNReal.ofReal (f ω)) (by fun_prop),
    ← ofReal_integral_eq_lintegral_ofReal hf
      (Filter.Eventually.of_forall (fun ω => norm_nonneg _)), integral_prod _ hf]

/-- [ Removing the population mean from each unit projection bounds the signed
norm maximum by the row count plus the largest centered empirical fluctuation.](goal) Under [the stated conditions](hyp:hmom,hiso). -/
-- @node: signingNormMax_le_centered_unit_projection
lemma signingNormMax_le_centered_unit_projection (n r : ℕ)
    (P : Measure (EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure P]
    (hmom : ∀ a, MemLp (fun v => v a) 2 P)
    (hiso : ∀ a b, (∫ v, v a * v b ∂P) = if a = b then 1 else 0)
    (vs : Fin n → EuclideanSpace ℝ (Fin r)) :
    signingNormMax vs ≤ (n : ℝ) +
      ⨆ u : {u : EuclideanSpace ℝ (Fin r) // ‖u‖ ≤ 1},
        |∑ i, (|inner ℝ u.val (vs i)| - ∫ v, |inner ℝ u.val v| ∂P)| := by
  let U := {u : EuclideanSpace ℝ (Fin r) // ‖u‖ ≤ 1}
  let c := fun u : U => ∫ v, |inner ℝ u.val v| ∂P
  have hc (u : U) : 0 ≤ c u ∧ c u ≤ 1 :=
    ⟨integral_nonneg (fun _ => abs_nonneg _),
      (isotropic_projection_abs_integral_le r P hmom hiso u.val).trans u.property⟩
  have hb : BddAbove (range (fun u : U =>
      |∑ i, (|inner ℝ u.val (vs i)| - c u)|)) := by
    refine ⟨(∑ i, ‖vs i‖) + n, ?_⟩
    rintro _ ⟨u, rfl⟩
    calc
      |∑ i, (|inner ℝ u.val (vs i)| - c u)| ≤
          ∑ i, |(|inner ℝ u.val (vs i)|) - c u| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (‖vs i‖ + 1) := by
        apply Finset.sum_le_sum
        intro i _
        have hproj : |inner ℝ u.val (vs i)| ≤ ‖vs i‖ :=
          (abs_real_inner_le_norm _ _).trans (by
            nlinarith [u.property, norm_nonneg (vs i)])
        exact (abs_sub _ _).trans (by
          rw [abs_abs, abs_of_nonneg (hc u).1]
          linarith [(hc u).2])
      _ = _ := by simp [Finset.sum_add_distrib]
  let : Nonempty U := ⟨⟨0, by simp⟩⟩
  rw [signingNormMax_eq_unit_projection_sum]
  apply ciSup_le
  intro u
  have hsup := le_ciSup hb u
  have he : ∑ i, |inner ℝ u.val (vs i)| =
      (∑ i : Fin n, (|inner ℝ u.val (vs i)| - c u)) + (n : ℝ) * c u := by
    simp [Finset.sum_sub_distrib]
  have hmean : (n : ℝ) * c u ≤ n := by
    nlinarith [(hc u).2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  change ∑ i, |inner ℝ u.val (vs i)| ≤ (n : ℝ) +
    ⨆ u : U, |∑ i, (|inner ℝ u.val (vs i)| - c u)|
  rw [he]
  linarith [le_abs_self (∑ i, (|inner ℝ u.val (vs i)| - c u))]

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

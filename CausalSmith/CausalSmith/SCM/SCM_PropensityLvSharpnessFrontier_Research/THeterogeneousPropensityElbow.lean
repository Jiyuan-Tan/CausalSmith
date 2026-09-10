import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TGeneratorIffFrontier
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TOneSidedGeneratorIffFrontier

/-! # Heterogeneous-propensity elbow -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open Set

/-- The adaptive hinge is an admissible member of the frontier at its own
propensity.  For the specified model objects, [the stated conditions](hyp:hPos), [the stated mathematical relationship holds](goal).
-/
-- @node: adaptiveHinge_mem_hingeClassSet
lemma adaptiveHinge_mem_hingeClassSet (e : ℝ) (hPos : StrictPositivity e) :
    adaptiveHinge e ∈ hingeClassSet (1 / e) := by
  have he : e ≠ 0 := ne_of_gt hPos.1
  refine
    { positivity := ?_
      admissible := ?_
      affine_hinge := ⟨0, ?_, ?_⟩ }
  · simpa [he] using hPos
  · refine ⟨?_, ?_, ?_⟩
    · apply Continuous.continuousOn
      unfold adaptiveHinge
      fun_prop
    · constructor
      · exact convex_Ici 0
      · intro x hx y hy a b ha hb hab
        change max (a * x + b * y - 1 / e) 0 ≤
          a * max (x - 1 / e) 0 + b * max (y - 1 / e) 0
        apply max_le
        · calc
            a * x + b * y - 1 / e =
                a * x + b * y - (a + b) * (1 / e) := by rw [hab]; ring
            _ = a * (x - 1 / e) + b * (y - 1 / e) := by ring
            _ ≤ a * max (x - 1 / e) 0 + b * max (y - 1 / e) 0 :=
              add_le_add
                (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
                (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
        · positivity
    · have hc : 1 ≤ 1 / e := one_le_one_div hPos.1 hPos.2.le
      simp only [adaptiveHinge, max_eq_right (sub_nonpos.mpr hc)]
  · intro t ht htc
    have htc' : t ≤ e⁻¹ := by simpa only [one_div] using htc
    simp [adaptiveHinge, one_div, max_eq_right (sub_nonpos.mpr htc')]
  · intro t hct
    have hct' : e⁻¹ < t := by simpa only [one_div] using hct
    simp [adaptiveHinge, one_div, hct']

/-- Frontier classes at distinct positive propensities are disjoint.  For the specified model objects, [the stated conditions](hyp:h1,h2,hne), [the stated mathematical relationship holds](goal).
-/
-- @node: hingeClassSet_disjoint_of_propensity_ne
lemma hingeClassSet_disjoint_of_propensity_ne (e1 e2 : ℝ)
    (h1 : StrictPositivity e1) (h2 : StrictPositivity e2) (hne : e1 ≠ e2) :
    hingeClassSet (1 / e1) ∩ hingeClassSet (1 / e2) = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨f, hf⟩
  rcases hf with ⟨hf1, hf2⟩
  obtain ⟨b1, hb1zero, hb1pos⟩ := hf1.affine_hinge
  obtain ⟨b2, hb2zero, hb2pos⟩ := hf2.affine_hinge
  have hc1 : 0 ≤ 1 / e1 := (one_div_pos.mpr h1.1).le
  have hc2 : 0 ≤ 1 / e2 := (one_div_pos.mpr h2.1).le
  have hz1 := hb1zero 0 (le_refl 0) hc1
  have hz2 := hb2zero 0 (le_refl 0) hc2
  have hb : b1 = b2 := by linarith
  have hcne : 1 / e1 ≠ 1 / e2 := by
    intro hc
    apply hne
    apply inv_injective
    simpa only [one_div] using hc
  rcases lt_or_gt_of_ne hcne with hc12 | hc21
  · have hp := hb1pos (1 / e2) hc12
    have hz := hb2zero (1 / e2) hc2 (le_refl _)
    rw [hb, hz] at hp
    exact (lt_irrefl 0 hp)
  · have hp := hb2pos (1 / e1) hc21
    have hz := hb1zero (1 / e1) hc1 (le_refl _)
    rw [← hb, hz] at hp
    exact (lt_irrefl 0 hp)

/-- No fixed generator is exact at two distinct propensities, while the
propensity-adaptive hinge is exact separately at every stratum.  For the specified model objects, [the stated conditions](hyp:h1,h2,hne), [the stated mathematical relationship holds](goal).
-/
-- @node: thm:heterogeneous-propensity-elbow
theorem heterogeneous_propensity_elbow (e1 e2 : ℝ)
    (h1 : StrictPositivity e1) (h2 : StrictPositivity e2) (hne : e1 ≠ e2) :
    (¬ ∃ f : ℝ → ℝ, AdmissibleGenerator f ∧
      UniversalOneSidedExact f e1 ∧ UniversalOneSidedExact f e2) ∧
    hingeClassSet (1 / e1) ∩ hingeClassSet (1 / e2) = ∅ ∧
    (∀ e : ℝ, StrictPositivity e →
      adaptiveHinge e ∈ hingeClassSet (1 / e) ∧
      UniversalOneSidedExact (adaptiveHinge e) e ∧
      UniversalMutualExact (adaptiveHinge e) e) := by
  have hDisjoint := hingeClassSet_disjoint_of_propensity_ne e1 e2 h1 h2 hne
  refine ⟨?_, hDisjoint, ?_⟩
  · rintro ⟨f, hf, hex1, hex2⟩
    have hmem1 : f ∈ hingeClassSet (1 / e1) :=
      (oneSided_generator_exactness_iff_hinge e1 f h1 hf).2.1
        ((oneSided_generator_exactness_iff_hinge e1 f h1 hf).1.1 hex1)
    have hmem2 : f ∈ hingeClassSet (1 / e2) :=
      (oneSided_generator_exactness_iff_hinge e2 f h2 hf).2.1
        ((oneSided_generator_exactness_iff_hinge e2 f h2 hf).1.1 hex2)
    have : f ∈ (∅ : Set (ℝ → ℝ)) := by
      rw [← hDisjoint]
      exact ⟨hmem1, hmem2⟩
    exact this
  · intro e hPos
    have hmem := adaptiveHinge_mem_hingeClassSet e hPos
    have hf := hmem.admissible
    refine ⟨hmem, ?_, ?_⟩
    · exact (oneSided_generator_exactness_iff_hinge e (adaptiveHinge e) hPos hf).1.2
        ((oneSided_generator_exactness_iff_hinge e (adaptiveHinge e) hPos hf).2.2 hmem)
    · exact (generator_exactness_iff_hinge e (adaptiveHinge e) hPos hf).1.2
        ((generator_exactness_iff_hinge e (adaptiveHinge e) hPos hf).2.2 hmem)
  -- @realizes e_1,e_2(distinct propensities in (0,1))

end CausalSmith.SCM.PropensityLvSharpnessFrontier

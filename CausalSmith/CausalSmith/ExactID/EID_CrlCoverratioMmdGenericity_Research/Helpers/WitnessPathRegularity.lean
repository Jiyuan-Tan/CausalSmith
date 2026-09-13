import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessPath

/-!
# Affine witness-path regularity

This file records the positive, normalized, smooth part of stratum preservation
along the closed affine path.  Causal minimality and the fixed-sign cell are
handled separately by the analytic perturbation argument.
-/

open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: affinePathExtension_positive_normalized_smooth
/-- Convex interpolation with the embedded sparse endpoint preserves positivity,
normalization, and `C³` smoothness throughout the closed unit interval.  Given [the stated inputs and conditions](hyp:hji,ht), [the stated conclusion](goal) follows. -/
lemma affinePathExtension_positive_normalized_smooth
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    PositiveNormalizedSmoothMechanisms G (affinePathExtension s θ hji t) := by
  let θstar := embeddedSparseWitness s hji
  have hθ := θ.property.positiveSmooth
  have hstar := embeddedSparseWitness_positive_normalized_smooth s hji
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l v hv
    change 0 < (1 - t) * θ.1.p l v + t * θstar.p l v
    have hp := hθ.1 l v hv
    have hpstar := hstar.1 l v hv
    by_cases ht0 : t = 0
    · simp [ht0, hp]
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht.2) hp.le) (mul_pos htpos hpstar)
  · intro l z hz
    change 0 < (1 - t) * θ.1.q l z + t * θstar.q l z
    have hq := hθ.2.1 l z hz
    have hqstar := hstar.2.1 l z hz
    by_cases ht0 : t = 0
    · simp [ht0, hq]
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht.2) hq.le) (mul_pos htpos hqstar)
  · intro l
    exact (hθ.2.2.1 l).const_smul (1 - t) |>.add ((hstar.2.2.1 l).const_smul t)
  · intro l
    exact (hθ.2.2.2.1 l).const_smul (1 - t) |>.add
      ((hstar.2.2.2.1 l).const_smul t)
  · intro l v hv
    have hupdate : Continuous (fun z : ℝ => Function.update v l z) := by fun_prop
    have hmaps : MapsTo (fun z : ℝ => Function.update v l z)
        (Set.Icc (0 : ℝ) 1) (latentCube n) := by
      intro z hz k _
      by_cases hkl : k = l
      · subst k
        simpa using hz
      · simpa only [Function.update, dif_neg hkl] using hv k (Set.mem_univ k)
    have hpInt : IntegrableOn (fun z : ℝ => (1 - t) * θ.1.p l (Function.update v l z))
        (Set.Icc (0 : ℝ) 1) := by
      exact ((hθ.2.2.1 l).continuousOn.comp hupdate.continuousOn hmaps |>.const_mul _)
        |>.integrableOn_Icc
    have hpstarInt : IntegrableOn (fun z : ℝ => t * θstar.p l (Function.update v l z))
        (Set.Icc (0 : ℝ) 1) := by
      exact ((hstar.2.2.1 l).continuousOn.comp hupdate.continuousOn hmaps |>.const_mul _)
        |>.integrableOn_Icc
    change ∫ z in Set.Icc (0 : ℝ) 1,
      ((1 - t) * θ.1.p l (Function.update v l z) +
        t * θstar.p l (Function.update v l z)) = 1
    rw [MeasureTheory.integral_add,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      hθ.2.2.2.2.1 l v hv, hstar.2.2.2.2.1 l v hv]
    · ring
    · exact hpInt
    · exact hpstarInt
  · intro l
    change ∫ z in Set.Icc (0 : ℝ) 1,
      ((1 - t) * θ.1.q l z + t * θstar.q l z) = 1
    rw [MeasureTheory.integral_add,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      hθ.2.2.2.2.2 l, hstar.2.2.2.2.2 l]
    · ring
    · exact ((hθ.2.2.2.1 l).continuousOn.const_mul _).integrableOn_Icc
    · exact ((hstar.2.2.2.1 l).continuousOn.const_mul _).integrableOn_Icc

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

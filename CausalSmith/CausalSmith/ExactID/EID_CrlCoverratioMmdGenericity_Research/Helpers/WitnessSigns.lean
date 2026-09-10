import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Witnesses

/-!
# Derivative signs for the explicit witnesses

This file proves the elementary logarithmic-derivative bounds that give the
sparse witness its prescribed own-coordinate signs after reflection.
-/

open Set
noncomputable section
namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: exponentialInterventionDensity_hasDerivAt
/-- The normalized exponential intervention density has logarithmic slope four. -/
lemma exponentialInterventionDensity_hasDerivAt (x : ℝ) :
    HasDerivAt exponentialInterventionDensity (4 * exponentialInterventionDensity x) x := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (4 * y))
      (4 * Real.exp (4 * x)) x := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (4 * x)).comp x (hasDerivAt_const_mul (x := x) 4)
  unfold exponentialInterventionDensity
  convert (hexp.const_mul 4).div_const (Real.exp 4 - 1) using 1 <;>
    first | rfl | ring

-- @node: exponentialLogRatio_hasDerivAt
/-- The unreflected child log ratio has slope `4 - K / (5p)`. -/
lemma exponentialLogRatio_hasDerivAt (K x : ℝ)
    (hden : 1 + (1 / 10 : ℝ) * K * centeredCoordinate x ≠ 0) :
    HasDerivAt (fun z : ℝ => Real.log
      (exponentialInterventionDensity z /
        (1 + (1/10 : ℝ) * K * centeredCoordinate z)))
      (4 - (1/5 : ℝ) * K /
        (1 + (1/10 : ℝ) * K * centeredCoordinate x)) x := by
  have hq := exponentialInterventionDensity_hasDerivAt x
  have hd : HasDerivAt (fun z : ℝ => 1 + (1/10 : ℝ) * K * centeredCoordinate z)
      ((1/5 : ℝ) * K) x := by
    unfold centeredCoordinate
    convert ((((hasDerivAt_id x).const_mul 2).sub_const 1).const_mul
      ((1/10 : ℝ) * K)).const_add 1 using 1 <;> first | rfl | ring
  have hquot := hq.div hd hden
  have hqpos := exponentialInterventionDensity_pos x
  have hh := hquot.log (div_ne_zero (ne_of_gt hqpos) hden)
  simp only [Pi.div_apply] at hh
  change HasDerivAt (fun z : ℝ => Real.log
      (exponentialInterventionDensity z /
        (1 + (1 / 10 : ℝ) * K * centeredCoordinate z))) _ x at hh
  convert hh using 1
  have hden' : 10 + K * centeredCoordinate x ≠ 0 := by
    intro h
    apply hden
    nlinarith
  field_simp [hden', ne_of_gt hqpos]

-- @node: reflectedExponentialLogRatio_hasDerivAt
/-- Reflection reverses the child log-ratio derivative. -/
lemma reflectedExponentialLogRatio_hasDerivAt (K x : ℝ)
    (hden : 1 + (1 / 10 : ℝ) * K * centeredCoordinate (1 - x) ≠ 0) :
    HasDerivAt (fun z : ℝ => Real.log
      (exponentialInterventionDensity (1-z) /
        (1 + (1/10 : ℝ) * K * centeredCoordinate (1-z))))
      (-4 + (1/5 : ℝ) * K /
        (1 + (1/10 : ℝ) * K * centeredCoordinate (1-x))) x := by
  have hh := (exponentialLogRatio_hasDerivAt K (1 - x) hden).comp x
    ((hasDerivAt_const (x := x) (1 : ℝ)).sub (hasDerivAt_id x))
  convert hh using 1 <;> first | rfl | ring

-- @node: sparseWitness_fixedOwnDerivativeSign
/-- The reflected sparse witness has the prescribed strict own-coordinate derivative signs. -/
lemma sparseWitness_fixedOwnDerivativeSign (s : SignVector 3) :
    FixedOwnDerivativeSign threeNodeDAG s (sparseWitness s) := by
  intro i v hv
  unfold ownLogRatioDerivative
  have hud : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) 1) (v i) :=
    (uniqueDiffOn_Icc (by norm_num)).uniqueDiffWithinAt (hv i (Set.mem_univ i))
  by_cases hi : i = 1
  · subst i
    have hv0 : v 0 ∈ Set.Icc (0 : ℝ) 1 := hv 0 (Set.mem_univ 0)
    have hK := abs_centeredCoordinate_le_one
      (reflectedCoordinate_mem_unitInterval s 0 hv0)
    rw [abs_le] at hK
    rcases s.signed 1 with hs | hs
    · rw [hs]
      have href (z : ℝ) : reflectedCoordinate s 1 z = 1-z := by
        simp [reflectedCoordinate, reflect, hs, show (-1 : ℝ) ≠ 1 by norm_num]
      have hup (z : ℝ) : reflectedCoordinate s 0 ((Function.update v 1 z) 0) =
          reflectedCoordinate s 0 (v 0) := by simp [Function.update]
      simp only [sparseWitness, sparseQ, sparseP, if_true]
      simp_rw [href, hup]
      simp only [Function.update_self]
      change 0 < (-1 : ℝ) * derivWithin (fun z : ℝ => Real.log
        (exponentialInterventionDensity (1-z) /
          (1 + (1/10 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (1-z)))) (Set.Icc 0 1) (v 1)
      have hp := sparseP_pos s 1 v hv
      have hden : 1 + (1 / 10 : ℝ) *
          centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (1 - v 1) ≠ 0 := by
        simpa [sparseP, reflectedCoordinate, reflect, hs,
          show (-1 : ℝ) ≠ 1 by norm_num] using ne_of_gt hp
      rw [(reflectedExponentialLogRatio_hasDerivAt _ _ hden).hasDerivWithinAt.derivWithin
        hud]
      have hp' : 0 < 1 + (1 / 10 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
          centeredCoordinate (1 - v 1) := by
        have hv1 : 0 ≤ v 1 ∧ v 1 ≤ 1 := hv 1 (Set.mem_univ 1)
        have h1 := abs_centeredCoordinate_le_one
          (show 1 - v 1 ∈ Set.Icc (0 : ℝ) 1 by constructor <;> linarith)
        rw [abs_le] at h1
        nlinarith
      have hv1 : 0 ≤ v 1 ∧ v 1 ≤ 1 := hv 1 (Set.mem_univ 1)
      have h1 := abs_centeredCoordinate_le_one
        (show 1 - v 1 ∈ Set.Icc (0 : ℝ) 1 by constructor <;> linarith)
      rw [abs_le] at h1
      have hden_lb : (9 / 10 : ℝ) ≤ 1 + (1 / 10 : ℝ) *
          centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (1 - v 1) := by
        nlinarith
      have hfrac : centeredCoordinate (reflectedCoordinate s 0 (v 0)) /
          (1 + (1 / 10 : ℝ) * centeredCoordinate
            (reflectedCoordinate s 0 (v 0)) * centeredCoordinate (1 - v 1)) ≤ 10 / 9 :=
        (div_le_iff₀ hp').2 (by nlinarith [hden_lb])
      norm_num at hfrac ⊢
      have hsmall : (1 / 5 : ℝ) *
          (centeredCoordinate (reflectedCoordinate s 0 (v 0)) /
            (1 + (1 / 10 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
              centeredCoordinate (1 - v 1))) ≤ 2 / 9 :=
        calc
          _ ≤ (1 / 5 : ℝ) * (10 / 9) :=
            mul_le_mul_of_nonneg_left hfrac (by norm_num)
          _ = 2 / 9 := by norm_num
      norm_num at hsmall
      rw [mul_div_assoc]
      linarith
    · rw [hs]
      have href (z : ℝ) : reflectedCoordinate s 1 z = z := by
        simp [reflectedCoordinate, reflect, hs]
      have hup (z : ℝ) : reflectedCoordinate s 0 ((Function.update v 1 z) 0) =
          reflectedCoordinate s 0 (v 0) := by simp [Function.update]
      simp only [sparseWitness, sparseQ, sparseP, if_true]
      simp_rw [href, hup]
      simp only [Function.update_self]
      change 0 < (1 : ℝ) * derivWithin (fun z : ℝ => Real.log
        (exponentialInterventionDensity z /
          (1 + (1/10 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate z))) (Set.Icc 0 1) (v 1)
      have hp := sparseP_pos s 1 v hv
      have hden : 1 + (1 / 10 : ℝ) *
          centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (v 1) ≠ 0 := by
        simpa [sparseP, reflectedCoordinate, reflect, hs] using ne_of_gt hp
      rw [(exponentialLogRatio_hasDerivAt _ _ hden).hasDerivWithinAt.derivWithin hud]
      have hv1 : 0 ≤ v 1 ∧ v 1 ≤ 1 := hv 1 (Set.mem_univ 1)
      have h1 := abs_centeredCoordinate_le_one hv1
      rw [abs_le] at h1
      have hp' : 0 < 1 + (1 / 10 : ℝ) *
          centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (v 1) := by
        nlinarith
      have hden_lb : (9 / 10 : ℝ) ≤ 1 + (1 / 10 : ℝ) *
          centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (v 1) := by
        nlinarith
      have hfrac : centeredCoordinate (reflectedCoordinate s 0 (v 0)) /
          (1 + (1 / 10 : ℝ) * centeredCoordinate
            (reflectedCoordinate s 0 (v 0)) * centeredCoordinate (v 1)) ≤ 10 / 9 :=
        (div_le_iff₀ hp').2 (by nlinarith [hden_lb])
      norm_num at hfrac ⊢
      have hsmall : (1 / 5 : ℝ) *
          (centeredCoordinate (reflectedCoordinate s 0 (v 0)) /
            (1 + (1 / 10 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
              centeredCoordinate (v 1))) ≤ 2 / 9 :=
        calc
          _ ≤ (1 / 5 : ℝ) * (10 / 9) :=
            mul_le_mul_of_nonneg_left hfrac (by norm_num)
          _ = 2 / 9 := by norm_num
      norm_num at hsmall
      rw [mul_div_assoc]
      linarith
  · rcases s.signed i with hs | hs
    · rw [hs]
      have href (z : ℝ) : reflectedCoordinate s i z = 1 - z := by
        simp [reflectedCoordinate, reflect, hs, show (-1 : ℝ) ≠ 1 by norm_num]
      simp only [sparseWitness, sparseQ, sparseP, hi]
      simp_rw [href]
      simp only [if_false, div_one]
      have hd := reflectedExponentialLogRatio_hasDerivAt (0 : ℝ) (v i) (by norm_num)
      have hd' : HasDerivAt (fun z : ℝ => Real.log
          (exponentialInterventionDensity (1 - z))) (-4) (v i) := by
        simpa using hd
      rw [hd'.hasDerivWithinAt.derivWithin hud]
      norm_num
    · rw [hs]
      have href (z : ℝ) : reflectedCoordinate s i z = z := by
        simp [reflectedCoordinate, reflect, hs]
      simp only [sparseWitness, sparseQ, sparseP, hi]
      simp_rw [href]
      simp only [if_false, div_one]
      have hd := exponentialLogRatio_hasDerivAt (0 : ℝ) (v i) (by norm_num)
      have hd' : HasDerivAt (fun z : ℝ => Real.log
          (exponentialInterventionDensity z)) 4 (v i) := by
        simpa using hd
      rw [hd'.hasDerivWithinAt.derivWithin hud]
      norm_num

-- @node: cancellationWitness_fixedOwnDerivativeSign
/-- The reflected cancellation witness has the prescribed strict own-coordinate derivative signs. -/
lemma cancellationWitness_fixedOwnDerivativeSign (s : SignVector 3) :
    FixedOwnDerivativeSign threeNodeDAG s (cancellationWitness s) := by
  intro i v hv
  unfold ownLogRatioDerivative
  have hud : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) 1) (v i) :=
    (uniqueDiffOn_Icc (by norm_num)).uniqueDiffWithinAt (hv i (Set.mem_univ i))
  by_cases hi : i = 1
  · subst i
    have hv0 : v 0 ∈ Set.Icc (0 : ℝ) 1 := hv 0 (Set.mem_univ 0)
    have hK := cancellationPrimitive_mem_unitInterval_sub
      (reflectedCoordinate_mem_unitInterval s 0 hv0)
    rcases s.signed 1 with hs | hs
    · rw [hs]
      have href (z : ℝ) : reflectedCoordinate s 1 z = 1-z := by
        simp [reflectedCoordinate, reflect, hs, show (-1 : ℝ) ≠ 1 by norm_num]
      have hup (z : ℝ) : reflectedCoordinate s 0 ((Function.update v 1 z) 0) =
          reflectedCoordinate s 0 (v 0) := by simp [Function.update]
      simp only [cancellationWitness, sparseQ, cancellationP, if_true]
      simp_rw [href, hup]
      simp only [Function.update_self]
      change 0 < (-1 : ℝ) * derivWithin (fun z : ℝ => Real.log
        (exponentialInterventionDensity (1-z) /
          (1 + (1/10 : ℝ) * cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (1-z)))) (Set.Icc 0 1) (v 1)
      have hp := cancellationP_pos s 1 v hv
      have hden : 1 + (1 / 10 : ℝ) *
          cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (1 - v 1) ≠ 0 := by
        simpa [cancellationP, reflectedCoordinate, reflect, hs,
          show (-1 : ℝ) ≠ 1 by norm_num] using ne_of_gt hp
      rw [(reflectedExponentialLogRatio_hasDerivAt _ _ hden).hasDerivWithinAt.derivWithin
        hud]
      have hv1 : 0 ≤ v 1 ∧ v 1 ≤ 1 := hv 1 (Set.mem_univ 1)
      have h1 := abs_centeredCoordinate_le_one
        (show 1 - v 1 ∈ Set.Icc (0 : ℝ) 1 by constructor <;> linarith)
      rw [abs_le] at h1
      have hp' : 0 < 1 + (1 / 10 : ℝ) *
          cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (1 - v 1) := by
        nlinarith [hK.1, hK.2]
      have hden_lb : (9 / 10 : ℝ) ≤ 1 + (1 / 10 : ℝ) *
          cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (1 - v 1) := by
        nlinarith [hK.1, hK.2]
      have hfrac : cancellationPrimitive (reflectedCoordinate s 0 (v 0)) /
          (1 + (1 / 10 : ℝ) * cancellationPrimitive
            (reflectedCoordinate s 0 (v 0)) * centeredCoordinate (1 - v 1)) ≤ 10 / 9 :=
        (div_le_iff₀ hp').2 (by nlinarith [hK.2, hden_lb])
      norm_num at hfrac ⊢
      have hsmall : (1 / 5 : ℝ) *
          (cancellationPrimitive (reflectedCoordinate s 0 (v 0)) /
            (1 + (1 / 10 : ℝ) * cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
              centeredCoordinate (1 - v 1))) ≤ 2 / 9 :=
        calc
          _ ≤ (1 / 5 : ℝ) * (10 / 9) :=
            mul_le_mul_of_nonneg_left hfrac (by norm_num)
          _ = 2 / 9 := by norm_num
      norm_num at hsmall
      rw [mul_div_assoc]
      linarith
    · rw [hs]
      have href (z : ℝ) : reflectedCoordinate s 1 z = z := by
        simp [reflectedCoordinate, reflect, hs]
      have hup (z : ℝ) : reflectedCoordinate s 0 ((Function.update v 1 z) 0) =
          reflectedCoordinate s 0 (v 0) := by simp [Function.update]
      simp only [cancellationWitness, sparseQ, cancellationP, if_true]
      simp_rw [href, hup]
      simp only [Function.update_self]
      change 0 < (1 : ℝ) * derivWithin (fun z : ℝ => Real.log
        (exponentialInterventionDensity z /
          (1 + (1/10 : ℝ) * cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate z))) (Set.Icc 0 1) (v 1)
      have hp := cancellationP_pos s 1 v hv
      have hden : 1 + (1 / 10 : ℝ) *
          cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (v 1) ≠ 0 := by
        simpa [cancellationP, reflectedCoordinate, reflect, hs] using ne_of_gt hp
      rw [(exponentialLogRatio_hasDerivAt _ _ hden).hasDerivWithinAt.derivWithin hud]
      have hv1 : 0 ≤ v 1 ∧ v 1 ≤ 1 := hv 1 (Set.mem_univ 1)
      have h1 := abs_centeredCoordinate_le_one hv1
      rw [abs_le] at h1
      have hp' : 0 < 1 + (1 / 10 : ℝ) *
          cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (v 1) := by
        nlinarith [hK.1, hK.2]
      have hden_lb : (9 / 10 : ℝ) ≤ 1 + (1 / 10 : ℝ) *
          cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
            centeredCoordinate (v 1) := by
        nlinarith [hK.1, hK.2]
      have hfrac : cancellationPrimitive (reflectedCoordinate s 0 (v 0)) /
          (1 + (1 / 10 : ℝ) * cancellationPrimitive
            (reflectedCoordinate s 0 (v 0)) * centeredCoordinate (v 1)) ≤ 10 / 9 :=
        (div_le_iff₀ hp').2 (by nlinarith [hK.2, hden_lb])
      norm_num at hfrac ⊢
      have hsmall : (1 / 5 : ℝ) *
          (cancellationPrimitive (reflectedCoordinate s 0 (v 0)) /
            (1 + (1 / 10 : ℝ) * cancellationPrimitive (reflectedCoordinate s 0 (v 0)) *
              centeredCoordinate (v 1))) ≤ 2 / 9 :=
        calc
          _ ≤ (1 / 5 : ℝ) * (10 / 9) :=
            mul_le_mul_of_nonneg_left hfrac (by norm_num)
          _ = 2 / 9 := by norm_num
      norm_num at hsmall
      rw [mul_div_assoc]
      linarith
  · rcases s.signed i with hs | hs
    · rw [hs]
      have href (z : ℝ) : reflectedCoordinate s i z = 1 - z := by
        simp [reflectedCoordinate, reflect, hs, show (-1 : ℝ) ≠ 1 by norm_num]
      simp only [cancellationWitness, sparseQ, cancellationP, hi]
      simp_rw [href]
      simp only [if_false, div_one]
      have hd := reflectedExponentialLogRatio_hasDerivAt (0 : ℝ) (v i) (by norm_num)
      have hd' : HasDerivAt (fun z : ℝ => Real.log
          (exponentialInterventionDensity (1 - z))) (-4) (v i) := by
        simpa using hd
      rw [hd'.hasDerivWithinAt.derivWithin hud]
      norm_num
    · rw [hs]
      have href (z : ℝ) : reflectedCoordinate s i z = z := by
        simp [reflectedCoordinate, reflect, hs]
      simp only [cancellationWitness, sparseQ, cancellationP, hi]
      simp_rw [href]
      simp only [if_false, div_one]
      have hd := exponentialLogRatio_hasDerivAt (0 : ℝ) (v i) (by norm_num)
      have hd' : HasDerivAt (fun z : ℝ => Real.log
          (exponentialInterventionDensity z)) 4 (v i) := by
        simpa using hd
      rw [hd'.hasDerivWithinAt.derivWithin hud]
      norm_num

-- @node: explicitWitness_regularities
/-- Both explicit witnesses are positive, normalized, smooth to every finite order, and obey
their prescribed own-coordinate derivative signs. -/
lemma explicitWitness_regularities (s : SignVector 3) :
    PositiveNormalizedSmoothMechanisms threeNodeDAG (sparseWitness s) ∧
    FixedOwnDerivativeSign threeNodeDAG s (sparseWitness s) ∧
    (∀ k i, ContDiffOn ℝ k ((sparseWitness s).p i) (latentCube 3)) ∧
    (∀ k i, ContDiffOn ℝ k ((sparseWitness s).q i) (Set.Icc (0 : ℝ) 1)) ∧
    PositiveNormalizedSmoothMechanisms threeNodeDAG (cancellationWitness s) ∧
    FixedOwnDerivativeSign threeNodeDAG s (cancellationWitness s) ∧
    (∀ k i, ContDiffOn ℝ k ((cancellationWitness s).p i) (latentCube 3)) ∧
    (∀ k i, ContDiffOn ℝ k ((cancellationWitness s).q i) (Set.Icc (0 : ℝ) 1)) := by
  rcases sparseWitness_contDiff_all s with ⟨hsp, hsq⟩
  rcases cancellationWitness_contDiff_all s with ⟨hcp, hcq⟩
  exact ⟨sparseWitness_positive_normalized_smooth s,
    sparseWitness_fixedOwnDerivativeSign s, hsp, hsq,
    cancellationWitness_positive_normalized_smooth s,
    cancellationWitness_fixedOwnDerivativeSign s, hcp, hcq⟩

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

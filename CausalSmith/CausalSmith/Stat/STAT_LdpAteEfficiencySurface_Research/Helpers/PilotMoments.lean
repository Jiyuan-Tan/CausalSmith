module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Pilot

/-! # Algebraic moment identities for the pilot score -/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open scoped BigOperators

/-- The randomized-response pilot output has the affine categorical
probability used by the inverse-frequency estimator. For [the displayed inputs and conditions](hyp:p), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:k), these specify the stated inputs. -/
lemma rrPilot_marginal_probability (θ : TrialParameter) (p ε : ℝ)
    (k : Fin 4) :
    ∑ j : Fin 4, piTheta θ p j * rrPilotProbability ε j k =
      ((Real.exp ε - 1) * piTheta θ p k + 1) / (Real.exp ε + 3) := by
  have hpi0 : piTheta θ p 0 = controlProb p * (1 - θ 0) := rfl
  have hpi1 : piTheta θ p 1 = controlProb p * θ 0 := rfl
  have hpi2 : piTheta θ p 2 = p * (1 - θ 1) := rfl
  have hpi3 : piTheta θ p 3 = p * θ 1 := rfl
  fin_cases k <;>
    simp +decide [rrPilotProbability, controlProb, Fin.sum_univ_succ,
      hpi0, hpi1, hpi2, hpi3] <;>
    field_simp [ne_of_gt (by positivity : 0 < Real.exp ε + 3)] <;> ring

/-- Inverting the exact randomized-response pilot probability recovers the corresponding private-input cell probability. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε), [the rr Pilot inverse marginal probability](goal).

Under the stated assumptions, the rr Pilot inverse marginal probability. -/
-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
lemma rrPilot_inverse_marginal_probability (θ : TrialParameter) (p ε : ℝ)
    (hε : 0 < ε) (k : Fin 4) :
    ((Real.exp ε + 3) *
        (∑ j : Fin 4, piTheta θ p j * rrPilotProbability ε j k) - 1) /
      (Real.exp ε - 1) = piTheta θ p k := by
  rw [rrPilot_marginal_probability]
  have he : Real.exp ε - 1 ≠ 0 := by
    have : 1 < Real.exp ε := by
      simpa using (Real.exp_lt_exp.mpr hε : Real.exp 0 < Real.exp ε)
    linarith
  field_simp [he, ne_of_gt (by positivity : 0 < Real.exp ε + 3)]
  ring

/-- Clipping is inactive once its margin is inside both distances to the
boundary. For [the displayed inputs and conditions](hyp:hleft), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:hright), these specify the stated inputs. -/
lemma clipInterior_eq_self {δ x : ℝ} (hleft : δ ≤ x)
    (hright : δ ≤ 1 - x) :
    clipInterior δ x = x := by
  rw [clipInterior, min_eq_right (by linarith), max_eq_right hleft]

/-- At a minimizing contrast direction, the information matrix sends that
direction to its quadratic value times the contrast vector. For [the displayed inputs and conditions](hyp:hI,t), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:I,hmin), these specify the stated inputs. -/
lemma matrix_mulVec_direction_eq_value_contrast
    (I : Matrix (Fin 2) (Fin 2) ℝ) (hI : I.IsHermitian) (t : ℝ)
    (hmin : ∀ u : ℝ,
      informationQuadratic I (direction t) ≤
        informationQuadratic I (direction u)) :
    I.mulVec (direction t) = fun k =>
      informationQuadratic I (direction t) * contrastVector k := by
  let A := I 0 0 + I 0 1 + I 1 0 + I 1 1
  let B := 2 * (I 0 0 * t + I 0 1 * (t + 1) +
    I 1 0 * t + I 1 1 * (t + 1))
  have hs := congrFun₂ hI 0 1
  have hpoly (x : ℝ) : 0 ≤ x * B + x ^ 2 * A := by
    have h := hmin (t + x)
    have hid : informationQuadratic I (direction (t + x)) =
        informationQuadratic I (direction t) + x * B + x ^ 2 * A := by
      dsimp [A, B]
      simp [informationQuadratic, direction, Fin.sum_univ_succ,
        star_trivial] at hs ⊢
      rw [hs]
      ring
    rw [hid] at h
    linarith
  have hB : B = 0 := by
    by_contra hB0
    have hden : 0 < |A| + 1 := by positivity
    have hAle : A ≤ |A| := le_abs_self A
    have h := hpoly (-B / (2 * (|A| + 1)))
    have hsq : 0 < B ^ 2 := sq_pos_of_ne_zero hB0
    field_simp at h
    nlinarith [mul_nonneg hsq.le (sub_nonneg.mpr hAle)]
  have hsum :
      (I 0 0 * t + I 0 1 * (t + 1)) +
        (I 1 0 * t + I 1 1 * (t + 1)) = 0 := by
    dsimp [B] at hB
    linarith
  have hj : informationQuadratic I (direction t) =
      I 1 0 * t + I 1 1 * (t + 1) := by
    simp [informationQuadratic, direction, Fin.sum_univ_succ]
    linear_combination t * hsum
  funext k
  fin_cases k <;>
    simp [Matrix.mulVec, direction, contrastVector, Fin.sum_univ_succ] at hs ⊢ <;>
    rw [hj] <;> linarith

/-- The saddle direction satisfies the exact score normal equation. For [the displayed inputs and conditions](hyp:p), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:t,J,hmin,hJ), these specify the stated inputs. -/
lemma saddle_information_normalEquation (θ : TrialParameter) (p ε : ℝ)
    (α : StaircaseWeight) (t J : ℝ)
    (hmin : ∀ u, informationObjective θ p ε α t ≤
      informationObjective θ p ε α u)
    (hJ : J = informationObjective θ p ε α t) :
    (informationMatrix θ p ε α).mulVec (direction t) =
      fun k => J * contrastVector k := by
  have hquad (u : ℝ) :
      informationQuadratic (informationMatrix θ p ε α) (direction u) =
        informationObjective θ p ε α u := by
    rw [informationObjective_eq_informationQuadratic]
    simp [informationQuadratic, dotProduct, Matrix.mulVec, star_trivial]
  have hmin' : ∀ u : ℝ,
      informationQuadratic (informationMatrix θ p ε α) (direction t) ≤
        informationQuadratic (informationMatrix θ p ε α) (direction u) := by
    intro u
    rw [hquad, hquad]
    exact hmin u
  have hHermitian : (informationMatrix θ p ε α).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    unfold informationMatrix
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hnormal := matrix_mulVec_direction_eq_value_contrast
    (informationMatrix θ p ε α)
    hHermitian t hmin'
  calc
    (informationMatrix θ p ε α).mulVec (direction t) =
        fun k => informationObjective θ p ε α t * contrastVector k := by
      rw [← hquad]
      exact hnormal
    _ = fun k => J * contrastVector k := by rw [hJ]

/-- Under [the supplied quantities and conditions](hyp:p), [the pattern mass affine difference assertion](goal) holds. For [the displayed quantities and conditions](hyp:s), these specify the stated inputs. -/
lemma patternMass_affine_difference (θ η : TrialParameter) (p ε : ℝ)
    (s : Fin 14) :
    patternMass θ p ε s = patternMass η p ε s +
      ∑ k : Fin 2, (θ k - η k) * patternGradient p ε s k := by
  have hpi (ξ : TrialParameter) (j : Fin 4) : piTheta ξ p j =
      if j.val = 0 then controlProb p * (1 - ξ 0)
      else if j.val = 1 then controlProb p * ξ 0
      else if j.val = 2 then p * (1 - ξ 1) else p * ξ 1 := by
    fin_cases j <;> rfl
  cases h0 : patternContains s 0 <;>
    cases h1 : patternContains s 1 <;>
    cases h2 : patternContains s 2 <;>
    cases h3 : patternContains s 3 <;>
    simp [patternMass, hpi, patternRay, patternGradient,
      privacyIncrement, controlProb, Fin.sum_univ_two, Fin.sum_univ_four,
      h0, h1, h2, h3] <;> ring

/-- Under [the supplied quantities and conditions](hyp:p,s), [the pattern gradient eq ray sub assertion](goal) holds. -/
lemma patternGradient_eq_ray_sub (p ε : ℝ) (s : Fin 14) :
    patternGradient p ε s 0 =
      controlProb p * (patternRay ε s 1 - patternRay ε s 0) ∧
    patternGradient p ε s 1 =
      p * (patternRay ε s 3 - patternRay ε s 2) := by
  cases h0 : patternContains s 0 <;>
    cases h1 : patternContains s 1 <;>
    cases h2 : patternContains s 2 <;>
    cases h3 : patternContains s 3 <;>
    simp [patternGradient, patternRay, privacyIncrement,
      h0, h1, h2, h3] <;> ring <;> simp

/-- Under the supplied quantities and conditions, the staircase weighted gradient sum eq zero assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hα), [the staircase weighted Gradient sum eq zero](goal).

Under the stated assumptions, the staircase weighted Gradient sum eq zero. -/
lemma staircase_weightedGradient_sum_eq_zero (p ε : ℝ)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) (k : Fin 2) :
    ∑ s : Fin 14, α s * patternGradient p ε s k = 0 := by
  fin_cases k
  · calc
      (∑ s : Fin 14, α s * patternGradient p ε s 0) =
          ∑ s : Fin 14, α s *
            (controlProb p * (patternRay ε s 1 - patternRay ε s 0)) := by
              apply Finset.sum_congr rfl
              intro s _
              rw [(patternGradient_eq_ray_sub p ε s).1]
      _ = controlProb p *
          ((∑ s : Fin 14, α s * patternRay ε s 1) -
            ∑ s : Fin 14, α s * patternRay ε s 0) := by
              rw [← Finset.sum_sub_distrib, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s _
              ring
      _ = controlProb p *
          (staircaseMatrix ε α 1 - staircaseMatrix ε α 0) := rfl
      _ = 0 := by rw [hα.2 1, hα.2 0]; ring
  · calc
      (∑ s : Fin 14, α s * patternGradient p ε s 1) =
          ∑ s : Fin 14, α s *
            (p * (patternRay ε s 3 - patternRay ε s 2)) := by
              apply Finset.sum_congr rfl
              intro s _
              rw [(patternGradient_eq_ray_sub p ε s).2]
      _ = p * ((∑ s : Fin 14, α s * patternRay ε s 3) -
            ∑ s : Fin 14, α s * patternRay ε s 2) := by
              rw [← Finset.sum_sub_distrib, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s _
              ring
      _ = p * (staircaseMatrix ε α 3 - staircaseMatrix ε α 2) := rfl
      _ = 0 := by rw [hα.2 3, hα.2 2]; ring

/-- Under the supplied quantities and conditions, the staircase weighted projected gradient sum eq zero assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hα), [the staircase weighted Projected Gradient sum eq zero](goal).

Under the stated assumptions, the staircase weighted Projected Gradient sum eq zero. -/
lemma staircase_weightedProjectedGradient_sum_eq_zero (p ε t : ℝ)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) :
    ∑ s : Fin 14, α s * projectedGradient p ε s t = 0 := by
  have h0 := staircase_weightedGradient_sum_eq_zero p ε α hα 0
  have h1 := staircase_weightedGradient_sum_eq_zero p ε α hα 1
  calc
    (∑ s : Fin 14, α s * projectedGradient p ε s t) =
        (∑ s : Fin 14, α s * patternGradient p ε s 0) * direction t 0 +
        (∑ s : Fin 14, α s * patternGradient p ε s 1) * direction t 1 := by
          unfold projectedGradient
          simp only [Fin.sum_univ_two]
          rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro s _
          ring
    _ = 0 := by rw [h0, h1]; ring

/-- Under [the supplied quantities and conditions](hyp:p), [the information matrix mul vec direction apply assertion](goal) holds. For [the displayed quantities and conditions](hyp:t,k), these specify the stated inputs. -/
lemma informationMatrix_mulVec_direction_apply (θ : TrialParameter) (p ε : ℝ)
    (α : StaircaseWeight) (t : ℝ) (k : Fin 2) :
    (informationMatrix θ p ε α).mulVec (direction t) k =
      ∑ s : Fin 14, α s * patternGradient p ε s k *
        projectedGradient p ε s t / patternMass θ p ε s := by
  fin_cases k <;>
    simp [informationMatrix, Matrix.mulVec, projectedGradient,
      Fin.sum_univ_two] <;>
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib] <;>
    apply Finset.sum_congr rfl <;>
    intro s _ <;> ring

/-- Exact one-step affine correction identity. If `η` selects a feasible saddle `(α,t,J)`, then averaging its influence score under the true parameter `θ` corrects `contrast η` exactly to `contrast θ`. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hη,hε,hα,hJ,hnormal), [the affine Correction mean identity](goal).

Under the stated assumptions, the affine Correction mean identity. -/
lemma affineCorrection_mean_identity (θ η : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hη : InteriorMeans η) (hε : 0 ≤ ε)
    (α : StaircaseWeight) (t J : ℝ) (hα : staircaseFeasible ε α)
    (hJ : J ≠ 0)
    (hnormal : (informationMatrix η p ε α).mulVec (direction t) =
      fun k => J * contrastVector k) :
    ∑ s : Fin 14, α s * patternMass θ p ε s *
        (projectedGradient p ε s t / (J * patternMass η p ε s)) =
      contrast θ - contrast η := by
  have hm (s : Fin 14) : patternMass η p ε s ≠ 0 :=
    ne_of_gt (patternMass_pos_interior η p ε hp hη hε s)
  have hexpand :
      (∑ s : Fin 14, α s * patternMass θ p ε s *
        (projectedGradient p ε s t / (J * patternMass η p ε s))) =
      J⁻¹ * ((∑ s : Fin 14, α s * projectedGradient p ε s t) +
        ∑ k : Fin 2, (θ k - η k) *
          (informationMatrix η p ε α).mulVec (direction t) k) := by
    simp only [Fin.sum_univ_two]
    rw [informationMatrix_mulVec_direction_apply η p ε α t 0,
      informationMatrix_mulVec_direction_apply η p ε α t 1]
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [patternMass_affine_difference θ η p ε s]
    simp only [Fin.sum_univ_two]
    field_simp [hJ, hm s]
  rw [hexpand, staircase_weightedProjectedGradient_sum_eq_zero p ε t α hα,
    zero_add, hnormal]
  simp only [Fin.sum_univ_two]
  simp [contrastVector, contrast]
  field_simp [hJ]
  ring

/-- The selected affine correction has the exact mean shift under every interior parameter. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hη,hε,hselect), [the phi Tilde mean identity](goal).

Under the stated assumptions, the phi Tilde mean identity. -/
lemma phiTilde_mean_identity (θ η : TrialParameter) (p ε : ℝ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    (hp : InteriorAssignment p) (hη : InteriorMeans η) (hε : 0 < ε)
    (hselect : SaddleSelection p ε select) :
    ∑ s : Fin 14, (select η).1 s * patternMass θ p ε s *
        phiTilde η p ε select s = contrast θ - contrast η := by
  have hs := hselect.2 η hη
  have hJpos : 0 < (select η).2.2 := by
    rw [← hs.2.2.1]
    exact Jstar_pos_interior η p ε hp hη hε
  have hnormal := saddle_information_normalEquation η p ε
    (select η).1 (select η).2.1 (select η).2.2 hs.2.1 hs.2.2.2
  simpa [phiTilde] using affineCorrection_mean_identity θ η p ε
    hp hη hε.le (select η).1 (select η).2.1 (select η).2.2
    hs.1 hJpos.ne' hnormal

/-- At its construction parameter, a saddle affine correction has second moment equal to reciprocal saddle information. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hη,hε,hJ,hvalue), [the affine Correction second Moment identity](goal).

Under the stated assumptions, the affine Correction second Moment identity. -/
lemma affineCorrection_secondMoment_identity (η : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hη : InteriorMeans η) (hε : 0 ≤ ε)
    (α : StaircaseWeight) (t J : ℝ) (hJ : J ≠ 0)
    (hvalue : J = informationObjective η p ε α t) :
    ∑ s : Fin 14, α s * patternMass η p ε s *
        (projectedGradient p ε s t / (J * patternMass η p ε s)) ^ 2 =
      J⁻¹ := by
  have hm (s : Fin 14) : patternMass η p ε s ≠ 0 :=
    ne_of_gt (patternMass_pos_interior η p ε hp hη hε s)
  calc
    (∑ s : Fin 14, α s * patternMass η p ε s *
        (projectedGradient p ε s t / (J * patternMass η p ε s)) ^ 2) =
        (J ^ 2)⁻¹ * informationObjective η p ε α t := by
          unfold informationObjective patternInformation
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          field_simp [hJ, hm s]
    _ = J⁻¹ := by rw [← hvalue]; field_simp [hJ]

/-- The selected influence value has exact conditional second moment `Vstar` at the selection parameter. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hη,hε,hselect), [the phi Tilde second Moment identity](goal).

Under the stated assumptions, the phi Tilde second Moment identity. -/
lemma phiTilde_secondMoment_identity (η : TrialParameter) (p ε : ℝ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    (hp : InteriorAssignment p) (hη : InteriorMeans η) (hε : 0 < ε)
    (hselect : SaddleSelection p ε select) :
    ∑ s : Fin 14, (select η).1 s * patternMass η p ε s *
        (phiTilde η p ε select s) ^ 2 = Vstar η p ε := by
  have hs := hselect.2 η hη
  have hJpos : 0 < (select η).2.2 := by
    rw [← hs.2.2.1]
    exact Jstar_pos_interior η p ε hp hη hε
  have hmoment := affineCorrection_secondMoment_identity η p ε hp hη hε.le
    (select η).1 (select η).2.1 (select η).2.2 hJpos.ne' hs.2.2.2
  simpa [phiTilde, Vstar, hs.2.2.1] using hmoment

end CausalSmith.Stat.LdpAteEfficiencySurface

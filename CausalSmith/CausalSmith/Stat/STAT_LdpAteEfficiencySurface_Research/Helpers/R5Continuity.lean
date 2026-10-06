module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.R3Continuity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.R5Rigidity

/-! # Continuous active-dual solver for the five-output region

The four active rows used to determine the dual certificate have an explicit
right inverse throughout the positive-privacy parameter region.  The fifth
active equality is supplied separately by the two constituent-objective
identity in the R5 continuation argument.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

/-- For [the supplied quantities and conditions](hyp:i), the [r5 dual mask](goal) is the mathematical object specified below. -/
def r5DualMask (i : Fin 4) : Fin 14 := ![2, 3, 5, 7] i

/-- [The dual constraint matrix for the five-output region](goal) is determined by [the displayed parameters](hyp:x). -/
noncomputable def r5DualMatrix (x : RegionParameter) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => patternRay x.2.2.2 (r5DualMask i) j

/-- [A right inverse for the five-output dual matrix](goal) is determined by [the displayed parameters](hyp:ε). -/
noncomputable def r5DualRightInverse (ε : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let r := Real.exp ε
  let a := (r - 1) * (r + 2)
  !![(r + 1) / a, (r + 1) / a, -1 / (r - 1), -1 / a;
     0, -1 / (r - 1), 1 / (r - 1), 0;
     -1 / a, (r + 1) / a, 0, -1 / a;
     -1 / a, -1 / a, 0, (r + 1) / a]

/-- Under the supplied quantities and conditions, the r5 dual matrix mul right inverse assertion holds. Under [the stated assumptions](hyp:hε), [the r5 Dual Matrix mul right Inverse](goal).

Under the stated assumptions, the r5 Dual Matrix mul right Inverse. -/
lemma r5DualMatrix_mul_rightInverse (x : RegionParameter) (hε : 0 < x.2.2.2) :
    r5DualMatrix x * r5DualRightInverse x.2.2.2 = 1 := by
  have hr : 1 < Real.exp x.2.2.2 := (Real.one_lt_exp_iff).2 hε
  have hd1 : Real.exp x.2.2.2 - 1 ≠ 0 := by positivity
  have hda : (Real.exp x.2.2.2 - 1) * (Real.exp x.2.2.2 + 2) ≠ 0 := by
    positivity
  ext i k
  change (∑ j : Fin 4, r5DualMatrix x i j *
    r5DualRightInverse x.2.2.2 j k) = (1 : Matrix (Fin 4) (Fin 4) ℝ) i k
  fin_cases i <;> fin_cases k <;>
    simp +decide [r5DualMatrix, r5DualRightInverse, r5DualMask,
      patternRay, patternContains, privacyIncrement, privacyRatio,
      Fin.sum_univ_succ] <;> field_simp [hd1, hda] <;> ring

/-- [the continuous r5 dual matrix assertion](goal) holds. -/
lemma continuous_r5DualMatrix : Continuous r5DualMatrix := by
  apply continuous_matrix
  intro i j
  exact continuous_patternRay_region (r5DualMask i) j

/-- The normalized objective contributed by the two binary active rays. [The r5 Binary Objective](goal) is determined by [the displayed parameters](hyp:x,t). -/
noncomputable def r5BinaryObjective (x : RegionParameter) (t : ℝ) : ℝ :=
  (patternInformation (regionTheta x) x.1 x.2.2.2 5 t +
    patternInformation (regionTheta x) x.1 x.2.2.2 8 t) /
      (Real.exp x.2.2.2 + 1)

/-- The normalized objective contributed by the three ternary active rays. [The r5 Ternary Objective](goal) is determined by [the displayed parameters](hyp:x,t). -/
noncomputable def r5TernaryObjective (x : RegionParameter) (t : ℝ) : ℝ :=
  (patternInformation (regionTheta x) x.1 x.2.2.2 2 t +
    patternInformation (regionTheta x) x.1 x.2.2.2 3 t +
    patternInformation (regionTheta x) x.1 x.2.2.2 7 t) /
      (Real.exp x.2.2.2 + 2)

/-- [The binary component coefficient in the five-output continuation argument](goal) is determined by [the displayed parameters](hyp:x). -/
noncomputable def r5BinaryCoeff (x : RegionParameter) : ℝ :=
  privacyIncrement x.2.2.2 ^ 2 / (Real.exp x.2.2.2 + 1) *
    (1 / patternMass (regionTheta x) x.1 x.2.2.2 5 +
      1 / patternMass (regionTheta x) x.1 x.2.2.2 8)

/-- [The ternary component coefficient in the five-output continuation argument](goal) is determined by [the displayed parameters](hyp:x). -/
noncomputable def r5TernaryCoeff (x : RegionParameter) : ℝ :=
  privacyIncrement x.2.2.2 ^ 2 * x.1 ^ 2 /
      (Real.exp x.2.2.2 + 2) *
    (1 / patternMass (regionTheta x) x.1 x.2.2.2 3 +
      1 / patternMass (regionTheta x) x.1 x.2.2.2 7)

/-- Under [the supplied quantities and conditions](hyp:x,t), [the r5 binary objective eq quadratic assertion](goal) holds. For [the displayed quantities and conditions](hyp:hm5,hm8), these specify the stated inputs. -/
lemma r5BinaryObjective_eq_quadratic (x : RegionParameter) (t : ℝ)
    (hm5 : patternMass (regionTheta x) x.1 x.2.2.2 5 ≠ 0)
    (hm8 : patternMass (regionTheta x) x.1 x.2.2.2 8 ≠ 0) :
    r5BinaryObjective x t =
      r5BinaryCoeff x * (x.1 - (1 - 2 * x.1) * t) ^ 2 := by
  have hd : Real.exp x.2.2.2 + 1 ≠ 0 := by positivity
  unfold r5BinaryObjective r5BinaryCoeff patternInformation
  simp +decide [projectedGradient, patternGradient, patternContains,
    controlProb, direction, Fin.sum_univ_succ]
  field_simp [hm5, hm8, hd]
  ring

/-- Under [the supplied quantities and conditions](hyp:x,t), [the r5 ternary objective eq quadratic assertion](goal) holds. For [the displayed quantities and conditions](hyp:hm3,hm7), these specify the stated inputs. -/
lemma r5TernaryObjective_eq_quadratic (x : RegionParameter) (t : ℝ)
    (hm3 : patternMass (regionTheta x) x.1 x.2.2.2 3 ≠ 0)
    (hm7 : patternMass (regionTheta x) x.1 x.2.2.2 7 ≠ 0) :
    r5TernaryObjective x t = r5TernaryCoeff x * (t + 1) ^ 2 := by
  have hd : Real.exp x.2.2.2 + 2 ≠ 0 := by positivity
  unfold r5TernaryObjective r5TernaryCoeff patternInformation
  simp +decide [projectedGradient, patternGradient, patternContains,
    controlProb, direction, Fin.sum_univ_succ]
  field_simp [hm3, hm7, hd]

/-- Under the supplied quantities and conditions, the r5 coeffs pos of interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp0,hp1,hμ00,hμ01,hμ10,hμ11,hε), [the r5 Coeffs pos of interior](goal).

Under the stated assumptions, the r5 Coeffs pos of interior. -/
lemma r5Coeffs_pos_of_interior (x : RegionParameter)
    (hp0 : 0 < x.1) (hp1 : x.1 < 1)
    (hμ00 : 0 < x.2.1) (hμ01 : x.2.1 < 1)
    (hμ10 : 0 < x.2.2.1) (hμ11 : x.2.2.1 < 1)
    (hε : 0 < x.2.2.2) :
    0 < r5BinaryCoeff x ∧ 0 < r5TernaryCoeff x := by
  have hd : 0 < privacyIncrement x.2.2.2 := by
    unfold privacyIncrement privacyRatio
    exact sub_pos.mpr ((Real.one_lt_exp_iff).2 hε)
  have hm (s : Fin 14) :
      0 < patternMass (regionTheta x) x.1 x.2.2.2 s := by
    exact patternMass_pos_of_interior x.1 x.2.1 x.2.2.1 x.2.2.2
      hp0 hp1 hμ00 hμ01 hμ10 hμ11 s
  constructor
  · unfold r5BinaryCoeff
    exact mul_pos (div_pos (sq_pos_of_pos hd) (by positivity))
      (add_pos (one_div_pos.mpr (hm 5)) (one_div_pos.mpr (hm 8)))
  · unfold r5TernaryCoeff
    exact mul_pos
      (div_pos (mul_pos (sq_pos_of_pos hd) (sq_pos_of_pos hp0)) (by positivity))
      (add_pos (one_div_pos.mpr (hm 3)) (one_div_pos.mpr (hm 7)))

/-- Under [the supplied quantities and conditions](hyp:x), [the continuous at r5 binary coeff assertion](goal) holds. For [the displayed quantities and conditions](hyp:hm5,hm8), these specify the stated inputs. -/
lemma continuousAt_r5BinaryCoeff (x : RegionParameter)
    (hm5 : patternMass (regionTheta x) x.1 x.2.2.2 5 ≠ 0)
    (hm8 : patternMass (regionTheta x) x.1 x.2.2.2 8 ≠ 0) :
    ContinuousAt r5BinaryCoeff x := by
  unfold r5BinaryCoeff privacyIncrement privacyRatio
  apply ContinuousAt.mul
  · apply ContinuousAt.div
    · exact (((Real.continuous_exp.comp continuous_snd.snd.snd).sub
        continuous_const).pow 2).continuousAt
    · exact ((Real.continuous_exp.comp continuous_snd.snd.snd).add
        continuous_const).continuousAt
    · positivity
  · apply ContinuousAt.add
    · exact continuousAt_const.div
        (continuous_patternMass_region 5).continuousAt hm5
    · exact continuousAt_const.div
        (continuous_patternMass_region 8).continuousAt hm8

/-- Under [the supplied quantities and conditions](hyp:x), [the continuous at r5 ternary coeff assertion](goal) holds. For [the displayed quantities and conditions](hyp:hm3,hm7), these specify the stated inputs. -/
lemma continuousAt_r5TernaryCoeff (x : RegionParameter)
    (hm3 : patternMass (regionTheta x) x.1 x.2.2.2 3 ≠ 0)
    (hm7 : patternMass (regionTheta x) x.1 x.2.2.2 7 ≠ 0) :
    ContinuousAt r5TernaryCoeff x := by
  unfold r5TernaryCoeff privacyIncrement privacyRatio
  apply ContinuousAt.mul
  · apply ContinuousAt.div
    · exact ((((Real.continuous_exp.comp continuous_snd.snd.snd).sub
        continuous_const).pow 2).mul (continuous_fst.pow 2)).continuousAt
    · exact ((Real.continuous_exp.comp continuous_snd.snd.snd).add
        continuous_const).continuousAt
    · positivity
  · apply ContinuousAt.add
    · exact continuousAt_const.div
        (continuous_patternMass_region 3).continuousAt hm3
    · exact continuousAt_const.div
        (continuous_patternMass_region 7).continuousAt hm7

/-- [The scaling factor in the five-output continuation argument](goal) is determined by [the displayed parameters](hyp:x). -/
noncomputable def r5Scale (x : RegionParameter) : ℝ :=
  Real.sqrt (r5TernaryCoeff x / r5BinaryCoeff x)

/-- [The selected directional branch for the five-output region](goal) is determined by [the displayed parameters](hyp:σ,x). -/
noncomputable def r5DirectionBranch (σ : ℝ) (x : RegionParameter) : ℝ :=
  (x.1 - σ * r5Scale x) / (1 - 2 * x.1 + σ * r5Scale x)

/-- Under [the supplied quantities and conditions](hyp:x), [the r5 scale sq assertion](goal) holds. For [the displayed quantities and conditions](hyp:hA,hC), these specify the stated inputs. -/
lemma r5Scale_sq (x : RegionParameter)
    (hA : 0 < r5BinaryCoeff x) (hC : 0 ≤ r5TernaryCoeff x) :
    r5Scale x ^ 2 = r5TernaryCoeff x / r5BinaryCoeff x := by
  unfold r5Scale
  rw [Real.sq_sqrt]
  exact div_nonneg hC hA.le

/-- Under the supplied quantities and conditions, the r5 direction branch objectives eq assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hσ,hA,hC,hden), [the r5 Direction Branch objectives eq](goal).

Under the stated assumptions, the r5 Direction Branch objectives eq. -/
lemma r5DirectionBranch_objectives_eq (x : RegionParameter) (σ : ℝ)
    (hσ : σ ^ 2 = 1)
    (hA : 0 < r5BinaryCoeff x) (hC : 0 ≤ r5TernaryCoeff x)
    (hden : 1 - 2 * x.1 + σ * r5Scale x ≠ 0) :
    r5BinaryCoeff x *
        (x.1 - (1 - 2 * x.1) * r5DirectionBranch σ x) ^ 2 =
      r5TernaryCoeff x * (r5DirectionBranch σ x + 1) ^ 2 := by
  have hs := r5Scale_sq x hA hC
  have hden' : 1 - x.1 * 2 + σ * r5Scale x ≠ 0 := by
    convert hden using 1 <;> ring
  have hleft :
      x.1 - (1 - 2 * x.1) * r5DirectionBranch σ x =
        σ * r5Scale x * (1 - x.1) /
          (1 - 2 * x.1 + σ * r5Scale x) := by
    unfold r5DirectionBranch
    field_simp [hden, hden']
    ring
  have hright : r5DirectionBranch σ x + 1 =
      (1 - x.1) / (1 - 2 * x.1 + σ * r5Scale x) := by
    unfold r5DirectionBranch
    field_simp [hden, hden']
    ring
  have hCA : r5BinaryCoeff x * r5Scale x ^ 2 = r5TernaryCoeff x := by
    rw [hs, mul_div_cancel₀ _ (ne_of_gt hA)]
  have hcore : r5BinaryCoeff x * σ ^ 2 * r5Scale x ^ 2 =
      r5TernaryCoeff x := by
    rw [hσ, mul_one]
    exact hCA
  rw [hleft, hright]
  field_simp [hden]
  rw [hcore]
  ring

/-- Under [the supplied quantities and conditions](hyp:x,t), [the exists r5 direction branch eq assertion](goal) holds. For [the displayed quantities and conditions](hyp:hp1,hA,hC,heq), these specify the stated inputs. -/
lemma exists_r5DirectionBranch_eq (x : RegionParameter) (t : ℝ)
    (hp1 : x.1 < 1)
    (hA : 0 < r5BinaryCoeff x) (hC : 0 ≤ r5TernaryCoeff x)
    (heq : r5BinaryCoeff x * (x.1 - (1 - 2 * x.1) * t) ^ 2 =
      r5TernaryCoeff x * (t + 1) ^ 2) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      1 - 2 * x.1 + σ * r5Scale x ≠ 0 ∧
      r5DirectionBranch σ x = t := by
  have hs := r5Scale_sq x hA hC
  have hCA : r5BinaryCoeff x * r5Scale x ^ 2 = r5TernaryCoeff x := by
    rw [hs, mul_div_cancel₀ _ (ne_of_gt hA)]
  have habsq : (x.1 - (1 - 2 * x.1) * t) ^ 2 =
      (r5Scale x * (t + 1)) ^ 2 := by
    rw [← hCA] at heq
    nlinarith [sq_nonneg (x.1 - (1 - 2 * x.1) * t),
      sq_nonneg (r5Scale x * (t + 1))]
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp habsq) with hrel | hrel
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · intro hden
      have hnum : x.1 - r5Scale x = 0 := by
        linear_combination hrel + t * hden
      nlinarith
    · unfold r5DirectionBranch
      rw [div_eq_iff (by
        intro hden
        have hnum : x.1 - r5Scale x = 0 := by
          linear_combination hrel + t * hden
        nlinarith : 1 - 2 * x.1 + 1 * r5Scale x ≠ 0)]
      nlinarith
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · intro hden
      have hnum : x.1 + r5Scale x = 0 := by
        linear_combination hrel + t * hden
      nlinarith
    · unfold r5DirectionBranch
      rw [div_eq_iff (by
        intro hden
        have hnum : x.1 + r5Scale x = 0 := by
          linear_combination hrel + t * hden
        nlinarith : 1 - 2 * x.1 + (-1) * r5Scale x ≠ 0)]
      nlinarith

/-- Under [the supplied quantities and conditions](hyp:x), [the continuous at r5 scale assertion](goal) holds. For [the displayed quantities and conditions](hyp:hA,hm3,hm5,hm7,hm8), these specify the stated inputs. -/
lemma continuousAt_r5Scale (x : RegionParameter)
    (hA : r5BinaryCoeff x ≠ 0)
    (hm3 : patternMass (regionTheta x) x.1 x.2.2.2 3 ≠ 0)
    (hm5 : patternMass (regionTheta x) x.1 x.2.2.2 5 ≠ 0)
    (hm7 : patternMass (regionTheta x) x.1 x.2.2.2 7 ≠ 0)
    (hm8 : patternMass (regionTheta x) x.1 x.2.2.2 8 ≠ 0) :
    ContinuousAt r5Scale x := by
  unfold r5Scale
  exact Real.continuous_sqrt.continuousAt.comp
    ((continuousAt_r5TernaryCoeff x hm3 hm7).div
      (continuousAt_r5BinaryCoeff x hm5 hm8) hA)

/-- Under [the supplied quantities and conditions](hyp:x), [the continuous at r5 direction branch assertion](goal) holds. For [the displayed quantities and conditions](hyp:hA,hm3,hm5,hm7,hm8,hden), these specify the stated inputs. -/
lemma continuousAt_r5DirectionBranch (x : RegionParameter) (σ : ℝ)
    (hA : r5BinaryCoeff x ≠ 0)
    (hm3 : patternMass (regionTheta x) x.1 x.2.2.2 3 ≠ 0)
    (hm5 : patternMass (regionTheta x) x.1 x.2.2.2 5 ≠ 0)
    (hm7 : patternMass (regionTheta x) x.1 x.2.2.2 7 ≠ 0)
    (hm8 : patternMass (regionTheta x) x.1 x.2.2.2 8 ≠ 0)
    (hden : 1 - 2 * x.1 + σ * r5Scale x ≠ 0) :
    ContinuousAt (r5DirectionBranch σ) x := by
  have hs := continuousAt_r5Scale x hA hm3 hm5 hm7 hm8
  unfold r5DirectionBranch
  apply ContinuousAt.div
  · exact continuous_fst.continuousAt.sub (continuousAt_const.mul hs)
  · exact (continuousAt_const.sub (continuousAt_const.mul continuous_fst.continuousAt)).add
      (continuousAt_const.mul hs)
  · exact hden

/-- [The mixture coordinate induced by a staircase weight](goal) is determined by [the displayed parameters](hyp:ε,α). -/
noncomputable def r5MixtureCoordinate (ε : ℝ) (α : StaircaseWeight) : ℝ :=
  (Real.exp ε + 1) * α 5

/-- Under the supplied quantities and conditions, the r5 supported feasible parameterization assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε,hα,hout), [the r5 supported feasible parameterization](goal).

Under the stated assumptions, the r5 supported feasible parameterization. -/
lemma r5_supported_feasible_parameterization (ε : ℝ) (hε : 0 < ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α)
    (hout : ∀ s ∉ r5Active, α s = 0) :
    α 5 = r5MixtureCoordinate ε α / (Real.exp ε + 1) ∧
    α 8 = r5MixtureCoordinate ε α / (Real.exp ε + 1) ∧
    α 2 = (1 - r5MixtureCoordinate ε α) / (Real.exp ε + 2) ∧
    α 3 = (1 - r5MixtureCoordinate ε α) / (Real.exp ε + 2) ∧
    α 7 = (1 - r5MixtureCoordinate ε α) / (Real.exp ε + 2) := by
  obtain ⟨h23, h37, h58, hnorm⟩ :=
    r5_supported_feasible_coordinates ε hε α hα hout
  have hd1 : Real.exp ε + 1 ≠ 0 := by positivity
  have hd2 : Real.exp ε + 2 ≠ 0 := by positivity
  have h5 : α 5 = r5MixtureCoordinate ε α / (Real.exp ε + 1) := by
    unfold r5MixtureCoordinate
    field_simp [hd1]
  have h2 : α 2 = (1 - r5MixtureCoordinate ε α) / (Real.exp ε + 2) := by
    unfold r5MixtureCoordinate
    apply (eq_div_iff hd2).2
    nlinarith
  exact ⟨h5, h58 ▸ h5, h2, h23 ▸ h2, h37 ▸ h23 ▸ h2⟩

/-- Under the supplied quantities and conditions, the r5 mixture coordinate mem ioo assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε,hα,hout,hpos), [the r5 Mixture Coordinate mem Ioo](goal).

Under the stated assumptions, the r5 Mixture Coordinate mem Ioo. -/
lemma r5MixtureCoordinate_mem_Ioo (ε : ℝ) (hε : 0 < ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α)
    (hout : ∀ s ∉ r5Active, α s = 0)
    (hpos : ∀ s ∈ r5Active, 0 < α s) :
    r5MixtureCoordinate ε α ∈ Set.Ioo 0 1 := by
  obtain ⟨_, _, h2, _, _⟩ :=
    r5_supported_feasible_parameterization ε hε α hα hout
  have hu0 : 0 < r5MixtureCoordinate ε α := by
    unfold r5MixtureCoordinate
    exact mul_pos (by positivity) (hpos 5 (by simp [r5Active]))
  have h2pos := hpos 2 (by simp [r5Active])
  have hd2 : 0 < Real.exp ε + 2 := by positivity
  rw [h2] at h2pos
  rcases div_pos_iff.mp h2pos with h | h
  · exact ⟨hu0, by linarith [h.1]⟩
  · linarith [h.2]

/-- [The derivative of the binary continuation component](goal) is determined by [the displayed parameters](hyp:x,t). -/
noncomputable def r5BinaryDerivative (x : RegionParameter) (t : ℝ) : ℝ :=
  (patternInformationSlope (regionTheta x) x.1 x.2.2.2 5 t +
    patternInformationSlope (regionTheta x) x.1 x.2.2.2 8 t) /
      (Real.exp x.2.2.2 + 1)

/-- [The derivative of the ternary continuation component](goal) is determined by [the displayed parameters](hyp:x,t). -/
noncomputable def r5TernaryDerivative (x : RegionParameter) (t : ℝ) : ℝ :=
  (patternInformationSlope (regionTheta x) x.1 x.2.2.2 2 t +
    patternInformationSlope (regionTheta x) x.1 x.2.2.2 3 t +
    patternInformationSlope (regionTheta x) x.1 x.2.2.2 7 t) /
      (Real.exp x.2.2.2 + 2)

-- keep: reusable mechanism-geometry certificate or refinement API for neighboring extremal analyses
/-- Under [the supplied quantities and conditions](hyp:x,t), [the r5 binary derivative eq assertion](goal) holds. For [the displayed quantities and conditions](hyp:hm5,hm8), these specify the stated inputs. -/
lemma r5BinaryDerivative_eq (x : RegionParameter) (t : ℝ)
    (hm5 : patternMass (regionTheta x) x.1 x.2.2.2 5 ≠ 0)
    (hm8 : patternMass (regionTheta x) x.1 x.2.2.2 8 ≠ 0) :
    r5BinaryDerivative x t =
      -2 * r5BinaryCoeff x * (1 - 2 * x.1) *
        (x.1 - (1 - 2 * x.1) * t) := by
  have hd : Real.exp x.2.2.2 + 1 ≠ 0 := by positivity
  unfold r5BinaryDerivative r5BinaryCoeff patternInformationSlope
  simp +decide [projectedGradient, patternGradient, patternContains,
    controlProb, direction, Fin.sum_univ_succ]
  field_simp [hm5, hm8, hd]
  ring

/-- Under [the supplied quantities and conditions](hyp:x,t), [the r5 ternary derivative eq assertion](goal) holds. For [the displayed quantities and conditions](hyp:hm3,hm7), these specify the stated inputs. -/
lemma r5TernaryDerivative_eq (x : RegionParameter) (t : ℝ)
    (hm3 : patternMass (regionTheta x) x.1 x.2.2.2 3 ≠ 0)
    (hm7 : patternMass (regionTheta x) x.1 x.2.2.2 7 ≠ 0) :
    r5TernaryDerivative x t = 2 * r5TernaryCoeff x * (t + 1) := by
  have hd : Real.exp x.2.2.2 + 2 ≠ 0 := by positivity
  unfold r5TernaryDerivative r5TernaryCoeff patternInformationSlope
  simp +decide [projectedGradient, patternGradient, patternContains,
    controlProb, direction, Fin.sum_univ_succ]
  field_simp [hm3, hm7, hd]

/-- Under the supplied quantities and conditions, the r5 stationarity eq mixture assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε,hα,hout,hstationary), [the r5 stationarity eq mixture](goal).

Under the stated assumptions, the r5 stationarity eq mixture. -/
lemma r5_stationarity_eq_mixture (x : RegionParameter) (α : StaircaseWeight)
    (hε : 0 < x.2.2.2) (hα : staircaseFeasible x.2.2.2 α)
    (hout : ∀ s ∉ r5Active, α s = 0) (t : ℝ)
    (hstationary :
      (∑ s : Fin 14, α s *
        patternInformationSlope (regionTheta x) x.1 x.2.2.2 s t) = 0) :
    r5MixtureCoordinate x.2.2.2 α * r5BinaryDerivative x t +
      (1 - r5MixtureCoordinate x.2.2.2 α) * r5TernaryDerivative x t = 0 := by
  obtain ⟨h5, h8, h2, h3, h7⟩ :=
    r5_supported_feasible_parameterization x.2.2.2 hε α hα hout
  have hd1 : Real.exp x.2.2.2 + 1 ≠ 0 := by positivity
  have hd2 : Real.exp x.2.2.2 + 2 ≠ 0 := by positivity
  unfold r5BinaryDerivative r5TernaryDerivative
  simp only [Fin.sum_univ_succ] at hstationary
  simp +decide [r5Active, hout] at hstationary
  rw [h2, h3, h5, h7, h8] at hstationary
  field_simp [hd1, hd2] at hstationary ⊢
  nlinarith

/-- Under [the supplied quantities and conditions](hyp:x), [the r5 ternary derivative ne zero of objectives eq assertion](goal) holds. For [the displayed quantities and conditions](hyp:t,hp1,hA,hC,hm3,hm7,heq), these specify the stated inputs. -/
lemma r5TernaryDerivative_ne_zero_of_objectives_eq (x : RegionParameter)
    (t : ℝ) (hp1 : x.1 < 1)
    (hA : 0 < r5BinaryCoeff x) (hC : 0 < r5TernaryCoeff x)
    (hm3 : patternMass (regionTheta x) x.1 x.2.2.2 3 ≠ 0)
    (hm7 : patternMass (regionTheta x) x.1 x.2.2.2 7 ≠ 0)
    (heq : r5BinaryCoeff x * (x.1 - (1 - 2 * x.1) * t) ^ 2 =
      r5TernaryCoeff x * (t + 1) ^ 2) :
    r5TernaryDerivative x t ≠ 0 := by
  rw [r5TernaryDerivative_eq x t hm3 hm7]
  intro hz
  have ht : t + 1 = 0 := by nlinarith
  rw [ht, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at heq
  have hpzero : x.1 - (1 - 2 * x.1) * t = 0 := by
    have hsquare : (x.1 - (1 - 2 * x.1) * t) ^ 2 = 0 :=
      (mul_eq_zero.mp heq).resolve_left (ne_of_gt hA)
    exact (sq_eq_zero_iff).mp hsquare
  nlinarith

/-- [the mixture stationarity solve assertion](goal) holds. For [the displayed quantities and conditions](hyp:hR,hstationary), these specify the stated inputs. -/
lemma mixture_stationarity_solve {u P R : ℝ}
    (hR : R ≠ 0) (hstationary : u * P + (1 - u) * R = 0) :
    P - R ≠ 0 ∧ u = -R / (P - R) := by
  have hden : P - R ≠ 0 := by
    intro h
    have : P = R := by linarith
    rw [this] at hstationary
    apply hR
    linear_combination hstationary
  refine ⟨hden, ?_⟩
  apply (eq_div_iff hden).2
  nlinarith

/-- [The continued mixture coordinate for the five-output region](goal) is determined by [the displayed parameters](hyp:σ,x). -/
noncomputable def r5ContinuedMixture (σ : ℝ) (x : RegionParameter) : ℝ :=
  let t := r5DirectionBranch σ x;
  -r5TernaryDerivative x t /
    (r5BinaryDerivative x t - r5TernaryDerivative x t)

/-- Under the supplied quantities and conditions, the r5 continued mixture eq assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:ht,hε,hα,hout,hstationary,hR), [the r5 Continued Mixture eq](goal).

Under the stated assumptions, the r5 Continued Mixture eq. -/
lemma r5ContinuedMixture_eq (x : RegionParameter) (α : StaircaseWeight)
    (t σ : ℝ) (ht : r5DirectionBranch σ x = t)
    (hε : 0 < x.2.2.2) (hα : staircaseFeasible x.2.2.2 α)
    (hout : ∀ s ∉ r5Active, α s = 0)
    (hstationary :
      (∑ s : Fin 14, α s *
        patternInformationSlope (regionTheta x) x.1 x.2.2.2 s t) = 0)
    (hR : r5TernaryDerivative x t ≠ 0) :
    r5ContinuedMixture σ x = r5MixtureCoordinate x.2.2.2 α := by
  have hmix := r5_stationarity_eq_mixture x α hε hα hout t hstationary
  obtain ⟨_, hu⟩ := mixture_stationarity_solve hR hmix
  unfold r5ContinuedMixture
  rw [ht]
  exact hu.symm

/-- Under [the supplied quantities and conditions](hyp:x), [the continuous at r5 binary derivative comp assertion](goal) holds. For [the displayed quantities and conditions](hyp:t,ht,hm5,hm8), these specify the stated inputs. -/
lemma continuousAt_r5BinaryDerivative_comp (x : RegionParameter)
    (t : RegionParameter → ℝ) (ht : ContinuousAt t x)
    (hm5 : patternMass (regionTheta x) x.1 x.2.2.2 5 ≠ 0)
    (hm8 : patternMass (regionTheta x) x.1 x.2.2.2 8 ≠ 0) :
    ContinuousAt (fun y ↦ r5BinaryDerivative y (t y)) x := by
  unfold r5BinaryDerivative
  apply ContinuousAt.div
  · exact (continuousAt_patternInformationSlope_region 5 t x ht hm5).add
      (continuousAt_patternInformationSlope_region 8 t x ht hm8)
  · exact ((Real.continuous_exp.comp continuous_snd.snd.snd).add
      continuous_const).continuousAt
  · positivity

/-- Under [the supplied quantities and conditions](hyp:x), [the continuous at r5 ternary derivative comp assertion](goal) holds. For [the displayed quantities and conditions](hyp:t,ht,hm2,hm3,hm7), these specify the stated inputs. -/
lemma continuousAt_r5TernaryDerivative_comp (x : RegionParameter)
    (t : RegionParameter → ℝ) (ht : ContinuousAt t x)
    (hm2 : patternMass (regionTheta x) x.1 x.2.2.2 2 ≠ 0)
    (hm3 : patternMass (regionTheta x) x.1 x.2.2.2 3 ≠ 0)
    (hm7 : patternMass (regionTheta x) x.1 x.2.2.2 7 ≠ 0) :
    ContinuousAt (fun y ↦ r5TernaryDerivative y (t y)) x := by
  unfold r5TernaryDerivative
  apply ContinuousAt.div
  · exact ((continuousAt_patternInformationSlope_region 2 t x ht hm2).add
      (continuousAt_patternInformationSlope_region 3 t x ht hm3)).add
        (continuousAt_patternInformationSlope_region 7 t x ht hm7)
  · exact ((Real.continuous_exp.comp continuous_snd.snd.snd).add
      continuous_const).continuousAt
  · positivity

/-- Under [the supplied quantities and conditions](hyp:x), [the continuous at r5 continued mixture assertion](goal) holds. For [the displayed quantities and conditions](hyp:ht,hm2,hm3,hm5,hm7,hm8,hden), these specify the stated inputs. -/
lemma continuousAt_r5ContinuedMixture (x : RegionParameter) (σ : ℝ)
    (ht : ContinuousAt (r5DirectionBranch σ) x)
    (hm2 : patternMass (regionTheta x) x.1 x.2.2.2 2 ≠ 0)
    (hm3 : patternMass (regionTheta x) x.1 x.2.2.2 3 ≠ 0)
    (hm5 : patternMass (regionTheta x) x.1 x.2.2.2 5 ≠ 0)
    (hm7 : patternMass (regionTheta x) x.1 x.2.2.2 7 ≠ 0)
    (hm8 : patternMass (regionTheta x) x.1 x.2.2.2 8 ≠ 0)
    (hden : r5BinaryDerivative x (r5DirectionBranch σ x) -
      r5TernaryDerivative x (r5DirectionBranch σ x) ≠ 0) :
    ContinuousAt (r5ContinuedMixture σ) x := by
  have hP := continuousAt_r5BinaryDerivative_comp x
    (r5DirectionBranch σ) ht hm5 hm8
  have hR := continuousAt_r5TernaryDerivative_comp x
    (r5DirectionBranch σ) ht hm2 hm3 hm7
  unfold r5ContinuedMixture
  exact hR.neg.div (hP.sub hR) hden

/-- [The staircase weight reconstructed from a mixture coordinate](goal) is determined by [the displayed parameters](hyp:ε,u). -/
noncomputable def r5WeightFromCoordinate (ε u : ℝ) : StaircaseWeight :=
  fun s ↦ if s = 5 ∨ s = 8 then u / (Real.exp ε + 1)
    else if s = 2 ∨ s = 3 ∨ s = 7 then (1 - u) / (Real.exp ε + 2)
    else 0

/-- Under [the supplied quantities and conditions](hyp:u), [the r5 weight from coordinate feasible assertion](goal) holds. -/
lemma r5WeightFromCoordinate_feasible (ε u : ℝ) :
    staircaseFeasible ε (r5WeightFromCoordinate ε u) ↔ u ∈ Set.Icc 0 1 := by
  have hd1 : 0 < Real.exp ε + 1 := by positivity
  have hd2 : 0 < Real.exp ε + 2 := by positivity
  constructor
  · intro h
    have h5 := h.1 5
    have h2 := h.1 2
    simp +decide [r5WeightFromCoordinate] at h5 h2
    constructor
    · rcases div_nonneg_iff.mp h5 with hpos | hneg
      · exact hpos.1
      · exact False.elim ((not_le_of_gt hd1) hneg.2)
    · have hn : 0 ≤ 1 - u := by
        rcases div_nonneg_iff.mp h2 with hpos | hneg
        · exact hpos.1
        · exact False.elim ((not_le_of_gt hd2) hneg.2)
      linarith
  · rintro ⟨hu0, hu1⟩
    constructor
    · intro s
      unfold r5WeightFromCoordinate
      split_ifs <;> positivity
    · intro j
      rcases j with ⟨j, hj⟩
      interval_cases j <;>
        simp +decide [staircaseMatrix, r5WeightFromCoordinate, patternRay,
          patternContains, privacyIncrement, privacyRatio, Fin.sum_univ_succ] <;>
        field_simp <;> ring

-- keep: reusable mechanism-geometry certificate or refinement API for neighboring extremal analyses
/-- Under the supplied quantities and conditions, the r5 weight from coordinate eq assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε,hα,hout), [the r5 Weight From Coordinate eq](goal).

Under the stated assumptions, the r5 Weight From Coordinate eq. -/
lemma r5WeightFromCoordinate_eq (ε : ℝ) (hε : 0 < ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α)
    (hout : ∀ s ∉ r5Active, α s = 0) :
    r5WeightFromCoordinate ε (r5MixtureCoordinate ε α) = α := by
  obtain ⟨h5, h8, h2, h3, h7⟩ :=
    r5_supported_feasible_parameterization ε hε α hα hout
  funext s
  rcases s with ⟨s, hs⟩
  interval_cases s <;>
    simp_all +decide [r5WeightFromCoordinate, r5Active]

/-- Under [the supplied quantities and conditions](hyp:u,hu), [the r5 weight from coordinate active assertion](goal) holds. -/
lemma r5WeightFromCoordinate_active (ε u : ℝ) (hu : u ∈ Set.Ioo 0 1) :
    activeSupport (r5WeightFromCoordinate ε u) r5Active := by
  rcases hu with ⟨hu0, hu1⟩
  intro s
  rcases s with ⟨s, hs⟩
  interval_cases s <;>
    simp +decide [r5WeightFromCoordinate, r5Active] <;>
      try (constructor <;> positivity) <;> try positivity

/-- Under [the supplied quantities and conditions](hyp:u,hu), [the r5 weight from coordinate pos assertion](goal) holds. -/
lemma r5WeightFromCoordinate_pos (ε u : ℝ) (hu : u ∈ Set.Ioo 0 1) :
    ∀ s ∈ r5Active, 0 < r5WeightFromCoordinate ε u s := by
  rcases hu with ⟨hu0, hu1⟩
  intro s hs
  rcases s with ⟨s, hslt⟩
  interval_cases s <;>
    simp_all +decide [r5WeightFromCoordinate, r5Active] <;> try positivity

/-- Under [the supplied quantities and conditions](hyp:x,u,t), [the r5 weight from coordinate stationarity assertion](goal) holds. -/
lemma r5WeightFromCoordinate_stationarity (x : RegionParameter) (u t : ℝ) :
    (∑ s : Fin 14, r5WeightFromCoordinate x.2.2.2 u s *
      patternInformationSlope (regionTheta x) x.1 x.2.2.2 s t) =
    u * r5BinaryDerivative x t + (1 - u) * r5TernaryDerivative x t := by
  have hd1 : Real.exp x.2.2.2 + 1 ≠ 0 := by positivity
  have hd2 : Real.exp x.2.2.2 + 2 ≠ 0 := by positivity
  unfold r5BinaryDerivative r5TernaryDerivative
  simp +decide [r5WeightFromCoordinate, Fin.sum_univ_succ]
  field_simp [hd1, hd2]
  ring

/-- Under [the supplied quantities and conditions](hyp:x), [the r5 continued weight stationary assertion](goal) holds. For [the displayed quantities and conditions](hyp:hden), these specify the stated inputs. -/
lemma r5ContinuedWeight_stationary (x : RegionParameter) (σ : ℝ)
    (hden : r5BinaryDerivative x (r5DirectionBranch σ x) -
      r5TernaryDerivative x (r5DirectionBranch σ x) ≠ 0) :
    (∑ s : Fin 14,
      r5WeightFromCoordinate x.2.2.2 (r5ContinuedMixture σ x) s *
        patternInformationSlope (regionTheta x) x.1 x.2.2.2 s
          (r5DirectionBranch σ x)) = 0 := by
  rw [r5WeightFromCoordinate_stationarity]
  unfold r5ContinuedMixture
  field_simp [hden]
  ring

/-- [The target vector in the five-output dual system](goal) is determined by [the displayed parameters](hyp:t,x). -/
noncomputable def r5DualTarget (t : RegionParameter → ℝ)
    (x : RegionParameter) : Fin 4 → ℝ :=
  fun i ↦ patternInformation (regionTheta x) x.1 x.2.2.2
    (r5DualMask i) (t x)

/-- Under [the supplied quantities and conditions](hyp:t), [the continuous at r5 dual target assertion](goal) holds. For [the displayed quantities and conditions](hyp:x,ht,hm), these specify the stated inputs. -/
lemma continuousAt_r5DualTarget (t : RegionParameter → ℝ)
    (x : RegionParameter) (ht : ContinuousAt t x)
    (hm : ∀ s : Fin 14,
      patternMass (regionTheta x) x.1 x.2.2.2 s ≠ 0) :
    ContinuousAt (r5DualTarget t) x := by
  apply continuousAt_pi.mpr
  intro i
  exact continuousAt_patternInformation_region (r5DualMask i) t x ht
    (hm (r5DualMask i))

/-- Under the supplied quantities and conditions, the exists local r5 dual assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε,ht,hm,hactive), [the exists local r5 Dual](goal).

Under the stated assumptions, the exists local r5 Dual. -/
lemma exists_local_r5Dual (x : RegionParameter) (t : RegionParameter → ℝ)
    (η0 : Fin 4 → ℝ) (hε : 0 < x.2.2.2)
    (ht : ContinuousAt t x)
    (hm : ∀ s : Fin 14,
      patternMass (regionTheta x) x.1 x.2.2.2 s ≠ 0)
    (hactive : ∀ s ∈ r5Active, dualRay x.2.2.2 η0 s =
      patternInformation (regionTheta x) x.1 x.2.2.2 s (t x)) :
    ∃ η : RegionParameter → Fin 4 → ℝ,
      ContinuousAt η x ∧ η x = η0 ∧
      ∀ᶠ y in nhds x,
        Matrix.mulVec (r5DualMatrix y) (η y) = r5DualTarget t y := by
  have hbase : Matrix.mulVec (r5DualMatrix x) η0 = r5DualTarget t x := by
    funext i
    have hi := hactive (r5DualMask i) (by
      fin_cases i <;> simp [r5DualMask, r5Active])
    simpa [r5DualMatrix, r5DualTarget, Matrix.mulVec, dotProduct,
      dualRay, mul_comm] using hi
  let η := Causalean.Mathlib.LinearAlgebra.anchoredSolution
    r5DualMatrix (r5DualTarget t) (r5DualRightInverse x.2.2.2) η0
  obtain ⟨hcont, hbaseη, hev⟩ :=
    exists_eventually_anchoredSolution_of_rightInverse
      r5DualMatrix (r5DualTarget t) (r5DualRightInverse x.2.2.2)
      x η0 continuous_r5DualMatrix.continuousAt
      (continuousAt_r5DualTarget t x ht hm)
      (r5DualMatrix_mul_rightInverse x hε) hbase
  exact ⟨η, hcont, hbaseη, hev⟩

/-- Under [the supplied quantities and conditions](hyp:x,t), [the r5 fifth dual eq assertion](goal) holds. For [the displayed quantities and conditions](hyp:hobj,h2,h3,h5,h7), these specify the stated inputs. -/
lemma r5_fifthDual_eq (x : RegionParameter) (η : Fin 4 → ℝ) (t : ℝ)
    (hobj : r5BinaryObjective x t = r5TernaryObjective x t)
    (h2 : dualRay x.2.2.2 η 2 =
      patternInformation (regionTheta x) x.1 x.2.2.2 2 t)
    (h3 : dualRay x.2.2.2 η 3 =
      patternInformation (regionTheta x) x.1 x.2.2.2 3 t)
    (h5 : dualRay x.2.2.2 η 5 =
      patternInformation (regionTheta x) x.1 x.2.2.2 5 t)
    (h7 : dualRay x.2.2.2 η 7 =
      patternInformation (regionTheta x) x.1 x.2.2.2 7 t) :
    dualRay x.2.2.2 η 8 =
      patternInformation (regionTheta x) x.1 x.2.2.2 8 t := by
  have hd1 : Real.exp x.2.2.2 + 1 ≠ 0 := by positivity
  have hd2 : Real.exp x.2.2.2 + 2 ≠ 0 := by positivity
  have hdualavg :
      (dualRay x.2.2.2 η 5 + dualRay x.2.2.2 η 8) /
          (Real.exp x.2.2.2 + 1) =
        (dualRay x.2.2.2 η 2 + dualRay x.2.2.2 η 3 +
          dualRay x.2.2.2 η 7) / (Real.exp x.2.2.2 + 2) := by
    simp +decide [dualRay, patternRay, patternContains, privacyIncrement,
      privacyRatio, Fin.sum_univ_succ]
    field_simp [hd1, hd2]
    ring
  unfold r5BinaryObjective r5TernaryObjective at hobj
  rw [← h5, ← h2, ← h3, ← h7] at hobj
  field_simp [hd1, hd2] at hobj hdualavg
  have hprod : (Real.exp x.2.2.2 + 2) *
      (patternInformation (regionTheta x) x.1 x.2.2.2 8 t -
        dualRay x.2.2.2 η 8) = 0 := by
    linear_combination hobj - hdualavg
  have hz := (mul_eq_zero.mp hprod).resolve_left hd2
  linarith

/-- The five active dual equalities force the two normalized constituent
objectives to agree. For [the displayed inputs and conditions](hyp:x), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:t,hdual), these specify the stated inputs. -/
lemma r5_objectives_eq_of_activeDual (x : RegionParameter)
    (η : Fin 4 → ℝ) (t : ℝ)
    (hdual : ∀ s ∈ r5Active,
      dualRay x.2.2.2 η s =
        patternInformation (regionTheta x) x.1 x.2.2.2 s t) :
    r5BinaryObjective x t = r5TernaryObjective x t := by
  have hr1 : Real.exp x.2.2.2 + 1 ≠ 0 := by positivity
  have hr2 : Real.exp x.2.2.2 + 2 ≠ 0 := by positivity
  have h2 := hdual 2 (by simp [r5Active])
  have h3 := hdual 3 (by simp [r5Active])
  have h5 := hdual 5 (by simp [r5Active])
  have h7 := hdual 7 (by simp [r5Active])
  have h8 := hdual 8 (by simp [r5Active])
  unfold r5BinaryObjective r5TernaryObjective
  rw [← h5, ← h8, ← h2, ← h3, ← h7]
  simp +decide [dualRay, patternRay, patternContains, privacyIncrement,
    privacyRatio, Fin.sum_univ_succ]
  field_simp [hr1, hr2]
  ring

end CausalSmith.Stat.LdpAteEfficiencySurface

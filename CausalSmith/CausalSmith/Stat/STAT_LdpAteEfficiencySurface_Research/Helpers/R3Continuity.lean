module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.RegionOpenness
public import Causalean.Mathlib.LinearAlgebra.ContinuousSolution

/-! # Continuous certificate data for the three-output region

This file supplies the canonical stationarity direction, continuity of the
rational information data on the interior, and an explicit right inverse for
the three active dual-ray equations. It also gives the local form of the
promoted anchored linear solver needed when coefficients are only continuous
at the certificate point.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface
open scoped BigOperators

/-- [The scalar score direction used in the three-output region](goal) is determined by [the displayed parameters](hyp:p,μ0,μ1,ε). -/
noncomputable def r3Direction (p μ0 μ1 ε : ℝ) : ℝ :=
  -r3Stationarity p μ0 μ1 ε 0 / r3StationarityCoeff p μ0 μ1 ε

/-- Under [the supplied quantities and conditions](hyp:p,t), [the r3 stationarity affine assertion](goal) holds. -/
lemma r3Stationarity_affine (p μ0 μ1 ε t : ℝ) :
    r3Stationarity p μ0 μ1 ε t =
      r3Stationarity p μ0 μ1 ε 0 +
        t * r3StationarityCoeff p μ0 μ1 ε := by
  unfold r3StationarityCoeff r3Stationarity
  rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp [patternInformationSlope, projectedGradient, direction,
    Fin.sum_univ_succ]
  ring

/-- Under [the supplied quantities and conditions](hyp:p), [the r3 stationarity r3 direction eq zero assertion](goal) holds. For [the displayed quantities and conditions](hyp:hcoeff), these specify the stated inputs. -/
lemma r3Stationarity_r3Direction_eq_zero (p μ0 μ1 ε : ℝ)
    (hcoeff : r3StationarityCoeff p μ0 μ1 ε ≠ 0) :
    r3Stationarity p μ0 μ1 ε (r3Direction p μ0 μ1 ε) = 0 := by
  rw [r3Stationarity_affine]
  unfold r3Direction
  field_simp
  ring

end CausalSmith.Stat.LdpAteEfficiencySurface

namespace CausalSmith.Stat.LdpAteEfficiencySurface

/-- the region parameter is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The Region Parameter](goal) is the displayed object. -/
abbrev RegionParameter := ℝ × ℝ × ℝ × ℝ

/-- For [the supplied quantities and conditions](hyp:x), the [region theta](goal) is the mathematical object specified below. -/
def regionTheta (x : RegionParameter) : TrialParameter :=
  fun k => if k = 0 then x.2.1 else x.2.2.1

/-- Under [the supplied quantities and conditions](hyp:s,j), [the continuous pattern ray region assertion](goal) holds. -/
lemma continuous_patternRay_region (s : Fin 14) (j : Fin 4) :
    Continuous (fun x : RegionParameter => patternRay x.2.2.2 s j) := by
  unfold patternRay privacyIncrement privacyRatio
  by_cases h : patternContains s j
  · simp [h]
    fun_prop
  · simp [h]
    exact continuous_const

/-- Under [the supplied quantities and conditions](hyp:s), [the continuous pattern mass region assertion](goal) holds. -/
lemma continuous_patternMass_region (s : Fin 14) :
    Continuous (fun x : RegionParameter =>
      patternMass (regionTheta x) x.1 x.2.2.2 s) := by
  unfold patternMass
  apply continuous_finsetSum
  intro j _
  apply Continuous.mul
  · fin_cases j <;> simp +decide [regionTheta, piTheta, controlProb] <;> fun_prop
  · exact continuous_patternRay_region s j

/-- Under [the supplied quantities and conditions](hyp:s), [the continuous at projected gradient region assertion](goal) holds. For [the displayed quantities and conditions](hyp:t,x,ht), these specify the stated inputs. -/
lemma continuousAt_projectedGradient_region (s : Fin 14)
    (t : RegionParameter → ℝ) (x : RegionParameter)
    (ht : ContinuousAt t x) :
    ContinuousAt (fun y : RegionParameter =>
      projectedGradient y.1 y.2.2.2 s (t y)) x := by
  simp +decide [projectedGradient, patternGradient, direction,
    privacyIncrement, privacyRatio, controlProb, Fin.sum_univ_succ]
  fun_prop

/-- Under [the supplied quantities and conditions](hyp:s), [the continuous at pattern information region assertion](goal) holds. For [the displayed quantities and conditions](hyp:t,x,ht,hm), these specify the stated inputs. -/
lemma continuousAt_patternInformation_region (s : Fin 14)
    (t : RegionParameter → ℝ) (x : RegionParameter)
    (ht : ContinuousAt t x)
    (hm : patternMass (regionTheta x) x.1 x.2.2.2 s ≠ 0) :
    ContinuousAt (fun y : RegionParameter =>
      patternInformation (regionTheta y) y.1 y.2.2.2 s (t y)) x := by
  unfold patternInformation
  apply ContinuousAt.div
  · exact (continuousAt_projectedGradient_region s t x ht).pow 2
  · exact (continuous_patternMass_region s).continuousAt
  · exact hm

/-- Under [the supplied quantities and conditions](hyp:s), [the continuous at projected score region assertion](goal) holds. For [the displayed quantities and conditions](hyp:t,x,ht,hm), these specify the stated inputs. -/
lemma continuousAt_projectedScore_region (s : Fin 14)
    (t : RegionParameter → ℝ) (x : RegionParameter)
    (ht : ContinuousAt t x)
    (hm : patternMass (regionTheta x) x.1 x.2.2.2 s ≠ 0) :
    ContinuousAt (fun y : RegionParameter =>
      projectedScore (regionTheta y) y.1 y.2.2.2 s (t y)) x := by
  unfold projectedScore
  exact (continuousAt_projectedGradient_region s t x ht).div
    (continuous_patternMass_region s).continuousAt hm

end CausalSmith.Stat.LdpAteEfficiencySurface

namespace CausalSmith.Stat.LdpAteEfficiencySurface

/-- Under [the supplied quantities and conditions](hyp:s), [the continuous at pattern information slope region assertion](goal) holds. For [the displayed quantities and conditions](hyp:t,x,ht,hm), these specify the stated inputs. -/
lemma continuousAt_patternInformationSlope_region (s : Fin 14)
    (t : RegionParameter → ℝ) (x : RegionParameter)
    (ht : ContinuousAt t x)
    (hm : patternMass (regionTheta x) x.1 x.2.2.2 s ≠ 0) :
    ContinuousAt (fun y : RegionParameter =>
      patternInformationSlope (regionTheta y) y.1 y.2.2.2 s (t y)) x := by
  unfold patternInformationSlope
  apply ContinuousAt.div
  · apply ContinuousAt.mul
    · apply ContinuousAt.mul continuousAt_const
        (continuousAt_projectedGradient_region s t x ht)
    · simp +decide [patternGradient, privacyIncrement, privacyRatio,
        controlProb]
      fun_prop
  · exact (continuous_patternMass_region s).continuousAt
  · exact hm

/-- Under [the supplied quantities and conditions](hyp:t,x), [the continuous at r3 stationarity region assertion](goal) holds. For [the displayed quantities and conditions](hyp:ht,hm), these specify the stated inputs. -/
lemma continuousAt_r3Stationarity_region
    (t : RegionParameter → ℝ) (x : RegionParameter)
    (ht : ContinuousAt t x)
    (hm : ∀ s : Fin 14,
      patternMass (regionTheta x) x.1 x.2.2.2 s ≠ 0) :
    ContinuousAt (fun y : RegionParameter =>
      r3Stationarity y.1 y.2.1 y.2.2.1 y.2.2.2 (t y)) x := by
  unfold r3Stationarity
  let f := fun s : Fin 14 => fun y : RegionParameter =>
    r3Weight y.2.2.2 s *
      patternInformationSlope (regionTheta y) y.1 y.2.2.2 s (t y)
  have hf (s : Fin 14) : ContinuousAt (f s) x := by
    apply ContinuousAt.mul
    · unfold r3Weight
      by_cases hs : s ∈ ({0, 5, 7} : Finset (Fin 14))
      · simp [hs]
        exact (((Real.continuous_exp.comp continuous_snd.snd.snd).add
          continuous_const).continuousAt.inv₀
            (show Real.exp x.2.2.2 + 2 ≠ 0 by positivity))
      · simp [hs]
        exact continuousAt_const
    · exact continuousAt_patternInformationSlope_region s t x ht (hm s)
  have hsum : ∀ S : Finset (Fin 14),
      ContinuousAt (fun y => ∑ s ∈ S, f s y) x := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : RegionParameter => (0 : ℝ)) x)
    | @insert a S ha ih =>
        simp only [Finset.sum_insert ha]
        change ContinuousAt (fun y => f a y + ∑ s ∈ S, f s y) x
        exact (hf a).add ih
  change ContinuousAt (fun y => ∑ s : Fin 14,
    r3Weight y.2.2.2 s *
      patternInformationSlope (regionTheta y) y.1 y.2.2.2 s (t y)) x
  simpa only [f] using hsum Finset.univ

/-- Under [the supplied quantities and conditions](hyp:x), [the continuous at r3 direction region assertion](goal) holds. For [the displayed quantities and conditions](hyp:hm,hc), these specify the stated inputs. -/
lemma continuousAt_r3Direction_region (x : RegionParameter)
    (hm : ∀ s : Fin 14,
      patternMass (regionTheta x) x.1 x.2.2.2 s ≠ 0)
    (hc : r3StationarityCoeff x.1 x.2.1 x.2.2.1 x.2.2.2 ≠ 0) :
    ContinuousAt (fun y : RegionParameter =>
      r3Direction y.1 y.2.1 y.2.2.1 y.2.2.2) x := by
  unfold r3Direction r3StationarityCoeff
  apply ContinuousAt.div
  · exact (continuousAt_r3Stationarity_region (fun _ => 0) x continuousAt_const hm).neg
  · exact (continuousAt_r3Stationarity_region (fun _ => 1) x continuousAt_const hm).sub
      (continuousAt_r3Stationarity_region (fun _ => 0) x continuousAt_const hm)
  · exact hc

end CausalSmith.Stat.LdpAteEfficiencySurface

namespace CausalSmith.Stat.LdpAteEfficiencySurface

/-- For [the supplied quantities and conditions](hyp:i), the [r3 mask](goal) is the mathematical object specified below. -/
def r3Mask (i : Fin 3) : Fin 14 := ![0, 5, 7] i

/-- [The dual constraint matrix for the three-output region](goal) is determined by [the displayed parameters](hyp:x). -/
noncomputable def r3DualMatrix (x : RegionParameter) : Matrix (Fin 3) (Fin 4) ℝ :=
  fun i j => patternRay x.2.2.2 (r3Mask i) j

/-- [A right inverse for the three-output dual matrix](goal) is determined by [the displayed parameters](hyp:ε). -/
noncomputable def r3DualRightInverse (ε : ℝ) : Matrix (Fin 4) (Fin 3) ℝ :=
  let r := Real.exp ε
  let den := (r - 1) * (r + 2)
  fun j i =>
    if j = 2 then 0
    else if (j = 0 ∧ i = 0) ∨ (j = 1 ∧ i = 1) ∨ (j = 3 ∧ i = 2)
      then (r + 1) / den else -1 / den

/-- Under the supplied quantities and conditions, the r3 dual matrix mul right inverse assertion holds. Under [the stated assumptions](hyp:hε), [the r3 Dual Matrix mul right Inverse](goal).

Under the stated assumptions, the r3 Dual Matrix mul right Inverse. -/
lemma r3DualMatrix_mul_rightInverse (x : RegionParameter) (hε : 0 < x.2.2.2) :
    r3DualMatrix x * r3DualRightInverse x.2.2.2 = 1 := by
  have hr : 1 < Real.exp x.2.2.2 := (Real.one_lt_exp_iff).2 hε
  have hd : (Real.exp x.2.2.2 - 1) * (Real.exp x.2.2.2 + 2) ≠ 0 := by
    positivity
  have hd1 : Real.exp x.2.2.2 - 1 ≠ 0 := by positivity
  ext i k
  change (∑ j : Fin 4, r3DualMatrix x i j *
    r3DualRightInverse x.2.2.2 j k) = (1 : Matrix (Fin 3) (Fin 3) ℝ) i k
  fin_cases i <;> fin_cases k <;>
    simp +decide [r3DualMatrix, r3DualRightInverse, r3Mask,
      patternRay, patternContains, privacyIncrement, privacyRatio,
      Fin.sum_univ_succ] <;> field_simp [hd, hd1] <;> ring

/-- [the continuous r3 dual matrix assertion](goal) holds. -/
lemma continuous_r3DualMatrix : Continuous r3DualMatrix := by
  apply continuous_matrix
  intro i j
  exact continuous_patternRay_region (r3Mask i) j

end CausalSmith.Stat.LdpAteEfficiencySurface

namespace CausalSmith.Stat.LdpAteEfficiencySurface
open Causalean.Mathlib.LinearAlgebra Filter

/-- the exists eventually anchored solution of right inverse assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hA,hb,hR,hy), [the exists eventually anchored Solution of right Inverse](goal).

Under the stated assumptions, the exists eventually anchored Solution of right Inverse. -/
lemma exists_eventually_anchoredSolution_of_rightInverse
    {X : Type*} [TopologicalSpace X] {k n : ℕ}
    (A : X → Matrix (Fin k) (Fin n) ℝ) (b : X → Fin k → ℝ)
    (R₀ : Matrix (Fin n) (Fin k) ℝ) (x₀ : X) (y₀ : Fin n → ℝ)
    (hA : ContinuousAt A x₀) (hb : ContinuousAt b x₀)
    (hR : A x₀ * R₀ = 1) (hy : Matrix.mulVec (A x₀) y₀ = b x₀) :
    let y := anchoredSolution A b R₀ y₀
    ContinuousAt y x₀ ∧ y x₀ = y₀ ∧
      ∀ᶠ x in nhds x₀, Matrix.mulVec (A x) (y x) = b x := by
  dsimp only
  have hM : ContinuousAt (fun x => A x * R₀) x₀ :=
    (continuous_fst.matrix_mul continuous_snd).continuousAt.comp
      (hA.prodMk continuousAt_const)
  have hdet : ContinuousAt (fun x => (A x * R₀).det) x₀ :=
    continuous_id.matrix_det.continuousAt.comp hM
  have hdet0 : (A x₀ * R₀).det ≠ 0 := by rw [hR]; simp
  have hev : ∀ᶠ x in nhds x₀, (A x * R₀).det ≠ 0 :=
    hdet.eventually_ne hdet0
  have hInv : ContinuousAt (fun x => (A x * R₀)⁻¹) x₀ := by
    have hringInv : ContinuousAt Ring.inverse (A x₀ * R₀).det := by
      rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv]
      exact continuousAt_inv₀ hdet0
    exact ContinuousAt.comp' (f := fun x => A x * R₀)
      (continuousAt_matrix_inv (A x₀ * R₀) hringInv)
      hM
  have hResidual : ContinuousAt (fun x => b x - Matrix.mulVec (A x) y₀) x₀ :=
    hb.sub ((continuous_fst.matrix_mulVec continuous_snd).continuousAt.comp
      (hA.prodMk continuousAt_const))
  have hInner : ContinuousAt
      (fun x => Matrix.mulVec (A x * R₀)⁻¹ (b x - Matrix.mulVec (A x) y₀)) x₀ :=
    (continuous_fst.matrix_mulVec continuous_snd).continuousAt.comp
      (hInv.prodMk hResidual)
  have hcont : ContinuousAt (anchoredSolution A b R₀ y₀) x₀ := by
    change ContinuousAt
      (fun x => y₀ + Matrix.mulVec R₀
        (Matrix.mulVec (A x * R₀)⁻¹ (b x - Matrix.mulVec (A x) y₀))) x₀
    exact continuousAt_const.add
      ((continuous_fst.matrix_mulVec continuous_snd).continuousAt.comp
        (continuousAt_const.prodMk hInner))
  refine ⟨hcont, anchoredSolution_at_base A b R₀ y₀ x₀ hR hy, ?_⟩
  filter_upwards [hev] with x hx
  exact anchoredSolution_eq_of_det_ne_zero A b R₀ y₀ x hx

end CausalSmith.Stat.LdpAteEfficiencySurface

module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Refinement
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.QuadraticConvexity
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Topology.Semicontinuity.Basic

/-! # Exact finite staircase oracle

The contrast variance is the information-matrix quadratic solution value,
with infinity when the contrast is outside the information range. The theorem
states both the arbitrary-channel comparison and the finite saddle identity. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- the [contrast in range](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:I), these specify the stated inputs. -/
def contrastInRange (I : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ v : TrialParameter, I.mulVec v = contrastVector

open Classical in
/-- the [contrast variance](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:I), these specify the stated inputs. -/
def contrastVariance (I : Matrix (Fin 2) (Fin 2) ℝ) : ℝ≥0∞ :=
  if contrastInRange I then
    ENNReal.ofReal (sInf {u : ℝ | ∃ v : TrialParameter,
      I.mulVec v = contrastVector ∧
      u = ∑ k : Fin 2, contrastVector k * v k})
  else ⊤

/-- the feasible set is the mathematical object specified below. [The feasible Set](goal) is determined by [the displayed parameters](hyp:ε). -/
def feasibleSet (ε : ℝ) : Set StaircaseWeight :=
  {α | staircaseFeasible ε α}

-- @node: piTheta_pos_interior
/-- Under the supplied quantities and conditions, the pi theta pos interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the pi Theta pos interior](goal).

Under the stated assumptions, the pi Theta pos interior. -/
lemma piTheta_pos_interior (θ : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (j : Fin 4) :
    0 < piTheta θ p j := by
  rcases hp with ⟨hp0, hp1⟩
  rcases hθ with ⟨h00, h01, h10, h11⟩
  fin_cases j <;> dsimp [piTheta, controlProb] <;> apply mul_pos <;> linarith

-- @node: patternRay_one_le_interior
/-- Under the supplied quantities and conditions, the pattern ray one le interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε), [the pattern Ray one le interior](goal).

Under the stated assumptions, the pattern Ray one le interior. -/
lemma patternRay_one_le_interior (ε : ℝ) (hε : 0 ≤ ε)
    (s : Fin 14) (j : Fin 4) : 1 ≤ patternRay ε s j := by
  unfold patternRay privacyIncrement privacyRatio
  split_ifs <;> simp_all [Real.one_le_exp_iff]

-- @node: patternMass_pos_interior
/-- Under the supplied quantities and conditions, the pattern mass pos interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the pattern Mass pos interior](goal).

Under the stated assumptions, the pattern Mass pos interior. -/
lemma patternMass_pos_interior (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (hε : 0 ≤ ε) (s : Fin 14) :
    0 < patternMass θ p ε s := by
  unfold patternMass
  apply Finset.sum_pos'
  · intro j _
    exact le_of_lt (mul_pos (piTheta_pos_interior θ p hp hθ j)
      (lt_of_lt_of_le (by norm_num) (patternRay_one_le_interior ε hε s j)))
  · exact ⟨0, Finset.mem_univ _, mul_pos
      (piTheta_pos_interior θ p hp hθ 0)
      (lt_of_lt_of_le (by norm_num) (patternRay_one_le_interior ε hε s 0))⟩

-- @node: informationObjective_nonneg_interior
/-- Under the supplied quantities and conditions, the information objective nonneg interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hα), [the information Objective nonneg interior](goal).

Under the stated assumptions, the information Objective nonneg interior. -/
lemma informationObjective_nonneg_interior (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 ≤ ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) (t : ℝ) :
    0 ≤ informationObjective θ p ε α t := by
  unfold informationObjective patternInformation
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (hα.1 s)
    (div_nonneg (sq_nonneg _) (le_of_lt (patternMass_pos_interior θ p ε hp hθ hε s)))

-- @node: informationQuadratic_nonneg_staircase
/-- Under the supplied quantities and conditions, the information quadratic nonneg staircase assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hα), [the information Quadratic nonneg staircase](goal).

Under the stated assumptions, the information Quadratic nonneg staircase. -/
lemma informationQuadratic_nonneg_staircase (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 ≤ ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α)
    (v : TrialParameter) :
    0 ≤ informationQuadratic (informationMatrix θ p ε α) v := by
  rw [informationQuadratic_eq_pattern_sum]
  apply Finset.sum_nonneg
  intro s _
  exact div_nonneg (mul_nonneg (hα.1 s) (sq_nonneg _))
    (le_of_lt (patternMass_pos_interior θ p ε hp hθ hε s))

-- @node: informationMatrix_posSemidef_interior
/-- Under the supplied quantities and conditions, the information matrix pos semidef interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hα), [the information Matrix pos Semidef interior](goal).

Under the stated assumptions, the information Matrix pos Semidef interior. -/
lemma informationMatrix_posSemidef_interior (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 ≤ ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) :
    (informationMatrix θ p ε α).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    unfold informationMatrix
    apply Finset.sum_congr rfl
    intro s _
    ring
  · intro v
    have hq := informationQuadratic_nonneg_staircase θ p ε hp hθ hε α hα v
    have heq : star v ⬝ᵥ (informationMatrix θ p ε α).mulVec v =
        informationQuadratic (informationMatrix θ p ε α) v := by
      simp [informationQuadratic, dotProduct, Matrix.mulVec,
        Fin.sum_univ_succ, star_trivial]
      ring
    rw [heq]
    exact hq

-- @node: contrastSolution_value_pos
/-- [the contrast solution value pos assertion](goal) holds. For [the displayed quantities and conditions](hyp:I,hI,w,hw), these specify the stated inputs. -/
lemma contrastSolution_value_pos (I : Matrix (Fin 2) (Fin 2) ℝ)
    (hI : I.PosSemidef) (w : TrialParameter)
    (hw : I.mulVec w = contrastVector) :
    0 < ∑ k : Fin 2, contrastVector k * w k := by
  let r := ∑ k : Fin 2, contrastVector k * w k
  have hq : informationQuadratic I w = r := by
    dsimp [r]
    calc
      informationQuadratic I w = ∑ k, w k * (I.mulVec w) k := by
        simp [informationQuadratic, Matrix.mulVec, Finset.mul_sum]
        ring
      _ = ∑ k, w k * contrastVector k := by rw [hw]
      _ = ∑ k, contrastVector k * w k := by
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hr : 0 ≤ r := by
    rw [← hq]
    have hn := hI.dotProduct_mulVec_nonneg w
    rw [show star w ⬝ᵥ I.mulVec w = informationQuadratic I w by
      simp [informationQuadratic, dotProduct, Matrix.mulVec, star_trivial]
      ring] at hn
    exact hn
  refine lt_of_le_of_ne hr ?_
  intro hr0
  have hzero : I.mulVec w = 0 := by
    apply (hI.dotProduct_mulVec_zero_iff w).mp
    rw [show star w ⬝ᵥ I.mulVec w = informationQuadratic I w by
      simp [informationQuadratic, dotProduct, Matrix.mulVec, star_trivial]
      ring]
    rw [hq, hr0]
  rw [hw] at hzero
  have := congrFun hzero 0
  norm_num [contrastVector] at this

-- @node: contrastSolution_value_unique
/-- [the contrast solution value unique assertion](goal) holds. For [the displayed quantities and conditions](hyp:I,hI,w,v,hw,hv), these specify the stated inputs. -/
lemma contrastSolution_value_unique (I : Matrix (Fin 2) (Fin 2) ℝ)
    (hI : I.PosSemidef) (w v : TrialParameter)
    (hw : I.mulVec w = contrastVector) (hv : I.mulVec v = contrastVector) :
    (∑ k : Fin 2, contrastVector k * v k) =
      ∑ k : Fin 2, contrastVector k * w k := by
  have hsym := hI.isHermitian
  have hs := congrFun₂ hsym 0 1
  calc
    (∑ k, contrastVector k * v k) =
        ∑ k, (I.mulVec w) k * v k := by rw [hw]
    _ = ∑ k, w k * (I.mulVec v) k := by
      simp [Matrix.mulVec, Fin.sum_univ_succ, star_trivial] at hs ⊢
      rw [hs]
      ring
    _ = ∑ k, w k * contrastVector k := by rw [hv]
    _ = ∑ k, contrastVector k * w k := by
      apply Finset.sum_congr rfl
      intro k _
      ring

-- @node: contrastVariance_eq_solution_value
/-- [the contrast variance eq solution value assertion](goal) holds. For [the displayed quantities and conditions](hyp:I,hI,w,hw), these specify the stated inputs. -/
lemma contrastVariance_eq_solution_value (I : Matrix (Fin 2) (Fin 2) ℝ)
    (hI : I.PosSemidef) (w : TrialParameter)
    (hw : I.mulVec w = contrastVector) :
    contrastVariance I =
      ENNReal.ofReal (∑ k : Fin 2, contrastVector k * w k) := by
  have hrange : contrastInRange I := ⟨w, hw⟩
  rw [contrastVariance, if_pos hrange]
  congr 1
  apply IsLeast.csInf_eq
  refine ⟨⟨w, hw, rfl⟩, ?_⟩
  rintro u ⟨v, hv, rfl⟩
  exact le_of_eq (contrastSolution_value_unique I hI w v hw hv).symm

-- @node: contrastInformation_cauchy
/-- [the contrast information cauchy assertion](goal) holds. For [the displayed quantities and conditions](hyp:I,hI,w,hw,t), these specify the stated inputs. -/
lemma contrastInformation_cauchy (I : Matrix (Fin 2) (Fin 2) ℝ)
    (hI : I.PosSemidef) (w : TrialParameter)
    (hw : I.mulVec w = contrastVector) (t : ℝ) :
    1 ≤ informationQuadratic I (direction t) *
      (∑ k : Fin 2, contrastVector k * w k) := by
  let r := ∑ k : Fin 2, contrastVector k * w k
  let x := direction t
  let y : TrialParameter := fun k => r * x k - w k
  have hr : 0 < r := contrastSolution_value_pos I hI w hw
  have hy : 0 ≤ informationQuadratic I y := by
    have hn := hI.dotProduct_mulVec_nonneg y
    rw [show star y ⬝ᵥ I.mulVec y = informationQuadratic I y by
      simp [informationQuadratic, dotProduct, Matrix.mulVec, star_trivial]
      ring] at hn
    exact hn
  have hsym := hI.isHermitian
  have hs := congrFun₂ hsym 0 1
  have hqw : informationQuadratic I w = r := by
    dsimp [r]
    calc
      informationQuadratic I w = ∑ k, w k * (I.mulVec w) k := by
        simp [informationQuadratic, Matrix.mulVec]
        ring
      _ = ∑ k, w k * contrastVector k := by rw [hw]
      _ = ∑ k, contrastVector k * w k := by
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hcross : (∑ k, x k * (I.mulVec w) k) = 1 := by
    rw [hw]
    simp [x, direction, contrastVector, Fin.sum_univ_succ]
  have hid : informationQuadratic I y =
      r * (r * informationQuadratic I x - 1) := by
    have hexpand : informationQuadratic I y =
        r ^ 2 * informationQuadratic I x -
          2 * r * (∑ k, x k * (I.mulVec w) k) +
          informationQuadratic I w := by
      dsimp [y]
      simp [informationQuadratic, Matrix.mulVec, Fin.sum_univ_succ,
        star_trivial] at hs ⊢
      rw [hs]
      ring
    rw [hexpand, hcross, hqw]
    ring
  rw [hid] at hy
  dsimp [r, x] at hy hr ⊢
  nlinarith

-- @node: reciprocal_le_contrastVariance
/-- [the reciprocal le contrast variance assertion](goal) holds. For [the displayed quantities and conditions](hyp:I,hI,j,hj,t,ht), these specify the stated inputs. -/
lemma reciprocal_le_contrastVariance (I : Matrix (Fin 2) (Fin 2) ℝ)
    (hI : I.PosSemidef) (j : ℝ) (hj : 0 < j)
    (t : ℝ) (ht : informationQuadratic I (direction t) ≤ j) :
    ENNReal.ofReal j⁻¹ ≤ contrastVariance I := by
  by_cases hrange : contrastInRange I
  · obtain ⟨w, hw⟩ := hrange
    rw [contrastVariance_eq_solution_value I hI w hw]
    apply ENNReal.ofReal_le_ofReal
    apply (inv_le_iff_one_le_mul₀' hj).2
    exact (contrastInformation_cauchy I hI w hw t).trans
      (mul_le_mul_of_nonneg_right ht
        (contrastSolution_value_pos I hI w hw).le)
  · simp [contrastVariance, hrange]

-- @node: contrastVariance_eq_reciprocal_of_minimizer
/-- Under [the supplied quantities and conditions](hyp:hI,t), [the contrast variance eq reciprocal of minimizer assertion](goal) holds. For [the displayed quantities and conditions](hyp:I,hmin,hpos), these specify the stated inputs. -/
lemma contrastVariance_eq_reciprocal_of_minimizer
    (I : Matrix (Fin 2) (Fin 2) ℝ) (hI : I.PosSemidef) (t : ℝ)
    (hmin : ∀ u : ℝ,
      informationQuadratic I (direction t) ≤
        informationQuadratic I (direction u))
    (hpos : 0 < informationQuadratic I (direction t)) :
    contrastVariance I =
      ENNReal.ofReal (informationQuadratic I (direction t))⁻¹ := by
  let j := informationQuadratic I (direction t)
  let A := I 0 0 + I 0 1 + I 1 0 + I 1 1
  let B := 2 * (I 0 0 * t + I 0 1 * (t + 1) +
    I 1 0 * t + I 1 1 * (t + 1))
  have hsym := hI.isHermitian
  have hs := congrFun₂ hsym 0 1
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
  let w : TrialParameter := fun k => direction t k / j
  have hsum :
      (I 0 0 * t + I 0 1 * (t + 1)) +
        (I 1 0 * t + I 1 1 * (t + 1)) = 0 := by
    dsimp [B] at hB
    linarith
  have hj_eq : j = I 1 0 * t + I 1 1 * (t + 1) := by
    dsimp [j]
    simp [informationQuadratic, direction, Fin.sum_univ_succ]
    linear_combination t * hsum
  have hw : I.mulVec w = contrastVector := by
    have hj : 0 < j := hpos
    funext k
    fin_cases k <;>
      simp [Matrix.mulVec, dotProduct, w, direction, contrastVector,
        Fin.sum_univ_succ] at hs ⊢ <;>
      field_simp [ne_of_gt hj] <;> nlinarith
  rw [contrastVariance_eq_solution_value I hI w hw]
  congr 1
  dsimp [w, j]
  simp [direction, contrastVector, Fin.sum_univ_succ]
  field_simp
  ring

-- @node: first_pattern_information_quadratic
/-- Under [the supplied quantities and conditions](hyp:p,t), [the first pattern information quadratic assertion](goal) holds. -/
lemma first_pattern_information_quadratic (θ : TrialParameter) (p ε t : ℝ) :
    patternInformation θ p ε 0 t =
      ((privacyIncrement ε * controlProb p) ^ 2 /
        patternMass θ p ε 0) * t ^ 2 := by
  simp +decide [patternInformation, projectedGradient, patternGradient,
    direction, Fin.sum_univ_succ]
  ring

-- @node: informationObjective_eq_informationQuadratic
/-- Under [the supplied quantities and conditions](hyp:p,t), [the information objective eq information quadratic assertion](goal) holds. -/
lemma informationObjective_eq_informationQuadratic
    (θ : TrialParameter) (p ε : ℝ) (α : StaircaseWeight) (t : ℝ) :
    informationObjective θ p ε α t =
      ∑ a : Fin 2, ∑ b : Fin 2,
        direction t a * informationMatrix θ p ε α a b * direction t b := by
  have h :
      (∑ a : Fin 2, ∑ b : Fin 2,
        direction t a * informationMatrix θ p ε α a b * direction t b) =
      ∑ s : Fin 14, α s *
        (∑ k : Fin 2, patternGradient p ε s k * direction t k) ^ 2 /
          patternMass θ p ε s := by
    unfold informationMatrix
    simp_rw [Finset.mul_sum, Finset.sum_mul, pow_two]
    calc
      (∑ a, ∑ b, ∑ s,
        direction t a * (α s * patternGradient p ε s a * patternGradient p ε s b /
          patternMass θ p ε s) * direction t b) =
          ∑ a, ∑ s, ∑ b,
            direction t a * (α s * patternGradient p ε s a * patternGradient p ε s b /
              patternMass θ p ε s) * direction t b := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
      _ = ∑ s, ∑ a, ∑ b,
            direction t a * (α s * patternGradient p ε s a * patternGradient p ε s b /
              patternMass θ p ε s) * direction t b := by rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s _
        simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a _
        simp_rw [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro b _
        ring
  calc
    informationObjective θ p ε α t =
        ∑ s : Fin 14, α s *
          (∑ k : Fin 2, patternGradient p ε s k * direction t k) ^ 2 /
            patternMass θ p ε s := by
      unfold informationObjective patternInformation projectedGradient
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := h.symm

-- @node: staircaseFeasible_weight_le_one
/-- Under the supplied quantities and conditions, the staircase feasible weight le one assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε,hα), [the staircase Feasible weight le one](goal).

Under the stated assumptions, the staircase Feasible weight le one. -/
lemma staircaseFeasible_weight_le_one (ε : ℝ) (hε : 0 ≤ ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) (s : Fin 14) :
    α s ≤ 1 := by
  have hr (u : Fin 14) : 1 ≤ patternRay ε u 0 := by
    unfold patternRay privacyIncrement privacyRatio
    split_ifs <;> simp_all [Real.one_le_exp_iff]
  have hterm (u : Fin 14) : 0 ≤ α u * patternRay ε u 0 :=
    mul_nonneg (hα.1 u) (by linarith [hr u])
  have hle : α s ≤ α s * patternRay ε s 0 := by
    nlinarith [mul_nonneg (hα.1 s) (sub_nonneg.mpr (hr s))]
  have hsingle : α s * patternRay ε s 0 ≤
      ∑ u : Fin 14, α u * patternRay ε u 0 :=
    Finset.single_le_sum (fun u _ => hterm u) (Finset.mem_univ s)
  rw [← staircaseMatrix, hα.2 0] at hsingle
  exact hle.trans hsingle

-- @node: staircaseFeasible_sum_le_one
/-- Under the supplied quantities and conditions, the staircase feasible sum le one assertion holds. Under [the stated assumptions](hyp:hε,hα), [the staircase Feasible sum le one](goal).

Under the stated assumptions, the staircase Feasible sum le one. -/
lemma staircaseFeasible_sum_le_one (ε : ℝ) (hε : 0 ≤ ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) :
    (∑ s : Fin 14, α s) ≤ 1 := by
  have hr (s : Fin 14) : 1 ≤ patternRay ε s 0 := by
    unfold patternRay privacyIncrement privacyRatio
    split_ifs <;> simp_all [Real.one_le_exp_iff]
  calc
    (∑ s : Fin 14, α s) = ∑ s : Fin 14, α s * 1 := by simp
    _ ≤ ∑ s : Fin 14, α s * patternRay ε s 0 := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (hr s) (hα.1 s)
    _ = 1 := hα.2 0

-- @node: staircaseFeasible_nonempty
/-- [the staircase feasible nonempty assertion](goal) holds. -/
lemma staircaseFeasible_nonempty (ε : ℝ) :
    (feasibleSet ε).Nonempty := by
  let α : StaircaseWeight :=
    fun s => if s = 0 ∨ s = 13 then 1 / (Real.exp ε + 1) else 0
  refine ⟨α, ?_⟩
  change staircaseFeasible ε α
  constructor
  · intro s
    dsimp [α]
    split_ifs <;> positivity
  · intro j
    fin_cases j <;>
      simp +decide [staircaseMatrix, α, patternRay, patternContains,
        privacyIncrement, privacyRatio, Fin.sum_univ_succ] <;>
      field_simp <;> ring

-- @node: staircaseFeasible_singleton_design
/-- [the staircase feasible singleton design assertion](goal) holds. -/
lemma staircaseFeasible_singleton_design (ε : ℝ) :
    staircaseFeasible ε (fun s : Fin 14 =>
      if s ∈ ({0, 1, 3, 7} : Finset (Fin 14)) then
        1 / (Real.exp ε + 3) else 0) := by
  constructor
  · intro s
    dsimp
    split_ifs <;> positivity
  · intro j
    fin_cases j <;>
      simp +decide [staircaseMatrix, patternRay, patternContains,
        privacyIncrement, privacyRatio, Fin.sum_univ_succ] <;>
      field_simp <;> ring

-- @node: staircaseFeasible_positive_first_pattern
/-- [the staircase feasible positive first pattern assertion](goal) holds. -/
lemma staircaseFeasible_positive_first_pattern (ε : ℝ) :
    ∃ α : StaircaseWeight, staircaseFeasible ε α ∧ 0 < α 0 := by
  let α : StaircaseWeight :=
    fun s => if s = 0 ∨ s = 13 then 1 / (Real.exp ε + 1) else 0
  refine ⟨α, ?_, by dsimp [α]; positivity⟩
  constructor
  · intro s
    dsimp [α]
    split_ifs <;> positivity
  · intro j
    fin_cases j <;>
      simp +decide [staircaseMatrix, α, patternRay, patternContains,
        privacyIncrement, privacyRatio, Fin.sum_univ_succ] <;>
      field_simp <;> ring

-- @node: staircaseFeasible_closed
/-- [the staircase feasible closed assertion](goal) holds. -/
lemma staircaseFeasible_closed (ε : ℝ) : IsClosed (feasibleSet ε) := by
  have hcoord (s : Fin 14) : Continuous (fun α : StaircaseWeight => α s) :=
    continuous_apply s
  have hrow (j : Fin 4) :
      Continuous (fun α : StaircaseWeight => staircaseMatrix ε α j) := by
    unfold staircaseMatrix
    fun_prop
  have hnonneg : IsClosed {α : StaircaseWeight | ∀ s, 0 ≤ α s} := by
    simpa only [Set.ofPred_forall] using
      (isClosed_iInter (fun s : Fin 14 =>
        isClosed_le continuous_const (hcoord s)))
  have hnormal : IsClosed {α : StaircaseWeight | ∀ j, staircaseMatrix ε α j = 1} := by
    simpa only [Set.ofPred_forall] using
      (isClosed_iInter (fun j : Fin 4 =>
        isClosed_eq (hrow j) continuous_const))
  convert hnonneg.inter hnormal using 1
  ext α
  simp only [feasibleSet, Set.mem_ofPred_eq, Set.mem_inter_iff,
    staircaseFeasible]

-- @node: staircaseFeasible_compact
/-- Under the supplied quantities and conditions, the staircase feasible compact assertion holds. Under [the stated assumptions](hyp:hε), [the staircase Feasible compact](goal).

Under the stated assumptions, the staircase Feasible compact. -/
lemma staircaseFeasible_compact (ε : ℝ) (hε : 0 ≤ ε) :
    IsCompact (feasibleSet ε) := by
  have hbox : IsCompact {α : StaircaseWeight | ∀ s, α s ∈ Set.Icc (0 : ℝ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  apply hbox.of_isClosed_subset (staircaseFeasible_closed ε)
  intro α hα s
  have hsingle : α s ≤ ∑ u : Fin 14, α u := by
    exact Finset.single_le_sum (fun u _ => hα.1 u) (Finset.mem_univ s)
  exact ⟨hα.1 s, hsingle.trans (staircaseFeasible_sum_le_one ε hε α hα)⟩

-- @node: staircaseFeasible_convex
/-- [the staircase feasible convex assertion](goal) holds. -/
lemma staircaseFeasible_convex (ε : ℝ) : Convex ℝ (feasibleSet ε) := by
  intro α hα β hβ a b ha hb hab
  constructor
  · intro s
    change 0 ≤ a * α s + b * β s
    exact add_nonneg (mul_nonneg ha (hα.1 s))
      (mul_nonneg hb (hβ.1 s))
  · intro j
    change (∑ s : Fin 14, (a * α s + b * β s) * patternRay ε s j) = 1
    calc
      _ = a * staircaseMatrix ε α j + b * staircaseMatrix ε β j := by
        simp only [staircaseMatrix, Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = 1 := by rw [hα.2 j, hβ.2 j]; linarith

/-- For the supplied quantities and conditions, the upper envelope is the mathematical object specified below. [The upper Envelope](goal) is determined by [the displayed parameters](hyp:θ,p,ε,t). -/
def upperEnvelope (θ : TrialParameter) (p ε t : ℝ) : ℝ :=
  sSup {u : ℝ | ∃ α ∈ feasibleSet ε, u = informationObjective θ p ε α t}

-- @node: informationObjective_continuous_weight
/-- [the information objective continuous weight assertion](goal) holds. For [the displayed quantities and conditions](hyp:p,t), these specify the stated inputs. -/
lemma informationObjective_continuous_weight (θ : TrialParameter)
    (p ε t : ℝ) :
    Continuous (fun α : StaircaseWeight => informationObjective θ p ε α t) := by
  unfold informationObjective
  fun_prop

-- @node: informationObjective_quadratic_difference
/-- Under [the supplied quantities and conditions](hyp:p), [the information objective quadratic difference assertion](goal) holds. For [the displayed quantities and conditions](hyp:t,u), these specify the stated inputs. -/
lemma informationObjective_quadratic_difference (θ : TrialParameter) (p ε : ℝ)
    (α : StaircaseWeight) (t u : ℝ) :
    informationObjective θ p ε α u =
      informationObjective θ p ε α t +
      (u - t) * (∑ s : Fin 14,
        2 * α s * projectedGradient p ε s t *
          (patternGradient p ε s 0 + patternGradient p ε s 1) /
            patternMass θ p ε s) +
      (u - t) ^ 2 * (∑ s : Fin 14,
        α s * (patternGradient p ε s 0 + patternGradient p ε s 1) ^ 2 /
          patternMass θ p ε s) := by
  simp only [informationObjective, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp [patternInformation, projectedGradient, direction, Fin.sum_univ_succ]
  ring

-- @node: informationObjective_min_of_stationary
/-- Under the supplied quantities and conditions, the information objective min of stationary assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hα,hstationary), [the information Objective min of stationary](goal).

Under the stated assumptions, the information Objective min of stationary. -/
lemma informationObjective_min_of_stationary (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 ≤ ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) (t : ℝ)
    (hstationary : (∑ s : Fin 14,
      2 * α s * projectedGradient p ε s t *
        (patternGradient p ε s 0 + patternGradient p ε s 1) /
          patternMass θ p ε s) = 0) :
    ∀ u : ℝ, informationObjective θ p ε α t ≤
      informationObjective θ p ε α u := by
  intro u
  conv_rhs => rw [informationObjective_quadratic_difference θ p ε α t u]
  rw [hstationary, mul_zero, add_zero]
  have hnonneg : 0 ≤ ∑ s : Fin 14,
      α s * (patternGradient p ε s 0 + patternGradient p ε s 1) ^ 2 /
        patternMass θ p ε s := by
    apply Finset.sum_nonneg
    intro s _
    exact div_nonneg (mul_nonneg (hα.1 s) (sq_nonneg _))
      (le_of_lt (patternMass_pos_interior θ p ε hp hθ hε s))
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hnonneg)

-- @node: informationObjective_stationary_of_min
/-- Under [the supplied quantities and conditions](hyp:p), [the information objective stationary of min assertion](goal) holds. For [the displayed quantities and conditions](hyp:t,hmin), these specify the stated inputs. -/
lemma informationObjective_stationary_of_min (θ : TrialParameter) (p ε : ℝ)
    (α : StaircaseWeight) (t : ℝ)
    (hmin : ∀ u : ℝ, informationObjective θ p ε α t ≤
      informationObjective θ p ε α u) :
    (∑ s : Fin 14,
      2 * α s * projectedGradient p ε s t *
        (patternGradient p ε s 0 + patternGradient p ε s 1) /
          patternMass θ p ε s) = 0 := by
  let A := ∑ s : Fin 14,
    2 * α s * projectedGradient p ε s t *
      (patternGradient p ε s 0 + patternGradient p ε s 1) /
        patternMass θ p ε s
  let B := ∑ s : Fin 14,
    α s * (patternGradient p ε s 0 + patternGradient p ε s 1) ^ 2 /
      patternMass θ p ε s
  have hpoly (x : ℝ) : 0 ≤ x * A + x ^ 2 * B := by
    have h := hmin (t + x)
    have hdiff := informationObjective_quadratic_difference θ p ε α t (t + x)
    rw [hdiff] at h
    simp only [add_sub_cancel_left] at h
    dsimp [A, B]
    linarith
  have hp (x : ℝ) : 0 ≤ x * A + x ^ 2 * B := hpoly x
  by_contra hn
  have hA : A ≠ 0 := hn
  have hden : 0 < |B| + 1 := by positivity
  have hB : B ≤ |B| := le_abs_self B
  have h := hp (-A / (2 * (|B| + 1)))
  have hsq : 0 < A ^ 2 := sq_pos_of_ne_zero hA
  have hden2 : 0 < (|B| + 1) ^ 2 := sq_pos_of_pos hden
  field_simp at h
  nlinarith [mul_nonneg hsq.le (sub_nonneg.mpr hB)]

-- @node: informationObjective_exists_minimizer
/-- Under the supplied quantities and conditions, the information objective exists minimizer assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hα), [the information Objective exists minimizer](goal).

Under the stated assumptions, the information Objective exists minimizer. -/
lemma informationObjective_exists_minimizer (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 ≤ ε)
    (α : StaircaseWeight) (hα : staircaseFeasible ε α) :
    ∃ t : ℝ, ∀ u : ℝ, informationObjective θ p ε α t ≤
      informationObjective θ p ε α u := by
  let A := ∑ s : Fin 14,
    2 * α s * projectedGradient p ε s 0 *
      (patternGradient p ε s 0 + patternGradient p ε s 1) /
        patternMass θ p ε s
  let B := ∑ s : Fin 14,
    α s * (patternGradient p ε s 0 + patternGradient p ε s 1) ^ 2 /
      patternMass θ p ε s
  have hB : 0 ≤ B := by
    dsimp [B]
    apply Finset.sum_nonneg
    intro s _
    exact div_nonneg (mul_nonneg (hα.1 s) (sq_nonneg _))
      (le_of_lt (patternMass_pos_interior θ p ε hp hθ hε s))
  have hquad (u : ℝ) :
      informationObjective θ p ε α u =
        informationObjective θ p ε α 0 + u * A + u ^ 2 * B := by
    convert informationObjective_quadratic_difference θ p ε α 0 u using 1
    simp [A, B]
  by_cases hB0 : B = 0
  · have hA0 : A = 0 := by
      by_contra hA
      have hval := informationObjective_nonneg_interior θ p ε hp hθ hε α hα
        (-(informationObjective θ p ε α 0 + 1) / A)
      rw [hquad, hB0] at hval
      have hident : informationObjective θ p ε α 0 +
          (-(informationObjective θ p ε α 0 + 1) / A) * A +
          (-(informationObjective θ p ε α 0 + 1) / A) ^ 2 * 0 = -1 := by
        field_simp [hA]
        ring
      rw [hident] at hval
      linarith
    refine ⟨0, fun u => ?_⟩
    rw [hquad u, hA0, hB0]
    simp
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    let t := -A / (2 * B)
    refine ⟨t, fun u => ?_⟩
    rw [hquad u, hquad t]
    have hsq : 0 ≤ B * (u - t) ^ 2 := mul_nonneg hB (sq_nonneg _)
    have hid :
        u * A + u ^ 2 * B - (t * A + t ^ 2 * B) =
          B * (u - t) ^ 2 := by
      dsimp [t]
      field_simp
      ring
    linarith


end CausalSmith.Stat.LdpAteEfficiencySurface

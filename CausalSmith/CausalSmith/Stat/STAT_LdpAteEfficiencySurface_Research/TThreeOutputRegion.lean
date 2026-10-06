module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.R3Continuity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.RegionOpenness
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TFiniteOracle
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TFiveOutputUpperBound

/-! # Three-output rational certificate

At the low-mean point, the exact primal and dual values certify a unique
three-ray optimum and its open neighborhood. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

-- @node: threeMaskWeights_feasible
/-- Under the supplied quantities and conditions, the three mask weights feasible assertion holds. Under [the stated assumptions](hyp:hε), [the three Mask Weights feasible](goal).

Under the stated assumptions, the three Mask Weights feasible. -/
lemma threeMaskWeights_feasible (ε : ℝ) (hε : 0 < ε) :
    staircaseFeasible ε
      (fun s => if s ∈ ({0, 5, 7} : Finset (Fin 14)) then
        (Real.exp ε + 2)⁻¹ else 0) := by
  constructor
  · intro s
    change 0 ≤ (if s ∈ ({0, 5, 7} : Finset (Fin 14)) then
      (Real.exp ε + 2)⁻¹ else 0)
    split_ifs <;> positivity
  · intro j
    have hd : Real.exp ε + 2 ≠ 0 := by positivity
    fin_cases j <;>
      simp +decide [staircaseMatrix, patternRay, patternContains,
        privacyIncrement, privacyRatio, Fin.sum_univ_succ] <;>
      field_simp <;> ring

-- @node: threeMaskWeights_unique
/-- Under the supplied quantities and conditions, the three mask weights unique assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε,hα,hsupp), [the three Mask Weights unique](goal).

Under the stated assumptions, the three Mask Weights unique. -/
lemma threeMaskWeights_unique (ε : ℝ) (hε : 0 < ε) (α : StaircaseWeight)
    (hα : staircaseFeasible ε α)
    (hsupp : staircaseSupport α = ({0, 5, 7} : Finset (Fin 14))) :
    α = fun s => if s ∈ ({0, 5, 7} : Finset (Fin 14)) then
      (Real.exp ε + 2)⁻¹ else 0 := by
  have hzero (s : Fin 14)
      (hs : s ∉ ({0, 5, 7} : Finset (Fin 14))) : α s = 0 := by
    by_contra hn
    have hm : s ∈ staircaseSupport α := by
      simp [staircaseSupport, hn]
    rw [hsupp] at hm
    exact hs hm
  have h0 := hα.2 0
  have h1 := hα.2 1
  have h3 := hα.2 3
  simp +decide [staircaseMatrix, patternRay, patternContains,
    privacyIncrement, privacyRatio, Fin.sum_univ_succ, hzero] at h0 h1 h3
  have hr : Real.exp ε ≠ 1 := ne_of_gt ((Real.one_lt_exp_iff).2 hε)
  have heq05 : α 0 = α 5 := by
    have hx : (Real.exp ε - 1) * (α 0 - α 5) = 0 := by
      linear_combination h0 - h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (sub_ne_zero.mpr hr))
  have heq57 : α 5 = α 7 := by
    have hx : (Real.exp ε - 1) * (α 5 - α 7) = 0 := by
      linear_combination h1 - h3
    exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (sub_ne_zero.mpr hr))
  have he : Real.exp ε + 2 ≠ 0 := by positivity
  have hα0 : α 0 = (Real.exp ε + 2)⁻¹ := by
    field_simp
    rw [← heq05, ← heq57, ← heq05] at h0
    nlinarith
  have hα5 : α 5 = (Real.exp ε + 2)⁻¹ := by
    exact heq05.symm.trans hα0
  have hα7 : α 7 = (Real.exp ε + 2)⁻¹ := by
    exact heq57.symm.trans hα5
  funext s
  by_cases hs : s ∈ ({0, 5, 7} : Finset (Fin 14))
  · have hcases : s = 0 ∨ s = 5 ∨ s = 7 := by simpa using hs
    rcases hcases with rfl | rfl | rfl
    · simpa using hα0
    · simpa using hα5
    · simpa using hα7
  · simp [hs, hzero s hs]

-- @node: threeMaskWeights_support
/-- [the three mask weights support assertion](goal) holds. -/
lemma threeMaskWeights_support (ε : ℝ) :
    staircaseSupport
      (fun s => if s ∈ ({0, 5, 7} : Finset (Fin 14)) then
        (Real.exp ε + 2)⁻¹ else 0) =
      ({0, 5, 7} : Finset (Fin 14)) := by
  ext s
  simp only [staircaseSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hs : s ∈ ({0, 5, 7} : Finset (Fin 14))
  · simp [hs, ne_of_gt (inv_pos.mpr (by positivity : 0 < Real.exp ε + 2))]
  · simp [hs]

-- @node: threeMaskWeights_continuous
/-- [the three mask weights continuous assertion](goal) holds. -/
lemma threeMaskWeights_continuous :
    Continuous (fun ε : ℝ =>
      (fun s : Fin 14 => if s ∈ ({0, 5, 7} : Finset (Fin 14)) then
        (Real.exp ε + 2)⁻¹ else (0 : ℝ))) := by
  apply continuous_pi
  intro s
  by_cases hs : s ∈ ({0, 5, 7} : Finset (Fin 14))
  · simp only [hs, ite_true]
    convert ((Real.continuous_exp.add continuous_const).inv₀
      (fun ε => ne_of_gt (by positivity : 0 < Real.exp ε + 2))) using 1
    funext ε
    rfl
  · simpa [hs] using (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))

-- @node: lowMeanCandidate_feasible
/-- [the low mean candidate feasible assertion](goal) holds. -/
lemma lowMeanCandidate_feasible :
    ∃ α : StaircaseWeight,
      staircaseFeasible (Real.log 3) α ∧
      staircaseSupport α = ({0, 5, 7} : Finset (Fin 14)) ∧
      ∀ s ∈ ({0, 5, 7} : Finset (Fin 14)), α s = (1 / 5 : ℝ) := by
  let α : StaircaseWeight := fun s => if s ∈ ({0, 5, 7} : Finset (Fin 14)) then 1 / 5 else 0
  refine ⟨α, ⟨?_, ?_⟩, ?_, ?_⟩
  · have h := (threeMaskWeights_feasible (Real.log 3)
      (Real.log_pos (by norm_num : (1 : ℝ) < 3))).1
    simpa [α, Real.exp_log (by norm_num : (0 : ℝ) < 3),
      show (3 + 2 : ℝ)⁻¹ = 1 / 5 by norm_num] using h
  · have h := (threeMaskWeights_feasible (Real.log 3)
      (Real.log_pos (by norm_num : (1 : ℝ) < 3))).2
    simpa [α, Real.exp_log (by norm_num : (0 : ℝ) < 3),
      show (3 + 2 : ℝ)⁻¹ = 1 / 5 by norm_num] using h
  · simpa [α, Real.exp_log (by norm_num : (0 : ℝ) < 3),
      show (3 + 2 : ℝ)⁻¹ = 1 / 5 by norm_num] using
        threeMaskWeights_support (Real.log 3)
  · intro s hs
    simp only [α, if_pos hs]

-- @node: lowMeanCandidate_information_value
/-- [the low mean candidate information value assertion](goal) holds. -/
lemma lowMeanCandidate_information_value :
    informationObjective (fun _ => (1 / 10 : ℝ)) (3 / 10) (Real.log 3)
      (fun s => if s ∈ ({0, 5, 7} : Finset (Fin 14)) then 1 / 5 else 0)
      (-(339 / 9985 : ℝ)) = 441 / 3994 := by
  have he : Real.exp (Real.log (3 : ℝ)) = 3 := Real.exp_log (by norm_num)
  have hpi (j : Fin 4) :
      piTheta (fun _ => (1 / 10 : ℝ)) (3 / 10) j =
        if j.val = 0 then 63 / 100
        else if j.val = 1 then 7 / 100
        else if j.val = 2 then 27 / 100 else 3 / 100 := by
    rcases j with ⟨j, hj⟩
    interval_cases j <;> norm_num [piTheta, controlProb] <;> rfl
  have hpi0 := hpi 0
  have hpi1 := hpi 1
  have hpi2 := hpi 2
  have hpi3 := hpi 3
  norm_num at hpi0 hpi1 hpi2 hpi3
  simp +decide [informationObjective, patternInformation, projectedGradient,
    patternGradient, patternMass, patternRay, patternContains,
    privacyIncrement, privacyRatio, controlProb, direction, he,
    Fin.sum_univ_succ]
  simp only [show (10⁻¹ : ℝ) = 1 / 10 by norm_num,
    hpi0, hpi1, hpi2, hpi3]
  norm_num

-- @node: lowMeanCandidate_stationary
/-- [the low mean candidate stationary assertion](goal) holds. -/
lemma lowMeanCandidate_stationary :
    (∑ s : Fin 14,
      (if s ∈ ({0, 5, 7} : Finset (Fin 14)) then (1 / 5 : ℝ) else 0) *
        patternInformationSlope (fun _ => (1 / 10 : ℝ)) (3 / 10)
          (Real.log 3) s (-(339 / 9985 : ℝ))) = 0 := by
  have he : Real.exp (Real.log (3 : ℝ)) = 3 := Real.exp_log (by norm_num)
  have hpi (j : Fin 4) :
      piTheta (fun _ => (1 / 10 : ℝ)) (3 / 10) j =
        if j.val = 0 then 63 / 100
        else if j.val = 1 then 7 / 100
        else if j.val = 2 then 27 / 100 else 3 / 100 := by
    rcases j with ⟨j, hj⟩
    interval_cases j <;> norm_num [piTheta, controlProb] <;> rfl
  have hpi0 := hpi 0
  have hpi1 := hpi 1
  have hpi2 := hpi 2
  have hpi3 := hpi 3
  norm_num at hpi0 hpi1 hpi2 hpi3
  simp +decide [patternInformationSlope, projectedGradient, patternGradient,
    patternMass, patternRay, patternContains, privacyIncrement,
    privacyRatio, controlProb, direction, he, Fin.sum_univ_succ]
  simp only [show (10⁻¹ : ℝ) = 1 / 10 by norm_num,
    hpi0, hpi1, hpi2, hpi3]
  norm_num

-- @node: lowMeanCandidate_global_min
/-- Under [the supplied quantities and conditions](hyp:t), [the low mean candidate global min assertion](goal) holds. -/
lemma lowMeanCandidate_global_min (t : ℝ) :
    (441 / 3994 : ℝ) ≤
      informationObjective (fun _ => (1 / 10 : ℝ)) (3 / 10) (Real.log 3)
        (fun s => if s ∈ ({0, 5, 7} : Finset (Fin 14)) then 1 / 5 else 0) t := by
  have he : Real.exp (Real.log (3 : ℝ)) = 3 := Real.exp_log (by norm_num)
  have hpi (j : Fin 4) :
      piTheta (fun _ => (1 / 10 : ℝ)) (3 / 10) j =
        if j.val = 0 then 63 / 100
        else if j.val = 1 then 7 / 100
        else if j.val = 2 then 27 / 100 else 3 / 100 := by
    rcases j with ⟨j, hj⟩
    interval_cases j <;> norm_num [piTheta, controlProb] <;> rfl
  have hpi0 := hpi 0
  have hpi1 := hpi 1
  have hpi2 := hpi 2
  have hpi3 := hpi 3
  norm_num at hpi0 hpi1 hpi2 hpi3
  simp +decide [informationObjective, patternInformation, projectedGradient,
    patternGradient, patternMass, patternRay, patternContains,
    privacyIncrement, privacyRatio, controlProb, direction, he,
    Fin.sum_univ_succ]
  simp only [show (10⁻¹ : ℝ) = 1 / 10 by norm_num,
    hpi0, hpi1, hpi2, hpi3]
  norm_num at *
  nlinarith [sq_nonneg (t + 339 / 9985)]

-- @node: lowMeanDual
/-- [The fixed dual certificate for the low-mean three-output region](goal) is the displayed object. -/
@[no_expose]
noncomputable def lowMeanDual : Fin 4 → ℝ :=
  ![-(21817593 / 398800900 : ℝ),
    (32820291 / 8773619800 : ℝ),
    (509870781 / 8773619800 : ℝ),
    (41183667 / 398800900 : ℝ)]

-- @node: lowMeanDual_value
/-- Under the supplied quantities and conditions, the low mean dual value assertion holds. [The low Mean Dual value](goal).

The low Mean Dual value. -/
lemma lowMeanDual_value :
    (∑ j : Fin 4, lowMeanDual j) = (441 / 3994 : ℝ) := by
  norm_num [lowMeanDual, Fin.sum_univ_succ]

-- @node: lowMeanDual_slack
/-- Under [the supplied quantities and conditions](hyp:s), [the low mean dual slack assertion](goal) holds. -/
lemma lowMeanDual_slack (s : Fin 14) :
    (if s ∈ ({0, 5, 7} : Finset (Fin 14)) then
      dualRay (Real.log 3) lowMeanDual s =
        patternInformation (fun _ => (1 / 10 : ℝ)) (3 / 10)
          (Real.log 3) s (-(339 / 9985 : ℝ))
    else
      patternInformation (fun _ => (1 / 10 : ℝ)) (3 / 10)
          (Real.log 3) s (-(339 / 9985 : ℝ)) <
        dualRay (Real.log 3) lowMeanDual s) := by
  have he : Real.exp (Real.log (3 : ℝ)) = 3 := Real.exp_log (by norm_num)
  have hpi (j : Fin 4) :
      piTheta (fun _ => (1 / 10 : ℝ)) (3 / 10) j =
        if j.val = 0 then 63 / 100
        else if j.val = 1 then 7 / 100
        else if j.val = 2 then 27 / 100 else 3 / 100 := by
    rcases j with ⟨j, hj⟩
    interval_cases j <;> norm_num [piTheta, controlProb] <;> rfl
  have hpi0 := hpi 0
  have hpi1 := hpi 1
  have hpi2 := hpi 2
  have hpi3 := hpi 3
  norm_num at hpi0 hpi1 hpi2 hpi3
  fin_cases s <;>
    simp +decide [dualRay, lowMeanDual, patternInformation, projectedGradient,
      patternGradient, patternMass, patternRay, patternContains,
      controlProb, privacyIncrement, privacyRatio, direction,
      he, Fin.sum_univ_succ] <;>
    (try simp only [show (10⁻¹ : ℝ) = 1 / 10 by norm_num,
    hpi0, hpi1, hpi2, hpi3]) <;> norm_num

-- @node: lowMeanPoint_mem_R3
/-- [the low mean point mem r3 assertion](goal) holds. -/
lemma lowMeanPoint_mem_R3 :
    ((3 / 10 : ℝ), (1 / 10 : ℝ), (1 / 10 : ℝ), Real.log 3) ∈ R3 := by
  simp only [R3, certifiedRegion, Set.mem_ofPred_eq]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, Real.log_pos (by norm_num), ?_⟩
  obtain ⟨α, hfeas, hsupp, hweight⟩ := lowMeanCandidate_feasible
  refine ⟨α, -(339 / 9985 : ℝ), lowMeanDual, ?_⟩
  have hθ : (fun k : Fin 2 => if k = 0 then (1 / 10 : ℝ) else 1 / 10) =
      (fun _ => (1 / 10 : ℝ)) := by
    funext k
    split_ifs <;> rfl
  rw [hθ]
  refine ⟨hfeas, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    change α s ≠ 0 ↔ s ∈ ({0, 5, 7} : Finset (Fin 14))
    have h := congrArg (fun K : Finset (Fin 14) => s ∈ K) hsupp
    simpa [staircaseSupport] using h
  · intro s hs
    rw [hweight s hs]
    norm_num
  · have hα : α = (fun s => if s ∈ ({0, 5, 7} : Finset (Fin 14)) then
        (1 / 5 : ℝ) else 0) := by
      funext s
      by_cases hs : s ∈ ({0, 5, 7} : Finset (Fin 14))
      · simpa [hs] using hweight s hs
      · have hzero : α s = 0 := by
          by_contra hn
          have hm : s ∈ staircaseSupport α := by
            simp [staircaseSupport, hn]
          rw [hsupp] at hm
          exact hs hm
        simp [hs, hzero]
    rw [hα]
    exact lowMeanCandidate_stationary
  · intro s hs
    simpa [hs] using lowMeanDual_slack s
  · intro s hs
    simpa [hs] using lowMeanDual_slack s
  · simp

-- @node: feasible_dualRay_sum
/-- the feasible dual ray sum assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hα), [the feasible dual Ray sum](goal).

Under the stated assumptions, the feasible dual Ray sum. -/
lemma feasible_dualRay_sum (ε : ℝ) (α : StaircaseWeight)
    (hα : staircaseFeasible ε α) (η : Fin 4 → ℝ) :
    (∑ s : Fin 14, α s * dualRay ε η s) = ∑ j : Fin 4, η j := by
  simp only [dualRay, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  change (∑ j : Fin 4, staircaseMatrix ε α j * η j) = ∑ j : Fin 4, η j
  simp only [hα.2, one_mul]

-- @node: lowMean_dual_upper_bound
/-- the low mean dual upper bound assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hβ), [the low Mean dual upper bound](goal).

Under the stated assumptions, the low Mean dual upper bound. -/
lemma lowMean_dual_upper_bound (β : StaircaseWeight)
    (hβ : staircaseFeasible (Real.log 3) β) :
    informationObjective (fun _ => (1 / 10 : ℝ)) (3 / 10)
      (Real.log 3) β (-(339 / 9985 : ℝ)) ≤ 441 / 3994 := by
  have hpoint (s : Fin 14) :
      patternInformation (fun _ => (1 / 10 : ℝ)) (3 / 10)
        (Real.log 3) s (-(339 / 9985 : ℝ)) ≤
        dualRay (Real.log 3) lowMeanDual s := by
    by_cases hs : s ∈ ({0, 5, 7} : Finset (Fin 14))
    · have h := lowMeanDual_slack s
      simp only [if_pos hs] at h
      exact le_of_eq h.symm
    · exact le_of_lt (by simpa [hs] using lowMeanDual_slack s)
  calc
    informationObjective (fun _ => (1 / 10 : ℝ)) (3 / 10)
        (Real.log 3) β (-(339 / 9985 : ℝ))
        = ∑ s : Fin 14, β s * patternInformation
          (fun _ => (1 / 10 : ℝ)) (3 / 10)
          (Real.log 3) s (-(339 / 9985 : ℝ)) := rfl
    _ ≤ ∑ s : Fin 14, β s * dualRay (Real.log 3) lowMeanDual s := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (hpoint s) (hβ.1 s)
    _ = 441 / 3994 := by rw [feasible_dualRay_sum _ _ hβ, lowMeanDual_value]

-- @node: lowMean_information_nonneg
/-- the low mean information nonneg assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hβ), [the low Mean information nonneg](goal).

Under the stated assumptions, the low Mean information nonneg. -/
lemma lowMean_information_nonneg (β : StaircaseWeight)
    (hβ : staircaseFeasible (Real.log 3) β) (t : ℝ) :
    0 ≤ informationObjective (fun _ => (1 / 10 : ℝ)) (3 / 10)
      (Real.log 3) β t := by
  have he : Real.exp (Real.log (3 : ℝ)) = 3 := Real.exp_log (by norm_num)
  have hpi (j : Fin 4) :
      piTheta (fun _ => (1 / 10 : ℝ)) (3 / 10) j =
        if j.val = 0 then 63 / 100
        else if j.val = 1 then 7 / 100
        else if j.val = 2 then 27 / 100 else 3 / 100 := by
    rcases j with ⟨j, hj⟩
    interval_cases j <;> norm_num [piTheta, controlProb] <;> rfl
  have hm (s : Fin 14) :
      0 ≤ patternMass (fun _ => (1 / 10 : ℝ)) (3 / 10) (Real.log 3) s := by
    unfold patternMass
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg
    · rw [hpi]
      split_ifs <;> norm_num
    · simp only [patternRay, privacyIncrement, privacyRatio, he]
      split_ifs <;> norm_num
  unfold informationObjective
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (hβ.1 s)
    (div_nonneg (sq_nonneg _) (hm s))

-- @node: lowMeanCandidate_inf_value
/-- [the low mean candidate inf value assertion](goal) holds. -/
lemma lowMeanCandidate_inf_value :
    sInf {u : ℝ | ∃ t : ℝ,
      u = informationObjective (fun _ => (1 / 10 : ℝ))
        (3 / 10) (Real.log 3)
        (fun s => if s ∈ ({0, 5, 7} : Finset (Fin 14)) then 1 / 5 else 0) t} =
      441 / 3994 := by
  let α : StaircaseWeight :=
    fun s => if s ∈ ({0, 5, 7} : Finset (Fin 14)) then 1 / 5 else 0
  let S : Set ℝ := {u | ∃ t : ℝ,
    u = informationObjective (fun _ => (1 / 10 : ℝ))
      (3 / 10) (Real.log 3) α t}
  have hnonempty : S.Nonempty := by
    refine ⟨informationObjective (fun _ => (1 / 10 : ℝ))
      (3 / 10) (Real.log 3) α 0, 0, rfl⟩
  have hbelow : BddBelow S := by
    refine ⟨441 / 3994, ?_⟩
    rintro u ⟨t, rfl⟩
    exact lowMeanCandidate_global_min t
  change sInf S = 441 / 3994
  apply le_antisymm
  · have hmem : (441 / 3994 : ℝ) ∈ S := by
      refine ⟨-(339 / 9985 : ℝ), ?_⟩
      exact lowMeanCandidate_information_value.symm
    exact csInf_le hbelow hmem
  · apply le_csInf hnonempty
    rintro u ⟨t, rfl⟩
    exact lowMeanCandidate_global_min t

-- @node: lowMean_Jstar_value
/-- [the low mean jstar value assertion](goal) holds. -/
lemma lowMean_Jstar_value :
    Jstar (fun _ => (1 / 10 : ℝ)) (3 / 10) (Real.log 3) =
      (441 / 3994 : ℝ) := by
  let θ : TrialParameter := fun _ => (1 / 10 : ℝ)
  let E : Set ℝ := {z | ∃ β : StaircaseWeight,
    staircaseFeasible (Real.log 3) β ∧
    z = sInf {u : ℝ | ∃ t : ℝ,
      u = informationObjective θ (3 / 10) (Real.log 3) β t}}
  have hupper : ∀ z ∈ E, z ≤ (441 / 3994 : ℝ) := by
    rintro z ⟨β, hβ, rfl⟩
    have hbelow : BddBelow {u : ℝ | ∃ t : ℝ,
        u = informationObjective θ (3 / 10) (Real.log 3) β t} := by
      refine ⟨0, ?_⟩
      rintro u ⟨t, rfl⟩
      exact lowMean_information_nonneg β hβ t
    exact (csInf_le hbelow ⟨-(339 / 9985 : ℝ), rfl⟩).trans
      (lowMean_dual_upper_bound β hβ)
  obtain ⟨α, hα, hsupp, hweight⟩ := lowMeanCandidate_feasible
  have hαeq : α = (fun s => if s ∈ ({0, 5, 7} : Finset (Fin 14)) then
        (1 / 5 : ℝ) else 0) := by
    funext s
    by_cases hs : s ∈ ({0, 5, 7} : Finset (Fin 14))
    · simpa [hs] using hweight s hs
    · have hzero : α s = 0 := by
        by_contra hn
        have hm : s ∈ staircaseSupport α := by
          simp [staircaseSupport, hn]
        rw [hsupp] at hm
        exact hs hm
      simp [hs, hzero]
  have hmem : (441 / 3994 : ℝ) ∈ E := by
    refine ⟨α, hα, ?_⟩
    rw [hαeq]
    exact lowMeanCandidate_inf_value.symm
  change sSup E = 441 / 3994
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hupper)
    (le_csSup ⟨_, hupper⟩ hmem)

open Filter Topology Causalean.Mathlib.LinearAlgebra


/-- [The target vector in the three-output dual system](goal) is determined by [the displayed parameters](hyp:x). -/
@[no_expose]
noncomputable def r3DualTarget (x : RegionParameter) : Fin 3 → ℝ :=
  fun i => patternInformation (regionTheta x) x.1 x.2.2.2 (r3Mask i)
    (r3Direction x.1 x.2.1 x.2.2.1 x.2.2.2)

/-- Under [the supplied quantities and conditions](hyp:i), [the r3 mask mem assertion](goal) holds. -/
lemma r3Mask_mem (i : Fin 3) : r3Mask i ∈ ({0, 5, 7} : Finset (Fin 14)) := by
  fin_cases i <;> simp [r3Mask]

/-- Under [the supplied quantities and conditions](hyp:x,hx), [the exists local r3 dual of mem assertion](goal) holds. -/
lemma exists_local_r3Dual_of_mem (x : RegionParameter) (hx : x ∈ R3) :
    ∃ η : RegionParameter → Fin 4 → ℝ,
      ContinuousAt η x ∧
      (∀ s ∉ ({0,5,7} : Finset (Fin 14)),
        patternInformation (regionTheta x) x.1 x.2.2.2 s
          (r3Direction x.1 x.2.1 x.2.2.1 x.2.2.2) <
            dualRay x.2.2.2 (η x) s) ∧
      ∀ᶠ y in nhds x, Matrix.mulVec (r3DualMatrix y) (η y) = r3DualTarget y := by
  rcases x with ⟨p, μ0, μ1, ε⟩
  change 0 < p ∧ p < 1 ∧ 0 < μ0 ∧ μ0 < 1 ∧ 0 < μ1 ∧ μ1 < 1 ∧ 0 < ε ∧
      ∃ α, ∃ t, ∃ η,
        staircaseFeasible ε α ∧ activeSupport α ({0,5,7} : Finset (Fin 14)) ∧
        (∀ s ∈ ({0,5,7} : Finset (Fin 14)), 0 < α s) ∧
        (∑ s, α s * patternInformationSlope (fun k => if k=0 then μ0 else μ1) p ε s t) = 0 ∧
        (∀ s ∈ ({0,5,7} : Finset (Fin 14)), dualRay ε η s =
          patternInformation (fun k => if k=0 then μ0 else μ1) p ε s t) ∧
        (∀ s ∉ ({0,5,7} : Finset (Fin 14)), patternInformation
          (fun k => if k=0 then μ0 else μ1) p ε s t < dualRay ε η s) ∧ _ at hx
  rcases hx with ⟨hp0,hp1,hm00,hm01,hm10,hm11,hε,α,t,η,hα,hsupp,_,hstat,hactive,hinactive,_⟩
  have hsupp' : staircaseSupport α = ({0,5,7} : Finset (Fin 14)) := by
    ext s
    simpa [staircaseSupport] using hsupp s
  have hαeq := threeMaskWeights_unique ε hε α hα hsupp'
  have hstat' : r3Stationarity p μ0 μ1 ε t = 0 := by
    rw [r3Stationarity]
    rw [← hstat]
    apply Finset.sum_congr rfl
    intro s _
    rw [hαeq]
    rfl
  have hc : r3StationarityCoeff p μ0 μ1 ε ≠ 0 :=
    ne_of_gt (r3StationarityCoeff_pos p μ0 μ1 ε hp0 hp1 hm00 hm01 hm10 hm11 hε)
  have hdir0 := r3Stationarity_r3Direction_eq_zero p μ0 μ1 ε hc
  rw [r3Stationarity_affine] at hstat' hdir0
  have ht : t = r3Direction p μ0 μ1 ε := by
    have hm : (t - r3Direction p μ0 μ1 ε) * r3StationarityCoeff p μ0 μ1 ε = 0 := by
      linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hc)
  let x : RegionParameter := (p,μ0,μ1,ε)
  have hmass (s : Fin 14) : patternMass (regionTheta x) x.1 x.2.2.2 s ≠ 0 :=
    ne_of_gt (patternMass_pos_of_interior p μ0 μ1 ε hp0 hp1 hm00 hm01 hm10 hm11 s)
  have htdir := continuousAt_r3Direction_region x hmass hc
  have hb : ContinuousAt r3DualTarget x := by
    apply (continuousAt_pi).2
    intro i
    exact continuousAt_patternInformation_region (r3Mask i)
      (fun y => r3Direction y.1 y.2.1 y.2.2.1 y.2.2.2) x htdir (hmass _)
  have hy : Matrix.mulVec (r3DualMatrix x) η = r3DualTarget x := by
    funext i
    have ha := hactive (r3Mask i) (r3Mask_mem i)
    have htheta : regionTheta x = (fun k => if k = 0 then μ0 else μ1) := by
      funext k
      fin_cases k <;> rfl
    change (r3DualMatrix x).mulVec η i =
      patternInformation (regionTheta x) p ε (r3Mask i)
        (r3Direction p μ0 μ1 ε)
    rw [htheta]
    simpa [x, r3DualTarget, r3DualMatrix, Matrix.mulVec,
      dotProduct, dualRay, ht, mul_comm] using ha
  have hR := r3DualMatrix_mul_rightInverse x hε
  obtain ⟨hcont, hbase, hev⟩ := exists_eventually_anchoredSolution_of_rightInverse
    r3DualMatrix r3DualTarget (r3DualRightInverse ε) x η
    continuous_r3DualMatrix.continuousAt hb hR hy
  let ηlocal := anchoredSolution r3DualMatrix r3DualTarget
    (r3DualRightInverse ε) η
  refine ⟨ηlocal, hcont, ?_, hev⟩
  intro s hs
  have htheta : regionTheta x = (fun k => if k = 0 then μ0 else μ1) := by
    funext k
    fin_cases k <;> rfl
  dsimp only [ηlocal]
  rw [hbase, htheta]
  simpa [x, ht] using hinactive s hs

/-- [the low mean r3 direction eq assertion](goal) holds. -/
lemma lowMean_r3Direction_eq :
    r3Direction (3 / 10) (1 / 10) (1 / 10) (Real.log 3) =
      -(339 / 9985 : ℝ) := by
  have hc : r3StationarityCoeff (3 / 10) (1 / 10) (1 / 10) (Real.log 3) ≠ 0 :=
    ne_of_gt (r3StationarityCoeff_pos _ _ _ _ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Real.log_pos (by norm_num)))
  have hnew := r3Stationarity_r3Direction_eq_zero _ _ _ _ hc
  have hold : r3Stationarity (3 / 10) (1 / 10) (1 / 10) (Real.log 3)
      (-(339 / 9985 : ℝ)) = 0 := by
    convert lowMeanCandidate_stationary using 1 <;>
      norm_num [r3Stationarity, r3Weight,
        Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  rw [r3Stationarity_affine] at hnew hold
  have hm : (r3Direction (3 / 10) (1 / 10) (1 / 10) (Real.log 3) -
      (-(339 / 9985 : ℝ))) *
      r3StationarityCoeff (3 / 10) (1 / 10) (1 / 10) (Real.log 3) = 0 := by
    linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hc)

/-- Under [the supplied quantities and conditions](hyp:i,k,hik), [the low mean r3 projected scores distinct assertion](goal) holds. -/
lemma lowMean_r3_projectedScores_distinct (i k : Fin 3) (hik : i ≠ k) :
    projectedScore (regionTheta ((3 / 10 : ℝ), (1 / 10 : ℝ),
      (1 / 10 : ℝ), Real.log 3)) (3 / 10) (Real.log 3) (r3Mask i)
        (r3Direction (3 / 10) (1 / 10) (1 / 10) (Real.log 3)) ≠
    projectedScore (regionTheta ((3 / 10 : ℝ), (1 / 10 : ℝ),
      (1 / 10 : ℝ), Real.log 3)) (3 / 10) (Real.log 3) (r3Mask k)
        (r3Direction (3 / 10) (1 / 10) (1 / 10) (Real.log 3)) := by
  have hpi (j : Fin 4) :
      piTheta (fun _ => (1 / 10 : ℝ)) (3 / 10) j =
        if j.val = 0 then 63 / 100
        else if j.val = 1 then 7 / 100
        else if j.val = 2 then 27 / 100 else 3 / 100 := by
    rcases j with ⟨j, hj⟩
    interval_cases j <;> norm_num [piTheta, controlProb] <;> rfl
  have hpi0 := hpi 0
  have hpi1 := hpi 1
  have hpi2 := hpi 2
  have hpi3 := hpi 3
  norm_num at hpi0 hpi1 hpi2 hpi3
  have htheta : regionTheta ((3 / 10 : ℝ), (1 / 10 : ℝ),
      (1 / 10 : ℝ), Real.log 3) = (fun _ => (1 / 10 : ℝ)) := by
    funext j
    fin_cases j <;> rfl
  rw [htheta]
  rw [lowMean_r3Direction_eq]
  simp only [projectedScore, patternMass, Fin.sum_univ_succ]
  simp_rw [hpi]
  fin_cases i <;> fin_cases k
  all_goals simp only [Fin.isValue] at hik ⊢
  all_goals try contradiction
  all_goals
    simp (disch := decide) [regionTheta, r3Mask, projectedScore,
      projectedGradient, patternGradient, patternMass, patternRay,
      patternContains, Nat.testBit, privacyIncrement, privacyRatio, controlProb, direction,
      Real.exp_log (by norm_num : (0 : ℝ) < 3), Fin.sum_univ_succ] <;>
    norm_num [piTheta, controlProb]


open Filter Topology

/-- [The projected score coordinate in the three-output region](goal) is determined by [the displayed parameters](hyp:x,i). -/
@[expose] public def r3ProjectedScoreAt (x : RegionParameter) (i : Fin 3) : ℝ :=
  projectedScore (regionTheta x) x.1 x.2.2.2 (r3Mask i)
    (r3Direction x.1 x.2.1 x.2.2.1 x.2.2.2)

/-- Under [the supplied quantities and conditions](hyp:x,i), [the r3 projected score at eq assertion](goal) holds. -/
lemma r3ProjectedScoreAt_eq (x : RegionParameter) (i : Fin 3) :
    r3ProjectedScoreAt x i = projectedScore (regionTheta x) x.1 x.2.2.2
      (r3Mask i) (r3Direction x.1 x.2.1 x.2.2.1 x.2.2.2) := rfl

/-- [the exists low mean r3 distinct score neighborhood assertion](goal) holds. -/
lemma exists_lowMean_r3_distinctScore_neighborhood :
    ∃ U : Set RegionParameter, IsOpen U ∧
      ((3 / 10 : ℝ), (1 / 10 : ℝ), (1 / 10 : ℝ), Real.log 3) ∈ U ∧
      ∀ x ∈ U, ∀ i k : Fin 3, i ≠ k →
        r3ProjectedScoreAt x i ≠ r3ProjectedScoreAt x k := by
  let x0 : RegionParameter :=
    ((3 / 10 : ℝ), (1 / 10 : ℝ), (1 / 10 : ℝ), Real.log 3)
  have hm (s : Fin 14) : patternMass (regionTheta x0) x0.1 x0.2.2.2 s ≠ 0 :=
    ne_of_gt (patternMass_pos_of_interior _ _ _ _ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) s)
  have hc : r3StationarityCoeff x0.1 x0.2.1 x0.2.2.1 x0.2.2.2 ≠ 0 :=
    ne_of_gt (r3StationarityCoeff_pos _ _ _ _ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Real.log_pos (by norm_num)))
  have ht := continuousAt_r3Direction_region x0 hm hc
  have hs (i : Fin 3) : ContinuousAt (fun x => r3ProjectedScoreAt x i) x0 := by
    exact continuousAt_projectedScore_region (r3Mask i)
      (fun x => r3Direction x.1 x.2.1 x.2.2.1 x.2.2.2) x0 ht (hm (r3Mask i))
  have hp (i k : Fin 3) (hik : i ≠ k) :
      ∀ᶠ x in nhds x0, r3ProjectedScoreAt x i ≠ r3ProjectedScoreAt x k := by
    have hne : r3ProjectedScoreAt x0 i ≠ r3ProjectedScoreAt x0 k := by
      exact lowMean_r3_projectedScores_distinct i k hik
    have hd := (hs i).sub (hs k)
    have hdiff : r3ProjectedScoreAt x0 i - r3ProjectedScoreAt x0 k ≠ 0 :=
      sub_ne_zero.mpr hne
    filter_upwards [hd.eventually_ne hdiff] with x hx
    exact sub_ne_zero.mp hx
  have hev : ∀ᶠ x in nhds x0, ∀ i k : Fin 3, i ≠ k →
      r3ProjectedScoreAt x i ≠ r3ProjectedScoreAt x k := by
    filter_upwards [hp 0 1 (by decide), hp 0 2 (by decide),
      hp 1 0 (by decide), hp 1 2 (by decide), hp 2 0 (by decide),
      hp 2 1 (by decide)] with x h01 h02 h10 h12 h20 h21
    intro i k hik
    fin_cases i <;> fin_cases k <;> simp_all
  rcases mem_nhds_iff.mp hev with ⟨U, hUsub, hUopen, hx0⟩
  exact ⟨U, hUopen, hx0, fun x hx => hUsub hx⟩

open scoped BigOperators

/-- [the is open r3 continuous certificate assertion](goal) holds. -/
lemma isOpen_R3_continuousCertificate : IsOpen R3 := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨η, hη, hbaseslack, heq⟩ := exists_local_r3Dual_of_mem x hx
  rcases x with ⟨p, μ0, μ1, ε⟩
  change 0 < p ∧ p < 1 ∧ 0 < μ0 ∧ μ0 < 1 ∧ 0 < μ1 ∧ μ1 < 1 ∧ 0 < ε ∧ _ at hx
  rcases hx with ⟨hp0,hp1,hm00,hm01,hm10,hm11,hε,α,t,η0,hα,hsupp,hpos,hstat,hactive,hinactive,_⟩
  let x0 : RegionParameter := (p,μ0,μ1,ε)
  have hmass (s : Fin 14) : patternMass (regionTheta x0) x0.1 x0.2.2.2 s ≠ 0 :=
    ne_of_gt (patternMass_pos_of_interior p μ0 μ1 ε hp0 hp1 hm00 hm01 hm10 hm11 s)
  have hc : r3StationarityCoeff p μ0 μ1 ε ≠ 0 :=
    ne_of_gt (r3StationarityCoeff_pos p μ0 μ1 ε hp0 hp1 hm00 hm01 hm10 hm11 hε)
  have ht := continuousAt_r3Direction_region x0 hmass hc
  have hinfo (s : Fin 14) : ContinuousAt (fun y : RegionParameter =>
      patternInformation (regionTheta y) y.1 y.2.2.2 s
        (r3Direction y.1 y.2.1 y.2.2.1 y.2.2.2)) x0 :=
    continuousAt_patternInformation_region s _ x0 ht (hmass s)
  have hdual (s : Fin 14) : ContinuousAt (fun y : RegionParameter =>
      dualRay y.2.2.2 (η y) s) x0 := by
    have hηj (j : Fin 4) : ContinuousAt (fun y => η y j) x0 :=
      (continuousAt_pi.mp hη) j
    unfold dualRay
    let f := fun j : Fin 4 => fun y : RegionParameter =>
      patternRay y.2.2.2 s j * η y j
    have hf (j : Fin 4) : ContinuousAt (f j) x0 :=
      (continuous_patternRay_region s j).continuousAt.mul (hηj j)
    have hsum : ∀ S : Finset (Fin 4),
        ContinuousAt (fun y => ∑ j ∈ S, f j y) x0 := by
      intro S
      induction S using Finset.induction_on with
      | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : RegionParameter => (0 : ℝ)) x0)
      | @insert a S ha ih =>
          simp only [Finset.sum_insert ha]
          change ContinuousAt (fun y => f a y + ∑ j ∈ S, f j y) x0
          exact (hf a).add ih
    simpa [f] using hsum Finset.univ
  have hslack : ∀ᶠ y in nhds x0, ∀ s : Fin 14,
      s ∉ ({0,5,7} : Finset (Fin 14)) →
      patternInformation (regionTheta y) y.1 y.2.2.2 s
        (r3Direction y.1 y.2.1 y.2.2.1 y.2.2.2) < dualRay y.2.2.2 (η y) s := by
    have hall : ∀ᶠ y in nhds x0, ∀ s ∈ (Finset.univ : Finset (Fin 14)),
        s ∉ ({0,5,7} : Finset (Fin 14)) →
        patternInformation (regionTheta y) y.1 y.2.2.2 s
          (r3Direction y.1 y.2.1 y.2.2.1 y.2.2.2) < dualRay y.2.2.2 (η y) s :=
      (eventually_all_finset (Finset.univ : Finset (Fin 14))).2 fun s _ => by
        by_cases hs : s ∈ ({0,5,7} : Finset (Fin 14))
        · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hs))
        · have hraw := (hinfo s).eventually_lt (hdual s)
            (by simpa [x0] using hbaseslack s hs)
          exact hraw.mono fun _ h _ => h
    exact hall.mono fun _ hy s hs => hy s (Finset.mem_univ s) hs
  have hbasic : ∀ᶠ y in nhds x0,
      0 < y.1 ∧ y.1 < 1 ∧ 0 < y.2.1 ∧ y.2.1 < 1 ∧
      0 < y.2.2.1 ∧ y.2.2.1 < 1 ∧ 0 < y.2.2.2 := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_fst hp0,
      continuousAt_fst.eventually_lt continuousAt_const hp1,
      continuousAt_const.eventually_lt continuousAt_snd.fst hm00,
      continuousAt_snd.fst.eventually_lt continuousAt_const hm01,
      continuousAt_const.eventually_lt continuousAt_snd.snd.fst hm10,
      continuousAt_snd.snd.fst.eventually_lt continuousAt_const hm11,
      continuousAt_const.eventually_lt continuousAt_snd.snd.snd hε] with y
      yp0 yp1 ym00 ym01 ym10 ym11 yε
    exact ⟨yp0,yp1,ym00,ym01,ym10,ym11,yε⟩
  filter_upwards [heq, hslack, hbasic] with y hyeq hyslack hybasic
  rcases y with ⟨q,ν0,ν1,δ⟩
  rcases hybasic with ⟨hq0,hq1,hν00,hν01,hν10,hν11,hδ⟩
  change 0 < q ∧ q < 1 ∧ 0 < ν0 ∧ ν0 < 1 ∧ 0 < ν1 ∧ ν1 < 1 ∧ 0 < δ ∧ _
  refine ⟨hq0,hq1,hν00,hν01,hν10,hν11,hδ, r3Weight δ,
    r3Direction q ν0 ν1 δ, η (q,ν0,ν1,δ), ?_⟩
  have hfeas := threeMaskWeights_feasible δ hδ
  have hsuppw := threeMaskWeights_support δ
  refine ⟨hfeas, ?_, ?_, ?_, ?_, ?_, by simp⟩
  · intro s
    by_cases hs : s ∈ ({0,5,7} : Finset (Fin 14))
    · simp [r3Weight, hs]
      positivity
    · simp [r3Weight, hs]
  · intro s hs
    simp [r3Weight, hs]
    positivity
  · exact r3Stationarity_r3Direction_eq_zero q ν0 ν1 δ
      (ne_of_gt (r3StationarityCoeff_pos q ν0 ν1 δ hq0 hq1 hν00 hν01 hν10 hν11 hδ))
  · intro s hs
    obtain ⟨i, rfl⟩ : ∃ i : Fin 3, r3Mask i = s := by
      have hcases : s = 0 ∨ s = 5 ∨ s = 7 := by simpa using hs
      rcases hcases with rfl | rfl | rfl
      · exact ⟨0, by simp [r3Mask]⟩
      · exact ⟨1, by simp [r3Mask]⟩
      · exact ⟨2, by simp [r3Mask]⟩
    have hi := congrFun hyeq i
    have htheta : regionTheta (q,ν0,ν1,δ) =
        (fun k => if k = 0 then ν0 else ν1) := by
      funext k
      fin_cases k <;> rfl
    change (r3DualMatrix (q,ν0,ν1,δ)).mulVec (η (q,ν0,ν1,δ)) i =
      patternInformation (regionTheta (q,ν0,ν1,δ)) q δ (r3Mask i)
        (r3Direction q ν0 ν1 δ) at hi
    rw [htheta] at hi
    change dualRay δ (η (q,ν0,ν1,δ)) (r3Mask i) =
      patternInformation (fun k => if k = 0 then ν0 else ν1) q δ
        (r3Mask i) (r3Direction q ν0 ν1 δ)
    simpa [r3DualMatrix, r3DualTarget, Matrix.mulVec, dotProduct,
      dualRay, mul_comm] using hi
  · exact hyslack

-- @node: thm:three-output-region
/-- [the three output region assertion](goal) holds. -/
theorem three_output_region :
    IsOpen R3 ∧
    ((3 / 10 : ℝ), (1 / 10 : ℝ), (1 / 10 : ℝ), Real.log 3) ∈ R3 ∧
    (∃ α : StaircaseWeight,
      staircaseFeasible (Real.log 3) α ∧
      staircaseSupport α = ({0, 5, 7} : Finset (Fin 14)) ∧
      (∀ s ∈ ({0, 5, 7} : Finset (Fin 14)), α s = (1 / 5 : ℝ)) ∧
      Jstar (fun _ => (1 / 10 : ℝ)) (3 / 10) (Real.log 3) =
        sInf {u : ℝ | ∃ t : ℝ,
          u = informationObjective (fun _ => (1 / 10 : ℝ))
            (3 / 10) (Real.log 3) α t} ∧
      (∀ β : StaircaseWeight, staircaseFeasible (Real.log 3) β →
        Jstar (fun _ => (1 / 10 : ℝ)) (3 / 10) (Real.log 3) =
          sInf {u : ℝ | ∃ t : ℝ,
            u = informationObjective (fun _ => (1 / 10 : ℝ))
              (3 / 10) (Real.log 3) β t} → β = α)) ∧
    Jstar (fun _ => (1 / 10 : ℝ)) (3 / 10) (Real.log 3) =
      (441 / 3994 : ℝ) ∧
    Vstar (fun _ => (1 / 10 : ℝ)) (3 / 10) (Real.log 3) =
      (3994 / 441 : ℝ) := by
  refine ⟨?_, lowMeanPoint_mem_R3, ?_, lowMean_Jstar_value, ?_⟩
  · exact isOpen_R3_continuousCertificate
  · obtain ⟨α, hα, hsupp, hweight⟩ := lowMeanCandidate_feasible
    refine ⟨α, hα, hsupp, hweight, ?_, ?_⟩
    · have hαeq : α = (fun s => if s ∈ ({0, 5, 7} : Finset (Fin 14)) then
          (1 / 5 : ℝ) else 0) := by
        funext s
        by_cases hs : s ∈ ({0, 5, 7} : Finset (Fin 14))
        · simpa [hs] using hweight s hs
        · have hzero : α s = 0 := by
            by_contra hn
            have hm : s ∈ staircaseSupport α := by
              simp [staircaseSupport, hn]
            rw [hsupp] at hm
            exact hs hm
          simp [hs, hzero]
      rw [lowMean_Jstar_value, hαeq]
      exact lowMeanCandidate_inf_value.symm
    · intro β hβ hopt
      let t : ℝ := -(339 / 9985)
      have hbelow : BddBelow {u : ℝ | ∃ x : ℝ,
          u = informationObjective (fun _ => (1 / 10 : ℝ))
            (3 / 10) (Real.log 3) β x} := by
        refine ⟨0, ?_⟩
        rintro u ⟨x, rfl⟩
        exact lowMean_information_nonneg β hβ x
      have hge : (441 / 3994 : ℝ) ≤
          informationObjective (fun _ => (1 / 10 : ℝ))
            (3 / 10) (Real.log 3) β t := by
        rw [← lowMean_Jstar_value, hopt]
        exact csInf_le hbelow ⟨t, rfl⟩
      have hvalue : informationObjective (fun _ => (1 / 10 : ℝ))
          (3 / 10) (Real.log 3) β t = 441 / 3994 :=
        le_antisymm (lowMean_dual_upper_bound β hβ) hge
      have hsum :
          (∑ s : Fin 14, β s * patternInformation
            (fun _ => (1 / 10 : ℝ)) (3 / 10) (Real.log 3) s t) =
          ∑ s : Fin 14, β s * dualRay (Real.log 3) lowMeanDual s := by
        calc
          _ = 441 / 3994 := hvalue
          _ = ∑ s : Fin 14, β s * dualRay (Real.log 3) lowMeanDual s := by
            rw [feasible_dualRay_sum _ _ hβ, lowMeanDual_value]
      have hterm (s : Fin 14) :
          β s * patternInformation (fun _ => (1 / 10 : ℝ))
              (3 / 10) (Real.log 3) s t ≤
          β s * dualRay (Real.log 3) lowMeanDual s := by
        have h := lowMeanDual_slack s
        by_cases hs : s ∈ ({0, 5, 7} : Finset (Fin 14))
        · simp only [if_pos hs] at h
          rw [h]
        · simp only [if_neg hs] at h
          exact mul_le_mul_of_nonneg_left (le_of_lt h) (hβ.1 s)
      have hterm_eq (s : Fin 14) :
          β s * patternInformation (fun _ => (1 / 10 : ℝ))
              (3 / 10) (Real.log 3) s t =
          β s * dualRay (Real.log 3) lowMeanDual s :=
        (Finset.sum_eq_sum_iff_of_le (fun s _ => hterm s)).mp hsum s
          (Finset.mem_univ s)
      have hzero (s : Fin 14)
          (hs : s ∉ ({0, 5, 7} : Finset (Fin 14))) : β s = 0 := by
        have h := lowMeanDual_slack s
        simp only [if_neg hs] at h
        have hn := hβ.1 s
        by_contra hz
        have hp : 0 < β s := lt_of_le_of_ne hn (Ne.symm hz)
        have hlt := mul_lt_mul_of_pos_left h hp
        exact (ne_of_lt hlt) (hterm_eq s)
      have he : Real.exp (Real.log (3 : ℝ)) = 3 := Real.exp_log (by norm_num)
      have h0 := hβ.2 0
      have h1 := hβ.2 1
      have h3 := hβ.2 3
      simp +decide [staircaseMatrix, patternRay, patternContains,
        privacyIncrement, privacyRatio, he, Fin.sum_univ_succ,
        hzero] at h0 h1 h3
      have hβ0 : β 0 = 1 / 5 := by linarith
      have hβ5 : β 5 = 1 / 5 := by linarith
      have hβ7 : β 7 = 1 / 5 := by linarith
      funext s
      by_cases hs : s ∈ ({0, 5, 7} : Finset (Fin 14))
      · have hcases : s = 0 ∨ s = 5 ∨ s = 7 := by simpa using hs
        rcases hcases with rfl | rfl | rfl
        · exact hβ0.trans (hweight 0 (by simp)).symm
        · exact hβ5.trans (hweight 5 (by simp)).symm
        · exact hβ7.trans (hweight 7 (by simp)).symm
      · rw [hzero s hs]
        have hαzero : α s = 0 := by
          by_contra hz
          have hm : s ∈ staircaseSupport α := by simp [staircaseSupport, hz]
          rw [hsupp] at hm
          exact hs hm
        exact hαzero.symm
  · norm_num [Vstar, lowMean_Jstar_value]

end CausalSmith.Stat.LdpAteEfficiencySurface

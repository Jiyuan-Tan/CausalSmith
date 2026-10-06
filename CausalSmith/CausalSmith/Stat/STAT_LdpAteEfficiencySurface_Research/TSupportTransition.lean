module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.AttainmentRigidity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.R3Rigidity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.GeneralR5Rigidity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.GeneralR3Cardinality
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TFiveOutputRegion
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TThreeOutputRegion

/-! # Transition between optimal support sizes

Disjoint neighborhoods of the balanced and low-mean points have unique
optimal staircase supports of sizes five and three, respectively. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open ProbabilityTheory

/-- For the supplied quantities and conditions, the unique optimal support is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The unique Optimal Support](goal) is determined by [the displayed parameters](hyp:θ,p,ε,K). -/
def uniqueOptimalSupport (θ : TrialParameter) (p ε : ℝ)
    (K : Finset (Fin 14)) : Prop :=
  ∃ α : StaircaseWeight,
    staircaseFeasible ε α ∧ staircaseSupport α = K ∧
    Jstar θ p ε =
      sInf {u : ℝ | ∃ t : ℝ, u = informationObjective θ p ε α t} ∧
    ∀ β : StaircaseWeight, staircaseFeasible ε β →
      Jstar θ p ε =
        sInf {u : ℝ | ∃ t : ℝ, u = informationObjective θ p ε β t} →
      β = α

/-- For the supplied quantities and conditions, the optimal cardinality is the mathematical object specified below. [The optimal Cardinality](goal) is determined by [the displayed parameters](hyp:θ,p,ε,k). -/
def optimalCardinality (θ : TrialParameter) (p ε : ℝ) (k : ℕ∞) : Prop :=
  (∃ α : StaircaseWeight, staircaseFeasible ε α ∧
    contrastVariance (informationMatrix θ p ε α) =
      ENNReal.ofReal (Vstar θ p ε) ∧
    outputCardinality θ p (staircaseChannel ε α) = k) ∧
  ∀ (Z : Type*) [MeasurableSpace Z] (Q : Kernel (Fin 4) Z),
    StationaryLDP ε Q →
    contrastVariance (channelFisherInfo θ p Q) =
      ENNReal.ofReal (Vstar θ p ε) →
    k ≤ outputCardinality θ p Q

-- @node: piTheta_by_val_transition
/-- Under [the supplied quantities and conditions](hyp:p,j), [the pi theta by val transition assertion](goal) holds. -/
lemma piTheta_by_val_transition (θ : TrialParameter) (p : ℝ) (j : Fin 4) :
    piTheta θ p j =
      if j.val = 0 then controlProb p * (1 - θ 0)
      else if j.val = 1 then controlProb p * θ 0
      else if j.val = 2 then p * (1 - θ 1)
      else p * θ 1 := by
  rcases j with ⟨j, hj⟩
  interval_cases j <;> rfl

-- @node: lowMean_informationMatrix_value
/-- [the low mean information matrix value assertion](goal) holds. -/
lemma lowMean_informationMatrix_value :
    informationMatrix (fun _ => (1 / 10 : ℝ)) (3 / 10) (Real.log 3)
      (fun s => if s ∈ ({0, 5, 7} : Finset (Fin 14)) then 1 / 5 else 0) =
      !![(1379 / 3390 : ℝ), -(1 / 10 : ℝ);
         -(1 / 10 : ℝ), (411 / 3710 : ℝ)] := by
  have he : Real.exp (Real.log (3 : ℝ)) = 3 := Real.exp_log (by norm_num)
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp +decide [informationMatrix, patternGradient, patternMass,
      patternRay, patternContains, piTheta_by_val_transition,
      privacyIncrement, privacyRatio, controlProb, he,
      Fin.sum_univ_succ] <;> norm_num

-- @node: lowMean_informationMatrix_direction
/-- [the low mean information matrix direction assertion](goal) holds. -/
lemma lowMean_informationMatrix_direction :
    (informationMatrix (fun _ => (1 / 10 : ℝ)) (3 / 10) (Real.log 3)
      (fun s => if s ∈ ({0, 5, 7} : Finset (Fin 14)) then 1 / 5 else 0)).mulVec
        (direction (-(339 / 9985 : ℝ))) =
      fun k => (441 / 3994 : ℝ) * contrastVector k := by
  rw [lowMean_informationMatrix_value]
  funext k
  fin_cases k <;>
    norm_num [Matrix.mulVec, dotProduct, direction, contrastVector,
      Fin.sum_univ_succ]

-- @node: lowMean_projectedScores_distinct
/-- [the low mean projected scores distinct assertion](goal) holds. -/
lemma lowMean_projectedScores_distinct :
    ∀ s ∈ ({0, 5, 7} : Finset (Fin 14)),
      ∀ u ∈ ({0, 5, 7} : Finset (Fin 14)), s ≠ u →
        projectedScore (fun _ => (1 / 10 : ℝ)) (3 / 10) (Real.log 3)
          s (-(339 / 9985 : ℝ)) ≠
        projectedScore (fun _ => (1 / 10 : ℝ)) (3 / 10) (Real.log 3)
          u (-(339 / 9985 : ℝ)) := by
  intro s hs u hu hne
  have he : Real.exp (Real.log (3 : ℝ)) = 3 := Real.exp_log (by norm_num)
  have hs : s = 0 ∨ s = 5 ∨ s = 7 := by simpa using hs
  have hu : u = 0 ∨ u = 5 ∨ u = 7 := by simpa using hu
  rcases hs with rfl | rfl | rfl
  all_goals rcases hu with rfl | rfl | rfl
  all_goals first | contradiction | simp +decide [projectedScore, projectedGradient,
    patternMass, patternGradient, patternRay, patternContains, piTheta_by_val_transition,
    privacyIncrement, privacyRatio, controlProb, direction, he,
    Fin.sum_univ_succ] <;> norm_num

-- @node: lowMean_outputCardinality_of_attainment
/-- [the low mean output cardinality of attainment assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,hQ,hattain), these specify the stated inputs. -/
lemma lowMean_outputCardinality_of_attainment
    {Z : Type*} [MeasurableSpace Z] (Q : Kernel (Fin 4) Z)
    (hQ : StationaryLDP (Real.log 3) Q)
    (hattain :
      contrastVariance
          (channelFisherInfo (fun _ ↦ (1 / 10 : ℝ)) (3 / 10) Q) =
        ENNReal.ofReal
          (Vstar (fun _ ↦ (1 / 10 : ℝ)) (3 / 10) (Real.log 3))) :
    3 ≤ outputCardinality (fun _ ↦ (1 / 10 : ℝ)) (3 / 10) Q := by
  let θ : TrialParameter := fun _ ↦ (1 / 10 : ℝ)
  let A : Finset (Fin 14) := {0, 5, 7}
  have hp : InteriorAssignment (3 / 10 : ℝ) := ⟨by norm_num, by norm_num⟩
  have hθ : InteriorMeans θ := by
    simp only [InteriorMeans, θ]
    norm_num
  have hε : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hupper : ∀ β : StaircaseWeight,
      staircaseFeasible (Real.log 3) β →
      informationObjective θ (3 / 10) (Real.log 3) β
        (-(339 / 9985 : ℝ)) ≤
        Jstar θ (3 / 10) (Real.log 3) := by
    intro β hβ
    dsimp only [θ]
    rw [lowMean_Jstar_value]
    exact lowMean_dual_upper_bound β hβ
  have hpositive : ∀ β : StaircaseWeight,
      staircaseFeasible (Real.log 3) β →
      informationObjective θ (3 / 10) (Real.log 3) β
          (-(339 / 9985 : ℝ)) =
        Jstar θ (3 / 10) (Real.log 3) →
      ∀ s ∈ A, 0 < β s := by
    intro β hβ heq
    have hactive : ∀ s ∈ A,
        dualRay (Real.log 3) lowMeanDual s =
          patternInformation θ (3 / 10) (Real.log 3) s
            (-(339 / 9985 : ℝ)) := by
      intro s hs
      simpa only [A, θ, if_pos hs] using lowMeanDual_slack s
    have hinactive : ∀ s ∉ A,
        patternInformation θ (3 / 10) (Real.log 3) s
            (-(339 / 9985 : ℝ)) <
          dualRay (Real.log 3) lowMeanDual s := by
      intro s hs
      simpa only [A, θ, if_neg hs] using lowMeanDual_slack s
    have hvalue : informationObjective θ (3 / 10) (Real.log 3) β
          (-(339 / 9985 : ℝ)) = ∑ j : Fin 4, lowMeanDual j := by
      rw [heq]
      dsimp only [θ]
      rw [lowMean_Jstar_value, lowMeanDual_value]
    have hout : ∀ s ∉ A, β s = 0 :=
      certificate_equality_forces_inactive_zero θ (3 / 10) (Real.log 3)
        (-(339 / 9985 : ℝ)) A lowMeanDual hactive hinactive β hβ hvalue
    have hcanonical := r3_feasible_eq_canonical β hβ (by
      simpa only [A] using hout)
    intro s hs
    rw [hcanonical]
    simp only [A] at hs
    simp [hs]
  have hcard := outputCardinality_ge_of_attainment_direction
    θ (3 / 10) (Real.log 3) (-(339 / 9985 : ℝ)) hp hθ hε A
    hupper hpositive (by
      simpa only [θ, A] using lowMean_projectedScores_distinct) Q hQ (by
        simpa only [θ] using hattain)
  norm_num [A] at hcard ⊢
  exact hcard

-- @node: supportRegion_slices
/-- Under [the supplied quantities and conditions](hyp:hR5), [the support region slices assertion](goal) holds. For [the displayed quantities and conditions](hyp:h5,hR3,h3), these specify the stated inputs. -/
lemma supportRegion_slices
    (hR5 : IsOpen R5)
    (h5 : ((3 / 10 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ), Real.log 3) ∈ R5)
    (hR3 : IsOpen R3)
    (h3 : ((3 / 10 : ℝ), (1 / 10 : ℝ), (1 / 10 : ℝ), Real.log 3) ∈ R3) :
    ∃ U5 U3 : Set (ℝ × ℝ),
      IsOpen U5 ∧ IsOpen U3 ∧
      ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ U5 ∧
      ((1 / 10 : ℝ), (1 / 10 : ℝ)) ∈ U3 ∧
      Disjoint U5 U3 ∧
      (∀ μ ∈ U5,
        ((3 / 10 : ℝ), μ.1, μ.2, Real.log 3) ∈ R5) ∧
      ∀ μ ∈ U3,
        ((3 / 10 : ℝ), μ.1, μ.2, Real.log 3) ∈ R3 := by
  let slice : ℝ × ℝ → ℝ × ℝ × ℝ × ℝ :=
    fun μ => ((3 / 10 : ℝ), μ.1, μ.2, Real.log 3)
  let U5 : Set (ℝ × ℝ) := slice ⁻¹' R5 ∩ {μ | (3 / 10 : ℝ) < μ.1}
  let U3 : Set (ℝ × ℝ) := slice ⁻¹' R3 ∩ {μ | μ.1 < (3 / 10 : ℝ)}
  have hslice : Continuous slice := by
    fun_prop
  refine ⟨U5, U3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hR5.preimage hslice).inter (isOpen_lt continuous_const continuous_fst)
  · exact (hR3.preimage hslice).inter (isOpen_lt continuous_fst continuous_const)
  · exact ⟨h5, by norm_num⟩
  · exact ⟨h3, by norm_num⟩
  · rw [Set.disjoint_left]
    intro μ hμ5 hμ3
    have hm5 := hμ5.2
    have hm3 := hμ3.2
    change (3 / 10 : ℝ) < μ.1 at hm5
    change μ.1 < (3 / 10 : ℝ) at hm3
    exact (not_lt_of_ge (le_of_lt hm5)) hm3
  · intro μ hμ
    exact hμ.1
  · intro μ hμ
    exact hμ.1

-- @node: optimalCardinality_of_mem_R5
/-- Under [the supplied quantities and conditions](hyp:p), [the optimal cardinality of mem r5 assertion](goal) holds. For [the displayed quantities and conditions](hyp:hx), these specify the stated inputs. -/
lemma optimalCardinality_of_mem_R5 (p μ0 μ1 ε : ℝ)
    (hx : (p, μ0, μ1, ε) ∈ R5) :
    optimalCardinality (fun k ↦ if k = 0 then μ0 else μ1) p ε 5 := by
  refine ⟨r5Certificate_staircase_attains_five p μ0 μ1 ε hx, ?_⟩
  intro Z _ Q hQ hattain
  exact r5Certificate_outputCardinality_ge_five p μ0 μ1 ε hx Q hQ hattain

-- @node: uniqueOptimalSupport_of_mem_R5
/-- Under [the supplied quantities and conditions](hyp:p), [the unique optimal support of mem r5 assertion](goal) holds. For [the displayed quantities and conditions](hyp:hx), these specify the stated inputs. -/
lemma uniqueOptimalSupport_of_mem_R5 (p μ0 μ1 ε : ℝ)
    (hx : (p, μ0, μ1, ε) ∈ R5) :
    uniqueOptimalSupport (fun k ↦ if k = 0 then μ0 else μ1)
      p ε r5Active := by
  obtain ⟨α, hα, hsupp, _, hopt, hunique⟩ :=
    r5Certificate_unique_optimum p μ0 μ1 ε hx
  refine ⟨α, hα, ?_, hopt, hunique⟩
  ext s
  simp only [staircaseSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hsupp s

-- @node: uniqueOptimalSupport_of_mem_R3
/-- Under [the supplied quantities and conditions](hyp:p), [the unique optimal support of mem r3 assertion](goal) holds. For [the displayed quantities and conditions](hyp:hx), these specify the stated inputs. -/
lemma uniqueOptimalSupport_of_mem_R3 (p μ0 μ1 : ℝ)
    (hx : (p, μ0, μ1, Real.log 3) ∈ R3) :
    uniqueOptimalSupport (fun k ↦ if k = 0 then μ0 else μ1)
      p (Real.log 3) ({0, 5, 7} : Finset (Fin 14)) := by
  obtain ⟨α, hα, hsupp, hopt, hunique⟩ :=
    r3Certificate_unique_optimum_log3 p μ0 μ1 hx
  refine ⟨α, hα, ?_, hopt, hunique⟩
  ext s
  simp only [staircaseSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hsupp s

-- @node: optimalCardinality_of_mem_R3_of_distinct
/-- Under [the supplied quantities and conditions](hyp:p), [the optimal cardinality of mem r3 of distinct assertion](goal) holds. For [the displayed quantities and conditions](hyp:hx,hdistinct), these specify the stated inputs. -/
lemma optimalCardinality_of_mem_R3_of_distinct (p μ0 μ1 : ℝ)
    (hx : (p, μ0, μ1, Real.log 3) ∈ R3)
    (hdistinct : ∀ i k : Fin 3, i ≠ k →
      r3ProjectedScoreAt (p, μ0, μ1, Real.log 3) i ≠
        r3ProjectedScoreAt (p, μ0, μ1, Real.log 3) k) :
    optimalCardinality (fun k ↦ if k = 0 then μ0 else μ1)
      p (Real.log 3) 3 := by
  refine ⟨r3Certificate_staircase_attains_three p μ0 μ1 hx, ?_⟩
  intro Z _ Q hQ hattain
  exact r3Certificate_outputCardinality_ge_three_of_distinct
    p μ0 μ1 hx hdistinct Q hQ hattain

-- @node: thm:support-transition
/-- [the support transition assertion](goal) holds. -/
theorem support_transition :
    ∃ U5 U3 : Set (ℝ × ℝ),
      IsOpen U5 ∧ IsOpen U3 ∧
      ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ U5 ∧
      ((1 / 10 : ℝ), (1 / 10 : ℝ)) ∈ U3 ∧
      Disjoint U5 U3 ∧
      (∀ μ ∈ U5,
        uniqueOptimalSupport (fun k => if k = 0 then μ.1 else μ.2)
          (3 / 10) (Real.log 3) ({2, 3, 5, 7, 8} : Finset (Fin 14)) ∧
        optimalCardinality (fun k => if k = 0 then μ.1 else μ.2)
          (3 / 10) (Real.log 3) 5) ∧
      (∀ μ ∈ U3,
        uniqueOptimalSupport (fun k => if k = 0 then μ.1 else μ.2)
          (3 / 10) (Real.log 3) ({0, 5, 7} : Finset (Fin 14)) ∧
        optimalCardinality (fun k => if k = 0 then μ.1 else μ.2)
          (3 / 10) (Real.log 3) 3) := by
  obtain ⟨V5, V3, hV5open, hV3open, hV5center, hV3center,
      hVdisjoint, hV5mem, hV3mem⟩ := supportRegion_slices
    isOpen_R5_continuousCertificate
    (centeredPoint_mem_R5 (3 / 10) (by norm_num) (by norm_num))
    three_output_region.1 three_output_region.2.1
  obtain ⟨D3, hD3open, hD3center, hD3distinct⟩ :=
    exists_lowMean_r3_distinctScore_neighborhood
  let slice : ℝ × ℝ → RegionParameter :=
    fun μ => ((3 / 10 : ℝ), μ.1, μ.2, Real.log 3)
  let U3 : Set (ℝ × ℝ) := V3 ∩ slice ⁻¹' D3
  have hslice : Continuous slice := by fun_prop
  refine ⟨V5, U3, hV5open, hV3open.inter (hD3open.preimage hslice),
    hV5center, ⟨hV3center, hD3center⟩, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro μ hμ5 hμ3
    exact Set.disjoint_left.mp hVdisjoint hμ5 hμ3.1
  · intro μ hμ
    have hx := hV5mem μ hμ
    refine ⟨?_, optimalCardinality_of_mem_R5 (3 / 10) μ.1 μ.2
      (Real.log 3) hx⟩
    simpa [r5Active] using uniqueOptimalSupport_of_mem_R5
      (3 / 10) μ.1 μ.2 (Real.log 3) hx
  · intro μ hμ
    have hx := hV3mem μ hμ.1
    have hd := hD3distinct (slice μ) hμ.2
    refine ⟨uniqueOptimalSupport_of_mem_R3 (3 / 10) μ.1 μ.2 hx,
      optimalCardinality_of_mem_R3_of_distinct (3 / 10) μ.1 μ.2 hx ?_⟩
    simpa [slice] using hd

end CausalSmith.Stat.LdpAteEfficiencySurface

module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.CalibrationRegularity
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedRootSmoothness

/-! # Smooth actual mixed cells

The literal selected root is substituted before differentiating the cells.
Positive radicands at zero amplitudes, smooth composition, and compactness give
one signed neighborhood and bounds for every fixed derivative order.
-/
public section
noncomputable section
open Filter
open scoped Topology
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- The covariance formula is smooth at zero effect and central margins. [the stated conclusion](goal) holds. -/
-- @node: covarianceBranch_contDiffAt_center
lemma covarianceBranch_contDiffAt_center :
    ContDiffAt ℝ ⊤ (fun v : Fin 3 → ℝ => covarianceBranch (v 0) (v 1) (v 2))
      ![0,1/2,1/2] := by
  unfold covarianceBranch
  dsimp only
  apply ContDiffAt.div
  · fun_prop
  · apply ContDiffAt.add
    · fun_prop
    · apply ContDiffAt.sqrt
      · fun_prop
      · norm_num
  · norm_num

/-- With the actual root substituted, every mixed cell is smooth on a full
neighborhood of every zero-amplitude spatial point. [the documented result](goal) -/
-- @node: localMixedCell_contDiffAt_zero
lemma localMixedCell_contDiffAt_zero (b : Bool) (s : Bool × Bool) (a y : Bool) (u : ℝ) :
    ContDiffAt ℝ ⊤ (localMixedCell b s a y) ![0,0,u] := by
  have hq := mixedRoot_contDiffAt_zero u
  have hZ : ContDiffAt ℝ ⊤ (fun v : Fin 3 → ℝ => localSignField (v 2) s) ![0,0,u] := by
    unfold localSignField
    fun_prop
  have he : ContDiffAt ℝ ⊤ (fun v : Fin 3 → ℝ =>
      if b then 1/2-v 0*mixedRoot (v 0) (v 1) (v 2)*localSignField (v 2) s
      else 1/2+v 0*mixedRoot (v 0) (v 1) (v 2)*localSignField (v 2) s) ![0,0,u] := by
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  have hm : ContDiffAt ℝ ⊤ (fun v : Fin 3 → ℝ => 1/2+v 1*localSignField (v 2) s)
      ![0,0,u] := by fun_prop
  have hc : ContDiffAt ℝ ⊤ (fun v : Fin 3 → ℝ =>
      if b then covarianceBranch (32*v 0*v 1)
        (if b then 1/2-v 0*mixedRoot (v 0) (v 1) (v 2)*localSignField (v 2) s
          else 1/2+v 0*mixedRoot (v 0) (v 1) (v 2)*localSignField (v 2) s)
        (1/2+v 1*localSignField (v 2) s) else 0) ![0,0,u] := by
    cases b
    · exact contDiffAt_const
    · let f : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun v =>
        ![32*v 0*v 1, 1/2-v 0*mixedRoot (v 0) (v 1) (v 2)*localSignField (v 2) s,
          1/2+v 1*localSignField (v 2) s]
      have hf : ContDiffAt ℝ ⊤ f ![0,0,u] := by
        apply contDiffAt_pi.mpr
        intro i
        fin_cases i <;> dsimp [f] <;> fun_prop
      have hbase : f ![0,0,u] = ![0,1/2,1/2] := by simp [f]
      have hout := covarianceBranch_contDiffAt_center
      rw [← hbase] at hout
      exact hout.comp _ hf
  unfold localMixedCell tableCell
  dsimp only
  cases a <;> cases y <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop

/-- A single signed square makes all actual mixed cells smooth, including
full neighborhoods of both spatial endpoints. [the documented result](goal) -/
-- @node: localMixedCell_uniform_contDiffAt
lemma localMixedCell_uniform_contDiffAt : ∃ ε : ℝ, 0 < ε ∧
    ∀ v ∈ mixedParameterRegion ε, ∀ b s a y,
      ContDiffAt ℝ ⊤ (localMixedCell b s a y) v := by
  have hevent : ∀ᶠ z : ℝ × ℝ in 𝓝 (0,0), ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ∀ b s a y, ContDiffAt ℝ ⊤ (localMixedCell b s a y) ![z.1,z.2,u] := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    simp only [Filter.eventually_all]
    intro b s a y
    obtain ⟨S, hS, hSmooth⟩ := (localMixedCell_contDiffAt_zero b s a y u).contDiffOn
      le_rfl (by simp)
    obtain ⟨D, hDsub, hDopen, hDbase⟩ := mem_nhds_iff.mp hS
    have hpre : ∀ᶠ z : (ℝ × ℝ) × ℝ in 𝓝 ((0,0),u), ![z.1.1,z.1.2,z.2] ∈ D :=
      (by fun_prop : ContinuousAt (fun z : (ℝ × ℝ) × ℝ => ![z.1.1,z.1.2,z.2]) ((0,0),u))
        (hDopen.mem_nhds hDbase)
    filter_upwards [hpre] with z hz
    exact (hSmooth.mono hDsub).contDiffAt (hDopen.mem_nhds hz)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨δ/2, by linarith, ?_⟩
  intro v hv b s a y
  have hmem : (v 0,v 1) ∈ Metric.ball (0,0) δ := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero]
    exact max_lt (by linarith [hv.1]) (by linarith [hv.2.1])
  have hvec : ![v 0,v 1,v 2] = v := by
    funext i
    fin_cases i <;> rfl
  simpa only [hvec] using hball hmem (v 2) hv.2.2 b s a y

/-- The closed mixed parameter square is compact. [the stated conclusion](goal) holds. -/
-- @node: mixedParameterRegion_isCompact
lemma mixedParameterRegion_isCompact (ε : ℝ) : IsCompact (mixedParameterRegion ε) := by
  let K : Set (Fin 3 → ℝ) := Set.pi Set.univ
    (fun i => if i = 2 then Set.Icc (0 : ℝ) 1 else Set.Icc (-ε) ε)
  have hK : IsCompact K := isCompact_univ_pi (fun i => by split <;> exact isCompact_Icc)
  have heq : K = mixedParameterRegion ε := by
    ext v
    simp only [K, Set.mem_pi, Set.mem_univ, forall_const, mixedParameterRegion, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨abs_le.mpr (by simpa using h 0), abs_le.mpr (by simpa using h 1),
        by simpa using h 2⟩
    · rintro ⟨h0,h1,h2⟩ i
      fin_cases i
      · simpa using abs_le.mp h0
      · simpa using abs_le.mp h1
      · simpa using h2
  rwa [heq] at hK

/-- Compactness bounds full derivatives of all finitely many actual mixed
cells simultaneously, at every fixed order. [the documented result](goal) -/
-- @node: localMixedCell_uniform_smooth_derivative_bounds
lemma localMixedCell_uniform_smooth_derivative_bounds : ∃ ε : ℝ, 0 < ε ∧
    (∀ v ∈ mixedParameterRegion ε, ∀ b s a y,
      ContDiffAt ℝ ⊤ (localMixedCell b s a y) v) ∧
    (∀ m : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ v ∈ mixedParameterRegion ε, ∀ b s a y,
      ‖iteratedFDeriv ℝ m (localMixedCell b s a y) v‖ ≤ B) := by
  obtain ⟨ε,hε,hSmooth⟩ := localMixedCell_uniform_contDiffAt
  refine ⟨ε,hε,hSmooth,?_⟩
  intro m
  let I := Bool × (Bool × Bool) × Bool × Bool
  have hb : ∀ i : I, ∃ B : ℝ, 0 < B ∧ ∀ v ∈ mixedParameterRegion ε,
      ‖iteratedFDeriv ℝ m (localMixedCell i.1 i.2.1 i.2.2.1 i.2.2.2) v‖ ≤ B := by
    intro i
    exact compact_smooth_derivative_bounds 3 _ _ (mixedParameterRegion_isCompact ε)
      (fun v hv => hSmooth v hv _ _ _ _) m
  choose B hB hBound using hb
  refine ⟨∑ i : I, B i, ?_, ?_⟩
  · exact Finset.sum_pos (fun i _ => hB i) Finset.univ_nonempty
  · intro v hv b s a y
    exact (hBound (b,s,a,y) v hv).trans
      (Finset.single_le_sum (fun i _ => (hB i).le) (Finset.mem_univ (b,s,a,y)))

end CausalSmith.Stat.LogoddsLowsmoothFrontier

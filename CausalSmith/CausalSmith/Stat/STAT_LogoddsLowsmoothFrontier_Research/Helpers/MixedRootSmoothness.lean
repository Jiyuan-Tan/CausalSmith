module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedEquationSmoothness
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ScalarImplicitFunction

/-! # Smoothness of the actual mixed root

Local implicit branches agree with the literal bracket selector by the uniform
negative derivative floor. Compactness extends their smoothness to a single
signed amplitude neighborhood, including the spatial endpoints.
-/
public section
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- The literal mixed selector chooses a bracket zero whenever one exists. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:h). -/
-- @node: mixedRoot_bracket_spec
lemma mixedRoot_bracket_spec (η ζ u : ℝ)
    (h : ∃ q ∈ Set.Ioo (3/4 : ℝ) (5/4), mixedEquation η ζ u q = 0) :
    mixedRoot η ζ u ∈ Set.Ioo (3/4 : ℝ) (5/4) ∧
      mixedEquation η ζ u (mixedRoot η ζ u) = 0 := by
  rw [mixedRoot, dif_pos h]
  exact Classical.choose_spec h

/-- At zero amplitudes the selector is exactly the affine-equation root one. [the stated conclusion](goal) holds. -/
-- @node: mixedRoot_zero_amplitudes
lemma mixedRoot_zero_amplitudes (u : ℝ) : mixedRoot 0 0 u = 1 := by
  have h : ∃ q ∈ Set.Ioo (3/4 : ℝ) (5/4), mixedEquation 0 0 u q = 0 :=
    ⟨1, by constructor <;> norm_num, by rw [mixedEquation_zero_amplitudes]; ring⟩
  have hz := (mixedRoot_bracket_spec 0 0 u h).2
  rw [mixedEquation_zero_amplitudes] at hz
  linarith

/-- The derivative floor holds on the whole bracket for parameters in a full
neighborhood of every zero-amplitude spatial point, even at the endpoints. [the documented result](goal) -/
-- @node: mixedEquation_eventually_bracket_deriv_neg
lemma mixedEquation_eventually_bracket_deriv_neg (u : ℝ) :
    ∀ᶠ a : Fin 3 → ℝ in 𝓝 ![0,0,u],
      ∀ q ∈ Set.Icc (3/4 : ℝ) (5/4),
        deriv (mixedEquation (a 0) (a 1) (a 2)) q < -1/2 := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro q hq
  have hc : ContinuousAt (fun z : (Fin 3 → ℝ) × ℝ =>
      deriv (mixedEquation (z.1 0) (z.1 1) (z.1 2)) z.2) (![0,0,u],q) := by
    exact (mixedEquation_partial_continuousAt_zero u q).comp
      (f := fun z : (Fin 3 → ℝ) × ℝ => ((z.1 0,z.1 1),(z.1 2,z.2)))
      (by fun_prop : ContinuousAt (fun z : (Fin 3 → ℝ) × ℝ =>
        ((z.1 0,z.1 1),(z.1 2,z.2))) (![0,0,u],q))
  exact hc.eventually (gt_mem_nhds
    (by simp only [mixedEquation_deriv_zero]; norm_num :
      deriv (mixedEquation 0 0 u) q < (-1/2 : ℝ)))

/-- The actual selected mixed root is smooth through both signed amplitude axes
at every spatial point. Local uniqueness identifies it with the implicit branch. [the documented result](goal) -/
-- @node: mixedRoot_contDiffAt_zero
lemma mixedRoot_contDiffAt_zero (u : ℝ) :
    ContDiffAt ℝ ⊤ (fun a : Fin 3 → ℝ => mixedRoot (a 0) (a 1) (a 2)) ![0,0,u] := by
  let F : ((Fin 3 → ℝ) × ℝ) → ℝ := fun z =>
    mixedEquation (z.1 0) (z.1 1) (z.1 2) z.2
  apply scalar_bracket_selector_contDiffAt 3 F
    (fun a => mixedRoot (a 0) (a 1) (a 2)) ![0,0,u] (3/4) (5/4)
  · rw [show mixedRoot (![0,0,u] 0) (![0,0,u] 1) (![0,0,u] 2) = 1 from
      mixedRoot_zero_amplitudes u]
    exact (mixedEquation_contDiffAt_zero u 1).comp (![0,0,u],1)
      (by fun_prop : ContDiffAt ℝ ⊤ (fun z : (Fin 3 → ℝ) × ℝ =>
        ((z.1 0,z.1 1),(z.1 2,z.2))) (![0,0,u],1))
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      mixedRoot_zero_amplitudes]
    constructor <;> norm_num
  · simp [F, mixedRoot_zero_amplitudes, mixedEquation_zero_amplitudes]
  · simpa [F, mixedRoot_zero_amplitudes] using
      (show deriv (mixedEquation 0 0 u) 1 ≠ 0 by rw [mixedEquation_deriv_zero]; norm_num)
  · intro a ha
    exact mixedRoot_bracket_spec (a 0) (a 1) (a 2) ha
  · filter_upwards [mixedEquation_eventually_bracket_deriv_neg u] with a ha
    intro p hp q hq hep heq
    exact mixedEquation_bracket_unique (a 0) (a 1) (a 2) ha p q hp hq hep heq

/-- Smoothness of the literal selector holds on one absolute closed signed
amplitude square, on full neighborhoods even at its spatial endpoints. [the documented result](goal) -/
-- @node: mixedRoot_uniform_contDiffAt
lemma mixedRoot_uniform_contDiffAt : ∃ ε : ℝ, 0 < ε ∧
    ∀ η ζ u : ℝ, |η| ≤ ε → |ζ| ≤ ε → u ∈ Set.Icc (0 : ℝ) 1 →
      ContDiffAt ℝ ⊤ (fun a : Fin 3 → ℝ => mixedRoot (a 0) (a 1) (a 2)) ![η,ζ,u] := by
  have hevent : ∀ᶠ a : ℝ × ℝ in 𝓝 (0,0), ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ContDiffAt ℝ ⊤ (fun v : Fin 3 → ℝ => mixedRoot (v 0) (v 1) (v 2)) ![a.1,a.2,u] := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    obtain ⟨S, hS, hSmooth⟩ := (mixedRoot_contDiffAt_zero u).contDiffOn le_rfl (by simp)
    obtain ⟨D, hDsub, hDopen, hDbase⟩ := mem_nhds_iff.mp hS
    have hpre : ∀ᶠ z : (ℝ × ℝ) × ℝ in 𝓝 ((0,0),u), ![z.1.1,z.1.2,z.2] ∈ D :=
      (by fun_prop : ContinuousAt (fun z : (ℝ × ℝ) × ℝ => ![z.1.1,z.1.2,z.2]) ((0,0),u))
        (hDopen.mem_nhds hDbase)
    filter_upwards [hpre] with z hz
    exact (hSmooth.mono hDsub).contDiffAt (hDopen.mem_nhds hz)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨δ/2, by linarith, ?_⟩
  intro η ζ u hη hζ hu
  have hmem : (η,ζ) ∈ Metric.ball (0,0) δ := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero]
    exact max_lt (by linarith) (by linarith)
  exact hball hmem u hu

/-- On the same signed neighborhood, every fixed derivative order of the
actual mixed selector has a finite absolute bound. [the documented result](goal) -/
-- @node: mixedRoot_uniform_smooth_derivative_bounds
lemma mixedRoot_uniform_smooth_derivative_bounds : ∃ ε : ℝ, 0 < ε ∧
    (∀ v : Fin 3 → ℝ, |v 0| ≤ ε → |v 1| ≤ ε → v 2 ∈ Set.Icc (0 : ℝ) 1 →
      ContDiffAt ℝ ⊤ (fun a : Fin 3 → ℝ => mixedRoot (a 0) (a 1) (a 2)) v) ∧
    (∀ m : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ v : Fin 3 → ℝ,
      |v 0| ≤ ε → |v 1| ≤ ε → v 2 ∈ Set.Icc (0 : ℝ) 1 →
      ‖iteratedFDeriv ℝ m (fun a : Fin 3 → ℝ => mixedRoot (a 0) (a 1) (a 2)) v‖ ≤ B) := by
  obtain ⟨ε, hε, hSmooth⟩ := mixedRoot_uniform_contDiffAt
  have hvec (v : Fin 3 → ℝ) : ![v 0,v 1,v 2] = v := by
    funext i
    fin_cases i <;> rfl
  have hAt (v : Fin 3 → ℝ) (h0 : |v 0| ≤ ε) (h1 : |v 1| ≤ ε)
      (h2 : v 2 ∈ Set.Icc (0 : ℝ) 1) :
      ContDiffAt ℝ ⊤ (fun a : Fin 3 → ℝ => mixedRoot (a 0) (a 1) (a 2)) v := by
    simpa only [hvec] using hSmooth (v 0) (v 1) (v 2) h0 h1 h2
  let K : Set (Fin 3 → ℝ) := Set.pi Set.univ
    (fun i => if i = 2 then Set.Icc (0 : ℝ) 1 else Set.Icc (-ε) ε)
  have hK : IsCompact K := isCompact_univ_pi (fun i => by split <;> exact isCompact_Icc)
  have hmem (v : Fin 3 → ℝ) : v ∈ K ↔
      |v 0| ≤ ε ∧ |v 1| ≤ ε ∧ v 2 ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [K, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro h
      exact ⟨abs_le.mpr (by simpa using h 0), abs_le.mpr (by simpa using h 1),
        by simpa using h 2⟩
    · rintro ⟨h0,h1,h2⟩ i
      fin_cases i
      · simpa using abs_le.mp h0
      · simpa using abs_le.mp h1
      · simpa using h2
  refine ⟨ε, hε, hAt, ?_⟩
  intro m
  obtain ⟨B,hB,hBound⟩ := compact_smooth_derivative_bounds 3
    (fun a : Fin 3 → ℝ => mixedRoot (a 0) (a 1) (a 2)) K hK
    (fun v hv => hAt v (hmem v |>.mp hv).1 (hmem v |>.mp hv).2.1
      (hmem v |>.mp hv).2.2) m
  exact ⟨B,hB,fun v h0 h1 h2 => hBound v ((hmem v).mpr ⟨h0,h1,h2⟩)⟩

end CausalSmith.Stat.LogoddsLowsmoothFrontier

module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairAmplitudeSymmetry
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairCellSmoothness

/-! # Smooth fair numerator and Taylor-axis cancellations

The numerator is smooth on full neighborhoods of the closed effect range,
small signed amplitudes, and the entire centering bracket. Sign symmetry kills
its first amplitude derivative at zero; the zero-effect identity kills every
amplitude derivative there. These are inputs to the two Taylor divisions.
-/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The shifted centering risk remains positive uniformly over the sign law.](goal) Under [the stated assumptions](hyp:hδ). Under [the stated assumptions](hyp:hξ). -/
-- @node: fairNumerator_shifted_risk_pos
lemma fairNumerator_shifted_risk_pos (δ ξ u : ℝ) (s : Bool × Bool)
    (hδ : |δ| ≤ 1 / 100) (hξ : ξ ∈ Set.Icc (3 / 10 : ℝ) (1 / 2)) :
    0 < ξ + δ * localSignField u s := by
  have hprod : |δ * localSignField u s| ≤ 1 / 50 := by
    rw [abs_mul]
    calc
      _ ≤ (1 / 100 : ℝ) * 2 :=
        mul_le_mul hδ (localSignField_abs_le_two u s) (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  linarith [(abs_le.mp hprod).1, hξ.1]

/-- [Smoothness concerns the actual numerator, jointly in all four variables.](goal) Under [the stated assumptions](hyp:hδ). Under [the stated assumptions](hyp:ht,hξ). -/
-- @node: fairNumerator_contDiffAt
lemma fairNumerator_contDiffAt (v : Fin 4 → ℝ)
    (ht : v 0 ∈ Set.Icc (0 : ℝ) (1 / 4)) (hδ : |v 1| ≤ 1 / 100)
    (hξ : v 2 ∈ Set.Icc (3 / 10 : ℝ) (1 / 2)) :
    ContDiffAt ℝ ⊤ (fun w : Fin 4 → ℝ => fairNumerator (w 0) (w 1) (w 2) (w 3)) v := by
  have hT : ContDiffAt ℝ ⊤ (fun w : Fin 4 → ℝ => comparatorEffect (w 0) (w 1)) v := by
    have hp : ContDiffAt ℝ ⊤ (fun w : Fin 4 → ℝ => ![w 0,w 1]) v := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> change ContDiffAt ℝ ⊤ (fun w : Fin 4 → ℝ => w _) v <;> fun_prop
    exact (comparatorEffect_contDiffAt ![v 0,v 1] ht hδ).comp v hp
  unfold fairNumerator signAverage
  apply ContDiffAt.sub
  · apply ContDiffAt.mul contDiffAt_const
    apply ContDiffAt.sum
    intro s hs
    unfold riskShift localSignField
    apply ContDiffAt.div
    · fun_prop
    · fun_prop
    · exact ne_of_gt (riskShift_denominator_pos (v 0)
        (v 2 + v 1 * localSignField (v 3) s) ht.1
        (fairNumerator_shifted_risk_pos _ _ _ s hδ hξ).le)
  · unfold riskShift
    apply ContDiffAt.div
    · fun_prop
    · fun_prop
    · have hTpos : 0 ≤ comparatorEffect (v 0) (v 1) := by
        linarith [(comparatorEffect_range_bounds _ _ ht hδ).1, ht.1]
      exact ne_of_gt (riskShift_denominator_pos _ _ hTpos (by linarith [hξ.1]))

/-- Evenness gives the missing linear Taylor coefficient without excluding the axes. [the stated conclusion](goal) holds. -/
-- @node: fairNumerator_deriv_zero_amplitude
lemma fairNumerator_deriv_zero_amplitude (t ξ u : ℝ) :
    deriv (fun δ => fairNumerator t δ ξ u) 0 = 0 := by
  have he : (fun δ => fairNumerator t (-δ) ξ u) =
      (fun δ => fairNumerator t δ ξ u) := funext (fun δ => fairNumerator_even t δ ξ u)
  have h := deriv_comp_neg (fun δ => fairNumerator t δ ξ u) 0
  rw [he] at h
  simp only [neg_zero] at h
  linarith

/-- At zero effect the whole second amplitude-derivative function vanishes. [the stated conclusion](goal) holds. -/
-- @node: fairNumerator_second_deriv_zero_effect
lemma fairNumerator_second_deriv_zero_effect (δ ξ u : ℝ) :
    deriv (deriv (fun D => fairNumerator 0 D ξ u)) δ = 0 := by
  simp only [fairNumerator_zero_effect]
  have he : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 :=
    funext (fun x => deriv_const x 0)
  rw [he]
  exact deriv_const δ 0

/-- The zero linear coefficient is an actual derivative at every allowed effect
and center, rather than only the value of a totalized derivative. [the documented result](goal) Under [the stated assumptions](hyp:ht,hξ). -/
-- @node: fairNumerator_hasDerivAt_zero_amplitude
lemma fairNumerator_hasDerivAt_zero_amplitude (t ξ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4))
    (hξ : ξ ∈ Set.Icc (3 / 10 : ℝ) (1 / 2)) :
    HasDerivAt (fun δ => fairNumerator t δ ξ u) 0 0 := by
  have hp : ContDiffAt ℝ ⊤ (fun δ : ℝ => ![t,δ,ξ,u]) 0 := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · change ContDiffAt ℝ ⊤ (fun _ : ℝ => t) 0
      fun_prop
    · change ContDiffAt ℝ ⊤ (fun δ : ℝ => δ) 0
      fun_prop
    · change ContDiffAt ℝ ⊤ (fun _ : ℝ => ξ) 0
      fun_prop
    · change ContDiffAt ℝ ⊤ (fun _ : ℝ => u) 0
      fun_prop
  have hf := (fairNumerator_contDiffAt ![t,0,ξ,u] ht (by norm_num) hξ).comp 0 hp
  have hd : DifferentiableAt ℝ (fun δ => fairNumerator t δ ξ u) 0 :=
    hf.differentiableAt (by simp)
  simpa only [fairNumerator_deriv_zero_amplitude] using hd.hasDerivAt

/-- Every fixed-order derivative of the actual numerator has one absolute
bound on the full closed effect, signed amplitude, center, and coordinate box. [the documented result](goal) -/
-- @node: fairNumerator_uniform_derivative_bounds
lemma fairNumerator_uniform_derivative_bounds :
    ∀ m : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ v : Fin 4 → ℝ,
      v 0 ∈ Set.Icc (0 : ℝ) (1 / 4) → |v 1| ≤ 1 / 100 →
      v 2 ∈ Set.Icc (3 / 10 : ℝ) (1 / 2) → v 3 ∈ Set.Icc (0 : ℝ) 1 →
      ‖iteratedFDeriv ℝ m (fun w : Fin 4 → ℝ =>
        fairNumerator (w 0) (w 1) (w 2) (w 3)) v‖ ≤ B := by
  let K : Set (Fin 4 → ℝ) := Set.pi Set.univ
    (fun i => if i = 0 then Set.Icc (0 : ℝ) (1 / 4)
      else if i = 1 then Set.Icc (-(1 / 100 : ℝ)) (1 / 100)
      else if i = 2 then Set.Icc (3 / 10 : ℝ) (1 / 2)
      else Set.Icc (0 : ℝ) 1)
  have hK : IsCompact K := isCompact_univ_pi (fun i => by
    split
    · exact isCompact_Icc
    · split
      · exact isCompact_Icc
      · split <;> exact isCompact_Icc)
  have hmem (v : Fin 4 → ℝ) : v ∈ K ↔
      v 0 ∈ Set.Icc (0 : ℝ) (1 / 4) ∧ |v 1| ≤ 1 / 100 ∧
      v 2 ∈ Set.Icc (3 / 10 : ℝ) (1 / 2) ∧ v 3 ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [K, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro h
      exact ⟨by simpa using h 0, abs_le.mpr (by simpa using h 1),
        by simpa using h 2, by simpa using h 3⟩
    · rintro ⟨ht,hδ,hξ,hu⟩ i
      fin_cases i
      · simpa using ht
      · simpa using abs_le.mp hδ
      · simpa using hξ
      · simpa using hu
  intro m
  obtain ⟨B,hB,hBound⟩ := compact_smooth_derivative_bounds 4 _ K hK
    (fun v hv => fairNumerator_contDiffAt v (hmem v |>.mp hv).1
      (hmem v |>.mp hv).2.1 (hmem v |>.mp hv).2.2.1) m
  exact ⟨B,hB,fun v ht hδ hξ hu => hBound v ((hmem v).mpr ⟨ht,hδ,hξ,hu⟩)⟩

end CausalSmith.Stat.LogoddsLowsmoothFrontier

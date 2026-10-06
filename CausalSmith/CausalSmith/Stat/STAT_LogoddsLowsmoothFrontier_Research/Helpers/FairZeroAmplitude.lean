module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairRootNearZero

/-! # Fair calibration on the zero - amplitude axis

The second amplitude derivative of the finite sign average depends only on
the unit second moment of the sign field. Thus the Taylor - normalized equation
is independent of position at zero amplitude, and the exact endpoint identity
supplies a center root throughout that axis.
-/
public section
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- The derivative of the risk under an affine amplitude perturbation is the
explicit squared - denominator expression. [the documented result](goal) Under [the stated assumptions](hyp:hden). -/
-- @node: riskShift_hasDerivAt_amplitude
lemma riskShift_hasDerivAt_amplitude (t ξ z δ : ℝ)
    (hden : 1 + (Real.exp t - 1) * (ξ + δ * z) ≠ 0) :
    HasDerivAt (fun D => riskShift t (ξ + D * z))
      (Real.exp t * z / (1 + (Real.exp t - 1) * (ξ + δ * z)) ^ 2) δ := by
  have hx := (hasDerivAt_const δ ξ).add ((hasDerivAt_id δ).mul_const z)
  convert (hx.const_mul (Real.exp t)).div
    ((hasDerivAt_const δ (1 : ℝ)).add (hx.const_mul (Real.exp t - 1))) hden using 1 <;>
    first | rfl | (dsimp; field_simp; ring)

/-- The second amplitude derivative of the risk at zero amplitude contains
exactly the squared perturbation mark. [the documented result](goal) Under [the stated assumptions](hyp:hden). -/
-- @node: riskShift_hasDerivAt_deriv_zero_amplitude
lemma riskShift_hasDerivAt_deriv_zero_amplitude (t ξ z : ℝ)
    (hden : 1 + (Real.exp t - 1) * ξ ≠ 0) :
    HasDerivAt (deriv (fun D => riskShift t (ξ + D * z)))
      (-2 * Real.exp t * (Real.exp t - 1) * z ^ 2 / (1 + (Real.exp t - 1) * ξ) ^ 3) 0 := by
  have hx := (hasDerivAt_const (0 : ℝ) ξ).add ((hasDerivAt_id 0).mul_const z)
  have hb := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
    (hx.const_mul (Real.exp t - 1))
  have hd := (hasDerivAt_const (0 : ℝ) (Real.exp t * z)).div (hb.pow 2)
    (by simpa using pow_ne_zero 2 hden)
  have hd' : HasDerivAt
      (fun D => Real.exp t * z / (1 + (Real.exp t - 1) * (ξ + D * z)) ^ 2)
      (-2 * Real.exp t * (Real.exp t - 1) * z ^ 2 / (1 + (Real.exp t - 1) * ξ) ^ 3) 0 := by
    convert hd using 1 <;> first | rfl | (dsimp; field_simp [hden]; ring)
  apply hd'.congr_of_eventuallyEq
  have he : ∀ᶠ D : ℝ in 𝓝 0, 1 + (Real.exp t - 1) * (ξ + D * z) ≠ 0 :=
    (by fun_prop : ContinuousAt (fun D : ℝ => 1 + (Real.exp t - 1) * (ξ + D * z)) 0).eventually_ne
      (by simpa using hden)
  filter_upwards [he] with D hD
  exact (riskShift_hasDerivAt_amplitude t ξ z D hD).deriv

/-- The second derivative of the sign - averaged risk is independent of the
within - cell coordinate because every sign field has unit second moment. [the documented result](goal) Under [the stated assumptions](hyp:hden). -/
-- @node: fairRiskAverage_second_deriv_zero_amplitude
lemma fairRiskAverage_second_deriv_zero_amplitude (t ξ u : ℝ)
    (hden : 1 + (Real.exp t - 1) * ξ ≠ 0) :
    deriv (deriv (fun D => signAverage (fun s => riskShift t (ξ + D * localSignField u s)))) 0 =
      -2 * Real.exp t * (Real.exp t - 1) / (1 + (Real.exp t - 1) * ξ) ^ 3 := by
  have hz : (1 / 4 : ℝ) * ∑ s : Bool × Bool, (localSignField u s) ^ 2 = 1 := by
    simp [localSignField, signValue, Fintype.sum_prod_type]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * u / 2)]
  have h2 := (HasDerivAt.sum (u := Finset.univ) (fun s _ =>
    riskShift_hasDerivAt_deriv_zero_amplitude t ξ (localSignField u s) hden)).const_mul (1 / 4 : ℝ)
  have hc : (1 / 4 : ℝ) * ∑ s : Bool × Bool,
      -2 * Real.exp t * (Real.exp t - 1) * (localSignField u s) ^ 2 /
        (1 + (Real.exp t - 1) * ξ) ^ 3 =
      -2 * Real.exp t * (Real.exp t - 1) / (1 + (Real.exp t - 1) * ξ) ^ 3 := by
    simp_rw [div_eq_mul_inv]
    calc
      _ = (-2 * Real.exp t * (Real.exp t - 1) * ((1 + (Real.exp t - 1) * ξ) ^ 3)⁻¹) *
          ((1 / 4 : ℝ) * ∑ s : Bool × Bool, (localSignField u s) ^ 2) := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = _ := by rw [hz]; ring
  rw [hc] at h2
  apply (h2.congr_of_eventuallyEq ?_).deriv
  have he : ∀ᶠ D : ℝ in 𝓝 0, ∀ s : Bool × Bool,
      1 + (Real.exp t - 1) * (ξ + D * localSignField u s) ≠ 0 := by
    rw [Filter.eventually_all]
    intro s
    exact (by fun_prop : ContinuousAt
      (fun D : ℝ => 1 + (Real.exp t - 1) * (ξ + D * localSignField u s)) 0).eventually_ne
      (by simpa using hden)
  filter_upwards [he] with D hD
  have h1 := ((HasDerivAt.sum (u := Finset.univ) (fun s _ =>
    riskShift_hasDerivAt_amplitude t ξ (localSignField u s) D (hD s))).const_mul
      (1 / 4 : ℝ)).deriv
  change deriv (fun D => signAverage (fun s => riskShift t (ξ + D * localSignField u s))) D =
    (1 / 4 : ℝ) * ∑ s : Bool × Bool, deriv (fun D => riskShift t (ξ + D * localSignField u s)) D
  refine h1.trans ?_
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  exact (riskShift_hasDerivAt_amplitude t ξ (localSignField u s) D (hD s)).deriv.symm

/-- The comparator term has no position argument, while the averaged risk's
second derivative depends only on the unit sign variance. Hence the actual
numerator's second derivative agrees with its endpoint value. [the documented result](goal) Under [the stated assumptions](hyp:ht,hξ). -/
-- @node: fairNumerator_second_deriv_zero_amplitude_endpoint
lemma fairNumerator_second_deriv_zero_amplitude_endpoint (t ξ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4))
    (hξ : ξ ∈ Set.Icc (3 / 10 : ℝ) (1 / 2)) :
    deriv (deriv (fun D => fairNumerator t D ξ u)) 0 =
      deriv (deriv (fun D => fairNumerator t D ξ 0)) 0 := by
  let A : ℝ → ℝ → ℝ := fun u D => signAverage (fun s => riskShift t (ξ + D * localSignField u s))
  let C : ℝ → ℝ := fun D => riskShift (comparatorEffect t D) ξ
  have hA (u D : ℝ) (hD : |D| ≤ 1 / 100) : ContDiffAt ℝ ⊤ (A u) D := by
    unfold A signAverage
    apply ContDiffAt.mul contDiffAt_const
    apply ContDiffAt.sum
    intro s hs
    apply (riskShift_contDiffAt ![t,ξ + D * localSignField u s] ?_).comp D
      (show ContDiffAt ℝ ⊤ (fun x : ℝ => ![t,ξ + x * localSignField u s]) D by
        apply contDiffAt_pi.mpr
        intro i
        fin_cases i <;> dsimp <;> fun_prop)
    exact ne_of_gt (riskShift_denominator_pos _ _ ht.1
      (fairNumerator_shifted_risk_pos D ξ u s hD hξ).le)
  have hN (u D : ℝ) (hD : |D| ≤ 1 / 100) :
      ContDiffAt ℝ ⊤ (fun x => fairNumerator t x ξ u) D := by
    have hp : ContDiffAt ℝ ⊤ (fun x : ℝ => ![t,x,ξ,u]) D := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop
    exact (fairNumerator_contDiffAt ![t,D,ξ,u] ht hD hξ).comp D hp
  have hC (D : ℝ) (hD : |D| ≤ 1 / 100) : ContDiffAt ℝ ⊤ C D := by
    have he : C = fun x => A 0 x - fairNumerator t x ξ 0 := by
      funext x
      dsimp [C, A, fairNumerator]
      ring
    rw [he]
    exact (hA 0 D hD).sub (hN 0 D hD)
  have hsecond (u : ℝ) : deriv (deriv (fun D => fairNumerator t D ξ u)) 0 =
      deriv (deriv (A u)) 0 - deriv (deriv C) 0 := by
    have he : deriv (fun D => fairNumerator t D ξ u) =ᶠ[𝓝 0]
        fun D => deriv (A u) D - deriv C D := by
      filter_upwards [isOpen_Ioo.mem_nhds
        (show (0 : ℝ) ∈ Set.Ioo (-(1 / 100 : ℝ)) (1 / 100) by constructor <;> norm_num)] with D hD
      have hδ : |D| ≤ 1 / 100 := abs_le.mpr ⟨hD.1.le,hD.2.le⟩
      exact deriv_sub ((hA u D hδ).differentiableAt (by simp))
        ((hC D hδ).differentiableAt (by simp))
    rw [he.deriv_eq]
    apply deriv_sub
    · exact ((hA u 0 (by norm_num)).derivWithin (m := ⊤)
        (by simp)).differentiableAt (by simp)
    · exact ((hC 0 (by norm_num)).derivWithin (m := ⊤)
        (by simp)).differentiableAt (by simp)
  rw [hsecond u, hsecond 0]
  dsimp only [A]
  rw [fairRiskAverage_second_deriv_zero_amplitude t ξ u
    (ne_of_gt (riskShift_denominator_pos _ _ ht.1 (by linarith [hξ.1]))),
    fairRiskAverage_second_deriv_zero_amplitude t ξ 0
    (ne_of_gt (riskShift_denominator_pos _ _ ht.1 (by linarith [hξ.1])))]

/-- Both integral Taylor divisions preserve the position - independent second
amplitude coefficient, including the effect - range boundary points. [the documented result](goal) Under [the stated assumptions](hyp:ht,hξ). -/
-- @node: fairEquation_zero_amplitude_endpoint
lemma fairEquation_zero_amplitude_endpoint (t ξ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4))
    (hξ : ξ ∈ Set.Icc (3 / 10 : ℝ) (1 / 2)) :
    fairEquation t 0 ξ u = fairEquation t 0 ξ 0 := by
  have hdiff (T u : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) (1 / 4)) :
      DifferentiableAt ℝ (fun x => deriv (deriv (fun D => fairNumerator x D ξ u)) 0) T := by
    have hp : ContDiffAt ℝ ⊤ (fun x : ℝ => ![x,0,ξ,u]) T := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop
    exact ((fairNumerator_second_amplitude_deriv_contDiffAt ![T,0,ξ,u]
      hT (by norm_num) hξ).comp T hp).differentiableAt (by simp)
  have he (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) (1 / 4)) :
      deriv (fun x => deriv (deriv (fun D => fairNumerator x D ξ u)) 0) T =
        deriv (fun x => deriv (deriv (fun D => fairNumerator x D ξ 0)) 0) T := by
    have hw : HasDerivWithinAt
        (fun x => deriv (deriv (fun D => fairNumerator x D ξ 0)) 0)
        (deriv (fun x => deriv (deriv (fun D => fairNumerator x D ξ u)) 0) T)
        (Set.Icc (0 : ℝ) (1 / 4)) T :=
      (hdiff T u hT).hasDerivAt.hasDerivWithinAt.congr_of_mem
        (fun x hx => (fairNumerator_second_deriv_zero_amplitude_endpoint x ξ u hx hξ).symm) hT
    have hUnique := uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1 / 4) T hT
    exact (hw.derivWithin hUnique).symm.trans
      ((hdiff T 0 hT).hasDerivAt.hasDerivWithinAt.derivWithin hUnique)
  unfold fairEquation
  simp only [mul_zero]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
  have hst : s * t ∈ Set.Icc (0 : ℝ) (1 / 4) :=
    ⟨mul_nonneg hs.1 ht.1, by nlinarith [hs.2,ht.1,ht.2]⟩
  apply intervalIntegral.integral_congr
  intro v hv
  rw [he (s * t) hst]

/-- The exact endpoint equation supplies the asymmetric center as a root on
the entire zero - amplitude axis, uniformly in effect and position. [the documented result](goal) Under [the stated assumptions](hyp:ht). -/
-- @node: fairEquation_zero_amplitude_center
lemma fairEquation_zero_amplitude_center (t u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4)) :
    fairEquation t 0 (2 / 5) u = 0 := by
  rw [fairEquation_zero_amplitude_endpoint t (2 / 5) u ht (by constructor <;> norm_num)]
  exact fairEquation_endpoint_zero t 0 0 ht (by norm_num) (Or.inl rfl)

/-- The center root lies strictly in the selector bracket at every point of
the zero - amplitude axis. [the documented result](goal) Under [the stated assumptions](hyp:ht). -/
-- @node: fairEquation_zero_amplitude_exists
lemma fairEquation_zero_amplitude_exists (t u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4)) :
    ∃ p ∈ Set.Ioo (3 / 10 : ℝ) (1 / 2), fairEquation t 0 p u = 0 :=
  ⟨2 / 5, by constructor <;> norm_num, fairEquation_zero_amplitude_center t u ht⟩

/-- An actual root exists on the zero - amplitude axis, so the literal selector
satisfies the normalized equation there without invoking a fallback case. [the documented result](goal) Under [the stated assumptions](hyp:ht). -/
-- @node: fairRoot_zero_amplitude_spec
lemma fairRoot_zero_amplitude_spec (t u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4)) :
    fairRoot t 0 u ∈ Set.Ioo (3 / 10 : ℝ) (1 / 2) ∧
      fairEquation t 0 (fairRoot t 0 u) u = 0 :=
  fairRoot_spec t 0 u (fairEquation_zero_amplitude_exists t u ht)

/-- The near - zero uniqueness neighborhood identifies the literal selector
with the fixed center at the cell endpoints and on the amplitude axis. [the documented result](goal) -/
-- @node: fairRoot_near_zero_center_identities
lemma fairRoot_near_zero_center_identities : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 100 ∧
    ε ≤ 1 / 4 ∧ ∀ t δ u : ℝ, t ∈ Set.Icc (0 : ℝ) ε → |δ| ≤ ε →
      u ∈ Set.Icc (0 : ℝ) 1 →
      fairRoot t δ 0 = 2 / 5 ∧ fairRoot t δ 1 = 2 / 5 ∧ fairRoot t 0 u = 2 / 5 := by
  obtain ⟨ε₀,hε₀,hUnique⟩ := fairRoot_uniform_spec_near_zero
  let ε := min ε₀ (1 / 100)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hsmall : ε ≤ 1 / 100 := min_le_right _ _
  have hquarter : ε ≤ 1 / 4 := by linarith
  refine ⟨ε,hε,hsmall,hquarter,?_⟩
  intro t δ u ht hδ hu
  have ht' : t ∈ Set.Icc (0 : ℝ) (1 / 4) := ⟨ht.1,ht.2.trans hquarter⟩
  have ht₀ : |t| ≤ ε₀ := by
    rw [abs_of_nonneg ht.1]
    exact ht.2.trans (min_le_left _ _)
  have hδ₀ : |δ| ≤ ε₀ := hδ.trans (min_le_left _ _)
  have hb : (2 / 5 : ℝ) ∈ Set.Ioo (3 / 10) (1 / 2) := by constructor <;> norm_num
  have h0 := (hUnique t δ 0 ht₀ hδ₀ (by constructor <;> norm_num)).2 (2 / 5) hb
    (fairEquation_endpoint_zero t δ 0 ht' (hδ.trans hsmall) (Or.inl rfl))
  have h1 := (hUnique t δ 1 ht₀ hδ₀ (by constructor <;> norm_num)).2 (2 / 5) hb
    (fairEquation_endpoint_zero t δ 1 ht' (hδ.trans hsmall) (Or.inr rfl))
  have ha := (hUnique t 0 u ht₀ (by simpa using hε₀.le) hu).2 (2 / 5) hb
    (fairEquation_zero_amplitude_center t u ht')
  exact ⟨h0.symm,h1.symm,ha.symm⟩

end CausalSmith.Stat.LogoddsLowsmoothFrontier

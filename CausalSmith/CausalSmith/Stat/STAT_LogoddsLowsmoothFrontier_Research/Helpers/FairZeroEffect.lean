module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairEquationSmoothness

/-! # Fair calibration on the zero-effect axis

The effect derivatives of the literal risk and comparator formulas identify the
limiting normalized equation and its unique bracket root.
-/
public section
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [At zero effect the logistic risk slope is its Bernoulli variance. [the stated conclusion](goal) holds. -/
-- @node: riskShift_hasDerivAt_zero_effect
lemma riskShift_hasDerivAt_zero_effect (ξ : ℝ) :
    HasDerivAt (fun t => riskShift t ξ) (ξ*(1-ξ)) 0 := by
  unfold riskShift
  convert ((Real.hasDerivAt_exp 0).mul_const ξ).div
    ((hasDerivAt_const 0 (1 : ℝ)).add
      (((Real.hasDerivAt_exp 0).sub_const 1).mul_const ξ)) (by simp) using 1 <;>
    first | rfl | (norm_num; ring)

/-- The comparator's zero-effect slope accounts for the amplitude variance. [the stated conclusion](goal) holds. -/
-- @node: comparatorEffect_hasDerivAt_zero_effect
lemma comparatorEffect_hasDerivAt_zero_effect (δ : ℝ) :
    HasDerivAt (fun t => comparatorEffect t δ) (1-δ^2/(6 / 25)) 0 := by
  have hd := (Real.hasDerivAt_exp 0).sub_const 1
  have hB := (hasDerivAt_const 0 (1 : ℝ)).add (hd.mul_const (2 / 5))
  have h1 := (hd.mul_const (δ^2)).div (hB.const_mul (2 / 5)) (by norm_num)
  have h2 := (hd.mul_const (δ^2)).div (hB.const_mul (1-2 / 5)) (by norm_num)
  have hlog1 := ((hasDerivAt_const 0 (1 : ℝ)).sub h1).log (by norm_num)
  have hlog2 := ((hasDerivAt_const 0 (1 : ℝ)).add h2).log (by norm_num)
  convert ((hasDerivAt_id 0).add hlog1).sub hlog2 using 1 <;>
    first | rfl | (simp; ring)

/-- Differentiating the actual finite sign average at zero effect gives exactly
its variance cancellation against the deterministic comparator. [the documented result](goal) -/
-- @node: fairNumerator_hasDerivAt_zero_effect
lemma fairNumerator_hasDerivAt_zero_effect (δ ξ u : ℝ) :
    HasDerivAt (fun t => fairNumerator t δ ξ u)
      (δ^2*(-1+ξ*(1-ξ)/(6 / 25))) 0 := by
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (fun s _ => riskShift_hasDerivAt_zero_effect (ξ+δ*localSignField u s))
  have hr : HasDerivAt (fun t => riskShift t ξ) (ξ*(1-ξ)) (comparatorEffect 0 δ) := by
    rw [comparatorEffect_zero_effect]
    exact riskShift_hasDerivAt_zero_effect ξ
  have hcomp := hr.comp 0 (comparatorEffect_hasDerivAt_zero_effect δ)
  convert (hsum.const_mul (1 / 4)).sub hcomp using 1 <;> try rfl
  simp [localSignField, signValue, Fintype.sum_prod_type ]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi*u/2)]

/-- The undivided Taylor identity identifies the normalized zero-effect
value whenever the signed amplitude is nonzero. [the documented result](goal) Under [the stated assumptions](hyp:hδ,hξ,hu,hne). -/
-- @node: fairEquation_zero_effect_nonzero_amplitude
lemma fairEquation_zero_effect_nonzero_amplitude (δ ξ u : ℝ)
    (hδ : |δ| ≤ 1 / 100) (hξ : ξ ∈ Set.Icc (3 / 10 : ℝ) (1 / 2))
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hne : δ ≠ 0) :
    fairEquation 0 δ ξ u = -1+ξ*(1-ξ)/(6 / 25) := by
  have hx : ![0,δ,ξ,u] ∈ fairTaylorParameterRegion :=
    (fairTaylorParameterRegion_mem _).mpr ⟨by constructor <;> norm_num, hδ, hξ, hu⟩
  have hp : ContDiffAt ℝ ∞ (fun t : ℝ => ![t,δ,ξ,u]) 0 := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  have hH := ((fairEquation_contDiffAt _ hx).comp 0 hp).differentiableAt (by simp)
  have hd := ((hasDerivAt_id 0).mul_const (δ^2)).mul hH.hasDerivAt
  have hs : HasDerivWithinAt (fun t => fairNumerator t δ ξ u)
      (δ^2*fairEquation 0 δ ξ u) (Set.Icc (0 : ℝ) (1 / 4)) 0 := by
    have hd' : HasDerivAt (fun t => t*δ^2*fairEquation t δ ξ u)
        (δ^2*fairEquation 0 δ ξ u) 0 := by
      convert hd using 1 <;> first | rfl | simp
    exact hd'.hasDerivWithinAt.congr_of_mem
      (fun t ht => (fairEquation_mul_parameters t δ ξ u ht hδ hξ).symm)
      (by constructor <;> norm_num)
  have hunique := uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1 / 4) 0
    (by constructor <;> norm_num)
  have he := (hs.derivWithin hunique).symm.trans
    ((fairNumerator_hasDerivAt_zero_effect δ ξ u).hasDerivWithinAt.derivWithin hunique)
  exact mul_left_cancel₀ (pow_ne_zero 2 hne) he

/-- [Continuity in the signed amplitude extends the explicit zero-effect
formula through the intersection of both removable axes. [the documented result](goal) Under [the stated assumptions](hyp:hδ,hξ,hu). -/
-- @node: fairEquation_zero_effect
lemma fairEquation_zero_effect (δ ξ u : ℝ)
    (hδ : |δ| ≤ 1 / 100) (hξ : ξ ∈ Set.Icc (3 / 10 : ℝ) (1 / 2))
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    fairEquation 0 δ ξ u = -1+ξ*(1-ξ)/(6 / 25) := by
  by_cases hne : δ ≠ 0
  · exact fairEquation_zero_effect_nonzero_amplitude δ ξ u hδ hξ hu hne
  · have hz : δ = 0 := not_ne_iff.mp hne
    subst δ
    have hc : ContinuousOn (fun D => fairEquation 0 D ξ u) (Set.Icc (0 : ℝ) (1 / 100)) := by
      have hp : ContinuousOn (fun D : ℝ => ![0,D,ξ,u]) (Set.Icc (0 : ℝ) (1 / 100)) := by
        apply Continuous.continuousOn
        apply continuous_pi
        intro i
        fin_cases i <;> dsimp <;> fun_prop
      have h := fairEquation_continuousOn.comp hp (fun D hD =>
        (fairTaylorParameterRegion_mem _).mpr
          ⟨by constructor <;> norm_num,
            by change |D| ≤ 1 / 100; rw [abs_of_nonneg hD.1]; exact hD.2, hξ, hu⟩)
      simpa only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val] using h
    have he : Set.EqOn (fun D => fairEquation 0 D ξ u)
        (fun _ => -1+ξ*(1-ξ)/(6 / 25)) (Set.Ioo (0 : ℝ) (1 / 100)) := by
      intro D hD
      exact fairEquation_zero_effect_nonzero_amplitude D ξ u
        (by simpa only [abs_of_pos hD.1] using hD.2.le) hξ hu (ne_of_gt hD.1)
    exact he.of_subset_closure hc continuousOn_const Set.Ioo_subset_Icc_self
      (by rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1 / 100)]) (by constructor <;> norm_num)

/-- [The prescribed asymmetric center is a root on the entire zero-effect axis.](goal) Under [the stated assumptions](hyp:hδ). Under [the stated assumptions](hyp:hu). -/
-- @node: fairEquation_zero_effect_center
lemma fairEquation_zero_effect_center (δ u : ℝ)
    (hδ : |δ| ≤ 1 / 100) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    fairEquation 0 δ (2 / 5) u = 0 := by
  rw [fairEquation_zero_effect δ (2 / 5) u hδ (by constructor <;> norm_num) hu]
  norm_num

/-- [The other quadratic root is outside the selector bracket, so the
zero-effect center is uniquely characterized within that bracket. [the documented result](goal) Under [the stated assumptions](hyp:hδ,hu,hq,he). -/
-- @node: fairEquation_zero_effect_unique
lemma fairEquation_zero_effect_unique (δ u q : ℝ)
    (hδ : |δ| ≤ 1 / 100) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Ioo (3 / 10 : ℝ) (1 / 2))
    (he : fairEquation 0 δ q u = 0) : q = 2 / 5 := by
  rw [fairEquation_zero_effect δ q u hδ ⟨hq.1.le, hq.2.le⟩ hu] at he
  have hfactor : (q-2 / 5)*(q-3 / 5) = 0 := by
    linarith [he]
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · linarith [hq.2]

/-- [The literal root selector equals the paper's center for zero effect,
including zero amplitude and both spatial endpoints. [the documented result](goal) Under [the stated assumptions](hyp:hδ,hu). -/
-- @node: fairRoot_zero_effect
lemma fairRoot_zero_effect (δ u : ℝ)
    (hδ : |δ| ≤ 1 / 100) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    fairRoot 0 δ u = 2 / 5 := by
  apply fairRoot_eq_of_unique
  · constructor <;> norm_num
  · exact fairEquation_zero_effect_center δ u hδ hu
  · intro q hq he
    exact fairEquation_zero_effect_unique δ u q hδ hu hq he

end CausalSmith.Stat.LogoddsLowsmoothFrontier

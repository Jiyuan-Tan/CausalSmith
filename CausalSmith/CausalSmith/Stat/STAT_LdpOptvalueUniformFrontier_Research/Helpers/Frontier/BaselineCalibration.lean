module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.BlockSampling
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.Resources

/-!
# Binary baseline calibration

The first block releases randomized-response outcomes. Its estimate is unbiased,
and independence of different people gives the baseline squared-error bound.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- [Every attaining row is a probability kernel, including the constant branch](goal). -/
-- @node: frontierKernel_markov
lemma frontierKernel_markov (n d : ℕ) (eps : ℝ) (i : Fin n) :
    IsMarkovKernel (frontierKernel n d eps i) := by
  exact ⟨fun o => (frontierStage_markov n d eps i).isProbabilityMeasure
    ((o, (0 : Fin 1)), fun _ => (false, fun _ => false))⟩

/-- Assume [the stated hn condition](hyp:hn) and [the stated hi condition](hyp:hi). [A baseline row releases a sign with the randomized-response conditional mean](goal). -/
-- @node: frontierKernel_baseline_sign_mean
lemma frontierKernel_baseline_sign_mean (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (i : Fin n) (hi : i.val < (frontierResources n d eps).m0) (o : ObsRecord d) :
    (∫ z, signVal z.1 ∂frontierKernel n d eps i o) =
      privacyDelta eps * signVal o.2.2 := by
  classical
  letI := frontierKernel_markov n d eps i
  rw [integral_fintype Integrable.of_finite]
  change (∑ z, (atomLaw (frontierMass n d eps i o)).real {z} * signVal z.1) = _
  have hm : ∀ z, 0 ≤ frontierMass n d eps i o z := by
    intro z
    simp only [frontierMass, hn, hi, ↓reduceIte]
    exact mul_nonneg (binaryOutcomeMass_nonneg eps o.2.2 z.1) (by split <;> positivity)
  simp only [measureReal_def, atomLaw_singleton, ENNReal.toReal_ofReal (hm _)]
  simp only [frontierMass, hn, hi, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  simp [signVal]
  ring

/-- [The observed outcome sign has mean twice the baseline minus one](goal). -/
-- @node: observed_outcome_sign_mean
lemma observed_outcome_sign_mean (d : ℕ) (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] :
    (∫ o, signVal o.2.2 ∂observedLaw P) = 2 * baseline P - 1 := by
  rw [observedLaw, integral_map (by fun_prop) (by fun_prop)]
  have heq : (fun w : FullRecord d => signVal (observe w).2.2) =
      (fun w => 2 * (if outcome w = true then (1 : ℝ) else 0) - 1) := by
    funext w
    cases h : outcome w <;> norm_num [observe, signVal, h]
  rw [heq]
  integral_linearity
  have hevent := integral_fullRecord_event P {w | outcome w = true}
  simp only [Set.mem_setOf_eq] at hevent
  rw [hevent]
  simp [baseline]

/-- Assume [the stated hn condition](hyp:hn) and [the stated hi condition](hyp:hi). [Averaging original records gives the baseline row's unconditional mean](goal). -/
-- @node: frontier_baseline_row_mean
lemma frontier_baseline_row_mean (n d : ℕ) (eps : ℝ) (hn : n ≠ 2)
    (i : Fin n) (hi : i.val < (frontierResources n d eps).m0)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] :
    (∫ z, signVal z.1 ∂(observedLaw P).bind (frontierKernel n d eps i)) =
      privacyDelta eps * (2 * baseline P - 1) := by
  letI := frontierKernel_markov n d eps i
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  change (∫ z, signVal z.1
    ∂((frontierKernel n d eps i) ∘ₖ Kernel.const Unit (observedLaw P)) ()) = _
  rw [Kernel.integral_comp Integrable.of_finite]
  simp_rw [frontierKernel_baseline_sign_mean n d eps hn i hi]
  rw [integral_const_mul]
  change privacyDelta eps * (∫ o, signVal o.2.2 ∂observedLaw P) = _
  rw [observed_outcome_sign_mean]

/-- [Averaging any attaining row over a probability input law preserves mass one](goal). -/
-- @node: frontier_averaged_row_probability
lemma frontier_averaged_row_probability (n d : ℕ) (eps : ℝ)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (i : Fin n) :
    IsProbabilityMeasure ((observedLaw P).bind (frontierKernel n d eps i)) := by
  letI := frontierKernel_markov n d eps i
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  exact isProbabilityMeasure_bind (Kernel.measurable _).aemeasurable
    (Filter.Eventually.of_forall (fun _ => inferInstance))

/-- Assume [the stated hn condition](hyp:hn), [the stated hg condition](hyp:hg), and [the stated hbase condition](hyp:hbase). [Distinct baseline rows have additive variances and the prescribed total mean](goal). -/
-- @node: frontier_baseline_sum_moments
lemma frontier_baseline_sum_moments {n d k : ℕ} (eps : ℝ) (hn : n ≠ 2)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (g : Fin k → Fin n) (hg : Function.Injective g)
    (hbase : ∀ i, (g i).val < (frontierResources n d eps).m0) :
    let L := Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))
    (∫ z, ∑ i, signVal (z (g i)).1 ∂L) =
        (k : ℝ) * (privacyDelta eps * (2 * baseline P - 1)) ∧
      variance (fun z => ∑ i, signVal (z (g i)).1) L ≤ k := by
  classical
  let μ := fun i => (observedLaw P).bind (frontierKernel n d eps i)
  letI : ∀ i, IsProbabilityMeasure (μ i) :=
    fun i => frontier_averaged_row_probability n d eps P i
  change (∫ z, ∑ i, signVal (z (g i)).1 ∂Measure.pi μ) = _ ∧ _
  have hmean : ∀ i, (∫ z, signVal (z (g i)).1 ∂Measure.pi μ) =
      privacyDelta eps * (2 * baseline P - 1) := by
    intro i
    rw [integral_comp_eval (μ := μ) (i := g i)
      (f := fun z : FrontierMessage d => signVal z.1) (by fun_prop)]
    exact frontier_baseline_row_mean n d eps hn (g i) (hbase i) P
  have hind := (iIndepFun_pi (μ := μ)
    (X := fun (_ : Fin n) (z : FrontierMessage d) => signVal z.1)
    (fun _ => (by fun_prop))).precomp hg
  have hvar : ∀ i, variance (fun z => signVal (z (g i)).1) (Measure.pi μ) ≤ 1 := by
    intro i
    have h := variance_le_expectation_sq
      (μ := Measure.pi μ) (X := fun z => signVal (z (g i)).1)
      ((show MemLp (fun z => signVal (z (g i)).1) 2 (Measure.pi μ)
        from MemLp.of_discrete).aestronglyMeasurable)
    have hs : ∀ z : Fin n → FrontierMessage d, (signVal (z (g i)).1)^2 = 1 := by
      intro z
      cases h : (z (g i)).1 <;> norm_num [signVal, h]
    simpa [Pi.pow_apply, hs] using h
  constructor
  · rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
    simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · have hv := IndepFun.variance_sum (s := Finset.univ)
      (X := fun i z => signVal (z (g i)).1) (μ := Measure.pi μ)
      (fun _ _ => MemLp.of_discrete) (fun i _ j _ hij => hind.indepFun hij)
    change variance (fun z => ∑ i, signVal (z (g i)).1) (Measure.pi μ) ≤ _
    have hv' : variance (fun z => ∑ i, signVal (z (g i)).1) (Measure.pi μ) =
        ∑ i, variance (fun z => signVal (z (g i)).1) (Measure.pi μ) := by
      convert hv using 1
      congr 1
      funext z
      simp
    rw [hv']
    calc
      _ ≤ ∑ _i : Fin k, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hvar i)
      _ = _ := by simp

/-- [The baseline block lies in the declared participant horizon](goal). -/
-- @node: frontier_baseline_block_le
lemma frontier_baseline_block_le (n d : ℕ) (eps : ℝ) :
    (frontierResources n d eps).m0 ≤ n := by
  simp only [frontierResources]
  omega

/-- [The transcript's natural-number sum is exactly its in-horizon baseline block](goal). -/
-- @node: frontierBaselineEstimate_eq_fin_sum
lemma frontierBaselineEstimate_eq_fin_sum (n d : ℕ) (eps : ℝ)
    (z : ProtocolTranscript (frontierProtocol n d eps)) :
    frontierBaselineEstimate n d eps z = 1/2 +
      ((frontierResources n d eps).m0 : ℝ)⁻¹ *
        (∑ i : Fin (frontierResources n d eps).m0,
          signVal (z (Fin.castLE (frontier_baseline_block_le n d eps) i)).1) /
            (2 * privacyDelta eps) := by
  change Fin n → FrontierMessage d at z
  dsimp only [frontierBaselineEstimate]
  rw [← Fin.sum_univ_eq_sum_range]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val < n := lt_of_lt_of_le i.isLt (frontier_baseline_block_le n d eps)
  simp only [messageAt, hi, ↓reduceDIte]
  rfl

/-- Assume [the stated hn3 condition](hyp:hn3) and [a privacy budget in the interval from zero to one](hyp:heps). [The actual binary baseline estimate has the roadmap's finite-block MSE](goal). -/
-- @node: frontierBaselineEstimate_mse
lemma frontierBaselineEstimate_mse (n d : ℕ) (eps : ℝ)
    (hn3 : 3 ≤ n) (heps : eps ∈ Set.Ioc 0 1)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] :
    (∫ z, (frontierBaselineEstimate n d eps z - baseline P)^2
      ∂Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))) ≤
        1 / (4 * (frontierResources n d eps).m0 * (privacyDelta eps)^2) := by
  classical
  let m0 := (frontierResources n d eps).m0
  have hm0 : 0 < m0 := by dsimp [m0, frontierResources]; omega
  have hm0r : (0 : ℝ) < m0 := by exact_mod_cast hm0
  have hdelta : 0 < privacyDelta eps := by
    have h := privacyDelta_lower_quarter eps heps
    linarith [heps.1]
  let g : Fin m0 → Fin n := Fin.castLE (frontier_baseline_block_le n d eps)
  let f : (Fin n → FrontierMessage d) → ℝ := fun z => ∑ i, signVal (z (g i)).1
  let L := Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))
  let c : ℝ := (m0 : ℝ)⁻¹ / (2 * privacyDelta eps)
  letI : ∀ i, IsProbabilityMeasure ((observedLaw P).bind (frontierKernel n d eps i)) :=
    fun i => frontier_averaged_row_probability n d eps P i
  obtain ⟨hmean, hvar⟩ := frontier_baseline_sum_moments eps (by omega : n ≠ 2) P g
    (by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin n => x.val) h)
    (fun i => i.isLt)
  change (∫ z, f z ∂L) = (m0 : ℝ) * (privacyDelta eps * (2 * baseline P - 1)) at hmean
  change variance f L ≤ (m0 : ℝ) at hvar
  have hrepr : ∀ z : Fin n → FrontierMessage d,
      frontierBaselineEstimate n d eps z - baseline P = c * (f z - ∫ w, f w ∂L) := by
    intro z
    rw [frontierBaselineEstimate_eq_fin_sum n d eps z, hmean]
    dsimp [c, f, g]
    change 1/2 + (m0 : ℝ)⁻¹ * (∑ i : Fin m0, signVal (z (Fin.castLE _ i)).1) /
      (2 * privacyDelta eps) - baseline P = _
    field_simp
    <;> ring
  have hv : (∫ z, (frontierBaselineEstimate n d eps z - baseline P)^2 ∂L) =
      c^2 * variance f L := by
    simp_rw [hrepr, mul_pow]
    rw [integral_const_mul, variance_eq_integral (by fun_prop)]
  change (∫ z, (frontierBaselineEstimate n d eps z - baseline P)^2 ∂L) ≤ _
  rw [hv]
  calc
    _ ≤ c^2 * m0 := mul_le_mul_of_nonneg_left hvar (sq_nonneg c)
    _ = _ := by
      dsimp [c]
      change ((m0 : ℝ)⁻¹ / (2 * privacyDelta eps))^2 * m0 =
        1 / (4 * m0 * (privacyDelta eps)^2)
      field_simp
      <;> ring

/-- [The baseline block contains at least one third of the people](goal). -/
-- @node: frontier_baseline_block_lower
lemma frontier_baseline_block_lower (n d : ℕ) (eps : ℝ) :
    (n : ℝ) / 3 ≤ (frontierResources n d eps).m0 := by
  have h : n ≤ 3 * (n - 2 * (n / 3)) := by omega
  have hr : (n : ℝ) ≤ 3 * (n - 2 * (n / 3) : ℕ) := by exact_mod_cast h
  change (n : ℝ) / 3 ≤ (n - 2 * (n / 3) : ℕ)
  linarith

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed) and [the stated hn condition](hyp:hn). [Equation (11)'s binary counterpart: baseline MSE is at most twelve over t](goal). -/
-- @node: frontierBaselineEstimate_mse_rate
lemma frontierBaselineEstimate_mse_rate (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) (hn : n ≠ 2)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] :
    (∫ z, (frontierBaselineEstimate n d eps z - baseline P)^2
      ∂Measure.pi (fun i => (observedLaw P).bind (frontierKernel n d eps i))) ≤
        12 / ((n : ℝ) * eps^2) := by
  apply (frontierBaselineEstimate_mse n d eps (by have := hAllowed.1; omega)
    hAllowed.2.2 P).trans
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
  have heps := hAllowed.2.2.1
  have hb := frontier_baseline_block_lower n d eps
  have hd := privacyDelta_lower_quarter eps hAllowed.2.2
  have hdelta : 0 < privacyDelta eps := by linarith [hAllowed.2.2.1]
  have hm : (0 : ℝ) < (frontierResources n d eps).m0 := by linarith
  have hdsq : eps^2 / 16 ≤ (privacyDelta eps)^2 := by
    nlinarith [hAllowed.2.2.1]
  calc
    _ ≤ 1 / (4 * ((n : ℝ)/3) * (eps^2/16)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      apply mul_le_mul (mul_le_mul_of_nonneg_left hb (by norm_num)) hdsq
        (by positivity) (by positivity)
    _ = _ := by field_simp; ring

end CausalSmith.Stat.LdpOptvalueUniformFrontier

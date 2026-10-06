module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.Identification
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.FallbackBias
public import Causalean.Mathlib.Probability.IidMeanVariance

/-! # Complete-arrival and fallback risk branches

The complete-outcome score is unbiased at arrival floor one. Its iid variance
bound and projection close that endpoint independently of the main frontier.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory

/-- Unprojected complete-outcome randomized difference. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `sample`](hyp:sample), [the stated mathematical conclusion holds](goal). -/
-- @node: unprojectedHT
noncomputable def unprojectedHT {n d : ℕ} (sample : Fin n → Obs d) : ℝ :=
  2 / (n : ℝ) * ∑ i : Fin n,
    (if (sample i).A then (1 : ℝ) else -1) *
      (if (sample i).RY then (1 : ℝ) else 0)

/-- The complete-arrival one-record randomized score. Given [the specified input `d`](hyp:d), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). -/
-- @node: completeHTScore
def completeHTScore {d : ℕ} (o : Obs d) : ℝ :=
  2 * (if o.A then (1 : ℝ) else -1) * (if o.RY then (1 : ℝ) else 0)

-- @node: completeHTScore_range
/-- Given [the specified input `d`](hyp:d), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). -/
lemma completeHTScore_range {d : ℕ} (o : Obs d) :
    completeHTScore o ∈ Set.Icc (-2) 2 := by
  cases hA : o.A <;> cases hRY : o.RY <;>
    simp [completeHTScore, hA, hRY]

-- @node: completeHTScore_variance_le
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
lemma completeHTScore_variance_le {d : ℕ} (P : FullLaw d) :
    ProbabilityTheory.variance completeHTScore (observedLaw P).toMeasure ≤ 4 := by
  haveI : IsProbabilityMeasure (observedLaw P).toMeasure := inferInstance
  have hbound : ∀ᵐ o ∂(observedLaw P).toMeasure,
      completeHTScore o ∈ Set.Icc (-2) 2 :=
    Filter.Eventually.of_forall completeHTScore_range
  have hmeas : AEMeasurable (completeHTScore (d := d)) (observedLaw P).toMeasure := by
    fun_prop
  have h := ProbabilityTheory.variance_le_sq_of_bounded hbound hmeas
  norm_num at h ⊢
  exact h

-- @node: unprojectedHT_eq_average
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `sample`](hyp:sample), [the stated mathematical conclusion holds](goal). -/
lemma unprojectedHT_eq_average {n d : ℕ} (sample : Fin n → Obs d) :
    unprojectedHT sample = (n : ℝ)⁻¹ * ∑ i : Fin n, completeHTScore (sample i) := by
  simp only [unprojectedHT, completeHTScore, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

-- @node: completeHTScore_memLp
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
lemma completeHTScore_memLp {d : ℕ} (P : FullLaw d) :
    MemLp completeHTScore 2 (observedLaw P).toMeasure := by
  haveI : IsFiniteMeasure (observedLaw P).toMeasure := inferInstance
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  exact Integrable.of_finite

-- @node: completeHTScore_integral_eq_arrived
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
lemma completeHTScore_integral_eq_arrived {d : ℕ} (P : FullLaw d) :
    (∫ o, completeHTScore o ∂(observedLaw P).toMeasure) =
      2 * (massOf P (fun w => w.A = true ∧ w.R = true ∧ w.Y = true) -
        massOf P (fun w => w.A = false ∧ w.R = true ∧ w.Y = true)) := by
  classical
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  have hpoint (o : Obs d) :
      (observedLaw P o).toReal * completeHTScore o =
        2 * (if o.A = true ∧ o.RY = true then obsMass (observedLaw P) o else 0) -
        2 * (if o.A = false ∧ o.RY = true then obsMass (observedLaw P) o else 0) := by
    cases hA : o.A <;> cases hRY : o.RY <;>
      simp [completeHTScore, obsMass, hA, hRY] <;> ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [obsMass_sum_event P (fun o : Obs d => o.A = true ∧ o.RY = true),
    obsMass_sum_event P (fun o : Obs d => o.A = false ∧ o.RY = true)]
  simp only [observe, Bool.and_eq_true, Bool.true_and]
  ring

-- @node: complete_arrival_missing_cell_mass_zero
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_missing_cell_mass_zero {d : ℕ} (P : FullLaw d)
    (h : LawClass d 1 P) (x : Fin d) (a s : Bool) :
    massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = false) = 0 := by
  classical
  let t := massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = true)
  let m := massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = false)
  change m = 0
  have hpart : cellMass P x a s = t + m := by
    unfold cellMass t m massOf
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    cases hw : w.R <;> simp [hw]
  have ht : 0 ≤ t := by
    unfold t massOf
    exact Finset.sum_nonneg (fun w _ => by split_ifs <;> simp [fullMass, ENNReal.toReal_nonneg])
  have hm : 0 ≤ m := by
    unfold m massOf
    exact Finset.sum_nonneg (fun w _ => by split_ifs <;> simp [fullMass, ENNReal.toReal_nonneg])
  by_cases hc : cellMass P x a s = 0
  · linarith
  · have hcpos : 0 < cellMass P x a s := by
      have : 0 ≤ cellMass P x a s := by linarith
      exact lt_of_le_of_ne this (Ne.symm hc)
    have hf := h.floor x a s hcpos
    change 1 ≤ t / cellMass P x a s at hf
    have hle : cellMass P x a s ≤ t := by
      have := (le_div_iff₀ hcpos).mp hf
      linarith
    linarith

-- @node: complete_arrival_missing_atom_zero
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `w`](hyp:w), [the specified input `hw`](hyp:hw), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_missing_atom_zero {d : ℕ} (P : FullLaw d)
    (h : LawClass d 1 P) (w : FullAtom d) (hw : w.R = false) :
    fullMass P w = 0 := by
  classical
  have hcell := complete_arrival_missing_cell_mass_zero P h w.X w.A w.S
  unfold massOf at hcell
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (f := fun v : FullAtom d =>
      @ite ℝ (v.X = w.X ∧ v.A = w.A ∧ v.S = w.S ∧ v.R = false)
        (Classical.propDecidable _) (fullMass P v) 0)
    (by intro v _; split_ifs <;> simp [fullMass, ENNReal.toReal_nonneg])).mp hcell
  have hwzero := hz w (Finset.mem_univ w)
  simpa [hw] using hwzero

-- @node: complete_arrival_arrived_outcome_eq
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `a`](hyp:a), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_arrived_outcome_eq {d : ℕ} (P : FullLaw d)
    (h : LawClass d 1 P) (a : Bool) :
    massOf P (fun w => w.A = a ∧ w.R = true ∧ w.Y = true) =
      massOf P (fun w => w.A = a ∧ w.Y = true) := by
  classical
  unfold massOf
  apply Finset.sum_congr rfl
  intro w _
  by_cases hr : w.R = true
  · simp [hr]
  · have hf : w.R = false := by cases hR : w.R <;> simp_all
    simp [hf, complete_arrival_missing_atom_zero P h w hf]

-- @node: complete_arrival_score_mean
/-- Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_score_mean {d : ℕ} (P : FullLaw d)
    (h : LawClass d 1 P) :
    (∫ o, completeHTScore o ∂(observedLaw P).toMeasure) = tau P := by
  rw [completeHTScore_integral_eq_arrived,
    complete_arrival_arrived_outcome_eq P h true,
    complete_arrival_arrived_outcome_eq P h false,
    tau_eq_potential_mass]
  have ht := randomized_arm_outcome P h.randomized h.balanced h.consistency true
  have hf := randomized_arm_outcome P h.randomized h.balanced h.consistency false
  have ht' : 2 * massOf P (fun w => w.A = true ∧ w.Y = true) =
      massOf P (fun w => w.Y1 = true) := by simpa using ht
  have hf' : 2 * massOf P (fun w => w.A = false ∧ w.Y = true) =
      massOf P (fun w => w.Y0 = true) := by simpa using hf
  rw [← ht', ← hf']
  ring

-- @node: complete_arrival_unprojected_risk_of_mean
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `hn`](hyp:hn), [the stated mathematical conclusion holds](goal). Given [the specified input `hmean`](hyp:hmean). -/
lemma complete_arrival_unprojected_risk_of_mean {n d : ℕ} (P : FullLaw d)
    (hn : 1 ≤ n)
    (hmean : (∫ o, completeHTScore o ∂(observedLaw P).toMeasure) = tau P) :
    (∫ sample, (unprojectedHT sample - tau P) ^ 2 ∂samplePi P n) ≤
      4 / (n : ℝ) := by
  let μ := (observedLaw P).toMeasure
  let F : Obs d → ℝ := completeHTScore
  have hF : MemLp F 2 μ := completeHTScore_memLp P
  have hmeanAve := Causalean.Mathlib.Probability.iid_average_integral μ n hn F
    (hF.integrable (by norm_num))
  have hmeanSample :
      (∫ sample : Fin n → Obs d, (n : ℝ)⁻¹ * ∑ i, F (sample i)
        ∂samplePi P n) = tau P := by
    change (∫ sample : Fin n → Obs d, (n : ℝ)⁻¹ * ∑ i, F (sample i)
        ∂Measure.pi (fun _ : Fin n => μ)) = tau P
    exact hmeanAve.trans hmean
  have hvar := Causalean.Mathlib.Probability.iid_average_variance μ n F hF
  have hmeas : AEMeasurable
      (fun sample : Fin n → Obs d => (n : ℝ)⁻¹ * ∑ i, F (sample i))
      (samplePi P n) := by
    exact (measurable_of_finite _).aemeasurable
  calc
    (∫ sample, (unprojectedHT sample - tau P) ^ 2 ∂samplePi P n) =
        ProbabilityTheory.variance
          (fun sample : Fin n → Obs d => (n : ℝ)⁻¹ * ∑ i, F (sample i))
          (samplePi P n) := by
      rw [ProbabilityTheory.variance_eq_integral hmeas]
      rw [hmeanSample]
      congr 1
      funext sample
      rw [unprojectedHT_eq_average]
    _ = (n : ℝ)⁻¹ * ProbabilityTheory.variance F μ := by
      simpa [samplePi, μ, F] using hvar
    _ ≤ (n : ℝ)⁻¹ * 4 := by
      exact mul_le_mul_of_nonneg_left (completeHTScore_variance_le P) (by positivity)
    _ = 4 / (n : ℝ) := by ring

-- @node: complete_arrival_gScale
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_gScale (n d : ℕ) : gScale n d 1 = 0 := by
  simp [gScale, delta]

-- @node: complete_arrival_rate
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_rate (n d : ℕ) : rate n d 1 = 1 / (n : ℝ) := by
  simp [rate, complete_arrival_gScale]

-- @node: complete_arrival_estimator
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `sample`](hyp:sample), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_estimator (n d : ℕ) (sample : Fin n → Obs d) :
    tauhatMM n d 1 sample = completeHT sample := by
  simp [tauhatMM]

-- @node: complete_arrival_unprojected_eq
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `sample`](hyp:sample), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_unprojected_eq {n d : ℕ} (sample : Fin n → Obs d) :
    completeHT sample = clipUnit (unprojectedHT sample) := by
  rfl

-- @node: clipUnit_contracts
/-- Given [the specified input `z`](hyp:z), [the specified input `t`](hyp:t), [the stated mathematical conclusion holds](goal). Given [the specified input `ht`](hyp:ht). -/
lemma clipUnit_contracts (z t : ℝ) (ht : t ∈ Set.Icc (-1) 1) :
    |clipUnit z - t| ≤ |z - t| := by
  rcases ht with ⟨htl, htu⟩
  unfold clipUnit
  rcases le_total z (-1) with h | h
  · have hz : min 1 z = z := min_eq_right (by linarith)
    rw [hz, max_eq_left h]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rcases le_total z 1 with h' | h'
    · rw [min_eq_right h', max_eq_right h]
    · rw [min_eq_left h', max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith

-- @node: complete_arrival_projection_error
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `sample`](hyp:sample), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_projection_error {n d : ℕ} (P : FullLaw d)
    (sample : Fin n → Obs d) :
    |tauhatMM n d 1 sample - tau P| ≤
      |unprojectedHT sample - tau P| := by
  rw [complete_arrival_estimator, complete_arrival_unprojected_eq]
  exact clipUnit_contracts _ _ (tau_range P)

-- @node: complete_arrival_projection_risk
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_projection_risk {n d : ℕ} (P : FullLaw d) :
    (∫ sample, (tauhatMM n d 1 sample - tau P) ^ 2 ∂ samplePi P n) ≤
      (∫ sample, (unprojectedHT sample - tau P) ^ 2 ∂ samplePi P n) := by
  haveI : IsFiniteMeasure (samplePi P n) := by
    unfold samplePi
    infer_instance
  apply integral_mono
  · exact Integrable.of_finite
  · exact Integrable.of_finite
  · intro sample
    nlinarith [complete_arrival_projection_error P sample,
      abs_nonneg (tauhatMM n d 1 sample - tau P),
      abs_nonneg (unprojectedHT sample - tau P),
      sq_abs (tauhatMM n d 1 sample - tau P),
      sq_abs (unprojectedHT sample - tau P)]

/-- At complete arrival, the projected estimator has risk at most four over n. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_complete_arrival_risk_rate
lemma upper_complete_arrival_risk_rate {n d : ℕ} (hn : 0 < n)
    (P : FullLaw d) (h : LawClass d 1 P) :
    (∫ sample, (tauhatMM n d 1 sample - tau P) ^ 2 ∂samplePi P n) ≤
      4 * rate n d 1 := by
  have hs := complete_arrival_unprojected_risk_of_mean P hn
    (complete_arrival_score_mean P h)
  have hp := complete_arrival_projection_risk (n := n) P
  simpa only [complete_arrival_rate, mul_one_div] using hp.trans hs

/-- All complete-arrival and fallback regimes share a universal risk constant. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `hb`](hyp:hb). -/
-- @node: upper_fallback_branches_risk_rate
lemma upper_fallback_branches_risk_rate {n d : ℕ} {q : ℝ} (hn : 0 < n)
    (P : FullLaw d) (h : LawClass d q P) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hb : q = 1 ∨ ell n < 128 ∨ (n : ℝ) * ell n ≤ d) :
    (∫ sample, (tauhatMM n d q sample - tau P) ^ 2 ∂samplePi P n) ≤
      (4 * Real.exp 128) * rate n d q := by
  have hr : 0 ≤ rate n d q := by
    unfold rate
    positivity
  have he : (1 : ℝ) ≤ Real.exp 128 := Real.one_le_exp (by norm_num)
  rcases hb with hcomplete | hsmall | hdim
  · subst q
    exact (upper_complete_arrival_risk_rate hn P h).trans
      (mul_le_mul_of_nonneg_right (by nlinarith : (4 : ℝ) ≤ 4 * Real.exp 128) hr)
  · exact upper_small_log_risk_rate hn q P hsmall
  · by_cases hcomplete : q = 1
    · subst q
      exact (upper_complete_arrival_risk_rate hn P h).trans
        (mul_le_mul_of_nonneg_right (by nlinarith : (4 : ℝ) ≤ 4 * Real.exp 128) hr)
    · exact (upper_large_dimension_risk_rate hn P h hq hcomplete hdim).trans
        (mul_le_mul_of_nonneg_right (by nlinarith : (2 : ℝ) ≤ 4 * Real.exp 128) hr)

end CausalSmith.Stat.MarNearcompleteFrontier

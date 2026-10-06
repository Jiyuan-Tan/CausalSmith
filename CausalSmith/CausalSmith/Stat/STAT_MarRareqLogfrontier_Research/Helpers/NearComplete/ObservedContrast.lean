module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Identification
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.NearComplete.CompleteArrivalTwoPoint
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import Causalean.Tactic.IntegralLinearity

/-! Armwise missing-outcome deficits and the clipped observed-contrast risk envelope. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
namespace CausalSmith.Stat.MarRareqLogfrontier

/-- For [the specified inputs and assumptions](hyp:d,P,a), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def armDeficit {d : ℕ} (P : FullLaw d) (a : Bool) : ℝ :=
  2 * ∫ r, (if r.A = a ∧ r.R = false ∧ r.Y = true then (1 : ℝ) else 0) ∂P.1

/-- Given [the specified inputs and assumptions](hyp:d,P,a,E), [the stated mathematical conclusion holds](goal). -/
-- @node: sum_armCell_event_mass
lemma sum_armCell_event_mass {d : ℕ} (P : FullLaw d) (a : Bool)
    (E : Set (FullRecord d)) :
    (∑ j : Fin d × Bool, P.1.real {r | inCell r (a, j.1, j.2) ∧ r ∈ E}) =
      P.1.real {r | r.A = a ∧ r ∈ E} := by
  classical
  let : IsProbabilityMeasure P.1 := P.2
  let μ := P.1.restrict {r | r.A = a ∧ r ∈ E}
  have hsum := sum_measureReal_preimage_singleton (μ := μ)
    (Finset.univ : Finset (Fin d × Bool))
    (f := fun r : FullRecord d => (r.X, r.S)) (by intro; simp)
  calc
    (∑ j : Fin d × Bool, P.1.real {r | inCell r (a, j.1, j.2) ∧ r ∈ E}) =
        ∑ j : Fin d × Bool, μ.real ((fun r : FullRecord d => (r.X, r.S)) ⁻¹' {j}) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hs : {r : FullRecord d | inCell r (a, j.1, j.2) ∧ r ∈ E} =
          ((fun r : FullRecord d => (r.X, r.S)) ⁻¹' {j}) ∩
            {r | r.A = a ∧ r ∈ E} := by
        rcases j with ⟨x, s⟩
        ext r
        simp [inCell, Prod.mk.injEq, and_assoc, and_left_comm, and_comm]
      rw [hs]
      simp [μ, measureReal_def, Measure.restrict_apply]
    _ = μ.real ((fun r : FullRecord d => (r.X, r.S)) ⁻¹'
        (Finset.univ : Finset (Fin d × Bool))) := hsum
    _ = P.1.real {r | r.A = a ∧ r ∈ E} := by
      simp [μ, measureReal_def, Measure.restrict_apply]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,j), [the stated mathematical conclusion holds](goal). -/
-- @node: absent_cell_mass_le
lemma absent_cell_mass_le {n d : ℕ} {q : ℝ} (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (j : Cell d) :
    P.1.real {r | inCell r j ∧ r.R = false} ≤ (1 - q) * cellProb P j := by
  let : IsProbabilityMeasure P.1 := P.2
  have harr : q * cellProb P j ≤ arrivedCell P j := by
    by_cases hp : 0 < cellProb P j
    · exact hP.arrival j hp
    · have hz : cellProb P j = 0 :=
        le_antisymm (le_of_not_gt hp) measureReal_nonneg
      rw [hz, mul_zero]
      exact measureReal_nonneg
  have hdiff : {r : FullRecord d | inCell r j ∧ r.R = false} =
      {r | inCell r j} \ {r | inCell r j ∧ r.R = true} := by
    ext r
    cases r.R <;> simp <;> tauto
  rw [hdiff, measureReal_sdiff (by intro r hr; exact hr.1) (by simp)]
  change cellProb P j - arrivedCell P j ≤ _
  linarith

/-- Given [the specified inputs and assumptions](hyp:d,P,hB,a), [the stated mathematical conclusion holds](goal). -/
-- @node: balanced_arm_mass
lemma balanced_arm_mass {d : ℕ} (P : FullLaw d)
    (hB : BalancedRandomization P) (a : Bool) :
    P.1.real {r | r.A = a} = 1 / 2 := by
  let : IsProbabilityMeasure P.1 := P.2
  cases a with
  | true => exact hB
  | false =>
      have hc : {r : FullRecord d | r.A = false} = {r | r.A = true}ᶜ := by
        ext r
        cases r.A <;> simp
      rw [hc, measureReal_compl (by simp), hB]
      norm_num

/-- Given [the specified inputs and assumptions](hyp:d,P,a), [the stated mathematical conclusion holds](goal). -/
-- @node: armDeficit_eq_missingOutcomeMass
lemma armDeficit_eq_missingOutcomeMass {d : ℕ} (P : FullLaw d) (a : Bool) :
    armDeficit P a = 2 * P.1.real {r | r.A = a ∧ r.R = false ∧ r.Y = true} := by
  classical
  let : IsProbabilityMeasure P.1 := P.2
  unfold armDeficit
  have hi : (fun r : FullRecord d =>
      if r.A = a ∧ r.R = false ∧ r.Y = true then (1 : ℝ) else 0) =
      {r : FullRecord d | r.A = a ∧ r.R = false ∧ r.Y = true}.indicator 1 := by
    funext r
    simp [Set.indicator]
  rw [hi, integral_indicator_one (by simp)]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,a), [the stated mathematical conclusion holds](goal). -/
-- @node: armDeficit_bounds
lemma armDeficit_bounds {n d : ℕ} {q : ℝ} (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (a : Bool) :
    0 ≤ armDeficit P a ∧ armDeficit P a ≤ 1 - q := by
  classical
  let : IsProbabilityMeasure P.1 := P.2
  rw [armDeficit_eq_missingOutcomeMass]
  constructor
  · positivity
  · have hsum : (∑ j : Fin d × Bool, cellProb P (a, j.1, j.2)) = 1 / 2 := by
      have h := sum_armCell_event_mass P a Set.univ
      simp only [Set.mem_univ, and_true] at h
      exact h.trans (balanced_arm_mass P hP.balanced a)
    have habsent : P.1.real {r | r.A = a ∧ r.R = false} ≤ (1 - q) / 2 := by
      calc
        P.1.real {r | r.A = a ∧ r.R = false} =
            ∑ j : Fin d × Bool, P.1.real {r | inCell r (a, j.1, j.2) ∧ r.R = false} :=
          (sum_armCell_event_mass P a {r | r.R = false}).symm
        _ ≤ ∑ j : Fin d × Bool, (1 - q) * cellProb P (a, j.1, j.2) :=
          Finset.sum_le_sum (fun j _ => absent_cell_mass_le P hP _)
        _ = (1 - q) / 2 := by rw [← Finset.mul_sum, hsum]; ring
    have hout : P.1.real {r | r.A = a ∧ r.R = false ∧ r.Y = true} ≤
        P.1.real {r | r.A = a ∧ r.R = false} :=
      measureReal_mono (by intro r hr; exact ⟨hr.1, hr.2.1⟩)
    linarith

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP), [the stated mathematical conclusion holds](goal). -/
-- @node: observed_contrast_score_mean
lemma observed_contrast_score_mean {n d : ℕ} {q : ℝ} (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) :
    (∫ o : ObsRecord d,
      2 * armSign o.A * (if o.R && o.RY then (1 : ℝ) else 0) ∂(P.1.map obs)) =
      ate P - armDeficit P true + armDeficit P false := by
  classical
  let : IsProbabilityMeasure P.1 := P.2
  rw [integral_map (by fun_prop) (by fun_prop)]
  let E (a : Bool) : Set (FullRecord d) := {r | r.A = a ∧ r.Y = true}
  let M (a : Bool) : Set (FullRecord d) :=
    {r | r.A = a ∧ r.R = false ∧ r.Y = true}
  have hp : (fun r : FullRecord d =>
      2 * armSign (obs r).A * (if (obs r).R && (obs r).RY then (1 : ℝ) else 0)) =
      (fun r => (E true).indicator (fun _ => (2 : ℝ)) r -
        (E false).indicator (fun _ => (2 : ℝ)) r -
        (M true).indicator (fun _ => (2 : ℝ)) r +
        (M false).indicator (fun _ => (2 : ℝ)) r) := by
    funext r
    cases hA : r.A <;> cases hR : r.R <;> cases hY : r.Y <;>
      simp [obs, armSign, E, M, Set.indicator, hA, hR, hY]
  rw [hp]
  have hi (a : Bool) : Integrable ((E a).indicator (fun _ => (2 : ℝ))) P.1 := by
    exact (integrable_const (2 : ℝ)).indicator (by simp [E])
  have hm (a : Bool) : Integrable ((M a).indicator (fun _ => (2 : ℝ))) P.1 := by
    exact (integrable_const (2 : ℝ)).indicator (by simp [M])
  have hit := hi true
  have hif := hi false
  have hmt := hm true
  have hmf := hm false
  integral_linearity
  rw [integral_indicator_const (s := E true) (2 : ℝ) (by simp [E]),
    integral_indicator_const (s := E false) (2 : ℝ) (by simp [E]),
    integral_indicator_const (s := M true) (2 : ℝ) (by simp [M]),
    integral_indicator_const (s := M false) (2 : ℝ) (by simp [M])]
  simp only [smul_eq_mul]
  rw [armDeficit_eq_missingOutcomeMass, armDeficit_eq_missingOutcomeMass,
    ate_eq_potentialOutcomeMass]
  have ht := randomized_armOutcomeMass P hP.randomized hP.balanced true
  have hf := randomized_armOutcomeMass P hP.randomized hP.balanced false
  simp only [ite_true, Bool.false_eq_true, ite_false] at ht hf
  dsimp only [E, M]
  linear_combination ht - hf

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP), [the stated mathematical conclusion holds](goal). -/
-- @node: observed_contrast_score_bias_le
lemma observed_contrast_score_bias_le {n d : ℕ} {q : ℝ} (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) :
    ((∫ o : ObsRecord d,
      2 * armSign o.A * (if o.R && o.RY then (1 : ℝ) else 0) ∂(P.1.map obs)) -
        ate P) ^ 2 ≤ (1 - q) ^ 2 := by
  rw [observed_contrast_score_mean P hP]
  have ht := armDeficit_bounds P hP true
  have hf := armDeficit_bounds P hP false
  have habs : |ate P - armDeficit P true + armDeficit P false - ate P| ≤ 1 - q := by
    rw [abs_le]
    constructor <;> linarith
  have hsq := (sq_le_sq₀ (abs_nonneg _) (sub_nonneg.mpr hP.q_le_one)).mpr habs
  simpa only [sq_abs] using hsq

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP), [the stated mathematical conclusion holds](goal). -/
-- @node: observed_contrast_risk_le
lemma observed_contrast_risk_le {n d : ℕ} {q : ℝ} (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) :
    deterministicRisk (completeArrivalHTEstimator n d) P ≤
      4 / (n : ℝ) + (1 - q) ^ 2 := by
  classical
  let : IsProbabilityMeasure P.1 := P.2
  let μ := P.1.map obs
  let : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure (sampleLaw n P) := by
    unfold sampleLaw
    infer_instance
  let ξ : ObsRecord d → ℝ := fun o =>
    2 * armSign o.A * (if o.R && o.RY then (1 : ℝ) else 0)
  let V : (Fin n → ObsRecord d) → ℝ := fun s => (n : ℝ)⁻¹ * ∑ i, ξ (s i)
  have hξ : MemLp ξ 2 μ := ⟨by fun_prop, eLpNorm_lt_top_of_finite⟩
  have hV : MemLp V 2 (sampleLaw n P) := ⟨by fun_prop, eLpNorm_lt_top_of_finite⟩
  have hmean : (∫ s, V s ∂sampleLaw n P) = ∫ o, ξ o ∂μ :=
    Causalean.Mathlib.Probability.iid_average_integral μ n hP.n_pos ξ
      (hξ.integrable (by norm_num))
  have hvar : variance V (sampleLaw n P) = (n : ℝ)⁻¹ * variance ξ μ :=
    Causalean.Mathlib.Probability.iid_average_variance μ n ξ hξ
  have hbound : ∀ᵐ o ∂μ, ξ o ∈ Set.Icc (-2) 2 := by
    filter_upwards [] with o
    dsimp only [ξ]
    cases o.A <;> cases o.R <;> cases o.RY <;> norm_num [armSign]
  have hvarle : variance ξ μ ≤ 4 := by
    have h := variance_le_sq_of_bounded hbound hξ.aemeasurable
    norm_num at h
    exact h
  have hdecomp : (∫ s, (V s - ate P) ^ 2 ∂sampleLaw n P) =
      (n : ℝ)⁻¹ * variance ξ μ + ((∫ o, ξ o ∂μ) - ate P) ^ 2 := by
    have h := variance_eq_sub (hV.sub (memLp_const (ate P)))
    change variance (fun s => V s - ate P) (sampleLaw n P) =
      (∫ s, (V s - ate P) ^ 2 ∂sampleLaw n P) -
        (∫ s, V s - ate P ∂sampleLaw n P) ^ 2 at h
    rw [variance_sub_const hV.aestronglyMeasurable, hvar,
      integral_sub (hV.integrable (by norm_num)) (integrable_const _),
      integral_const, probReal_univ, one_smul, hmean] at h
    linarith
  have hclip : ∀ s, (completeArrivalHTEstimator n d s - ate P) ^ 2 ≤
      (V s - ate P) ^ 2 := by
    intro s
    have he : completeArrivalHTEstimator n d s = clip (V s) := by
      unfold completeArrivalHTEstimator V ξ
      congr 1
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [div_eq_mul_inv]
      ring
    rw [he]
    exact clip_sq_error_le _ _ (ate_mem_unit_interval P)
  calc
    deterministicRisk (completeArrivalHTEstimator n d) P ≤
        ∫ s, (V s - ate P) ^ 2 ∂sampleLaw n P :=
      integral_mono Integrable.of_finite Integrable.of_finite hclip
    _ = (n : ℝ)⁻¹ * variance ξ μ + ((∫ o, ξ o ∂μ) - ate P) ^ 2 := hdecomp
    _ ≤ 4 / (n : ℝ) + (1 - q) ^ 2 := by
      have hb := observed_contrast_score_bias_le P hP
      change ((∫ o, ξ o ∂μ) - ate P) ^ 2 ≤ (1 - q) ^ 2 at hb
      have hv := mul_le_mul_of_nonneg_left hvarle (inv_nonneg.mpr (Nat.cast_nonneg n))
      simpa only [div_eq_mul_inv, mul_comm] using add_le_add hv hb

end CausalSmith.Stat.MarRareqLogfrontier

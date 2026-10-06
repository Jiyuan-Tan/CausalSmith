module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Defs.Model
public import Causalean.Mathlib.MeasureTheory.IntegralBind
public import Causalean.Stat.Concentration.Poisson.FactorialPolynomial
public import Mathlib.Probability.Independence.Integration

/-! Factorial moments for finite product Poisson mixtures. -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

open Causalean.Stat.Concentration.Poisson

private lemma poissonCountLaw_eval_map {p : ℕ} (s z : Fin p → ℝ) (j : Fin p) :
    Measure.map (fun x : Fin p → ℕ => x j) (poissonCountLaw s z) =
      poissonMeasure (Real.toNNReal (s j * Real.exp (z j))) := by
  rw [poissonCountLaw, Measure.pi_map_eval]
  simp

private lemma poissonCountLaw_eval_integrable {p : ℕ} (s z : Fin p → ℝ) (j : Fin p) :
    Integrable (fun x : Fin p → ℕ => (x j : ℝ)) (poissonCountLaw s z) := by
  let rate := Real.toNNReal (s j * Real.exp (z j))
  have hp : MeasurePreserving (fun x : Fin p → ℕ => x j) (poissonCountLaw s z)
      (poissonMeasure rate) := ⟨measurable_pi_apply j, by
        simpa [rate] using poissonCountLaw_eval_map s z j⟩
  change Integrable ((fun N : ℕ => (N : ℝ)) ∘ fun x : Fin p → ℕ => x j)
    (poissonCountLaw s z)
  exact (hp.integrable_comp (by measurability)).2 <| by
    simpa using poisson_descFactorial_integrable rate 1

private lemma poissonCountLaw_eval_integral {p : ℕ} (s z : Fin p → ℝ) (j : Fin p) :
    (∫ x : Fin p → ℕ, (x j : ℝ) ∂poissonCountLaw s z) =
      (Real.toNNReal (s j * Real.exp (z j)) : ℝ) := by
  let rate := Real.toNNReal (s j * Real.exp (z j))
  calc
    _ = ∫ N : ℕ, (N : ℝ) ∂Measure.map (fun x : Fin p → ℕ => x j)
          (poissonCountLaw s z) := by
      rw [integral_map (measurable_pi_apply j).aemeasurable (by measurability)]
    _ = ∫ N : ℕ, (N : ℝ) ∂poissonMeasure rate := by
      rw [poissonCountLaw_eval_map]
    _ = _ := by simpa [rate] using poisson_descFactorial_moment rate 1

private lemma poissonCountLaw_second_integrable {p : ℕ} (s z : Fin p → ℝ) (j : Fin p) :
    Integrable (fun x : Fin p → ℕ => (x j : ℝ) * ((x j : ℝ) - 1))
      (poissonCountLaw s z) := by
  let rate := Real.toNNReal (s j * Real.exp (z j))
  have hp : MeasurePreserving (fun x : Fin p → ℕ => x j) (poissonCountLaw s z)
      (poissonMeasure rate) := ⟨measurable_pi_apply j, by
        simpa [rate] using poissonCountLaw_eval_map s z j⟩
  have hi := (hp.integrable_comp (by measurability)).2
    (poisson_descFactorial_integrable rate 2)
  convert hi using 1
  funext x
  simp only [Function.comp_apply]
  by_cases hx : x j = 0
  · simp [hx]
  · rw [show (x j).descFactorial 2 = (x j - 1) * x j by
      simp [Nat.descFactorial]]
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hx)]
    ring

private lemma poissonCountLaw_second_integral {p : ℕ} (s z : Fin p → ℝ) (j : Fin p) :
    (∫ x : Fin p → ℕ, (x j : ℝ) * ((x j : ℝ) - 1) ∂poissonCountLaw s z) =
      (Real.toNNReal (s j * Real.exp (z j)) : ℝ) ^ 2 := by
  let rate := Real.toNNReal (s j * Real.exp (z j))
  calc
    _ = ∫ x : Fin p → ℕ, ((x j).descFactorial 2 : ℝ) ∂poissonCountLaw s z := by
      congr 1
      funext x
      by_cases hx : x j = 0
      · simp [hx]
      · rw [show (x j).descFactorial 2 = (x j - 1) * x j by
          simp [Nat.descFactorial]]
        push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hx)]
        ring
    _ = ∫ N : ℕ, (N.descFactorial 2 : ℝ) ∂Measure.map
          (fun x : Fin p → ℕ => x j) (poissonCountLaw s z) := by
      rw [integral_map (measurable_pi_apply j).aemeasurable (by measurability)]
    _ = _ := by
      rw [poissonCountLaw_eval_map, poisson_descFactorial_moment]

private lemma poisson_descFactorial_mixed_integrable (rate : NNReal) (h t : ℕ) :
    Integrable (fun N : ℕ => (N.descFactorial h : ℝ) * (N.descFactorial t : ℝ))
      (poissonMeasure rate) := by
  have hi := integrable_finsetSum (Finset.range (min h t + 1))
    (fun r _ => (poisson_descFactorial_integrable rate (h + t - r)).const_mul
      ((h.choose r : ℝ) * (t.choose r : ℝ) * (Nat.factorial r : ℝ)))
  rw [show (fun N : ℕ => (N.descFactorial h : ℝ) * (N.descFactorial t : ℝ)) =
      (fun N : ℕ => ∑ r ∈ Finset.range (min h t + 1),
        (h.choose r : ℝ) * (t.choose r : ℝ) * (Nat.factorial r : ℝ) *
          (N.descFactorial (h + t - r) : ℝ)) by
    funext N
    exact descFactorial_mul N h t]
  exact hi

private lemma poissonCountLaw_eval_sq_integrable {p : ℕ} (s z : Fin p → ℝ) (j : Fin p) :
    Integrable (fun x : Fin p → ℕ => (x j : ℝ) ^ 2) (poissonCountLaw s z) := by
  let rate := Real.toNNReal (s j * Real.exp (z j))
  have hp : MeasurePreserving (fun x : Fin p → ℕ => x j) (poissonCountLaw s z)
      (poissonMeasure rate) := ⟨measurable_pi_apply j, by
        simpa [rate] using poissonCountLaw_eval_map s z j⟩
  have hi := (hp.integrable_comp (by measurability)).2
    (poisson_descFactorial_mixed_integrable rate 1 1)
  convert hi using 1
  funext x
  simp only [Function.comp_apply]
  norm_num [Nat.descFactorial]
  ring

private lemma poissonCountLaw_eval_sq_integral {p : ℕ} (s z : Fin p → ℝ) (j : Fin p) :
    (∫ x : Fin p → ℕ, (x j : ℝ) ^ 2 ∂poissonCountLaw s z) =
      (Real.toNNReal (s j * Real.exp (z j)) : ℝ) ^ 2 +
        (Real.toNNReal (s j * Real.exp (z j)) : ℝ) := by
  let rate := Real.toNNReal (s j * Real.exp (z j))
  calc
    _ = ∫ N : ℕ, (N.descFactorial 1 : ℝ) * (N.descFactorial 1 : ℝ)
          ∂Measure.map (fun x : Fin p → ℕ => x j) (poissonCountLaw s z) := by
      rw [integral_map (measurable_pi_apply j).aemeasurable (by measurability)]
      congr 1
      funext x
      norm_num [Nat.descFactorial]
      ring
    _ = ∫ N : ℕ, (N.descFactorial 1 : ℝ) * (N.descFactorial 1 : ℝ)
          ∂poissonMeasure rate := by rw [poissonCountLaw_eval_map]
    _ = _ := by
      rw [poisson_descFactorial_mixed]
      simp [Finset.sum_range_succ, rate]

private lemma poissonCountLaw_second_sq_integrable {p : ℕ}
    (s z : Fin p → ℝ) (j : Fin p) :
    Integrable (fun x : Fin p → ℕ =>
      ((x j : ℝ) * ((x j : ℝ) - 1)) ^ 2) (poissonCountLaw s z) := by
  let rate := Real.toNNReal (s j * Real.exp (z j))
  have hp : MeasurePreserving (fun x : Fin p → ℕ => x j) (poissonCountLaw s z)
      (poissonMeasure rate) := ⟨measurable_pi_apply j, by
        simpa [rate] using poissonCountLaw_eval_map s z j⟩
  have hi := (hp.integrable_comp (by measurability)).2
    (poisson_descFactorial_mixed_integrable rate 2 2)
  convert hi using 1
  funext x
  simp only [Function.comp_apply]
  by_cases hx : x j = 0
  · simp [hx]
  · rw [show (x j).descFactorial 2 = (x j - 1) * x j by
      simp [Nat.descFactorial]]
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hx)]
    ring

private lemma poissonCountLaw_second_sq_integral {p : ℕ}
    (s z : Fin p → ℝ) (j : Fin p) :
    (∫ x : Fin p → ℕ, ((x j : ℝ) * ((x j : ℝ) - 1)) ^ 2
      ∂poissonCountLaw s z) =
      (Real.toNNReal (s j * Real.exp (z j)) : ℝ) ^ 4 +
        4 * (Real.toNNReal (s j * Real.exp (z j)) : ℝ) ^ 3 +
        2 * (Real.toNNReal (s j * Real.exp (z j)) : ℝ) ^ 2 := by
  let rate := Real.toNNReal (s j * Real.exp (z j))
  change (∫ x : Fin p → ℕ, ((x j : ℝ) * ((x j : ℝ) - 1)) ^ 2
      ∂poissonCountLaw s z) =
    (rate : ℝ) ^ 4 + 4 * (rate : ℝ) ^ 3 + 2 * (rate : ℝ) ^ 2
  calc
    _ = ∫ N : ℕ, (N.descFactorial 2 : ℝ) * (N.descFactorial 2 : ℝ)
          ∂Measure.map (fun x : Fin p → ℕ => x j) (poissonCountLaw s z) := by
      rw [integral_map (measurable_pi_apply j).aemeasurable (by measurability)]
      congr 1
      funext x
      by_cases hx : x j = 0
      · simp [hx]
      · rw [show (x j).descFactorial 2 = (x j - 1) * x j by
          simp [Nat.descFactorial]]
        push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hx)]
        ring
    _ = ∫ N : ℕ, (N.descFactorial 2 : ℝ) * (N.descFactorial 2 : ℝ)
          ∂poissonMeasure rate := by rw [poissonCountLaw_eval_map]
    _ = _ := by
      rw [poisson_descFactorial_mixed]
      norm_num [Finset.sum_range_succ]

private lemma poissonCountLaw_cross_integrable {p : ℕ} (s z : Fin p → ℝ)
    (j k : Fin p) (hjk : j ≠ k) :
    Integrable (fun x : Fin p → ℕ => (x j : ℝ) * (x k : ℝ))
      (poissonCountLaw s z) := by
  have hi : iIndepFun (fun i (x : Fin p → ℕ) => x i) (poissonCountLaw s z) := by
    simpa only [poissonCountLaw, id_eq] using
      (iIndepFun_pi
        (μ := fun i : Fin p => poissonMeasure (Real.toNNReal (s i * Real.exp (z i))))
        (X := fun _ => id) (fun _ => aemeasurable_id))
  have hjk' : (fun x : Fin p → ℕ => (x j : ℝ)) ⟂ᵢ[poissonCountLaw s z]
      (fun x => (x k : ℝ)) := by
    simpa only [Function.comp_def] using
      (hi.indepFun hjk).comp (measurable_of_countable _) (measurable_of_countable _)
  exact hjk'.integrable_mul (poissonCountLaw_eval_integrable s z j)
    (poissonCountLaw_eval_integrable s z k)

private lemma poissonCountLaw_cross_integral {p : ℕ} (s z : Fin p → ℝ)
    (j k : Fin p) (hjk : j ≠ k) :
    (∫ x : Fin p → ℕ, (x j : ℝ) * (x k : ℝ) ∂poissonCountLaw s z) =
      (Real.toNNReal (s j * Real.exp (z j)) : ℝ) *
        (Real.toNNReal (s k * Real.exp (z k)) : ℝ) := by
  have hi : iIndepFun (fun i (x : Fin p → ℕ) => x i) (poissonCountLaw s z) := by
    simpa only [poissonCountLaw, id_eq] using
      (iIndepFun_pi
        (μ := fun i : Fin p => poissonMeasure (Real.toNNReal (s i * Real.exp (z i))))
        (X := fun _ => id) (fun _ => aemeasurable_id))
  have hjk' : (fun x : Fin p → ℕ => (x j : ℝ)) ⟂ᵢ[poissonCountLaw s z]
      (fun x => (x k : ℝ)) := by
    simpa only [Function.comp_def] using
      (hi.indepFun hjk).comp (measurable_of_countable _) (measurable_of_countable _)
  rw [hjk'.integral_fun_mul_eq_mul_integral
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aestronglyMeasurable,
    poissonCountLaw_eval_integral, poissonCountLaw_eval_integral]

private lemma firstFactorial_poisson_integrable {p : ℕ} (s z : Fin p → ℝ) (j : Fin p)
    (_hs : s j ≠ 0) :
    Integrable (fun x => firstFactorial x s j) (poissonCountLaw s z) := by
  simpa only [firstFactorial, div_eq_mul_inv] using
    (poissonCountLaw_eval_integrable s z j).mul_const (s j)⁻¹

private lemma firstFactorial_poisson_integral {p : ℕ} (s z : Fin p → ℝ) (j : Fin p)
    (hs : 0 < s j) :
    (∫ x, firstFactorial x s j ∂poissonCountLaw s z) = Real.exp (z j) := by
  simp only [firstFactorial]
  rw [integral_div, poissonCountLaw_eval_integral]
  rw [Real.coe_toNNReal _ (mul_nonneg hs.le (Real.exp_pos _).le)]
  field_simp

private lemma crossFactorial_poisson_integrable {p : ℕ} (s z : Fin p → ℝ)
    (j k : Fin p) (_hsj : s j ≠ 0) (hsk : s k ≠ 0) :
    Integrable (fun x => crossFactorial x s j k) (poissonCountLaw s z) := by
  by_cases hjk : j = k
  · subst k
    simp only [crossFactorial, if_pos]
    simpa only [secondFactorial, div_eq_mul_inv] using
      (poissonCountLaw_second_integrable s z j).mul_const ((s j) ^ 2)⁻¹
  · simp only [crossFactorial, if_neg hjk, div_eq_mul_inv]
    exact (poissonCountLaw_cross_integrable s z j k hjk).mul_const (s j * s k)⁻¹

private lemma crossFactorial_poisson_integral {p : ℕ} (s z : Fin p → ℝ)
    (j k : Fin p) (hsj : 0 < s j) (hsk : 0 < s k) :
    (∫ x, crossFactorial x s j k ∂poissonCountLaw s z) =
      Real.exp (z j + z k) := by
  by_cases hjk : j = k
  · subst k
    simp only [crossFactorial, if_pos, secondFactorial]
    rw [integral_div, poissonCountLaw_second_integral,
      Real.coe_toNNReal _ (mul_nonneg hsj.le (Real.exp_pos _).le)]
    field_simp
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  · simp only [crossFactorial, if_neg hjk]
    rw [integral_div, poissonCountLaw_cross_integral _ _ _ _ hjk,
      Real.coe_toNNReal _ (mul_nonneg hsj.le (Real.exp_pos _).le),
      Real.coe_toNNReal _ (mul_nonneg hsk.le (Real.exp_pos _).le)]
    field_simp
    rw [← Real.exp_add]

private lemma firstFactorial_sq_poisson_integrable {p : ℕ}
    (s z : Fin p → ℝ) (j : Fin p) (_hs : s j ≠ 0) :
    Integrable (fun x => (firstFactorial x s j) ^ 2) (poissonCountLaw s z) := by
  convert (poissonCountLaw_eval_sq_integrable s z j).mul_const ((s j) ^ 2)⁻¹ using 1
  funext x
  simp only [firstFactorial, div_eq_mul_inv]
  ring

private lemma firstFactorial_sq_poisson_integral {p : ℕ}
    (s z : Fin p → ℝ) (j : Fin p) (hs : 0 < s j) :
    (∫ x, (firstFactorial x s j) ^ 2 ∂poissonCountLaw s z) =
      Real.exp (2 * z j) + Real.exp (z j) / s j := by
  simp only [firstFactorial, div_pow]
  rw [integral_div, poissonCountLaw_eval_sq_integral,
    Real.coe_toNNReal _ (mul_nonneg hs.le (Real.exp_pos _).le)]
  have he : Real.exp (2 * z j) = Real.exp (z j) ^ 2 := by
    rw [show 2 * z j = z j + z j by ring, Real.exp_add, pow_two]
  rw [he]
  field_simp

private lemma secondFactorial_sq_poisson_integrable {p : ℕ}
    (s z : Fin p → ℝ) (j : Fin p) (_hs : s j ≠ 0) :
    Integrable (fun x => (secondFactorial x s j) ^ 2) (poissonCountLaw s z) := by
  convert (poissonCountLaw_second_sq_integrable s z j).mul_const (((s j) ^ 2) ^ 2)⁻¹ using 1
  funext x
  simp only [secondFactorial, div_eq_mul_inv]
  ring

private lemma secondFactorial_sq_poisson_integral {p : ℕ}
    (s z : Fin p → ℝ) (j : Fin p) (hs : 0 < s j) :
    (∫ x, (secondFactorial x s j) ^ 2 ∂poissonCountLaw s z) =
      Real.exp (4 * z j) + 4 * Real.exp (3 * z j) / s j +
        2 * Real.exp (2 * z j) / (s j) ^ 2 := by
  simp only [secondFactorial, div_pow]
  rw [integral_div, poissonCountLaw_second_sq_integral,
    Real.coe_toNNReal _ (mul_nonneg hs.le (Real.exp_pos _).le)]
  have he2 : Real.exp (2 * z j) = Real.exp (z j) ^ 2 := by
    rw [show 2 * z j = z j + z j by ring, Real.exp_add, pow_two]
  have he3 : Real.exp (3 * z j) = Real.exp (z j) ^ 3 := by
    rw [show 3 * z j = z j + z j + z j by ring, Real.exp_add, Real.exp_add]
    ring
  have he4 : Real.exp (4 * z j) = Real.exp (z j) ^ 4 := by
    rw [show 4 * z j = z j + z j + z j + z j by ring,
      Real.exp_add, Real.exp_add, Real.exp_add]
    ring
  rw [he2, he3, he4]
  field_simp

set_option maxHeartbeats 2400000 in
-- The bind-law normalization elaborates a large dependent product-measure expression.
/-- Conditional coordinatewise Poisson factorial moments pass through the exact joint
mixture law. The adjusted first factorial expectation is the latent exponential moment,
and the adjusted cross factorial expectation is the exponential moment of the coordinate
sum; on the diagonal the cross statistic uses the second falling factorial. -/
-- @node: gate:poisson-mixture-factorial-moment-transfer
lemma poisson_mixture_factorial_moment_transfer {p : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S Z : Ω → Fin p → ℝ) (X : Ω → Fin p → ℕ)
    (hP : PoissonMeasurement μ (fun _ : Unit => fun _ : Unit => Z)
      (fun _ _ => S) (fun _ _ => X))
    (j k : Fin p)
    (hj : Integrable (fun ω => Real.exp (Z ω j)) μ)
    (hjk : Integrable (fun ω => Real.exp (Z ω j + Z ω k)) μ) :
    (∫ ω, firstFactorial (X ω) (S ω) j ∂μ) =
        ∫ ω, Real.exp (Z ω j) ∂μ ∧
      (∫ ω, crossFactorial (X ω) (S ω) j k ∂μ) =
        ∫ ω, Real.exp (Z ω j + Z ω k) ∂μ := by
  have hp := hP () ()
  have hpos : ∀ᵐ ω ∂μ, ∀ i, 0 < S ω i := by simpa only using hp.1
  have hcond : AEMeasurable (fun ω => (S ω, Z ω)) μ := by simpa only using hp.2.1
  have hfull : AEMeasurable (fun ω => ((S ω, Z ω), X ω)) μ := by
    simpa only using hp.2.2.1
  have hjoint : μ.map (fun ω => ((S ω, Z ω), X ω)) =
      Measure.bind (μ.map (fun ω => (S ω, Z ω)))
        (fun sz => (poissonCountLaw sz.1 sz.2).map (fun x => (sz, x))) := by
    simpa only using hp.2.2.2
  let base := μ.map (fun ω => (S ω, Z ω))
  let κ := fun sz : (Fin p → ℝ) × (Fin p → ℝ) =>
    (poissonCountLaw sz.1 sz.2).map (fun x => (sz, x))
  have hμne : μ ≠ 0 := by
    intro hzero
    have hu := isProbabilityMeasure_iff.mp (inferInstance : IsProbabilityMeasure μ)
    rw [hzero] at hu
    simp at hu
  have hκ : AEMeasurable κ base := by
    apply AEMeasurable.of_map_ne_zero
    intro hzero
    have hb : base.bind κ = 0 := by simp [Measure.bind, hzero]
    have hjoint_ne := (Measure.map_ne_zero_iff hfull).2 hμne
    apply hjoint_ne
    rw [hjoint]
    exact hb
  have hposBase : ∀ᵐ sz ∂base, ∀ i, 0 < sz.1 i := by
    have hm : MeasurableSet {sz : (Fin p → ℝ) × (Fin p → ℝ) |
        ∀ i, 0 < sz.1 i} := by
      convert MeasurableSet.iInter fun i => measurableSet_lt
        (measurable_const : Measurable
          (fun _ : (Fin p → ℝ) × (Fin p → ℝ) => (0 : ℝ)))
        ((measurable_pi_apply i).comp
          (measurable_fst : Measurable
            (fun sz : (Fin p → ℝ) × (Fin p → ℝ) => sz.1))) using 1
      ext sz
      simp
    exact (ae_map_iff hcond hm).2 hpos
  have hfirstMeas : Measurable (fun y : ((Fin p → ℝ) × (Fin p → ℝ)) ×
      (Fin p → ℕ) => firstFactorial y.2 y.1.1 j) := by
    simp only [firstFactorial]
    fun_prop
  have hfirstNonneg : ∀ᵐ ω ∂μ, 0 ≤ firstFactorial (X ω) (S ω) j := by
    filter_upwards [hpos] with ω hs
    exact div_nonneg (Nat.cast_nonneg _) (hs j).le
  have hfirstLin : (∫⁻ y, ENNReal.ofReal (firstFactorial y.2 y.1.1 j)
        ∂μ.map (fun ω => ((S ω, Z ω), X ω))) =
      ∫⁻ sz, ENNReal.ofReal (Real.exp (sz.2 j)) ∂base := by
    rw [hjoint, Measure.lintegral_bind hκ
      hfirstMeas.ennreal_ofReal.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hposBase] with sz hs
    rw [lintegral_map' hfirstMeas.ennreal_ofReal.aemeasurable (by fun_prop)]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (firstFactorial_poisson_integrable sz.1 sz.2 j (ne_of_gt (hs j)))
      (ae_of_all _ fun x => div_nonneg (Nat.cast_nonneg _) (hs j).le)]
    rw [firstFactorial_poisson_integral sz.1 sz.2 j (hs j)]
  have hfirst : (∫ ω, firstFactorial (X ω) (S ω) j ∂μ) =
      ∫ ω, Real.exp (Z ω j) ∂μ := by
    rw [integral_eq_lintegral_of_nonneg_ae hfirstNonneg
      (hfirstMeas.aestronglyMeasurable.comp_aemeasurable hfull)]
    rw [← lintegral_map' hfirstMeas.ennreal_ofReal.aemeasurable hfull]
    rw [hfirstLin]
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun _ => (Real.exp_pos _).le) hj.1]
    change ENNReal.toReal (∫⁻ sz, ENNReal.ofReal (Real.exp (sz.2 j))
      ∂μ.map (fun ω => (S ω, Z ω))) = _
    rw [lintegral_map' (by fun_prop) hcond]
  have hcrossMeas : Measurable (fun y : ((Fin p → ℝ) × (Fin p → ℝ)) ×
      (Fin p → ℕ) => crossFactorial y.2 y.1.1 j k) := by
    by_cases h : j = k
    · subst k
      simp only [crossFactorial, ite_true, secondFactorial]
      fun_prop
    · simp only [crossFactorial, if_neg h]
      fun_prop
  have hcrossNonneg : ∀ᵐ ω ∂μ, 0 ≤ crossFactorial (X ω) (S ω) j k := by
    filter_upwards [hpos] with ω hs
    simp only [crossFactorial]
    split
    · apply div_nonneg _ (sq_nonneg _)
      by_cases hx : X ω j = 0
      · simp [hx]
      · exact mul_nonneg (Nat.cast_nonneg _)
          (sub_nonneg.mpr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hx))
    · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (mul_nonneg (hs j).le (hs k).le)
  have hcrossLin : (∫⁻ y, ENNReal.ofReal (crossFactorial y.2 y.1.1 j k)
        ∂μ.map (fun ω => ((S ω, Z ω), X ω))) =
      ∫⁻ sz, ENNReal.ofReal (Real.exp (sz.2 j + sz.2 k)) ∂base := by
    rw [hjoint, Measure.lintegral_bind hκ
      hcrossMeas.ennreal_ofReal.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hposBase] with sz hs
    rw [lintegral_map' hcrossMeas.ennreal_ofReal.aemeasurable (by fun_prop)]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (crossFactorial_poisson_integrable sz.1 sz.2 j k
        (ne_of_gt (hs j)) (ne_of_gt (hs k)))
      (ae_of_all _ fun x => by
        simp only [crossFactorial]
        split
        · apply div_nonneg _ (sq_nonneg _)
          by_cases hx : x j = 0
          · simp [hx]
          · exact mul_nonneg (Nat.cast_nonneg _)
              (sub_nonneg.mpr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hx))
        · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            (mul_nonneg (hs j).le (hs k).le))]
    rw [crossFactorial_poisson_integral sz.1 sz.2 j k (hs j) (hs k)]
  refine ⟨hfirst, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hcrossNonneg
    (hcrossMeas.aestronglyMeasurable.comp_aemeasurable hfull)]
  rw [← lintegral_map' hcrossMeas.ennreal_ofReal.aemeasurable hfull]
  rw [hcrossLin]
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun _ => (Real.exp_pos _).le) hjk.1]
  change ENNReal.toReal (∫⁻ sz, ENNReal.ofReal (Real.exp (sz.2 j + sz.2 k))
    ∂μ.map (fun ω => (S ω, Z ω))) = _
  rw [lintegral_map' (by fun_prop) hcond]

private lemma poisson_mixture_integral_of_fiber {p : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S Z : Ω → Fin p → ℝ) (X : Ω → Fin p → ℕ)
    (hP : PoissonMeasurement μ (fun _ : Unit => fun _ : Unit => Z)
      (fun _ _ => S) (fun _ _ => X))
    (F : (((Fin p → ℝ) × (Fin p → ℝ)) × (Fin p → ℕ)) → ℝ)
    (G : ((Fin p → ℝ) × (Fin p → ℝ)) → ℝ)
    (hFmeas : Measurable F) (hGmeas : Measurable G)
    (hFnonneg : ∀ s z, (∀ i, 0 < s i) → ∀ x, 0 ≤ F ((s, z), x))
    (hGnonneg : ∀ s z, (∀ i, 0 < s i) → 0 ≤ G (s, z))
    (hFint : ∀ s z, (∀ i, 0 < s i) → Integrable (fun x => F ((s, z), x))
      (poissonCountLaw s z))
    (hFmean : ∀ s z, (∀ i, 0 < s i) →
      (∫ x, F ((s, z), x) ∂poissonCountLaw s z) = G (s, z))
    (hGint : Integrable (fun ω => G (S ω, Z ω)) μ) :
    Integrable (fun ω => F ((S ω, Z ω), X ω)) μ ∧
      (∫ ω, F ((S ω, Z ω), X ω) ∂μ) = ∫ ω, G (S ω, Z ω) ∂μ := by
  have hp := hP () ()
  have hpos : ∀ᵐ ω ∂μ, ∀ i, 0 < S ω i := by simpa only using hp.1
  have hcond : AEMeasurable (fun ω => (S ω, Z ω)) μ := by simpa only using hp.2.1
  have hfull : AEMeasurable (fun ω => ((S ω, Z ω), X ω)) μ := by
    simpa only using hp.2.2.1
  have hjoint : μ.map (fun ω => ((S ω, Z ω), X ω)) =
      Measure.bind (μ.map (fun ω => (S ω, Z ω)))
        (fun sz => (poissonCountLaw sz.1 sz.2).map (fun x => (sz, x))) := by
    simpa only using hp.2.2.2
  let base := μ.map (fun ω => (S ω, Z ω))
  let κ := fun sz : (Fin p → ℝ) × (Fin p → ℝ) =>
    (poissonCountLaw sz.1 sz.2).map (fun x => (sz, x))
  have hμne : μ ≠ 0 := by
    intro hzero
    have hu := isProbabilityMeasure_iff.mp (inferInstance : IsProbabilityMeasure μ)
    rw [hzero] at hu
    simp at hu
  have hκ : AEMeasurable κ base := by
    apply AEMeasurable.of_map_ne_zero
    intro hzero
    have hb : base.bind κ = 0 := by simp [Measure.bind, hzero]
    have hjoint_ne := (Measure.map_ne_zero_iff hfull).2 hμne
    apply hjoint_ne
    rw [hjoint]
    exact hb
  have hposBase : ∀ᵐ sz ∂base, ∀ i, 0 < sz.1 i := by
    have hm : MeasurableSet {sz : (Fin p → ℝ) × (Fin p → ℝ) |
        ∀ i, 0 < sz.1 i} := by
      convert MeasurableSet.iInter fun i => measurableSet_lt
        (measurable_const : Measurable
          (fun _ : (Fin p → ℝ) × (Fin p → ℝ) => (0 : ℝ)))
        ((measurable_pi_apply i).comp
          (measurable_fst : Measurable
            (fun sz : (Fin p → ℝ) × (Fin p → ℝ) => sz.1))) using 1
      ext sz
      simp
    exact (ae_map_iff hcond hm).2 hpos
  have hsourceNonneg : ∀ᵐ ω ∂μ, 0 ≤ F ((S ω, Z ω), X ω) := by
    filter_upwards [hpos] with ω hs
    exact hFnonneg _ _ hs _
  have hlin : (∫⁻ y, ENNReal.ofReal (F y)
        ∂μ.map (fun ω => ((S ω, Z ω), X ω))) =
      ∫⁻ sz, ENNReal.ofReal (G sz) ∂base := by
    rw [hjoint, Measure.lintegral_bind hκ hFmeas.ennreal_ofReal.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hposBase] with sz hs
    rw [lintegral_map' hFmeas.ennreal_ofReal.aemeasurable (by fun_prop)]
    rw [← ofReal_integral_eq_lintegral_ofReal (hFint _ _ hs)
      (ae_of_all _ (hFnonneg _ _ hs))]
    rw [hFmean _ _ hs]
  have hsourceInt : Integrable (fun ω => F ((S ω, Z ω), X ω)) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (hFmeas.aestronglyMeasurable.comp_aemeasurable hfull) hsourceNonneg).mp
    change (∫⁻ ω, ENNReal.ofReal (F ((S ω, Z ω), X ω)) ∂μ) ≠ ⊤
    rw [← lintegral_map' hFmeas.ennreal_ofReal.aemeasurable hfull, hlin]
    rw [lintegral_map' hGmeas.ennreal_ofReal.aemeasurable hcond]
    exact (lintegral_ofReal_ne_top_iff_integrable hGint.1
      (by filter_upwards [hpos] with ω hs; exact hGnonneg _ _ hs)).mpr hGint
  refine ⟨hsourceInt, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hsourceNonneg
    (hFmeas.aestronglyMeasurable.comp_aemeasurable hfull)]
  rw [← lintegral_map' hFmeas.ennreal_ofReal.aemeasurable hfull, hlin]
  rw [integral_eq_lintegral_of_nonneg_ae
    (by filter_upwards [hpos] with ω hs; exact hGnonneg _ _ hs) hGint.1]
  change ENNReal.toReal (∫⁻ sz, ENNReal.ofReal (G sz)
    ∂μ.map (fun ω => (S ω, Z ω))) = _
  rw [lintegral_map' hGmeas.ennreal_ofReal.aemeasurable hcond]

set_option maxHeartbeats 1000000 in
-- The nested finite-product Poisson mixture elaboration exceeds the default heartbeat budget.
/-- For a positive measurable offset, the first two raw moments of the adjusted count
and adjusted second falling factorial are the corresponding conditional Poisson mixture
moments. The offset may depend arbitrarily on the latent log-rate. -/
-- @node: gate:poisson-mixture-adjusted-factorial-raw-moments
lemma poisson_mixture_adjusted_factorial_raw_moments {p : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S Z : Ω → Fin p → ℝ) (X : Ω → Fin p → ℕ)
    (hP : PoissonMeasurement μ (fun _ : Unit => fun _ : Unit => Z)
      (fun _ _ => S) (fun _ _ => X)) (j : Fin p)
    (h1 : Integrable (fun ω => Real.exp (Z ω j)) μ)
    (h2 : Integrable (fun ω => Real.exp (2 * Z ω j)) μ)
    (hU2 : Integrable (fun ω => Real.exp (2 * Z ω j) +
      Real.exp (Z ω j) / S ω j) μ)
    (hW2 : Integrable (fun ω => Real.exp (4 * Z ω j) +
      4 * Real.exp (3 * Z ω j) / S ω j +
      2 * Real.exp (2 * Z ω j) / (S ω j) ^ 2) μ) :
    (∫ ω, firstFactorial (X ω) (S ω) j ∂μ) =
        ∫ ω, Real.exp (Z ω j) ∂μ ∧
      (∫ ω, (firstFactorial (X ω) (S ω) j) ^ 2 ∂μ) =
        ∫ ω, (Real.exp (2 * Z ω j) + Real.exp (Z ω j) / S ω j) ∂μ ∧
      (∫ ω, secondFactorial (X ω) (S ω) j ∂μ) =
        ∫ ω, Real.exp (2 * Z ω j) ∂μ ∧
      (∫ ω, (secondFactorial (X ω) (S ω) j) ^ 2 ∂μ) =
        ∫ ω, (Real.exp (4 * Z ω j) + 4 * Real.exp (3 * Z ω j) / S ω j +
          2 * Real.exp (2 * Z ω j) / (S ω j) ^ 2) ∂μ ∧
      MemLp (fun ω => firstFactorial (X ω) (S ω) j) 2 μ ∧
      MemLp (fun ω => secondFactorial (X ω) (S ω) j) 2 μ := by
  have hdiag : Integrable (fun ω => Real.exp (Z ω j + Z ω j)) μ := by
    convert h2 using 1
    funext ω
    congr 1
    ring
  have hbasic := poisson_mixture_factorial_moment_transfer μ S Z X hP j j h1 hdiag
  have hfirst := hbasic.1
  have hsecond : (∫ ω, secondFactorial (X ω) (S ω) j ∂μ) =
      ∫ ω, Real.exp (2 * Z ω j) ∂μ := by
    simpa only [crossFactorial, if_pos, show ∀ ω, Z ω j + Z ω j = 2 * Z ω j by
      intro ω; ring] using hbasic.2
  have hfirstSq := poisson_mixture_integral_of_fiber μ S Z X hP
    (fun y => (firstFactorial y.2 y.1.1 j) ^ 2)
    (fun sz => Real.exp (2 * sz.2 j) + Real.exp (sz.2 j) / sz.1 j)
    (by simp only [firstFactorial]; fun_prop) (by fun_prop)
    (fun _ _ _ _ => sq_nonneg _)
    (fun s z hs => add_nonneg (Real.exp_pos _).le
      (div_nonneg (Real.exp_pos _).le (hs j).le))
    (fun s z hs => firstFactorial_sq_poisson_integrable s z j (ne_of_gt (hs j)))
    (fun s z hs => firstFactorial_sq_poisson_integral s z j (hs j)) hU2
  have hsecondSq := poisson_mixture_integral_of_fiber μ S Z X hP
    (fun y => (secondFactorial y.2 y.1.1 j) ^ 2)
    (fun sz => Real.exp (4 * sz.2 j) + 4 * Real.exp (3 * sz.2 j) / sz.1 j +
      2 * Real.exp (2 * sz.2 j) / (sz.1 j) ^ 2)
    (by simp only [secondFactorial]; fun_prop) (by fun_prop)
    (fun _ _ _ _ => sq_nonneg _)
    (fun s z hs => add_nonneg
      (add_nonneg (Real.exp_pos _).le
        (div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (hs j).le))
      (div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (sq_nonneg _)))
    (fun s z hs => secondFactorial_sq_poisson_integrable s z j (ne_of_gt (hs j)))
    (fun s z hs => secondFactorial_sq_poisson_integral s z j (hs j)) hW2
  have hfull : AEMeasurable (fun ω => ((S ω, Z ω), X ω)) μ := by
    simpa only using (hP () ()).2.2.1
  have hUmeas : AEStronglyMeasurable
      (fun ω => firstFactorial (X ω) (S ω) j) μ := by
    have hm : Measurable (fun y : ((Fin p → ℝ) × (Fin p → ℝ)) ×
        (Fin p → ℕ) => firstFactorial y.2 y.1.1 j) := by
      simp only [firstFactorial]
      fun_prop
    exact hm.aestronglyMeasurable.comp_aemeasurable hfull
  have hWmeas : AEStronglyMeasurable
      (fun ω => secondFactorial (X ω) (S ω) j) μ := by
    have hm : Measurable (fun y : ((Fin p → ℝ) × (Fin p → ℝ)) ×
        (Fin p → ℕ) => secondFactorial y.2 y.1.1 j) := by
      simp only [secondFactorial]
      fun_prop
    exact hm.aestronglyMeasurable.comp_aemeasurable hfull
  refine ⟨hfirst, hfirstSq.2, hsecond, hsecondSq.2, ?_, ?_⟩
  · exact (memLp_two_iff_integrable_sq hUmeas).2 hfirstSq.1
  · exact (memLp_two_iff_integrable_sq hWmeas).2 hsecondSq.1

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

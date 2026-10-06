module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.Experiment
public import Causalean.Stat.Minimax.ChiSquaredFinite
public import Causalean.Stat.Minimax.MarkovKernelTransport

/-! A two-point zero-control submodel for the parametric term. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- For [the specified inputs and assumptions](hyp:d,x₀,x), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def zengOneCellMass {d : ℕ} (x₀ : Fin d) (x : Fin d) : ℝ :=
  if x = x₀ then 1 else 0

/-- Given [the specified inputs and assumptions](hyp:d,x₀,x), [the stated mathematical conclusion holds](goal). -/
lemma zengOneCellMass_nonneg {d : ℕ} (x₀ x : Fin d) :
    0 ≤ zengOneCellMass x₀ x := by
  unfold zengOneCellMass
  split <;> norm_num

/-- Given [the specified inputs and assumptions](hyp:d,x₀), [the stated mathematical conclusion holds](goal). -/
lemma zengOneCellMass_sum {d : ℕ} (x₀ : Fin d) :
    ∑ x : Fin d, zengOneCellMass x₀ x = 1 := by
  simp [zengOneCellMass]

/-- Given [the specified inputs and assumptions](hyp:d,ε,u,hd,hε,hu), [the stated mathematical conclusion holds](goal). -/
lemma zeng_parametric_exists (d : ℕ) (ε u : ℝ) (hd : 1 ≤ d)
    (hε : 0 < ε ∧ ε < 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1) :
    ∃ P : ZengLaw d,
      P.1 = zengFiniteTable d (zengOneCellMass ⟨0, hd⟩) (fun _ => 1 / 2)
        (fun _ => u) ∧
      P ∈ zengZeroControlClass d ε ∧ zengATE P = u := by
  obtain ⟨P, hmeasure, hclass, hATE⟩ := zeng_finiteTable_zero_control d ε hd hε
    (zengOneCellMass ⟨0, hd⟩) (fun _ => 1 / 2) (fun _ => u)
    (zengOneCellMass_nonneg ⟨0, hd⟩) (zengOneCellMass_sum ⟨0, hd⟩)
    (by intro x hx; constructor <;> linarith [hε.2]) (fun _ => hu)
  refine ⟨P, hmeasure, hclass, ?_⟩
  rw [hATE]
  simp [zengOneCellMass]

/-- For [the specified inputs and assumptions](hyp:d,ε,u,hd,hε,hu), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def zengParametricLaw (d : ℕ) (ε u : ℝ) (hd : 1 ≤ d)
    (hε : 0 < ε ∧ ε < 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1) : ZengLaw d :=
  Classical.choose (zeng_parametric_exists d ε u hd hε hu)

/-- Given [the specified inputs and assumptions](hyp:d,ε,u,hd,hε,hu), [the stated mathematical conclusion holds](goal). -/
lemma zengParametricLaw_measure (d : ℕ) (ε u : ℝ) (hd : 1 ≤ d)
    (hε : 0 < ε ∧ ε < 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1) :
    (zengParametricLaw d ε u hd hε hu).1 =
      zengFiniteTable d (zengOneCellMass ⟨0, hd⟩) (fun _ => 1 / 2)
        (fun _ => u) :=
  (Classical.choose_spec (zeng_parametric_exists d ε u hd hε hu)).1

/-- Given [the specified inputs and assumptions](hyp:d,ε,u,hd,hε,hu), [the stated mathematical conclusion holds](goal). -/
lemma zengParametricLaw_mem (d : ℕ) (ε u : ℝ) (hd : 1 ≤ d)
    (hε : 0 < ε ∧ ε < 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1) :
    zengParametricLaw d ε u hd hε hu ∈ zengZeroControlClass d ε :=
  by
    unfold zengParametricLaw
    exact (Classical.choose_spec (zeng_parametric_exists d ε u hd hε hu)).2.1

/-- Given [the specified inputs and assumptions](hyp:d,ε,u,hd,hε,hu), [the stated mathematical conclusion holds](goal). -/
lemma zengParametricLaw_ate (d : ℕ) (ε u : ℝ) (hd : 1 ≤ d)
    (hε : 0 < ε ∧ ε < 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1) :
    zengATE (zengParametricLaw d ε u hd hε hu) = u :=
  by
    unfold zengParametricLaw
    exact (Classical.choose_spec (zeng_parametric_exists d ε u hd hε hu)).2.2

/-- Given [the specified inputs and assumptions](hyp:d,ε,u,hd,hε,hu,r), [the stated mathematical conclusion holds](goal). -/
lemma zengParametricLaw_singleton (d : ℕ) (ε u : ℝ) (hd : 1 ≤ d)
    (hε : 0 < ε ∧ ε < 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1)
    (r : ZengRecord d) :
    (zengParametricLaw d ε u hd hε hu).1.real {r} =
      if r.1 = (⟨0, hd⟩ : Fin d) then
        if r.2.1 then (if r.2.2 then u / 2 else (1 - u) / 2)
        else (if r.2.2 then 0 else 1 / 2)
      else 0 := by
  rcases r with ⟨x, b, y⟩
  rw [zengParametricLaw_measure]
  simp [zengFiniteTable, Measure.real, Set.indicator, zengOneCellMass]
  rw [Finset.sum_eq_single x]
  · cases b
    · cases y
      · by_cases hx : x = (⟨0, hd⟩ : Fin d)
        · simp [hx, zengBernWeight]
          norm_num [ENNReal.toReal_ofReal]
        · simp [hx]
      · norm_num [zengBernWeight, ENNReal.toReal_ofReal]
    · cases y
      · by_cases hx : x = (⟨0, hd⟩ : Fin d)
        · have hnon : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
          simp [hx, zengBernWeight, ENNReal.toReal_ofReal hnon]
          ring
        · simp [hx]
      · by_cases hx : x = (⟨0, hd⟩ : Fin d)
        · simp [hx, zengBernWeight, ENNReal.toReal_ofReal hu.1]
          ring
        · simp [hx]
  · intro x' hx hne
    simp [hne]
  · simp

/-- Given [the specified inputs and assumptions](hyp:d,ε,u,hd,hε,hu), [the stated mathematical conclusion holds](goal). -/
lemma zengParametricLaw_ac_half (d : ℕ) (ε u : ℝ) (hd : 1 ≤ d)
    (hε : 0 < ε ∧ ε < 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1) :
    (zengParametricLaw d ε u hd hε hu).1 ≪
      (zengParametricLaw d ε (1 / 2) hd hε (by norm_num)).1 := by
  intro s hzero
  rw [zengParametricLaw_measure] at hzero ⊢
  simp [zengFiniteTable, zengOneCellMass, zengBernWeight] at hzero ⊢
  intro i
  by_cases hi : i = (⟨0, hd⟩ : Fin d)
  · subst i
    have hsupport := hzero (⟨0, hd⟩ : Fin d)
    norm_num at hsupport
    simp [hsupport]
  · simp [hi]

/-- Given [the specified inputs and assumptions](hyp:d,ε,u,hd,hε,hu), [the stated mathematical conclusion holds](goal). -/
lemma zengParametricLaw_chiSq_half (d : ℕ) (ε u : ℝ) (hd : 1 ≤ d)
    (hε : 0 < ε ∧ ε < 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1) :
    1 + Causalean.Stat.chiSqDiv
        (zengParametricLaw d ε u hd hε hu).1
        (zengParametricLaw d ε (1 / 2) hd hε (by norm_num)).1 =
      1 + 2 * (u - 1 / 2) ^ 2 := by
  let P₁ := zengParametricLaw d ε u hd hε hu
  let P₀ := zengParametricLaw d ε (1 / 2) hd hε (by norm_num)
  letI : IsProbabilityMeasure P₁.1 := P₁.2
  letI : IsProbabilityMeasure P₀.1 := P₀.2
  change 1 + Causalean.Stat.chiSqDiv P₁.1 P₀.1 = _
  rw [Causalean.Stat.finite_one_add_chiSqDiv _ _
    (zengParametricLaw_ac_half d ε u hd hε hu)]
  simp_rw [zengParametricLaw_singleton]
  simp only [Fintype.sum_prod_type]
  simp
  rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · norm_num
    ring
  · intro x hx hne
    simp [hne]
  · simp

/-- For [the specified inputs and assumptions](hyp:n), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def zengParametricStep (n : ℕ) : ℝ :=
  1 / (4 * Real.sqrt n)

/-- Given [the specified inputs and assumptions](hyp:n,hn), [the stated mathematical conclusion holds](goal). -/
lemma zengParametricStep_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < zengParametricStep n := by
  unfold zengParametricStep
  positivity

/-- Given [the specified inputs and assumptions](hyp:n,hn), [the stated mathematical conclusion holds](goal). -/
lemma zengParametricStep_le_quarter (n : ℕ) (hn : 1 ≤ n) :
    zengParametricStep n ≤ 1 / 4 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : (1 : ℝ) ≤ Real.sqrt n := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hnR
  unfold zengParametricStep
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.sqrt n)]
  nlinarith

/-- Given [the specified inputs and assumptions](hyp:n,hn), [the stated mathematical conclusion holds](goal). -/
lemma zengParametricPerturbation_mem (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ (1 / 2 + zengParametricStep n) ∧
      (1 / 2 + zengParametricStep n) ≤ 1 := by
  have hp := zengParametricStep_pos n hn
  have hq := zengParametricStep_le_quarter n hn
  constructor <;> linarith

/-- Given [the specified inputs and assumptions](hyp:n,d,ε,hn,hd,hε), [the stated mathematical conclusion holds](goal). -/
lemma zengParametricPerturbation_chiSq (n d : ℕ) (ε : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hε : 0 < ε ∧ ε < 1 / 2) :
    Causalean.Stat.chiSqDiv
        (zengParametricLaw d ε (1 / 2 + zengParametricStep n) hd hε
          (zengParametricPerturbation_mem n hn)).1
        (zengParametricLaw d ε (1 / 2) hd hε (by norm_num)).1 ≤
      (1 / 8 : ℝ) / n := by
  have hEq := zengParametricLaw_chiSq_half d ε
    (1 / 2 + zengParametricStep n) hd hε
    (zengParametricPerturbation_mem n hn)
  have hchi : Causalean.Stat.chiSqDiv
        (zengParametricLaw d ε (1 / 2 + zengParametricStep n) hd hε
          (zengParametricPerturbation_mem n hn)).1
        (zengParametricLaw d ε (1 / 2) hd hε (by norm_num)).1 =
      2 * (zengParametricStep n) ^ 2 := by
    linarith
  rw [hchi]
  have hnR : (0 : ℝ) < n := by positivity
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ 2 = n := by
    rw [Real.sq_sqrt (le_of_lt hnR)]
  unfold zengParametricStep
  rw [div_pow]
  field_simp
  nlinarith

/-- [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def ZengParametricDecisionReduction : Prop :=
  ∀ (n d : ℕ) (ε c : ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d)
      (hε : 0 < ε ∧ ε < 1 / 2),
    0 < c →
    (∀ A : Set (Fin n → ZengRecord d), MeasurableSet A →
      (zengSampleLaw n
        (zengParametricLaw d ε (1 / 2 + zengParametricStep n) hd hε
          (zengParametricPerturbation_mem n hn))).real Aᶜ +
      (zengSampleLaw n
        (zengParametricLaw d ε (1 / 2) hd hε (by norm_num))).real A ≥ c) →
    ∀ T : ZengEstimator n d,
      c * (zengParametricStep n) ^ 2 / 8 ≤
        max
          (zengSquaredRisk T
            (zengParametricLaw d ε (1 / 2) hd hε (by norm_num)))
          (zengSquaredRisk T
            (zengParametricLaw d ε (1 / 2 + zengParametricStep n) hd hε
              (zengParametricPerturbation_mem n hn)))

private def zengClip (t : ℝ) : ℝ := max (-1) (min 1 t)

private lemma zengClip_measurable : Measurable zengClip := by
  unfold zengClip
  fun_prop

private lemma zengClip_bound : Causalean.Stat.UniformlyBounded zengClip := by
  refine ⟨1, by norm_num, ?_⟩
  intro t
  rw [abs_le]
  simp [zengClip]

private lemma zengClip_eq {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : zengClip t = t := by
  simp [zengClip, ht.1, ht.2]

private lemma zengClip_abs_le (t : ℝ) : |zengClip t| ≤ 1 := by
  rw [abs_le]
  constructor <;> simp [zengClip]

private lemma zeng_kernelMean_risk_le {n d : ℕ} (T : ZengEstimator n d)
    (P : ZengLaw d) :
    zengDeterministicRisk (Causalean.Stat.kernelMean T.1 zengClip) P ≤
      zengSquaredRisk T P := by
  letI : IsMarkovKernel T.1 := T.2.1
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsProbabilityMeasure (zengSampleLaw n P) := by
    unfold zengSampleLaw
    infer_instance
  have hpoint (s : Fin n → ZengRecord d) :
      (Causalean.Stat.kernelMean T.1 zengClip s - zengATE P) ^ 2 ≤
        ∫ t, (t - zengATE P) ^ 2 ∂(T.1 s) := by
    calc
      _ ≤ ∫ t, (zengClip t - zengATE P) ^ 2 ∂(T.1 s) :=
        Causalean.Stat.sqLoss_kernelMean_le T.1 zengClip_measurable
          zengClip_bound (zengATE P) s
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [(mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (T.2.2 s)] with t ht
        rw [zengClip_eq ht]
  have hmeas : Measurable (fun s ↦ ∫ t, (t - zengATE P) ^ 2 ∂(T.1 s)) := by
    exact ((measurable_id.sub measurable_const).pow_const 2).stronglyMeasurable.integral_kernel.measurable
  have hbound (s : Fin n → ZengRecord d) :
      |(∫ t, (t - zengATE P) ^ 2 ∂(T.1 s))| ≤ 4 := by
    have hATE := zeng_ate_mem_Icc P
    have hs : ∀ᵐ t ∂(T.1 s), t ∈ Icc (-1 : ℝ) 1 :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (T.2.2 s)
    have hle : ∀ᵐ t ∂(T.1 s), (t - zengATE P) ^ 2 ≤ 4 := by
      filter_upwards [hs] with t ht
      rw [Set.mem_Icc] at ht hATE
      nlinarith [sq_nonneg (t - zengATE P + 2), sq_nonneg (t - zengATE P - 2)]
    have hnon : 0 ≤ ∫ t, (t - zengATE P) ^ 2 ∂(T.1 s) := integral_nonneg (fun _ ↦ sq_nonneg _)
    rw [abs_of_nonneg hnon]
    simpa using integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t ↦ sq_nonneg (t - zengATE P))
      (integrable_const 4) hle
  unfold zengDeterministicRisk zengSquaredRisk
  exact integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
    (Integrable.of_bound hmeas.aestronglyMeasurable 4
      (Filter.Eventually.of_forall fun s ↦ by simpa [Real.norm_eq_abs] using hbound s))
    (Filter.Eventually.of_forall hpoint)

/-- [the stated mathematical conclusion holds](goal). -/
theorem zengParametricDecisionReduction_proved : ZengParametricDecisionReduction := by
  intro n d ε c hn hd hε hc htest T
  let P₀ := zengParametricLaw d ε (1 / 2) hd hε (by norm_num)
  let P₁ := zengParametricLaw d ε (1 / 2 + zengParametricStep n) hd hε
    (zengParametricPerturbation_mem n hn)
  let f := Causalean.Stat.kernelMean T.1 zengClip
  let δ := zengParametricStep n
  let θ₀ : ℝ := 1 / 2
  let θ₁ : ℝ := 1 / 2 + δ
  let E₀ : Set (Fin n → ZengRecord d) := {s | δ / 2 ≤ |f s - θ₀|}
  let E₁ : Set (Fin n → ZengRecord d) := {s | δ / 2 ≤ |f s - θ₁|}
  let A : Set (Fin n → ZengRecord d) := {s | |f s - θ₁| ≤ |f s - θ₀|}
  letI : IsMarkovKernel T.1 := T.2.1
  letI : IsProbabilityMeasure P₀.1 := P₀.2
  letI : IsProbabilityMeasure P₁.1 := P₁.2
  letI : IsProbabilityMeasure (zengSampleLaw n P₀) := by
    unfold zengSampleLaw
    infer_instance
  letI : IsProbabilityMeasure (zengSampleLaw n P₁) := by
    unfold zengSampleLaw
    infer_instance
  have hδ : 0 < δ := zengParametricStep_pos n hn
  have hf : Measurable f := Causalean.Stat.measurable_kernelMean T.1 zengClip_measurable
  have hA : MeasurableSet A := by
    exact measurableSet_le
      (continuous_abs.measurable.comp (hf.sub measurable_const))
      (continuous_abs.measurable.comp (hf.sub measurable_const))
  have hA_E₀ : A ⊆ E₀ := by
    intro s hs
    simp only [A, E₀, Set.mem_setOf_eq] at hs ⊢
    have htri : δ ≤ |f s - θ₀| + |f s - θ₁| := by
      have := abs_sub_le θ₁ (f s) θ₀
      dsimp [θ₀, θ₁, δ] at this ⊢
      norm_num at this
      rw [abs_of_pos (zengParametricStep_pos n hn)] at this
      simpa [abs_sub_comm, add_comm] using this
    linarith
  have hAc_E₁ : Aᶜ ⊆ E₁ := by
    intro s hs
    simp only [A, E₁, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hs ⊢
    have htri : δ ≤ |f s - θ₀| + |f s - θ₁| := by
      have := abs_sub_le θ₁ (f s) θ₀
      dsimp [θ₀, θ₁, δ] at this ⊢
      norm_num at this
      rw [abs_of_pos (zengParametricStep_pos n hn)] at this
      simpa [abs_sub_comm, add_comm] using this
    linarith
  have htest' : c ≤ (zengSampleLaw n P₁).real E₁ +
      (zengSampleLaw n P₀).real E₀ := by
    calc
      c ≤ (zengSampleLaw n P₁).real Aᶜ +
          (zengSampleLaw n P₀).real A := htest A hA
      _ ≤ _ := add_le_add
        (measureReal_mono hAc_E₁ (by finiteness))
        (measureReal_mono hA_E₀ (by finiteness))
  have hfbound : ∀ s, f s ∈ Icc (-1 : ℝ) 1 := by
    intro s
    rw [Set.mem_Icc, ← abs_le]
    exact Causalean.Stat.abs_kernelMean_le T.1 (M := 1) (by norm_num)
      zengClip_abs_le s
  have hint₀ : Integrable (fun s ↦ (f s - θ₀) ^ 2) (zengSampleLaw n P₀) :=
    Causalean.Stat.mse_integrable_of_estimator_bound _ f hf (by norm_num) hfbound
  have hint₁ : Integrable (fun s ↦ (f s - θ₁) ^ 2) (zengSampleLaw n P₁) :=
    Causalean.Stat.mse_integrable_of_estimator_bound _ f hf (by norm_num) hfbound
  have hmse₀ : (δ / 2) ^ 2 * (zengSampleLaw n P₀).real E₀ ≤
      zengDeterministicRisk f P₀ := by
    unfold zengDeterministicRisk E₀
    rw [zengParametricLaw_ate]
    have hset : {s | (δ / 2) ^ 2 ≤ (f s - θ₀) ^ 2} =
        {s | δ / 2 ≤ |f s - θ₀|} := by
      ext s
      simp only [Set.mem_setOf_eq]
      rw [sq_le_sq, abs_of_nonneg (show (0 : ℝ) ≤ δ / 2 by positivity)]
    rw [← hset]
    exact mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun s ↦ sq_nonneg _) hint₀ _
  have hmse₁ : (δ / 2) ^ 2 * (zengSampleLaw n P₁).real E₁ ≤
      zengDeterministicRisk f P₁ := by
    unfold zengDeterministicRisk E₁
    rw [zengParametricLaw_ate]
    have hset : {s | (δ / 2) ^ 2 ≤ (f s - θ₁) ^ 2} =
        {s | δ / 2 ≤ |f s - θ₁|} := by
      ext s
      simp only [Set.mem_setOf_eq]
      rw [sq_le_sq, abs_of_nonneg (show (0 : ℝ) ≤ δ / 2 by positivity)]
    rw [← hset]
    exact mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun s ↦ sq_nonneg _) hint₁ _
  have hmax : c / 2 ≤ max ((zengSampleLaw n P₀).real E₀)
      ((zengSampleLaw n P₁).real E₁) := by
    nlinarith [le_max_left ((zengSampleLaw n P₀).real E₀)
      ((zengSampleLaw n P₁).real E₁),
      le_max_right ((zengSampleLaw n P₀).real E₀)
        ((zengSampleLaw n P₁).real E₁)]
  calc
    c * δ ^ 2 / 8 ≤ (δ / 2) ^ 2 *
        max ((zengSampleLaw n P₀).real E₀)
          ((zengSampleLaw n P₁).real E₁) := by nlinarith [sq_nonneg δ]
    _ = max ((δ / 2) ^ 2 * (zengSampleLaw n P₀).real E₀)
          ((δ / 2) ^ 2 * (zengSampleLaw n P₁).real E₁) := by
      by_cases hle : (zengSampleLaw n P₀).real E₀ ≤
          (zengSampleLaw n P₁).real E₁
      · rw [max_eq_right hle, max_eq_right]
        exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
      · have hge := le_of_not_ge hle
        rw [max_eq_left hge, max_eq_left]
        exact mul_le_mul_of_nonneg_left hge (sq_nonneg _)
    _ ≤ max (zengDeterministicRisk f P₀) (zengDeterministicRisk f P₁) :=
      max_le_max hmse₀ hmse₁
    _ ≤ max (zengSquaredRisk T P₀) (zengSquaredRisk T P₁) :=
      max_le_max (zeng_kernelMean_risk_le T P₀) (zeng_kernelMean_risk_le T P₁)

/-- Given [the specified inputs and assumptions](hyp:hdecision), [the stated mathematical conclusion holds](goal). -/
theorem zeng_parametric_lower_of_decisionReduction
    (hdecision : ZengParametricDecisionReduction) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n d : ℕ) (ε : ℝ), 1 ≤ n → 1 ≤ d →
        0 < ε ∧ ε < 1 / 2 →
        c / n ≤ zengZeroControlRisk n d ε := by
  obtain ⟨ctest, hctest, htest⟩ :=
    Causalean.Stat.le_cam_two_point_chisq.2 (1 / 8) (by norm_num)
  refine ⟨ctest / 128, by positivity, ?_⟩
  intro n d ε hn hd hε
  let P₁ := zengParametricLaw d ε (1 / 2 + zengParametricStep n) hd hε
    (zengParametricPerturbation_mem n hn)
  let P₀ := zengParametricLaw d ε (1 / 2) hd hε (by norm_num)
  letI : IsProbabilityMeasure P₁.1 := P₁.2
  letI : IsProbabilityMeasure P₀.1 := P₀.2
  have hfloor : ∀ A : Set (Fin n → ZengRecord d), MeasurableSet A →
      (zengSampleLaw n P₁).real Aᶜ + (zengSampleLaw n P₀).real A ≥ ctest := by
    intro A hA
    apply htest P₁.1 P₀.1
      (zengParametricLaw_ac_half d ε
        (1 / 2 + zengParametricStep n) hd hε
        (zengParametricPerturbation_mem n hn))
      (Integrable.of_finite) n (by omega)
      (zengParametricPerturbation_chiSq n d ε hn hd hε) A hA
  have htwo : ∀ T : ZengEstimator n d,
      ctest * (zengParametricStep n) ^ 2 / 8 ≤
        max (zengSquaredRisk T P₀) (zengSquaredRisk T P₁) := by
    exact hdecision n d ε ctest hn hd hε hctest hfloor
  let θ₀ : {P : ZengLaw d // P ∈ zengZeroControlClass d ε} :=
    ⟨P₀, zengParametricLaw_mem d ε (1 / 2) hd hε (by norm_num)⟩
  let θ₁ : {P : ZengLaw d // P ∈ zengZeroControlClass d ε} :=
    ⟨P₁, zengParametricLaw_mem d ε
      (1 / 2 + zengParametricStep n) hd hε
      (zengParametricPerturbation_mem n hn)⟩
  let T₀ : ZengEstimator n d :=
    ⟨Kernel.const _ (Measure.dirac 0), inferInstance, by
      intro s
      simp [Kernel.const_apply]⟩
  letI : Nonempty (ZengEstimator n d) := ⟨T₀⟩
  have hmini : ctest * (zengParametricStep n) ^ 2 / 8 ≤
      zengZeroControlRisk n d ε := by
    apply Causalean.Stat.le_minimaxValue_of_two_point θ₀ θ₁
    · intro T
      refine ⟨4, ?_⟩
      rintro r ⟨θ, rfl⟩
      exact (zeng_squaredRisk_bounds ε T θ.1 θ.2.1).2
    · intro T
      exact htwo T
  apply le_trans ?_ hmini
  have hnR : (0 : ℝ) < n := by positivity
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ 2 = n :=
    Real.sq_sqrt (le_of_lt hnR)
  unfold zengParametricStep
  rw [div_pow]
  field_simp
  nlinarith

/-- [the stated mathematical conclusion holds](goal). -/
theorem zeng_parametric_lower :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n d : ℕ) (ε : ℝ), 1 ≤ n → 1 ≤ d →
        0 < ε ∧ ε < 1 / 2 →
        c / n ≤ zengZeroControlRisk n d ε :=
  zeng_parametric_lower_of_decisionReduction zengParametricDecisionReduction_proved

end CausalSmith.Stat.MarRareqLogfrontier

module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-! Bounded randomized decision class for the fixed-positivity comparison. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @env: S4
variable (n d : ℕ) (ε : ℝ)
/-- For [the specified inputs and assumptions](hyp:n,d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
abbrev ZengEstimator (n d : ℕ) :=
  {T : Kernel (Fin n → ZengRecord d) ℝ //
    IsMarkovKernel T ∧ ∀ s, T s (Icc (-1 : ℝ) 1) = 1}
  -- @realizes \(\mathbf Z_n\)(observational sample); @realizes \(P_Z\)(law input)

/-- For [the specified inputs and assumptions](hyp:d,n,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def zengSampleLaw {d : ℕ} (n : ℕ) (P : ZengLaw d) :
    Measure (Fin n → ZengRecord d) := Measure.pi (fun _ : Fin n => P.1)

/-- For [the specified inputs and assumptions](hyp:n,d,T,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def zengSquaredRisk {n d : ℕ}
    (T : ZengEstimator n d) (P : ZengLaw d) : ℝ :=
  ∫ s, (∫ t, (t - zengATE P) ^ 2 ∂(T.1 s)) ∂(zengSampleLaw n P)

/-- For [the specified inputs and assumptions](hyp:n,d,f,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def zengDeterministicRisk {n d : ℕ}
    (f : (Fin n → ZengRecord d) → ℝ) (P : ZengLaw d) : ℝ :=
  ∫ s, (f s - zengATE P) ^ 2 ∂(zengSampleLaw n P)

/-- For [the specified inputs and assumptions](hyp:n,d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def fixedQRate (n d : ℕ) : ℝ :=
  min 1 ((n : ℝ)⁻¹ +
    ((d : ℝ) / ((n : ℝ) * Real.log (Real.exp 1 + n))) ^ 2)

/-- For [the specified inputs and assumptions](hyp:d,ε), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def zengZeroControlClass (d : ℕ) (ε : ℝ) : Set (ZengLaw d) :=
  {P | P ∈ zengDiscreteClass d ε ∧
    ∀ x : Fin d, ∀ h : 0 < zengCategory P x, zengMean P x false h = 0}

/-- For [the specified inputs and assumptions](hyp:n,d,ε), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def zengZeroControlRisk (n d : ℕ) (ε : ℝ) : ℝ :=
  Causalean.Stat.minimaxValueReal
    (E := ZengEstimator n d) (Θ := {P : ZengLaw d // P ∈ zengZeroControlClass d ε})
    (fun T P => zengSquaredRisk T P.1)

-- @node: def:zeng-minimax-risk
/-- For [the specified inputs and assumptions](hyp:n,d,ε), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def zengMinimaxRisk (n d : ℕ) (ε : ℝ) : ℝ :=
  Causalean.Stat.minimaxValueReal
    (E := ZengEstimator n d) (Θ := {P : ZengLaw d // P ∈ zengDiscreteClass d ε})
    (fun T P => zengSquaredRisk T P.1)
  -- @realizes \(\mathfrak R^Z_{n,d,\epsilon}\)(bounded-kernel minimax risk)

-- @node: zeng_category_sum
/-- Given [the specified inputs and assumptions](hyp:d,P), [the stated mathematical conclusion holds](goal). -/
lemma zeng_category_sum {d : ℕ} (P : ZengLaw d) :
    ∑ x : Fin d, zengCategory P x = 1 := by
  letI : IsProbabilityMeasure P.1 := P.2
  have h := MeasureTheory.sum_measureReal_preimage_singleton
    (μ := P.1) (s := Finset.univ) (f := fun r : ZengRecord d => r.1)
      (by intro x hx; exact MeasurableSet.of_discrete)
  calc
    ∑ x : Fin d, zengCategory P x =
        ∑ x : Fin d, P.1.real ((fun r : ZengRecord d => r.1) ⁻¹' {x}) := by
      congr 1
    _ = 1 := by simpa using h

-- @node: zeng_mean_mem_Icc
/-- Given [the specified inputs and assumptions](hyp:d,P,x,b,h), [the stated mathematical conclusion holds](goal). -/
lemma zeng_mean_mem_Icc {d : ℕ} (P : ZengLaw d) (x : Fin d)
    (b : Bool) (h : 0 < zengCategory P x) :
    zengMean P x b h ∈ Set.Icc (0 : ℝ) 1 := by
  letI : IsProbabilityMeasure P.1 := P.2
  have hnum : 0 ≤ P.1.real {r | r.1 = x ∧ r.2.1 = b ∧ r.2.2 = true} :=
    measureReal_nonneg
  have hle : P.1.real {r | r.1 = x ∧ r.2.1 = b ∧ r.2.2 = true} ≤
      zengArm P x b := by
    apply measureReal_mono (by
      intro r hr
      exact ⟨hr.1, hr.2.1⟩) (by finiteness)
  have hden : 0 ≤ zengArm P x b := measureReal_nonneg
  rcases hden.eq_or_lt with hzero | hpos
  · have hnumzero := le_antisymm (hzero ▸ hle) hnum
    simp [zengMean, ← hzero, hnumzero, Set.mem_Icc]
  · simp only [zengMean, Set.mem_Icc]
    constructor
    · exact div_nonneg hnum (le_of_lt hpos)
    · exact (div_le_iff₀ hpos).mpr (by simpa using hle)

-- @node: zeng_ate_mem_Icc
/-- Given [the specified inputs and assumptions](hyp:d,P), [the stated mathematical conclusion holds](goal). -/
lemma zeng_ate_mem_Icc {d : ℕ} (P : ZengLaw d) :
    zengATE P ∈ Set.Icc (-1 : ℝ) 1 := by
  letI : IsProbabilityMeasure P.1 := P.2
  have hterm (x : Fin d) :
      -zengCategory P x ≤
        (if h : 0 < zengCategory P x then
          zengCategory P x * (zengMean P x true h - zengMean P x false h) else 0) ∧
      (if h : 0 < zengCategory P x then
          zengCategory P x * (zengMean P x true h - zengMean P x false h) else 0) ≤
        zengCategory P x := by
    by_cases hx : 0 < zengCategory P x
    · simp only [dif_pos hx]
      have htrue := zeng_mean_mem_Icc P x true hx
      have hfalse := zeng_mean_mem_Icc P x false hx
      rw [Set.mem_Icc] at htrue hfalse
      constructor
      · have hd : -1 ≤ zengMean P x true hx - zengMean P x false hx := by
          linarith [htrue.1, hfalse.2]
        calc
          -zengCategory P x = zengCategory P x * (-1) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hd (le_of_lt hx)
      · have hd : zengMean P x true hx - zengMean P x false hx ≤ 1 := by
          linarith [htrue.2, hfalse.1]
        calc
          _ ≤ zengCategory P x * 1 := mul_le_mul_of_nonneg_left hd (le_of_lt hx)
          _ = zengCategory P x := by ring
    · simp only [dif_neg hx]
      have hc : 0 ≤ zengCategory P x := measureReal_nonneg
      constructor <;> linarith
  have hsum := zeng_category_sum P
  rw [Set.mem_Icc]
  constructor
  · calc
      (-1 : ℝ) = ∑ x : Fin d, -zengCategory P x := by
        simp [Finset.sum_neg_distrib, hsum]
      _ ≤ zengATE P := by
        simp only [zengATE]
        exact Finset.sum_le_sum (fun x _ => (hterm x).1)
  · calc
      zengATE P ≤ ∑ x : Fin d, zengCategory P x := by
        simp only [zengATE]
        exact Finset.sum_le_sum (fun x _ => (hterm x).2)
      _ = 1 := hsum

/-- Given [the specified inputs and assumptions](hyp:n,d,ε,T,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma zeng_squaredRisk_bounds {n d : ℕ} (ε : ℝ) (T : ZengEstimator n d)
    (P : ZengLaw d) (hP : P ∈ zengDiscreteClass d ε) :
    0 ≤ zengSquaredRisk T P ∧ zengSquaredRisk T P ≤ 4 := by
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsMarkovKernel T.1 := T.2.1
  have hATE := zeng_ate_mem_Icc P
  rw [Set.mem_Icc] at hATE
  have hinner_nonneg (s : Fin n → ZengRecord d) :
      0 ≤ ∫ t, (t - zengATE P) ^ 2 ∂(T.1 s) := by
    exact integral_nonneg (fun t => sq_nonneg _)
  have hinner_le (s : Fin n → ZengRecord d) :
      (∫ t, (t - zengATE P) ^ 2 ∂(T.1 s)) ≤ 4 := by
    haveI : IsProbabilityMeasure (T.1 s) := inferInstance
    have hs : ∀ᵐ t ∂(T.1 s), t ∈ Set.Icc (-1 : ℝ) 1 :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (T.2.2 s)
    have hb : ∀ᵐ t ∂(T.1 s), (t - zengATE P) ^ 2 ≤ 4 := by
      filter_upwards [hs] with t ht
      rw [Set.mem_Icc] at ht
      nlinarith [sq_nonneg (t - zengATE P + 2), sq_nonneg (t - zengATE P - 2)]
    simpa using (integral_mono_of_nonneg (μ := T.1 s)
      (Filter.Eventually.of_forall (fun t => sq_nonneg (t - zengATE P)))
      (integrable_const 4) hb)
  haveI : IsProbabilityMeasure (zengSampleLaw n P) := by
    unfold zengSampleLaw
    infer_instance
  constructor
  · exact integral_nonneg hinner_nonneg
  · simpa [zengSquaredRisk] using (integral_mono_of_nonneg (μ := zengSampleLaw n P)
      (Filter.Eventually.of_forall hinner_nonneg) (integrable_const 4)
      (Filter.Eventually.of_forall hinner_le))

private def zengClip (t : ℝ) : ℝ := max (-1) (min 1 t)

private lemma zengClip_measurable : Measurable zengClip := by
  unfold zengClip
  fun_prop

private lemma zengClip_mem (t : ℝ) : zengClip t ∈ Set.Icc (-1 : ℝ) 1 := by
  simp [zengClip]

private lemma zengClip_sq_sub_le (t θ : ℝ) (hθ : θ ∈ Set.Icc (-1 : ℝ) 1) :
    (zengClip t - θ) ^ 2 ≤ (t - θ) ^ 2 := by
  rw [Set.mem_Icc] at hθ
  unfold zengClip
  by_cases htlo : t < -1
  · have hclip : max (-1) (min 1 t) = -1 := by
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    rw [hclip]
    nlinarith [sq_nonneg (t - θ), sq_nonneg (t + 1)]
  · have htlo' : -1 ≤ t := le_of_not_gt htlo
    by_cases hthi : 1 < t
    · have hclip : max (-1) (min 1 t) = 1 := by
        rw [min_eq_left (le_of_lt hthi), max_eq_right (by norm_num)]
      rw [hclip]
      nlinarith [sq_nonneg (t - θ), sq_nonneg (t - 1)]
    · have hthi' : t ≤ 1 := le_of_not_gt hthi
      simp [min_eq_right hthi', max_eq_right htlo']

private noncomputable def zengClipKernel {n d : ℕ}
    (T : {K : Kernel (Fin n → ZengRecord d) ℝ // IsMarkovKernel K}) :
    ZengEstimator n d := by
  haveI : IsMarkovKernel T.1 := T.2
  let K := T.1.map zengClip
  have hK : IsMarkovKernel K := Kernel.IsMarkovKernel.map T.1 zengClip_measurable
  refine ⟨K, hK, ?_⟩
  intro s
  rw [Kernel.map_apply _ zengClip_measurable]
  rw [Measure.map_apply zengClip_measurable measurableSet_Icc]
  have hpre : zengClip ⁻¹' Set.Icc (-1 : ℝ) 1 = Set.univ := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_univ, iff_true]
    exact zengClip_mem t
  rw [hpre, measure_univ]

private lemma zengClipKernel_lintegral_le {n d : ℕ}
    (T : {K : Kernel (Fin n → ZengRecord d) ℝ // IsMarkovKernel K})
    (P : ZengLaw d) :
    (∫⁻ s, (∫⁻ t, ENNReal.ofReal ((t - zengATE P) ^ 2)
      ∂((zengClipKernel T).1 s)) ∂(zengSampleLaw n P)) ≤
    ∫⁻ s, (∫⁻ t, ENNReal.ofReal ((t - zengATE P) ^ 2)
      ∂(T.1 s)) ∂(zengSampleLaw n P) := by
  apply lintegral_mono
  intro s
  change (∫⁻ t, ENNReal.ofReal ((t - zengATE P) ^ 2)
      ∂((T.1.map zengClip) s)) ≤ _
  rw [Kernel.map_apply _ zengClip_measurable]
  have hg : AEMeasurable (fun t : ℝ => ENNReal.ofReal ((t - zengATE P) ^ 2))
      (Measure.map zengClip (T.1 s)) := by fun_prop
  rw [MeasureTheory.lintegral_map' hg zengClip_measurable.aemeasurable]
  apply lintegral_mono
  intro t
  exact ENNReal.ofReal_le_ofReal (zengClip_sq_sub_le t (zengATE P) (zeng_ate_mem_Icc P))

private lemma zeng_bounded_lintegral_eq_ofReal {n d : ℕ}
    (T : ZengEstimator n d) (P : ZengLaw d) :
    (∫⁻ s, (∫⁻ t, ENNReal.ofReal ((t - zengATE P) ^ 2)
      ∂(T.1 s)) ∂(zengSampleLaw n P)) = ENNReal.ofReal (zengSquaredRisk T P) := by
  letI : IsMarkovKernel T.1 := T.2.1
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsProbabilityMeasure (zengSampleLaw n P) := by
    unfold zengSampleLaw
    infer_instance
  have hATE := zeng_ate_mem_Icc P
  have hloss_int (s : Fin n → ZengRecord d) :
      Integrable (fun t => (t - zengATE P) ^ 2) (T.1 s) := by
    refine (integrable_const 4).mono'
      ((measurable_id.sub measurable_const).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [(mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (T.2.2 s)] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [Set.mem_Icc] at hATE
    rw [Set.mem_Icc] at ht
    nlinarith [sq_nonneg (t - zengATE P + 2), sq_nonneg (t - zengATE P - 2)]
  let g : (Fin n → ZengRecord d) → ℝ :=
    fun s => ∫ t, (t - zengATE P) ^ 2 ∂(T.1 s)
  have hg_meas : Measurable g := by
    exact ((measurable_id.sub measurable_const).pow_const 2).stronglyMeasurable.integral_kernel.measurable
  have hg_nonneg : ∀ s, 0 ≤ g s := fun s => integral_nonneg (fun t => sq_nonneg _)
  have hg_le : ∀ s, g s ≤ 4 := by
    intro s
    haveI : IsProbabilityMeasure (T.1 s) := inferInstance
    have ht : ∀ᵐ u ∂(T.1 s), u ∈ Set.Icc (-1 : ℝ) 1 :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (T.2.2 s)
    have hmono := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun u => sq_nonneg (u - zengATE P))
      (integrable_const 4) (by
        filter_upwards [ht] with u hu
        rw [Set.mem_Icc] at hu hATE
        nlinarith [sq_nonneg (u - zengATE P + 2), sq_nonneg (u - zengATE P - 2)])
    have huniv : (T.1 s).real Set.univ = 1 := by simp
    rw [integral_const, huniv, one_smul] at hmono
    simpa [g] using hmono
  have hg_int : Integrable g (zengSampleLaw n P) :=
    (integrable_const 4).mono' hg_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg s)]
        exact hg_le s)
  unfold zengSquaredRisk
  change (∫⁻ s, ∫⁻ t, ENNReal.ofReal ((t - zengATE P) ^ 2) ∂(T.1 s)
      ∂(zengSampleLaw n P)) = ENNReal.ofReal (∫ s, g s ∂(zengSampleLaw n P))
  rw [ofReal_integral_eq_lintegral_ofReal hg_int
    (Filter.Eventually.of_forall hg_nonneg)]
  apply lintegral_congr
  intro s
  exact (ofReal_integral_eq_lintegral_ofReal (hloss_int s)
    (Filter.Eventually.of_forall fun t => sq_nonneg _)).symm

end CausalSmith.Stat.MarRareqLogfrontier

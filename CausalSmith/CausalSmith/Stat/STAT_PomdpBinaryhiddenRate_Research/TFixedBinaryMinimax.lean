module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.ModelRegularity
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.TestingFamily
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.TStableGridUpper
public import Causalean.Stat.Minimax.Pinsker
public import Causalean.Stat.Minimax.LeCam
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Fixed-binary POMDP minimax rate

The seven-moment upper bound and positive four-state testing pair give a
uniform parametric minimax rate. The cited cardinality-uniform comparator is
an explicit input only to the contrast with growing hidden cardinality.
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

-- @node: sqRisk_ge_error_probability
/-- A squared risk dominates the squared threshold times its error probability. [Under the listed formal conditions](hyp:hest,hs,hint), [the stated conclusion holds](goal).-/
lemma sqRisk_ge_error_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (est : Ω → ℝ) (hest : Measurable est) (theta s : ℝ) (hs : 0 ≤ s)
    (hint : MeasureTheory.Integrable (fun ω => (est ω - theta) ^ 2) P) :
    s ^ 2 * P.real {ω | s ≤ |est ω - theta|} ≤
      Causalean.Stat.sqRisk P est theta := by
  let A : Set Ω := {ω | s ≤ |est ω - theta|}
  have hpoint (ω : Ω) : (s ^ 2 * Set.indicator A (fun _ : Ω => (1 : ℝ)) ω) ≤
      (est ω - theta) ^ 2 := by
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω, mul_one]
      have ha : s ≤ |est ω - theta| := hω
      nlinarith [sq_nonneg (est ω - theta), sq_nonneg (|est ω - theta|),
        abs_nonneg (est ω - theta), sq_abs (est ω - theta)]
    · simp [Set.indicator, hω]
      positivity
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_of_all P (fun ω => mul_nonneg (sq_nonneg s)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) ω))) hint
    (MeasureTheory.ae_of_all P hpoint)
  have hA : MeasurableSet A := by
    change MeasurableSet ((fun ω => |est ω - theta|) ⁻¹' Set.Ici s)
    have hm : Measurable (fun ω => |est ω - theta|) := by fun_prop
    exact hm measurableSet_Ici
  have hind : (∫ ω, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P) = P.real A := by
    exact MeasureTheory.integral_indicator_one hA
  calc
    s ^ 2 * P.real {ω | s ≤ |est ω - theta|} =
        ∫ ω, s ^ 2 * A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P := by
      rw [MeasureTheory.integral_const_mul, hind]
    _ ≤ Causalean.Stat.sqRisk P est theta := hmono

-- @node: bounded_estimator_sqError_integrable
/-- A measurable estimator taking values in the unit interval has integrable square loss. [Under the listed formal conditions](hyp:hest,hbound), [the stated conclusion holds](goal).-/
lemma bounded_estimator_sqError_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (est : Ω → ℝ) (hest : Measurable est)
    (hbound : ∀ ω, est ω ∈ Set.Icc (0 : ℝ) 1) (theta : ℝ) :
    MeasureTheory.Integrable (fun ω => (est ω - theta) ^ 2) P := by
  apply MeasureTheory.Integrable.of_bound (by fun_prop) ((1 + |theta|) ^ 2)
  filter_upwards [] with ω
  have hb := hbound ω
  have heAbs : |est ω| ≤ 1 := abs_le.mpr ⟨by linarith [hb.1], hb.2⟩
  have hd : |est ω - theta| ≤ 1 + |theta| := by
    calc
      |est ω - theta| ≤ |est ω| + |theta| := abs_sub _ _
      _ ≤ 1 + |theta| := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hmul := mul_nonneg (sub_nonneg.mpr hd)
    (add_nonneg (by positivity : 0 ≤ 1 + |theta|) (abs_nonneg (est ω - theta)))
  nlinarith [sq_abs (est ω - theta)]

-- @node: testingPair_observedRisk_lower
/-- The finite-KL testing pair forces a squared-risk lower bound for each observable estimator. [Under the listed formal conditions](hyp:hT,hb,he,hsep,hfin,hkl), [the stated conclusion holds](goal).-/
lemma testingPair_observedRisk_lower (T : Nat) (hT : 12 ≤ T)
    (Mp Mm : RawPomdpExperiment T 2 2)
    (hb : Mp.b = Mm.b) (he : Mp.e = Mm.e)
    (hsep : |targetValue Mp - targetValue Mm| = 1 / (8 * Real.sqrt T))
    (hfin : InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm) ≠ ⊤)
    (hkl : (InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm)).toReal ≤ 1 / 12)
    (est : ObservableEstimator T) :
    1 / (1024 * (T : ℝ)) ≤
      max (Causalean.Stat.sqRisk (obsLaw Mp) (est.1 Mp.b Mp.e) (targetValue Mp))
        (Causalean.Stat.sqRisk (obsLaw Mm) (est.1 Mm.b Mm.e) (targetValue Mm)) := by
  let f := est.1 Mp.b Mp.e
  have hf : Measurable f := est.2.2 Mp.b Mp.e
  have hfBound : ∀ w, f w ∈ Set.Icc (0 : ℝ) 1 := est.2.1 Mp.b Mp.e
  have hfo : est.1 Mm.b Mm.e = f := by simp only [← hb, ← he, f]
  letI : MeasureTheory.IsProbabilityMeasure (obsLaw Mp) := by
    unfold obsLaw
    exact MeasureTheory.Measure.isProbabilityMeasure_map (by
      unfold obsProj curState actionAt rewardAt
      fun_prop)
  letI : MeasureTheory.IsProbabilityMeasure (obsLaw Mm) := by
    unfold obsLaw
    exact MeasureTheory.Measure.isProbabilityMeasure_map (by
      unfold obsProj curState actionAt rewardAt
      fun_prop)
  have htv0 : Causalean.Stat.tvDist (obsLaw Mp) (obsLaw Mm) ≤
      Real.sqrt ((InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm)).toReal / 2) :=
    Causalean.Stat.pinskerBound_of_ac_of_ne_top _ _
      (InformationTheory.klDiv_ne_top_iff.mp hfin).1 hfin
  have htv : Causalean.Stat.tvDist (obsLaw Mp) (obsLaw Mm) ≤ 1 / 4 := by
    have hk0 : 0 ≤ (InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm)).toReal :=
      ENNReal.toReal_nonneg
    have hsq := Real.sq_sqrt (by positivity :
      0 ≤ (InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm)).toReal / 2)
    have hroot := Real.sqrt_nonneg
      ((InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm)).toReal / 2)
    nlinarith
  let s : ℝ := 1 / (16 * Real.sqrt T)
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.2
    (by exact_mod_cast (by omega : 0 < T))
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsep' : 2 * s ≤ |targetValue Mp - targetValue Mm| := by
    rw [hsep]
    dsimp [s]
    ring_nf
    exact le_refl _
  have herr := Causalean.Stat.two_point_lower_bound_of_tvDist_le
    (P₀ := obsLaw Mp) (P₁ := obsLaw Mm) (est := f) hf hsep' htv
  have hrp := sqRisk_ge_error_probability (obsLaw Mp) f hf
    (targetValue Mp) s hs
    (bounded_estimator_sqError_integrable (obsLaw Mp) f hf hfBound _)
  have hrm := sqRisk_ge_error_probability (obsLaw Mm) f hf
    (targetValue Mm) s hs
    (bounded_estimator_sqError_integrable (obsLaw Mm) f hf hfBound _)
  have htwo : s ^ 2 * ((1 - 1 / 4 : ℝ) / 2) ≤
      max (Causalean.Stat.sqRisk (obsLaw Mp) f (targetValue Mp))
        (Causalean.Stat.sqRisk (obsLaw Mm) f (targetValue Mm)) := by
    rcases le_total
        ((obsLaw Mp).real {ω | s ≤ |f ω - targetValue Mp|})
        ((obsLaw Mm).real {ω | s ≤ |f ω - targetValue Mm|}) with hle | hle
    · rw [max_eq_right hle] at herr
      have h := (mul_le_mul_of_nonneg_left herr (sq_nonneg s)).trans hrm
      exact h.trans (le_max_right _ _)
    · rw [max_eq_left hle] at herr
      have h := (mul_le_mul_of_nonneg_left herr (sq_nonneg s)).trans hrp
      exact h.trans (le_max_left _ _)
  rw [hfo]
  have hsqrt_sq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt
    (by exact_mod_cast (by omega : 0 ≤ T))
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hnum : 1 / (1024 * (T : ℝ)) ≤ s ^ 2 * ((1 - 1 / 4 : ℝ) / 2) := by
    dsimp [s]
    field_simp
    nlinarith [hsqrt_sq]
  exact hnum.trans htwo

-- @node: observedRisk_unit_bounds
/-- Every admissible observable estimator has squared risk between zero and one. [the stated conclusion holds](goal).-/
lemma observedRisk_unit_bounds {T : Nat} {t0 zeta : ℝ}
    (est : ObservableEstimator T) (m : ModelIndex T t0 zeta) :
    0 ≤ observedRisk est m ∧ observedRisk est m ≤ 1 := by
  let M := m.raw
  let f := est.1 M.b M.e
  have hf : Measurable f := est.2.2 M.b M.e
  have hfB : ∀ w, f w ∈ Set.Icc (0 : ℝ) 1 := est.2.1 M.b M.e
  have htheta : targetValue M ∈ Set.Icc (0 : ℝ) 1 :=
    targetValue_mem_unitInterval M m.mem.pomdp_kernel
      (targetStationary_of_class M m.mem) m.mem.policy_overlap.1
  letI : MeasureTheory.IsProbabilityMeasure (obsLaw M) := by
    unfold obsLaw
    exact MeasureTheory.Measure.isProbabilityMeasure_map (by
      unfold obsProj curState actionAt rewardAt
      fun_prop)
  have hInt := bounded_estimator_sqError_integrable (obsLaw M) f hf hfB (targetValue M)
  have hpoint (w : ObsView T 2) : (f w - targetValue M) ^ 2 ≤ 1 := by
    have hb := hfB w
    have hd : |f w - targetValue M| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hb.1, hb.2, htheta.1, htheta.2],
        by linarith [hb.1, hb.2, htheta.1, htheta.2]⟩
    nlinarith [sq_abs (f w - targetValue M), abs_nonneg (f w - targetValue M)]
  constructor
  · exact MeasureTheory.integral_nonneg (fun w => sq_nonneg _)
  · have h := MeasureTheory.integral_mono hInt
      (MeasureTheory.integrable_const (μ := obsLaw M) (1 : ℝ)) hpoint
    simpa only [observedRisk, Causalean.Stat.sqRisk,
      MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul] using h

-- @node: comparator_reset_depth_growth
/-- For [positive mixing time](hyp:ht0), [positive overlap exponent](hyp:hzeta),
a [fixed overlap constant](hyp:hC), and the [cited comparator](hyp:hComparator),
the reset construction has logarithmic depth and eventually needs
[more than two hidden states](goal). -/
lemma comparator_reset_depth_growth (t0 zeta C : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C)
    (hComparator : CardinalityUniformComparator t0 zeta ⟨C, hC⟩) :
    ∃ cReset : ℝ, ∃ Q : Nat → Nat,
      0 < cReset ∧
      (∃ a1 a2 : ℝ, 0 < a1 ∧ 0 < a2 ∧
        ∀ᶠ n : Nat in Filter.atTop,
          a1 * Real.log n ≤ Q n ∧ Q n ≤ a2 * Real.log n) ∧
      ComparatorResetLowerWitness t0 zeta C cReset Q ht0 hzeta hC ∧
      (∀ᶠ n : Nat in Filter.atTop,
        ∃ (hT : 1 ≤ n) (hQ : 1 ≤ Q n),
          let M0 := CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthModel
            n (Q n) t0 zeta C false hT ht0 hzeta hC hQ
          M0.nH = 2 * (Q n + 1) ∧ 2 < M0.nH) := by
  obtain ⟨_, _, cReset, _, _, hcReset, _, Q, hlog, hreset⟩ :=
    hComparator ht0 hzeta
  refine ⟨cReset, Q, hcReset, hlog, hreset, ?_⟩
  filter_upwards [hreset] with n hn
  obtain ⟨hT, hQ, hn0, _, _⟩ := hn
  refine ⟨hT, hQ, hn0, ?_⟩
  rw [hn0]
  omega

-- @node: thm:fixed-binary-minimax
/-- For [positive mixing time](hyp:ht0), [nonnegative overlap exponent](hyp:hzeta),
the [stated horizon range](hyp:hT), and the [cited comparator](hyp:hComparator_of_gate),
the [exact fixed-binary minimax rate, transferable testing pair, and asymptotic
separation](goal) hold. -/
theorem fixedBinary_minimax (T : Nat) (t0 zeta C : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 ≤ zeta) (hT : 12 ≤ T)
    (hComparator_of_gate : ∀ hC : 1 < C,
      CardinalityUniformComparator t0 zeta ⟨C, hC⟩) :
    (1 / (1024 * (T : ℝ)) ≤ minimaxRisk T t0 zeta ∧
      minimaxRisk T t0 zeta ≤
        (stabilityFactor (mixingAlpha t0) ^ 2 *
          (112 * varianceFactor (mixingAlpha t0) (policyFactor zeta) + 2)) / T) ∧
    (let Mp := testingExperiment T (vT T) (Or.inl rfl) (vT_bound T hT)
     let Mm := testingExperiment T (-(vT T)) (Or.inr rfl) (neg_vT_bound T hT)
     BinaryPomdpClass t0 zeta Mp ∧ BinaryPomdpClass t0 zeta Mm ∧
     Mp.e = Mp.b ∧ Mm.e = Mm.b ∧
     stationaryLaw (policyKernel Mp Mp.e) = stationaryLaw (policyKernel Mp Mp.b) ∧
     stationaryLaw (policyKernel Mm Mm.e) = stationaryLaw (policyKernel Mm Mm.b) ∧
     (∀ C0 : ℝ, 1 < C0 → ∀ s,
       stationaryLaw (policyKernel Mp Mp.e) s ≤
         C0 * stationaryLaw (policyKernel Mp Mp.b) s ∧
       stationaryLaw (policyKernel Mm Mm.e) s ≤
         C0 * stationaryLaw (policyKernel Mm Mm.b) s) ∧
     ∀ (hMp : BinaryPomdpClass t0 zeta Mp)
       (hMm : BinaryPomdpClass t0 zeta Mm) (est : ObservableEstimator T),
       1 / (1024 * (T : ℝ)) ≤
         max (observedRisk est ⟨Mp, hMp⟩)
           (observedRisk est ⟨Mm, hMm⟩)) ∧
    (∀ (hz : 0 < zeta) (hC : 1 < C),
      0 < rateExponent t0 zeta ∧ rateExponent t0 zeta < 1 ∧
      Filter.Tendsto
        (fun n : Nat ↦
          (n : ℝ)⁻¹ /
            ((n : ℝ) ^ (-(rateExponent t0 zeta)) *
              overlapRadius C ^ (2 * (1 - rateExponent t0 zeta))))
        Filter.atTop (nhds 0) ∧
      ∃ cReset : ℝ, ∃ Q : Nat → Nat,
        0 < cReset ∧
        (∃ a1 a2 : ℝ, 0 < a1 ∧ 0 < a2 ∧
          ∀ᶠ n : Nat in Filter.atTop,
            a1 * Real.log n ≤ Q n ∧ Q n ≤ a2 * Real.log n) ∧
        ComparatorResetLowerWitness t0 zeta C cReset Q ht0 hz hC ∧
        (∀ᶠ n : Nat in Filter.atTop,
          ∃ (hn : 1 ≤ n) (hQ : 1 ≤ Q n),
            let M0 := CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthModel
              n (Q n) t0 zeta C false hn ht0 hz hC hQ
            M0.nH = 2 * (Q n + 1) ∧ 2 < M0.nH)) := by
  have hpair := testingFamily_membership T t0 zeta ht0 hzeta hT
  rcases hpair with ⟨hMp, hMm, hsep, hfin, hkl, heqp, heqm, hdp, hdm, hoccup⟩
  have htesting (est : ObservableEstimator T) :
      1 / (1024 * (T : ℝ)) ≤
        max (observedRisk est
          ⟨testingExperiment T (vT T) (Or.inl rfl) (vT_bound T hT), hMp⟩)
          (observedRisk est
            ⟨testingExperiment T (-(vT T)) (Or.inr rfl) (neg_vT_bound T hT), hMm⟩) := by
    simpa only [observedRisk] using testingPair_observedRisk_lower T hT
      (testingExperiment T (vT T) (Or.inl rfl) (vT_bound T hT))
      (testingExperiment T (-(vT T)) (Or.inr rfl) (neg_vT_bound T hT))
      rfl rfl hsep hfin hkl est
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · let mp : ModelIndex T t0 zeta :=
        ⟨testingExperiment T (vT T) (Or.inl rfl) (vT_bound T hT), hMp⟩
      let mm : ModelIndex T t0 zeta :=
        ⟨testingExperiment T (-(vT T)) (Or.inr rfl) (neg_vT_bound T hT), hMm⟩
      letI : Nonempty (ObservableEstimator T) := ⟨⟨(fun _ _ _ => 0), by
        constructor
        · intro b e w
          exact ⟨le_refl 0, zero_le_one⟩
        · intro b e
          exact measurable_const⟩⟩
      have hbdd (est : ObservableEstimator T) :
          BddAbove (Set.range (observedRisk est (t0 := t0) (zeta := zeta))) := by
        refine ⟨1, ?_⟩
        rintro x ⟨m, rfl⟩
        exact (observedRisk_unit_bounds est m).2
      have hlower := Causalean.Stat.le_minimaxValue_of_two_point mp mm hbdd htesting
      simpa only [minimaxRisk] using hlower
    · let est : ObservableEstimator T :=
        ⟨fun b e w => stableGridEstimator T t0 b e w,
          stableGridEstimator_admissible T t0 ht0 hT⟩
      have hnonneg (e : ObservableEstimator T) (m : ModelIndex T t0 zeta) :
          0 ≤ observedRisk e m := (observedRisk_unit_bounds e m).1
      have hbound (m : ModelIndex T t0 zeta) :
          observedRisk est m ≤
            (stabilityFactor (mixingAlpha t0) ^ 2 *
              (112 * varianceFactor (mixingAlpha t0) (policyFactor zeta) + 2)) / T := by
        exact stableGrid_upper T t0 zeta ht0 hzeta hT m
      letI : Nonempty (ModelIndex T t0 zeta) :=
        ⟨⟨testingExperiment T (vT T) (Or.inl rfl) (vT_bound T hT), hMp⟩⟩
      calc
        minimaxRisk T t0 zeta ≤
            Causalean.Stat.worstCaseRiskReal observedRisk est := by
          exact Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg hnonneg est
        _ ≤ _ := Causalean.Stat.worstCaseRisk_le hbound
  · exact ⟨hMp, hMm, heqp, heqm, hdp, hdm, hoccup,
      fun _ _ est => htesting est⟩
  · intro hz hC
    have hdepth := comparator_reset_depth_growth t0 zeta C ht0 hz hC
      (hComparator_of_gate hC)
    refine ⟨?_, ?_, ?_, hdepth⟩
    · unfold rateExponent
      positivity
    · unfold rateExponent
      have hprod : 0 < t0 * zeta := mul_pos ht0 hz
      apply (div_lt_iff₀ (by linarith : 0 < 2 + t0 * zeta)).mpr
      nlinarith
    · have hbeta : 0 < 1 - rateExponent t0 zeta := by
        have hprod : 0 < t0 * zeta := mul_pos ht0 hz
        unfold rateExponent
        have hden : 0 < 2 + t0 * zeta := by linarith
        have hlt : 2 / (2 + t0 * zeta) < 1 := by
          apply (div_lt_iff₀ hden).mpr
          linarith
        linarith
      have hq : 0 < overlapRadius C := by
        unfold overlapRadius
        exact div_pos (by linarith) (by linarith)
      have hqpow : 0 < overlapRadius C ^ (2 * (1 - rateExponent t0 zeta)) :=
        Real.rpow_pos_of_pos hq _
      have ht : Filter.Tendsto
          (fun n : Nat => (n : ℝ) ^ (-(1 - rateExponent t0 zeta)))
          Filter.atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop hbeta).comp tendsto_natCast_atTop_atTop
      have hlim := ht.mul_const
        ((overlapRadius C ^ (2 * (1 - rateExponent t0 zeta)))⁻¹)
      simpa only [zero_mul] using hlim.congr' (by
        filter_upwards [Filter.eventually_gt_atTop (0 : Nat)] with n hn
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn'
        have hp : (n : ℝ) ^ rateExponent t0 zeta ≠ 0 :=
          ne_of_gt (Real.rpow_pos_of_pos hn' _)
        have hr : (n : ℝ)⁻¹ / (n : ℝ) ^ (-rateExponent t0 zeta) =
            (n : ℝ) ^ (-(1 - rateExponent t0 zeta)) := by
          rw [show -(1 - rateExponent t0 zeta) =
            rateExponent t0 zeta - 1 by ring,
            Real.rpow_sub hn', Real.rpow_one,
            Real.rpow_neg (le_of_lt hn')]
          field_simp
        rw [← hr]
        field_simp [ne_of_gt hqpow])
  -- @realizes \(C\)(comparator overlap bound) @realizes \(Q\)(growing reset depth)

end CausalSmith.Stat.PomdpBinaryhiddenRate

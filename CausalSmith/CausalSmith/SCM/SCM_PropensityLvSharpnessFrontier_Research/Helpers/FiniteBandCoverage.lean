import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Statements
import Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw.TailLift

/-! # Finite-sample endpoint-band coverage helpers -/


namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

open Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw

universe u

/-- For the specified model objects, [the stated conditions](hyp:hAlpha,hm), [the stated mathematical relationship holds](goal). -/
-- @node: dkwGate_fixedCDFBadSet
lemma dkwGate_fixedCDFBadSet (dkw : DkwMassartCdfBand)
    (P : Measure ℝ) [IsProbabilityMeasure P] (alpha : ℝ)
    (hAlpha : MiscoverageLevel alpha) (m : ℕ) (hm : 0 < m) :
    (Measure.pi (fun _ : Fin m => P)) (fixedCDFBadSet P (dkwRadius alpha m)) ≤
      ENNReal.ofReal (alpha / 2) := by
  let X : Fin m → (Fin m → ℝ) → ℝ := fun i x => x i
  have hmeas : ∀ i, Measurable (X i) := fun i => measurable_pi_apply i
  have hind : iIndepFun X (Measure.pi fun _ : Fin m => P) := by
    exact ProbabilityTheory.iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hlaw : ∀ i y, (Measure.pi fun _ : Fin m => P) {x | X i x ≤ y} = P (Set.Iic y) := by
    intro i y
    have hmp := MeasureTheory.measurePreserving_eval (fun _ : Fin m => P) i
    calc
      (Measure.pi fun _ : Fin m => P) {x | X i x ≤ y} =
          (Measure.pi fun _ : Fin m => P).map (X i) (Set.Iic y) := by
            rw [Measure.map_apply (hmeas i) measurableSet_Iic]
            congr 1
      _ = P (Set.Iic y) := by rw [hmp.map_eq]
  have ht : 0 < dkwRadius alpha m := by
    unfold dkwRadius
    have ha0 := hAlpha.1
    have ha1 := hAlpha.2
    have hratio : 1 < 4 / alpha := (lt_div_iff₀ ha0).2 (by linarith)
    exact Real.sqrt_pos.2 (div_pos (Real.log_pos hratio) (by positivity))
  have htail := dkw m (Nat.succ_le_iff.mpr hm) (Fin m → ℝ) inferInstance
    (Measure.pi fun _ : Fin m => P) inferInstance X P inferInstance hmeas hind
    (fun i y => hlaw i y) (dkwRadius alpha m) ht
  have hset : fixedCDFBadSet P (dkwRadius alpha m) =
      {omega | sSup {r : ℝ | ∃ y : ℝ,
        r = |∑ i, (if X i omega ≤ y then (1 : ℝ) else 0) / (m : ℝ) -
          (P (Set.Iic y)).toReal|} > dkwRadius alpha m} := by
    ext x
    simp only [fixedCDFBadSet, uniformCDFDeviation, Set.mem_setOf_eq]
    have heq (y : ℝ) : empiricalCDFVec x y - cdf P y =
        ∑ i, (if X i x ≤ y then (1 : ℝ) else 0) / (m : ℝ) -
          (P (Set.Iic y)).toReal := by
      rw [ProbabilityTheory.cdf_eq_real]
      simp only [empiricalCDFVec, X, Causalean.Stat.cdfStat, Measure.real]
      have hindEq : (∑ i, (Set.Iic y).indicator (fun _ => (1 : ℝ)) (x i)) =
          ∑ i, if x i ≤ y then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        simp [Set.indicator]
      rw [hindEq, ← Finset.sum_div, div_eq_mul_inv]
      ring
    have hrange : (Set.range fun y : ℝ => |empiricalCDFVec x y - cdf P y|) =
        {r : ℝ | ∃ y : ℝ, r = |∑ i, (if X i x ≤ y then (1 : ℝ) else 0) /
          (m : ℝ) - (P (Set.Iic y)).toReal|} := by
      ext r
      simp only [Set.mem_range, Set.mem_setOf_eq]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y, by rw [heq]⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, by rw [heq]⟩
    rw [hrange]
  rw [hset]
  refine htail.trans_eq ?_
  congr 1
  have ha0 := hAlpha.1
  have hratio0 : 0 < 4 / alpha := div_pos (by norm_num) ha0
  have hratio1 : 1 < 4 / alpha := (lt_div_iff₀ ha0).2 (by linarith [hAlpha.2])
  have hq : 0 ≤ Real.log (4 / alpha) / (2 * (m : ℝ)) :=
    (div_pos (Real.log_pos hratio1) (by positivity)).le
  rw [dkwRadius, Real.sq_sqrt hq]
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
  rw [show -2 * (m : ℝ) * (Real.log (4 / alpha) / (2 * (m : ℝ))) =
      -Real.log (4 / alpha) by field_simp]
  rw [Real.exp_neg, Real.exp_log hratio0]
  field_simp
  ring

/-- For the specified model objects, [the stated conditions](hyp:hn,hIID,hFactor,hoeffding,hPos,hAlpha), [the stated mathematical relationship holds](goal). -/
-- @node: hoeffdingGate_empiricalArmPropensity
lemma hoeffdingGate_empiricalArmPropensity
    {Omega : Type u} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] (n : ℕ) (hn : 0 < n) (a : Bool) (alpha e : ℝ)
    (nu : Measure (Bool × ℝ)) (P : Measure ℝ) [IsProbabilityMeasure P]
    (Z : ℕ → Omega → Bool × ℝ)
    (hIID : IidObservationalSampling n Z mu nu)
    (hFactor : ∀ B : Set ℝ, MeasurableSet B →
      nu {z | z.1 = a ∧ z.2 ∈ B} = ENNReal.ofReal e * P B)
    (hoeffding : HoeffdingBoundedMean.{u}) (hPos : StrictPositivity e)
    (hAlpha : MiscoverageLevel alpha) :
    mu {omega | |empiricalArmPropensity (fun i : Fin n => Z i omega) a - e| >
      Real.sqrt (Real.log (4 / alpha) / (2 * n))} ≤ ENNReal.ofReal (alpha / 2) := by
  let W : Fin n → Omega → ℝ := fun i omega =>
    if (Z i omega).1 = a then 1 else 0
  have hWmeas : ∀ i, Measurable (W i) := by
    intro i
    dsimp [W]
    apply Measurable.ite
    · exact (measurableSet_singleton a).preimage (hIID.2.2.1 i).fst
    · exact measurable_const
    · exact measurable_const
  have hWind : iIndepFun W mu := by
    apply hIID.2.2.2.1.comp (fun _ z => if z.1 = a then (1 : ℝ) else 0)
    intro i
    apply Measurable.ite
    · exact (measurableSet_singleton a).preimage measurable_fst
    · exact measurable_const
    · exact measurable_const
  have hWbound : ∀ i, ∀ᵐ omega ∂mu, 0 ≤ W i omega ∧ W i omega ≤ 1 := by
    intro i
    filter_upwards with omega
    dsimp [W]
    split_ifs <;> norm_num
  have hWmean (i : Fin n) : ∫ omega, W i omega ∂mu = e := by
    let E : Set Omega := {omega | (Z i omega).1 = a}
    have hE : MeasurableSet E :=
      (measurableSet_singleton a).preimage (hIID.2.2.1 i).fst
    have hWE : W i = E.indicator (1 : Omega → ℝ) := by
      funext omega
      simp [W, E, Set.indicator]
    rw [hWE]
    have hint : ∫ omega, E.indicator (1 : Omega → ℝ) omega ∂mu = mu.real E :=
      MeasureTheory.integral_indicator_one hE
    rw [hint]
    have hmap : mu E = nu {z | z.1 = a} := by
      calc
        mu E = mu ((Z i) ⁻¹' {z | z.1 = a}) := by
          congr 1
        _ = mu.map (Z i) {z | z.1 = a} := by
          exact (Measure.map_apply (hIID.2.2.1 i)
            ((measurableSet_singleton a).preimage measurable_fst)).symm
        _ = nu {z | z.1 = a} := by rw [hIID.2.2.2.2 i]
    rw [Measure.real, hmap]
    have hfac := hFactor Set.univ MeasurableSet.univ
    simp only [Set.mem_univ, and_true, measure_univ, mul_one] at hfac
    rw [hfac, ENNReal.toReal_ofReal hPos.1.le]
  have ht : 0 < Real.sqrt (Real.log (4 / alpha) / (2 * (n : ℝ))) := by
    have hratio : 1 < 4 / alpha := (lt_div_iff₀ hAlpha.1).2 (by linarith [hAlpha.2])
    exact Real.sqrt_pos.2 (div_pos (Real.log_pos hratio) (by positivity))
  have htail := hoeffding n (Nat.succ_le_iff.mpr hn) Omega inferInstance mu inferInstance
    W hWmeas hWind hWbound _ ht
  have hmean : ∑ i, (∫ omega, W i omega ∂mu) / (n : ℝ) = e := by
    simp_rw [hWmean]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
    field_simp
  have hsample (omega : Omega) : ∑ i, W i omega / (n : ℝ) =
      empiricalArmPropensity (fun i : Fin n => Z i omega) a := by
    simp only [W, empiricalArmPropensity, armCount]
    rw [← Finset.sum_div]
    congr 1
    norm_cast
  simpa only [hsample, hmean] using htail.trans_eq (by
    congr 1
    have hratio0 : 0 < 4 / alpha := div_pos (by norm_num) hAlpha.1
    have hratio1 : 1 < 4 / alpha := (lt_div_iff₀ hAlpha.1).2 (by linarith [hAlpha.2])
    have hq : 0 ≤ Real.log (4 / alpha) / (2 * (n : ℝ)) :=
      (div_pos (Real.log_pos hratio1) (by positivity)).le
    rw [Real.sq_sqrt hq]
    rw [show -2 * (n : ℝ) * (Real.log (4 / alpha) / (2 * (n : ℝ))) =
        -Real.log (4 / alpha) by field_simp]
    rw [Real.exp_neg, Real.exp_log hratio0]
    field_simp
    ring)

/-- For the specified model objects, [the stated conditions](hyp:hcount), [the stated mathematical relationship holds](goal). -/
-- @node: selectedEmpiricalCDF_mem_Icc
lemma selectedEmpiricalCDF_mem_Icc {Omega : Type*} {n : ℕ}
    (Z : Fin n → Omega → Bool × ℝ) (a : Bool) (omega : Omega)
    (hcount : 0 < selectedCount Z a omega) (y : ℝ) :
    selectedEmpiricalCDF Z a omega y ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  let s := Finset.univ.filter (fun i => (Z i omega).1 = a)
  have hs : s.card = selectedCount Z a omega := by rfl
  have hscard : 0 < s.card := hs.symm ▸ hcount
  have hsum0 : 0 ≤ ∑ i ∈ s, Causalean.Stat.cdfStat y (Z i omega).2 :=
    Finset.sum_nonneg fun i _ => Causalean.Stat.cdfStat_nonneg y _
  have hsum1 : ∑ i ∈ s, Causalean.Stat.cdfStat y (Z i omega).2 ≤ (s.card : ℝ) := by
    simpa using Finset.sum_le_card_nsmul s
      (fun i => Causalean.Stat.cdfStat y (Z i omega).2) (1 : ℝ)
      (fun i _ => Causalean.Stat.cdfStat_le_one y _)
  rw [selectedEmpiricalCDF]
  change (s.card : ℝ)⁻¹ * (∑ i ∈ s, Causalean.Stat.cdfStat y (Z i omega).2) ∈
    Set.Icc 0 1
  constructor
  · positivity
  · rw [inv_mul_le_one₀ (Nat.cast_pos.mpr hscard)]
    exact hsum1

/-- For the specified model objects, [the stated mathematical relationship holds](goal). -/
-- @node: armCount_eq_selectedCount
lemma armCount_eq_selectedCount {n : ℕ} (S : ObservedSample n) (a : Bool) :
    armCount S a = selectedCount (fun i (T : ObservedSample n) => T i) a S := by
  classical
  unfold armCount selectedCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- For the specified model objects, [the stated mathematical relationship holds](goal). -/
-- @node: armCount_sample_eq_selectedCount
lemma armCount_sample_eq_selectedCount {Omega : Type*} {n : ℕ}
    (Z : Fin n → Omega → Bool × ℝ) (a : Bool) (omega : Omega) :
    armCount (fun i => Z i omega) a = selectedCount Z a omega := by
  classical
  unfold armCount selectedCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- For the specified model objects, [the stated conditions](hyp:hcount), [the stated mathematical relationship holds](goal). -/
-- @node: empiricalArmCDF_eq_selectedEmpiricalCDF
lemma empiricalArmCDF_eq_selectedEmpiricalCDF {n : ℕ}
    (S : ObservedSample n) (a : Bool) (y : ℝ) (hcount : armCount S a ≠ 0) :
    empiricalArmCDF S a y =
      selectedEmpiricalCDF (fun i (T : ObservedSample n) => T i) a S y := by
  classical
  simp only [empiricalArmCDF, hcount, if_false, selectedEmpiricalCDF,
    ← armCount_eq_selectedCount]
  rw [div_eq_inv_mul]
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Causalean.Stat.cdfStat, Set.indicator]
  by_cases ha : (S i).1 = a <;> by_cases hy : (S i).2 ≤ y <;> simp [ha, hy]

/-- For the specified model objects, [the stated conditions](hyp:hcount), [the stated mathematical relationship holds](goal). -/
-- @node: empiricalArmCDF_sample_eq_selectedEmpiricalCDF
lemma empiricalArmCDF_sample_eq_selectedEmpiricalCDF {Omega : Type*} {n : ℕ}
    (Z : Fin n → Omega → Bool × ℝ) (a : Bool) (omega : Omega) (y : ℝ)
    (hcount : armCount (fun i => Z i omega) a ≠ 0) :
    empiricalArmCDF (fun i => Z i omega) a y = selectedEmpiricalCDF Z a omega y := by
  classical
  simp only [empiricalArmCDF, hcount, if_false, selectedEmpiricalCDF,
    ← armCount_sample_eq_selectedCount]
  rw [div_eq_inv_mul]
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Causalean.Stat.cdfStat, Set.indicator]
  by_cases ha : (Z i omega).1 = a <;> by_cases hy : (Z i omega).2 ≤ y <;> simp [ha, hy]

/-- For the specified model objects, [the stated conditions](hyp:hgood,hcount), [the stated mathematical relationship holds](goal). -/
-- @node: selectedCDF_good_pointwise
lemma selectedCDF_good_pointwise {Omega : Type*} {n : ℕ}
    (Z : Fin n → Omega → Bool × ℝ) (a : Bool) (omega : Omega)
    (P : Measure ℝ) [IsProbabilityMeasure P] (alpha : ℝ)
    (hgood : omega ∉ selectedCDFBadEvent Z a P (dkwRadius alpha))
    (hcount : 0 < selectedCount Z a omega) (y : ℝ) :
    |selectedEmpiricalCDF Z a omega y - cdf P y| ≤
      dkwRadius alpha (selectedCount Z a omega) := by
  have hsup : sSup (Set.range fun y : ℝ =>
      |selectedEmpiricalCDF Z a omega y - cdf P y|) ≤
      dkwRadius alpha (selectedCount Z a omega) := by
    exact le_of_not_gt fun h => hgood ⟨hcount, h⟩
  have hbdd : BddAbove (Set.range fun y : ℝ =>
      |selectedEmpiricalCDF Z a omega y - cdf P y|) := by
    refine ⟨1, ?_⟩
    rintro x ⟨t, rfl⟩
    have hecdf := selectedEmpiricalCDF_mem_Icc Z a omega hcount t
    have hpcdf : cdf P t ∈ Set.Icc (0 : ℝ) 1 := ⟨cdf_nonneg P t, cdf_le_one P t⟩
    rcases hecdf with ⟨he0, he1⟩
    rcases hpcdf with ⟨hp0, hp1⟩
    rw [abs_le]
    constructor <;> linarith
  exact (le_csSup hbdd ⟨y, rfl⟩).trans hsup

/-- For the specified model objects, [the stated conditions](hyp:hz), [the stated mathematical relationship holds](goal). -/
-- @node: cdfEndpoints_mem_rectangularHull
lemma cdfEndpoints_mem_rectangularHull
    (C : Set (Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1)) (z) (hz : z ∈ C) :
    cdfEndpoints z.1 z.2 ∈
      rectangularHull ((fun ep => cdfEndpoints ep.1 ep.2) '' C) := by
  let D := (fun ep => cdfEndpoints ep.1 ep.2) '' C
  have hzD : cdfEndpoints z.1 z.2 ∈ D := ⟨z, hz, rfl⟩
  have hfst : BddBelow (Prod.fst '' D) ∧ BddAbove (Prod.fst '' D) := by
    constructor
    · refine ⟨0, ?_⟩
      rintro x ⟨w, ⟨ep, hep, rfl⟩, rfl⟩
      simp only [cdfEndpoints]
      split_ifs
      · exact mul_nonneg ep.1.2.1 ep.2.2.1
      · norm_num
    · refine ⟨1, ?_⟩
      rintro x ⟨w, ⟨ep, hep, rfl⟩, rfl⟩
      simp only [cdfEndpoints]
      split_ifs
      · have h := mul_le_mul_of_nonneg_left ep.2.2.2 ep.1.2.1
        simpa using h.trans (by simpa using ep.1.2.2)
      · norm_num
  have hsnd : BddBelow (Prod.snd '' D) ∧ BddAbove (Prod.snd '' D) := by
    constructor
    · refine ⟨0, ?_⟩
      rintro x ⟨w, ⟨ep, hep, rfl⟩, rfl⟩
      simp only [cdfEndpoints]
      split_ifs
      · norm_num
      · nlinarith [mul_nonneg ep.1.2.1 ep.2.2.1,
          sub_nonneg.mpr ep.1.2.2]
    · refine ⟨1, ?_⟩
      rintro x ⟨w, ⟨ep, hep, rfl⟩, rfl⟩
      simp only [cdfEndpoints]
      split_ifs
      · norm_num
      · nlinarith [mul_nonneg ep.1.2.1 (sub_nonneg.mpr ep.2.2.2)]
  exact ⟨⟨csInf_le hfst.1 ⟨_, hzD, rfl⟩, le_csSup hfst.2 ⟨_, hzD, rfl⟩⟩,
    ⟨csInf_le hsnd.1 ⟨_, hzD, rfl⟩, le_csSup hsnd.2 ⟨_, hzD, rfl⟩⟩⟩

/-- For the specified model objects, [the stated mathematical relationship holds](goal). -/
-- @node: cdfEndpoints_mem_unitSquare
lemma cdfEndpoints_mem_unitSquare
    (e p : Set.Icc (0 : ℝ) 1) : cdfEndpoints e p ∈ Set.Icc 0 1 ×ˢ Set.Icc 0 1 := by
  change (if p.1 < 1 then e.1 * p.1 else 1) ∈ Set.Icc 0 1 ∧
    (if p.1 = 0 then 0 else e.1 * p.1 + 1 - e.1) ∈ Set.Icc 0 1
  constructor
  · split_ifs
    · exact ⟨mul_nonneg e.2.1 p.2.1,
        (mul_le_mul_of_nonneg_left p.2.2 e.2.1).trans (by simpa using e.2.2)⟩
    · exact ⟨zero_le_one, le_rfl⟩
  · split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · constructor
      · nlinarith [mul_nonneg e.2.1 p.2.1, sub_nonneg.mpr e.2.2]
      · nlinarith [mul_nonneg e.2.1 (sub_nonneg.mpr p.2.2)]

/-- For the specified model objects, [the stated conditions](hyp:hPos,hE,hF), [the stated mathematical relationship holds](goal). -/
-- @node: honestBand_contains_of_good_events
lemma honestBand_contains_of_good_events
    {Omega : Type*} [MeasurableSpace Omega] (n : ℕ) (a : Bool) (alpha e : ℝ)
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (Z : ℕ → Omega → Bool × ℝ) (omega : Omega)
    (hPos : StrictPositivity e)
    (hE : |empiricalArmPropensity (fun i : Fin n => Z i omega) a - e| ≤
      Real.sqrt (Real.log (4 / alpha) / (2 * n)))
    (hF : omega ∉ selectedCDFBadEvent (fun i : Fin n => Z i) a P (dkwRadius alpha)) :
    ∀ y : ℝ, cdfEndpoints (endpointPropensity e (Or.inl hPos)) (cdfProbability P y) ∈
      honestBand Z a n alpha omega y := by
  intro y
  let S : ObservedSample n := fun i => Z i omega
  rw [honestBand]
  dsimp only
  split_ifs with hzero
  · exact cdfEndpoints_mem_unitSquare _ _
  · refine cdfEndpoints_mem_rectangularHull _
      (endpointPropensity e (Or.inl hPos), cdfProbability P y) ?_
    constructor
    · change e ∈ Set.Icc
        (empiricalArmPropensity S a - Real.sqrt (Real.log (4 / alpha) / (2 * n)))
        (empiricalArmPropensity S a + Real.sqrt (Real.log (4 / alpha) / (2 * n)))
      rw [abs_le] at hE
      exact ⟨by linarith, by linarith⟩
    · change cdf P y ∈ Set.Icc
        (empiricalArmCDF S a y -
          Real.sqrt (Real.log (4 / alpha) / (2 * armCount S a)))
        (empiricalArmCDF S a y +
          Real.sqrt (Real.log (4 / alpha) / (2 * armCount S a)))
      have hcount : 0 < selectedCount (fun i : Fin n => Z i) a omega := by
        have hcEq : armCount S a = selectedCount (fun i : Fin n => Z i) a omega := by
          simpa only [S] using armCount_sample_eq_selectedCount (fun i : Fin n => Z i) a omega
        rw [← hcEq]
        exact Nat.pos_of_ne_zero hzero
      have hp := selectedCDF_good_pointwise (fun i : Fin n => Z i) a omega P alpha
        hF hcount y
      have hecdfEq : empiricalArmCDF S a y =
          selectedEmpiricalCDF (fun i : Fin n => Z i) a omega y := by
        simpa only [S] using empiricalArmCDF_sample_eq_selectedEmpiricalCDF
          (fun i : Fin n => Z i) a omega y hzero
      have hcEq : armCount S a = selectedCount (fun i : Fin n => Z i) a omega := by
        simpa only [S] using armCount_sample_eq_selectedCount (fun i : Fin n => Z i) a omega
      rw [← hecdfEq, ← hcEq] at hp
      simp only [dkwRadius] at hp
      rw [abs_le] at hp
      exact ⟨by linarith, by linarith⟩

end CausalSmith.SCM.PropensityLvSharpnessFrontier

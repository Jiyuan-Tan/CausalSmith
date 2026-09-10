import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.UpperNoise

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- Expected absolute error of a bounded empirical average over an arbitrary
nonempty deterministic block of a finite product sample. The result uses [the `hI` condition](hyp:hI), [the `hf` condition](hyp:hf), [the `hf0` condition](hyp:hf0), [the `hf1` condition](hyp:hf1), [the `hm` condition](hyp:hm). [This is the stated conclusion](goal).
-/
lemma blockAverage_l1_le {J n : ℕ} (P : ClampLaw J)
    (I : Finset (Fin n)) (hI : 0 < I.card)
    (f : ClampObs J → ℝ) (hf : Measurable f)
    (hf0 : ∀ o, 0 ≤ f o) (hf1 : ∀ o, f o ≤ 1)
    (m : ℝ) (hm : ∫ o, f o ∂P.dataMeasure = m)
    [IsProbabilityMeasure P.dataMeasure] :
    (∫ z, |blockAverage I z f - m| ∂iidProduct P n) ≤
      (1 / 2 : ℝ) * Real.sqrt (I.card : ℝ)⁻¹ := by
  letI : IsProbabilityMeasure (iidProduct P n) := by
    unfold iidProduct
    infer_instance
  letI : MeasurableSpace Unit := ⊥
  let design : ClampObs J → Unit := fun _ => ()
  let mD : Unit → ℝ := fun _ => m
  let w : (Fin n → Unit) → Fin n → ℝ := fun _ i =>
    if i ∈ I then (I.card : ℝ)⁻¹ else 0
  have hd : Measurable design := measurable_const
  have hmD : Measurable mD := measurable_const
  have hcond :
      P.dataMeasure[f | MeasurableSpace.comap design inferInstance] =ᵐ[P.dataMeasure]
        mD ∘ design := by
    have hspace : MeasurableSpace.comap design inferInstance = ⊥ := by
      ext s
      rw [MeasurableSpace.measurableSet_comap,
        MeasurableSpace.measurableSet_bot_iff]
      constructor
      · rintro ⟨t, ht, rfl⟩
        rcases MeasurableSpace.measurableSet_bot_iff.mp ht with rfl | rfl <;> simp
      · rintro (rfl | rfl)
        · exact ⟨∅, MeasurableSet.empty, by simp⟩
        · exact ⟨Set.univ, MeasurableSet.univ, by simp⟩
    rw [hspace, condExp_bot]
    filter_upwards with o
    simp [mD, hm]
  have hw : Measurable w := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i ∈ I <;> simp [w, hi]
  have henergy (z : Fin n → ClampObs J) :
      (∑ i, w (Causalean.Mathlib.Probability.designVector design z) i ^ 2) =
        (I.card : ℝ)⁻¹ := by
    classical
    simp only [w]
    have hcard : (I.card : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
    simp [hcard]
    field_simp
  have henergyInt : Integrable (fun z : Fin n → ClampObs J =>
      ∑ i, w (Causalean.Mathlib.Probability.designVector design z) i ^ 2)
      (iidProduct P n) := by
    convert integrable_const (μ := iidProduct P n) (I.card : ℝ)⁻¹ using 1
    funext z
    exact henergy z
  have hcenter (o : ClampObs J) : |f o - m| ≤ 1 := by
    have hm0 : 0 ≤ m := by rw [← hm]; exact integral_nonneg hf0
    have hm1 : m ≤ 1 := by
      have hfint : Integrable f P.dataMeasure := Integrable.of_bound hf.aestronglyMeasurable 1
        (ae_of_all _ fun o => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hf0 o)]
          exact hf1 o)
      rw [← hm]
      calc
        (∫ o, f o ∂P.dataMeasure) ≤ ∫ _o, (1 : ℝ) ∂P.dataMeasure :=
          integral_mono_ae hfint (integrable_const 1) (ae_of_all _ hf1)
        _ = 1 := by simp
    rw [abs_le]
    constructor <;> linarith [hf0 o, hf1 o]
  let S := Causalean.Mathlib.Probability.weightedCenteredSum design f mD w
  have hSmeas : Measurable S := by
    dsimp [S]
    unfold Causalean.Mathlib.Probability.weightedCenteredSum
    exact Finset.measurable_fun_sum _ fun i _ =>
      ((measurable_pi_apply i).comp
        (hw.comp (Causalean.Mathlib.Probability.measurable_designVector design hd))).mul
      ((hf.comp (measurable_pi_apply i)).sub
        (hmD.comp (hd.comp (measurable_pi_apply i))))
  have hSbound (z : Fin n → ClampObs J) : |S z| ≤ 1 := by
    dsimp [S]
    unfold Causalean.Mathlib.Probability.weightedCenteredSum
    calc
      _ ≤ ∑ i, |w (Causalean.Mathlib.Probability.designVector design z) i *
          (f (z i) - mD (design (z i)))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, if i ∈ I then (I.card : ℝ)⁻¹ else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hiI : i ∈ I
        · simp only [w, mD, hiI, if_true, abs_mul, abs_inv]
          rw [abs_of_nonneg (Nat.cast_nonneg I.card)]
          simpa using mul_le_mul_of_nonneg_left (hcenter (z i))
            (inv_nonneg.mpr (Nat.cast_nonneg I.card))
        · simp [w, hiI]
      _ = ∑ i ∈ I, (I.card : ℝ)⁻¹ := by simp
      _ = 1 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hc : (I.card : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
        field_simp
  have hSsq : Integrable (fun z => (S z) ^ 2) (iidProduct P n) := by
    refine Integrable.of_bound (hSmeas.pow_const 2).aestronglyMeasurable 1 ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [← sq_abs]
    nlinarith [hSbound z, abs_nonneg (S z)]
  have hbase := Causalean.Mathlib.Probability.product_weighted_centered_l1_le
    P.dataMeasure design hd f hf hf0 hf1 mD hmD hcond w hw henergyInt hSsq
  have hSid (z : Fin n → ClampObs J) : S z = blockAverage I z f - m := by
    unfold S Causalean.Mathlib.Probability.weightedCenteredSum blockAverage
    simp only [w, mD]
    rw [show (∑ x, (if x ∈ I then (I.card : ℝ)⁻¹ else 0) * (f (z x) - m)) =
        ∑ i ∈ I, (I.card : ℝ)⁻¹ * (f (z i) - m) by simp]
    have hsum : ∑ i ∈ I, (I.card : ℝ)⁻¹ * (f (z i) - m) =
        (I.card : ℝ)⁻¹ * ∑ i ∈ I, f (z i) - m := by
      rw [Finset.mul_sum]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      have hc : (I.card : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
      field_simp
    exact hsum
  rw [show (∫ z, |blockAverage I z f - m| ∂iidProduct P n) =
      ∫ z, |S z| ∂iidProduct P n by
        apply integral_congr_ae
        filter_upwards with z
        rw [hSid]]
  have henergyIntegral : (∫ z : Fin n → ClampObs J,
      ∑ i, w (Causalean.Mathlib.Probability.designVector design z) i ^ 2
      ∂iidProduct P n) = (I.card : ℝ)⁻¹ := by
    calc
      _ = ∫ _z : Fin n → ClampObs J, (I.card : ℝ)⁻¹ ∂iidProduct P n :=
        integral_congr_ae (ae_of_all _ henergy)
      _ = _ := by simp
  rw [show Measure.pi (fun _ : Fin n => P.dataMeasure) = iidProduct P n by rfl,
    henergyIntegral] at hbase
  simpa only [S] using hbase

/-- [retained estimate absolute-error satisfies the stated upper bound](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `delta` input](hyp:delta), [the specified `hmodel` input](hyp:hmodel), [the specified `B` input](hyp:B), [the specified `hcard` input](hyp:hcard). -/
lemma retainedEstimate_l1_le {J n : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (B : SplitBlocks n) (hcard : 0 < B.I0.card) :
    (∫ z, |retainedEstimate B z delta - retainedMean P delta| ∂iidProduct P n) ≤
      (1 / 2 : ℝ) * Real.sqrt (B.I0.card : ℝ)⁻¹ := by
  let _ := hmodel.probability
  let f : ClampObs J → ℝ := fun o => if delta < o.A then clampUnit o.Y else 0
  have hf : Measurable f := by
    have hA : Measurable (fun o : ClampObs J => o.A) :=
      measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))
    apply Measurable.ite
    · exact measurableSet_lt measurable_const hA
    · exact clampUnit_measurable'.comp clampOutcome_measurable
    · exact measurable_const
  have hf0 : ∀ o, 0 ≤ f o := by
    intro o
    dsimp [f]
    split_ifs
    · exact (clampUnit_mem_Icc o.Y).1
    · norm_num
  have hf1 : ∀ o, f o ≤ 1 := by
    intro o
    dsimp [f]
    split_ifs
    · exact (clampUnit_mem_Icc o.Y).2
    · norm_num
  have hm : ∫ o, f o ∂P.dataMeasure = retainedMean P delta := by
    calc
      _ = ∫ o, (if delta < o.A then o.Y else 0) ∂P.dataMeasure := by
        apply integral_congr_ae
        filter_upwards [hmodel.outcomeSupport] with o ho
        simp [f, clampUnit, ho.1, ho.2]
      _ = _ := by
        unfold retainedMean
        apply integral_congr_ae
        filter_upwards with o
        by_cases ha : delta < o.A <;> simp [Set.indicator, ha]
  have hb := blockAverage_l1_le P B.I0 hcard f hf hf0 hf1
    (retainedMean P delta) hm
  calc
    (∫ z, |retainedEstimate B z delta - retainedMean P delta| ∂iidProduct P n) =
        ∫ z, |blockAverage B.I0 z f - retainedMean P delta| ∂iidProduct P n := by
      apply integral_congr_ae
      filter_upwards [iidProduct_outcomeSupport P hmodel] with z hz
      congr 2
      unfold retainedEstimate blockAverage
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp [f, clampUnit, (hz i).1, (hz i).2]
    _ ≤ _ := hb

/-- [atom event integral satisfies the stated identity](goal) for [the specified `J` input](hyp:J), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `delta` input](hyp:delta), [the specified `hmodel` input](hyp:hmodel), [the specified `x` input](hyp:x), [the specified `hdelta1` input](hyp:hdelta1). -/
lemma atomEvent_integral_eq {J : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (x : Fin J) (hdelta1 : delta ≤ 1) :
    (∫ o, (if o.X = x ∧ o.A ≤ delta then (1 : ℝ) else 0) ∂P.dataMeasure) =
      P.px x * atomMass P x delta := by
  let _ := hmodel.probability
  have hX : Measurable (fun o : ClampObs J => o.X) :=
    measurable_fst.comp (Measurable.of_comap_le le_rfl)
  have hA : Measurable (fun o : ClampObs J => o.A) :=
    measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))
  have hset : MeasurableSet {o : ClampObs J |
      o.X = x ∧ o.A ∈ Set.Icc (0 : ℝ) delta} :=
    (measurableSet_eq_fun hX measurable_const).inter (measurableSet_Icc.preimage hA)
  calc
    _ = ∫ o, Set.indicator {o : ClampObs J |
        o.X = x ∧ o.A ∈ Set.Icc (0 : ℝ) delta} (fun _ => (1 : ℝ)) o
        ∂P.dataMeasure := by
      apply integral_congr_ae
      filter_upwards [hmodel.treatmentSupport] with o ho
      by_cases hx : o.X = x <;> by_cases ha : o.A ≤ delta <;>
        simp [Set.indicator, hx, ha, ho.1]
    _ = P.dataMeasure.real {o : ClampObs J |
        o.X = x ∧ o.A ∈ Set.Icc (0 : ℝ) delta} := by
      rw [integral_indicator hset]
      simp
    _ = P.px x * atomMass P x delta := by
      rw [(hmodel.condDensity.2.2 x).2 (Set.Icc 0 delta) measurableSet_Icc]
      · rfl
      · intro a ha
        exact ⟨ha.1, ha.2.trans hdelta1⟩

/-- [atom estimate absolute-error satisfies the stated upper bound](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `delta` input](hyp:delta), [the specified `hmodel` input](hyp:hmodel), [the specified `B` input](hyp:B), [the specified `hcard` input](hyp:hcard), [the specified `x` input](hyp:x), [the specified `hdelta` input](hyp:hdelta), [the specified `hdelta1` input](hyp:hdelta1). -/
lemma atomEstimate_l1_le {J n : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (B : SplitBlocks n) (hcard : 0 < B.I1.card) (x : Fin J)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (∫ z, |atomEstimate B z x delta - P.px x * atomMass P x delta|
      ∂iidProduct P n) ≤ (1 / 2 : ℝ) * Real.sqrt (B.I1.card : ℝ)⁻¹ := by
  let _ := hmodel.probability
  let f : ClampObs J → ℝ := fun o => if o.X = x ∧ o.A ≤ delta then 1 else 0
  have hX : Measurable (fun o : ClampObs J => o.X) :=
    measurable_fst.comp (Measurable.of_comap_le le_rfl)
  have hA : Measurable (fun o : ClampObs J => o.A) :=
    measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))
  have hf : Measurable f := by
    apply Measurable.ite
    · exact (measurableSet_eq_fun hX measurable_const).inter
        (measurableSet_le hA measurable_const)
    · exact measurable_const
    · exact measurable_const
  have hf0 : ∀ o, 0 ≤ f o := by intro o; dsimp [f]; split_ifs <;> norm_num
  have hf1 : ∀ o, f o ≤ 1 := by intro o; dsimp [f]; split_ifs <;> norm_num
  have hset : MeasurableSet {o : ClampObs J |
      o.X = x ∧ o.A ∈ Set.Icc (0 : ℝ) delta} :=
    (measurableSet_eq_fun hX measurable_const).inter (measurableSet_Icc.preimage hA)
  have hm : ∫ o, f o ∂P.dataMeasure = P.px x * atomMass P x delta := by
    calc
      _ = ∫ o, Set.indicator {o : ClampObs J |
          o.X = x ∧ o.A ∈ Set.Icc (0 : ℝ) delta} (fun _ => (1 : ℝ)) o
          ∂P.dataMeasure := by
        apply integral_congr_ae
        filter_upwards [hmodel.treatmentSupport] with o ho
        by_cases hx : o.X = x <;> by_cases ha : o.A ≤ delta <;>
          simp [f, Set.indicator, hx, ha, ho.1]
      _ = P.dataMeasure.real {o : ClampObs J |
          o.X = x ∧ o.A ∈ Set.Icc (0 : ℝ) delta} := by
        rw [integral_indicator hset]
        simp
      _ = P.px x * atomMass P x delta := by
        rw [(hmodel.condDensity.2.2 x).2 (Set.Icc 0 delta) measurableSet_Icc]
        · rfl
        · intro a ha
          exact ⟨ha.1, ha.2.trans hdelta1⟩
  have hb := blockAverage_l1_le P B.I1 hcard f hf hf0 hf1
    (P.px x * atomMass P x delta) hm
  simpa [atomEstimate, f] using hb

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier

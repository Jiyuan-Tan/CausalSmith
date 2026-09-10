import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.UpperEmpirical

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- [clamp functional integral satisfies the stated identity](goal) for [the specified `J` input](hyp:J), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `delta` input](hyp:delta), [the specified `hmodel` input](hyp:hmodel), [the specified `hdelta` input](hyp:hdelta), [the specified `hdelta1` input](hyp:hdelta1). -/
lemma clampFunctional_integral_eq {J : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (∫ o, if delta < o.A then o.Y else P.mu o.X delta ∂P.dataMeasure) =
      clampFunctional P delta := by
  let _ := hmodel.probability
  let atomTerm : Fin J → ClampObs J → ℝ := fun x o =>
    if o.X = x ∧ o.A ≤ delta then P.mu x delta else 0
  have hatomInt (x : Fin J) : Integrable (atomTerm x) P.dataMeasure := by
    have hX : Measurable (fun o : ClampObs J => o.X) :=
      measurable_fst.comp (Measurable.of_comap_le le_rfl)
    have hA : Measurable (fun o : ClampObs J => o.A) :=
      measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))
    have hm : Measurable (atomTerm x) := by
      dsimp [atomTerm]
      apply Measurable.ite
      · exact (measurableSet_eq_fun hX measurable_const).inter
          (measurableSet_le hA measurable_const)
      · exact measurable_const
      · exact measurable_const
    refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
    filter_upwards with o
    have hmu := (hmodel.holder x).2.1 delta
      ⟨hdelta, hdelta1⟩
    dsimp [atomTerm]
    split_ifs
    · rw [abs_of_nonneg hmu.1]
      exact hmu.2
    · simp
  have hpoint : ∀ᵐ o ∂P.dataMeasure,
      (if delta < o.A then o.Y else P.mu o.X delta) =
        o.Y * Set.indicator {o : ClampObs J | delta < o.A} (fun _ => (1 : ℝ)) o +
          ∑ x : Fin J, atomTerm x o := by
    filter_upwards [hmodel.treatmentSupport] with o ho
    by_cases ha : delta < o.A
    · have hnone (x : Fin J) : ¬(o.X = x ∧ o.A ≤ delta) := fun h => by linarith
      simp [atomTerm, Set.indicator, ha, hnone]
    · have hle : o.A ≤ delta := le_of_not_gt ha
      simp [atomTerm, Set.indicator, ha, hle]
  rw [integral_congr_ae hpoint]
  rw [integral_add]
  · rw [integral_finsetSum Finset.univ]
    · unfold clampFunctional retainedMean
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      have hevent := atomEvent_integral_eq P hmodel x hdelta1
      calc
        (∫ o, atomTerm x o ∂P.dataMeasure) =
            P.mu x delta * ∫ o,
              (if o.X = x ∧ o.A ≤ delta then (1 : ℝ) else 0) ∂P.dataMeasure := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with o
          by_cases h : o.X = x ∧ o.A ≤ delta <;> simp [atomTerm, h]
        _ = P.mu x delta * (P.px x * atomMass P x delta) := by rw [hevent]
        _ = P.px x * atomMass P x delta * P.mu x delta := by ring
    · exact fun x _ => hatomInt x
  · exact Integrable.of_bound
      ((clampOutcome_measurable.mul
        (Measurable.indicator measurable_const
          (measurableSet_lt measurable_const
            (measurable_fst.comp (measurable_snd.comp
              (Measurable.of_comap_le le_rfl))))))).aestronglyMeasurable 1
      (by filter_upwards [hmodel.outcomeSupport] with o ho
          by_cases ha : delta < o.A
          · simp [Set.indicator, ha, abs_of_nonneg ho.1, ho.2]
          · simp [Set.indicator, ha])
  · exact integrable_finsetSum Finset.univ fun x _ => hatomInt x

/-- [clamp functional lies in the stated closed interval](goal) for [the specified `J` input](hyp:J), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `delta` input](hyp:delta), [the specified `hmodel` input](hyp:hmodel), [the specified `hdelta` input](hyp:hdelta), [the specified `hdelta1` input](hyp:hdelta1). -/
lemma clampFunctional_mem_Icc {J : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    clampFunctional P delta ∈ Set.Icc (0 : ℝ) 1 := by
  let _ := hmodel.probability
  let g : ClampObs J → ℝ := fun o => if delta < o.A then o.Y else P.mu o.X delta
  have hmuMeas : Measurable (fun o : ClampObs J => P.mu o.X delta) := by
    exact (measurable_of_countable (fun x : Fin J => P.mu x delta)).comp
      (measurable_fst.comp (Measurable.of_comap_le le_rfl))
  have hgmeas : Measurable g := by
    dsimp [g]
    exact Measurable.ite
      (measurableSet_lt measurable_const
        (measurable_fst.comp (measurable_snd.comp
          (Measurable.of_comap_le le_rfl))))
      clampOutcome_measurable
      hmuMeas
  have hg0 : ∀ᵐ o ∂P.dataMeasure, 0 ≤ g o := by
    filter_upwards [hmodel.outcomeSupport] with o ho
    dsimp [g]
    split_ifs
    · exact ho.1
    · exact ((hmodel.holder _).2.1 delta ⟨hdelta, hdelta1⟩).1
  have hg1 : ∀ᵐ o ∂P.dataMeasure, g o ≤ 1 := by
    filter_upwards [hmodel.outcomeSupport] with o ho
    dsimp [g]
    split_ifs
    · exact ho.2
    · exact ((hmodel.holder _).2.1 delta ⟨hdelta, hdelta1⟩).2
  rw [← clampFunctional_integral_eq P hmodel hdelta hdelta1]
  constructor
  · exact integral_nonneg_of_ae hg0
  · calc
      (∫ o, g o ∂P.dataMeasure) ≤ ∫ _o, (1 : ℝ) ∂P.dataMeasure :=
        integral_mono_ae
          (Integrable.of_bound
            hgmeas.aestronglyMeasurable 1
            (hg0.and hg1 |>.mono fun o h => by
              rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2))
          (integrable_const 1) hg1
      _ = 1 := by simp

/-- [local regression estimate lies in the stated closed interval](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `z` input](hyp:z), [the specified `x` input](hyp:x), [the specified `kappa` input](hyp:kappa), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h). -/
lemma localRegressionEstimate_mem_Icc {J n ell : ℕ}
    (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (kappa cminus cplus delta h : ℝ) :
    localRegressionEstimate B z x ell kappa cminus cplus delta h ∈
      Set.Icc (0 : ℝ) 1 := by
  unfold localRegressionEstimate
  split_ifs
  · exact clampUnit_mem_Icc _
  · norm_num

/-- [block average lies in the stated closed interval](goal) for [the specified `X` input](hyp:X), [the specified `n` input](hyp:n), [the specified `I` input](hyp:I), [the specified `z` input](hyp:z), [the specified `f` input](hyp:f), [the specified `hf` input](hyp:hf). -/
lemma blockAverage_mem_Icc {X : Type*} {n : ℕ} (I : Finset (Fin n))
    (z : Fin n → X) (f : X → ℝ) (hf : ∀ u, f u ∈ Set.Icc (0 : ℝ) 1) :
    blockAverage I z f ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hI : I.card = 0
  · simp [blockAverage, hI]
  have hcard : 0 < (I.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hI
  have hsum0 : 0 ≤ ∑ i ∈ I, f (z i) :=
    Finset.sum_nonneg fun i _ => (hf (z i)).1
  have hsum1 : (∑ i ∈ I, f (z i)) ≤ (I.card : ℝ) := by
    calc
      (∑ i ∈ I, f (z i)) ≤ ∑ _i ∈ I, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => (hf (z i)).2
      _ = (I.card : ℝ) := by simp
  unfold blockAverage
  constructor
  · positivity
  · calc
      (I.card : ℝ)⁻¹ * ∑ i ∈ I, f (z i) ≤
          (I.card : ℝ)⁻¹ * (I.card : ℝ) :=
        mul_le_mul_of_nonneg_left hsum1 (inv_nonneg.mpr hcard.le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hcard)

/-- [atom estimate lies in the stated closed interval](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `B` input](hyp:B), [the specified `z` input](hyp:z), [the specified `x` input](hyp:x), [the specified `delta` input](hyp:delta). -/
lemma atomEstimate_mem_Icc {J n : ℕ} (B : SplitBlocks n)
    (z : Fin n → ClampObs J) (x : Fin J) (delta : ℝ) :
    atomEstimate B z x delta ∈ Set.Icc (0 : ℝ) 1 := by
  apply blockAverage_mem_Icc
  intro o
  split_ifs <;> norm_num

/-- [the stated split block inv sqrt bound root property holds](goal) for [the specified `n` input](hyp:n), [the specified `m` input](hyp:m), [the specified `hn` input](hyp:hn), [the specified `hm` input](hyp:hm). -/
lemma splitBlock_invSqrt_le_root {n m : ℕ} (hn : 0 < n) (hm : n ≤ 8 * m) :
    Real.sqrt (m : ℝ)⁻¹ ≤ 3 * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmR : 0 < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hInv : (m : ℝ)⁻¹ ≤ 9 * (n : ℝ)⁻¹ := by
    have hR : (n : ℝ) ≤ 8 * (m : ℝ) := by exact_mod_cast hm
    rw [show 9 * (n : ℝ)⁻¹ = 9 / (n : ℝ) by ring]
    rw [le_div_iff₀ hnR]
    rw [inv_mul_le_iff₀ hmR]
    nlinarith
  have hl0 : 0 ≤ Real.sqrt (m : ℝ)⁻¹ := Real.sqrt_nonneg _
  have hr0 : 0 ≤ 3 * (n : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
  rw [← sq_le_sq₀ hl0 hr0]
  rw [Real.sq_sqrt (inv_nonneg.mpr (Nat.cast_nonneg m))]
  calc
    (m : ℝ)⁻¹ ≤ 9 * (n : ℝ)⁻¹ := hInv
    _ = (3 * (n : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 := by
      rw [mul_pow]
      norm_num
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hnR.le]
      norm_num
      rw [Real.rpow_neg_one]

/-- [balanced gram tail satisfies the stated upper bound](goal) for [the specified `n` input](hyp:n), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h), [the specified `C` input](hyp:C), [the specified `c` input](hyp:c), [the specified `hn` input](hyp:hn), [the specified `hbeta` input](hyp:hbeta), [the specified `hh` input](hyp:hh), [the specified `hh1` input](hyp:hh1), [the specified `hC` input](hyp:hC), [the specified `hc` input](hyp:hc), [the specified `hbalance` input](hyp:hbalance). -/
lemma balancedGramTail_le {n : ℕ} {beta kappa delta h C c : ℝ}
    (hn : 0 < n) (hbeta : 0 < beta) (hh : 0 < h) (hh1 : h ≤ 1)
    (hC : 0 ≤ C) (hc : 0 < c)
    (hbalance : (n : ℝ) * h ^ (2 * beta + 1) * (delta + h) ^ kappa = 1) :
    C * Real.exp (-c * (n : ℝ) * h * (delta + h) ^ kappa) ≤
      (C / c) * h ^ beta := by
  have heff := effectiveSampleSize_eq_rpow hh hbalance
  let e : ℝ := (n : ℝ) * h * (delta + h) ^ kappa
  have hepos : 0 < e := by
    rw [show e = h ^ (-2 * beta) by simpa [e] using heff]
    exact Real.rpow_pos_of_pos hh _
  let t : ℝ := 20 * c * e
  have ht : 0 < t := by dsimp [t]; positivity
  have hexp := exp_neg_scaled_le_inv ht
  have harg : -t / 20 = -c * e := by dsimp [t]; ring
  rw [harg] at hexp
  have hinv : 20 / t = (1 / c) * h ^ (2 * beta) := by
    have heq : e = h ^ (-2 * beta) := by simpa [e] using heff
    change 20 / (20 * c * e) = _
    rw [heq]
    rw [show -2 * beta = -(2 * beta) by ring, Real.rpow_neg hh.le]
    have hp : 0 < h ^ (2 * beta) := Real.rpow_pos_of_pos hh _
    field_simp [hc.ne', hp.ne']
  have hpow : h ^ (2 * beta) ≤ h ^ beta :=
    Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith)
  calc
    C * Real.exp (-c * (n : ℝ) * h * (delta + h) ^ kappa) =
        C * Real.exp (-c * e) := by
      congr 2
      dsimp [e]
      ring
    _ ≤ C * (20 / t) := mul_le_mul_of_nonneg_left hexp hC
    _ = (C / c) * h ^ (2 * beta) := by rw [hinv]; ring
    _ ≤ (C / c) * h ^ beta := by
      exact mul_le_mul_of_nonneg_left hpow (div_nonneg hC hc.le)

/-- [atom coefficient lies in the stated closed interval](goal) for [the specified `J` input](hyp:J), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `delta` input](hyp:delta), [the specified `hmodel` input](hyp:hmodel), [the specified `x` input](hyp:x), [the specified `hdelta1` input](hyp:hdelta1). -/
lemma atomCoefficient_mem_Icc {J : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (x : Fin J) (hdelta1 : delta ≤ 1) :
    P.px x * atomMass P x delta ∈ Set.Icc (0 : ℝ) 1 := by
  let _ := hmodel.probability
  let f : ClampObs J → ℝ := fun o =>
    if o.X = x ∧ o.A ≤ delta then 1 else 0
  have hX : Measurable (fun o : ClampObs J => o.X) :=
    measurable_fst.comp (Measurable.of_comap_le le_rfl)
  have hA : Measurable (fun o : ClampObs J => o.A) :=
    measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))
  have hf : Measurable f := by
    dsimp [f]
    exact Measurable.ite
      ((measurableSet_eq_fun hX measurable_const).inter
        (measurableSet_le hA measurable_const)) measurable_const measurable_const
  have hf0 : ∀ o, 0 ≤ f o := by intro o; dsimp [f]; split_ifs <;> norm_num
  have hf1 : ∀ o, f o ≤ 1 := by intro o; dsimp [f]; split_ifs <;> norm_num
  have hfint : Integrable f P.dataMeasure := by
    refine Integrable.of_bound hf.aestronglyMeasurable 1 ?_
    filter_upwards with o
    dsimp [f]
    split_ifs <;> norm_num
  have hint : ∫ o, f o ∂P.dataMeasure = P.px x * atomMass P x delta := by
    simpa [f] using atomEvent_integral_eq P hmodel x hdelta1
  rw [← hint]
  constructor
  · exact integral_nonneg_of_ae (ae_of_all _ hf0)
  · calc
      (∫ o, f o ∂P.dataMeasure) ≤ ∫ _o, (1 : ℝ) ∂P.dataMeasure :=
        integral_mono_ae hfint (integrable_const 1) (ae_of_all _ hf1)
      _ = 1 := by simp

/-- [the stated abs atom coefficient bound envelope property holds](goal) for [the specified `J` input](hyp:J), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `deltaBar` input](hyp:deltaBar), [the specified `alpha` input](hyp:alpha), [the specified `delta` input](hyp:delta), [the specified `hmodel` input](hyp:hmodel), [the specified `hreg` input](hyp:hreg), [the specified `x` input](hyp:x), [the specified `hdelta` input](hyp:hdelta). -/
lemma abs_atomCoefficient_le_envelope
    (J : ℕ) (P : ClampLaw J)
    {beta kappa L cminus cplus pmin deltaBar alpha delta : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (x : Fin J) (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar) :
    |P.px x * atomMass P x delta| ≤
      cplus * delta ^ (kappa + 1) / (kappa + 1) := by
  have hreg' := hreg
  rcases hreg' with
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
      hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha1⟩
  have hdelta1 : delta ≤ 1 := hdelta.2.trans hdeltaBar1.le
  have hcoef := atomCoefficient_mem_Icc P hmodel x hdelta1
  have hpush := clamp_pushforward_decomposition P beta kappa L cminus cplus
    pmin deltaBar alpha hmodel hreg x delta hdelta
  have hmass0 : 0 ≤ atomMass P x delta := by
    have hlower0 : 0 ≤ cminus * delta ^ (kappa + 1) / (kappa + 1) :=
      div_nonneg (mul_nonneg hcminus.le (Real.rpow_nonneg hdelta.1 _)) (by linarith)
    exact hlower0.trans hpush.2.1
  have hX : Measurable (fun o : ClampObs J => o.X) :=
    measurable_fst.comp (Measurable.of_comap_le le_rfl)
  let _ := hmodel.probability
  letI : IsProbabilityMeasure (P.dataMeasure.map (fun o => o.X)) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  have hpx0 : 0 ≤ P.px x := by
    rw [(hmodel.stratumMass x).1]
    exact measureReal_nonneg
  have hpx1 : P.px x ≤ 1 := by
    rw [(hmodel.stratumMass x).1]
    exact measureReal_le_one
  rw [abs_of_nonneg hcoef.1]
  calc
    P.px x * atomMass P x delta ≤ 1 * atomMass P x delta :=
      mul_le_mul_of_nonneg_right hpx1 hmass0
    _ ≤ _ := by simpa using hpush.2.2

/-- Deterministic decomposition of the total estimator into the retained-block
error, the atom-mass empirical errors, and the local-regression errors. The result uses [the `hmodel` condition](hyp:hmodel), [the `hdelta` condition](hyp:hdelta), [the `hdelta1` condition](hyp:hdelta1). [This is the stated conclusion](goal).
-/
lemma totalGramEstimator_error_le {J n ell : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta h : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (B : SplitBlocks n) (z : Fin n → ClampObs J) :
    |totalGramEstimator B z ell kappa cminus cplus delta h -
        clampFunctional P delta| ≤
      |retainedEstimate B z delta - retainedMean P delta| +
        ∑ x : Fin J,
          (|atomEstimate B z x delta - P.px x * atomMass P x delta| +
            |P.px x * atomMass P x delta| *
              |localRegressionEstimate B z x ell kappa cminus cplus delta h -
                P.mu x delta|) := by
  let center := retainedEstimate B z delta + ∑ x : Fin J,
    atomEstimate B z x delta *
      localRegressionEstimate B z x ell kappa cminus cplus delta h
  have htarget := clampFunctional_mem_Icc P hmodel hdelta hdelta1
  have hclamp := abs_clampUnit_sub_le center (clampFunctional P delta) htarget
  have hprod (x : Fin J) :
      |atomEstimate B z x delta *
          localRegressionEstimate B z x ell kappa cminus cplus delta h -
        P.px x * atomMass P x delta * P.mu x delta| ≤
        |atomEstimate B z x delta - P.px x * atomMass P x delta| +
          |P.px x * atomMass P x delta| *
            |localRegressionEstimate B z x ell kappa cminus cplus delta h -
              P.mu x delta| := by
    let ah := atomEstimate B z x delta
    let a := P.px x * atomMass P x delta
    let mh := localRegressionEstimate B z x ell kappa cminus cplus delta h
    let m := P.mu x delta
    have hmh := localRegressionEstimate_mem_Icc (ell := ell)
      B z x kappa cminus cplus delta h
    have hid : ah * mh - a * m = (ah - a) * mh + a * (mh - m) := by ring
    rw [hid]
    calc
      |(ah - a) * mh + a * (mh - m)| ≤
          |(ah - a) * mh| + |a * (mh - m)| := abs_add_le _ _
      _ = |ah - a| * |mh| + |a| * |mh - m| := by rw [abs_mul, abs_mul]
      _ ≤ |ah - a| + |a| * |mh - m| := by
        apply add_le_add_left
        apply mul_le_of_le_one_right (abs_nonneg _)
        rw [abs_of_nonneg hmh.1]
        exact hmh.2
  have hsum :
      |∑ x : Fin J,
          (atomEstimate B z x delta *
              localRegressionEstimate B z x ell kappa cminus cplus delta h -
            P.px x * atomMass P x delta * P.mu x delta)| ≤
        ∑ x : Fin J,
          (|atomEstimate B z x delta - P.px x * atomMass P x delta| +
            |P.px x * atomMass P x delta| *
              |localRegressionEstimate B z x ell kappa cminus cplus delta h -
                P.mu x delta|) := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun x _ => hprod x)
  calc
    |totalGramEstimator B z ell kappa cminus cplus delta h -
        clampFunctional P delta| ≤ |center - clampFunctional P delta| := by
      simpa [totalGramEstimator, center] using hclamp
    _ = |(retainedEstimate B z delta - retainedMean P delta) +
        ∑ x : Fin J,
          (atomEstimate B z x delta *
              localRegressionEstimate B z x ell kappa cminus cplus delta h -
            P.px x * atomMass P x delta * P.mu x delta)| := by
      congr 1
      simp only [clampFunctional, Finset.sum_sub_distrib]
      ring
    _ ≤ |retainedEstimate B z delta - retainedMean P delta| +
        |∑ x : Fin J,
          (atomEstimate B z x delta *
              localRegressionEstimate B z x ell kappa cminus cplus delta h -
            P.px x * atomMass P x delta * P.mu x delta)| := abs_add_le _ _
    _ ≤ _ := add_le_add_right hsum _

/-- Integrated form of `totalGramEstimator_error_le`, with every finite-sample
term exposed for the concentration and empirical-process bounds. The result uses [the `hmodel` condition](hyp:hmodel), [the `hdelta` condition](hyp:hdelta), [the `hdelta1` condition](hyp:hdelta1). [This is the stated conclusion](goal).
-/
lemma totalGramEstimator_risk_decomposition {J n ell : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta h : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (B : SplitBlocks n) :
    (∫ z, |totalGramEstimator B z ell kappa cminus cplus delta h -
        clampFunctional P delta| ∂iidProduct P n) ≤
      (∫ z, |retainedEstimate B z delta - retainedMean P delta|
        ∂iidProduct P n) +
      ∑ x : Fin J,
        ((∫ z, |atomEstimate B z x delta - P.px x * atomMass P x delta|
            ∂iidProduct P n) +
          |P.px x * atomMass P x delta| *
            ∫ z, |localRegressionEstimate B z x ell kappa cminus cplus delta h -
              P.mu x delta| ∂iidProduct P n) := by
  let _ := hmodel.probability
  letI : IsProbabilityMeasure (iidProduct P n) := by
    unfold iidProduct
    infer_instance
  let eret : (Fin n → ClampObs J) → ℝ := fun z =>
    |retainedEstimate B z delta - retainedMean P delta|
  let eatom : Fin J → (Fin n → ClampObs J) → ℝ := fun x z =>
    |atomEstimate B z x delta - P.px x * atomMass P x delta|
  let elocal : Fin J → (Fin n → ClampObs J) → ℝ := fun x z =>
    |localRegressionEstimate B z x ell kappa cminus cplus delta h - P.mu x delta|
  let lhs : (Fin n → ClampObs J) → ℝ := fun z =>
    |totalGramEstimator B z ell kappa cminus cplus delta h - clampFunctional P delta|
  have hretBase : Integrable (fun z : Fin n → ClampObs J =>
      retainedEstimate B z delta) (iidProduct P n) := by
    refine Integrable.of_bound
      (retainedEstimate_measurable B delta).aestronglyMeasurable 1 ?_
    filter_upwards [iidProduct_outcomeSupport P hmodel] with z hz
    have hrange : retainedEstimate B z delta ∈ Set.Icc (0 : ℝ) 1 := by
      have hi := blockAverage_mem_Icc B.I0 (fun i : Fin n => i)
        (fun i => if delta < (z i).A then (z i).Y else 0) (by
          intro i
          by_cases ha : delta < (z i).A
          · simpa [ha] using hz i
          · simp [ha])
      simpa [retainedEstimate, blockAverage] using hi
    rw [Real.norm_eq_abs, abs_of_nonneg hrange.1]
    exact hrange.2
  have hretInt : Integrable eret (iidProduct P n) := by
    exact (hretBase.sub (integrable_const (retainedMean P delta))).abs
  have hatomInt (x : Fin J) : Integrable (eatom x) (iidProduct P n) := by
    apply Integrable.abs
    apply Integrable.sub
    · refine Integrable.of_bound
        (atomEstimate_measurable B x delta).aestronglyMeasurable 1 ?_
      filter_upwards with z
      have hr := atomEstimate_mem_Icc B z x delta
      rw [Real.norm_eq_abs, abs_of_nonneg hr.1]
      exact hr.2
    · exact integrable_const _
  have hlocalInt (x : Fin J) : Integrable (elocal x) (iidProduct P n) := by
    apply Integrable.abs
    apply Integrable.sub
    · refine Integrable.of_bound
        (localRegressionEstimate_measurable B x kappa cminus cplus delta h).aestronglyMeasurable
        1 ?_
      filter_upwards with z
      have hr := localRegressionEstimate_mem_Icc (ell := ell)
        B z x kappa cminus cplus delta h
      rw [Real.norm_eq_abs, abs_of_nonneg hr.1]
      exact hr.2
    · exact integrable_const _
  have hlhsInt : Integrable lhs (iidProduct P n) := by
    apply Integrable.abs
    exact ((Integrable.of_bound
      (totalGramEstimator_measurable B kappa cminus cplus delta h).aestronglyMeasurable
      1 (by
        filter_upwards with z
        have hr := clampUnit_mem_Icc
          (retainedEstimate B z delta + ∑ x : Fin J,
            atomEstimate B z x delta *
              localRegressionEstimate B z x ell kappa cminus cplus delta h)
        rw [show totalGramEstimator B z ell kappa cminus cplus delta h =
            clampUnit (retainedEstimate B z delta + ∑ x : Fin J,
              atomEstimate B z x delta *
                localRegressionEstimate B z x ell kappa cminus cplus delta h) by rfl]
        rw [Real.norm_eq_abs, abs_of_nonneg hr.1]
        exact hr.2)).sub (integrable_const _))
  have hrhsInt : Integrable (fun z => eret z + ∑ x : Fin J,
      (eatom x z + |P.px x * atomMass P x delta| * elocal x z))
      (iidProduct P n) :=
    hretInt.add (integrable_finsetSum Finset.univ fun x _ =>
      (hatomInt x).add ((hlocalInt x).const_mul _))
  have hmono : (∫ z, lhs z ∂iidProduct P n) ≤
      ∫ z, (eret z + ∑ x : Fin J,
        (eatom x z + |P.px x * atomMass P x delta| * elocal x z))
        ∂iidProduct P n := by
    exact integral_mono_ae hlhsInt hrhsInt
      (ae_of_all _ fun z => totalGramEstimator_error_le P hmodel hdelta hdelta1 B z)
  calc
    (∫ z, |totalGramEstimator B z ell kappa cminus cplus delta h -
        clampFunctional P delta| ∂iidProduct P n) =
        ∫ z, lhs z ∂iidProduct P n := rfl
    _ ≤ _ := hmono
    _ = (∫ z, eret z ∂iidProduct P n) + ∫ z, ∑ x : Fin J,
        (eatom x z + |P.px x * atomMass P x delta| * elocal x z)
        ∂iidProduct P n := integral_add hretInt
          (integrable_finsetSum Finset.univ fun x _ =>
            (hatomInt x).add ((hlocalInt x).const_mul _))
    _ = (∫ z, eret z ∂iidProduct P n) + ∑ x : Fin J,
        ∫ z, (eatom x z + |P.px x * atomMass P x delta| * elocal x z)
          ∂iidProduct P n := by
      rw [integral_finsetSum Finset.univ]
      exact fun x _ => (hatomInt x).add ((hlocalInt x).const_mul _)
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      rw [integral_add (hatomInt x) ((hlocalInt x).const_mul _), integral_const_mul]

/-- Explicit finite-sample risk bound at an information-balanced bandwidth,
before the elementary eventual-rate simplifications. The result uses [the `hmodel` condition](hyp:hmodel), [the `hreg` condition](hyp:hreg), [the `hsampling` condition](hyp:hsampling), [the `hn` condition](hyp:hn), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hupper` condition](hyp:hupper), [the `hbalance` condition](hyp:hbalance), [the `hlambda` condition](hyp:hlambda), [the `htail` condition](hyp:htail). [This is the stated conclusion](goal).
-/
lemma totalGramEstimator_risk_le_explicit
    {J n : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin deltaBar alpha delta h Ctail ctail : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (hsampling : IidSampling P n) (B : SplitBlocks n)
    (hn : 8 ≤ n) (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (hh : 0 < h) (hupper : delta + h ≤ 1)
    (hbalance : (n : ℝ) * h ^ (2 * beta + 1) * (delta + h) ^ kappa = 1)
    (hlambda : 0 < lambdaStar (ellOf beta) kappa cminus cplus)
    (htail : ∀ x : Fin J,
      (iidProduct P n).real {z |
        ¬ GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h} ≤
        Ctail * Real.exp (-ctail * (n : ℝ) * h * (delta + h) ^ kappa)) :
    (∫ z, |totalGramEstimator B z (ellOf beta) kappa cminus cplus delta h -
        clampFunctional P delta| ∂iidProduct P n) ≤
      (1 / 2 : ℝ) * Real.sqrt (B.I0.card : ℝ)⁻¹ +
      (J : ℝ) * ((1 / 2 : ℝ) * Real.sqrt (B.I1.card : ℝ)⁻¹ +
        (cplus * delta ^ (kappa + 1) / (kappa + 1)) *
          ((1 / 2 : ℝ) * Real.sqrt
              (336 * (4 * (ellOf beta + 1 : ℝ) /
                lambdaStar (ellOf beta) kappa cminus cplus ^ 2) /
                (pmin * cminus / (2 * (2 : ℝ) ^ kappa))) * h ^ beta +
            (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
              lambdaStar (ellOf beta) kappa cminus cplus) * L * h ^ beta +
            Ctail * Real.exp (-ctail * (n : ℝ) * h *
              (delta + h) ^ kappa))) := by
  rcases hreg with
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
      hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha1⟩
  have hregFull : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha :=
    ⟨hJ, hbeta, hkappa, hL, hcminus, hcminus_le, hcplus,
      hpmin, hpmin_le, hdeltaBar, hdeltaBar1, halpha, halpha1⟩
  have hdelta1 : delta ≤ 1 := hdelta.2.trans hdeltaBar1.le
  have hcard0 : 0 < B.I0.card := lt_of_lt_of_le (by omega) B.card_I0
  have hcard1 : 0 < B.I1.card := lt_of_lt_of_le (by omega) B.card_I1
  let noiseC : ℝ := (1 / 2 : ℝ) * Real.sqrt
    (336 * (4 * (ellOf beta + 1 : ℝ) /
      lambdaStar (ellOf beta) kappa cminus cplus ^ 2) /
      (pmin * cminus / (2 * (2 : ℝ) ^ kappa)))
  let biasC : ℝ := 2 * Real.sqrt (ellOf beta + 1 : ℝ) /
    lambdaStar (ellOf beta) kappa cminus cplus
  let tail : ℝ := Ctail * Real.exp
    (-ctail * (n : ℝ) * h * (delta + h) ^ kappa)
  let localBound : ℝ := noiseC * h ^ beta + biasC * L * h ^ beta + tail
  let atomBound : ℝ := cplus * delta ^ (kappa + 1) / (kappa + 1)
  have hnoise (x : Fin J) :
      (∫ z, |∑ i ∈ B.I2,
        interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
          (clampUnit (z i).Y -
            clampRegressionExtension P ((z i).X, (z i).A))| ∂iidProduct P n) ≤
        noiseC * h ^ beta := by
    simpa [noiseC] using localRegression_centered_balanced_l1_le
      (ell := ellOf beta) P hmodel hsampling B x hn hbeta hkappa hcminus
        (by linarith) hpmin hdelta.1 hh hupper hlambda hbalance
  have hlocal (x : Fin J) :
      (∫ z, |localRegressionEstimate B z x (ellOf beta) kappa cminus cplus
          delta h - P.mu x delta| ∂iidProduct P n) ≤ localBound := by
    have hd := localRegression_risk_le_noise_bias_bad P hmodel hbeta hL B x
      hdelta.1 hh hupper hlambda
    calc
      _ ≤
          (∫ z, |∑ i ∈ B.I2,
            interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
              (clampUnit (z i).Y -
                clampRegressionExtension P ((z i).X, (z i).A))| ∂iidProduct P n) +
          biasC * L * h ^ beta +
          (iidProduct P n).real {z |
            ¬ GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h} := by
        simpa [biasC] using hd
      _ ≤ noiseC * h ^ beta + biasC * L * h ^ beta + tail := by
        exact add_le_add (add_le_add (hnoise x) le_rfl) (htail x)
      _ = localBound := rfl
  have hatomBound0 : 0 ≤ atomBound := by
    dsimp [atomBound]
    exact div_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hdelta.1 _)) (by linarith)
  have hdec := totalGramEstimator_risk_decomposition (ell := ellOf beta) (h := h)
    P hmodel hdelta.1 hdelta1 B
  calc
    _ ≤
        (∫ z, |retainedEstimate B z delta - retainedMean P delta| ∂iidProduct P n) +
        ∑ x : Fin J,
          ((∫ z, |atomEstimate B z x delta - P.px x * atomMass P x delta|
              ∂iidProduct P n) +
            |P.px x * atomMass P x delta| *
              ∫ z, |localRegressionEstimate B z x (ellOf beta) kappa cminus cplus
                delta h - P.mu x delta| ∂iidProduct P n) := hdec
    _ ≤ (1 / 2 : ℝ) * Real.sqrt (B.I0.card : ℝ)⁻¹ +
        ∑ _x : Fin J,
          ((1 / 2 : ℝ) * Real.sqrt (B.I1.card : ℝ)⁻¹ +
            atomBound * localBound) := by
      apply add_le_add
      · exact retainedEstimate_l1_le P hmodel B hcard0
      · apply Finset.sum_le_sum
        intro x hx
        apply add_le_add
        · exact atomEstimate_l1_le P hmodel B hcard1 x hdelta.1 hdelta1
        · exact mul_le_mul
            (by simpa [atomBound] using
              abs_atomCoefficient_le_envelope J P hmodel hregFull x hdelta)
            (hlocal x) (integral_nonneg fun _ => abs_nonneg _) hatomBound0
    _ = _ := by
      simp [atomBound, localBound, noiseC, biasC, tail]
      ring

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier

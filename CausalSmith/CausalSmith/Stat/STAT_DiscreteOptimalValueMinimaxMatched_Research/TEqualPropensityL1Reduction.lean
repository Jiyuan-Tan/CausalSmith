import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.L1Embedding

/-! Equal-propensity L1 identities and minimax transfer. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

-- @node: l1_source_singleton
/-- [the stated l1 source singleton relation holds](goal). -/
lemma l1_source_singleton {d : ℕ} (Pv Qv : ProbabilitySimplex d) (z : Fin d × Fin d) :
    ((simplexPMF Pv).toMeasure.prod (simplexPMF Qv).toMeasure) {z} =
      ENNReal.ofReal (Pv.1 z.1) * ENNReal.ofReal (Qv.1 z.2) := by
  classical
  calc
    _ = ((simplexPMF Pv).toMeasure.prod (simplexPMF Qv).toMeasure)
        ({z.1} ×ˢ {z.2}) := by
          congr 1
          ext w
          simp
    _ = (simplexPMF Pv).toMeasure {z.1} * (simplexPMF Qv).toMeasure {z.2} :=
      Measure.prod_prod _ _
    _ = _ := by simp [simplexPMF]

-- @node: l1_kernel_singleton
/-- [the stated l1 kernel singleton relation holds](goal). -/
lemma l1_kernel_singleton {d : ℕ} (z : Fin d × Fin d) (o : Obs d) :
    l1SingleKernel z {o} =
      (PMF.map (fun k : Fin 4 =>
        if k = 0 then (z.1, false, false)
        else if k = 1 then (z.1, true, true)
        else if k = 2 then (z.2, false, true)
        else (z.2, true, false)) (PMF.uniformOfFintype (Fin 4))) o := by
  unfold l1SingleKernel
  exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)

-- @node: l1_kernel_atoms
/-- [the stated l1 kernel atoms relation holds](goal). -/
lemma l1_kernel_atoms {d : ℕ} (z : Fin d × Fin d) (x : Fin d) :
    (l1SingleKernel z {(x, true, true)}).toReal = (if z.1 = x then 1 / 4 else 0) ∧
    (l1SingleKernel z {(x, false, false)}).toReal = (if z.1 = x then 1 / 4 else 0) ∧
    (l1SingleKernel z {(x, true, false)}).toReal = (if z.2 = x then 1 / 4 else 0) ∧
    (l1SingleKernel z {(x, false, true)}).toReal = (if z.2 = x then 1 / 4 else 0) := by
  simp [l1_kernel_singleton, PMF.map_apply, tsum_fintype, Fin.sum_univ_four]
  constructor
  · by_cases h : z.1 = x
    · subst x; simp
    · have hn : x ≠ z.1 := Ne.symm h
      simp [h, hn]
  · by_cases h : z.2 = x
    · subst x; simp
    · have hn : x ≠ z.2 := Ne.symm h
      simp [h, hn]

-- @node: l1_kernel_atom_formula
/-- [the stated l1 kernel atom formula relation holds](goal). -/
lemma l1_kernel_atom_formula {d : ℕ} (z : Fin d × Fin d) (x : Fin d) (a y : Bool) :
    (l1SingleKernel z {(x, a, y)}).toReal =
      if (if a = y then z.1 else z.2) = x then 1 / 4 else 0 := by
  fin_cases a <;> fin_cases y
  · simpa using (l1_kernel_atoms z x).1
  · simpa using (l1_kernel_atoms z x).2.2.1
  · simpa using (l1_kernel_atoms z x).2.2.2
  · simpa using (l1_kernel_atoms z x).2.1

-- @node: l1SingleKernel_comp_pair
/-- [the stated l1 single kernel composition pair relation holds](goal). -/
lemma l1SingleKernel_comp_pair {d : ℕ} (Pv Qv : ProbabilitySimplex d) :
    l1SingleKernel ∘ₘ
        ((simplexPMF Pv).toMeasure.prod (simplexPMF Qv).toMeasure) =
      obsLaw (observedMarginal (l1Embedding Pv Qv)) := by
  classical
  letI : IsMarkovKernel (l1SingleKernel (d := d)) := by
    unfold l1SingleKernel
    refine ⟨fun z => ⟨?_⟩⟩
    change (PMF.map _ (PMF.uniformOfFintype (Fin 4))).toMeasure Set.univ = 1
    exact measure_univ
  letI : IsProbabilityMeasure
      ((simplexPMF Pv).toMeasure.prod (simplexPMF Qv).toMeasure) := by infer_instance
  apply Measure.ext_of_singleton
  rintro ⟨x, a, y⟩
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
  unfold obsLaw
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change ((l1SingleKernel ∘ₘ
    ((simplexPMF Pv).toMeasure.prod (simplexPMF Qv).toMeasure)) {(x, a, y)}).toReal =
      jointMass (observedMarginal (l1Embedding Pv Qv)) x a y
  rw [Measure.bind_apply (measurableSet_singleton _) (Kernel.aemeasurable _)]
  rw [MeasureTheory.lintegral_fintype]
  change (∑ z : Fin d × Fin d,
    (l1SingleKernel z {(x, a, y)}) *
      (((simplexPMF Pv).toMeasure.prod (simplexPMF Qv).toMeasure) {z})).toReal = _
  simp_rw [l1_source_singleton Pv Qv]
  have hs := l1Embedding_spec Pv Qv
  fin_cases a <;> fin_cases y
  all_goals
    rw [ENNReal.toReal_sum (by
      intro z _hz
      exact ENNReal.mul_ne_top (measure_ne_top _ _)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))]
  all_goals
    simp_rw [ENNReal.toReal_mul, l1_kernel_atom_formula,
      ENNReal.toReal_ofReal (Pv.2.1 _), ENNReal.toReal_ofReal (Qv.2.1 _)]
  all_goals rw [Fintype.sum_prod_type]
  all_goals
    simp [Pv.2.2, Qv.2.2, hs.2.2.1 x, hs.2.2.2.1 x,
      hs.2.2.2.2.1 x, hs.2.2.2.2.2 x]
  · calc
      _ = (1 / 4 * Pv.1 x) * ∑ i, Qv.1 i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = _ := by rw [Qv.2.2]; ring
  · calc
      _ = (∑ i, Pv.1 i) * (1 / 4 * Qv.1 x) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = _ := by rw [Pv.2.2]; ring
  · calc
      _ = (∑ i, Pv.1 i) * (1 / 4 * Qv.1 x) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = _ := by rw [Pv.2.2]; ring
  · calc
      _ = (1 / 4 * Pv.1 x) * ∑ i, Qv.1 i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = _ := by rw [Qv.2.2]; ring

-- @node: observedOptimalValue_mem_unitInterval
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), then [the stated observed optimal value mem unit interval relation holds](goal). -/
lemma observedOptimalValue_mem_unitInterval {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P) :
    observedOptimalValue P hP ∈ Set.Icc (0 : ℝ) 1 := by
  have hj (x : Fin d) (a y : Bool) : 0 ≤ jointMass P x a y := ENNReal.toReal_nonneg
  have hc (x : Fin d) : 0 ≤ cellMass P x := by
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun y _ => hj x a y
  have hm (x : Fin d) (a : Bool) : outcomeMean P a x ∈ Set.Icc (0 : ℝ) 1 := by
    have ha : 0 ≤ armMass P a x := Finset.sum_nonneg fun y _ => hj x a y
    have hle : jointMass P x a true ≤ armMass P a x := by
      simp [armMass]
      exact hj x a false
    exact ⟨div_nonneg (hj x a true) ha, div_le_one_of_le₀ hle ha⟩
  have hsum : ∑ x : Fin d, cellMass P x = 1 := by
    calc
      _ = ∑ z : Obs d, (P.pmf z).toReal := by
        simp [cellMass, jointMass, Fintype.sum_prod_type]
      _ = 1 := by
        simpa using (PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : ℝ))).symm
  rw [observedOptimalValue, observedOptimalValueRaw]
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (hc x)
      ((hm x false).1.trans (le_max_left _ _))
  · calc
      ∑ x : Fin d, cellMass P x * max (outcomeMean P false x) (outcomeMean P true x) ≤
          ∑ x : Fin d, cellMass P x * 1 := by
        apply Finset.sum_le_sum
        intro x _hx
        exact mul_le_mul_of_nonneg_left
          (max_le (hm x false).2 (hm x true).2) (hc x)
      _ = 1 := by simpa using hsum

-- @node: uniformlyBounded_of_fintype
/-- [every real-valued function on a finite set is uniformly bounded](goal). -/
lemma uniformlyBounded_of_fintype {α : Type*} [Fintype α] (f : α → ℝ) :
    Causalean.Stat.UniformlyBounded f := by
  classical
  refine ⟨∑ x, |f x|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro x
  exact Finset.single_le_sum (fun y _hy => abs_nonneg (f y)) (Finset.mem_univ x)

-- @node: observedRisk_bddAbove
/-- [the family of observed squared-error risks is bounded above](goal). -/
lemma observedRisk_bddAbove {n d : ℕ} {epsilon : ℝ} (est : Estimator n d) :
    BddAbove (Set.range (observedRisk n (d := d) (epsilon := epsilon) est)) := by
  classical
  let M : ℝ := ∑ s, |est.1 s|
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hest : ∀ s, |est.1 s| ≤ M := fun s =>
    Finset.single_le_sum (fun t _ht => abs_nonneg (est.1 t)) (Finset.mem_univ s)
  refine ⟨(M + 1) ^ 2, ?_⟩
  rintro _ ⟨P, rfl⟩
  have htheta := observedOptimalValue_mem_unitInterval P.1 P.2
  have hthetaAbs : |observedOptimalValue P.1 P.2| ≤ 1 := by
    rw [abs_of_nonneg htheta.1]
    exact htheta.2
  unfold observedRisk Causalean.Stat.sqRisk
  have hi := norm_integral_le_of_norm_le_const
    (μ := productLaw P.1 n) (f := fun s => (est.1 s - observedOptimalValue P.1 P.2) ^ 2)
    (C := (M + 1) ^ 2) (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq,
        abs_of_nonneg (add_nonneg hM (by norm_num))]
      exact (abs_sub _ _).trans (add_le_add (hest s) hthetaAbs))
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hi)

-- @node: l1Embedding_observed_reduction
/-- If [the alphabet size satisfies its stated restriction](hyp:hd), and [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), then [the L1 embedding is an admissible equal-propensity observed model whose optimal value is one half plus one quarter of the L1 distance](goal). -/
lemma l1Embedding_observed_reduction {n d : ℕ} {epsilon : ℝ}
    (hd : 2 ≤ d) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2) :
    ∀ Pv Qv : ProbabilitySimplex d,
      let P := observedMarginal (l1Embedding Pv Qv)
      ∃ hP : ObservedModelClass epsilon P,
      (∀ x, cellMass P x = (Pv.1 x + Qv.1 x) / 2) ∧
      (∀ x, 0 < cellMass P x → propensity P x = 1 / 2) ∧
      observedOptimalValue P hP = 1 / 2 + l1Distance Pv Qv / 4 ∧
      l1FixedSampleKernel n d ∘ₘ fixedPairLaw n (Pv, Qv) = productLaw P n := by
  classical
  intro Pv Qv
  let P := observedMarginal (l1Embedding Pv Qv)
  have hs := l1Embedding_spec Pv Qv
  have hcell : ∀ x, cellMass P x = (Pv.1 x + Qv.1 x) / 2 := by
    intro x
    simp [P, cellMass, armMass, hs.2.2.1 x, hs.2.2.2.1 x,
      hs.2.2.2.2.1 x, hs.2.2.2.2.2 x]
    ring
  have hprop : ∀ x, 0 < cellMass P x → propensity P x = 1 / 2 := by
    intro x hx
    rw [propensity]
    have hsum : Pv.1 x + Qv.1 x ≠ 0 := by
      intro hs0
      rw [hcell x, hs0] at hx
      norm_num at hx
    simp [P, armMass, hs.2.2.1 x, hs.2.2.2.1 x,
      hs.2.2.2.2.1 x, hs.2.2.2.2.2 x, hcell x]
    field_simp
    norm_num
  have hP : ObservedModelClass epsilon P := by
    refine ⟨hd, hepsilon.1, hepsilon.2, ?_⟩
    intro x hx
    rw [hprop x hx]
    constructor <;> linarith
  refine ⟨hP, hcell, hprop, ?_, ?_⟩
  · rw [observedOptimalValue, observedOptimalValueRaw]
    have hterm : ∀ x : Fin d,
        cellMass P x * max (outcomeMean P false x) (outcomeMean P true x) =
          max (Pv.1 x) (Qv.1 x) / 2 := by
      intro x
      have hp := Pv.2.1 x
      have hq := Qv.2.1 x
      by_cases hz : Pv.1 x + Qv.1 x = 0
      · have hp0 : Pv.1 x = 0 := by nlinarith
        have hq0 : Qv.1 x = 0 := by nlinarith
        simp [P, cellMass, armMass, outcomeMean, hs.2.2.1 x, hs.2.2.2.1 x,
          hs.2.2.2.2.1 x, hs.2.2.2.2.2 x, hp0, hq0]
      · have hspos : 0 < Pv.1 x + Qv.1 x :=
          lt_of_le_of_ne (add_nonneg hp hq) (Ne.symm hz)
        have hmuf : outcomeMean P false x = Qv.1 x / (Pv.1 x + Qv.1 x) := by
          have hz' : Qv.1 x + Pv.1 x ≠ 0 := by
            intro h
            apply hz
            linarith
          simp [P, armMass, outcomeMean, hs.2.2.2.1 x, hs.2.2.2.2.2 x]
          field_simp [hz, hz']
          ring
        have hmut : outcomeMean P true x = Pv.1 x / (Pv.1 x + Qv.1 x) := by
          simp [P, armMass, outcomeMean, hs.2.2.1 x, hs.2.2.2.2.1 x]
          field_simp [hz]
        rw [hmuf, hmut, hcell x]
        by_cases hle : Pv.1 x ≤ Qv.1 x
        · rw [max_eq_right hle]
          have hratio : Pv.1 x / (Pv.1 x + Qv.1 x) ≤
              Qv.1 x / (Pv.1 x + Qv.1 x) := by gcongr
          rw [max_eq_left hratio]
          field_simp [hz]
        · have hle' : Qv.1 x ≤ Pv.1 x := le_of_not_ge hle
          rw [max_eq_left hle']
          have hratio : Qv.1 x / (Pv.1 x + Qv.1 x) ≤
              Pv.1 x / (Pv.1 x + Qv.1 x) := by gcongr
          rw [max_eq_right hratio]
          field_simp [hz]
    rw [Finset.sum_congr rfl (fun x _ => hterm x)]
    unfold l1Distance
    have hpoint : ∀ x : Fin d,
        max (Pv.1 x) (Qv.1 x) / 2 =
          (Pv.1 x + Qv.1 x) / 4 + |Pv.1 x - Qv.1 x| / 4 := by
      intro x
      by_cases hle : Pv.1 x ≤ Qv.1 x
      · rw [max_eq_right hle, abs_of_nonpos (sub_nonpos.mpr hle)]
        ring
      · have hle' : Qv.1 x ≤ Pv.1 x := le_of_not_ge hle
        rw [max_eq_left hle', abs_of_nonneg (sub_nonneg.mpr hle')]
        ring
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
      Finset.sum_add_distrib, Pv.2.2, Qv.2.2]
    ring
  · letI : IsMarkovKernel (l1SingleKernel (d := d)) := by
      unfold l1SingleKernel
      refine ⟨fun z => ⟨?_⟩⟩
      change (PMF.map _ (PMF.uniformOfFintype (Fin 4))).toMeasure Set.univ = 1
      exact measure_univ
    unfold l1FixedSampleKernel fixedPairLaw productLaw
    rw [Causalean.Stat.finProductKernel_comp_pi]
    congr 1
    funext i
    exact l1SingleKernel_comp_pair Pv Qv

-- @node: l1_minimax_transfer
/-- If [the alphabet size satisfies its stated restriction](hyp:hd), and [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), then [observed optimal-value minimax risk is at least one sixteenth of the paired-distribution L1 minimax risk](goal). -/
lemma l1_minimax_transfer {n d : ℕ} {epsilon : ℝ}
    (hd : 2 ≤ d) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (Pv0 Qv0 : ProbabilitySimplex d) :
    fixedL1MinimaxRisk n d / 16 ≤ minimaxRisk n d epsilon := by
  classical
  letI : IsMarkovKernel (l1SingleKernel (d := d)) := by
    unfold l1SingleKernel
    refine ⟨fun z => ⟨?_⟩⟩
    change (PMF.map _ (PMF.uniformOfFintype (Fin 4))).toMeasure Set.univ = 1
    exact measure_univ
  letI : Nonempty (Estimator n d) := ⟨⟨fun _ => 0, measurable_const⟩⟩
  letI : Nonempty (ProbabilitySimplex d × ProbabilitySimplex d) := ⟨(Pv0, Qv0)⟩
  letI : IsMarkovKernel (l1FixedSampleKernel n d) := by
    unfold l1FixedSampleKernel
    infer_instance
  unfold minimaxRisk
  apply Causalean.Stat.le_minimaxValue
  intro est
  let sourceEst : FixedL1Estimator n d :=
    ⟨Causalean.Stat.kernelAffinePullback (l1FixedSampleKernel n d) (1 / 4) (1 / 2) est.1,
      Causalean.Stat.measurable_kernelAffinePullback _ est.2⟩
  have hmin : fixedL1MinimaxRisk n d ≤
      Causalean.Stat.worstCaseRisk (fixedL1Risk (d := d) n) sourceEst := by
    unfold fixedL1MinimaxRisk
    exact Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
      (fun _ _ => by unfold fixedL1Risk Causalean.Stat.sqRisk; positivity) sourceEst
  have hwc : Causalean.Stat.worstCaseRisk (fixedL1Risk (d := d) n) sourceEst ≤
      16 * Causalean.Stat.worstCaseRisk
        (observedRisk n (d := d) (epsilon := epsilon)) est := by
    apply Causalean.Stat.worstCaseRisk_le
    rintro ⟨Pv, Qv⟩
    obtain ⟨hP, _hcell, _hprop, hvalue, hkernel⟩ :=
      l1Embedding_observed_reduction (n := n) hd hepsilon Pv Qv
    let MP : ModelLaw d epsilon := ⟨observedMarginal (l1Embedding Pv Qv), hP⟩
    letI : IsProbabilityMeasure (fixedPairLaw n (Pv, Qv)) := by
      unfold fixedPairLaw
      infer_instance
    have htarget := Causalean.Stat.le_worstCaseRisk (observedRisk_bddAbove est) MP
    have htransport := Causalean.Stat.sqRisk_kernelAffinePullback_le_comp
      (fixedPairLaw n (Pv, Qv)) (l1FixedSampleKernel n d)
      (a := (1 / 4 : ℝ)) (b := (1 / 2 : ℝ)) (theta := l1Distance Pv Qv)
      (by norm_num) est.2 (uniformlyBounded_of_fintype est.1)
    have hpoint : fixedL1Risk n sourceEst (Pv, Qv) ≤
        16 * observedRisk (epsilon := epsilon) n est MP := by
      change Causalean.Stat.sqRisk (fixedPairLaw n (Pv, Qv)) sourceEst.1
          (l1Distance Pv Qv) ≤
        16 * Causalean.Stat.sqRisk
          (productLaw (observedMarginal (l1Embedding Pv Qv)) n) est.1
          (observedOptimalValue (observedMarginal (l1Embedding Pv Qv)) hP)
      dsimp [sourceEst]
      rw [hkernel] at htransport
      rw [hvalue]
      have htransport' : (1 / 16 : ℝ) *
          Causalean.Stat.sqRisk (fixedPairLaw n (Pv, Qv))
            (Causalean.Stat.kernelAffinePullback
              (l1FixedSampleKernel n d) (1 / 4) (1 / 2) est.1)
            (l1Distance Pv Qv) ≤
          Causalean.Stat.sqRisk (productLaw (observedMarginal (l1Embedding Pv Qv)) n)
            est.1 (1 / 2 + l1Distance Pv Qv / 4) := by
        convert htransport using 1 <;> ring
      linarith
    exact hpoint.trans (mul_le_mul_of_nonneg_left htarget (by norm_num))
  calc
    fixedL1MinimaxRisk n d / 16 ≤
        Causalean.Stat.worstCaseRisk (fixedL1Risk (d := d) n) sourceEst / 16 := by
      gcongr
    _ ≤ Causalean.Stat.worstCaseRisk
        (observedRisk n (d := d) (epsilon := epsilon)) est := by linarith

-- @node: prop:equal-propensity-l1-reduction
/-- If [the product experiment has the stated independent-sampling law](hyp:h_iid), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), then [the equal-propensity embedding transfers the paired-distribution L1 minimax lower bound to observed optimal-value estimation](goal). -/
theorem equal_propensity_l1_reduction {n d : ℕ} {epsilon : ℝ}
    (P0 : DiscreteLaw d) (mu_n : MeasureTheory.Measure (Fin n → Obs d))
    (h_iid : IidSampling P0 mu_n) (hd : 2 ≤ d)
    (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2) :
    ∀ Pv Qv : ProbabilitySimplex d,
      let P := observedMarginal (l1Embedding Pv Qv)
      ∃ hP : ObservedModelClass epsilon P,
      (∀ x, cellMass P x = (Pv.1 x + Qv.1 x) / 2) ∧
      (∀ x, 0 < cellMass P x → propensity P x = 1 / 2) ∧
      observedOptimalValue P hP = 1 / 2 + l1Distance Pv Qv / 4 ∧
      l1FixedSampleKernel n d ∘ₘ fixedPairLaw n (Pv, Qv) = productLaw P n ∧
      fixedL1MinimaxRisk n d / 16 ≤ minimaxRisk n d epsilon := by
  intro Pv Qv
  obtain ⟨hP, hcell, hprop, hvalue, hkernel⟩ :=
    l1Embedding_observed_reduction (n := n) hd hepsilon Pv Qv
  exact ⟨hP, hcell, hprop, hvalue, hkernel, l1_minimax_transfer hd hepsilon Pv Qv⟩

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

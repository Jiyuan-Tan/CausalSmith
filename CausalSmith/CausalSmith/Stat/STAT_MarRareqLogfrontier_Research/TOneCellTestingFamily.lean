module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TOneCellTestingRisk
public import Causalean.Stat.Minimax.HonestConfidenceSet
public import Causalean.Mathlib.MeasureTheory.IntegralBind

/-! Assembly of the one-cell testing family and its honest-interval consequence. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

private lemma oneCell_product_tv_le {n d : ℕ} (x : Fin d) (q z η : ℝ)
    (hn : 1 ≤ n) (hq : 0 < q) (hq1 : q ≤ 1)
    (hz : 0 ≤ z) (hz1 : z ≤ 1 / 2) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hbudget : 2 * effectiveSize n q * z ^ 2 ≤ η ^ 2 / 8) :
    Causalean.Stat.tvDist
        (sampleLaw n (oneCellFamilyLaw x (1 / 2) q (by norm_num) ⟨hq.le, hq1⟩))
        (sampleLaw n (oneCellFamilyLaw x (1 / 2 + z) q
          (by constructor <;> linarith) ⟨hq.le, hq1⟩)) ≤ η := by
  let L₀ := oneCellFamilyLaw x (1 / 2) q (by norm_num) ⟨hq.le, hq1⟩
  let L₁ := oneCellFamilyLaw x (1 / 2 + z) q
    (by constructor <;> linarith) ⟨hq.le, hq1⟩
  letI : IsProbabilityMeasure L₀.1 := L₀.2
  letI : IsProbabilityMeasure L₁.1 := L₁.2
  let P₀ := L₀.1.map obs
  let P₁ := L₁.1.map obs
  let Q₀ := Measure.pi (fun _ : Fin n => P₀)
  let Q₁ := Measure.pi (fun _ : Fin n => P₁)
  letI : IsProbabilityMeasure P₀ := by
    dsimp [P₀]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure P₁ := by
    dsimp [P₁]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure Q₀ := by dsimp [Q₀]; infer_instance
  letI : IsProbabilityMeasure Q₁ := by dsimp [Q₁]; infer_instance
  have hac : P₁ ≪ P₀ := oneCellFamilyLaw_obs_ac x (1 / 2 + z) q
    (by constructor <;> linarith) ⟨hq.le, hq1⟩
  have hacn : Q₁ ≪ Q₀ :=
    Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous
      P₁ P₀ hac n
  have hint : Integrable (fun s => ((Q₁.rnDeriv Q₀ s).toReal - 1) ^ 2) Q₀ :=
    Integrable.of_finite
  have hchi : Causalean.Stat.chiSqDiv P₁ P₀ = 2 * q * z ^ 2 := by
    dsimp [P₀, P₁, L₀, L₁]
    convert oneCellFamilyLaw_obs_chi x (1 / 2 + z) q
      (by constructor <;> linarith) ⟨hq.le, hq1⟩ using 1 <;> ring
  have hprod := Causalean.Stat.one_add_chiSqDiv_pi_iid_general P₁ P₀ hac
    (Integrable.of_finite : Integrable (fun y => ((P₁.rnDeriv P₀ y).toReal - 1) ^ 2) P₀) n
  have hpow : (1 + Causalean.Stat.chiSqDiv P₁ P₀) ^ n ≤
      Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv P₁ P₀) := by
    calc
      _ ≤ (Real.exp (Causalean.Stat.chiSqDiv P₁ P₀)) ^ n :=
        pow_le_pow_left₀ (by linarith [Causalean.Stat.chiSqDiv_nonneg (μ := P₁) (ν := P₀)])
          (by linarith [Real.add_one_le_exp (Causalean.Stat.chiSqDiv P₁ P₀)]) n
      _ = _ := by rw [← Real.exp_nat_mul]
  have hx : (n : ℝ) * Causalean.Stat.chiSqDiv P₁ P₀ ≤ η ^ 2 / 8 := by
    rw [hchi]
    unfold effectiveSize at hbudget
    nlinarith
  have hx0 : 0 ≤ (n : ℝ) * Causalean.Stat.chiSqDiv P₁ P₀ :=
    mul_nonneg (Nat.cast_nonneg _) Causalean.Stat.chiSqDiv_nonneg
  have hx1 : (n : ℝ) * Causalean.Stat.chiSqDiv P₁ P₀ < 1 := by
    nlinarith [sq_nonneg η]
  have hexp := Real.exp_bound_div_one_sub_of_interval hx0 hx1
  have hfrac : 1 / (1 - (n : ℝ) * Causalean.Stat.chiSqDiv P₁ P₀) - 1 ≤ η ^ 2 := by
    have hden : 0 < 1 - (n : ℝ) * Causalean.Stat.chiSqDiv P₁ P₀ := by linarith
    have hηsq : η ^ 2 ≤ 1 := by nlinarith
    have hmul : ((n : ℝ) * Causalean.Stat.chiSqDiv P₁ P₀) * η ^ 2 ≤
        (n : ℝ) * Causalean.Stat.chiSqDiv P₁ P₀ :=
      mul_le_of_le_one_right hx0 hηsq
    apply (sub_le_iff_le_add).2
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg η]
  have hchiQ : Causalean.Stat.chiSqDiv Q₁ Q₀ ≤ η ^ 2 := by
    change 1 + Causalean.Stat.chiSqDiv Q₁ Q₀ =
      (1 + Causalean.Stat.chiSqDiv P₁ P₀) ^ n at hprod
    linarith [hpow.trans hexp, hfrac]
  have htv := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv Q₁ Q₀ hacn hint
  have hsqrt : Real.sqrt (Causalean.Stat.chiSqDiv Q₁ Q₀) ≤ η := by
    have hs := Real.sqrt_le_sqrt hchiQ
    simpa [Real.sqrt_sq hη] using hs
  change Causalean.Stat.tvDist Q₀ Q₁ ≤ η
  rw [Causalean.Stat.tvDist_symm]
  exact htv.trans (by nlinarith)

private lemma connectedInterval_endpoint_measurable :
    Measurable (fun I : ConnectedInterval => I.lo) ∧
      Measurable (fun I : ConnectedInterval => I.hi) := by
  have hF : Measurable (fun I : ConnectedInterval =>
      (I.lo, I.hi, I.closedLeft, I.closedRight)) := by
    exact (measurable_fst.comp measurable_subtype_coe).prodMk
      ((measurable_snd.comp measurable_subtype_coe).prodMk
        (measurable_const.prodMk measurable_const))
  exact ⟨measurable_connectedInterval_lo,
    measurable_connectedInterval_hi⟩

private lemma measurableSet_intervalContains (t : ℝ) :
    MeasurableSet {I : ConnectedInterval | intervalContains I t} := by
  have hF : Measurable (fun I : ConnectedInterval =>
      (I.lo, I.hi, I.closedLeft, I.closedRight)) := by
    exact (measurable_fst.comp measurable_subtype_coe).prodMk
      ((measurable_snd.comp measurable_subtype_coe).prodMk
        (measurable_const.prodMk measurable_const))
  have hlo : Measurable (fun I : ConnectedInterval => I.lo) := measurable_connectedInterval_lo
  have hhi : Measurable (fun I : ConnectedInterval => I.hi) :=
    measurable_connectedInterval_hi
  have hleft : Measurable (fun I : ConnectedInterval => I.closedLeft) :=
    measurable_const
  have hright : Measurable (fun I : ConnectedInterval => I.closedRight) :=
    measurable_const
  unfold intervalContains
  have hseteq :
      {I : ConnectedInterval |
        (if I.closedLeft = true then I.lo ≤ t else I.lo < t) ∧
          (if I.closedRight = true then t ≤ I.hi else t < I.hi)} =
      (({I | I.closedLeft = true} ∩ {I | I.lo ≤ t}) ∪
          ({I | I.closedLeft = false} ∩ {I | I.lo < t})) ∩
        (({I | I.closedRight = true} ∩ {I | t ≤ I.hi}) ∪
          ({I | I.closedRight = false} ∩ {I | t < I.hi})) := by
    ext I
    by_cases hl : I.closedLeft = true <;>
      by_cases hr : I.closedRight = true <;> simp [hl, hr]
  rw [hseteq]
  measurability

private lemma measureReal_bind_eq_integral {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Kernel Ω β) [IsMarkovKernel K]
    (B : Set β) (hB : MeasurableSet B) :
    (K ∘ₘ μ).real B = ∫ x, (K x).real B ∂μ := by
  rw [measureReal_def, Measure.bind_apply hB K.aemeasurable, ←
    integral_toReal (K.measurable_coe hB).aemeasurable
      (Filter.Eventually.of_forall fun x =>
        (lt_top_iff_ne_top).2 (measure_ne_top (K x) B))]
  apply integral_congr_ae
  filter_upwards with x
  rw [Measure.real]

private lemma intervalRisk_bind_lintegral {n d : ℕ}
    (T : IntervalProcedure n d) (P : FullLaw d) :
    ENNReal.ofReal (intervalRisk T P) =
      ∫⁻ I : ConnectedInterval, ENNReal.ofReal (I.hi - I.lo) ∂(T.1 ∘ₘ sampleLaw n P) := by
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsProbabilityMeasure (P.1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (sampleLaw n P) := by unfold sampleLaw; infer_instance
  letI : IsMarkovKernel T.1 := T.2
  let μ := T.1 ∘ₘ sampleLaw n P
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hm := connectedInterval_endpoint_measurable
  have hlen : Measurable (fun I : ConnectedInterval => I.hi - I.lo) := hm.2.sub hm.1
  have hint : Integrable (fun I : ConnectedInterval => I.hi - I.lo) μ :=
    Integrable.of_bound hlen.aestronglyMeasurable 2
      (Filter.Eventually.of_forall fun I => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr I.ordered)]
        linarith [I.lower, I.upper])
  have heq : intervalRisk T P =
      ∫ I : ConnectedInterval, I.hi - I.lo ∂μ := by
    unfold intervalRisk μ
    exact (Causalean.Mathlib.MeasureTheory.integral_bind T.1.measurable hint).symm
  rw [heq, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun I => sub_nonneg.mpr I.ordered)]

-- @node: intervalRisk_bounds
/-- Given [the specified inputs and assumptions](hyp:n,d,T,P), [the stated mathematical conclusion holds](goal). -/
lemma intervalRisk_bounds {n d : ℕ} (T : IntervalProcedure n d) (P : FullLaw d) :
    0 ≤ intervalRisk T P ∧ intervalRisk T P ≤ 2 := by
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsProbabilityMeasure (P.1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (sampleLaw n P) := by unfold sampleLaw; infer_instance
  letI : IsMarkovKernel T.1 := T.2
  have hinner (s : Fin n → ObsRecord d) :
      0 ≤ ∫ I : ConnectedInterval, I.hi - I.lo ∂(T.1 s) ∧
      (∫ I : ConnectedInterval, I.hi - I.lo ∂(T.1 s)) ≤ 2 := by
    constructor
    · exact integral_nonneg (fun I => sub_nonneg.mpr I.ordered)
    · have hb : ∀ I : ConnectedInterval, I.hi - I.lo ≤ 2 := by
        intro I
        linarith [I.lower, I.upper]
      simpa using integral_mono_of_nonneg (μ := T.1 s)
        (Filter.Eventually.of_forall (fun I => sub_nonneg.mpr I.ordered))
        (integrable_const (2 : ℝ)) (Filter.Eventually.of_forall hb)
  unfold intervalRisk
  constructor
  · exact integral_nonneg (fun s => (hinner s).1)
  · simpa using integral_mono_of_nonneg (μ := sampleLaw n P)
      (Filter.Eventually.of_forall (fun s => (hinner s).1))
      (integrable_const (2 : ℝ))
      (Filter.Eventually.of_forall (fun s => (hinner s).2))

/-- Given [the specified inputs and assumptions](hyp:n,d,q,α,hn,hd,hq,hq1,hslice,hα,hα1), [the stated mathematical conclusion holds](goal). -/
lemma oneCell_interval_minimax_floor {n d : ℕ} (q α : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1)
    (hslice : RareArrivalSlice n q) (hα : 0 < α) (hα1 : α < 1) :
    ∃ (M : ℕ) (grid : Fin (M + 1) → ℝ),
      0 < M ∧ Function.Injective grid ∧
      (∀ i, grid i ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ)) ∧
      (∀ (I : IntervalProcedure n d), HonestInterval n d q α I →
        (3 * (1 - α) ^ 2 / 512) * min 1 (Real.sqrt (effectiveSize n q))⁻¹ ≤
          ⨆ i, intervalRisk I
            (oneCellFamilyLaw (⟨0, hd⟩ : Fin d) (max 0 (min 1 (grid i))) q
              ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
              ⟨hq.le, hq1⟩)) ∧
      (3 * (1 - α) ^ 2 / 512) *
          min 1 (Real.sqrt (effectiveSize n q))⁻¹ ≤ intervalLengthRisk n d q α := by
  let η := (1 - α) / 8
  have hη : 0 < η := by dsimp [η]; linarith
  have hη1 : η ≤ 1 := by dsimp [η]; linarith
  obtain ⟨M, hMlarge⟩ := exists_nat_ge (8 / (1 - α) : ℝ)
  have hM : 0 < M := by
    have : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hMlarge
    exact_mod_cast this
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hN : 0 < effectiveSize n q := by unfold effectiveSize; positivity
  have hsqrt : 0 < Real.sqrt (effectiveSize n q) := Real.sqrt_pos.2 hN
  let w := min (1 / 4 : ℝ) (η / (4 * Real.sqrt (effectiveSize n q)))
  have hw : 0 < w := by dsimp [w]; exact lt_min (by norm_num) (by positivity)
  have hwle : w ≤ 1 / 4 := by dsimp [w]; exact min_le_left _ _
  have hwbudget : 2 * effectiveSize n q * w ^ 2 ≤ η ^ 2 / 8 := by
    have hle : w ≤ η / (4 * Real.sqrt (effectiveSize n q)) := by
      dsimp [w]; exact min_le_right _ _
    have hsquare : w ^ 2 ≤ (η / (4 * Real.sqrt (effectiveSize n q))) ^ 2 := by
      nlinarith
    have hsqrt_sq : (Real.sqrt (effectiveSize n q)) ^ 2 = effectiveSize n q :=
      Real.sq_sqrt hN.le
    rw [div_pow, mul_pow, hsqrt_sq] at hsquare
    field_simp [ne_of_gt hN] at hsquare ⊢
    nlinarith
  let δ := w / M
  let grid : Fin (M + 1) → ℝ := fun j => 1 / 2 + (j : ℝ) * δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hgrid_inj : Function.Injective grid := by
    intro i j hij
    have hcast : (i : ℝ) = (j : ℝ) := by
      dsimp [grid] at hij
      have := mul_right_cancel₀ (ne_of_gt hδ) (sub_eq_zero.mp (by linarith :
        (i : ℝ) * δ - (j : ℝ) * δ = 0))
      exact this
    exact Fin.ext (by exact_mod_cast hcast)
  have hgrid_mem : ∀ i, grid i ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
    intro i
    have hi : (i : ℝ) ≤ M := by exact_mod_cast (Nat.lt_succ_iff.mp i.isLt)
    have hiz : 0 ≤ (i : ℝ) := by positivity
    have hterm0 : 0 ≤ (i : ℝ) * δ := mul_nonneg hiz hδ.le
    have hterm1 : (i : ℝ) * δ ≤ w := by
      rw [show (i : ℝ) * δ = ((i : ℝ) * w) / M by dsimp [δ]; ring]
      apply (div_le_iff₀ hMr).2
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hi hw.le
    dsimp [grid]
    constructor <;> linarith
  refine ⟨M, grid, hM, hgrid_inj, hgrid_mem, ?_⟩
  let x : Fin d := ⟨0, hd⟩
  let P₀ := oneCellFamilyLaw x (1 / 2) q (by norm_num) ⟨hq.le, hq1⟩
  have hP₀ : RareArrivalModelClass n d q P₀ :=
    oneCellFamilyLaw_model x (1 / 2) q hn hd (by norm_num) hq hq1 hslice
  have hwscale : (η / 4) * min 1 (Real.sqrt (effectiveSize n q))⁻¹ ≤ w := by
    dsimp [w]
    by_cases hc : (1 / 4 : ℝ) ≤ η / (4 * Real.sqrt (effectiveSize n q))
    · rw [min_eq_left hc]
      have hm : min 1 (Real.sqrt (effectiveSize n q))⁻¹ ≤ 1 := min_le_left _ _
      have : η / 4 ≤ 1 / 4 := by linarith
      nlinarith [mul_nonneg hη.le (show 0 ≤ min 1 (Real.sqrt (effectiveSize n q))⁻¹ by
        exact le_min (by norm_num) (by positivity))]
    · rw [min_eq_right (le_of_not_ge hc)]
      have hm : min 1 (Real.sqrt (effectiveSize n q))⁻¹ ≤
          (Real.sqrt (effectiveSize n q))⁻¹ := min_le_right _ _
      calc
        η / 4 * min 1 (Real.sqrt (effectiveSize n q))⁻¹ ≤
            η / 4 * (Real.sqrt (effectiveSize n q))⁻¹ :=
          mul_le_mul_of_nonneg_left hm (by positivity)
        _ = η / (4 * Real.sqrt (effectiveSize n q)) := by ring
  have hproc : ∀ H : {T : IntervalProcedure n d // HonestInterval n d q α T},
      (3 * (1 - α) / 4) * w ≤ intervalRisk H.1 P₀ := by
    intro H
    have hgrid_unit (j : Fin (M + 1)) : 0 ≤ grid j ∧ grid j ≤ 1 := by
      rcases hgrid_mem j with ⟨hj0, hj1⟩
      constructor <;> linarith
    let P : Fin (M + 1) → FullLaw d := fun j =>
      oneCellFamilyLaw x (grid j) q (hgrid_unit j) ⟨hq.le, hq1⟩
    have hP (j : Fin (M + 1)) : RareArrivalModelClass n d q (P j) :=
      oneCellFamilyLaw_model x (grid j) q hn hd (hgrid_unit j) hq hq1 hslice
    let μ₀ := H.1.1 ∘ₘ sampleLaw n P₀
    let μ : Fin (M + 1) → Measure ConnectedInterval := fun j =>
      H.1.1 ∘ₘ sampleLaw n (P j)
    letI : IsMarkovKernel H.1.1 := H.1.2
    letI : IsProbabilityMeasure P₀.1 := P₀.2
    letI : IsProbabilityMeasure (P₀.1.map obs) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    letI : IsProbabilityMeasure (sampleLaw n P₀) := by unfold sampleLaw; infer_instance
    letI : IsProbabilityMeasure μ₀ := by dsimp [μ₀]; infer_instance
    letI (j : Fin (M + 1)) : IsProbabilityMeasure (P j).1 := (P j).2
    letI (j : Fin (M + 1)) : IsProbabilityMeasure ((P j).1.map obs) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    letI (j : Fin (M + 1)) : IsProbabilityMeasure (sampleLaw n (P j)) := by
      unfold sampleLaw; infer_instance
    letI (j : Fin (M + 1)) : IsProbabilityMeasure (μ j) := by dsimp [μ]; infer_instance
    have hm := connectedInterval_endpoint_measurable
    have hhonest : ∀ j,
        1 - α ≤ (μ j).real
          (Causalean.Stat.coverageEvent
            (fun I : ConnectedInterval => I.lo) (fun I => I.hi)
            (Causalean.Stat.gridPoint (M := M)
              (1 / 2) δ j)) := by
      intro j
      have hpoint : Causalean.Stat.gridPoint
          (M := M) (1 / 2) δ j = grid j := by
        simp [Causalean.Stat.gridPoint, grid, mul_comm]
      rw [hpoint]
      have hsub : {I : ConnectedInterval | intervalContains I (grid j)} ⊆
          Causalean.Stat.coverageEvent
            (fun I : ConnectedInterval => I.lo) (fun I => I.hi) (grid j) := by
        intro I hI
        cases hl : I.closedLeft <;> cases hr : I.closedRight <;>
          simp [intervalContains, Causalean.Stat.coverageEvent,
            hl, hr] at hI ⊢ <;> constructor <;> linarith
      rw [measureReal_bind_eq_integral (sampleLaw n (P j)) H.1.1 _
        (Causalean.Stat.measurableSet_coverageEvent
          hm.1 hm.2)]
      calc
        1 - α ≤ ∫ s, (H.1.1 s).real {I | intervalContains I (ate (P j))}
            ∂(sampleLaw n (P j)) := H.2 (P j) (hP j)
        _ = ∫ s, (H.1.1 s).real {I | intervalContains I (grid j)}
            ∂(sampleLaw n (P j)) := by rw [oneCellFamilyLaw_ate]
        _ ≤ ∫ s, (H.1.1 s).real
            (Causalean.Stat.coverageEvent
              (fun I : ConnectedInterval => I.lo) (fun I => I.hi) (grid j))
            ∂(sampleLaw n (P j)) := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun _ => measureReal_nonneg)
          · exact Integrable.of_bound
              (H.1.1.measurable_coe
                (Causalean.Stat.measurableSet_coverageEvent
                  hm.1 hm.2)).ennreal_toReal.aestronglyMeasurable 1
              (Filter.Eventually.of_forall fun s => by
                rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
                exact measureReal_le_one)
          · exact Filter.Eventually.of_forall (fun _ => measureReal_mono hsub)
    have htv : ∀ j, Causalean.Stat.tvDist μ₀ (μ j) ≤ η := by
      intro j
      have hj : (j : ℝ) * δ ≤ w := by
        have hi : (j : ℝ) ≤ M := by exact_mod_cast (Nat.lt_succ_iff.mp j.isLt)
        rw [show (j : ℝ) * δ = ((j : ℝ) * w) / M by dsimp [δ]; ring]
        apply (div_le_iff₀ hMr).2
        simpa [mul_comm] using mul_le_mul_of_nonneg_right hi hw.le
      have hz0 : 0 ≤ (j : ℝ) * δ := by positivity
      have hz1 : (j : ℝ) * δ ≤ 1 / 2 := hj.trans (by linarith)
      have hb : 2 * effectiveSize n q * ((j : ℝ) * δ) ^ 2 ≤ η ^ 2 / 8 := by
        have hsq : ((j : ℝ) * δ) ^ 2 ≤ w ^ 2 := by nlinarith
        exact (mul_le_mul_of_nonneg_left hsq (by positivity)).trans hwbudget
      exact (Causalean.Stat.tvDist_bind_le (sampleLaw n P₀) (sampleLaw n (P j)) H.1.1).trans
        (by
          dsimp [P, P₀, grid]
          simpa [δ, mul_comm] using
            oneCell_product_tv_le x q ((j : ℝ) * δ) η hn hq hq1 hz0 hz1 hη.le hη1 hb)
    have hgeneric :=
      Causalean.Stat.honest_interval_length_lower_of_grid_tv_positive
        μ₀ M μ (1 / 2) δ α η hm.1 hm.2 hδ hα hα1 hMlarge (le_rfl)
        hhonest htv
    have hwidth : (M : ℝ) * δ = w := by
      dsimp [δ]
      field_simp [ne_of_gt hMr]
    have hrisk0 := (intervalRisk_bounds H.1 P₀).1
    have hreal : (3 * (1 - α) / 4) * ((M : ℝ) * δ) ≤ intervalRisk H.1 P₀ := by
      rw [← ENNReal.ofReal_le_ofReal_iff hrisk0]
      rw [intervalRisk_bind_lintegral]
      simpa [μ₀, Causalean.Stat.intervalLength,
        max_eq_right] using hgeneric.2.1
    simpa [hwidth] using hreal
  let Iall : ConnectedInterval := ⟨(-1, 1), by norm_num, by norm_num, by norm_num⟩
  let Tall : IntervalProcedure n d :=
    ⟨Kernel.const _ (Measure.dirac Iall), inferInstance⟩
  have hTall : HonestInterval n d q α Tall := by
    intro P hP
    letI : IsProbabilityMeasure P.1 := P.2
    letI : IsProbabilityMeasure (P.1.map obs) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    letI : IsProbabilityMeasure (sampleLaw n P) := by unfold sampleLaw; infer_instance
    rcases ate_mem_unit_interval P with ⟨hATE0, hATE1⟩
    have heq (s : Fin n → ObsRecord d) :
        (Tall.1 s).real {I | intervalContains I (ate P)} = 1 := by
      rw [Kernel.const_apply, Measure.real,
        Measure.dirac_apply' _ (measurableSet_intervalContains (ate P))]
      have hmem : Iall ∈ {I : ConnectedInterval | intervalContains I (ate P)} :=
        ⟨hATE0, hATE1⟩
      rw [Set.indicator_of_mem hmem]
      norm_num
    simp_rw [heq]
    simp
    linarith
  let HAll : {T : IntervalProcedure n d // HonestInterval n d q α T} := ⟨Tall, hTall⟩
  letI : Nonempty {T : IntervalProcedure n d // HonestInterval n d q α T} := ⟨HAll⟩
  let θ₀ : {P : FullLaw d // RareArrivalModelClass n d q P} := ⟨P₀, hP₀⟩
  unfold intervalLengthRisk
  have hmin : (3 * (1 - α) / 4) * w ≤
      Causalean.Stat.minimaxValueReal
        (fun (T : {T : IntervalProcedure n d // HonestInterval n d q α T})
          (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
            intervalRisk T.1 P.1) :=
    Causalean.Stat.le_minimaxValue (fun H =>
      (hproc H).trans (Causalean.Stat.le_worstCaseRisk
        (risk := fun
          (T : {T : IntervalProcedure n d // HonestInterval n d q α T})
          (P : {P : FullLaw d // RareArrivalModelClass n d q P}) =>
            intervalRisk T.1 P.1)
        (by
          show BddAbove (Set.range (fun
            P : {P : FullLaw d // RareArrivalModelClass n d q P} => intervalRisk H.1 P.1))
          refine ⟨2, ?_⟩
          rintro _ ⟨P, rfl⟩
          exact (intervalRisk_bounds H.1 P).2)
        θ₀))
  have hscale : (3 * (1 - α) ^ 2 / 512) *
      min 1 (Real.sqrt (effectiveSize n q))⁻¹ ≤ (3 * (1 - α) / 4) * w := by
    have hcoeff : 0 ≤ 3 * (1 - α) / 4 := by positivity
    have h := mul_le_mul_of_nonneg_left hwscale hcoeff
    dsimp [η] at h
    nlinarith [mul_nonneg (sq_nonneg (1 - α))
      (show 0 ≤ min 1 (Real.sqrt (effectiveSize n q))⁻¹ by
        exact le_min (by norm_num) (by positivity))]
  constructor
  · intro I hI
    apply le_trans (hscale.trans (hproc ⟨I, hI⟩))
    refine le_ciSup_of_le ?_ (0 : Fin (M + 1)) ?_
    · refine ⟨2, ?_⟩
      rintro _ ⟨i, rfl⟩
      exact (intervalRisk_bounds I _).2
    · norm_num [grid, P₀, x]
  · exact hscale.trans hmin

-- @node: lem:one-cell-testing-family
/-- [the stated mathematical conclusion holds](goal). -/
lemma one_cell_testing_family :
    ∃ (c : ℝ) (cInterval : ℝ → ℝ),
      0 < c ∧ (∀ α : ℝ, 0 < α → α < 1 → 0 < cInterval α) ∧
      ∀ (n d : ℕ) (q : ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d),
        0 < q → q ≤ 1 → RareArrivalSlice n q →
        ∃ bernoulliFamily : ℝ → FullLaw d,
          (∀ u ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ),
            RareArrivalModelClass n d q (bernoulliFamily u) ∧
            (∀ᵐ r : FullRecord d ∂((bernoulliFamily u).1),
              r.X = (⟨0, hd⟩ : Fin d) ∧
              r.S0 = false ∧ r.S1 = false ∧ r.Y0 = false) ∧
            (bernoulliFamily u).1.real {r | r.R = true} = q ∧
            ate (bernoulliFamily u) = u) ∧
          (∃ u₀ ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ),
            ∃ u₁ ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ),
              u₀ ≠ u₁ ∧
              (∀ T : Estimator n d,
                c * min 1 (effectiveSize n q)⁻¹ ≤
                  max (squaredRisk T (bernoulliFamily u₀))
                    (squaredRisk T (bernoulliFamily u₁))) ∧
              c * min 1 (effectiveSize n q)⁻¹ ≤ minimaxRisk n d q) ∧
          ∀ α : ℝ, 0 < α → α < 1 →
            ∃ (M : ℕ) (grid : Fin (M + 1) → ℝ),
              0 < M ∧ Function.Injective grid ∧
              (∀ i, grid i ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ)) ∧
              (∀ (I : IntervalProcedure n d), HonestInterval n d q α I →
                cInterval α * min 1 (Real.sqrt (effectiveSize n q))⁻¹ ≤
                  ⨆ i, intervalRisk I (bernoulliFamily (grid i))) ∧
              cInterval α * min 1 (Real.sqrt (effectiveSize n q))⁻¹ ≤
                intervalLengthRisk n d q α := by
  refine ⟨1 / 256, fun α => 3 * (1 - α) ^ 2 / 512, by norm_num, ?_, ?_⟩
  · intro α hα hα1
    positivity
  · intro n d q hn hd hq hq1 hslice
    let x : Fin d := ⟨0, hd⟩
    let clamp : ℝ → ℝ := fun u => max 0 (min 1 u)
    have hclamp_mem (u : ℝ) : 0 ≤ clamp u ∧ clamp u ≤ 1 := by
      dsimp [clamp]
      exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
    let family : ℝ → FullLaw d := fun u =>
      oneCellFamilyLaw x (clamp u) q (hclamp_mem u) ⟨hq.le, hq1⟩
    refine ⟨family, ?_, ?_, ?_⟩
    · intro u hu
      have hu0 : 0 ≤ u := by linarith [hu.1]
      have hu1 : u ≤ 1 := by linarith [hu.2]
      have hclamp : clamp u = u := by simp [clamp, min_eq_right hu1, max_eq_right hu0]
      simpa [family, hclamp] using
        (⟨oneCellFamilyLaw_model x u q hn hd ⟨hu0, hu1⟩ hq hq1 hslice,
        oneCellFamilyLaw_support x u q ⟨hu0, hu1⟩ ⟨hq.le, hq1⟩,
        oneCellFamilyLaw_arrival_mass x u q ⟨hu0, hu1⟩ ⟨hq.le, hq1⟩,
        oneCellFamilyLaw_ate x u q ⟨hu0, hu1⟩ ⟨hq.le, hq1⟩⟩ :
          RareArrivalModelClass n d q
              (oneCellFamilyLaw x u q ⟨hu0, hu1⟩ ⟨hq.le, hq1⟩) ∧
            (∀ᵐ r : FullRecord d ∂((oneCellFamilyLaw x u q ⟨hu0, hu1⟩
                ⟨hq.le, hq1⟩).1),
              r.X = x ∧ r.S0 = false ∧ r.S1 = false ∧ r.Y0 = false) ∧
            (oneCellFamilyLaw x u q ⟨hu0, hu1⟩ ⟨hq.le, hq1⟩).1.real
              {r | r.R = true} = q ∧
            ate (oneCellFamilyLaw x u q ⟨hu0, hu1⟩ ⟨hq.le, hq1⟩) = u)
    · have hrisk := oneCell_minimax_risk_floors q hn hd hq hq1 hslice
      have hstep := oneCellStep_pos n q hn hq
      have hstep_le := oneCellStep_le_quarter n q
      have hu₁ : (1 / 2 : ℝ) + oneCellStep n q ∈ Set.Icc (1 / 4) (3 / 4) := by
        constructor <;> linarith
      refine ⟨1 / 2, by norm_num, 1 / 2 + oneCellStep n q, hu₁,
        by linarith, ?_, hrisk.1⟩
      have hclamp₀ : clamp (1 / 2) = 1 / 2 := by norm_num [clamp]
      have hclamp₁ : clamp (1 / 2 + oneCellStep n q) = 1 / 2 + oneCellStep n q := by
        dsimp [clamp]
        rw [min_eq_right (by linarith : (1 / 2 : ℝ) + oneCellStep n q ≤ 1),
          max_eq_right (by linarith : (0 : ℝ) ≤ 1 / 2 + oneCellStep n q)]
      simpa only [family, hclamp₀, hclamp₁] using oneCell_two_point_risk_floor x q hn hq hq1
    · intro α hα hα1
      simpa [family, clamp, x] using
        oneCell_interval_minimax_floor q α hn hd hq hq1 hslice hα hα1

end CausalSmith.Stat.MarRareqLogfrontier

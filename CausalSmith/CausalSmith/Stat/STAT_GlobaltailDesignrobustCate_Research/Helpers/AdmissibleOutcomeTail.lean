module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CountAdmissibility
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.T_FiniteBandwidth

/-! # Outcome tails restricted to count admissibility

The conditional-product cell tail can be averaged while retaining the
count-only admissibility event. A cell union and the half-tilt split give
the probabilistic part of adaptation roadmap (7)--(8).
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped ENNReal BigOperators

/-- Admissibility is constant when only the observed outcomes change. -/
-- @node: selectorAdmissible_congr_design
lemma selectorAdmissible_congr_design {d n : ℕ} (s s' : Fin n → Obs d)
    (hX : ∀ i, (s' i).1 = (s i).1) (hA : ∀ i, (s' i).2.1 = (s i).2.1)
    (j : ℕ) (β : ℝ) :
    selectorAdmissible s' j β ↔ selectorAdmissible s j β := by
  simp only [selectorAdmissible_iff_minimumCount,
    minimumCellCount_congr_design s s' hX hA]

/-- Averaging the actual conditional outcome tail retains the admissibility
indicator in its count Laplace transform, as required in roadmap (7). -/
-- @node: balancedEstimator_admissible_cell_laplace
lemma balancedEstimator_admissible_cell_laplace (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B : ℝ, 0 < B ∧ ∀ (n j : ℕ) (P : Law d),
      LawClass d β γ C L M P → 0 < n →
      ∀ (Q : Fin d → Fin (2 ^ j)) (t : ℝ), 0 ≤ t →
        (P.sample n).real {sample | selectorAdmissible sample j β ∧
          ∃ x ∈ cube d, cellIndex d j x = Q ∧
            B * L * (dyadicWidth j) ^ β + t <
              |balancedEstimator sample j β M x - P.mu1 x|} ≤
          (2 * (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ)) *
            (∫ sample, {sample | selectorAdmissible sample j β}.indicator
              (fun sample => Real.exp (-(referenceLowerEigenvalue d (polynomialOrder β) ^ 2 /
                (32 * (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ)) * t ^ 2 / M ^ 2) *
                  (minimumCellCount sample true j (polynomialOrder β)
                    (normingSubcells d β).radius Q : ℝ))) sample ∂P.sample n) := by
  classical
  obtain ⟨B, hB, hfiber⟩ := treated_balancedEstimator_productFiber_cell_tail
    d β γ C L M hparam
  refine ⟨B, hB, ?_⟩
  intro n j P hP hn Q t ht
  let : IsProbabilityMeasure P.full := hP.iid.1
  let : IsProbabilityMeasure (P.full.map (fun u : Full d => (u.1, u.2.1))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let μ := Measure.pi (fun _ : Fin n =>
    P.full.map (fun u : Full d => (u.1, u.2.1)))
  let S := fun (design : Fin n → (Fin d → ℝ) × Bool) i =>
    ((design i).1, (design i).2, (0 : ℝ))
  let A := {design | selectorAdmissible (S design) j β}
  let R : ℝ := Fintype.card (MultiIndex d (polynomialOrder β))
  let c : ℝ := referenceLowerEigenvalue d (polynomialOrder β) ^ 2 / (32 * R)
  let N := fun design => minimumCellCount (S design) true j (polynomialOrder β)
    (normingSubcells d β).radius Q
  let f := fun design => Real.exp (-(c * t ^ 2 / M ^ 2) * (N design : ℝ))
  have hA : MeasurableSet A :=
    (selectorAdmissible_measurableSet d n j β).preimage (by dsimp [S]; fun_prop)
  have hf : Measurable f := by dsimp [f, N, S]; fun_prop
  have hfi : Integrable f μ := by
    apply Integrable.of_mem_Icc 0 1 hf.aemeasurable
    apply ae_of_all
    intro design
    refine ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr ?_⟩
    have hcn : 0 ≤ c * t ^ 2 / M ^ 2 := by dsimp [c]; positivity
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcn) (Nat.cast_nonneg _)
  have hg : Integrable (fun design => (2 * R) * A.indicator f design) μ :=
    (hfi.indicator hA).const_mul _
  have hgmeas : Measurable (fun design => (2 * R) * A.indicator f design) := by
    fun_prop
  have hb : 0 ≤ B * L * (dyadicWidth j) ^ β + t := by
    have hL := hparam.2.2.2.2.1
    have hh := (dyadicWidth_mem_Ioc j).1
    positivity
  have hE := (selectorAdmissible_measurableSet d n j β).inter
    (balancedEstimator_cellEvent_measurableSet j β M _ hb P.mu1
      (holderOnCube_continuousOn hparam.2.1 hP.treatedHolder) Q)
  have havg := sample_real_event_le_conditionalFiber_integral P hP.iid
    hP.consistency hn _ hE _ hg (by
      filter_upwards [hfiber P hP n j] with design hd
      have hcongr (y : Fin n → ℝ) :
          selectorAdmissible (fun i => ((design i).1, (design i).2, y i)) j β ↔
            selectorAdmissible (S design) j β :=
        selectorAdmissible_congr_design (S design) _ (fun _ => rfl) (fun _ => rfl) j β
      by_cases ha : design ∈ A
      · have heq : {y : Fin n → ℝ |
            selectorAdmissible (fun i => ((design i).1, (design i).2, y i)) j β ∧
            ∃ x ∈ cube d, cellIndex d j x = Q ∧
              B * L * (dyadicWidth j) ^ β + t <
                |balancedEstimator (fun i => ((design i).1, (design i).2, y i)) j β M x - P.mu1 x|} =
            {y | ∃ x ∈ cube d, cellIndex d j x = Q ∧
              B * L * (dyadicWidth j) ^ β + t <
                |balancedEstimator (fun i => ((design i).1, (design i).2, y i)) j β M x - P.mu1 x|} := by
          ext y
          simp only [Set.mem_setOf_eq, hcongr y, show selectorAdmissible (S design) j β from ha,
            true_and]
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        rw [heq, Set.indicator_of_mem ha]
        convert hd Q t ht using 1 <;> dsimp [f, N, S, c, R]
        congr 2
        ring
      · have heq : {y : Fin n → ℝ |
            selectorAdmissible (fun i => ((design i).1, (design i).2, y i)) j β ∧
            ∃ x ∈ cube d, cellIndex d j x = Q ∧
              B * L * (dyadicWidth j) ^ β + t <
                |balancedEstimator (fun i => ((design i).1, (design i).2, y i)) j β M x - P.mu1 x|} = ∅ := by
          ext y
          simp only [Set.mem_setOf_eq, hcongr y,
            show ¬ selectorAdmissible (S design) j β from ha, false_and, Set.mem_empty_iff_false]
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        rw [heq, Set.indicator_of_notMem ha, mul_zero, measureReal_empty])
  apply havg.trans_eq
  rw [sample_design_integral_eq P hP.iid hP.consistency hn _ hgmeas, integral_const_mul]
  congr 1

/-- A union over the actual fitted cells followed by the admissible-count
half-tilt split proves roadmap (8) before ranking the cell masses. -/
-- @node: balancedEstimator_admissible_global_tail
lemma balancedEstimator_admissible_global_tail (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ (n j : ℕ) (P : Law d),
      LawClass d β γ C L M P → 0 < n → ∀ t : ℝ, 0 ≤ t →
        (P.sample n).real {sample | selectorAdmissible sample j β ∧
          ENNReal.ofReal (B * L * (dyadicWidth j) ^ β + t) <
            supLoss (balancedEstimator sample j β M) P.mu1} ≤
          (2 * (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) ^ 2) *
            Real.exp (-(c * t ^ 2 / M ^ 2) * (selectorThreshold j β : ℝ) / 2) *
              ∑ Q : Fin d → Fin (2 ^ j), Real.exp (-(n : ℝ) *
                minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q *
                  (1 - Real.exp (-(c * t ^ 2 / M ^ 2 / 2)))) := by
  classical
  obtain ⟨B, hB, hcell⟩ := balancedEstimator_admissible_cell_laplace
    d β γ C L M hparam
  let R : ℝ := Fintype.card (MultiIndex d (polynomialOrder β))
  let c : ℝ := referenceLowerEigenvalue d (polynomialOrder β) ^ 2 / (32 * R)
  have hR : 0 < R := by dsimp [R]; exact_mod_cast Fintype.card_pos
  have hc : 0 < c := by
    have hlam := referenceLowerEigenvalue_pos d (polynomialOrder β)
    dsimp [c]; positivity
  refine ⟨B, c, hB, hc, ?_⟩
  intro n j P hP hn t ht
  letI : IsProbabilityMeasure (P.sample n) :=
    sample_isProbabilityMeasure P hP.iid hP.consistency hn
  let s : ℝ := c * t ^ 2 / M ^ 2
  let E : ℝ := Real.exp (-s * (selectorThreshold j β : ℝ) / 2)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hb : 0 ≤ B * L * (dyadicWidth j) ^ β + t := by
    have hL := hparam.2.2.2.2.1
    have hh := (dyadicWidth_mem_Ioc j).1
    positivity
  have heq : {sample : Fin n → Obs d | selectorAdmissible sample j β ∧
      ENNReal.ofReal (B * L * (dyadicWidth j) ^ β + t) <
        supLoss (balancedEstimator sample j β M) P.mu1} =
      ⋃ Q : Fin d → Fin (2 ^ j), {sample | selectorAdmissible sample j β ∧
        ∃ x ∈ cube d, cellIndex d j x = Q ∧
          B * L * (dyadicWidth j) ^ β + t <
            |balancedEstimator sample j β M x - P.mu1 x|} := by
    have h := supLoss_event_eq_cellUnion
      (fun sample : Fin n → Obs d => balancedEstimator sample j β M) P.mu1 j _ hb
    ext sample
    have hmem := Set.ext_iff.mp h sample
    simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hmem ⊢
    rw [hmem]
    constructor
    · rintro ⟨ha, Q, hx⟩
      exact ⟨Q, ha, hx⟩
    · rintro ⟨Q, ha, hx⟩
      exact ⟨ha, Q, hx⟩
  rw [heq]
  calc
    _ ≤ ∑ Q : Fin d → Fin (2 ^ j), (P.sample n).real
        {sample | selectorAdmissible sample j β ∧
          ∃ x ∈ cube d, cellIndex d j x = Q ∧
            B * L * (dyadicWidth j) ^ β + t <
              |balancedEstimator sample j β M x - P.mu1 x|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ Q : Fin d → Fin (2 ^ j),
        (2 * R) * (E * (R * Real.exp (-(n : ℝ) *
          minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q *
            (1 - Real.exp (-(s / 2)))))) := by
      apply Finset.sum_le_sum
      intro Q _
      apply (hcell n j P hP hn Q t ht).trans
      exact mul_le_mul_of_nonneg_left
        (admissible_count_laplace_split P β γ C L M hP hn j Q s hs) (by positivity)
    _ = _ := by
      change _ = (2 * R ^ 2) * E * ∑ Q : Fin d → Fin (2 ^ j),
        Real.exp (-(n : ℝ) * minimumTreatedMass P j (polynomialOrder β)
          (normingSubcells d β).radius Q * (1 - Real.exp (-(s / 2))))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q _
      ring

/-- On a specified selected-level event, the adaptive fit is the balanced
fit at that level; the empty-set fallback cannot occur on this event. -/
-- @node: selectorHandle_eq_of_selectedLevel
lemma selectorHandle_eq_of_selectedLevel {d n : ℕ} (sample : Fin n → Obs d)
    (β M : ℝ) (j : ℕ)
    (hsel : ∃ h : (admissibleLevels sample β).Nonempty,
      (admissibleLevels sample β).max' h = j) :
    selectorHandle sample β M = balancedEstimator sample j β M := by
  obtain ⟨h, hj⟩ := hsel
  funext x
  unfold selectorHandle
  rw [dif_pos h, hj]

/-- The selector's actual outcome loss on each selected-level event obeys
the admissibility-weighted tail, retaining the threshold exponential needed
to sum over finer levels without a logarithm. -/
-- @node: selectorHandle_selectedLevel_tail
lemma selectorHandle_selectedLevel_tail (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ (n j : ℕ) (P : Law d),
      LawClass d β γ C L M P → 0 < n → ∀ t : ℝ, 0 ≤ t →
        (P.sample n).real {sample |
          (∃ h : (admissibleLevels sample β).Nonempty,
            (admissibleLevels sample β).max' h = j) ∧
          ENNReal.ofReal (B * L * (dyadicWidth j) ^ β + t) <
            supLoss (selectorHandle sample β M) P.mu1} ≤
          (2 * (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) ^ 2) *
            Real.exp (-(c * t ^ 2 / M ^ 2) * (selectorThreshold j β : ℝ) / 2) *
              ∑ Q : Fin d → Fin (2 ^ j), Real.exp (-(n : ℝ) *
                minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q *
                  (1 - Real.exp (-(c * t ^ 2 / M ^ 2 / 2)))) := by
  obtain ⟨B, c, hB, hc, htail⟩ := balancedEstimator_admissible_global_tail
    d β γ C L M hparam
  refine ⟨B, c, hB, hc, ?_⟩
  intro n j P hP hn t ht
  letI : IsProbabilityMeasure (P.sample n) :=
    sample_isProbabilityMeasure P hP.iid hP.consistency hn
  apply le_trans (measureReal_mono (h₂ := measure_ne_top (P.sample n) _) ?_)
    (htail n j P hP hn t ht)
  intro sample hs
  obtain ⟨hsel, hloss⟩ := hs
  have heq := selectorHandle_eq_of_selectedLevel sample β M j hsel
  obtain ⟨h, hj⟩ := hsel
  have ha := (selectedLevel_admissible sample β h).2
  rw [hj] at ha
  exact ⟨ha, by simpa only [heq] using hloss⟩

end CausalSmith.Stat.GlobalTailDesignRobustCate

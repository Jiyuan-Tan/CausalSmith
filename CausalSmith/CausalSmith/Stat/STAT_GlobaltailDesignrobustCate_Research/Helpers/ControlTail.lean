module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.ControlResiduals
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.T_FiniteBandwidth

/-! # Unconditional control estimator tails

Roadmap (C16): average the identified conditional control tails against the
minimum-count Laplace transform, then take the finite union over dyadic cells.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory
open scoped ENNReal BigOperators

/-- A control cell exceedance is measurable for a continuous target. -/
-- @node: controlBalancedEstimator_cellEvent_measurableSet
lemma controlBalancedEstimator_cellEvent_measurableSet {d n : ℕ} (j : ℕ) (β M b : ℝ)
    (hb : 0 ≤ b) (g : (Fin d → ℝ) → ℝ) (hg : ContinuousOn g (cube d))
    (Q : Fin d → Fin (2 ^ j)) :
    MeasurableSet {sample : Fin n → Obs d | ∃ x ∈ cube d,
      cellIndex d j x = Q ∧ b < |controlBalancedEstimator sample j β M x - g x|} := by
  have heq : {sample : Fin n → Obs d | ∃ x ∈ cube d,
      cellIndex d j x = Q ∧ b < |controlBalancedEstimator sample j β M x - g x|} =
      {sample | ENNReal.ofReal b <
        ⨆ x : {x : Fin d → ℝ | x ∈ cube d ∧ cellIndex d j x = Q},
          ENNReal.ofReal |armBalancedEstimator sample false j β M x - g x|} := by
    ext sample
    simp only [Set.mem_setOf_eq, lt_iSup_iff,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg hb]
    constructor
    · rintro ⟨x, hx, hQ, hlt⟩
      exact ⟨⟨x, hx, hQ⟩, hlt⟩
    · rintro ⟨x, hlt⟩
      exact ⟨x, x.property.1, x.property.2, hlt⟩
  rw [heq]
  exact measurableSet_lt measurable_const
    (armBalancedEstimator_cellSup_measurable false j β M g hg Q)

/-- Averaging the control outcome-fiber bound gives a cell probability
bounded by the actual sample minimum-count Laplace transform, including zero counts. -/
-- @node: control_balancedEstimator_cell_tail_of_laplace
lemma control_balancedEstimator_cell_tail_of_laplace (d : ℕ) (β γ C L M κ : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B : ℝ, 0 < B ∧ ∀ (n j : ℕ), 1 ≤ n → ∀ P : Law d,
      CATEClass d β γ C L M κ P →
      ∀ (Q : Fin d → Fin (2 ^ j)) (t : ℝ), 0 < t → t ≤ 2 * M →
        (P.sample n).real {sample | ∃ x ∈ cube d, cellIndex d j x = Q ∧
          B * L * (dyadicWidth j) ^ β + t <
            |controlBalancedEstimator sample j β M x - P.mu0 x|} ≤
          (2 * (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ)) *
            (∫ sample, Real.exp (-(referenceLowerEigenvalue d (polynomialOrder β) ^ 2 /
              (32 * (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ)) * t ^ 2 / M ^ 2) *
              (minimumCellCount sample false j (polynomialOrder β)
                (normingSubcells d β).radius Q : ℝ)) ∂P.sample n) := by
  obtain ⟨B, hB, hfiber⟩ := control_balancedEstimator_productFiber_cell_tail
    d β γ C L M κ hparam
  let R : ℝ := Fintype.card (MultiIndex d (polynomialOrder β))
  let c₁ : ℝ := referenceLowerEigenvalue d (polynomialOrder β) ^ 2 / (32 * R)
  have hR : 0 < R := by dsimp [R]; exact_mod_cast Fintype.card_pos
  have hc₁ : 0 < c₁ := by
    have hlam := referenceLowerEigenvalue_pos d (polynomialOrder β)
    dsimp [c₁]
    positivity
  refine ⟨B, hB, ?_⟩
  intro n j hn P hP Q t ht htM
  let : IsProbabilityMeasure P.full := hP.iid.1
  let μ := Measure.pi (fun _ : Fin n =>
    P.full.map (fun u : Full d => (u.1, u.2.1)))
  let N := fun design : Fin n → (Fin d → ℝ) × Bool =>
    minimumCellCount (fun i => ((design i).1, (design i).2, (0 : ℝ)))
      false j (polynomialOrder β) (normingSubcells d β).radius Q
  let g := fun design => (2 * R) * Real.exp (-(c₁ * t ^ 2 / M ^ 2) * (N design : ℝ))
  have hN : Measurable N := by dsimp [N]; fun_prop
  have hgmeas : Measurable g := by dsimp [g]; fun_prop
  let : IsProbabilityMeasure (P.full.map (fun u : Full d => (u.1, u.2.1))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hg : Integrable g μ := by
    apply Integrable.of_mem_Icc 0 (2 * R) hgmeas.aemeasurable
    apply Filter.Eventually.of_forall
    intro design
    have hexp : Real.exp (-(c₁ * t ^ 2 / M ^ 2) * (N design : ℝ)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hNnonneg : (0 : ℝ) ≤ N design := Nat.cast_nonneg _
      have hsnonneg : 0 ≤ c₁ * t ^ 2 / M ^ 2 := by positivity
      nlinarith [mul_nonneg hsnonneg hNnonneg]
    dsimp only [g]
    exact ⟨mul_nonneg (by positivity) (Real.exp_nonneg _),
      (mul_le_mul_of_nonneg_left hexp (by positivity)).trans_eq (mul_one _)⟩
  have hE := controlBalancedEstimator_cellEvent_measurableSet (n := n) j β M
    (B * L * (dyadicWidth j) ^ β + t) (by
      have hL := hparam.2.2.2.2.1
      have hh := (dyadicWidth_mem_Ioc j).1
      positivity) P.mu0 (holderOnCube_continuousOn hparam.2.1 hP.controlHolder) Q
  have hbound := sample_real_event_le_conditionalFiber_integral P hP.iid
    hP.consistency (by omega : 0 < n) _ hE g hg (by
      filter_upwards [hfiber P hP n j] with design hd
      have h := hd Q t ht.le
      dsimp only at h
      convert h using 1 <;> dsimp [g, N, c₁, R]
      congr 2
      ring)
  apply hbound.trans_eq
  rw [show (∫ design, g design ∂μ) =
      (2 * R) * ∫ design, Real.exp (-(c₁ * t ^ 2 / M ^ 2) * (N design : ℝ)) ∂μ by
        exact integral_const_mul _ _]
  congr 1
  exact minimumCellCount_design_integral_eq P hP.iid hP.consistency (by omega)
    false j (polynomialOrder β) (normingSubcells d β).radius (c₁ * t ^ 2 / M ^ 2) Q


/-- Roadmap (C16): averaging the control cell tails and taking the dyadic
cell union yields a Gaussian tail with the ordinary design dimension.
The minimum-count calculation retains the estimator's zero-count fallback. -/
-- @node: control_balancedEstimator_global_tail
lemma control_balancedEstimator_global_tail (d : ℕ) (β γ C L M κ : ℝ)
    (hparam : ParameterDomain d β γ C L M) (hκ : 0 < κ) :
    ∃ B K c : ℝ, 0 < B ∧ 0 < K ∧ 0 < c ∧
      ∀ (n j : ℕ), 1 ≤ n → ∀ P : Law d, CATEClass d β γ C L M κ P →
      ∀ t : ℝ, 0 < t → t ≤ 2 * M →
        (P.sample n).real {sample | supLoss (controlBalancedEstimator sample j β M) P.mu0 >
          ENNReal.ofReal (B * L * (dyadicWidth j) ^ β + t)} ≤
            K / (dyadicWidth j) ^ d *
              Real.exp (-c * (n : ℝ) * (dyadicWidth j) ^ d * t ^ 2 / M ^ 2) := by
  classical
  obtain ⟨B, hB, hcell⟩ := control_balancedEstimator_cell_tail_of_laplace
    d β γ C L M κ hparam
  let R : ℝ := Fintype.card (MultiIndex d (polynomialOrder β))
  let c₁ : ℝ := referenceLowerEigenvalue d (polynomialOrder β) ^ 2 / (32 * R)
  have hR : 0 < R := by dsimp [R]; exact_mod_cast Fintype.card_pos
  have hc₁ : 0 < c₁ := by
    have hlam := referenceLowerEigenvalue_pos d (polynomialOrder β)
    dsimp [c₁]
    positivity
  obtain ⟨c₂, hc₂, hlap⟩ := minimumControlCount_quadratic_laplace
    d β γ C L M κ c₁ hparam hc₁
  let c : ℝ := c₂ * κ * (2 * (normingSubcells d β).radius) ^ d
  have hc : 0 < c := by
    have hε := (normingSubcells d β).radius_pos
    dsimp [c]
    positivity
  refine ⟨B, (2 * R) * R, c, hB, by positivity, hc, ?_⟩
  intro n j hn P hP t ht htM
  let : IsProbabilityMeasure (P.sample n) :=
    sample_isProbabilityMeasure P hP.iid hP.consistency (by omega)
  have hL := hparam.2.2.2.2.1
  have hh := (dyadicWidth_mem_Ioc j).1
  have hb : 0 ≤ B * L * (dyadicWidth j) ^ β + t := by positivity
  rw [supLoss_event_eq_cellUnion _ _ j _ hb]
  have hmass : κ * (2 * dyadicWidth j * (normingSubcells d β).radius) ^ d =
      κ * (2 * (normingSubcells d β).radius) ^ d * (dyadicWidth j) ^ d := by
    rw [show 2 * dyadicWidth j * (normingSubcells d β).radius =
      (2 * (normingSubcells d β).radius) * dyadicWidth j by ring, mul_pow, mul_assoc]
  have hcard : (Fintype.card (Fin d → Fin (2 ^ j)) : ℝ) =
      1 / (dyadicWidth j) ^ d := by
    simp [Fintype.card_fun, dyadicWidth, div_pow]
  calc
    _ ≤ ∑ Q : Fin d → Fin (2 ^ j), (P.sample n).real
        {sample | ∃ x ∈ cube d, cellIndex d j x = Q ∧
          B * L * (dyadicWidth j) ^ β + t <
            |controlBalancedEstimator sample j β M x - P.mu0 x|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _Q : Fin d → Fin (2 ^ j), ((2 * R) * R) *
        Real.exp (-c * (n : ℝ) * (dyadicWidth j) ^ d * t ^ 2 / M ^ 2) := by
      apply Finset.sum_le_sum
      intro Q _
      apply (hcell n j hn P hP Q t ht htM).trans
      have h := mul_le_mul_of_nonneg_left
        (hlap n j P hP (by omega) Q t ht htM) (show 0 ≤ 2 * R by positivity)
      dsimp only [R, c₁] at h
      convert h using 1
      rw [hmass]
      dsimp [c, R]
      rw [mul_assoc]
      congr 2
      ring
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      ring

/-- The logarithmic threshold absorbs the number of dyadic cells in (C17).
After normalization, its Gaussian decay is uniform over bandwidths. -/
-- @node: controlLog_gaussian_envelope
lemma controlLog_gaussian_envelope (d : ℕ) {h u K : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hu : 1 ≤ u) (hK : 0 ≤ K) :
    K / h ^ d * Real.exp (-((d : ℝ) + 1) * u ^ 2 * Real.log (2 / h)) ≤
      K * Real.exp (-Real.log 2 * u ^ 2) := by
  have hlog : Real.log h ≤ 0 := Real.log_nonpos hh.le hh1
  have htwo : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hu2 : 1 ≤ u ^ 2 := by nlinarith
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hpow : 1 / h ^ d = Real.exp (-(d : ℝ) * Real.log h) := by
    rw [show -(d : ℝ) * Real.log h = -Real.log (h ^ d) by rw [Real.log_pow]; ring,
      Real.exp_neg, Real.exp_log (pow_pos hh d)]
    simp
  rw [div_eq_mul_one_div, hpow, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hK
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (by norm_num) hh.ne']
  nlinarith [mul_nonneg hd (mul_nonneg (sub_nonneg.mpr hu2) (neg_nonneg.mpr hlog)),
    mul_nonneg hd (mul_nonneg (sq_nonneg u) htwo)]

end CausalSmith.Stat.GlobalTailDesignRobustCate

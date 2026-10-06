module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.IdealCountTransport
public import Causalean.Stat.Concentration.Poisson.EmpiricalRadius
public import Causalean.Stat.Concentration.Poisson.FactorialPolynomial

/-! Ordinary second moments of the paper's pilot rectangle radii. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.Poisson
open scoped BigOperators NNReal

/-- The paper's pilot half-width is exactly the promoted empirical Poisson
radius with multiplier `4096` and logarithmic level `logAlphabet d`. With [the specified inputs and conditions](hyp:m,hm,d,pilot,zeta), [the stated relationship holds](goal). -/
-- @node: pilotHalfWidth_eq_empiricalRadius
lemma pilotHalfWidth_eq_empiricalRadius {m : ℝ} (hm : 0 < m)
    (d : ℕ) (pilot : Cell → ℕ) (zeta : Cell) :
    pilotHalfWidth m d pilot zeta =
      empiricalRadius pilotRadiusConstant (Real.toNNReal m)
        (logAlphabet d / m) (pilot zeta) := by
  unfold pilotHalfWidth empiricalRadius pilotCenter
  rw [Real.coe_toNNReal m hm.le]
  congr 3
  ring

/-- The local mass scale `v_j` with `L = log(ed)` and `m = n/8`. -/
noncomputable def badPilotCellScale {n d : ℕ}
    (P : DiscreteLaw d) (j : Fin d) : ℝ :=
  let m := (n : ℝ) / 8
  let L := logAlphabet d
  Real.sqrt (cellMass P j * L / m) + L / m

/-- Truncating the lower endpoint of a nonnegative pilot interval can only
decrease its radius below the untruncated half-width. With [the specified inputs and conditions](hyp:m,hm,d,hd,pilot,zeta), [the stated relationship holds](goal). -/
-- @node: pilotRadius_le_pilotHalfWidth
lemma pilotRadius_le_pilotHalfWidth {m : ℝ} (hm : 0 < m) {d : ℕ}
    (hd : 1 ≤ d) (pilot : Cell → ℕ) (zeta : Cell) :
    pilotRadius m d pilot zeta ≤ pilotHalfWidth m d pilot zeta := by
  have hc : 0 ≤ pilotCenter m pilot zeta := by
    unfold pilotCenter
    positivity
  have hL : 0 < logAlphabet d := by
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith [Real.log_nonneg hdreal]
  have hh : 0 ≤ pilotHalfWidth m d pilot zeta := by
    unfold pilotHalfWidth pilotRadiusConstant
    positivity
  unfold pilotRadius pilotUpper pilotLower
  have hlo := le_max_right (0 : ℝ)
    (pilotCenter m pilot zeta - pilotHalfWidth m d pilot zeta)
  linarith

/-- A single squared pilot radius is bounded by an affine function of its
Poisson count. With [the specified inputs and conditions](hyp:m,hm,d,hd,pilot,zeta), [the stated relationship holds](goal). -/
-- @node: pilotRadius_sq_le_count_envelope
lemma pilotRadius_sq_le_count_envelope {m : ℝ} (hm : 0 < m) {d : ℕ}
    (hd : 1 ≤ d) (pilot : Cell → ℕ) (zeta : Cell) :
    pilotRadius m d pilot zeta ^ 2 ≤
      2 * pilotRadiusConstant ^ 2 *
        ((pilot zeta : ℝ) * logAlphabet d / m ^ 2 +
          (logAlphabet d / m) ^ 2) := by
  have hL : 0 ≤ logAlphabet d := by
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith [Real.log_nonneg hdreal]
  have hR0 : 0 ≤ pilotRadius m d pilot zeta := by
    have hc : 0 ≤ pilotCenter m pilot zeta := by
      unfold pilotCenter
      positivity
    have hh : 0 ≤ pilotHalfWidth m d pilot zeta := by
      unfold pilotHalfWidth pilotRadiusConstant
      positivity
    unfold pilotRadius pilotUpper pilotLower
    have hlo : max 0 (pilotCenter m pilot zeta -
        pilotHalfWidth m d pilot zeta) ≤
        pilotCenter m pilot zeta + pilotHalfWidth m d pilot zeta := by
      apply max_le <;> linarith
    linarith
  have hhalf := pilotRadius_le_pilotHalfWidth hm hd pilot zeta
  let A := (pilot zeta : ℝ) * logAlphabet d / m ^ 2
  let delta := logAlphabet d / m
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hd0 : 0 ≤ delta := by dsimp [delta]; positivity
  have hsqrt := Real.sq_sqrt hA
  have hformula : pilotHalfWidth m d pilot zeta =
      pilotRadiusConstant * (Real.sqrt A + delta) := by
    unfold pilotHalfWidth pilotCenter
    dsimp [A, delta]
    congr 2
    field_simp
  have hhalf0 : 0 ≤ pilotHalfWidth m d pilot zeta := by
    rw [hformula]
    unfold pilotRadiusConstant
    positivity
  have hsq : pilotRadius m d pilot zeta ^ 2 ≤
      pilotHalfWidth m d pilot zeta ^ 2 :=
    (sq_le_sq₀ hR0 hhalf0).2 hhalf
  rw [hformula] at hsq
  dsimp [A, delta] at hsqrt ⊢
  nlinarith [sq_nonneg (Real.sqrt
    ((pilot zeta : ℝ) * logAlphabet d / m ^ 2) - logAlphabet d / m)]

/-- Under the flattened pilot Poisson table law, the squared sum of the four
pilot radii has the ordinary second-moment bound required in equation (21). With [the specified inputs and conditions](hyp:n,d,hn,hd,P,j), [the stated relationship holds](goal). -/
-- @node: pilotRadius_sum_sq_integral_le_cellScale
lemma pilotRadius_sum_sq_integral_le_cellScale {n d : ℕ} (hn : 1 ≤ n)
    (hd : 16 ≤ d) (P : DiscreteLaw d) (j : Fin d) :
    let m : ℝ := (n : ℝ) / 8
    let rate : Fin d → Fin 4 → ℝ≥0 := idealFlatRate (n := n) P
    let μ := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
    Integrable (fun p => (∑ zeta : Cell,
      pilotRadius m d (curryCountTable p j) zeta) ^ 2) μ ∧
    (∫ p, (∑ zeta : Cell,
      pilotRadius m d (curryCountTable p j) zeta) ^ 2 ∂μ) ≤
      32 * pilotRadiusConstant ^ 2 * badPilotCellScale (n := n) P j ^ 2 := by
  dsimp only
  let m : ℝ := (n : ℝ) / 8
  let L : ℝ := logAlphabet d
  let rate : Fin d → Fin 4 → ℝ≥0 := idealFlatRate (n := n) P
  let μ := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  let N : Cell → ((Fin d × Fin 4) → ℕ) → ℝ := fun z p =>
    (p (j, CellFourEquiv z) : ℕ)
  have hm : 0 < m := by dsimp [m]; positivity
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, poissonTableLaw]
    infer_instance
  have hL : 0 < L := by
    dsimp [L]
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith [Real.log_nonneg this]
  have hNlaw (z : Cell) : HasLaw (fun p => p (j, CellFourEquiv z))
      (poissonMeasure (rate j (CellFourEquiv z))) μ := by
    simpa [N, μ, rate, poissonTableCell] using
      poissonTable_eval_coordinate_law
        (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
        (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
        (fun _ => 0) (j, CellFourEquiv z)
  have hNint (z : Cell) : Integrable (N z) μ := by
    have hi : Integrable (fun w : ℕ => (w : ℝ))
        (poissonMeasure (rate j (CellFourEquiv z))) := by
      simpa using poisson_descFactorial_integrable (rate j (CellFourEquiv z)) 1
    have hi' : Integrable (fun w : ℕ => (w : ℝ))
        (Measure.map (fun p => p (j, CellFourEquiv z)) μ) := by
      rw [(hNlaw z).map_eq]
      exact hi
    exact hi'.comp_aemeasurable
      (measurable_pi_apply (j, CellFourEquiv z)).aemeasurable
  have hNmean (z : Cell) : (∫ p, N z p ∂μ) =
      (rate j (CellFourEquiv z) : ℝ) := by
    calc
      (∫ p, N z p ∂μ) = ∫ w : ℕ, (w : ℝ)
          ∂poissonMeasure (rate j (CellFourEquiv z)) := by
        simpa [N, Function.comp_def] using
          (hNlaw z).integral_comp (f := fun w : ℕ => (w : ℝ))
            (measurable_of_countable _).aestronglyMeasurable
      _ = _ := by
        simpa using poisson_descFactorial_moment (rate j (CellFourEquiv z)) 1
  let f : ((Fin d × Fin 4) → ℕ) → ℝ := fun p =>
    (∑ zeta : Cell, pilotRadius m d (curryCountTable p j) zeta) ^ 2
  let g : ((Fin d × Fin 4) → ℕ) → ℝ := fun p =>
    8 * pilotRadiusConstant ^ 2 *
      (L / m ^ 2 * ∑ zeta : Cell, N zeta p + 4 * (L / m) ^ 2)
  have hpoint (p : (Fin d × Fin 4) → ℕ) : f p ≤ g p := by
    have hcs := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun zeta : Cell =>
        pilotRadius m d (curryCountTable p j) zeta)
    have hcoord (zeta : Cell) :
        pilotRadius m d (curryCountTable p j) zeta ^ 2 ≤
          2 * pilotRadiusConstant ^ 2 *
            (N zeta p * L / m ^ 2 + (L / m) ^ 2) := by
      simpa [N, m, L, curryCountTable] using
        pilotRadius_sq_le_count_envelope hm (show 1 ≤ d by omega)
          (curryCountTable p j) zeta
    calc
      f p ≤ 4 * ∑ zeta : Cell,
          pilotRadius m d (curryCountTable p j) zeta ^ 2 := by
        simpa [f, Fintype.card_congr CellFourEquiv] using hcs
      _ ≤ 4 * ∑ zeta : Cell, (2 * pilotRadiusConstant ^ 2 *
          (N zeta p * L / m ^ 2 + (L / m) ^ 2)) := by
        gcongr with zeta
        exact hcoord zeta
      _ = g p := by
        dsimp [g]
        simp_rw [Fintype.sum_prod_type, Fin.sum_univ_two]
        ring
  have hgint : Integrable g μ := by
    apply Integrable.const_mul
    apply Integrable.add
    · exact (integrable_finset_sum _ fun z _ => hNint z).const_mul _
    · exact integrable_const _
  have hfint : Integrable f μ := by
    apply hgint.mono' (by fun_prop)
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hpoint p
    · dsimp [f]
      positivity
  have hint : (∫ p, f p ∂μ) ≤ ∫ p, g p ∂μ :=
    integral_mono hfint hgint hpoint
  have hrate (z : Cell) : (rate j (CellFourEquiv z) : ℝ) =
      m * cellVector P j z := by
    simp only [rate, idealFlatRate, Real.coe_toNNReal,
      Equiv.symm_apply_apply, m]
    exact max_eq_left (mul_nonneg hm.le ENNReal.toReal_nonneg)
  have hmass : ∑ z : Cell, cellVector P j z = cellMass P j := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fin.sum_univ_two]
    simp [cellMass, cellVector,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellVector,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.jointMass,
      finTwoEquiv]
    ring
  have hgmean : (∫ p, g p ∂μ) =
      8 * pilotRadiusConstant ^ 2 *
        (cellMass P j * L / m + 4 * (L / m) ^ 2) := by
    change (∫ p, 8 * pilotRadiusConstant ^ 2 *
      (L / m ^ 2 * ∑ zeta : Cell, N zeta p + 4 * (L / m) ^ 2) ∂μ) = _
    rw [integral_const_mul, integral_add]
    · rw [integral_const_mul, integral_finset_sum _ (fun z _ => hNint z)]
      simp_rw [hNmean]
      rw [integral_const]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      simp_rw [hrate]
      rw [← Finset.mul_sum, hmass]
      field_simp
    · exact (integrable_finset_sum _ fun z _ => hNint z).const_mul _
    · exact integrable_const _
  refine ⟨by simpa [f] using hfint, ?_⟩
  rw [show (fun p => (∑ zeta : Cell,
      pilotRadius m d (curryCountTable p j) zeta) ^ 2) = f by rfl]
  calc
    (∫ p, f p ∂μ) ≤ ∫ p, g p ∂μ := hint
    _ = 8 * pilotRadiusConstant ^ 2 *
        (cellMass P j * L / m + 4 * (L / m) ^ 2) := hgmean
    _ ≤ 32 * pilotRadiusConstant ^ 2 *
        (Real.sqrt (cellMass P j * L / m) + L / m) ^ 2 := by
      have hmass0 : 0 ≤ cellMass P j := by
        rw [← hmass]
        exact Finset.sum_nonneg fun z _ => ENNReal.toReal_nonneg
      have hA : 0 ≤ cellMass P j * L / m := by positivity
      have hsqrt := Real.sq_sqrt hA
      have hdelta : 0 ≤ L / m := by positivity
      have hcross := mul_nonneg
        (Real.sqrt_nonneg (cellMass P j * L / m)) hdelta
      unfold pilotRadiusConstant
      norm_num
      nlinarith
    _ = _ := by rfl

end CausalSmith.Stat.DiscreteBudgetvalueCurve

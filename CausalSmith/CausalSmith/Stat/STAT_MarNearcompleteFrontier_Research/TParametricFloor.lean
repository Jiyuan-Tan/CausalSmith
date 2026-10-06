module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.Decision
public import Causalean.Stat.Minimax.ChiSquared
public import Causalean.Stat.Minimax.TotalVariation
public import Causalean.Stat.Minimax.LeCamTwoPoint
public import Causalean.Stat.Minimax.MinimaxRisk

/-!
# One-cell parametric minimax floors

The point-risk constant is universal. The interval constant may depend only on
its fixed noncoverage level.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory

-- @node: lawClass_mono_floor
/-- Lowering the required arrival floor preserves membership in the MAR class. Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `q'`](hyp:q'), [the specified input `hqq'`](hyp:hqq'), [the specified input `P`](hyp:P), [the specified input `hP`](hyp:hP), [the stated mathematical conclusion holds](goal). -/
lemma lawClass_mono_floor {d : ℕ} {q q' : ℝ} (hqq' : q ≤ q')
    {P : FullLaw d} (hP : LawClass d q' P) : LawClass d q P := by
  refine ⟨hP.randomized, hP.balanced, hP.consistency, hP.mar, ?_⟩
  intro x a s hcell
  exact le_trans hqq' (hP.floor x a s hcell)

-- @node: mar_of_complete_arrival
/-- A law with deterministic outcome arrival satisfies MAR on every cell. Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `hR`](hyp:hR), [the stated mathematical conclusion holds](goal). -/
lemma mar_of_complete_arrival {d : ℕ} (P : FullLaw d)
    (hR : ∀ w : FullAtom d, w.R = false → fullMass P w = 0) :
    MissingAtRandom P := by
  classical
  intro x a s r y
  have erase_arrival (E : FullAtom d → Prop) [DecidablePred E] :
      massOf P (fun w => E w ∧ w.R = true) = massOf P E := by
    unfold massOf
    apply Finset.sum_congr rfl
    intro w _
    by_cases hr : w.R = true
    · simp [hr]
    · have hf : w.R = false := by cases h : w.R <;> simp_all
      simp [hr, hR w hf]
  have no_nonarrival (E : FullAtom d → Prop) [DecidablePred E] :
      massOf P (fun w => E w ∧ w.R = false) = 0 := by
    unfold massOf
    apply Finset.sum_eq_zero
    intro w _
    by_cases hr : w.R = false
    · simp [hr, hR w hr]
    · simp [hr]
  cases r with
  | false =>
      have hjoint := no_nonarrival
        (fun w : FullAtom d => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.Y = y)
      have hmarg := no_nonarrival
        (fun w : FullAtom d => w.X = x ∧ w.A = a ∧ w.S = s)
      have hzero : massOf P
          (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = false ∧ w.Y = y) = 0 := by
        simpa only [and_assoc, and_left_comm, and_comm] using hjoint
      rw [hzero]
      have hzero' : massOf P
          (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = false) = 0 := by
        simpa only [and_assoc] using hmarg
      rw [hzero']
      ring
  | true =>
      have hjoint := erase_arrival
        (fun w : FullAtom d => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.Y = y)
      have hmarg := erase_arrival
        (fun w : FullAtom d => w.X = x ∧ w.A = a ∧ w.S = s)
      have heq : massOf P
          (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = true ∧ w.Y = y) =
          massOf P (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.Y = y) := by
        simpa only [and_assoc, and_left_comm, and_comm] using hjoint
      have heq' : massOf P
          (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = true) =
          cellMass P x a s := by
        simpa only [cellMass, and_assoc] using hmarg
      rw [heq, heq']
      ring

-- @node: complete_arrival_mass
/-- An event has the same mass after intersecting with certain arrival. Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `hR`](hyp:hR), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_mass {d : ℕ} (P : FullLaw d)
    (hR : ∀ w : FullAtom d, w.R = false → fullMass P w = 0)
    (E : FullAtom d → Prop) :
    massOf P (fun w => E w ∧ w.R = true) = massOf P E := by
  classical
  unfold massOf
  apply Finset.sum_congr rfl
  intro w _
  by_cases hr : w.R = true
  · simp [hr]
  · have hf : w.R = false := by cases h : w.R <;> simp_all
    simp [hr, hR w hf]

-- @node: complete_arrival_floor
/-- Certain arrival meets every arrival floor at most one. Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `q`](hyp:q), [the specified input `hq`](hyp:hq), [the specified input `hR`](hyp:hR), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_floor {d : ℕ} (P : FullLaw d) (q : ℝ)
    (hq : q ≤ 1)
    (hR : ∀ w : FullAtom d, w.R = false → fullMass P w = 0) :
    ArrivalFloor q P := by
  intro x a s hcell
  have heq : massOf P
      (fun w => w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = true) =
      cellMass P x a s := by
    simpa only [cellMass, and_assoc] using
      complete_arrival_mass P hR (fun w => w.X = x ∧ w.A = a ∧ w.S = s)
  rw [arrivalProb, heq, div_self (ne_of_gt hcell)]
  exact hq

-- @node: complete_arrival_lawClass
/-- A randomized, balanced and consistent law with certain arrival is legal. Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `q`](hyp:q), [the specified input `hq`](hyp:hq), [the specified input `hrandom`](hyp:hrandom), [the specified input `hbalanced`](hyp:hbalanced), [the specified input `hconsistent`](hyp:hconsistent), [the specified input `hR`](hyp:hR), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_lawClass {d : ℕ} (P : FullLaw d) (q : ℝ)
    (hq : q ≤ 1)
    (hrandom : RandomizedIndependence P)
    (hbalanced : BalancedRandomization P)
    (hconsistent : Consistency P)
    (hR : ∀ w : FullAtom d, w.R = false → fullMass P w = 0) :
    LawClass d q P := by
  exact ⟨hrandom, hbalanced, hconsistent,
    mar_of_complete_arrival P hR, complete_arrival_floor P q hq hR⟩

-- @node: parametric_oneCell_lawClass
/-- The complete-arrival one-cell Bernoulli family belongs to every required floor class. Given [the specified input `d`](hyp:d), [the specified input `x`](hyp:x), [the specified input `p`](hyp:p), [the specified input `q`](hyp:q), [the specified input `hp`](hyp:hp), [the specified input `hq`](hyp:hq), [the stated mathematical conclusion holds](goal). -/
lemma parametric_oneCell_lawClass {d : ℕ} (x : Fin d) (p q : ℝ)
    (hp : p ∈ Set.Icc 0 1) (hq : q ≤ 1) :
    LawClass d q (parametricFullLaw x p hp) := by
  exact complete_arrival_lawClass (parametricFullLaw x p hp) q hq
    (parametricFullLaw_randomized x p hp)
    (parametricFullLaw_balanced x p hp)
    (parametricFullLaw_consistency x p hp)
    (parametricFullLaw_complete x p hp)

-- @node: parametric_chisq_bound
/-- The one-record chi-square expression of the one-cell Bernoulli submodel
is at most sixteen times the squared half-separation. Given [the specified input `u`](hyp:u), [the specified input `hu0`](hyp:hu0), [the specified input `hu1`](hyp:hu1), [the stated mathematical conclusion holds](goal). -/
lemma parametric_chisq_bound (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 4) :
    8 * u ^ 2 / (1 - 4 * u ^ 2) ≤ 16 * u ^ 2 := by
  have hu_sq : u ^ 2 ≤ 1 / 16 := by nlinarith
  have hden : 0 < 1 - 4 * u ^ 2 := by nlinarith
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg u]

-- @node: parametric_chisq_identity
/-- The two treated-atom contributions in the paper's one-record calculation. Given [the specified input `u`](hyp:u), [the specified input `hu0`](hyp:hu0), [the specified input `hu1`](hyp:hu1), [the stated mathematical conclusion holds](goal). -/
lemma parametric_chisq_identity (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 4) :
    u ^ 2 * (1 / (1 / 4 + u / 2) + 1 / (1 / 4 - u / 2)) =
      8 * u ^ 2 / (1 - 4 * u ^ 2) := by
  have hplus : 1 / 4 + u / 2 ≠ 0 := by linarith
  have hminus : 1 / 4 - u / 2 ≠ 0 := by linarith
  have hden : 1 - 4 * u ^ 2 ≠ 0 := by nlinarith [sq_nonneg u]
  have hplus' : 2 + u * 4 ≠ 0 := by linarith
  have hminus' : 2 - u * 4 ≠ 0 := by linarith
  have hden' : 1 - u ^ 2 * 4 ≠ 0 := by convert hden using 1; ring
  field_simp [hplus, hminus, hden, hplus', hminus', hden']
  ring

-- @node: parametric_chisq_le
/-- Equation (45), ready for the product chi-square comparison. Given [the specified input `u`](hyp:u), [the specified input `hu0`](hyp:hu0), [the specified input `hu1`](hyp:hu1), [the stated mathematical conclusion holds](goal). -/
lemma parametric_chisq_le (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 4) :
    u ^ 2 * (1 / (1 / 4 + u / 2) + 1 / (1 / 4 - u / 2)) ≤
      16 * u ^ 2 := by
  rw [parametric_chisq_identity u hu0 hu1]
  exact parametric_chisq_bound u hu0 hu1

-- @node: parametric_product_tv_of_chisq
/-- The product chi-square identity and Cauchy--Schwarz give equation (46)
once the one-record divergence is bounded by `16u²`. Given [the specified input `d`](hyp:d), [the specified input `n`](hyp:n), [the specified input `hac`](hyp:hac), [the specified input `u`](hyp:u), [the specified input `hchi`](hyp:hchi), [the stated mathematical conclusion holds](goal). Given [the specified input `μ`](hyp:μ), [the specified input `ν`](hyp:ν). -/
lemma parametric_product_tv_of_chisq {d n : ℕ}
    (μ ν : Measure (Obs d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (u : ℝ)
    (hchi : Causalean.Stat.chiSqDiv μ ν ≤ 16 * u ^ 2) :
    Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => μ))
        (Measure.pi (fun _ : Fin n => ν)) ≤
      (1 / 2 : ℝ) * Real.sqrt (Real.exp (16 * (n : ℝ) * u ^ 2) - 1) := by
  let μn := Measure.pi (fun _ : Fin n => μ)
  let νn := Measure.pi (fun _ : Fin n => ν)
  have hint : Integrable (fun x => ((μn.rnDeriv νn x).toReal - 1) ^ 2) νn :=
    Integrable.of_finite
  have hacn : μn ≪ νn :=
    Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous
      μ ν hac n
  have htv := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv μn νn hacn hint
  have hprod := Causalean.Stat.one_add_chiSqDiv_pi_iid μ ν hac n
  have hbase : 0 ≤ 1 + Causalean.Stat.chiSqDiv μ ν := by
    linarith [Causalean.Stat.chiSqDiv_nonneg (μ := μ) (ν := ν)]
  have hpow : (1 + Causalean.Stat.chiSqDiv μ ν) ^ n ≤
      Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv μ ν) := by
    have hbase_exp : 1 + Causalean.Stat.chiSqDiv μ ν ≤
        Real.exp (Causalean.Stat.chiSqDiv μ ν) := by
      linarith [Real.add_one_le_exp (Causalean.Stat.chiSqDiv μ ν)]
    calc
      _ ≤ (Real.exp (Causalean.Stat.chiSqDiv μ ν)) ^ n :=
        pow_le_pow_left₀ hbase hbase_exp n
      _ = _ := by rw [← Real.exp_nat_mul]
  have hchi_prod : Causalean.Stat.chiSqDiv μn νn ≤
      Real.exp (16 * (n : ℝ) * u ^ 2) - 1 := by
    have hscale : (n : ℝ) * Causalean.Stat.chiSqDiv μ ν ≤
        16 * (n : ℝ) * u ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hchi (Nat.cast_nonneg n)]
    have h := hpow.trans (Real.exp_le_exp.mpr hscale)
    rw [← hprod] at h
    linarith
  exact htv.trans (by gcongr)

-- @node: parametric_product_tv_half
/-- A logarithmic chi-square budget makes the two product laws hard to test. Given [the specified input `d`](hyp:d), [the specified input `n`](hyp:n), [the specified input `hac`](hyp:hac), [the specified input `u`](hyp:u), [the specified input `hchi`](hyp:hchi), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `μ`](hyp:μ), [the specified input `ν`](hyp:ν), [the specified input `hbudget`](hyp:hbudget). -/
lemma parametric_product_tv_half {d n : ℕ}
    (μ ν : Measure (Obs d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (u : ℝ)
    (hchi : Causalean.Stat.chiSqDiv μ ν ≤ 16 * u ^ 2)
    (hbudget : 16 * (n : ℝ) * u ^ 2 ≤ Real.log 2) :
    Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => μ))
        (Measure.pi (fun _ : Fin n => ν)) ≤ 1 / 2 := by
  have htv := parametric_product_tv_of_chisq (n := n) μ ν hac u hchi
  have hexp : Real.exp (16 * (n : ℝ) * u ^ 2) ≤ 2 := by
    calc
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hbudget
      _ = 2 := Real.exp_log (by norm_num)
  have hroot : Real.sqrt (Real.exp (16 * (n : ℝ) * u ^ 2) - 1) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show Real.exp (16 * (n : ℝ) * u ^ 2) - 1 ≤ 1 by
      linarith)
    simpa using h
  nlinarith

-- @node: parametric_radius_budget
/-- A single positive perturbation scale meets the product testing budget at every sample size. [the stated mathematical conclusion holds](goal). -/
lemma parametric_radius_budget :
    ∃ a : ℝ, 0 < a ∧
      ∀ n : ℕ, 1 ≤ n →
        0 < a / Real.sqrt n ∧
        a / Real.sqrt n ≤ 1 / 4 ∧
        16 * (n : ℝ) * (a / Real.sqrt n) ^ 2 ≤ Real.log 2 := by
  let a : ℝ := min (1 / 4) (Real.sqrt (Real.log 2) / 4)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have haquarter : a ≤ 1 / 4 := min_le_left _ _
  have haroot : a ≤ Real.sqrt (Real.log 2) / 4 := min_le_right _ _
  refine ⟨a, ha, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hroot1 : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hroot_sq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (le_of_lt hnpos)
  have hlogsqrt : 0 ≤ Real.sqrt (Real.log 2) := Real.sqrt_nonneg _
  have ha2 : a ^ 2 ≤ Real.log 2 / 16 := by
    have hright : 0 ≤ Real.sqrt (Real.log 2) / 4 := by positivity
    have h := mul_nonneg (sub_nonneg.mpr haroot)
      (add_nonneg (le_of_lt ha) hright)
    have hsqrt : (Real.sqrt (Real.log 2)) ^ 2 = Real.log 2 :=
      Real.sq_sqrt (le_of_lt hlog)
    nlinarith [h]
  constructor
  · exact div_pos ha hroot
  constructor
  · exact (div_le_iff₀ hroot).2 (by nlinarith [haquarter, hroot1])
  · have hscale : (n : ℝ) * (a / Real.sqrt n) ^ 2 = a ^ 2 := by
      have hdiv : (a / Real.sqrt n) * Real.sqrt n = a :=
        div_mul_cancel₀ a (ne_of_gt hroot)
      calc
        (n : ℝ) * (a / Real.sqrt n) ^ 2 =
            ((a / Real.sqrt n) * Real.sqrt n) ^ 2 := by
              rw [mul_pow, hroot_sq]
              ring
        _ = a ^ 2 := by rw [hdiv]
    calc
      16 * (n : ℝ) * (a / Real.sqrt n) ^ 2 = 16 * a ^ 2 := by
        rw [mul_assoc, hscale]
      _ ≤ Real.log 2 := by nlinarith [ha2]

-- @node: parametric_product_tv_at_radius
/-- For [absolutely continuous observed laws](hyp:hac), [a positive sample size](hyp:hn), [a radius budget valid at every positive integer](hyp:ha), and [the stated chi-square bound](hyp:hchi), [the product laws have total variation distance at most one half](goal). -/
lemma parametric_product_tv_at_radius {d n : ℕ}
    (μ ν : Measure (Obs d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (a : ℝ) (hn : 1 ≤ n)
    (ha : ∀ m : ℕ, 1 ≤ m →
      0 < a / Real.sqrt m ∧ a / Real.sqrt m ≤ 1 / 4 ∧
        16 * (m : ℝ) * (a / Real.sqrt m) ^ 2 ≤ Real.log 2)
    (hchi : Causalean.Stat.chiSqDiv μ ν ≤
      16 * (a / Real.sqrt n) ^ 2) :
    Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => μ))
      (Measure.pi (fun _ : Fin n => ν)) ≤ 1 / 2 := by
  exact parametric_product_tv_half μ ν hac (a / Real.sqrt n) hchi (ha n hn).2.2

-- @node: parametric_product_tv_at_budget
/-- A chi-square budget calibrated to an arbitrary positive testing tolerance. Given [the specified input `d`](hyp:d), [the specified input `n`](hyp:n), [the specified input `hac`](hyp:hac), [the specified input `u`](hyp:u), [the specified input `b`](hyp:b), [the specified input `hb`](hyp:hb), [the specified input `hchi`](hyp:hchi), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `μ`](hyp:μ), [the specified input `ν`](hyp:ν), [the specified input `hbudget`](hyp:hbudget). -/
lemma parametric_product_tv_at_budget {d n : ℕ}
    (μ ν : Measure (Obs d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (u b : ℝ) (hb : 0 ≤ b)
    (hchi : Causalean.Stat.chiSqDiv μ ν ≤ 16 * u ^ 2)
    (hbudget : 16 * (n : ℝ) * u ^ 2 ≤ Real.log (1 + b ^ 2)) :
    Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => μ))
      (Measure.pi (fun _ : Fin n => ν)) ≤ b / 2 := by
  have htv := parametric_product_tv_of_chisq (n := n) μ ν hac u hchi
  have harg : 0 < 1 + b ^ 2 := by positivity
  have hexp : Real.exp (16 * (n : ℝ) * u ^ 2) ≤ 1 + b ^ 2 := by
    calc
      _ ≤ Real.exp (Real.log (1 + b ^ 2)) := Real.exp_le_exp.mpr hbudget
      _ = 1 + b ^ 2 := Real.exp_log harg
  have hroot : Real.sqrt (Real.exp (16 * (n : ℝ) * u ^ 2) - 1) ≤ b := by
    have h := Real.sqrt_le_sqrt (show
      Real.exp (16 * (n : ℝ) * u ^ 2) - 1 ≤ b ^ 2 by linarith)
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hb] using h
  nlinarith

-- @node: parametric_radius_budget_at_tolerance
/-- The one-cell perturbation can be scaled to any positive interval-testing tolerance. Given [the specified input `b`](hyp:b), [the specified input `hb`](hyp:hb), [the stated mathematical conclusion holds](goal). -/
lemma parametric_radius_budget_at_tolerance (b : ℝ) (hb : 0 < b) :
    ∃ a : ℝ, 0 < a ∧
      ∀ n : ℕ, 1 ≤ n →
        0 < a / Real.sqrt n ∧ a / Real.sqrt n ≤ 1 / 4 ∧
        16 * (n : ℝ) * (a / Real.sqrt n) ^ 2 ≤
          Real.log (1 + b ^ 2) := by
  let a : ℝ := min (1 / 4) (Real.sqrt (Real.log (1 + b ^ 2)) / 4)
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hlog : 0 < Real.log (1 + b ^ 2) := Real.log_pos (by linarith)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have haquarter : a ≤ 1 / 4 := min_le_left _ _
  have haroot : a ≤ Real.sqrt (Real.log (1 + b ^ 2)) / 4 := min_le_right _ _
  refine ⟨a, ha, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hroot1 : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hroot_sq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (le_of_lt hnpos)
  have ha2 : a ^ 2 ≤ Real.log (1 + b ^ 2) / 16 := by
    have hright : 0 ≤ Real.sqrt (Real.log (1 + b ^ 2)) / 4 := by positivity
    have h := mul_nonneg (sub_nonneg.mpr haroot)
      (add_nonneg (le_of_lt ha) hright)
    have hsqrt : Real.sqrt (Real.log (1 + b ^ 2)) ^ 2 =
        Real.log (1 + b ^ 2) := Real.sq_sqrt (le_of_lt hlog)
    nlinarith [h]
  constructor
  · exact div_pos ha hroot
  constructor
  · exact (div_le_iff₀ hroot).2 (by nlinarith [haquarter, hroot1])
  · have hscale : (n : ℝ) * (a / Real.sqrt n) ^ 2 = a ^ 2 := by
      have hdiv : (a / Real.sqrt n) * Real.sqrt n = a :=
        div_mul_cancel₀ a (ne_of_gt hroot)
      calc
        (n : ℝ) * (a / Real.sqrt n) ^ 2 =
            ((a / Real.sqrt n) * Real.sqrt n) ^ 2 := by
              rw [mul_pow, hroot_sq]
              ring
        _ = a ^ 2 := by rw [hdiv]
    calc
      16 * (n : ℝ) * (a / Real.sqrt n) ^ 2 = 16 * a ^ 2 := by
        rw [mul_assoc, hscale]
      _ ≤ Real.log (1 + b ^ 2) := by nlinarith [ha2]

-- @node: parametric_product_tv_at_tolerance_radius
/-- For [absolutely continuous observed laws](hyp:hac), [a nonnegative tolerance](hyp:hb), [a positive sample size](hyp:hn), [a tolerance radius budget](hyp:ha), and [the stated chi-square bound](hyp:hchi), [the product laws have total variation distance at most half the tolerance](goal). -/
lemma parametric_product_tv_at_tolerance_radius {d n : ℕ}
    (μ ν : Measure (Obs d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (a b : ℝ) (hb : 0 ≤ b) (hn : 1 ≤ n)
    (ha : ∀ m : ℕ, 1 ≤ m →
      0 < a / Real.sqrt m ∧ a / Real.sqrt m ≤ 1 / 4 ∧
        16 * (m : ℝ) * (a / Real.sqrt m) ^ 2 ≤
          Real.log (1 + b ^ 2))
    (hchi : Causalean.Stat.chiSqDiv μ ν ≤
      16 * (a / Real.sqrt n) ^ 2) :
    Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => μ))
      (Measure.pi (fun _ : Fin n => ν)) ≤ b / 2 := by
  exact parametric_product_tv_at_budget μ ν hac (a / Real.sqrt n) b hb hchi
    (ha n hn).2.2

-- @node: parametric_oneCell_pair
/-- The central and perturbed one-cell laws form a legal pair with controlled divergence. Given [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `u`](hyp:u), [the specified input `hd`](hyp:hd), [the specified input `hq`](hyp:hq), [the specified input `hu`](hyp:hu), [the specified input `huquarter`](hyp:huquarter), [the stated mathematical conclusion holds](goal). -/
lemma parametric_oneCell_pair {d : ℕ} {q u : ℝ} (hd : 1 ≤ d) (hq : q ≤ 1)
    (hu : 0 < u) (huquarter : u ≤ 1 / 4) :
    ∃ P₀ P₁ : ClassLaw d q,
      tau P₀.val = 1 / 2 ∧ tau P₁.val = 1 / 2 + u ∧
      (observedLaw P₁.val).toMeasure ≪ (observedLaw P₀.val).toMeasure ∧
      Causalean.Stat.chiSqDiv (observedLaw P₁.val).toMeasure
        (observedLaw P₀.val).toMeasure ≤ 16 * u ^ 2 := by
  let x : Fin d := ⟨0, by omega⟩
  have hp₀ : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by norm_num
  have hp₁ : (1 / 2 + u : ℝ) ∈ Set.Icc 0 1 := by
    constructor <;> linarith
  let P₀ : ClassLaw d q :=
    ⟨parametricFullLaw x (1 / 2) hp₀,
      parametric_oneCell_lawClass x (1 / 2) q hp₀ hq⟩
  let P₁ : ClassLaw d q :=
    ⟨parametricFullLaw x (1 / 2 + u) hp₁,
      parametric_oneCell_lawClass x (1 / 2 + u) q hp₁ hq⟩
  refine ⟨P₀, P₁, ?_, ?_, ?_, ?_⟩
  · simpa [P₀] using parametricFullLaw_tau x (1 / 2) hp₀
  · simpa [P₁] using parametricFullLaw_tau x (1 / 2 + u) hp₁
  · simpa [P₀, P₁] using parametric_observed_ac x (1 / 2 + u) hp₁
  · rw [show (observedLaw P₁.val).toMeasure =
        (observedLaw (parametricFullLaw x (1 / 2 + u) hp₁)).toMeasure by rfl,
      show (observedLaw P₀.val).toMeasure =
        (observedLaw (parametricFullLaw x (1 / 2) hp₀)).toMeasure by rfl,
      parametric_observed_chisq]
    nlinarith [sq_nonneg u]

-- @node: lem:parametric-floor-infrastructure
/-- One-cell Bernoulli submodels give the standard parametric floors. [the stated mathematical conclusion holds](goal). -/
lemma parametric_floor :
    ∃ c0 : ℝ, 0 < c0 ∧
      (∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d →
        q ∈ Set.Icc ((1 : ℝ) / 2) 1 →
        c0 / (n : ℝ) ≤ pointMinimaxRisk n d q) ∧
      (∀ α : ℝ, α ∈ Set.Ioo 0 ((1 : ℝ) / 2) →
        ∃ cα : ℝ, 0 < cα ∧
          ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d →
            q ∈ Set.Icc ((1 : ℝ) / 2) 1 →
            cα / Real.sqrt n ≤ lengthMinimaxRisk n d q α) := by
  obtain ⟨a, ha, hbudget⟩ := parametric_radius_budget
  refine ⟨a ^ 2 / 16, by positivity, ?_, ?_⟩
  · intro n d q hn hd hq
    let u := a / Real.sqrt n
    have hu := (hbudget n hn).1
    have huquarter := (hbudget n hn).2.1
    obtain ⟨P₀, P₁, htau₀, htau₁, hac, hchi⟩ :=
      parametric_oneCell_pair hd hq.2 hu huquarter
    have htv : Causalean.Stat.tvDist
        (samplePi P₁.val n) (samplePi P₀.val n) ≤ 1 / 2 := by
      unfold samplePi
      exact parametric_product_tv_at_radius
        (observedLaw P₁.val).toMeasure (observedLaw P₀.val).toMeasure
        hac a hn hbudget hchi
    have hlower := parametric_point_pair_lower P₀ P₁ hu htau₀ htau₁ htv
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hsqrt : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (le_of_lt hnpos)
    calc
      (a ^ 2 / 16) / (n : ℝ) = u ^ 2 / 16 := by
        dsimp [u]
        rw [div_pow, hsqrt]
        ring
      _ ≤ pointMinimaxRisk n d q := hlower
  · intro α hα
    let b := 1 - 2 * α
    have hb : 0 < b := by dsimp [b]; linarith [hα.2]
    obtain ⟨aα, haα, hbudgetα⟩ :=
      parametric_radius_budget_at_tolerance b hb
    let cα := aα * b / 2
    have hcα : 0 < cα := by dsimp [cα]; positivity
    refine ⟨cα, hcα, ?_⟩
    intro n d q hn hd hq
    let u := aα / Real.sqrt n
    have hu := (hbudgetα n hn).1
    have huquarter := (hbudgetα n hn).2.1
    obtain ⟨P₀, P₁, htau₀, htau₁, hac, hchi⟩ :=
      parametric_oneCell_pair hd hq.2 hu huquarter
    have htv : Causalean.Stat.tvDist
        (samplePi P₀.val n) (samplePi P₁.val n) ≤ (1 - 2 * α) / 2 := by
      have htv' := parametric_product_tv_at_tolerance_radius
        (observedLaw P₁.val).toMeasure (observedLaw P₀.val).toMeasure
        hac aα b (le_of_lt hb) hn hbudgetα hchi
      unfold samplePi
      rw [Causalean.Stat.tvDist_symm]
      simpa [b] using htv'
    have hlower := parametric_interval_pair_lower P₀ P₁ hu (le_of_lt hα.1)
      htau₀ htau₁ htv
    calc
      cα / Real.sqrt n = u * (1 - 2 * α) / 2 := by
        dsimp [cα, u, b]
        ring
      _ ≤ lengthMinimaxRisk n d q α := hlower

end CausalSmith.Stat.MarNearcompleteFrontier

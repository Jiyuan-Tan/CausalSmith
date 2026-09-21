module
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Contour.ComplexExp

/-!
# Shared schedules and certified circle nodes

This module defines the single schedule record consumed by evaluation,
schedule manifests, and specifications. It also evaluates every rational
circle node, including the terminal endpoint used by deterministic trapezoidal
quadrature, from the same scheduled π and complex-exponential fuel.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.IntervalArithmetic.Contour

open Causalean.Mathlib.Analysis.IntervalArithmetic
open Causalean.Mathlib.Analysis.IntervalArithmetic.Contour
/-- A contour schedule packages [a requested rational error tolerance](hyp:tolerance),
[supplied operation-count metadata](hyp:operationCount), [an input precision](hyp:inputPrecision),
[a mesh size](hyp:mesh) that is [nonempty](hyp:mesh_pos),
[a fuel budget](hyp:fuel) for transcendental evaluation, and
[a nonnegative Lipschitz constant](hyp:lipschitzConstant,lipschitzConstant_nonneg), together with
three nonnegative error budgets — [for node evaluation](hyp:nodeBudget,nodeBudget_nonneg),
[for the uniform mesh](hyp:meshBudget,meshBudget_nonneg), and
[for final quadrature widening](hyp:quadratureBudget,quadratureBudget_nonneg) — such that
[the three budgets together fit within the tolerance](hyp:budget_sum_le) and
[the mesh budget absorbs the Lipschitz discretization error](hyp:mesh_error_le). -/
structure Schedule where
  /-- The requested final rational tolerance. -/
  tolerance : PosRat
  /-- Supplied primitive-operation-count metadata for one node program. -/
  operationCount : ℕ
  /-- Input-name precision used by every node evaluation. -/
  inputPrecision : ℕ
  /-- Number of uniform trapezoidal mesh cells. -/
  mesh : ℕ
  /-- The scheduled mesh is nonempty. -/
  mesh_pos : 0 < mesh
  /-- Common Taylor/intersection fuel used at all nodes. -/
  fuel : ℕ
  /-- Rational Lipschitz constant used to bound quadrature discretization error. -/
  lipschitzConstant : ℚ
  /-- The Lipschitz constant is nonnegative. -/
  lipschitzConstant_nonneg : 0 ≤ lipschitzConstant
  /-- Budget allocated to node evaluation error. -/
  nodeBudget : ℚ
  /-- Budget allocated to uniform-mesh error. -/
  meshBudget : ℚ
  /-- Budget allocated to the final quadrature widening. -/
  quadratureBudget : ℚ
  /-- Node error budget is nonnegative. -/
  nodeBudget_nonneg : 0 ≤ nodeBudget
  /-- Mesh error budget is nonnegative. -/
  meshBudget_nonneg : 0 ≤ meshBudget
  /-- Quadrature error budget is nonnegative. -/
  quadratureBudget_nonneg : 0 ≤ quadratureBudget
  /-- The three split budgets fit within the requested tolerance. -/
  budget_sum_le : nodeBudget + meshBudget + quadratureBudget ≤ tolerance.1
  /-- The selected mesh absorbs the Lipschitz discretization error. -/
  mesh_error_le : lipschitzConstant / mesh ≤ meshBudget

/-- Given [a positive rational tolerance](hyp:tolerance), [natural-number operation-count
metadata](hyp:operationCount), [a rational Lipschitz constant](hyp:lipschitzConstant), and
[evidence that this constant is nonnegative](hyp:hlipschitz), the [canonical contour
schedule](goal) allocates one third of the tolerance to each error budget and selects its input
precision, mesh size, and fuel from the stated rational data.

This construction uses conservative integer bounds derived from the tolerance denominator and
Lipschitz constant. -/
def Schedule.canonical (tolerance : PosRat) (operationCount : ℕ)
    (lipschitzConstant : ℚ) (hlipschitz : 0 ≤ lipschitzConstant) : Schedule where
  tolerance := tolerance
  operationCount := operationCount
  inputPrecision :=
    64 * (operationCount + 1) * (tolerance.1.den + 1) *
      (lipschitzConstant.num.natAbs + 2) ^ 2
  mesh := 3 * (lipschitzConstant.num.natAbs + 1) * tolerance.1.den
  mesh_pos := by positivity
  fuel :=
    64 * (operationCount + 1) * (tolerance.1.den + 1) *
      (lipschitzConstant.num.natAbs + 2) ^ 2
  lipschitzConstant := lipschitzConstant
  lipschitzConstant_nonneg := hlipschitz
  nodeBudget := tolerance.1 / 3
  meshBudget := tolerance.1 / 3
  quadratureBudget := tolerance.1 / 3
  nodeBudget_nonneg := by exact (div_nonneg tolerance.2.le (by norm_num))
  meshBudget_nonneg := by exact (div_nonneg tolerance.2.le (by norm_num))
  quadratureBudget_nonneg := by exact (div_nonneg tolerance.2.le (by norm_num))
  budget_sum_le := by
    linarith
  mesh_error_le := by
    have hMle : lipschitzConstant ≤ (lipschitzConstant.num.natAbs : ℕ) := by
      have hnum0 : 0 ≤ lipschitzConstant.num := Rat.num_nonneg.mpr hlipschitz
      calc
        lipschitzConstant =
            (lipschitzConstant.num : ℚ) / (lipschitzConstant.den : ℕ) :=
          (Rat.num_div_den lipschitzConstant).symm
        _ ≤ (lipschitzConstant.num : ℚ) := div_le_self (by exact_mod_cast hnum0)
          (by exact_mod_cast Rat.den_pos lipschitzConstant)
        _ = (lipschitzConstant.num.natAbs : ℕ) := by
          have hi : (lipschitzConstant.num.natAbs : ℤ) = lipschitzConstant.num :=
            Int.natAbs_of_nonneg hnum0
          exact (congrArg (fun x : ℤ => (x : ℚ)) hi).symm
    have hεden : (1 : ℚ) ≤ tolerance.1 * (tolerance.1.den : ℕ) := by
      have hnumpos : 0 < tolerance.1.num := (Rat.num_pos).2 tolerance.2
      have hrepr := Rat.num_div_den tolerance.1
      have hdenpos : (0 : ℚ) < tolerance.1.den := by
        exact_mod_cast Rat.den_pos tolerance.1
      have heq : (tolerance.1.num : ℚ) =
          tolerance.1 * (tolerance.1.den : ℕ) :=
        (div_eq_iff hdenpos.ne').mp hrepr
      rw [← heq]
      exact_mod_cast hnumpos
    have hA : (0 : ℚ) ≤ lipschitzConstant.num.natAbs + 1 := by positivity
    have hcoarse : lipschitzConstant ≤
        tolerance.1 *
          (((lipschitzConstant.num.natAbs : ℚ) + 1) * tolerance.1.den) := by
      calc
        lipschitzConstant ≤ (lipschitzConstant.num.natAbs : ℕ) := hMle
        _ ≤ (lipschitzConstant.num.natAbs + 1 : ℕ) := by
          exact_mod_cast Nat.le_succ _
        _ ≤ tolerance.1 * (((lipschitzConstant.num.natAbs : ℚ) + 1) *
            tolerance.1.den) := by
          have h := mul_le_mul_of_nonneg_left hεden hA
          push_cast at h ⊢
          nlinarith
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    calc
      lipschitzConstant /
          (3 * (lipschitzConstant.num.natAbs + 1) * tolerance.1.den) ≤
          (tolerance.1 *
              ((lipschitzConstant.num.natAbs + 1) * tolerance.1.den)) /
            (3 * (lipschitzConstant.num.natAbs + 1) * tolerance.1.den) :=
        div_le_div_of_nonneg_right hcoarse (by positivity)
      _ = tolerance.1 / 3 := by field_simp

/-- A schedule-manifest entry records [a shared schedule](hyp:schedule), [an endpoint
index](hyp:node), and [an operation ordinal](hyp:operation). -/
structure ScheduleManifestEntry where
  /-- The exact shared schedule stored in this entry. -/
  schedule : Schedule
  /-- The endpoint index recorded by the entry. -/
  node : ℕ
  /-- An ordinal bounded by the node program's supplied operation-count metadata. -/
  operation : ℕ

/-- Given [a contour schedule](hyp:schedule), [a mesh-endpoint index](hyp:node), and [an operation
ordinal](hyp:operation), the [circle-node schedule-manifest entry](goal) records exactly those
three quantities. -/
def circleNodeManifestEntry (schedule : Schedule) (node operation : ℕ) :
    ScheduleManifestEntry :=
  ⟨schedule, node, operation⟩

/-- Given [a contour schedule](hyp:schedule) and [a natural-number endpoint index](hyp:k), the [rational rectangle enclosing the corresponding pure-imaginary circle angle](goal) has real coordinate zero and imaginary coordinate $2πk/m$, where $m$ is the schedule's mesh size. -/
def circleAngle (schedule : Schedule) (k : ℕ) : ComplexRatInterval :=
  ⟨RatInterval.point 0,
    (RatInterval.point (2 * k / schedule.mesh : ℚ)).mul
      (Transcendental.piInterval schedule.inputPrecision)⟩

/-- Given [a rational radius](hyp:radius), [a contour schedule](hyp:schedule), and [a natural-number endpoint index](hyp:k), the [scheduled circle-node rectangle](goal) is the rational-interval evaluation of $r\exp(2πik/m)$ using that schedule's angle enclosure and fuel. -/
def circleNode (radius : ℚ) (schedule : Schedule) (k : ℕ) : ComplexRatInterval :=
  (Transcendental.complexExp (circleAngle schedule k) schedule.fuel).smulRat radius

/-- Given [a rational radius](hyp:radius) and [a positive rational target width](hyp:target), the [internal circle tolerance](goal) is the smaller of $\mathrm{target}/(256(|r|+1))$ and $1/1024$.

The cap at $1/1024$ keeps the elementary-factor magnitude estimates used in complex multiplication uniform. -/
def circleInnerTolerance (radius : ℚ) (target : PosRat) : PosRat :=
  ⟨min (target.1 / (256 * (|radius| + 1))) (1 / 1024), by
    apply lt_min
    · exact div_pos target.2
        (mul_pos (by norm_num) (by linarith [abs_nonneg radius]))
    · norm_num⟩

/-- Given [a rational radius](hyp:radius) and [a positive rational target width](hyp:target), the [circle input precision](goal) is the π-approximation precision selected for their internal circle tolerance. -/
def circleInputPrecision (radius : ℚ) (target : PosRat) : ℕ :=
  Transcendental.piPrecision (circleInnerTolerance radius target)

/-- Given [a rational radius](hyp:radius), [a natural-number mesh size](hyp:_mesh), and [a positive rational target width](hyp:target), the [circle exponential fuel](goal) is the larger of the zero-input exponential precision and an explicit trigonometric Taylor-fuel bound computed from the internal circle tolerance.

This rational-data bound is valid uniformly for all endpoints of the finite mesh. -/
def circleExpFuel (radius : ℚ) (_mesh : ℕ) (target : PosRat) : ℕ :=
  max
    (Transcendental.expPrecision
      0 (circleInnerTolerance radius target))
    (32 * ((circleInnerTolerance radius target).1.den + 1) * 12 ^ 2)

private theorem point_mul_width (q : ℚ) (hq : 0 ≤ q) (I : RatInterval) :
    ((RatInterval.point q).mul I).width = q * I.width := by
  have h : q * I.lo ≤ q * I.hi := mul_le_mul_of_nonneg_left I.lo_le_hi hq
  simp [RatInterval.mul, RatInterval.point, RatInterval.width, h]
  ring

private theorem point_mul_maxAbs (q : ℚ) (hq : 0 ≤ q) (I : RatInterval) :
    ((RatInterval.point q).mul I).maxAbs = q * I.maxAbs := by
  have h : q * I.lo ≤ q * I.hi := mul_le_mul_of_nonneg_left I.lo_le_hi hq
  simp [RatInterval.mul, RatInterval.point, RatInterval.maxAbs, h, abs_mul,
    abs_of_nonneg hq, mul_max_of_nonneg _ _ hq]

private theorem interval_maxAbs_le_of_contains_width {I : RatInterval} {x : ℝ}
    {C w : ℚ} (hx : I.Contains x) (habs : |x| ≤ C) (hw : I.width ≤ w) :
    I.maxAbs ≤ C + w := by
  rw [abs_le] at habs
  rcases hx with ⟨hxlo, hxhi⟩
  rcases habs with ⟨habslo, habshi⟩
  have hw' : (I.hi : ℝ) - I.lo ≤ w := by exact_mod_cast hw
  apply max_le
  · rw [abs_le]
    constructor
    · have h : (-(C + w) : ℝ) ≤ (I.lo : ℚ) := by
        push_cast
        linarith [hxhi, habslo, hw']
      exact_mod_cast h
    · have h : ((I.lo : ℚ) : ℝ) ≤ (C + w : ℚ) := by
        push_cast
        linarith [hxlo, habshi]
      exact_mod_cast h
  · rw [abs_le]
    constructor
    · have h : (-(C + w) : ℝ) ≤ (I.hi : ℚ) := by
        push_cast
        linarith [hxhi, habslo]
      exact_mod_cast h
    · have h : ((I.hi : ℚ) : ℝ) ≤ (C + w : ℚ) := by
        push_cast
        linarith [hxlo, habshi, hw']
      exact_mod_cast h

private theorem complex_smul_width (q : ℚ) (hq : 0 ≤ q) (I : ComplexRatInterval) :
    ComplexRatInterval.width (I.smulRat q) = q * ComplexRatInterval.width I := by
  have hre := point_mul_width q hq I.re
  have him := point_mul_width q hq I.im
  change max ((RatInterval.point q).mul I.re).width
      ((RatInterval.point q).mul I.im).width = q * max I.re.width I.im.width
  rw [hre, him, ← mul_max_of_nonneg I.re.width I.im.width hq]

/-- The explicit circle input precision and exponential fuel make every
actually evaluated endpoint rectangle no wider than the requested target. -/
theorem circleNode_width_at_selected_precision (radius : ℚ) (hradius : 0 ≤ radius)
    (schedule : Schedule) (target : PosRat)
    (hprecision : schedule.inputPrecision = circleInputPrecision radius target)
    (hfuel : circleExpFuel radius schedule.mesh target ≤ schedule.fuel)
    {k : ℕ} (hk : k ≤ schedule.mesh) :
    ComplexRatInterval.width (circleNode radius schedule k) ≤ target.1 := by
  let τ := circleInnerTolerance radius target
  let c : ℚ := 2 * k / schedule.mesh
  let P := Transcendental.piInterval schedule.inputPrecision
  let K := (circleAngle schedule k).im
  let E := Transcendental.expInterval (circleAngle schedule k).re schedule.fuel
  let C := Transcendental.cosInterval K schedule.fuel
  let S := Transcendental.sinInterval K schedule.fuel
  have hτ0 : 0 < τ.1 := τ.2
  have hτone : τ.1 ≤ 1 / 1024 := by
    exact min_le_right _ _
  have hτtarget : τ.1 ≤ target.1 / (256 * (|radius| + 1)) := by
    exact min_le_left _ _
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hcle : c ≤ 2 := by
    apply (div_le_iff₀ (show (0 : ℚ) < schedule.mesh by
      exact_mod_cast schedule.mesh_pos)).2
    push_cast
    exact_mod_cast (Nat.mul_le_mul_left 2 hk)
  have hPw : P.width ≤ τ.1 := by
    dsimp [P]
    rw [hprecision]
    exact Transcendental.piInterval_width τ
  have hKw : K.width ≤ 2 * τ.1 := by
    change ((RatInterval.point c).mul P).width ≤ 2 * τ.1
    rw [point_mul_width c hc0 P]
    calc
      c * P.width ≤ 2 * P.width :=
        mul_le_mul_of_nonneg_right hcle (RatInterval.width_nonneg P)
      _ ≤ 2 * τ.1 := mul_le_mul_of_nonneg_left hPw (by norm_num)
  have hP0 : P.Subinterval (Transcendental.piInterval 0) := by
    exact CertifiedReal.approx_mono Transcendental.piName (Nat.zero_le _)
  have hP0w : (Transcendental.piInterval 0).width ≤ 1 := by
    norm_num [Transcendental.piInterval, Transcendental.piRaw,
      Transcendental.atanRaw, Transcendental.atanPartial, Transcendental.atanError,
      RatInterval.mul, RatInterval.sub, RatInterval.add, RatInterval.neg,
      RatInterval.point, RatInterval.width]
  have hPwide : P.width ≤ 1 :=
    (RatInterval.width_mono hP0).trans hP0w
  have hPabs : P.maxAbs ≤ 5 := by
    have h := interval_maxAbs_le_of_contains_width
      (C := 4) (w := 1) (Transcendental.piInterval_sound schedule.inputPrecision)
      (by simpa [abs_of_pos Real.pi_pos] using Real.pi_le_four) hPwide
    convert h using 1 <;> norm_num [P]
  have hKabs : K.maxAbs ≤ 10 := by
    change ((RatInterval.point c).mul P).maxAbs ≤ 10
    rw [point_mul_maxAbs c hc0 P]
    nlinarith
  have hmidK : K.Contains (Transcendental.intervalMid K : ℝ) := by
    constructor <;> exact_mod_cast (by
      dsimp [Transcendental.intervalMid]
      linarith [K.lo_le_hi])
  have hmidA : |Transcendental.intervalMid K| ≤ (12 : ℚ) := by
    exact (abs_le_max_abs_abs (by exact_mod_cast hmidK.1)
      (by exact_mod_cast hmidK.2)).trans (hKabs.trans (by norm_num))
  have hfuelExp :
      Transcendental.expPrecision
        0 τ ≤ schedule.fuel := by
    exact (le_max_left _ _).trans (by simpa [circleExpFuel, τ] using hfuel)
  have hfuelTrig : 32 * (τ.1.den + 1) * 12 ^ 2 ≤ schedule.fuel := by
    exact (le_max_right _ _).trans (by simpa [circleExpFuel, τ] using hfuel)
  have hEw : E.width ≤ τ.1 := by
    have hraw := Transcendental.expInterval_width
      (RatInterval.point 0) schedule.fuel
    have hscalar :
        (Transcendental.expScalar
          0 schedule.fuel).width ≤ τ.1 := by
      exact (RatInterval.width_mono (CertifiedReal.approx_mono
        (Transcendental.expName 0)
        hfuelExp)).trans
          (Transcendental.expScalar_width
            0 τ)
    change (Transcendental.expInterval (RatInterval.point 0) schedule.fuel).width ≤ τ.1
    exact hraw.trans (by
      simpa [RatInterval.point, Transcendental.intervalMid,
        Transcendental.intervalRadius, RatInterval.width]
        using hscalar)
  have hsinErr : Transcendental.sinError (Transcendental.intervalMid K) schedule.fuel ≤ τ.1 / 4 := by
    have herr := Transcendental.power_div_factorial_le (Transcendental.intervalMid K) 12
      (τ.1.den + 1) schedule.fuel 3 hmidA (by norm_num) (by omega) (by omega) hfuelTrig
    have hinv : 1 / ((τ.1.den + 1 : ℕ) : ℚ) ≤ τ.1 := by
      exact (div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (by exact_mod_cast Nat.le_succ τ.1.den)).trans
          (Transcendental.inv_den_le_of_pos
            τ.1 τ.2)
    calc
      _ ≤ 1 / ((4 * (τ.1.den + 1) : ℕ) : ℚ) := by
        simpa [Transcendental.sinError] using herr
      _ = (1 / ((τ.1.den + 1 : ℕ) : ℚ)) / 4 := by push_cast; field_simp
      _ ≤ τ.1 / 4 := div_le_div_of_nonneg_right hinv (by norm_num)
  have hcosErr : Transcendental.cosError (Transcendental.intervalMid K) schedule.fuel ≤ τ.1 / 4 := by
    have herr := Transcendental.power_div_factorial_le (Transcendental.intervalMid K) 12
      (τ.1.den + 1) schedule.fuel 2 hmidA (by norm_num) (by omega) (by omega) hfuelTrig
    have hinv : 1 / ((τ.1.den + 1 : ℕ) : ℚ) ≤ τ.1 := by
      exact (div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (by exact_mod_cast Nat.le_succ τ.1.den)).trans
          (Transcendental.inv_den_le_of_pos
            τ.1 τ.2)
    calc
      _ ≤ 1 / ((4 * (τ.1.den + 1) : ℕ) : ℚ) := by
        simpa [Transcendental.cosError] using herr
      _ = (1 / ((τ.1.den + 1 : ℕ) : ℚ)) / 4 := by push_cast; field_simp
      _ ≤ τ.1 / 4 := div_le_div_of_nonneg_right hinv (by norm_num)
  have hCw : C.width ≤ 5 * τ.1 / 2 :=
    (Transcendental.cosInterval_width K schedule.fuel).trans (by nlinarith)
  have hSw : S.width ≤ 5 * τ.1 / 2 :=
    (Transcendental.sinInterval_width K schedule.fuel).trans (by nlinarith)
  have hEcontains : E.Contains (1 : ℝ) := by
    change (Transcendental.expInterval (RatInterval.point 0) schedule.fuel).Contains 1
    simpa using Transcendental.expInterval_sound (RatInterval.point_sound (0 : ℚ)) schedule.fuel
  have hEabs : E.maxAbs ≤ 2 := by
    exact (interval_maxAbs_le_of_contains_width (C := 1) (w := τ.1)
      hEcontains (by norm_num) hEw).trans (by nlinarith)
  have hCcontains : C.Contains (Real.cos (Transcendental.intervalMid K : ℝ)) :=
    Transcendental.cosInterval_sound hmidK schedule.fuel
  have hScontains : S.Contains (Real.sin (Transcendental.intervalMid K : ℝ)) :=
    Transcendental.sinInterval_sound hmidK schedule.fuel
  have hCabs : C.maxAbs ≤ 2 := by
    exact (interval_maxAbs_le_of_contains_width (C := 1) (w := 5 * τ.1 / 2) hCcontains
      (by simpa only [Rat.cast_one] using
        Real.abs_cos_le_one (Transcendental.intervalMid K : ℝ)) hCw).trans (by nlinarith)
  have hSabs : S.maxAbs ≤ 2 := by
    exact (interval_maxAbs_le_of_contains_width (C := 1) (w := 5 * τ.1 / 2) hScontains
      (by simpa only [Rat.cast_one] using
        Real.abs_sin_le_one (Transcendental.intervalMid K : ℝ)) hSw).trans (by nlinarith)
  have hout := Transcendental.complexExp_width (circleAngle schedule k) schedule.fuel
  have hout' :
      ComplexRatInterval.width
          (Transcendental.complexExp (circleAngle schedule k) schedule.fuel) ≤
        2 * (max E.maxAbs 0 * max C.width S.width +
          max C.maxAbs S.maxAbs * max E.width 0) := by
    simpa only [E, C, S, K] using hout
  have hcomplex :
      ComplexRatInterval.width
          (Transcendental.complexExp (circleAngle schedule k) schedule.fuel) ≤
        14 * τ.1 := by
    change _ ≤ 14 * τ.1
    have hTW : max C.width S.width ≤ 5 * τ.1 / 2 := max_le hCw hSw
    have hTA : max C.maxAbs S.maxAbs ≤ 2 := max_le hCabs hSabs
    have hEA : max E.maxAbs 0 ≤ 2 := max_le hEabs (by norm_num)
    have hEW : max E.width 0 ≤ τ.1 := max_le hEw hτ0.le
    have hTW0 : 0 ≤ max C.width S.width :=
      (RatInterval.width_nonneg C).trans (le_max_left _ _)
    have hEW0 : 0 ≤ max E.width 0 := le_max_right _ _
    have hprod1 := mul_le_mul hEA hTW hTW0 (by norm_num : (0 : ℚ) ≤ 2)
    have hprod2 := mul_le_mul hTA hEW hEW0 (by norm_num : (0 : ℚ) ≤ 2)
    exact hout'.trans (by nlinarith)
  rw [circleNode, complex_smul_width radius hradius]
  rw [abs_of_nonneg hradius] at hτtarget
  have hden : 0 < 256 * (radius + 1) := by positivity
  have hprod : 256 * (radius + 1) * τ.1 ≤ target.1 :=
    by simpa [mul_comm, mul_left_comm] using (le_div_iff₀ hden).mp hτtarget
  calc
    radius * ComplexRatInterval.width
        (Transcendental.complexExp (circleAngle schedule k) schedule.fuel) ≤
        radius * (14 * τ.1) := mul_le_mul_of_nonneg_left hcomplex hradius
    _ ≤ target.1 := by nlinarith

/-- Given [a rational radius](hyp:radius), [a contour schedule](hyp:schedule), and [a natural-number endpoint index](hyp:k), the [exact circle node](goal) is the complex number $r\exp(2πik/m)$, where $m$ is the schedule's mesh size. -/
noncomputable def exactCircleNode (radius : ℚ) (schedule : Schedule) (k : ℕ) : ℂ :=
  (radius : ℂ) * Complex.exp
    (((2 : ℝ) * Real.pi * ((k : ℝ) / schedule.mesh)) * Complex.I)

/-- The angle rectangle contains the exact pure-imaginary angle at every
endpoint from zero through the terminal mesh endpoint. -/
theorem circleAngle_sound (schedule : Schedule) {k : ℕ} (hk : k ≤ schedule.mesh) :
    (circleAngle schedule k).Contains
      (((2 : ℝ) * Real.pi * ((k : ℝ) / schedule.mesh)) * Complex.I) := by
  constructor
  · simpa [circleAngle] using RatInterval.point_sound (0 : ℚ)
  · have h := RatInterval.mul_sound
      (RatInterval.point_sound (2 * k / schedule.mesh : ℚ))
      (Transcendental.piInterval_sound schedule.inputPrecision)
    have heq : (((2 * k / schedule.mesh : ℚ) : ℝ) * Real.pi) =
        ((((2 : ℝ) * Real.pi * ((k : ℝ) / schedule.mesh)) * Complex.I).im) := by
      push_cast
      simp
      ring
    rw [← heq]
    exact h

/-- For a rational radius, a quadrature schedule, and a mesh index `k`, if [`k`
does not exceed the schedule's mesh size](hyp:hk), then [the computed rational
circle-node rectangle at index `k` contains the exact complex circle point
`radius · exp(2πi · k / mesh)`](goal). -/
theorem circleNode_sound (radius : ℚ) (schedule : Schedule) {k : ℕ}
    (hk : k ≤ schedule.mesh) :
    (circleNode radius schedule k).Contains (exactCircleNode radius schedule k) := by
  exact ComplexRatInterval.smulRat_sound radius
    (Transcendental.complexExp_sound (circleAngle_sound schedule hk) schedule.fuel)

/-- The terminal endpoint `k = mesh`, which is explicitly used by the
trapezoidal program, is certified and denotes the same point as endpoint zero. -/
theorem circleNode_endpoint (radius : ℚ) (schedule : Schedule) :
    (circleNode radius schedule schedule.mesh).Contains (radius : ℂ) ∧
      exactCircleNode radius schedule schedule.mesh = (radius : ℂ) := by
  have hratio : ((schedule.mesh : ℝ) : ℂ) / schedule.mesh = 1 := by
    apply div_self
    exact_mod_cast schedule.mesh_pos.ne'
  have hexact : exactCircleNode radius schedule schedule.mesh = (radius : ℂ) := by
    rw [exactCircleNode, hratio]
    simp [Complex.exp_two_pi_mul_I]
  constructor
  · rw [← hexact]
    exact circleNode_sound radius schedule (le_refl schedule.mesh)
  · exact hexact

/-- Circle-node width propagation exposes radius scaling and the scheduled
complex-exponential approximation width. -/
theorem circleNode_width (radius : ℚ) (hradius : 0 ≤ radius)
    (schedule : Schedule) (k : ℕ) :
    ComplexRatInterval.width (circleNode radius schedule k) ≤
      radius * ComplexRatInterval.width (Transcendental.complexExp
        (circleAngle schedule k) schedule.fuel) := by
  let I := Transcendental.complexExp (circleAngle schedule k) schedule.fuel
  have hre : ((RatInterval.point radius).mul I.re).width = radius * I.re.width := by
    have h := mul_le_mul_of_nonneg_left I.re.lo_le_hi hradius
    simp [RatInterval.mul, RatInterval.point, RatInterval.width,
      min_eq_left h, max_eq_right h]
    ring
  have him : ((RatInterval.point radius).mul I.im).width = radius * I.im.width := by
    have h := mul_le_mul_of_nonneg_left I.im.lo_le_hi hradius
    simp [RatInterval.mul, RatInterval.point, RatInterval.width,
      min_eq_left h, max_eq_right h]
    ring
  change max ((RatInterval.point radius).mul I.re).width
      ((RatInterval.point radius).mul I.im).width ≤
        radius * max I.re.width I.im.width
  rw [hre, him, ← mul_max_of_nonneg I.re.width I.im.width hradius]

/-- For [a rational radius](hyp:radius), [a schedule](hyp:schedule), and [node and operation
ordinals](hyp:k,operation), [the manifest's stored schedule data and circle-node construction
agree definitionally with the supplied schedule](goal). -/
theorem circleNode_schedule_correspondence (radius : ℚ) (schedule : Schedule)
    (k operation : ℕ) :
    (circleNodeManifestEntry schedule k operation).schedule.operationCount =
        schedule.operationCount ∧
      (circleNodeManifestEntry schedule k operation).schedule.inputPrecision =
        schedule.inputPrecision ∧
      (circleNodeManifestEntry schedule k operation).schedule.fuel = schedule.fuel ∧
      (circleNodeManifestEntry schedule k operation).schedule.mesh = schedule.mesh ∧
      circleNode radius (circleNodeManifestEntry schedule k operation).schedule k =
        circleNode radius schedule k := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Causalean.Mathlib.Analysis.IntervalArithmetic.Contour

module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Probability.Kernel.Composition.MapComap
/-! Public cells, count-weighted pair statistics and the single Laplace release; scalar,
interval, dyadic tuning and inversion postprocessings are defined concretely. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign
-- @env: S3
variable (n : ℕ) (epsilon : ℝ)
variable (h : ℝ) -- @realizes h(public real radius)
variable (k : ℕ) -- @realizes k(public integer cell count)
-- @realizes delta(equal cell width)
open Classical in
/-- The equal cell width is twice the public radius divided by the public cell count. -/
def cellWidth : ℝ := 2*h/k
-- @realizes cells(left-closed equal cells; final endpoint included)
open Classical in
/-- Public cells partition the localization window with left endpoints included and only the final
right endpoint included. -/
def cell (j : Fin k) : Set Covariate :=
  {x | (x0 : ℝ) - h + j.val * cellWidth h k ≤ (x : ℝ) ∧
    ((x : ℝ) < (x0 : ℝ) - h + (j.val+1) * cellWidth h k ∨
      (j.val+1 = k ∧ (x : ℝ) = (x0 : ℝ) + h))}
open Classical in
/-- A cell selects the dataset indices whose covariates belong to that public cell. -/
def cellRecords (D : Dataset n) (j : Fin k) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (D i).1 ∈ cell h k j)
-- @realizes Nj(cell occupancy)
open Classical in
/-- Cell occupancy is the cardinality of the selected dataset indices. -/
def cellCount (D : Dataset n) (j : Fin k) : ℕ := (cellRecords n h k D j).card
-- @realizes KN(numerator pair kernel)
open Classical in
/-- The numerator pair kernel multiplies treatment difference by outcome difference. -/
def KN (z z' : O) : ℝ := (bit z.2.1 - bit z'.2.1) * (bit z.2.2 - bit z'.2.2)
-- @realizes KD(denominator pair kernel)
open Classical in
/-- The denominator pair kernel squares the treatment difference. -/
def KD (z z' : O) : ℝ := (bit z.2.1 - bit z'.2.1)^2
-- @realizes F(count-weighted symmetric pair sum; zero for fewer than two records)
open Classical in
/-- The count-weighted pair sum is zero below occupancy two, and otherwise weights the sum over
unordered pairs by occupancy divided by the number of pairs. -/
def pairContribution {s : ℕ} (K : O → O → ℝ) (z : Fin s → O) : ℝ :=
  if s < 2 then 0 else (s : ℝ) / Nat.choose s 2 *
    ∑ i : Fin s, ∑ l : Fin s, if i < l then K (z i) (z l) else 0

open Classical in
/-- A cell moment sum adds a record function across the selected dataset indices. -/
def cellSum (D : Dataset n) (j : Fin k) (v : O → ℝ) : ℝ :=
  ∑ i ∈ cellRecords n h k D j, v (D i)
open Classical in
/-- The numerator cell contribution uses the displayed closed treatment-outcome moment formula,
with zero below occupancy two. -/
def numeratorCell (D : Dataset n) (j : Fin k) : ℝ :=
  let s := cellCount n h k D j
  if s < 2 then 0 else
    2 * ((s : ℝ) * cellSum n h k D j (fun z => bit z.2.1 * bit z.2.2) -
      cellSum n h k D j (fun z => bit z.2.1) *
        cellSum n h k D j (fun z => bit z.2.2)) / ((s : ℝ) - 1)
open Classical in
/-- The denominator cell contribution uses the displayed closed treatment moment formula, with
zero below occupancy two. -/
def denominatorCell (D : Dataset n) (j : Fin k) : ℝ :=
  let s := cellCount n h k D j
  let a := cellSum n h k D j (fun z => bit z.2.1)
  if s < 2 then 0 else 2 * ((s : ℝ) * a - a^2) / ((s : ℝ) - 1)
-- @realizes SN(sum of closed numerator moment formulas)
open Classical in
/-- The numerator statistic sums the closed cell contributions. -/
def SN (D : Dataset n) : ℝ := ∑ j : Fin k, numeratorCell n h k D j
-- @realizes SD(sum of closed denominator moment formulas)
open Classical in
/-- The denominator statistic sums the closed cell contributions. -/
def SD (D : Dataset n) : ℝ := ∑ j : Fin k, denominatorCell n h k D j
/-- The sum of pairwise difference products equals the centered finite cross moment. [The displayed conclusion](goal) follows. -/
-- @node: pair_difference_sum
lemma pair_difference_sum (s : ℕ) (a b : Fin s → ℝ) :
    (∑ i : Fin s, ∑ j : Fin s, if i < j then (a i-a j)*(b i-b j) else 0) =
      (s : ℝ) * ∑ i, a i*b i - (∑ i, a i)*(∑ i, b i) := by
  classical
  let K := fun i j => (a i-a j)*(b i-b j)
  have hsymm : ∀ i j, K i j = K j i := by intros; dsimp [K]; ring
  have hsplit : ∀ i j, K i j = (if i < j then K i j else 0) +
      (if j < i then K i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, not_lt.mpr hij.le]
    · subst j; simp [K]
    · simp [hij, not_lt.mpr hij.le]
  have htwice : (∑ i : Fin s, ∑ j : Fin s, K i j) =
      2 * ∑ i : Fin s, ∑ j : Fin s, if i < j then K i j else 0 := by
    calc
      _ = ∑ i : Fin s, ∑ j : Fin s, ((if i < j then K i j else 0) +
          (if j < i then K i j else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hsplit i j
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j => if j < i then K i j else 0)]
        conv_lhs => rhs; arg 2; ext i; arg 2; ext j; rw [hsymm j i]
        ring
  have hfull : (∑ i : Fin s, ∑ j : Fin s, K i j) =
      2 * ((s : ℝ) * ∑ i, a i*b i - (∑ i, a i)*(∑ i, b i)) := by
    dsimp [K]
    simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  dsimp [K] at htwice
  linarith

/-- The pair kernels give the displayed count-weighted moment formulas, including s < 2.  [the theorem's stated inputs and assumptions](hyp:s,s,s,s), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:z). -/
-- @node: pair_moment_formulas
lemma pair_moment_formulas (s : ℕ) (z : Fin s → O) :
    pairContribution KN z = (if s < 2 then 0 else
      2 * ((s : ℝ) * ∑ i, bit (z i).2.1 * bit (z i).2.2 -
        (∑ i, bit (z i).2.1) * (∑ i, bit (z i).2.2)) / ((s : ℝ) - 1)) ∧
    pairContribution KD z = (if s < 2 then 0 else
      2 * ((s : ℝ) * ∑ i, bit (z i).2.1 - (∑ i, bit (z i).2.1)^2) /
        ((s : ℝ) - 1)) := by
  classical
  by_cases hs : s < 2
  · simp [pairContribution, hs]
  have hs0 : (s : ℝ) ≠ 0 := by
    have : 0 < s := by omega
    exact_mod_cast this.ne'
  have hs1 : (s : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast (show 2 ≤ s by omega)
    linarith
  have hN := pair_difference_sum s (fun i => bit (z i).2.1) (fun i => bit (z i).2.2)
  have hD := pair_difference_sum s (fun i => bit (z i).2.1) (fun i => bit (z i).2.1)
  have hbit : ∀ a : Bool, bit a * bit a = bit a := by
    intro a; cases a <;> norm_num [bit]
  simp only [hbit] at hD
  constructor
  · simp only [pairContribution, hs, if_false, KN]
    rw [hN, Nat.cast_choose_two ℝ]
    field_simp [hs0, hs1]
    <;> ring
  · simp only [pairContribution, hs, if_false, KD, pow_two]
    rw [hD, Nat.cast_choose_two ℝ]
    field_simp [hs0, hs1]
    <;> ring
/-- Each public cell is a Borel covariate set, including the final endpoint.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:j). -/
-- @node: measurableSet_cell
lemma measurableSet_cell (j : Fin k) : MeasurableSet (cell h k j) := by
  unfold cell
  measurability

/-- Counting cell members is measurable on the full dataset space. [The displayed conclusion](goal) follows. -/
-- @node: measurable_cellCount
@[fun_prop] lemma measurable_cellCount (j : Fin k) : Measurable (fun D => cellCount n h k D j) := by
  classical
  have heq : (fun D => cellCount n h k D j) =
      (fun D => ∑ i : Fin n, if (D i).1 ∈ cell h k j then (1 : ℕ) else 0) := by
    funext D
    simp [cellCount, cellRecords, Finset.sum_boole]
  rw [heq]
  apply Finset.measurable_fun_sum
  intro i hi
  exact measurable_const.ite ((measurableSet_cell h k j).preimage (by fun_prop))
    measurable_const

/-- Summing a measurable record function over a public cell is measurable. The result uses [the stated assumptions](hyp:hv) and establishes [the displayed conclusion](goal). -/
-- @node: measurable_cellSum
@[fun_prop] lemma measurable_cellSum (j : Fin k) (v : O → ℝ) (hv : Measurable v) :
    Measurable (fun D => cellSum n h k D j v) := by
  classical
  simp only [cellSum, cellRecords, Finset.sum_filter]
  apply Finset.measurable_fun_sum
  intro i hi
  exact (hv.comp (measurable_pi_apply i)).ite
    ((measurableSet_cell h k j).preimage (by fun_prop)) measurable_const

/-- Numerically encoding a binary mark is measurable. [The displayed conclusion](goal) follows. -/
@[fun_prop] lemma measurable_bit : Measurable bit := by
  fun_prop

/-- Each closed numerator cell contribution is measurable, including occupancies zero and one. [The displayed conclusion](goal) follows. -/
-- @node: measurable_numeratorCell
@[fun_prop] lemma measurable_numeratorCell (j : Fin k) :
    Measurable (fun D => numeratorCell n h k D j) := by
  unfold numeratorCell
  dsimp only
  refine measurable_const.ite (measurableSet_lt (measurable_cellCount n h k j) measurable_const) ?_
  fun_prop

/-- Each closed denominator cell contribution is measurable, including occupancies zero and one. [The displayed conclusion](goal) follows. -/
-- @node: measurable_denominatorCell
@[fun_prop] lemma measurable_denominatorCell (j : Fin k) :
    Measurable (fun D => denominatorCell n h k D j) := by
  unfold denominatorCell
  dsimp only
  refine measurable_const.ite (measurableSet_lt (measurable_cellCount n h k j) measurable_const) ?_
  fun_prop

/-- The numerator statistic is measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_SN
@[fun_prop] lemma measurable_SN : Measurable (SN n h k) := by
  unfold SN
  fun_prop
/-- The denominator statistic is measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_SD
@[fun_prop] lemma measurable_SD : Measurable (SD n h k) := by
  unfold SD
  fun_prop

-- @realizes info(public occupancy scale)
open Classical in
/-- The public occupancy scale is sample size times radius times the truncated expected cell
occupancy. -/
def info : ℝ := n*h*min 1 (n*cellWidth h k)
-- @realizes d0(public denominator floor)
open Classical in
/-- The public denominator floor is three sixty-fourths of the occupancy scale. -/
def d0 : ℝ := 3*info n h k/64
-- @realizes bias(public bias envelope)
open Classical in
/-- The public bias envelope retains the localization and rough-nuisance cell terms. -/
def bias : ℝ := 3*h + 24*(cellWidth h k)^(1/5 : ℝ)
-- @realizes Vbound(public second moment envelope)
open Classical in
/-- The public squared-error envelope retains localization, cell bias, occupancy and the Laplace
second-moment terms with the specified multiplier. -/
def Vbound : ℝ := 2^20 * (h^2 + (cellWidth h k)^(2/5 : ℝ) +
  (info n h k)⁻¹ + (epsilon*info n h k)^(-2 : ℤ))
open Classical in
/-- The joint query consists of the numerator and denominator statistics. -/
def pairQuery (D : Dataset n) : Fin 2 → ℝ := ![SN n h k D, SD n h k D]
/-- Both coordinates of the joint query are measurable functions of the dataset. [The displayed conclusion](goal) follows. -/
-- @node: measurable_pairQuery
@[fun_prop] lemma measurable_pairQuery : Measurable (pairQuery n h k) := by
  unfold pairQuery
  fun_prop
/-- The joint Laplace release is measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_pairRelease
@[fun_prop] lemma measurable_pairRelease :
    Measurable (Causalean.Stat.Privacy.laplaceMechPi (12/epsilon) (pairQuery n h k)) := by
  classical
  letI : SigmaFinite (Causalean.Stat.Privacy.laplaceMeasure (12/epsilon)) := by
    unfold Causalean.Stat.Privacy.laplaceMeasure
    infer_instance
  unfold Causalean.Stat.Privacy.laplaceMechPi
  apply Measure.measurable_of_measurable_coe
  intro E hE
  have hshift : Measurable (fun p : Dataset n × (Fin 2 → ℝ) => p.2 + pairQuery n h k p.1) := by
    fun_prop
  have hm : Measurable (fun p : Dataset n × (Fin 2 → ℝ) =>
      E.indicator (fun _ => (1 : ℝ≥0∞)) (p.2 + pairQuery n h k p.1)) :=
    (measurable_const.indicator hE).comp hshift
  have hmeas := hm.lintegral_prod_right' (ν := Measure.pi
    (fun _ : Fin 2 => Causalean.Stat.Privacy.laplaceMeasure (12/epsilon)))
  convert hmeas using 1
  funext D
  rw [Measure.map_apply (by fun_prop) hE]
  simpa only [Set.indicator, Set.preimage, Set.mem_setOf_eq, Pi.one_apply] using
    (lintegral_indicator_one (μ := Measure.pi
      (fun _ : Fin 2 => Causalean.Stat.Privacy.laplaceMeasure (12/epsilon)))
      (hE.preimage (show Measurable (fun z : Fin 2 → ℝ => z + pairQuery n h k D) by
        fun_prop))).symm
-- @node: def:private-ratio
-- @realizes release(single noisy pair release; Laplace substrate)
open Classical in
/-- The single joint Laplace release adds the specified independent noise to the two count-
weighted statistics. -/
def privateRatioRelease : Kernel (Dataset n) (Fin 2 → ℝ) where
  toFun := Causalean.Stat.Privacy.laplaceMechPi (12/epsilon) (pairQuery n h k)
  measurable' := measurable_pairRelease n epsilon h k

open Classical in
/-- Clipping truncates a real number to the specified lower and upper endpoints. -/
def clip (l u z : ℝ) : ℝ := max l (min u z)
-- @realizes Thk(floored clipped ratio postprocessing)
open Classical in
/-- The scalar postprocessing floors the noisy denominator and clips the ratio to the target
range. -/
def ratioMap (v : Fin 2 → ℝ) : ℝ := clip (-1) 1 (v 0 / max (d0 n h k) (v 1))
open Classical in
/-- Finite closed endpoints give an interval code with both endpoints included. -/
def closedInterval (l u : ℝ) : IntervalCode := .inr (l,u,true,true)
-- @realizes Ihk(conservative interval centered at the clipped ratio)
open Classical in
/-- The conservative interval centers the public radius at the clipped ratio and truncates it to
the target range. -/
def intervalMap (v : Fin 2 → ℝ) : IntervalCode :=
  closedInterval (max (-1) (ratioMap n h k v - Real.sqrt (10*Vbound n epsilon h k)))
    (min 1 (ratioMap n h k v + Real.sqrt (10*Vbound n epsilon h k)))
/-- The floored clipped ratio is measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_ratioMap
@[fun_prop] lemma measurable_ratioMap : Measurable (ratioMap n h k) := by
  unfold ratioMap clip
  fun_prop
/-- The conservative interval postprocessing is measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_intervalMap
@[fun_prop] lemma measurable_intervalMap : Measurable (intervalMap n epsilon h k) := by
  unfold intervalMap closedInterval
  fun_prop

open Classical in
/-- The scalar release is measurable postprocessing of the single joint noisy release. -/
def Thk : Kernel (Dataset n) ℝ :=
  (privateRatioRelease n epsilon h k).mapOfMeasurable (ratioMap n h k)
    (measurable_ratioMap n h k)
open Classical in
/-- The interval release is measurable postprocessing of that same single joint noisy release. -/
def Ihk : Kernel (Dataset n) IntervalCode :=
  (privateRatioRelease n epsilon h k).mapOfMeasurable (intervalMap n epsilon h k)
    (measurable_intervalMap n epsilon h k)

-- @realizes r(numerical benchmark)
open Classical in
/-- The numerical benchmark is the truncated maximum of the sampling, sparse-privacy and dense-
privacy terms. -/
def rate : ℝ := min 1 (max ((n : ℝ)^(-1/4 : ℝ))
  (max (((n : ℝ)^2*epsilon)^(-1/7 : ℝ)) (((n : ℝ)*epsilon)^(-1/2 : ℝ))))
open Classical in
/-- The public radius is the specified dyadic rounding of the benchmark scale. -/
def tunedH : ℝ := (2 : ℝ)^(-Int.ceil (Real.logb 2 (1/rate n epsilon)))
open Classical in
/-- The public integer cell count is twice the inverse fourth power of the dyadic radius. -/
def tunedK : ℕ := ⌊2*(tunedH n epsilon)^(-4 : ℤ)⌋₊
/-- The benchmark is strictly positive at every positive sample size.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hn). -/
-- @node: rate_pos
lemma rate_pos (hn : 0 < n) : 0 < rate n epsilon := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  unfold rate
  exact lt_min zero_lt_one (lt_max_of_lt_left (Real.rpow_pos_of_pos hn' _))

/-- Dyadic rounding brackets the benchmark between the radius and twice the radius.  [the theorem's stated inputs and assumptions](hyp:hn), and [the asserted conclusion follows](goal). -/
-- @node: tunedH_bounds
lemma tunedH_bounds (hn : 0 < n) :
    0 < tunedH n epsilon ∧ rate n epsilon / 2 ≤ tunedH n epsilon ∧
      tunedH n epsilon ≤ rate n epsilon := by
  have hr := rate_pos n epsilon hn
  let c := Int.ceil (Real.logb 2 (1 / rate n epsilon))
  have hc : Real.logb 2 (1 / rate n epsilon) ≤ (c : ℝ) := Int.le_ceil _
  have hc' : (c : ℝ) ≤ Real.logb 2 (1 / rate n epsilon) + 1 :=
    le_of_lt (Int.ceil_lt_add_one _)
  have hp : 0 < (2 : ℝ) ^ c := zpow_pos (by norm_num) _
  have hl : 1 / rate n epsilon ≤ (2 : ℝ) ^ c := by
    rw [← Real.rpow_intCast]
    exact (Real.logb_le_iff_le_rpow (by norm_num) (by positivity)).mp hc
  have hu : (2 : ℝ) ^ c ≤ 2 / rate n epsilon := by
    rw [← Real.rpow_intCast]
    calc
      (2 : ℝ) ^ (c : ℝ) ≤ 2 ^ (Real.logb 2 (1 / rate n epsilon) + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hc'
      _ = 2 / rate n epsilon := by
        rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num)
          (by norm_num) (by positivity), Real.rpow_one]
        ring
  change 0 < (2 : ℝ) ^ (-c) ∧ rate n epsilon / 2 ≤ (2 : ℝ) ^ (-c) ∧
    (2 : ℝ) ^ (-c) ≤ rate n epsilon
  rw [zpow_neg]
  refine ⟨inv_pos.mpr hp, ?_, ?_⟩
  · rw [← one_div]
    apply (le_div_iff₀ hp).mpr
    have hu' := (le_div_iff₀ hr).mp hu
    nlinarith
  · apply (inv_le_iff_one_le_mul₀ hp).mpr
    have hl' := (div_le_iff₀ hr).mp hl
    nlinarith

/-- The integer conversion is exact on the dyadic branch; its radius, cell count and
cell width obey the public construction constraints.  [the theorem's stated inputs and assumptions](hyp:hr), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hn,he). -/
-- @node: public_tuning_parameters
lemma public_tuning_parameters (hn : 2 ≤ n) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (hr : rate n epsilon < 1 / 8) :
    0 < tunedH n epsilon ∧ tunedH n epsilon ≤ 1 / 4 ∧ 2 ≤ tunedK n epsilon ∧
    (tunedK n epsilon : ℝ) = 2*(tunedH n epsilon)^(-4 : ℤ) ∧
    cellWidth (tunedH n epsilon) (tunedK n epsilon) = (tunedH n epsilon)^5 := by
  have hb := tunedH_bounds n epsilon (by omega)
  let c := Int.ceil (Real.logb 2 (1 / rate n epsilon))
  have hc : 0 ≤ c := by
    apply Int.ceil_nonneg
    apply Real.logb_nonneg (by norm_num)
    apply (le_div_iff₀ (rate_pos n epsilon (by omega))).mpr
    linarith
  have hex : 2 * (tunedH n epsilon) ^ (-4 : ℤ) =
      ((2 * 2 ^ (c.toNat * 4) : ℕ) : ℝ) := by
    unfold tunedH
    change 2 * ((2 : ℝ) ^ (-c)) ^ (-4 : ℤ) = _
    rw [← zpow_mul]
    have hm : -c * (-4 : ℤ) = ((c.toNat * 4 : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Int.toNat_of_nonneg hc]
      ring
    rw [hm, zpow_natCast]
    push_cast
    rfl
  have hk : tunedK n epsilon = 2 * 2 ^ (c.toNat * 4) := by
    unfold tunedK
    rw [hex, Nat.floor_natCast]
  have hkcast : (tunedK n epsilon : ℝ) = 2*(tunedH n epsilon)^(-4 : ℤ) := by
    rw [hk, ← hex]
  refine ⟨hb.1, by linarith [hb.2.2], ?_, hkcast, ?_⟩
  · rw [hk]
    have hp : 1 ≤ (2 : ℕ) ^ (c.toNat * 4) := Nat.one_le_pow _ _ (by omega)
    omega
  · unfold cellWidth
    rw [hkcast]
    rw [zpow_neg, zpow_ofNat]
    field_simp
    <;> ring
-- @node: def:public-tuning
-- @realizes Tstar(publicly tuned scalar kernel; fallback zero)
open Classical in
/-- Public tuning returns zero in the constant branch and otherwise uses the specified dyadic
pair-ratio release. -/
def publicTunedRelease : Kernel (Dataset n) ℝ :=
  if 1/8 ≤ rate n epsilon then Kernel.const _ (Measure.dirac 0)
  else Thk n epsilon (tunedH n epsilon) (tunedK n epsilon)
-- @realizes Istar(publicly tuned conservative interval kernel)
open Classical in
/-- Public tuning returns the entire target range in the constant branch and otherwise uses the
conservative pair-ratio interval. -/
def publicTunedInterval : Kernel (Dataset n) IntervalCode :=
  if 1/8 ≤ rate n epsilon then Kernel.const _ (Measure.dirac (closedInterval (-1) 1))
  else Ihk n epsilon (tunedH n epsilon) (tunedK n epsilon)
-- @realizes p(population cell mass)
open Classical in
/-- The population cell mass is the real measure of the cell under the design marginal. -/
def cellMass (P : CausalLaw) (j : Fin k) : ℝ := (PX P).real (cell h k j)
-- @realizes w(population occupancy weight)
open Classical in
/-- The population weight is expected occupancy multiplied by the probability of another record in
the same cell. -/
def occupancyWeight (P : CausalLaw) (j : Fin k) : ℝ :=
  n*cellMass h k P j * (1-(1-cellMass h k P j)^(n-1))
-- @realizes Wocc(total population occupancy weight)
open Classical in
/-- The total occupancy weight sums the population cell weights. -/
def Wocc (P : CausalLaw) : ℝ := ∑ j : Fin k, occupancyWeight n h k P j

open Classical in
/-- The conditional record law is the observed marginal restricted to the cell and normalized by
its mass. -/
def conditionalCellLaw (P : CausalLaw) (j : Fin k) : Measure O :=
  ((Pobs P) {z | z.1 ∈ cell h k j})⁻¹ • (Pobs P).restrict {z | z.1 ∈ cell h k j}
-- @realizes nu(conditional independent-pair numerator moment)
open Classical in
/-- The conditional numerator moment integrates the pair kernel under two independent draws from
the conditional cell law. -/
def nu (P : CausalLaw) (j : Fin k) : ℝ :=
  ∫ zz, KN zz.1 zz.2 ∂((conditionalCellLaw h k P j).prod (conditionalCellLaw h k P j))
-- @realizes dj(conditional independent-pair denominator moment)
open Classical in
/-- The conditional denominator moment integrates its pair kernel under those independent draws. -/
def dj (P : CausalLaw) (j : Fin k) : ℝ :=
  ∫ zz, KD zz.1 zz.2 ∂((conditionalCellLaw h k P j).prod (conditionalCellLaw h k P j))
-- @realizes Nbar(population expectation of numerator)
open Classical in
/-- The population numerator is the expectation of the count-weighted numerator under the dataset
law. -/
def Nbar (Q : Measure (Dataset n)) : ℝ := ∫ D, SN n h k D ∂Q
-- @realizes Dbar(population expectation of denominator)
open Classical in
/-- The population denominator is the expectation of the count-weighted denominator under the
dataset law. -/
def Dbar (Q : Measure (Dataset n)) : ℝ := ∫ D, SD n h k D ∂Q
end CausalSmith.Stat.PrivateCateRoughdesign

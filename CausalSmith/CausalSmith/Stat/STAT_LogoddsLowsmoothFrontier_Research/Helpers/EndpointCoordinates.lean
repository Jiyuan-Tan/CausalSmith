module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.EndpointRanges

/-! # Literal coordinate enclosures

The original-record ordered-pair expression propagates kernel widths through exact
binary marks and exact normalization. The empirical mean is rational and exact,
so both coordinate expressions inherit the kernel width bound without a sample
size loss. These are bounds on the actual expression tree.
-/
public section
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Finite expression sums preserve containment and add width bounds for any index type.](goal) Under [the stated assumptions](hyp:f). Under [the stated assumptions](hyp:h). -/
-- @node: endpoint_indexed_sum_enclosure
lemma endpoint_indexed_sum_enclosure {ι : Type*} (E : ArithmeticEngine) (q : ℕ)
    (xs : List RatInterval) (f : ι → BoxExpr) (v w : ι → ℝ) (js : List ι)
    (h : ∀ j ∈ js, ∃ B : RatInterval, (f j).eval E q xs = some B ∧
      B.Contains (v j) ∧ (B.width : ℝ) ≤ w j) :
    ∃ B : RatInterval, (expressionSum (js.map f)).eval E q xs = some B ∧
      B.Contains ((js.map v).sum) ∧ (B.width : ℝ) ≤ (js.map w).sum := by
  induction js with
  | nil =>
    refine ⟨RatInterval.point 0, rfl, ?_, ?_⟩
    · simp
    · simp [RatInterval.width, RatInterval.point]
  | cons j js ih =>
    obtain ⟨A, hA, hvA, hwA⟩ := h j (by simp)
    obtain ⟨B, hB, hvB, hwB⟩ := ih (fun l hl => h l (by simp [hl]))
    refine ⟨A.add B, ?_, ?_, ?_⟩
    · change (BoxExpr.add (f j) (expressionSum (js.map f))).eval E q xs = some (A.add B)
      simp [BoxExpr.eval, hA, hB]
    · simpa only [List.map_cons, List.sum_cons] using RatInterval.add_sound hvA hvB
    · rw [RatInterval.width_add]
      push_cast
      simpa only [List.map_cons, List.sum_cons] using add_le_add hwA hwB

/-- [Multiplication by an exact nonnegative rational scales the width exactly.](goal) Under [the stated assumptions](hyp:ha). -/
-- @node: endpoint_point_scale_width
lemma endpoint_point_scale_width (I : RatInterval) (a : ℚ) (ha : 0 ≤ a) :
    (I.mul (RatInterval.point a)).width = I.width*a ∧
    ((RatInterval.point a).mul I).width = a*I.width := by
  obtain ⟨hlo, hhi⟩ := endpoint_mul_point_endpoints I a ha
  constructor
  · change (I.mul (RatInterval.point a)).hi - (I.mul (RatInterval.point a)).lo =
      (I.hi-I.lo)*a
    rw [hlo, hhi]
    ring
  · have heq : (RatInterval.point a).mul I = I.mul (RatInterval.point a) := by
      have h := mul_le_mul_of_nonneg_left I.lo_le_hi ha
      simp [RatInterval.mul, RatInterval.point, mul_comm, min_eq_left h, max_eq_right h]
    rw [heq]
    change (I.mul (RatInterval.point a)).hi - (I.mul (RatInterval.point a)).lo =
      a*(I.hi-I.lo)
    rw [hlo, hhi]
    ring

/-- [The filtered list in the literal statistic enumerates precisely the ordered distinct pairs. [the stated conclusion](goal) holds. -/
-- @node: endpoint_pair_list_finset
lemma endpoint_pair_list_finset (n : ℕ) :
    ((Finset.univ : Finset (Fin n × Fin n)).toList.filter (fun ij => ij.1 ≠ ij.2)).toFinset =
      (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 ≠ ij.2) := by
  ext ij
  simp

/-- There are exactly n(n-1) ordered distinct pairs, including the small sample cases. [the stated conclusion](goal) holds. -/
-- @node: endpoint_pair_card
lemma endpoint_pair_card (n : ℕ) :
    (((Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 ≠ ij.2)).card : ℝ) =
      (n : ℝ)*((n : ℝ)-1) := by
  have heq : (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 ≠ ij.2) =
      (Finset.univ : Finset (Fin n)).offDiag := by
    ext ij
    simp
  rw [heq, Finset.offDiag_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [Nat.cast_sub (by nlinarith : n ≤ n*n)]
  push_cast
  ring

/-- Normalizing the actual ordered-pair sum cancels the pair count in the width bound. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hE,hq,hn,hX,hW,hV) hold, and [the stated conclusion follows](goal). -/
lemma endpoint_statistic_enclosure (E : ArithmeticEngine) (hE : E.Admissible)
    (q : ℕ) (hq : precisionError q ≤ 1/4) (n k : ℕ) (hn : 2 ≤ n)
    (o : Fin n → Record) (xs : List RatInterval) (X : Fin n → RatInterval)
    (hX : ∀ i, xs[2+i.val]? = some (X i) ∧
      (X i).Contains (covariate (o i)) ∧ -precisionError q ≤ ((X i).lo : ℝ) ∧
      ((X i).hi : ℝ) ≤ 1 + precisionError q ∧
      ((X i).width : ℝ) ≤ precisionError q)
    (W V : Fin n → ℚ) (hW : ∀ i, 0 ≤ W i ∧ W i ≤ 1)
    (hV : ∀ i, 0 ≤ V i ∧ V i ≤ 1) :
    ∃ B : RatInterval, (statisticExpression n k W V).eval E q xs = some B ∧
      B.Contains (((n : ℝ)*((n : ℝ)-1))⁻¹ *
        ∑ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 ≠ ij.2),
          projectionKernel k (covariate (o ij.1)) (covariate (o ij.2)) * (W ij.1 : ℝ) * V ij.2) ∧
      (B.width : ℝ) ≤ 160*(k : ℝ)^2*precisionError q := by
  let pairs := (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 ≠ ij.2)
  let js := (Finset.univ : Finset (Fin n × Fin n)).toList.filter (fun ij => ij.1 ≠ ij.2)
  have hjs : js.Nodup := Finset.nodup_toList _ |>.filter _
  have hjsFin : js.toFinset = pairs := endpoint_pair_list_finset n
  let f := fun ij : Fin n × Fin n =>
    BoxExpr.mul (kernelExpression k ij.1.val ij.2.val) (.constant (W ij.1*V ij.2))
  let v := fun ij : Fin n × Fin n =>
    projectionKernel k (covariate (o ij.1)) (covariate (o ij.2)) * (W ij.1 : ℝ) * V ij.2
  let w := 160*(k : ℝ)^2*precisionError q
  have hw : 0 ≤ w := by dsimp [w, precisionError]; positivity
  have hTerm (ij : Fin n × Fin n) (_ : ij ∈ js) :
      ∃ B : RatInterval, (f ij).eval E q xs = some B ∧ B.Contains (v ij) ∧
        (B.width : ℝ) ≤ w := by
    obtain ⟨hXi, hxi, hXlo, hXhi, hXW⟩ := hX ij.1
    obtain ⟨hZi, hzi, hZlo, hZhi, hZW⟩ := hX ij.2
    obtain ⟨B, hB, hvB, hwB⟩ := endpoint_kernel_enclosure E hE q hq k ij.1.val ij.2.val
      xs (X ij.1) (X ij.2) hXi hZi (covariate (o ij.1)) (covariate (o ij.2))
      hxi hzi hXlo hXhi hZlo hZhi hXW hZW
    have ha : 0 ≤ W ij.1*V ij.2 := mul_nonneg (hW _).1 (hV _).1
    have haOne : W ij.1*V ij.2 ≤ 1 := by
      simpa using mul_le_mul (hW ij.1).2 (hV ij.2).2 (hV _).1 (by norm_num : (0 : ℚ) ≤ 1)
    refine ⟨B.mul (RatInterval.point (W ij.1*V ij.2)), ?_, ?_, ?_⟩
    · simp [f, BoxExpr.eval, hB]
    · simpa only [v, Rat.cast_mul, mul_assoc] using
        RatInterval.mul_sound hvB (RatInterval.point_sound (W ij.1*V ij.2))
    · rw [(endpoint_point_scale_width B _ ha).1]
      push_cast
      have ha' : (W ij.1 : ℝ)*(V ij.2 : ℝ) ≤ 1 := by exact_mod_cast haOne
      have ha0 : 0 ≤ (W ij.1 : ℝ)*(V ij.2 : ℝ) := by exact_mod_cast ha
      calc
        _ ≤ w*((W ij.1 : ℝ)*V ij.2) := mul_le_mul_of_nonneg_right hwB ha0
        _ ≤ w := by simpa using mul_le_mul_of_nonneg_left ha' hw
  obtain ⟨B, hB, hvB, hwB⟩ := endpoint_indexed_sum_enclosure E q xs f v (fun _ => w)
    js hTerm
  let a : ℚ := 1/((n : ℚ)*((n : ℚ)-1))
  have hn' : (1 : ℚ) < n := by exact_mod_cast (show 1 < n by omega)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have haReal : (a : ℝ) = ((n : ℝ)*((n : ℝ)-1))⁻¹ := by
    dsimp [a]
    push_cast
    rw [one_div]
  have hPairs : (pairs.card : ℝ) = (n : ℝ)*((n : ℝ)-1) := endpoint_pair_card n
  have hPos : 0 < (n : ℝ)*((n : ℝ)-1) := by
    have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    positivity
  refine ⟨(RatInterval.point a).mul B, ?_, ?_, ?_⟩
  · change (BoxExpr.mul (.constant a) (expressionSum (js.map f))).eval E q xs = _
    simp only [BoxExpr.eval, hB]
    rfl
  · have hsum : (js.map v).sum = ∑ ij ∈ pairs, v ij := by
      rw [← List.sum_toFinset _ hjs, hjsFin]
    rw [hsum] at hvB
    simpa only [haReal] using RatInterval.mul_sound (RatInterval.point_sound a) hvB
  · rw [(endpoint_point_scale_width B a ha).2]
    push_cast
    have hsum : (js.map (fun _ => w)).sum = (pairs.card : ℝ)*w := by
      have hlen : js.length = pairs.card := by rw [← List.toFinset_card_of_nodup hjs, hjsFin]
      simp [hlen]
    rw [hsum] at hwB
    calc
      _ ≤ (a : ℝ)*((pairs.card : ℝ)*w) := mul_le_mul_of_nonneg_left hwB (by exact_mod_cast ha)
      _ = w := by rw [haReal, hPairs, ← mul_assoc, inv_mul_cancel₀ hPos.ne']; ring

/-- [The binary-label coordinate trees terminate, contain the exact sample coordinates,
and inherit the kernel width bounds since the empirical mean is evaluated exactly. [the documented result](goal) Under [the stated assumptions](hyp:hq,hn,hX). Under [the stated assumptions](hyp:hE). -/
lemma endpoint_coordinates_enclosure (E : ArithmeticEngine) (hE : E.Admissible)
    (q : ℕ) (hq : precisionError q ≤ 1/4) (n kC kS : ℕ) (hn : 2 ≤ n)
    (o : Fin n → Record) (xs : List RatInterval) (X : Fin n → RatInterval)
    (hX : ∀ i, xs[2+i.val]? = some (X i) ∧
      (X i).Contains (covariate (o i)) ∧ -precisionError q ≤ ((X i).lo : ℝ) ∧
      ((X i).hi : ℝ) ≤ 1 + precisionError q ∧
      ((X i).width : ℝ) ≤ precisionError q) :
    ∃ C S : RatInterval,
      (coordinateExpressions n kC kS o).1.eval E q xs = some C ∧
      (coordinateExpressions n kC kS o).2.eval E q xs = some S ∧
      C.Contains (cHat n kC o) ∧ S.Contains (sHat n kS o) ∧
      (C.width : ℝ) ≤ 160*(kC : ℝ)^2*precisionError q ∧
      (S.width : ℝ) ≤ 160*(kS : ℝ)^2*precisionError q := by
  let A : Fin n → ℚ := fun i => if (o i).2.1 then 1 else 0
  let Y : Fin n → ℚ := fun i => if (o i).2.2 then 1 else 0
  have hA (i : Fin n) : 0 ≤ A i ∧ A i ≤ 1 := by dsimp [A]; split <;> norm_num
  have hY (i : Fin n) : 0 ≤ Y i ∧ Y i ≤ 1 := by dsimp [Y]; split <;> norm_num
  have hAc (i : Fin n) : (A i : ℝ) = treatment (o i) := by
    dsimp [A, treatment]; split <;> norm_num
  have hYc (i : Fin n) : (Y i : ℝ) = outcome (o i) := by
    dsimp [Y, outcome]; split <;> norm_num
  have hW (i : Fin n) : 0 ≤ A i*(1-Y i) ∧ A i*(1-Y i) ≤ 1 := by
    constructor
    · exact mul_nonneg (hA i).1 (sub_nonneg.mpr (hY i).2)
    · simpa using mul_le_mul (hA i).2 (show 1-Y i ≤ 1 by linarith [(hY i).1])
        (sub_nonneg.mpr (hY i).2) (by norm_num : (0 : ℚ) ≤ 1)
  have hV (i : Fin n) : 0 ≤ (1-A i)*Y i ∧ (1-A i)*Y i ≤ 1 := by
    constructor
    · exact mul_nonneg (sub_nonneg.mpr (hA i).2) (hY i).1
    · simpa using mul_le_mul (show 1-A i ≤ 1 by linarith [(hA i).1]) (hY i).2
        (hY i).1 (by norm_num : (0 : ℚ) ≤ 1)
  obtain ⟨B, hB, hvB, hwB⟩ := endpoint_statistic_enclosure E hE q hq n kC hn o xs X hX A Y hA hY
  obtain ⟨S, hS, hvS, hwS⟩ := endpoint_statistic_enclosure E hE q hq n kS hn o xs X hX
    (fun i => A i*(1-Y i)) (fun i => (1-A i)*Y i) hW hV
  let m : ℚ := (n : ℚ)⁻¹ * ∑ i, A i*Y i
  have hm : (m : ℝ) = (n : ℝ)⁻¹ * ∑ i, treatment (o i)*outcome (o i) := by
    simp [m, hAc, hYc]
  have hvB' : B.Contains (projectionStatistic n kC treatment outcome o) := by
    simpa only [projectionStatistic, hAc, hYc] using hvB
  have hvS' : S.Contains (sHat n kS o) := by
    simpa only [sHat, projectionStatistic, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, hAc, hYc] using hvS
  refine ⟨(RatInterval.point m).sub B, S, ?_, ?_, ?_, hvS', ?_, hwS⟩
  · change (BoxExpr.sub (.constant m) (statisticExpression n kC A Y)).eval E q xs = _
    simp only [BoxExpr.eval, hB]
    rfl
  · exact hS
  · simpa only [hm, cHat] using RatInterval.sub_sound (RatInterval.point_sound m) hvB'
  · rw [RatInterval.width_sub]
    simpa [RatInterval.width, RatInterval.point] using hwB

/-- [A finite list of successful input queries evaluates to the list of their selected boxes.](goal) Under [the stated assumptions](hyp:f). Under [the stated assumptions](hyp:h). -/
-- @node: endpoint_mapM_boxes
lemma endpoint_mapM_boxes {ι : Type*} (f : ι → Option RatInterval) (X : ι → RatInterval)
    (js : List ι) (h : ∀ i ∈ js, f i = some (X i)) :
    js.mapM f = some (js.map X) := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp [List.mapM_cons, h i (by simp), ih (fun j hj => h j (by simp [hj]))]

/-- [All literal endpoint inputs are available at the prescribed precision, with
the supplied raw covariate boxes at their exact input positions. [the documented result](goal) Under [the stated assumptions](hyp:hN). -/
lemma endpoint_inputs_contract (N : NamingPolicy) (hN : N.Admissible)
    (n : ℕ) (α β : ℝ) (_hab : ExponentDomain α β) (o : Fin n → Record) (q : ℕ) :
    ∃ xs : List RatInterval, ∃ X : Fin n → RatInterval,
      endpointInputs N n α β o q = some xs ∧
      (∀ i, xs[2+i.val]? = some (X i) ∧
        (X i).Contains (covariate (o i)) ∧ -precisionError q ≤ ((X i).lo : ℝ) ∧
        ((X i).hi : ℝ) ≤ 1 + precisionError q ∧
        ((X i).width : ℝ) ≤ precisionError q) := by
  let X : Fin n → RatInterval := fun i => N.covariateName n α β o i q
  refine ⟨N.alphaName n α β q :: N.betaName n α β q :: (List.finRange n).map X,
    X, rfl, ?_⟩
  intro i
  have hName := (hN.2.1 n α β o i).1 q
  obtain ⟨hlo, hhi⟩ := endpoint_raw_box_bounds (X i) (covariate (o i)) 0 1
    (precisionError q) hName.2.2.1 (unitInterval.nonneg _) (unitInterval.le_one _)
    hName.2.2.2
  refine ⟨?_, hName.2.2.1, ?_, hhi, hName.2.2.2⟩
  · simp [List.getElem?_cons, i.isLt]
  · simpa using hlo

/-- [At the actual endpoint budget and with the actual naming policy, both literal
coordinate evaluations succeed with the roadmap's width bounds. [the documented result](goal) Under [the stated assumptions](hyp:hN,hn,hab). Under [the stated assumptions](hyp:hE). -/
-- @node: endpoint_coordinates_budget_contract
lemma endpoint_coordinates_budget_contract (E : ArithmeticEngine) (hE : E.Admissible)
    (N : NamingPolicy) (hN : N.Admissible) (n kC kS : ℕ) (hn : 2 ≤ n)
    (α β : ℝ) (hab : ExponentDomain α β) (o : Fin n → Record) :
    ∃ xs : List RatInterval, ∃ C S : RatInterval,
      endpointInputs N n α β o (qEnd n kC kS) = some xs ∧
      (coordinateExpressions n kC kS o).1.eval E (qEnd n kC kS) xs = some C ∧
      (coordinateExpressions n kC kS o).2.eval E (qEnd n kC kS) xs = some S ∧
      C.Contains (cHat n kC o) ∧ S.Contains (sHat n kS o) ∧
      (C.width : ℝ) ≤ 160*(kC : ℝ)^2*precisionError (qEnd n kC kS) ∧
      (S.width : ℝ) ≤ 160*(kS : ℝ)^2*precisionError (qEnd n kC kS) := by
  obtain ⟨xs, X, hinputs, hX⟩ := endpoint_inputs_contract N hN n α β hab o (qEnd n kC kS)
  obtain ⟨C, S, hC, hS, hc, hs, hwC, hwS⟩ := endpoint_coordinates_enclosure E hE
    (qEnd n kC kS) (endpoint_precision_small n kC kS) n kC kS hn o xs X hX
  exact ⟨xs, C, S, hinputs, hC, hS, hc, hs, hwC, hwS⟩

end CausalSmith.Stat.LogoddsLowsmoothFrontier

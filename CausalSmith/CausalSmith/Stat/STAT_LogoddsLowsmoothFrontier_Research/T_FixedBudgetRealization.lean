module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.EndpointQuotients

/-! # T FixedBudgetRealization

Unit-width enclosure rounding controls the selected ranks. Ideal endpoint ordering,
rational output shape, and outward clipping assemble realization from the proved
rank-budget contract and the proved literal endpoint box-evaluation estimates. -/
@[expose] public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The literal output has rational closed ordered endpoints in the public effect region. -/
def RationalOutputShape (B : EffectInterval) : Prop :=
  ∃ l u : ℚ, B.val = ((l : ℝ),(u : ℝ),true,true) ∧
    -1/2 ≤ l ∧ l ≤ u ∧ u ≤ 1/2

/-- The rational output has the prescribed shape even on totalized inputs. [the stated conclusion](goal) holds. -/
-- @node: upperOutput_rational_shape
lemma upperOutput_rational_shape (E : ArithmeticEngine) (N : NamingPolicy)
    (n : ℕ) (α β : ℝ) (o : Fin n → Record) :
    RationalOutputShape (upperOutput E N n α β o) := by
  have h := upperRawBox_subinterval E N n α β o
  refine ⟨(upperRawBox E N n α β o).lo, (upperRawBox E N n α β o).hi,
    rfl, ?_, (upperRawBox E N n α β o).lo_le_hi, ?_⟩
  · norm_num [fullEffectBox, rationalBox] at h
    convert h.1 using 1; norm_num
  · norm_num [fullEffectBox, rationalBox] at h
    exact h.2

/-- Ceiling the upper endpoint of a unit-width enclosure gives the strict two-unit
rank excess in the roadmap; the target's unit lower bound controls the multiplicative excess. [the documented result](goal) Under [the stated assumptions](hyp:hR,hContains,hWidth). -/
-- @node: enclosure_ceiling_rank_bounds
lemma enclosure_ceiling_rank_bounds
    (I : Causalean.Mathlib.Analysis.IntervalArithmetic.RatInterval) (R : ℝ)
    (hR : 1 ≤ R) (hContains : I.Contains R) (hWidth : I.width ≤ 1) :
    R ≤ (((⌈I.hi⌉ : ℤ).toNat : ℕ) : ℝ) ∧
    (((⌈I.hi⌉ : ℤ).toNat : ℕ) : ℝ) < R+2 ∧ R+2 ≤ 3*R := by
  have hhi : (0 : ℚ) ≤ I.hi := by
    exact_mod_cast (show (0 : ℝ) ≤ I.hi from (by linarith [hContains.2]))
  have hceil : (0 : ℤ) ≤ ⌈I.hi⌉ := Int.ceil_nonneg hhi
  have hcast : (((⌈I.hi⌉ : ℤ).toNat : ℕ) : ℝ) = (⌈I.hi⌉ : ℤ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hceil]
  rw [hcast]
  have hceilLower : (I.hi : ℝ) ≤ (⌈I.hi⌉ : ℤ) := by
    exact_mod_cast Int.le_ceil I.hi
  have hceilUpper : ((⌈I.hi⌉ : ℤ) : ℝ) < (I.hi : ℝ)+1 := by
    exact_mod_cast Int.ceil_lt_add_one I.hi
  have hwidth : (I.hi : ℝ) - I.lo ≤ 1 := by
    exact_mod_cast hWidth
  exact ⟨hContains.2.trans hceilLower, by linarith [hContains.1], by linarith⟩

/-- [Both exact rank targets are at least one on the public exponent domain.](goal) Under [the stated assumptions](hyp:hn,hab). -/
-- @node: rank_targets_one_le
lemma rank_targets_one_le (n : ℕ) (hn : 2 ≤ n) (α β : ℝ)
    (hab : ExponentDomain α β) :
    1 ≤ (n : ℝ)^(2/(2*α+2*β+1)) ∧ 1 ≤ (n : ℝ)^(2/(4*β+1)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hα : 0 < α := hab.1.trans hab.2.2.1
  have hβ : 0 < β := hab.1
  exact ⟨Real.one_le_rpow hn' (by positivity), Real.one_le_rpow hn' (by positivity)⟩

/-- [Clipped odds inversion stays inside the public effect interval. [the stated conclusion](goal) holds. -/
-- @node: inversion_effect_bounds
lemma inversion_effect_bounds (c d : ℝ) :
    -(1/2 : ℝ) ≤ inversion c d ∧ inversion c d ≤ 1/2 := by
  have hExp : Real.exp (-1/2 : ℝ) ≤ Real.exp (1/2) :=
    Real.exp_le_exp.mpr (by norm_num)
  have hlo : Real.exp (-(1/2 : ℝ)) ≤
      clip (Real.exp (-1/2)) (Real.exp (1/2)) (1+c/d) := by
    simpa only [clip, neg_div] using le_max_left (Real.exp (-1/2))
      (min (Real.exp (1/2)) (1+c/d))
  have hhi : clip (Real.exp (-1/2)) (Real.exp (1/2)) (1+c/d) ≤ Real.exp (1/2) :=
    max_le hExp (min_le_left _ _)
  constructor
  · simpa [inversion] using Real.log_le_log (Real.exp_pos (-(1/2 : ℝ))) hlo
  · simpa [inversion] using Real.log_le_log ((Real.exp_pos (-(1/2 : ℝ))).trans_le hlo) hhi

/-- For a positive denominator, clipped odds inversion is nondecreasing in its numerator. Under the stated assumptions. [The stated hypotheses](hyp:hd) hold, and [the stated conclusion follows](goal). -/
-- @node: inversion_mono_numerator
lemma inversion_mono_numerator (d : ℝ) (hd : 0 < d) :
    Monotone (fun c => inversion c d) := by
  intro c c' hcc'
  have hclip : clip (Real.exp (-1/2)) (Real.exp (1/2)) (1+c/d) ≤
      clip (Real.exp (-1/2)) (Real.exp (1/2)) (1+c'/d) := by
    apply max_le_max_left
    apply min_le_min_left
    exact add_le_add_right (div_le_div_of_nonneg_right hcc' hd.le) 1
  apply Real.log_le_log _ hclip
  simpa only [clip] using (Real.exp_pos (-1/2 : ℝ)).trans_le
    (le_max_left (Real.exp (-1/2)) (min (Real.exp (1/2)) (1+c/d)))

/-- [The ideal interval is ordered on every sample and lies in the public effect region. [the stated conclusion](goal) holds. -/
-- @node: idealEndpoints_ordered_bounded
lemma idealEndpoints_ordered_bounded (E : ArithmeticEngine) (N : NamingPolicy)
    (n : ℕ) (α β : ℝ) (o : Fin n → Record) :
    -(1/2 : ℝ) ≤ (idealEndpoints E N n α β o).1 ∧
    (idealEndpoints E N n α β o).1 ≤ (idealEndpoints E N n α β o).2 ∧
    (idealEndpoints E N n α β o).2 ≤ 1/2 := by
  unfold idealEndpoints
  dsimp only
  refine ⟨le_min (inversion_effect_bounds _ _).1 (inversion_effect_bounds _ _).1,
    ?_, max_le (inversion_effect_bounds _ _).2 (inversion_effect_bounds _ _).2⟩
  apply (min_le_left _ _).trans
  apply le_trans _ (le_max_left _ _)
  apply inversion_mono_numerator
  · have hfloor : (0 : ℝ) < denominatorFloor := by norm_num [denominatorFloor]
    exact hfloor.trans_le (le_max_left _ _)
  · have hb : 0 ≤ 8 * ((resolutions E N n α β).1 : ℝ)^(-(α+β)) +
        Real.sqrt (20 * varianceRadius n (resolutions E N n α β).1) := by positivity
    linarith

/-- Outward endpoint enclosures survive intersection with the effect region, and
their widths bound the extra length. This step uses no arithmetic approximation estimate. [the documented result](goal) Under [the stated assumptions](hyp:hn,hRank,hEnd,hL,hR,hLW,hRW). -/
-- @node: upperOutput_enclosure_guarantees
lemma upperOutput_enclosure_guarantees (E : ArithmeticEngine) (N : NamingPolicy)
    (n : ℕ) (hn : 2 ≤ n) (α β : ℝ) (o : Fin n → Record)
    (c s L R : Causalean.Mathlib.Analysis.IntervalArithmetic.RatInterval)
    (hRank : rankBoxes E N n α β = some (c, s))
    (hEnd : endpointBoxes E N n α β o = some (L, R))
    (hL : L.Contains (idealEndpoints E N n α β o).1)
    (hR : R.Contains (idealEndpoints E N n α β o).2)
    (ε : ℝ) (hLW : (L.width : ℝ) ≤ ε) (hRW : (R.width : ℝ) ≤ ε) :
    Set.Icc (idealEndpoints E N n α β o).1 (idealEndpoints E N n α β o).2 ⊆
      intervalSet (upperOutput E N n α β o) ∧
    intervalLength (upperOutput E N n α β o) ≤
      (idealEndpoints E N n α β o).2 - (idealEndpoints E N n α β o).1 + 2*ε := by
  obtain ⟨hlo, horder, hhi⟩ := idealEndpoints_ordered_bounded E N n α β o
  have hLR : L.lo ≤ R.hi := by
    exact_mod_cast hL.1.trans (horder.trans hR.2)
  have hLoClip : ((max L.lo (-1/2) : ℚ) : ℝ) ≤ (idealEndpoints E N n α β o).1 := by
    push_cast
    exact max_le hL.1 (by linarith)
  have hHiClip : (idealEndpoints E N n α β o).2 ≤ ((min R.hi (1/2) : ℚ) : ℝ) := by
    push_cast
    exact le_min hR.2 hhi
  have hClip : max L.lo (-1/2) ≤ min R.hi (1/2) := by
    exact_mod_cast hLoClip.trans (horder.trans hHiClip)
  have hraw : upperRawBox E N n α β o =
      ⟨max L.lo (-1/2), min R.hi (1/2), hClip⟩ := by
    unfold upperRawBox
    rw [if_neg (by omega), hRank, hEnd]
    simp only [rationalBox, min_eq_left hLR, max_eq_right hLR]
    have hflo : fullEffectBox.lo = (-1/2 : ℚ) := by norm_num [fullEffectBox, rationalBox]
    have hfhi : fullEffectBox.hi = (1/2 : ℚ) := by norm_num [fullEffectBox, rationalBox]
    simp only [boxIntersection, hflo, hfhi]
    rw [dif_pos hClip]
  have hLength : intervalLength (upperOutput E N n α β o) =
      ((min R.hi (1/2) : ℚ) : ℝ) - ((max L.lo (-1/2) : ℚ) : ℝ) := by
    simp only [intervalLength, upperOutput, hraw]
  constructor
  · intro x hx
    have hxlo := hLoClip.trans hx.1
    have hxhi := hx.2.trans hHiClip
    simp only [intervalSet, upperOutput, hraw, Set.mem_ofPred_eq]
    exact ⟨(lt_or_eq_of_le hxlo).imp_right (fun h => ⟨True.intro, h⟩),
      (lt_or_eq_of_le hxhi).imp_right (fun h => ⟨True.intro, h⟩)⟩
  · rw [hLength]
    have hLW' : (L.hi : ℝ) - L.lo ≤ ε := by exact_mod_cast hLW
    have hRW' : (R.hi : ℝ) - R.lo ≤ ε := by exact_mod_cast hRW
    have hmax : (L.lo : ℝ) ≤ ((max L.lo (-1/2) : ℚ) : ℝ) := by
      exact_mod_cast le_max_left L.lo (-1/2)
    have hmin : ((min R.hi (1/2) : ℚ) : ℝ) ≤ R.hi := by
      exact_mod_cast min_le_left R.hi (1/2)
    linarith [hL.2, hR.1]
-- @node: lem:fixed-budget-realization
/-- Primitive contracts alone suffice at both prescribed budgets, and the floor policy is valid. Under the stated assumptions. [The stated conclusion follows](goal). -/
lemma fixed_budget_realization : NamingPolicy.Admissible dyadicFloorPolicy ∧
  ∀ (E : ArithmeticEngine), E.Admissible →
  ∀ (N : NamingPolicy) (hN : N.Admissible) (n : ℕ), 2 ≤ n →
  ∀ (α β : ℝ), ExponentDomain α β → ∀ o : Fin n → Record,
    let k := resolutions E N n α β
    let RC := (n : ℝ)^(2/(2*α+2*β+1))
    let RS := (n : ℝ)^(2/(4*β+1))
    let lr := idealEndpoints E N n α β o
    ∃ c s L R : Causalean.Mathlib.Analysis.IntervalArithmetic.RatInterval,
      rankBoxes E N n α β = some (c,s) ∧ c.width ≤ 1 ∧ s.width ≤ 1 ∧
      RC ≤ k.1 ∧ (k.1 : ℝ) < RC+2 ∧ RC+2 ≤ 3*RC ∧
      RS ≤ k.2 ∧ (k.2 : ℝ) < RS+2 ∧ RS+2 ≤ 3*RS ∧
      endpointBoxes E N n α β o = some (L,R) ∧
      L.Contains lr.1 ∧ R.Contains lr.2 ∧
      (L.width : ℝ) ≤ 1/(n : ℝ) ∧ (R.width : ℝ) ≤ 1/(n : ℝ) ∧
      Set.Icc lr.1 lr.2 ⊆ intervalSet (upperOutput E N n α β o) ∧
      intervalLength (upperOutput E N n α β o) ≤ lr.2-lr.1+2/(n : ℝ) ∧
      RationalOutputShape (upperOutput E N n α β o) ∧
      Measurable (upperInterval E N hN n α β).output := by
  refine ⟨dyadicFloorPolicy_admissible, ?_⟩
  intro E hE N hN n hn α β hab o
  dsimp only
  -- The rank-box contract includes domain safety, containment, and unit width.
  obtain ⟨c, s, hRank, hcW, hsW, hcR, hsR⟩ :
      ∃ c s : Causalean.Mathlib.Analysis.IntervalArithmetic.RatInterval,
        rankBoxes E N n α β = some (c, s) ∧ c.width ≤ 1 ∧ s.width ≤ 1 ∧
        c.Contains ((n : ℝ)^(2/(2*α+2*β+1))) ∧
        s.Contains ((n : ℝ)^(2/(4*β+1))) := by
    obtain ⟨c, s, hRank, hcR, hsR, hcW, hsW⟩ :=
      rankBoxes_rank_budget_contract E hE N hN n (by omega) α β hab
    exact ⟨c, s, hRank, hcW, hsW, hcR, hsR⟩
  obtain ⟨hcOne, hsOne⟩ := rank_targets_one_le n hn α β hab
  obtain ⟨hcLower, hcUpper, hcTriple⟩ :=
    enclosure_ceiling_rank_bounds c _ hcOne hcR hcW
  obtain ⟨hsLower, hsUpper, hsTriple⟩ :=
    enclosure_ceiling_rank_bounds s _ hsOne hsR hsW
  have hk : resolutions E N n α β = ((⌈c.hi⌉ : ℤ).toNat, (⌈s.hi⌉ : ℤ).toNat) := by
    simp only [resolutions, hRank]
  -- Literal coordinates now have the roadmap widths at the actual endpoint inputs.
  obtain ⟨L, R, hEnd, hL, hR, hLW, hRW⟩ :
      ∃ L R : Causalean.Mathlib.Analysis.IntervalArithmetic.RatInterval,
        endpointBoxes E N n α β o = some (L, R) ∧
        L.Contains (idealEndpoints E N n α β o).1 ∧
        R.Contains (idealEndpoints E N n α β o).2 ∧
        (L.width : ℝ) ≤ 1/(n : ℝ) ∧ (R.width : ℝ) ≤ 1/(n : ℝ) := by
    obtain ⟨xs, C, S, hInputs, hC, hS, hContainsC, hContainsS, hWidthC, hWidthS⟩ :=
      endpoint_coordinates_budget_contract E hE N hN n
        (resolutions E N n α β).1 (resolutions E N n α β).2 hn α β hab o
    have hkC : 1 ≤ (resolutions E N n α β).1 := by
      have h : (1 : ℝ) ≤ (resolutions E N n α β).1 := by
        rw [hk]
        exact hcOne.trans hcLower
      exact_mod_cast h
    have hkS : 1 ≤ (resolutions E N n α β).2 := by
      have h : (1 : ℝ) ≤ (resolutions E N n α β).2 := by
        rw [hk]
        exact hsOne.trans hsLower
      exact_mod_cast h
    obtain ⟨BC, BS, hEvalBC, hEvalBS, hContainsBC, hContainsBS, hWidthBC, hWidthBS⟩ :=
      endpoint_radii_budget_contract E hE N hN n
        (resolutions E N n α β).1 (resolutions E N n α β).2 hn hkC hkS α β hab o xs hInputs
    obtain ⟨Dm, Dp, hEvalDm, hEvalDp, hContainsDm, hContainsDp,
        hDmLo, hDmHi, hDpLo, hDpHi, hWidthDm, hWidthDp⟩ :=
      endpoint_denominator_corners E
        (qEnd n (resolutions E N n α β).1 (resolutions E N n α β).2) n
        (resolutions E N n α β).1 (resolutions E N n α β).2 hkS xs o β
        S BS hS hEvalBS hContainsS hContainsBS hWidthS hWidthBS
    obtain ⟨L, R, hEvalL, hEvalR, hContainsL, hContainsR, hWidthL, hWidthR⟩ :
        ∃ L R : Causalean.Mathlib.Analysis.IntervalArithmetic.RatInterval,
          (endpointExpressions n (resolutions E N n α β).1
            (resolutions E N n α β).2 o).1.eval E
              (qEnd n (resolutions E N n α β).1 (resolutions E N n α β).2) xs = some L ∧
          (endpointExpressions n (resolutions E N n α β).1
            (resolutions E N n α β).2 o).2.eval E
              (qEnd n (resolutions E N n α β).1 (resolutions E N n α β).2) xs = some R ∧
          L.Contains (idealEndpoints E N n α β o).1 ∧
          R.Contains (idealEndpoints E N n α β o).2 ∧
          (L.width : ℝ) ≤ 1/(n : ℝ) ∧ (R.width : ℝ) ≤ 1/(n : ℝ) := by
      obtain ⟨Cm, Cp, heCm, heCp, hvCm, hvCp, hmLo, hmHi, hpLo, hpHi, hwCm, hwCp⟩ :=
        endpoint_numerator_corners E n (resolutions E N n α β).1
          (resolutions E N n α β).2 hn hkC α β hab o xs C BC
          hC hEvalBC hContainsC hContainsBC hWidthC hWidthBC
      obtain ⟨Lmm, heLmm, hvLmm, hwLmm⟩ := endpoint_inversion_budget_contract E hE n
        (resolutions E N n α β).1 (resolutions E N n α β).2 hn xs _ _ Cm Dm _ _
        heCm hEvalDm hvCm hContainsDm hDmLo hmLo hmHi hwCm hWidthDm
      obtain ⟨Lmp, heLmp, hvLmp, hwLmp⟩ := endpoint_inversion_budget_contract E hE n
        (resolutions E N n α β).1 (resolutions E N n α β).2 hn xs _ _ Cm Dp _ _
        heCm hEvalDp hvCm hContainsDp hDpLo hmLo hmHi hwCm hWidthDp
      obtain ⟨Rpm, heRpm, hvRpm, hwRpm⟩ := endpoint_inversion_budget_contract E hE n
        (resolutions E N n α β).1 (resolutions E N n α β).2 hn xs _ _ Cp Dm _ _
        heCp hEvalDm hvCp hContainsDm hDmLo hpLo hpHi hwCp hWidthDm
      obtain ⟨Rpp, heRpp, hvRpp, hwRpp⟩ := endpoint_inversion_budget_contract E hE n
        (resolutions E N n α β).1 (resolutions E N n α β).2 hn xs _ _ Cp Dp _ _
        heCp hEvalDp hvCp hContainsDp hDpLo hpLo hpHi hwCp hWidthDp
      simp only [endpointRadiusExpressions] at heLmm heLmp heRpm heRpp
      refine ⟨boxMin Lmm Lmp, boxMax Rpm Rpp, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change (do let A ← (inversionExpression _ _).eval E
                    (qEnd n (resolutions E N n α β).1 (resolutions E N n α β).2) xs
                   let B ← (inversionExpression _ _).eval E
                    (qEnd n (resolutions E N n α β).1 (resolutions E N n α β).2) xs
                   pure (boxMin A B)) = _
        rw [heLmm, heLmp]; rfl
      · change (do let A ← (inversionExpression _ _).eval E
                    (qEnd n (resolutions E N n α β).1 (resolutions E N n α β).2) xs
                   let B ← (inversionExpression _ _).eval E
                    (qEnd n (resolutions E N n α β).1 (resolutions E N n α β).2) xs
                   pure (boxMax A B)) = _
        rw [heRpm, heRpp]; rfl
      · simpa only [idealEndpoints] using (endpoint_min_max_contains _ _ _ _ hvLmm hvLmp).1
      · simpa only [idealEndpoints] using (endpoint_min_max_contains _ _ _ _ hvRpm hvRpp).2
      · have h : ((boxMin Lmm Lmp).width : ℝ) ≤ max (Lmm.width : ℝ) (Lmp.width : ℝ) := by
          exact_mod_cast (endpoint_min_max_width Lmm Lmp).1
        exact h.trans (max_le hwLmm hwLmp)
      · have h : ((boxMax Rpm Rpp).width : ℝ) ≤ max (Rpm.width : ℝ) (Rpp.width : ℝ) := by
          exact_mod_cast (endpoint_min_max_width Rpm Rpp).2
        exact h.trans (max_le hwRpm hwRpp)
    refine ⟨L, R, ?_, hContainsL, hContainsR, hWidthL, hWidthR⟩
    simp [endpointBoxes, hInputs, hEvalL, hEvalR]
  obtain ⟨hSubset, hLength⟩ :=
    upperOutput_enclosure_guarantees E N n hn α β o c s L R hRank hEnd hL hR _ hLW hRW
  refine ⟨c, s, L, R, hRank, hcW, hsW, ?_, ?_, hcTriple, ?_, ?_, hsTriple,
    hEnd, hL, hR, hLW, hRW, hSubset, ?_,
    upperOutput_rational_shape E N n α β o, (upperInterval E N hN n α β).borel⟩
  · simpa only [hk] using hcLower
  · simpa only [hk] using hcUpper
  · simpa only [hk] using hsLower
  · simpa only [hk] using hsUpper
  · simpa only [mul_one_div] using hLength
end CausalSmith.Stat.LogoddsLowsmoothFrontier

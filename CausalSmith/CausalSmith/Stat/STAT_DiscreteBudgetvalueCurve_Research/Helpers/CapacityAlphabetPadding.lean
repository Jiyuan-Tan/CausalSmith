module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.CapacityLowerTransport
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedAlphabetPadding

/-! Zero-mass padding of the paper's full-data causal laws. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Embed an observed record along an enlargement of its covariate alphabet. -/
-- @node: padCausalObs
noncomputable def padCausalObs {r d : ℕ} (h : r ≤ d) : Obs r → Obs d :=
  fun z => (Fin.castLE h z.1, z.2.1, z.2.2)

/-- Embed a full-data record along an enlargement of its covariate alphabet. -/
-- @node: padCausalFullObs
noncomputable def padCausalFullObs {r d : ℕ} (h : r ≤ d) : FullObs r → FullObs d :=
  fun z => (Fin.castLE h z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2)

/-- Extend a full-data causal law by zero mass on the new covariate cells. -/
-- @node: padPotentialLaw
noncomputable def padPotentialLaw {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) : PotentialLaw d :=
  let Qpad : CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.PotentialLaw d :=
    ⟨Q.pmf.map (padCausalFullObs h)⟩
  have hcons : CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.Consistency Qpad := by
    intro z hz
    change ((Q.pmf.map (padCausalFullObs h)) z).toReal = 0
    rw [PMF.map_apply]
    apply (ENNReal.toReal_eq_zero_iff _).2
    left
    rw [ENNReal.tsum_eq_zero]
    intro w
    split_ifs with hw
    · have hwbad : w.2.2.1 ≠
          (if w.2.1 then w.2.2.2.2 else w.2.2.2.1) := by
        intro heq
        apply hz
        have hgood : (padCausalFullObs h w).2.2.1 =
            (if (padCausalFullObs h w).2.1 then
              (padCausalFullObs h w).2.2.2.2 else
              (padCausalFullObs h w).2.2.2.1) := by
          simpa [padCausalFullObs] using heq
        exact hw ▸ hgood
      have hzero := Q.property.1 w hwbad
      change (Q.pmf w).toReal = 0 at hzero
      rcases (ENNReal.toReal_eq_zero_iff _).1 hzero with hz0 | htop
      · exact hz0
      · exact ((Q.pmf.apply_ne_top w) htop).elim
    · rfl
  let hcanonical := canonicalObservedOutcome_of_consistency Qpad hcons
  ⟨Classical.choose hcanonical, Qpad, Classical.choose_spec hcanonical, hcons⟩

private lemma padCausalFullObs_injective {r d : ℕ} (h : r ≤ d) :
    Function.Injective (padCausalFullObs h) := by
  intro x y hxy
  apply Prod.ext
  · exact Fin.castLE_injective h (congrArg Prod.fst hxy)
  · simpa [padCausalFullObs] using congrArg Prod.snd hxy

/-- Padded full atom masses agree with the original masses on embedded cells. With [the specified inputs and conditions](hyp:r,d,h,Q,x,a,y,y0,y1), [the stated relationship holds](goal). -/
-- @node: padPotentialLaw_fullMass_castLE
lemma padPotentialLaw_fullMass_castLE {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (x : Fin r) (a y y0 y1 : Bool) :
    fullMass (padPotentialLaw h Q) (Fin.castLE h x, a, y, y0, y1) =
      fullMass Q (x, a, y, y0, y1) := by
  unfold fullMass CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass
  simp only [padPotentialLaw, PMF.map_apply]
  rw [tsum_eq_single (x, a, y, y0, y1)]
  · simp [padCausalFullObs, PotentialLaw.pmf]
  · intro z hz
    simp only [ite_eq_right_iff]
    intro heq
    exact (hz ((padCausalFullObs_injective h) heq.symm)).elim

/-- Every atom in a newly added covariate cell has zero padded mass. With [the specified inputs and conditions](hyp:r,d,h,Q,x,hx,a,y,y0,y1), [the stated relationship holds](goal). -/
-- @node: padPotentialLaw_fullMass_new
lemma padPotentialLaw_fullMass_new {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (x : Fin d) (hx : r ≤ (x : ℕ))
    (a y y0 y1 : Bool) :
    fullMass (padPotentialLaw h Q) (x, a, y, y0, y1) = 0 := by
  unfold fullMass CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass
  simp only [padPotentialLaw, PMF.map_apply]
  apply (ENNReal.toReal_eq_zero_iff _).2
  left
  rw [ENNReal.tsum_eq_zero]
  intro z
  split_ifs with heq
  · have hv := congrArg (fun w : FullObs d => (w.1 : ℕ)) heq
    simp only [padCausalFullObs] at hv
    have : (z.1 : ℕ) = (x : ℕ) := by simpa using hv.symm
    omega
  · rfl

/-- Padded cell masses agree with the original masses on embedded cells. With [the specified inputs and conditions](hyp:r,d,h,Q,x), [the stated relationship holds](goal). -/
-- @node: padPotentialLaw_poCellMass_castLE
lemma padPotentialLaw_poCellMass_castLE {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (x : Fin r) :
    poCellMass (padPotentialLaw h Q) (Fin.castLE h x) = poCellMass Q x := by
  simp only [poCellMass, CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass,
    padPotentialLaw_fullMass_castLE]

/-- Padded regressions agree with the original regressions on embedded cells. With [the specified inputs and conditions](hyp:r,d,h,Q,a,x), [the stated relationship holds](goal). -/
-- @node: padPotentialLaw_poRegression_castLE
lemma padPotentialLaw_poRegression_castLE {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (a : Fin 2) (x : Fin r) :
    poRegression (padPotentialLaw h Q) a (Fin.castLE h x) = poRegression Q a x := by
  simp only [poRegression, CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poRegression,
    padPotentialLaw_poCellMass_castLE, padPotentialLaw_fullMass_castLE]

/-- Newly added cells have zero padded mass. With [the specified inputs and conditions](hyp:r,d,h,Q,x,hx), [the stated relationship holds](goal). -/
-- @node: padPotentialLaw_poCellMass_new
lemma padPotentialLaw_poCellMass_new {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (x : Fin d) (hx : r ≤ (x : ℕ)) :
    poCellMass (padPotentialLaw h Q) x = 0 := by
  simp only [poCellMass, CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass,
    padPotentialLaw_fullMass_new h Q x hx]
  simp

private lemma sum_castLE_ite {r d : ℕ} (h : r ≤ d) (f : Fin r → ℝ) :
    (∑ x : Fin d, if hx : (x : ℕ) < r then f ⟨x, hx⟩ else 0) = ∑ x : Fin r, f x := by
  classical
  calc
    _ = ∑ j ∈ Finset.range d, if hj : j < r then f ⟨j, hj⟩ else 0 := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj]
    _ = ∑ j ∈ Finset.range r, if hj : j < r then f ⟨j, hj⟩ else 0 := by
      exact (Finset.sum_subset (Finset.range_mono h)
        (by intro j hj hnot; simp [Finset.mem_range] at hnot; simp [hnot])).symm
    _ = _ := by rw [Finset.sum_fin_eq_sum_range]

/-- Newly added cells have totalized regression and effect zero. With [the specified inputs and conditions](hyp:r,d,h,Q,x,hx), [the stated relationship holds](goal). -/
-- @node: padPotentialLaw_effect_new
lemma padPotentialLaw_effect_new {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (x : Fin d) (hx : r ≤ (x : ℕ)) :
    effect (padPotentialLaw h Q) x = 0 := by
  have hm := padPotentialLaw_poCellMass_new h Q x hx
  unfold effect
  simp [poRegression, CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poRegression, hm]

/-- Padding preserves effects on embedded cells. With [the specified inputs and conditions](hyp:r,d,h,Q,x), [the stated relationship holds](goal). -/
-- @node: padPotentialLaw_effect_castLE
lemma padPotentialLaw_effect_castLE {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (x : Fin r) :
    effect (padPotentialLaw h Q) (Fin.castLE h x) = effect Q x := by
  simp only [effect, padPotentialLaw_poRegression_castLE]

/-- Padding preserves the never-treat value. With [the specified inputs and conditions](hyp:r,d,h,Q), [the stated relationship holds](goal). -/
-- @node: padPotentialLaw_controlValue
lemma padPotentialLaw_controlValue {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) :
    controlValue (padPotentialLaw h Q) = controlValue Q := by
  classical
  unfold controlValue
  calc
    (∑ x : Fin d, poCellMass (padPotentialLaw h Q) x *
        poRegression (padPotentialLaw h Q) 0 x) =
      ∑ x : Fin d, if hx : (x : ℕ) < r then
        poCellMass Q ⟨x, hx⟩ * poRegression Q 0 ⟨x, hx⟩ else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          split_ifs with hx
          · let xi : Fin r := ⟨x, hx⟩
            have he : Fin.castLE h xi = x := Fin.ext (by rfl)
            calc
              _ = poCellMass (padPotentialLaw h Q) (Fin.castLE h xi) *
                  poRegression (padPotentialLaw h Q) 0 (Fin.castLE h xi) := by rw [he]
              _ = poCellMass Q xi * poRegression Q 0 xi := by
                rw [padPotentialLaw_poCellMass_castLE,
                  padPotentialLaw_poRegression_castLE]
          · have hnew : r ≤ (x : ℕ) := Nat.le_of_not_gt hx
            rw [padPotentialLaw_poCellMass_new h Q x hnew]
            simp
    _ = _ := by
      simpa using sum_castLE_ite h
        (fun x => poCellMass Q x * poRegression Q 0 x)

private noncomputable def extendPolicy {r d : ℕ} (h : r ≤ d)
    (pi : Fin r → ℝ) : Fin d → ℝ :=
  fun x => if hx : (x : ℕ) < r then pi ⟨x, hx⟩ else 0

private lemma padded_weighted_sum {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (pi : Fin d → ℝ) :
    (∑ x : Fin d, poCellMass (padPotentialLaw h Q) x * pi x) =
      ∑ x : Fin r, poCellMass Q x * pi (Fin.castLE h x) := by
  classical
  calc
    _ = ∑ x : Fin d, if hx : (x : ℕ) < r then
        poCellMass Q ⟨x, hx⟩ * pi (Fin.castLE h ⟨x, hx⟩) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs with hx
      · let xi : Fin r := ⟨x, hx⟩
        have he : Fin.castLE h xi = x := Fin.ext (by rfl)
        calc
          _ = poCellMass (padPotentialLaw h Q) (Fin.castLE h xi) *
              pi (Fin.castLE h xi) := by rw [he]
          _ = _ := by rw [padPotentialLaw_poCellMass_castLE]
      · rw [padPotentialLaw_poCellMass_new h Q x (Nat.le_of_not_gt hx)]
        simp
    _ = _ := by
      exact sum_castLE_ite h (fun x => poCellMass Q x * pi (Fin.castLE h x))

private lemma padded_gain_sum {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (pi : Fin d → ℝ) :
    (∑ x : Fin d, poCellMass (padPotentialLaw h Q) x * pi x *
        effect (padPotentialLaw h Q) x) =
      ∑ x : Fin r, poCellMass Q x * pi (Fin.castLE h x) * effect Q x := by
  classical
  calc
    _ = ∑ x : Fin d, if hx : (x : ℕ) < r then
        poCellMass Q ⟨x, hx⟩ * pi (Fin.castLE h ⟨x, hx⟩) *
          effect Q ⟨x, hx⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs with hx
      · let xi : Fin r := ⟨x, hx⟩
        have he : Fin.castLE h xi = x := Fin.ext (by rfl)
        calc
          _ = poCellMass (padPotentialLaw h Q) (Fin.castLE h xi) *
              pi (Fin.castLE h xi) * effect (padPotentialLaw h Q) (Fin.castLE h xi) := by rw [he]
          _ = _ := by rw [padPotentialLaw_poCellMass_castLE,
            padPotentialLaw_effect_castLE]
      · rw [padPotentialLaw_poCellMass_new h Q x (Nat.le_of_not_gt hx)]
        simp
    _ = _ := by
      exact sum_castLE_ite h
        (fun x => poCellMass Q x * pi (Fin.castLE h x) * effect Q x)

/-- Zero-mass alphabet padding preserves the budget-constrained value. With [the specified inputs and conditions](hyp:r,d,h,Q,b), [the stated relationship holds](goal). -/
-- @node: padPotentialLaw_budgetValue
lemma padPotentialLaw_budgetValue {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (b : ℝ) :
    budgetValue (padPotentialLaw h Q) b = budgetValue Q b := by
  classical
  unfold budgetValue
  split_ifs with hb
  · rw [padPotentialLaw_controlValue h Q]
    congr 1
    apply congrArg sSup
    ext v
    constructor
    · rintro ⟨pi, hpi, rfl⟩
      let rho : Fin r → ℝ := fun x => pi (Fin.castLE h x)
      refine ⟨rho, ?_, ?_⟩
      · refine ⟨fun x => hpi.1 (Fin.castLE h x), ?_⟩
        simpa [rho, padded_weighted_sum h Q pi] using hpi.2
      · simpa [rho] using (padded_gain_sum h Q pi).symm
    · rintro ⟨rho, hrho, rfl⟩
      let pi := extendPolicy h rho
      refine ⟨pi, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro x
          dsimp [pi, extendPolicy]
          split_ifs with hx
          · exact hrho.1 ⟨x, hx⟩
          · norm_num
        · rw [padded_weighted_sum]
          simpa [pi, extendPolicy] using hrho.2
      · change (∑ x : Fin d, poCellMass (padPotentialLaw h Q) x * pi x *
            effect (padPotentialLaw h Q) x) =
          ∑ x : Fin r, poCellMass Q x * rho x * effect Q x
        rw [padded_gain_sum]
        simp [pi, extendPolicy]
  · rfl

private lemma padPotentialLaw_poPairAtom_castLE {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (x : Fin r) (y0 y1 : Bool) :
    poPairAtom (padPotentialLaw h Q) (Fin.castLE h x) y0 y1 =
      poPairAtom Q x y0 y1 := by
  simp [poPairAtom, padPotentialLaw_fullMass_castLE]

private lemma padPotentialLaw_poTreatmentAtom_castLE {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (x : Fin r) (a : Bool) :
    poTreatmentAtom (padPotentialLaw h Q) (Fin.castLE h x) a =
      poTreatmentAtom Q x a := by
  simp [poTreatmentAtom, padPotentialLaw_fullMass_castLE]

private lemma padPotentialLaw_poJointAtom_castLE {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (x : Fin r) (a y0 y1 : Bool) :
    poJointAtom (padPotentialLaw h Q) (Fin.castLE h x) a y0 y1 =
      poJointAtom Q x a y0 y1 := by
  simp [poJointAtom, padPotentialLaw_fullMass_castLE]

private lemma padPotentialLaw_poAtoms_new {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (x : Fin d) (hx : r ≤ (x : ℕ)) :
    (∀ y0 y1, poPairAtom (padPotentialLaw h Q) x y0 y1 = 0) ∧
    (∀ a, poTreatmentAtom (padPotentialLaw h Q) x a = 0) ∧
    (∀ a y0 y1, poJointAtom (padPotentialLaw h Q) x a y0 y1 = 0) := by
  constructor
  · intro y0 y1
    simp [poPairAtom, padPotentialLaw_fullMass_new h Q x hx]
  constructor
  · intro a
    simp [poTreatmentAtom, padPotentialLaw_fullMass_new h Q x hx]
  · intro a y0 y1
    simp [poJointAtom, padPotentialLaw_fullMass_new h Q x hx]

private lemma padPotentialLaw_jointMass_castLE {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (x : Fin r) (a y : Bool) :
    jointMass (observedMarginal (padPotentialLaw h Q)) (Fin.castLE h x) a y =
      jointMass (observedMarginal Q) x a y := by
  change CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.jointMass
      (CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal
        (padPotentialLaw h Q)) (Fin.castLE h x) a y =
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.jointMass
      (CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal Q) x a y
  rw [CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal_jointMass,
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal_jointMass]
  simp [padPotentialLaw_fullMass_castLE]

private lemma padPotentialLaw_jointMass_new {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (x : Fin d) (hx : r ≤ (x : ℕ)) (a y : Bool) :
    jointMass (observedMarginal (padPotentialLaw h Q)) x a y = 0 := by
  change CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.jointMass
      (CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal
        (padPotentialLaw h Q)) x a y = 0
  rw [CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal_jointMass]
  simp [padPotentialLaw_fullMass_new h Q x hx]

private lemma padPotentialLaw_cellMass_castLE {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (x : Fin r) :
    cellMass (observedMarginal (padPotentialLaw h Q)) (Fin.castLE h x) =
      cellMass (observedMarginal Q) x := by
  simp [cellMass, CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass,
    padPotentialLaw_jointMass_castLE]

private lemma padPotentialLaw_propensity_castLE {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (x : Fin r) :
    propensity (observedMarginal (padPotentialLaw h Q)) (Fin.castLE h x) =
      propensity (observedMarginal Q) x := by
  simp [propensity, CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.propensity,
    armMass, CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.armMass,
    padPotentialLaw_cellMass_castLE, padPotentialLaw_jointMass_castLE]

/-- Zero-mass padding preserves all restrictions defining the capacity hard
class and its binding half-budget certificate. With [the specified inputs and conditions](hyp:r,d,hr,h,epsilon,Q,hQ), [the stated relationship holds](goal). -/
-- @node: padPotentialLaw_capacityHardClass
lemma padPotentialLaw_capacityHardClass {r d : ℕ} (hr : 2 ≤ r) (h : r ≤ d)
    {epsilon : ℝ} {Q : PotentialLaw r} (hQ : Q ∈ capacityHardClass r epsilon) :
    padPotentialLaw h Q ∈ capacityHardClass d epsilon := by
  classical
  rcases hQ with ⟨hmodel, hvalue, heffects, hbinding⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨hr.trans h, hmodel.overlapParameter, ?_, ?_, ?_⟩
    · intro z hz
      by_cases hx : (z.1 : ℕ) < r
      · let x : Fin r := ⟨z.1, hx⟩
        have he : Fin.castLE h x = z.1 := Fin.ext (by rfl)
        let z0 : FullObs r :=
          (x, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2)
        have hez : padCausalFullObs h z0 = z := by
          apply Prod.ext
          · exact he
          · rfl
        have hs := hmodel.consistency
          z0 (by simpa [z0] using hz)
        rw [← hez]
        change fullMass (padPotentialLaw h Q)
            (Fin.castLE h x, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2) = 0
        exact (padPotentialLaw_fullMass_castLE h Q x
          z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2).trans (by simpa [z0] using hs)
      · exact padPotentialLaw_fullMass_new h Q z.1 (Nat.le_of_not_gt hx)
          z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2
    · intro x a y0 y1
      by_cases hx : (x : ℕ) < r
      · let xi : Fin r := ⟨x, hx⟩
        have he : Fin.castLE h xi = x := Fin.ext (by rfl)
        rw [← he, padPotentialLaw_poJointAtom_castLE,
          padPotentialLaw_poCellMass_castLE,
          padPotentialLaw_poTreatmentAtom_castLE,
          padPotentialLaw_poPairAtom_castLE]
        exact hmodel.exchangeability xi a y0 y1
      · obtain ⟨hp, ht, hj⟩ := padPotentialLaw_poAtoms_new h Q x (Nat.le_of_not_gt hx)
        simp [hp, ht, hj, padPotentialLaw_poCellMass_new h Q x (Nat.le_of_not_gt hx)]
    · intro x hxpos
      by_cases hx : (x : ℕ) < r
      · let xi : Fin r := ⟨x, hx⟩
        have he : Fin.castLE h xi = x := Fin.ext (by rfl)
        rw [← he, padPotentialLaw_propensity_castLE]
        apply hmodel.overlap xi
        rw [← he, padPotentialLaw_cellMass_castLE] at hxpos
        exact hxpos
      · have hz : cellMass (observedMarginal (padPotentialLaw h Q)) x = 0 := by
          simp [cellMass, CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass,
            padPotentialLaw_jointMass_new h Q x (Nat.le_of_not_gt hx)]
        linarith
  · simpa [padPotentialLaw_budgetValue] using hvalue
  · intro x hxpos
    by_cases hx : (x : ℕ) < r
    · let xi : Fin r := ⟨x, hx⟩
      have he : Fin.castLE h xi = x := Fin.ext (by rfl)
      rw [← he, padPotentialLaw_effect_castLE]
      apply heffects xi
      rw [← he, padPotentialLaw_poCellMass_castLE] at hxpos
      exact hxpos
    · rw [padPotentialLaw_poCellMass_new h Q x (Nat.le_of_not_gt hx)] at hxpos
      linarith
  · rcases hbinding with ⟨rho, hrho, hmass, hgain⟩
    let pi := extendPolicy h rho
    refine ⟨pi, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro x
        dsimp [pi, extendPolicy]
        split_ifs with hx
        · exact hrho.1 ⟨x, hx⟩
        · norm_num
      · rw [padded_weighted_sum]
        simpa [pi, extendPolicy] using hrho.2
    · rw [padded_weighted_sum]
      simpa [pi, extendPolicy] using hmass
    · rw [padPotentialLaw_budgetValue, padPotentialLaw_controlValue,
        padded_gain_sum]
      simpa [pi, extendPolicy] using hgain

/-- The observed PMF of a padded potential law is the pushforward of the
original observed PMF. With [the specified inputs and conditions](hyp:r,d,h,Q), [the stated relationship holds](goal). -/
-- @node: padPotentialLaw_observedMarginal_pmf
lemma padPotentialLaw_observedMarginal_pmf {r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) :
    (observedMarginal (padPotentialLaw h Q)).pmf =
      (observedMarginal Q).pmf.map (padCausalObs h) := by
  change PMF.map _ (PMF.map (padCausalFullObs h) Q.val.pmf) =
    PMF.map (padCausalObs h) (PMF.map _ Q.val.pmf)
  rw [PMF.map_comp, PMF.map_comp]
  congr 1

/-- Coordinatewise padding transports the iid observed sample law exactly. With [the specified inputs and conditions](hyp:n,r,d,h,Q), [the stated relationship holds](goal). -/
-- @node: padPotentialLaw_productLaw_map
lemma padPotentialLaw_productLaw_map {n r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) :
    Measure.map (fun z : Fin n → Obs r => fun i => padCausalObs h (z i))
      (productLaw (observedMarginal Q) n) =
        productLaw (observedMarginal (padPotentialLaw h Q)) n := by
  unfold productLaw CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.productLaw
  rw [Measure.pi_map_pi (fun _ =>
    (measurable_of_finite (padCausalObs h)).aemeasurable)]
  congr 1
  funext i
  unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.obsLaw
  rw [PMF.toMeasure_map (padCausalObs h) _ (measurable_of_finite _)]
  congr 1
  exact (padPotentialLaw_observedMarginal_pmf h Q).symm

/-- Pulling an estimator back along coordinatewise alphabet padding preserves
its squared risk, including the half-budget target. With [the specified inputs and conditions](hyp:n,r,d,h,Q,T,hT), [the stated relationship holds](goal). -/
-- @node: sqRisk_padPotentialLaw
lemma sqRisk_padPotentialLaw {n r d : ℕ} (h : r ≤ d)
    (Q : PotentialLaw r) (T : (Fin n → Obs d) → ℝ) (hT : Measurable T) :
    Causalean.Stat.sqRisk (productLaw (observedMarginal Q) n)
        (fun z => T (fun i => padCausalObs h (z i))) (budgetValue Q (1 / 2)) =
      Causalean.Stat.sqRisk
        (productLaw (observedMarginal (padPotentialLaw h Q)) n)
        T (budgetValue (padPotentialLaw h Q) (1 / 2)) := by
  unfold Causalean.Stat.sqRisk
  rw [padPotentialLaw_budgetValue]
  let μ := productLaw (observedMarginal Q) n
  have hi := MeasureTheory.integral_map
    (μ := μ) (φ := fun z : Fin n → Obs r => fun i => padCausalObs h (z i))
    (f := fun z : Fin n → Obs d => (T z - budgetValue Q (1 / 2)) ^ 2)
    (measurable_of_finite _).aemeasurable
    ((hT.sub measurable_const).pow_const 2).aestronglyMeasurable
  rw [padPotentialLaw_productLaw_map h Q] at hi
  exact hi.symm

/-- A paired lower bound on an even subalphabet transfers to any larger paper
alphabet by zero-mass padding. With [the specified inputs and conditions](hyp:n,k,d,hk,hkd,epsilon,he,he',L,hL,hlower,mu,hmu,T), [the stated relationship holds](goal). -/
-- @node: pairedL1_lower_transport_capacity_padded
lemma pairedL1_lower_transport_capacity_padded {n k d : ℕ} (hk : 1 ≤ k)
    (hkd : 2 * k ≤ d) (epsilon : ℝ) (he : 0 < epsilon)
    (he' : epsilon < 1 / 2) (L : ℝ) (hL : 0 < L)
    (hlower : L ≤ twoSampleL1MinimaxRisk n k)
    (mu : PotentialLaw d → Measure (Fin n → Obs d))
    (hmu : ∀ Q, IidSampling (observedMarginal Q) (mu Q))
    (T : {f : (Fin n → Obs d) → ℝ // Measurable f}) :
    ∃ Q : PotentialLaw d, Q ∈ capacityHardClass d epsilon ∧
      (1 / 32 : ℝ) ^ 2 * (L / 2) ≤
        Causalean.Stat.sqRisk (mu Q) T.1 (budgetValue Q (1 / 2)) := by
  let Tsmall : {f : (Fin n → Obs (2 * k)) → ℝ // Measurable f} :=
    ⟨fun z => T.1 (fun i => padCausalObs hkd (z i)), measurable_of_finite _⟩
  obtain ⟨Q, hQ, hrisk⟩ := pairedL1_lower_transport_capacity hk epsilon he he'
    L hL hlower Tsmall
  refine ⟨padPotentialLaw hkd Q,
    padPotentialLaw_capacityHardClass (by omega) hkd hQ, ?_⟩
  rw [hmu (padPotentialLaw hkd Q)]
  exact hrisk.trans_eq (sqRisk_padPotentialLaw hkd Q T.1 T.2)

end CausalSmith.Stat.DiscreteBudgetvalueCurve

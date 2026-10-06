module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.GoodPilotCellMoment
public import Causalean.Mathlib.Probability.Independence.Pair

/-! Block-local composition and unconditional good-pilot cell moments. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Causalean.Stat.Concentration.BoundedVariation
open Causalean.Stat.Concentration.Poisson
open Causalean.Mathlib.Probability.Independence

/-- Boolean reflection of the paper's cellwise good-pilot event. -/
-- @node: idealPilotGoodBool
noncomputable def idealPilotGoodBool {n d : ℕ} (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) (j : Fin d) : Bool := by
  classical
  exact decide (idealPilotGood (n := n) P counts j)

/-- The Boolean good-pilot event reflects the propositional definition. With [the specified inputs and conditions](hyp:n,d,P,counts,j), [the stated relationship holds](goal). -/
-- @node: idealPilotGoodBool_eq_true
lemma idealPilotGoodBool_eq_true {n d : ℕ} (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) (j : Fin d) :
    idealPilotGoodBool (n := n) P counts j = true ↔
      idealPilotGood (n := n) P counts j := by
  classical
  simp [idealPilotGoodBool]

/-- Embed four counts into one cell of a flattened count table. -/
-- @node: singleCellCountTable
def singleCellCountTable {d : ℕ} (j : Fin d) (u : Fin 4 → ℕ) :
    (Fin d × Fin 4) → ℕ := fun iz => if iz.1 = j then u iz.2 else 0

/-- Extracting the embedded cell recovers its four counts. The [cell extraction identity](goal) follows. -/
-- @node: poissonTableCell_singleCellCountTable
@[simp] lemma poissonTableCell_singleCellCountTable {d : ℕ} (j : Fin d)
    (u : Fin 4 → ℕ) : poissonTableCell j (singleCellCountTable j u) = u := by
  funext i
  simp [poissonTableCell, singleCellCountTable]

/-- At the selected cell, currying a table depends only on its extracted
four-count block. With [the specified inputs and conditions](hyp:d,j,p,q,h), [the stated relationship holds](goal). -/
-- @node: curryCountTable_eq_of_poissonTableCell_eq
lemma curryCountTable_eq_at_of_poissonTableCell_eq {d : ℕ} (j : Fin d)
    (p q : (Fin d × Fin 4) → ℕ) (h : poissonTableCell j p = poissonTableCell j q) :
    curryCountTable p j = curryCountTable q j := by
  funext z
  exact congrFun h (CellFourEquiv z)

/-- The paper's good-pilot predicate is local to the selected four-count
pilot block. With [the specified inputs and conditions](hyp:n,d,P,j,p), [the stated relationship holds](goal). -/
-- @node: idealPilotGood_singleCell_iff
lemma idealPilotGood_singleCell_iff {n d : ℕ} (P : DiscreteLaw d) (j : Fin d)
    (p : (Fin d × Fin 4) → ℕ) :
    idealPilotGood (n := n) P (curryCountTable p, fun _ _ => 0) j ↔
      idealPilotGood (n := n) P
        (curryCountTable (singleCellCountTable j (poissonTableCell j p)),
          fun _ _ => 0) j := by
  unfold idealPilotGood
  have hcell : curryCountTable p j =
      curryCountTable (singleCellCountTable j (poissonTableCell j p)) j := by
    apply curryCountTable_eq_at_of_poissonTableCell_eq
    simp
  change (∀ zeta : Cell,
      |pilotCenter ((n : ℝ) / 8) (curryCountTable p j) zeta - cellVector P j zeta| ≤
        pilotHalfWidth ((n : ℝ) / 8) d (curryCountTable p j) zeta / 4) ↔
    ∀ zeta : Cell,
      |pilotCenter ((n : ℝ) / 8)
          (curryCountTable (singleCellCountTable j (poissonTableCell j p)) j) zeta -
          cellVector P j zeta| ≤
        pilotHalfWidth ((n : ℝ) / 8) d
          (curryCountTable (singleCellCountTable j (poissonTableCell j p)) j) zeta / 4
  rw [hcell]

/-- Replacing both flattened tables by their selected-cell embeddings leaves
the selected ideal cell-error path unchanged. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,p,e,j), [the stated relationship holds](goal). -/
-- @node: idealPilotErrorCellPath_singleCell_local
lemma idealPilotErrorCellPath_singleCell_local
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (hn : 1 ≤ n)
    (hd : 1 ≤ d) (P : DiscreteLaw d)
    (p e : (Fin d × Fin 4) → ℕ) (j : Fin d) :
    idealPilotErrorCellPath epsilon P (curryCountTable p, curryCountTable e) j true
        (idealPilotErrorCell_continuous_time_of_pos he hn hd
          P (curryCountTable p, curryCountTable e) j true) =
      idealPilotErrorCellPath epsilon P
        (curryCountTable (singleCellCountTable j (poissonTableCell j p)),
          curryCountTable (singleCellCountTable j (poissonTableCell j e))) j true
        (idealPilotErrorCell_continuous_time_of_pos he hn hd
          P
          (curryCountTable (singleCellCountTable j (poissonTableCell j p)),
            curryCountTable (singleCellCountTable j (poissonTableCell j e))) j true) := by
  apply ContinuousMap.ext
  intro lambda
  change idealPilotErrorCell (n := n) epsilon lambda P
      (curryCountTable p, curryCountTable e) j true =
    idealPilotErrorCell (n := n) epsilon lambda P
      (curryCountTable (singleCellCountTable j (poissonTableCell j p)),
        curryCountTable (singleCellCountTable j (poissonTableCell j e))) j true
  have hp : curryCountTable p j =
      curryCountTable (singleCellCountTable j (poissonTableCell j p)) j := by
    apply curryCountTable_eq_at_of_poissonTableCell_eq
    simp
  have heval : curryCountTable e j =
      curryCountTable (singleCellCountTable j (poissonTableCell j e)) j := by
    apply curryCountTable_eq_at_of_poissonTableCell_eq
    simp
  unfold idealPilotErrorCell idealPilotGood
  simp only [hp, heval]

set_option maxHeartbeats 800000 in
/-- Under the two flattened Poisson table laws, the indicator-weighted full
good-pilot cell path has the unconditional equation (21) moment scale. With [the specified inputs and conditions](hyp:epsilon,he,he'), [the stated relationship holds](goal). -/
-- @node: flatGoodPilotCellPath_sq_integral_le
lemma flatGoodPilotCellPath_sq_integral_le
    (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n d : ℕ} (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d),
      ∀ j : Fin d,
      let rate : Fin d → Fin 4 → ℝ≥0 := idealFlatRate (n := n) P
      let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
      Integrable (fun pe =>
        (if idealPilotGoodBool (n := n) P
            (curryCountTable pe.1, fun _ _ => 0) j then
          pathSize (idealPilotErrorCellPath epsilon P
            (curryCountTable pe.1, curryCountTable pe.2) j true
            (idealPilotErrorCell_continuous_time_of_pos he hn
              (show 1 ≤ d by omega) P
              (curryCountTable pe.1, curryCountTable pe.2) j true)) ^ 2
        else 0)) (mu.prod mu) ∧
      (∫ pe,
        (if idealPilotGoodBool (n := n) P
            (curryCountTable pe.1, fun _ _ => 0) j then
          pathSize (idealPilotErrorCellPath epsilon P
            (curryCountTable pe.1, curryCountTable pe.2) j true
            (idealPilotErrorCell_continuous_time_of_pos he hn
              (show 1 ≤ d by omega) P
              (curryCountTable pe.1, curryCountTable pe.2) j true)) ^ 2
        else 0) ∂mu.prod mu) ≤
          C * (d : ℝ) ^ (1 / 16 : ℝ) * badPilotCellScale (n := n) P j ^ 2 := by
  classical
  obtain ⟨C₀, hC₀, hsectionUniform⟩ :=
    goodPilot_fullCellErrorPath_sq_integral_le
      epsilon he he'
  refine ⟨32 * pilotRadiusConstant ^ 2 * C₀, by
    unfold pilotRadiusConstant
    positivity, ?_⟩
  intro n d hn hd P j
  dsimp only
  let rate : Fin d → Fin 4 → ℝ≥0 := idealFlatRate (n := n) P
  let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  let good : (Fin 4 → ℕ) → Bool := fun u => decide
    (idealPilotGood (n := n) P
      (curryCountTable (singleCellCountTable j u), fun _ _ => 0) j)
  let phi : (Fin 4 → ℕ) → (Fin 4 → ℕ) → ℝ := fun u v =>
    pathSize (idealPilotErrorCellPath epsilon P
      (curryCountTable (singleCellCountTable j u),
        curryCountTable (singleCellCountTable j v)) j true
      (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega) P
        (curryCountTable (singleCellCountTable j u),
          curryCountTable (singleCellCountTable j v)) j true)) ^ 2
  let bound : ((Fin d × Fin 4) → ℕ) → ℝ := fun p =>
    C₀ * (d : ℝ) ^ (1 / 16 : ℝ) *
      (∑ zeta : Cell,
        pilotRadius ((n : ℝ) / 8) d (curryCountTable p j) zeta) ^ 2
  have hgoodMeas : Measurable good := measurable_of_countable _
  have hphiMeas : Measurable (Function.uncurry phi) := measurable_of_countable _
  have hphiNonneg (u v) : 0 ≤ phi u v := by dsimp [phi]; positivity
  have hsectionInt (p : (Fin d × Fin 4) → ℕ) : Integrable
      (fun e : (Fin d × Fin 4) → ℕ =>
        if good (poissonTableCell j p) then
          phi (poissonTableCell j p) (poissonTableCell j e) else 0) mu := by
    by_cases hg : good (poissonTableCell j p) = true
    · simp only [hg, if_true]
      have hprop : idealPilotGood (n := n) P
          (curryCountTable (singleCellCountTable j (poissonTableCell j p)),
            fun _ _ => 0) j := by
        simpa [good] using hg
      have hpkg := hsectionUniform hn hd P
        (singleCellCountTable j (poissonTableCell j p)) j hprop
      have hi := hpkg.1
      apply hi.congr
      filter_upwards [] with e
      dsimp [phi]
      rw [idealPilotErrorCellPath_singleCell_local epsilon he hn
        (show 1 ≤ d by omega) P
        (singleCellCountTable j (poissonTableCell j p)) e j]
      simp
    · have hg' : good (poissonTableCell j p) = false := Bool.eq_false_of_not_eq_true hg
      simp [hg']
  have hradius := pilotRadius_sum_sq_integral_le_cellScale hn hd P j
  have hboundInt : Integrable bound mu := by
    exact hradius.1.const_mul (C₀ * (d : ℝ) ^ (1 / 16 : ℝ))
  have hsectionBound (p : (Fin d × Fin 4) → ℕ) :
      (∫ e : (Fin d × Fin 4) → ℕ,
        (if good (poissonTableCell j p) then
          phi (poissonTableCell j p) (poissonTableCell j e) else 0) ∂mu) ≤
        bound p := by
    by_cases hg : good (poissonTableCell j p) = true
    · simp only [hg, if_true]
      have hprop : idealPilotGood (n := n) P
          (curryCountTable (singleCellCountTable j (poissonTableCell j p)),
            fun _ _ => 0) j := by
        simpa [good] using hg
      have hpkg := hsectionUniform hn hd P
        (singleCellCountTable j (poissonTableCell j p)) j hprop
      have heq : (∫ e, phi (poissonTableCell j p) (poissonTableCell j e) ∂mu) =
          ∫ e, pathSize (idealPilotErrorCellPath epsilon P
            (curryCountTable (singleCellCountTable j (poissonTableCell j p)),
              curryCountTable e) j true
            (idealPilotErrorCell_continuous_time_of_pos he hn
              (show 1 ≤ d by omega) P
              (curryCountTable (singleCellCountTable j (poissonTableCell j p)),
                curryCountTable e) j true)) ^ 2 ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with e
        dsimp [phi]
        rw [idealPilotErrorCellPath_singleCell_local epsilon he hn
          (show 1 ≤ d by omega) P
          (singleCellCountTable j (poissonTableCell j p)) e j]
        simp
      rw [heq]
      have hcell : curryCountTable
          (singleCellCountTable j (poissonTableCell j p)) j =
          curryCountTable p j := by
        symm
        apply curryCountTable_eq_at_of_poissonTableCell_eq
        simp
      simpa [bound, mu, rate, hcell] using hpkg.2
    · have hg' : good (poissonTableCell j p) = false := Bool.eq_false_of_not_eq_true hg
      simp only [hg', Bool.false_eq_true, if_false, integral_zero]
      dsimp [bound]
      exact mul_nonneg
        (mul_nonneg hC₀.le (Real.rpow_nonneg (by positivity) _)) (sq_nonneg _)
  have hflat := poissonTable_cell_nonneg_integral_le_of_sections
    rate rate j good hgoodMeas phi hphiMeas hphiNonneg hsectionInt bound hboundInt
      hsectionBound
  have hidentify (pe : ((Fin d × Fin 4) → ℕ) × ((Fin d × Fin 4) → ℕ)) :
      (if idealPilotGoodBool (n := n) P
          (curryCountTable pe.1, fun _ _ => 0) j then
          pathSize (idealPilotErrorCellPath epsilon P
            (curryCountTable pe.1, curryCountTable pe.2) j true
            (idealPilotErrorCell_continuous_time_of_pos he hn
              (show 1 ≤ d by omega) P
              (curryCountTable pe.1, curryCountTable pe.2) j true)) ^ 2 else 0) =
        (if good (poissonTableCell j pe.1) then
          phi (poissonTableCell j pe.1) (poissonTableCell j pe.2) else 0) := by
    have hiff := idealPilotGood_singleCell_iff (n := n) P j pe.1
    by_cases hg : idealPilotGood (n := n) P
        (curryCountTable pe.1, fun _ _ => 0) j
    · have hgb : good (poissonTableCell j pe.1) = true := by
        simp [good, hiff.mp hg]
      have hgoodBool : idealPilotGoodBool (n := n) P
          (curryCountTable pe.1, fun _ _ => 0) j = true :=
        (idealPilotGoodBool_eq_true P _ j).2 hg
      simp only [hgoodBool, hgb, if_true]
      dsimp [phi]
      rw [← idealPilotErrorCellPath_singleCell_local epsilon he hn
        (show 1 ≤ d by omega) P pe.1 pe.2 j]
    · have hgb : good (poissonTableCell j pe.1) = false := by
        have hcanon : ¬ idealPilotGood (n := n) P
            (curryCountTable (singleCellCountTable j (poissonTableCell j pe.1)),
              fun _ _ => 0) j := fun hc => hg (hiff.mpr hc)
        simp [good, hcanon]
      have hgoodBool : idealPilotGoodBool (n := n) P
          (curryCountTable pe.1, fun _ _ => 0) j = false := by
        apply Bool.eq_false_of_not_eq_true
        exact fun ht => hg ((idealPilotGoodBool_eq_true P _ j).1 ht)
      simp [hgoodBool, hgb]
  let f : (((Fin d × Fin 4) → ℕ) × ((Fin d × Fin 4) → ℕ)) → ℝ := fun pe =>
    if good (poissonTableCell j pe.1) then
      phi (poissonTableCell j pe.1) (poissonTableCell j pe.2) else 0
  have hfMeas : Measurable f :=
    poissonTable_cell_indicator_measurable j good hgoodMeas phi hphiMeas
  have hfNonneg (pe) : 0 ≤ f pe := by
    dsimp [f]
    split_ifs <;> simp [hphiNonneg]
  have hnorm : (fun p => ∫ e, ‖f (p, e)‖ ∂mu) =
      (fun p => ∫ e, f (p, e) ∂mu) := by
    funext p
    congr 1
    funext e
    rw [Real.norm_eq_abs, abs_of_nonneg (hfNonneg (p, e))]
  have houter : Integrable (fun p => ∫ e, ‖f (p, e)‖ ∂mu) mu := by
    letI : IsProbabilityMeasure mu := by dsimp [mu, poissonTableLaw]; infer_instance
    rw [hnorm]
    apply integrable_of_le_of_le (g₁ := fun _ => (0 : ℝ)) (g₂ := bound)
    · exact hfMeas.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun p => integral_nonneg fun e => hfNonneg (p, e)
    · exact Filter.Eventually.of_forall hsectionBound
    · exact integrable_const 0
    · exact hboundInt
  have hfInt : Integrable f (mu.prod mu) :=
    (integrable_prod_iff hfMeas.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall hsectionInt, houter⟩
  have horigInt : Integrable (fun pe =>
      (if idealPilotGoodBool (n := n) P
          (curryCountTable pe.1, fun _ _ => 0) j then
        pathSize (idealPilotErrorCellPath epsilon P
          (curryCountTable pe.1, curryCountTable pe.2) j true
          (idealPilotErrorCell_continuous_time_of_pos he hn
            (show 1 ≤ d by omega) P
            (curryCountTable pe.1, curryCountTable pe.2) j true)) ^ 2 else 0))
      (mu.prod mu) := by
    apply hfInt.congr
    exact Filter.Eventually.of_forall fun pe => (hidentify pe).symm
  refine ⟨horigInt, ?_⟩
  calc
    _ = ∫ pe, (if good (poissonTableCell j pe.1) then
          phi (poissonTableCell j pe.1) (poissonTableCell j pe.2) else 0) ∂mu.prod mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hidentify
    _ ≤ ∫ p, bound p ∂mu := hflat
    _ ≤ (32 * pilotRadiusConstant ^ 2 * C₀) *
        (d : ℝ) ^ (1 / 16 : ℝ) * badPilotCellScale (n := n) P j ^ 2 := by
      rw [show (∫ p, bound p ∂mu) =
          (C₀ * (d : ℝ) ^ (1 / 16 : ℝ)) *
            ∫ p, (∑ zeta : Cell,
              pilotRadius ((n : ℝ) / 8) d (curryCountTable p j) zeta) ^ 2 ∂mu by
        rw [integral_const_mul]
        ]
      have hcoef : 0 ≤ C₀ * (d : ℝ) ^ (1 / 16 : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left hradius.2 hcoef
      nlinarith [sq_nonneg (badPilotCellScale (n := n) P j)]

/-- Pushing the flattened product experiment through the count-table
equivalence gives the unconditional full good-pilot cell moment under the
paper's `idealCountLaw`. With [the specified inputs and conditions](hyp:epsilon,he,he'), [the stated relationship holds](goal). -/
-- @node: idealGoodPilotCellPath_sq_integral_le
lemma idealGoodPilotCellPath_sq_integral_le
    (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n d : ℕ} (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d),
      ∀ j : Fin d,
      Integrable (fun counts =>
        pathSize (idealPilotErrorCellPath epsilon P counts j true
          (idealPilotErrorCell_continuous_time_of_pos he hn
            (show 1 ≤ d by omega) P counts j true)) ^ 2)
        (idealCountLaw (n := n) P) ∧
      (∫ counts,
        (if idealPilotGoodBool (n := n) P counts j then
          pathSize (idealPilotErrorCellPath epsilon P counts j true
            (idealPilotErrorCell_continuous_time_of_pos he hn
              (show 1 ≤ d by omega) P counts j true)) ^ 2
        else 0) ∂idealCountLaw (n := n) P) ≤
          C * (d : ℝ) ^ (1 / 16 : ℝ) * badPilotCellScale (n := n) P j ^ 2 := by
  classical
  obtain ⟨C, hC, hflat⟩ :=
    flatGoodPilotCellPath_sq_integral_le epsilon he he'
  refine ⟨C, hC, ?_⟩
  intro n d hn hd P j
  have hflatj := hflat hn hd P j
  let rate : Fin d → Fin 4 → ℝ≥0 := idealFlatRate (n := n) P
  let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  let F : (((Fin d × Fin 4) → ℕ) × ((Fin d × Fin 4) → ℕ)) →
      (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ) := fun pe =>
    (curryCountTable pe.1, curryCountTable pe.2)
  let g : ((Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) → ℝ :=
    fun counts => if idealPilotGoodBool (n := n) P counts j then
      pathSize (idealPilotErrorCellPath epsilon P counts j true
        (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega)
          P counts j true)) ^ 2 else 0
  have hF : Measurable F := by fun_prop
  have hg : Measurable g := measurable_of_countable _
  have hmap : Measure.map F (mu.prod mu) = idealCountLaw (n := n) P := by
    simpa [F, mu, rate] using map_flatIdealCountLaw (n := n) P
  have hintegral : (∫ counts, g counts ∂idealCountLaw (n := n) P) =
      ∫ pe, g (F pe) ∂mu.prod mu := by
    rw [← hmap, integral_map hF.aemeasurable hg.aestronglyMeasurable]
  rw [show (∫ counts,
      (if idealPilotGoodBool (n := n) P counts j then
        pathSize (idealPilotErrorCellPath epsilon P counts j true
          (idealPilotErrorCell_continuous_time_of_pos he hn
            (show 1 ≤ d by omega) P counts j true)) ^ 2 else 0)
      ∂idealCountLaw (n := n) P) =
      ∫ counts, g counts ∂idealCountLaw (n := n) P by rfl]
  rw [hintegral]
  have hpoint (pe : (((Fin d × Fin 4) → ℕ) × ((Fin d × Fin 4) → ℕ))) :
      g (F pe) =
        (if idealPilotGoodBool (n := n) P
            (curryCountTable pe.1, fun _ _ => 0) j then
          pathSize (idealPilotErrorCellPath epsilon P
            (curryCountTable pe.1, curryCountTable pe.2) j true
            (idealPilotErrorCell_continuous_time_of_pos he hn
              (show 1 ≤ d by omega) P
              (curryCountTable pe.1, curryCountTable pe.2) j true)) ^ 2 else 0) := by
    dsimp [g, F]
    have hgood : idealPilotGood (n := n) P
        (curryCountTable pe.1, curryCountTable pe.2) j ↔
      idealPilotGood (n := n) P (curryCountTable pe.1, fun _ _ => 0) j := by
      rfl
    by_cases hp : idealPilotGood (n := n) P
        (curryCountTable pe.1, curryCountTable pe.2) j
    · have hp0 := hgood.mp hp
      have hb : idealPilotGoodBool (n := n) P
          (curryCountTable pe.1, curryCountTable pe.2) j = true :=
        (idealPilotGoodBool_eq_true P _ j).2 hp
      have hb0 : idealPilotGoodBool (n := n) P
          (curryCountTable pe.1, fun _ _ => 0) j = true :=
        (idealPilotGoodBool_eq_true P _ j).2 hp0
      simp [hb, hb0]
    · have hp0 : ¬ idealPilotGood (n := n) P
          (curryCountTable pe.1, fun _ _ => 0) j := fun h => hp (hgood.mpr h)
      have hb : idealPilotGoodBool (n := n) P
          (curryCountTable pe.1, curryCountTable pe.2) j = false := by
        apply Bool.eq_false_of_not_eq_true
        exact fun ht => hp ((idealPilotGoodBool_eq_true P _ j).1 ht)
      have hb0 : idealPilotGoodBool (n := n) P
          (curryCountTable pe.1, fun _ _ => 0) j = false := by
        apply Bool.eq_false_of_not_eq_true
        exact fun ht => hp0 ((idealPilotGoodBool_eq_true P _ j).1 ht)
      simp [hb, hb0]
  have hcompInt : Integrable (g ∘ F) (mu.prod mu) := by
    apply hflatj.1.congr
    exact Filter.Eventually.of_forall fun pe => (hpoint pe).symm
  have hgMapInt : Integrable g (Measure.map F (mu.prod mu)) :=
    (integrable_map_measure hg.aestronglyMeasurable hF.aemeasurable).2 hcompInt
  have hgIdealInt : Integrable g (idealCountLaw (n := n) P) := by
    rw [← hmap]
    exact hgMapInt
  have hpathInt : Integrable (fun counts =>
      pathSize (idealPilotErrorCellPath epsilon P counts j true
        (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega)
          P counts j true)) ^ 2) (idealCountLaw (n := n) P) := by
    apply hgIdealInt.congr
    exact Filter.Eventually.of_forall fun counts => by
      dsimp [g]
      by_cases hgood : idealPilotGood (n := n) P counts j
      · have hb := (idealPilotGoodBool_eq_true P counts j).2 hgood
        simp [hb]
      · have hb : idealPilotGoodBool (n := n) P counts j = false := by
          apply Bool.eq_false_of_not_eq_true
          exact fun ht => hgood ((idealPilotGoodBool_eq_true P counts j).1 ht)
        have hz : idealPilotErrorCellPath epsilon P counts j true
            (idealPilotErrorCell_continuous_time_of_pos he hn
              (show 1 ≤ d by omega) P counts j true) = 0 := by
          apply ContinuousMap.ext
          intro lambda
          simp [idealPilotErrorCellPath, idealPilotErrorCell, hgood]
        rw [hz]
        simp [hb, pathSize, pathTV, eVariationOn]
  refine ⟨hpathInt, ?_⟩
  calc
    (∫ pe, g (F pe) ∂mu.prod mu) =
        ∫ pe, (if idealPilotGoodBool (n := n) P
            (curryCountTable pe.1, fun _ _ => 0) j then
          pathSize (idealPilotErrorCellPath epsilon P
            (curryCountTable pe.1, curryCountTable pe.2) j true
            (idealPilotErrorCell_continuous_time_of_pos he hn
              (show 1 ≤ d by omega) P
              (curryCountTable pe.1, curryCountTable pe.2) j true)) ^ 2 else 0)
          ∂mu.prod mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ ≤ C * (d : ℝ) ^ (1 / 16 : ℝ) * badPilotCellScale (n := n) P j ^ 2 :=
      by simpa [mu, rate] using hflatj.2

/-- Outside the good-pilot event, the `good = true` cell path is the zero
path; hence its squared path size equals its indicator-weighted version. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,counts,j), [the stated relationship holds](goal). -/
-- @node: idealGoodPilotCellPath_sq_eq_indicator
lemma idealGoodPilotCellPath_sq_eq_indicator
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) (j : Fin d) :
    pathSize (idealPilotErrorCellPath epsilon P counts j true
      (idealPilotErrorCell_continuous_time_of_pos he hn hd P counts j true)) ^ 2 =
      if idealPilotGoodBool (n := n) P counts j then
        pathSize (idealPilotErrorCellPath epsilon P counts j true
          (idealPilotErrorCell_continuous_time_of_pos he hn hd P counts j true)) ^ 2
      else 0 := by
  classical
  by_cases hg : idealPilotGood (n := n) P counts j
  · have hb := (idealPilotGoodBool_eq_true P counts j).2 hg
    simp [hb]
  · have hb : idealPilotGoodBool (n := n) P counts j = false := by
      apply Bool.eq_false_of_not_eq_true
      exact fun ht => hg ((idealPilotGoodBool_eq_true P counts j).1 ht)
    have hz : idealPilotErrorCellPath epsilon P counts j true
        (idealPilotErrorCell_continuous_time_of_pos he hn hd P counts j true) = 0 := by
      apply ContinuousMap.ext
      intro lambda
      simp [idealPilotErrorCellPath, idealPilotErrorCell, hg]
    rw [hz]
    simp [hb, pathSize, pathTV, eVariationOn]

/-- A sum of two finite-variation continuous paths again has finite extended
variation. With [the specified inputs and conditions](hyp:f,g,hf,hg), [the stated relationship holds](goal). -/
-- @node: eVariationOn_path_add_lt_top
lemma eVariationOn_path_add_lt_top (f g : Path)
    (hf : eVariationOn f Set.univ < ⊤) (hg : eVariationOn g Set.univ < ⊤) :
    eVariationOn (f + g) Set.univ < ⊤ := by
  have hnegEq : eVariationOn (-g) Set.univ = eVariationOn g Set.univ := by
    unfold eVariationOn
    congr 1 with p
    congr 1 with i
    exact edist_neg_neg (G := ℝ) _ _
  have hnegEq' : eVariationOn (-g) Set.univ = eVariationOn g Set.univ := by
    change eVariationOn (fun t => -g t) Set.univ = _
    exact hnegEq
  have hneg : eVariationOn (-g) Set.univ < ⊤ := by rw [hnegEq']; exact hg
  have hle := eVariationOn_path_sub_le f (-g)
  rw [sub_neg_eq_add] at hle
  exact hle.trans_lt (ENNReal.add_lt_top.mpr ⟨hf, hneg⟩)

/-- Every realization of the good-pilot cell path has finite variation: it
is zero off the good event and factorial path plus correction on that event. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,counts,j), [the stated relationship holds](goal). -/
-- @node: idealGoodPilotCellPath_bv
lemma idealGoodPilotCellPath_bv
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 16 ≤ d)
    (P : DiscreteLaw d)
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) (j : Fin d) :
    eVariationOn (idealPilotErrorCellPath epsilon P counts j true
      (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega)
        P counts j true)) Set.univ < ⊤ := by
  classical
  by_cases hgood : idealPilotGood (n := n) P counts j
  · let p := flattenCountTable counts.1
    let e := flattenCountTable counts.2
    have hp : curryCountTable p = counts.1 := by
      exact (countTableEquiv d).right_inv counts.1
    have heval : curryCountTable e = counts.2 := by
      exact (countTableEquiv d).right_inv counts.2
    have hgoodFlat : idealPilotGood (n := n) P
        (curryCountTable p, fun _ _ => 0) j := by
      simpa [hp, idealPilotGood] using hgood
    have hpkg := goodPilot_localJacksonFourPoissonFactorialPath_sq_bound
      epsilon he hn hd P p j hgoodFlat
    let pilot := curryCountTable p j
    let W : Fin 4 → ((Fin d × Fin 4) → ℕ) → ℕ :=
      fun i table => poissonTableCell j table i
    let hpull := fun lambda => pilotRectangle_threshold_pullback_continuousOn
      (epsilon := epsilon) (m := (n : ℝ) / 8) he (by positivity)
      (show 1 ≤ d by omega) pilot lambda
    let fact := localJacksonFourPoissonFactorialPath epsilon (jacksonDegree d)
      (pilotMidpoint ((n : ℝ) / 8) d pilot)
      (pilotRadius ((n : ℝ) / 8) d pilot)
      (by unfold jacksonDegree; omega) hpull (le_refl _) W ((n : ℝ) / 8)
      ((d : ℝ) ^ (1 / 4 : ℝ) *
        ∑ zeta, pilotRadius ((n : ℝ) / 8) d pilot zeta) e
    let corr := idealGoodThresholdCorrectionPath (n := n) epsilon P pilot j
    have hfact : eVariationOn fact Set.univ < ⊤ := by
      simpa [fact, pilot, W, hpull] using hpkg.2.1 e
    have hcorr : eVariationOn corr Set.univ < ⊤ :=
      idealGoodThresholdCorrectionPath_bv epsilon P pilot j
    have heq := idealGoodCellErrorPath_eq_factorial_add_correction
      epsilon he hn hd P p e j (by simpa [hp, heval] using hgood)
    have hpathEq : idealPilotErrorCellPath epsilon P counts j true
        (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega)
          P counts j true) = fact + corr := by
      simpa [p, e, hp, heval, fact, corr, pilot, W, hpull] using heq
    rw [hpathEq]
    exact eVariationOn_path_add_lt_top fact corr hfact hcorr
  · have hz : idealPilotErrorCellPath epsilon P counts j true
        (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega)
          P counts j true) = 0 := by
      apply ContinuousMap.ext
      intro lambda
      simp [idealPilotErrorCellPath, idealPilotErrorCell, hgood]
    rw [hz]
    simp [eVariationOn]

/-- The pointwise finite-variation result supplies the almost-everywhere BV
hypothesis used by the centered maximal theorem. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,j), [the stated relationship holds](goal). -/
-- @node: idealGoodPilotCellPath_ae_bv
lemma idealGoodPilotCellPath_ae_bv
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 16 ≤ d)
    (P : DiscreteLaw d) (j : Fin d) :
    ∀ᵐ counts ∂idealCountLaw (n := n) P,
      eVariationOn (idealPilotErrorCellPath epsilon P counts j true
        (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega)
          P counts j true)) Set.univ < ⊤ :=
  Filter.Eventually.of_forall fun counts =>
    idealGoodPilotCellPath_bv epsilon he hn hd P counts j

/-- For a fixed cell, the ideal good-pilot error is a measurable random
continuous path under the count-table sigma algebra. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P,j), [the stated relationship holds](goal). -/
-- @node: idealGoodPilotCellPath_measurable
lemma idealGoodPilotCellPath_measurable
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d) (j : Fin d) :
    Measurable (fun counts => idealPilotErrorCellPath epsilon P counts j true
      (idealPilotErrorCell_continuous_time_of_pos he hn hd P counts j true)) := by
  exact measurable_of_countable _

/-- The unconditional equation (21) theorem exports square-path-size
integrability in the exact form required by the maximal inequality. With [the specified inputs and conditions](hyp:n,d,epsilon,he,he',hn,hd,P,j), [the stated relationship holds](goal). -/
-- @node: idealGoodPilotCellPath_sq_integrable
lemma idealGoodPilotCellPath_sq_integrable
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d)
    (j : Fin d) :
    Integrable (fun counts =>
      pathSize (idealPilotErrorCellPath epsilon P counts j true
        (idealPilotErrorCell_continuous_time_of_pos he hn
          (show 1 ≤ d by omega) P counts j true)) ^ 2)
      (idealCountLaw (n := n) P) := by
  obtain ⟨C, hC, hall⟩ :=
    idealGoodPilotCellPath_sq_integral_le epsilon he he'
  exact (hall hn hd P j).1

/-- Square-path-size integrability implies Bochner integrability of the
good-pilot random path. With [the specified inputs and conditions](hyp:n,d,epsilon,he,he',hn,hd,P), [the stated relationship holds](goal). The argument assumes [the probability-law premise](hyp:hprob). -/
-- @node: idealGoodPilotCellPath_integrable
lemma idealGoodPilotCellPath_integrable
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d)
    (hprob : IsProbabilityMeasure (idealCountLaw (n := n) P))
    (j : Fin d) :
    Integrable (fun counts => idealPilotErrorCellPath epsilon P counts j true
      (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega)
        P counts j true)) (idealCountLaw (n := n) P) := by
  letI : IsProbabilityMeasure (idealCountLaw (n := n) P) := hprob
  letI : BorelSpace Path := ⟨rfl⟩
  let F := fun counts => idealPilotErrorCellPath epsilon P counts j true
    (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega)
      P counts j true)
  have hsq : Integrable (fun counts => pathSize (F counts) ^ 2)
      (idealCountLaw (n := n) P) := by
    simpa [F] using idealGoodPilotCellPath_sq_integrable
      epsilon he he' hn hd P j
  have henv : Integrable (fun counts => 1 + pathSize (F counts) ^ 2)
      (idealCountLaw (n := n) P) := (integrable_const 1).add hsq
  apply henv.mono'
    (idealGoodPilotCellPath_measurable epsilon he hn (show 1 ≤ d by omega) P j).aestronglyMeasurable
  filter_upwards [] with counts
  change ‖F counts‖ ≤ 1 + pathSize (F counts) ^ 2
  have hnorm : ‖F counts‖ ≤ pathSize (F counts) := by
    unfold pathSize
    exact le_add_of_nonneg_right (pathTV_nonneg _)
  have hsize := pathSize_nonneg (F counts)
  nlinarith [sq_nonneg (pathSize (F counts) - 1 / 2)]

/-- Cellwise good-pilot error paths are mutually independent under the ideal
count law because each is a measurable function of its paired pilot/evaluation
four-count block. With [the specified inputs and conditions](hyp:n,d,epsilon,he,hn,hd,P), [the stated relationship holds](goal). -/
-- @node: idealGoodPilotCellPaths_independent
lemma idealGoodPilotCellPaths_independent
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (hn : 1 ≤ n) (hd : 16 ≤ d)
    (P : DiscreteLaw d) :
    iIndepFun (fun j counts => idealPilotErrorCellPath epsilon P counts j true
      (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega)
        P counts j true)) (idealCountLaw (n := n) P) := by
  classical
  let rate : Fin d → Fin 4 → ℝ≥0 := idealFlatRate (n := n) P
  let mu := poissonTableLaw (fun iz : Fin d × Fin 4 => rate iz.1 iz.2)
  let X : Fin d → ((Fin d × Fin 4) → ℕ) → (Fin 4 → ℕ) :=
    fun j p => poissonTableCell j p
  let F : (((Fin d × Fin 4) → ℕ) × ((Fin d × Fin 4) → ℕ)) →
      (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ) := fun pe =>
    (curryCountTable pe.1, curryCountTable pe.2)
  let G : Fin d →
      ((Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) → Path :=
    fun j counts => idealPilotErrorCellPath epsilon P counts j true
      (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega)
        P counts j true)
  let phi : Fin d → ((Fin 4 → ℕ) × (Fin 4 → ℕ)) → Path :=
    fun j uv => idealPilotErrorCellPath epsilon P
      (curryCountTable (singleCellCountTable j uv.1),
        curryCountTable (singleCellCountTable j uv.2)) j true
      (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega) P
        (curryCountTable (singleCellCountTable j uv.1),
          curryCountTable (singleCellCountTable j uv.2)) j true)
  letI : IsProbabilityMeasure mu := by dsimp [mu, poissonTableLaw]; infer_instance
  letI : BorelSpace Path := ⟨rfl⟩
  have hXmeas : ∀ j, Measurable (X j) := by intro j; fun_prop
  have hXind : iIndepFun X mu := by
    change iIndepFun (fun j p z => p (j, z)) mu
    simpa [mu, rate] using poissonTable_cell_blocks_independent rate
  have hpair : iIndepFun (fun j pe => (X j pe.1, X j pe.2)) (mu.prod mu) :=
    iIndepFun_pair_prod hXmeas hXmeas hXind hXind
  have hphi : ∀ j, Measurable (phi j) := by
    intro j
    exact measurable_of_countable _
  have hcanon := hpair.comp phi hphi
  have hflat : iIndepFun (fun j pe => G j (F pe)) (mu.prod mu) := by
    apply hcanon.congr
    intro j
    exact Filter.Eventually.of_forall fun pe => by
      dsimp [G, F, phi, X]
      exact (idealPilotErrorCellPath_singleCell_local epsilon he hn
        (show 1 ≤ d by omega) P pe.1 pe.2 j).symm
  have hmap : Measure.map F (mu.prod mu) = idealCountLaw (n := n) P := by
    simpa [F, mu, rate] using map_flatIdealCountLaw (n := n) P
  have hGmeas : ∀ j, Measurable (G j) := by
    intro j
    exact measurable_of_countable _
  letI : IsProbabilityMeasure (Measure.map F (mu.prod mu)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [← hmap]
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map hGmeas).2
  have hflatMap := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun j => (hGmeas j).comp (by fun_prop : Measurable F))).1 hflat
  calc
    Measure.map (fun counts j => G j counts) (Measure.map F (mu.prod mu)) =
        Measure.map (fun pe j => G j (F pe)) (mu.prod mu) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = Measure.infinitePi (fun j => Measure.map (fun pe => G j (F pe))
          (mu.prod mu)) := hflatMap
    _ = Measure.infinitePi (fun j => Measure.map (G j)
          (Measure.map F (mu.prod mu))) := by
      congr 1
      funext j
      exact (Measure.map_map (hGmeas j) (by fun_prop : Measurable F)).symm

/-- The abstract centered maximal inequality applies to the complete family of
good-pilot cell paths under the ideal count experiment. With [the specified inputs and conditions](hyp:n,d,epsilon,he,he',hn,hd,P), [the stated relationship holds](goal). The argument assumes [the probability-law premise](hyp:hprob). -/
-- @node: idealGoodPilotError_centered_maximal
lemma idealGoodPilotError_centered_maximal
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d)
    (hprob : IsProbabilityMeasure (idealCountLaw (n := n) P)) :
    let hcont : ∀ j counts, Continuous (fun lambda : Time =>
      idealPilotErrorCell (n := n) epsilon lambda P counts j true) :=
      fun j counts => idealPilotErrorCell_continuous_time_of_pos he hn
        (show 1 ≤ d by omega) P counts j true
    (∫ counts, ‖∑ j, (idealPilotErrorCellPath epsilon P counts j true
          (hcont j counts) -
        ∫ x, idealPilotErrorCellPath epsilon P x j true (hcont j x)
          ∂idealCountLaw (n := n) P)‖ ^ 2
      ∂idealCountLaw (n := n) P) ≤
      16384 * ∑ j, (∫ counts,
        (pathSize (idealPilotErrorCellPath epsilon P counts j true
          (hcont j counts))) ^ 2 ∂idealCountLaw (n := n) P) := by
  dsimp only
  let hcont : ∀ j counts, Continuous (fun lambda : Time =>
      idealPilotErrorCell (n := n) epsilon lambda P counts j true) :=
    fun j counts => idealPilotErrorCell_continuous_time_of_pos he hn
      (show 1 ≤ d by omega) P counts j true
  exact idealPilotErrorCellPath_centered_maximal epsilon P true hprob hcont
    (fun j => idealGoodPilotCellPath_measurable epsilon he hn
      (show 1 ≤ d by omega) P j)
    (fun j => idealGoodPilotCellPath_integrable epsilon he he' hn hd P hprob j)
    (fun j => idealGoodPilotCellPath_ae_bv epsilon he hn hd P j)
    (fun j => idealGoodPilotCellPath_sq_integrable epsilon he he' hn hd P j)
    (idealGoodPilotCellPaths_independent epsilon he hn hd P)

/-- The marginal masses of a discrete observed law sum to one. With [the specified inputs and conditions](hyp:d,P), [the stated relationship holds](goal). -/
-- @node: discreteLaw_sum_cellMass
lemma discreteLaw_sum_cellMass {d : ℕ} (P : DiscreteLaw d) :
    ∑ j : Fin d, cellMass P j = 1 := by
  change ∑ j : Fin d, ∑ a : Bool, ∑ y : Bool,
    (P.pmf (j, a, y)).toReal = 1
  simpa [Fintype.sum_prod_type] using
    (PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : ℝ))).symm

/-- Equation (32): the squared local mass scales sum to a linear mass term
plus the uniform four-count remainder. With [the specified inputs and conditions](hyp:n,d,hn,hd,P), [the stated relationship holds](goal). -/
-- @node: sum_badPilotCellScale_sq_le
lemma sum_badPilotCellScale_sq_le {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d) :
    ∑ j : Fin d, badPilotCellScale (n := n) P j ^ 2 ≤
      2 * logAlphabet d / ((n : ℝ) / 8) +
        2 * d * (logAlphabet d / ((n : ℝ) / 8)) ^ 2 := by
  let m : ℝ := (n : ℝ) / 8
  let L : ℝ := logAlphabet d
  have hm : 0 < m := by dsimp [m]; positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith [Real.log_nonneg hdreal]
  have hmass0 (j : Fin d) : 0 ≤ cellMass P j := by
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun y _ =>
      ENNReal.toReal_nonneg
  have hpoint (j : Fin d) : badPilotCellScale (n := n) P j ^ 2 ≤
      2 * (cellMass P j * L / m) + 2 * (L / m) ^ 2 := by
    have hA : 0 ≤ cellMass P j * L / m :=
      div_nonneg (mul_nonneg (hmass0 j) hL) (le_of_lt hm)
    have hdelta : 0 ≤ L / m := by positivity
    have hsqrt := Real.sq_sqrt hA
    unfold badPilotCellScale
    dsimp only
    change (Real.sqrt (cellMass P j * L / m) + L / m) ^ 2 ≤ _
    nlinarith [sq_nonneg (Real.sqrt (cellMass P j * L / m) - L / m)]
  calc
    ∑ j : Fin d, badPilotCellScale (n := n) P j ^ 2 ≤
        ∑ j : Fin d, (2 * (cellMass P j * L / m) + 2 * (L / m) ^ 2) := by
      gcongr with j
      exact hpoint j
    _ = 2 * L / m + 2 * d * (L / m) ^ 2 := by
      rw [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum, ← Finset.sum_div]
      rw [← Finset.sum_mul]
      rw [discreteLaw_sum_cellMass P]
      simp
      ring
    _ = 2 * logAlphabet d / ((n : ℝ) / 8) +
        2 * d * (logAlphabet d / ((n : ℝ) / 8)) ^ 2 := by rfl

/-- Combining equations (21), (32), and the BV maximal inequality gives a
single quantitative bound for the centered sum of all good-pilot paths. With [the specified inputs and conditions](hyp:epsilon,he,he'), [the stated relationship holds](goal). -/
-- @node: idealGoodPilotError_centered_maximal_quantitative
lemma idealGoodPilotError_centered_maximal_quantitative
    (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n d : ℕ} (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d),
      IsProbabilityMeasure (idealCountLaw (n := n) P) →
      let hcont : ∀ j counts, Continuous (fun lambda : Time =>
        idealPilotErrorCell (n := n) epsilon lambda P counts j true) :=
        fun j counts => idealPilotErrorCell_continuous_time_of_pos he hn
          (show 1 ≤ d by omega) P counts j true
      (∫ counts, ‖∑ j, (idealPilotErrorCellPath epsilon P counts j true
            (hcont j counts) -
          ∫ x, idealPilotErrorCellPath epsilon P x j true (hcont j x)
            ∂idealCountLaw (n := n) P)‖ ^ 2
        ∂idealCountLaw (n := n) P) ≤
        C * (d : ℝ) ^ (1 / 16 : ℝ) *
          (2 * logAlphabet d / ((n : ℝ) / 8) +
            2 * d * (logAlphabet d / ((n : ℝ) / 8)) ^ 2) := by
  classical
  obtain ⟨C₀, hC₀, hcellAll⟩ :=
    idealGoodPilotCellPath_sq_integral_le epsilon he he'
  refine ⟨16384 * C₀, by positivity, ?_⟩
  intro n d hn hd P hprob
  dsimp only
  have hcell (j : Fin d) :
      (∫ counts, pathSize (idealPilotErrorCellPath epsilon P counts j true
        (idealPilotErrorCell_continuous_time_of_pos he hn (show 1 ≤ d by omega)
          P counts j true)) ^ 2 ∂idealCountLaw (n := n) P) ≤
        C₀ * (d : ℝ) ^ (1 / 16 : ℝ) *
          badPilotCellScale (n := n) P j ^ 2 := by
    calc
      _ = ∫ counts, (if idealPilotGoodBool (n := n) P counts j then
          pathSize (idealPilotErrorCellPath epsilon P counts j true
            (idealPilotErrorCell_continuous_time_of_pos he hn
              (show 1 ≤ d by omega) P counts j true)) ^ 2 else 0)
          ∂idealCountLaw (n := n) P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun counts =>
          idealGoodPilotCellPath_sq_eq_indicator epsilon he hn
            (show 1 ≤ d by omega) P counts j
      _ ≤ _ := (hcellAll hn hd P j).2
  have hsum :
      ∑ j : Fin d, (∫ counts,
        pathSize (idealPilotErrorCellPath epsilon P counts j true
          (idealPilotErrorCell_continuous_time_of_pos he hn
            (show 1 ≤ d by omega) P counts j true)) ^ 2
        ∂idealCountLaw (n := n) P) ≤
      (C₀ * (d : ℝ) ^ (1 / 16 : ℝ)) *
        ∑ j : Fin d, badPilotCellScale (n := n) P j ^ 2 := by
    rw [Finset.mul_sum]
    gcongr with j
    exact hcell j
  have hscale := sum_badPilotCellScale_sq_le hn (show 1 ≤ d by omega) P
  have hcoef : 0 ≤ C₀ * (d : ℝ) ^ (1 / 16 : ℝ) := by positivity
  calc
    _ ≤ 16384 * ∑ j : Fin d, (∫ counts,
        pathSize (idealPilotErrorCellPath epsilon P counts j true
          (idealPilotErrorCell_continuous_time_of_pos he hn
            (show 1 ≤ d by omega) P counts j true)) ^ 2
        ∂idealCountLaw (n := n) P) :=
      idealGoodPilotError_centered_maximal epsilon he he' hn hd P hprob
    _ ≤ 16384 * ((C₀ * (d : ℝ) ^ (1 / 16 : ℝ)) *
        ∑ j : Fin d, badPilotCellScale (n := n) P j ^ 2) := by
      gcongr
    _ ≤ 16384 * ((C₀ * (d : ℝ) ^ (1 / 16 : ℝ)) *
        (2 * logAlphabet d / ((n : ℝ) / 8) +
          2 * d * (logAlphabet d / ((n : ℝ) / 8)) ^ 2)) := by
      gcongr
    _ = (16384 * C₀) * (d : ℝ) ^ (1 / 16 : ℝ) *
        (2 * logAlphabet d / ((n : ℝ) / 8) +
          2 * d * (logAlphabet d / ((n : ℝ) / 8)) ^ 2) := by ring

end CausalSmith.Stat.DiscreteBudgetvalueCurve

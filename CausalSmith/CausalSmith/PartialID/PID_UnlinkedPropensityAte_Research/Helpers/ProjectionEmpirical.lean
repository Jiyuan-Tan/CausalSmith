module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.Projection
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionGeometry
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.Variance
public import Causalean.Mathlib.Probability.IidMeanVariance

/-!
# Empirical trial cell coordinates

This file records the finite-sample identities behind the trial half of the
projection radius.  A cell cumulative mass is a measurable finite average of
coordinate indicators, and under the i.i.d. product law its expectation is the
corresponding population cell mass.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:J,n,a,r,B,x), [this definition](goal) introduces the corresponding object. -/
def trialCellFrequency {J n : ℕ} (a : ArmSpace) (r : LabelSpace J)
    (B : Set OutcomeSpace) (x : TrialSample n J) : ℝ := by
  classical
  exact (n : ℝ)⁻¹ * ∑ i : Fin n,
    if (x i).1 = r ∧ (x i).2.1 = a ∧ (x i).2.2 ∈ B then (1 : ℝ) else 0

/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,a,r,B,hB,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma empiricalTrialCells_real_apply {J n : ℕ} (a : ArmSpace)
    (r : LabelSpace J) (B : Set OutcomeSpace) (hB : MeasurableSet B)
    (x : TrialSample n J) :
    (empiricalTrialCells x a r).real B = trialCellFrequency a r B x := by
  classical
  unfold empiricalTrialCells trialCellFrequency Measure.real
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  congr 1
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hcell : (x i).1 = r ∧ (x i).2.1 = a
    · simp only [hcell, and_self, ↓reduceIte]
      rw [Measure.dirac_apply' _ hB]
      by_cases hmem : (x i).2.2 ∈ B <;> simp [Set.indicator, hmem]
    · simp only [hcell, ↓reduceIte, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero]
      have hfull : ¬((x i).1 = r ∧ (x i).2.1 = a ∧ (x i).2.2 ∈ B) := by
        intro h
        exact hcell ⟨h.1, h.2.1⟩
      simp [hfull]
  · intro i _
    by_cases hcell : (x i).1 = r ∧ (x i).2.1 = a
    · by_cases hmem : (x i).2.2 ∈ B <;> simp [hcell, hmem, Set.indicator]
    · simp [hcell]

/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
@[fun_prop]
lemma measurable_trialCellFrequency {J n : ℕ} (a : ArmSpace)
    (r : LabelSpace J) (B : Set OutcomeSpace) (hB : MeasurableSet B) :
    Measurable (trialCellFrequency (n := n) a r B) := by
  classical
  unfold trialCellFrequency
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  have hi : Measurable (fun x : TrialSample n J => x i) := measurable_pi_apply i
  apply Measurable.ite
  · exact (measurableSet_eq_fun hi.fst
        (measurable_const : Measurable (fun _ : TrialSample n J => r))).inter
      ((measurableSet_eq_fun hi.snd.fst
        (measurable_const : Measurable (fun _ : TrialSample n J => a))).inter
      (hB.preimage hi.snd.snd))
  · fun_prop
  · fun_prop

/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
@[fun_prop]
lemma measurable_empiricalTrialCells_real_apply {J n : ℕ} (a : ArmSpace)
    (r : LabelSpace J) (B : Set OutcomeSpace) (hB : MeasurableSet B) :
    Measurable (fun x : TrialSample n J => (empiricalTrialCells x a r).real B) := by
  rw [show (fun x : TrialSample n J => (empiricalTrialCells x a r).real B) =
      trialCellFrequency a r B by
    funext x
    exact empiricalTrialCells_real_apply a r B hB x]
  exact measurable_trialCellFrequency a r B hB

/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,a,r,t), this result [establishes the stated mathematical conclusion](goal). -/
@[fun_prop]
lemma measurable_empiricalTrialCellCDF {J n : ℕ} (a : ArmSpace)
    (r : LabelSpace J) (t : ℝ) :
    Measurable (fun x : TrialSample n J =>
      (empiricalTrialCells x a r).real {y | (y : ℝ) ≤ t}) := by
  apply measurable_empiricalTrialCells_real_apply
  exact measurableSet_le (by fun_prop) measurable_const

/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,μ,hn,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma integral_trialCellFrequency_pi {J n : ℕ} (μ : Measure (Observation J))
    [IsProbabilityMeasure μ] (hn : 0 < n) (a : ArmSpace) (r : LabelSpace J)
    (B : Set OutcomeSpace) (hB : MeasurableSet B) :
    ∫ x, trialCellFrequency a r B x ∂Measure.pi (fun _ : Fin n => μ) =
      μ.real {z | z.1 = r ∧ z.2.1 = a ∧ z.2.2 ∈ B} := by
  classical
  let C : Set (Observation J) := {z | z.1 = r ∧ z.2.1 = a ∧ z.2.2 ∈ B}
  have hC : MeasurableSet C := by
    change MeasurableSet {z : Observation J | z.1 = r ∧ z.2.1 = a ∧ z.2.2 ∈ B}
    have hz : Measurable (fun z : Observation J => z) := measurable_id
    exact (measurableSet_eq_fun hz.fst
        (measurable_const : Measurable (fun _ : Observation J => r))).inter
      ((measurableSet_eq_fun hz.snd.fst
        (measurable_const : Measurable (fun _ : Observation J => a))).inter
      (hB.preimage hz.snd.snd))
  have hcoord (i : Fin n) :
      Integrable (fun x : TrialSample n J => if x i ∈ C then (1 : ℝ) else 0)
        (Measure.pi fun _ : Fin n => μ) := by
    have hm : Measurable (fun x : TrialSample n J => if x i ∈ C then (1 : ℝ) else 0) :=
      Measurable.ite (hC.preimage (measurable_pi_apply i)) measurable_const measurable_const
    exact Integrable.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      by_cases hx : x i ∈ C <;> simp [hx])
  unfold trialCellFrequency
  rw [MeasureTheory.integral_const_mul]
  change (n : ℝ)⁻¹ *
      ∫ x : TrialSample n J, ∑ i : Fin n, if x i ∈ C then (1 : ℝ) else 0
        ∂Measure.pi (fun _ : Fin n => μ) = μ.real C
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun i _ => hcoord i)]
  have heach (i : Fin n) :
      ∫ x : TrialSample n J, (if x i ∈ C then (1 : ℝ) else 0)
          ∂Measure.pi (fun _ : Fin n => μ) = μ.real C := by
    calc
      (∫ x : TrialSample n J, (if x i ∈ C then (1 : ℝ) else 0)
          ∂Measure.pi (fun _ : Fin n => μ)) =
          ∫ x : TrialSample n J, C.indicator (fun _ => (1 : ℝ)) (x i)
            ∂Measure.pi (fun _ : Fin n => μ) := by
              apply integral_congr_ae
              filter_upwards [] with x
              simp [Set.indicator]
      _ = ∫ z : Observation J, C.indicator (fun _ => (1 : ℝ)) z ∂μ := by
        rw [MeasureTheory.integral_comp_eval (μ := fun _ : Fin n => μ) (i := i)]
        exact (measurable_const.indicator hC).aestronglyMeasurable
      _ = μ.real C := MeasureTheory.integral_indicator_one hC
  simp_rw [heach]
  simp [Nat.ne_of_gt hn]

-- @node: empiricalScoreCells_real_apply
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,g,a,r,B,hB,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma empiricalScoreCells_real_apply {ε : ℝ} {J m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (a : ArmSpace) (r : LabelSpace J)
    (B : Set (ScoreSpace ε)) (hB : MeasurableSet B)
    (x : Fin m → ScoreSpace ε) :
    (empiricalScoreCells g x a r).real B =
      ∑ j : Fin m, {j | g (x j) = r ∧ x j ∈ B}.indicator
        (fun j => ENNReal.toReal (ENNReal.ofReal (armProb a (x j)) / m)) j := by
  classical
  unfold empiricalScoreCells Measure.real
  rw [Measure.coe_finsetSum, Finset.sum_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro j _
    by_cases hr : g (x j) = r
    · simp only [hr, ↓reduceIte, Measure.smul_apply]
      rw [Measure.dirac_apply' _ hB]
      by_cases hmem : x j ∈ B <;> simp [Set.indicator, hr, hmem, ENNReal.toReal_div]
    · simp [hr]
  · intro j _
    by_cases hr : g (x j) = r
    · by_cases hmem : x j ∈ B
      · simp only [hr, ↓reduceIte, Measure.smul_apply]
        rw [Measure.dirac_apply' _ hB]
        simp only [Set.indicator, if_pos hmem, Pi.one_apply, smul_eq_mul, mul_one]
        by_cases hm : m = 0
        · subst m
          exact Fin.elim0 j
        · exact ne_of_lt (ENNReal.div_lt_top ENNReal.ofReal_ne_top (by simp [hm]))
      · simp [hr, hmem]
    · simp [hr]

-- @node: variance_scoreCellIndicator
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,hOverlap,H,g,hg,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma variance_scoreCellIndicator {ε : ℝ} {J : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (a : ArmSpace) (r : LabelSpace J)
    (B : Set (ScoreSpace ε)) (hB : MeasurableSet B) :
    ProbabilityTheory.variance
      ({e : ScoreSpace ε | g e = r ∧ e ∈ B}.indicator (armProb a)) H ≤ 1 / 4 := by
  classical
  have hcell : MeasurableSet {e : ScoreSpace ε | g e = r ∧ e ∈ B} :=
    (measurableSet_eq_fun hg measurable_const).inter hB
  have hp : Measurable (armProb a : ScoreSpace ε → ℝ) := by
    unfold armProb
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hm : Measurable ({e : ScoreSpace ε | g e = r ∧ e ∈ B}.indicator (armProb a)) :=
    hp.indicator hcell
  have hb : ∀ e : ScoreSpace ε,
      {e : ScoreSpace ε | g e = r ∧ e ∈ B}.indicator (armProb a) e ∈
        Set.Icc (0 : ℝ) 1 := by
    intro e
    by_cases he : g e = r ∧ e ∈ B
    · simpa [Set.indicator, he] using
        (show armProb a e ∈ Set.Icc (0 : ℝ) 1 from
          ⟨le_trans (le_of_lt hOverlap.1) (projectionArmProb_bounds hOverlap a e).1,
            (projectionArmProb_bounds hOverlap a e).2⟩)
    · simp [Set.indicator, he]
  have hv := ProbabilityTheory.variance_le_sq_of_bounded
    (μ := H) (a := 0) (b := 1) (Filter.Eventually.of_forall hb) hm.aemeasurable
  norm_num at hv
  exact hv

-- @node: variance_trialCellIndicator_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,μ,i,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma variance_trialCellIndicator_pi {J n : ℕ}
    (μ : Measure (Observation J)) [IsProbabilityMeasure μ]
    (i : Fin n) (a : ArmSpace) (r : LabelSpace J)
    (B : Set OutcomeSpace) (hB : MeasurableSet B) :
    ProbabilityTheory.variance
      (fun x : TrialSample n J =>
        {z : Observation J | z.1 = r ∧ z.2.1 = a ∧ z.2.2 ∈ B}.indicator
          (fun _ => (1 : ℝ)) (x i))
      (Measure.pi fun _ : Fin n => μ) ≤ 1 / 4 := by
  classical
  let C : Set (Observation J) :=
    {z | z.1 = r ∧ z.2.1 = a ∧ z.2.2 ∈ B}
  have hC : MeasurableSet C := by
    exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      ((measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const).inter
        (hB.preimage (measurable_snd.comp measurable_snd)))
  have hm : Measurable (fun x : TrialSample n J =>
      if x i ∈ C then (1 : ℝ) else 0) := by
    exact Measurable.ite (hC.preimage (measurable_pi_apply i))
      measurable_const measurable_const
  have hb : ∀ x : TrialSample n J,
      (if x i ∈ C then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    by_cases hx : x i ∈ C <;> simp [hx]
  have hv := ProbabilityTheory.variance_le_sq_of_bounded
    (μ := Measure.pi fun _ : Fin n => μ)
    (X := fun x : TrialSample n J => if x i ∈ C then (1 : ℝ) else 0)
    (a := 0) (b := 1) (Filter.Eventually.of_forall hb) hm.aemeasurable
  norm_num at hv
  simpa [Set.indicator, C] using hv

-- @node: variance_trialCellFrequency_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,μ,hn,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma variance_trialCellFrequency_pi {J n : ℕ}
    (μ : Measure (Observation J)) [IsProbabilityMeasure μ]
    (hn : 0 < n) (a : ArmSpace) (r : LabelSpace J)
    (B : Set OutcomeSpace) (hB : MeasurableSet B) :
    ProbabilityTheory.variance (trialCellFrequency a r B)
      (Measure.pi fun _ : Fin n => μ) ≤ 1 / (4 * n) := by
  classical
  let C : Set (Observation J) :=
    {z | z.1 = r ∧ z.2.1 = a ∧ z.2.2 ∈ B}
  let F : Observation J → ℝ := C.indicator (fun _ => 1)
  have hC : MeasurableSet C := by
    exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      ((measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const).inter
        (hB.preimage (measurable_snd.comp measurable_snd)))
  have hF : Measurable F := measurable_const.indicator hC
  have hbound : ∀ z, F z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z
    by_cases hz : z ∈ C <;> simp [F, hz]
  have hlp : MemLp F 2 μ :=
    memLp_of_bounded (Filter.Eventually.of_forall hbound) hF.aestronglyMeasurable 2
  have hvar : ProbabilityTheory.variance F μ ≤ 1 / 4 := by
    have hv := ProbabilityTheory.variance_le_sq_of_bounded
      (μ := μ) (X := F) (a := 0) (b := 1)
      (Filter.Eventually.of_forall hbound) hF.aemeasurable
    norm_num at hv
    exact hv
  have hmain := Causalean.Mathlib.Probability.iid_average_variance_fintype
    (ι := Fin n) μ F hlp
  have hfun : trialCellFrequency a r B =
      (fun x : TrialSample n J => (n : ℝ)⁻¹ * ∑ i : Fin n, F (x i)) := by
    funext x
    unfold trialCellFrequency F C
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Set.indicator]
    rfl
  rw [hfun]
  simp only [Fintype.card_fin] at hmain
  rw [hmain]
  have hn0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  calc
    (n : ℝ)⁻¹ * ProbabilityTheory.variance F μ ≤ (n : ℝ)⁻¹ * (1 / 4) :=
      mul_le_mul_of_nonneg_left hvar hn0
    _ = 1 / (4 * n) := by field_simp

-- @node: scoreCellFrequency
/-- For [the specified mathematical inputs](hyp:ε,J,m,g,a,r,B,x), [this definition](goal) introduces the corresponding object. -/
def scoreCellFrequency {ε : ℝ} {J m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (a : ArmSpace) (r : LabelSpace J)
    (B : Set (ScoreSpace ε)) (x : Fin m → ScoreSpace ε) : ℝ :=
  (m : ℝ)⁻¹ * ∑ j : Fin m,
    {e : ScoreSpace ε | g e = r ∧ e ∈ B}.indicator (armProb a) (x j)

-- @node: empiricalScoreCells_real_eq_scoreCellFrequency
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,g,a,r,B,hB,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma empiricalScoreCells_real_eq_scoreCellFrequency {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε)
    (g : ScoreSpace ε → LabelSpace J) (a : ArmSpace) (r : LabelSpace J)
    (B : Set (ScoreSpace ε)) (hB : MeasurableSet B)
    (x : Fin m → ScoreSpace ε) :
    (empiricalScoreCells g x a r).real B = scoreCellFrequency g a r B x := by
  classical
  rw [empiricalScoreCells_real_apply g a r B hB x]
  unfold scoreCellFrequency
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : g (x j) = r ∧ x j ∈ B
  · simp only [Set.indicator]
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal
      (le_trans (le_of_lt hOverlap.1)
        (projectionArmProb_bounds hOverlap a (x j)).1), ENNReal.toReal_natCast]
    simp [hj, div_eq_mul_inv, mul_comm]
  · simp [Set.indicator, hj]

-- @node: measurable_scoreCellFrequency
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,g,hg,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
@[fun_prop]
lemma measurable_scoreCellFrequency {ε : ℝ} {J m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (hg : Measurable g)
    (a : ArmSpace) (r : LabelSpace J)
    (B : Set (ScoreSpace ε)) (hB : MeasurableSet B) :
    Measurable (scoreCellFrequency (m := m) g a r B) := by
  have hcell : MeasurableSet {e : ScoreSpace ε | g e = r ∧ e ∈ B} :=
    (measurableSet_eq_fun hg measurable_const).inter hB
  have hp : Measurable (armProb a : ScoreSpace ε → ℝ) := by
    unfold armProb
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  unfold scoreCellFrequency
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j _
  exact (hp.indicator hcell).comp (measurable_pi_apply j)

-- @node: integral_scoreCellFrequency_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,H,g,hg,hm,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma integral_scoreCellFrequency_pi {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (hm : 0 < m) (a : ArmSpace) (r : LabelSpace J)
    (B : Set (ScoreSpace ε)) (hB : MeasurableSet B) :
    ∫ x, scoreCellFrequency g a r B x ∂Measure.pi (fun _ : Fin m => H) =
      ∫ e, {e : ScoreSpace ε | g e = r ∧ e ∈ B}.indicator (armProb a) e ∂H := by
  let F : ScoreSpace ε → ℝ :=
    {e : ScoreSpace ε | g e = r ∧ e ∈ B}.indicator (armProb a)
  have hcell : MeasurableSet {e : ScoreSpace ε | g e = r ∧ e ∈ B} :=
    (measurableSet_eq_fun hg measurable_const).inter hB
  have hp : Measurable (armProb a : ScoreSpace ε → ℝ) := by
    unfold armProb
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hF : Measurable F := hp.indicator hcell
  have hbound : ∀ e, F e ∈ Set.Icc (0 : ℝ) 1 := by
    intro e
    by_cases he : g e = r ∧ e ∈ B
    · simpa [F, Set.indicator, he] using
        (show armProb a e ∈ Set.Icc (0 : ℝ) 1 from
          ⟨le_trans (le_of_lt hOverlap.1) (projectionArmProb_bounds hOverlap a e).1,
            (projectionArmProb_bounds hOverlap a e).2⟩)
    · simp [F, he]
  have hInt : Integrable F H :=
    Integrable.of_bound hF.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun e => by
        have he := hbound e
        simpa [Real.norm_eq_abs, abs_of_nonneg he.1] using he.2)
  have hcoord (j : Fin m) :
      Integrable (fun x : Fin m → ScoreSpace ε => F (x j))
        (Measure.pi fun _ : Fin m => H) :=
    MeasureTheory.integrable_comp_eval hInt
  change (∫ x : Fin m → ScoreSpace ε,
      (m : ℝ)⁻¹ * ∑ j : Fin m, F (x j)
      ∂Measure.pi (fun _ : Fin m => H)) = ∫ e, F e ∂H
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hcoord j)]
  have heach (j : Fin m) :
      ∫ x : Fin m → ScoreSpace ε, F (x j)
        ∂Measure.pi (fun _ : Fin m => H) = ∫ e, F e ∂H := by
    rw [MeasureTheory.integral_comp_eval (μ := fun _ : Fin m => H) (i := j)]
    exact hF.aestronglyMeasurable
  simp_rw [heach]
  simp [Nat.ne_of_gt hm]

-- @node: integral_empiricalScoreCells_real_apply_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,H,g,hg,hm,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma integral_empiricalScoreCells_real_apply_pi {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (hm : 0 < m) (a : ArmSpace) (r : LabelSpace J)
    (B : Set (ScoreSpace ε)) (hB : MeasurableSet B) :
    ∫ x, (empiricalScoreCells g x a r).real B
        ∂Measure.pi (fun _ : Fin m => H) =
      ∫ e, {e : ScoreSpace ε | g e = r ∧ e ∈ B}.indicator (armProb a) e ∂H := by
  simpa only [empiricalScoreCells_real_eq_scoreCellFrequency hOverlap g a r B hB] using
    integral_scoreCellFrequency_pi hOverlap H g hg hm a r B hB

-- @node: variance_scoreCellFrequency_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,H,g,hg,hm,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma variance_scoreCellFrequency_pi {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (hm : 0 < m) (a : ArmSpace) (r : LabelSpace J)
    (B : Set (ScoreSpace ε)) (hB : MeasurableSet B) :
    ProbabilityTheory.variance (scoreCellFrequency g a r B)
      (Measure.pi fun _ : Fin m => H) ≤ 1 / (4 * m) := by
  let F : ScoreSpace ε → ℝ :=
    {e : ScoreSpace ε | g e = r ∧ e ∈ B}.indicator (armProb a)
  have hcell : MeasurableSet {e : ScoreSpace ε | g e = r ∧ e ∈ B} :=
    (measurableSet_eq_fun hg measurable_const).inter hB
  have hp : Measurable (armProb a : ScoreSpace ε → ℝ) := by
    unfold armProb
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hF : Measurable F := hp.indicator hcell
  have hbound : ∀ e, F e ∈ Set.Icc (0 : ℝ) 1 := by
    intro e
    by_cases he : g e = r ∧ e ∈ B
    · simpa [F, Set.indicator, he] using
        (show armProb a e ∈ Set.Icc (0 : ℝ) 1 from
          ⟨le_trans (le_of_lt hOverlap.1) (projectionArmProb_bounds hOverlap a e).1,
            (projectionArmProb_bounds hOverlap a e).2⟩)
    · simp [F, he]
  have hlp : MemLp F 2 H :=
    memLp_of_bounded (Filter.Eventually.of_forall hbound) hF.aestronglyMeasurable 2
  have hvar : ProbabilityTheory.variance F H ≤ 1 / 4 := by
    simpa [F] using variance_scoreCellIndicator hOverlap H g hg a r B hB
  have hmain := Causalean.Mathlib.Probability.iid_average_variance_fintype
    (ι := Fin m) H F hlp
  change ProbabilityTheory.variance
    (fun x : Fin m → ScoreSpace ε => (m : ℝ)⁻¹ * ∑ j : Fin m, F (x j))
      (Measure.pi fun _ : Fin m => H) ≤ 1 / (4 * m)
  simp only [Fintype.card_fin] at hmain
  rw [hmain]
  calc
    (m : ℝ)⁻¹ * ProbabilityTheory.variance F H ≤ (m : ℝ)⁻¹ * (1 / 4) :=
      mul_le_mul_of_nonneg_left hvar (by positivity)
    _ = 1 / (4 * m) := by field_simp

-- @node: variance_empiricalScoreCells_real_apply_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,m,hOverlap,H,g,hg,hm,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma variance_empiricalScoreCells_real_apply_pi {ε : ℝ} {J m : ℕ}
    (hOverlap : Overlap ε) (H : Measure (ScoreSpace ε))
    [IsProbabilityMeasure H] (g : ScoreSpace ε → LabelSpace J)
    (hg : Measurable g) (hm : 0 < m) (a : ArmSpace) (r : LabelSpace J)
    (B : Set (ScoreSpace ε)) (hB : MeasurableSet B) :
    ProbabilityTheory.variance
      (fun x : Fin m → ScoreSpace ε => (empiricalScoreCells g x a r).real B)
      (Measure.pi fun _ : Fin m => H) ≤ 1 / (4 * m) := by
  simpa only [empiricalScoreCells_real_eq_scoreCellFrequency hOverlap g a r B hB] using
    variance_scoreCellFrequency_pi hOverlap H g hg hm a r B hB

-- @node: projectionMeanAbs_le_sqrt_variance
/-- Given [the stated mathematical inputs and assumptions](hyp:Ω,μ,X,hX), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionMeanAbs_le_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : MemLp X 2 μ) :
    ∫ x, |X x - ∫ y, X y ∂μ| ∂μ ≤
      Real.sqrt (ProbabilityTheory.variance X μ) := by
  let Z : Ω → ℝ := fun x => X x - ∫ y, X y ∂μ
  have hZ : MemLp Z 2 μ := hX.sub (memLp_const _)
  have hOne : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ := memLp_const _
  have hh : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hZ' : MemLp Z (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hZ
  have hOne' : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hOne
  have h := integral_mul_norm_le_Lp_mul_Lq hh hZ' hOne'
  simp only [norm_one, mul_one, integral_const, smul_eq_mul, mul_one,
    Real.one_rpow, Real.norm_eq_abs] at h
  rw [show μ.real Set.univ = 1 from isProbabilityMeasure_iff_real.mp inferInstance,
    Real.one_rpow, mul_one] at h
  rw [ProbabilityTheory.variance_eq_integral hX.1.aemeasurable]
  simpa [Z, sq_abs, Real.sqrt_eq_rpow, div_eq_mul_inv] using h

-- @node: projectionMeanAbs_le_inv_two_sqrt
/-- Given [the stated mathematical inputs and assumptions](hyp:Ω,μ,X,N,hN,hX,hvar), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionMeanAbs_le_inv_two_sqrt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (N : ℕ) (hN : 0 < N) (hX : MemLp X 2 μ)
    (hvar : ProbabilityTheory.variance X μ ≤ 1 / (4 * N)) :
    ∫ x, |X x - ∫ y, X y ∂μ| ∂μ ≤ 1 / (2 * Real.sqrt N) := by
  have hcs := projectionMeanAbs_le_sqrt_variance μ X hX
  have hs := Real.sqrt_le_sqrt hvar
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsimp : Real.sqrt (1 / (4 * (N : ℝ))) =
      1 / (2 * Real.sqrt N) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
    simp only [show Real.sqrt (4 : ℝ) = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    simp only [Real.sqrt_one]
  calc
    ∫ x, |X x - ∫ y, X y ∂μ| ∂μ ≤
      Real.sqrt (ProbabilityTheory.variance X μ) := hcs
    _ ≤ Real.sqrt (1 / (4 * N)) := hs
    _ = 1 / (2 * Real.sqrt N) := hsimp

-- @node: meanAbs_trialCellFrequency_pi
/-- Given [the stated mathematical inputs and assumptions](hyp:J,n,μ,hn,a,r,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma meanAbs_trialCellFrequency_pi {J n : ℕ}
    (μ : Measure (Observation J)) [IsProbabilityMeasure μ]
    (hn : 0 < n) (a : ArmSpace) (r : LabelSpace J)
    (B : Set OutcomeSpace) (hB : MeasurableSet B) :
    ∫ x, |trialCellFrequency a r B x -
      μ.real {z | z.1 = r ∧ z.2.1 = a ∧ z.2.2 ∈ B}|
      ∂Measure.pi (fun _ : Fin n => μ) ≤ 1 / (2 * Real.sqrt n) := by
  classical
  let C : Set (Observation J) :=
    {z | z.1 = r ∧ z.2.1 = a ∧ z.2.2 ∈ B}
  have hC : MeasurableSet C := by
    exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      ((measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const).inter
        (hB.preimage (measurable_snd.comp measurable_snd)))
  have hcoord (i : Fin n) :
      MemLp (fun x : TrialSample n J => if x i ∈ C then (1 : ℝ) else 0) 2
        (Measure.pi fun _ : Fin n => μ) := by
    have hm : Measurable (fun x : TrialSample n J =>
        if x i ∈ C then (1 : ℝ) else 0) :=
      Measurable.ite (hC.preimage (measurable_pi_apply i)) measurable_const measurable_const
    have hb : ∀ x : TrialSample n J,
        (if x i ∈ C then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := by
      intro x
      by_cases hx : x i ∈ C <;> simp [hx]
    exact memLp_of_bounded (Filter.Eventually.of_forall hb) hm.aestronglyMeasurable 2
  have hX : MemLp (trialCellFrequency a r B) 2
      (Measure.pi fun _ : Fin n => μ) := by
    have hs := memLp_finsetSum Finset.univ (fun i _ => hcoord i)
    have hs' := hs.const_mul (n : ℝ)⁻¹
    unfold trialCellFrequency
    simpa only [C, Set.mem_ofPred_eq] using hs'
  rw [← integral_trialCellFrequency_pi μ hn a r B hB]
  exact projectionMeanAbs_le_inv_two_sqrt
    (Measure.pi fun _ : Fin n => μ) (trialCellFrequency a r B) n hn hX
    (variance_trialCellFrequency_pi μ hn a r B hB)

end
end CausalSmith.PartialID.UnlinkedPropensityAte

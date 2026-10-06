module
public import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Basic
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.Definitions

/-!
# Discrete budget value curves

The finite observed and potential-outcome carriers reuse the earlier finite-PMF
development. The causal restrictions and budget functional are paper-specific.
-/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- the cell definition specifies [the stated object](goal). -/
abbrev Cell := CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.Cell
/-- the obs definition specifies [the stated object](goal). -/
abbrev Obs := CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.Obs
/-- the discrete law definition specifies [the stated object](goal). -/
abbrev DiscreteLaw := CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.DiscreteLaw
  -- @realizes q_j(observed law PMF carrier)
/-- For [d](hyp:d), the potential atom definition specifies [the stated object](goal). -/
abbrev PotentialAtom (d : ℕ) := Fin d × Bool × Bool × Bool
  -- @realizes P(four-coordinate atom X,A,Y(0),Y(1))
/-- For [d](hyp:d), the observed from potential definition specifies [the stated object](goal). -/
def observedFromPotential {d : ℕ} : PotentialAtom d →
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.FullObs d :=
  fun z => (z.1, z.2.1, if z.2.1 then z.2.2.2 else z.2.2.1,
    z.2.2.1, z.2.2.2)
  -- @realizes P(observed Y is selected deterministically from Y(0),Y(1))
/-- For [d](hyp:d), [Q](hyp:Q), the canonical observed outcome definition specifies [the stated object](goal). -/
def CanonicalObservedOutcome {d : ℕ}
    (Q : CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.PotentialLaw d) : Prop :=
  ∃ R : PMF (PotentialAtom d), Q.pmf = R.map observedFromPotential
  -- @realizes P(five-coordinate representation is the deterministic lift of a four-coordinate law)

/-- The canonical observed outcome of consistency result. It proves [the stated conclusion](goal). -/
lemma canonicalObservedOutcome_of_consistency {d : ℕ}
    (Q : CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.PotentialLaw d)
    (h : CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.Consistency Q) :
    CanonicalObservedOutcome Q := by
  let forgetObserved :
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.FullObs d → PotentialAtom d :=
    fun z => (z.1, z.2.1, z.2.2.2.1, z.2.2.2.2)
  let R : PMF (PotentialAtom d) := Q.pmf.map forgetObserved
  refine ⟨R, ?_⟩
  rw [show R.map observedFromPotential =
      Q.pmf.map (observedFromPotential ∘ forgetObserved) by
    simp [R, PMF.map_comp]]
  apply PMF.ext
  intro z
  rw [PMF.map_apply]
  have hzero (w : CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.FullObs d)
      (hw : w.2.2.1 ≠ (if w.2.1 then w.2.2.2.2 else w.2.2.2.1)) :
      Q.pmf w = 0 := by
    have hr := h w hw
    unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass at hr
    apply ((ENNReal.toReal_eq_zero_iff _).mp hr).resolve_right
    exact PMF.apply_ne_top Q.pmf w
  by_cases hz : z.2.2.1 = (if z.2.1 then z.2.2.2.2 else z.2.2.2.1)
  · have heqz : z = (observedFromPotential ∘ forgetObserved) z := by
      rcases z with ⟨x, a, y, y0, y1⟩
      simp only [Function.comp_apply, observedFromPotential, forgetObserved,
        Prod.mk.injEq] at hz ⊢
      aesop
    rw [tsum_eq_single z]
    · rw [if_pos heqz]
    · intro w hw
      split_ifs with heq
      · apply hzero w
        intro hcanonical
        apply hw
        rcases z with ⟨x, a, y, y0, y1⟩
        rcases w with ⟨x', a', y', y0', y1'⟩
        simp only [Function.comp_apply, observedFromPotential, forgetObserved,
          Prod.mk.injEq] at heq
        simp only [Prod.mk.injEq] at hz hcanonical ⊢
        aesop
      · rfl
  · rw [hzero z hz]
    symm
    apply ENNReal.tsum_eq_zero.2
    intro w
    split_ifs with heq
    · exfalso
      apply hz
      rcases z with ⟨x, a, y, y0, y1⟩
      rcases w with ⟨x', a', y', y0', y1'⟩
      simp only [Function.comp_apply, observedFromPotential, forgetObserved,
        Prod.mk.injEq] at heq ⊢
      aesop
    · rfl

/-- The potential law structure records the data and laws for [d](hyp:d). -/
structure PotentialLaw (d : ℕ) where
  fourPmf : PMF (PotentialAtom d)
    -- @realizes P(primary probability law of X,A,Y(0),Y(1))
  val : CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.PotentialLaw d
  canonical : val.pmf = fourPmf.map observedFromPotential
    -- @realizes P(observed Y is fixed by the four-coordinate law at the binder)
  consistent : CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.Consistency val
  -- @realizes P(five-coordinate compatibility view is a deterministic lift)
namespace PotentialLaw
/-- For [d](hyp:d), [Q](hyp:Q), the pmf definition specifies [the stated object](goal). -/
noncomputable def pmf {d : ℕ} (Q : PotentialLaw d) :
    PMF (CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.FullObs d) := Q.val.pmf
/-- The property result. It proves [the stated conclusion](goal). -/
theorem property {d : ℕ} (Q : PotentialLaw d) :
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.Consistency Q.val ∧
      CanonicalObservedOutcome Q.val :=
  ⟨Q.consistent, ⟨Q.fourPmf, Q.canonical⟩⟩
end PotentialLaw
/-- For [d](hyp:d), this instance provides [the stated structure](goal). -/
instance {d : ℕ} : Coe (PotentialLaw d)
    (CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.PotentialLaw d) where
  coe Q := Q.val
/-- the full obs definition specifies [the stated object](goal). -/
abbrev FullObs := CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.FullObs
/-- For [d](hyp:d), [P](hyp:P), [j](hyp:j), [a](hyp:a), the joint mass definition specifies [the stated object](goal). -/
noncomputable abbrev jointMass {d : ℕ} (P : DiscreteLaw d) (j : Fin d) (a y : Bool) : ℝ :=
  CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.jointMass P j a y
/-- For [d](hyp:d), [Q](hyp:Q), [z](hyp:z), the full mass definition specifies [the stated object](goal). -/
noncomputable abbrev fullMass {d : ℕ} (Q : PotentialLaw d) (z : FullObs d) : ℝ :=
  CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass Q z
/-- For [d](hyp:d), [P](hyp:P), [j](hyp:j), the cell vector definition specifies [the stated object](goal). -/
noncomputable abbrev cellVector {d : ℕ} (P : DiscreteLaw d) (j : Fin d) : Cell → ℝ :=
  CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellVector P j
-- @realizes p_j(observed covariate-cell mass)
/-- For [d](hyp:d), [P](hyp:P), [j](hyp:j), the cell mass definition specifies [the stated object](goal). -/
noncomputable abbrev cellMass {d : ℕ} (P : DiscreteLaw d) (j : Fin d) : ℝ :=
  CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass P j
/-- For [d](hyp:d), [P](hyp:P), [a](hyp:a), [j](hyp:j), the arm mass definition specifies [the stated object](goal). -/
noncomputable abbrev armMass {d : ℕ} (P : DiscreteLaw d) (a : Bool) (j : Fin d) : ℝ :=
  CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.armMass P a j
/-- For [d](hyp:d), [P](hyp:P), [j](hyp:j), the propensity definition specifies [the stated object](goal). -/
noncomputable abbrev propensity {d : ℕ} (P : DiscreteLaw d) (j : Fin d) : ℝ :=
  CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.propensity P j
  -- @realizes e_j(occupied-cell treatment propensity)
/-- For [d](hyp:d), [P](hyp:P), [n](hyp:n), the product law definition specifies [the stated object](goal). -/
noncomputable abbrev productLaw {d : ℕ} (P : DiscreteLaw d) (n : ℕ) : Measure (Fin n → Obs d) :=
  CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.productLaw P n
/-- For [d](hyp:d), [Q](hyp:Q), the observed marginal definition specifies [the stated object](goal). -/
noncomputable abbrev observedMarginal {d : ℕ} (Q : PotentialLaw d) : DiscreteLaw d :=
  CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal Q
-- @realizes p_j(full-data covariate-cell mass)
/-- For [d](hyp:d), [Q](hyp:Q), [j](hyp:j), the po cell mass definition specifies [the stated object](goal). -/
noncomputable abbrev poCellMass {d : ℕ} (Q : PotentialLaw d) (j : Fin d) : ℝ :=
  CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass Q j
/-- For [d](hyp:d), [Q](hyp:Q), [a](hyp:a), [j](hyp:j), the po regression definition specifies [the stated object](goal). -/
noncomputable abbrev poRegression {d : ℕ} (Q : PotentialLaw d) (a : Fin 2) (j : Fin d) : ℝ :=
  CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poRegression Q a j

-- @env: S1
variable (n : ℕ) -- @realizes n(sample size)
variable (d : {d : ℕ // 2 ≤ d}) -- @realizes d(alphabet size at least two)
variable (epsilon : Set.Ioo (0 : ℝ) (1 / 2)) -- @realizes \epsilon(overlap bound in (0,1/2))
variable (b0 : Set.Icc (0 : ℝ) (1 / 2)) -- @realizes b_0(budget endpoint in [0,1/2])
variable (j : Fin d.1) (a : Bool) -- @realizes j(cell index) @realizes a(binary arm)

/-- The finite observation carrier. -/
abbrev ObservedRecord (d : ℕ) := Obs d
  -- @realizes [d](Fin d) @realizes X(first coordinate) @realizes A(second coordinate)
  -- @realizes Y(third coordinate) @realizes O(observed record)

/-- A finite observed sample. -/
abbrev ObservedSample (n d : ℕ) := Fin n → Obs d
  -- @realizes O^{(n)}(n independent records)

/-- The four nonnegative observed cell masses. -/
noncomputable abbrev observedCellVector {d : ℕ} (P : DiscreteLaw d) (j : Fin d) := cellVector P j
  -- @realizes q_j(observed four-mass vector) @realizes u(generic four-vector)

-- @node: ass:iid-sampling
/-- For [d](hyp:d), [P](hyp:P), [mu](hyp:mu), the iid sampling definition specifies [the stated object](goal). -/
def IidSampling {d n : ℕ} (P : DiscreteLaw d)
    (mu : Measure (Fin n → Obs d)) : Prop := mu = productLaw P n

/-- A four-variable potential-outcome law with its derived observed outcome. -/
abbrev FullRecord (d : ℕ) := FullObs d
  -- @realizes Y(a)(last two coordinates)

-- @env: S2
variable (Q : PotentialLaw d) -- @realizes P(full-data law)

-- @node: ass:consistency
/-- For [d](hyp:d), [Q](hyp:Q), the consistency definition specifies [the stated object](goal). -/
def Consistency {d : ℕ} (Q : PotentialLaw d) : Prop :=
  ∀ z, z.2.2.1 ≠ (if z.2.1 then z.2.2.2.2 else z.2.2.2.1) → fullMass Q z = 0
  -- @realizes Y(a)(selected potential outcome) @realizes Y(observed selected outcome)

/-- Joint atom mass for the two potential outcomes, after marginalizing observed Y. -/
noncomputable def poPairAtom {d : ℕ} (Q : PotentialLaw d)
    (j : Fin d) (y0 y1 : Bool) : ℝ :=
  ∑ a : Bool, ∑ y : Bool, fullMass Q (j, a, y, y0, y1)

/-- Treatment atom mass within a covariate cell. -/
noncomputable def poTreatmentAtom {d : ℕ} (Q : PotentialLaw d)
    (j : Fin d) (a : Bool) : ℝ :=
  ∑ y : Bool, ∑ y0 : Bool, ∑ y1 : Bool, fullMass Q (j, a, y, y0, y1)

/-- Joint treatment and potential-outcome atom. -/
noncomputable def poJointAtom {d : ℕ} (Q : PotentialLaw d)
    (j : Fin d) (a y0 y1 : Bool) : ℝ :=
  ∑ y : Bool, fullMass Q (j, a, y, y0, y1)

-- @node: ass:conditional-exchangeability
/-- For [d](hyp:d), [Q](hyp:Q), the conditional exchangeability definition specifies [the stated object](goal). -/
def ConditionalExchangeability {d : ℕ} (Q : PotentialLaw d) : Prop :=
  ∀ j a y0 y1, poJointAtom Q j a y0 y1 * poCellMass Q j =
    poTreatmentAtom Q j a * poPairAtom Q j y0 y1
  -- @realizes Y(a)(joint pair of potential outcomes) @realizes A(independent arm)
  -- @realizes X(conditioning cell)

-- @node: ass:overlap
/-- For [d](hyp:d), [epsilon](hyp:epsilon), [P](hyp:P), the overlap definition specifies [the stated object](goal). -/
def Overlap {d : ℕ} (epsilon : ℝ) (P : DiscreteLaw d) : Prop :=
  ∀ j, 0 < cellMass P j →
    epsilon ≤ propensity P j ∧ propensity P j ≤ 1 - epsilon
    -- @realizes p_j(occupied cells) @realizes e_j(propensity band)

-- @node: def:model-class
/-- The causal model class structure records the data and laws for [epsilon](hyp:epsilon), [d](hyp:d), [Q](hyp:Q). -/
structure CausalModelClass (epsilon : ℝ) {d : ℕ} (Q : PotentialLaw d) : Prop where
  alphabet : 2 ≤ d -- @realizes d(model alphabet has at least two cells)
  overlapParameter : epsilon ∈ Set.Ioo (0 : ℝ) (1 / 2)
    -- @realizes \epsilon(model overlap parameter in (0,1/2))
  consistency : Consistency Q
  exchangeability : ConditionalExchangeability Q
  overlap : Overlap epsilon (observedMarginal Q)
    -- @realizes \mathcal M_{d,\epsilon}(three causal restrictions)

/-- Cell effect, totalized to zero on null cells. -/
noncomputable def effect {d : ℕ} (Q : PotentialLaw d) (j : Fin d) : ℝ :=
  poRegression Q 1 j - poRegression Q 0 j
  -- @realizes \tau_j(difference of potential-outcome means)

/-- Cell potential-outcome regression. -/
noncomputable abbrev potentialMean {d : ℕ} (Q : PotentialLaw d)
    (a : Fin 2) (j : Fin d) := poRegression Q a j
  -- @realizes \mu_{aj}(totalized conditional potential-outcome mean)

-- @node: def:budget-policy-class
/-- For [d](hyp:d), [Q](hyp:Q), [b](hyp:b), the budget policy class definition specifies [the stated object](goal). -/
def budgetPolicyClass {d : ℕ} (Q : PotentialLaw d)
    (b : Set.Icc (0 : ℝ) 1) : Set (Fin d → ℝ) :=
  {pi | (∀ j, pi j ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ j, poCellMass Q j * pi j ≤ b.1}
  -- @realizes \pi(cell treatment probabilities) @realizes b(capacity in [0,1])
  -- @realizes \Pi_b(P)(feasible randomized policies)

/-- Value of the never-treat policy. -/
noncomputable def controlValue {d : ℕ} (Q : PotentialLaw d) : ℝ :=
  ∑ j, poCellMass Q j * poRegression Q 0 j
  -- @realizes B(P)(control-policy value)

-- @node: def:budget-value
/-- For [d](hyp:d), [Q](hyp:Q), [b](hyp:b), the budget value definition specifies [the stated object](goal). -/
noncomputable def budgetValue {d : ℕ} (Q : PotentialLaw d) (b : ℝ) : ℝ :=
  if hb : b ∈ Set.Icc (0 : ℝ) 1 then
    controlValue Q + sSup ((fun pi : Fin d → ℝ =>
      ∑ j, poCellMass Q j * pi j * effect Q j) '' budgetPolicyClass Q ⟨b, hb⟩)
  else 0
  -- @realizes V_b(P)(optimal budget-constrained value)

-- @node: poRegression_unit_interval_budget
/-- The po regression unit interval budget result. It proves [the stated conclusion](goal). -/
lemma poRegression_unit_interval_budget {d : ℕ} (Q : PotentialLaw d)
    (a : Fin 2) (j : Fin d) : poRegression Q a j ∈ Set.Icc (0 : ℝ) 1 := by
  have hmass : 0 ≤ poCellMass Q j := by
    unfold poCellMass CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  let num : ℝ := ∑ arm : Bool, ∑ y : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
    (if (if a = 0 then y0 else y1) then 1 else 0 : ℝ) *
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass Q (j, arm, y, y0, y1)
  have hnum_nonneg : 0 ≤ num := by
    dsimp [num]
    apply Finset.sum_nonneg
    intro arm _
    apply Finset.sum_nonneg
    intro y _
    apply Finset.sum_nonneg
    intro y0 _
    apply Finset.sum_nonneg
    intro y1 _
    exact mul_nonneg (by split_ifs <;> norm_num) ENNReal.toReal_nonneg
  have hnum_le : num ≤ poCellMass Q j := by
    dsimp [num, poCellMass, CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass]
    apply Finset.sum_le_sum
    intro arm _
    apply Finset.sum_le_sum
    intro y _
    apply Finset.sum_le_sum
    intro y0 _
    apply Finset.sum_le_sum
    intro y1 _
    split_ifs <;> simp [CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass,
      ENNReal.toReal_nonneg]
  change 0 ≤ num / poCellMass Q j ∧ num / poCellMass Q j ≤ 1
  constructor
  · exact div_nonneg hnum_nonneg hmass
  · by_cases hp : poCellMass Q j = 0
    · simp [hp] at hnum_nonneg hnum_le ⊢
    · exact (div_le_iff₀ (lt_of_le_of_ne hmass (Ne.symm hp))).2 (by simpa using hnum_le)

-- @node: poCellMass_sum_one_budget
/-- The po cell mass sum one budget result. It proves [the stated conclusion](goal). -/
lemma poCellMass_sum_one_budget {d : ℕ} (Q : PotentialLaw d) :
    ∑ j : Fin d, poCellMass Q j = 1 := by
  calc
    _ = ∑ z : FullObs d, (Q.pmf z).toReal := by
      simp [poCellMass, PotentialLaw.pmf,
        CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass,
        CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass,
        Fintype.sum_prod_type]
    _ = 1 := by
      simpa using (PMF.integral_eq_sum Q.pmf (fun _ : FullObs d => (1 : ℝ))).symm

-- @node: budgetValue_unit_interval
/-- The budget value unit interval result. Under [the hb premise](hyp:hb), It proves [the stated conclusion](goal). -/
lemma budgetValue_unit_interval {d : ℕ} (Q : PotentialLaw d)
    (b : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    budgetValue Q b ∈ Set.Icc (0 : ℝ) 1 := by
  let gain (pi : Fin d → ℝ) :=
    ∑ j, poCellMass Q j * pi j * effect Q j
  have hmass (j : Fin d) : 0 ≤ poCellMass Q j := by
    unfold poCellMass CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hvalue (pi : Fin d → ℝ) (hpi : pi ∈ budgetPolicyClass Q ⟨b, hb⟩) :
      0 ≤ controlValue Q + gain pi ∧ controlValue Q + gain pi ≤ 1 := by
    have heq : controlValue Q + gain pi =
        ∑ j, poCellMass Q j *
          ((1 - pi j) * poRegression Q 0 j + pi j * poRegression Q 1 j) := by
      simp only [controlValue, gain, effect, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    constructor
    · apply Finset.sum_nonneg
      intro j _
      have h0 := poRegression_unit_interval_budget Q 0 j
      have h1 := poRegression_unit_interval_budget Q 1 j
      exact mul_nonneg (hmass j)
        (add_nonneg (mul_nonneg (by linarith [(hpi.1 j).2]) h0.1)
          (mul_nonneg (hpi.1 j).1 h1.1))
    · calc
        _ ≤ ∑ j : Fin d, poCellMass Q j := by
          apply Finset.sum_le_sum
          intro j _
          have h0 := poRegression_unit_interval_budget Q 0 j
          have h1 := poRegression_unit_interval_budget Q 1 j
          have hj : (1 - pi j) * poRegression Q 0 j +
              pi j * poRegression Q 1 j ≤ 1 := by
            calc
              _ ≤ (1 - pi j) * 1 + pi j * 1 := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left h0.2 (by linarith [(hpi.1 j).2]))
                  (mul_le_mul_of_nonneg_left h1.2 (hpi.1 j).1)
              _ = 1 := by ring
          exact mul_le_of_le_one_right (hmass j) hj
        _ = 1 := poCellMass_sum_one_budget Q
  let pi0 : Fin d → ℝ := fun _ => 0
  have hpi0 : pi0 ∈ budgetPolicyClass Q ⟨b, hb⟩ := by
    constructor
    · intro j
      norm_num [pi0]
    · simp [pi0, hb.1]
  have hsup : 0 ≤ sSup (gain '' budgetPolicyClass Q ⟨b, hb⟩) + controlValue Q ∧
      sSup (gain '' budgetPolicyClass Q ⟨b, hb⟩) + controlValue Q ≤ 1 := by
    have hne : (gain '' budgetPolicyClass Q ⟨b, hb⟩).Nonempty :=
      ⟨gain pi0, pi0, hpi0, rfl⟩
    have hbd : BddAbove (gain '' budgetPolicyClass Q ⟨b, hb⟩) := by
      refine ⟨1 - controlValue Q, ?_⟩
      rintro _ ⟨pi, hpi, rfl⟩
      linarith [(hvalue pi hpi).2]
    constructor
    · have h := le_csSup hbd (Set.mem_image_of_mem gain hpi0)
      have h0 := (hvalue pi0 hpi0).1
      linarith
    · have h := csSup_le hne (show ∀ x ∈ gain '' budgetPolicyClass Q ⟨b, hb⟩,
          x ≤ 1 - controlValue Q by
            rintro x ⟨pi, hpi, rfl⟩
            linarith [(hvalue pi hpi).2])
      linarith
  simpa [budgetValue, hb, gain, add_comm] using hsup

-- @node: budgetValue_order_lipschitz
/-- The budget value order lipschitz result. Under [the horder premise](hyp:horder), It proves [the stated conclusion](goal). The argument assumes [the two ordered-budget premises](hyp:hb₁,hb₂). -/
lemma budgetValue_order_lipschitz {d : ℕ} (Q : PotentialLaw d)
    {b₁ b₂ : ℝ} (hb₁ : b₁ ∈ Set.Icc (0 : ℝ) 1)
    (hb₂ : b₂ ∈ Set.Icc (0 : ℝ) 1) (horder : b₁ ≤ b₂) :
    0 ≤ budgetValue Q b₂ - budgetValue Q b₁ ∧
      budgetValue Q b₂ - budgetValue Q b₁ ≤ b₂ - b₁ := by
  let p : Fin d → ℝ := poCellMass Q
  let tau : Fin d → ℝ := effect Q
  let gain (pi : Fin d → ℝ) := ∑ j, p j * pi j * tau j
  let cost (pi : Fin d → ℝ) := ∑ j, p j * pi j
  let feasible (b : ℝ) :=
    {pi : Fin d → ℝ | (∀ j, pi j ∈ Set.Icc (0 : ℝ) 1) ∧ cost pi ≤ b}
  have hp (j : Fin d) : 0 ≤ p j := by
    dsimp [p, poCellMass, CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have ht (j : Fin d) : tau j ≤ 1 := by
    have h0 := (poRegression_unit_interval_budget Q 0 j).1
    have h1 := (poRegression_unit_interval_budget Q 1 j).2
    dsimp [tau, effect]
    linarith
  have hzero (b : ℝ) (hb : 0 ≤ b) : (fun _ : Fin d => (0 : ℝ)) ∈ feasible b := by
    constructor
    · intro j; norm_num
    · simp [cost, hb]
  have hne (b : ℝ) (hb : 0 ≤ b) : (gain '' feasible b).Nonempty :=
    ⟨gain (fun _ => 0), _, hzero b hb, rfl⟩
  have hcost_nonneg (pi : Fin d → ℝ) (hpi : ∀ j, pi j ∈ Set.Icc (0 : ℝ) 1) :
      0 ≤ cost pi := by
    dsimp [cost]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hp j) (hpi j).1)
  have hgain_le_cost (pi : Fin d → ℝ)
      (hpi : ∀ j, pi j ∈ Set.Icc (0 : ℝ) 1) : gain pi ≤ cost pi := by
    dsimp [gain, cost]
    apply Finset.sum_le_sum
    intro j _
    have h := mul_nonneg (hp j) (hpi j).1
    nlinarith [mul_le_mul_of_nonneg_left (ht j) h]
  have hbd (b : ℝ) : BddAbove (gain '' feasible b) := by
    refine ⟨b, ?_⟩
    rintro x ⟨pi, hpi, rfl⟩
    exact (hgain_le_cost pi hpi.1).trans hpi.2
  have hmono : sSup (gain '' feasible b₁) ≤ sSup (gain '' feasible b₂) := by
    apply csSup_le (hne b₁ hb₁.1)
    rintro x ⟨pi, hpi, rfl⟩
    apply le_csSup (hbd b₂)
    exact ⟨pi, ⟨hpi.1, hpi.2.trans horder⟩, rfl⟩
  have hupper : sSup (gain '' feasible b₂) ≤
      sSup (gain '' feasible b₁) + (b₂ - b₁) := by
    apply csSup_le (hne b₂ hb₂.1)
    rintro x ⟨pi, hpi, rfl⟩
    by_cases hz : b₂ = 0
    · have hb₁z : b₁ = 0 := by linarith [hb₁.1]
      subst b₁
      subst b₂
      simpa using le_csSup (hbd 0) (show gain pi ∈ gain '' feasible 0 from
        ⟨pi, hpi, rfl⟩)
    · have hb₂pos : 0 < b₂ := lt_of_le_of_ne hb₂.1 (Ne.symm hz)
      let t : ℝ := b₁ / b₂
      have ht0 : 0 ≤ t := div_nonneg hb₁.1 hb₂.1
      have ht1 : t ≤ 1 := (div_le_one hb₂pos).2 horder
      let pi' : Fin d → ℝ := fun j => t * pi j
      have hpi' : pi' ∈ feasible b₁ := by
        constructor
        · intro j
          dsimp [pi']
          constructor
          · exact mul_nonneg ht0 (hpi.1 j).1
          · exact (mul_le_mul_of_nonneg_left (hpi.1 j).2 ht0).trans (by simpa using ht1)
        · have hcost : cost pi' = t * cost pi := by
            dsimp [cost, pi']
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          rw [hcost]
          calc
            _ ≤ t * b₂ := mul_le_mul_of_nonneg_left hpi.2 ht0
            _ = b₁ := by dsimp [t]; field_simp
      have hgain : gain pi' = t * gain pi := by
        dsimp [gain, pi']
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hgain_bound : gain pi ≤ cost pi := hgain_le_cost pi hpi.1
      have hgap : gain pi - gain pi' ≤ b₂ - b₁ := by
        rw [hgain]
        have hfac : 0 ≤ 1 - t := by linarith
        have hmul := mul_le_mul_of_nonneg_left hgain_bound hfac
        have hmul2 := mul_le_mul_of_nonneg_left hpi.2 hfac
        have hid : (1 - t) * b₂ = b₂ - b₁ := by dsimp [t]; field_simp
        nlinarith
      have hsup := le_csSup (hbd b₁) (show gain pi' ∈ gain '' feasible b₁ from
        ⟨pi', hpi', rfl⟩)
      linarith
  have hv (b : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
      budgetValue Q b = controlValue Q + sSup (gain '' feasible b) := by
    simp only [budgetValue, dif_pos hb]
    rfl
  rw [hv b₂ hb₂, hv b₁ hb₁]
  constructor <;> linarith

/-- The mass of treatment arm `a` in a generic four-vector. -/
def armMassFn (a : Fin 2) (u : Cell → ℝ) : ℝ := u (a, 0) + u (a, 1)
  -- @realizes s_a(u)(arm mass)

/-- Total mass of a generic four-vector. -/
def totalMass (u : Cell → ℝ) : ℝ := armMassFn 0 u + armMassFn 1 u
  -- @realizes s(u)(sum of arm masses)

/-- Globally extended arm value. -/
noncomputable def armValue (epsilon : ℝ) (a : Fin 2) (u : Cell → ℝ) : ℝ :=
  totalMass u * u (a, 1) / max (armMassFn a u) (epsilon * totalMass u)
  -- @realizes g_a(u)(extended arm value, zero at zero vector)

/-- Cellwise threshold functional. -/
noncomputable def thresholdFun (epsilon : ℝ) (lambda : Set.Icc (0 : ℝ) 1)
    (u : Cell → ℝ) : ℝ :=
  armValue epsilon 0 u +
    max 0 (armValue epsilon 1 u - armValue epsilon 0 u - lambda.1 * totalMass u)
  -- @realizes f_\lambda(u)(hinge functional) @realizes \lambda(shadow price in [0,1])

/-- Zero extension used by intermediate polynomial calculations at real arguments. -/
noncomputable def thresholdFunReal (epsilon lambda : ℝ) (u : Cell → ℝ) : ℝ :=
  if h : lambda ∈ Set.Icc (0 : ℝ) 1 then thresholdFun epsilon ⟨lambda, h⟩ u else 0

-- @node: def:dual-process
/-- For [d](hyp:d), [epsilon](hyp:epsilon), [P](hyp:P), [lambda](hyp:lambda), the dual process definition specifies [the stated object](goal). -/
noncomputable def dualProcess {d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d) (lambda : Set.Icc (0 : ℝ) 1) : ℝ :=
  ∑ j, thresholdFun epsilon lambda (cellVector P j)
  -- @realizes F_P(\lambda)(sum of observed cell thresholds)

/-- Zero extension of the dual process for real-indexed auxiliary processes. -/
noncomputable def dualProcessReal {d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d) (lambda : ℝ) : ℝ :=
  if h : lambda ∈ Set.Icc (0 : ℝ) 1 then dualProcess epsilon P ⟨lambda, h⟩ else 0

/-- Bounded measurable curve estimators on the stated interval. -/
abbrev CurveEstimator (n d : ℕ) (b0 : ℝ) :=
  {f : (Fin n → Obs d) → (Set.Icc b0 (1 - b0) → ℝ) //
    b0 ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ -- @realizes I(b0 ∈ [0,1/2]; interval [b0,1-b0] ⊆ [0,1])
    Measurable f ∧ ∃ B : ℝ, ∀ z b, |f z b| ≤ B}
  -- @realizes \widehat V^{\mathrm{JF}}(curve-valued estimator carrier)

/-- Causal laws in the stated model class. -/
abbrev ModelLaw (d : ℕ) (epsilon : ℝ) :=
  {Q : PotentialLaw d // CausalModelClass epsilon Q}

/-- Squared supremum curve risk at a single causal law. -/
noncomputable def curveRisk (n : ℕ) {d : ℕ} {epsilon : ℝ} (b0 : ℝ)
    (est : CurveEstimator n d b0) (Q : ModelLaw d epsilon) : ℝ :=
  ∫ z, (⨆ b : Set.Icc b0 (1 - b0),
    (est.1 z b - budgetValue Q.1 b.1) ^ 2) ∂productLaw (observedMarginal Q.1) n

-- @node: def:curve-risk
/-- For [n](hyp:n), [epsilon](hyp:epsilon), the curve minimax risk definition specifies [the stated object](goal). -/
noncomputable def curveMinimaxRisk (n d : ℕ) (epsilon b0 : ℝ) : ℝ :=
  Causalean.Stat.minimaxValueReal (curveRisk n (d := d) (epsilon := epsilon) b0)
  -- @realizes \mathfrak R_{n,d,\epsilon,b_0}^{\mathrm{curve}}(all-procedure squared sup risk)

/-- The logarithmic alphabet scale `log(e d)`. -/
noncomputable def logAlphabet (d : ℕ) : ℝ := Real.log (Real.exp 1 * d)

-- @env: S3
variable (k : ℕ) (i : Fin k) (sigma : Bool)
  -- @realizes k(number of pairs) @realizes i(pair index) @realizes \sigma(pair sign)

/-- A probability simplex represented by real coordinates. -/
abbrev ProbabilitySimplex :=
  Causalean.Stat.Minimax.Multinomial.TwoSampleL1.ProbabilitySimplex
  -- @realizes r(pair masses) @realizes R(first sampling law) @realizes S(second sampling law)

/-- Contrasts on the stated cube. -/
def PairedContrasts (k : ℕ) :=
  {theta : Fin k → ℝ // ∀ i, theta i ∈ Set.Icc (-1 / 8) (1 / 8)}
  -- @realizes \theta(paired contrasts)

/-- Bernoulli atom mass. -/
def bernoulliMass (p : ℝ) (y : Bool) : ℝ := if y then p else 1 - p

/-- Full-data atom mass in the paired construction. -/
noncomputable def pairedFullMass {k : ℕ} (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) (z : FullObs (2 * k)) : ℝ :=
  let pair := (finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm z.1
  let mu0 : ℝ := 1 / 4
  let mu1 : ℝ := 1 / 2 + (if pair.1 = 0 then 1 else -1) * theta.1 pair.2
  if z.2.2.1 = (if z.2.1 then z.2.2.2.2 else z.2.2.2.1) then
    r.1 pair.2 / 4 * bernoulliMass mu0 z.2.2.2.1 * bernoulliMass mu1 z.2.2.2.2
  else 0

/-- The finite masses sum to one. With [the specified inputs and conditions](hyp:k,r,theta), [the stated relationship holds](goal). -/
-- @node: pairedFullMass_sum
lemma pairedFullMass_sum {k : ℕ} (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) :
    ∑ z : FullObs (2 * k), ENNReal.ofReal (pairedFullMass r theta z) = 1 := by
  classical
  have hcell (j : Fin (2 * k)) :
      (∑ a : Bool, ∑ y : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        pairedFullMass r theta (j, a, y, y0, y1)) =
        r.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2 / 2 := by
    simp [pairedFullMass, bernoulliMass]
    ring
  have hm (z : FullObs (2 * k)) : 0 ≤ pairedFullMass r theta z := by
    let i := ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm z.1).2
    have ht := theta.2 i
    have hr := r.2.1 i
    simp only [Set.mem_Icc] at ht
    have hmu : 0 ≤ (1 / 2 : ℝ) +
        (if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm z.1).1 = 0
         then 1 else -1) * theta.1 i ∧
        (1 / 2 : ℝ) +
        (if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm z.1).1 = 0
         then 1 else -1) * theta.1 i ≤ 1 := by
      split_ifs <;> constructor <;> nlinarith [ht.1, ht.2]
    have h0 : 0 ≤ bernoulliMass (1 / 4) z.2.2.2.1 := by
      cases z.2.2.2.1 <;> norm_num [bernoulliMass]
    have h1 : 0 ≤ bernoulliMass
        ((1 / 2 : ℝ) +
          (if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm z.1).1 = 0
           then 1 else -1) * theta.1 i) z.2.2.2.2 := by
      cases z.2.2.2.2 <;> simp only [bernoulliMass, Bool.false_eq_true, ↓reduceIte] <;>
        linarith [hmu.1, hmu.2]
    by_cases hy : z.2.2.1 = (if z.2.1 then z.2.2.2.2 else z.2.2.2.1)
    · simpa [pairedFullMass, hy, i] using
        (mul_nonneg (mul_nonneg (div_nonneg hr (by norm_num)) h0) h1)
    · simp [pairedFullMass, hy]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hm z)]
  have hsum : (∑ z : FullObs (2 * k), pairedFullMass r theta z) = 1 := by
    simp only [Fintype.sum_prod_type, hcell]
    rw [← Equiv.sum_comp (finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k))]
    simp [Fintype.sum_prod_type, ← Finset.sum_div, r.2.2]
  rw [hsum]
  norm_num

/-- For [k](hyp:k), [r](hyp:r), [theta](hyp:theta), the paired law definition specifies [the stated object](goal). -/
noncomputable def pairedLaw {k : ℕ} (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) : PotentialLaw (2 * k) :=
  let Q : CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.PotentialLaw (2 * k) :=
    ⟨PMF.ofFintype (fun z => ENNReal.ofReal (pairedFullMass r theta z))
      (pairedFullMass_sum r theta)⟩
  have hcons : CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.Consistency Q := by
    intro z hz
    simp [CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass,
      pairedFullMass, hz, Q]
  let hcanonical := canonicalObservedOutcome_of_consistency Q hcons
  ⟨Classical.choose hcanonical, Q, Classical.choose_spec hcanonical, hcons⟩
  -- @realizes \mathcal P^{\mathrm{pair}}_{k}(explicit paired causal law)

/-- A completion may couple the two potential outcomes arbitrarily, but their
joint law is independent of treatment conditional on the covariate cell. -/
def PairedCompletion {k : ℕ} (Q : PotentialLaw (2 * k))
    (r : ProbabilitySimplex k) (theta : PairedContrasts k) : Prop :=
  Consistency Q ∧ ConditionalExchangeability Q ∧
    ∀ j : Fin (2 * k),
      let pair := (finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j
      poCellMass Q j = r.1 pair.2 / 2 ∧
      poTreatmentAtom Q j true = poCellMass Q j / 2 ∧
      poCellMass Q j * poRegression Q 0 j = poCellMass Q j * (1 / 4 : ℝ) ∧
      poCellMass Q j * poRegression Q 1 j =
        poCellMass Q j * (1 / 2 + (if pair.1 = 0 then 1 else -1) * theta.1 pair.2)

/-- All admissible causal completions of the paired cell marginals. -/
-- @node: def:paired-family
def pairedFamily (k : ℕ) : Set (PotentialLaw (2 * k)) :=
  {Q | ∃ r : ProbabilitySimplex k, ∃ theta : PairedContrasts k,
    PairedCompletion Q r theta}
  -- @realizes \mathcal P^{\mathrm{pair}}_{k}(all A-independent paired completions)

end CausalSmith.Stat.DiscreteBudgetvalueCurve

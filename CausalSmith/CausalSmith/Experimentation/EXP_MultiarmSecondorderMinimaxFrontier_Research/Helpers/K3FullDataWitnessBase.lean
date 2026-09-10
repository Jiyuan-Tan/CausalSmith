import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.K3Numerics
import Causalean.Experimentation.DesignBased.ProductVariance

/-! Definitions for the exact finite full-data three-arm witness. -/

open scoped BigOperators

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

-- @node: k3FullDataFin3FunEquiv
/-- A three-bit response type is identified with its ordered triple of binary potential outcomes. -/
def k3FullDataFin3FunEquiv (α : Type*) : (Fin 3 → α) ≃ α × α × α where
  toFun f := (f 0, f 1, f 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a, b, c⟩; rfl

-- @node: k3FullDataR1
/-- The three-arm full data r1 property holds. -/
def k3FullDataR1 (A : Assign 3 3) : ℕ :=
  (if A 0 = 0 then 1 else 0) + (if A 1 = 0 then 1 else 0) +
    (if A 2 = 0 then 1 else 0)

-- @node: k3FullDataS1
/-- The three-arm full data s1 property holds. -/
def k3FullDataS1 (A : Assign 3 3) (y : ObservedOutcome 3) : ℤ :=
  (if A 0 = 0 then if y 0 then 1 else -1 else 0) +
    (if A 1 = 0 then if y 1 then 1 else -1 else 0) +
    (if A 2 = 0 then if y 2 then 1 else -1 else 0)

-- @node: k3FullDataSMinus
/-- The three-arm full data sminus property holds. -/
def k3FullDataSMinus (A : Assign 3 3) (y : ObservedOutcome 3) : ℤ :=
  (if A 0 = 0 then 0 else if y 0 then -1 else 1) +
    (if A 1 = 0 then 0 else if y 1 then -1 else 1) +
    (if A 2 = 0 then 0 else if y 2 then -1 else 1)

-- @node: k3FullDataTable
/-- The exact three-arm full-data table assigns the certified rational estimate to every binary response triple. -/
def k3FullDataTable (r : ℕ) (s h : ℤ) : {v : ℤ // -1000 ≤ v ∧ v ≤ 1000} :=
  if r = 0 ∧ s = 0 ∧ h = -3 then ⟨-623, by norm_num⟩ else
  if r = 0 ∧ s = 0 ∧ h = -1 then ⟨-183, by norm_num⟩ else
  if r = 0 ∧ s = 0 ∧ h = 1 then ⟨183, by norm_num⟩ else
  if r = 0 ∧ s = 0 ∧ h = 3 then ⟨623, by norm_num⟩ else
  if r = 1 ∧ s = -1 ∧ h = -2 then ⟨-638, by norm_num⟩ else
  if r = 1 ∧ s = -1 ∧ h = 0 then ⟨-199, by norm_num⟩ else
  if r = 1 ∧ s = -1 ∧ h = 2 then ⟨148, by norm_num⟩ else
  if r = 1 ∧ s = 1 ∧ h = -2 then ⟨-148, by norm_num⟩ else
  if r = 1 ∧ s = 1 ∧ h = 0 then ⟨199, by norm_num⟩ else
  if r = 1 ∧ s = 1 ∧ h = 2 then ⟨638, by norm_num⟩ else
  if r = 2 ∧ s = -2 ∧ h = -1 then ⟨-648, by norm_num⟩ else
  if r = 2 ∧ s = -2 ∧ h = 1 then ⟨-210, by norm_num⟩ else
  if r = 2 ∧ s = 0 ∧ h = -1 then ⟨-167, by norm_num⟩ else
  if r = 2 ∧ s = 0 ∧ h = 1 then ⟨167, by norm_num⟩ else
  if r = 2 ∧ s = 2 ∧ h = -1 then ⟨210, by norm_num⟩ else
  if r = 2 ∧ s = 2 ∧ h = 1 then ⟨648, by norm_num⟩ else
  if r = 3 ∧ s = -3 ∧ h = 0 then ⟨-660, by norm_num⟩ else
  if r = 3 ∧ s = -1 ∧ h = 0 then ⟨-167, by norm_num⟩ else
  if r = 3 ∧ s = 1 ∧ h = 0 then ⟨167, by norm_num⟩ else
  if r = 3 ∧ s = 3 ∧ h = 0 then ⟨660, by norm_num⟩ else ⟨0, by norm_num⟩

-- @node: cDaggerQ_zero
/-- [the c dagger q zero property holds](goal). -/
lemma cDaggerQ_zero : cDaggerQ (0 : Arm 3) = 1 := by rfl

-- @node: cDaggerQ_one
/-- [the c dagger q one property holds](goal). -/
lemma cDaggerQ_one : cDaggerQ (1 : Arm 3) = -(1 / 2) := by
  have h : (1 : Fin 3) = Fin.succ (0 : Fin 2) := Fin.ext (by rfl)
  simp only [cDaggerQ, h, Fin.cases_succ, Fin.cases_zero]
  ring_nf

-- @node: cDaggerQ_two
/-- [the c dagger q two property holds](goal). -/
lemma cDaggerQ_two : cDaggerQ (2 : Arm 3) = -(1 / 2) := by
  have h : (2 : Fin 3) = Fin.succ (1 : Fin 2) := Fin.ext (by rfl)
  have h' : (1 : Fin 2) = Fin.succ (0 : Fin 1) := Fin.ext (by rfl)
  simp only [cDaggerQ, h, h', Fin.cases_succ]
  ring_nf

-- @node: cDagger_apply
/-- [the c dagger evaluation property holds](goal). -/
@[simp] lemma cDagger_apply (a : Arm 3) :
    cDagger a = if a = 0 then 1 else -(1 / 2) := by
  change ((cDaggerQ a : ℚ) : ℝ) = _
  fin_cases a
  · simpa using congrArg (fun q : ℚ ↦ (q : ℝ)) cDaggerQ_zero
  · simpa using congrArg (fun q : ℚ ↦ (q : ℝ)) cDaggerQ_one
  · simpa using congrArg (fun q : ℚ ↦ (q : ℝ)) cDaggerQ_two

-- @node: qStarDesign_cDagger_p
/-- [the q star design c dagger p property holds](goal). -/
@[simp] lemma qStarDesign_cDagger_p (a : Arm 3) :
    (qStarDesign cDagger).p a = if a = 0 then 1 / 2 else 1 / 4 := by
  have hLc : Lc cDagger = 2 := by
    norm_num [Lc, cDagger, cDaggerQ, ratContrastToReal, Fin.sum_univ_succ]
  change |cDagger a| / Lc cDagger = _
  rw [hLc, cDagger_apply]
  by_cases h : a = 0 <;> simp [h] <;> ring

-- @node: k3FullDataTable_scaled_mem
/-- [the three-arm full data table scaled belongs to property holds](goal). -/
lemma k3FullDataTable_scaled_mem (r : ℕ) (s h : ℤ) :
    (((k3FullDataTable r s h).1 : ℝ) / 1000) ∈ Set.Icc (-1) 1 := by
  have hb := (k3FullDataTable r s h).2
  have hlow : (-1000 : ℝ) ≤ ((k3FullDataTable r s h).1 : ℝ) := by
    exact_mod_cast hb.1
  have hupp : ((k3FullDataTable r s h).1 : ℝ) ≤ 1000 := by
    exact_mod_cast hb.2
  constructor
  · norm_num
    linarith
  · norm_num
    linarith

-- @node: clip_cDagger_eq_self
/-- [the observed count satisfies its stated condition](hyp:hx), [the clip c dagger equals self](goal). -/
lemma clip_cDagger_eq_self (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) :
    clip cDagger x = x := by
  have hLc : Lc cDagger = 2 := by
    norm_num [Lc, cDagger, cDaggerQ, ratContrastToReal, Fin.sum_univ_succ]
  unfold clip
  rw [hLc]
  norm_num
  rw [min_eq_right hx.2, max_eq_right hx.1]

-- @node: k3FullDataRule
/-- The three-arm full-data rule clips the certified table value to the natural contrast interval. -/
noncomputable def k3FullDataRule : Estimator 3 3 cDagger := fun A y ↦
  ⟨clip cDagger
      (((k3FullDataTable (k3FullDataR1 A) (k3FullDataS1 A y)
        (k3FullDataSMinus A y)).1 : ℝ) / 1000),
    clip_mem cDagger _⟩

-- @node: k3FullDataRule_coe
/-- [the three-arm full data rule real-valued representation property holds](goal). -/
@[simp] lemma k3FullDataRule_coe (A : Assign 3 3) (y : ObservedOutcome 3) :
    (k3FullDataRule A y : ℝ) =
      ((k3FullDataTable (k3FullDataR1 A) (k3FullDataS1 A y)
        (k3FullDataSMinus A y)).1 : ℝ) / 1000 := by
  simp only [k3FullDataRule]
  exact clip_cDagger_eq_self _ (k3FullDataTable_scaled_mem _ _ _)

-- @node: k3BoundarySchedule
/-- The boundary schedule repeats a fixed three-arm response type across the whole population. -/
def k3BoundarySchedule : Schedule 3 3 := fun i _ ↦ i ≠ 0

-- @node: k3FullDataTargetQ
/-- The three-arm full data target q property holds. -/
def k3FullDataTargetQ (z : Schedule 3 3) : ℚ :=
  ((3 : ℚ)⁻¹) * ∑ i : Fin 3, ∑ a : Fin 3,
    cDaggerQ a * if z i a then 1 else 0

-- @node: k3FullDataAssignmentProbQ
/-- The three-arm full data assignment prob q property holds. -/
def k3FullDataAssignmentProbQ (A : Assign 3 3) : ℚ :=
  ∏ i : Fin 3, if A i = 0 then 1 / 2 else 1 / 4

-- @node: k3FullDataEstimateQ
/-- The three-arm full data estimate q property holds. -/
def k3FullDataEstimateQ (A : Assign 3 3) (z : Schedule 3 3) : ℚ :=
  (k3FullDataTable (k3FullDataR1 A) (k3FullDataS1 A (obsOutcome z A))
    (k3FullDataSMinus A (obsOutcome z A))).1 / 1000

-- @node: k3FullDataRiskQ
/-- The three-arm full data risk q property holds. -/
def k3FullDataRiskQ (z : Schedule 3 3) : ℚ :=
  ∑ A : Assign 3 3,
    k3FullDataAssignmentProbQ A *
      (k3FullDataEstimateQ A z - k3FullDataTargetQ z) ^ 2

-- @node: k3FullDataTargetQ_cast
/-- [the three-arm full data target q real-valued identity property holds](goal). -/
lemma k3FullDataTargetQ_cast (z : Schedule 3 3) :
    tauC cDagger z = (k3FullDataTargetQ z : ℝ) := by
  unfold tauC k3FullDataTargetQ cDagger ratContrastToReal
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : z i a = true <;> simp [h]

-- @node: k3FullDataAssignmentProbQ_cast
/-- [the three-arm full data assignment prob q real-valued identity property holds](goal). -/
lemma k3FullDataAssignmentProbQ_cast (A : Assign 3 3) :
    (Causalean.Experimentation.DesignBased.prodDesign
      (fun _ : Unit 3 ↦ qStarDesign cDagger)).p A =
      (k3FullDataAssignmentProbQ A : ℝ) := by
  rw [Causalean.Experimentation.DesignBased.prodDesign_p]
  unfold k3FullDataAssignmentProbQ
  push_cast
  simp only [qStarDesign_cDagger_p]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : A i = 0 <;> simp [h]

-- @node: k3FullDataEstimateQ_cast
/-- [the three-arm full data estimate q real-valued identity property holds](goal). -/
lemma k3FullDataEstimateQ_cast (A : Assign 3 3) (z : Schedule 3 3) :
    (k3FullDataRule A (obsOutcome z A) : ℝ) =
      (k3FullDataEstimateQ A z : ℝ) := by
  simp [k3FullDataEstimateQ]

-- @node: k3FullDataRiskQ_cast
/-- [the three-arm full data risk q real-valued identity property holds](goal). -/
lemma k3FullDataRiskQ_cast (z : Schedule 3 3) :
    labeledRisk cDagger
      (Causalean.Experimentation.DesignBased.prodDesign
        (fun _ : Unit 3 ↦ qStarDesign cDagger), k3FullDataRule) z =
      (k3FullDataRiskQ z : ℝ) := by
  unfold labeledRisk Causalean.Experimentation.DesignBased.FiniteDesign.mse
    Causalean.Experimentation.DesignBased.FiniteDesign.E k3FullDataRiskQ
  push_cast
  apply Finset.sum_congr rfl
  intro A hA
  rw [k3FullDataAssignmentProbQ_cast, k3FullDataEstimateQ_cast,
    k3FullDataTargetQ_cast]

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

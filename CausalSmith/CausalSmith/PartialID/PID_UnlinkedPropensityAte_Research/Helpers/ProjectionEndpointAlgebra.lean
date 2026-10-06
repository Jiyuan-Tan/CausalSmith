module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ProjectionGeometry

/-! Endpoint algebra for the external projection candidate envelope. -/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

-- @node: projectedArmEndpoint_abs_le_of_cellBounds
/-- Given [the endpoint arrays, arm, endpoint direction, bound, and cellwise endpoint differences](hyp:ε,J,lam,lam',σ,σ',a,upper,L,hcell), this result [bounds the absolute difference of the corresponding projected arm endpoints](goal). -/
lemma projectedArmEndpoint_abs_le_of_cellBounds
    {ε : ℝ} {J : ℕ}
    (lam lam' : ArmCellArray J OutcomeSpace)
    (σ σ' : ArmCellArray J (ScoreSpace ε))
    (a : ArmSpace) (upper : Bool) (L : ℝ)
    (hcell : ∀ r : LabelSpace J,
      |(let q := (lam a r).real Set.univ
        if 0 < q then
          q * ∫ u in (0 : ℝ)..1,
            Causalean.Stat.quantile
              (((lam a r Set.univ)⁻¹ • (lam a r)).map
                (fun y : OutcomeSpace => (y : ℝ))) u *
            Causalean.Stat.quantile
              (((σ a r Set.univ)⁻¹ • (σ a r)).map
                (fun e => (armProb a e)⁻¹)) (if upper then u else 1 - u)
        else 0) -
       (let q := (lam' a r).real Set.univ
        if 0 < q then
          q * ∫ u in (0 : ℝ)..1,
            Causalean.Stat.quantile
              (((lam' a r Set.univ)⁻¹ • (lam' a r)).map
                (fun y : OutcomeSpace => (y : ℝ))) u *
            Causalean.Stat.quantile
              (((σ' a r Set.univ)⁻¹ • (σ' a r)).map
                (fun e => (armProb a e)⁻¹)) (if upper then u else 1 - u)
        else 0)| ≤
      L * (outcomeCDFDistance (lam a r) (lam' a r) +
        scoreCDFDistance (σ a r) (σ' a r))) :
    |projectedArmEndpoint lam σ a upper -
      projectedArmEndpoint lam' σ' a upper| ≤
      L * ((∑ r : LabelSpace J,
        outcomeCDFDistance (lam a r) (lam' a r)) +
        ∑ r : LabelSpace J,
          scoreCDFDistance (σ a r) (σ' a r)) := by
  unfold projectedArmEndpoint
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r : LabelSpace J,
      |(let q := (lam a r).real Set.univ
        if 0 < q then
          q * ∫ u in (0 : ℝ)..1,
            Causalean.Stat.quantile
              (((lam a r Set.univ)⁻¹ • (lam a r)).map
                (fun y : OutcomeSpace => (y : ℝ))) u *
            Causalean.Stat.quantile
              (((σ a r Set.univ)⁻¹ • (σ a r)).map
                (fun e => (armProb a e)⁻¹)) (if upper then u else 1 - u)
        else 0) -
       (let q := (lam' a r).real Set.univ
        if 0 < q then
          q * ∫ u in (0 : ℝ)..1,
            Causalean.Stat.quantile
              (((lam' a r Set.univ)⁻¹ • (lam' a r)).map
                (fun y : OutcomeSpace => (y : ℝ))) u *
            Causalean.Stat.quantile
              (((σ' a r Set.univ)⁻¹ • (σ' a r)).map
                (fun e => (armProb a e)⁻¹)) (if upper then u else 1 - u)
        else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : LabelSpace J,
      L * (outcomeCDFDistance (lam a r) (lam' a r) +
        scoreCDFDistance (σ a r) (σ' a r)) :=
      Finset.sum_le_sum (fun r _ => hcell r)
    _ = _ := by simp only [← Finset.mul_sum, Finset.sum_add_distrib]

-- @node: projectionCandidate_populationDistance_le
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,x,b,lam,σ,hb,htrial,hscore), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionCandidate_populationDistance_le
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m)
    (b : ArmCellArray J OutcomeSpace × ArmCellArray J (ScoreSpace ε))
    (lam : ArmCellArray J OutcomeSpace)
    (σ : ArmCellArray J (ScoreSpace ε))
    (hb : b ∈ projectionCandidates g α x)
    (htrial : ∀ a r,
      outcomeCDFDistance (b.1 a r) (lam a r) ≤
        outcomeCDFDistance (b.1 a r) (empiricalTrialCells x.1 a r) +
          outcomeCDFDistance (empiricalTrialCells x.1 a r) (lam a r))
    (hscore : ∀ a r,
      scoreCDFDistance (b.2 a r) (σ a r) ≤
        scoreCDFDistance (b.2 a r) (empiricalScoreCells g x.2 a r) +
          scoreCDFDistance (empiricalScoreCells g x.2 a r) (σ a r)) :
    (∑ a : ArmSpace, ∑ r : LabelSpace J,
      outcomeCDFDistance (b.1 a r) (lam a r)) +
      (∑ a : ArmSpace, ∑ r : LabelSpace J,
        scoreCDFDistance (b.2 a r) (σ a r)) ≤
      4 * J / (α * Real.sqrt n) +
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          outcomeCDFDistance (empiricalTrialCells x.1 a r) (lam a r)) +
      2 * J * (2 - 2 * ε) / (α * Real.sqrt m) +
        (∑ a : ArmSpace, ∑ r : LabelSpace J,
          scoreCDFDistance (empiricalScoreCells g x.2 a r) (σ a r)) := by
  have hbt := hb.2.2.1
  have hbs := hb.2.2.2
  have ht : (∑ a : ArmSpace, ∑ r : LabelSpace J,
      outcomeCDFDistance (b.1 a r) (lam a r)) ≤
      4 * J / (α * Real.sqrt n) +
        ∑ a : ArmSpace, ∑ r : LabelSpace J,
          outcomeCDFDistance (empiricalTrialCells x.1 a r) (lam a r) := by
    calc
      _ ≤ ∑ a : ArmSpace, ∑ r : LabelSpace J,
          (outcomeCDFDistance (b.1 a r) (empiricalTrialCells x.1 a r) +
            outcomeCDFDistance (empiricalTrialCells x.1 a r) (lam a r)) := by
              apply Finset.sum_le_sum
              intro a _
              apply Finset.sum_le_sum
              intro r _
              exact htrial a r
      _ = (∑ a : ArmSpace, ∑ r : LabelSpace J,
          outcomeCDFDistance (b.1 a r) (empiricalTrialCells x.1 a r)) +
          (∑ a : ArmSpace, ∑ r : LabelSpace J,
            outcomeCDFDistance (empiricalTrialCells x.1 a r) (lam a r)) := by
              simp only [Finset.sum_add_distrib]
      _ ≤ _ := add_le_add hbt le_rfl
  have hs : (∑ a : ArmSpace, ∑ r : LabelSpace J,
      scoreCDFDistance (b.2 a r) (σ a r)) ≤
      2 * J * (2 - 2 * ε) / (α * Real.sqrt m) +
        ∑ a : ArmSpace, ∑ r : LabelSpace J,
          scoreCDFDistance (empiricalScoreCells g x.2 a r) (σ a r) := by
    calc
      _ ≤ ∑ a : ArmSpace, ∑ r : LabelSpace J,
          (scoreCDFDistance (b.2 a r) (empiricalScoreCells g x.2 a r) +
            scoreCDFDistance (empiricalScoreCells g x.2 a r) (σ a r)) := by
              apply Finset.sum_le_sum
              intro a _
              apply Finset.sum_le_sum
              intro r _
              exact hscore a r
      _ = (∑ a : ArmSpace, ∑ r : LabelSpace J,
          scoreCDFDistance (b.2 a r) (empiricalScoreCells g x.2 a r)) +
          (∑ a : ArmSpace, ∑ r : LabelSpace J,
            scoreCDFDistance (empiricalScoreCells g x.2 a r) (σ a r)) := by
              simp only [Finset.sum_add_distrib]
      _ ≤ _ := add_le_add hbs le_rfl
  linarith

-- @node: projectedATEInterval_subset_of_armEndpoint_bounds
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,lam,lam',σ,σ',δ,h), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectedATEInterval_subset_of_armEndpoint_bounds
    {ε : ℝ} {J : ℕ}
    (lam lam' : ArmCellArray J OutcomeSpace)
    (σ σ' : ArmCellArray J (ScoreSpace ε))
    {δ : ℝ}
    (h : ∀ a upper,
      |projectedArmEndpoint lam σ a upper -
        projectedArmEndpoint lam' σ' a upper| ≤ δ) :
    projectedATEInterval lam σ ⊆
      Set.Icc
        ((projectedArmEndpoint lam' σ' true false -
          projectedArmEndpoint lam' σ' false true) - 2 * δ)
        ((projectedArmEndpoint lam' σ' true true -
          projectedArmEndpoint lam' σ' false false) + 2 * δ) := by
  intro z hz
  change projectedArmEndpoint lam σ true false -
      projectedArmEndpoint lam σ false true ≤ z ∧
      z ≤ projectedArmEndpoint lam σ true true -
        projectedArmEndpoint lam σ false false at hz
  have h₁ := (abs_le.mp (h true false))
  have h₂ := (abs_le.mp (h false true))
  have h₃ := (abs_le.mp (h true true))
  have h₄ := (abs_le.mp (h false false))
  change _ ≤ z ∧ z ≤ _
  constructor <;> linarith

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,x,lam,σ,δ,hδ,hLU,hclip,hendpoint), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalProjectionCI_excessLength_le_of_armEndpoint_bounds
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m)
    (lam : ArmCellArray J OutcomeSpace)
    (σ : ArmCellArray J (ScoreSpace ε)) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hLU : projectedArmEndpoint lam σ true false -
        projectedArmEndpoint lam σ false true ≤
      projectedArmEndpoint lam σ true true -
        projectedArmEndpoint lam σ false false)
    (hclip : (sievedProjectionCandidates g α x).Nonempty →
      (Set.Icc (-1 : ℝ) 1 ∩
      closure (convexHull ℝ
        (⋃ b ∈ sievedProjectionCandidates g α x,
          projectedATEInterval b.1 b.2))).Nonempty)
    (hendpoint : ∀ b ∈ sievedProjectionCandidates g α x, ∀ a upper,
      |projectedArmEndpoint b.1 b.2 a upper -
        projectedArmEndpoint lam σ a upper| ≤ δ) :
    ∃ lo hi : ℝ, sievedTotalizedProjectionCI g α x = Set.Icc lo hi ∧
      max 0 ((hi - lo) -
        ((projectedArmEndpoint lam σ true true -
          projectedArmEndpoint lam σ false false) -
         (projectedArmEndpoint lam σ true false -
          projectedArmEndpoint lam σ false true))) ≤ 4 * δ := by
  have hEach : ∀ b ∈ sievedProjectionCandidates g α x,
      projectedATEInterval b.1 b.2 ⊆
        Set.Icc
          ((projectedArmEndpoint lam σ true false -
            projectedArmEndpoint lam σ false true) - 2 * δ)
          ((projectedArmEndpoint lam σ true true -
            projectedArmEndpoint lam σ false false) + 2 * δ) := by
    intro b hb
    exact projectedATEInterval_subset_of_armEndpoint_bounds
      b.1 lam b.2 σ (hendpoint b hb)
  have h := externalProjectionCI_excessLength_le_of_candidate_envelopes
    g α x hLU (by linarith : 0 ≤ 2 * δ) hclip hEach
  obtain ⟨lo, hi, heq, hbound⟩ := h
  refine ⟨lo, hi, heq, ?_⟩
  simpa only [show 2 * (2 * δ) = 4 * δ by ring] using hbound

-- @node: outcomeCDFDistance_nonneg
/-- Given [the stated mathematical inputs and assumptions](hyp:μ,ν), this result [establishes the stated mathematical conclusion](goal). -/
lemma outcomeCDFDistance_nonneg (μ ν : Measure OutcomeSpace) :
    0 ≤ outcomeCDFDistance μ ν := by
  unfold outcomeCDFDistance
  apply add_nonneg (abs_nonneg _)
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t _
  exact abs_nonneg _

-- @node: scoreCDFDistance_nonneg
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,μ,ν), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreCDFDistance_nonneg {ε : ℝ} (hOverlap : Overlap ε)
    (μ ν : Measure (ScoreSpace ε)) :
    0 ≤ scoreCDFDistance μ ν := by
  unfold scoreCDFDistance
  apply add_nonneg (abs_nonneg _)
  apply intervalIntegral.integral_nonneg (by linarith [hOverlap.2])
  intro t _
  exact abs_nonneg _

-- @node: projectedArmEndpoint_abs_le_of_armBounds
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,hOverlap,lam,lam',σ,σ',L,hL,hArm,a,upper), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectedArmEndpoint_abs_le_of_armBounds
    {ε : ℝ} {J : ℕ} (hOverlap : Overlap ε)
    (lam lam' : ArmCellArray J OutcomeSpace)
    (σ σ' : ArmCellArray J (ScoreSpace ε))
    (L : ℝ) (hL : 0 ≤ L)
    (hArm : ∀ a upper,
      |projectedArmEndpoint lam σ a upper -
        projectedArmEndpoint lam' σ' a upper| ≤
        L * ((∑ r : LabelSpace J,
          outcomeCDFDistance (lam a r) (lam' a r)) +
          ∑ r : LabelSpace J,
            scoreCDFDistance (σ a r) (σ' a r)))
    (a : ArmSpace) (upper : Bool) :
    |projectedArmEndpoint lam σ a upper -
      projectedArmEndpoint lam' σ' a upper| ≤
      L * ((∑ a : ArmSpace, ∑ r : LabelSpace J,
        outcomeCDFDistance (lam a r) (lam' a r)) +
        ∑ a : ArmSpace, ∑ r : LabelSpace J,
          scoreCDFDistance (σ a r) (σ' a r)) := by
  have ht (a' : ArmSpace) :
      0 ≤ ∑ r : LabelSpace J,
        outcomeCDFDistance (lam a' r) (lam' a' r) :=
    Finset.sum_nonneg (fun r _ => outcomeCDFDistance_nonneg _ _)
  have hs (a' : ArmSpace) :
      0 ≤ ∑ r : LabelSpace J,
        scoreCDFDistance (σ a' r) (σ' a' r) :=
    Finset.sum_nonneg (fun r _ => scoreCDFDistance_nonneg hOverlap _ _)
  have htAll :
      (∑ r : LabelSpace J,
        outcomeCDFDistance (lam a r) (lam' a r)) ≤
      ∑ a' : ArmSpace, ∑ r : LabelSpace J,
        outcomeCDFDistance (lam a' r) (lam' a' r) := by
    cases a <;> simp only [Fintype.sum_bool] <;> linarith [ht true, ht false]
  have hsAll :
      (∑ r : LabelSpace J,
        scoreCDFDistance (σ a r) (σ' a r)) ≤
      ∑ a' : ArmSpace, ∑ r : LabelSpace J,
        scoreCDFDistance (σ a' r) (σ' a' r) := by
    cases a <;> simp only [Fintype.sum_bool] <;> linarith [hs true, hs false]
  exact (hArm a upper).trans (mul_le_mul_of_nonneg_left
    (add_le_add htAll hsAll) hL)

end CausalSmith.PartialID.UnlinkedPropensityAte

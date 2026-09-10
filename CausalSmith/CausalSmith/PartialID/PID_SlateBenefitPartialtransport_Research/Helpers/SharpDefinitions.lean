import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.TTieFaceCollapse
import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.Transport
import Causalean.PO.ID.Partial.Basic

open scoped BigOperators
open MeasureTheory Set Causalean PO

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

universe uV uVal uOmega uCell

variable {𝒳 : Type uCell} [Fintype 𝒳] [DecidableEq 𝒳] [MeasurableSpace 𝒳]
  [MeasurableSingletonClass 𝒳]
variable {K : ℕ} {P : POSystem.{uV, uVal, uOmega}} [StandardBorelSpace P.Ω]

/-- The latent cell table is the object specified here for the slate-benefit partial-transport construction. -/
abbrev LatentCellTable (K : ℕ) :=
  Bool → Bool → Bool → Bool → Fin K → Fin K → ℝ

/-- The latent table nonnegative condition is the stated property of the slate-benefit partial-transport model. -/
def latentTableNonnegative (T : LatentCellTable K) : Prop :=
  ∀ d0 d1 s0 s1 y0 y1, 0 ≤ T d0 d1 s0 s1 y0 y1

/-- The table survivor coupling is the object specified here for the slate-benefit partial-transport construction. -/
def tableSurvivorCoupling (T : LatentCellTable K) : Coupling K :=
  fun i j => T false true true true i j

/-- The compatible latent cell table condition is the stated property of the slate-benefit partial-transport model. -/
def CompatibleLatentCellTable (c : Capacities 𝒳 K) (x : 𝒳) (dir : Bool)
    (T : LatentCellTable K) : Prop :=
  latentTableNonnegative T ∧
  (∀ d0 d1 s0 s1 y0 y1, d0 = true → d1 = false → T d0 d1 s0 s1 y0 y1 = 0) ∧
  (dir = true → ∀ y0 y1, T false true true false y0 y1 = 0) ∧
  (dir = false → ∀ y0 y1, T false true false true y0 y1 = 0) ∧
  (∀ i, ∑ j, tableSurvivorCoupling T i j ≤ c.lower x i) ∧
  (∀ j, ∑ i, tableSurvivorCoupling T i j ≤ c.upper x j) ∧
  (∑ i, ∑ j, tableSurvivorCoupling T i j = c.mass x)

/-- The full law survivor coupling is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def fullLawSurvivorCoupling (W : FullLawCandidate P 𝒳 K)
    (x : 𝒳) : Coupling K :=
  fun i j => conditionalReal W.system.μ
    {ω | W.slate.Y0 ω = i ∧ W.slate.Y1 ω = j ∧
      W.slate.S0 ω = true ∧ W.slate.S1 ω = true ∧ ω ∈ W.slate.complierEvent}
    (W.slate.xEvent x)

/-- The benefit probability of is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
noncomputable def benefitProbabilityOf (W : FullLawCandidate P 𝒳 K) : ℝ :=
  conditionalReal W.system.μ
    {ω | W.slate.Y0 ω < W.slate.Y1 ω ∧ W.slate.S0 ω = true ∧
      W.slate.S1 ω = true ∧ ω ∈ W.slate.complierEvent}
    {ω | W.slate.S0 ω = true ∧ W.slate.S1 ω = true ∧
      ω ∈ W.slate.complierEvent}

/-- Given [the stated hypotheses](hyp:hValid,hmass), [the branch free polytope equals singleton zero whenever mass equals zero property holds](goal). -/
theorem branchFreePolytope_eq_singleton_zero_of_mass_eq_zero
    (c : Capacities 𝒳 K) (hValid : ValidCapacities c) (x : 𝒳)
    (hmass : c.mass x = 0) : branchFreePolytope c hValid x = {0} := by
  ext γ
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hγ
    change matrixNonnegative γ ∧ (∀ i, rowMass γ i ≤ c.lower x i) ∧
      (∀ j, columnMass γ j ≤ c.upper x j) ∧ totalMass γ = c.mass x at hγ
    funext i j
    have hrowNonneg : ∀ i, 0 ≤ ∑ j, γ i j := fun i =>
      Finset.sum_nonneg fun j _ => hγ.1 i j
    have hrows : ∀ i, (∑ j, γ i j) = 0 := by
      have hsum : (∑ i, ∑ j, γ i j) = 0 := by
        simpa [totalMass, hmass] using hγ.2.2.2
      exact fun i => congrFun
        ((Fintype.sum_eq_zero_iff_of_nonneg hrowNonneg).mp hsum) i
    have hij := congrFun
      ((Fintype.sum_eq_zero_iff_of_nonneg (fun j => hγ.1 i j)).mp (hrows i)) j
    simpa using hij
  · rintro rfl
    change matrixNonnegative (0 : Coupling K) ∧
      (∀ i, rowMass 0 i ≤ c.lower x i) ∧
      (∀ j, columnMass 0 j ≤ c.upper x j) ∧ totalMass 0 = c.mass x
    simp [matrixNonnegative, rowMass, columnMass, totalMass, hValid.1, hValid.2,
      hmass]

private theorem benefitMass_le_strictRow_add_strictColumn {K : ℕ}
    (γ : Coupling K) (hn : matrixNonnegative γ) (t : Fin K) :
    benefitMass γ ≤ (∑ i with i < t, rowMass γ i) +
      (∑ j with t < j, columnMass γ j) := by
  classical
  unfold benefitMass
  calc
    (∑ i, ∑ j with i < j, γ i j) =
        ∑ i, ∑ j, if i < j then γ i j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_filter]
    _ ≤ ∑ i, ∑ j, ((if i < t then γ i j else 0) +
        (if t < j then γ i j else 0)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i < j
      · rw [if_pos hij]
        by_cases hit : i < t
        · rw [if_pos hit]
          exact le_add_of_nonneg_right (by
            by_cases htj : t < j <;> simp [htj, hn i j])
        · have htj : t < j := lt_of_le_of_lt (le_of_not_gt hit) hij
          rw [if_neg hit, if_pos htj, zero_add]
      · rw [if_neg hij]
        by_cases hit : i < t <;> by_cases htj : t < j <;>
          simp [hit, htj, hn i j]
    _ = (∑ i with i < t, ∑ j, γ i j) +
        (∑ j with t < j, ∑ i, γ i j) := by
      simp only [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hit : i < t <;> simp [hit]
      · rw [Finset.sum_comm, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _
        by_cases htj : t < j <;> simp [htj]

private theorem prefixRow_sub_prefixColumn_le_benefitMass {K : ℕ}
    (γ : Coupling K) (hn : matrixNonnegative γ) (t : Fin K) :
    (∑ i with i ≤ t, rowMass γ i) - (∑ j with j ≤ t, columnMass γ j) ≤
      benefitMass γ := by
  classical
  unfold benefitMass
  have hrow : (∑ i with i ≤ t, rowMass γ i) =
      ∑ i, ∑ j, if i ≤ t then γ i j else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hit : i ≤ t <;> simp [hit, rowMass]
  have hcol : (∑ j with j ≤ t, columnMass γ j) =
      ∑ i, ∑ j, if j ≤ t then γ i j else 0 := by
    rw [Finset.sum_filter]
    unfold columnMass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hit : i ≤ t <;> simp [hit]
  calc
    (∑ i with i ≤ t, rowMass γ i) - (∑ j with j ≤ t, columnMass γ j) =
        ∑ i, ∑ j, ((if i ≤ t then γ i j else 0) -
          (if j ≤ t then γ i j else 0)) := by
      rw [hrow, hcol, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, ∑ j, if i < j then γ i j else 0 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hit : i ≤ t
      · by_cases hjt : j ≤ t
        · simp only [hit, hjt, ↓reduceIte, sub_self]
          by_cases hij : i < j <;> simp [hij, hn i j]
        · have hij : i < j := lt_of_le_of_lt hit (lt_of_not_ge hjt)
          simp [hit, hjt, hij]
      · by_cases hjt : j ≤ t
        · simp only [hit, hjt, ↓reduceIte, zero_sub]
          by_cases hij : i < j <;> simp [hij, hn i j]
        · simp only [hit, hjt, ↓reduceIte, sub_zero]
          by_cases hij : i < j <;> simp [hij, hn i j]
    _ = (∑ i, ∑ j with i < j, γ i j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_filter]

private theorem benefitMass_nonneg {K : ℕ} (γ : Coupling K)
    (hn : matrixNonnegative γ) : 0 ≤ benefitMass γ := by
  unfold benefitMass
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn i j

private theorem benefitMass_le_totalMass {K : ℕ} (γ : Coupling K)
    (hn : matrixNonnegative γ) : benefitMass γ ≤ totalMass γ := by
  unfold benefitMass totalMass
  apply Finset.sum_le_sum
  intro i _
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => hn i _)

/-- Given [the stated hypotheses](hyp:hValid,hγ), [the branch free benefit mass is at most upper property holds](goal). -/
theorem branchFree_benefitMass_le_upper
    (c : Capacities 𝒳 K) (hValid : ValidCapacities c) (x : 𝒳)
    {γ : Coupling K} (hγ : γ ∈ branchFreePolytope c hValid x) :
    benefitMass γ ≤ c.benefitUpper x := by
  unfold Capacities.benefitUpper
  apply Finset.le_inf' Finset.univ_nonempty
  intro o _
  cases o with
  | none =>
      change benefitMass γ ≤ c.mass x
      exact (benefitMass_le_totalMass γ hγ.1).trans_eq hγ.2.2.2
  | some t =>
      change benefitMass γ ≤ c.lowerLt x t + c.upperGt x t
      apply (benefitMass_le_strictRow_add_strictColumn γ hγ.1 t).trans
      apply add_le_add
      · unfold Capacities.lowerLt
        exact Finset.sum_le_sum fun i _ => hγ.2.1 i
      · unfold Capacities.upperGt
        exact Finset.sum_le_sum fun j _ => hγ.2.2.1 j

/-- Given [the stated hypotheses](hyp:hValid,hγ), [the branch free lower is at most benefit mass property holds](goal). -/
theorem branchFree_lower_le_benefitMass
    (c : Capacities 𝒳 K) (hValid : ValidCapacities c) (x : 𝒳)
    {γ : Coupling K} (hγ : γ ∈ branchFreePolytope c hValid x) :
    c.benefitLower x ≤ benefitMass γ := by
  unfold Capacities.benefitLower
  apply Finset.sup'_le Finset.univ_nonempty
  intro o _
  cases o with
  | none =>
      change 0 ≤ benefitMass γ
      exact benefitMass_nonneg γ hγ.1
  | some t =>
      change c.lowerLe x t - c.upperLe x t + min (c.gap x) 0 ≤ benefitMass γ
      have hcut := prefixRow_sub_prefixColumn_le_benefitMass γ hγ.1 t
      by_cases hg : c.gap x < 0
      · have hq : c.q1 x ≤ c.q0 x := by
          unfold Capacities.gap at hg
          linarith
        have hcols := branchFree_exact_columns_of_q1_le_q0 c hValid x hq hγ
        have hcolPrefix : (∑ j with j ≤ t, columnMass γ j) = c.upperLe x t := by
          unfold Capacities.upperLe
          exact Finset.sum_congr rfl fun j _ => hcols j
        have hdefnonneg : ∀ i, 0 ≤ c.lower x i - rowMass γ i :=
          fun i => sub_nonneg.mpr (hγ.2.1 i)
        have hpref : (∑ i with i ≤ t, (c.lower x i - rowMass γ i)) ≤
            ∑ i, (c.lower x i - rowMass γ i) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => hdefnonneg _)
        have hprefEq : (∑ i with i ≤ t, (c.lower x i - rowMass γ i)) =
            c.lowerLe x t - ∑ i with i ≤ t, rowMass γ i := by
          unfold Capacities.lowerLe
          rw [Finset.sum_sub_distrib]
        have htotalEq : (∑ i, (c.lower x i - rowMass γ i)) = -c.gap x := by
          rw [Finset.sum_sub_distrib, ← Capacities.q0,
            sum_rowMass_eq_totalMass, hγ.2.2.2]
          rw [Capacities.mass, min_eq_right hq]
          unfold Capacities.gap
          ring
        rw [hprefEq, htotalEq] at hpref
        rw [hcolPrefix] at hcut
        rw [min_eq_left hg.le]
        linarith
      · have hq : c.q0 x ≤ c.q1 x := by
          unfold Capacities.gap at hg
          linarith
        have hrows := branchFree_exact_rows_of_q0_le_q1 c hValid x hq hγ
        have hrowPrefix : (∑ i with i ≤ t, rowMass γ i) = c.lowerLe x t := by
          unfold Capacities.lowerLe
          exact Finset.sum_congr rfl fun i _ => hrows i
        have hcolPrefix : (∑ j with j ≤ t, columnMass γ j) ≤ c.upperLe x t := by
          unfold Capacities.upperLe
          exact Finset.sum_le_sum fun j _ => hγ.2.2.1 j
        rw [hrowPrefix] at hcut
        rw [min_eq_right (le_of_not_gt hg)]
        linarith

/-- The pointwise affine segment between two finite couplings. -/
def couplingSegment (t : ℝ) (γ₀ γ₁ : Coupling K) : Coupling K :=
  fun i j => (1 - t) * γ₀ i j + t * γ₁ i j

/-- Given [the stated hypotheses](hyp:hValid,h₀,h₁,ht0,ht1), [the coupling segment belongs to branch free property holds](goal). -/
theorem couplingSegment_mem_branchFree
    (c : Capacities 𝒳 K) (hValid : ValidCapacities c) (x : 𝒳)
    {γ₀ γ₁ : Coupling K} (h₀ : γ₀ ∈ branchFreePolytope c hValid x)
    (h₁ : γ₁ ∈ branchFreePolytope c hValid x)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    couplingSegment t γ₀ γ₁ ∈ branchFreePolytope c hValid x := by
  change matrixNonnegative _ ∧ (∀ i, rowMass _ i ≤ c.lower x i) ∧
    (∀ j, columnMass _ j ≤ c.upper x j) ∧ totalMass _ = c.mass x
  have hcoef : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  refine ⟨fun i j => add_nonneg (mul_nonneg hcoef (h₀.1 i j))
      (mul_nonneg ht0 (h₁.1 i j)), ?_, ?_, ?_⟩
  · intro i
    simp only [rowMass, couplingSegment, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    calc
      (1 - t) * (∑ j, γ₀ i j) + t * (∑ j, γ₁ i j) ≤
          (1 - t) * c.lower x i + t * c.lower x i :=
        add_le_add (mul_le_mul_of_nonneg_left (h₀.2.1 i) hcoef)
          (mul_le_mul_of_nonneg_left (h₁.2.1 i) ht0)
      _ = c.lower x i := by ring
  · intro j
    simp only [columnMass, couplingSegment, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    calc
      (1 - t) * (∑ i, γ₀ i j) + t * (∑ i, γ₁ i j) ≤
          (1 - t) * c.upper x j + t * c.upper x j :=
        add_le_add (mul_le_mul_of_nonneg_left (h₀.2.2.1 j) hcoef)
          (mul_le_mul_of_nonneg_left (h₁.2.2.1 j) ht0)
      _ = c.upper x j := by ring
  · simp only [totalMass, couplingSegment, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    change (1 - t) * totalMass γ₀ + t * totalMass γ₁ = c.mass x
    rw [h₀.2.2.2, h₁.2.2.2]
    ring

/-- [the benefit mass coupling segment property holds](goal). -/
theorem benefitMass_couplingSegment (t : ℝ) (γ₀ γ₁ : Coupling K) :
    benefitMass (couplingSegment t γ₀ γ₁) =
      (1 - t) * benefitMass γ₀ + t * benefitMass γ₁ := by
  simp only [benefitMass, couplingSegment, Finset.sum_add_distrib,
    ← Finset.mul_sum]

end CausalSmith.PartialID.SlateBenefitPartialTransport

module
public import Causalean.Stat.Coupling.AtomicCdf

/-!
# Cut-monotone transport plans of finite atomic laws

This module selects a no-counterflow transport plan between two finite atomic laws by minimizing
a quadratic displacement objective over the finite transport polytope.  It proves that such a
cut-monotone plan exists and that its transport cost equals the integrated absolute CDF gap.
-/

@[expose] public section

namespace Causalean.Stat.Coupling

open MeasureTheory Set
open scoped BigOperators ENNReal Interval

namespace AtomicLaw

/-- The quadratic displacement objective of a finite transport plan: the sum over slot pairs of
the transported mass times the squared distance between the two atoms.  It is used only to select
a no-counterflow plan from the finite transport polytope. -/
def transportSqCost {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν) : ℝ :=
  ∑ i, ∑ j, π.mass i j * (μ.atom i - ν.atom j) ^ 2

/-- Among all transport plans between two valid finite atomic laws, one minimizes the quadratic
displacement objective. -/
theorem exists_transportPlan_minimizing_sqCost
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid) :
    ∃ π : TransportPlan μ ν, ∀ q : TransportPlan μ ν,
      transportSqCost π ≤ transportSqCost q := by
  /- Reuse the compact finite transport polytope argument from `exists_optimalTransportPlan`,
  replacing absolute displacement by the continuous quadratic objective. -/
  classical
  let S : Set (ι → κ → ℝ) := {m |
    (∀ i j, 0 ≤ m i j) ∧
    (∀ i, ∑ j, m i j = μ.weight i) ∧
    ∀ j, ∑ i, m i j = ν.weight j}
  have hSne : S.Nonempty := by
    refine ⟨fun i j => μ.weight i * ν.weight j, ?_⟩
    refine ⟨fun i j => mul_nonneg (hμ.1 i) (hν.1 j), ?_, ?_⟩
    · intro i
      rw [← Finset.mul_sum, hν.2, mul_one]
    · intro j
      rw [← Finset.sum_mul, hμ.2, one_mul]
  have hweight_le_one (i : ι) : μ.weight i ≤ 1 := by
    rw [← hμ.2]
    exact Finset.single_le_sum (fun j _ => hμ.1 j) (Finset.mem_univ i)
  have hSsub : S ⊆ Set.Icc (fun _ _ => 0) (fun _ _ => 1) := by
    intro m hm
    refine ⟨fun i j => hm.1 i j, fun i j => ?_⟩
    calc
      m i j ≤ ∑ r, m i r :=
        Finset.single_le_sum (fun r _ => hm.1 i r) (Finset.mem_univ j)
      _ = μ.weight i := hm.2.1 i
      _ ≤ 1 := hweight_le_one i
  have hSclosed : IsClosed S := by
    dsimp [S]
    simp only [Set.setOf_and]
    apply IsClosed.inter
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun i => isClosed_iInter fun j =>
          isClosed_le
            (continuous_const : Continuous (fun _ : ι → κ → ℝ => (0 : ℝ)))
            (by fun_prop : Continuous (fun m : ι → κ → ℝ => m i j)))
    apply IsClosed.inter
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun i => isClosed_eq
          (by fun_prop : Continuous (fun m : ι → κ → ℝ => ∑ j, m i j))
          (by fun_prop : Continuous (fun _ : ι → κ → ℝ => μ.weight i)))
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun j => isClosed_eq
          (by fun_prop : Continuous (fun m : ι → κ → ℝ => ∑ i, m i j))
          (by fun_prop : Continuous (fun _ : ι → κ → ℝ => ν.weight j)))
  have hScompact : IsCompact S :=
    IsCompact.of_isClosed_subset isCompact_Icc hSclosed hSsub
  let cost : (ι → κ → ℝ) → ℝ := fun m =>
    ∑ i, ∑ j, m i j * (μ.atom i - ν.atom j) ^ 2
  have hcost_cont : Continuous cost := by
    unfold cost
    fun_prop
  obtain ⟨m, hmS, hmmin⟩ := hScompact.exists_isMinOn hSne hcost_cont.continuousOn
  let π : TransportPlan μ ν :=
    { mass := m
      nonneg := hmS.1
      fst_marginal := hmS.2.1
      snd_marginal := hmS.2.2 }
  refine ⟨π, fun q => ?_⟩
  simpa [cost, transportSqCost, π] using
    hmmin ⟨q.nonneg, q.fst_marginal, q.snd_marginal⟩

/-- A quadratic-cost-minimizing finite transport plan cannot send positive mass in opposite
directions across the same real cut. -/
theorem cutMonotone_of_sqCost_minimal
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν)
    (hmin : ∀ q : TransportPlan μ ν, transportSqCost π ≤ transportSqCost q) :
    CutMonotone π := by
  /- If positive entries `(i,j)` and `(k,l)` cross a cut in opposite directions, move their
  common minimum mass from `(i,j),(k,l)` to `(i,l),(k,j)`.  Marginals and nonnegativity are
  preserved, while the quadratic objective falls by
  `2 * ε * (μ.atom k - μ.atom i) * (ν.atom j - ν.atom l) > 0`. -/
  classical
  intro x
  by_contra hcounter
  rw [not_or] at hcounter
  let right : ℝ :=
    ∑ i, ∑ j, if μ.atom i ≤ x ∧ x < ν.atom j then π.mass i j else 0
  let left : ℝ :=
    ∑ i, ∑ j, if ν.atom j ≤ x ∧ x < μ.atom i then π.mass i j else 0
  have hright_nonneg : 0 ≤ right := by
    dsimp [right]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact π.nonneg i j
      · exact le_rfl
  have hleft_nonneg : 0 ≤ left := by
    dsimp [left]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact π.nonneg i j
      · exact le_rfl
  have hright_ne : right ≠ 0 := by
    simpa [right] using hcounter.1
  have hleft_ne : left ≠ 0 := by
    simpa [left] using hcounter.2
  have hright_pos : 0 < right := lt_of_le_of_ne hright_nonneg (Ne.symm hright_ne)
  have hleft_pos : 0 < left := lt_of_le_of_ne hleft_nonneg (Ne.symm hleft_ne)
  obtain ⟨i, hi, hi_pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg fun j _ => by
        split_ifs
        · exact π.nonneg i j
        · exact le_rfl)).mp hright_pos
  obtain ⟨j, hj, hij_pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun j _ => by
      split_ifs
      · exact π.nonneg i j
      · exact le_rfl)).mp hi_pos
  have hij_cut : μ.atom i ≤ x ∧ x < ν.atom j := by
    by_contra hij
    simp [hij] at hij_pos
  have hij_mass : 0 < π.mass i j := by
    simpa [hij_cut] using hij_pos
  obtain ⟨k, hk, hk_pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun k _ =>
      Finset.sum_nonneg fun l _ => by
        split_ifs
        · exact π.nonneg k l
        · exact le_rfl)).mp hleft_pos
  obtain ⟨l, hl, hkl_pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun l _ => by
      split_ifs
      · exact π.nonneg k l
      · exact le_rfl)).mp hk_pos
  have hkl_cut : ν.atom l ≤ x ∧ x < μ.atom k := by
    by_contra hkl
    simp [hkl] at hkl_pos
  have hkl_mass : 0 < π.mass k l := by
    simpa [hkl_cut] using hkl_pos
  have hsource : μ.atom i < μ.atom k := lt_of_le_of_lt hij_cut.1 hkl_cut.2
  have htarget : ν.atom l < ν.atom j := lt_of_le_of_lt hkl_cut.1 hij_cut.2
  have hik : i ≠ k := by
    intro hik
    subst k
    exact (lt_irrefl _ hsource)
  have hjl : j ≠ l := by
    intro hjl
    subst l
    exact (lt_irrefl _ htarget)
  let ε : ℝ := min (π.mass i j) (π.mass k l)
  have hε_pos : 0 < ε := by
    exact lt_min hij_mass hkl_mass
  have hε_ij : ε ≤ π.mass i j := min_le_left _ _
  have hε_kl : ε ≤ π.mass k l := min_le_right _ _
  let q : TransportPlan μ ν :=
    { mass := fun a b =>
        π.mass a b
          - (if a = i ∧ b = j then ε else 0)
          - (if a = k ∧ b = l then ε else 0)
          + (if a = i ∧ b = l then ε else 0)
          + (if a = k ∧ b = j then ε else 0)
      nonneg := by
        intro a b
        by_cases hai : a = i <;> by_cases hak : a = k <;>
          by_cases hbj : b = j <;> by_cases hbl : b = l <;>
          simp_all [sub_nonneg.mpr hε_ij, sub_nonneg.mpr hε_kl,
            π.nonneg] <;>
          exact add_nonneg (π.nonneg _ _) (le_of_lt hε_pos)
      fst_marginal := by
        intro a
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        by_cases hai : a = i
        · subst a
          simp [π.fst_marginal, hik]
        · by_cases hak : a = k
          · subst a
            simp [π.fst_marginal, hai, Ne.symm hik]
          · simp [π.fst_marginal, hai, hak]
      snd_marginal := by
        intro b
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        by_cases hbj : b = j
        · subst b
          simp [π.snd_marginal, hjl]
        · by_cases hbl : b = l
          · subst b
            simp [π.snd_marginal, hbj, Ne.symm hjl]
          · simp [π.snd_marginal, hbj, hbl] }
  have hsum_single (a : ι) (b : κ) (f : ι → κ → ℝ) :
      (∑ u, ∑ v, if u = a ∧ v = b then f u v else 0) = f a b := by
    calc
      _ = ∑ v, if a = a ∧ v = b then f a v else 0 := by
        apply Finset.sum_eq_single a
        · intro u hu hua
          simp [hua]
        · simp
      _ = f a b := by simp
  have hcost : transportSqCost q = transportSqCost π -
      2 * ε * (μ.atom k - μ.atom i) * (ν.atom j - ν.atom l) := by
    unfold transportSqCost
    dsimp [q]
    simp only [sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp [hik, hjl, hsum_single]
    ring
  have hdecrease : 0 < 2 * ε * (μ.atom k - μ.atom i) * (ν.atom j - ν.atom l) := by
    positivity
  have hstrict : transportSqCost q < transportSqCost π := by
    rw [hcost]
    linarith
  exact (not_lt_of_ge (hmin q)) hstrict

/-- Any two valid finite atomic laws have a transport plan with no simultaneous flow in opposite
directions across any cut. -/
theorem exists_cutMonotone_transportPlan
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid) :
    ∃ π : TransportPlan μ ν, CutMonotone π := by
  obtain ⟨π, hπ⟩ := exists_transportPlan_minimizing_sqCost μ ν hμ hν
  exact ⟨π, cutMonotone_of_sqCost_minimal π hπ⟩

/-- A no-counterflow transport plan attains the integrated absolute CDF gap. -/
theorem transportCost_eq_integral_abs_cdfGap_of_cutMonotone
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν)
    (hπ : CutMonotone π) :
    transportCost π = ∫ x, |cdfGap μ ν x| := by
  /- At each cut, `CutMonotone` turns the absolute signed crossing mass into the unsigned
  crossing envelope.  Integrate and use `integral_crossingEnvelope_eq_transportCost`. -/
  classical
  rw [← integral_crossingEnvelope_eq_transportCost π]
  apply integral_congr_ae
  filter_upwards with x
  let right : ℝ :=
    ∑ i, ∑ j, if μ.atom i ≤ x ∧ x < ν.atom j then π.mass i j else 0
  let left : ℝ :=
    ∑ i, ∑ j, if ν.atom j ≤ x ∧ x < μ.atom i then π.mass i j else 0
  have hright : 0 ≤ right := by
    dsimp [right]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact π.nonneg i j
      · exact le_rfl
  have hleft : 0 ≤ left := by
    dsimp [left]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact π.nonneg i j
      · exact le_rfl
  have hsigned : signedCrossing π x = right - left := by
    unfold signedCrossing
    dsimp [right, left]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hr : μ.atom i ≤ x ∧ x < ν.atom j
    · have hl : ¬(ν.atom j ≤ x ∧ x < μ.atom i) := by
        rintro ⟨hjx, hxi⟩
        exact (not_lt_of_ge hjx) hr.2
      simp [hr, hl]
    · by_cases hl : ν.atom j ≤ x ∧ x < μ.atom i
      · simp [hr, hl]
      · simp [hr, hl]
  have henvelope : crossingEnvelope π x = right + left := by
    unfold crossingEnvelope
    dsimp [right, left]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hr : μ.atom i ≤ x ∧ x < ν.atom j
    · have hl : ¬(ν.atom j ≤ x ∧ x < μ.atom i) := by
        rintro ⟨hjx, hxi⟩
        exact (not_lt_of_ge hjx) hr.2
      simp [hr, hl]
    · by_cases hl : ν.atom j ≤ x ∧ x < μ.atom i
      · simp [hr, hl]
      · simp [hr, hl]
  rw [cdfGap_eq_signedCrossing π x, hsigned, henvelope]
  rcases hπ x with hright_zero | hleft_zero
  · change right = 0 at hright_zero
    rw [hright_zero, zero_sub, abs_neg, abs_of_nonneg hleft, zero_add]
  · change left = 0 at hleft_zero
    rw [hleft_zero, sub_zero, abs_of_nonneg hright, add_zero]

/-- [Two finite atomic laws with finite slot types](hyp:ι,κ,μ,ν) and [nonnegative unit-mass weights](hyp:hμ,hν) have [a transport plan whose absolute-distance cost equals their integrated absolute CDF gap, the Lebesgue integral over the real line of the absolute difference of the two cumulative distribution functions](goal). -/
theorem exists_transportPlan_cost_eq_integral_abs_cdfGap
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid) :
    ∃ π : TransportPlan μ ν, transportCost π = ∫ x, |cdfGap μ ν x| := by
  obtain ⟨π, hπ⟩ := exists_cutMonotone_transportPlan μ ν hμ hν
  exact ⟨π, transportCost_eq_integral_abs_cdfGap_of_cutMonotone π hπ⟩

end AtomicLaw

end Causalean.Stat.Coupling

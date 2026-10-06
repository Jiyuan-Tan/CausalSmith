module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.IntervalConcentration
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.IntervalScales

/-! The activated full-data target is the rare-cell reciprocal sum used in
 equations (7)--(8) of the connected-interval lower bound. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:d,J,hJ,f), [the stated mathematical conclusion holds](goal). -/
-- @node: activation_sum_initial_cells
lemma activation_sum_initial_cells (d J : ℕ) (hJ : J ≤ d) (f : Fin d → ℝ) :
    (∑ x : Fin d, if x.val < J then f x else 0) =
      ∑ x : Fin J, f (x.castLE hJ) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun x _ => x.castLE hJ)
  · intro x hx
    simp [x.isLt]
  · intro x hx y hy hxy
    apply Fin.ext
    exact congrArg (fun t : Fin d => t.val) hxy
  · intro y hy
    have hyl : y.val < J := (Finset.mem_filter.mp hy).2
    exact ⟨⟨y.val, hyl⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro x hx
    rfl

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hd), [the stated mathematical conclusion holds](goal). -/
-- @node: baselineMass_sum
lemma baselineMass_sum (η : ℝ) (n d : ℕ) (q : ℝ) (hd : 1 ≤ d) :
    (∑ x : Fin d, baselineMass η n d q x) = 1 := by
  classical
  have hJ : rareCount η n d q < d := by
    have h := min_le_left (d - 1) (Nat.floor ((2 * rareMass η n q)⁻¹))
    change rareCount η n d q ≤ d - 1 at h
    omega
  let reservoir : Fin d := ⟨rareCount η n d q, hJ⟩
  have hsplit (x : Fin d) : baselineMass η n d q x =
      (if x.val < rareCount η n d q then rareMass η n q else 0) +
        (if x = reservoir then 1 - rareCount η n d q * rareMass η n q else 0) := by
    have heq : x = reservoir ↔ x.val = rareCount η n d q := by
      simp [reservoir, Fin.ext_iff]
    by_cases hl : x.val < rareCount η n d q
    · have hn : x.val ≠ rareCount η n d q := by omega
      simp [baselineMass, hl, heq, hn]
    · simp [baselineMass, hl, heq]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, activation_sum_initial_cells d _ (Nat.le_of_lt hJ)]
  simp

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hb,x), [the stated mathematical conclusion holds](goal). -/
-- @node: baselineMass_nonneg
lemma baselineMass_nonneg (η : ℝ) (n d : ℕ) (q : ℝ)
    (hb : 0 < rareMass η n q) (x : Fin d) :
    0 ≤ baselineMass η n d q x := by
  have hmass := rareCount_mass_le_half η n d q hb
  unfold baselineMass
  split_ifs <;> linarith

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,hb,hq,hslice,hz,x,y,arrival), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedLaw_weight_nonneg
lemma activatedLaw_weight_nonneg (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q)
    (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q))
    (x : Fin d) (y arrival : Bool) :
    0 ≤ baselineMass η n d q x / 2 *
      bernWeight (if x.val < rareCount η n d q then (z x)⁻¹ else 0) y *
      bernWeight (q * lowerCellZ η n d q z x) arrival := by
  have hH : 0 ≤ lowerEndpoint n q := by unfold lowerEndpoint; positivity
  have hcell : 0 ≤ lowerCellZ η n d q z x ∧
      lowerCellZ η n d q z x ≤ lowerEndpoint n q := by
    unfold lowerCellZ
    split_ifs <;> constructor <;> linarith [(hz x).1, (hz x).2]
  have hprob : 0 ≤ q * lowerCellZ η n d q z x ∧
      q * lowerCellZ η n d q z x ≤ 1 :=
    ⟨mul_nonneg hq.le hcell.1,
      (mul_le_mul_of_nonneg_left hcell.2 hq.le).trans
        (lower_activation_probability_le_one n q hq.le hslice)⟩
  have hy : 0 ≤ (if x.val < rareCount η n d q then (z x)⁻¹ else 0) ∧
      (if x.val < rareCount η n d q then (z x)⁻¹ else 0) ≤ 1 := by
    split_ifs
    · exact ⟨inv_nonneg.mpr (by linarith [(hz x).1]),
        inv_le_one_of_one_le₀ (hz x).1⟩
    · norm_num
  have hbern (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (v : Bool) :
      0 ≤ bernWeight p v := by
    cases v <;> simp [bernWeight] <;> linarith [hp.1, hp.2]
  exact mul_nonneg
    (mul_nonneg (div_nonneg (baselineMass_nonneg η n d q hb x) (by norm_num))
      (hbern _ hy y)) (hbern _ hprob arrival)

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,hb,hq,hslice,hz), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedLaw_target_integral
lemma activatedLaw_target_integral (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q)
    (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q)) :
    (∫ r : FullRecord d,
      ((if r.Y1 then (1 : ℝ) else 0) - (if r.Y0 then (1 : ℝ) else 0))
        ∂activatedLaw η n d q z hz) =
      rareMass η n q * ∑ x : Fin d,
        if x.val < rareCount η n d q then (z x)⁻¹ else 0 := by
  let f : FullRecord d → ℝ := fun r =>
    (if r.Y1 then 1 else 0) - (if r.Y0 then 1 else 0)
  let μ (x : Fin d) (a y arrival : Bool) : Measure (FullRecord d) :=
    ENNReal.ofReal (baselineMass η n d q x / 2 *
      bernWeight (if x.val < rareCount η n d q then (z x)⁻¹ else 0) y *
      bernWeight (q * lowerCellZ η n d q z x) arrival) •
      Measure.dirac (lowerFullRecord x a y arrival)
  have hInt (x : Fin d) (a y arrival : Bool) : Integrable f (μ x a y arrival) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hIntY (x : Fin d) (a y : Bool) :
      Integrable f (∑ arrival, μ x a y arrival) :=
    integrable_finsetSum_measure.mpr (fun arrival _ => hInt x a y arrival)
  have hIntA (x : Fin d) (a : Bool) :
      Integrable f (∑ y, ∑ arrival, μ x a y arrival) :=
    integrable_finsetSum_measure.mpr (fun y _ => hIntY x a y)
  have hIntX (x : Fin d) :
      Integrable f (∑ a, ∑ y, ∑ arrival, μ x a y arrival) :=
    integrable_finsetSum_measure.mpr (fun a _ => hIntA x a)
  change (∫ r, f r ∂(∑ x, ∑ a, ∑ y, ∑ arrival, μ x a y arrival)) = _
  rw [integral_finsetSum_measure (fun x _ => hIntX x)]
  simp_rw [integral_finsetSum_measure (fun a _ => hIntA _ a),
    integral_finsetSum_measure (fun y _ => hIntY _ _ y),
    integral_finsetSum_measure (fun arrival _ => hInt _ _ _ arrival)]
  simp only [μ, integral_smul_measure, integral_dirac, smul_eq_mul]
  simp_rw [ENNReal.toReal_ofReal (activatedLaw_weight_nonneg η n d q z hb hq hslice hz _ _ _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hr : x.val < rareCount η n d q
  · simp [f, lowerFullRecord, bernWeight, hr, baselineMass]
    ring
  · simp [f, lowerFullRecord, bernWeight, hr]

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,hd,hb,hq,hslice,hz), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedLaw_univ
lemma activatedLaw_univ (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (hd : 1 ≤ d) (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q)
    (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q)) :
    activatedLaw η n d q z hz Set.univ = 1 := by
  classical
  let w (x : Fin d) (y arrival : Bool) : ℝ :=
    baselineMass η n d q x / 2 *
      bernWeight (if x.val < rareCount η n d q then (z x)⁻¹ else 0) y *
      bernWeight (q * lowerCellZ η n d q z x) arrival
  have hw (x : Fin d) (y arrival : Bool) : 0 ≤ w x y arrival :=
    activatedLaw_weight_nonneg η n d q z hb hq hslice hz x y arrival
  have hcell (x : Fin d) :
      (∑ y : Bool, ∑ arrival : Bool, ENNReal.ofReal (w x y arrival)) =
        ENNReal.ofReal (baselineMass η n d q x / 2) := by
    simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun arrival _ => hw x _ arrival)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ =>
      Finset.sum_nonneg (fun arrival _ => hw x y arrival))]
    congr 1
    by_cases hr : x.val < rareCount η n d q <;>
      simp [w, bernWeight, hr] <;> ring
  simp only [activatedLaw, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  change (∑ x : Fin d, ∑ _a : Bool, ∑ y : Bool, ∑ arrival : Bool,
    ENNReal.ofReal (w x y arrival)) = 1
  simp_rw [hcell]
  have harm (x : Fin d) :
      (∑ _a : Bool, ENNReal.ofReal (baselineMass η n d q x / 2)) =
        ENNReal.ofReal (baselineMass η n d q x) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
      div_nonneg (baselineMass_nonneg η n d q hb x) (by norm_num))]
    congr 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  simp_rw [harm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => baselineMass_nonneg η n d q hb x),
    baselineMass_sum η n d q hd]
  norm_num

/-- For [the specified inputs and assumptions](hyp:η,n,d,q,z,hd,hb,hq,hslice,hz), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: activatedFullLaw
noncomputable def activatedFullLaw (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (hd : 1 ≤ d) (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q)
    (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q)) : FullLaw d :=
  ⟨activatedLaw η n d q z hz,
    ⟨activatedLaw_univ η n d q z hd hb hq hslice hz⟩⟩

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,z,hd,hb,hq,hslice,hz), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedFullLaw_ate
lemma activatedFullLaw_ate (η : ℝ) (n d : ℕ) (q : ℝ)
    (z : Fin d → ℝ) (hd : 1 ≤ d) (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q)
    (hz : ∀ x, z x ∈ Icc (1 : ℝ) (lowerEndpoint n q)) :
    ate (activatedFullLaw η n d q z hd hb hq hslice hz) =
      intervalPriorTarget (rareCount η n d q) (rareMass η n q)
        (fun x => z (x.castLE (show rareCount η n d q ≤ d from
          (min_le_left _ _).trans (Nat.sub_le d 1)))) := by
  change (∫ r : FullRecord d,
      ((if r.Y1 then (1 : ℝ) else 0) - (if r.Y0 then (1 : ℝ) else 0))
        ∂activatedLaw η n d q z hz) = _
  rw [activatedLaw_target_integral η n d q z hb hq hslice hz,
    activation_sum_initial_cells d (rareCount η n d q) (show rareCount η n d q ≤ d from
          (min_le_left _ _).trans (Nat.sub_le d 1)) (fun x => (z x)⁻¹)]
  rfl

end CausalSmith.Stat.MarRareqLogfrontier

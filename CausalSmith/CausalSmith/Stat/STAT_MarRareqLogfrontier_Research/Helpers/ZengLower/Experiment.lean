module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.MomentCertificate

/-! Finite zero-control observational laws for the cited fixed-positivity experiment. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- For [the specified inputs and assumptions](hyp:p,b), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def zengBernWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- For [the specified inputs and assumptions](hyp:d,p,π,μ), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def zengFiniteTable (d : ℕ) (p π μ : Fin d → ℝ) :
    Measure (ZengRecord d) :=
  ∑ x : Fin d, ∑ b : Bool, ∑ y : Bool,
    ENNReal.ofReal (p x * zengBernWeight (π x) b *
      (if b then zengBernWeight (μ x) y else if y then 0 else 1)) •
        Measure.dirac (x, b, y)

private lemma sum_bool (f : Bool → ℝ≥0∞) :
    ∑ b : Bool, f b = f false + f true := by
  rw [show (Finset.univ : Finset Bool) = {false, true} by decide]
  simp

private lemma zeng_cell_mass (q a m : ℝ) (hq : 0 ≤ q)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hm : 0 ≤ m) (hm' : m ≤ 1) :
    ∑ b : Bool, ∑ y : Bool,
      ENNReal.ofReal (q * zengBernWeight a b *
        (if b then zengBernWeight m y else if y then 0 else 1)) =
      ENNReal.ofReal q := by
  rw [sum_bool]
  simp_rw [sum_bool]
  change
    (ENNReal.ofReal (q * (1 - a) * 1) + ENNReal.ofReal (q * (1 - a) * 0)) +
      (ENNReal.ofReal (q * a * (1 - m)) + ENNReal.ofReal (q * a * m)) =
        ENNReal.ofReal q
  simp only [mul_zero, mul_one, ENNReal.ofReal_zero, add_zero]
  rw [← ENNReal.ofReal_add
    (mul_nonneg (mul_nonneg hq ha) (sub_nonneg.mpr hm'))
    (mul_nonneg (mul_nonneg hq ha) hm)]
  rw [← ENNReal.ofReal_add
    (mul_nonneg hq (sub_nonneg.mpr ha'))
    (add_nonneg
      (mul_nonneg (mul_nonneg hq ha) (sub_nonneg.mpr hm'))
      (mul_nonneg (mul_nonneg hq ha) hm))]
  congr 1
  ring

private lemma zeng_cell_mass_of_conditional (q a m : ℝ) (hq : 0 ≤ q)
    (ha : 0 < q → 0 ≤ a ∧ a ≤ 1) (hm : 0 ≤ m) (hm' : m ≤ 1) :
    ∑ b : Bool, ∑ y : Bool,
      ENNReal.ofReal (q * zengBernWeight a b *
        (if b then zengBernWeight m y else if y then 0 else 1)) =
      ENNReal.ofReal q := by
  rcases hq.eq_or_lt with hq0 | hqpos
  · simp [← hq0]
  · exact zeng_cell_mass q a m hq (ha hqpos).1 (ha hqpos).2 hm hm'

private lemma zengFiniteTable_univ (d : ℕ) (p π μ : Fin d → ℝ)
    (hp : ∀ x, 0 ≤ p x)
    (hπ : ∀ x, 0 < p x → 0 ≤ π x ∧ π x ≤ 1)
    (hμ : ∀ x, 0 ≤ μ x ∧ μ x ≤ 1) :
    zengFiniteTable d p π μ Set.univ = ENNReal.ofReal (∑ x, p x) := by
  calc
    zengFiniteTable d p π μ Set.univ =
        ∑ x, ∑ b, ∑ y, ENNReal.ofReal
          (p x * zengBernWeight (π x) b *
            if b then zengBernWeight (μ x) y else if y then 0 else 1) := by
      simp [zengFiniteTable]
    _ = ∑ x, ENNReal.ofReal (p x) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact zeng_cell_mass_of_conditional (p x) (π x) (μ x) (hp x)
        (hπ x) (hμ x).1 (hμ x).2
    _ = ENNReal.ofReal (∑ x, p x) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      exact fun x hx => hp x

private lemma zengFiniteTable_category_apply (d : ℕ) (p π μ : Fin d → ℝ)
    (x : Fin d) :
    zengFiniteTable d p π μ {r | r.1 = x} =
      ∑ b : Bool, ∑ y : Bool,
        ENNReal.ofReal (p x * zengBernWeight (π x) b *
          (if b then zengBernWeight (μ x) y else if y then 0 else 1)) := by
  simp [zengFiniteTable, Set.indicator]
  rw [Finset.sum_eq_single x]
  · simp
  · intro x' hx' hne
    simp [hne]
  · simp

private lemma zengFiniteTable_arm_apply (d : ℕ) (p π μ : Fin d → ℝ)
    (x : Fin d) (b : Bool) :
    zengFiniteTable d p π μ {r | r.1 = x ∧ r.2.1 = b} =
      ∑ y : Bool, ENNReal.ofReal (p x * zengBernWeight (π x) b *
        (if b then zengBernWeight (μ x) y else if y then 0 else 1)) := by
  simp [zengFiniteTable, Set.indicator]
  rw [Finset.sum_eq_single x]
  · cases b <;> simp
  · intro x' hx' hne
    simp [hne]
  · simp

private lemma zengFiniteTable_outcome_apply (d : ℕ) (p π μ : Fin d → ℝ)
    (x : Fin d) (b y : Bool) :
    zengFiniteTable d p π μ {r | r.1 = x ∧ r.2.1 = b ∧ r.2.2 = y} =
      ENNReal.ofReal (p x * zengBernWeight (π x) b *
        (if b then zengBernWeight (μ x) y else if y then 0 else 1)) := by
  simp [zengFiniteTable, Set.indicator]
  rw [Finset.sum_eq_single x]
  · cases b <;> cases y <;> simp
  · intro x' hx' hne
    simp [hne]
  · simp

private lemma zeng_outcome_mass (q a m : ℝ) (hq : 0 ≤ q)
    (ha : 0 ≤ a) (hm : 0 ≤ m) (hm' : m ≤ 1) (b : Bool) :
    ∑ y : Bool, ENNReal.ofReal (q * zengBernWeight a b *
      (if b then zengBernWeight m y else if y then 0 else 1)) =
      ENNReal.ofReal (q * zengBernWeight a b) := by
  rw [sum_bool]
  cases b
  · simp [zengBernWeight]
  · change ENNReal.ofReal (q * a * (1 - m)) + ENNReal.ofReal (q * a * m) =
      ENNReal.ofReal (q * a)
    rw [← ENNReal.ofReal_add
      (mul_nonneg (mul_nonneg hq ha) (sub_nonneg.mpr hm'))
      (mul_nonneg (mul_nonneg hq ha) hm)]
    congr 1
    ring

private lemma zeng_outcome_mass_of_conditional (q a m : ℝ) (hq : 0 ≤ q)
    (ha : 0 < q → 0 ≤ a) (hm : 0 ≤ m) (hm' : m ≤ 1) (b : Bool) :
    ∑ y : Bool, ENNReal.ofReal (q * zengBernWeight a b *
      (if b then zengBernWeight m y else if y then 0 else 1)) =
      ENNReal.ofReal (q * zengBernWeight a b) := by
  rcases hq.eq_or_lt with hq0 | hqpos
  · simp [← hq0]
  · exact zeng_outcome_mass q a m hq (ha hqpos) hm hm' b

private lemma zengFiniteTable_category_real (d : ℕ) (p π μ : Fin d → ℝ)
    (hp : ∀ x, 0 ≤ p x)
    (hπ : ∀ x, 0 < p x → 0 ≤ π x ∧ π x ≤ 1)
    (hμ : ∀ x, 0 ≤ μ x ∧ μ x ≤ 1) (x : Fin d) :
    (zengFiniteTable d p π μ).real {r | r.1 = x} = p x := by
  rw [Measure.real, zengFiniteTable_category_apply,
    zeng_cell_mass_of_conditional (p x) (π x) (μ x) (hp x) (hπ x)
      (hμ x).1 (hμ x).2]
  exact ENNReal.toReal_ofReal (hp x)

private lemma zengFiniteTable_true_arm_real (d : ℕ) (p π μ : Fin d → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hπ : ∀ x, 0 < p x → 0 ≤ π x)
    (hμ : ∀ x, 0 ≤ μ x ∧ μ x ≤ 1) (x : Fin d) :
    (zengFiniteTable d p π μ).real {r | r.1 = x ∧ r.2.1 = true} =
      p x * π x := by
  rw [Measure.real, zengFiniteTable_arm_apply,
    zeng_outcome_mass_of_conditional (p x) (π x) (μ x) (hp x) (hπ x)
      (hμ x).1 (hμ x).2 true]
  simp only [zengBernWeight]
  apply ENNReal.toReal_ofReal
  rcases (hp x).eq_or_lt with hpx | hpx
  · simp [← hpx]
  · exact mul_nonneg (hp x) (hπ x hpx)

private lemma zengFiniteTable_true_outcome_real (d : ℕ) (p π μ : Fin d → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hπ : ∀ x, 0 < p x → 0 ≤ π x)
    (hμ : ∀ x, 0 ≤ μ x) (x : Fin d) :
    (zengFiniteTable d p π μ).real
      {r | r.1 = x ∧ r.2.1 = true ∧ r.2.2 = true} =
      p x * π x * μ x := by
  rw [Measure.real, zengFiniteTable_outcome_apply]
  simp only [zengBernWeight]
  apply ENNReal.toReal_ofReal
  rcases (hp x).eq_or_lt with hpx | hpx
  · simp [← hpx]
  · exact mul_nonneg (mul_nonneg (hp x) (hπ x hpx)) (hμ x)

private lemma zengFiniteTable_false_outcome_real (d : ℕ) (p π μ : Fin d → ℝ)
    (x : Fin d) :
    (zengFiniteTable d p π μ).real
      {r | r.1 = x ∧ r.2.1 = false ∧ r.2.2 = true} = 0 := by
  rw [Measure.real, zengFiniteTable_outcome_apply]
  simp [zengBernWeight]

/-- Given [the specified inputs and assumptions](hyp:d,ε,hd,hε,p,π,μ,hp,hsum,hπ,hμ), [the stated mathematical conclusion holds](goal). -/
lemma zeng_finiteTable_zero_control (d : ℕ) (ε : ℝ)
    (hd : 1 ≤ d) (hε : 0 < ε ∧ ε < 1 / 2)
    (p π μ : Fin d → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x : Fin d, p x = 1)
    (hπ : ∀ x, 0 < p x → ε ≤ π x ∧ π x ≤ 1 - ε)
    (hμ : ∀ x, 0 ≤ μ x ∧ μ x ≤ 1) :
    ∃ P : ZengLaw d, P.1 = zengFiniteTable d p π μ ∧
      P ∈ zengZeroControlClass d ε ∧
      zengATE P = ∑ x : Fin d, p x * μ x := by
  have hπ01 (x : Fin d) (hx : 0 < p x) : 0 ≤ π x ∧ π x ≤ 1 := by
    constructor
    · exact le_trans (le_of_lt hε.1) (hπ x hx).1
    · exact le_trans (hπ x hx).2 (by linarith [hε.1])
  let M := zengFiniteTable d p π μ
  have hM_univ : M Set.univ = 1 := by
    rw [zengFiniteTable_univ d p π μ hp hπ01 hμ, hsum]
    norm_num
  let P : ZengLaw d := ⟨M, ⟨hM_univ⟩⟩
  have hcat (x : Fin d) : zengCategory P x = p x := by
    exact zengFiniteTable_category_real d p π μ hp hπ01 hμ x
  have harm_true (x : Fin d) : zengArm P x true = p x * π x := by
    exact zengFiniteTable_true_arm_real d p π μ hp
      (fun x hx => (hπ01 x hx).1) hμ x
  have hnum_true (x : Fin d) :
      P.1.real {r | r.1 = x ∧ r.2.1 = true ∧ r.2.2 = true} =
        p x * π x * μ x := by
    exact zengFiniteTable_true_outcome_real d p π μ hp
      (fun x hx => (hπ01 x hx).1) (fun x => (hμ x).1) x
  have hnum_false (x : Fin d) :
      P.1.real {r | r.1 = x ∧ r.2.1 = false ∧ r.2.2 = true} = 0 := by
    exact zengFiniteTable_false_outcome_real d p π μ x
  have hmean_true (x : Fin d) (hx : 0 < zengCategory P x) :
      zengMean P x true hx = μ x := by
    have hpx : 0 < p x := by simpa [hcat x] using hx
    have hπx : 0 < π x := lt_of_lt_of_le hε.1 (hπ x hpx).1
    rw [zengMean, hnum_true x, harm_true x]
    field_simp
  have hmean_false (x : Fin d) (hx : 0 < zengCategory P x) :
      zengMean P x false hx = 0 := by
    simp [zengMean, hnum_false x]
  refine ⟨P, rfl, ?_, ?_⟩
  · constructor
    · refine ⟨hε.1, hε.2, hd, ?_⟩
      intro x hx
      have hpx : 0 < p x := by simpa [hcat x] using hx
      rw [hcat x, harm_true x]
      constructor
      · simpa [mul_comm] using
          (mul_le_mul_of_nonneg_left (hπ x hpx).1 (hp x))
      · simpa [mul_comm] using
          (mul_le_mul_of_nonneg_left (hπ x hpx).2 (hp x))
    · intro x hx
      exact hmean_false x hx
  · unfold zengATE
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hpx : 0 < p x
    · rw [dif_pos (by simpa [hcat x] using hpx)]
      simp only [hmean_true x, hmean_false x, sub_zero]
      rw [hcat x]
    · rw [dif_neg (by simpa [hcat x] using hpx)]
      have hpx0 : p x = 0 := le_antisymm (le_of_not_gt hpx) (hp x)
      simp [hpx0]

end CausalSmith.Stat.MarRareqLogfrontier

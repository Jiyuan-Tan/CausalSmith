import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Legality

/-! # Finite-alphabet query legality -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open Set
open scoped BigOperators

/-- Cellwise propensity caps make the finite `f`-divergence constraint
redundant.  For the specified model objects, [the stated conditions](hyp:hPos,hf,hp,hq,hcap), [the stated mathematical relationship holds](goal).
-/
-- @node: finiteFDiv_le_radius_of_cap
lemma finiteFDiv_le_radius_of_cap {J : Type} [Fintype J]
    (f : ℝ → ℝ) (e : ℝ) (p q : J → ℝ)
    (hPos : StrictPositivity e) (hf : AdmissibleGenerator f)
    (hp : FiniteProbabilityVector p) (hq : FiniteProbabilityVector q)
    (hcap : ∀ j, e * p j ≤ q j) :
    finiteFDiv f p q ≤ divRadius f e := by
  have he0 : e ≠ 0 := ne_of_gt hPos.1
  have hc0 : 0 < 1 / e := one_div_pos.mpr hPos.1
  have hpoint : ∀ j, q j * f (p j / q j) ≤
      q j * f 0 + (p j / (1 / e)) * (f (1 / e) - f 0) := by
    intro j
    have hp0 := (hp.1 j).1
    have hq0 := (hq.1 j).1
    by_cases hqz : q j = 0
    · have hpz : p j = 0 := by
        have : e * p j = 0 := le_antisymm (hqz ▸ hcap j)
          (mul_nonneg hPos.1.le hp0)
        exact (mul_eq_zero.mp this).resolve_left he0
      simp [hqz, hpz]
    · have hqpos : 0 < q j := lt_of_le_of_ne hq0 (Ne.symm hqz)
      have hr0 : 0 ≤ p j / q j := div_nonneg hp0 hq0
      have hrc : p j / q j ≤ 1 / e := by
        apply (div_le_iff₀ hqpos).2
        calc
          p j = (1 / e) * (e * p j) := by field_simp [he0]
          _ ≤ (1 / e) * q j :=
            mul_le_mul_of_nonneg_left (hcap j) hc0.le
      have ha : 0 ≤ 1 - (p j / q j) / (1 / e) := by
        exact sub_nonneg.mpr ((div_le_one hc0).2 hrc)
      have hb : 0 ≤ (p j / q j) / (1 / e) := div_nonneg hr0 hc0.le
      have hab : (1 - (p j / q j) / (1 / e)) +
          (p j / q j) / (1 / e) = 1 := by ring
      have hconv := hf.2.1.2 (show (0 : ℝ) ∈ Set.Ici 0 by simp)
        (show 1 / e ∈ Set.Ici 0 by exact hc0.le) ha hb hab
      have harg : (1 - (p j / q j) / (1 / e)) * 0 +
          ((p j / q j) / (1 / e)) * (1 / e) = p j / q j := by
        field_simp [hqz, he0]
        <;> ring
      have hchord : f (p j / q j) ≤
          (1 - (p j / q j) / (1 / e)) * f 0 +
            ((p j / q j) / (1 / e)) * f (1 / e) := by
        rw [show (1 - (p j / q j) / (1 / e)) • (0 : ℝ) +
            ((p j / q j) / (1 / e)) • (1 / e) = p j / q j by
          simpa only [smul_eq_mul] using harg] at hconv
        simpa only [smul_eq_mul] using hconv
      calc
        q j * f (p j / q j) ≤ q j *
            ((1 - (p j / q j) / (1 / e)) * f 0 +
              ((p j / q j) / (1 / e)) * f (1 / e)) :=
          mul_le_mul_of_nonneg_left hchord hq0
        _ = q j * f 0 + (p j / (1 / e)) * (f (1 / e) - f 0) := by
          field_simp [hqz, he0]
          <;> ring
  rw [finiteFDiv, divRadius]
  calc
    ∑ j, q j * f (p j / q j) ≤
        ∑ j, (q j * f 0 + (p j / (1 / e)) * (f (1 / e) - f 0)) :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ = e * f (1 / e) + (1 - e) * f 0 := by
      rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul]
      rw [← Finset.sum_mul]
      rw [← Finset.sum_div]
      rw [hq.2, hp.2]
      field_simp [he0]
      <;> ring

/-- On a finite alphabet, the cellwise cap is equivalent to a propensity
mixture representation.  For the specified model objects, [the stated conditions](hyp:hPos,hp), [the stated mathematical relationship holds](goal).
-/
-- @node: finiteMixtures_eq_cap
lemma finiteMixtures_eq_cap {J : Type} [Fintype J]
    (e : ℝ) (p : J → ℝ) (hPos : StrictPositivity e)
    (hp : FiniteProbabilityVector p) :
    {q : J → ℝ | FiniteProbabilityVector q ∧ ∃ r : J → ℝ,
      FiniteProbabilityVector r ∧
        ∀ j, q j = e * p j + (1 - e) * r j} =
    {q : J → ℝ | FiniteProbabilityVector q ∧ ∀ j, e * p j ≤ q j} := by
  ext q
  constructor
  · rintro ⟨hq, r, hr, hrepr⟩
    refine ⟨hq, fun j => ?_⟩
    rw [hrepr j]
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hPos.2.le) (hr.1 j).1)
  · rintro ⟨hq, hcap⟩
    let r : J → ℝ := fun j => (q j - e * p j) / (1 - e)
    have hone : 0 < 1 - e := sub_pos.mpr hPos.2
    have hr0 : ∀ j, 0 ≤ r j := fun j =>
      div_nonneg (sub_nonneg.mpr (hcap j)) hone.le
    have hrsum : ∑ j, r j = 1 := by
      dsimp [r]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hq.2, hp.2]
      field_simp [ne_of_gt hone]
    have hr : FiniteProbabilityVector r := by
      constructor
      · intro j
        constructor
        · exact hr0 j
        · rw [← hrsum]
          exact Finset.single_le_sum (fun i _ => hr0 i) (Finset.mem_univ j)
      · exact hrsum
    refine ⟨hq, r, hr, ?_⟩
    intro j
    dsimp [r]
    field_simp [ne_of_gt hone]
    <;> ring

/-- A convex combination of two finite probability vectors is a finite
probability vector.  For the specified model objects, [the stated conditions](hyp:hPos,hp,hr), [the stated mathematical relationship holds](goal).
-/
-- @node: finiteProbabilityVector_mixture
lemma finiteProbabilityVector_mixture {J : Type} [Fintype J]
    (e : ℝ) (p r : J → ℝ) (hPos : StrictPositivity e)
    (hp : FiniteProbabilityVector p) (hr : FiniteProbabilityVector r) :
    FiniteProbabilityVector (fun j => e * p j + (1 - e) * r j) := by
  have hnonneg : ∀ j, 0 ≤ e * p j + (1 - e) * r j := fun j =>
    add_nonneg (mul_nonneg hPos.1.le (hp.1 j).1)
      (mul_nonneg (sub_nonneg.mpr hPos.2.le) (hr.1 j).1)
  have hsum : ∑ j, (e * p j + (1 - e) * r j) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.2, hr.2]
    ring
  constructor
  · intro j
    refine ⟨hnonneg j, ?_⟩
    calc
      _ ≤ ∑ i, (e * p i + (1 - e) * r i) :=
        Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ j)
      _ = 1 := hsum
  · exact hsum

/-- A finite probability vector averages a bounded score below its largest
cell value.  For the specified model objects, [the stated conditions](hyp:h,hr,hmax), [the stated mathematical relationship holds](goal).
-/
-- @node: finiteProbabilityVector_sum_le_max
lemma finiteProbabilityVector_sum_le_max {J : Type} [Fintype J]
    (r : J → ℝ) (h : J → ℝ) (jMax : J)
    (hr : FiniteProbabilityVector r) (hmax : ∀ j, h j ≤ h jMax) :
    ∑ j, h j * r j ≤ h jMax := by
  calc
    ∑ j, h j * r j ≤ ∑ j, h jMax * r j := by
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hmax j) (hr.1 j).1
    _ = h jMax := by rw [← Finset.mul_sum, hr.2, mul_one]

/-- The finite-alphabet cap program has exactly the mixture feasible set, and
its linear optimum has the claimed weak and strict comparison.  For the specified model objects, [the stated conditions](hyp:hPos,hf), [the stated mathematical relationship holds](goal).
-/
-- @node: finiteAlphabetLegality_of_admissible
lemma finiteAlphabetLegality_of_admissible
    (f : ℝ → ℝ) (e : ℝ) (hPos : StrictPositivity e)
    (hf : AdmissibleGenerator f) (oneSided : Bool) :
    FiniteAlphabetLegality f e oneSided := by
  classical
  intro J _ p hp _hsupport
  dsimp only
  let relaxed : Set (J → ℝ) :=
    {q | FiniteProbabilityVector q ∧ (∀ j, 0 < p j → 0 < q j) ∧
      finiteFDiv f p q ≤ divRadius f e}
  let lawful : Set (J → ℝ) := {q | q ∈ relaxed ∧ ∀ j, e * p j ≤ q j}
  let mixtures : Set (J → ℝ) :=
    {q | FiniteProbabilityVector q ∧ ∃ r : J → ℝ,
      FiniteProbabilityVector r ∧ ∀ j, q j = e * p j + (1 - e) * r j}
  have hcap_relaxed : ∀ q, FiniteProbabilityVector q →
      (∀ j, e * p j ≤ q j) → q ∈ relaxed := by
    intro q hq hcap
    refine ⟨hq, ?_, finiteFDiv_le_radius_of_cap f e p q hPos hf hp hq hcap⟩
    intro j hpj
    exact lt_of_lt_of_le (mul_pos hPos.1 hpj) (hcap j)
  have hlaw_mix : lawful = mixtures := by
    calc
      lawful = {q : J → ℝ | FiniteProbabilityVector q ∧ ∀ j, e * p j ≤ q j} := by
        ext q
        simp only [lawful, Set.mem_setOf_eq]
        constructor
        · rintro ⟨hrel, hcap⟩
          exact ⟨hrel.1, hcap⟩
        · rintro ⟨hq, hcap⟩
          exact ⟨hcap_relaxed q hq hcap, hcap⟩
      _ = mixtures := (finiteMixtures_eq_cap e p hPos hp).symm
  refine ⟨hlaw_mix, ?_⟩
  intro h
  constructor
  · apply csSup_le
    · have hp_cap : ∀ j, e * p j ≤ p j := by
        intro j
        exact mul_le_of_le_one_left (hp.1 j).1 hPos.2.le
      refine ⟨∑ j, h j * p j, p, ?_, rfl⟩
      exact ⟨hcap_relaxed p hp hp_cap, hp_cap⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact le_csSup (by
        refine ⟨∑ j, |h j|, ?_⟩
        rintro _ ⟨r, hr, rfl⟩
        apply Finset.sum_le_sum
        intro j _
        have hr0 := (hr.1.1 j).1
        have hr1 := (hr.1.1 j).2
        by_cases hh : 0 ≤ h j
        · rw [abs_of_nonneg hh]
          exact mul_le_of_le_one_right hh hr1
        · exact le_trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hh) hr0)
            (abs_nonneg _)) ⟨q, hq.1, rfl⟩
  · intro qStar hqStar hoptimal hunique hviolates
    have hne : (Finset.univ : Finset J).Nonempty := by
      by_contra hempty
      have hone := hp.2
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hone
      simp at hone
    obtain ⟨jMax, _, hmax⟩ := Finset.exists_max_image Finset.univ h hne
    have hmax' : ∀ j, h j ≤ h jMax := fun j => hmax j (Finset.mem_univ j)
    let rMax : J → ℝ := fun j => if j = jMax then 1 else 0
    have hrMax : FiniteProbabilityVector rMax := by
      constructor
      · intro j
        simp only [rMax]
        split <;> simp
      · simp [rMax]
    let qMax : J → ℝ := fun j => e * p j + (1 - e) * rMax j
    have hqMaxProb : FiniteProbabilityVector qMax :=
      finiteProbabilityVector_mixture e p rMax hPos hp hrMax
    have hqMaxCap : ∀ j, e * p j ≤ qMax j := by
      intro j
      exact le_add_of_nonneg_right
        (mul_nonneg (sub_nonneg.mpr hPos.2.le) (hrMax.1 j).1)
    have hqMaxLaw : qMax ∈ lawful :=
      ⟨hcap_relaxed qMax hqMaxProb hqMaxCap, hqMaxCap⟩
    have hqMaxObj : ∑ j, h j * qMax j =
        e * ∑ j, h j * p j + (1 - e) * h jMax := by
      simp only [qMax]
      have : ∑ j, h j * rMax j = h jMax := by simp [rMax]
      calc
        ∑ j, h j * (e * p j + (1 - e) * rMax j) =
            ∑ j, (e * (h j * p j) + (1 - e) * (h j * rMax j)) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = e * ∑ j, h j * p j + (1 - e) * h jMax := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, this]
    have hLawBound : ∀ q ∈ lawful, ∑ j, h j * q j ≤ ∑ j, h j * qMax j := by
      intro q hq
      have hqmix : q ∈ mixtures := hlaw_mix ▸ hq
      rcases hqmix with ⟨_, r, hr, hrepr⟩
      calc
        ∑ j, h j * q j =
            e * ∑ j, h j * p j + (1 - e) * ∑ j, h j * r j := by
          calc
            ∑ j, h j * q j =
                ∑ j, (e * (h j * p j) + (1 - e) * (h j * r j)) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hrepr j]
              ring
            _ = _ := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ e * ∑ j, h j * p j + (1 - e) * h jMax := by
          exact add_le_add_right (mul_le_mul_of_nonneg_left
            (finiteProbabilityVector_sum_le_max r h jMax hr hmax')
            (sub_nonneg.mpr hPos.2.le)) (e * ∑ j, h j * p j)
        _ = ∑ j, h j * qMax j := hqMaxObj.symm
    have hsup_eq : sSup ((fun q => ∑ j, h j * q j) '' lawful) =
        ∑ j, h j * qMax j := by
      apply le_antisymm
      · apply csSup_le
        · exact ⟨_, qMax, hqMaxLaw, rfl⟩
        · rintro _ ⟨q, hq, rfl⟩
          exact hLawBound q hq
      · exact le_csSup (by
          refine ⟨∑ j, h j * qStar j, ?_⟩
          rintro _ ⟨q, hq, rfl⟩
          exact hoptimal q hq.1) ⟨qMax, hqMaxLaw, rfl⟩
    rw [hsup_eq]
    have hle : ∑ j, h j * qMax j ≤ ∑ j, h j * qStar j :=
      hoptimal qMax hqMaxLaw.1
    exact lt_of_le_of_ne hle fun heq => by
      have hsame : qMax = qStar := hunique qMax hqMaxLaw.1 heq
      rcases hviolates with ⟨j, hj⟩
      have := hqMaxCap j
      rw [hsame] at this
      exact (not_lt_of_ge this) hj

end CausalSmith.SCM.PropensityLvSharpnessFrontier

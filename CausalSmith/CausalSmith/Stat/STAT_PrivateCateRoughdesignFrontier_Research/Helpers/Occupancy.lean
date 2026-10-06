module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.Construction
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.PointVersion
/-! Occupancy cancellation and design-uniform population bias and denominator bounds. -/
public section
open MeasureTheory
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign
/-- Density bounds compare every design-event mass with its Lebesgue mass.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:P,hP,s). -/
-- @node: design_mass_bounds
lemma design_mass_bounds (P : CausalLaw) (hP : CompleteModel P) (s : Set Covariate) :
    volume.real s / 2 ≤ (PX P).real s ∧
      (PX P).real s ≤ 3 * volume.real s / 2 := by
  let : IsProbabilityMeasure (PX P) := Measure.isProbabilityMeasure_map measurable_X.aemeasurable
  have hlo : (ENNReal.ofReal (1 / 2 : ℝ)) • (volume : Measure Covariate) ≤ PX P := by
    rw [PX, P.density_version hP.density.1, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [hP.density.2] with x hx
    exact ENNReal.ofReal_le_ofReal hx.1
  have hhi : PX P ≤ (ENNReal.ofReal (3 / 2 : ℝ)) • (volume : Measure Covariate) := by
    rw [PX, P.density_version hP.density.1, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [hP.density.2] with x hx
    exact ENNReal.ofReal_le_ofReal hx.2
  have hl := ENNReal.toReal_mono (measure_ne_top (PX P) s) (hlo s)
  have hu := ENNReal.toReal_mono
    (show ((ENNReal.ofReal (3 / 2 : ℝ)) • (volume : Measure Covariate)) s ≠ ∞ by
      simp only [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top volume s)) (hhi s)
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2), ← measureReal_def] at hl hu
  constructor <;> linarith

/-- Each cell's endpoints lie in the unit interval and differ by the public width.  [the theorem's stated inputs and assumptions](hyp:hh,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: cell_endpoint_bounds
lemma cell_endpoint_bounds (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (j : Fin k) :
    0 ≤ (x0 : ℝ) - h + j.val * cellWidth h k ∧
    (x0 : ℝ) - h + (j.val + 1) * cellWidth h k ≤ 1 ∧
    (x0 : ℝ) - h + (j.val + 1) * cellWidth h k ≤ (x0 : ℝ) + h ∧
    0 < cellWidth h k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hh0 := hh.1
  have hd : 0 < cellWidth h k := by unfold cellWidth; positivity
  have hwidth : (k : ℝ) * cellWidth h k = 2 * h := by
    unfold cellWidth
    field_simp
  have hj : (j.val : ℝ) + 1 ≤ k := by exact_mod_cast j.isLt
  have hju := mul_le_mul_of_nonneg_right hj hd.le
  have hjl := mul_nonneg (Nat.cast_nonneg j.val) hd.le
  simp only [x0] at *
  refine ⟨?_, ?_, ?_, hd⟩ <;> linarith

/-- Including the final right endpoint does not change the Lebesgue mass of a cell.  [the theorem's stated inputs and assumptions](hyp:hh,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: cell_volume
lemma cell_volume (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (j : Fin k) :
    volume.real (cell h k j) = cellWidth h k := by
  obtain ⟨hl, hu, hwindow, hd⟩ := cell_endpoint_bounds k h hk hh j
  let a : Covariate := ⟨(x0 : ℝ) - h + j.val * cellWidth h k,
    hl, by nlinarith⟩
  let b : Covariate := ⟨(x0 : ℝ) - h + (j.val + 1) * cellWidth h k,
    by nlinarith, hu⟩
  have hab : (b : ℝ) - (a : ℝ) = cellWidth h k := by dsimp [a, b]; ring
  have hsub : Set.Ico a b ⊆ cell h k j := by
    intro x hx
    exact ⟨hx.1, Or.inl hx.2⟩
  have hsup : cell h k j ⊆ Set.Icc a b := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    rcases hx.2 with hx | ⟨hj, hx⟩
    · exact hx.le
    · change (x : ℝ) ≤ (x0 : ℝ) - h + (j.val + 1) * cellWidth h k
      have he : ((j.val + 1 : ℕ) : ℝ) = k := by exact_mod_cast hj
      have hw : (k : ℝ) * cellWidth h k = 2 * h := by
        unfold cellWidth
        have : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
        field_simp
      rw [Nat.cast_add, Nat.cast_one] at he
      rw [hx, he, hw]
      linarith
  have hlo := measure_mono (μ := (volume : Measure Covariate)) hsub
  have hhi := measure_mono (μ := (volume : Measure Covariate)) hsup
  rw [unitInterval.volume_Ico, hab] at hlo
  rw [unitInterval.volume_Icc, hab] at hhi
  have heq := le_antisymm hhi hlo
  rw [measureReal_def, heq, ENNReal.toReal_ofReal hd.le]

/-- The complete model supplies both cellwise mass estimates without design smoothness.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: cellMass_density_bounds
lemma cellMass_density_bounds (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) (j : Fin k) :
    cellWidth h k / 2 ≤ cellMass h k P j ∧
      cellMass h k P j ≤ 3 * cellWidth h k / 2 := by
  have hb := design_mass_bounds P hP (cell h k j)
  rw [cell_volume k h hk hh j] at hb
  exact hb

/-- Summing equal-cell mass bounds gives the local-window mass bounds.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: local_cellMass_sum_bounds
lemma local_cellMass_sum_bounds (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) :
    h ≤ ∑ j : Fin k, cellMass h k P j ∧
      (∑ j : Fin k, cellMass h k P j) ≤ 3 * h := by
  have hl := Finset.sum_le_sum (s := Finset.univ)
    (fun (j : Fin k) _ => (cellMass_density_bounds k h hk hh P hP j).1)
  have hu := Finset.sum_le_sum (s := Finset.univ)
    (fun (j : Fin k) _ => (cellMass_density_bounds k h hk hh P hP j).2)
  have hw : (k : ℝ) * cellWidth h k = 2 * h := by
    unfold cellWidth
    have : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    field_simp
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hl hu
  constructor <;> nlinarith

/-- Every population cell mass lies between zero and one.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:h,k,P,j). -/
-- @node: cellMass_bounds
lemma cellMass_bounds (h : ℝ) (k : ℕ) (P : CausalLaw) (j : Fin k) :
    0 ≤ cellMass h k P j ∧ cellMass h k P j ≤ 1 := by
  let : IsProbabilityMeasure (PX P) := Measure.isProbabilityMeasure_map measurable_X.aemeasurable
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- The probability of no partner has the usual exponential envelope.  [the theorem's stated inputs and assumptions](hyp:m), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:p,hp). -/
-- @node: occupancy_no_partner_exp
lemma occupancy_no_partner_exp (p : ℝ) (m : ℕ) (hp : p ≤ 1) :
    (1 - p) ^ m ≤ Real.exp (-(m : ℝ) * p) := by
  calc
    _ ≤ (Real.exp (-p)) ^ m :=
      pow_le_pow_left₀ (sub_nonneg.mpr hp) (Real.one_sub_le_exp_neg p) m
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- The union bound controls the probability that a cell has a partner.  [the theorem's stated inputs and assumptions](hyp:hp), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:p,m). -/
-- @node: occupancy_partner_union_bound
lemma occupancy_partner_union_bound (p : ℝ) (m : ℕ)
    (hp : 0 ≤ p ∧ p ≤ 1) : 1 - (1 - p) ^ m ≤ min 1 ((m : ℝ) * p) := by
  apply le_min
  · have := pow_nonneg (sub_nonneg.mpr hp.2) m
    linarith
  · have hb := one_add_mul_le_pow (a := -p) (by linarith [hp.2]) m
    have heq : 1 + -p = 1 - p := by ring
    rw [heq] at hb
    linarith

/-- The exponential partner probability dominates a rational envelope.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,hx). -/
-- @node: occupancy_exp_rational_lower
lemma occupancy_exp_rational_lower (x : ℝ) (hx : 0 ≤ x) :
    x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have hpos : 0 < 1 + x := by linarith
  have hE : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hi : Real.exp (-x) ≤ (1 + x)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos x) hpos).mpr hE
  have hid : x / (1 + x) = 1 - (1 + x)⁻¹ := by
    field_simp
    <;> ring
  rw [hid]
  linarith

/-- The rational envelope controls both sparse and dense occupancies uniformly.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,hx). -/
-- @node: occupancy_rational_truncation
lemma occupancy_rational_truncation (x : ℝ) (hx : 0 ≤ x) :
    min 1 x / 8 ≤ x / (4 + x) := by
  have hd : 0 < 4 + x := by linarith
  rw [le_div_iff₀ hd]
  by_cases hsmall : x ≤ 1
  · rw [min_eq_right hsmall]
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hsmall)]
  · rw [min_eq_left (le_of_not_ge hsmall)]
    linarith

/-- The lower cell-mass bound gives a uniform partner-probability lower bound.  [the theorem's stated inputs and assumptions](hyp:hd,hp,hp1), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,delta,p,hn). -/
-- @node: occupancy_partner_lower
lemma occupancy_partner_lower (n : ℕ) (delta p : ℝ) (hn : 2 ≤ n)
    (hd : 0 ≤ delta) (hp : delta / 2 ≤ p) (hp1 : p ≤ 1) :
    min 1 ((n : ℝ) * delta) / 8 ≤ 1 - (1 - p) ^ (n - 1) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hp0 : 0 ≤ p := by linarith
  have hprod : (n : ℝ) * delta / 4 ≤ ((n - 1 : ℕ) : ℝ) * p := by
    rw [hm]
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) / 2 by positivity)
      (show 0 ≤ p - delta / 2 by linarith),
      mul_nonneg (show 0 ≤ (n : ℝ) - 1 - (n : ℝ) / 2 by linarith) hp0]
  have hpow : (1 - p) ^ (n - 1) ≤ Real.exp (-((n : ℝ) * delta / 4)) :=
    (occupancy_no_partner_exp p (n - 1) hp1).trans
      (Real.exp_le_exp.mpr (by linarith))
  calc
    _ ≤ ((n : ℝ) * delta) / (4 + (n : ℝ) * delta) :=
      occupancy_rational_truncation _ (mul_nonneg hn0 hd)
    _ = ((n : ℝ) * delta / 4) / (1 + (n : ℝ) * delta / 4) := by
      have : 4 + (n : ℝ) * delta ≠ 0 := by positivity
      field_simp
      <;> ring
    _ ≤ 1 - Real.exp (-((n : ℝ) * delta / 4)) :=
      occupancy_exp_rational_lower _ (by positivity)
    _ ≤ _ := by linarith

/-- The upper cell-mass bound gives a uniform partner-probability upper bound.  [the theorem's stated inputs and assumptions](hyp:hd,hp,hpu), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,delta,p). -/
-- @node: occupancy_partner_upper
lemma occupancy_partner_upper (n : ℕ) (delta p : ℝ)
    (hd : 0 ≤ delta) (hp : 0 ≤ p ∧ p ≤ 1) (hpu : p ≤ 3 * delta / 2) :
    1 - (1 - p) ^ (n - 1) ≤ (3 / 2) * min 1 ((n : ℝ) * delta) := by
  have hb := occupancy_partner_union_bound p (n - 1) hp
  have hm : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmp : ((n - 1 : ℕ) : ℝ) * p ≤ (3 / 2) * ((n : ℝ) * delta) := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - ((n - 1 : ℕ) : ℝ) by linarith) hp.1,
      mul_nonneg hn0 (show 0 ≤ 3 * delta / 2 - p by linarith)]
  by_cases hs : (n : ℝ) * delta ≤ 1
  · rw [min_eq_right hs]
    exact (hb.trans (min_le_right _ _)).trans hmp
  · rw [min_eq_left (le_of_not_ge hs)]
    linarith [hb.trans (min_le_left _ _)]

/-- Summing the partner envelopes gives both design-uniform occupancy comparisons.
The premises are the cell-mass estimates supplied by the model's density bounds. The result uses [the stated assumptions](hyp:hn,hd,hp,hs) and establishes [the displayed conclusion](goal). -/
-- @node: occupancy_comparisons_of_cell_masses
lemma occupancy_comparisons_of_cell_masses (n k : ℕ) (h : ℝ) (P : CausalLaw)
    (hn : 2 ≤ n) (hd : 0 ≤ cellWidth h k)
    (hp : ∀ j : Fin k, cellWidth h k / 2 ≤ cellMass h k P j ∧
      cellMass h k P j ≤ 3 * cellWidth h k / 2)
    (hs : h ≤ ∑ j : Fin k, cellMass h k P j ∧
      (∑ j : Fin k, cellMass h k P j) ≤ 3 * h) :
    info n h k / 8 ≤ Wocc n h k P ∧ Wocc n h k P ≤ 9 * info n h k / 2 := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ht : 0 ≤ min 1 ((n : ℝ) * cellWidth h k) :=
    le_min (by norm_num) (mul_nonneg hn0 hd)
  have hsumlo :
      (∑ j : Fin k, (n : ℝ) * cellMass h k P j *
        (min 1 ((n : ℝ) * cellWidth h k) / 8)) ≤ Wocc n h k P := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (occupancy_partner_lower n _ _ hn hd (hp j).1 (cellMass_bounds h k P j).2)
      (mul_nonneg hn0 (cellMass_bounds h k P j).1)
  have hsumhi : Wocc n h k P ≤
      ∑ j : Fin k, (n : ℝ) * cellMass h k P j *
        ((3 / 2) * min 1 ((n : ℝ) * cellWidth h k)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (occupancy_partner_upper n _ _ hd (cellMass_bounds h k P j) (hp j).2)
      (mul_nonneg hn0 (cellMass_bounds h k P j).1)
  simp only [← Finset.sum_mul, ← Finset.mul_sum] at hsumlo hsumhi
  constructor
  · have hmass := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs.1 hn0) (show 0 ≤ min 1 ((n : ℝ) * cellWidth h k) / 8 by positivity)
    unfold info
    nlinarith
  · have hmass := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs.2 hn0)
      (show 0 ≤ (3 / 2 : ℝ) * min 1 ((n : ℝ) * cellWidth h k) by positivity)
    unfold info
    nlinarith

/-- The density bounds imply both occupancy comparisons for every law in the complete model.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,hn,hk). -/
-- @node: occupancy_comparisons
lemma occupancy_comparisons (n k : ℕ) (h : ℝ) (hn : 2 ≤ n) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) :
    info n h k / 8 ≤ Wocc n h k P ∧ Wocc n h k P ≤ 9 * info n h k / 2 := by
  exact occupancy_comparisons_of_cell_masses n k h P hn
    (cell_endpoint_bounds k h hk hh ⟨0, hk⟩).2.2.2.le
    (cellMass_density_bounds k h hk hh P hP)
    (local_cellMass_sum_bounds k h hk hh P hP)

/-- The common occupancy weights are nonnegative, even without model assumptions.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,P,j). -/
-- @node: occupancyWeight_nonneg
lemma occupancyWeight_nonneg (n k : ℕ) (h : ℝ) (P : CausalLaw) (j : Fin k) :
    0 ≤ occupancyWeight n h k P j := by
  obtain ⟨hp0, hp1⟩ := cellMass_bounds h k P j
  have hpow : (1 - cellMass h k P j) ^ (n - 1) ≤ 1 :=
    pow_le_one₀ (sub_nonneg.mpr hp1) (by linarith)
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hp0) (sub_nonneg.mpr hpow)

/-- The public information and denominator floor are strictly positive on the public domain.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,hn,hk,hh). -/
-- @node: info_d0_pos
lemma info_d0_pos (n k : ℕ) (h : ℝ) (hn : 0 < n) (hk : 0 < k) (hh : 0 < h) :
    0 < info n h k ∧ 0 < d0 n h k := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hk' : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hw : 0 < cellWidth h k := by unfold cellWidth; positivity
  have hi : 0 < info n h k := by unfold info; positivity
  exact ⟨hi, by unfold d0; positivity⟩

/-- A common nonnegative weight preserves the cellwise denominator lower bound.  [the theorem's stated inputs and assumptions](hyp:hd), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,P). -/
-- @node: occupancy_denominator_lower
lemma occupancy_denominator_lower (n k : ℕ) (h : ℝ) (P : CausalLaw)
    (hd : ∀ j : Fin k, 3 / 8 ≤ dj h k P j) :
    (3 / 8) * Wocc n h k P ≤
      ∑ j : Fin k, occupancyWeight n h k P j * dj h k P j := by
  unfold Wocc
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  calc
    (3 / 8) * occupancyWeight n h k P j = occupancyWeight n h k P j * (3 / 8) := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hd j) (occupancyWeight_nonneg n k h P j)

/-- Common nonnegative weights preserve the conditional cell bias certificate.  [the theorem's stated inputs and assumptions](hyp:hb), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,P). -/
-- @node: occupancy_weighted_bias
lemma occupancy_weighted_bias (n k : ℕ) (h : ℝ) (P : CausalLaw)
    (hb : ∀ j : Fin k,
      |nu h k P j - theta P * dj h k P j| ≤ bias h k * dj h k P j) :
    |(∑ j : Fin k, occupancyWeight n h k P j * nu h k P j) -
      theta P * (∑ j : Fin k, occupancyWeight n h k P j * dj h k P j)| ≤
      bias h k * (∑ j : Fin k, occupancyWeight n h k P j * dj h k P j) := by
  classical
  calc
    _ = |∑ j : Fin k, occupancyWeight n h k P j *
        (nu h k P j - theta P * dj h k P j)| := by
      congr 1
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ ∑ j : Fin k, |occupancyWeight n h k P j *
        (nu h k P j - theta P * dj h k P j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin k, occupancyWeight n h k P j * (bias h k * dj h k P j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (occupancyWeight_nonneg n k h P j)]
      exact mul_le_mul_of_nonneg_left (hb j) (occupancyWeight_nonneg n k h P j)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Dividing a weighted bias certificate by a positive denominator gives the ratio bound.  [the theorem's stated inputs and assumptions](hyp:hb), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:N,D,target,b,hD). -/
-- @node: ratio_bias_of_positive_denominator
lemma ratio_bias_of_positive_denominator (N D target b : ℝ) (hD : 0 < D)
    (hb : |N - target * D| ≤ b * D) : |N / D - target| ≤ b := by
  have heq : N / D - target = (N - target * D) / D := by
    field_simp
  rw [heq, abs_div, abs_of_pos hD]
  exact (div_le_iff₀ hD).mpr hb

/-- The independent cross-treatment probability is at least three eighths under overlap.  [the theorem's stated inputs and assumptions](hyp:he,he'), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:e,e'). -/
-- @node: cross_treatment_denominator_bounds
lemma cross_treatment_denominator_bounds (e e' : ℝ)
    (he : 1 / 4 ≤ e ∧ e ≤ 3 / 4) (he' : 1 / 4 ≤ e' ∧ e' ≤ 3 / 4) :
    3 / 8 ≤ e * (1 - e') + e' * (1 - e) ∧
      e * (1 - e') + e' * (1 - e) ≤ 1 := by
  have h1 := mul_nonneg (sub_nonneg.mpr he.1) (sub_nonneg.mpr he'.2)
  have h2 := mul_nonneg (sub_nonneg.mpr he.2) (sub_nonneg.mpr he'.1)
  have h3 := mul_nonneg (show 0 ≤ e by linarith) (show 0 ≤ e' by linarith)
  have h4 := mul_nonneg (show 0 ≤ 1 - e by linarith) (show 0 ≤ 1 - e' by linarith)
  constructor <;> nlinarith

/-- The pointwise conditional numerator identity gives the paper's cellwise bias envelope.  [the theorem's stated inputs and assumptions](hyp:he,he',hr,ht0,ht1), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:e,e',residual,tau0,tau1,target,u). -/
-- @node: cross_treatment_bias_bound
lemma cross_treatment_bias_bound (e e' residual tau0 tau1 target h u : ℝ)
    (he : 1 / 4 ≤ e ∧ e ≤ 3 / 4) (he' : 1 / 4 ≤ e' ∧ e' ≤ 3 / 4)
    (hr : |residual| ≤ 9 * u)
    (ht0 : |tau0 - target| ≤ 3 * h) (ht1 : |tau1 - target| ≤ 3 * h) :
    |residual + e * (1 - e') * tau0 + e' * (1 - e) * tau1 -
      target * (e * (1 - e') + e' * (1 - e))| ≤
      (3 * h + 24 * u) * (e * (1 - e') + e' * (1 - e)) := by
  have hw0 : 0 ≤ e * (1 - e') :=
    mul_nonneg (by linarith [he.1]) (by linarith [he'.2])
  have hw1 : 0 ≤ e' * (1 - e) :=
    mul_nonneg (by linarith [he'.1]) (by linarith [he.2])
  have hu : 0 ≤ u := by nlinarith [abs_nonneg residual]
  have hd := (cross_treatment_denominator_bounds e e' he he').1
  calc
    _ = |residual + (e * (1 - e') * (tau0 - target) +
        e' * (1 - e) * (tau1 - target))| := by congr 1; ring
    _ ≤ |residual| + |e * (1 - e') * (tau0 - target) +
        e' * (1 - e) * (tau1 - target)| := abs_add_le _ _
    _ ≤ |residual| + (|e * (1 - e') * (tau0 - target)| +
        |e' * (1 - e) * (tau1 - target)|) := by
      exact add_le_add (le_refl |residual|)
        (abs_add_le (e * (1 - e') * (tau0 - target)) (e' * (1 - e) * (tau1 - target)))
    _ ≤ 9 * u + (e * (1 - e') * (3 * h) + e' * (1 - e) * (3 * h)) := by
      rw [abs_mul (e * (1 - e')), abs_mul (e' * (1 - e)),
        abs_of_nonneg hw0, abs_of_nonneg hw1]
      exact add_le_add hr (add_le_add
        (mul_le_mul_of_nonneg_left ht0 hw0) (mul_le_mul_of_nonneg_left ht1 hw1))
    _ ≤ _ := by nlinarith [mul_nonneg hu (sub_nonneg.mpr hd)]

/-- Every point of a public cell lies within the public radius of the target covariate.  [the theorem's stated inputs and assumptions](hyp:hh,j,x,hx), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: cell_distance_to_target
lemma cell_distance_to_target (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (j : Fin k) (x : Covariate)
    (hx : x ∈ cell h k j) : |(x : ℝ) - x0| ≤ h := by
  obtain ⟨hl, hu, hw, hd⟩ := cell_endpoint_bounds k h hk hh j
  have hj : 0 ≤ (j.val : ℝ) * cellWidth h k :=
    mul_nonneg (Nat.cast_nonneg _) hd.le
  have hxlo : (x0 : ℝ) - h ≤ (x : ℝ) := by linarith [hx.1]
  have hxhi : (x : ℝ) ≤ (x0 : ℝ) + h := by
    rcases hx.2 with hx | ⟨_, hx⟩
    · linarith
    · exact hx.le
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Two covariates in one cell are separated by at most the public cell width,
including the right endpoint of the final cell.  [the theorem's stated inputs and assumptions](hyp:hh,j,x,x',hx,hx'), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: cell_pair_distance
lemma cell_pair_distance (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (j : Fin k) (x x' : Covariate)
    (hx : x ∈ cell h k j) (hx' : x' ∈ cell h k j) :
    |(x : ℝ) - x'| ≤ cellWidth h k := by
  have hwidth : (k : ℝ) * cellWidth h k = 2 * h := by
    unfold cellWidth
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    field_simp
  have hupper : ∀ z : Covariate, z ∈ cell h k j →
      (z : ℝ) ≤ (x0 : ℝ) - h + (j.val + 1) * cellWidth h k := by
    intro z hz
    rcases hz.2 with hz | ⟨hj, hz⟩
    · exact hz.le
    · have hjR : (j.val : ℝ) + 1 = k := by exact_mod_cast hj
      rw [hz, hjR, hwidth]
      linarith
  have hu := hupper x hx
  have hu' := hupper x' hx'
  exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx'.1]⟩

/-- The two one-tenth Holder remainders multiply to the one-fifth cell-width term.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j,x,x',hx,hx'), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: cell_nuisance_product_bound
lemma cell_nuisance_product_bound (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P)
    (j : Fin k) (x x' : Covariate) (hx : x ∈ cell h k j)
    (hx' : x' ∈ cell h k j) :
    |(P.e x - P.e x') * (P.mu0 x - P.mu0 x')| ≤
      9 * (cellWidth h k) ^ (1 / 5 : ℝ) := by
  have hdelta := (cell_endpoint_bounds k h hk hh j).2.2.2
  have hd := cell_pair_distance k h hk hh j x x' hx hx'
  have he := hP.propensity_holder x x'
  have hm := hP.control_holder x x'
  change |P.e x - P.e x'| ≤ 3 * |(x : ℝ) - x'| ^ (1 / 10 : ℝ) at he
  change |P.mu0 x - P.mu0 x'| ≤ 3 * |(x : ℝ) - x'| ^ (1 / 10 : ℝ) at hm
  have hr : |(x : ℝ) - x'| ^ (1 / 10 : ℝ) ≤
      cellWidth h k ^ (1 / 10 : ℝ) :=
    Real.rpow_le_rpow (abs_nonneg _) hd (by norm_num)
  have hpow : cellWidth h k ^ (1 / 10 : ℝ) *
      cellWidth h k ^ (1 / 10 : ℝ) = cellWidth h k ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_add (cell_endpoint_bounds k h hk hh j).2.2.2]
    norm_num
  calc
    _ = |P.e x - P.e x'| * |P.mu0 x - P.mu0 x'| := abs_mul _ _
    _ ≤ (3 * cellWidth h k ^ (1 / 10 : ℝ)) *
        (3 * cellWidth h k ^ (1 / 10 : ℝ)) :=
      mul_le_mul (he.trans (by linarith)) (hm.trans (by linarith))
        (abs_nonneg _) (by positivity)
    _ = 9 * cellWidth h k ^ (1 / 5 : ℝ) := by nlinarith [hpow]

/-- Expanding the two cross-treatment cases separates nuisance variation from the contrast.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:e,e',m,m',t,t'). -/
-- @node: independent_pair_numerator_expansion
lemma independent_pair_numerator_expansion (e e' m m' t t' : ℝ) :
    e * (1 - e') * (m + t - m') + e' * (1 - e) * (m' + t' - m) =
      (e - e') * (m - m') + e * (1 - e') * t + e' * (1 - e) * t' := by
  ring

/-- At any two covariates in one cell, the independent binary cross-treatment moments
satisfy both the denominator lower bound and the paper's complete bias envelope.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j,x,x',hx,hx'), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: cell_cross_treatment_certificate
lemma cell_cross_treatment_certificate (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P)
    (j : Fin k) (x x' : Covariate) (hx : x ∈ cell h k j)
    (hx' : x' ∈ cell h k j) :
    3 / 8 ≤ P.e x * (1 - P.e x') + P.e x' * (1 - P.e x) ∧
    |P.e x * (1 - P.e x') * (P.mu1 x - P.mu0 x') +
      P.e x' * (1 - P.e x) * (P.mu1 x' - P.mu0 x) -
      theta P * (P.e x * (1 - P.e x') + P.e x' * (1 - P.e x))| ≤
      bias h k * (P.e x * (1 - P.e x') + P.e x' * (1 - P.e x)) := by
  have ht : ∀ z : Covariate, z ∈ cell h k j → |tau P z - theta P| ≤ 3 * h := by
    intro z hz
    have hc : |tau P z - theta P| ≤ 3 * |(z : ℝ) - x0| :=
      hP.contrast_lipschitz z x0
    exact hc.trans
      (mul_le_mul_of_nonneg_left (cell_distance_to_target k h hk hh j z hz) (by norm_num))
  refine ⟨(cross_treatment_denominator_bounds _ _ (hP.overlap x) (hP.overlap x')).1, ?_⟩
  have hn := independent_pair_numerator_expansion (P.e x) (P.e x')
    (P.mu0 x) (P.mu0 x') (tau P x) (tau P x')
  simp only [tau] at hn
  have hb := cross_treatment_bias_bound (P.e x) (P.e x')
    ((P.e x - P.e x') * (P.mu0 x - P.mu0 x')) (tau P x) (tau P x')
    (theta P) h (cellWidth h k ^ (1 / 5 : ℝ)) (hP.overlap x) (hP.overlap x')
    (cell_nuisance_product_bound k h hk hh P hP j x x' hx hx') (ht x hx) (ht x' hx')
  rw [show P.mu0 x + (P.mu1 x - P.mu0 x) = P.mu1 x by ring,
    show P.mu0 x' + (P.mu1 x' - P.mu0 x') = P.mu1 x' by ring] at hn
  rw [hn]
  exact hb

/-- The population identities and cellwise certificates imply the floor and ratio bias bounds.  [the theorem's stated inputs and assumptions](hyp:Q,hn,hk,hh,hN,hD,hc,hW), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,P). -/
-- @node: occupancy_ratio_assembly
lemma occupancy_ratio_assembly (n k : ℕ) (h : ℝ) (P : CausalLaw)
    (Q : Measure (Dataset n)) (hn : 0 < n) (hk : 0 < k) (hh : 0 < h)
    (hN : Nbar n h k Q = ∑ j : Fin k, occupancyWeight n h k P j * nu h k P j)
    (hD : Dbar n h k Q = ∑ j : Fin k, occupancyWeight n h k P j * dj h k P j)
    (hc : ∀ j : Fin k, 3 / 8 ≤ dj h k P j ∧
      |nu h k P j - theta P * dj h k P j| ≤ bias h k * dj h k P j)
    (hW : info n h k / 8 ≤ Wocc n h k P) :
    d0 n h k ≤ Dbar n h k Q ∧
      |Nbar n h k Q / Dbar n h k Q - theta P| ≤ bias h k := by
  have hden : (3 / 8) * Wocc n h k P ≤ Dbar n h k Q := by
    rw [hD]
    exact occupancy_denominator_lower n k h P (fun j => (hc j).1)
  have hfloor : d0 n h k ≤ Dbar n h k Q := by
    unfold d0
    linarith
  have hpos : 0 < Dbar n h k Q :=
    lt_of_lt_of_le (info_d0_pos n k h hn hk hh).2 hfloor
  have hb : |Nbar n h k Q - theta P * Dbar n h k Q| ≤ bias h k * Dbar n h k Q := by
    rw [hN, hD]
    exact occupancy_weighted_bias n k h P (fun j => (hc j).2)
  exact ⟨hfloor, ratio_bias_of_positive_denominator _ _ _ _ hpos hb⟩

end CausalSmith.Stat.PrivateCateRoughdesign

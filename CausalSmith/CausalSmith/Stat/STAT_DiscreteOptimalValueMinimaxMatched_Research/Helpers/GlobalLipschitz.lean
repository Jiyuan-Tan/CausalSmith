import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.ConeExtension

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

-- @node: l1CellDistance
/-- For [the specified first cell vector, second cell vector](hyp:u,v), the [cellwise L1 distance is the sum of absolute coordinate differences across the four cells](goal). -/
def l1CellDistance (u v : Cell → ℝ) : ℝ := ∑ j, |u j - v j|

-- @node: armCellValue_bounds
/-- If [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the stated u condition holds](hyp:hu), then [the stated arm cell value bounds relation holds](goal). -/
lemma armCellValue_bounds {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (u : Cell → ℝ) (hu : ∀ j, 0 ≤ u j) (a : Fin 2) :
    0 ≤ armCellValue epsilon a u ∧ armCellValue epsilon a u ≤ vectorMass u := by
  have hArm : 0 ≤ vectorArmMass u a := by
    exact add_nonneg (hu (a, 0)) (hu (a, 1))
  have hz : 0 ≤ u (a, 1) := hu _
  have hzle : u (a, 1) ≤ vectorArmMass u a := by
    simp [vectorArmMass]
    exact hu (a, 0)
  have hMass : 0 ≤ vectorMass u := by
    unfold vectorMass
    exact add_nonneg
      (add_nonneg (hu (0, 0)) (hu (0, 1)))
      (add_nonneg (hu (1, 0)) (hu (1, 1)))
  by_cases hzero : vectorMass u = 0
  · simp [armCellValue, hzero]
  · have hMassPos : 0 < vectorMass u := lt_of_le_of_ne hMass (Ne.symm hzero)
    have hden : 0 < max (vectorArmMass u a) (epsilon * vectorMass u) :=
      lt_of_lt_of_le (mul_pos hepsilon hMassPos) (le_max_right _ _)
    rw [armCellValue, if_neg hzero]
    constructor
    · positivity
    · rw [div_le_iff₀ hden]
      exact mul_le_mul_of_nonneg_left
        (hzle.trans (le_max_left _ _)) hMass

-- @node: globalCellValue_bounds
/-- If [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the stated u condition holds](hyp:hu), then [the stated global cell value bounds relation holds](goal). -/
lemma globalCellValue_bounds {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (u : Cell → ℝ) (hu : ∀ j, 0 ≤ u j) :
    0 ≤ globalCellValue epsilon u ∧ globalCellValue epsilon u ≤ vectorMass u := by
  have h0 := armCellValue_bounds hepsilon u hu 0
  have h1 := armCellValue_bounds hepsilon u hu 1
  exact ⟨h0.1.trans (le_max_left _ _), max_le h0.2 h1.2⟩

-- @node: unitRatio_diff_bound
/-- If [the target function is continuous](hyp:hf), and [the stated z condition holds](hyp:hz), and [the stated f' condition holds](hyp:hf'), and [the stated z' condition holds](hyp:hz'), and [the argument satisfies the stated support or positivity restriction](hyp:ht), and [the stated t' condition holds](hyp:ht'), then [the stated unit ratio diff bound relation holds](goal). -/
lemma unitRatio_diff_bound (f z f' z' : ℝ)
    (hf : 0 ≤ f) (hz : 0 ≤ z) (hf' : 0 ≤ f') (hz' : 0 ≤ z')
    (ht : 0 < f + z) (ht' : 0 < f' + z') :
    |z / (f + z) - z' / (f' + z')| ≤
      (|z - z'| + |f - f'|) / (f + z) := by
  have hiden : z / (f + z) - z' / (f' + z') =
      (f' * (z - z') + z' * (f' - f)) / ((f + z) * (f' + z')) := by
    field_simp
    ring
  rw [hiden, abs_div, abs_mul, abs_of_pos ht, abs_of_pos ht']
  have hden : 0 < (f + z) * (f' + z') := mul_pos ht ht'
  calc
    |f' * (z - z') + z' * (f' - f)| / ((f + z) * (f' + z'))
        ≤ (f' * |z - z'| + z' * |f - f'|) / ((f + z) * (f' + z')) := by
          gcongr
          calc
            |f' * (z - z') + z' * (f' - f)|
                ≤ |f' * (z - z')| + |z' * (f' - f)| := abs_add_le _ _
            _ = f' * |z - z'| + z' * |f - f'| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hf', abs_of_nonneg hz', abs_sub_comm f' f]
    _ ≤ ((f' + z') * (|z - z'| + |f - f'|)) /
          ((f + z) * (f' + z')) := by
          gcongr
          nlinarith [abs_nonneg (z - z'), abs_nonneg (f - f')]
    _ = (|z - z'| + |f - f'|) / (f + z) := by
          field_simp

-- @node: scalarArmValue
/-- For [the specified overlap level, first failure mass, data point or sample, third cell mass, smaller alphabet size](hyp:epsilon,f,z,r,s), the [scalar arm value is zero at zero total mass and otherwise equals total mass times the success-cell mass divided by the larger of arm mass and overlap-truncated total mass](goal). -/
noncomputable def scalarArmValue (epsilon f z r s : ℝ) : ℝ :=
  let S := f + z + r + s
  if S = 0 then 0 else S * z / max (f + z) (epsilon * S)

-- @node: scalarArmValue_of_low
/-- If [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the stated s condition holds](hyp:hS), and [the stated low condition holds](hyp:hlow), then [the stated scalar arm value of low relation holds](goal). -/
lemma scalarArmValue_of_low {epsilon f z r s : ℝ} (hepsilon : 0 < epsilon)
    (hS : 0 < f + z + r + s) (hlow : f + z ≤ epsilon * (f + z + r + s)) :
    scalarArmValue epsilon f z r s = z / epsilon := by
  rw [scalarArmValue, if_neg (ne_of_gt hS), max_eq_right hlow]
  field_simp

-- @node: scalarArmValue_of_high
/-- If [the stated s condition holds](hyp:hS), and [the stated high condition holds](hyp:hhigh), then [the stated scalar arm value of high relation holds](goal). -/
lemma scalarArmValue_of_high {epsilon f z r s : ℝ}
    (hS : 0 < f + z + r + s) (hhigh : epsilon * (f + z + r + s) ≤ f + z) :
    scalarArmValue epsilon f z r s = (f + z + r + s) * (z / (f + z)) := by
  rw [scalarArmValue, if_neg (ne_of_gt hS), max_eq_left hhigh]
  ring

-- @node: scalarArmValue_lipschitz_of_pos
/-- If [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the target function is continuous](hyp:hf), and [the stated z condition holds](hyp:hz), and [the stated r condition holds](hyp:hr), and [the stated support condition holds](hyp:hs), and [the stated f' condition holds](hyp:hf'), and [the stated z' condition holds](hyp:hz'), and [the stated r' condition holds](hyp:hr'), and [the stated s' condition holds](hyp:hs'), and [the stated s condition holds](hyp:hS), and [the stated s' condition holds](hyp:hS'), then [the stated scalar arm value lipschitz of pos relation holds](goal). -/
lemma scalarArmValue_lipschitz_of_pos {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (f z r s f' z' r' s' : ℝ)
    (hf : 0 ≤ f) (hz : 0 ≤ z) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hf' : 0 ≤ f') (hz' : 0 ≤ z') (hr' : 0 ≤ r') (hs' : 0 ≤ s')
    (hS : 0 < f + z + r + s) (hS' : 0 < f' + z' + r' + s') :
    |scalarArmValue epsilon f z r s - scalarArmValue epsilon f' z' r' s'| ≤
      (1 + epsilon⁻¹) * (|f - f'| + |z - z'| + |r - r'| + |s - s'|) := by
  let S := f + z + r + s
  let S' := f' + z' + r' + s'
  let D := |f - f'| + |z - z'| + |r - r'| + |s - s'|
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hmass : |S - S'| ≤ D := by
    dsimp [S, S', D]
    calc
      |(f + z + r + s) - (f' + z' + r' + s')|
          = |(f - f') + (z - z') + (r - r') + (s - s')| := by ring_nf
      _ ≤ |f - f'| + |z - z'| + |r - r'| + |s - s'| := by
        calc
          |(f - f') + (z - z') + (r - r') + (s - s')|
              ≤ |(f - f') + (z - z') + (r - r')| + |s - s'| := abs_add_le _ _
          _ ≤ (|(f - f') + (z - z')| + |r - r'|) + |s - s'| := by
            gcongr
            exact abs_add_le _ _
          _ ≤ |f - f'| + |z - z'| + |r - r'| + |s - s'| := by
            gcongr
            exact abs_add_le _ _
  have harm : |z - z'| + |f - f'| ≤ D := by
    dsimp [D]
    nlinarith [abs_nonneg (r - r'), abs_nonneg (s - s')]
  have hfd : |f - f'| ≤ D := by
    apply le_trans (show |f - f'| ≤ |z - z'| + |f - f'| by
      nlinarith [abs_nonneg (z - z')]) harm
  have hzD : |z - z'| ≤ D := by
    apply le_trans (show |z - z'| ≤ |z - z'| + |f - f'| by
      nlinarith [abs_nonneg (f - f')]) harm
  have hinv : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have heinv : epsilon * epsilon⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hepsilon)
  have hcoef : 0 ≤ 1 + epsilon⁻¹ := by positivity
  by_cases hu : f + z ≤ epsilon * S
  · rw [scalarArmValue_of_low hepsilon hS (by simpa [S] using hu)]
    by_cases hv : f' + z' ≤ epsilon * S'
    · rw [scalarArmValue_of_low hepsilon hS' (by simpa [S'] using hv)]
      rw [← sub_div, abs_div, abs_of_pos hepsilon]
      calc
        |z - z'| / epsilon ≤ epsilon⁻¹ * D := by
          rw [div_eq_inv_mul]
          exact mul_le_mul_of_nonneg_left hzD (le_of_lt hinv)
        _ ≤ (1 + epsilon⁻¹) * D := by
          exact mul_le_mul_of_nonneg_right (by linarith) hD
    · have hv' : epsilon * S' ≤ f' + z' := le_of_not_ge hv
      rw [scalarArmValue_of_high hS' (by simpa [S'] using hv')]
      have ht' : 0 < f' + z' := lt_of_lt_of_le (mul_pos hepsilon hS') hv'
      have hratio : 0 ≤ z' / (f' + z') ∧ z' / (f' + z') ≤ 1 := by
        constructor
        · positivity
        · exact (div_le_one ht').2 (by linarith)
      have hgap : 0 ≤ (f' + z') - epsilon * S' := by linarith
      have hid : z / epsilon - S' * (z' / (f' + z')) =
          (z - z') / epsilon + (z' / (f' + z')) *
            (((f' + z') - epsilon * S') / epsilon) := by
        field_simp
        ring
      rw [hid, abs_le]
      constructor
      · have hlower : -(1 + epsilon⁻¹) * D ≤ (z - z') / epsilon := by
          rw [div_eq_inv_mul]
          have hzabs := neg_abs_le (z - z')
          dsimp [D] at *
          nlinarith [abs_nonneg (f - f'), abs_nonneg (r - r'), abs_nonneg (s - s')]
        have hsecond : 0 ≤ (z' / (f' + z')) *
            (((f' + z') - epsilon * S') / epsilon) := by positivity
        linarith
      · have hgap_le : (f' + z') - epsilon * S' ≤
            ((f' + z') - (f + z)) - epsilon * (S' - S) := by linarith
        have hsecond_le : (z' / (f' + z')) *
            (((f' + z') - epsilon * S') / epsilon) ≤
            (((f' + z') - epsilon * S') / epsilon) := by
          exact mul_le_of_le_one_left (by positivity) hratio.2
        have hraw : (z - z') / epsilon +
              (((f' + z') - epsilon * S') / epsilon) ≤
            (f' - f - epsilon * (S' - S)) / epsilon := by
          rw [← add_div, div_le_div_iff_of_pos_right hepsilon]
          linarith
        have hbound : (f' - f - epsilon * (S' - S)) / epsilon ≤
            (1 + epsilon⁻¹) * D := by
          have hrewrite : (f' - f - epsilon * (S' - S)) / epsilon =
              epsilon⁻¹ * (f' - f) - (S' - S) := by
            field_simp
          rw [hrewrite]
          have hff := le_abs_self (f' - f)
          have hm : -(S' - S) ≤ D := by
            calc
              -(S' - S) ≤ |S' - S| := neg_le_abs _
              _ = |S - S'| := abs_sub_comm _ _
              _ ≤ D := hmass
          rw [abs_sub_comm f' f] at hff
          have hmul := mul_le_mul_of_nonneg_left hff (le_of_lt hinv)
          nlinarith
        linarith
  · have hu' : epsilon * S ≤ f + z := le_of_not_ge hu
    rw [scalarArmValue_of_high hS (by simpa [S] using hu')]
    by_cases hv : f' + z' ≤ epsilon * S'
    · rw [scalarArmValue_of_low hepsilon hS' (by simpa [S'] using hv)]
      have ht : 0 < f + z := lt_of_lt_of_le (mul_pos hepsilon hS) hu'
      have hratio : 0 ≤ z / (f + z) ∧ z / (f + z) ≤ 1 := by
        constructor
        · positivity
        · exact (div_le_one ht).2 (by linarith)
      have hgap : 0 ≤ (f + z) - epsilon * S := by linarith
      have hid : S * (z / (f + z)) - z' / epsilon =
          (z - z') / epsilon - (z / (f + z)) *
            (((f + z) - epsilon * S) / epsilon) := by
        field_simp
        ring
      rw [hid, abs_le]
      constructor
      · have hgap_le : (f + z) - epsilon * S ≤
            ((f + z) - (f' + z')) - epsilon * (S - S') := by linarith
        have hsecond_le : (z / (f + z)) *
            (((f + z) - epsilon * S) / epsilon) ≤
            (((f + z) - epsilon * S) / epsilon) := by
          exact mul_le_of_le_one_left (by positivity) hratio.2
        have hraw : (f' - f + epsilon * (S - S')) / epsilon ≤
            (z - z') / epsilon - (((f + z) - epsilon * S) / epsilon) := by
          rw [← sub_div, div_le_div_iff_of_pos_right hepsilon]
          linarith
        have hbound : -(1 + epsilon⁻¹) * D ≤
            (f' - f + epsilon * (S - S')) / epsilon := by
          have hrewrite : (f' - f + epsilon * (S - S')) / epsilon =
              epsilon⁻¹ * (f' - f) + (S - S') := by
            field_simp
          rw [hrewrite]
          have hff := neg_abs_le (f' - f)
          rw [abs_sub_comm f' f] at hff
          have hm : -D ≤ S - S' := by
            calc
              -D ≤ -|S - S'| := neg_le_neg hmass
              _ ≤ S - S' := neg_abs_le _
          have hmul := mul_le_mul_of_nonneg_left hff (le_of_lt hinv)
          nlinarith
        linarith
      · have hupper : (z - z') / epsilon ≤ (1 + epsilon⁻¹) * D := by
          rw [div_eq_inv_mul]
          have hzabs := le_trans (le_abs_self (z - z')) hzD
          have hmul := mul_le_mul_of_nonneg_left hzabs (le_of_lt hinv)
          exact hmul.trans (mul_le_mul_of_nonneg_right (by linarith) hD)
        have hsecond : 0 ≤ (z / (f + z)) *
            (((f + z) - epsilon * S) / epsilon) := by positivity
        linarith
    · have hv' : epsilon * S' ≤ f' + z' := le_of_not_ge hv
      rw [scalarArmValue_of_high hS' (by simpa [S'] using hv')]
      have ht : 0 < f + z := lt_of_lt_of_le (mul_pos hepsilon hS) hu'
      have ht' : 0 < f' + z' := lt_of_lt_of_le (mul_pos hepsilon hS') hv'
      have hratio' : 0 ≤ z' / (f' + z') ∧ z' / (f' + z') ≤ 1 := by
        constructor
        · positivity
        · exact (div_le_one ht').2 (by linarith)
      have hratioDiff := unitRatio_diff_bound f z f' z' hf hz hf' hz' ht ht'
      have hid : S * (z / (f + z)) - S' * (z' / (f' + z')) =
          (S - S') * (z' / (f' + z')) +
            S * (z / (f + z) - z' / (f' + z')) := by ring
      rw [hid]
      calc
        |(S - S') * (z' / (f' + z')) +
              S * (z / (f + z) - z' / (f' + z'))|
            ≤ |S - S'| * (z' / (f' + z')) +
                S * |z / (f + z) - z' / (f' + z')| := by
              calc
                _ ≤ |(S - S') * (z' / (f' + z'))| +
                    |S * (z / (f + z) - z' / (f' + z'))| := abs_add_le _ _
                _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hratio'.1, abs_of_pos hS]
        _ ≤ |S - S'| + S * ((|z - z'| + |f - f'|) / (f + z)) := by
          apply add_le_add
          · exact mul_le_of_le_one_right (abs_nonneg _) hratio'.2
          · exact mul_le_mul_of_nonneg_left hratioDiff (le_of_lt hS)
        _ ≤ D + epsilon⁻¹ * (|z - z'| + |f - f'|) := by
          have hSt : S / (f + z) ≤ epsilon⁻¹ := by
            calc
              S / (f + z) ≤ ((f + z) / epsilon) / (f + z) := by
                gcongr
                exact (le_div_iff₀ hepsilon).2 (by simpa [mul_comm] using hu')
              _ = epsilon⁻¹ := by field_simp
          have hmul : S * ((|z - z'| + |f - f'|) / (f + z)) =
              (S / (f + z)) * (|z - z'| + |f - f'|) := by ring
          rw [hmul]
          exact add_le_add hmass (mul_le_mul_of_nonneg_right hSt (by positivity))
        _ ≤ D + epsilon⁻¹ * D := by
          gcongr
        _ = (1 + epsilon⁻¹) * D := by ring

-- @node: cell_eq_zero_of_vectorMass_eq_zero
/-- If [the stated u condition holds](hyp:hu), and [the stated mass condition holds](hyp:hmass), then [a nonnegative cell vector with zero total mass vanishes in every coordinate](goal). -/
lemma cell_eq_zero_of_vectorMass_eq_zero (u : Cell → ℝ) (hu : ∀ j, 0 ≤ u j)
    (hmass : vectorMass u = 0) : ∀ j, u j = 0 := by
  rintro ⟨a, y⟩
  fin_cases a <;> fin_cases y <;>
    simp [vectorMass, vectorArmMass] at hmass ⊢ <;>
    nlinarith [hu (0, 0), hu (0, 1), hu (1, 0), hu (1, 1)]

-- @node: l1CellDistance_zero_left
/-- If [the stated u condition holds](hyp:hu), and [the stated v condition holds](hyp:hv), then [the stated l1 cell distance zero left relation holds](goal). -/
lemma l1CellDistance_zero_left (u v : Cell → ℝ) (hu : ∀ j, u j = 0)
    (hv : ∀ j, 0 ≤ v j) : l1CellDistance u v = vectorMass v := by
  simp only [l1CellDistance, Fintype.sum_prod_type, hu, zero_sub, abs_neg, vectorMass,
    vectorArmMass, Fin.sum_univ_two]
  rw [abs_of_nonneg (hv (0, 0)), abs_of_nonneg (hv (0, 1)),
    abs_of_nonneg (hv (1, 0)), abs_of_nonneg (hv (1, 1))]

-- @node: armCellValue_lipschitz
/-- If [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the stated u condition holds](hyp:hu), and [the stated v condition holds](hyp:hv), then [arm value is Lipschitz in cellwise L1 distance with constant $1+1/epsilon$](goal). -/
lemma armCellValue_lipschitz {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (u v : Cell → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) (a : Fin 2) :
    |armCellValue epsilon a u - armCellValue epsilon a v| ≤
      (1 + epsilon⁻¹) * l1CellDistance u v := by
  have hmu := (armCellValue_bounds hepsilon u hu a)
  have hmv := (armCellValue_bounds hepsilon v hv a)
  have hMassU : 0 ≤ vectorMass u := hmu.1.trans hmu.2
  have hMassV : 0 ≤ vectorMass v := hmv.1.trans hmv.2
  have hinv : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have hcoef : 1 ≤ 1 + epsilon⁻¹ := by linarith
  by_cases hU : vectorMass u = 0
  · have hu0 := cell_eq_zero_of_vectorMass_eq_zero u hu hU
    have hdist := l1CellDistance_zero_left u v hu0 hv
    have huvalue : armCellValue epsilon a u = 0 := by rw [armCellValue, if_pos hU]
    rw [huvalue, zero_sub, abs_neg, abs_of_nonneg hmv.1, hdist]
    exact hmv.2.trans (by simpa using mul_le_mul_of_nonneg_right hcoef hMassV)
  · by_cases hV : vectorMass v = 0
    · have hv0 := cell_eq_zero_of_vectorMass_eq_zero v hv hV
      have hdist := l1CellDistance_zero_left v u hv0 hu
      have hvvalue : armCellValue epsilon a v = 0 := by rw [armCellValue, if_pos hV]
      rw [hvvalue, sub_zero, abs_of_nonneg hmu.1]
      have hsym : l1CellDistance u v = l1CellDistance v u := by
        simp [l1CellDistance, abs_sub_comm]
      rw [hsym, hdist]
      exact hmu.2.trans (by simpa using mul_le_mul_of_nonneg_right hcoef hMassU)
    · have hUpos : 0 < vectorMass u := lt_of_le_of_ne hMassU (Ne.symm hU)
      have hVpos : 0 < vectorMass v := lt_of_le_of_ne hMassV (Ne.symm hV)
      fin_cases a
      · simpa [scalarArmValue, armCellValue, vectorMass, vectorArmMass, l1CellDistance,
          Fintype.sum_prod_type, add_assoc] using
          (scalarArmValue_lipschitz_of_pos hepsilon
            (u (0, 0)) (u (0, 1)) (u (1, 0)) (u (1, 1))
            (v (0, 0)) (v (0, 1)) (v (1, 0)) (v (1, 1))
            (hu _) (hu _) (hu _) (hu _) (hv _) (hv _) (hv _) (hv _)
            (by simpa [vectorMass, vectorArmMass, add_assoc] using hUpos)
            (by simpa [vectorMass, vectorArmMass, add_assoc] using hVpos))
      · simpa [scalarArmValue, armCellValue, vectorMass, vectorArmMass, l1CellDistance,
          Fintype.sum_prod_type, add_assoc, add_comm, add_left_comm] using
          (scalarArmValue_lipschitz_of_pos hepsilon
            (u (1, 0)) (u (1, 1)) (u (0, 0)) (u (0, 1))
            (v (1, 0)) (v (1, 1)) (v (0, 0)) (v (0, 1))
            (hu _) (hu _) (hu _) (hu _) (hv _) (hv _) (hv _) (hv _)
            (by simpa [vectorMass, vectorArmMass, add_assoc, add_comm, add_left_comm] using hUpos)
            (by simpa [vectorMass, vectorArmMass, add_assoc, add_comm, add_left_comm] using hVpos))

-- @node: globalCellValue_lipschitz
/-- If [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the stated u condition holds](hyp:hu), and [the stated v condition holds](hyp:hv), then [global cell value is Lipschitz in cellwise L1 distance with constant $1+1/epsilon$](goal). -/
lemma globalCellValue_lipschitz {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (u v : Cell → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) :
    |globalCellValue epsilon u - globalCellValue epsilon v| ≤
      (1 + epsilon⁻¹) * l1CellDistance u v := by
  rw [globalCellValue]
  exact (abs_max_sub_max_le_max _ _ _ _).trans
    (max_le (armCellValue_lipschitz hepsilon u v hu hv 0)
      (armCellValue_lipschitz hepsilon u v hu hv 1))

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

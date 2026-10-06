module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedBranchAssembly
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedSignedCoverage

/-! # Uniform signed envelope for the perturbed seven-branch grid -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

noncomputable def perturbedBranchLowerShift (h a ε : ℝ) (c : ℤ → ℝ)
    (i : Fin 7) (k : ℤ) : ℝ :=
  (perturbedBranches h a ε (c k) i).lower -
    (perturbedBranches h a ε 0 i).lower

noncomputable def perturbedBranchUpperShift (h a ε : ℝ) (c : ℤ → ℝ)
    (i : Fin 7) (k : ℤ) : ℝ :=
  (perturbedBranches h a ε (c k) i).upper -
    (perturbedBranches h a ε 0 i).upper

noncomputable def perturbedBranchRealWeight (h a ε : ℝ) (c : ℤ → ℝ)
    (i : Fin 7) (k : ℤ) : ℝ :=
  h / (perturbedBranches h a ε (c k) i).slope

noncomputable def signedPerturbedGridDensity (h a ε : ℝ)
    (c : ℤ → ℝ) (y : ℝ) : ℝ :=
  ∑ i : Fin 7, ∑ k ∈ shiftedGridIndices h
      (perturbedBranches h a ε 0 i).lower
      (perturbedBranches h a ε 0 i).upper (ε * a)
      (perturbedBranchLowerShift h a ε c i)
      (perturbedBranchUpperShift h a ε c i) y,
    perturbedBranchRealWeight h a ε c i k

noncomputable def signedPerturbedGridError (h a ε : ℝ) : ℝ :=
  ∑ i : Fin 7, (
    h / (perturbedBranches h a ε 0 i).slope * (1 + 2 * (ε * a) / h) +
    (4 * ε * h / a) *
      (((perturbedBranches h a ε 0 i).upper -
          (perturbedBranches h a ε 0 i).lower) / h +
        2 * (ε * a) / h + 1))

noncomputable def reflectedCoefficient (q : ℕ) (c : ℕ → ℝ) (z : ℤ) : ℝ :=
  if 0 ≤ z ∧ z < q then c z.toNat
  else if -(q : ℤ) ≤ z ∧ z < 0 then -c (-z - 1).toNat
  else if (q : ℤ) ≤ z ∧ z < 2 * q then -c (2 * q - z - 1).toNat
  else 0

lemma reflectedCoefficient_ofNat {q k : ℕ} (c : ℕ → ℝ) (hk : k < q) :
    reflectedCoefficient q c (k : ℤ) = c k := by
  simp [reflectedCoefficient, hk]

lemma reflectedCoefficient_neg {q k : ℕ} (hq : 0 < q) (c : ℕ → ℝ)
    (hk : k < q) :
    reflectedCoefficient q c (-((k : ℤ)) - 1) = -c k := by
  have hkZ : (k : ℤ) < q := by exact_mod_cast hk
  have hlo : -(q : ℤ) ≤ -((k : ℤ)) - 1 := by omega
  have hneg : -((k : ℤ)) - 1 < 0 := by omega
  have hnfirst : ¬(0 ≤ -((k : ℤ)) - 1 ∧ -((k : ℤ)) - 1 < q) := by omega
  rw [reflectedCoefficient, if_neg hnfirst, if_pos ⟨hlo, hneg⟩]
  congr 2
  simp

lemma reflectedCoefficient_upper {q k : ℕ} (hq : 0 < q) (c : ℕ → ℝ)
    (hk : k < q) :
    reflectedCoefficient q c (2 * (q : ℤ) - (k : ℤ) - 1) = -c k := by
  have hkZ : (k : ℤ) < q := by exact_mod_cast hk
  have hlo : (q : ℤ) ≤ 2 * (q : ℤ) - (k : ℤ) - 1 := by
    omega
  have hhi : 2 * (q : ℤ) - (k : ℤ) - 1 < 2 * (q : ℤ) := by omega
  have hnfirst : ¬(0 ≤ 2 * (q : ℤ) - (k : ℤ) - 1 ∧
      2 * (q : ℤ) - (k : ℤ) - 1 < q) := by omega
  have hnsecond : ¬(-(q : ℤ) ≤ 2 * (q : ℤ) - (k : ℤ) - 1 ∧
      2 * (q : ℤ) - (k : ℤ) - 1 < 0) := by omega
  rw [reflectedCoefficient, if_neg hnfirst, if_neg hnsecond,
    if_pos ⟨hlo, hhi⟩]
  congr 2
  have hz : 2 * (q : ℤ) - (2 * (q : ℤ) - (k : ℤ) - 1) = (k : ℤ) + 1 := by ring
  rw [hz]
  simp

lemma reflectedCoefficient_mem_Icc {q : ℕ} {c : ℕ → ℝ}
    (hc : ∀ k, c k ∈ Set.Icc (-1 : ℝ) 1) (z : ℤ) :
    reflectedCoefficient q c z ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold reflectedCoefficient
  split
  next h => exact hc _
  next h =>
    split
    next h' =>
      have hz := hc (-z - 1).toNat
      exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
    next h' =>
      split
      next h'' =>
        have hz := hc (2 * (q : ℤ) - z - 1).toNat
        exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
      next h'' => norm_num

lemma mem_shiftedPerturbed_iff {h a ε y : ℝ} {c : ℤ → ℝ}
    (hh : 0 < h) (ha : 0 ≤ a) (hε0 : 0 ≤ ε)
    (hc : ∀ k, c k ∈ Set.Icc (-1 : ℝ) 1) (i : Fin 7) (k : ℤ) :
    k ∈ shiftedGridIndices h
        (perturbedBranches h a ε 0 i).lower
        (perturbedBranches h a ε 0 i).upper (ε * a)
        (perturbedBranchLowerShift h a ε c i)
        (perturbedBranchUpperShift h a ε c i) y ↔
      y ∈ Set.Icc
        ((k : ℝ) * h + (perturbedBranches h a ε (c k) i).lower)
        ((k : ℝ) * h + (perturbedBranches h a ε (c k) i).upper) := by
  have hdl := perturbedBranches_lower_displacement (h := h) ha hε0 (hc k) i
  have hdu := perturbedBranches_upper_displacement (h := h) ha hε0 (hc k) i
  rw [shiftedGridIndices_def, Finset.mem_filter]
  constructor
  · rintro ⟨hk, hmem⟩
    simpa [perturbedBranchLowerShift, perturbedBranchUpperShift] using hmem
  · intro hmem
    have hmem' : y ∈ Set.Icc
        ((k : ℝ) * h + (perturbedBranches h a ε 0 i).lower +
          perturbedBranchLowerShift h a ε c i k)
        ((k : ℝ) * h + (perturbedBranches h a ε 0 i).upper +
          perturbedBranchUpperShift h a ε c i k) := by
      simpa [perturbedBranchLowerShift, perturbedBranchUpperShift] using hmem
    have hdl' : -(ε * a) ≤ perturbedBranchLowerShift h a ε c i k := by
      simpa [perturbedBranchLowerShift] using (abs_le.mp hdl).1
    have hdu' : perturbedBranchUpperShift h a ε c i k ≤ ε * a := by
      simpa [perturbedBranchUpperShift] using (abs_le.mp hdu).2
    refine ⟨(mem_gridIntervalIndices_iff hh k).2 ?_, hmem'⟩
    constructor <;> linarith [hmem'.1, hmem'.2]

lemma perturbedBranches_relative_bounds {h a ε c : ℝ}
    (hh : 0 ≤ h) (ha : 0 ≤ a) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hc : c ∈ Set.Icc (-1 : ℝ) 1)
    (i : Fin 7) :
    -(2 * a) ≤ (perturbedBranches h a ε c i).lower ∧
      (perturbedBranches h a ε c i).upper ≤ h + 2 * a := by
  have heanon : 0 ≤ ε * a := mul_nonneg hε0 ha
  have heac_lo : -(ε * a) ≤ ε * a * c := by
    nlinarith [mul_le_mul_of_nonneg_left hc.1 heanon]
  have heac_hi : ε * a * c ≤ ε * a := by
    nlinarith [mul_le_mul_of_nonneg_left hc.2 heanon]
  have hea : ε * a ≤ a := by nlinarith
  fin_cases i <;> simp [perturbedBranches] <;> constructor <;> nlinarith

lemma shiftedPerturbed_index_bounds {q : ℕ} {h a ε y : ℝ} {c : ℤ → ℝ}
    (hq : 0 < q) (hhq : h = (q : ℝ)⁻¹)
    (ha : 0 ≤ a) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hc : ∀ k, c k ∈ Set.Icc (-1 : ℝ) 1)
    (ha12 : a ≤ 1 / 12) (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    (i : Fin 7) {k : ℤ}
    (hk : k ∈ shiftedGridIndices h
      (perturbedBranches h a ε 0 i).lower
      (perturbedBranches h a ε 0 i).upper (ε * a)
      (perturbedBranchLowerShift h a ε c i)
      (perturbedBranchUpperShift h a ε c i) y) :
    -(q : ℤ) ≤ k ∧ k < 2 * (q : ℤ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : 0 < h := by rw [hhq]; positivity
  have hqh : (q : ℝ) * h = 1 := by rw [hhq]; exact mul_inv_cancel₀ hqR.ne'
  have hmem := (mem_shiftedPerturbed_iff hh ha hε0 hc i k).mp hk
  have hb := perturbedBranches_relative_bounds (h := h) hh.le ha hε0 hε (hc k) i
  constructor
  · by_contra hn
    have hkz : k ≤ -(q : ℤ) - 1 := by omega
    have hkR : (k : ℝ) ≤ -(q : ℝ) - 1 := by exact_mod_cast hkz
    have : (k : ℝ) * h +
        (perturbedBranches h a ε (c k) i).upper < 0 := by
      nlinarith [mul_le_mul_of_nonneg_right hkR hh.le]
    linarith [hmem.2, hy.1]
  · by_contra hn
    have hkz : 2 * (q : ℤ) ≤ k := by omega
    have hkR : 2 * (q : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkz
    have : 1 < (k : ℝ) * h +
        (perturbedBranches h a ε (c k) i).lower := by
      nlinarith [mul_le_mul_of_nonneg_right hkR hh.le]
    linarith [hmem.1, hy.2]

/-- The all-integer perturbed grid has density uniformly close to one even
when every cell carries an unrelated signed transverse coefficient. -/
lemma signedPerturbedGridDensity_error {h a ε : ℝ} (c : ℤ → ℝ)
    (hh : 0 < h) (ha : 0 ≤ a) (hscale : 4 ≤ a / h)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 64)
    (hc : ∀ k, c k ∈ Set.Icc (-1 : ℝ) 1) (y : ℝ) :
    |signedPerturbedGridDensity h a ε c y - 1| ≤
      signedPerturbedGridError h a ε := by
  have ha_pos : 0 < a := by
    have := (le_div_iff₀ hh).mp hscale
    linarith
  have hD : 0 ≤ ε * a := mul_nonneg hε0 ha
  have hs (i : Fin 7) : 0 < (perturbedBranches h a ε 0 i).slope := by
    have hlo := perturbedBranches_slope_lower hh hscale hε0 hε
      (by exact ⟨by norm_num, by norm_num⟩ : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1) i
    linarith
  have hr (i : Fin 7) : 0 ≤ (perturbedBranches h a ε 0 i).domainLength := by
    fin_cases i <;> norm_num [perturbedBranches]
  have hwidth (i : Fin 7) :
      2 * (ε * a) ≤ (perturbedBranches h a ε 0 i).upper -
        (perturbedBranches h a ε 0 i).lower := by
    have ha4 : 4 * h ≤ a := (le_div_iff₀ hh).mp hscale
    fin_cases i <;> simp [perturbedBranches] <;> nlinarith
  have hlen (i : Fin 7) :
      (perturbedBranches h a ε 0 i).upper -
          (perturbedBranches h a ε 0 i).lower =
        (perturbedBranches h a ε 0 i).slope *
          (perturbedBranches h a ε 0 i).domainLength := by
    fin_cases i <;> simp [perturbedBranches] <;> ring
  have hdl (i : Fin 7) (k : ℤ) :
      |perturbedBranchLowerShift h a ε c i k| ≤ ε * a := by
    exact perturbedBranches_lower_displacement ha hε0 (hc k) i
  have hdu (i : Fin 7) (k : ℤ) :
      |perturbedBranchUpperShift h a ε c i k| ≤ ε * a := by
    exact perturbedBranches_upper_displacement ha hε0 (hc k) i
  have hw (i : Fin 7) (k : ℤ) :
      |perturbedBranchRealWeight h a ε c i k -
        h / (perturbedBranches h a ε 0 i).slope| ≤ 4 * ε * h / a := by
    exact perturbedBranches_weight_displacement hh hscale hε0 hε (hc k) i
  have hi (i : Fin 7) :
      |(∑ k ∈ shiftedGridIndices h
          (perturbedBranches h a ε 0 i).lower
          (perturbedBranches h a ε 0 i).upper (ε * a)
          (perturbedBranchLowerShift h a ε c i)
          (perturbedBranchUpperShift h a ε c i) y,
          perturbedBranchRealWeight h a ε c i k) -
        (perturbedBranches h a ε 0 i).domainLength| ≤
        h / (perturbedBranches h a ε 0 i).slope * (1 + 2 * (ε * a) / h) +
        (4 * ε * h / a) *
          (((perturbedBranches h a ε 0 i).upper -
              (perturbedBranches h a ε 0 i).lower) / h +
            2 * (ε * a) / h + 1) := by
    exact weighted_shiftedGridIndices_variable_error hh hD (hs i) (hr i)
      (by positivity) (hwidth i) (hlen i)
      (perturbedBranchLowerShift h a ε c i)
      (perturbedBranchUpperShift h a ε c i)
      (perturbedBranchRealWeight h a ε c i)
      (hdl i) (hdu i) (hw i)
  have hmass : (∑ i : Fin 7,
      (perturbedBranches h a ε 0 i).domainLength) = 1 := by
    norm_num [Fin.sum_univ_succ, perturbedBranches]
  rw [signedPerturbedGridDensity, ← hmass, ← Finset.sum_sub_distrib]
  rw [signedPerturbedGridError]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => hi i)

lemma signedPerturbedGridError_le {h a ε : ℝ}
    (hh : 0 < h) (ha : 0 ≤ a) (hscale : 4 ≤ a / h)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 64) :
    signedPerturbedGridError h a ε ≤ 4 * h / a + 24 * ε := by
  have ha_pos : 0 < a := by
    have := (le_div_iff₀ hh).mp hscale
    linarith
  have hs3 (i : Fin 7) :
      3 * a ≤ (perturbedBranches h a ε 0 i).slope :=
    perturbedBranches_slope_lower hh hscale hε0 hε
      (by exact ⟨by norm_num, by norm_num⟩ : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1) i
  have hs (i : Fin 7) : 0 < (perturbedBranches h a ε 0 i).slope :=
    lt_of_lt_of_le (by positivity : 0 < 3 * a) (hs3 i)
  have hfrac (i : Fin 7) :
      h / (perturbedBranches h a ε 0 i).slope ≤ h / (3 * a) :=
    div_le_div_of_nonneg_left hh.le (by positivity) (hs3 i)
  have hfac : 0 ≤ 1 + 2 * (ε * a) / h := by positivity
  have hE : 0 ≤ 4 * ε * h / a := by positivity
  rw [signedPerturbedGridError]
  calc
    (∑ i : Fin 7, _) ≤ ∑ i : Fin 7, (
        (h / (3 * a)) * (1 + 2 * (ε * a) / h) +
        (4 * ε * h / a) *
          (((perturbedBranches h a ε 0 i).upper -
              (perturbedBranches h a ε 0 i).lower) / h +
            2 * (ε * a) / h + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact add_le_add (mul_le_mul_of_nonneg_right (hfrac i) hfac) le_rfl
    _ = 7 * ((h / (3 * a)) * (1 + 2 * (ε * a) / h)) +
        (4 * ε * h / a) * (4 * a / h + 7 * (2 * (ε * a) / h + 1)) := by
      simp [Fin.sum_univ_succ, perturbedBranches]
      ring
    _ ≤ 4 * h / a + 24 * ε := by
      field_simp [hh.ne', ha_pos.ne']
      nlinarith [mul_nonneg hε0 hh.le, mul_nonneg hε0 ha]

/-- Reindex the unreflected finite cells as the nonnegative middle block of
the all-integer signed grid. -/
lemma middle_block_reindex {q : ℕ} {h a ε y : ℝ} (c : ℕ → ℝ)
    (hh : 0 < h) (ha : 0 ≤ a) (hε0 : 0 ≤ ε)
    (hc : ∀ k, c k ∈ Set.Icc (-1 : ℝ) 1) (i : Fin 7) :
    (∑ k ∈ Finset.range q,
      (Set.Icc
        ((k : ℝ) * h + (perturbedBranches h a ε (c k) i).lower)
        ((k : ℝ) * h + (perturbedBranches h a ε (c k) i).upper)).indicator
          (fun _ => h / (perturbedBranches h a ε (c k) i).slope) y) =
      ∑ z ∈ (shiftedGridIndices h
        (perturbedBranches h a ε 0 i).lower
        (perturbedBranches h a ε 0 i).upper (ε * a)
        (perturbedBranchLowerShift h a ε (reflectedCoefficient q c) i)
        (perturbedBranchUpperShift h a ε (reflectedCoefficient q c) i) y).filter
          (fun z : ℤ => 0 ≤ z ∧ z < q),
        perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i z := by
  classical
  simp_rw [Set.indicator_apply]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun (k : ℕ) _ => (k : ℤ))
  · intro k hk
    have hk0 := (Finset.mem_filter.mp hk).2
    have hkq := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_shiftedPerturbed_iff hh ha hε0
        (reflectedCoefficient_mem_Icc hc) i (k : ℤ)).2
      simpa [reflectedCoefficient_ofNat c hkq] using hk0
    · exact ⟨by positivity, by exact_mod_cast hkq⟩
  · intro k₁ hk₁ k₂ hk₂ heq
    exact Int.ofNat_inj.mp heq
  · intro z hz
    have hzfilter := Finset.mem_filter.mp hz
    have hznonneg := hzfilter.2.1
    have hzq := hzfilter.2.2
    let k := z.toNat
    have hkcast : (k : ℤ) = z := Int.toNat_of_nonneg hznonneg
    have hkqZ : (k : ℤ) < q := by simpa [hkcast] using hzq
    have hkq : k < q := by exact_mod_cast hkqZ
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkq, ?_⟩, hkcast⟩
    have hzmem := (mem_shiftedPerturbed_iff hh ha hε0
      (reflectedCoefficient_mem_Icc hc) i z).mp hzfilter.1
    have hcoeff : reflectedCoefficient q c z = c k := by
      rw [← hkcast]
      exact reflectedCoefficient_ofNat c hkq
    have hkcastR : (k : ℝ) = (z : ℝ) := by exact_mod_cast hkcast
    simpa [k, hcoeff, hkcastR] using hzmem
  · intro k hk
    have hkq := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    simp [perturbedBranchRealWeight, reflectedCoefficient_ofNat c hkq]

/-- Reindex the left reflected copy as the negative integer block. -/
lemma negative_block_reindex {q : ℕ} {h a ε y : ℝ} (c : ℕ → ℝ)
    (hq : 0 < q) (hh : 0 < h) (ha : 0 ≤ a) (hε0 : 0 ≤ ε)
    (hc : ∀ k, c k ∈ Set.Icc (-1 : ℝ) 1) (i : Fin 7) :
    (∑ k ∈ Finset.range q,
      (Set.Icc
        ((k : ℝ) * h + (perturbedBranches h a ε (c k) i).lower)
        ((k : ℝ) * h + (perturbedBranches h a ε (c k) i).upper)).indicator
          (fun _ => h / (perturbedBranches h a ε (c k) i).slope) (-y)) =
      ∑ z ∈ (shiftedGridIndices h
        (perturbedBranches h a ε 0 i.rev).lower
        (perturbedBranches h a ε 0 i.rev).upper (ε * a)
        (perturbedBranchLowerShift h a ε (reflectedCoefficient q c) i.rev)
        (perturbedBranchUpperShift h a ε (reflectedCoefficient q c) i.rev) y).filter
          (fun z : ℤ => -(q : ℤ) ≤ z ∧ z < 0),
        perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i.rev z := by
  classical
  simp_rw [Set.indicator_apply]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun (k : ℕ) _ => -((k : ℤ)) - 1)
  · intro k hk
    have hkmem := (Finset.mem_filter.mp hk).2
    have hkq := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_shiftedPerturbed_iff hh ha hε0
        (reflectedCoefficient_mem_Icc hc) i.rev (-((k : ℤ)) - 1)).2
      rw [reflectedCoefficient_neg hq c hkq,
        perturbedBranches_reflect_lower, perturbedBranches_reflect_upper]
      have hzR : ((-((k : ℤ)) - 1 : ℤ) : ℝ) = -(k : ℝ) - 1 := by
        push_cast
        rfl
      rw [hzR]
      constructor <;> nlinarith [hkmem.1, hkmem.2]
    · constructor
      · have hkqZ : (k : ℤ) < q := by exact_mod_cast hkq
        omega
      · omega
  · intro k₁ hk₁ k₂ hk₂ heq
    omega
  · intro z hz
    have hzfilter := Finset.mem_filter.mp hz
    have hzlo := hzfilter.2.1
    have hzneg := hzfilter.2.2
    let k := (-z - 1).toNat
    have hkcast : (k : ℤ) = -z - 1 := Int.toNat_of_nonneg (by omega)
    have hkqZ : (k : ℤ) < q := by omega
    have hkq : k < q := by exact_mod_cast hkqZ
    have hzform : -((k : ℤ)) - 1 = z := by omega
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkq, ?_⟩, hzform⟩
    have hzmem := (mem_shiftedPerturbed_iff hh ha hε0
      (reflectedCoefficient_mem_Icc hc) i.rev z).mp hzfilter.1
    have hcoeff : reflectedCoefficient q c z = -c k := by
      rw [← hzform]
      exact reflectedCoefficient_neg hq c hkq
    rw [hcoeff, perturbedBranches_reflect_lower,
      perturbedBranches_reflect_upper] at hzmem
    have hkcastR : (k : ℝ) = (-z - 1 : ℤ) := by exact_mod_cast hkcast
    have hzformR : -(k : ℝ) - 1 = (z : ℝ) := by exact_mod_cast hzform
    rw [← hzformR] at hzmem
    constructor <;> nlinarith [hzmem.1, hzmem.2]
  · intro k hk
    have hkq := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    simp [perturbedBranchRealWeight, reflectedCoefficient_neg hq c hkq,
      perturbedBranches_reflect_slope]

/-- Reindex the right reflected copy as the upper integer block. -/
lemma upper_block_reindex {q : ℕ} {h a ε y : ℝ} (c : ℕ → ℝ)
    (hq : 0 < q) (hhq : h = (q : ℝ)⁻¹) (ha : 0 ≤ a) (hε0 : 0 ≤ ε)
    (hc : ∀ k, c k ∈ Set.Icc (-1 : ℝ) 1) (i : Fin 7) :
    (∑ k ∈ Finset.range q,
      (Set.Icc
        ((k : ℝ) * h + (perturbedBranches h a ε (c k) i).lower)
        ((k : ℝ) * h + (perturbedBranches h a ε (c k) i).upper)).indicator
          (fun _ => h / (perturbedBranches h a ε (c k) i).slope) (2 - y)) =
      ∑ z ∈ (shiftedGridIndices h
        (perturbedBranches h a ε 0 i.rev).lower
        (perturbedBranches h a ε 0 i.rev).upper (ε * a)
        (perturbedBranchLowerShift h a ε (reflectedCoefficient q c) i.rev)
        (perturbedBranchUpperShift h a ε (reflectedCoefficient q c) i.rev) y).filter
          (fun z : ℤ => (q : ℤ) ≤ z ∧ z < 2 * q),
        perturbedBranchRealWeight h a ε (reflectedCoefficient q c) i.rev z := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : 0 < h := by rw [hhq]; positivity
  have hqh : (q : ℝ) * h = 1 := by rw [hhq]; exact mul_inv_cancel₀ hqR.ne'
  simp_rw [Set.indicator_apply]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun (k : ℕ) _ => 2 * (q : ℤ) - (k : ℤ) - 1)
  · intro k hk
    have hkmem := (Finset.mem_filter.mp hk).2
    have hkq := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_shiftedPerturbed_iff hh ha hε0
        (reflectedCoefficient_mem_Icc hc) i.rev
          (2 * (q : ℤ) - (k : ℤ) - 1)).2
      rw [reflectedCoefficient_upper hq c hkq,
        perturbedBranches_reflect_lower, perturbedBranches_reflect_upper]
      have hzR : ((2 * (q : ℤ) - (k : ℤ) - 1 : ℤ) : ℝ) =
          2 * (q : ℝ) - (k : ℝ) - 1 := by push_cast; rfl
      rw [hzR]
      constructor <;> nlinarith [hkmem.1, hkmem.2]
    · have hkqZ : (k : ℤ) < q := by exact_mod_cast hkq
      constructor <;> omega
  · intro k₁ hk₁ k₂ hk₂ heq
    omega
  · intro z hz
    have hzfilter := Finset.mem_filter.mp hz
    have hzlo := hzfilter.2.1
    have hzhi := hzfilter.2.2
    let k := (2 * (q : ℤ) - z - 1).toNat
    have hkcast : (k : ℤ) = 2 * (q : ℤ) - z - 1 :=
      Int.toNat_of_nonneg (by omega)
    have hkqZ : (k : ℤ) < q := by omega
    have hkq : k < q := by exact_mod_cast hkqZ
    have hzform : 2 * (q : ℤ) - (k : ℤ) - 1 = z := by omega
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkq, ?_⟩, hzform⟩
    have hzmem := (mem_shiftedPerturbed_iff hh ha hε0
      (reflectedCoefficient_mem_Icc hc) i.rev z).mp hzfilter.1
    have hcoeff : reflectedCoefficient q c z = -c k := by
      rw [← hzform]
      exact reflectedCoefficient_upper hq c hkq
    rw [hcoeff, perturbedBranches_reflect_lower,
      perturbedBranches_reflect_upper] at hzmem
    have hzformR : 2 * (q : ℝ) - (k : ℝ) - 1 = (z : ℝ) := by
      exact_mod_cast hzform
    rw [← hzformR] at hzmem
    constructor <;> nlinarith [hzmem.1, hzmem.2]
  · intro k hk
    have hkq := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    simp [perturbedBranchRealWeight, reflectedCoefficient_upper hq c hkq,
      perturbedBranches_reflect_slope]

end CausalSmith.Experimentation.PilotscorePairingFrontier

private noncomputable def cutIndicator (a b x : ℝ) : ℝ :=
  if a ≤ x ∧ x < b then 1 else 0

private theorem cutIndicator_eq_indicator (a b : ℝ) :
    cutIndicator a b = (Ico a b).indicator (1 : ℝ → ℝ) := by
  funext x
  simp [cutIndicator, Set.indicator_apply, Set.mem_Ico]

private theorem cutIndicator_integrable (a b : ℝ) :
    Integrable (cutIndicator a b) volume := by
  rw [cutIndicator_eq_indicator]
  exact (integrableOn_const (μ := volume) (s := Ico a b) (by simp)).integrable_indicator
    measurableSet_Ico

private theorem integral_cutIndicator (a b : ℝ) :
    (∫ x, cutIndicator a b x) = max (b - a) 0 := by
  rw [cutIndicator_eq_indicator, integral_indicator_one measurableSet_Ico,
    Real.volume_real_Ico]

private theorem signedCut_eq (a b x : ℝ) :
    (if a ≤ x ∧ x < b then (1 : ℝ)
      else if b ≤ x ∧ x < a then -1 else 0) =
      cutIndicator a b x - cutIndicator b a x := by
  unfold cutIndicator
  split_ifs with h₁ h₂ h₃ h₄ <;> simp_all <;> linarith

private theorem unsignedCut_eq (a b x : ℝ) :
    (if a ≤ x ∧ x < b ∨ b ≤ x ∧ x < a then (1 : ℝ) else 0) =
      cutIndicator a b x + cutIndicator b a x := by
  unfold cutIndicator
  split_ifs with h₁ h₂ h₃ <;> simp_all <;> linarith

private theorem signedPair_integrable (m a b : ℝ) :
    Integrable (fun x => m *
      (if a ≤ x ∧ x < b then (1 : ℝ)
        else if b ≤ x ∧ x < a then -1 else 0)) volume := by
  simp_rw [signedCut_eq]
  exact ((cutIndicator_integrable a b).sub (cutIndicator_integrable b a)).const_mul m

private theorem unsignedPair_integrable (m a b : ℝ) :
    Integrable (fun x => m *
      (if a ≤ x ∧ x < b ∨ b ≤ x ∧ x < a then (1 : ℝ) else 0)) volume := by
  simp_rw [unsignedCut_eq]

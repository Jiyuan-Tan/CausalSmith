open scoped BigOperators ENNReal

/-- For [a positive finite sample size](hyp:hN), [a finite family of measurable,
integrable statistics](hyp:hgmeas,hgint) under [a probability law](hyp:P), and
[nonnegative coordinatewise envelopes and variance proxies](hyp:hb,hsigma2), suppose
[each positive coordinate threshold](hyp:heta) is compared with a statistic whose
[centered values are bounded by its envelope](hyp:henvelope) and whose [centered second
moment is bounded by its variance proxy](hyp:hvariance).  Then [the probability that any
coordinate sum differs from its population total by at least its own threshold is at most
the sum of the corresponding two-sided Bernstein tails](goal). -/
-- Proof route: apply `bernstein_abs_ge` to `iidSample_infinitePi P` at threshold
-- `eta a / N` with variance parameter `sqrt (sigma2 a)`, transport the first `N`
-- coordinates using `iidSample_finN_pushforward`, then take a finite union bound.
theorem iid_sum_bernstein_union_bound
    {N : ℕ} {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (g : ι → X → ℝ) (hgmeas : ∀ a, Measurable (g a))
    (hgint : ∀ a, Integrable (g a) P)
    (b sigma2 eta : ι → ℝ)
    (hb : ∀ a, 0 ≤ b a) (hsigma2 : ∀ a, 0 ≤ sigma2 a)
    (heta : ∀ a, 0 < eta a) (hN : 0 < N)
    (henvelope : ∀ a, ∀ᵐ x ∂P, |g a x - ∫ y, g a y ∂P| ≤ b a)
    (hvariance : ∀ a, ∫ x, (g a x - ∫ y, g a y ∂P) ^ 2 ∂P ≤ sigma2 a) :
    (Measure.pi (fun _ : Fin N ↦ P)).real
        {omega : Fin N → X |
          ∃ a, eta a ≤ |(∑ i, g a (omega i)) - (N : ℝ) * ∫ x, g a x ∂P|} ≤
      ∑ a, 2 * Real.exp
        (-(eta a) ^ 2 /
          (2 * (2 * (N : ℝ) * sigma2 a + b a * eta a))) := by
  let S := Causalean.Stat.iidSample_infinitePi P
  let μInf : Measure (ℕ → X) := Measure.infinitePi (fun _ : ℕ => P)
  let Ψ : (ℕ → X) → (Fin N → X) := fun omega i => S.Z i omega
  let E : ι → Set (Fin N → X) := fun a =>
    {omega | eta a ≤ |(∑ i, g a (omega i)) - (N : ℝ) * ∫ x, g a x ∂P|}
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := ne_of_gt hnR
  have hΨ : Measurable Ψ := Causalean.Stat.iidSample_finN_measurable S N
  have hE : ∀ a, MeasurableSet (E a) := by
    intro a
    change MeasurableSet
      ((fun omega : Fin N → X =>
        |(∑ i, g a (omega i)) - (N : ℝ) * ∫ x, g a x ∂P|) ⁻¹' Set.Ici (eta a))
    exact measurableSet_Ici.preimage <| (Measurable.abs <| Measurable.sub
      (Finset.measurable_sum Finset.univ fun i _ =>
        (hgmeas a).comp (measurable_pi_apply i)) measurable_const)
  have hpush : Measure.map Ψ μInf = Measure.pi (fun _ : Fin N => P) := by
    exact Causalean.Stat.iidSample_finN_pushforward S N
  have htransport : ∀ a, (Measure.pi (fun _ : Fin N => P)).real (E a) =
      μInf.real (Ψ ⁻¹' E a) := by
    intro a
    simp only [measureReal_def]
    rw [← hpush, Measure.map_apply hΨ (hE a)]
  have hpull : ∀ a, Ψ ⁻¹' E a =
      {omega | eta a / (N : ℝ) ≤
        |S.sampleMean (g a) N omega - ∫ x, g a x ∂P|} := by
    intro a
    ext omega
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    change eta a ≤
        |(∑ i : Fin N, g a (S.Z i omega)) -
          (N : ℝ) * ∫ x, g a x ∂P| ↔ _
    rw [Causalean.Stat.IIDSample.sampleMean, ← Fin.sum_univ_eq_sum_range]
    let T : ℝ := ∑ i : Fin N, g a (S.Z i omega)
    let m : ℝ := ∫ x, g a x ∂P
    change eta a ≤ |T - (N : ℝ) * m| ↔
      eta a / (N : ℝ) ≤ |(N : ℝ)⁻¹ * T - m|
    have hcenter : (N : ℝ)⁻¹ * T - m = (T - (N : ℝ) * m) / (N : ℝ) := by
      field_simp
    rw [hcenter, abs_div, abs_of_pos hnR, div_le_div_iff_of_pos_right hnR]
  have hcoord : ∀ a, (Measure.pi (fun _ : Fin N => P)).real (E a) ≤
      2 * Real.exp
        (-(eta a) ^ 2 /
          (2 * (2 * (N : ℝ) * sigma2 a + b a * eta a))) := by
    intro a
    rw [htransport a, hpull a]
    have htail := Causalean.Stat.Concentration.bernstein_abs_ge S
      (hgmeas a) (hgint a) (hb a) (henvelope a)
      (σ := Real.sqrt (sigma2 a))
      (hvar := by rw [Real.sq_sqrt (hsigma2 a)]; exact hvariance a)
      N hN (div_nonneg (le_of_lt (heta a)) (le_of_lt hnR))
    rw [Real.sq_sqrt (hsigma2 a)] at htail
    convert htail using 1
    field_simp [hn0]
  rw [show {omega : Fin N → X |
      ∃ a, eta a ≤ |(∑ i, g a (omega i)) - (N : ℝ) * ∫ x, g a x ∂P|} =
      ⋃ a, E a by simp [E, Set.ofPred_exists]]
  simp only [measureReal_def]
  rw [← hpush, Measure.map_apply hΨ (MeasurableSet.iUnion hE)]
  rw [Set.preimage_iUnion]
  calc
    μInf.real (⋃ a, Ψ ⁻¹' E a)
        ≤ ∑ a, μInf.real (Ψ ⁻¹' E a) := by
          rw [measureReal_def]
          calc
            (μInf (⋃ a, Ψ ⁻¹' E a)).toReal
                ≤ (∑' a, μInf (Ψ ⁻¹' E a)).toReal := by
                  apply ENNReal.toReal_mono
                  · rw [tsum_fintype]
                    exact (ENNReal.sum_ne_top.mpr fun a _ => measure_ne_top μInf _)
                  · exact measure_iUnion_le _
            _ = ∑ a, μInf.real (Ψ ⁻¹' E a) := by
                  rw [tsum_fintype, ENNReal.toReal_sum]
                  · simp only [measureReal_def]
                  · exact fun a _ => measure_ne_top μInf _
    _ = ∑ a, (Measure.pi (fun _ : Fin N => P)).real (E a) := by
          apply Finset.sum_congr rfl
          intro a _
          exact (htransport a).symm
    _ ≤ ∑ a, 2 * Real.exp
        (-(eta a) ^ 2 /
          (2 * (2 * (N : ℝ) * sigma2 a + b a * eta a))) :=
      Finset.sum_le_sum fun a _ => hcoord a

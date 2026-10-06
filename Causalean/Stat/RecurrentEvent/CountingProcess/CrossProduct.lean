module
public import Causalean.Stat.RecurrentEvent.CountingProcess.CrossPrefix
public import Causalean.Stat.RecurrentEvent.CountingProcess.IntegralSquare
public import Causalean.Stat.RecurrentEvent.CountingProcess.PathwiseStop

/-!
A pathwise product formula for two compensated one-jump censor integrals.
Distinct censor times remove the common-jump term; the remaining terms use
strict-past compensated integrals, which are predictable.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- When [the horizon u is nonnegative](hyp:hu) and [two functions f and g are integrable on the
interval from 0 to u](hyp:hf,hg), [the product of their integrals over that interval equals the
integral of the running integral of f times g plus the integral of the running integral of g
times f](goal). -/
private theorem integral_prefix_mul_bilinear (f g : ℝ → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hf : Integrable f (volume.restrict (Set.Icc 0 u)))
    (hg : Integrable g (volume.restrict (Set.Icc 0 u))) :
    (∫ s in Set.Icc 0 u, f s ∂volume) *
      (∫ s in Set.Icc 0 u, g s ∂volume) =
      (∫ s in Set.Icc 0 u,
        (∫ t in Set.Icc 0 s, f t ∂volume) * g s ∂volume) +
      (∫ s in Set.Icc 0 u,
        (∫ t in Set.Icc 0 s, g t ∂volume) * f s ∂volume) := by
  let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t
  let G : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, g t
  have hfi : IntervalIntegrable f volume 0 u :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hu).2 hf
  have hgi : IntervalIntegrable g volume 0 u :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hu).2 hg
  have hF : AbsolutelyContinuousOnInterval F 0 u :=
    hfi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hG : AbsolutelyContinuousOnInterval G 0 u :=
    hgi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hderivF := hfi.ae_hasDerivAt_integral
  have hderivG := hgi.ae_hasDerivAt_integral
  have hprod := hF.integral_deriv_mul_eq_sub hG
  have heq : (∫ s in (0 : ℝ)..u, deriv F s * G s + F s * deriv G s) =
      (∫ s in (0 : ℝ)..u,
        (∫ t in Set.Icc 0 s, f t ∂volume) * g s +
        (∫ t in Set.Icc 0 s, g t ∂volume) * f s) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderivF, hderivG] with s hfs hgs hsmem
    have hsIcc : s ∈ Set.Icc (0 : ℝ) u := by
      simpa [Set.uIcc_of_le hu] using (Set.uIoc_subset_uIcc hsmem)
    have hdsF : deriv F s = f s :=
      (hfs (by simpa [Set.uIcc_of_le hu] using hsIcc) 0 (by simp)).deriv
    have hdsG : deriv G s = g s :=
      (hgs (by simpa [Set.uIcc_of_le hu] using hsIcc) 0 (by simp)).deriv
    have hprefixF : F s = ∫ t in Set.Icc 0 s, f t ∂volume := by
      dsimp [F]
      rw [intervalIntegral.integral_of_le hsIcc.1, ← integral_Icc_eq_integral_Ioc]
    have hprefixG : G s = ∫ t in Set.Icc 0 s, g t ∂volume := by
      dsimp [G]
      rw [intervalIntegral.integral_of_le hsIcc.1, ← integral_Icc_eq_integral_Ioc]
    rw [hdsF, hdsG, hprefixF, hprefixG]
    ring
  rw [heq] at hprod
  have hzeroF : F 0 = 0 := by simp [F]
  have hzeroG : G 0 = 0 := by simp [G]
  have hfinalF : F u = ∫ s in Set.Icc 0 u, f s ∂volume := by
    dsimp [F]
    rw [intervalIntegral.integral_of_le hu, ← integral_Icc_eq_integral_Ioc]
  have hfinalG : G u = ∫ s in Set.Icc 0 u, g s ∂volume := by
    dsimp [G]
    rw [intervalIntegral.integral_of_le hu, ← integral_Icc_eq_integral_Ioc]
  have hfg : Integrable
      (fun s => (∫ t in Set.Icc 0 s, f t ∂volume) * g s)
      (volume.restrict (Set.Icc 0 u)) := by
    have h : Integrable (fun s => F s * g s)
        (volume.restrict (Set.Icc 0 u)) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hu).1
      (hgi.continuousOn_mul (by simpa [Set.uIcc_of_le hu] using hF.continuousOn))
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    dsimp only [F]
    rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
  have hgf : Integrable
      (fun s => (∫ t in Set.Icc 0 s, g t ∂volume) * f s)
      (volume.restrict (Set.Icc 0 u)) := by
    have h : Integrable (fun s => G s * f s)
        (volume.restrict (Set.Icc 0 u)) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hu).1
      (hfi.continuousOn_mul (by simpa [Set.uIcc_of_le hu] using hG.continuousOn))
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    dsimp only [G]
    rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
  rw [hfinalF, hfinalG, hzeroF, hzeroG] at hprod
  rw [intervalIntegral.integral_of_le hu, ← integral_Icc_eq_integral_Ioc,
    integral_add hfg hgf] at hprod
  simpa only [zero_mul, sub_zero] using hprod.symm

/-- For [a cutoff c between 0 and the horizon u](hyp:hc,hu) and [a function integrable on the
interval from 0 to u](hyp:hf), [integrating the function over the times in that interval strictly
after c gives its integral up to u minus its integral up to c](goal). -/
private theorem integral_strict_tail (f : ℝ → ℝ) (c u : ℝ)
    (hc : 0 ≤ c) (hu : c ≤ u)
    (hf : Integrable f (volume.restrict (Set.Icc 0 u))) :
    (∫ s in Set.Icc 0 u, if c < s then f s else 0 ∂volume) =
      (∫ s in Set.Icc 0 u, f s ∂volume) -
        ∫ s in Set.Icc 0 c, f s ∂volume := by
  have hfc : Integrable f (volume.restrict (Set.Icc 0 c)) :=
    IntegrableOn.mono_set hf (Set.Icc_subset_Icc_right hu)
  have hfi : IntervalIntegrable f volume 0 u :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (le_trans hc hu)).2 hf
  have hfci : IntervalIntegrable f volume 0 c :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hc).2 hfc
  have htail := intervalIntegral.integral_interval_sub_left hfi hfci
  rw [intervalIntegral.integral_of_le (le_trans hc hu),
    intervalIntegral.integral_of_le hc,
    intervalIntegral.integral_of_le hu] at htail
  simp only [← integral_Icc_eq_integral_Ioc] at htail
  calc
    (∫ s in Set.Icc 0 u, if c < s then f s else 0 ∂volume) =
        ∫ s in Set.Icc 0 u, (Set.Ioi c).indicator f s ∂volume := by
          congr 1
    _ = ∫ s in Set.Icc 0 u ∩ Set.Ioi c, f s ∂volume :=
      setIntegral_indicator measurableSet_Ioi
    _ = ∫ s in Set.Ioc c u, f s ∂volume := by
      have hs : Set.Icc 0 u ∩ Set.Ioi c = Set.Ioc c u := by
        ext s
        simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi, Set.mem_Ioc]
        constructor
        · intro h
          exact ⟨h.2, h.1.2⟩
        · intro h
          exact ⟨⟨le_trans hc (le_of_lt h.1), h.2⟩, h.1⟩
      rw [hs]
    _ = ∫ s in Set.Icc c u, f s ∂volume := by
      rw [integral_Icc_eq_integral_Ioc]
    _ = _ := htail.symm

private theorem integral_event_tail (f : ℝ → ℝ) (a c d u : ℝ)
    (hc : 0 ≤ c) (hf : Integrable f (volume.restrict (Set.Icc 0 u))) :
    (∫ s in Set.Icc 0 u, (if c < s ∧ c < d then a else 0) * f s ∂volume) =
      if c ≤ u ∧ c < d then
        a * ((∫ s in Set.Icc 0 u, f s ∂volume) -
          ∫ s in Set.Icc 0 c, f s ∂volume)
      else 0 := by
  by_cases hcd : c < d
  · by_cases hcu : c ≤ u
    · have hcalc :
          (∫ s in Set.Icc 0 u, (if c < s ∧ c < d then a else 0) * f s ∂volume) =
            a * ((∫ s in Set.Icc 0 u, f s ∂volume) -
              ∫ s in Set.Icc 0 c, f s ∂volume) := by
        calc
        (∫ s in Set.Icc 0 u, (if c < s ∧ c < d then a else 0) * f s ∂volume) =
            ∫ s in Set.Icc 0 u, a * (if c < s then f s else 0) ∂volume := by
              congr 1
              funext s
              by_cases hcs : c < s <;> simp [hcs, hcd]
        _ = a * ∫ s in Set.Icc 0 u, (if c < s then f s else 0) ∂volume :=
          by rw [integral_const_mul]
        _ = _ := by rw [integral_strict_tail f c u hc hcu hf]
      simpa [hcu, hcd] using hcalc
    · have hzero : (∫ s in Set.Icc 0 u,
          (if c < s ∧ c < d then a else 0) * f s ∂volume) = 0 := by
        calc
          _ = ∫ s in Set.Icc 0 u, (0 : ℝ) ∂volume := by
            apply setIntegral_congr_fun measurableSet_Icc
            intro s hs
            have hns : ¬ c < s := not_lt.mpr (le_trans hs.2 (le_of_lt (lt_of_not_ge hcu)))
            simp [hns]
          _ = 0 := by simp
      simpa [hcu] using hzero
  · simp [hcd]

private theorem integrable_prefix_cross (f g : ℝ → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hf : Integrable f (volume.restrict (Set.Icc 0 u)))
    (hg : Integrable g (volume.restrict (Set.Icc 0 u))) :
    Integrable (fun s => (∫ t in Set.Icc 0 s, g t ∂volume) * f s)
      (volume.restrict (Set.Icc 0 u)) := by
  let G : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, g t
  have hfi : IntervalIntegrable f volume 0 u :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hu).2 hf
  have hgi : IntervalIntegrable g volume 0 u :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hu).2 hg
  have hG : ContinuousOn G (Set.Icc 0 u) := by
    simpa [Set.uIcc_of_le hu] using
      (hgi.absolutelyContinuousOnInterval_intervalIntegral (by simp)).continuousOn
  have h : Integrable (fun s => G s * f s)
      (volume.restrict (Set.Icc 0 u)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hu).1
      (hfi.continuousOn_mul (by simpa [Set.uIcc_of_le hu] using hG))
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  dsimp only [G]
  rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]

private theorem integral_before_cross (f g : ℝ → ℝ) (a c d u : ℝ)
    (hc : 0 ≤ c) (hu : 0 ≤ u)
    (hf : Integrable f (volume.restrict (Set.Icc 0 u)))
    (hg : Integrable g (volume.restrict (Set.Icc 0 u))) :
    (∫ s in Set.Icc 0 u,
      ((if c < s ∧ c < d then a else 0) -
        ∫ t in Set.Icc 0 s, g t ∂volume) * f s ∂volume) =
      (if c ≤ u ∧ c < d then
        a * ((∫ s in Set.Icc 0 u, f s ∂volume) -
          ∫ s in Set.Icc 0 c, f s ∂volume)
      else 0) -
      ∫ s in Set.Icc 0 u,
        (∫ t in Set.Icc 0 s, g t ∂volume) * f s ∂volume := by
  have hevent : Integrable
      (fun s => (if c < s ∧ c < d then a else 0) * f s)
      (volume.restrict (Set.Icc 0 u)) := by
    by_cases hcd : c < d
    · have h := (hf.const_mul a).indicator measurableSet_Ioi (s := Set.Ioi c)
      exact h.congr (Filter.Eventually.of_forall (fun s => by
        simp [Set.indicator, hcd]))
    · simp [hcd]
  have hprefix := integrable_prefix_cross f g u hu hf hg
  have hpoint (s : ℝ) :
      ((if c < s ∧ c < d then a else 0) -
        ∫ t in Set.Icc 0 s, g t ∂volume) * f s =
      (if c < s ∧ c < d then a else 0) * f s -
        (∫ t in Set.Icc 0 s, g t ∂volume) * f s := by ring
  simp_rw [hpoint]
  rw [integral_sub hevent hprefix, integral_event_tail f a c d u hc hf]

/-- For two subjects in a sample, [a nonnegative horizon u](hyp:hu), [nonnegative censor
times](hyp:hci0,hcj0) that [differ between the two subjects](hyp:hCensorDistinct), and
[integrable at-risk integrands for each subject, weighted by the censor
hazard](hyp:hazard,hPathi,hPathj),
[the product of the two subjects' compensated integrals up to u equals each subject's observed
censor-jump payoff times the other subject's strict-past integral at that jump, summed, minus the
two cross-compensator integrals of one subject's strict-past integral against the other's hazard
payoff](goal).

The formula is a pathwise integration by parts for the two compensated censor integrals. -/
theorem distinct_subject_integral_product_pathwise {n : ℕ}
    (hazard : ℝ → ℝ) (H : ℝ → Sample n → ℝ)
    (i j : Fin n) (u : ℝ) (hu : 0 ≤ u) (x : Sample n)
    (hci0 : 0 ≤ (x i).2) (hcj0 : 0 ≤ (x j).2)
    (hCensorDistinct : (x i).2 ≠ (x j).2)
    (hPathi : Integrable (fun s => H s x * hazard s * riskIndicator i s x)
      (volume.restrict (Set.Icc 0 u)))
    (hPathj : Integrable (fun s => H s x * hazard s * riskIndicator j s x)
      (volume.restrict (Set.Icc 0 u))) :
    subjectIntegral hazard H i u x * subjectIntegral hazard H j u x =
      (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then
        H (x i).2 x * subjectIntegralBefore hazard H j (x i).2 x else 0) +
      (if (x j).2 ≤ u ∧ (x j).2 < (x j).1 then
        H (x j).2 x * subjectIntegralBefore hazard H i (x j).2 x else 0) -
      (∫ s in Set.Icc 0 u,
        subjectIntegralBefore hazard H j s x * H s x * hazard s *
          riskIndicator i s x ∂volume) -
      (∫ s in Set.Icc 0 u,
        subjectIntegralBefore hazard H i s x * H s x * hazard s *
          riskIndicator j s x ∂volume) := by
  let ci := (x i).2
  let cj := (x j).2
  let di := (x i).1
  let dj := (x j).1
  let fi : ℝ → ℝ := fun s => H s x * hazard s * riskIndicator i s x
  let fj : ℝ → ℝ := fun s => H s x * hazard s * riskIndicator j s x
  let Ai := H ci x
  let Aj := H cj x
  let Ii := ∫ s in Set.Icc 0 u, fi s ∂volume
  let Ij := ∫ s in Set.Icc 0 u, fj s ∂volume
  let Pi := fun s => ∫ t in Set.Icc 0 s, fi t ∂volume
  let Pj := fun s => ∫ t in Set.Icc 0 s, fj t ∂volume
  have hbilin := integral_prefix_mul_bilinear fi fj u hu hPathi hPathj
  have hcrossj := integral_before_cross fi fj Aj cj dj u hcj0 hu hPathi hPathj
  have hcrossi := integral_before_cross fj fi Ai ci di u hci0 hu hPathj hPathi
  have hR :
      (if ci ≤ u ∧ ci < di then Ai else 0) *
        (if cj ≤ u ∧ cj < dj then Aj else 0) =
      (if ci ≤ u ∧ ci < di then Ai else 0) *
        (if cj < ci ∧ cj < dj then Aj else 0) +
      (if cj ≤ u ∧ cj < dj then Aj else 0) *
        (if ci < cj ∧ ci < di then Ai else 0) := by
    change ci ≠ cj at hCensorDistinct
    by_cases hci : ci ≤ u ∧ ci < di
    · by_cases hcj : cj ≤ u ∧ cj < dj
      · rcases lt_or_gt_of_ne hCensorDistinct with hlt | hlt
        · have hnot : ¬ cj < ci := not_lt_of_ge (le_of_lt hlt)
          simp [hci, hcj, hlt, hnot, mul_comm]
        · have hnot : ¬ ci < cj := not_lt_of_ge (le_of_lt hlt)
          simp [hci, hcj, hlt, hnot]
      · have hnot : ¬ (cj < ci ∧ cj < dj) := by
          intro h
          exact hcj ⟨le_trans (le_of_lt h.1) hci.1, h.2⟩
        simp [hci, hcj, hnot]
    · by_cases hcj : cj ≤ u ∧ cj < dj
      · have hnot : ¬ (ci < cj ∧ ci < di) := by
          intro h
          exact hci ⟨le_trans (le_of_lt h.1) hcj.1, h.2⟩
        simp [hci, hcj, hnot]
      · simp [hci, hcj]
  have hmain :
      ((if ci ≤ u ∧ ci < di then Ai else 0) - Ii) *
        ((if cj ≤ u ∧ cj < dj then Aj else 0) - Ij) =
      (if ci ≤ u ∧ ci < di then
        Ai * ((if cj < ci ∧ cj < dj then Aj else 0) - Pj ci) else 0) +
      (if cj ≤ u ∧ cj < dj then
        Aj * ((if ci < cj ∧ ci < di then Ai else 0) - Pi cj) else 0) -
      (∫ s in Set.Icc 0 u,
        ((if cj < s ∧ cj < dj then Aj else 0) - Pj s) * fi s ∂volume) -
      (∫ s in Set.Icc 0 u,
        ((if ci < s ∧ ci < di then Ai else 0) - Pi s) * fj s ∂volume) := by
    rw [hcrossj, hcrossi]
    unfold Ii Ij Pi Pj at *
    by_cases hi : ci ≤ u ∧ ci < di
    · by_cases hj : cj ≤ u ∧ cj < dj
      · simp only [if_pos hi, if_pos hj] at hR ⊢
        nlinarith [hR, hbilin]
      · simp only [if_pos hi, if_neg hj] at hR ⊢
        nlinarith [hR, hbilin]
    · by_cases hj : cj ≤ u ∧ cj < dj
      · simp only [if_neg hi, if_pos hj] at hR ⊢
        nlinarith [hR, hbilin]
      · simp only [if_neg hi, if_neg hj] at hR ⊢
        nlinarith [hR, hbilin]
  simpa only [subjectIntegral, subjectIntegralBefore,
    ci, cj, di, dj, fi, fj, Ai, Aj, Ii, Ij, Pi, Pj, mul_assoc] using hmain

end Causalean.Stat.RecurrentEvent.CountingProcess

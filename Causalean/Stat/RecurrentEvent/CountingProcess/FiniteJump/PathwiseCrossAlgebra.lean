module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.Basic

/-!
# Elementary cross products of finite jumps and continuous integrals

These deterministic identities separate the three independent parts of the
compensated cross-product expansion. They concern two finite event sets and two
integrable time functions, with no stochastic, predictability, or moment premise.
The strict prefixes agree with the public counting-process product convention.
-/

public section

open MeasureTheory Set

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

/-- The product of payoff sums on disjoint finite time sets splits into the
two strict temporal orderings, with no same-time contribution. -/
theorem finiteJump_sum_product (E F : Finset ℝ) (f g : ℝ → ℝ)
    (hdisjoint : Disjoint E F) :
    (∑ s ∈ E, f s) * (∑ t ∈ F, g t) =
      (∑ s ∈ E, f s * (∑ t ∈ F.filter (fun t => t < s), g t)) +
      (∑ t ∈ F, g t * (∑ s ∈ E.filter (fun s => s < t), f s)) := by
  classical
  have hpair (s : ℝ) (hs : s ∈ E) (t : ℝ) (ht : t ∈ F) :
      f s * g t = f s * (if t < s then g t else 0) +
        g t * (if s < t then f s else 0) := by
    have hne : s ≠ t := by
      intro heq
      subst t
      exact Finset.disjoint_left.mp hdisjoint hs ht
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · simp [hlt, not_lt_of_ge hlt.le, mul_comm]
    · simp [hgt, not_lt_of_ge hgt.le]
  calc
    (∑ s ∈ E, f s) * (∑ t ∈ F, g t) =
        ∑ s ∈ E, ∑ t ∈ F, f s * g t := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.mul_sum]
    _ = ∑ s ∈ E, ∑ t ∈ F,
        (f s * (if t < s then g t else 0) +
          g t * (if s < t then f s else 0)) := by
          apply Finset.sum_congr rfl
          intro s hs
          exact Finset.sum_congr rfl (fun t ht => hpair s hs t ht)
    _ = (∑ s ∈ E, ∑ t ∈ F, f s * (if t < s then g t else 0)) +
        (∑ s ∈ E, ∑ t ∈ F, g t * (if s < t then f s else 0)) := by
          simp_rw [Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      · simp_rw [← Finset.mul_sum, ← Finset.sum_filter]
      · rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, ← Finset.sum_filter]

/-- A finite event payoff sum times an integrable time integral splits into
the integrated prefix evaluated at each event and the strict event prefix
integrated against the time function. -/
theorem finiteJump_sum_integral_product (E : Finset ℝ) (f g : ℝ → ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (hE : ∀ s ∈ E, 0 < s ∧ s ≤ T)
    (hg : IntegrableOn g (Ioc 0 T) volume) :
    (∑ s ∈ E, f s) * (∫ t in Ioc 0 T, g t ∂volume) =
      (∑ s ∈ E, f s * (∫ t in Ioc 0 s, g t ∂volume)) +
      ∫ t in Ioc 0 T,
        (∑ s ∈ E.filter (fun s => s < t), f s) * g t ∂volume := by
  -- The event support already implies a nonnegative horizon when nonempty.
  have _ := hT
  classical
  have hsplit (s : ℝ) (hs : s ∈ E) :
      (∫ t in Ioc 0 T, g t ∂volume) =
        (∫ t in Ioc 0 s, g t ∂volume) + ∫ t in Ioc s T, g t ∂volume := by
    have hs0 := (hE s hs).1.le
    have hsT := (hE s hs).2
    have hdisj : Disjoint (Ioc 0 s) (Ioc s T) := by
      apply Set.disjoint_left.mpr
      intro t ht hu
      exact (not_lt_of_ge ht.2) hu.1
    rw [← Ioc_union_Ioc_eq_Ioc hs0 hsT,
      setIntegral_union hdisj measurableSet_Ioc
        (hg.mono_set (Ioc_subset_Ioc_right hsT))
        (hg.mono_set (Ioc_subset_Ioc_left hs0))]
  let k : ℝ → ℝ → ℝ := fun s t => if s < t then f s * g t else 0
  have hk (s : ℝ) : IntegrableOn (k s) (Ioc 0 T) volume := by
    change Integrable ((Ioi s).indicator (fun t => f s * g t))
      (volume.restrict (Ioc 0 T))
    exact (integrable_indicator_iff measurableSet_Ioi).2
      ((hg.const_mul (f s)).mono_measure Measure.restrict_le_self)
  have htail (s : ℝ) (hs : s ∈ E) :
      (∫ t in Ioc 0 T, k s t ∂volume) =
        f s * ∫ t in Ioc s T, g t ∂volume := by
    have hs0 := (hE s hs).1.le
    have hset : Ioc 0 T ∩ Ioi s = Ioc s T := by
      ext t
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · rintro ⟨⟨_, htT⟩, hst⟩
        exact ⟨hst, htT⟩
      · rintro ⟨hst, htT⟩
        exact ⟨⟨lt_of_le_of_lt hs0 hst, htT⟩, hst⟩
    calc
      (∫ t in Ioc 0 T, k s t ∂volume) =
          ∫ t in Ioc 0 T, (Ioi s).indicator (fun t => f s * g t) t ∂volume := by
            congr 1
      _ = ∫ t in Ioc s T, f s * g t ∂volume := by
        rw [setIntegral_indicator measurableSet_Ioi, hset]
      _ = _ := by rw [integral_const_mul]
  have hpoint (t : ℝ) :
      (∑ s ∈ E, k s t) = (∑ s ∈ E.filter (fun s => s < t), f s) * g t := by
    rw [Finset.sum_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hst : s < t <;> simp [k, hst]
  calc
    (∑ s ∈ E, f s) * (∫ t in Ioc 0 T, g t ∂volume) =
        ∑ s ∈ E, f s * ∫ t in Ioc 0 T, g t ∂volume := by rw [Finset.sum_mul]
    _ = ∑ s ∈ E, (f s * (∫ t in Ioc 0 s, g t ∂volume) +
        f s * ∫ t in Ioc s T, g t ∂volume) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hsplit s hs, mul_add]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        (∑ s ∈ E, f s * ∫ t in Ioc s T, g t ∂volume) =
            ∑ s ∈ E, ∫ t in Ioc 0 T, k s t ∂volume :=
          Finset.sum_congr rfl (fun s hs => (htail s hs).symm)
        _ = ∫ t in Ioc 0 T, ∑ s ∈ E, k s t ∂volume :=
          (integral_finsetSum E (fun s _ => hk s)).symm
        _ = _ := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro t ht
          exact hpoint t

/-- The product of two integrable finite-horizon time integrals is the sum
of their two oriented running-prefix integrals. [The two functions and
horizon](hyp:f,g,T), [nonnegative horizon](hyp:hT), and [integrability of both
functions](hyp:hf,hg) give [the prefix-product identity](goal). -/
theorem integral_prefix_product (f g : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hf : IntegrableOn f (Ioc 0 T) volume)
    (hg : IntegrableOn g (Ioc 0 T) volume) :
    (∫ t in Ioc 0 T, f t ∂volume) * (∫ t in Ioc 0 T, g t ∂volume) =
      (∫ t in Ioc 0 T, (∫ s in Ioc 0 t, f s ∂volume) * g t ∂volume) +
      (∫ t in Ioc 0 T, (∫ s in Ioc 0 t, g s ∂volume) * f t ∂volume) := by
  let F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, f s
  let G : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, g s
  have hfi : IntervalIntegrable f volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hf
  have hgi : IntervalIntegrable g volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hg
  have hF : AbsolutelyContinuousOnInterval F 0 T :=
    hfi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hG : AbsolutelyContinuousOnInterval G 0 T :=
    hgi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hprod := hF.integral_deriv_mul_eq_sub hG
  have heq : (∫ t in (0 : ℝ)..T, deriv F t * G t + F t * deriv G t) =
      ∫ t in (0 : ℝ)..T,
        (∫ s in Ioc 0 t, f s ∂volume) * g t +
        (∫ s in Ioc 0 t, g s ∂volume) * f t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hfi.ae_hasDerivAt_integral, hgi.ae_hasDerivAt_integral]
      with t hft hgt htm
    have htIcc : t ∈ Icc (0 : ℝ) T := by
      simpa [uIcc_of_le hT] using (uIoc_subset_uIcc htm)
    have hdF : deriv F t = f t :=
      (hft (by simpa [uIcc_of_le hT] using htIcc) 0 (by simp)).deriv
    have hdG : deriv G t = g t :=
      (hgt (by simpa [uIcc_of_le hT] using htIcc) 0 (by simp)).deriv
    rw [hdF, hdG]
    simp only [F, G, intervalIntegral.integral_of_le htIcc.1]
    ring
  have hfg : IntegrableOn
      (fun t => (∫ s in Ioc 0 t, f s ∂volume) * g t) (Ioc 0 T) volume := by
    have h : IntegrableOn (fun t => F t * g t) (Ioc 0 T) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
        (hgi.continuousOn_mul (by simpa [uIcc_of_le hT] using hF.continuousOn))
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [F, intervalIntegral.integral_of_le ht.1.le]
  have hgf : IntegrableOn
      (fun t => (∫ s in Ioc 0 t, g s ∂volume) * f t) (Ioc 0 T) volume := by
    have h : IntegrableOn (fun t => G t * f t) (Ioc 0 T) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
        (hfi.continuousOn_mul (by simpa [uIcc_of_le hT] using hG.continuousOn))
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [G, intervalIntegral.integral_of_le ht.1.le]
  rw [heq, intervalIntegral.integral_of_le hT, integral_add hfg hgf] at hprod
  simpa only [F, G, intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_same, zero_mul, sub_zero] using hprod.symm

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

module
public import Causalean.Stat.OrderStatistic.Moments

/-!
# Uniform order-statistic moments

Exact first and second moments of one coordinate of a sorted finite iid
unit-uniform tuple. These refine the existing spacing moment API.

Proof route: the first `j+1` spacings sum to the `j`th zero-based order
statistic. The existing uniform-spacing law and coordinate-square moment
reduce the two order-statistic moments to the first and mixed moments of
coordinates in the spacing simplex, recorded separately below.
-/

public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open Causalean.Stat.OrderStatistic
open scoped Pointwise

noncomputable section

/-- For a [simplex dimension](hyp:n) and [coordinate](hyp:i),
 [the factorial-scaled mean of that spacing coordinate is `1/(n+1)`](goal). -/
theorem simplex_coordinate_first_moment (n : ℕ) (i : Fin n) :
    (n.factorial : ℝ) *
      (∫ z in spacingSimplex n, z i ∂volume) =
        (1 : ℝ) / (n + 1) := by
  -- Slice the simplex by one coordinate and use permutation symmetry for `i`.
  have hfirst_fubini (m : ℕ) :
      (∫ z in spacingSimplex (m + 1), (z (0 : Fin (m + 1))) ∂volume) =
        ∫ t in Set.Icc (0 : ℝ) 1,
          t * (volume (scaledSpacingSimplex m (1 - t))).toReal := by
    let e : (ℝ × (Fin m → ℝ)) ≃ᵐ (Fin (m + 1) → ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm
    let S : Set (ℝ × (Fin m → ℝ)) := e ⁻¹' spacingSimplex (m + 1)
    have hem : MeasurePreserving e :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm _
    have hsimplex : MeasurableSet (spacingSimplex (m + 1)) := by
      have hclosed : IsClosed (spacingSimplex (m + 1)) := by
        change IsClosed {z : Fin (m + 1) → ℝ |
          (∀ i, 0 ≤ z i) ∧ (∑ i, z i) ≤ 1}
        apply IsClosed.inter
        · have hp : IsClosed (⋂ i : Fin (m + 1),
              (fun z : Fin (m + 1) → ℝ => z i) ⁻¹' Set.Ici (0 : ℝ)) :=
            isClosed_iInter (fun i => isClosed_Ici.preimage (continuous_apply i))
          have heq : {z : Fin (m + 1) → ℝ | ∀ i, 0 ≤ z i} =
              ⋂ i : Fin (m + 1), (fun z : Fin (m + 1) → ℝ => z i) ⁻¹' Set.Ici 0 := by
            ext z
            simp
          change IsClosed {z : Fin (m + 1) → ℝ | ∀ i, 0 ≤ z i}
          rw [heq]
          exact hp
        · exact isClosed_Iic.preimage
            (continuous_finsetSum _ (fun i _ => continuous_apply i))
      exact hclosed.measurableSet
    have hS : MeasurableSet S := hsimplex.preimage e.measurable
    have hfinite : volume (spacingSimplex (m + 1)) ≠ ⊤ := by
      change volume (scaledSpacingSimplex (m + 1) 1) ≠ ⊤
      rw [scaledSpacingSimplex_volume (m + 1) 1 (by norm_num)]
      simp
    have hInt : IntegrableOn (fun z : Fin (m + 1) → ℝ => z 0)
        (spacingSimplex (m + 1)) volume := by
      apply Measure.integrableOn_of_bounded hfinite
        ((measurable_pi_apply 0).aestronglyMeasurable) (M := 1)
      apply ae_restrict_of_forall_mem hsimplex
      intro z hz
      have h0 : 0 ≤ z 0 := hz.1 0
      have hle : z 0 ≤ 1 := by
        calc
          z 0 ≤ ∑ i, z i :=
            Finset.single_le_sum (fun i _ => hz.1 i) (Finset.mem_univ 0)
          _ ≤ 1 := hz.2
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hle
    have hpreInt : IntegrableOn (fun p : ℝ × (Fin m → ℝ) => p.1) S
        ((volume : Measure ℝ).prod volume) := by
      rw [← Measure.volume_eq_prod]
      rw [← hem.integrableOn_comp_preimage e.measurableEmbedding] at hInt
      convert hInt using 1
      funext p
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]
    have hprodInt : Integrable
        (S.indicator (fun p : ℝ × (Fin m → ℝ) => p.1))
        ((volume : Measure ℝ).prod volume) := by
      exact hpreInt.integrable_indicator hS
    have hsection (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
        {w : Fin m → ℝ | (t, w) ∈ S} = scaledSpacingSimplex m (1 - t) := by
      simpa [S, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero,
        Fin.consEquiv]
        using simplex_tail_section m t ht
    have hsubset (p : ℝ × (Fin m → ℝ)) (hp : p ∈ S) :
        p.1 ∈ Set.Icc (0 : ℝ) 1 := by
      have hp' : Fin.cons p.1 p.2 ∈ spacingSimplex (m + 1) := by
        simpa [S, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero,
          Fin.consEquiv] using hp
      have h0 : 0 ≤ p.1 := hp'.1 0
      have hle : p.1 ≤ 1 := by
        calc
          p.1 ≤ ∑ i, (Fin.cons p.1 p.2) i := by
            simpa using (Finset.single_le_sum (fun i _ => hp'.1 i)
              (Finset.mem_univ (0 : Fin (m + 1))))
          _ ≤ 1 := hp'.2
      exact ⟨h0, hle⟩
    have hfiber (t : ℝ) :
        (∫ w : Fin m → ℝ,
          S.indicator (fun p : ℝ × (Fin m → ℝ) => p.1) (t, w) ∂volume) =
          if ht : t ∈ Set.Icc (0 : ℝ) 1 then
            t * (volume (scaledSpacingSimplex m (1 - t))).toReal else 0 := by
      split_ifs with ht
      · have hs : MeasurableSet {w : Fin m → ℝ | (t, w) ∈ S} :=
          hS.preimage measurable_prodMk_left
        calc
          _ = ∫ w in {w : Fin m → ℝ | (t, w) ∈ S}, t ∂volume := by
            rw [← integral_indicator hs]
            congr 1
          _ = t * (volume (scaledSpacingSimplex m (1 - t))).toReal := by
            rw [setIntegral_const, hsection t ht]
            simp [measureReal_def, smul_eq_mul, mul_comm]
      · have hzero : ∀ w : Fin m → ℝ, (t, w) ∉ S := by
          intro w hw
          exact ht (hsubset (t, w) hw)
        simp [Set.indicator, hzero]
    calc
      (∫ z in spacingSimplex (m + 1), z 0 ∂volume) =
          ∫ p in S, p.1 ∂volume := by
            rw [← hem.map_eq, setIntegral_map_equiv]
            rfl
      _ = ∫ p : ℝ × (Fin m → ℝ),
            S.indicator (fun p : ℝ × (Fin m → ℝ) => p.1) p ∂volume := by
            rw [integral_indicator hS]
      _ = ∫ t : ℝ, ∫ w : Fin m → ℝ,
            S.indicator (fun p : ℝ × (Fin m → ℝ) => p.1) (t, w) ∂volume := by
            rw [Measure.volume_eq_prod]
            exact integral_prod _ hprodInt
      _ = ∫ t in Set.Icc (0 : ℝ) 1,
            t * (volume (scaledSpacingSimplex m (1 - t))).toReal := by
            simp_rw [hfiber]
            rw [← integral_indicator measurableSet_Icc]
            congr 1
            funext t
            simp [Set.indicator, dite_eq_ite]
  have hfirst_slice (m : ℕ) :
      (∫ z in spacingSimplex (m + 1), (z (0 : Fin (m + 1))) ∂volume) =
        ∫ t in (0 : ℝ)..1, t * ((1 - t) ^ m / (m.factorial : ℝ)) := by
    rw [hfirst_fubini,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have hr : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    change t * (volume (scaledSpacingSimplex m (1 - t))).toReal =
      t * ((1 - t) ^ m / (m.factorial : ℝ))
    rw [scaledSpacingSimplex_volume m (1 - t) hr]
    rw [ENNReal.toReal_ofReal (div_nonneg (pow_nonneg hr m) (by positivity))]
  have hbeta_first (m : ℕ) :
      (∫ t in (0 : ℝ)..1, t * (1 - t) ^ m) =
        (m.factorial : ℝ) / ((m + 2).factorial : ℝ) := by
    have hbeta :
        (∫ t in (0 : ℝ)..1, ((t * (1 - t) ^ m : ℝ) : ℂ)) =
          Complex.betaIntegral 2 (m + 1) := by
      rw [Complex.betaIntegral]
      apply intervalIntegral.integral_congr
      intro t ht
      have ht0 : 0 ≤ t := by simpa using ht.1
      have ht1 : t ≤ 1 := by simpa using ht.2
      dsimp
      simp only [Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_sub, Complex.ofReal_one]
      norm_num
    have heval := Complex.betaIntegral_eq_Gamma_mul_div 2 (m + 1)
      (by norm_num) (by simp; positivity)
    rw [← hbeta] at heval
    have hg3 : Complex.Gamma 2 = 1 := by
      convert Complex.Gamma_nat_eq_factorial 1 using 1 <;> norm_num
    have hgn : Complex.Gamma (m + 1) = (m.factorial : ℂ) := by
      simpa using Complex.Gamma_nat_eq_factorial m
    have hgn3 : Complex.Gamma (2 + (m + 1)) = ((m + 2).factorial : ℂ) := by
      convert Complex.Gamma_nat_eq_factorial (m + 2) using 1 <;> push_cast <;> ring
    rw [hg3, hgn, hgn3] at heval
    rw [intervalIntegral.integral_ofReal] at heval
    exact Complex.ofReal_inj.mp (by simpa using heval)
  have hcoord_eq_first (m : ℕ) (k : Fin m) :
      (∫ z in spacingSimplex m, z k ∂volume) =
        ∫ z in spacingSimplex m,
          z (⟨0, by have := k.isLt; omega⟩ : Fin m) ∂volume := by
    classical
    let j : Fin m := ⟨0, by have := k.isLt; omega⟩
    let σ : Equiv.Perm (Fin m) := Equiv.swap k j
    let e : (Fin m → ℝ) ≃ᵐ (Fin m → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : Fin m => ℝ) σ.symm
    have he : MeasurePreserving e volume volume :=
      volume_measurePreserving_piCongrLeft (fun _ : Fin m => ℝ) σ.symm
    have hfun (z : Fin m → ℝ) : e z = z ∘ σ := by
      funext k
      simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    have hpre : e ⁻¹' spacingSimplex m = spacingSimplex m := by
      ext z
      simp only [Set.mem_preimage, spacingSimplex, Set.mem_ofPred_eq]
      rw [hfun]
      have hsum : (∑ k, z (σ k)) = ∑ k, z k := Equiv.sum_comp σ z
      constructor
      · rintro ⟨hp, hs⟩
        exact ⟨fun k => by simpa using hp (σ.symm k), by simpa [hsum] using hs⟩
      · rintro ⟨hp, hs⟩
        exact ⟨fun k => hp (σ k), by simpa [hsum] using hs⟩
    have hmp : MeasurePreserving e
        (volume.restrict (spacingSimplex m)) (volume.restrict (spacingSimplex m)) := by
      refine ⟨e.measurable, ?_⟩
      calc
        (volume.restrict (spacingSimplex m)).map e =
            (volume.restrict (e ⁻¹' spacingSimplex m)).map e := by rw [hpre]
        _ = (volume.map e).restrict (spacingSimplex m) :=
          (e.restrict_map volume (spacingSimplex m)).symm
        _ = volume.restrict (spacingSimplex m) := by rw [he.map_eq]
    have hint := hmp.integral_comp' (fun z : Fin m → ℝ => z j)
    simp only [hfun] at hint
    have hswap : σ j = k := Equiv.swap_apply_right k j
    simpa [j, hswap] using hint
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
      rw [hcoord_eq_first]
      change (m + 1).factorial *
        (∫ z in spacingSimplex (m + 1), z (0 : Fin (m + 1)) ∂volume) = _
      rw [hfirst_slice]
      have hfactorial : (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
      simp_rw [← mul_div_assoc]
      rw [intervalIntegral.integral_div]
      rw [hbeta_first]
      norm_num [hfactorial, Nat.factorial_succ]
      have hm : (m.factorial : ℝ) ≠ 0 := by positivity
      field_simp

/-- For a [simplex dimension](hyp:n), [nonnegative scale](hyp:hr), and
 [coordinate](hyp:i), [the factorial-scaled coordinate integral over the scaled
 simplex is `r^(n+1)/(n+1)`](goal). -/
theorem scaled_simplex_coordinate_first_moment (n : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (i : Fin n) :
    (n.factorial : ℝ) *
      (∫ z in scaledSpacingSimplex n r, z i ∂volume) =
        r ^ (n + 1) / (n + 1) := by
  classical
  have hn : n ≠ 0 := by have := i.isLt; omega
  by_cases hr0 : r = 0
  · subst r
    have hzero : volume (scaledSpacingSimplex n 0) = 0 := by
      rw [scaledSpacingSimplex_volume n 0 (le_refl 0)]
      simp [hn]
    simp [hzero]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hscale : r • spacingSimplex n = scaledSpacingSimplex n r := by
      ext z
      simp only [Set.mem_smul_set, spacingSimplex, scaledSpacingSimplex,
        Set.mem_ofPred_eq]
      constructor
      · rintro ⟨y, ⟨hp, hs⟩, rfl⟩
        constructor
        · intro j
          simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg hr (hp j)
        · simpa [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] using
            (mul_le_mul_of_nonneg_left hs hr)
      · rintro ⟨hp, hs⟩
        refine ⟨r⁻¹ • z, ?_, ?_⟩
        · constructor
          · intro j
            exact smul_nonneg (inv_nonneg.mpr hr) (hp j)
          · have hs' : (∑ j, (r⁻¹ • z) j) = r⁻¹ * ∑ j, z j := by
              simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
            rw [hs']
            calc
              r⁻¹ * ∑ j, z j ≤ r⁻¹ * r :=
                mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hr)
              _ = 1 := inv_mul_cancel₀ hr0
        · simp [smul_smul, hr0]
    have hchange := Measure.setIntegral_comp_smul
      (μ := (volume : Measure (Fin n → ℝ)))
      (f := fun z : Fin n → ℝ => z i) (s := spacingSimplex n) hr0
    rw [hscale] at hchange
    simp only [Pi.smul_apply, smul_eq_mul, Module.finrank_pi,
      Fintype.card_fin] at hchange
    rw [integral_const_mul] at hchange
    simp only [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr n))] at hchange
    have hmean := simplex_coordinate_first_moment n i
    calc
      (n.factorial : ℝ) *
        (∫ z in scaledSpacingSimplex n r, z i ∂volume) =
          r ^ (n + 1) * ((n.factorial : ℝ) *
            (∫ z in spacingSimplex n, z i ∂volume)) := by
              have hpow : r ^ n ≠ 0 := pow_ne_zero n hr0
              field_simp at hchange ⊢
              rw [pow_succ]
              nlinarith [hchange]
      _ = r ^ (n + 1) / (n + 1) := by rw [hmean]; ring

/-- For a [remaining simplex dimension](hyp:n),
 [the first two coordinate product integral is the first-coordinate slice
 weighted by the scaled tail's coordinate integral](goal). -/
theorem simplex_first_second_cross_fubini (n : ℕ) :
    (∫ z in spacingSimplex (n + 2),
      z (0 : Fin (n + 2)) * z (1 : Fin (n + 2)) ∂volume) =
      ∫ t in Set.Icc (0 : ℝ) 1, t *
        (∫ w in scaledSpacingSimplex (n + 1) (1 - t),
          w (0 : Fin (n + 1)) ∂volume) ∂volume := by
  let m := n + 1
  let e : (ℝ × (Fin m → ℝ)) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm
  let S : Set (ℝ × (Fin m → ℝ)) := e ⁻¹' spacingSimplex (m + 1)
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm _
  have hsimplex : MeasurableSet (spacingSimplex (m + 1)) := by
    have hclosed : IsClosed (spacingSimplex (m + 1)) := by
      change IsClosed {z : Fin (m + 1) → ℝ |
        (∀ i, 0 ≤ z i) ∧ (∑ i, z i) ≤ 1}
      apply IsClosed.inter
      · have hp : IsClosed (⋂ i : Fin (m + 1),
            (fun z : Fin (m + 1) → ℝ => z i) ⁻¹' Set.Ici (0 : ℝ)) :=
          isClosed_iInter (fun i => isClosed_Ici.preimage (continuous_apply i))
        have heq : {z : Fin (m + 1) → ℝ | ∀ i, 0 ≤ z i} =
            ⋂ i : Fin (m + 1), (fun z : Fin (m + 1) → ℝ => z i) ⁻¹' Set.Ici 0 := by
          ext z
          simp
        change IsClosed {z : Fin (m + 1) → ℝ | ∀ i, 0 ≤ z i}
        rw [heq]
        exact hp
      · exact isClosed_Iic.preimage
          (continuous_finsetSum _ (fun i _ => continuous_apply i))
    exact hclosed.measurableSet
  have hS : MeasurableSet S := hsimplex.preimage e.measurable
  have hfinite : volume (spacingSimplex (m + 1)) ≠ ⊤ := by
    change volume (scaledSpacingSimplex (m + 1) 1) ≠ ⊤
    rw [scaledSpacingSimplex_volume (m + 1) 1 (by norm_num)]
    simp
  have hInt : IntegrableOn
      (fun z : Fin (m + 1) → ℝ => z 0 * z 1)
      (spacingSimplex (m + 1)) volume := by
    apply Measure.integrableOn_of_bounded hfinite
      (((measurable_pi_apply 0).mul (measurable_pi_apply 1)).aestronglyMeasurable)
      (M := 1)
    apply ae_restrict_of_forall_mem hsimplex
    intro z hz
    have hcoord (j : Fin (m + 1)) : 0 ≤ z j ∧ z j ≤ 1 := by
      refine ⟨hz.1 j, ?_⟩
      calc
        z j ≤ ∑ k, z k :=
          Finset.single_le_sum (fun k _ => hz.1 k) (Finset.mem_univ j)
        _ ≤ 1 := hz.2
    change ‖z 0 * z 1‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hcoord 0).1 (hcoord 1).1)]
    calc
      z 0 * z 1 ≤ 1 * z 1 :=
        mul_le_mul_of_nonneg_right (hcoord 0).2 (hcoord 1).1
      _ ≤ 1 := by simpa using (hcoord 1).2
  have hpreInt : IntegrableOn
      (fun p : ℝ × (Fin m → ℝ) => p.1 * p.2 0) S
      ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    rw [← hem.integrableOn_comp_preimage e.measurableEmbedding] at hInt
    convert hInt using 1
    funext p
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]
  have hprodInt : Integrable
      (S.indicator (fun p : ℝ × (Fin m → ℝ) => p.1 * p.2 0))
      ((volume : Measure ℝ).prod volume) :=
    hpreInt.integrable_indicator hS
  have hsection (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      {w : Fin m → ℝ | (t, w) ∈ S} = scaledSpacingSimplex m (1 - t) := by
    simpa [S, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero,
      Fin.consEquiv] using simplex_tail_section m t ht
  have hsubset (p : ℝ × (Fin m → ℝ)) (hp : p ∈ S) :
      p.1 ∈ Set.Icc (0 : ℝ) 1 := by
    have hp' : Fin.cons p.1 p.2 ∈ spacingSimplex (m + 1) := by
      simpa [S, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero,
        Fin.consEquiv] using hp
    have h0 : 0 ≤ p.1 := hp'.1 0
    have hle : p.1 ≤ 1 := by
      calc
        p.1 ≤ ∑ i, (Fin.cons p.1 p.2) i := by
          simpa using (Finset.single_le_sum (fun i _ => hp'.1 i)
            (Finset.mem_univ (0 : Fin (m + 1))))
        _ ≤ 1 := hp'.2
    exact ⟨h0, hle⟩
  have hfiber (t : ℝ) :
      (∫ w : Fin m → ℝ,
        S.indicator (fun p : ℝ × (Fin m → ℝ) => p.1 * p.2 0) (t, w) ∂volume) =
        if ht : t ∈ Set.Icc (0 : ℝ) 1 then
          t * (∫ w in scaledSpacingSimplex m (1 - t), w 0 ∂volume) else 0 := by
    split_ifs with ht
    · have hs : MeasurableSet {w : Fin m → ℝ | (t, w) ∈ S} :=
        hS.preimage measurable_prodMk_left
      calc
        _ = ∫ w in {w : Fin m → ℝ | (t, w) ∈ S}, t * w 0 ∂volume := by
          rw [← integral_indicator hs]
          congr 1
        _ = t * (∫ w in scaledSpacingSimplex m (1 - t), w 0 ∂volume) := by
          rw [hsection t ht, integral_const_mul]
    · have hzero : ∀ w : Fin m → ℝ, (t, w) ∉ S := by
        intro w hw
        exact ht (hsubset (t, w) hw)
      simp [Set.indicator, hzero]
  change (∫ z in spacingSimplex (m + 1), z 0 * z 1 ∂volume) = _
  calc
    (∫ z in spacingSimplex (m + 1), z 0 * z 1 ∂volume) =
        ∫ p in S, p.1 * p.2 0 ∂volume := by
          rw [← hem.map_eq, setIntegral_map_equiv]
          rfl
    _ = ∫ p : ℝ × (Fin m → ℝ),
          S.indicator (fun p : ℝ × (Fin m → ℝ) => p.1 * p.2 0) p ∂volume := by
          rw [integral_indicator hS]
    _ = ∫ t : ℝ, ∫ w : Fin m → ℝ,
          S.indicator (fun p : ℝ × (Fin m → ℝ) => p.1 * p.2 0) (t, w) ∂volume := by
          rw [Measure.volume_eq_prod]
          exact integral_prod _ hprodInt
    _ = ∫ t in Set.Icc (0 : ℝ) 1,
          t * (∫ w in scaledSpacingSimplex m (1 - t), w 0 ∂volume) ∂volume := by
          simp_rw [hfiber]
          rw [← integral_indicator measurableSet_Icc]
          congr 1
          funext t
          simp [Set.indicator, dite_eq_ite]

/-- For a [natural exponent](hyp:n), [the first-moment beta integral over the unit
 interval equals the factorial ratio `n!/(n+2)!`](goal). -/
theorem unit_beta_linear_integral (n : ℕ) :
    (∫ t in Set.Icc (0 : ℝ) 1, t * (1 - t) ^ n ∂volume) =
      (n.factorial : ℝ) / ((n + 2).factorial : ℝ) := by
  have hbeta :
      (∫ t in (0 : ℝ)..1, t * (1 - t) ^ n) =
        (n.factorial : ℝ) / ((n + 2).factorial : ℝ) := by
    have hbeta_complex :
        (∫ t in (0 : ℝ)..1, ((t * (1 - t) ^ n : ℝ) : ℂ)) =
          Complex.betaIntegral 2 (n + 1) := by
      rw [Complex.betaIntegral]
      apply intervalIntegral.integral_congr
      intro t ht
      have ht0 : 0 ≤ t := by simpa using ht.1
      have ht1 : t ≤ 1 := by simpa using ht.2
      dsimp
      simp only [Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_sub, Complex.ofReal_one]
      norm_num
    have heval := Complex.betaIntegral_eq_Gamma_mul_div 2 (n + 1)
      (by norm_num) (by simp; positivity)
    rw [← hbeta_complex] at heval
    have hg3 : Complex.Gamma 2 = 1 := by
      convert Complex.Gamma_nat_eq_factorial 1 using 1 <;> norm_num
    have hgn : Complex.Gamma (n + 1) = (n.factorial : ℂ) := by
      simpa using Complex.Gamma_nat_eq_factorial n
    have hgn3 : Complex.Gamma (2 + (n + 1)) = ((n + 2).factorial : ℂ) := by
      convert Complex.Gamma_nat_eq_factorial (n + 2) using 1 <;> push_cast <;> ring
    rw [hg3, hgn, hgn3] at heval
    rw [intervalIntegral.integral_ofReal] at heval
    exact Complex.ofReal_inj.mp (by simpa using heval)
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact hbeta

/-- For [distinct coordinates](hyp:hij) in a spacing simplex,
 [their product integral equals the product integral of coordinates zero and one](goal). -/
theorem simplex_cross_coordinate_eq_first_two (n : ℕ)
    (i j : Fin (n + 2)) (hij : i ≠ j) :
    (∫ z in spacingSimplex (n + 2), z i * z j ∂volume) =
      ∫ z in spacingSimplex (n + 2),
        z (0 : Fin (n + 2)) * z (1 : Fin (n + 2)) ∂volume := by
  classical
  let τ : Equiv.Perm (Fin (n + 2)) := Equiv.swap 0 i
  let σ : Equiv.Perm (Fin (n + 2)) := τ.trans (Equiv.swap (τ 1) j)
  have hτ0 : τ 0 = i := Equiv.swap_apply_left 0 i
  have hτ1i : τ 1 ≠ i := by
    intro h
    have h' : (1 : Fin (n + 2)) = 0 := τ.injective (h.trans hτ0.symm)
    exact (by norm_num : (1 : Fin (n + 2)) ≠ 0) h'
  have hσ0 : σ 0 = i := by
    change (Equiv.swap (τ 1) j) (τ 0) = i
    rw [hτ0]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hτ1i) hij
  have hσ1 : σ 1 = j := Equiv.swap_apply_left (τ 1) j
  let e : (Fin (n + 2) → ℝ) ≃ᵐ (Fin (n + 2) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin (n + 2) => ℝ) σ.symm
  have he : MeasurePreserving e volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin (n + 2) => ℝ) σ.symm
  have hfun (z : Fin (n + 2) → ℝ) : e z = z ∘ σ := by
    funext k
    simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have hpre : e ⁻¹' spacingSimplex (n + 2) = spacingSimplex (n + 2) := by
    ext z
    simp only [Set.mem_preimage, spacingSimplex, Set.mem_ofPred_eq]
    rw [hfun]
    have hsum : (∑ k, z (σ k)) = ∑ k, z k := Equiv.sum_comp σ z
    constructor
    · rintro ⟨hp, hs⟩
      exact ⟨fun k => by simpa using hp (σ.symm k), by simpa [hsum] using hs⟩
    · rintro ⟨hp, hs⟩
      exact ⟨fun k => hp (σ k), by simpa [hsum] using hs⟩
  have hmp : MeasurePreserving e
      (volume.restrict (spacingSimplex (n + 2)))
      (volume.restrict (spacingSimplex (n + 2))) := by
    refine ⟨e.measurable, ?_⟩
    calc
      (volume.restrict (spacingSimplex (n + 2))).map e =
          (volume.restrict (e ⁻¹' spacingSimplex (n + 2))).map e := by rw [hpre]
      _ = (volume.map e).restrict (spacingSimplex (n + 2)) :=
        (e.restrict_map volume (spacingSimplex (n + 2))).symm
      _ = volume.restrict (spacingSimplex (n + 2)) := by rw [he.map_eq]
  have hint := hmp.integral_comp'
    (fun z : Fin (n + 2) → ℝ => z (0 : Fin (n + 2)) * z (1 : Fin (n + 2)))
  simp only [hfun] at hint
  simpa [hσ0, hσ1] using hint

/-- For a [simplex dimension](hyp:n), [two coordinates](hyp:i,j) that are [distinct](hyp:hij),
 [their factorial-scaled product integral is `1/((n+1)(n+2))`](goal). -/
theorem simplex_coordinate_cross_moment (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) :
    (n.factorial : ℝ) *
      (∫ z in spacingSimplex n, z i * z j ∂volume) =
        (1 : ℝ) / ((n + 1) * (n + 2)) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    cases n with
    | zero =>
      exact False.elim (hij (Fin.ext (by
        have hi := i.isLt
        have hj := j.isLt
        omega)))
    | succ m =>
      have hcross := simplex_cross_coordinate_eq_first_two m i j hij
      have hfubini := simplex_first_second_cross_fubini m
      have hinner (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
          (∫ w in scaledSpacingSimplex (m + 1) (1 - t),
            w (0 : Fin (m + 1)) ∂volume) =
            (1 - t) ^ (m + 2) /
              ((m + 2) * ((m + 1).factorial : ℝ)) := by
        have h := scaled_simplex_coordinate_first_moment (m + 1) (1 - t)
          (sub_nonneg.mpr ht.2) (0 : Fin (m + 1))
        have hfac : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
        have hdim : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        push_cast at h ⊢
        field_simp at h ⊢
        nlinarith [h]
      have hint :
          (∫ z in spacingSimplex (m + 2),
            z (0 : Fin (m + 2)) * z (1 : Fin (m + 2)) ∂volume) =
            (m + 2).factorial / (m + 4).factorial /
              ((m + 2) * ((m + 1).factorial : ℝ)) := by
        rw [hfubini]
        have heq :
            (∫ t in Set.Icc (0 : ℝ) 1, t *
              (∫ w in scaledSpacingSimplex (m + 1) (1 - t),
                w (0 : Fin (m + 1)) ∂volume) ∂volume) =
              ∫ t in Set.Icc (0 : ℝ) 1,
                t * ((1 - t) ^ (m + 2) /
                  ((m + 2) * ((m + 1).factorial : ℝ))) ∂volume := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro t ht
          change t * _ = t * _
          rw [hinner t ht]
        rw [heq]
        simp_rw [← mul_div_assoc]
        rw [integral_div]
        rw [unit_beta_linear_integral (m + 2)]
      rw [hcross, hint]
      have hfac : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
      simp only [Nat.factorial_succ]
      push_cast
      field_simp
      ring

end
end Causalean.Stat.OrderStatistic.WeightedConcomitant

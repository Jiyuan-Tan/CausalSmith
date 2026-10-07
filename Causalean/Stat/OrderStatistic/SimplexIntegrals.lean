module
public import Causalean.Stat.OrderStatistic.Dirichlet

/-!
# Elementary integrals on spacing simplices

This module isolates the volume, slicing, and one-variable integral needed to
compute a coordinate's second moment under the uniform spacing law.
-/

@[expose] public section

namespace Causalean.Stat.OrderStatistic

open MeasureTheory
open scoped Pointwise

noncomputable section

/-- Given [a finite dimension](hyp:n) and [a real radius](hyp:r), the [scaled spacing simplex](goal) is [the nonnegative coordinate simplex with total at most that radius](step:1). -/
def scaledSpacingSimplex (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) :=
  {z | (∀ i, 0 ≤ z i) ∧ (∑ i, z i) ≤ r}

/-- Given [a finite dimension](hyp:n), [a real radius](hyp:r), and [its nonnegativity](hyp:hr), [the scaled spacing simplex has the stated factorial-normalized Lebesgue volume](goal). -/
theorem scaledSpacingSimplex_volume (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    volume (scaledSpacingSimplex n r) =
      ENNReal.ofReal (r ^ n / (n.factorial : ℝ)) := by
  classical
  have hsort : AEMeasurable (sortedSample n) (volume : Measure (Fin n → ℝ)) := by
    let s (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
      {x | Monotone (x ∘ σ)}
    have hs (σ : Equiv.Perm (Fin n)) : MeasurableSet (s σ) := by
      have hc : Continuous (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
      exact (isClosed_monotone.preimage hc).measurableSet
    have hcover : (⋃ σ, s σ) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨Tuple.sort x, Tuple.monotone_sort x⟩
    have hpiece (σ : Equiv.Perm (Fin n)) :
        AEMeasurable (sortedSample n) (volume.restrict (s σ)) := by
      have hp : Measurable (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
      apply hp.aemeasurable.congr
      exact ae_restrict_of_forall_mem (hs σ) (fun x hx =>
        (show (fun x => x ∘ σ) x = sortedSample n x from
          (Tuple.comp_sort_eq_comp_iff_monotone (f := x) (σ := σ)).2 hx))
    simpa only [hcover, Measure.restrict_univ] using (AEMeasurable.iUnion hpiece)
  have hsort' : AEMeasurable (sortedSample n) (iidSample uniform01 n) := by
    rw [iid_uniform_cube_law]
    exact hsort.restrict
  have hspacing : Measurable (orderedSpacings n) :=
    (orderedSpacings_measurePreserving n).measurable
  have hfirst : AEMeasurable (firstNSpacings n) (iidSample uniform01 n) := by
    convert hspacing.comp_aemeasurable hsort' using 1
    funext x
    exact firstNSpacings_eq_orderedSpacings n x
  have hprob : (iidSample uniform01 n) Set.univ = 1 := by
    haveI : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
    simp [iidSample]
  have hunit : volume (spacingSimplex n) = (n.factorial : ENNReal)⁻¹ := by
    have h := congrArg (fun μ : Measure (Fin n → ℝ) => μ Set.univ)
      (uniform_firstN_spacings_law n)
    rw [Measure.map_apply_of_aemeasurable hfirst MeasurableSet.univ] at h
    simp only [Set.preimage_univ, Measure.smul_apply, Measure.restrict_apply,
      Set.univ_inter, hprob] at h
    exact ENNReal.eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using h.symm)
  have hscale : r • spacingSimplex n = scaledSpacingSimplex n r := by
    ext z
    simp only [Set.mem_smul_set, spacingSimplex, scaledSpacingSimplex,
      Set.mem_ofPred_eq]
    by_cases hr0 : r = 0
    · subst r
      constructor
      · rintro ⟨y, _, rfl⟩
        simp
      · rintro ⟨hp, hs⟩
        have hz : z = 0 := by
          funext i
          have hi : z i ≤ ∑ j, z j :=
            Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
          exact le_antisymm (le_trans hi hs) (hp i)
        subst z
        refine ⟨0, ?_, by simp⟩
        simp [spacingSimplex]
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      constructor
      · rintro ⟨y, ⟨hp, hs⟩, rfl⟩
        constructor
        · intro i
          simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg hr (hp i)
        · simpa [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] using
            (mul_le_mul_of_nonneg_left hs hr)
      · rintro ⟨hp, hs⟩
        refine ⟨r⁻¹ • z, ?_, ?_⟩
        · constructor
          · intro i
            exact smul_nonneg (inv_nonneg.mpr hr) (hp i)
          · have hs' : (∑ i, (r⁻¹ • z) i) = r⁻¹ * ∑ i, z i := by
              simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
            rw [hs']
            calc
              r⁻¹ * ∑ i, z i ≤ r⁻¹ * r :=
                mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hr)
              _ = 1 := inv_mul_cancel₀ hr0
        · simp [smul_smul, hr0]
  rw [← hscale, Measure.addHaar_smul, hunit]
  simp only [Module.finrank_pi, Module.finrank_self, Finset.sum_const_zero,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [abs_of_nonneg (pow_nonneg hr n), ENNReal.ofReal_div_of_pos (by positivity)]
  simp [ENNReal.ofReal_natCast, div_eq_mul_inv]

/-- Given [a finite dimension](hyp:n), [a first coordinate](hyp:t), and [its membership in the unit interval](hyp:ht), [the remaining simplex section has radius one minus that coordinate](goal). -/
theorem simplex_tail_section (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    {w : Fin n → ℝ | Fin.cons t w ∈ spacingSimplex (n + 1)} =
      scaledSpacingSimplex n (1 - t) := by
  ext w
  simp only [Set.mem_ofPred_eq, spacingSimplex, scaledSpacingSimplex]
  constructor
  · rintro ⟨hpos, hsum⟩
    constructor
    · intro i
      simpa using hpos i.succ
    · rw [Fin.sum_cons] at hsum
      linarith
  · rintro ⟨hpos, hsum⟩
    constructor
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact ht.1
      · intro j
        simpa using hpos j
    · rw [Fin.sum_cons]
      linarith

/-- Given [a finite dimension](hyp:n), [integrating the squared first spacing coordinate equals integrating it against its tail-section volume](goal). -/
theorem simplex_first_coordinate_square_fubini (n : ℕ) :
    (∫ z in spacingSimplex (n + 1), (z (0 : Fin (n + 1))) ^ 2 ∂volume) =
      ∫ t in Set.Icc (0 : ℝ) 1,
        t ^ 2 * (volume (scaledSpacingSimplex n (1 - t))).toReal := by
  let e : (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm
  let S : Set (ℝ × (Fin n → ℝ)) := e ⁻¹' spacingSimplex (n + 1)
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm _
  have hsimplex : MeasurableSet (spacingSimplex (n + 1)) := by
    have hclosed : IsClosed (spacingSimplex (n + 1)) := by
      change IsClosed {z : Fin (n + 1) → ℝ |
        (∀ i, 0 ≤ z i) ∧ (∑ i, z i) ≤ 1}
      apply IsClosed.inter
      · have hp : IsClosed (⋂ i : Fin (n + 1),
            (fun z : Fin (n + 1) → ℝ => z i) ⁻¹' Set.Ici (0 : ℝ)) :=
          isClosed_iInter (fun i => isClosed_Ici.preimage (continuous_apply i))
        have heq : {z : Fin (n + 1) → ℝ | ∀ i, 0 ≤ z i} =
            ⋂ i : Fin (n + 1), (fun z : Fin (n + 1) → ℝ => z i) ⁻¹' Set.Ici 0 := by
          ext z
          simp
        change IsClosed {z : Fin (n + 1) → ℝ | ∀ i, 0 ≤ z i}
        rw [heq]
        exact hp
      · exact isClosed_Iic.preimage
          (continuous_finsetSum _ (fun i _ => continuous_apply i))
    exact hclosed.measurableSet
  have hS : MeasurableSet S := hsimplex.preimage e.measurable
  have hfinite : volume (spacingSimplex (n + 1)) ≠ ⊤ := by
    change volume (scaledSpacingSimplex (n + 1) 1) ≠ ⊤
    rw [scaledSpacingSimplex_volume (n + 1) 1 (by norm_num)]
    simp
  have hInt : IntegrableOn (fun z : Fin (n + 1) → ℝ => z 0 ^ 2)
      (spacingSimplex (n + 1)) volume := by
    apply Measure.integrableOn_of_bounded hfinite
      (((measurable_pi_apply 0).pow_const 2).aestronglyMeasurable) (M := 1)
    apply ae_restrict_of_forall_mem hsimplex
    intro z hz
    have h0 : 0 ≤ z 0 := hz.1 0
    have hle : z 0 ≤ 1 := by
      calc
        z 0 ≤ ∑ i, z i :=
          Finset.single_le_sum (fun i _ => hz.1 i) (Finset.mem_univ 0)
        _ ≤ 1 := hz.2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hpreInt : IntegrableOn (fun p : ℝ × (Fin n → ℝ) => p.1 ^ 2) S
      ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    rw [← hem.integrableOn_comp_preimage e.measurableEmbedding] at hInt
    convert hInt using 1
    funext p
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]
  have hprodInt : Integrable
      (S.indicator (fun p : ℝ × (Fin n → ℝ) => p.1 ^ 2))
      ((volume : Measure ℝ).prod volume) := by
    exact hpreInt.integrable_indicator hS
  have hsection (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      {w : Fin n → ℝ | (t, w) ∈ S} = scaledSpacingSimplex n (1 - t) := by
    simpa [S, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero,
      Fin.consEquiv]
      using simplex_tail_section n t ht
  have hsubset (p : ℝ × (Fin n → ℝ)) (hp : p ∈ S) :
      p.1 ∈ Set.Icc (0 : ℝ) 1 := by
    have hp' : Fin.cons p.1 p.2 ∈ spacingSimplex (n + 1) := by
      simpa [S, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero,
        Fin.consEquiv] using hp
    have h0 : 0 ≤ p.1 := hp'.1 0
    have hle : p.1 ≤ 1 := by
      calc
        p.1 ≤ ∑ i, (Fin.cons p.1 p.2) i := by
          simpa using (Finset.single_le_sum (fun i _ => hp'.1 i)
            (Finset.mem_univ (0 : Fin (n + 1))))
        _ ≤ 1 := hp'.2
    exact ⟨h0, hle⟩
  have hfiber (t : ℝ) :
      (∫ w : Fin n → ℝ,
        S.indicator (fun p : ℝ × (Fin n → ℝ) => p.1 ^ 2) (t, w) ∂volume) =
        if ht : t ∈ Set.Icc (0 : ℝ) 1 then
          t ^ 2 * (volume (scaledSpacingSimplex n (1 - t))).toReal else 0 := by
    split_ifs with ht
    · have hs : MeasurableSet {w : Fin n → ℝ | (t, w) ∈ S} :=
        hS.preimage measurable_prodMk_left
      calc
        _ = ∫ w in {w : Fin n → ℝ | (t, w) ∈ S}, t ^ 2 ∂volume := by
          rw [← integral_indicator hs]
          congr 1
        _ = t ^ 2 * (volume (scaledSpacingSimplex n (1 - t))).toReal := by
          rw [setIntegral_const, hsection t ht]
          simp [measureReal_def, smul_eq_mul, mul_comm]
    · have hzero : ∀ w : Fin n → ℝ, (t, w) ∉ S := by
        intro w hw
        exact ht (hsubset (t, w) hw)
      simp [Set.indicator, hzero]
  calc
    (∫ z in spacingSimplex (n + 1), z 0 ^ 2 ∂volume) =
        ∫ p in S, p.1 ^ 2 ∂volume := by
          rw [← hem.map_eq, setIntegral_map_equiv]
          rfl
    _ = ∫ p : ℝ × (Fin n → ℝ),
          S.indicator (fun p : ℝ × (Fin n → ℝ) => p.1 ^ 2) p ∂volume := by
          rw [integral_indicator hS]
    _ = ∫ t : ℝ, ∫ w : Fin n → ℝ,
          S.indicator (fun p : ℝ × (Fin n → ℝ) => p.1 ^ 2) (t, w) ∂volume := by
          rw [Measure.volume_eq_prod]
          exact integral_prod _ hprodInt
    _ = ∫ t in Set.Icc (0 : ℝ) 1,
          t ^ 2 * (volume (scaledSpacingSimplex n (1 - t))).toReal := by
          simp_rw [hfiber]
          rw [← integral_indicator measurableSet_Icc]
          congr 1
          funext t
          simp [Set.indicator, dite_eq_ite]

/-- Given [a finite dimension](hyp:n), [the squared first-coordinate simplex integral equals its one-dimensional sliced integral](goal). -/
theorem simplex_first_coordinate_square_slice (n : ℕ) :
    (∫ z in spacingSimplex (n + 1), (z (0 : Fin (n + 1))) ^ 2 ∂volume) =
      ∫ t in (0 : ℝ)..1, t ^ 2 * ((1 - t) ^ n / (n.factorial : ℝ)) := by
  rw [simplex_first_coordinate_square_fubini,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  have hr : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  change t ^ 2 * (volume (scaledSpacingSimplex n (1 - t))).toReal =
    t ^ 2 * ((1 - t) ^ n / (n.factorial : ℝ))
  rw [scaledSpacingSimplex_volume n (1 - t) hr]
  rw [ENNReal.toReal_ofReal (div_nonneg (pow_nonneg hr n) (by positivity))]

/-- Given [a nonnegative integer exponent](hyp:n), [the unit-interval beta-type polynomial integral has the stated factorial value](goal). -/
theorem unit_beta_square_integral (n : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ 2 * (1 - t) ^ n) =
      2 * (n.factorial : ℝ) / ((n + 3).factorial : ℝ) := by
  have hbeta :
      (∫ t in (0 : ℝ)..1, ((t ^ 2 * (1 - t) ^ n : ℝ) : ℂ)) =
        Complex.betaIntegral 3 (n + 1) := by
    rw [Complex.betaIntegral]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 ≤ t := by simpa using ht.1
    have ht1 : t ≤ 1 := by simpa using ht.2
    dsimp
    simp only [Complex.ofReal_mul, Complex.ofReal_cpow ht0,
      Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.cpow_natCast]
    norm_num
  have heval := Complex.betaIntegral_eq_Gamma_mul_div 3 (n + 1)
    (by norm_num) (by simp; positivity)
  rw [← hbeta] at heval
  have hg3 : Complex.Gamma 3 = 2 := by
    convert Complex.Gamma_nat_eq_factorial 2 using 1 <;> norm_num
  have hgn : Complex.Gamma (n + 1) = (n.factorial : ℂ) := by
    simpa using Complex.Gamma_nat_eq_factorial n
  have hgn3 : Complex.Gamma (3 + (n + 1)) = ((n + 3).factorial : ℂ) := by
    convert Complex.Gamma_nat_eq_factorial (n + 3) using 1 <;> push_cast <;> ring
  rw [hg3, hgn, hgn3] at heval
  rw [intervalIntegral.integral_ofReal] at heval
  exact Complex.ofReal_inj.mp (by simpa using heval)

/-- Given [a finite dimension](hyp:n) and [a coordinate index](hyp:i), [the integral over the spacing simplex of the square of that coordinate equals the integral of the square of the first coordinate](goal). -/
theorem simplex_coordinate_square_eq_first (n : ℕ) (i : Fin n) :
    (∫ z in spacingSimplex n, (z i) ^ 2 ∂volume) =
      ∫ z in spacingSimplex n,
        (z (⟨0, by have := i.isLt; omega⟩ : Fin n)) ^ 2 ∂volume := by
  classical
  let j : Fin n := ⟨0, by have := i.isLt; omega⟩
  let σ : Equiv.Perm (Fin n) := Equiv.swap i j
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have he : MeasurePreserving e volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have hfun (z : Fin n → ℝ) : e z = z ∘ σ := by
    funext k
    simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have hpre : e ⁻¹' spacingSimplex n = spacingSimplex n := by
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
      (volume.restrict (spacingSimplex n)) (volume.restrict (spacingSimplex n)) := by
    refine ⟨e.measurable, ?_⟩
    calc
      (volume.restrict (spacingSimplex n)).map e =
          (volume.restrict (e ⁻¹' spacingSimplex n)).map e := by rw [hpre]
      _ = (volume.map e).restrict (spacingSimplex n) :=
        (e.restrict_map volume (spacingSimplex n)).symm
      _ = volume.restrict (spacingSimplex n) := by rw [he.map_eq]
  have hint := hmp.integral_comp' (fun z : Fin n → ℝ => (z j) ^ 2)
  simp only [hfun] at hint
  have hswap : σ j = i := Equiv.swap_apply_right i j
  simpa [j, hswap] using hint

end
end Causalean.Stat.OrderStatistic

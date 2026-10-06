module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ExactConditionalMeansQuadratic

/-! # Exact conditional means of the quadratic and cubic corrections

This module exports the exact training-conditional means of both held-out
histogram corrections. The quadratic proof is split into its own dependency;
this file supplies the cubic identity.
-/

public section

open MeasureTheory
open Causalean.Mathlib.Probability.Independence
open scoped BigOperators

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The exact training-conditional mean of the cubic correction is its
cellwise projection polynomial.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
lemma condExp_cubicTerm_eq_cubicProjectionMean (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    condExp (trainingSigma n) (dataLaw P n n)
      (fun ω : TwoSample n n => cubicTerm c_f C_f ω A) =ᵐ[dataLaw P n n]
      (fun ω => cubicProjectionMean c_f C_f L P n hP ω A) := by
  classical
  let K := cubicResolution n
  have hK : 0 < K := by
    dsimp [K, cubicResolution, dyadicResolution]
    split_ifs <;> positivity
  let E := MeasurableEquiv.sumPiEquivProdPi (FlatObs n)
  have hEembed : @MeasurableEmbedding
      (TwoSample n n) ((a : FlatIndex n) → FlatObs n a)
      inferInstance MeasurableSpace.pi (flattenSample n) :=
    (MeasurableEquiv.sumPiEquivProdPi (FlatObs n)).symm.measurableEmbedding
  let μ := Measure.pi (flatLaw P n)
  let m := MeasurableSpace.comap
    (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi
  let M := fourthDerivativeEnvelope c_f C_f
  let U := 2 * (1 + C_f)
  let C := M * (1 + U) ^ 2 / 6
  let shift (i : Fin 7) (l : Fin K)
      (z : (a : FlatIndex n) → FlatObs n a) :=
    cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
      pilot c_f C_f (E z) (midpoint K l) i
  let coeff (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) (l : Fin K)
      (z : (a : FlatIndex n) → FlatObs n a) :=
    let a := (1 / 6 : ℝ) *
      dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) q.2.1 q.2.2.1 q.2.2.2
    ![a, a * shift q.2.1 l z, a * shift q.2.2.1 l z, a * shift q.2.2.2 l z,
      a * shift q.2.1 l z * shift q.2.2.1 l z,
      a * shift q.2.1 l z * shift q.2.2.2 l z,
      a * shift q.2.2.1 l z * shift q.2.2.2 l z] q.1
  let leaf (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) (l : Fin K)
      (z : (a : FlatIndex n) → FlatObs n a) :=
    ![flatCenteredCubicCell P ![q.2.1, q.2.2.1, q.2.2.2] l z,
      flatCenteredPairCell P ![q.2.2.1, q.2.2.2] ![1, 2] l z,
      flatCenteredPairCell P ![q.2.1, q.2.2.2] ![0, 2] l z,
      flatCenteredPairCell P ![q.2.1, q.2.2.1] ![0, 1] l z,
      flatCenteredCellScore P q.2.2.2 3 l (finsetCoordProj (flatBlock n 3) z),
      flatCenteredCellScore P q.2.2.1 2 l (finsetCoordProj (flatBlock n 2) z),
      flatCenteredCellScore P q.2.1 1 l (finsetCoordProj (flatBlock n 1) z)] q.1
  let Y (q : Fin 7 × Fin 7 × Fin 7 × Fin 7)
      (z : (a : FlatIndex n) → FlatObs n a) :=
    (K : ℝ)⁻¹ * ∑ l : Fin K, coeff q l z * leaf q l z
  let Z (z : (a : FlatIndex n) → FlatObs n a) :=
    ∑ q : Fin 7 × Fin 7 × Fin 7 × Fin 7, Y q z
  let G (z : (a : FlatIndex n) → FlatObs n a) :=
    (K : ℝ)⁻¹ * ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, ∑ l : Fin K,
      (1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
        shift i l z * shift j l z * shift k l z
  let F (z : (a : FlatIndex n) → FlatObs n a) := cubicTerm c_f C_f (E z) A
  letI : ∀ a, StandardBorelSpace (FlatObs n a) := fun a => by
    cases a <;> dsimp [FlatObs] <;> infer_instance
  letI : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  have hm : m ≤ (MeasurableSpace.pi : MeasurableSpace ((a : FlatIndex n) → FlatObs n a)) := by
    dsimp [m]
    exact (measurable_finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)).comap_le
  have hM : 0 ≤ M := by
    dsimp [M, fourthDerivativeEnvelope]
    have hc := hP.sourceBounds.1.1
    positivity
  have hU : 0 ≤ U := by
    dsimp [U]
    have := hP.sourceBounds.2.1
    positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcoeff_meas (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) (l : Fin K) :
      StronglyMeasurable[m] (coeff q l) := by
    rcases q with ⟨t, i, j, k⟩
    have hd := stronglyMeasurable_dPhi3_pilot_flatTraining
      c_f C_f L P n hn hP A (midpoint K l) i j k
    have hs (r : Fin 7) : StronglyMeasurable[m] (shift r l) :=
      stronglyMeasurable_const.sub
        (stronglyMeasurable_pilot_eval_flatTraining c_f C_f n (midpoint K l) r)
    fin_cases t
    all_goals change StronglyMeasurable[m] _; dsimp only [coeff]
    · exact hd.const_mul (1 / 6)
    · exact (hd.const_mul (1 / 6)).mul (hs i)
    · exact (hd.const_mul (1 / 6)).mul (hs j)
    · exact (hd.const_mul (1 / 6)).mul (hs k)
    · exact ((hd.const_mul (1 / 6)).mul (hs i)).mul (hs j)
    · exact ((hd.const_mul (1 / 6)).mul (hs i)).mul (hs k)
    · exact ((hd.const_mul (1 / 6)).mul (hs j)).mul (hs k)
  have hcoeff (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) :
      ∀ᵐ z ∂μ, ∀ l, |coeff q l z| ≤ C := by
    filter_upwards [] with z
    intro l
    rcases q with ⟨t, i, j, k⟩
    have hd := dPhi3_abs_le c_f C_f hP.sourceBounds.1 hP.sourceBounds.2.1 A
      (pilot c_f C_f (E z) (midpoint K l))
      (pilot_mem_clippingRectangle c_f C_f L P n hn hP (E z) (midpoint K l)) i j k
    have hi := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l i
    have hj := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l j
    have hk := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l k
    change |dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k| ≤ M at hd
    change |shift i l z| ≤ U at hi
    change |shift j l z| ≤ U at hj
    change |shift k l z| ≤ U at hk
    have hb : |(1 / 6 : ℝ) * dPhi3 A
        (pilot c_f C_f (E z) (midpoint K l)) i j k| ≤ M / 6 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)]
      nlinarith
    have h0 : M / 6 ≤ C := by
      dsimp [C]
      nlinarith [mul_nonneg hM hU, sq_nonneg U]
    have h1 : M / 6 * U ≤ C := by
      dsimp [C]
      nlinarith [mul_nonneg hM hU, mul_nonneg hM (sq_nonneg U)]
    have h2 : M / 6 * U * U ≤ C := by
      dsimp [C]
      nlinarith [mul_nonneg hM hU]
    have hb0 : 0 ≤ M / 6 := div_nonneg hM (by norm_num)
    fin_cases t
    all_goals dsimp [coeff]
    · exact hb.trans h0
    · rw [abs_mul]; exact (mul_le_mul hb hi (abs_nonneg _) hb0).trans h1
    · rw [abs_mul]; exact (mul_le_mul hb hj (abs_nonneg _) hb0).trans h1
    · rw [abs_mul]; exact (mul_le_mul hb hk (abs_nonneg _) hb0).trans h1
    · rw [abs_mul, abs_mul]
      exact (mul_le_mul (mul_le_mul hb hi (abs_nonneg _) hb0) hj
        (abs_nonneg _) (mul_nonneg hb0 hU)).trans h2
    · rw [abs_mul, abs_mul]
      exact (mul_le_mul (mul_le_mul hb hi (abs_nonneg _) hb0) hk
        (abs_nonneg _) (mul_nonneg hb0 hU)).trans h2
    · rw [abs_mul, abs_mul]
      exact (mul_le_mul (mul_le_mul hb hj (abs_nonneg _) hb0) hk
        (abs_nonneg _) (mul_nonneg hb0 hU)).trans h2
  have hleaf_lp (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) (l : Fin K) : MemLp (leaf q l) 2 μ := by
    rcases q with ⟨t, i, j, k⟩
    fin_cases t
    · simpa [leaf, μ] using flatCenteredCubicCell_memLp c_f C_f L P n K hn hP ![i, j, k] l
    · simpa [leaf, μ] using flatCenteredPairCell_memLp c_f C_f L P n K hn hP
        ![j, k] ![1, 2] (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all) l
    · simpa [leaf, μ] using flatCenteredPairCell_memLp c_f C_f L P n K hn hP
        ![i, k] ![0, 2] (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all) l
    · simpa [leaf, μ] using flatCenteredPairCell_memLp c_f C_f L P n K hn hP
        ![i, j] ![0, 1] (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all) l
    · simpa [leaf, μ] using flatCenteredCellScore_comp_memLp c_f C_f L P n K hn hP k 3 l
    · simpa [leaf, μ] using flatCenteredCellScore_comp_memLp c_f C_f L P n K hn hP j 2 l
    · simpa [leaf, μ] using flatCenteredCellScore_comp_memLp c_f C_f L P n K hn hP i 1 l
  have hterm (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) (l : Fin K) :
      Integrable (fun z => coeff q l z * leaf q l z) μ := by
    apply (hleaf_lp q l).integrable (by norm_num) |>.bdd_mul
      ((hcoeff_meas q l).mono hm).aestronglyMeasurable
    filter_upwards [hcoeff q] with z hz
    simpa only [Real.norm_eq_abs] using hz l
  have hYint (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) : Integrable (Y q) μ :=
    (integrable_finsetSum Finset.univ (fun l _ => hterm q l)).const_mul (K : ℝ)⁻¹
  have hleaf_zero (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) (l : Fin K) :
      condExp m μ (leaf q l) =ᵐ[μ]
        (0 : ((a : FlatIndex n) → FlatObs n a) → ℝ) := by
    rcases q with ⟨t, i, j, k⟩
    fin_cases t
    · simpa [leaf, m, μ] using condExp_flatCenteredCubicCell_zero
        c_f C_f L P n K hn hP ![i, j, k] l
    · simpa [leaf, m, μ] using condExp_flatCenteredPairCell_zero c_f C_f L P n K hn hP
        ![j, k] ![1, 2] (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all) l
    · simpa [leaf, m, μ] using condExp_flatCenteredPairCell_zero c_f C_f L P n K hn hP
        ![i, k] ![0, 2] (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all) l
    · simpa [leaf, m, μ] using condExp_flatCenteredPairCell_zero c_f C_f L P n K hn hP
        ![i, j] ![0, 1] (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all) l
    · simpa [leaf, m, μ] using condExp_flatCenteredCellScore_zero c_f C_f L P n K hn hP k 2 l
    · simpa [leaf, m, μ] using condExp_flatCenteredCellScore_zero c_f C_f L P n K hn hP j 1 l
    · simpa [leaf, m, μ] using condExp_flatCenteredCellScore_zero c_f C_f L P n K hn hP i 0 l
  have hYzero (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) :
      condExp m μ (Y q) =ᵐ[μ] (0 : ((a : FlatIndex n) → FlatObs n a) → ℝ) :=
    @condExp_weighted_cellAverage_zero
      ((a : FlatIndex n) → FlatObs n a) MeasurableSpace.pi μ m K hm _
      (coeff q) (leaf q) (hcoeff_meas q)
      (fun l => (hleaf_lp q l).integrable (by norm_num)) (hterm q) (hleaf_zero q)
  have hZint : Integrable Z μ := by
    simpa only [Z] using integrable_finsetSum Finset.univ (fun q _ => hYint q)
  have hZzero : condExp m μ Z =ᵐ[μ]
      (0 : ((a : FlatIndex n) → FlatObs n a) → ℝ) := by
    have hs := condExp_finsetSum (μ := μ) (s := Finset.univ) (f := Y)
      (fun q _ => hYint q) m
    filter_upwards [hs, ae_all_iff.mpr hYzero] with z hs hz
    simp only [Finset.sum_fn, Finset.sum_apply] at hs
    dsimp only [Z]
    rw [hs]
    simp only [hz, Pi.zero_apply, Finset.sum_const_zero]
  have hgterm_meas (i j k : Fin 7) (l : Fin K) : StronglyMeasurable[m] (fun z =>
      (1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
        shift i l z * shift j l z * shift k l z) := by
    have hd := stronglyMeasurable_dPhi3_pilot_flatTraining
      c_f C_f L P n hn hP A (midpoint K l) i j k
    have hs (r : Fin 7) : StronglyMeasurable[m] (shift r l) :=
      stronglyMeasurable_const.sub
        (stronglyMeasurable_pilot_eval_flatTraining c_f C_f n (midpoint K l) r)
    exact (((hd.const_mul (1 / 6)).mul (hs i)).mul (hs j)).mul (hs k)
  have hGmeas : StronglyMeasurable[m] G := by
    simpa only [G, Finset.sum_apply] using
      ((Finset.stronglyMeasurable_sum Finset.univ fun i _ =>
        Finset.stronglyMeasurable_sum Finset.univ fun j _ =>
        Finset.stronglyMeasurable_sum Finset.univ fun k _ =>
        Finset.stronglyMeasurable_sum Finset.univ fun l _ => hgterm_meas i j k l)).const_mul
          (K : ℝ)⁻¹
  have hGlp : MemLp G 2 μ := by
    have ht (i j k : Fin 7) (l : Fin K) : MemLp (fun z =>
        (1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
          shift i l z * shift j l z * shift k l z) 2 μ := by
      refine MemLp.of_bound ((hgterm_meas i j k l).mono hm).aestronglyMeasurable
        (M * U ^ 3) ?_
      filter_upwards [] with z
      simp only [Real.norm_eq_abs, abs_mul]
      have hd := dPhi3_abs_le c_f C_f hP.sourceBounds.1 hP.sourceBounds.2.1 A
        (pilot c_f C_f (E z) (midpoint K l))
        (pilot_mem_clippingRectangle c_f C_f L P n hn hP (E z) (midpoint K l)) i j k
      have hi := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l i
      have hj := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l j
      have hk := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l k
      change |dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k| ≤ M at hd
      change |shift i l z| ≤ U at hi
      change |shift j l z| ≤ U at hj
      change |shift k l z| ≤ U at hk
      calc
        _ ≤ 1 * M * U * U * U := by gcongr <;> norm_num
        _ = M * U ^ 3 := by ring
    have hs1 (i j k : Fin 7) : MemLp (fun z => ∑ l : Fin K,
        (1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
          shift i l z * shift j l z * shift k l z) 2 μ :=
      memLp_finsetSum Finset.univ (fun l _ => ht i j k l)
    have hs2 (i j : Fin 7) : MemLp (fun z => ∑ k : Fin 7, ∑ l : Fin K,
        (1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
          shift i l z * shift j l z * shift k l z) 2 μ :=
      memLp_finsetSum Finset.univ (fun k _ => hs1 i j k)
    have hs3 (i : Fin 7) : MemLp (fun z => ∑ j : Fin 7, ∑ k : Fin 7, ∑ l : Fin K,
        (1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
          shift i l z * shift j l z * shift k l z) 2 μ :=
      memLp_finsetSum Finset.univ (fun j _ => hs2 i j)
    have hs4 : MemLp (fun z => ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, ∑ l : Fin K,
        (1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
          shift i l z * shift j l z * shift k l z) 2 μ :=
      memLp_finsetSum Finset.univ (fun i _ => hs3 i)
    exact hs4.const_mul (K : ℝ)⁻¹
  have hGint : Integrable G μ := hGlp.integrable (by norm_num)
  have hdecomp : F = Z + G := by
    funext z
    dsimp only [F, Z, Y, G]
    unfold cubicTerm
    dsimp only
    change (1 / (6 * (K : ℝ))) * ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, ∑ l : Fin K,
        dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
          residual c_f C_f (E z) i K 1 (midpoint K l) *
          residual c_f C_f (E z) j K 2 (midpoint K l) *
          residual c_f C_f (E z) k K 3 (midpoint K l) = _
    simp only [Pi.add_apply]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    conv_rhs => rw [Fin.sum_univ_succ, Fin.sum_univ_six]
    simp [coeff, leaf]
    simp only [← Finset.mul_sum, ← Finset.sum_add_distrib]
    repeat' rw [← mul_add]
    rw [mul_assoc]
    apply congrArg (fun x : ℝ => (K : ℝ)⁻¹ * x)
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    have hdec := cubic_residual_seven_subset_decomposition
      c_f C_f L P hn hP hK (E z) i j k l
    dsimp only at hdec
    simp only [E, MeasurableEquiv.symm_apply_apply] at hdec
    dsimp only [shift]
    simp [flatCenteredCubicCell, flatCenteredPairCell, Fin.prod_univ_two,
      Fin.prod_univ_three]
    linear_combination
      ((1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k) * hdec
  have hFint : Integrable F μ := by
    rw [hdecomp]
    exact hZint.add hGint
  have hflat : condExp m μ F =ᵐ[μ] G := by
    rw [hdecomp]
    exact @condExp_add_eq_shift_of_centered
      ((a : FlatIndex n) → FlatObs n a) MeasurableSpace.pi μ m hm _
      Z G hZint hGint hGmeas hZzero
  have hpull := condExp_comp_flattenSample c_f C_f L P n hP F hFint
  have hcompF : F ∘ flattenSample n = fun ω => cubicTerm c_f C_f ω A := by
    funext ω
    simp [F, E, Function.comp_apply]
  have hcompG : G ∘ flattenSample n =
      fun ω => cubicProjectionMean c_f C_f L P n hP ω A := by
    funext ω
    rw [cubicProjectionMean_eq]
    simp [G, shift, E, K, Function.comp_apply]
  have hmap : @Measure.map _ _ _ MeasurableSpace.pi
      (flattenSample n) (dataLaw P n n) = μ := by
    simpa only [μ] using map_flattenSample_dataLaw c_f C_f L P n hP
  have hflat_pull : ∀ᵐ ω ∂dataLaw P n n,
      @condExp ((a : FlatIndex n) → FlatObs n a) ℝ m MeasurableSpace.pi _ _ μ F
        (flattenSample n ω) = G (flattenSample n ω) := by
    have hp : ∀ᵐ z ∂(@Measure.map _ _ _ MeasurableSpace.pi
        (flattenSample n) (dataLaw P n n)), condExp m μ F z = G z := by
      rw [hmap]
      exact hflat
    exact (@MeasurableEmbedding.ae_map_iff
      (TwoSample n n) ((a : FlatIndex n) → FlatObs n a)
      inferInstance MeasurableSpace.pi (flattenSample n) hEembed
      (fun z => condExp m μ F z = G z) (dataLaw P n n)).mp hp
  rw [hcompF] at hpull
  filter_upwards [hpull, hflat_pull] with ω hp hf
  rw [hp]
  change @condExp ((a : FlatIndex n) → FlatObs n a) ℝ m
      MeasurableSpace.pi _ _ μ F (flattenSample n ω) = _
  rw [hf]
  exact congrFun hcompG ω

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

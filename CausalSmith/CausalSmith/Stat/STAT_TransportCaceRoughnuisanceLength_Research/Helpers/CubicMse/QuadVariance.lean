module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.Cancellation
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CenteredPairCells
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ExactStatisticBridge
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.VarianceAggregation
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Reduction
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Constants for the quadratic conditional variance calculation -/

@[expose] public section
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- [The quad variance constant object](goal) is defined from [the supplied inputs](hyp:c_f,C_f). -/

noncomputable def quadVarianceConstant (c_f C_f : ℝ) : ℝ :=
  let d : ℝ := 7
  let U := 2 * (1 + C_f)
  let V := 1 + C_f + C_f ^ 2
  let M := fourthDerivativeEnvelope c_f C_f
  d ^ 4 * (2 ^ (2 : ℕ) - 1) ^ 2 * M ^ 2 *
    (1 + U) ^ 4 * (1 + V) ^ 2

open MeasureTheory
open Causalean.Mathlib.Probability.Independence
open scoped BigOperators

-- @node: quadratic_conditional_variance_with_memLp
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated result about quadratic conditional variance with mem lp holds](goal). -/
lemma quadratic_conditional_variance_with_memLp (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    MemLp (fun ξ : TwoSample n n => quadraticTerm c_f C_f ξ A) 2
      (dataLaw P n n) ∧
    (∀ᵐ ω ∂dataLaw P n n,
      MeasureTheory.condExp (trainingSigma n) (dataLaw P n n)
        (fun ξ : TwoSample n n =>
        (quadraticTerm c_f C_f ξ A -
          MeasureTheory.condExp (trainingSigma n) (dataLaw P n n)
            (fun ζ : TwoSample n n => quadraticTerm c_f C_f ζ A) ξ) ^ 2) ω ≤
          quadVarianceConstant c_f C_f *
            ((n : ℝ) ^ (-1 : ℝ) +
              (quadraticResolution n : ℝ) * (n : ℝ) ^ (-2 : ℝ))) := by
  classical
  let K := quadraticResolution n
  have hK : 0 < K := by
    dsimp [K, quadraticResolution, dyadicResolution]
    split_ifs <;> positivity
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by norm_num [threshold] at hn; omega)
  let E := MeasurableEquiv.sumPiEquivProdPi (FlatObs n)
  have hEembed : @MeasurableEmbedding
      (TwoSample n n) ((a : FlatIndex n) → FlatObs n a)
      inferInstance MeasurableSpace.pi (flattenSample n) := by
    exact (MeasurableEquiv.sumPiEquivProdPi (FlatObs n)).symm.measurableEmbedding
  let μ := Measure.pi (flatLaw P n)
  let m := MeasurableSpace.comap
    (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi
  let M := fourthDerivativeEnvelope c_f C_f
  let U := 2 * (1 + C_f)
  let V := 1 + C_f + C_f ^ 2
  let C := M * (1 + U) / 2
  let R := (n : ℝ) ^ (-1 : ℝ) + (K : ℝ) * (n : ℝ) ^ (-2 : ℝ)
  let B := M ^ 2 * (1 + U) ^ 4 * (1 + V) ^ 2 * R
  let shift (i : Fin 7) (l : Fin K)
      (z : (a : FlatIndex n) → FlatObs n a) :=
    cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
      pilot c_f C_f (E z) (midpoint K l) i
  let coeff (q : Fin 3 × Fin 7 × Fin 7) (l : Fin K)
      (z : (a : FlatIndex n) → FlatObs n a) :=
    ![(1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) q.2.1 q.2.2,
      (1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) q.2.1 q.2.2 *
        shift q.2.1 l z,
      (1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) q.2.1 q.2.2 *
        shift q.2.2 l z] q.1
  let leaf (q : Fin 3 × Fin 7 × Fin 7) (l : Fin K)
      (z : (a : FlatIndex n) → FlatObs n a) :=
    ![flatCenteredPairCell P ![q.2.1, q.2.2] ![0, 1] l z,
      flatCenteredCellScore P q.2.2 2 l
        (finsetCoordProj (flatBlock n 2) z),
      flatCenteredCellScore P q.2.1 1 l
        (finsetCoordProj (flatBlock n 1) z)] q.1
  let Y (q : Fin 3 × Fin 7 × Fin 7)
      (z : (a : FlatIndex n) → FlatObs n a) :=
    (K : ℝ)⁻¹ * ∑ l : Fin K, coeff q l z * leaf q l z
  let Z (z : (a : FlatIndex n) → FlatObs n a) :=
    ∑ q : Fin 3 × Fin 7 × Fin 7, Y q z
  let G (z : (a : FlatIndex n) → FlatObs n a) :=
    (K : ℝ)⁻¹ * ∑ i : Fin 7, ∑ j : Fin 7, ∑ l : Fin K,
      (1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j *
        shift i l z * shift j l z
  let F (z : (a : FlatIndex n) → FlatObs n a) := quadraticTerm c_f C_f (E z) A
  letI : ∀ a, StandardBorelSpace (FlatObs n a) := fun a => by
    cases a <;> dsimp [FlatObs] <;> infer_instance
  letI : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  have hm : m ≤ (MeasurableSpace.pi : MeasurableSpace ((a : FlatIndex n) → FlatObs n a)) :=
    by
      dsimp [m]
      exact (measurable_finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)).comap_le
  have hM : 0 ≤ M := by
    dsimp [M, fourthDerivativeEnvelope]
    have hc : 0 < c_f := hP.sourceBounds.1.1
    positivity
  have hU : 0 ≤ U := by
    dsimp [U]
    have := hP.sourceBounds.2.1
    positivity
  have hV : 0 ≤ V := by
    dsimp [V]
    nlinarith [sq_nonneg C_f]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcoeff_meas (q : Fin 3 × Fin 7 × Fin 7) (l : Fin K) :
      StronglyMeasurable[m] (coeff q l) := by
    rcases q with ⟨t, i, j⟩
    have hd := stronglyMeasurable_dPhi2_pilot_flatTraining
      c_f C_f L P n hn hP A (midpoint K l) i j
    have hs (k : Fin 7) : StronglyMeasurable[m] (shift k l) := by
      exact stronglyMeasurable_const.sub
        (stronglyMeasurable_pilot_eval_flatTraining c_f C_f n (midpoint K l) k)
    fin_cases t
    · change StronglyMeasurable[m] (fun z =>
        (1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j)
      exact hd.const_mul (1 / 2)
    · change StronglyMeasurable[m] (fun z =>
        (1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j * shift i l z)
      exact (hd.const_mul (1 / 2)).mul (hs i)
    · change StronglyMeasurable[m] (fun z =>
        (1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j * shift j l z)
      exact (hd.const_mul (1 / 2)).mul (hs j)
  have hcoeff (q : Fin 3 × Fin 7 × Fin 7) :
      ∀ᵐ z ∂μ, ∀ l, |coeff q l z| ≤ C := by
    filter_upwards [] with z
    intro l
    rcases q with ⟨t, i, j⟩
    have hd := dPhi2_abs_le c_f C_f hP.sourceBounds.1 hP.sourceBounds.2.1 A
      (pilot c_f C_f (E z) (midpoint K l))
      (pilot_mem_clippingRectangle c_f C_f L P n hn hP (E z) (midpoint K l))
      i j
    have hsi := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l i
    have hsj := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l j
    change |dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j| ≤ M at hd
    change |shift i l z| ≤ U at hsi
    change |shift j l z| ≤ U at hsj
    have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
    fin_cases t
    · change |(1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j| ≤ C
      rw [abs_mul, abs_of_nonneg hhalf]
      dsimp [C]
      calc
        1 / 2 * |dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j| ≤
            1 / 2 * M := mul_le_mul_of_nonneg_left hd hhalf
        _ ≤ M * (1 + U) / 2 := by nlinarith [mul_nonneg hM hU]
    · change |(1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j *
        shift i l z| ≤ C
      rw [abs_mul, abs_mul, abs_of_nonneg hhalf]
      dsimp [C]
      calc
        1 / 2 * |dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j| *
            |shift i l z| ≤ 1 / 2 * M * U := by gcongr
        _ ≤ M * (1 + U) / 2 := by nlinarith [mul_nonneg hM hU]
    · change |(1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j *
        shift j l z| ≤ C
      rw [abs_mul, abs_mul, abs_of_nonneg hhalf]
      dsimp [C]
      calc
        1 / 2 * |dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j| *
            |shift j l z| ≤ 1 / 2 * M * U := by gcongr
        _ ≤ M * (1 + U) / 2 := by nlinarith [mul_nonneg hM hU]
  have hleaf_lp (q : Fin 3 × Fin 7 × Fin 7) (l : Fin K) :
      MemLp (leaf q l) 2 μ := by
    rcases q with ⟨t, i, j⟩
    fin_cases t
    · simpa [leaf, μ] using
        flatCenteredPairCell_memLp c_f C_f L P n K hn hP
          ![i, j] ![0, 1]
          (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all) l
    · simpa [leaf, μ] using
        flatCenteredCellScore_comp_memLp c_f C_f L P n K hn hP j 2 l
    · simpa [leaf, μ] using
        flatCenteredCellScore_comp_memLp c_f C_f L P n K hn hP i 1 l
  have hYlp (q : Fin 3 × Fin 7 × Fin 7) : MemLp (Y q) 2 μ := by
    have hterm (l : Fin K) : MemLp (fun z => coeff q l z * leaf q l z) 2 μ := by
      have hmeas := ((hcoeff_meas q l).mono hm).aestronglyMeasurable.mul
        (hleaf_lp q l).aestronglyMeasurable
      apply (memLp_two_iff_integrable_sq hmeas).2
      have hb : ∀ᵐ z ∂μ, ‖(coeff q l z) ^ 2‖ ≤ C ^ 2 := by
        filter_upwards [hcoeff q] with z hz
        simp only [Real.norm_eq_abs, abs_pow]
        have hzl := hz l
        exact (sq_le_sq₀ (abs_nonneg _) hC).2 hzl
      have hb' : ∀ᵐ z ∂μ, ‖((coeff q l) * (coeff q l)) z‖ ≤ C ^ 2 := by
        simpa only [Pi.mul_apply, pow_two] using hb
      have hi := (hleaf_lp q l).integrable_sq.bdd_mul
        (((hcoeff_meas q l).mono hm).mul ((hcoeff_meas q l).mono hm)).aestronglyMeasurable hb'
      convert hi using 1
      funext z
      dsimp only [Pi.mul_apply]
      ring
    exact (memLp_finsetSum Finset.univ (fun l _ => hterm l)).const_mul (K : ℝ)⁻¹
  have hZlp : MemLp Z 2 μ := by
    simpa only [Z] using
      (memLp_finsetSum Finset.univ (fun q _ => hYlp q))
  have hgterm_meas (i j : Fin 7) (l : Fin K) : StronglyMeasurable[m] (fun z =>
      (1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j *
        shift i l z * shift j l z) := by
    have hd := stronglyMeasurable_dPhi2_pilot_flatTraining
      c_f C_f L P n hn hP A (midpoint K l) i j
    have hsi : StronglyMeasurable[m] (shift i l) := stronglyMeasurable_const.sub
      (stronglyMeasurable_pilot_eval_flatTraining c_f C_f n (midpoint K l) i)
    have hsj : StronglyMeasurable[m] (shift j l) := stronglyMeasurable_const.sub
      (stronglyMeasurable_pilot_eval_flatTraining c_f C_f n (midpoint K l) j)
    exact ((hd.const_mul (1 / 2)).mul hsi).mul hsj
  have hGmeas : StronglyMeasurable[m] G := by
    simpa only [G, Finset.sum_apply] using
      (((Finset.stronglyMeasurable_sum Finset.univ fun i _ =>
      Finset.stronglyMeasurable_sum Finset.univ fun j _ =>
        Finset.stronglyMeasurable_sum Finset.univ fun l _ => hgterm_meas i j l)).const_mul
          (K : ℝ)⁻¹)
  have hGlp : MemLp G 2 μ := by
    have hgterm (i j : Fin 7) (l : Fin K) : MemLp (fun z =>
        (1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j *
          shift i l z * shift j l z) 2 μ := by
      refine MemLp.of_bound ((hgterm_meas i j l).mono hm).aestronglyMeasurable
        (M * U ^ 2) ?_
      filter_upwards [] with z
      simp only [Real.norm_eq_abs, abs_mul]
      have hd := dPhi2_abs_le c_f C_f hP.sourceBounds.1 hP.sourceBounds.2.1 A
        (pilot c_f C_f (E z) (midpoint K l))
        (pilot_mem_clippingRectangle c_f C_f L P n hn hP (E z) (midpoint K l)) i j
      have hsi := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l i
      have hsj := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l j
      change |dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j| ≤ M at hd
      change |shift i l z| ≤ U at hsi
      change |shift j l z| ≤ U at hsj
      have h12 : |(1 / 2 : ℝ)| ≤ 1 := by norm_num
      calc
        |(1 / 2 : ℝ)| * |dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j| *
              |shift i l z| * |shift j l z| ≤ 1 * M * U * U := by
          gcongr
        _ = M * U ^ 2 := by ring
    have hs1 (i j : Fin 7) : MemLp (fun z => ∑ l : Fin K,
        (1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j *
          shift i l z * shift j l z) 2 μ :=
      memLp_finsetSum Finset.univ (fun l _ => hgterm i j l)
    have hs2 (i : Fin 7) : MemLp (fun z => ∑ j : Fin 7, ∑ l : Fin K,
        (1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j *
          shift i l z * shift j l z) 2 μ :=
      memLp_finsetSum Finset.univ (fun j _ => hs1 i j)
    have hs3 : MemLp (fun z => ∑ i : Fin 7, ∑ j : Fin 7, ∑ l : Fin K,
        (1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j *
          shift i l z * shift j l z) 2 μ :=
      memLp_finsetSum Finset.univ (fun i _ => hs2 i)
    exact hs3.const_mul (K : ℝ)⁻¹
  have hdecomp : F = Z + G := by
    funext z
    dsimp only [F, Z, Y, G]
    unfold quadraticTerm
    dsimp only
    change (1 / (2 * (K : ℝ))) * ∑ i : Fin 7, ∑ j : Fin 7, ∑ l : Fin K,
        dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j *
          residual c_f C_f (E z) i K 1 (midpoint K l) *
          residual c_f C_f (E z) j K 2 (midpoint K l) = _
    simp only [Pi.add_apply]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [Fin.sum_univ_three]
    simp [coeff, leaf]
    simp only [← Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [← mul_add, ← mul_add, ← mul_add]
    rw [mul_assoc]
    apply congrArg (fun x : ℝ => (K : ℝ)⁻¹ * x)
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    have hdec := quadratic_residual_three_subset_decomposition
      c_f C_f L P hn hP hK (E z) i j l
    dsimp only at hdec
    simp only [E, MeasurableEquiv.symm_apply_apply] at hdec
    dsimp only [shift]
    simp [flatCenteredPairCell, Fin.prod_univ_two]
    linear_combination
      ((1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f (E z) (midpoint K l)) i j) * hdec
  have hFlp : MemLp F 2 μ := by
    rw [hdecomp]
    exact hZlp.add hGlp
  have hcenter : (fun z => F z - condExp m μ F z) =ᵐ[μ]
      (fun z => Z z - condExp m μ Z z) := by
    rw [hdecomp]
    exact sub_condExp_add_stronglyMeasurable
      (mΩ := MeasurableSpace.pi) (μ := μ) (m := m) hm Z G
      (hZlp.integrable (by norm_num)) (hGlp.integrable (by norm_num)) hGmeas
  have hleaf_bound (q : Fin 3 × Fin 7 × Fin 7) :
      ∀ᵐ z ∂μ, condExp m μ (fun y =>
        (Y q y - condExp m μ (Y q) y) ^ 2) z ≤ B := by
    rcases q with ⟨t, i, j⟩
    have hn1 : (1 : ℝ) ≤ n := by
      have hn' : 1 ≤ n := by norm_num [threshold] at hn; omega
      exact_mod_cast hn'
    have hVU : 25 * V ^ 2 ≤ 4 * (1 + U) ^ 2 * (1 + V) ^ 2 := by
      have hU4 : 4 ≤ U := by dsimp [U]; linarith [hP.sourceBounds.2.1]
      nlinarith [sq_nonneg V, sq_nonneg (1 + V), sq_nonneg (1 + U)]
    have hsingle : 10 * V ≤ 4 * (1 + U) ^ 2 * (1 + V) ^ 2 := by
      have hU4 : 4 ≤ U := by dsimp [U]; linarith [hP.sourceBounds.2.1]
      nlinarith [sq_nonneg V, sq_nonneg (1 + V), sq_nonneg (1 + U)]
    fin_cases t
    · have hraw := conditional_variance_centeredPair_cellAverage
        c_f C_f L P n K hn hP hK ![i, j] ![0, 1]
        (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)
        (fun l z => coeff (0, i, j) l z) C hC
        (fun l => hcoeff_meas (0, i, j) l) (hcoeff (0, i, j))
      filter_upwards [hraw] with z hz
      change condExp m μ (fun y =>
        (Y (0, i, j) y - condExp m μ (Y (0, i, j)) y) ^ 2) z ≤ B
      apply hz.trans
      dsimp [B, C, R, V] at hz ⊢
      rw [Real.rpow_neg_one, show (n : ℝ) ^ (-2 : ℝ) = 1 / (n : ℝ) ^ 2 by
        rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_two]; ring]
      norm_num
      field_simp
      have hscaled := mul_le_mul_of_nonneg_left hVU (sq_nonneg M)
      have hscaled' := mul_le_mul_of_nonneg_right hscaled
        (by positivity : 0 ≤ (K : ℝ) + 1)
      have hnk : (K : ℝ) + 1 ≤ (n : ℝ) + K := by linarith
      have hcoef : 0 ≤ M ^ 2 * (4 * (1 + U) ^ 2 * (1 + V) ^ 2) := by positivity
      have hscaled'' := mul_le_mul_of_nonneg_left hnk hcoef
      nlinarith [hscaled', hscaled'']
    · have hraw := conditional_variance_centeredSingle_cellAverage
        c_f C_f L P n K hn hP hK j 1
        (fun l z => coeff (1, i, j) l z) C hC
        (fun l => hcoeff_meas (1, i, j) l) (hcoeff (1, i, j))
      filter_upwards [hraw] with z hz
      change condExp m μ (fun y =>
        (Y (1, i, j) y - condExp m μ (Y (1, i, j)) y) ^ 2) z ≤ B
      apply hz.trans
      dsimp [B, C, R, V] at hz ⊢
      rw [Real.rpow_neg_one, show (n : ℝ) ^ (-2 : ℝ) = 1 / (n : ℝ) ^ 2 by
        rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_two]; ring]
      norm_num
      field_simp
      have hs := mul_le_mul_of_nonneg_left hsingle (sq_nonneg M)
      have hsn := mul_le_mul_of_nonneg_right hs hnpos.le
      have hnk : (n : ℝ) ≤ n + K := le_add_of_nonneg_right (Nat.cast_nonneg K)
      have hc0 : 0 ≤ M ^ 2 * (4 * (1 + U) ^ 2 * (1 + V) ^ 2) := by positivity
      have hsn' := mul_le_mul_of_nonneg_left hnk hc0
      nlinarith [hsn, hsn']
    · have hraw := conditional_variance_centeredSingle_cellAverage
        c_f C_f L P n K hn hP hK i 0
        (fun l z => coeff (2, i, j) l z) C hC
        (fun l => hcoeff_meas (2, i, j) l) (hcoeff (2, i, j))
      filter_upwards [hraw] with z hz
      change condExp m μ (fun y =>
        (Y (2, i, j) y - condExp m μ (Y (2, i, j)) y) ^ 2) z ≤ B
      apply hz.trans
      dsimp [B, C, R, V] at hz ⊢
      rw [Real.rpow_neg_one, show (n : ℝ) ^ (-2 : ℝ) = 1 / (n : ℝ) ^ 2 by
        rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_two]; ring]
      norm_num
      field_simp
      have hs := mul_le_mul_of_nonneg_left hsingle (sq_nonneg M)
      have hsn := mul_le_mul_of_nonneg_right hs hnpos.le
      have hnk : (n : ℝ) ≤ n + K := le_add_of_nonneg_right (Nat.cast_nonneg K)
      have hc0 : 0 ≤ M ^ 2 * (4 * (1 + U) ^ 2 * (1 + V) ^ 2) := by positivity
      have hsn' := mul_le_mul_of_nonneg_left hnk hc0
      nlinarith [hsn, hsn']
  let W (q : Fin 3 × Fin 7 × Fin 7) (z : (a : FlatIndex n) → FlatObs n a) :=
    Y q z - @condExp ((a : FlatIndex n) → FlatObs n a) ℝ m
      MeasurableSpace.pi _ _ μ (Y q) z
  have hWlp (q : Fin 3 × Fin 7 × Fin 7) : MemLp (W q) 2 μ :=
    (hYlp q).sub ((hYlp q).condExp (by norm_num))
  have hagg := @condExp_sq_finsetSum_le
    ((a : FlatIndex n) → FlatObs n a) (Fin 3 × Fin 7 × Fin 7)
    MeasurableSpace.pi μ m
    (Finset.univ : Finset (Fin 3 × Fin 7 × Fin 7)) W B
    (fun q _ => hWlp q) (fun q _ => by simpa only [W] using hleaf_bound q)
  have hsum_center : (fun z => ∑ q : Fin 3 × Fin 7 × Fin 7, W q z) =ᵐ[μ]
      (fun z => Z z - condExp m μ Z z) := by
    have hs := condExp_finsetSum (μ := μ) (s := Finset.univ) (f := Y)
      (fun q _ => (hYlp q).integrable (by norm_num)) m
    filter_upwards [hs] with z hz
    simp only [Finset.sum_fn, Finset.sum_apply] at hz
    dsimp only [W, Z]
    rw [hz]
    simp only [Finset.sum_sub_distrib]
  have hflat : ∀ᵐ z ∂μ,
      condExp m μ (fun y => (F y - condExp m μ F y) ^ 2) z ≤
        (147 : ℝ) ^ 2 * B := by
    have hsquare : (fun y => (F y - condExp m μ F y) ^ 2) =ᵐ[μ]
        (fun y => (∑ q : Fin 3 × Fin 7 × Fin 7, W q y) ^ 2) :=
      (hcenter.trans hsum_center.symm).fun_comp (fun x => x ^ 2)
    have hc := condExp_congr_ae (m := m) hsquare
    filter_upwards [hagg, hc] with z hz hc
    rw [hc]
    norm_num at hz ⊢
    exact hz
  have hFsquare : Integrable (fun z => (F z - condExp m μ F z) ^ 2) μ := by
    have hcLp : MemLp (condExp m μ F) 2 μ := hFlp.condExp (by norm_num)
    exact (hFlp.sub hcLp).integrable_sq
  have hinner := condExp_comp_flattenSample c_f C_f L P n hP F
    (hFlp.integrable (by norm_num))
  have houter := condExp_comp_flattenSample c_f C_f L P n hP
    (fun z : (a : FlatIndex n) → FlatObs n a =>
      (F z - @condExp ((a : FlatIndex n) → FlatObs n a) ℝ m
        MeasurableSpace.pi _ _ μ F z) ^ 2) hFsquare
  have hmap : @Measure.map _ _ _ MeasurableSpace.pi
      (flattenSample n) (dataLaw P n n) = μ := by
    simpa only [μ] using map_flattenSample_dataLaw c_f C_f L P n hP
  have hflat_pull : ∀ᵐ ω ∂dataLaw P n n,
      condExp m μ (fun y => (F y - condExp m μ F y) ^ 2) (flattenSample n ω) ≤
        (147 : ℝ) ^ 2 * B := by
    have hp : ∀ᵐ z ∂(@Measure.map _ _ _ MeasurableSpace.pi
        (flattenSample n) (dataLaw P n n)),
        condExp m μ (fun y => (F y - condExp m μ F y) ^ 2) z ≤
          (147 : ℝ) ^ 2 * B := by
      rw [hmap]
      exact hflat
    exact (@MeasurableEmbedding.ae_map_iff
      (TwoSample n n) ((a : FlatIndex n) → FlatObs n a)
      inferInstance MeasurableSpace.pi (flattenSample n)
      hEembed
      (fun z => @condExp ((a : FlatIndex n) → FlatObs n a) ℝ m
        MeasurableSpace.pi _ _ μ
          (fun y => (F y - @condExp ((a : FlatIndex n) → FlatObs n a) ℝ m
            MeasurableSpace.pi _ _ μ F y) ^ 2) z ≤
          (147 : ℝ) ^ 2 * B) (dataLaw P n n)).mp hp
  have hFcomp : F ∘ flattenSample n = fun ξ => quadraticTerm c_f C_f ξ A := by
    funext ξ
    simp only [F, E, Function.comp_apply, MeasurableEquiv.apply_symm_apply]
  rw [hFcomp] at hinner
  have hintegrand :
      (fun ξ => (quadraticTerm c_f C_f ξ A -
        condExp (trainingSigma n) (dataLaw P n n)
          (fun ζ => quadraticTerm c_f C_f ζ A) ξ) ^ 2) =ᵐ[dataLaw P n n]
      (fun z => (F z - condExp m μ F z) ^ 2) ∘ flattenSample n := by
    filter_upwards [hinner] with ξ hi
    have hFpoint := congrFun hFcomp ξ
    simp only [Function.comp_apply] at hFpoint ⊢
    rw [← hFpoint, hi]
    rfl
  have houter_congr := condExp_congr_ae (m := trainingSigma n) hintegrand
  constructor
  · letI : MeasurableSpace ((a : FlatIndex n) → FlatObs n a) := MeasurableSpace.pi
    have hlp : MemLp F 2 (@Measure.map _ _ _ MeasurableSpace.pi
        (flattenSample n) (dataLaw P n n)) := by
      rw [hmap]
      exact hFlp
    have hp := hlp.comp_of_map (mβ := MeasurableSpace.pi) hEembed.measurable.aemeasurable
    rwa [hFcomp] at hp
  · filter_upwards [houter_congr, houter, hflat_pull] with ω hc ho hb
    rw [hc, ho]
    apply hb.trans_eq
    dsimp [B, R, M, U, V, quadVarianceConstant, K]
    norm_num
    ring

/-- The exact quadratic correction variance bound.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: quadratic_conditional_variance
lemma quadratic_conditional_variance (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    ∀ᵐ ω ∂dataLaw P n n,
      MeasureTheory.condExp (trainingSigma n) (dataLaw P n n)
        (fun ξ : TwoSample n n =>
        (quadraticTerm c_f C_f ξ A -
          MeasureTheory.condExp (trainingSigma n) (dataLaw P n n)
            (fun ζ : TwoSample n n => quadraticTerm c_f C_f ζ A) ξ) ^ 2) ω ≤
          quadVarianceConstant c_f C_f *
            ((n : ℝ) ^ (-1 : ℝ) +
              (quadraticResolution n : ℝ) * (n : ℝ) ^ (-2 : ℝ)) := by
  exact (quadratic_conditional_variance_with_memLp c_f C_f L P n hn hP A).2

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

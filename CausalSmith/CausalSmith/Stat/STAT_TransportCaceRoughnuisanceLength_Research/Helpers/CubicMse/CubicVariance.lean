module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CenteredCubicCells
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CellMoments
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CellPairCovariance
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ConditionalCellSum
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.IidBlockAverage
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.MarkedCellCovariance
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.QuadVariance
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.SubsetAggregation

/-! # Constants for the cubic conditional variance calculation -/

@[expose] public section
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- [The cubic variance constant object](goal) is defined from [the supplied inputs](hyp:c_f,C_f). -/

noncomputable def cubicVarianceConstant (c_f C_f : ℝ) : ℝ :=
  let d : ℝ := 7
  let U := 2 * (1 + C_f)
  let V := 1 + C_f + C_f ^ 2
  let M := fourthDerivativeEnvelope c_f C_f
  d ^ 6 * (2 ^ (3 : ℕ) - 1) ^ 2 * M ^ 2 *
    (1 + U) ^ 6 * (1 + V) ^ 3

open MeasureTheory
open Causalean.Mathlib.Probability.Independence
open scoped BigOperators

set_option maxHeartbeats 800000 in
-- The explicit 2401-component finite-sum normalization exceeds the default budget.
-- @node: cubic_conditional_variance_with_memLp
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated result about cubic conditional variance with mem lp holds](goal). -/
lemma cubic_conditional_variance_with_memLp (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    MemLp (fun ξ : TwoSample n n => cubicTerm c_f C_f ξ A) 2
      (dataLaw P n n) ∧
    (∀ᵐ ω ∂dataLaw P n n,
      MeasureTheory.condExp (trainingSigma n) (dataLaw P n n)
        (fun ξ : TwoSample n n =>
        (cubicTerm c_f C_f ξ A -
          MeasureTheory.condExp (trainingSigma n) (dataLaw P n n)
            (fun ζ : TwoSample n n => cubicTerm c_f C_f ζ A) ξ) ^ 2) ω ≤
          cubicVarianceConstant c_f C_f *
            ((n : ℝ) ^ (-1 : ℝ) +
              (cubicResolution n : ℝ) * (n : ℝ) ^ (-2 : ℝ) +
              (cubicResolution n : ℝ) ^ 2 * (n : ℝ) ^ (-3 : ℝ))) := by
  classical
  let K := cubicResolution n
  have hK : 0 < K := by
    dsimp [K, cubicResolution, dyadicResolution]
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
  let C := M * (1 + U) ^ 2 / 6
  let R := (n : ℝ) ^ (-1 : ℝ) + (K : ℝ) * (n : ℝ) ^ (-2 : ℝ) +
    (K : ℝ) ^ 2 * (n : ℝ) ^ (-3 : ℝ)
  let B := M ^ 2 * (1 + U) ^ 6 * (1 + V) ^ 3 * R
  let shift (i : Fin 7) (l : Fin K)
      (z : (a : FlatIndex n) → FlatObs n a) :=
    cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
      pilot c_f C_f (E z) (midpoint K l) i
  let coeff (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) (l : Fin K)
      (z : (a : FlatIndex n) → FlatObs n a) :=
    let a := (1 / 6 : ℝ) *
      dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) q.2.1 q.2.2.1 q.2.2.2
    ![a,
      a * shift q.2.1 l z,
      a * shift q.2.2.1 l z,
      a * shift q.2.2.2 l z,
      a * shift q.2.1 l z * shift q.2.2.1 l z,
      a * shift q.2.1 l z * shift q.2.2.2 l z,
      a * shift q.2.2.1 l z * shift q.2.2.2 l z] q.1
  let leaf (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) (l : Fin K)
      (z : (a : FlatIndex n) → FlatObs n a) :=
    ![flatCenteredCubicCell P ![q.2.1, q.2.2.1, q.2.2.2] l z,
      flatCenteredPairCell P ![q.2.2.1, q.2.2.2] ![1, 2] l z,
      flatCenteredPairCell P ![q.2.1, q.2.2.2] ![0, 2] l z,
      flatCenteredPairCell P ![q.2.1, q.2.2.1] ![0, 1] l z,
      flatCenteredCellScore P q.2.2.2 3 l
        (finsetCoordProj (flatBlock n 3) z),
      flatCenteredCellScore P q.2.2.1 2 l
        (finsetCoordProj (flatBlock n 2) z),
      flatCenteredCellScore P q.2.1 1 l
        (finsetCoordProj (flatBlock n 1) z)] q.1
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
  have hcoeff_meas (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) (l : Fin K) :
      StronglyMeasurable[m] (coeff q l) := by
    rcases q with ⟨t, i, j, k⟩
    have hd := stronglyMeasurable_dPhi3_pilot_flatTraining
      c_f C_f L P n hn hP A (midpoint K l) i j k
    have hs (r : Fin 7) : StronglyMeasurable[m] (shift r l) :=
      stronglyMeasurable_const.sub
        (stronglyMeasurable_pilot_eval_flatTraining c_f C_f n (midpoint K l) r)
    fin_cases t
    all_goals
      change StronglyMeasurable[m] _
      dsimp only [coeff]
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
    have hsi := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l i
    have hsj := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l j
    have hsk := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l k
    change |dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k| ≤ M at hd
    change |shift i l z| ≤ U at hsi
    change |shift j l z| ≤ U at hsj
    change |shift k l z| ≤ U at hsk
    have h16 : (0 : ℝ) ≤ 1 / 6 := by norm_num
    have hbase : |(1 / 6 : ℝ) *
        dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k| ≤ M / 6 := by
      rw [abs_mul, abs_of_nonneg h16]
      exact (mul_le_mul_of_nonneg_left hd h16).trans_eq (by ring)
    have h0 : M / 6 ≤ C := by
      dsimp [C]
      nlinarith [mul_nonneg hM hU, sq_nonneg U]
    have h1 : M / 6 * U ≤ C := by
      dsimp [C]
      nlinarith [mul_nonneg hM hU, mul_nonneg hM (sq_nonneg U)]
    have h2 : M / 6 * U * U ≤ C := by
      dsimp [C]
      nlinarith [mul_nonneg hM hU]
    fin_cases t
    · exact hbase.trans h0
    · change |(1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
          shift i l z| ≤ C
      rw [abs_mul]; exact (mul_le_mul hbase hsi (abs_nonneg _) (by positivity)).trans h1
    · change |(1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
          shift j l z| ≤ C
      rw [abs_mul]; exact (mul_le_mul hbase hsj (abs_nonneg _) (by positivity)).trans h1
    · change |(1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
          shift k l z| ≤ C
      rw [abs_mul]; exact (mul_le_mul hbase hsk (abs_nonneg _) (by positivity)).trans h1
    · change |(1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
          shift i l z * shift j l z| ≤ C
      rw [abs_mul, abs_mul]
      exact (mul_le_mul (mul_le_mul hbase hsi (abs_nonneg _) (by positivity)) hsj
        (abs_nonneg _) (by positivity)).trans h2
    · change |(1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
          shift i l z * shift k l z| ≤ C
      rw [abs_mul, abs_mul]
      exact (mul_le_mul (mul_le_mul hbase hsi (abs_nonneg _) (by positivity)) hsk
        (abs_nonneg _) (by positivity)).trans h2
    · change |(1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
          shift j l z * shift k l z| ≤ C
      rw [abs_mul, abs_mul]
      exact (mul_le_mul (mul_le_mul hbase hsj (abs_nonneg _) (by positivity)) hsk
        (abs_nonneg _) (by positivity)).trans h2
  have hleaf_lp (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) (l : Fin K) :
      MemLp (leaf q l) 2 μ := by
    rcases q with ⟨t, i, j, k⟩
    fin_cases t
    · simpa [leaf, μ] using
        flatCenteredCubicCell_memLp c_f C_f L P n K hn hP ![i, j, k] l
    · simpa [leaf, μ] using
        flatCenteredPairCell_memLp c_f C_f L P n K hn hP ![j, k] ![1, 2]
          (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all) l
    · simpa [leaf, μ] using
        flatCenteredPairCell_memLp c_f C_f L P n K hn hP ![i, k] ![0, 2]
          (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all) l
    · simpa [leaf, μ] using
        flatCenteredPairCell_memLp c_f C_f L P n K hn hP ![i, j] ![0, 1]
          (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all) l
    · simpa [leaf, μ] using flatCenteredCellScore_comp_memLp
        c_f C_f L P n K hn hP k 3 l
    · simpa [leaf, μ] using flatCenteredCellScore_comp_memLp
        c_f C_f L P n K hn hP j 2 l
    · simpa [leaf, μ] using flatCenteredCellScore_comp_memLp
        c_f C_f L P n K hn hP i 1 l
  have hYlp (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) : MemLp (Y q) 2 μ := by
    have hterm (l : Fin K) : MemLp (fun z => coeff q l z * leaf q l z) 2 μ := by
      have hmeas := ((hcoeff_meas q l).mono hm).aestronglyMeasurable.mul
        (hleaf_lp q l).aestronglyMeasurable
      apply (memLp_two_iff_integrable_sq hmeas).2
      have hb : ∀ᵐ z ∂μ, ‖(coeff q l z) ^ 2‖ ≤ C ^ 2 := by
        filter_upwards [hcoeff q] with z hz
        simp only [Real.norm_eq_abs, abs_pow]
        exact (sq_le_sq₀ (abs_nonneg _) hC).2 (hz l)
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
    simpa only [Z] using memLp_finsetSum Finset.univ (fun q _ => hYlp q)
  have hgterm_meas (i j k : Fin 7) (l : Fin K) : StronglyMeasurable[m] (fun z =>
      (1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
        shift i l z * shift j l z * shift k l z) := by
    have hd := stronglyMeasurable_dPhi3_pilot_flatTraining
      c_f C_f L P n hn hP A (midpoint K l) i j k
    have hs (r : Fin 7) : StronglyMeasurable[m] (shift r l) :=
      stronglyMeasurable_const.sub
        (stronglyMeasurable_pilot_eval_flatTraining c_f C_f n (midpoint K l) r)
    exact ((((hd.const_mul (1 / 6)).mul (hs i)).mul (hs j)).mul (hs k))
  have hGmeas : StronglyMeasurable[m] G := by
    simpa only [G, Finset.sum_apply] using
      ((Finset.stronglyMeasurable_sum Finset.univ fun i _ =>
        Finset.stronglyMeasurable_sum Finset.univ fun j _ =>
        Finset.stronglyMeasurable_sum Finset.univ fun k _ =>
        Finset.stronglyMeasurable_sum Finset.univ fun l _ => hgterm_meas i j k l)).const_mul
          (K : ℝ)⁻¹
  have hGlp : MemLp G 2 μ := by
    have hgterm (i j k : Fin 7) (l : Fin K) : MemLp (fun z =>
        (1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
          shift i l z * shift j l z * shift k l z) 2 μ := by
      refine MemLp.of_bound ((hgterm_meas i j k l).mono hm).aestronglyMeasurable
        (M * U ^ 3) ?_
      filter_upwards [] with z
      simp only [Real.norm_eq_abs, abs_mul]
      have hd := dPhi3_abs_le c_f C_f hP.sourceBounds.1 hP.sourceBounds.2.1 A
        (pilot c_f C_f (E z) (midpoint K l))
        (pilot_mem_clippingRectangle c_f C_f L P n hn hP (E z) (midpoint K l)) i j k
      have hsi := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l i
      have hsj := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l j
      have hsk := abs_trainingShift_le c_f C_f L P n K hn hP hK (E z) l k
      change |dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k| ≤ M at hd
      change |shift i l z| ≤ U at hsi
      change |shift j l z| ≤ U at hsj
      change |shift k l z| ≤ U at hsk
      calc
        |(1 / 6 : ℝ)| * |dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k| *
            |shift i l z| * |shift j l z| * |shift k l z| ≤ 1 * M * U * U * U := by
          gcongr <;> norm_num
        _ = M * U ^ 3 := by ring
    have hs1 (i j k : Fin 7) : MemLp (fun z => ∑ l : Fin K,
        (1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f (E z) (midpoint K l)) i j k *
          shift i l z * shift j l z * shift k l z) 2 μ :=
      memLp_finsetSum Finset.univ (fun l _ => hgterm i j k l)
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
  have hFlp : MemLp F 2 μ := by
    rw [hdecomp]
    exact hZlp.add hGlp
  have hcenter : (fun z => F z - condExp m μ F z) =ᵐ[μ]
      (fun z => Z z - condExp m μ Z z) := by
    rw [hdecomp]
    exact sub_condExp_add_stronglyMeasurable
      (mΩ := MeasurableSpace.pi) (μ := μ) (m := m) hm Z G
      (hZlp.integrable (by norm_num)) (hGlp.integrable (by norm_num)) hGmeas
  have hleaf_bound (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) :
      ∀ᵐ z ∂μ, condExp m μ (fun y =>
        (Y q y - condExp m μ (Y q) y) ^ 2) z ≤ B := by
    rcases q with ⟨t, i, j, k⟩
    have hU4 : 4 ≤ U := by dsimp [U]; linarith [hP.sourceBounds.2.1]
    have hV1 : 1 ≤ 1 + V := by linarith
    have hsingle : 10 * V ≤ 36 * (1 + U) ^ 2 * (1 + V) ^ 3 := by
      nlinarith [mul_nonneg hV (sq_nonneg (1 + U)),
        mul_nonneg (sq_nonneg (1 + V)) (by linarith : 0 ≤ 1 + V)]
    have hpair : 25 * V ^ 2 ≤ 36 * (1 + U) ^ 2 * (1 + V) ^ 3 := by
      nlinarith [sq_nonneg V,
        mul_nonneg (sq_nonneg (1 + V)) (by linarith : 0 ≤ 1 + V),
        mul_nonneg (sq_nonneg (1 + U)) (by linarith : 0 ≤ 1 + V)]
    have hcubic : 125 * V ^ 3 ≤ 36 * (1 + U) ^ 2 * (1 + V) ^ 3 := by
      have hVpow : V ^ 3 ≤ (1 + V) ^ 3 := by nlinarith [sq_nonneg V]
      have hfactor : 125 ≤ 36 * (1 + U) ^ 2 := by nlinarith [sq_nonneg (1 + U)]
      exact (mul_le_mul_of_nonneg_left hVpow (by norm_num)).trans
        (mul_le_mul_of_nonneg_right hfactor (by positivity))
    have finish_single :
        C ^ 2 * V ^ 1 * ((K : ℝ) ^ 0 / ((n : ℝ) / 5) ^ 1 +
          1 / ((n : ℝ) / 5) ^ 1) ≤ B := by
      dsimp [B, C, R]
      rw [Real.rpow_neg_one,
        show (n : ℝ) ^ (-2 : ℝ) = 1 / (n : ℝ) ^ 2 by
          rw [Real.rpow_neg hnpos.le, Real.rpow_two]; ring,
        show (n : ℝ) ^ (-3 : ℝ) = 1 / (n : ℝ) ^ 3 by
          rw [Real.rpow_neg hnpos.le, one_div]
          exact congrArg Inv.inv (Real.rpow_natCast (n : ℝ) 3)]
      norm_num
      field_simp
      have hs := mul_le_mul_of_nonneg_left hsingle (sq_nonneg M)
      have hsn := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ (n : ℝ) ^ 2)
      have hpoly : (n : ℝ) ^ 2 ≤ n * (n + K) + K ^ 2 := by
        nlinarith [mul_nonneg hnpos.le (Nat.cast_nonneg K), sq_nonneg (K : ℝ)]
      have hr := mul_le_mul_of_nonneg_left hpoly
        (by positivity : 0 ≤ M ^ 2 * (36 * (1 + U) ^ 2 * (1 + V) ^ 3))
      ring_nf at hsn hr ⊢
      exact hsn.trans hr
    have finish_pair :
        C ^ 2 * V ^ 2 * ((K : ℝ) ^ 1 / ((n : ℝ) / 5) ^ 2 +
          1 / ((n : ℝ) / 5) ^ 2) ≤ B := by
      dsimp [B, C, R]
      rw [Real.rpow_neg_one,
        show (n : ℝ) ^ (-2 : ℝ) = 1 / (n : ℝ) ^ 2 by
          rw [Real.rpow_neg hnpos.le, Real.rpow_two]; ring,
        show (n : ℝ) ^ (-3 : ℝ) = 1 / (n : ℝ) ^ 3 by
          rw [Real.rpow_neg hnpos.le, one_div]
          exact congrArg Inv.inv (Real.rpow_natCast (n : ℝ) 3)]
      norm_num
      field_simp
      have hs := mul_le_mul_of_nonneg_left hpair (sq_nonneg M)
      have hsn := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ (n : ℝ) * (K + 1))
      have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (show 1 ≤ n by norm_num [threshold] at hn; omega)
      have hnk : (n : ℝ) * (K + 1) ≤ n ^ 2 + n * K + K ^ 2 := by
        nlinarith [hn1, sq_nonneg (K : ℝ)]
      have hc0 : 0 ≤ M ^ 2 * (36 * (1 + U) ^ 2 * (1 + V) ^ 3) := by positivity
      have hr := mul_le_mul_of_nonneg_left hnk hc0
      ring_nf at hsn hr ⊢
      exact hsn.trans hr
    have finish_cubic :
        C ^ 2 * V ^ 3 * ((K : ℝ) ^ 2 / ((n : ℝ) / 5) ^ 3 +
          1 / ((n : ℝ) / 5) ^ 3) ≤ B := by
      dsimp [B, C, R]
      rw [Real.rpow_neg_one,
        show (n : ℝ) ^ (-2 : ℝ) = 1 / (n : ℝ) ^ 2 by
          rw [Real.rpow_neg hnpos.le, Real.rpow_two]; ring,
        show (n : ℝ) ^ (-3 : ℝ) = 1 / (n : ℝ) ^ 3 by
          rw [Real.rpow_neg hnpos.le, one_div]
          exact congrArg Inv.inv (Real.rpow_natCast (n : ℝ) 3)]
      norm_num
      field_simp
      have hs := mul_le_mul_of_nonneg_left hcubic (sq_nonneg M)
      have hsk := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ (K : ℝ) ^ 2 + 1)
      have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (show 1 ≤ n by norm_num [threshold] at hn; omega)
      have hkn : (K : ℝ) ^ 2 + 1 ≤ n ^ 2 + n * K + K ^ 2 := by
        nlinarith [hn1]
      have hc0 : 0 ≤ M ^ 2 * (36 * (1 + U) ^ 2 * (1 + V) ^ 3) := by positivity
      have hr := mul_le_mul_of_nonneg_left hkn hc0
      ring_nf at hsk hr ⊢
      exact hsk.trans hr
    fin_cases t
    · have hraw := conditional_variance_centeredCubic_cellAverage
        c_f C_f L P n K hn hP hK ![i, j, k]
        (fun l z => coeff (0, i, j, k) l z) C hC
        (fun l => hcoeff_meas (0, i, j, k) l) (hcoeff (0, i, j, k))
      filter_upwards [hraw] with z hz
      exact hz.trans finish_cubic
    · have hraw := conditional_variance_centeredPair_cellAverage
        c_f C_f L P n K hn hP hK ![j, k] ![1, 2]
        (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)
        (fun l z => coeff (1, i, j, k) l z) C hC
        (fun l => hcoeff_meas (1, i, j, k) l) (hcoeff (1, i, j, k))
      filter_upwards [hraw] with z hz
      exact hz.trans finish_pair
    · have hraw := conditional_variance_centeredPair_cellAverage
        c_f C_f L P n K hn hP hK ![i, k] ![0, 2]
        (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)
        (fun l z => coeff (2, i, j, k) l z) C hC
        (fun l => hcoeff_meas (2, i, j, k) l) (hcoeff (2, i, j, k))
      filter_upwards [hraw] with z hz
      exact hz.trans finish_pair
    · have hraw := conditional_variance_centeredPair_cellAverage
        c_f C_f L P n K hn hP hK ![i, j] ![0, 1]
        (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)
        (fun l z => coeff (3, i, j, k) l z) C hC
        (fun l => hcoeff_meas (3, i, j, k) l) (hcoeff (3, i, j, k))
      filter_upwards [hraw] with z hz
      exact hz.trans finish_pair
    · have hraw := conditional_variance_centeredSingle_cellAverage
        c_f C_f L P n K hn hP hK k 2
        (fun l z => coeff (4, i, j, k) l z) C hC
        (fun l => hcoeff_meas (4, i, j, k) l) (hcoeff (4, i, j, k))
      filter_upwards [hraw] with z hz
      exact hz.trans finish_single
    · have hraw := conditional_variance_centeredSingle_cellAverage
        c_f C_f L P n K hn hP hK j 1
        (fun l z => coeff (5, i, j, k) l z) C hC
        (fun l => hcoeff_meas (5, i, j, k) l) (hcoeff (5, i, j, k))
      filter_upwards [hraw] with z hz
      exact hz.trans finish_single
    · have hraw := conditional_variance_centeredSingle_cellAverage
        c_f C_f L P n K hn hP hK i 0
        (fun l z => coeff (6, i, j, k) l z) C hC
        (fun l => hcoeff_meas (6, i, j, k) l) (hcoeff (6, i, j, k))
      filter_upwards [hraw] with z hz
      exact hz.trans finish_single
  let W (q : Fin 7 × Fin 7 × Fin 7 × Fin 7)
      (z : (a : FlatIndex n) → FlatObs n a) :=
    Y q z - @condExp ((a : FlatIndex n) → FlatObs n a) ℝ m
      MeasurableSpace.pi _ _ μ (Y q) z
  have hWlp (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) : MemLp (W q) 2 μ :=
    (hYlp q).sub ((hYlp q).condExp (by norm_num))
  have hagg := @condExp_sq_finsetSum_le
    ((a : FlatIndex n) → FlatObs n a) (Fin 7 × Fin 7 × Fin 7 × Fin 7)
    MeasurableSpace.pi μ m
    (Finset.univ : Finset (Fin 7 × Fin 7 × Fin 7 × Fin 7)) W B
    (fun q _ => hWlp q) (fun q _ => by simpa only [W] using hleaf_bound q)
  have hsum_center : (fun z => ∑ q : Fin 7 × Fin 7 × Fin 7 × Fin 7, W q z) =ᵐ[μ]
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
        (2401 : ℝ) ^ 2 * B := by
    have hsquare : (fun y => (F y - condExp m μ F y) ^ 2) =ᵐ[μ]
        (fun y => (∑ q : Fin 7 × Fin 7 × Fin 7 × Fin 7, W q y) ^ 2) :=
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
        (2401 : ℝ) ^ 2 * B := by
    have hp : ∀ᵐ z ∂(@Measure.map _ _ _ MeasurableSpace.pi
        (flattenSample n) (dataLaw P n n)),
        condExp m μ (fun y => (F y - condExp m μ F y) ^ 2) z ≤
          (2401 : ℝ) ^ 2 * B := by
      rw [hmap]
      exact hflat
    exact (@MeasurableEmbedding.ae_map_iff
      (TwoSample n n) ((a : FlatIndex n) → FlatObs n a)
      inferInstance MeasurableSpace.pi (flattenSample n) hEembed
      (fun z => @condExp ((a : FlatIndex n) → FlatObs n a) ℝ m
        MeasurableSpace.pi _ _ μ
          (fun y => (F y - @condExp ((a : FlatIndex n) → FlatObs n a) ℝ m
            MeasurableSpace.pi _ _ μ F y) ^ 2) z ≤
          (2401 : ℝ) ^ 2 * B) (dataLaw P n n)).mp hp
  have hFcomp : F ∘ flattenSample n = fun ξ => cubicTerm c_f C_f ξ A := by
    funext ξ
    simp only [F, E, Function.comp_apply, MeasurableEquiv.apply_symm_apply]
  rw [hFcomp] at hinner
  have hintegrand :
      (fun ξ => (cubicTerm c_f C_f ξ A -
        condExp (trainingSigma n) (dataLaw P n n)
          (fun ζ => cubicTerm c_f C_f ζ A) ξ) ^ 2) =ᵐ[dataLaw P n n]
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
    dsimp [B, R, M, U, V, cubicVarianceConstant, K]
    norm_num
    ring

/-- The exact cubic correction variance bound.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: cubic_conditional_variance
lemma cubic_conditional_variance (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    ∀ᵐ ω ∂dataLaw P n n,
      MeasureTheory.condExp (trainingSigma n) (dataLaw P n n)
        (fun ξ : TwoSample n n =>
        (cubicTerm c_f C_f ξ A -
          MeasureTheory.condExp (trainingSigma n) (dataLaw P n n)
            (fun ζ : TwoSample n n => cubicTerm c_f C_f ζ A) ξ) ^ 2) ω ≤
          cubicVarianceConstant c_f C_f *
            ((n : ℝ) ^ (-1 : ℝ) +
              (cubicResolution n : ℝ) * (n : ℝ) ^ (-2 : ℝ) +
              (cubicResolution n : ℝ) ^ 2 * (n : ℝ) ^ (-3 : ℝ)) := by
  exact (cubic_conditional_variance_with_memLp c_f C_f L P n hn hP A).2

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

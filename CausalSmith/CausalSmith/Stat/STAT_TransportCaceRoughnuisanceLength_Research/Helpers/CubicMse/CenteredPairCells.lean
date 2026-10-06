module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CenteredSingleCells

/-! # Two-residual contributions to quadratic and cubic variance

Roadmap (16) for two actual centered histograms on distinct evaluation blocks.
The same statement handles all three two-block subsets of the cubic statistic.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Independence
open Causalean.Mathlib.Probability.Independence.Conditional
open scoped BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The product of two centered cell heights on distinct evaluation blocks.  For [the displayed assumptions and inputs](hyp:P,n,K,i,b,l,x), [the stated object is defined](goal). -/
-- @node: flatCenteredPairCell
noncomputable def flatCenteredPairCell (P : TransportLaw) {n K : ℕ}
    (i : Fin 2 → Fin 7) (b : Fin 2 → Fin 3) (l : Fin K)
    (x : (a : FlatIndex n) → FlatObs n a) : ℝ :=
  ∏ t : Fin 2, flatCenteredCellScore P (i t) (b t).succ l
    (finsetCoordProj (flatBlock n (b t).succ) x)

/-- The two-residual member obeys the exact `C² V² (K+1)/(n/5)²`
conditional variance estimate, derived from disjoint-block independence.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,i,b,hb,c,C,hC,hcmeas,hc), [the stated conclusion holds](goal). -/
-- @node: conditional_variance_centeredPair_cellAverage
lemma conditional_variance_centeredPair_cellAverage (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (i : Fin 2 → Fin 7) (b : Fin 2 → Fin 3) (hb : Function.Injective b)
    (c : Fin K → ((a : FlatIndex n) → FlatObs n a) → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hcmeas : ∀ l, StronglyMeasurable[
      MeasurableSpace.comap (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi] (c l))
    (hc : ∀ᵐ x ∂Measure.pi (flatLaw P n), ∀ l, |c l x| ≤ C) :
    ∀ᵐ x ∂Measure.pi (flatLaw P n),
      condExp (MeasurableSpace.comap
        (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi)
        (Measure.pi (flatLaw P n)) (fun y =>
          ((K : ℝ)⁻¹ * ∑ l : Fin K, c l y * flatCenteredPairCell P i b l y -
            condExp (MeasurableSpace.comap
              (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi)
              (Measure.pi (flatLaw P n))
              (fun z => (K : ℝ)⁻¹ * ∑ l : Fin K, c l z * flatCenteredPairCell P i b l z) y) ^ 2) x ≤
      C ^ 2 * (1 + C_f + C_f ^ 2) ^ 2 *
        ((K : ℝ) ^ 1 / ((n : ℝ) / 5) ^ 2 + 1 / ((n : ℝ) / 5) ^ 2) := by
  let : ∀ a, StandardBorelSpace (FlatObs n a) := fun a => by
    cases a <;> dsimp [FlatObs] <;> infer_instance
  let : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  let μ := Measure.pi (flatLaw P n)
  let m := MeasurableSpace.comap
    (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi
  let : MeasurableSpace ((a : FlatIndex n) → FlatObs n a) := MeasurableSpace.pi
  let X (l : Fin K) := flatCenteredPairCell P (n := n) i b l
  let κ (t : Fin 2) (l r : Fin K) := covariance
    (fun x => flatBlockHeight (i t) (b t).succ l (finsetCoordProj (flatBlock n (b t).succ) x))
    (fun x => flatBlockHeight (i t) (b t).succ r (finsetCoordProj (flatBlock n (b t).succ) x)) μ
  have hm : m ≤ (inferInstance : MeasurableSpace ((a : FlatIndex n) → FlatObs n a)) :=
    (measurable_finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)).comap_le
  let F (t : Fin 2) (l : Fin K) := flatCenteredCellScore P (n := n) (i t) (b t).succ l
  have hf (t : Fin 2) (l : Fin K) : Measurable (F t l) :=
    (measurable_flatBlockHeight (i t) (b t).succ l).sub measurable_const
  have hflp (t : Fin 2) (l : Fin K) :
      MemLp (fun x => F t l (finsetCoordProj (flatBlock n (b t).succ) x)) 2 μ :=
    (flatBlockHeight_memLp c_f C_f L P n K hn hP (i t) (b t).succ l).sub (memLp_const _)
  have hX (l : Fin K) : X l = (fun x =>
      F 0 l (finsetCoordProj (flatBlock n (b 0).succ) x) *
      F 1 l (finsetCoordProj (flatBlock n (b 1).succ) x)) := by
    funext x
    simp only [X, flatCenteredPairCell, Fin.prod_univ_two, F]
  have hdisj : Disjoint (flatBlock n (b 0).succ) (flatBlock n (b 1).succ) :=
    flatBlock_eval_pairwise n (hb.ne (by decide : (0 : Fin 2) ≠ 1))
  have hind := condIndepFun_eval_pair (flatLaw P n) (flatBlock n 0)
    (fun t : Fin 3 => flatBlock n t.succ) (flatBlock_training_disjoint n)
    (flatBlock_eval_pairwise n) (b 0) (b 1) (hb.ne (by decide : (0 : Fin 2) ≠ 1))
  have hprod (l : Fin K) : Integrable (fun x =>
      F 0 l (finsetCoordProj (flatBlock n (b 0).succ) x) *
      F 1 l (finsetCoordProj (flatBlock n (b 1).succ) x)) μ :=
    integrable_twoBlockProduct (flatLaw P n) _ _ hdisj (F 0 l) (F 1 l)
      (hf 0 l) (hf 1 l) ((hflp 0 l).integrable (by norm_num))
      ((hflp 1 l).integrable (by norm_num))
  have hlp (l : Fin K) : MemLp (X l) 2 μ := by
    have hs := integrable_twoBlockProduct (flatLaw P n) _ _ hdisj
      (fun z => F 0 l z ^ 2) (fun z => F 1 l z ^ 2)
      ((hf 0 l).pow_const 2) ((hf 1 l).pow_const 2)
      ((hflp 0 l).integrable_sq) ((hflp 1 l).integrable_sq)
    apply (memLp_two_iff_integrable_sq ?_).mpr
    · simpa only [X, flatCenteredPairCell, Fin.prod_univ_two, mul_pow, F] using hs
    · rw [hX]
      exact (((hf 0 l).comp (measurable_finsetCoordProj _)).mul
        ((hf 1 l).comp (measurable_finsetCoordProj _))).aestronglyMeasurable
  have hz (l : Fin K) : condExp m μ (X l) =ᵐ[μ]
      (0 : ((a : FlatIndex n) → FlatObs n a) → ℝ) := by
    have hp := condExp_mul_of_condIndep hm
      (measurable_finsetCoordProj (flatBlock n (b 0).succ))
      (measurable_finsetCoordProj (flatBlock n (b 1).succ)) hind
      (hf 0 l) (hf 1 l) ((hflp 0 l).integrable (by norm_num))
      ((hflp 1 l).integrable (by norm_num)) (hprod l)
    have hz0 := condExp_centeredBlockScore_zero (flatLaw P n)
      (flatBlock n 0) (flatBlock n (b 0).succ) (flatBlock_training_disjoint n (b 0))
      (flatBlockHeight (i 0) (b 0).succ l) (measurable_flatBlockHeight _ _ _)
      (flatBlockHeight_memLp c_f C_f L P n K hn hP (i 0) (b 0).succ l)
    rw [hX]
    filter_upwards [hp, hz0] with x hp hz0
    change condExp m μ (fun y =>
      F 0 l (finsetCoordProj (flatBlock n (b 0).succ) y) *
      F 1 l (finsetCoordProj (flatBlock n (b 1).succ) y)) x = 0
    simpa only [X, flatCenteredPairCell, Fin.prod_univ_two, F, flatCenteredCellScore,
      Pi.mul_apply, hz0, Pi.zero_apply, zero_mul, μ, m] using hp
  have hx (l r : Fin K) : condExp m μ (fun x => X l x * X r x) =ᵐ[μ]
      (fun _ => ∏ t : Fin 2, κ t l r) := by
    let G (t : Fin 2) := fun z => F t l z * F t r z
    have hg (t : Fin 2) : Measurable (G t) := (hf t l).mul (hf t r)
    have hgi (t : Fin 2) : Integrable
        (fun x => G t (finsetCoordProj (flatBlock n (b t).succ) x)) μ :=
      (hflp t l).integrable_mul (hflp t r)
    have hgp := integrable_twoBlockProduct (flatLaw P n) _ _ hdisj
      (G 0) (G 1) (hg 0) (hg 1) (hgi 0) (hgi 1)
    have hp := condExp_mul_of_condIndep hm
      (measurable_finsetCoordProj (flatBlock n (b 0).succ))
      (measurable_finsetCoordProj (flatBlock n (b 1).succ)) hind
      (hg 0) (hg 1) (hgi 0) (hgi 1) hgp
    have hcross (t : Fin 2) := condExp_centeredBlockCross_eq_covariance
      (flatLaw P n) (flatBlock n 0) (flatBlock n (b t).succ)
      (flatBlock_training_disjoint n (b t))
      (flatBlockHeight (i t) (b t).succ l) (flatBlockHeight (i t) (b t).succ r)
      (measurable_flatBlockHeight _ _ _) (measurable_flatBlockHeight _ _ _)
    have heq : (fun x => X l x * X r x) =
        (fun x => G 0 (finsetCoordProj (flatBlock n (b 0).succ) x) *
          G 1 (finsetCoordProj (flatBlock n (b 1).succ) x)) := by
      funext x
      simp only [X, flatCenteredPairCell, Fin.prod_univ_two, G, F]
      ring
    rw [heq]
    filter_upwards [hp, hcross 0, hcross 1] with x hp h0 h1
    simpa only [G, F, flatCenteredCellScore, μ, m, Pi.mul_apply, h0, h1,
      Fin.prod_univ_two, κ] using hp
  have hnpos : (0 : ℝ) < n := by
    norm_num [threshold] at hn
    exact_mod_cast (show 0 < n by omega)
  have hB : 0 < (n : ℝ) / 5 := by positivity
  have hCf : 0 ≤ C_f := le_trans (by norm_num) hP.sourceBounds.2.1.le
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hV : 0 ≤ 1 + C_f + C_f ^ 2 := by positivity
  have hcard (t : Fin 2) : 0 < (blockIdx n (b t).succ).card := by
    rw [block_card]
    exact_mod_cast (lt_of_lt_of_le hB (block_size_lower n hn (b t).succ))
  apply conditional_variance_weighted_centered_cells (q := 1) hm hK X c κ
    C (1 + C_f + C_f ^ 2) ((n : ℝ) / 5) hC hV hB hcmeas hc hlp hz hx
  · intro t l
    have hb := flatBlockHeight_same_cell_covariance_le c_f C_f L P n K hP hK
      (b t).succ (hcard t) l (i t) (i t)
    have hnum : (K : ℝ) * C_f + C_f ^ 2 ≤ (1 + C_f + C_f ^ 2) * K := by
      nlinarith [mul_nonneg (sq_nonneg C_f) (sub_nonneg.mpr hKr)]
    have hd := block_size_lower n hn (b t).succ
    rw [← block_card] at hd
    exact hb.trans (div_le_div₀ (by positivity) hnum hB hd)
  · intro t l r hlr
    have hb := flatBlockHeight_off_cell_covariance_le c_f C_f L P n K hP hK
      (b t).succ (hcard t) hlr (i t) (i t)
    have hd := block_size_lower n hn (b t).succ
    rw [← block_card] at hd
    exact hb.trans (div_le_div₀ hV (by linarith) hB hd)

/-- The flattened pair is exactly the product of two of the paper's marked
histograms at a cell midpoint, centered at their experiment means.  Under [the displayed assumptions and inputs](hyp:P,n,K,hn,hK,i,b,l), [the stated conclusion holds](goal). -/
-- @node: flatCenteredPairCell_flattenSample
lemma flatCenteredPairCell_flattenSample (P : TransportLaw) {n K : ℕ}
    (hn : threshold ≤ n) (hK : 0 < K) (i : Fin 2 → Fin 7)
    (b : Fin 2 → Fin 3) (l : Fin K) (ω : TwoSample n n) :
    flatCenteredPairCell P i b l (flattenSample n ω) =
      ∏ t : Fin 2, (markedHistogram ω (i t) K (b t).succ (midpoint K l) -
        ∫ x, flatBlockHeight (i t) (b t).succ l
          (finsetCoordProj (flatBlock n (b t).succ) x) ∂Measure.pi (flatLaw P n)) := by
  unfold flatCenteredPairCell flatCenteredCellScore
  apply Finset.prod_congr rfl
  intro t _
  rw [flatBlockHeight_proj hn hK]
  simp only [flattenSample, MeasurableEquiv.apply_symm_apply]

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

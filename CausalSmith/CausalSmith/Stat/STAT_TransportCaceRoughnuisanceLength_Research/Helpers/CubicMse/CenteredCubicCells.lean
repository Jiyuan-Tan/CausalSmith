module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ConditionalBlockCovariance
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ConditionalCellSum
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CubicBlockCovariance
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.WeightedCenteredCells

/-! # Conditional variance of the fully centered cubic cell component

This proves the three-residual member of roadmap (16) for the actual marked
histograms, with bounded training-measurable coefficients. The block covariance
factorization is derived from the product experiment, rather than supplied as
a premise of the variance bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Independence
open Causalean.Mathlib.Probability.Independence.Conditional
open scoped BigOperators

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- A held-out cell histogram centered at its exact experiment mean.  For [the displayed assumptions and inputs](hyp:P,n,K,i,b,l,z), [the stated object is defined](goal). -/
-- @node: flatCenteredCellScore
noncomputable def flatCenteredCellScore (P : TransportLaw) {n K : ℕ}
    (i : Fin 7) (b : Fin 4) (l : Fin K)
    (z : (a : {a // a ∈ flatBlock n b}) → FlatObs n a.val) : ℝ :=
  flatBlockHeight i b l z -
    ∫ x, flatBlockHeight i b l (finsetCoordProj (flatBlock n b) x)
      ∂Measure.pi (flatLaw P n)

/-- The fully centered three-block product in a single histogram cell.  For [the displayed assumptions and inputs](hyp:P,n,K,i,l,x), [the stated object is defined](goal). -/
-- @node: flatCenteredCubicCell
noncomputable def flatCenteredCubicCell (P : TransportLaw) {n K : ℕ}
    (i : Fin 3 → Fin 7) (l : Fin K)
    (x : (a : FlatIndex n) → FlatObs n a) : ℝ :=
  ∏ t : Fin 3,
    flatCenteredCellScore P (i t) t.succ l
      (finsetCoordProj (flatBlock n t.succ) x)

/-- Independence of the three evaluation blocks preserves square integrability
of their centered histogram product.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,i,l), [the stated conclusion holds](goal). -/
-- @node: flatCenteredCubicCell_memLp
lemma flatCenteredCubicCell_memLp (c_f C_f L : ℝ) (P : TransportLaw)
    (n K : ℕ) (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n)
    (i : Fin 3 → Fin 7) (l : Fin K) :
    MemLp (flatCenteredCubicCell P i l) 2 (Measure.pi (flatLaw P n)) := by
  let : ∀ a, StandardBorelSpace (FlatObs n a) := fun a => by
    cases a <;> dsimp [FlatObs] <;> infer_instance
  let : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  apply memLp_threeBlockProduct (flatLaw P n)
    (fun t : Fin 3 => flatBlock n t.succ) (flatBlock_eval_pairwise n)
    (fun t => flatCenteredCellScore P (i t) t.succ l)
  · intro t
    exact (measurable_flatBlockHeight (i t) t.succ l).sub measurable_const
  · intro t
    exact (flatBlockHeight_memLp c_f C_f L P n K hn hP (i t) t.succ l).sub
      (memLp_const _)

/-- The fully centered cubic histogram cell product has zero training-conditional
mean, derived from the disjoint evaluation blocks.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,i,l), [the stated conclusion holds](goal). -/
-- @node: condExp_flatCenteredCubicCell_zero
lemma condExp_flatCenteredCubicCell_zero (c_f C_f L : ℝ) (P : TransportLaw)
    (n K : ℕ) (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n)
    (i : Fin 3 → Fin 7) (l : Fin K) :
    condExp (MeasurableSpace.comap
      (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi)
      (Measure.pi (flatLaw P n)) (flatCenteredCubicCell P i l) =ᵐ[Measure.pi (flatLaw P n)]
      (0 : ((a : FlatIndex n) → FlatObs n a) → ℝ) := by
  let : ∀ a, StandardBorelSpace (FlatObs n a) := fun a => by
    cases a <;> dsimp [FlatObs] <;> infer_instance
  let : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  apply condExp_threeBlockProduct_zero (flatLaw P n) (flatBlock n 0)
    (fun t : Fin 3 => flatBlock n t.succ) (flatBlock_training_disjoint n)
    (flatBlock_eval_pairwise n)
    (fun t => flatCenteredCellScore P (i t) t.succ l)
  · intro t
    exact (measurable_flatBlockHeight (i t) t.succ l).sub measurable_const
  · intro t
    exact (flatBlockHeight_memLp c_f C_f L P n K hn hP (i t) t.succ l).sub
      (memLp_const _)
  · intro t
    exact condExp_centeredBlockScore_zero (flatLaw P n)
      (flatBlock n 0) (flatBlock n t.succ) (flatBlock_training_disjoint n t)
      (flatBlockHeight (i t) t.succ l) (measurable_flatBlockHeight _ _ _)
      (flatBlockHeight_memLp c_f C_f L P n K hn hP (i t) t.succ l)

/-- The conditional cross moment of actual centered cubic histogram products
is exactly the product of three blockwise histogram covariances.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,i,j,l,r), [the stated conclusion holds](goal). -/
-- @node: condExp_flatCenteredCubicCell_cross
lemma condExp_flatCenteredCubicCell_cross (c_f C_f L : ℝ) (P : TransportLaw)
    (n K : ℕ) (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n)
    (i j : Fin 3 → Fin 7) (l r : Fin K) :
    condExp (MeasurableSpace.comap
      (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi)
      (Measure.pi (flatLaw P n))
      (fun x => flatCenteredCubicCell P i l x * flatCenteredCubicCell P j r x)
      =ᵐ[Measure.pi (flatLaw P n)] (fun _ => ∏ t : Fin 3,
        covariance
          (fun x => flatBlockHeight (i t) t.succ l (finsetCoordProj (flatBlock n t.succ) x))
          (fun x => flatBlockHeight (j t) t.succ r (finsetCoordProj (flatBlock n t.succ) x))
          (Measure.pi (flatLaw P n))) := by
  let : ∀ a, StandardBorelSpace (FlatObs n a) := fun a => by
    cases a <;> dsimp [FlatObs] <;> infer_instance
  let : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  have hmain := condExp_threeBlockCross (flatLaw P n) (flatBlock n 0)
    (fun t : Fin 3 => flatBlock n t.succ) (flatBlock_training_disjoint n)
    (flatBlock_eval_pairwise n)
    (fun t => flatCenteredCellScore P (i t) t.succ l)
    (fun t => flatCenteredCellScore P (j t) t.succ r)
    (fun t => (measurable_flatBlockHeight (i t) t.succ l).sub measurable_const)
    (fun t => (measurable_flatBlockHeight (j t) t.succ r).sub measurable_const)
    (fun t => (flatBlockHeight_memLp c_f C_f L P n K hn hP (i t) t.succ l).sub
      (memLp_const _))
    (fun t => (flatBlockHeight_memLp c_f C_f L P n K hn hP (j t) t.succ r).sub
      (memLp_const _))
  have hcross (t : Fin 3) := condExp_centeredBlockCross_eq_covariance
    (flatLaw P n) (flatBlock n 0) (flatBlock n t.succ)
    (flatBlock_training_disjoint n t)
    (flatBlockHeight (i t) t.succ l) (flatBlockHeight (j t) t.succ r)
    (measurable_flatBlockHeight _ _ _) (measurable_flatBlockHeight _ _ _)
  filter_upwards [hmain, hcross 0, hcross 1, hcross 2] with x hx h0 h1 h2
  simpa only [flatCenteredCubicCell, flatCenteredCellScore, threeBlockProduct,
    Fin.prod_univ_three, h0, h1, h2] using hx

/-- The three-residual part of the exact cubic histogram sum satisfies the
`K² / m³ + 1 / m³` conditional variance bound in roadmap (16). The
training coefficient can be random; only its measurability and envelope are
needed. Covariance factorization is proved above for the actual histograms.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,i,c,C,hC,hcmeas,hc), [the stated conclusion holds](goal). -/
-- @node: conditional_variance_centeredCubic_cellAverage
lemma conditional_variance_centeredCubic_cellAverage (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (i : Fin 3 → Fin 7)
    (c : Fin K → ((a : FlatIndex n) → FlatObs n a) → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hcmeas : ∀ l, StronglyMeasurable[
      MeasurableSpace.comap (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi] (c l))
    (hc : ∀ᵐ x ∂Measure.pi (flatLaw P n), ∀ l, |c l x| ≤ C) :
    ∀ᵐ x ∂Measure.pi (flatLaw P n),
      condExp (MeasurableSpace.comap
        (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi)
        (Measure.pi (flatLaw P n)) (fun y =>
          ((K : ℝ)⁻¹ * ∑ l : Fin K, c l y * flatCenteredCubicCell P i l y -
            condExp (MeasurableSpace.comap
              (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi)
              (Measure.pi (flatLaw P n))
              (fun z => (K : ℝ)⁻¹ * ∑ l : Fin K, c l z * flatCenteredCubicCell P i l z) y) ^ 2) x ≤
      C ^ 2 * (1 + C_f + C_f ^ 2) ^ 3 *
        ((K : ℝ) ^ 2 / ((n : ℝ) / 5) ^ 3 + 1 / ((n : ℝ) / 5) ^ 3) := by
  let : ∀ a, StandardBorelSpace (FlatObs n a) := fun a => by
    cases a <;> dsimp [FlatObs] <;> infer_instance
  let : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  let μ := Measure.pi (flatLaw P n)
  let m := MeasurableSpace.comap (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi
  letI : MeasurableSpace ((a : FlatIndex n) → FlatObs n a) := MeasurableSpace.pi
  let X (l : Fin K) := flatCenteredCubicCell P (n := n) i l
  let κ (t : Fin 3) (l r : Fin K) := covariance
    (fun x => flatBlockHeight (i t) t.succ l (finsetCoordProj (flatBlock n t.succ) x))
    (fun x => flatBlockHeight (i t) t.succ r (finsetCoordProj (flatBlock n t.succ) x)) μ
  have hm : m ≤ (inferInstance : MeasurableSpace ((a : FlatIndex n) → FlatObs n a)) :=
    (measurable_finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)).comap_le
  have hlp (l : Fin K) : MemLp (X l) 2 μ :=
    flatCenteredCubicCell_memLp c_f C_f L P n K hn hP i l
  have hz (l : Fin K) : condExp m μ (X l) =ᵐ[μ]
      (0 : ((a : FlatIndex n) → FlatObs n a) → ℝ) :=
    condExp_flatCenteredCubicCell_zero c_f C_f L P n K hn hP i l
  have hx (l r : Fin K) : condExp m μ (fun x => X l x * X r x) =ᵐ[μ]
      (fun _ => ∏ t : Fin 3, κ t l r) :=
    condExp_flatCenteredCubicCell_cross c_f C_f L P n K hn hP i i l r
  have hnpos : (0 : ℝ) < n := by
    norm_num [threshold] at hn
    exact_mod_cast (show 0 < n by omega)
  have hB : 0 < (n : ℝ) / 5 := by positivity
  have hCf : 0 ≤ C_f := le_trans (by norm_num) hP.sourceBounds.2.1.le
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hV : 0 ≤ 1 + C_f + C_f ^ 2 := by positivity
  have hcard (t : Fin 3) : 0 < (blockIdx n t.succ).card := by
    rw [block_card]
    exact_mod_cast (lt_of_lt_of_le hB (block_size_lower n hn t.succ))
  apply conditional_variance_weighted_centered_cells (q := 2) hm hK X c κ
    C (1 + C_f + C_f ^ 2) ((n : ℝ) / 5) hC hV hB hcmeas hc hlp hz hx
  · intro t l
    have hb := flatBlockHeight_same_cell_covariance_le c_f C_f L P n K hP hK
      t.succ (hcard t) l (i t) (i t)
    have hnum : (K : ℝ) * C_f + C_f ^ 2 ≤ (1 + C_f + C_f ^ 2) * K := by
      nlinarith [mul_nonneg (sq_nonneg C_f) (sub_nonneg.mpr hKr)]
    have hd := block_size_lower n hn t.succ
    rw [← block_card] at hd
    exact hb.trans (div_le_div₀ (by positivity) hnum hB hd)
  · intro t l r hlr
    have hb := flatBlockHeight_off_cell_covariance_le c_f C_f L P n K hP hK
      t.succ (hcard t) hlr (i t) (i t)
    have hd := block_size_lower n hn t.succ
    rw [← block_card] at hd
    exact hb.trans (div_le_div₀ hV (by linarith) hB hd)

/-- The flattened centered product is precisely the product of the paper's
three held-out marked histograms at a cell midpoint, each minus its exact mean.  Under [the displayed assumptions and inputs](hyp:P,n,K,hn,hK,i,l), [the stated conclusion holds](goal). -/
-- @node: flatCenteredCubicCell_flattenSample
lemma flatCenteredCubicCell_flattenSample (P : TransportLaw) {n K : ℕ}
    (hn : threshold ≤ n) (hK : 0 < K) (i : Fin 3 → Fin 7) (l : Fin K)
    (ω : TwoSample n n) :
    flatCenteredCubicCell P i l (flattenSample n ω) =
      ∏ t : Fin 3, (markedHistogram ω (i t) K t.succ (midpoint K l) -
        ∫ x, flatBlockHeight (i t) t.succ l
          (finsetCoordProj (flatBlock n t.succ) x) ∂Measure.pi (flatLaw P n)) := by
  unfold flatCenteredCubicCell flatCenteredCellScore
  apply Finset.prod_congr rfl
  intro t _
  rw [flatBlockHeight_proj hn hK]
  simp only [flattenSample, MeasurableEquiv.apply_symm_apply]

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CenteredCubicCells
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.WeightedCenteredCells

/-! # One-residual contributions to quadratic and cubic variance

Roadmap (16) for a single centered histogram factor, with the actual finite
product experiment and a bounded training-measurable cell coefficient.
-/

public section
open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Independence
open scoped BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The one-residual member of the subset expansion obeys the exact
`2 C² V / (n/5)` conditional variance estimate.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,i,b,c,C,hC,hcmeas,hc), [the stated conclusion holds](goal). -/
-- @node: conditional_variance_centeredSingle_cellAverage
lemma conditional_variance_centeredSingle_cellAverage (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (i : Fin 7) (b : Fin 3)
    (c : Fin K → ((a : FlatIndex n) → FlatObs n a) → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hcmeas : ∀ l, StronglyMeasurable[
      MeasurableSpace.comap (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi] (c l))
    (hc : ∀ᵐ x ∂Measure.pi (flatLaw P n), ∀ l, |c l x| ≤ C) :
    ∀ᵐ x ∂Measure.pi (flatLaw P n),
      condExp (MeasurableSpace.comap
        (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi)
        (Measure.pi (flatLaw P n)) (fun y =>
          ((K : ℝ)⁻¹ * ∑ l : Fin K, c l y *
            flatCenteredCellScore P i b.succ l (finsetCoordProj (flatBlock n b.succ) y) -
            condExp (MeasurableSpace.comap
              (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi)
              (Measure.pi (flatLaw P n))
              (fun z => (K : ℝ)⁻¹ * ∑ l : Fin K, c l z *
                flatCenteredCellScore P i b.succ l (finsetCoordProj (flatBlock n b.succ) z)) y) ^ 2) x ≤
      C ^ 2 * (1 + C_f + C_f ^ 2) ^ 1 *
        ((K : ℝ) ^ 0 / ((n : ℝ) / 5) ^ 1 + 1 / ((n : ℝ) / 5) ^ 1) := by
  let : ∀ a, StandardBorelSpace (FlatObs n a) := fun a => by
    cases a <;> dsimp [FlatObs] <;> infer_instance
  let : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  -- Condition on the training view of the actual product experiment.
  let μ := Measure.pi (flatLaw P n)
  let m := MeasurableSpace.comap (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi
  let : MeasurableSpace ((a : FlatIndex n) → FlatObs n a) := MeasurableSpace.pi
  let X (l : Fin K) (x : (a : FlatIndex n) → FlatObs n a) :=
    flatCenteredCellScore P i b.succ l (finsetCoordProj (flatBlock n b.succ) x)
  let κ (_t : Fin 1) (l r : Fin K) := covariance
    (fun x => flatBlockHeight i b.succ l (finsetCoordProj (flatBlock n b.succ) x))
    (fun x => flatBlockHeight i b.succ r (finsetCoordProj (flatBlock n b.succ) x)) μ
  have hm : m ≤ (inferInstance : MeasurableSpace ((a : FlatIndex n) → FlatObs n a)) :=
    (measurable_finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)).comap_le
  have hlp (l : Fin K) : MemLp (X l) 2 μ :=
    (flatBlockHeight_memLp c_f C_f L P n K hn hP i b.succ l).sub (memLp_const _)
  have hz (l : Fin K) : condExp m μ (X l) =ᵐ[μ]
      (0 : ((a : FlatIndex n) → FlatObs n a) → ℝ) :=
    condExp_centeredBlockScore_zero (flatLaw P n)
      (flatBlock n 0) (flatBlock n b.succ) (flatBlock_training_disjoint n b)
      (flatBlockHeight i b.succ l) (measurable_flatBlockHeight _ _ _)
      (flatBlockHeight_memLp c_f C_f L P n K hn hP i b.succ l)
  have hx (l r : Fin K) : condExp m μ (fun x => X l x * X r x) =ᵐ[μ]
      (fun _ => ∏ t : Fin 1, κ t l r) := by
    simpa only [Fin.prod_univ_one, X, κ, flatCenteredCellScore, μ, m] using
      condExp_centeredBlockCross_eq_covariance (flatLaw P n)
        (flatBlock n 0) (flatBlock n b.succ) (flatBlock_training_disjoint n b)
        (flatBlockHeight i b.succ l) (flatBlockHeight i b.succ r)
        (measurable_flatBlockHeight _ _ _) (measurable_flatBlockHeight _ _ _)
  have hnpos : (0 : ℝ) < n := by
    norm_num [threshold] at hn
    exact_mod_cast (show 0 < n by omega)
  have hB : 0 < (n : ℝ) / 5 := by positivity
  have hCf : 0 ≤ C_f := le_trans (by norm_num) hP.sourceBounds.2.1.le
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hV : 0 ≤ 1 + C_f + C_f ^ 2 := by positivity
  have hcard (t : Fin 1) : 0 < (blockIdx n b.succ).card := by
    rw [block_card]
    exact_mod_cast (lt_of_lt_of_le hB (block_size_lower n hn b.succ))
  apply conditional_variance_weighted_centered_cells (q := 0) hm hK X c κ
    C (1 + C_f + C_f ^ 2) ((n : ℝ) / 5) hC hV hB hcmeas hc hlp hz hx
  · intro t l
    have hb := flatBlockHeight_same_cell_covariance_le c_f C_f L P n K hP hK
      b.succ (hcard t) l (i) (i)
    have hnum : (K : ℝ) * C_f + C_f ^ 2 ≤ (1 + C_f + C_f ^ 2) * K := by
      nlinarith [mul_nonneg (sq_nonneg C_f) (sub_nonneg.mpr hKr)]
    have hd := block_size_lower n hn b.succ
    rw [← block_card] at hd
    exact hb.trans (div_le_div₀ (by positivity) hnum hB hd)
  · intro t l r hlr
    have hb := flatBlockHeight_off_cell_covariance_le c_f C_f L P n K hP hK
      b.succ (hcard t) hlr (i) (i)
    have hd := block_size_lower n hn b.succ
    rw [← block_card] at hd
    exact hb.trans (div_le_div₀ hV (by linarith) hB hd)

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.BoundedLinearScores
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.WeightedCenteredCells

/-! # Conditional second moments of bounded linear cell scores

Training coefficients pull out of the exact cell cross moments. The signed
covariance quadratic form is bounded by the single-record envelope, yielding
the density-free per-coordinate bound needed in roadmap (19).
-/

public section

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Independence
open scoped BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The conditional square of a weighted normalized cell sum equals its
signed covariance quadratic form, keeping cancellation between cells.  Under [the displayed assumptions and inputs](hyp:Ω,mΩ,m,hm,K,X,c,κ,C,hC,hcmeas,hc,hlp,hcross), [the stated conclusion holds](goal). -/
-- @node: condExp_sq_weighted_cellAverage_eq_covariance_sum
lemma condExp_sq_weighted_cellAverage_eq_covariance_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {K : ℕ}
    (X c : Fin K → Ω → ℝ) (κ : Fin K → Fin K → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcmeas : ∀ l, StronglyMeasurable[m] (c l))
    (hc : ∀ᵐ x ∂μ, ∀ l, |c l x| ≤ C)
    (hlp : ∀ l, MemLp (X l) 2 μ)
    (hcross : ∀ l r, condExp m μ (fun x => X l x * X r x) =ᵐ[μ]
      (fun _ => κ l r)) :
    condExp m μ (fun x => ((K : ℝ)⁻¹ * ∑ l : Fin K, c l x * X l x) ^ 2) =ᵐ[μ]
      (fun x => (K : ℝ)⁻¹ ^ 2 * ∑ l : Fin K, ∑ r : Fin K,
        c l x * c r x * κ l r) := by
  let Y (l : Fin K) (x : Ω) := c l x * X l x
  have hbound (l r : Fin K) : ∀ᵐ x ∂μ, ‖c l x * c r x‖ ≤ C ^ 2 := by
    filter_upwards [hc] with x hx
    simpa only [Real.norm_eq_abs, abs_mul, pow_two] using
      mul_le_mul (hx l) (hx r) (abs_nonneg _) hC
  have hint (l r : Fin K) : Integrable (fun x => Y l x * Y r x) μ := by
    have hi := ((hlp l).integrable_mul (hlp r)).bdd_mul
      (((hcmeas l).mono hm).mul ((hcmeas r).mono hm)).aestronglyMeasurable
      (hbound l r)
    convert hi using 1
    funext x
    dsimp [Y, Pi.mul_apply]
    ring
  have hfactor (l r : Fin K) :
      condExp m μ (fun x => Y l x * Y r x) =ᵐ[μ]
        (fun x => c l x * c r x * κ l r) := by
    have hi := ((hlp l).integrable_mul (hlp r)).bdd_mul
      (((hcmeas l).mono hm).mul ((hcmeas r).mono hm)).aestronglyMeasurable
      (hbound l r)
    have hp := condExp_mul_of_stronglyMeasurable_left
      ((hcmeas l).mul (hcmeas r)) hi ((hlp l).integrable_mul (hlp r))
    have heq : (fun x => Y l x * Y r x) =
        (fun x => (c l x * c r x) * (X l x * X r x)) := by
      funext x
      dsimp [Y]
      ring
    rw [heq]
    filter_upwards [hp, hcross l r] with x hp hx
    change condExp m μ (fun x => (c l x * c r x) * (X l x * X r x)) x =
      c l x * c r x * condExp m μ (fun x => X l x * X r x) x at hp
    rw [hx] at hp
    exact hp
  have hs := @condExp_sq_cellSum_eq_sum_cross Ω mΩ μ m K Y hint
  have hscale := condExp_smul (μ := μ) ((K : ℝ)⁻¹ ^ 2)
    (fun x => (∑ l : Fin K, Y l x) ^ 2) m
  have heq : (fun x => ((K : ℝ)⁻¹ * ∑ l : Fin K, c l x * X l x) ^ 2) =
      ((K : ℝ)⁻¹ ^ 2) • (fun x => (∑ l : Fin K, Y l x) ^ 2) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Y]
  rw [heq]
  have hall := ae_all_iff.mpr (fun l => ae_all_iff.mpr (hfactor l))
  filter_upwards [hs, hscale, hall] with x hs ht hx
  simp only [Pi.smul_apply, smul_eq_mul] at ht
  rw [ht, hs]
  congr 1
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun r _ => hx l r

/-- Each bounded training-weighted marked coordinate in a held-out block
has conditional second moment at most `5 C² / n`. This is the sharp
per-coordinate ingredient of the linear variance estimate (19).  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,hK,i,b,c,C,hC,hcmeas,hc), [the stated conclusion holds](goal). -/
-- @node: condExp_sq_bounded_linear_cellAverage_le
lemma condExp_sq_bounded_linear_cellAverage_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (hK : 0 < K)
    (i : Fin 7) (b : Fin 3)
    (c : Fin K → ((a : FlatIndex n) → FlatObs n a) → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcmeas : ∀ l, StronglyMeasurable[
      MeasurableSpace.comap (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0))
        MeasurableSpace.pi] (c l))
    (hc : ∀ᵐ x ∂Measure.pi (flatLaw P n), ∀ l, |c l x| ≤ C) :
    ∀ᵐ x ∂Measure.pi (flatLaw P n),
      condExp (MeasurableSpace.comap
        (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi)
        (Measure.pi (flatLaw P n))
        (fun y => ((K : ℝ)⁻¹ * ∑ l : Fin K, c l y *
          flatCenteredCellScore P i b.succ l
            (finsetCoordProj (flatBlock n b.succ) y)) ^ 2) x ≤
      5 * C ^ 2 * (n : ℝ) ^ (-1 : ℝ) := by
  let : ∀ a, StandardBorelSpace (FlatObs n a) := fun a => by
    cases a <;> dsimp [FlatObs] <;> infer_instance
  let : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  let μ := Measure.pi (flatLaw P n)
  let m := MeasurableSpace.comap
    (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi
  let X (l : Fin K) (z : (a : FlatIndex n) → FlatObs n a) :=
    flatCenteredCellScore P i b.succ l (finsetCoordProj (flatBlock n b.succ) z)
  let κ (l r : Fin K) := covariance
    (fun z => flatBlockHeight i b.succ l (finsetCoordProj (flatBlock n b.succ) z))
    (fun z => flatBlockHeight i b.succ r (finsetCoordProj (flatBlock n b.succ) z)) μ
  have hm : m ≤ (MeasurableSpace.pi : MeasurableSpace ((a : FlatIndex n) → FlatObs n a)) :=
    (measurable_finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)).comap_le
  have hlp (l : Fin K) : MemLp (X l) 2 μ :=
    flatCenteredCellScore_comp_memLp c_f C_f L P n K hn hP i b.succ l
  have hx (l r : Fin K) : condExp m μ (fun z => X l z * X r z) =ᵐ[μ]
      (fun _ => κ l r) := by
    exact condExp_centeredBlockCross_eq_covariance (flatLaw P n)
      (flatBlock n 0) (flatBlock n b.succ) (flatBlock_training_disjoint n b)
      (flatBlockHeight i b.succ l) (flatBlockHeight i b.succ r)
      (measurable_flatBlockHeight _ _ _) (measurable_flatBlockHeight _ _ _)
  have heq := @condExp_sq_weighted_cellAverage_eq_covariance_sum
    ((a : FlatIndex n) → FlatObs n a) MeasurableSpace.pi μ m hm K
    X c κ C hC hcmeas hc hlp hx
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by norm_num [threshold] at hn; omega)
  have hB : 0 < (n : ℝ) / 5 := by positivity
  have hsize := block_size_lower n hn b.succ
  have hcard : 0 < (blockIdx n b.succ).card := by
    rw [block_card]
    exact_mod_cast lt_of_lt_of_le hB hsize
  filter_upwards [heq, hc] with z hz hc
  rw [hz]
  calc
    _ ≤ C ^ 2 / blockSize n b.succ :=
      normalized_flatBlockHeight_covariance_sum_le c_f C_f L P n K hP hK
        b.succ hcard i (fun l => c l z) C hC hc
    _ ≤ C ^ 2 / ((n : ℝ) / 5) :=
      div_le_div_of_nonneg_left (sq_nonneg C) hB hsize
    _ = 5 * C ^ 2 * (n : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]
      ring

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CenteredPairCells
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ConditionalCellSum
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ExactStatisticBridge
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.PilotProjection
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.VarianceAggregation

/-! # Cellwise projection-bias assembly for the exact cubic statistic

This module turns the exact quadratic and cubic cell projection identities
into quantitative bounds.  It isolates the deterministic part of the bias
calculation from the conditional-expectation argument for the held-out
histogram blocks.
-/

@[expose] public section

open MeasureTheory Set
open Causalean.Mathlib.Probability.Independence
open Causalean.Mathlib.Probability.Independence.Conditional
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- In a decomposition into a conditionally centered fluctuation and a
training-measurable shift, the shift is the exact conditional mean.  Under [the displayed assumptions and inputs](hyp:Ω,mΩ,m,hm,z,g,hz,hg,hgm,hz0), [the stated conclusion holds](goal). -/
lemma condExp_add_eq_shift_of_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (z g : Ω → ℝ) (hz : Integrable z μ) (hg : Integrable g μ)
    (hgm : StronglyMeasurable[m] g)
    (hz0 : condExp m μ z =ᵐ[μ] (0 : Ω → ℝ)) :
    condExp m μ (z + g) =ᵐ[μ] g := by
  have hadd := condExp_add hz hg m
  have hfix := condExp_of_stronglyMeasurable hm hgm hg
  rw [hfix] at hadd
  filter_upwards [hadd, hz0] with x hx hz0x
  simp only [Pi.add_apply] at hx
  rw [hx, hz0x]
  simp only [Pi.zero_apply, zero_add]

/-- A normalized finite cell sum remains conditionally centered after
multiplication by cellwise training-measurable coefficients.  Under [the displayed assumptions and inputs](hyp:Ω,mΩ,m,K,hm,c,X,hc,hX,hprod,hzero), [the stated conclusion holds](goal). -/
lemma condExp_weighted_cellAverage_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {m : MeasurableSpace Ω} {K : ℕ} (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)] (c X : Fin K → Ω → ℝ)
    (hc : ∀ l, StronglyMeasurable[m] (c l))
    (hX : ∀ l, Integrable (X l) μ)
    (hprod : ∀ l, Integrable (fun x => c l x * X l x) μ)
    (hzero : ∀ l, condExp m μ (X l) =ᵐ[μ] (0 : Ω → ℝ)) :
    condExp m μ (fun x => (K : ℝ)⁻¹ * ∑ l : Fin K, c l x * X l x) =ᵐ[μ]
      (0 : Ω → ℝ) := by
  have hterm (l : Fin K) : condExp m μ (fun x => c l x * X l x) =ᵐ[μ]
      (0 : Ω → ℝ) := by
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (hc l) (hprod l) (hX l)
    filter_upwards [hpull, hzero l] with x hp hx
    change condExp m μ (c l * X l) x = (0 : Ω → ℝ) x
    rw [hp]
    simp only [Pi.mul_apply, Pi.zero_apply]
    rw [hx, Pi.zero_apply, mul_zero]
  exact @condExp_cellAverage_zero Ω mΩ μ m K
    (fun l x => c l x * X l x) hprod hterm

/-- A single centered held-out histogram cell has zero conditional mean given
the training block.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,i,b,l), [the stated conclusion holds](goal). -/
lemma condExp_flatCenteredCellScore_zero (c_f C_f L : ℝ) (P : TransportLaw)
    (n K : ℕ) (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n)
    (i : Fin 7) (b : Fin 3) (l : Fin K) :
    condExp (MeasurableSpace.comap
      (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi)
      (Measure.pi (flatLaw P n))
      (fun x => flatCenteredCellScore P i b.succ l
        (finsetCoordProj (flatBlock n b.succ) x)) =ᵐ[Measure.pi (flatLaw P n)]
      (0 : ((a : FlatIndex n) → FlatObs n a) → ℝ) := by
  letI : ∀ a, StandardBorelSpace (FlatObs n a) := fun a => by
    cases a <;> dsimp [FlatObs] <;> infer_instance
  letI : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  exact condExp_centeredBlockScore_zero (flatLaw P n)
    (flatBlock n 0) (flatBlock n b.succ) (flatBlock_training_disjoint n b)
    (flatBlockHeight i b.succ l) (measurable_flatBlockHeight _ _ _)
    (flatBlockHeight_memLp c_f C_f L P n K hn hP i b.succ l)

/-- The product of two centered held-out histogram cells from distinct
evaluation blocks has zero conditional mean given training.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hn,hP,i,b,hb,l), [the stated conclusion holds](goal). -/
lemma condExp_flatCenteredPairCell_zero (c_f C_f L : ℝ) (P : TransportLaw)
    (n K : ℕ) (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n)
    (i : Fin 2 → Fin 7) (b : Fin 2 → Fin 3) (hb : Function.Injective b)
    (l : Fin K) :
    condExp (MeasurableSpace.comap
      (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi)
      (Measure.pi (flatLaw P n)) (flatCenteredPairCell P i b l)
      =ᵐ[Measure.pi (flatLaw P n)]
      (0 : ((a : FlatIndex n) → FlatObs n a) → ℝ) := by
  letI : ∀ a, StandardBorelSpace (FlatObs n a) := fun a => by
    cases a <;> dsimp [FlatObs] <;> infer_instance
  letI : ∀ a, IsProbabilityMeasure (flatLaw P n a) := fun a =>
    flatLaw_isProbabilityMeasure c_f C_f L P n hP a
  let μ := Measure.pi (flatLaw P n)
  let m := MeasurableSpace.comap
    (finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)) MeasurableSpace.pi
  let F (t : Fin 2) := flatCenteredCellScore P (n := n) (i t) (b t).succ l
  have hf (t : Fin 2) : Measurable (F t) :=
    (measurable_flatBlockHeight (i t) (b t).succ l).sub measurable_const
  have hflp (t : Fin 2) : MemLp
      (fun x => F t (finsetCoordProj (flatBlock n (b t).succ) x)) 2 μ :=
    (flatBlockHeight_memLp c_f C_f L P n K hn hP
      (i t) (b t).succ l).sub (memLp_const _)
  have hdisj : Disjoint (flatBlock n (b 0).succ) (flatBlock n (b 1).succ) :=
    flatBlock_eval_pairwise n (hb.ne (by decide : (0 : Fin 2) ≠ 1))
  have hind := condIndepFun_eval_pair (flatLaw P n) (flatBlock n 0)
    (fun t : Fin 3 => flatBlock n t.succ) (flatBlock_training_disjoint n)
    (flatBlock_eval_pairwise n) (b 0) (b 1) (hb.ne (by decide : (0 : Fin 2) ≠ 1))
  have hprod : Integrable (fun x =>
      F 0 (finsetCoordProj (flatBlock n (b 0).succ) x) *
      F 1 (finsetCoordProj (flatBlock n (b 1).succ) x)) μ :=
    integrable_twoBlockProduct (flatLaw P n) _ _ hdisj (F 0) (F 1)
      (hf 0) (hf 1) ((hflp 0).integrable (by norm_num))
      ((hflp 1).integrable (by norm_num))
  have hp := condExp_mul_of_condIndep
    (show m ≤ MeasurableSpace.pi from
      (measurable_finsetCoordProj (Ω := FlatObs n) (flatBlock n 0)).comap_le)
    (measurable_finsetCoordProj (flatBlock n (b 0).succ))
    (measurable_finsetCoordProj (flatBlock n (b 1).succ)) hind
    (hf 0) (hf 1) ((hflp 0).integrable (by norm_num))
    ((hflp 1).integrable (by norm_num)) hprod
  have hz0 := condExp_flatCenteredCellScore_zero c_f C_f L P n K hn hP
    (i 0) (b 0) l
  change condExp m μ (flatCenteredPairCell P i b l) =ᵐ[μ] _
  have heq : flatCenteredPairCell P i b l = (fun y =>
      F 0 (finsetCoordProj (flatBlock n (b 0).succ) y) *
      F 1 (finsetCoordProj (flatBlock n (b 1).succ) y)) := by
    funext y
    simp only [F, flatCenteredPairCell, Fin.prod_univ_two]
  rw [heq]
  filter_upwards [hp, hz0] with x hp hz0
  rw [hp]
  change condExp m μ (fun y =>
      F 0 (finsetCoordProj (flatBlock n (b 0).succ) y)) x *
    condExp m μ (fun y =>
      F 1 (finsetCoordProj (flatBlock n (b 1).succ) y)) x = 0
  rw [hz0]
  simp only [Pi.zero_apply, zero_mul]

/-- The training-measurable quadratic projection polynomial: every held-out
residual is replaced by its exact cell-mean shift.  For [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated object is defined](goal). -/
@[no_expose]
noncomputable def quadraticProjectionMean (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (ω : TwoSample n n) (A : Bool) : ℝ :=
  let K := quadraticResolution n
  (K : ℝ)⁻¹ * ∑ i : Fin 7, ∑ j : Fin 7, ∑ l : Fin K,
    (1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f ω (midpoint K l)) i j *
      (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
        pilot c_f C_f ω (midpoint K l) i) *
      (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y j) K l -
        pilot c_f C_f ω (midpoint K l) j)

/-- The training-measurable cubic projection polynomial: every held-out
residual is replaced by its exact cell-mean shift.  For [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated object is defined](goal). -/
@[no_expose]
noncomputable def cubicProjectionMean (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (ω : TwoSample n n) (A : Bool) : ℝ :=
  let K := cubicResolution n
  (K : ℝ)⁻¹ * ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, ∑ l : Fin K,
    (1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f ω (midpoint K l)) i j k *
      (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
        pilot c_f C_f ω (midpoint K l) i) *
      (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y j) K l -
        pilot c_f C_f ω (midpoint K l) j) *
      (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y k) K l -
        pilot c_f C_f ω (midpoint K l) k)

/-- The explicit finite-sum formula defining the quadratic projection mean.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated conclusion holds](goal). -/
lemma quadraticProjectionMean_eq (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (ω : TwoSample n n) (A : Bool) :
    quadraticProjectionMean c_f C_f L P n hP ω A =
      let K := quadraticResolution n
      (K : ℝ)⁻¹ * ∑ i : Fin 7, ∑ j : Fin 7, ∑ l : Fin K,
        (1 / 2 : ℝ) * dPhi2 A (pilot c_f C_f ω (midpoint K l)) i j *
          (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
            pilot c_f C_f ω (midpoint K l) i) *
          (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y j) K l -
            pilot c_f C_f ω (midpoint K l) j) := by
  rfl

/-- The explicit finite-sum formula defining the cubic projection mean.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated conclusion holds](goal). -/
lemma cubicProjectionMean_eq (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n)
    (ω : TwoSample n n) (A : Bool) :
    cubicProjectionMean c_f C_f L P n hP ω A =
      let K := cubicResolution n
      (K : ℝ)⁻¹ * ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, ∑ l : Fin K,
        (1 / 6 : ℝ) * dPhi3 A (pilot c_f C_f ω (midpoint K l)) i j k *
          (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
            pilot c_f C_f ω (midpoint K l) i) *
          (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y j) K l -
            pilot c_f C_f ω (midpoint K l) j) *
          (cellAverage (fun y => markedDensityVector c_f C_f L P n hP y k) K l -
            pilot c_f C_f ω (midpoint K l) k) := by
  rfl

/-- The quadratic projection polynomial is measurable with respect to the
training sigma algebra.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
lemma stronglyMeasurable_quadraticProjectionMean (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    StronglyMeasurable[trainingSigma n]
      (fun ω => quadraticProjectionMean c_f C_f L P n hP ω A) := by
  let K := quadraticResolution n
  have hd (i j : Fin 7) (l : Fin K) : StronglyMeasurable[trainingSigma n]
      (fun ω => dPhi2 A (pilot c_f C_f ω (midpoint K l)) i j) :=
    stronglyMeasurable_dPhi2_pilot_trainingSigma
      c_f C_f L P n hn hP A (midpoint K l) i j
  have hs (i : Fin 7) (l : Fin K) : StronglyMeasurable[trainingSigma n]
      (fun ω => cellAverage
        (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
          pilot c_f C_f ω (midpoint K l) i) :=
    stronglyMeasurable_const.sub
      (stronglyMeasurable_pilot_eval_trainingSigma c_f C_f (midpoint K l) i)
  unfold quadraticProjectionMean
  dsimp only
  fun_prop

/-- The cubic projection polynomial is measurable with respect to the
training sigma algebra.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
lemma stronglyMeasurable_cubicProjectionMean (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    StronglyMeasurable[trainingSigma n]
      (fun ω => cubicProjectionMean c_f C_f L P n hP ω A) := by
  let K := cubicResolution n
  have hd (i j k : Fin 7) (l : Fin K) : StronglyMeasurable[trainingSigma n]
      (fun ω => dPhi3 A (pilot c_f C_f ω (midpoint K l)) i j k) :=
    stronglyMeasurable_dPhi3_pilot_trainingSigma
      c_f C_f L P n hn hP A (midpoint K l) i j k
  have hs (i : Fin 7) (l : Fin K) : StronglyMeasurable[trainingSigma n]
      (fun ω => cellAverage
        (fun y => markedDensityVector c_f C_f L P n hP y i) K l -
          pilot c_f C_f ω (midpoint K l) i) :=
    stronglyMeasurable_const.sub
      (stronglyMeasurable_pilot_eval_trainingSigma c_f C_f (midpoint K l) i)
  unfold cubicProjectionMean
  dsimp only
  fun_prop

/-- A marked-density coordinate differs from its cell average by at most the
common Hölder modulus times the cell width.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l,x,hx,i), [the stated conclusion holds](goal). -/
lemma markedDensity_sub_cellAverage_abs_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (l : Fin K) (x : ℝ) (hx : x ∈ cell K l) (i : Fin 7) :
    |markedDensityVector c_f C_f L P n hP x i -
      cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l| ≤
        3 * (1 + C_f) * L * (1 / (K : ℝ)) ^ holderExponent := by
  rw [abs_sub_comm]
  exact markedDensityVector_cell_bias c_f C_f L P n K hP hK l x hx i

/-- The integral of a quadratic Taylor monomial loses only the product of two
within-cell projection residuals.  Its absolute size is bounded explicitly.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,K,hP,hK,l,i,j,ti,tj,c), [the stated conclusion holds](goal). -/
lemma markedDensity_quadratic_cell_projection_abs_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n K : ℕ) (hP : ModelClass c_f C_f L P n)
    (hK : 0 < K) (l : Fin K) (i j : Fin 7) (ti tj c : ℝ) :
    let F := markedDensityVector c_f C_f L P n hP
    let ai := cellAverage (fun y => F y i) K l
    let aj := cellAverage (fun y => F y j) K l
    |∫ x in cell K l,
        c * ((F x i - ti) * (F x j - tj) - (ai - ti) * (aj - tj))| ≤
      |c| * (3 * (1 + C_f) * L *
        (1 / (K : ℝ)) ^ holderExponent) ^ 2 / (K : ℝ) := by
  dsimp only
  rw [markedDensity_quadratic_cell_projection_identity
    c_f C_f L P n K hP hK l i j ti tj c]
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  let B := 3 * (1 + C_f) * L * (1 / (K : ℝ)) ^ holderExponent
  have hB : 0 ≤ B := by
    dsimp [B]
    have hC : 0 ≤ C_f := le_trans (by norm_num) hP.sourceBounds.2.1.le
    have hL : 0 ≤ L := hP.sourceHolder.1.le.trans' (by norm_num)
    positivity
  have hi : IntegrableOn (fun x => c *
      ((markedDensityVector c_f C_f L P n hP x i -
          cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l) *
       (markedDensityVector c_f C_f L P n hP x j -
          cellAverage (fun y => markedDensityVector c_f C_f L P n hP y j) K l)))
      (cell K l) := by
    have hci := markedDensityVector_continuousOn c_f C_f L P n hP i
    have hcj := markedDensityVector_continuousOn c_f C_f L P n hP j
    have hc : ContinuousOn (fun x => c *
      ((markedDensityVector c_f C_f L P n hP x i -
          cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l) *
       (markedDensityVector c_f C_f L P n hP x j -
          cellAverage (fun y => markedDensityVector c_f C_f L P n hP y j) K l)))
        covariateSpace := by fun_prop
    exact hc.integrableOn_Icc.mono_set (cell_subset_covariateSpace hK l)
  have hfinite : volume (cell K l) ≠ ⊤ := by
    rw [volume_cell hK l]
    exact ENNReal.ofReal_ne_top
  calc
    _ ≤ ∫ x in cell K l, |c *
        ((markedDensityVector c_f C_f L P n hP x i -
            cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l) *
         (markedDensityVector c_f C_f L P n hP x j -
            cellAverage (fun y => markedDensityVector c_f C_f L P n hP y j) K l))| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => c *
          ((markedDensityVector c_f C_f L P n hP x i -
              cellAverage (fun y => markedDensityVector c_f C_f L P n hP y i) K l) *
           (markedDensityVector c_f C_f L P n hP x j -
              cellAverage (fun y => markedDensityVector c_f C_f L P n hP y j) K l)))
    _ ≤ ∫ _x in cell K l, |c| * B ^ 2 := by
      apply setIntegral_mono_on hi.norm (integrableOn_const hfinite) (measurableSet_cell K l)
      intro x hx
      simp only [Real.norm_eq_abs, abs_mul]
      have hri := markedDensity_sub_cellAverage_abs_le c_f C_f L P n K hP hK l x hx i
      have hrj := markedDensity_sub_cellAverage_abs_le c_f C_f L P n K hP hK l x hx j
      change _ ≤ B at hri hrj
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
      calc
        _ ≤ B * B := mul_le_mul hri hrj (abs_nonneg _) hB
        _ = B ^ 2 := by ring
    _ = |c| * B ^ 2 / (K : ℝ) := by
      rw [setIntegral_const, Measure.real, volume_cell hK l,
        ENNReal.toReal_ofReal (by positivity)]
      simp only [smul_eq_mul]
      ring
    _ = _ := by rfl

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

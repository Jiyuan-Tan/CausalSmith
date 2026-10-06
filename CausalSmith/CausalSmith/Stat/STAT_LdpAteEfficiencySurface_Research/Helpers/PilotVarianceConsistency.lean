module
public import Causalean.Experimentation.DesignBased.InProb
public import Causalean.Stat.CLT.FiniteIidTriangular.Consistency
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotLocalRiskAttainment
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotRowVariance

/-! # Consistency of the pilot plug-in variance

The arguments here use only finite-product second-moment bounds.  In particular,
they are independent of the triangular-array central limit theorem.
-/

@[expose] public section
noncomputable section

namespace Causalean.Stat.CLT.FiniteIidTriangular

open Filter Topology

namespace RowModel

variable {Y : Type*} [Fintype Y] (M : RowModel Y)

/-- A finite-row Chebyshev bound for empirical variance around its own one-coordinate second moment. For the displayed inputs and conditions, the stated result follows. Under [the stated assumptions](hyp:hn,hδ), [the event Probability empirical Variance sub one Second le](goal).

Under the stated assumptions, the event Probability empirical Variance sub one Second le. -/
theorem eventProbability_empiricalVariance_sub_oneSecond_le
    (n : ℕ) (hn : 0 < M.N n) (δ : ℝ) (hδ : 0 < δ) :
    M.eventProbability n (fun ys =>
      δ ≤ |M.empiricalVariance n ys - M.oneSecond n|) ≤
      M.B ^ 4 / (M.N n : ℝ) / (δ / 2) ^ 2 +
        M.B ^ 2 / (M.N n : ℝ) / (δ / 2) := by
  classical
  have hhalf : 0 < δ / 2 := half_pos hδ
  have hsqrt : 0 < Real.sqrt (δ / 2) := Real.sqrt_pos.2 hhalf
  rw [M.eventProbability_eq_designPr]
  have hmono : (M.productDesign n).Pr
      (fun ys => δ ≤ |M.empiricalVariance n ys - M.oneSecond n|) ≤
      (M.productDesign n).Pr (fun ys =>
        δ / 2 ≤ |M.empiricalSecond n ys - M.oneSecond n| ∨
          Real.sqrt (δ / 2) ≤ |M.empiricalMean n ys|) := by
    apply (M.productDesign n).Pr_mono
    intro ys hys
    by_contra hc
    push Not at hc
    obtain ⟨hsecond, hmean⟩ := hc
    have hmean_sq : (M.empiricalMean n ys) ^ 2 < δ / 2 := by
      have hpow := (sq_lt_sq₀ (abs_nonneg (M.empiricalMean n ys)) hsqrt.le).2 hmean
      rw [sq_abs, Real.sq_sqrt hhalf.le] at hpow
      exact hpow
    have htri : |M.empiricalVariance n ys - M.oneSecond n| ≤
        |M.empiricalSecond n ys - M.oneSecond n| +
          (M.empiricalMean n ys) ^ 2 := by
      rw [empiricalVariance]
      have heq : M.empiricalSecond n ys - (M.empiricalMean n ys) ^ 2 -
          M.oneSecond n =
          (M.empiricalSecond n ys - M.oneSecond n) -
            (M.empiricalMean n ys) ^ 2 := by ring
      rw [heq]
      calc
        _ ≤ |M.empiricalSecond n ys - M.oneSecond n| +
            |(M.empiricalMean n ys) ^ 2| := abs_sub _ _
        _ = _ := by
          rw [abs_of_nonneg (sq_nonneg (M.empiricalMean n ys))]
    linarith
  have hEsecond : (M.productDesign n).E (M.empiricalSecond n) =
      M.oneSecond n := M.expect_empiricalSecond n hn
  have hsecondCheb := (M.productDesign n).chebyshev
    (M.empiricalSecond n) hhalf
  rw [hEsecond] at hsecondCheb
  have hsecondVar : (M.productDesign n).Var (M.empiricalSecond n) =
      M.expect n (fun ys =>
        (M.empiricalSecond n ys - M.oneSecond n) ^ 2) := by
    rw [show (M.productDesign n).Var (M.empiricalSecond n) =
      M.expect n (fun ys => (M.empiricalSecond n ys -
        (M.productDesign n).E (M.empiricalSecond n)) ^ 2) from rfl,
      hEsecond]
  rw [hsecondVar] at hsecondCheb
  have hsecondBound : (M.productDesign n).Pr
      (fun ys => δ / 2 ≤ |M.empiricalSecond n ys - M.oneSecond n|) ≤
      M.B ^ 4 / (M.N n : ℝ) / (δ / 2) ^ 2 :=
    hsecondCheb.trans
      (div_le_div_of_nonneg_right (M.empiricalSecond_mse_le n hn)
        (sq_nonneg _))
  have hEmean : (M.productDesign n).E (M.empiricalMean n) = 0 := by
    change M.expect n (M.empiricalMean n) = 0
    simp only [expect, empiricalMean, scoreSum, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hcoord (i : Fin (M.N n)) :
        ∑ ys : Fin (M.N n) → Y, M.mass n ys * M.f n (ys i) = 0 := by
      change M.expect n (fun ys => M.f n (ys i)) = 0
      rw [M.expect_coordinate]
      exact M.centered n
    calc
      (∑ i : Fin (M.N n), ∑ ys : Fin (M.N n) → Y,
          M.mass n ys * ((M.N n : ℝ)⁻¹ * M.f n (ys i))) =
          ∑ i : Fin (M.N n), (M.N n : ℝ)⁻¹ *
            (∑ ys : Fin (M.N n) → Y, M.mass n ys * M.f n (ys i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ys _
        ring
      _ = 0 := by simp [hcoord]
  have hmeanCheb := (M.productDesign n).chebyshev (M.empiricalMean n) hsqrt
  rw [hEmean] at hmeanCheb
  simp only [sub_zero, Real.sq_sqrt hhalf.le] at hmeanCheb
  have hmeanVar : (M.productDesign n).Var (M.empiricalMean n) =
      M.expect n (fun ys => (M.empiricalMean n ys) ^ 2) := by
    rw [show (M.productDesign n).Var (M.empiricalMean n) =
      M.expect n (fun ys => (M.empiricalMean n ys -
        (M.productDesign n).E (M.empiricalMean n)) ^ 2) from rfl, hEmean]
    simp
  rw [hmeanVar] at hmeanCheb
  have hmeanBound : (M.productDesign n).Pr
      (fun ys => Real.sqrt (δ / 2) ≤ |M.empiricalMean n ys|) ≤
      M.B ^ 2 / (M.N n : ℝ) / (δ / 2) :=
    hmeanCheb.trans
      (div_le_div_of_nonneg_right (M.empiricalMean_mse_le n hn)
        hhalf.le)
  calc
    _ ≤ (M.productDesign n).Pr
        (fun ys => δ / 2 ≤ |M.empiricalSecond n ys - M.oneSecond n|) +
        (M.productDesign n).Pr
          (fun ys => Real.sqrt (δ / 2) ≤ |M.empiricalMean n ys|) :=
      hmono.trans (Causalean.Experimentation.DesignBased.FiniteDesign.Pr_or_le
        (M.productDesign n) _ _)
    _ ≤ M.B ^ 4 / (M.N n : ℝ) / (δ / 2) ^ 2 +
        M.B ^ 2 / (M.N n : ℝ) / (δ / 2) :=
      add_le_add hsecondBound hmeanBound

end RowModel
end Causalean.Stat.CLT.FiniteIidTriangular

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology
open Causalean.Stat.CLT.FiniteIidTriangular

/-- Conditional main-row probability that the encoded empirical variance misses the oracle variance. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The pilot Conditional Variance Bad Mass](goal) is determined by [the displayed parameters](hyp:select,θ,p,ε,δ,m,hselect,hp,hε,hmn,u). -/
def pilotConditionalVarianceBadMass
    (θ : TrialParameter) (p ε δ : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) {n : ℕ}
    (hmn : m n ≤ n) (u : Fin (m n) → Fin 4) : ℝ :=
  let η := fun _ : ℕ => pilotAdaptivePrefixTheta p ε m hmn u
  ∑ v : Fin (adaptiveMainSize m n) → Fin 14,
    adaptivePilotRowProductMass select θ (fun _ => 0) η p ε m hselect hp hε n v *
    if δ < |adaptivePilotRowEmpiricalVariance select θ (fun _ => 0) η
        p ε m hselect hp hε n v - Vstar θ p ε| then 1 else 0

/-- Prefix mixture of the conditional bad-variance probabilities. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The pilot Variance Bad Mass](goal) is determined by [the displayed parameters](hyp:select,θ,p,ε,δ,m,hselect,hp,hε,hmn). -/
def pilotVarianceBadMass
    (θ : TrialParameter) (p ε δ : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) {n : ℕ}
    (hmn : m n ≤ n) : ℝ :=
  ∑ u : Fin (m n) → Fin 4,
    pilotPrefixWeight θ p ε m n u *
      pilotConditionalVarianceBadMass select θ p ε δ m hselect hp hε hmn u

/-- The finite-product Chebyshev bound, specialized to one genuine adaptive main row and centered at its population variance. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hsub,hn,hmn,hδ,hclose), [the pilot Conditional Variance Bad Mass le](goal).

Under the stated assumptions, the pilot Conditional Variance Bad Mass le. -/
lemma pilotConditionalVarianceBadMass_le
    (θ : TrialParameter) (p ε δ : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hsub : PilotSublinear m) {n : ℕ} (hn : 2 ≤ n)
    (hmn : m n ≤ n) (u : Fin (m n) → Fin 4) (hδ : 0 < δ)
    (hclose : |adaptiveScoreVariance select θ
      (pilotAdaptivePrefixTheta p ε m hmn u) p ε -
        Vstar θ p ε| < δ / 2) :
    pilotConditionalVarianceBadMass select θ p ε δ m hselect hp hε hmn u ≤
      (2 * pilotPhiUpper p ε) ^ 4 /
          (adaptiveMainSize m n : ℝ) / (δ / 4) ^ 2 +
        (2 * pilotPhiUpper p ε) ^ 2 /
          (adaptiveMainSize m n : ℝ) / (δ / 4) := by
  classical
  let η₀ := pilotAdaptivePrefixTheta p ε m hmn u
  let η : ℕ → TrialParameter := fun k => if k = n then η₀ else θ
  have hη₀ : InteriorMeans η₀ := by
    exact pilotTheta_interior p ε m (pilotAdaptiveEncode hmn u (fun _ => 0))
  have hη : ∀ k, InteriorMeans (η k) := by
    intro k
    simp only [η]
    split_ifs <;> assumption
  have hηlim : Tendsto η atTop (nhds θ) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop n] with k hk
    simp [η, ne_of_gt hk]
  let M : RowModel (Fin 14) :=
    { N := adaptiveMainSize m
      w := adaptivePilotRowMass select θ (fun _ => 0) η p ε hselect hp hε
      f := adaptivePilotRowScore select θ (fun _ => 0) η p ε hselect hp hε
      B := 2 * pilotPhiUpper p ε
      v₀ := adaptivePilotLimitVariance select θ p ε hselect hp hθ hε
      mass_nonneg := adaptivePilotRowMass_nonneg
        select θ (fun _ => 0) η p ε hselect hp hθ hη hε
      mass_one := adaptivePilotRowMass_sum select θ (fun _ => 0) η p ε hselect hp hη hε
      centered := adaptivePilotRowScore_centered
        select θ (fun _ => 0) η p ε hselect hp hη hε
      bound := adaptivePilotRowScore_abs_le
        select θ (fun _ => 0) η p ε hselect hp hθ hη hε
      variance_tendsto := adaptivePilotRow_variance_tendsto
        select θ (fun _ => 0) η p ε hselect hp hθ hη hε hηlim
      variance_pos := adaptivePilotLimitVariance_pos select θ p ε hselect hp hθ hε
      length_tendsto := adaptiveMainSize_tendsto_atTop m hsub }
  have hN : 0 < M.N n := by
    change 0 < adaptiveMainSize m n
    rw [adaptiveMainSize, adaptivePilotSize_eq m hsub hn]
    exact Nat.sub_pos_of_lt (hsub.2 n hn).2
  have hmain : adaptiveMainSize m n = n - m n := by
    simp [adaptiveMainSize, adaptivePilotSize_eq m hsub hn]
  have hzero : adaptiveTrueParam θ (fun _ => 0) n = θ := by
    have hlocal : localAlternative θ (fun _ => 0) n = θ := by
      funext k
      simp [localAlternative]
    rw [adaptiveTrueParam_eq_localAlternative]
    · exact hlocal
    · simpa only [hlocal] using hθ
  have honeSecond : M.oneSecond n =
      adaptiveScoreVariance select θ η₀ p ε := by
    change (∑ s : Fin 14,
      adaptivePilotRowMass select θ (fun _ => 0) η p ε hselect hp hε n s *
        (adaptivePilotRowScore select θ (fun _ => 0) η p ε hselect hp hε n s) ^ 2) = _
    rw [adaptivePilotRow_secondMoment_eq
      select θ (fun _ => 0) η p ε hselect hp hη hε n, hzero]
    simp only [η, if_pos, η₀]
  have hrow (v : Fin (adaptiveMainSize m n) → Fin 14) :
      M.empiricalVariance n v =
        adaptivePilotRowEmpiricalVariance select θ (fun _ => 0)
          (fun _ => η₀) p ε m hselect hp hε n v := by
    simp only [M, RowModel.empiricalVariance, RowModel.empiricalSecond,
      RowModel.empiricalMean, RowModel.scoreSum,
      adaptivePilotRowEmpiricalVariance, adaptivePilotRowEmpiricalSecond,
      adaptivePilotRowEmpiricalMean, adaptivePilotRowScore, η]
    simp
  have hmass (v : Fin (adaptiveMainSize m n) → Fin 14) :
      adaptivePilotRowProductMass select θ (fun _ => 0) (fun _ => η₀)
          p ε m hselect hp hε n v = M.mass n v := by
    simp only [M, RowModel.mass, adaptivePilotRowProductMass,
      adaptivePilotRowMass, η, if_pos]
  have hmono : pilotConditionalVarianceBadMass select θ p ε δ m hselect hp hε hmn u ≤
      (M.productDesign n).Pr (fun v =>
        δ / 2 ≤ |M.empiricalVariance n v - M.oneSecond n|) := by
    unfold pilotConditionalVarianceBadMass
    dsimp only
    rw [Causalean.Experimentation.DesignBased.FiniteDesign.Pr,
      M.productDesign_expect]
    unfold RowModel.expect Causalean.Experimentation.DesignBased.FiniteDesign.ind
    change (∑ v : Fin (adaptiveMainSize m n) → Fin 14,
      adaptivePilotRowProductMass select θ (fun _ => 0) (fun _ => η₀)
          p ε m hselect hp hε n v *
        (if δ < |adaptivePilotRowEmpiricalVariance select θ (fun _ => 0)
          (fun _ => η₀) p ε m hselect hp hε n v - Vstar θ p ε| then 1 else 0)) ≤ _
    apply Finset.sum_le_sum
    intro v _
    rw [hmass v]
    have hind :
        (if δ < |adaptivePilotRowEmpiricalVariance select θ (fun _ => 0)
            (fun _ => η₀) p ε m hselect hp hε n v - Vstar θ p ε|
          then (1 : ℝ) else 0) ≤
          if δ / 2 ≤ |M.empiricalVariance n v - M.oneSecond n|
          then (1 : ℝ) else 0 := by
      by_cases hv : δ < |adaptivePilotRowEmpiricalVariance select θ (fun _ => 0)
          (fun _ => η₀) p ε m hselect hp hε n v - Vstar θ p ε|
      · have hgood : δ / 2 ≤ |M.empiricalVariance n v - M.oneSecond n| := by
          rw [hrow v, honeSecond]
          have htri := abs_sub_le
            (adaptivePilotRowEmpiricalVariance select θ (fun _ => 0)
              (fun _ => η₀) p ε m hselect hp hε n v)
            (adaptiveScoreVariance select θ η₀ p ε) (Vstar θ p ε)
          by_contra hc
          have hc' : |adaptivePilotRowEmpiricalVariance select θ (fun _ => 0)
              (fun _ => η₀) p ε m hselect hp hε n v -
                adaptiveScoreVariance select θ η₀ p ε| < δ / 2 :=
            lt_of_not_ge hc
          linarith
        simp [hv, hgood]
      · by_cases hg : δ / 2 ≤ |M.empiricalVariance n v - M.oneSecond n|
        · simp [hv, hg]
        · simp [hv, hg]
    exact mul_le_mul_of_nonneg_left hind (M.mass_nonnegative n v)
  rw [← M.eventProbability_eq_designPr] at hmono
  have hbound := M.eventProbability_empiricalVariance_sub_oneSecond_le
    n hN (δ / 2) (half_pos hδ)
  have hrhs : M.B ^ 4 / (M.N n : ℝ) / (δ / 2 / 2) ^ 2 +
      M.B ^ 2 / (M.N n : ℝ) / (δ / 2 / 2) =
      (2 * pilotPhiUpper p ε) ^ 4 /
          (adaptiveMainSize m n : ℝ) / (δ / 4) ^ 2 +
        (2 * pilotPhiUpper p ε) ^ 2 /
          (adaptiveMainSize m n : ℝ) / (δ / 4) := by
    dsimp only [M]
    ring
  exact (hmono.trans hbound).trans_eq hrhs

/-- Averaging the uniform finite-row bound over the genuine pilot prefixes gives vanishing bad variance mass. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hdiv,hsub,hδ), [the pilot Variance Bad Mass tendsto zero](goal).

Under the stated assumptions, the pilot Variance Bad Mass tendsto zero. -/
lemma pilotVarianceBadMass_tendsto_zero
    (θ : TrialParameter) (p ε δ : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hdiv : PilotDiverges m) (hsub : PilotSublinear m) (hδ : 0 < δ) :
    Tendsto (fun n => if hn : 2 ≤ n then
      pilotVarianceBadMass select θ p ε δ m hselect hp hε
        (Nat.le_of_lt (hsub.2 n hn).2) else 0) atTop (nhds 0) := by
  obtain ⟨R, hR, hcont⟩ := adaptiveScoreVariance_uniform_near_diag
    select θ p ε hselect hp hθ hε (δ / 2) (half_pos hδ)
  let M₀ := adaptiveInteriorMargin θ
  have hM₀ : 0 < M₀ := adaptiveInteriorMargin_pos θ hθ
  let r := min (R / 2) (M₀ / 4)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r ≤ R / 2 := min_le_left _ _
  have hrM : r ≤ M₀ / 4 := min_le_right _ _
  let rowEnvelope : ℕ → ℝ := fun n =>
    (2 * pilotPhiUpper p ε) ^ 4 /
        (adaptiveMainSize m n : ℝ) / (δ / 4) ^ 2 +
      (2 * pilotPhiUpper p ε) ^ 2 /
        (adaptiveMainSize m n : ℝ) / (δ / 4)
  have hrowEnv : Tendsto rowEnvelope atTop (nhds 0) := by
    have hlen := adaptiveMainSize_tendsto_atTop m hsub
    have hfirst := (tendsto_const_div_atTop_nhds_zero_nat
      ((2 * pilotPhiUpper p ε) ^ 4)).comp hlen
    have hsecond := (tendsto_const_div_atTop_nhds_zero_nat
      ((2 * pilotPhiUpper p ε) ^ 2)).comp hlen
    dsimp only [rowEnvelope]
    simpa only [Function.comp_def, zero_div, add_zero] using
      (hfirst.div_const ((δ / 4) ^ 2)).add
        (hsecond.div_const (δ / 4))
  have hreg := pilotRegularizer_eventually_lt m hdiv (M₀ / 2) (by positivity)
  have hbadEnv := pilotBadMassEnvelope_tendsto_zero
    p ε r m hp hε hr hdiv
  have hbound : ∀ᶠ n in atTop,
      (if hn : 2 ≤ n then pilotVarianceBadMass select θ p ε δ m hselect hp hε
          (Nat.le_of_lt (hsub.2 n hn).2) else 0) ≤
        pilotBadMassEnvelope p ε r m n + rowEnvelope n := by
    filter_upwards [eventually_ge_atTop 2, hreg] with n hn hnreg
    let hmn : m n ≤ n := Nat.le_of_lt (hsub.2 n hn).2
    rw [dif_pos hn]
    have hproof : Nat.le_of_lt (hsub.2 n hn).2 = hmn := Subsingleton.elim _ _
    rw [show Nat.le_of_lt (hsub.2 n hn).2 = hmn from hproof]
    have hmpos : 0 < m n := lt_of_lt_of_le Nat.zero_lt_one (hsub.2 n hn).1
    have hM0l : M₀ ≤ θ 0 := (min_le_left _ _).trans (min_le_left _ _)
    have hM0r : M₀ ≤ 1 - θ 0 := (min_le_left _ _).trans (min_le_right _ _)
    have hM1l : M₀ ≤ θ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have hM1r : M₀ ≤ 1 - θ 1 := (min_le_right _ _).trans (min_le_right _ _)
    have hδ0l : (m n + 2 : ℝ)⁻¹ + r ≤ θ 0 := by
      dsimp only [M₀] at hnreg hrM hM0l
      linarith
    have hδ0r : (m n + 2 : ℝ)⁻¹ + r ≤ 1 - θ 0 := by
      dsimp only [M₀] at hnreg hrM hM0r
      linarith
    have hδ1l : (m n + 2 : ℝ)⁻¹ + r ≤ θ 1 := by
      dsimp only [M₀] at hnreg hrM hM1l
      linarith
    have hδ1r : (m n + 2 : ℝ)⁻¹ + r ≤ 1 - θ 1 := by
      dsimp only [M₀] at hnreg hrM hM1r
      linarith
    have hbad := pilotPrefixBadMass_le select θ p ε r m hselect hp hθ hε hr hmn hmpos
      hδ0l hδ0r hδ1l hδ1r
    have hw (u : Fin (m n) → Fin 4) :
        0 ≤ pilotPrefixWeight θ p ε m n u :=
      pilotPrefixWeight_nonneg θ p ε m n hp hθ u
    have hcond (u : Fin (m n) → Fin 4) :
        pilotConditionalVarianceBadMass select θ p ε δ m hselect hp hε hmn u ≤
          (if r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 0 - θ 0| ∨
              r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 1 - θ 1|
            then 1 else rowEnvelope n) := by
      by_cases hu : r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 0 - θ 0| ∨
          r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 1 - θ 1|
      · rw [if_pos hu]
        let η := fun _ : ℕ => pilotAdaptivePrefixTheta p ε m hmn u
        have hη : ∀ k, InteriorMeans (η k) := fun _ =>
          pilotTheta_interior p ε m (pilotAdaptiveEncode hmn u (fun _ => 0))
        unfold pilotConditionalVarianceBadMass
        dsimp only
        calc
          _ ≤ ∑ v : Fin (adaptiveMainSize m n) → Fin 14,
              adaptivePilotRowProductMass select θ (fun _ => 0) η
                p ε m hselect hp hε n v := by
            apply Finset.sum_le_sum
            intro v _
            apply mul_le_of_le_one_right
            · exact adaptivePilotRowProductMass_nonneg
                select θ (fun _ => 0) η p ε m hselect hp hθ hη hε n v
            · split_ifs <;> norm_num
          _ = 1 := adaptivePilotRowProductMass_sum
            select θ (fun _ => 0) η p ε m hselect hp hη hε n
      · rw [if_neg hu]
        push Not at hu
        have hηdist : dist (pilotAdaptivePrefixTheta p ε m hmn u) θ < R := by
          rw [dist_pi_lt_iff hR]
          intro k
          have hrltR : r < R := lt_of_le_of_lt hrR (by linarith)
          fin_cases k
          · rw [Real.dist_eq]
            change |pilotAdaptivePrefixTheta p ε m hmn u 0 - θ 0| < R
            linarith [hu.1]
          · rw [Real.dist_eq]
            change |pilotAdaptivePrefixTheta p ε m hmn u 1 - θ 1| < R
            linarith [hu.2]
        have hclose : |adaptiveScoreVariance select θ
            (pilotAdaptivePrefixTheta p ε m hmn u) p ε -
              Vstar θ p ε| < δ / 2 := by
          exact hcont θ (pilotAdaptivePrefixTheta p ε m hmn u)
            (by simpa using hR) hηdist
        exact pilotConditionalVarianceBadMass_le
          select θ p ε δ m hselect hp hθ hε hsub hn hmn u hδ hclose
    unfold pilotVarianceBadMass
    calc
      _ ≤ ∑ u : Fin (m n) → Fin 4,
          pilotPrefixWeight θ p ε m n u *
            (if r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 0 - θ 0| ∨
                r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 1 - θ 1|
              then 1 else rowEnvelope n) :=
        Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hcond u) (hw u)
      _ ≤ ∑ u : Fin (m n) → Fin 4,
          pilotPrefixWeight θ p ε m n u *
            ((if r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 0 - θ 0| ∨
                r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 1 - θ 1|
              then 1 else 0) + rowEnvelope n) := by
        apply Finset.sum_le_sum
        intro u _
        apply mul_le_mul_of_nonneg_left _ (hw u)
        have hrow0 : 0 ≤ rowEnvelope n := by
          dsimp only [rowEnvelope]
          positivity
        split_ifs <;> linarith
      _ = pilotPrefixBadMass θ p ε r m hmn + rowEnvelope n := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul,
          pilotPrefixWeight_sum θ p ε m n, one_mul]
        rfl
      _ ≤ pilotBadMassEnvelope p ε r m n + rowEnvelope n :=
        add_le_add hbad le_rfl
  have hnonneg : ∀ n, 0 ≤ (if hn : 2 ≤ n then
      pilotVarianceBadMass select θ p ε δ m hselect hp hε
        (Nat.le_of_lt (hsub.2 n hn).2) else 0) := by
    intro n
    by_cases hn : 2 ≤ n
    · rw [dif_pos hn]
      let hmn : m n ≤ n := Nat.le_of_lt (hsub.2 n hn).2
      have hproof : Nat.le_of_lt (hsub.2 n hn).2 = hmn := Subsingleton.elim _ _
      rw [show Nat.le_of_lt (hsub.2 n hn).2 = hmn from hproof]
      unfold pilotVarianceBadMass pilotConditionalVarianceBadMass
      exact Finset.sum_nonneg fun u _ => mul_nonneg
        (pilotPrefixWeight_nonneg θ p ε m n hp hθ u)
        (Finset.sum_nonneg fun v _ => mul_nonneg
          (adaptivePilotRowProductMass_nonneg select θ (fun _ => 0)
            (fun _ => pilotAdaptivePrefixTheta p ε m hmn u)
            p ε m hselect hp hθ (fun _ => pilotTheta_interior p ε m
              (pilotAdaptiveEncode hmn u (fun _ => 0))) hε n v)
          (by split_ifs <;> positivity))
    · simp [hn]
  exact squeeze_zero' (Eventually.of_forall hnonneg) hbound
    (by simpa only [add_zero] using hbadEnv.add hrowEnv)

end CausalSmith.Stat.LdpAteEfficiencySurface

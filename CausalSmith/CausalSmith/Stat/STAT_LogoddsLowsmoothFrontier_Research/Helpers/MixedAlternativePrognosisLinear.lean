module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedNullPrognosisLinear
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedPropensityLinear
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Alternative mixed prognosis spatial bounds

The smooth control-logit map is locally Lipschitz on a fixed interior box.
The spatial moduli of the calibrated margins then preserve the prognosis amplitude.
-/
public section
set_option linter.style.whitespace false
set_option linter.style.longLine false
noncomputable section
open Filter
open scoped Topology
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The control logit is smooth at the independent central table. [the stated conclusion](goal) holds. -/
-- @node: mixedControlLogit_contDiffAt_center
lemma mixedControlLogit_contDiffAt_center :
    ContDiffAt ℝ 1 (fun v : Fin 3 → ℝ =>
      logit (v 2-covarianceBranch (v 0) (v 1) (v 2)/(1-v 1))) ![0,1/2,1/2] := by
  have hc := covarianceBranch_contDiffAt_center.of_le (show (1 : WithTop ℕ∞) ≤ ⊤ by simp)
  have hr : ContDiffAt ℝ 1 (fun v : Fin 3 → ℝ =>
      v 2-covarianceBranch (v 0) (v 1) (v 2)/(1-v 1)) ![0,1/2,1/2] := by
    apply ContDiffAt.sub
    · fun_prop
    · exact hc.div (by fun_prop) (by norm_num)
  unfold logit
  apply ContDiffAt.log
  · exact hr.div (contDiffAt_const.sub hr) (by change 1-(1/2-covarianceBranch 0 (1/2) (1/2)/(1-1/2)) ≠ (0 : ℝ); norm_num [covarianceBranch])
  · change (1/2-covarianceBranch 0 (1/2) (1/2)/(1-1/2))/(1-(1/2-covarianceBranch 0 (1/2) (1/2)/(1-1/2))) ≠ (0 : ℝ)
    norm_num [covarianceBranch]

/-- A fixed signed interior box has one finite control-logit Lipschitz constant. [the stated conclusion](goal) holds. -/
-- @node: mixedControlLogit_uniform_lipschitz
lemma mixedControlLogit_uniform_lipschitz : ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
    ∀ t ex ez mx mz : ℝ,
      |t| ≤ r → |ex-1/2| ≤ r → |ez-1/2| ≤ r →
      |mx-1/2| ≤ r → |mz-1/2| ≤ r →
      |logit (mx-covarianceBranch t ex mx/(1-ex))-
        logit (mz-covarianceBranch t ez mz/(1-ez))| ≤
        C*(|ex-ez|+|mx-mz|) := by
  obtain ⟨K,S,hS,hLip⟩ := mixedControlLogit_contDiffAt_center.exists_lipschitzOnWith
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨d/2,(K : ℝ)+1,by linarith,by positivity,?_⟩
  intro t ex ez mx mz ht hex hez hmx hmz
  have hmem (e m : ℝ) (he : |e-1/2| ≤ d/2) (hm : |m-1/2| ≤ d/2) :
      ![t,e,m] ∈ S := by
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hd]
    intro i
    fin_cases i
    · change dist t 0 < d
      rw [Real.dist_eq, sub_zero]; linarith
    · change dist e (1/2) < d
      rw [Real.dist_eq]; linarith
    · change dist m (1/2) < d
      rw [Real.dist_eq]; linarith
  have hh := hLip.dist_le_mul _ (hmem ex mx hex hmx) _ (hmem ez mz hez hmz)
  have hv : dist (![t,ex,mx] : Fin 3 → ℝ) ![t,ez,mz] ≤ |ex-ez|+|mx-mz| := by
    apply (dist_pi_le_iff (by positivity)).mpr
    intro i
    fin_cases i <;> simp [Real.dist_eq] <;> positivity
  have hh' := mul_le_mul_of_nonneg_left hv K.coe_nonneg
  simp only [Real.dist_eq] at hh
  change |logit (mx-covarianceBranch t ex mx/(1-ex))-
    logit (mz-covarianceBranch t ez mz/(1-ez))| ≤ _ at hh
  nlinarith [abs_nonneg (ex-ez),abs_nonneg (mx-mz)]

/-- The actual alternative control risk uses the smooth calibrated margin map. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hη,hζ,hv) hold, and [the stated conclusion follows](goal). -/
-- @node: mixedCells_alternative_control_risk_eq
lemma mixedCells_alternative_control_risk_eq (k : ℕ) (σ : Fin (k+1) → Bool)
    (η ζ : ℝ) (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100)
    (hv : ValidCells (mixedCells true k σ η ζ)) (x : Covariate) :
    let e := 1/2-η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x
    let m := 1/2+ζ*signFieldZ k σ x
    armRisk (mixedLaw true k σ η ζ) false x = m-covarianceBranch (32*η*ζ) e m/(1-e) := by
  have he := (abs_le.mp (mixed_margin_bounds true k σ η ζ x hη hζ).1).2
  simp only [if_true] at he
  rw [armRisk, mixedLaw, totalCellLaw_cells_of_valid _ hv]
  dsimp only
  change tableCell _ _ _ false true / (tableCell _ _ _ false false + tableCell _ _ _ false true) = _
  exact mixed_table_control_risk_eq _ _ _ (by simp only [if_true]; linarith)

/-- [Fixed local Lipschitz and root derivative bounds yield the alternative
prognosis spatial modulus with its amplitude factor intact. [the documented result](goal) Under [the stated assumptions](hyp:hC,hB,hLip,hk,hη,hζ,horder,ht,he,hm,hd,hb,x). -/
-- @node: mixedCells_alternative_prognosis_linear_of_root
lemma mixedCells_alternative_prognosis_linear_of_root (r C B : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hLip : ∀ t ex ez mx mz : ℝ,
      |t| ≤ r → |ex-1/2| ≤ r → |ez-1/2| ≤ r →
      |mx-1/2| ≤ r → |mz-1/2| ≤ r →
      |logit (mx-covarianceBranch t ex mx/(1-ex))-
        logit (mz-covarianceBranch t ez mz/(1-ez))| ≤ C*(|ex-ez|+|mx-mz|))
    (k : ℕ) (hk : 1 ≤ k) (σ : Fin (k+1) → Bool) (η ζ : ℝ)
    (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100) (horder : |η| ≤ |ζ|)
    (ht : |32*η*ζ| ≤ r) (he : (5/2)*|η| ≤ r) (hm : 2*|ζ| ≤ r)
    (hd : ∀ u ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (mixedRoot η ζ) u)
    (hb : ∀ u ∈ Set.Icc (0 : ℝ) 1, |deriv (mixedRoot η ζ) u| ≤ B)
    (x z : Covariate) :
    |prognosisLogit (mixedLaw true k σ η ζ) x-
      prognosisLogit (mixedLaw true k σ η ζ) z| ≤
      C*(9+2*B)*|ζ| *(k : ℝ)*|(x : ℝ)-(z : ℝ)| := by
  classical
  by_cases hv : ValidCells (mixedCells true k σ η ζ)
  · let e := fun w : Covariate => 1/2-η*mixedRoot η ζ (cellCoord k w)*signFieldZ k σ w
    let m := fun w : Covariate => 1/2+ζ*signFieldZ k σ w
    have hew (w : Covariate) : |e w-1/2| ≤ r :=
      (mixed_margin_displacement true k σ η ζ w).trans he
    have hmw (w : Covariate) : |m w-1/2| ≤ r := by
      dsimp [m]
      rw [add_sub_cancel_left,abs_mul]
      exact (mul_le_mul_of_nonneg_left (signFieldZ_abs_le_two k σ w) (abs_nonneg ζ)).trans (by nlinarith)
    have hl := hLip (32*η*ζ) (e x) (e z) (m x) (m z) ht (hew x) (hew z) (hmw x) (hmw z)
    have hel : |e x-e z| ≤ |η| *(5+2*B)*(k : ℝ)*|(x : ℝ)-(z : ℝ)| := by
      dsimp [e]
      rw [show 1/2-η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x-
        (1/2-η*mixedRoot η ζ (cellCoord k z)*signFieldZ k σ z) =
        -η*(mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x-
          mixedRoot η ζ (cellCoord k z)*signFieldZ k σ z) by ring,abs_mul,abs_neg]
      have hh := mul_le_mul_of_nonneg_left (mixedRoot_signField_lipschitz k hk σ η ζ B hB hd hb x z) (abs_nonneg η)
      nlinarith only [hh]
    have hml : |m x-m z| ≤ 4*|ζ| *(k : ℝ)*|(x : ℝ)-(z : ℝ)| := by
      dsimp [m]
      rw [show 1/2+ζ*signFieldZ k σ x-(1/2+ζ*signFieldZ k σ z) =
        ζ*(signFieldZ k σ x-signFieldZ k σ z) by ring,abs_mul]
      have hh := mul_le_mul_of_nonneg_left (signFieldZ_lipschitz k hk σ x z) (abs_nonneg ζ)
      nlinarith only [hh]
    have heorder := mul_le_mul_of_nonneg_right horder
      (show 0 ≤ (5+2*B)*(k : ℝ)*|(x : ℝ)-(z : ℝ)| by positivity)
    have hsum : |e x-e z|+|m x-m z| ≤
        (9+2*B)*|ζ| *(k : ℝ)*|(x : ℝ)-(z : ℝ)| := by
      nlinarith only [hel,hml,heorder]
    change |logit (armRisk _ false x)-logit (armRisk _ false z)| ≤ _
    rw [mixedCells_alternative_control_risk_eq k σ η ζ hη hζ hv x,
      mixedCells_alternative_control_risk_eq k σ η ζ hη hζ hv z]
    exact hl.trans (by nlinarith only [mul_le_mul_of_nonneg_left hsum hC])
  · have hz : ∀ w, prognosisLogit (mixedLaw true k σ η ζ) w = 0 := by
      intro w
      norm_num [prognosisLogit,armRisk,mixedLaw,totalCellLaw,hv,lawFromCells,logit]
    rw [hz x,hz z,sub_self,abs_zero]
    positivity

/-- One positive radius fits the alternative prognosis modulus to the public rate for every legal exponent pair, including the Lipschitz endpoint. the documented result Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: mixedCells_uniform_alternative_prognosis_linear
lemma mixedCells_uniform_alternative_prognosis_linear : ∃ r : ℝ, 0 < r ∧ r ≤ 1/100 ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α β : ℝ, ExponentDomain α β →
      ∀ k : ℕ, 1 ≤ k → ∀ σ : Fin (k+1) → Bool, ∀ x z,
        |prognosisLogit (mixedLaw true k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))) x-
          prognosisLogit (mixedLaw true k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))) z| ≤
          (k : ℝ)^(1-β)*|(x : ℝ)-(z : ℝ)| := by
  obtain ⟨d,C,hd,hC,hLip⟩ := mixedControlLogit_uniform_lipschitz
  obtain ⟨a,ha,hs,hbounds⟩ := mixedRoot_uniform_smooth_derivative_bounds
  obtain ⟨B,hB,hb⟩ := hbounds 1
  let r := min a (min (1/100) (min (d/3) (1/(C*(9+2*B)))))
  have hr : 0 < r := lt_min ha (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
  have hra : r ≤ a := min_le_left _ _
  have hrsmall : r ≤ 1/100 := (min_le_right _ _).trans (min_le_left _ _)
  have hrd : r ≤ d/3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrcoef : C*(9+2*B)*r ≤ 1 := by
    have hh : r ≤ 1/(C*(9+2*B)) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (show 0 < C*(9+2*B) by positivity)).mp hh
    nlinarith only [hh']
  refine ⟨r,hr,hrsmall,?_⟩
  intro ε hε hεr α β hab k hk σ x z
  let η := ε*(k : ℝ)^(-α)
  let ζ := ε*(k : ℝ)^(-β)
  have hα : 0 ≤ α := (hab.1.trans hab.2.2.1).le
  have hβ : 0 ≤ β := hab.1.le
  have hη : |η| ≤ r := (calibrated_amplitude_abs_le ε α hε.le hα k hk).trans hεr
  have hζ : |ζ| ≤ r := (calibrated_amplitude_abs_le ε β hε.le hβ k hk).trans hεr
  have hηpos : 0 ≤ η := by dsimp [η]; positivity
  have hζpos : 0 ≤ ζ := by dsimp [ζ]; positivity
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have horder : |η| ≤ |ζ| := by
    rw [abs_of_nonneg hηpos,abs_of_nonneg hζpos]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk) (neg_le_neg hab.2.2.1.le)) hε.le
  have ht : |32*η*ζ| ≤ d := by
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 32)]
    have hh := mul_le_mul_of_nonneg_right (hη.trans hrsmall) (abs_nonneg ζ)
    nlinarith only [hh,hζ,hrd,hd]
  have he : (5/2)*|η| ≤ d := by linarith
  have hm : 2*|ζ| ≤ d := by linarith
  have hroot (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :=
    mixedRoot_spatial_derivative_bound η ζ u B
      (hs ![η,ζ,u] (hη.trans hra) (hζ.trans hra) hu)
      (hb ![η,ζ,u] (hη.trans hra) (hζ.trans hra) hu)
  have hl := mixedCells_alternative_prognosis_linear_of_root d C B hC.le hB.le hLip
    k hk σ η ζ (hη.trans hrsmall) (hζ.trans hrsmall) horder ht he hm
    (fun u hu => (hroot u hu).1) (fun u hu => (hroot u hu).2) x z
  have heps : C*(9+2*B)*ε ≤ 1 :=
    (mul_le_mul_of_nonneg_left hεr (by positivity)).trans hrcoef
  have hrate : (k : ℝ)^(1-β) = (k : ℝ)^(-β)*(k : ℝ) := by
    rw [show 1-β = -β+1 by ring,Real.rpow_add hkpos,Real.rpow_one]
  rw [abs_of_nonneg hζpos] at hl
  have hh := mul_le_mul_of_nonneg_right heps (Real.rpow_nonneg hkpos.le (-β))
  have hh' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hh hkpos.le) (abs_nonneg ((x : ℝ)-(z : ℝ)))
  rw [hrate]
  dsimp [ζ] at hl
  nlinarith only [hl,hh']

end CausalSmith.Stat.LogoddsLowsmoothFrontier

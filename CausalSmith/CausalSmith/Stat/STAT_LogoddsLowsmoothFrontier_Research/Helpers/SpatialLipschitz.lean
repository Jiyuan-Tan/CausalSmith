module
public import Causalean.Mathlib.Analysis.PiecewiseLipschitz
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairSpatialOscillation
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.SpatialGluing
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Shared-endpoint Lipschitz gluing

Local Lipschitz bounds telescope across the finite chain of cells. This is the
roadmap's subdivision argument and does not require matching endpoint derivatives.
-/
public section
set_option linter.style.whitespace false
noncomputable section
open scoped ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- Given [a finite number of cells](hyp:k), [a profile on each cell](hyp:F), and [a common local
constant](hyp:C), [local bounds](hyp:hlocal) and [matching endpoint values](hyp:hend) telescope for
[cell indices](hyp:i,j) satisfying [their order](hyp:hij) and [range condition](hyp:hjk), and for
[cell coordinates](hyp:u,v) satisfying [the first unit-interval condition](hyp:hu), [the second
unit-interval condition](hyp:hv), and [global coordinate order](hyp:horder), to [exactly the distance
between the two cell coordinates](goal). -/
-- @node: cell_profile_chain_bound
lemma cell_profile_chain_bound (k : ℕ) (F : ℕ → ℝ → ℝ) (C : ℝ)
    (hlocal : ∀ j < k, ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      |F j u-F j v| ≤ C*|u-v|)
    (hend : ∀ j, j+1 < k → F j 1 = F (j+1) 0)
    (i j : ℕ) (hij : i ≤ j) (hjk : j < k)
    (u v : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (horder : (i : ℝ)+u ≤ (j : ℝ)+v) :
    |F i u-F j v| ≤ C*((j : ℝ)-(i : ℝ)+v-u) := by
  exact Causalean.Mathlib.Analysis.piecewiseLipschitz_chain_bound
    k F C hlocal hend i j hij hjk u v hu hv horder

/-- [The cell selector is monotone in the covariate.](goal) Under [the stated assumptions](hyp:x). Under [the stated assumptions](hyp:hxz). -/
-- @node: cellIndex_mono
lemma cellIndex_mono (k : ℕ) (x z : Covariate) (hxz : (x : ℝ) ≤ z) :
    cellIndex k x ≤ cellIndex k z := by
  have hf := Int.floor_mono (mul_le_mul_of_nonneg_left hxz (Nat.cast_nonneg k))
  have hn : (⌊(k : ℝ)*(x : ℝ)⌋ : ℤ).toNat ≤
      (⌊(k : ℝ)*(z : ℝ)⌋ : ℤ).toNat := by omega
  exact min_le_min_left _ hn

/-- [A common local Lipschitz constant becomes a global constant multiplied by
rank after gluing the shared endpoints, including points in different cells. [the documented result](goal) Under [the stated assumptions](hyp:hlocal,hend,x). Under [the stated assumptions](hyp:hk). -/
-- @node: cell_profile_lipschitz
lemma cell_profile_lipschitz (k : ℕ) (hk : 1 ≤ k) (F : ℕ → ℝ → ℝ) (C : ℝ)
    (hlocal : ∀ j < k, ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      |F j u-F j v| ≤ C*|u-v|)
    (hend : ∀ j, j+1 < k → F j 1 = F (j+1) 0) (x z : Covariate) :
    |F (cellIndex k x) (cellCoord k x)-F (cellIndex k z) (cellCoord k z)| ≤
      C*(k : ℝ)*|(x : ℝ)-(z : ℝ)| := by
  have ordered (x z : Covariate) (hxz : (x : ℝ) ≤ z) :
      |F (cellIndex k x) (cellCoord k x)-F (cellIndex k z) (cellCoord k z)| ≤
        C*(k : ℝ)*|(x : ℝ)-(z : ℝ)| := by
    have hb := cell_profile_chain_bound k F C hlocal hend _ _ (cellIndex_mono k x z hxz)
      (cellIndex_lt k hk z) _ _ (cellCoord_mem_unit k hk x) (cellCoord_mem_unit k hk z)
      (by dsimp [cellCoord]; nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k])
    rw [abs_of_nonpos (sub_nonpos.mpr hxz)]
    convert hb using 1; dsimp [cellCoord]; ring
  rcases le_total (x : ℝ) (z : ℝ) with h | h
  · exact ordered x z h
  · simpa only [abs_sub_comm] using ordered z x h

/-- [A profile whose endpoint values agree inherits the global rank-scaled
Lipschitz bound through the discontinuous within-cell coordinate selector. [the documented result](goal) Under [the stated assumptions](hyp:hf,hend,x). Under [the stated assumptions](hyp:hk). -/
-- @node: cellCoord_comp_lipschitz
lemma cellCoord_comp_lipschitz (k : ℕ) (hk : 1 ≤ k) (f : ℝ → ℝ) (C : ℝ)
    (hf : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      |f u-f v| ≤ C*|u-v|) (hend : f 1 = f 0) (x z : Covariate) :
    |f (cellCoord k x)-f (cellCoord k z)| ≤ C*(k : ℝ)*|(x : ℝ)-(z : ℝ)| := by
  exact cell_profile_lipschitz k hk (fun _ => f) C (fun _ _ => hf) (fun _ _ => hend) x z

/-- [The shared sign field has a global Lipschitz constant at most four times
rank, obtained from the two trigonometric profiles and endpoint gluing. [the documented result](goal) Under [the stated assumptions](hyp:x). Under [the stated assumptions](hyp:hk). -/
-- @node: signFieldZ_lipschitz
lemma signFieldZ_lipschitz (k : ℕ) (hk : 1 ≤ k) (σ : Fin (k+1) → Bool)
    (x z : Covariate) :
    |signFieldZ k σ x-signFieldZ k σ z| ≤ 4*(k : ℝ)*|(x : ℝ)-(z : ℝ)| := by
  apply cell_profile_lipschitz k hk
    (fun j u => endpointSign k σ j*Real.cos (Real.pi*u/2)+
      endpointSign k σ (j+1)*Real.sin (Real.pi*u/2)) 4
  · intro j hj u hu v hv
    have hc := Real.abs_cos_sub_cos_le (Real.pi*u/2) (Real.pi*v/2)
    have hs := Real.abs_sin_sub_sin_le (Real.pi*u/2) (Real.pi*v/2)
    have hab : |Real.pi*u/2-Real.pi*v/2| = (Real.pi/2)*|u-v| := by
      rw [show Real.pi*u/2-Real.pi*v/2 = (Real.pi/2)*(u-v) by ring, abs_mul,
        abs_of_pos (by positivity : 0 < Real.pi/2)]
    rw [hab] at hc hs
    have he (j : ℕ) : |endpointSign k σ j| = 1 := by
      unfold endpointSign signValue
      split <;> norm_num
    calc
      _ = |endpointSign k σ j*(Real.cos (Real.pi*u/2)-Real.cos (Real.pi*v/2))+
          endpointSign k σ (j+1)*(Real.sin (Real.pi*u/2)-Real.sin (Real.pi*v/2))| := by
        congr 1; ring
      _ ≤ |endpointSign k σ j*(Real.cos (Real.pi*u/2)-Real.cos (Real.pi*v/2))|+
          |endpointSign k σ (j+1)*(Real.sin (Real.pi*u/2)-Real.sin (Real.pi*v/2))| := abs_add_le _ _
      _ ≤ 4*|u-v| := by
        simp only [abs_mul, he, one_mul]
        nlinarith [Real.pi_lt_four, abs_nonneg (u-v)]
  · intro j hj
    simp

/-- [The fair root's quadratic spatial derivative bound becomes a global
quadratic Lipschitz bound; its two endpoint values agree. [the documented result](goal) Under [the stated assumptions](hyp:hd,hb,x). Under [the stated assumptions](hyp:hk). -/
-- @node: fairRoot_spatial_lipschitz
lemma fairRoot_spatial_lipschitz (k : ℕ) (hk : 1 ≤ k) (t δ B : ℝ)
    (hd : ∀ u ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (fairRoot t δ) u)
    (hb : ∀ u ∈ Set.Icc (0 : ℝ) 1, |deriv (fairRoot t δ) u| ≤ B*δ^2)
    (x z : Covariate) :
    |fairRoot t δ (cellCoord k x)-fairRoot t δ (cellCoord k z)| ≤
      B*δ^2*(k : ℝ)*|(x : ℝ)-(z : ℝ)| := by
  apply cellCoord_comp_lipschitz k hk _ (B*δ^2) _ (fairRoot_endpoints t δ).symm
  intro u hu v hv
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le hd
      (by simpa only [Real.norm_eq_abs] using hb) hv hu

/-- [Global fair root and sign bounds give a linear spatial bound for the
native prognosis logit of either construction, with zero on fallback laws. [the documented result](goal) Under [the stated assumptions](hyp:hB,hδ,hp,hd,hb,x). Under [the stated assumptions](hyp:hk). -/
-- @node: fairCells_prognosis_linear_of_centering
lemma fairCells_prognosis_linear_of_centering (b : Bool) (k : ℕ) (hk : 1 ≤ k)
    (σ : Fin (k+1) → Bool) (t δ B : ℝ) (hB : 0 ≤ B) (hδ : |δ| ≤ 1/100)
    (hp : ∀ x : Covariate, |fairRoot t δ (cellCoord k x)-2/5| ≤ 1/100)
    (hd : ∀ u ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (fairRoot t δ) u)
    (hb : ∀ u ∈ Set.Icc (0 : ℝ) 1, |deriv (fairRoot t δ) u| ≤ B*δ^2)
    (x z : Covariate) :
    |prognosisLogit (totalCellLaw (fairCells b k σ t δ)) x-
      prognosisLogit (totalCellLaw (fairCells b k σ t δ)) z| ≤
      6*(B*δ^2+4*|δ|)*(k : ℝ)*|(x : ℝ)-(z : ℝ)| := by
  classical
  by_cases hv : ValidCells (fairCells b k σ t δ)
  · change |logit (armRisk _ false x)-logit (armRisk _ false z)| ≤ _
    rw [fairCells_armRisk_control b k σ t δ hv x, fairCells_armRisk_control b k σ t δ hv z]
    have hl := calibrated_logit_difference_le _ _
      (fair_control_risk_bounds_of_centering b k σ t δ x hδ (hp x))
      (fair_control_risk_bounds_of_centering b k σ t δ z hδ (hp z))
    have hr := fairRoot_spatial_lipschitz k hk t δ B hd hb x z
    have hs := signFieldZ_lipschitz k hk σ x z
    have hprod := mul_le_mul_of_nonneg_left hs (abs_nonneg δ)
    have hctrl : |(if b then fairRoot t δ (cellCoord k x)+δ*signFieldZ k σ x
        else fairRoot t δ (cellCoord k x))-
        (if b then fairRoot t δ (cellCoord k z)+δ*signFieldZ k σ z
        else fairRoot t δ (cellCoord k z))| ≤
        (B*δ^2+4*|δ|)*(k : ℝ)*|(x : ℝ)-(z : ℝ)| := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · nlinarith [mul_nonneg (abs_nonneg δ)
          (mul_nonneg (Nat.cast_nonneg k) (abs_nonneg ((x : ℝ)-(z : ℝ))))]
      · calc
          _ = |(fairRoot t δ (cellCoord k x)-fairRoot t δ (cellCoord k z))+
              δ*(signFieldZ k σ x-signFieldZ k σ z)| := by congr 1; ring
          _ ≤ |fairRoot t δ (cellCoord k x)-fairRoot t δ (cellCoord k z)|+
              |δ*(signFieldZ k σ x-signFieldZ k σ z)| := abs_add_le _ _
          _ ≤ _ := by rw [abs_mul]; nlinarith
    nlinarith
  · have hz : ∀ w, prognosisLogit (totalCellLaw (fairCells b k σ t δ)) w = 0 := by
      intro w
      norm_num [prognosisLogit, armRisk, totalCellLaw, hv, lawFromCells, logit]
    rw [hz x, hz z, sub_self, abs_zero]
    positivity

/-- One absolute positive radius proves the fair prognosis linear scale bound for every nonnegative exponent and every rank, for both calibrated laws. the documented result Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: fairCells_uniform_prognosis_linear
lemma fairCells_uniform_prognosis_linear : ∃ r : ℝ, 0 < r ∧ r ≤ 1/100 ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ β : ℝ, 0 ≤ β → ∀ k : ℕ, 1 ≤ k →
      ∀ σ : Fin (k+1) → Bool, ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → ∀ b,
        ∀ x z, |prognosisLogit (totalCellLaw (fairCells b k σ t (ε*(k : ℝ)^(-β)))) x-
          prognosisLogit (totalCellLaw (fairCells b k σ t (ε*(k : ℝ)^(-β)))) z| ≤
          (k : ℝ)^(1-β)*|(x : ℝ)-(z : ℝ)| := by
  obtain ⟨a, B, ha, hB, _, _, _, _, hf⟩ := exact_calibrations
  obtain ⟨s, hs, _, hsm⟩ := fairRoot_uniform_contDiffAt
  let r := min a (min s (min (1/100) (1/(100*(B+1)))))
  have hr : 0 < r := lt_min ha (lt_min hs (lt_min (by norm_num) (by positivity)))
  have hra : r ≤ a := min_le_left _ _
  have hrs : r ≤ s := (min_le_right _ _).trans (min_le_left _ _)
  have hrt : r ≤ min (1/100) (1/(100*(B+1))) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hrsmall : r ≤ 1/100 := hrt.trans (min_le_left _ _)
  have hrB : r ≤ 1/(100*(B+1)) := hrt.trans (min_le_right _ _)
  have hBr : B*r ≤ 1/100 := by
    have hh := (le_div_iff₀ (show 0 < 100*(B+1) by positivity)).mp hrB
    nlinarith
  refine ⟨r,hr,hrsmall,?_⟩
  intro ε hε hεr β hβ k hk σ t ht b x z
  let δ := ε*(k : ℝ)^(-β)
  have hd : |δ| ≤ ε := calibrated_amplitude_abs_le ε β hε.le hβ k hk
  have hdr : |δ| ≤ r := hd.trans hεr
  have hbounds (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      |fairRoot t δ u-2/5|+|deriv (fairRoot t δ) u| ≤ B*δ^2 :=
    (hf t δ u ht (hdr.trans hra) hu).2.2.2.2.2.2.2.2.1
  have hp : ∀ w : Covariate, |fairRoot t δ (cellCoord k w)-2/5| ≤ 1/100 := by
    intro w
    have hb := hbounds _ (cellCoord_mem_unit k hk w)
    have hsquare : δ^2 ≤ r^2 := by nlinarith [sq_abs δ, abs_nonneg δ]
    have hh := mul_le_mul_of_nonneg_left hsquare hB.le
    nlinarith [abs_nonneg (deriv (fairRoot t δ) (cellCoord k w))]
  have hdiff : ∀ u ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (fairRoot t δ) u := by
    intro u hu
    have hc := hsm ![t,δ,u] (by exact ⟨ht,hdr.trans hrs,hu⟩)
    have hm : ContDiffAt ℝ ∞ (fun v : ℝ => ![t,δ,v]) u := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i
      · change ContDiffAt ℝ ∞ (fun _ : ℝ => t) u
        fun_prop
      · change ContDiffAt ℝ ∞ (fun _ : ℝ => δ) u
        fun_prop
      · change ContDiffAt ℝ ∞ (fun v : ℝ => v) u
        fun_prop
    exact (hc.comp u hm).differentiableAt (by simp)
  have hb : ∀ u ∈ Set.Icc (0 : ℝ) 1, |deriv (fairRoot t δ) u| ≤ B*δ^2 := by
    intro u hu
    linarith [hbounds u hu, abs_nonneg (fairRoot t δ u-2/5)]
  have hl := fairCells_prognosis_linear_of_centering b k hk σ t δ B hB.le
    (hdr.trans hrsmall) hp hdiff hb x z
  have hsq : δ^2 ≤ r*|δ| := by nlinarith [sq_abs δ,abs_nonneg δ]
  have hcoef : 6*(B*δ^2+4*|δ|) ≤ 25*|δ| := by
    nlinarith [mul_le_mul_of_nonneg_left hsq hB.le]
  have heps : 25*ε ≤ 1 := by linarith [hεr.trans hrsmall]
  have hδpos : 0 ≤ δ := by dsimp [δ]; positivity
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hrate : (k : ℝ)^(1-β) = (k : ℝ)^(-β)*(k : ℝ) := by
    rw [show 1-β = -β+1 by ring,Real.rpow_add hkpos,Real.rpow_one]
  calc
    _ ≤ 6*(B*δ^2+4*|δ|)*(k : ℝ)*|(x : ℝ)-(z : ℝ)| := hl
    _ ≤ 25*|δ| *(k : ℝ)*|(x : ℝ)-(z : ℝ)| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hkpos.le) (abs_nonneg _)
    _ ≤ (k : ℝ)^(1-β)*|(x : ℝ)-(z : ℝ)| := by
      rw [hrate,abs_of_nonneg hδpos]
      dsimp [δ]
      have hh := mul_le_mul_of_nonneg_right heps (Real.rpow_nonneg hkpos.le (-β))
      have hh' := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hh hkpos.le) (abs_nonneg ((x : ℝ)-(z : ℝ)))
      nlinarith [hh']

end CausalSmith.Stat.LogoddsLowsmoothFrontier

module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedPropensityOscillation
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.SpatialLipschitz

/-! # Mixed propensity spatial bounds

Bounded root derivatives and shared endpoint gluing preserve the propensity
amplitude in the global Lipschitz constant.
-/
public section
noncomputable section
open scoped ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Restricting the smooth root to its spatial coordinate preserves the first
Fréchet derivative bound, since the coordinate tangent has norm one. [the documented result](goal) Under [the stated assumptions](hyp:hs,hb). -/
-- @node: mixedRoot_spatial_derivative_bound
lemma mixedRoot_spatial_derivative_bound (η ζ u B : ℝ)
    (hs : ContDiffAt ℝ ⊤ (fun v : Fin 3 → ℝ => mixedRoot (v 0) (v 1) (v 2)) ![η,ζ,u])
    (hb : ‖iteratedFDeriv ℝ 1 (fun v : Fin 3 → ℝ => mixedRoot (v 0) (v 1) (v 2)) ![η,ζ,u]‖ ≤ B) :
    DifferentiableAt ℝ (mixedRoot η ζ) u ∧ |deriv (mixedRoot η ζ) u| ≤ B := by
  have hl : HasDerivAt (fun w : ℝ => ![η,ζ,w]) (Pi.single 2 1) u := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i <;> simp
    · exact hasDerivAt_const u η
    · exact hasDerivAt_const u ζ
    · exact hasDerivAt_id u
  have hd := (hs.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt u hl
  change HasDerivAt (mixedRoot η ζ) _ u at hd
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.deriv, ← Real.norm_eq_abs]
  calc
    _ ≤ ‖fderiv ℝ (fun v : Fin 3 → ℝ => mixedRoot (v 0) (v 1) (v 2)) ![η,ζ,u]‖ *
        ‖(Pi.single 2 (1 : ℝ) : Fin 3 → ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ B := by simpa only [Pi.norm_single, norm_one, mul_one, norm_iteratedFDeriv_one] using hb

/-- Equal endpoint roots and the derivative bound give a global spatial
Lipschitz estimate without requiring matching endpoint derivatives. [the documented result](goal) Under [the stated assumptions](hyp:hd,hb,x). Under [the stated assumptions](hyp:hk). -/
-- @node: mixedRoot_spatial_lipschitz
lemma mixedRoot_spatial_lipschitz (k : ℕ) (hk : 1 ≤ k) (η ζ B : ℝ)
    (hd : ∀ u ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (mixedRoot η ζ) u)
    (hb : ∀ u ∈ Set.Icc (0 : ℝ) 1, |deriv (mixedRoot η ζ) u| ≤ B)
    (x z : Covariate) :
    |mixedRoot η ζ (cellCoord k x)-mixedRoot η ζ (cellCoord k z)| ≤
      B*(k : ℝ)*|(x : ℝ)-(z : ℝ)| := by
  apply cellCoord_comp_lipschitz k hk _ B _ (mixedRoot_endpoints η ζ).symm
  intro u hu v hv
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le hd
      (by simpa only [Real.norm_eq_abs] using hb) hv hu

/-- [The bounded root times the sign field has Lipschitz constant at most
five plus twice the root derivative bound, multiplied by rank. [the documented result](goal) Under [the stated assumptions](hyp:hB,hd,hb,x). Under [the stated assumptions](hyp:hk). -/
-- @node: mixedRoot_signField_lipschitz
lemma mixedRoot_signField_lipschitz (k : ℕ) (hk : 1 ≤ k)
    (σ : Fin (k+1) → Bool) (η ζ B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ u ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (mixedRoot η ζ) u)
    (hb : ∀ u ∈ Set.Icc (0 : ℝ) 1, |deriv (mixedRoot η ζ) u| ≤ B)
    (x z : Covariate) :
    |mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x-
      mixedRoot η ζ (cellCoord k z)*signFieldZ k σ z| ≤
      (5+2*B)*(k : ℝ)*|(x : ℝ)-(z : ℝ)| := by
  have hr := mixedRoot_spatial_lipschitz k hk η ζ B hd hb x z
  have hs := signFieldZ_lipschitz k hk σ x z
  have hq := mixedRoot_mem_bracket η ζ (cellCoord k x)
  have hqa : |mixedRoot η ζ (cellCoord k x)| ≤ 5/4 := by
    rw [abs_of_pos (by linarith [hq.1])]; exact hq.2.le
  have hsz := signFieldZ_abs_le_two k σ z
  calc
    _ = |mixedRoot η ζ (cellCoord k x)*(signFieldZ k σ x-signFieldZ k σ z)+
        (mixedRoot η ζ (cellCoord k x)-mixedRoot η ζ (cellCoord k z))*signFieldZ k σ z| := by congr 1; ring
    _ ≤ |mixedRoot η ζ (cellCoord k x)*(signFieldZ k σ x-signFieldZ k σ z)|+
        |(mixedRoot η ζ (cellCoord k x)-mixedRoot η ζ (cellCoord k z))*signFieldZ k σ z| := abs_add_le _ _
    _ ≤ (5/4)*(4*(k : ℝ)*|(x : ℝ)-(z : ℝ)|)+
        (B*(k : ℝ)*|(x : ℝ)-(z : ℝ)|)*2 := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul hqa hs (abs_nonneg _) (by norm_num))
        (mul_le_mul hr hsz (abs_nonneg _) (by positivity))
    _ = _ := by ring

/-- [Interior logits transfer the margin's amplitude-preserving spatial bound
to the actual mixed law; the totalization fallback is constant. [the documented result](goal) Under [the stated assumptions](hyp:hB,hη,hζ,hd,hb,x). Under [the stated assumptions](hyp:hk). -/
-- @node: mixedCells_propensity_linear_of_root
lemma mixedCells_propensity_linear_of_root (b : Bool) (k : ℕ) (hk : 1 ≤ k)
    (σ : Fin (k+1) → Bool) (η ζ B : ℝ) (hB : 0 ≤ B)
    (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100)
    (hd : ∀ u ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (mixedRoot η ζ) u)
    (hb : ∀ u ∈ Set.Icc (0 : ℝ) 1, |deriv (mixedRoot η ζ) u| ≤ B)
    (x z : Covariate) :
    |propensityLogit (mixedLaw b k σ η ζ) x-propensityLogit (mixedLaw b k σ η ζ) z| ≤
      6*|η| *(5+2*B)*(k : ℝ)*|(x : ℝ)-(z : ℝ)| := by
  classical
  by_cases hv : ValidCells (mixedCells b k σ η ζ)
  · have hi (w : Covariate) := abs_le.mp (mixed_margin_bounds b k σ η ζ w hη hζ).1
    change |logit (propensity _ x)-logit (propensity _ z)| ≤ _
    rw [mixedCells_propensity_eq b k σ η ζ hv x, mixedCells_propensity_eq b k σ η ζ hv z]
    have hl := calibrated_logit_difference_le
      (if b then 1/2-η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x else 1/2+η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x)
      (if b then 1/2-η*mixedRoot η ζ (cellCoord k z)*signFieldZ k σ z else 1/2+η*mixedRoot η ζ (cellCoord k z)*signFieldZ k σ z)
      ⟨by linarith [(hi x).1], by linarith [(hi x).2]⟩
      ⟨by linarith [(hi z).1], by linarith [(hi z).2]⟩
    have hp := mul_le_mul_of_nonneg_left
      (mixedRoot_signField_lipschitz k hk σ η ζ B hB hd hb x z) (abs_nonneg η)
    have he : |(if b then 1/2-η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x else 1/2+η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x)-
        (if b then 1/2-η*mixedRoot η ζ (cellCoord k z)*signFieldZ k σ z else 1/2+η*mixedRoot η ζ (cellCoord k z)*signFieldZ k σ z)| =
        |η| *|mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x-mixedRoot η ζ (cellCoord k z)*signFieldZ k σ z| := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [show 1/2+η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x-(1/2+η*mixedRoot η ζ (cellCoord k z)*signFieldZ k σ z) = η*(mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x-mixedRoot η ζ (cellCoord k z)*signFieldZ k σ z) by ring, abs_mul]
      · rw [show 1/2-η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x-(1/2-η*mixedRoot η ζ (cellCoord k z)*signFieldZ k σ z) = -η*(mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x-mixedRoot η ζ (cellCoord k z)*signFieldZ k σ z) by ring, abs_mul, abs_neg]
    rw [he] at hl
    nlinarith
  · have hz : ∀ w, propensityLogit (mixedLaw b k σ η ζ) w = 0 := by
      intro w
      norm_num [propensityLogit, propensity, mixedLaw, totalCellLaw, hv, lawFromCells, logit]
    rw [hz x, hz z, sub_self, abs_zero]
    positivity

/-- A fixed positive radius makes the mixed propensity Lipschitz constant fit the prescribed scale for every nonnegative exponent pair and every rank. the documented result Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: mixedCells_uniform_propensity_linear
lemma mixedCells_uniform_propensity_linear : ∃ r : ℝ, 0 < r ∧ r ≤ 1/100 ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
      ∀ k : ℕ, 1 ≤ k → ∀ σ : Fin (k+1) → Bool, ∀ b x z,
        |propensityLogit (mixedLaw b k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))) x-
          propensityLogit (mixedLaw b k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))) z| ≤
          (k : ℝ)^(1-α)*|(x : ℝ)-(z : ℝ)| := by
  obtain ⟨a, ha, hs, hbounds⟩ := mixedRoot_uniform_smooth_derivative_bounds
  obtain ⟨B,hB,hb⟩ := hbounds 1
  let r := min a (min (1/100) (1/(6*(5+2*B))))
  have hr : 0 < r := lt_min ha (lt_min (by norm_num) (by positivity))
  have hra : r ≤ a := min_le_left _ _
  have hrsmall : r ≤ 1/100 := (min_le_right _ _).trans (min_le_left _ _)
  have hrcoef : 6*(5+2*B)*r ≤ 1 := by
    have hh : r ≤ 1/(6*(5+2*B)) := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (show 0 < 6*(5+2*B) by positivity)).mp hh
    nlinarith
  refine ⟨r,hr,hrsmall,?_⟩
  intro ε hε hεr α β hα hβ k hk σ b x z
  let η := ε*(k : ℝ)^(-α)
  let ζ := ε*(k : ℝ)^(-β)
  have hη : |η| ≤ r := (calibrated_amplitude_abs_le ε α hε.le hα k hk).trans hεr
  have hζ : |ζ| ≤ r := (calibrated_amplitude_abs_le ε β hε.le hβ k hk).trans hεr
  have hroot (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :=
    mixedRoot_spatial_derivative_bound η ζ u B
      (hs ![η,ζ,u] (hη.trans hra) (hζ.trans hra) hu)
      (hb ![η,ζ,u] (hη.trans hra) (hζ.trans hra) hu)
  have hl := mixedCells_propensity_linear_of_root b k hk σ η ζ B hB.le
    (hη.trans hrsmall) (hζ.trans hrsmall) (fun u hu => (hroot u hu).1)
    (fun u hu => (hroot u hu).2) x z
  have heps : 6*(5+2*B)*ε ≤ 1 :=
    (mul_le_mul_of_nonneg_left hεr (by positivity)).trans hrcoef
  have hηpos : 0 ≤ η := by dsimp [η]; positivity
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hrate : (k : ℝ)^(1-α) = (k : ℝ)^(-α)*(k : ℝ) := by
    rw [show 1-α = -α+1 by ring,Real.rpow_add hkpos,Real.rpow_one]
  calc
    _ ≤ 6*|η| *(5+2*B)*(k : ℝ)*|(x : ℝ)-(z : ℝ)| := hl
    _ ≤ (k : ℝ)^(1-α)*|(x : ℝ)-(z : ℝ)| := by
      rw [hrate,abs_of_nonneg hηpos]
      dsimp [η]
      have hh := mul_le_mul_of_nonneg_right heps (Real.rpow_nonneg hkpos.le (-α))
      have hh' := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hh hkpos.le) (abs_nonneg ((x : ℝ)-(z : ℝ)))
      nlinarith [hh']

end CausalSmith.Stat.LogoddsLowsmoothFrontier

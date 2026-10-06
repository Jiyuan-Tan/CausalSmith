module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.TStrictEnlargement
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Identification
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ScaledProductBump
public import Causalean.Mathlib.InformationTheory.CommonStatisticBernoulli
public import Causalean.Stat.Minimax.LeCamTwoPoint
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! # Bounded radial Bernoulli two-point experiment -/
public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory

/-- One coordinate factor of the explicit bump is Mathlib's standard smooth
flat function composed with `1 - x²`. [For the stated inputs and conditions](hyp:x), [the asserted conclusion holds](goal). -/
lemma smoothBump_factor_eq_expNegInvGlue (x : ℝ) :
    (if |x| < 1 then Real.exp (1 - 1 / (1 - x ^ 2)) else 0) =
      Real.exp 1 * expNegInvGlue (1 - x ^ 2) := by
  by_cases hx : |x| < 1
  · have hden : 0 < 1 - x ^ 2 := by
      rw [sub_pos, sq_lt_one_iff_abs_lt_one]
      exact hx
    rw [if_pos hx]
    simp only [expNegInvGlue, if_neg (not_le.mpr hden)]
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  · have hden : 1 - x ^ 2 ≤ 0 := by
      rw [sub_nonpos]
      simpa using (sq_le_sq₀ (by norm_num) (abs_nonneg x)).2 (le_of_not_gt hx)
    rw [if_neg hx, expNegInvGlue.zero_of_nonpos hden, mul_zero]

/-- The explicit finite product bump is infinitely differentiable. [For the stated inputs and conditions](hyp:d), [the asserted conclusion holds](goal). -/
lemma smoothBump_contDiff {d : ℕ} :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Fin d → ℝ => smoothBump z) := by
  have hfactor : ∀ i : Fin d, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Fin d → ℝ =>
      Real.exp 1 * expNegInvGlue (1 - (z i) ^ 2)) := by
    intro i
    have hinner : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : Fin d → ℝ => 1 - (z i) ^ 2) := by
      fun_prop
    exact contDiff_const.mul (expNegInvGlue.contDiff.comp hinner)
  have hprod : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Fin d → ℝ =>
      ∏ i : Fin d, Real.exp 1 * expNegInvGlue (1 - (z i) ^ 2)) := by
    fun_prop (disch := assumption)
  simpa only [smoothBump, smoothBump_factor_eq_expNegInvGlue] using hprod

/-- The product bump is a valid unit-scale Bernoulli perturbation. [For the stated inputs and conditions](hyp:d,z), [the asserted conclusion holds](goal). -/
lemma smoothBump_mem_Icc {d : ℕ} (z : Fin d → ℝ) :
    smoothBump z ∈ Set.Icc 0 1 := by
  unfold smoothBump
  let f : Fin d → ℝ := fun i =>
    if |z i| < 1 then Real.exp (1 - 1 / (1 - (z i) ^ 2)) else 0
  have hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1 := by
    intro i
    dsimp [f]
    split_ifs with hi
    · have hsq : 0 ≤ (z i) ^ 2 ∧ (z i) ^ 2 < 1 := by
        constructor
        · positivity
        · exact (sq_lt_one_iff_abs_lt_one _).2 hi
      have hden : 0 < 1 - (z i) ^ 2 := by linarith
      have hden_le : 1 - (z i) ^ 2 ≤ 1 := by linarith
      have hrecip : 1 ≤ 1 / (1 - (z i) ^ 2) :=
        (le_div_iff₀ hden).2 (by linarith)
      exact ⟨Real.exp_nonneg _, (Real.exp_le_one_iff).2 (by linarith)⟩
    · exact ⟨le_refl 0, zero_le_one⟩
  constructor
  · exact Finset.prod_nonneg (by intro i hi; exact (hf i).1)
  · exact Finset.prod_le_one (by intro i hi; exact (hf i).1)
      (by intro i hi; exact (hf i).2)

/-- A perturbation below the baseline keeps both response kernels Bernoulli. [For the stated inputs and conditions](hyp:d,j,x₀,β,B,L,a,h,hB,hL,hβ,ha,hh,x), [the asserted conclusion holds](goal). -/
lemma pairSuccess_mem_Icc_of_small {d : ℕ} (j : Bool)
    (x₀ : Fin d → ℝ) (β B L a h : ℝ)
    (hB : 0 < B) (hL : 0 < L) (hβ : 0 < β)
    (ha : 0 ≤ a ∧ a ≤ baselineSuccess B L)
    (hh : 0 ≤ h ∧ h ≤ 1) (x : Fin d → ℝ) :
    pairSuccess j x₀ β B L a h x ∈ Set.Icc 0 1 := by
  have hbase : 0 ≤ baselineSuccess B L ∧ baselineSuccess B L ≤ 1 / 4 := by
    unfold baselineSuccess
    constructor
    · apply le_min (by norm_num)
      positivity
    · exact min_le_left _ _
  have hbump := smoothBump_mem_Icc (fun i => (x i - x₀ i) / h)
  have hpow : 0 ≤ h ^ β ∧ h ^ β ≤ 1 :=
    ⟨Real.rpow_nonneg hh.1 _, Real.rpow_le_one hh.1 hh.2 hβ.le⟩
  unfold pairSuccess
  split_ifs
  · constructor
    · exact add_nonneg hbase.1 (mul_nonneg (mul_nonneg ha.1 hpow.1) hbump.1)
    · have hprod : a * h ^ β * smoothBump (fun i => (x i - x₀ i) / h) ≤ a := by
        calc
          a * h ^ β * smoothBump (fun i => (x i - x₀ i) / h) ≤
              a * 1 * smoothBump (fun i => (x i - x₀ i) / h) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow.2 ha.1) hbump.1
          _ ≤ a * 1 * 1 := mul_le_mul_of_nonneg_left hbump.2 (by simpa using ha.1)
          _ = a := by ring
      have hbase_le : baselineSuccess B L ≤ 1 / 4 := hbase.2
      linarith
  · simpa using (show baselineSuccess B L ∈ Set.Icc (0 : ℝ) 1 from
      ⟨hbase.1, hbase.2.trans (by norm_num)⟩)

/-- The radial CDF formula gives a valid treatment probability at every point. [For the stated inputs and conditions](hyp:d,x₀,x,γ,hγ), [the asserted conclusion holds](goal). -/
lemma radialPropensity_mem_Icc {d : ℕ} (x₀ x : Fin d → ℝ)
    (γ : ℝ) (hγ : 1 < γ) :
    radialPropensity x₀ γ x ∈ Set.Icc 0 1 := by
  have hfactor : ∀ i : Fin d, 0 ≤
      max 0 (min 1 (x₀ i + ‖x - x₀‖) - max 0 (x₀ i - ‖x - x₀‖)) ∧
      max 0 (min 1 (x₀ i + ‖x - x₀‖) - max 0 (x₀ i - ‖x - x₀‖)) ≤ 1 := by
    intro i
    constructor
    · exact le_max_left _ _
    · apply max_le (by norm_num)
      have hmin := min_le_left (1 : ℝ) (x₀ i + ‖x - x₀‖)
      have hmax := le_max_left (0 : ℝ) (x₀ i - ‖x - x₀‖)
      linarith
  have hbase : 0 ≤ radialCDF x₀ ‖x - x₀‖ ∧
      radialCDF x₀ ‖x - x₀‖ ≤ 1 := by
    unfold radialCDF
    exact ⟨Finset.prod_nonneg (by intro i hi; exact (hfactor i).1),
      Finset.prod_le_one (by intro i hi; exact (hfactor i).1)
        (by intro i hi; exact (hfactor i).2)⟩
  unfold radialPropensity
  constructor
  · exact Real.rpow_nonneg hbase.1 _
  · exact Real.rpow_le_one hbase.1 hbase.2 (by positivity)

/-- The truncated radial CDF is bounded by the volume of a full cube of
radius `r`, including when the centre is on the boundary. [For the stated inputs and conditions](hyp:d,x₀,r,hr), [the asserted conclusion holds](goal). -/
lemma radialCDF_le_cube_radius_volume {d : ℕ} (x₀ : Fin d → ℝ)
    (r : ℝ) (hr : 0 ≤ r) : radialCDF x₀ r ≤ (2 * r) ^ d := by
  unfold radialCDF
  calc
    (∏ i : Fin d, max 0 (min 1 (x₀ i + r) - max 0 (x₀ i - r))) ≤
        ∏ _i : Fin d, (2 * r) := by
      apply Finset.prod_le_prod
      · intro i _
        exact le_max_left _ _
      · intro i _
        have hlo : x₀ i - r ≤ max 0 (x₀ i - r) := le_max_right _ _
        have hhi : min 1 (x₀ i + r) ≤ x₀ i + r := min_le_right _ _
        exact max_le (by linarith) (by linarith)
    _ = (2 * r) ^ d := by simp

/-- The radial propensity is at most the full-cube radius power. [For the stated inputs and conditions](hyp:d,x₀,x,γ,hγ), [the asserted conclusion holds](goal). -/
lemma radialPropensity_le_cube_radius_power {d : ℕ} (x₀ x : Fin d → ℝ)
    (γ : ℝ) (hγ : 1 < γ) :
    radialPropensity x₀ γ x ≤
      ((2 * ‖x - x₀‖) ^ d) ^ ((1 : ℝ) / (γ - 1)) := by
  unfold radialPropensity
  apply Real.rpow_le_rpow
  · unfold radialCDF
    exact Finset.prod_nonneg (by intro i _; exact le_max_left _ _)
  · exact radialCDF_le_cube_radius_volume x₀ _ (norm_nonneg _)
  · positivity

/-- A uniform propensity bound on a radius-`h` neighbourhood of the bump. [For the stated inputs and conditions](hyp:d,x₀,x,γ,h,hγ,hr), [the asserted conclusion holds](goal). -/
lemma radialPropensity_le_on_radius {d : ℕ} (x₀ x : Fin d → ℝ)
    (γ h : ℝ) (hγ : 1 < γ)
    (hr : ‖x - x₀‖ ≤ h) :
    radialPropensity x₀ γ x ≤
      ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) := by
  calc
    radialPropensity x₀ γ x ≤
        ((2 * ‖x - x₀‖) ^ d) ^ ((1 : ℝ) / (γ - 1)) :=
      radialPropensity_le_cube_radius_power x₀ x γ hγ
    _ ≤ ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) := by
      apply Real.rpow_le_rpow (pow_nonneg (by positivity) _)
      · exact pow_le_pow_left₀ (by positivity) (by linarith) _
      · positivity

/-- Restricted volume on the unit cube is a probability measure. [For the stated inputs and conditions](hyp:d), [the asserted conclusion holds](goal). -/
lemma uniformCube_probability_lowerPair (d : ℕ) :
    IsProbabilityMeasure (volume.restrict (cube d)) := by
  apply isProbabilityMeasure_iff.mpr
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hcube : cube d =
      Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
    ext x
    simp [cube, Set.mem_Icc, Pi.le_def]
  rw [hcube, Real.volume_Icc_pi]
  simp

/-- The uniform-cube mass of a sup-norm ball is the displayed truncated radial
CDF. [For the stated inputs and conditions](hyp:d,x₀,hx₀,r,hr), [the asserted conclusion holds](goal). -/
lemma uniformCube_radius_sublevel_real {d : ℕ} (x₀ : Fin d → ℝ)
    (hx₀ : x₀ ∈ cube d) (r : ℝ) (hr : 0 ≤ r) :
    (volume.restrict (cube d)).real {x | ‖x - x₀‖ ≤ r} = radialCDF x₀ r := by
  have hset : {x | ‖x - x₀‖ ≤ r} ∩ cube d =
      Set.Icc (fun i => max 0 (x₀ i - r)) (fun i => min 1 (x₀ i + r)) := by
    ext x
    simp only [cube, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_pi,
      Set.mem_univ, forall_const, Set.mem_Icc, Pi.le_def]
    constructor
    · rintro ⟨hnorm, hx⟩
      have hcoord := (pi_norm_le_iff_of_nonneg hr).1 hnorm
      constructor <;> intro i
      · exact max_le (hx i).1 (by
          have := hcoord i
          rw [Pi.sub_apply, Real.norm_eq_abs] at this
          linarith [(abs_le.mp this).1])
      · exact le_min (hx i).2 (by
          have := hcoord i
          rw [Pi.sub_apply, Real.norm_eq_abs] at this
          linarith [(abs_le.mp this).2])
    · rintro ⟨hlo, hhi⟩
      constructor
      · apply (pi_norm_le_iff_of_nonneg hr).2
        intro i
        rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
        constructor
        · linarith [le_max_right (0 : ℝ) (x₀ i - r), hlo i]
        · linarith [hhi i, min_le_right (1 : ℝ) (x₀ i + r)]
      · intro i
        exact ⟨(le_max_left _ _).trans (hlo i),
          (hhi i).trans (min_le_left _ _)⟩
  rw [measureReal_def, Measure.restrict_apply (by measurability), hset,
    Real.volume_Icc_pi_toReal]
  · simp only [radialCDF]
    apply Finset.prod_congr rfl
    intro i _
    have hx := hx₀ i (Set.mem_univ i)
    change 0 ≤ x₀ i ∧ x₀ i ≤ 1 at hx
    have hdiff : 0 ≤ min 1 (x₀ i + r) - max 0 (x₀ i - r) := sub_nonneg.mpr (by
      show max (0 : ℝ) (x₀ i - r) ≤ min 1 (x₀ i + r)
      apply max_le
      · exact le_min (by norm_num) (by linarith)
      · exact le_min (by linarith) (by linarith))
    exact (max_eq_right hdiff).symm
  · intro i
    have hx := hx₀ i (Set.mem_univ i)
    change 0 ≤ x₀ i ∧ x₀ i ≤ 1 at hx
    apply max_le
    · exact le_min (by norm_num) (by linarith)
    · exact le_min (by linarith) (by linarith)

/-- [For the stated inputs and conditions](hyp:d,x₀), [the asserted conclusion holds](goal). -/

lemma radialCDF_continuous {d : ℕ} (x₀ : Fin d → ℝ) :
    Continuous (radialCDF x₀) := by
  unfold radialCDF
  fun_prop

/-- [For the stated inputs and conditions](hyp:d,x₀,hx₀,hd), [the asserted conclusion holds](goal). -/

lemma radialCDF_zero_of_positive_dimension {d : ℕ} (x₀ : Fin d → ℝ)
    (hx₀ : x₀ ∈ cube d) (hd : 0 < d) : radialCDF x₀ 0 = 0 := by
  let i : Fin d := ⟨0, hd⟩
  unfold radialCDF
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hx := hx₀ i (Set.mem_univ i)
  change 0 ≤ x₀ i ∧ x₀ i ≤ 1 at hx
  simp [hx.1, hx.2]

/-- [For the stated inputs and conditions](hyp:d,x₀,hx₀), [the asserted conclusion holds](goal). -/

lemma radialCDF_one {d : ℕ} (x₀ : Fin d → ℝ) (hx₀ : x₀ ∈ cube d) :
    radialCDF x₀ 1 = 1 := by
  unfold radialCDF
  apply Finset.prod_eq_one
  intro i _
  have hx := hx₀ i (Set.mem_univ i)
  change 0 ≤ x₀ i ∧ x₀ i ≤ 1 at hx
  rw [show min 1 (x₀ i + 1) = 1 by exact min_eq_left (by linarith),
    show max 0 (x₀ i - 1) = 0 by exact max_eq_left (by linarith)]
  norm_num

/-- [For the stated inputs and conditions](hyp:d,x₀,hx₀,r,s,hr,hrs), [the asserted conclusion holds](goal). -/

lemma radialCDF_mono_nonneg {d : ℕ} (x₀ : Fin d → ℝ) (hx₀ : x₀ ∈ cube d)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) : radialCDF x₀ r ≤ radialCDF x₀ s := by
  letI := uniformCube_probability_lowerPair d
  have hs : 0 ≤ s := hr.trans hrs
  rw [← uniformCube_radius_sublevel_real x₀ hx₀ r hr,
    ← uniformCube_radius_sublevel_real x₀ hx₀ s hs]
  exact measureReal_mono (fun x hx => hx.trans hrs) (measure_ne_top _ _)

/-- Applying the radial CDF to its own radius variable is stochastically no
smaller than a uniform variable. [For the stated inputs and conditions](hyp:d,x₀,hx₀,hd,s,hs), [the asserted conclusion holds](goal). -/
lemma radialCDF_self_sublevel_mass {d : ℕ} (x₀ : Fin d → ℝ)
    (hx₀ : x₀ ∈ cube d) (hd : 0 < d) (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
    (volume.restrict (cube d)).real
      {x | radialCDF x₀ ‖x - x₀‖ ≤ s} ≤ s := by
  letI := uniformCube_probability_lowerPair d
  by_cases hs1 : s = 1
  · subst s
    exact measureReal_le_one
  have hslt : s < 1 := lt_of_le_of_ne hs.2 hs1
  let S : Set ℝ := {r | 0 ≤ r ∧ radialCDF x₀ r ≤ s}
  have hSnonempty : S.Nonempty := by
    refine ⟨0, le_rfl, ?_⟩
    rw [radialCDF_zero_of_positive_dimension x₀ hx₀ hd]
    exact hs.1
  have hSbdd : BddAbove S := by
    refine ⟨1, ?_⟩
    intro r hr
    by_contra hnot
    have h1r : 1 ≤ r := le_of_not_ge hnot
    have hFr : 1 ≤ radialCDF x₀ r := by
      rw [← radialCDF_one x₀ hx₀]
      exact radialCDF_mono_nonneg x₀ hx₀ zero_le_one h1r
    linarith [hr.2]
  have hSclosed : IsClosed S := by
    exact isClosed_Ici.inter
      (isClosed_Iic.preimage (radialCDF_continuous x₀))
  have hsup : sSup S ∈ S := hSclosed.csSup_mem hSnonempty hSbdd
  calc
    (volume.restrict (cube d)).real
        {x | radialCDF x₀ ‖x - x₀‖ ≤ s} ≤
        (volume.restrict (cube d)).real {x | ‖x - x₀‖ ≤ sSup S} := by
      exact measureReal_mono (fun x hx => le_csSup hSbdd
        ⟨norm_nonneg _, hx⟩) (measure_ne_top _ _)
    _ = radialCDF x₀ (sSup S) :=
      uniformCube_radius_sublevel_real x₀ hx₀ _ hsup.1
    _ ≤ s := hsup.2

/-- [For the stated inputs and conditions](hyp:d,x₀,hx₀,hd,γ,hγ,t,ht), [the asserted conclusion holds](goal). -/

lemma radialPropensity_uniform_tail {d : ℕ} (x₀ : Fin d → ℝ)
    (hx₀ : x₀ ∈ cube d) (hd : 0 < d) (γ : ℝ) (hγ : 1 < γ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (volume.restrict (cube d)).real {x | radialPropensity x₀ γ x ≤ t} ≤
      t ^ (γ - 1) := by
  letI := uniformCube_probability_lowerPair d
  have htPow : t ^ (γ - 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.rpow_nonneg ht.1 _, Real.rpow_le_one ht.1 ht.2 (by linarith)⟩
  calc
    _ ≤ (volume.restrict (cube d)).real
        {x | radialCDF x₀ ‖x - x₀‖ ≤ t ^ (γ - 1)} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro x hx
      have hbase : 0 ≤ radialCDF x₀ ‖x - x₀‖ := by
        rw [← uniformCube_radius_sublevel_real x₀ hx₀ _ (norm_nonneg _)]
        exact measureReal_nonneg
      have hpow := Real.rpow_le_rpow
        (Real.rpow_nonneg hbase ((1 : ℝ) / (γ - 1))) hx (by linarith : 0 ≤ γ - 1)
      simpa [radialPropensity,
        Real.rpow_inv_rpow hbase (by linarith : γ - 1 ≠ 0)] using hpow
    _ ≤ _ := radialCDF_self_sublevel_mass x₀ hx₀ hd _ htPow

/-- [For the stated inputs and conditions](hyp:d,x₀,hx₀,hd,γ,hγ), [the asserted conclusion holds](goal). -/

lemma radialPropensity_uniform_pos_ae {d : ℕ} (x₀ : Fin d → ℝ)
    (hx₀ : x₀ ∈ cube d) (hd : 0 < d) (γ : ℝ) (hγ : 1 < γ) :
    ∀ᵐ x ∂volume.restrict (cube d), 0 < radialPropensity x₀ γ x := by
  letI := uniformCube_probability_lowerPair d
  have htail := radialPropensity_uniform_tail x₀ hx₀ hd γ hγ 0
    (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
  rw [Real.zero_rpow (by linarith : γ - 1 ≠ 0)] at htail
  have hreal : (volume.restrict (cube d)).real
      {x | radialPropensity x₀ γ x = 0} = 0 := by
    apply le_antisymm _ measureReal_nonneg
    exact (measureReal_mono (fun x hx => by
      change radialPropensity x₀ γ x = 0 at hx
      exact hx.le) (measure_ne_top _ _)).trans htail
  have hzero : (volume.restrict (cube d))
      {x | radialPropensity x₀ γ x = 0} = 0 := by
    exact (ENNReal.toReal_eq_zero_iff _).mp hreal |>.resolve_right (measure_ne_top _ _)
  have hne := measure_eq_zero_iff_ae_notMem.mp hzero
  filter_upwards [hne] with x hx
  exact lt_of_le_of_ne (radialPropensity_mem_Icc x₀ x γ hγ).1 (Ne.symm hx)

/-- Fixed positive choices of the bump amplitude and mesh multiplier satisfy
all Bernoulli parameter constraints in the lower-pair construction. [For the stated inputs and conditions](hyp:d,β,B,L,γ,a,c,x₀,hd,hβ,hB,hL,hγ,ha,hc), [the asserted conclusion holds](goal). -/
lemma boundedLowerPairAdmissible_of_small (d : ℕ) (β B L γ a c : ℝ)
    (x₀ : Fin d → ℝ) (hd : 0 < d) (hβ : 1 < β) (hB : 0 < B)
    (hL : 0 < L) (hγ : 1 < γ)
    (ha : 0 < a ∧ a ≤ baselineSuccess B L)
    (hc : 0 < c ∧ c ≤ 1) :
    boundedLowerPairAdmissible d β B L γ a c x₀ := by
  refine ⟨ha.1, hc.1, ?_⟩
  intro n hn x hx
  have hmesh := oracleMesh_mem_Ioc d n β γ
    ⟨Nat.succ_le_iff.mpr hd, hn, hβ, hγ⟩
  have hwidth : 0 ≤ c * oracleMesh d n β γ ∧
      c * oracleMesh d n β γ ≤ 1 := by
    constructor
    · exact mul_nonneg hc.1.le hmesh.1.le
    · calc
        c * oracleMesh d n β γ ≤ 1 * oracleMesh d n β γ :=
          mul_le_mul_of_nonneg_right hc.2 hmesh.1.le
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hmesh.2 (by norm_num)
        _ = 1 := by ring
  refine ⟨radialPropensity_mem_Icc x₀ x γ hγ, ?_, ?_⟩
  · exact pairSuccess_mem_Icc_of_small false x₀ β B L a
      (c * oracleMesh d n β γ) hB hL (by linarith)
      ⟨ha.1.le, ha.2⟩ hwidth x
  · exact pairSuccess_mem_Icc_of_small true x₀ β B L a
      (c * oracleMesh d n β γ) hB hL (by linarith)
      ⟨ha.1.le, ha.2⟩ hwidth x

/-- Both testing responses retain the positive baseline success probability. [For the stated inputs and conditions](hyp:d,j,x₀,x,β,B,L,a,h,ha,hh), [the asserted conclusion holds](goal). -/
lemma pairSuccess_baseline_le {d : ℕ} (j : Bool) (x₀ x : Fin d → ℝ)
    (β B L a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) :
    baselineSuccess B L ≤ pairSuccess j x₀ β B L a h x := by
  have hbump := (smoothBump_mem_Icc (fun i => (x i - x₀ i) / h)).1
  unfold pairSuccess
  split_ifs
  · exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg ha (Real.rpow_nonneg hh _)) hbump)
  · simp

/-- The perturbed testing response remains within twice its baseline. [For the stated inputs and conditions](hyp:d,j,x₀,x,β,B,L,a,h,ha,hh,hβ), [the asserted conclusion holds](goal). -/
lemma pairSuccess_le_twice_baseline {d : ℕ} (j : Bool)
    (x₀ x : Fin d → ℝ) (β B L a h : ℝ)
    (ha : 0 ≤ a ∧ a ≤ baselineSuccess B L)
    (hh : 0 ≤ h ∧ h ≤ 1) (hβ : 0 ≤ β) :
    pairSuccess j x₀ β B L a h x ≤ 2 * baselineSuccess B L := by
  have hbump := (smoothBump_mem_Icc (fun i => (x i - x₀ i) / h)).2
  have hpow : 0 ≤ h ^ β ∧ h ^ β ≤ 1 :=
    ⟨Real.rpow_nonneg hh.1 _, Real.rpow_le_one hh.1 hh.2 hβ⟩
  have hperturb : a * h ^ β * smoothBump (fun i => (x i - x₀ i) / h) ≤ a := by
    calc
      _ ≤ a * h ^ β * 1 :=
        mul_le_mul_of_nonneg_left hbump (mul_nonneg ha.1 hpow.1)
      _ ≤ a * 1 := by simpa using mul_le_mul_of_nonneg_left hpow.2 ha.1
      _ = a := by ring
  unfold pairSuccess
  split_ifs <;> nlinarith

/-- Both Bernoulli response parameters stay strictly inside the unit interval,
so their two-point response laws have common support. [For the stated inputs and conditions](hyp:d,j,x₀,x,β,B,L,a,h,hB,hL,ha,hh,hβ), [the asserted conclusion holds](goal). -/
lemma pairSuccess_mem_Ioo_of_small {d : ℕ} (j : Bool)
    (x₀ x : Fin d → ℝ) (β B L a h : ℝ)
    (hB : 0 < B) (hL : 0 < L)
    (ha : 0 ≤ a ∧ a ≤ baselineSuccess B L)
    (hh : 0 ≤ h ∧ h ≤ 1) (hβ : 0 ≤ β) :
    pairSuccess j x₀ β B L a h x ∈ Set.Ioo 0 1 := by
  have hbase : 0 < baselineSuccess B L ∧ baselineSuccess B L ≤ 1 / 4 := by
    unfold baselineSuccess
    exact ⟨lt_min (by norm_num) (by positivity), min_le_left _ _⟩
  have hlower := pairSuccess_baseline_le j x₀ x β B L a h ha.1 hh.1
  have hupper := pairSuccess_le_twice_baseline j x₀ x β B L a h ha hh hβ
  exact ⟨lt_of_lt_of_le hbase.1 hlower,
    lt_of_le_of_lt hupper (by linarith [hbase.2])⟩

/-- The product bump has unit height at its centre. [For the stated inputs and conditions](hyp:d), [the asserted conclusion holds](goal). -/
lemma smoothBump_zero (d : ℕ) :
    smoothBump (fun _ : Fin d => (0 : ℝ)) = 1 := by
  simp [smoothBump]

/-- Every nonzero bump value lies inside the unit box in each coordinate. [For the stated inputs and conditions](hyp:d,z,hz,i), [the asserted conclusion holds](goal). -/
lemma smoothBump_support_coordinate {d : ℕ} (z : Fin d → ℝ)
    (hz : smoothBump z ≠ 0) (i : Fin d) : |z i| < 1 := by
  by_contra hi
  apply hz
  unfold smoothBump
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi]

/-- A scaled nonzero bump is confined to the radius-`h` test cube. [For the stated inputs and conditions](hyp:d,x₀,x,h,hh,hb), [the asserted conclusion holds](goal). -/
lemma smoothBump_scaled_support {d : ℕ} (x₀ x : Fin d → ℝ)
    (h : ℝ) (hh : 0 < h)
    (hb : smoothBump (fun i => (x i - x₀ i) / h) ≠ 0) :
    ∀ i : Fin d, |x i - x₀ i| < h := by
  intro i
  have hi := smoothBump_support_coordinate _ hb i
  rw [abs_div, abs_of_pos hh] at hi
  simpa using (div_lt_iff₀ hh).mp hi

/-- A nonzero scaled bump lies in the closed sup-norm radius-`h` cube. [For the stated inputs and conditions](hyp:d,x₀,x,h,hh,hb), [the asserted conclusion holds](goal). -/
lemma smoothBump_scaled_support_radius {d : ℕ} (x₀ x : Fin d → ℝ)
    (h : ℝ) (hh : 0 < h)
    (hb : smoothBump (fun i => (x i - x₀ i) / h) ≠ 0) :
    ‖x - x₀‖ ≤ h := by
  apply (pi_norm_le_iff_of_nonneg hh.le).2
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    (smoothBump_scaled_support x₀ x h hh hb i).le

/-- On the perturbation support, the treated-design weight has the small
radius factor used in the lower-pair entropy estimate. [For the stated inputs and conditions](hyp:d,x₀,x,γ,h,hγ,hh,hb), [the asserted conclusion holds](goal). -/
lemma radialPropensity_le_on_bump_support {d : ℕ} (x₀ x : Fin d → ℝ)
    (γ h : ℝ) (hγ : 1 < γ) (hh : 0 < h)
    (hb : smoothBump (fun i => (x i - x₀ i) / h) ≠ 0) :
    radialPropensity x₀ γ x ≤
      ((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)) :=
  radialPropensity_le_on_radius x₀ x γ h hγ
    (smoothBump_scaled_support_radius x₀ x h hh hb)

/-- The two treated Bernoulli parameters differ by the full bump amplitude
at the designated test point. [For the stated inputs and conditions](hyp:d,x₀,β,B,L,a,h), [the asserted conclusion holds](goal). -/
lemma pairSuccess_center_gap {d : ℕ} (x₀ : Fin d → ℝ)
    (β B L a h : ℝ) :
    pairSuccess true x₀ β B L a h x₀ -
      pairSuccess false x₀ β B L a h x₀ = a * h ^ β := by
  simp [pairSuccess, smoothBump_zero]

/-- The treated Bernoulli perturbation is nonnegative and bounded by its
nominal amplitude at every covariate point. [For the stated inputs and conditions](hyp:d,x₀,x,β,B,L,a,h,ha,hh), [the asserted conclusion holds](goal). -/
lemma pairSuccess_perturbation_bound {d : ℕ} (x₀ x : Fin d → ℝ)
    (β B L a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) :
    0 ≤ pairSuccess true x₀ β B L a h x -
      pairSuccess false x₀ β B L a h x ∧
    pairSuccess true x₀ β B L a h x -
      pairSuccess false x₀ β B L a h x ≤ a * h ^ β := by
  have hbump := smoothBump_mem_Icc (fun i => (x i - x₀ i) / h)
  have hamp : 0 ≤ a * h ^ β := mul_nonneg ha (Real.rpow_nonneg hh _)
  have hbound :
      0 ≤ a * h ^ β * smoothBump (fun i => (x i - x₀ i) / h) ∧
      a * h ^ β * smoothBump (fun i => (x i - x₀ i) / h) ≤ a * h ^ β :=
    ⟨mul_nonneg hamp hbump.1, by simpa using
      (mul_le_mul_of_nonneg_left hbump.2 hamp)⟩
  simpa [pairSuccess] using hbound

/-- The observed Bernoulli kernels differ only inside the bump cube. [For the stated inputs and conditions](hyp:d,x₀,x,β,B,L,a,h,hh,hdiff), [the asserted conclusion holds](goal). -/
lemma pairSuccess_difference_support {d : ℕ} (x₀ x : Fin d → ℝ)
    (β B L a h : ℝ) (hh : 0 < h)
    (hdiff : pairSuccess true x₀ β B L a h x ≠
      pairSuccess false x₀ β B L a h x) :
    ∀ i : Fin d, |x i - x₀ i| < h := by
  apply smoothBump_scaled_support x₀ x h hh
  intro hb
  apply hdiff
  simp [pairSuccess, hb]

/-- Scaling the bump by the oracle mesh yields the oracle separation scale. [For the stated inputs and conditions](hyp:d,n,x₀,β,B,L,γ,a,c,hc), [the asserted conclusion holds](goal). -/
lemma pairSuccess_oracle_separation {d n : ℕ} (x₀ : Fin d → ℝ)
    (β B L γ a c : ℝ) (hc : 0 ≤ c) :
    pairSuccess true x₀ β B L a (c * oracleMesh d n β γ) x₀ -
      pairSuccess false x₀ β B L a (c * oracleMesh d n β γ) x₀ =
        a * c ^ β * oracleRate d n β γ := by
  have hmesh : 0 ≤ oracleMesh d n β γ := by
    unfold oracleMesh
    exact Real.rpow_nonneg (by exact_mod_cast Nat.zero_le n) _
  rw [pairSuccess_center_gap, oracleRate, Real.mul_rpow hc hmesh]
  ring

/-- Fixed positive construction constants give an admissible Bernoulli pair
and the oracle-scale response-parameter gap at every sample size. [For the stated inputs and conditions](hyp:d,β,B,L,γ,x₀,hd,hβ,hB,hL,hγ), [the asserted conclusion holds](goal). -/
lemma boundedLowerPair_fixed_constants_separation (d : ℕ)
    (β B L γ : ℝ) (x₀ : Fin d → ℝ)
    (hd : 0 < d) (hβ : 1 < β) (hB : 0 < B)
    (hL : 0 < L) (hγ : 1 < γ) :
    ∃ a c c₀ : ℝ, 0 < a ∧ 0 < c ∧ 0 < c₀ ∧
      boundedLowerPairAdmissible d β B L γ a c x₀ ∧
      ∀ n : ℕ, 1 ≤ n →
        c₀ * oracleRate d n β γ =
          B * (pairSuccess true x₀ β B L a
            (c * oracleMesh d n β γ) x₀ -
            pairSuccess false x₀ β B L a
              (c * oracleMesh d n β γ) x₀) := by
  let a := baselineSuccess B L / 2
  let c : ℝ := 1 / 2
  let c₀ := B * a * c ^ β
  have hbase : 0 < baselineSuccess B L := by
    unfold baselineSuccess
    positivity
  have ha : 0 < a ∧ a ≤ baselineSuccess B L := by
    dsimp [a]
    constructor <;> linarith
  have hc : 0 < c ∧ c ≤ 1 := by dsimp [c]; norm_num
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨a, c, c₀, ha.1, hc.1, hc₀,
    boundedLowerPairAdmissible_of_small d β B L γ a c x₀
      hd hβ hB hL hγ ha hc, ?_⟩
  intro n _
  rw [pairSuccess_oracle_separation x₀ β B L γ a c hc.1.le]
  dsimp [c₀]
  ring

/-- The oracle bandwidth cancels the sample-size factor in the pair's KL bound. [For the stated inputs and conditions](hyp:d,n,β,γ,c,hn,hc,hden), [the asserted conclusion holds](goal). -/
lemma lowerPair_oracle_kl_balance (d n : ℕ) (β γ c : ℝ)
    (hn : 0 < n) (hc : 0 ≤ c)
    (hden : 0 < 2 * β + effectiveDimension d γ) :
    (n : ℝ) * (c * oracleMesh d n β γ) ^
        (2 * β + effectiveDimension d γ) =
      c ^ (2 * β + effectiveDimension d γ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmesh : 0 ≤ oracleMesh d n β γ := by
    unfold oracleMesh
    positivity
  have hexp : -(1 : ℝ) / (2 * β + effectiveDimension d γ) *
      (2 * β + effectiveDimension d γ) = -1 := by
    field_simp
  have hpow : (oracleMesh d n β γ) ^
      (2 * β + effectiveDimension d γ) = (n : ℝ)⁻¹ := by
    rw [oracleMesh, ← Real.rpow_mul hn'.le, hexp]
    exact Real.rpow_neg_one (n : ℝ)
  rw [Real.mul_rpow hc hmesh, hpow]
  calc
    _ = c ^ (2 * β + effectiveDimension d γ) * ((n : ℝ) * (n : ℝ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ (ne_of_gt hn'), mul_one]

/-- A fixed bandwidth multiplier makes any finite oracle-scale KL coefficient
small, uniformly in the sample size. [For the stated inputs and conditions](hyp:K,a,D,hK,hD), [the asserted conclusion holds](goal). -/
lemma lowerPair_choose_kl_scale (K a D : ℝ)
    (hK : 0 ≤ K) (hD : 1 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ K * a ^ 2 * c ^ D ≤ 1 / 8 := by
  let c : ℝ := 1 / (8 * (K * a ^ 2 + 1))
  have hden : 0 < 8 * (K * a ^ 2 + 1) := by positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hK (sq_nonneg a)]
  refine ⟨c, hc, hc1, ?_⟩
  have hpow : c ^ D ≤ c := Real.rpow_le_self_of_le_one hc.le hc1 hD
  have hcoef : 0 ≤ K * a ^ 2 := mul_nonneg hK (sq_nonneg a)
  have hsmall : K * a ^ 2 * c ≤ 1 / 8 := by
    dsimp [c]
    calc
      K * a ^ 2 * (1 / (8 * (K * a ^ 2 + 1))) =
          (K * a ^ 2) / (8 * (K * a ^ 2 + 1)) := by ring
      _ ≤ 1 / 8 := (div_le_iff₀ hden).2 (by
        nlinarith [mul_nonneg hK (sq_nonneg a)])
  exact (mul_le_mul_of_nonneg_left hpow hcoef).trans hsmall

/-- Choose admissible testing parameters once, with both the oracle-scale KL
budget and a positive response separation constant. [For the stated inputs and conditions](hyp:d,β,B,L,γ,K,x₀,hd,hβ,hB,hL,hγ,hK), [the asserted conclusion holds](goal). -/
lemma boundedLowerPair_fixed_kl_and_separation_constants (d : ℕ)
    (β B L γ K : ℝ) (x₀ : Fin d → ℝ)
    (hd : 0 < d) (hβ : 1 < β) (hB : 0 < B)
    (hL : 0 < L) (hγ : 1 < γ) (hK : 0 ≤ K) :
    ∃ a c c₀ : ℝ, 0 < a ∧ 0 < c ∧ 0 < c₀ ∧
      boundedLowerPairAdmissible d β B L γ a c x₀ ∧
      K * a ^ 2 * c ^ (2 * β + effectiveDimension d γ) ≤ 1 / 8 ∧
      ∀ n : ℕ, 1 ≤ n →
        c₀ * oracleRate d n β γ =
          B * (pairSuccess true x₀ β B L a
            (c * oracleMesh d n β γ) x₀ -
            pairSuccess false x₀ β B L a
              (c * oracleMesh d n β γ) x₀) := by
  let a := baselineSuccess B L / 2
  have hbase : 0 < baselineSuccess B L := by
    unfold baselineSuccess
    positivity
  have ha : 0 < a ∧ a ≤ baselineSuccess B L := by
    dsimp [a]
    constructor <;> linarith
  have hD : 1 ≤ 2 * β + effectiveDimension d γ := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hγ' : 0 < γ - 1 := by linarith
    have hdim : 0 ≤ effectiveDimension d γ := by
      unfold effectiveDimension
      positivity
    linarith
  obtain ⟨c, hc, hc1, hkl⟩ :=
    lowerPair_choose_kl_scale K a (2 * β + effectiveDimension d γ) hK hD
  let c₀ := B * a * c ^ β
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨a, c, c₀, ha.1, hc, hc₀,
    boundedLowerPairAdmissible_of_small d β B L γ a c x₀
      hd hβ hB hL hγ ha ⟨hc, hc1⟩, hkl, ?_⟩
  intro n _
  rw [pairSuccess_oracle_separation x₀ β B L γ a c hc.le]
  dsimp [c₀]
  ring

/-- The binary relative entropy is bounded by the Pearson quadratic at the
second Bernoulli parameter. [For the stated inputs and conditions](hyp:p,q,hp,hq), [the asserted conclusion holds](goal). -/
lemma lowerPair_bernoulli_kl_le_quadratic (p q : ℝ)
    (hp : p ∈ Set.Ioo 0 1) (hq : q ∈ Set.Ioo 0 1) :
    p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤
      (p - q) ^ 2 / (q * (1 - q)) := by
  have hqpos : 0 < q := hq.1
  have hqcomp : 0 < 1 - q := by linarith [hq.2]
  have hpcomp : 0 < 1 - p := by linarith [hp.2]
  have h₁ := Real.log_le_sub_one_of_pos (div_pos hp.1 hqpos)
  have h₂ := Real.log_le_sub_one_of_pos (div_pos hpcomp hqcomp)
  have h₁' := mul_le_mul_of_nonneg_left h₁ hp.1.le
  have h₂' := mul_le_mul_of_nonneg_left h₂ hpcomp.le
  calc
    p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤
        p * (p / q - 1) + (1 - p) * ((1 - p) / (1 - q) - 1) := add_le_add h₁' h₂'
    _ = (p - q) ^ 2 / (q * (1 - q)) := by
      field_simp
      ring

/-- A common positive Bernoulli baseline makes the KL constant uniform over
the testing pair. [For the stated inputs and conditions](hyp:p,q,δ,hp,hq,hδ,hqlo,hqhi), [the asserted conclusion holds](goal). -/
lemma lowerPair_bernoulli_kl_le_baseline_quadratic (p q δ : ℝ)
    (hp : p ∈ Set.Ioo 0 1) (hq : q ∈ Set.Ioo 0 1)
    (hδ : 0 < δ) (hqlo : δ ≤ q) (hqhi : q ≤ 1 / 2) :
    p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤
      (2 / δ) * (p - q) ^ 2 := by
  have hden : δ / 2 ≤ q * (1 - q) := by nlinarith
  have hdenpos : 0 < q * (1 - q) := mul_pos hq.1 (by linarith [hq.2])
  have hsq : 0 ≤ (p - q) ^ 2 := sq_nonneg _
  calc
    _ ≤ (p - q) ^ 2 / (q * (1 - q)) :=
      lowerPair_bernoulli_kl_le_quadratic p q hp hq
    _ ≤ (p - q) ^ 2 / (δ / 2) := by gcongr
    _ = (2 / δ) * (p - q) ^ 2 := by field_simp

/-- The Bernoulli response kernels in the lower pair satisfy the quadratic
KL estimate uniformly in location and bandwidth. [For the stated inputs and conditions](hyp:d,x₀,x,β,B,L,a,h,hβ,hB,hL,ha,hh), [the asserted conclusion holds](goal). -/
lemma lowerPair_pointwise_kl_bound {d : ℕ} (x₀ x : Fin d → ℝ)
    (β B L a h : ℝ) (hβ : 0 < β) (hB : 0 < B) (hL : 0 < L)
    (ha : 0 ≤ a ∧ a ≤ baselineSuccess B L)
    (hh : 0 ≤ h ∧ h ≤ 1) :
    let p := pairSuccess false x₀ β B L a h x
    let q := pairSuccess true x₀ β B L a h x
    p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤
      (2 / baselineSuccess B L) * (p - q) ^ 2 := by
  dsimp
  have hbase : 0 < baselineSuccess B L ∧ baselineSuccess B L ≤ 1 / 4 := by
    unfold baselineSuccess
    exact ⟨lt_min (by norm_num) (by positivity), min_le_left _ _⟩
  have hp := pairSuccess_mem_Ioo_of_small false x₀ x β B L a h
    hB hL ha hh hβ.le
  have hq := pairSuccess_mem_Ioo_of_small true x₀ x β B L a h
    hB hL ha hh hβ.le
  have hqlo := pairSuccess_baseline_le true x₀ x β B L a h ha.1 hh.1
  have hqhi := pairSuccess_le_twice_baseline true x₀ x β B L a h ha hh hβ.le
  apply lowerPair_bernoulli_kl_le_baseline_quadratic _ _ _ hp hq hbase.1 hqlo
  linarith [hbase.2]

/-- The treated KL integrand has the small propensity factor on the bump
support, and vanishes away from that support. [For the stated inputs and conditions](hyp:d,x₀,x,β,B,L,γ,a,h,hβ,hB,hL,hγ,ha,hh), [the asserted conclusion holds](goal). -/
lemma lowerPair_weighted_pointwise_kl_bound {d : ℕ}
    (x₀ x : Fin d → ℝ) (β B L γ a h : ℝ)
    (hβ : 0 < β) (hB : 0 < B) (hL : 0 < L) (hγ : 1 < γ)
    (ha : 0 ≤ a ∧ a ≤ baselineSuccess B L)
    (hh : 0 < h ∧ h ≤ 1) :
    let p := pairSuccess false x₀ β B L a h x
    let q := pairSuccess true x₀ β B L a h x
    radialPropensity x₀ γ x *
        (p * Real.log (p / q) +
          (1 - p) * Real.log ((1 - p) / (1 - q))) ≤
      (2 / baselineSuccess B L) * (a * h ^ β) ^ 2 *
        (((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1))) := by
  dsimp
  have hbase : 0 ≤ 2 / baselineSuccess B L := by
    unfold baselineSuccess
    positivity
  have hprop : 0 ≤ radialPropensity x₀ γ x :=
    (radialPropensity_mem_Icc x₀ x γ hγ).1
  by_cases hb : smoothBump (fun i => (x i - x₀ i) / h) = 0
  · simp [pairSuccess, hb]
    exact mul_nonneg (mul_nonneg hbase (sq_nonneg _))
      (Real.rpow_nonneg (pow_nonneg (mul_nonneg (by norm_num) hh.1.le) _) _)
  · have hbound := lowerPair_pointwise_kl_bound x₀ x β B L a h
        hβ hB hL ha ⟨hh.1.le, hh.2⟩
    dsimp at hbound
    have hgap := pairSuccess_perturbation_bound x₀ x β B L a h
      ha.1 hh.1.le
    have hgap' : (pairSuccess false x₀ β B L a h x -
        pairSuccess true x₀ β B L a h x) ^ 2 ≤ (a * h ^ β) ^ 2 := by
      nlinarith [sq_nonneg (pairSuccess true x₀ β B L a h x -
        pairSuccess false x₀ β B L a h x)]
    have hweight := radialPropensity_le_on_bump_support x₀ x γ h
      hγ hh.1 hb
    calc
      _ ≤ radialPropensity x₀ γ x *
          ((2 / baselineSuccess B L) *
            (pairSuccess false x₀ β B L a h x -
              pairSuccess true x₀ β B L a h x) ^ 2) :=
          mul_le_mul_of_nonneg_left hbound hprop
      _ ≤ radialPropensity x₀ γ x *
          ((2 / baselineSuccess B L) * (a * h ^ β) ^ 2) := by
          gcongr
      _ ≤ (2 / baselineSuccess B L) * (a * h ^ β) ^ 2 *
          (((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1))) := by
          rw [mul_comm (radialPropensity x₀ γ x)]
          exact mul_le_mul_of_nonneg_left hweight
            (mul_nonneg hbase (sq_nonneg _))

/-- Both potential outcomes of every admissible testing law lie in `{0, B}`. [For the stated inputs and conditions](hyp:d,n,β,B,L,γ,a,c,x₀,j,hadm,hn), [the asserted conclusion holds](goal). -/
lemma lowerPairCompletion_supported_on_endpoints (d n : ℕ)
    (β B L γ a c : ℝ) (x₀ : Fin d → ℝ) (j : Bool)
    (hadm : boundedLowerPairAdmissible d β B L γ a c x₀)
    (hn : 1 ≤ n) :
    ∀ᵐ ω ∂lowerPairCompletion d n β B L γ a c x₀ j,
      ω.2.2.1 ∈ ({0, B} : Set ℝ) ∧
        ω.2.2.2.1 ∈ ({0, B} : Set ℝ) := by
  let S : Set (Completion d) :=
    {ω | ω.2.2.1 ∈ ({0, B} : Set ℝ) ∧
      ω.2.2.2.1 ∈ ({0, B} : Set ℝ)}
  have hS : MeasurableSet S := by
    dsimp [S]
    measurability
  have hzero : (lowerPairCompletion d n β B L γ a c x₀ j) Sᶜ = 0 := by
    unfold lowerPairCompletion
    apply le_antisymm _ zero_le
    calc
      _ ≤ ∫⁻ x, (completionAt B (radialPropensity x₀ γ)
          (fun _ => baselineSuccess B L)
          (pairSuccess j x₀ β B L a (c * oracleMesh d n β γ)) x) Sᶜ
          ∂volume.restrict (cube d) := Measure.bind_apply_le _ hS.compl
      _ = 0 := by
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
        obtain ⟨he, hp₀, hp₁⟩ := hadm.2.2 n hn x hx
        apply (measure_eq_zero_iff_ae_notMem).2
        filter_upwards [CausalSmith.Stat.WeakOverlap.completionAt_supported_on_endpoints B
          (radialPropensity x₀ γ) (fun _ => baselineSuccess B L)
          (pairSuccess j x₀ β B L a (c * oracleMesh d n β γ)) x
          he (by simpa [pairSuccess] using hp₀)
          (by cases j with
              | false => simpa [pairSuccess] using hp₀
              | true => exact hp₁)]
          with ω hω
        simp only [Set.mem_compl_iff, not_not]
        change ω.2.2.1 ∈ ({0, B} : Set ℝ) ∧
          ω.2.2.2.1 ∈ ({0, B} : Set ℝ)
        exact hω
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hzero] with ω hω
  simp only [Set.mem_compl_iff, not_not] at hω
  change ω.2.2.1 ∈ ({0, B} : Set ℝ) ∧
    ω.2.2.2.1 ∈ ({0, B} : Set ℝ) at hω
  exact hω

/-- The paper's explicit bump is the promoted normalized product bump. [For the stated inputs and conditions](hyp:d,z), [the asserted conclusion holds](goal). -/
lemma smoothBump_eq_productBump {d : ℕ} (z : Fin d → ℝ) :
    smoothBump z =
      Causalean.Mathlib.Analysis.Calculus.CubeExtension.productBump z := by
  unfold smoothBump
  rw [Causalean.Mathlib.Analysis.Calculus.CubeExtension.productBump]
  apply Finset.prod_congr rfl
  intro i _
  rw [smoothBump_factor_eq_expNegInvGlue]
  rfl

/-- The treated response perturbation belongs to the paper Hölder ball when
the promoted uniform bump radius fits inside `L`. [For the stated inputs and conditions](hyp:d,β,B,L,a,h,x₀,hβ,hh,hh1,A,hA,hscaled,hrad), [the asserted conclusion holds](goal). -/
lemma pairSuccess_true_holderBall {d : ℕ} (β B L a h : ℝ)
    (x₀ : Fin d → ℝ) (hβ : 0 < β) (hh : 0 < h) (hh1 : h ≤ 1)
    (A : ℝ) (hA : 0 < A)
    (hscaled : Causalean.Mathlib.Analysis.Calculus.CubeExtension.HolderBallOn
      (Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.unitCube d)
      (polynomialDegree β) (β - (polynomialDegree β : ℝ)) A
      (Causalean.Mathlib.Analysis.Calculus.CubeExtension.scaledProductBump β h x₀))
    (hrad : |B * baselineSuccess B L| + |B * a| * A ≤ L) :
    HolderBall β L (fun x => B * pairSuccess true x₀ β B L a h x) := by
  open Causalean.Mathlib.Analysis.Calculus.CubeExtension in
    have haff := holderBallOn_unitCube_add_const_mul hA.le hscaled
      (B * baselineSuccess B L) (B * a)
  have hre : (fun x => B * pairSuccess true x₀ β B L a h x) =
      (fun x => B * baselineSuccess B L + B * a *
        Causalean.Mathlib.Analysis.Calculus.CubeExtension.scaledProductBump β h x₀ x) := by
    funext x
    rw [Causalean.Mathlib.Analysis.Calculus.CubeExtension.scaledProductBump_eq_coordinate_div
      β (ne_of_gt hh), ← smoothBump_eq_productBump]
    simp only [pairSuccess, if_true]
    ring
  rw [hre]
  have hbase :
      Causalean.Mathlib.Analysis.Calculus.CubeExtension.HolderBallOn
        (cube d) (polynomialDegree β) (β - (polynomialDegree β : ℝ))
        (|B * baselineSuccess B L| + |B * a| * A)
        (fun x => B * baselineSuccess B L + B * a *
          Causalean.Mathlib.Analysis.Calculus.CubeExtension.scaledProductBump β h x₀ x) := by
    simpa [polynomialDegree, cube,
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.unitCube] using haff
  refine ⟨hbase.regularity, ?_, ?_⟩
  · intro j hj f x hx
    exact (hbase.derivBound j hj f x hx).trans hrad
  · intro f x hx y hy
    exact (hbase.modulus f x hx y hy).trans
      (mul_le_mul_of_nonneg_right hrad (Real.rpow_nonneg (norm_nonneg _) _))

/-- A Hölder representative `B p₁` identifies the conditional mean of the
treated potential outcome in the explicit completion. [For the stated inputs and conditions](hyp:d,mu,B,β,L,e,p₀,p₁,he,hp₀,hp₁,hvalid,hball), [the asserted conclusion holds](goal). -/
lemma completionBind_holderResponse {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [SFinite mu] (B β L : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hp₀ : Measurable p₀) (hp₁ : Measurable p₁)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      p₁ x ∈ Set.Icc 0 1)
    [IsFiniteMeasure (mu.bind (completionAt B e p₀ p₁))]
    (hball : HolderBall β L (fun x => B * p₁ x)) :
    HolderResponse (mu.bind (completionAt B e p₀ p₁))
      (fun x => B * p₁ x) β L := by
  let Pc := mu.bind (completionAt B e p₀ p₁)
  let X : Completion d → (Fin d → ℝ) := fun ω => ω.1
  let Y₁ : Completion d → ℝ := fun ω => ω.2.2.2.1
  let k₁ : ProbabilityTheory.Kernel (Fin d → ℝ) ℝ :=
    ProbabilityTheory.Kernel.mk (fun x => scaledBernoulli B (p₁ x))
      (by unfold scaledBernoulli realBernoulli; fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel k₁ :=
    ⟨fun x => scaledBernoulli_probability B (p₁ x) (hvalid x).2.2⟩
  have hcomp : Measurable (completionAt B e p₀ p₁) :=
    completionAt_measurable_of_measurable B e p₀ p₁ he hp₀ hp₁ hvalid
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hY₁ : Measurable Y₁ := by dsimp [Y₁]; fun_prop
  have hcov : Pc.map X = mu := by
    dsimp [Pc, X]
    exact completionBind_covariate_marginal mu B e p₀ p₁ hcomp.aemeasurable
      (Filter.Eventually.of_forall hvalid)
  have hjoint : Pc.map (fun ω => (X ω, Y₁ ω)) = Measure.compProd mu k₁ := by
    dsimp [Pc, X, Y₁, k₁]
    exact completionBind_covariate_treatedPotential_compProd mu B e p₀ p₁
      he hp₀ hp₁ hvalid
  have hcond : ProbabilityTheory.condDistrib Y₁ X Pc =ᵐ[mu] k₁ := by
    have h := ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      (μ := Pc) (X := X) (Y := Y₁) (κ := k₁) hX hY₁
        (by simpa [hcov] using hjoint)
    simpa [hcov] using h
  have hY₁int : Integrable Y₁ Pc := by
    apply Integrable.mono' (integrable_const |B|) hY₁.aestronglyMeasurable
    filter_upwards [completionBind_supported_on_endpoints mu B e p₀ p₁
      (Filter.Eventually.of_forall hvalid)] with ω hω
    rcases hω.2 with hzero | hBval
    · simp [Y₁, hzero]
    · dsimp [Y₁]
      rw [Set.mem_singleton_iff.mp hBval]
  have hce : Pc[Y₁ | MeasurableSpace.comap X inferInstance] =ᵐ[Pc]
      fun ω => ∫ y : ℝ, y ∂ProbabilityTheory.condDistrib Y₁ X Pc (X ω) := by
    simpa using ProbabilityTheory.condExp_ae_eq_integral_condDistrib' hX hY₁int
  have hcond' : ProbabilityTheory.condDistrib Y₁ X Pc =ᵐ[Pc.map X] k₁ := by
    rw [hcov]
    exact hcond
  have hkernel := ae_eq_comp hX.aemeasurable hcond'
  have hmean : (fun ω : Completion d =>
      ∫ y : ℝ, y ∂ProbabilityTheory.condDistrib Y₁ X Pc (X ω)) =ᵐ[Pc]
      fun ω => B * p₁ (X ω) := by
    filter_upwards [hkernel] with ω hω
    calc
      _ = ∫ y : ℝ, y ∂k₁ (X ω) := by congr 1
      _ = _ := scaledBernoulli_integral_id B (p₁ (X ω)) (hvalid (X ω)).2.2
  exact ⟨hball, hmean.symm.trans hce.symm⟩

/-- Endpoint-supported potential outcomes give the required treated mean and
sub-Gaussian residual bound whenever treatment is positive almost everywhere. [For the stated inputs and conditions](hyp:d,mu,B,hB,e,p₀,p₁,he,hp₀,hp₁,hvalid,hpos), [the asserted conclusion holds](goal). -/
lemma completionBind_boundedOutcome_of_endpoint_support {d : ℕ}
    (mu : Measure (Fin d → ℝ)) [IsProbabilityMeasure mu] (B : ℝ) (hB : 0 < B)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hp₀ : Measurable p₀) (hp₁ : Measurable p₁)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      p₁ x ∈ Set.Icc 0 1)
    [IsFiniteMeasure ((mu.bind (completionAt B e p₀ p₁)).map observed)]
    (hpos : ∀ᵐ x ∂mu, 0 < e x) :
    let Pc := mu.bind (completionAt B e p₀ p₁)
    let P := Pc.map observed
    BoundedMeanSubGaussianResidual P B := by
  dsimp
  let Pc := mu.bind (completionAt B e p₀ p₁)
  let P := Pc.map observed
  let XA : Obs d → ((Fin d → ℝ) × Bool) := fun z => (z.1, z.2.1)
  let Y : Obs d → ℝ := fun z => z.2.2
  let kA : ProbabilityTheory.Kernel (Fin d → ℝ) Bool :=
    ProbabilityTheory.Kernel.mk (fun x => realBernoulli (e x))
      (by unfold realBernoulli; fun_prop)
  letI : ProbabilityTheory.IsMarkovKernel kA :=
    ⟨fun x => realBernoulli_probability (e x) (hvalid x).1⟩
  have hk : Measurable (completionAt B e p₀ p₁) :=
    completionAt_measurable_of_measurable B e p₀ p₁ he hp₀ hp₁ hvalid
  letI : IsProbabilityMeasure Pc := by
    apply isProbabilityMeasure_bind hk.aemeasurable
    filter_upwards [] with x
    letI := realBernoulli_probability (e x) (hvalid x).1
    letI := scaledBernoulli_probability B (p₀ x) (hvalid x).2.1
    letI := scaledBernoulli_probability B (p₁ x) (hvalid x).2.2
    unfold completionAt
    apply Measure.isProbabilityMeasure_map
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption)
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    apply Measure.isProbabilityMeasure_map
    unfold observed
    fun_prop
  have hXA : Measurable XA := by dsimp [XA]; fun_prop
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hXAmap : P.map XA = Measure.compProd mu kA := by
    dsimp [P, Pc, XA]
    rw [Measure.map_map (by fun_prop) (by unfold observed; fun_prop)]
    exact completionBind_covariate_treatment_compProd mu B e p₀ p₁
      he hp₀ hp₁ hvalid
  have hsuppP : ∀ᵐ z ∂P, Y z ∈ Set.Icc (0 : ℝ) B := by
    rw [show P = Pc.map observed by rfl]
    apply (ae_map_iff (by unfold observed; fun_prop)
      (by measurability : MeasurableSet {z : Obs d | Y z ∈ Set.Icc (0 : ℝ) B})).2
    filter_upwards [completionBind_supported_on_endpoints mu B e p₀ p₁
      (Filter.Eventually.of_forall hvalid),
      completionBind_consistency mu B e p₀ p₁ hk.aemeasurable] with ω hω hcons
    have hy : ω.2.2.2.2 ∈ ({0, B} : Set ℝ) := by
      rw [hcons]
      split
      · exact hω.2
      · exact hω.1
    rcases hy with hzero | hBval
    · change ω.2.2.2.2 = 0 at hzero
      dsimp [Y, observed]
      rw [hzero]
      exact ⟨le_rfl, hB.le⟩
    · change ω.2.2.2.2 = B at hBval
      dsimp [Y, observed]
      rw [hBval]
      exact ⟨hB.le, le_rfl⟩
  have hsuppProd : ∀ᵐ q ∂Measure.compProd (P.map XA)
      (ProbabilityTheory.condDistrib Y XA P), q.2 ∈ Set.Icc (0 : ℝ) B := by
    rw [ProbabilityTheory.compProd_map_condDistrib hY.aemeasurable]
    exact (ae_map_iff (by fun_prop)
      (by measurability : MeasurableSet
        {q : ((Fin d → ℝ) × Bool) × ℝ | q.2 ∈ Set.Icc (0 : ℝ) B})).2 hsuppP
  rw [hXAmap] at hsuppProd
  have hsections := Measure.ae_ae_of_ae_compProd
    (Measure.ae_ae_of_ae_compProd hsuppProd)
  have htreat : ∀ᵐ x ∂mu, ∀ᵐ y ∂treatedKernel P x,
      y ∈ Set.Icc (0 : ℝ) B := by
    filter_upwards [hsections, hpos] with x hx hxp
    have htrue := realBernoulli_ae_at_true_of_pos (e x) hxp
      (fun a => ∀ᵐ y ∂ProbabilityTheory.condDistrib Y XA P (x, a),
        y ∈ Set.Icc (0 : ℝ) B) (by simpa [kA] using hx)
    simpa [treatedKernel, XA, Y] using htrue
  have hcov : covariateLaw P = mu := by
    dsimp [P, Pc, covariateLaw]
    rw [Measure.map_map (by fun_prop) (by unfold observed; fun_prop)]
    exact completionBind_covariate_marginal mu B e p₀ p₁ hk.aemeasurable
      (Filter.Eventually.of_forall hvalid)
  unfold BoundedMeanSubGaussianResidual
  rw [hcov]
  filter_upwards [htreat] with x hsupp
  let ν := treatedKernel P x
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, treatedKernel]
    infer_instance
  have hint : Integrable (fun y : ℝ => y) ν :=
    Integrable.of_mem_Icc 0 B measurable_id.aemeasurable hsupp
  have hmean0 : 0 ≤ ∫ y : ℝ, y ∂ν := integral_nonneg_of_ae (hsupp.mono fun _ h => h.1)
  have hmeanB : ∫ y : ℝ, y ∂ν ≤ B := by
    simpa using integral_mono_ae hint (integrable_const B) (hsupp.mono fun _ h => h.2)
  have hsg := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
    (X := fun y : ℝ => y) (μ := ν) measurable_id.aemeasurable hsupp
  constructor
  · change |∫ y : ℝ, y ∂ν| ≤ B
    rw [abs_of_nonneg hmean0]
    exact hmeanB
  · intro t
    change Integrable (fun y : ℝ => Real.exp (t * (y - ∫ z : ℝ, z ∂ν))) ν ∧
      ProbabilityTheory.mgf (fun y : ℝ => y - ∫ z : ℝ, z ∂ν) ν t ≤
        Real.exp (B ^ 2 * t ^ 2 / 2)
    constructor
    · exact hsg.integrable_exp_mul t
    · exact (hsg.mgf_le t).trans (Real.exp_le_exp.mpr (by
        rw [show ‖B - 0‖₊ = ⟨B, hB.le⟩ by
          apply Subtype.ext
          simp [Real.norm_eq_abs, abs_of_pos hB]]
        change (B / 2) ^ 2 * t ^ 2 / 2 ≤ B ^ 2 * t ^ 2 / 2
        nlinarith [sq_nonneg B, sq_nonneg t]))

/-- A valid explicit completion over the uniform cube is a global-tail model
once its response representative and sharp propensity tail are supplied. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,hB,hC,hcf,e,p₀,p₁,μ₁,he,hp₀,hp₁,hvalid,hpos,htail,hholder), [the asserted conclusion holds](goal). -/
lemma completionBind_uniformCube_globalTailModel {d : ℕ}
    (β B L C c_f γ : ℝ) (hB : 0 < B) (hC : 1 ≤ C) (hcf : c_f ≤ 1)
    (e p₀ p₁ μ₁ : (Fin d → ℝ) → ℝ)
    (he : Measurable e) (hp₀ : Measurable p₀) (hp₁ : Measurable p₁)
    (hvalid : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      p₁ x ∈ Set.Icc 0 1)
    (hpos : ∀ᵐ x ∂volume.restrict (cube d), 0 < e x)
    (htail : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (volume.restrict (cube d)).real {x | e x ≤ t} ≤ t ^ (γ - 1))
    [IsProbabilityMeasure
      ((volume.restrict (cube d)).bind (completionAt B e p₀ p₁))]
    (hholder : HolderResponse
      ((volume.restrict (cube d)).bind (completionAt B e p₀ p₁)) μ₁ β L) :
    @GlobalTailModel d β B L C c_f γ
      ((volume.restrict (cube d)).bind (completionAt B e p₀ p₁)) inferInstance
      μ₁ e := by
  let mu := volume.restrict (cube d)
  letI : IsProbabilityMeasure mu := uniformCube_probability_lowerPair d
  let Pc := mu.bind (completionAt B e p₀ p₁)
  let P := Pc.map observed
  have hk : Measurable (completionAt B e p₀ p₁) :=
    completionAt_measurable_of_measurable B e p₀ p₁ he hp₀ hp₁ hvalid
  letI : IsProbabilityMeasure Pc := by
    apply isProbabilityMeasure_bind hk.aemeasurable
    filter_upwards [] with x
    letI := realBernoulli_probability (e x) (hvalid x).1
    letI := scaledBernoulli_probability B (p₀ x) (hvalid x).2.1
    letI := scaledBernoulli_probability B (p₁ x) (hvalid x).2.2
    unfold completionAt
    apply Measure.isProbabilityMeasure_map
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption)
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    apply Measure.isProbabilityMeasure_map
    unfold observed
    fun_prop
  have hcov : covariateLaw P = mu := by
    dsimp [P, Pc, covariateLaw]
    rw [Measure.map_map (by fun_prop) (by unfold observed; fun_prop)]
    exact completionBind_covariate_marginal mu B e p₀ p₁ hk.aemeasurable
      (Filter.Eventually.of_forall hvalid)
  refine {
    cubeSupport := ?_
    covariateAC := ?_
    density := ?_
    consistency := ?_
    exchangeability := ?_
    tail := ?_
    outcome := ?_
    smooth := hholder }
  · rw [hcov]
    change (volume.restrict (cube d)) (cube d) = 1
    rw [Measure.restrict_apply (by simp [cube] : MeasurableSet (cube d)),
      Set.inter_self]
    have hcube : cube d =
        Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
      ext x
      simp [cube, Set.mem_Icc, Pi.le_def]
    rw [hcube, Real.volume_Icc_pi]
    simp [observed]
  · rw [hcov]
  · unfold CovariateDensityLowerBound covariateDensity
    rw [hcov]
    filter_upwards [Measure.rnDeriv_self mu] with x hx
    rw [hx, ENNReal.toReal_one]
    exact hcf
  · exact completionBind_consistency mu B e p₀ p₁ hk.aemeasurable
  · exact completionBind_condExchangeable mu B e p₀ p₁ he hp₀ hp₁ hvalid
  · constructor
    · have hpraw := completionBind_propensity_ae mu B e p₀ p₁
        he hp₀ hp₁ hvalid
      dsimp at hpraw
      rw [hcov]
      filter_upwards [hpraw] with x hx
      exact hx.symm
    · intro t ht
      rw [hcov]
      exact (htail t ht).trans (by
        have hnonneg := Real.rpow_nonneg ht.1 (γ - 1)
        nlinarith [hC])
  · exact completionBind_boundedOutcome_of_endpoint_support mu B hB e p₀ p₁
      he hp₀ hp₁ hvalid hpos

/-- The localized common-statistic Bernoulli KL estimate over an arbitrary
measurable base space. [For the stated inputs and conditions](hyp:S,m,p,q,hp,hq,hp0,hp1,hq0,hq1,D,hD,E,hE,hdiff), [the asserted conclusion holds](goal). -/
lemma genericCommonBernoulli_klDiv_le_of_localized_parameter
    {S : Type*} [MeasurableSpace S]
    (m : Measure S) [IsFiniteMeasure m] (p q : S → ℝ)
    (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ r, 1 / 4 ≤ p r) (hp1 : ∀ r, p r ≤ 3 / 4)
    (hq0 : ∀ r, 1 / 4 ≤ q r) (hq1 : ∀ r, q r ≤ 3 / 4)
    {D : ℝ} (hD : 0 ≤ D) {E : Set S} (hE : MeasurableSet E)
    (hdiff : ∀ᵐ r ∂m, |p r - q r| ≤ E.indicator (fun _ => D) r) :
    InformationTheory.klDiv
        (Measure.compProd m
          (Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p hp))
        (Measure.compProd m
          (Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel q hq)) ≤
      ENNReal.ofReal (4 * D ^ 2) * m E := by
  let k : ProbabilityTheory.Kernel S ℝ :=
    Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p hp
  let k' : ProbabilityTheory.Kernel S ℝ :=
    Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel q hq
  letI : ProbabilityTheory.IsMarkovKernel k :=
    Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel_isMarkovKernel p hp
      (fun r => by linarith [hp0 r]) (fun r => by linarith [hp1 r])
  letI : ProbabilityTheory.IsMarkovKernel k' :=
    Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel_isMarkovKernel q hq
      (fun r => by linarith [hq0 r]) (fun r => by linarith [hq1 r])
  rw [Causalean.Mathlib.InformationTheory.Measure.klDiv_compProd_right_of_forall_ac]
  · calc
      (∫⁻ r, InformationTheory.klDiv (k r) (k' r) ∂m) ≤
          ∫⁻ r, E.indicator (fun _ => ENNReal.ofReal (4 * D ^ 2)) r ∂m := by
        apply lintegral_mono_ae
        filter_upwards [hdiff] with r hr
        have hkl :=
          Causalean.Mathlib.Probability.bernoulliLaw_klDiv_le_four_sq_sub
            (hp0 r) (hp1 r) (hq0 r) (hq1 r)
        change InformationTheory.klDiv (k r) (k' r) ≤ _ at hkl
        by_cases hrE : r ∈ E
        · rw [Set.indicator_of_mem hrE]
          exact hkl.trans (ENNReal.ofReal_le_ofReal (by
            have habs : |p r - q r| ≤ D := by simpa [hrE] using hr
            have hsq := (sq_le_sq₀ (abs_nonneg (p r - q r)) hD).2 habs
            rw [← sq_abs (p r - q r)]
            nlinarith))
        · rw [Set.indicator_of_notMem hrE]
          have hpq : p r = q r := by
            have hz : |p r - q r| ≤ 0 := by simpa [hrE] using hr
            exact sub_eq_zero.mp (abs_eq_zero.mp
              (le_antisymm hz (abs_nonneg _)))
          have hkk : k r = k' r := by
            ext A hA
            simp [k, k',
              Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel, hpq]
          rw [hkk, InformationTheory.klDiv_self]
      _ = ∫⁻ _r in E, ENNReal.ofReal (4 * D ^ 2) ∂m :=
        lintegral_indicator hE _
      _ = ENNReal.ofReal (4 * D ^ 2) * m E :=
        setLIntegral_const E (ENNReal.ofReal (4 * D ^ 2))
  · filter_upwards with r
    have hkl :=
      Causalean.Mathlib.Probability.bernoulliLaw_klDiv_le_four_sq_sub
        (hp0 r) (hp1 r) (hq0 r) (hq1 r)
    have hfinite : InformationTheory.klDiv (k r) (k' r) ≠ ⊤ := by
      change InformationTheory.klDiv (k r) (k' r) ≤ _ at hkl
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
    exact (InformationTheory.klDiv_ne_top_iff.mp hfinite).1

/-- At a fixed covariate, the observed completion is the disjoint sum of its
control and treated scaled-Bernoulli cells. [For the stated inputs and conditions](hyp:d,B,e,p₀,p₁,x,he,hp₀,hp₁), [the asserted conclusion holds](goal). -/
lemma completionAt_observed_map_unequal_arms {d : ℕ} (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc 0 1) (hp₀ : p₀ x ∈ Set.Icc 0 1)
    (hp₁ : p₁ x ∈ Set.Icc 0 1) :
    (completionAt B e p₀ p₁ x).map observed =
      ENNReal.ofReal (1 - e x) •
          ((Measure.dirac x).prod
            ((Measure.dirac false).prod (scaledBernoulli B (p₀ x)))) +
        ENNReal.ofReal (e x) •
          ((Measure.dirac x).prod
            ((Measure.dirac true).prod (scaledBernoulli B (p₁ x)))) := by
  letI := realBernoulli_probability (e x) he
  letI := scaledBernoulli_probability B (p₀ x) hp₀
  letI := scaledBernoulli_probability B (p₁ x) hp₁
  unfold completionAt
  rw [Measure.map_map (by unfold observed; fun_prop) (by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption))]
  rw [Measure.dirac_prod]
  let g : Bool × ℝ × ℝ → Obs d :=
    fun z => (x, z.1, if z.1 then z.2.2 else z.2.1)
  change Measure.map g ((realBernoulli (e x)).prod
      ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))) = _
  have hg : Measurable g := by
    dsimp [g]
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop (disch := assumption)
  unfold realBernoulli
  rw [Measure.add_prod, Measure.map_add _ _ hg]
  congr 1
  · rw [Measure.prod_smul_left, Measure.map_smul]
    congr 1
    rw [Measure.dirac_prod, Measure.map_map hg (by fun_prop)]
    change Measure.map ((fun y : ℝ => (x, false, y)) ∘ Prod.fst)
      ((scaledBernoulli B (p₀ x)).prod
        (scaledBernoulli B (p₁ x))) = _
    rw [← Measure.map_map (by fun_prop : Measurable (fun y : ℝ => (x, false, y)))
      measurable_fst, Measure.map_fst_prod]
    simp only [measure_univ, one_smul]
    rw [Measure.dirac_prod (x := false)]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  · rw [Measure.prod_smul_left, Measure.map_smul]
    congr 1
    rw [Measure.dirac_prod, Measure.map_map hg (by fun_prop)]
    change Measure.map ((fun y : ℝ => (x, true, y)) ∘ Prod.snd)
      ((scaledBernoulli B (p₀ x)).prod
        (scaledBernoulli B (p₁ x))) = _
    rw [← Measure.map_map (by fun_prop : Measurable (fun y : ℝ => (x, true, y)))
      measurable_snd, Measure.map_snd_prod]
    simp only [measure_univ, one_smul]
    rw [Measure.dirac_prod (x := true)]
    rw [Measure.dirac_prod x]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl

/-- [For the stated inputs and conditions](hyp:S,T,s,k), [the asserted conclusion holds](goal). -/

lemma dirac_compProd_eq_map_prodMk
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSingletonClass S] (s : S) (k : ProbabilityTheory.Kernel S T)
    [ProbabilityTheory.IsSFiniteKernel k] :
    Measure.compProd (Measure.dirac s) k = (k s).map (Prod.mk s) := by
  ext A hA
  rw [Measure.dirac_compProd_apply hA,
    Measure.map_apply measurable_prodMk_left hA]

/-- The fixed-covariate observed law is a measurable embedding of a treatment
Bernoulli followed by the selected arm's scaled Bernoulli response. [For the stated inputs and conditions](hyp:d,B,e,p₀,p₁,x,he,hp₀,hp₁), [the asserted conclusion holds](goal). -/
lemma completionAt_observed_eq_selected_compProd {d : ℕ} (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc 0 1) (hp₀ : p₀ x ∈ Set.Icc 0 1)
    (hp₁ : p₁ x ∈ Set.Icc 0 1) :
    let kY : ProbabilityTheory.Kernel Bool ℝ :=
      ProbabilityTheory.Kernel.mk
        (fun a => scaledBernoulli B (if a then p₁ x else p₀ x))
        (measurable_of_finite _)
    (completionAt B e p₀ p₁ x).map observed =
      (Measure.compProd (realBernoulli (e x)) kY).map
        (fun ay => (x, ay.1, ay.2)) := by
  dsimp
  let kY : ProbabilityTheory.Kernel Bool ℝ :=
    ProbabilityTheory.Kernel.mk
      (fun a => scaledBernoulli B (if a then p₁ x else p₀ x))
      (measurable_of_finite _)
  letI := scaledBernoulli_probability B (p₀ x) hp₀
  letI := scaledBernoulli_probability B (p₁ x) hp₁
  letI : ProbabilityTheory.IsMarkovKernel kY := ⟨by
    intro a
    cases a
    · exact scaledBernoulli_probability B (p₀ x) hp₀
    · exact scaledBernoulli_probability B (p₁ x) hp₁⟩
  rw [completionAt_observed_map_unequal_arms B e p₀ p₁ x he hp₀ hp₁]
  have hsource : Measure.compProd (realBernoulli (e x)) kY =
      ENNReal.ofReal (1 - e x) •
          (scaledBernoulli B (p₀ x)).map (Prod.mk false) +
        ENNReal.ofReal (e x) •
          (scaledBernoulli B (p₁ x)).map (Prod.mk true) := by
    unfold realBernoulli
    rw [Measure.compProd_add_left,
      Measure.compProd_smul_left, Measure.compProd_smul_left,
      dirac_compProd_eq_map_prodMk false kY,
      dirac_compProd_eq_map_prodMk true kY]
    rfl
  rw [hsource, Measure.map_add _ _ (by fun_prop),
    Measure.map_smul, Measure.map_smul]
  congr 1
  · rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.dirac_prod, Measure.dirac_prod,
      Measure.map_map (by fun_prop) (by fun_prop)]
  · rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.dirac_prod, Measure.dirac_prod,
      Measure.map_map (by fun_prop) (by fun_prop)]

/-- [For the stated inputs and conditions](hyp:B,p), [the asserted conclusion holds](goal). -/

lemma scaledBernoulli_eq_map_bernoulliLaw (B p : ℝ) :
    scaledBernoulli B p =
      (Causalean.Mathlib.Probability.bernoulliLaw p).map (fun y => B * y) := by
  unfold scaledBernoulli realBernoulli
    Causalean.Mathlib.Probability.bernoulliLaw
  rw [Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul,
    Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul]
  simp [add_comm]

/-- A localized common-statistic KL bound from any supplied pointwise
quadratic Bernoulli estimate. [For the stated inputs and conditions](hyp:S,m,p,q,hp,hq,hp01,hq01,K,D,hK,hD,hpoint,E,hE,hdiff), [the asserted conclusion holds](goal). -/
lemma genericCommonBernoulli_klDiv_le_of_localized_quadratic
    {S : Type*} [MeasurableSpace S]
    (m : Measure S) [IsFiniteMeasure m] (p q : S → ℝ)
    (hp : Measurable p) (hq : Measurable q)
    (hp01 : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (hq01 : ∀ r, q r ∈ Set.Icc (0 : ℝ) 1)
    {K D : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hpoint : ∀ r, InformationTheory.klDiv
      (Causalean.Mathlib.Probability.bernoulliLaw (p r))
      (Causalean.Mathlib.Probability.bernoulliLaw (q r)) ≤
        ENNReal.ofReal (K * (p r - q r) ^ 2))
    {E : Set S} (hE : MeasurableSet E)
    (hdiff : ∀ᵐ r ∂m, |p r - q r| ≤ E.indicator (fun _ => D) r) :
    InformationTheory.klDiv
        (Measure.compProd m
          (Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p hp))
        (Measure.compProd m
          (Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel q hq)) ≤
      ENNReal.ofReal (K * D ^ 2) * m E := by
  let k := Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p hp
  let k' := Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel q hq
  letI : ProbabilityTheory.IsMarkovKernel k :=
    Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel_isMarkovKernel p hp
      (fun r => (hp01 r).1) (fun r => (hp01 r).2)
  letI : ProbabilityTheory.IsMarkovKernel k' :=
    Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel_isMarkovKernel q hq
      (fun r => (hq01 r).1) (fun r => (hq01 r).2)
  rw [Causalean.Mathlib.InformationTheory.Measure.klDiv_compProd_right_of_forall_ac]
  · calc
      (∫⁻ r, InformationTheory.klDiv (k r) (k' r) ∂m) ≤
          ∫⁻ r, E.indicator (fun _ => ENNReal.ofReal (K * D ^ 2)) r ∂m := by
        apply lintegral_mono_ae
        filter_upwards [hdiff] with r hr
        by_cases hrE : r ∈ E
        · rw [Set.indicator_of_mem hrE]
          exact (hpoint r).trans (ENNReal.ofReal_le_ofReal (by
            have habs : |p r - q r| ≤ D := by simpa [hrE] using hr
            have hsq := (sq_le_sq₀ (abs_nonneg (p r - q r)) hD).2 habs
            rw [← sq_abs (p r - q r)]
            exact mul_le_mul_of_nonneg_left hsq hK))
        · rw [Set.indicator_of_notMem hrE]
          have hpq : p r = q r := by
            have hz : |p r - q r| ≤ 0 := by simpa [hrE] using hr
            exact sub_eq_zero.mp (abs_eq_zero.mp
              (le_antisymm hz (abs_nonneg _)))
          have hkk : k r = k' r := by
            ext A hA
            simp [k, k',
              Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel, hpq]
          rw [hkk, InformationTheory.klDiv_self]
      _ = ∫⁻ _r in E, ENNReal.ofReal (K * D ^ 2) ∂m :=
        lintegral_indicator hE _
      _ = ENNReal.ofReal (K * D ^ 2) * m E :=
        setLIntegral_const E (ENNReal.ofReal (K * D ^ 2))
  · filter_upwards with r
    have hfinite : InformationTheory.klDiv (k r) (k' r) ≠ ⊤ := by
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hpoint r)
    exact (InformationTheory.klDiv_ne_top_iff.mp hfinite).1

/-- [For the stated inputs and conditions](hyp:m,B,p,hp,hp01), [the asserted conclusion holds](goal). -/

lemma selectedScaled_compProd_eq_map_commonBernoulli
    (m : Measure Bool) [SFinite m] (B : ℝ) (p : Bool → ℝ)
    (hp : Measurable p) (hp01 : ∀ a, p a ∈ Set.Icc (0 : ℝ) 1) :
    let kS : ProbabilityTheory.Kernel Bool ℝ :=
      ProbabilityTheory.Kernel.mk (fun a => scaledBernoulli B (p a))
        (measurable_of_finite _)
    let kB := Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p hp
    Measure.compProd m kS =
      (Measure.compProd m kB).map (Prod.map id (fun y => B * y)) := by
  dsimp
  let kS : ProbabilityTheory.Kernel Bool ℝ :=
    ProbabilityTheory.Kernel.mk (fun a => scaledBernoulli B (p a))
      (measurable_of_finite _)
  let kB := Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p hp
  letI : ProbabilityTheory.IsMarkovKernel kB :=
    Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel_isMarkovKernel p hp
      (fun a => (hp01 a).1) (fun a => (hp01 a).2)
  have hk : kS = kB.map (fun y => B * y) := by
    ext a A hA
    rw [ProbabilityTheory.Kernel.map_apply _ (by fun_prop)]
    exact congrArg (fun ν : Measure ℝ => ν A)
      (scaledBernoulli_eq_map_bernoulliLaw B (p a))
  change Measure.compProd m kS =
    (Measure.compProd m kB).map (Prod.map id (fun y => B * y))
  rw [hk, Measure.compProd_map (by fun_prop)]

/-- The observed fixed-covariate KL has the treatment-propensity weight. [For the stated inputs and conditions](hyp:d,x₀,x,B,L,β,γ,a,h,hβ,hB,hL,hγ,ha,hh), [the asserted conclusion holds](goal). -/
lemma lowerPair_completionAt_observed_klDiv_le {d : ℕ}
    (x₀ x : Fin d → ℝ) (B L β γ a h : ℝ)
    (hβ : 0 < β) (hB : 0 < B) (hL : 0 < L) (hγ : 1 < γ)
    (ha : 0 ≤ a ∧ a ≤ baselineSuccess B L)
    (hh : 0 < h ∧ h ≤ 1) :
    InformationTheory.klDiv
      ((completionAt B (radialPropensity x₀ γ)
        (fun _ => baselineSuccess B L)
        (pairSuccess false x₀ β B L a h) x).map observed)
      ((completionAt B (radialPropensity x₀ γ)
        (fun _ => baselineSuccess B L)
        (pairSuccess true x₀ β B L a h) x).map observed) ≤
      ENNReal.ofReal ((2 / baselineSuccess B L) * (a * h ^ β) ^ 2) *
        ENNReal.ofReal (radialPropensity x₀ γ x) := by
  let e := radialPropensity x₀ γ
  let p₀ : (Fin d → ℝ) → ℝ := fun _ => baselineSuccess B L
  let pF := pairSuccess false x₀ β B L a h
  let pT := pairSuccess true x₀ β B L a h
  have he := radialPropensity_mem_Icc x₀ x γ hγ
  letI := realBernoulli_probability (radialPropensity x₀ γ x) he
  have hpF := pairSuccess_mem_Icc_of_small false x₀ β B L a h hB hL hβ
    ha ⟨hh.1.le, hh.2⟩ x
  have hpT := pairSuccess_mem_Icc_of_small true x₀ β B L a h hB hL hβ
    ha ⟨hh.1.le, hh.2⟩ x
  let m := realBernoulli (e x)
  let p : Bool → ℝ := fun z => if z then pF x else p₀ x
  let q : Bool → ℝ := fun z => if z then pT x else p₀ x
  have hp : Measurable p := measurable_of_finite _
  have hq : Measurable q := measurable_of_finite _
  have hp01 : ∀ z, p z ∈ Set.Icc (0 : ℝ) 1 := fun z => by
    cases z
    · simpa [p, p₀, pF, pairSuccess] using hpF
    · simpa [p, pF] using hpF
  have hq01 : ∀ z, q z ∈ Set.Icc (0 : ℝ) 1 := fun z => by
    cases z
    · simpa [q, p₀, pT, pairSuccess] using hpF
    · simpa [q, pT] using hpT
  let kSF : ProbabilityTheory.Kernel Bool ℝ :=
    ProbabilityTheory.Kernel.mk (fun z => scaledBernoulli B (p z))
      (measurable_of_finite _)
  let kST : ProbabilityTheory.Kernel Bool ℝ :=
    ProbabilityTheory.Kernel.mk (fun z => scaledBernoulli B (q z))
      (measurable_of_finite _)
  let kBF := Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel p hp
  let kBT := Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel q hq
  letI : ProbabilityTheory.IsMarkovKernel kSF := ⟨fun z =>
    scaledBernoulli_probability B (p z) (hp01 z)⟩
  letI : ProbabilityTheory.IsMarkovKernel kST := ⟨fun z =>
    scaledBernoulli_probability B (q z) (hq01 z)⟩
  letI : ProbabilityTheory.IsMarkovKernel kBF :=
    Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel_isMarkovKernel p hp
      (fun z => (hp01 z).1) (fun z => (hp01 z).2)
  letI : ProbabilityTheory.IsMarkovKernel kBT :=
    Causalean.Mathlib.InformationTheory.commonStatisticBernoulliKernel_isMarkovKernel q hq
      (fun z => (hq01 z).1) (fun z => (hq01 z).2)
  have hobsF := completionAt_observed_eq_selected_compProd B e p₀ pF x he
    (by simpa [p₀, pF, pairSuccess] using hpF) hpF
  have hobsT := completionAt_observed_eq_selected_compProd B e p₀ pT x he
    (by simpa [p₀, pT, pairSuccess] using hpF) hpT
  have hsF : Measure.compProd m kSF =
      (Measure.compProd m kBF).map (Prod.map id (fun y => B * y)) := by
    exact selectedScaled_compProd_eq_map_commonBernoulli m B p hp hp01
  have hsT : Measure.compProd m kST =
      (Measure.compProd m kBT).map (Prod.map id (fun y => B * y)) := by
    exact selectedScaled_compProd_eq_map_commonBernoulli m B q hq hq01
  rw [hobsF, hobsT]
  change InformationTheory.klDiv
      ((Measure.compProd m kSF).map (fun ay => (x, ay.1, ay.2)))
      ((Measure.compProd m kST).map (fun ay => (x, ay.1, ay.2))) ≤ _
  calc
    _ ≤ InformationTheory.klDiv (Measure.compProd m kSF)
        (Measure.compProd m kST) := InformationTheory.klDiv_map_le _ _ (by fun_prop)
    _ ≤ InformationTheory.klDiv (Measure.compProd m kBF)
        (Measure.compProd m kBT) := by
      rw [hsF, hsT]
      exact InformationTheory.klDiv_map_le _ _ (by fun_prop)
    _ ≤ ENNReal.ofReal ((2 / baselineSuccess B L) * (a * h ^ β) ^ 2) *
        m {true} := by
      apply genericCommonBernoulli_klDiv_le_of_localized_quadratic m p q hp hq
        hp01 hq01
        (by
          show 0 ≤ 2 / baselineSuccess B L
          unfold baselineSuccess
          positivity)
        (mul_nonneg ha.1 (Real.rpow_nonneg hh.1.le _))
      · intro z
        cases z
        · simp only [p, q, Bool.false_eq_true, if_false]
          have hbase01 : p₀ x ∈ Set.Icc (0 : ℝ) 1 := by
            simpa [p₀, pF, pairSuccess] using hpF
          letI := Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure
            hbase01.1 hbase01.2
          rw [InformationTheory.klDiv_self]
          exact bot_le
        · have hpi := pairSuccess_mem_Ioo_of_small false x₀ x β B L a h
            hB hL ha ⟨hh.1.le, hh.2⟩ hβ.le
          have hqi := pairSuccess_mem_Ioo_of_small true x₀ x β B L a h
            hB hL ha ⟨hh.1.le, hh.2⟩ hβ.le
          have hfin : InformationTheory.klDiv
              (Causalean.Mathlib.Probability.bernoulliLaw (pF x))
              (Causalean.Mathlib.Probability.bernoulliLaw (pT x)) ≠ ⊤ :=
            InformationTheory.klDiv_ne_top
              (Causalean.Mathlib.Probability.bernoulliLaw_ac_of_reference_interior
                hqi.1 hqi.2)
              Causalean.Mathlib.Probability.bernoulliLaw_llr_integrable
          change InformationTheory.klDiv
              (Causalean.Mathlib.Probability.bernoulliLaw (pF x))
              (Causalean.Mathlib.Probability.bernoulliLaw (pT x)) ≤
            ENNReal.ofReal ((2 / baselineSuccess B L) * (pF x - pT x) ^ 2)
          rw [← ENNReal.ofReal_toReal hfin]
          apply ENNReal.ofReal_le_ofReal
          rw [Causalean.Mathlib.Probability.bernoulliLaw_klDiv_toReal
            hpi.1.le hpi.2.le hqi.1 hqi.2]
          simpa [p, q, pF, pT] using
            lowerPair_pointwise_kl_bound x₀ x β B L a h hβ hB hL ha
              ⟨hh.1.le, hh.2⟩
      · exact MeasurableSet.singleton true
      · filter_upwards with z
        cases z
        · simp [p, q, p₀]
        · simp only [Set.indicator_of_mem (Set.mem_singleton true)]
          change |pF x - pT x| ≤ a * h ^ β
          rw [abs_sub_comm, abs_of_nonneg
            (pairSuccess_perturbation_bound x₀ x β B L a h ha.1 hh.1.le).1]
          exact (pairSuccess_perturbation_bound x₀ x β B L a h ha.1 hh.1.le).2
    _ = _ := by
      change _ * (realBernoulli (e x)) {true} = _
      simp [realBernoulli, e, he.1]

/-- Integrating the fixed-covariate bound over the bump support gives the
raw one-observation KL rate. [For the stated inputs and conditions](hyp:d,x₀,hx₀,B,L,β,γ,a,h,hβ,hB,hL,hγ,ha,hh), [the asserted conclusion holds](goal). -/
lemma lowerPair_observed_klDiv_le_raw {d : ℕ}
    (x₀ : Fin d → ℝ) (hx₀ : x₀ ∈ cube d) (B L β γ a h : ℝ)
    (hβ : 0 < β) (hB : 0 < B) (hL : 0 < L) (hγ : 1 < γ)
    (ha : 0 ≤ a ∧ a ≤ baselineSuccess B L)
    (hh : 0 < h ∧ h ≤ 1) :
    let mu := volume.restrict (cube d)
    let e := radialPropensity x₀ γ
    let p₀ : (Fin d → ℝ) → ℝ := fun _ => baselineSuccess B L
    let pF := pairSuccess false x₀ β B L a h
    let pT := pairSuccess true x₀ β B L a h
    let PF := (mu.bind (completionAt B e p₀ pF)).map observed
    let PT := (mu.bind (completionAt B e p₀ pT)).map observed
    InformationTheory.klDiv PF PT ≤
      ENNReal.ofReal ((2 / baselineSuccess B L) * (a * h ^ β) ^ 2 *
        (((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)))) *
      ENNReal.ofReal ((2 * h) ^ d) := by
  dsimp
  let mu := volume.restrict (cube d)
  letI : IsProbabilityMeasure mu := uniformCube_probability_lowerPair d
  let e := radialPropensity x₀ γ
  let p₀ : (Fin d → ℝ) → ℝ := fun _ => baselineSuccess B L
  let pF := pairSuccess false x₀ β B L a h
  let pT := pairSuccess true x₀ β B L a h
  have he : Measurable e := radialPropensity_measurable x₀ γ
  have hp₀ : Measurable p₀ := measurable_const
  have hpF : Measurable pF := pairSuccess_measurable false x₀ β B L a h
  have hpT : Measurable pT := pairSuccess_measurable true x₀ β B L a h
  have hvalidF : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      pF x ∈ Set.Icc 0 1 := by
    intro x
    exact ⟨radialPropensity_mem_Icc x₀ x γ hγ,
      by simpa [p₀, pF, pairSuccess] using
        pairSuccess_mem_Icc_of_small false x₀ β B L a h hB hL hβ ha
          ⟨hh.1.le, hh.2⟩ x,
      pairSuccess_mem_Icc_of_small false x₀ β B L a h hB hL hβ ha
        ⟨hh.1.le, hh.2⟩ x⟩
  have hvalidT : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      pT x ∈ Set.Icc 0 1 := by
    intro x
    exact ⟨radialPropensity_mem_Icc x₀ x γ hγ,
      by simpa [p₀, pF, pairSuccess] using
        pairSuccess_mem_Icc_of_small false x₀ β B L a h hB hL hβ ha
          ⟨hh.1.le, hh.2⟩ x,
      pairSuccess_mem_Icc_of_small true x₀ β B L a h hB hL hβ ha
        ⟨hh.1.le, hh.2⟩ x⟩
  have hcF : Measurable (completionAt B e p₀ pF) :=
    completionAt_measurable_of_measurable B e p₀ pF he hp₀ hpF hvalidF
  have hcT : Measurable (completionAt B e p₀ pT) :=
    completionAt_measurable_of_measurable B e p₀ pT he hp₀ hpT hvalidT
  let kF : ProbabilityTheory.Kernel (Fin d → ℝ) (Obs d) :=
    (ProbabilityTheory.Kernel.mk (completionAt B e p₀ pF) hcF).map observed
  let kT : ProbabilityTheory.Kernel (Fin d → ℝ) (Obs d) :=
    (ProbabilityTheory.Kernel.mk (completionAt B e p₀ pT) hcT).map observed
  letI : ProbabilityTheory.IsMarkovKernel kF := ⟨fun x => by
    dsimp [kF]
    rw [ProbabilityTheory.Kernel.map_apply _ (by unfold observed; fun_prop)]
    letI := completionAt_probability B e p₀ pF x
      (hvalidF x).1 (hvalidF x).2.1 (hvalidF x).2.2
    exact Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)⟩
  letI : ProbabilityTheory.IsMarkovKernel kT := ⟨fun x => by
    dsimp [kT]
    rw [ProbabilityTheory.Kernel.map_apply _ (by unfold observed; fun_prop)]
    letI := completionAt_probability B e p₀ pT x
      (hvalidT x).1 (hvalidT x).2.1 (hvalidT x).2.2
    exact Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)⟩
  have hPF : (mu.bind (completionAt B e p₀ pF)).map observed = mu.bind kF := by
    simpa [kF] using Measure.map_comp mu
      (ProbabilityTheory.Kernel.mk (completionAt B e p₀ pF) hcF)
      (by unfold observed; fun_prop)
  have hPT : (mu.bind (completionAt B e p₀ pT)).map observed = mu.bind kT := by
    simpa [kT] using Measure.map_comp mu
      (ProbabilityTheory.Kernel.mk (completionAt B e p₀ pT) hcT)
      (by unfold observed; fun_prop)
  rw [hPF, hPT]
  have hfib (p₁ : (Fin d → ℝ) → ℝ)
      (k : ProbabilityTheory.Kernel (Fin d → ℝ) (Obs d))
      (hk : ∀ x, (k x) = (completionAt B e p₀ p₁ x).map observed) :
      ∀ᵐ x ∂mu, (k x) {z | z.1 = x}ᶜ = 0 := by
    filter_upwards with x
    rw [hk x, Measure.map_apply (by unfold observed; fun_prop) (by measurability)]
    unfold completionAt
    rw [Measure.map_apply (by
      have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
          if z.1 then z.2.2 else z.2.1) :=
        Measurable.ite (measurable_fst (MeasurableSet.singleton true))
          (by fun_prop) (by fun_prop)
      fun_prop (disch := assumption)) (by measurability)]
    have hset : (fun z : Bool × ℝ × ℝ =>
        (x, z.1, z.2.1, z.2.2, if z.1 then z.2.2 else z.2.1)) ⁻¹'
          observed ⁻¹' {z : Obs d | z.1 = x}ᶜ = ∅ := by
      ext a
      simp [observed]
    rw [hset, measure_empty]
  have hkF : ∀ x, kF x = (completionAt B e p₀ pF x).map observed := by
    intro x
    rw [show kF x = (completionAt B e p₀ pF x).map observed by
      exact ProbabilityTheory.Kernel.map_apply _ (by unfold observed; fun_prop) x]
  have hkT : ∀ x, kT x = (completionAt B e p₀ pT x).map observed := by
    intro x
    rw [show kT x = (completionAt B e p₀ pT x).map observed by
      exact ProbabilityTheory.Kernel.map_apply _ (by unfold observed; fun_prop) x]
  have hfinite : ∀ x, InformationTheory.klDiv (kF x) (kT x) ≠ ⊤ := by
    intro x
    apply ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    rw [hkF x, hkT x]
    simpa [e, p₀, pF, pT] using
      lowerPair_completionAt_observed_klDiv_le x₀ x B L β γ a h hβ hB hL hγ ha hh
  have hac : ∀ᵐ x ∂mu, kF x ≪ kT x :=
    Filter.Eventually.of_forall fun x => (InformationTheory.klDiv_ne_top_iff.mp (hfinite x)).1
  rw [Causalean.Mathlib.InformationTheory.Measure.klDiv_bind_eq_of_base_recording
    mu kF kT Prod.fst measurable_fst (by measurability)
    (hfib pF kF hkF) (hfib pT kT hkT) hac]
  let E : Set (Fin d → ℝ) := {x | ∀ i, |x i - x₀ i| < h}
  have hE : MeasurableSet E := by
    dsimp [E]
    measurability
  let M := (2 / baselineSuccess B L) * (a * h ^ β) ^ 2 *
    (((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)))
  calc
    (∫⁻ x, InformationTheory.klDiv (kF x) (kT x) ∂mu) ≤
        ∫⁻ x, E.indicator (fun _ => ENNReal.ofReal M) x ∂mu := by
      apply lintegral_mono
      intro x
      by_cases hxE : x ∈ E
      · rw [Set.indicator_of_mem hxE]
        change InformationTheory.klDiv (kF x) (kT x) ≤ _
        rw [hkF x, hkT x]
        calc
          _ ≤ ENNReal.ofReal ((2 / baselineSuccess B L) * (a * h ^ β) ^ 2) *
              ENNReal.ofReal (e x) := by
            simpa [e, p₀, pF, pT] using
              lowerPair_completionAt_observed_klDiv_le x₀ x B L β γ a h
                hβ hB hL hγ ha hh
          _ ≤ ENNReal.ofReal ((2 / baselineSuccess B L) * (a * h ^ β) ^ 2) *
              ENNReal.ofReal (((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1))) := by
            gcongr
            exact radialPropensity_le_on_radius x₀ x γ h hγ
              ((pi_norm_le_iff_of_nonneg hh.1.le).2 fun i => le_of_lt (hxE i))
          _ = ENNReal.ofReal M := by
            rw [← ENNReal.ofReal_mul (by unfold baselineSuccess; positivity)]
      · rw [Set.indicator_of_notMem hxE]
        have heq : pF x = pT x := by
          by_contra hne
          exact hxE (pairSuccess_difference_support x₀ x β B L a h hh.1 (Ne.symm hne))
        change InformationTheory.klDiv (kF x) (kT x) ≤ 0
        have hkEq : kF x = kT x := by
          rw [hkF x, hkT x]
          unfold completionAt
          rw [heq]
        rw [hkEq, InformationTheory.klDiv_self]
    _ = ENNReal.ofReal M * mu E := by
      rw [lintegral_indicator hE, setLIntegral_const]
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal ((2 * h) ^ d) := by
      gcongr
      apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
        (pow_nonneg (mul_nonneg (by norm_num) hh.1.le) _)).2
      change mu.real E ≤ (2 * h) ^ d
      calc
        mu.real E ≤ mu.real {x | ‖x - x₀‖ ≤ h} := by
          apply measureReal_mono _ (measure_ne_top _ _)
          intro x hx
          exact (pi_norm_le_iff_of_nonneg hh.1.le).2 fun i =>
            (le_of_lt (hx i))
        _ = radialCDF x₀ h := uniformCube_radius_sublevel_real x₀ hx₀ h hh.1.le
        _ ≤ (2 * h) ^ d := radialCDF_le_cube_radius_volume x₀ h hh.1.le

/-- [For the stated inputs and conditions](hyp:d,β,γ,a,h,hh,hγ), [the asserted conclusion holds](goal). -/

lemma lowerPair_raw_rate_identity (d : ℕ) (β γ a h : ℝ)
    (hh : 0 < h) (hγ : 1 < γ) :
    (a * h ^ β) ^ 2 * (((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1))) *
        ((2 * h) ^ d) =
      2 ^ (effectiveDimension d γ) * a ^ 2 *
        h ^ (2 * β + effectiveDimension d γ) := by
  rw [show (a * h ^ β) ^ 2 = a ^ 2 * h ^ (2 * β) by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast (x := h ^ β) (n := 2),
      ← Real.rpow_mul hh.le]
    ring]
  rw [← Real.rpow_natCast (x := 2 * h) (n := d)]
  rw [← Real.rpow_mul (mul_nonneg (by norm_num) hh.le)]
  rw [show a ^ 2 * h ^ (2 * β) * (2 * h) ^
      ((d : ℝ) * (1 / (γ - 1))) * (2 * h) ^ (d : ℝ) =
      a ^ 2 * h ^ (2 * β) * ((2 * h) ^ ((d : ℝ) * (1 / (γ - 1))) *
        (2 * h) ^ (d : ℝ)) by ring]
  rw [← Real.rpow_add (mul_pos (by norm_num) hh)]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hh.le]
  rw [show a ^ 2 * h ^ (2 * β) *
      (2 ^ ((d : ℝ) * (1 / (γ - 1)) + d) *
        h ^ ((d : ℝ) * (1 / (γ - 1)) + d)) =
      2 ^ ((d : ℝ) * (1 / (γ - 1)) + d) * a ^ 2 *
        (h ^ (2 * β) * h ^ ((d : ℝ) * (1 / (γ - 1)) + d)) by ring]
  rw [← Real.rpow_add hh]
  unfold effectiveDimension
  have he : (d : ℝ) * (1 / (γ - 1)) + d = (d : ℝ) * γ / (γ - 1) := by
    field_simp [ne_of_gt (sub_pos.mpr hγ)]
    ring
  rw [he]

/-- [For the stated inputs and conditions](hyp:d,x₀,hx₀,B,L,β,γ,a,h,hβ,hB,hL,hγ,ha,hh), [the asserted conclusion holds](goal). -/

lemma lowerPair_observed_guards_and_kl_rate {d : ℕ}
    (x₀ : Fin d → ℝ) (hx₀ : x₀ ∈ cube d) (B L β γ a h : ℝ)
    (hβ : 0 < β) (hB : 0 < B) (hL : 0 < L) (hγ : 1 < γ)
    (ha : 0 ≤ a ∧ a ≤ baselineSuccess B L)
    (hh : 0 < h ∧ h ≤ 1) :
    let mu := volume.restrict (cube d)
    let e := radialPropensity x₀ γ
    let p₀ : (Fin d → ℝ) → ℝ := fun _ => baselineSuccess B L
    let pF := pairSuccess false x₀ β B L a h
    let pT := pairSuccess true x₀ β B L a h
    let PF := (mu.bind (completionAt B e p₀ pF)).map observed
    let PT := (mu.bind (completionAt B e p₀ pT)).map observed
    PF ≪ PT ∧ Integrable (llr PF PT) PF ∧
      (InformationTheory.klDiv PF PT).toReal ≤
        ((2 / baselineSuccess B L) * 2 ^ (effectiveDimension d γ)) *
          a ^ 2 * h ^ (2 * β + effectiveDimension d γ) := by
  dsimp
  have hraw := lowerPair_observed_klDiv_le_raw x₀ hx₀ B L β γ a h
    hβ hB hL hγ ha hh
  have htopR : ENNReal.ofReal ((2 / baselineSuccess B L) * (a * h ^ β) ^ 2 *
      (((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)))) *
      ENNReal.ofReal ((2 * h) ^ d) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hfin : InformationTheory.klDiv
      (((volume.restrict (cube d)).bind
        (completionAt B (radialPropensity x₀ γ) (fun _ => baselineSuccess B L)
          (pairSuccess false x₀ β B L a h))).map observed)
      (((volume.restrict (cube d)).bind
        (completionAt B (radialPropensity x₀ γ) (fun _ => baselineSuccess B L)
          (pairSuccess true x₀ β B L a h))).map observed) ≠ ⊤ :=
    ne_top_of_le_ne_top htopR hraw
  refine ⟨(InformationTheory.klDiv_ne_top_iff.mp hfin).1,
    (InformationTheory.klDiv_ne_top_iff.mp hfin).2, ?_⟩
  have hreal := ENNReal.toReal_mono htopR hraw
  have hMnonneg : 0 ≤ (2 / baselineSuccess B L) * (a * h ^ β) ^ 2 *
      (((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1))) :=
    mul_nonneg (mul_nonneg (by unfold baselineSuccess; positivity) (sq_nonneg _))
      (Real.rpow_nonneg (pow_nonneg (mul_nonneg (by norm_num) hh.1.le) _) _)
  have hpow : 0 ≤ (2 * h) ^ d := pow_nonneg (mul_nonneg (by norm_num) hh.1.le) _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hMnonneg,
    ENNReal.toReal_ofReal hpow] at hreal
  calc
      _ ≤ ((2 / baselineSuccess B L) * (a * h ^ β) ^ 2 *
          (((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1)))) * ((2 * h) ^ d) := hreal
      _ = _ := by
        rw [show (2 / baselineSuccess B L) * (a * h ^ β) ^ 2 *
            (((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1))) * ((2 * h) ^ d) =
            (2 / baselineSuccess B L) *
              ((a * h ^ β) ^ 2 * (((2 * h) ^ d) ^ ((1 : ℝ) / (γ - 1))) *
                ((2 * h) ^ d)) by ring,
          lowerPair_raw_rate_identity d β γ a h hh.1 hγ]
        ring

/-- [For the stated inputs and conditions](hyp:d,P,Q,h), [the asserted conclusion holds](goal). -/

lemma treatedRegression_eq_of_measure_eq {d : ℕ}
    (P Q : Measure (Obs d)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : P = Q) : treatedRegression P = treatedRegression Q := by
  subst Q
  rfl

/-- Identification makes the noncomputably selected response representative
agree on the cube with any displayed model witness for the same observed law. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,P,hP,Pc,μ,e,hEq,hmodel,x,hx), [the asserted conclusion holds](goal). -/
lemma responseOf_eq_given_model_response {d : ℕ} {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) (hP : P ∈ ModelClass d β B L C c_f γ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ e : (Fin d → ℝ) → ℝ) (hEq : P = Pc.map observed)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ e)
    (x : Fin d → ℝ) (hx : x ∈ cube d) :
    responseOf P hP x = μ x := by
  let Pc' : Measure (Completion d) := Classical.choose hP.2.2
  let hPc' := Classical.choose_spec hP.2.2
  let hpPc' : IsProbabilityMeasure Pc' := Classical.choose hPc'
  let hrest := Classical.choose_spec hPc'
  let μ' : (Fin d → ℝ) → ℝ := Classical.choose hrest
  let hrest' := Classical.choose_spec hrest
  let e' : (Fin d → ℝ) → ℝ := Classical.choose hrest'
  have hchosen := Classical.choose_spec hrest'
  letI : IsProbabilityMeasure Pc' := hpPc'
  have hP' : P = Pc'.map observed := hchosen.1
  have hmodel' : GlobalTailModel β B L C c_f γ Pc' μ' e' := hchosen.2
  have hid' := (mu1_eq_treatedRegression β B L C c_f γ Pc' μ' e'
    hP.1 hP.2.1 hmodel').2.1
  have hcont' : ContinuousOn μ' (cube d) :=
    hmodel'.smooth.1.regularity.continuousOn
  letI : IsProbabilityMeasure (Pc.map observed) :=
    Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  letI : IsProbabilityMeasure (Pc'.map observed) :=
    Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  have hid'given : ∀ᵐ y ∂covariateLaw (Pc.map observed),
      μ' y = treatedRegression (Pc.map observed) y := by
    have hmeasure : Pc.map observed = Pc'.map observed := hEq.symm.trans hP'
    have hcov : covariateLaw (Pc.map observed) =
        covariateLaw (Pc'.map observed) := congrArg covariateLaw hmeasure
    have htreat : treatedRegression (Pc.map observed) =
        treatedRegression (Pc'.map observed) := by
      exact treatedRegression_eq_of_measure_eq _ _ hmeasure
    rw [hcov]
    filter_upwards [hid'] with y hy
    rwa [htreat]
  have huniq := (mu1_eq_treatedRegression β B L C c_f γ Pc μ e
    hP.1 hP.2.1 hmodel).2.2 μ' hcont' hid'given x hx
  change μ' x = μ x
  exact huniq

/-- The exact completion witnesses underlying the two observed lower-pair laws. For [the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,a,c,x₀), [the `LowerPairExactModelWitness` object being defined](goal). -/
@[expose] def LowerPairExactModelWitness (d n : ℕ) (β B L C c_f γ a c : ℝ)
    (x₀ : Fin d → ℝ) : Prop :=
  ∃ (hF : IsProbabilityMeasure
      (lowerPairCompletion d n β B L γ a c x₀ false))
    (hT : IsProbabilityMeasure
      (lowerPairCompletion d n β B L γ a c x₀ true)),
    @GlobalTailModel d β B L C c_f γ
        (lowerPairCompletion d n β B L γ a c x₀ false) hF
        (fun x => B * pairSuccess false x₀ β B L a
          (c * oracleMesh d n β γ) x)
        (radialPropensity x₀ γ) ∧
      @GlobalTailModel d β B L C c_f γ
        (lowerPairCompletion d n β B L γ a c x₀ true) hT
        (fun x => B * pairSuccess true x₀ β B L a
          (c * oracleMesh d n β γ) x)
        (radialPropensity x₀ γ)

/-- Fixed admissible pair constants work at every positive sample size. The
KL and separation conditions are stated in the single-observation form used
by the Le Cam substrate; both laws have bounded potential outcomes. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,x₀,hd,hβ,hγ,hB,hL,hC,hcf,hx₀), [the asserted conclusion holds](goal). -/
lemma boundedLowerPair_spec_exact_completion (d : ℕ) (β B L C c_f γ : ℝ)
    (x₀ : Fin d → ℝ) -- @realizes x0(covariate evaluation point)
    (hd : 0 < d) (hβ : 1 < β) (hγ : 1 < γ)
    (hB : 0 < B) (hL : 0 < L) (hC : 1 ≤ C)
    (hcf : 0 < c_f ∧ c_f ≤ 1)
    (hx₀ : x₀ ∈ cube d) : -- @realizes x0(range in closed cube, including boundary)
    ∃ a c c₀ : ℝ, ∃ ha : 0 < a, ∃ hc : 0 < c, 0 < c₀ ∧
      boundedLowerPairAdmissible d β B L γ a c x₀ ∧
      ∀ n : ℕ, 1 ≤ n →
        let P₀ := boundedLowerPair d β B L γ a c x₀ ha hc false n
        let P₁ := boundedLowerPair d β B L γ a c x₀ ha hc true n
        ∃ (hP₀ : P₀ ∈ ModelClass d β B L C c_f γ)
          (hP₁ : P₁ ∈ ModelClass d β B L C c_f γ),
          (∀ j : Bool, ∀ᵐ ω ∂lowerPairCompletion d n β B L γ a c x₀ j,
            ω.2.2.1 ∈ ({0, B} : Set ℝ) ∧
              ω.2.2.2.1 ∈ ({0, B} : Set ℝ)) ∧
          P₀ ≪ P₁ ∧ Integrable (llr P₀ P₁) P₀ ∧
          (n : ℝ) * (_root_.InformationTheory.klDiv P₀ P₁).toReal ≤ 1 / 8 ∧
          c₀ * oracleRate d n β γ ≤
            |responseOf P₁ hP₁ x₀ - responseOf P₀ hP₀ x₀| ∧
          LowerPairExactModelWitness d n β B L C c_f γ a c x₀ := by
  open Causalean.Mathlib.Analysis.Calculus.CubeExtension in
    obtain ⟨A, hA, hscaled⟩ :=
      exists_uniform_scaledProductBump_holderBallOn (d := d) β (by linarith)
  let a := min (baselineSuccess B L / 2) (L / (4 * B * A))
  have hbase : 0 < baselineSuccess B L := by
    unfold baselineSuccess
    positivity
  have ha : 0 < a := by
    dsimp [a]
    apply lt_min
    · linarith
    · positivity
  have hale : a ≤ baselineSuccess B L :=
    (min_le_left _ _).trans (by linarith)
  let K := (2 / baselineSuccess B L) * 2 ^ (effectiveDimension d γ)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hD : 1 ≤ 2 * β + effectiveDimension d γ := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have heff : 0 ≤ effectiveDimension d γ := by
      unfold effectiveDimension
      positivity
    linarith
  obtain ⟨c, hc, hc1, hsmall⟩ := lowerPair_choose_kl_scale K a
    (2 * β + effectiveDimension d γ) hK hD
  let c₀ := B * a * c ^ β
  have hc₀ : 0 < c₀ := by
    dsimp [c₀]
    positivity
  have hadm : boundedLowerPairAdmissible d β B L γ a c x₀ :=
    boundedLowerPairAdmissible_of_small d β B L γ a c x₀
      hd hβ hB hL hγ ⟨ha, hale⟩ ⟨hc, hc1⟩
  refine ⟨a, c, c₀, ha, hc, hc₀, hadm, ?_⟩
  intro n hn
  let h := c * oracleMesh d n β γ
  let mu := volume.restrict (cube d)
  let e := radialPropensity x₀ γ
  let p₀ : (Fin d → ℝ) → ℝ := fun _ => baselineSuccess B L
  let pF := pairSuccess false x₀ β B L a h
  let pT := pairSuccess true x₀ β B L a h
  let PcF := mu.bind (completionAt B e p₀ pF)
  let PcT := mu.bind (completionAt B e p₀ pT)
  let PF := PcF.map observed
  let PT := PcT.map observed
  have hmesh := oracleMesh_mem_Ioc d n β γ
    ⟨Nat.succ_le_iff.mpr hd, hn, hβ, hγ⟩
  have hh : 0 < h ∧ h ≤ 1 := by
    dsimp [h]
    exact ⟨mul_pos hc hmesh.1,
      (by simpa using
        (mul_le_mul_of_nonneg_right hc1 hmesh.1.le).trans (by simpa using hmesh.2))⟩
  have he : Measurable e := radialPropensity_measurable x₀ γ
  have hp₀ : Measurable p₀ := measurable_const
  have hpF : Measurable pF := pairSuccess_measurable false x₀ β B L a h
  have hpT : Measurable pT := pairSuccess_measurable true x₀ β B L a h
  have hvalidF : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      pF x ∈ Set.Icc 0 1 := by
    intro x
    exact ⟨radialPropensity_mem_Icc x₀ x γ hγ,
      by simpa [p₀, pF, pairSuccess] using
        pairSuccess_mem_Icc_of_small false x₀ β B L a h hB hL (by linarith)
          ⟨ha.le, hale⟩ ⟨hh.1.le, hh.2⟩ x,
      pairSuccess_mem_Icc_of_small false x₀ β B L a h hB hL (by linarith)
        ⟨ha.le, hale⟩ ⟨hh.1.le, hh.2⟩ x⟩
  have hvalidT : ∀ x, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      pT x ∈ Set.Icc 0 1 := by
    intro x
    exact ⟨radialPropensity_mem_Icc x₀ x γ hγ,
      by simpa [p₀, pF, pairSuccess] using
        pairSuccess_mem_Icc_of_small false x₀ β B L a h hB hL (by linarith)
          ⟨ha.le, hale⟩ ⟨hh.1.le, hh.2⟩ x,
      pairSuccess_mem_Icc_of_small true x₀ β B L a h hB hL (by linarith)
        ⟨ha.le, hale⟩ ⟨hh.1.le, hh.2⟩ x⟩
  letI : IsProbabilityMeasure mu := uniformCube_probability_lowerPair d
  letI : IsProbabilityMeasure PcF := by
    apply isProbabilityMeasure_bind
      (completionAt_measurable_of_measurable B e p₀ pF he hp₀ hpF hvalidF).aemeasurable
    filter_upwards with x
    exact completionAt_probability B e p₀ pF x
      (hvalidF x).1 (hvalidF x).2.1 (hvalidF x).2.2
  letI : IsProbabilityMeasure PcT := by
    apply isProbabilityMeasure_bind
      (completionAt_measurable_of_measurable B e p₀ pT he hp₀ hpT hvalidT).aemeasurable
    filter_upwards with x
    exact completionAt_probability B e p₀ pT x
      (hvalidT x).1 (hvalidT x).2.1 (hvalidT x).2.2
  have hbaseBL : B * baselineSuccess B L ≤ L / 4 := by
    unfold baselineSuccess
    calc
      B * min (1 / 4) (L / (4 * B)) ≤ B * (L / (4 * B)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hB.le
      _ = L / 4 := by field_simp
  have hbaseabs : |B * baselineSuccess B L| ≤ L / 4 := by
    rw [abs_of_pos (mul_pos hB hbase)]
    exact hbaseBL
  have hamp : |B * a| * A ≤ L / 4 := by
    rw [abs_of_pos (mul_pos hB ha)]
    have hale' : a ≤ L / (4 * B * A) := min_le_right _ _
    have hpos : 0 < 4 * B * A := by positivity
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    calc
      B * a * A * 4 = a * (4 * B * A) := by ring
      _ ≤ (L / (4 * B * A)) * (4 * B * A) :=
        mul_le_mul_of_nonneg_right hale' hpos.le
      _ = L := by field_simp
  have hrad : |B * baselineSuccess B L| + |B * a| * A ≤ L := by
    linarith [hbaseabs, hamp, hL]
  have hballF : HolderBall β L (fun x => B * pF x) := by
    have hcball := constant_holderBall (d := d) β L (B * baselineSuccess B L)
      (by linarith) hL.le (hbaseabs.trans (by linarith))
    simpa [pF, pairSuccess] using hcball
  have hballT : HolderBall β L (fun x => B * pT x) := by
    exact pairSuccess_true_holderBall β B L a h x₀ (by linarith) hh.1 hh.2 A hA
      (hscaled h hh.1 hh.2 x₀) hrad
  have hholderF : HolderResponse PcF (fun x => B * pF x) β L :=
    completionBind_holderResponse mu B β L e p₀ pF he hp₀ hpF hvalidF hballF
  have hholderT : HolderResponse PcT (fun x => B * pT x) β L :=
    completionBind_holderResponse mu B β L e p₀ pT he hp₀ hpT hvalidT hballT
  have htail := radialPropensity_uniform_tail x₀ hx₀ hd γ hγ
  have hpos := radialPropensity_uniform_pos_ae x₀ hx₀ hd γ hγ
  have hmodelF : @GlobalTailModel d β B L C c_f γ PcF inferInstance
      (fun x => B * pF x) e :=
    completionBind_uniformCube_globalTailModel β B L C c_f γ hB hC hcf.2
      e p₀ pF (fun x => B * pF x) he hp₀ hpF hvalidF hpos htail hholderF
  have hmodelT : @GlobalTailModel d β B L C c_f γ PcT inferInstance
      (fun x => B * pT x) e :=
    completionBind_uniformCube_globalTailModel β B L C c_f γ hB hC hcf.2
      e p₀ pT (fun x => B * pT x) he hp₀ hpT hvalidT hpos htail hholderT
  have hdomain : ModelParameterDomain d β B L C c_f :=
    ⟨Nat.succ_le_iff.mpr hd, hβ, hB, hL, hC, hcf⟩
  let hPFmem : PF ∈ ModelClass d β B L C c_f γ :=
    ⟨hdomain, hγ, PcF, inferInstance, (fun x => B * pF x), e, rfl, hmodelF⟩
  let hPTmem : PT ∈ ModelClass d β B L C c_f γ :=
    ⟨hdomain, hγ, PcT, inferInstance, (fun x => B * pT x), e, rfl, hmodelT⟩
  change ∃ (hPF' : PF ∈ ModelClass d β B L C c_f γ)
    (hPT' : PT ∈ ModelClass d β B L C c_f γ), _
  refine ⟨hPFmem, hPTmem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact lowerPairCompletion_supported_on_endpoints d n β B L γ a c x₀ j hadm hn
  · exact (lowerPair_observed_guards_and_kl_rate x₀ hx₀ B L β γ a h
      (by linarith) hB hL hγ ⟨ha.le, hale⟩ hh).1
  · exact (lowerPair_observed_guards_and_kl_rate x₀ hx₀ B L β γ a h
      (by linarith) hB hL hγ ⟨ha.le, hale⟩ hh).2.1
  · have hrate := (lowerPair_observed_guards_and_kl_rate x₀ hx₀ B L β γ a h
        (by linarith) hB hL hγ ⟨ha.le, hale⟩ hh).2.2
    calc
      (n : ℝ) * (InformationTheory.klDiv PF PT).toReal ≤
          (n : ℝ) * (K * a ^ 2 * h ^ (2 * β + effectiveDimension d γ)) := by
        exact mul_le_mul_of_nonneg_left (by simpa [K] using hrate) (by positivity)
      _ = K * a ^ 2 * c ^ (2 * β + effectiveDimension d γ) := by
        dsimp [h]
        rw [show (n : ℝ) * (K * a ^ 2 *
            (c * oracleMesh d n β γ) ^ (2 * β + effectiveDimension d γ)) =
            K * a ^ 2 * ((n : ℝ) *
              (c * oracleMesh d n β γ) ^
                (2 * β + effectiveDimension d γ)) by ring,
          lowerPair_oracle_kl_balance d n β γ c (Nat.zero_lt_of_lt hn) hc.le
            (lt_of_lt_of_le zero_lt_one hD)]
      _ ≤ 1 / 8 := hsmall
  · have hrespF : responseOf PF hPFmem x₀ = B * pF x₀ :=
      responseOf_eq_given_model_response PF hPFmem PcF (fun x => B * pF x) e
        rfl hmodelF x₀ hx₀
    have hrespT : responseOf PT hPTmem x₀ = B * pT x₀ :=
      responseOf_eq_given_model_response PT hPTmem PcT (fun x => B * pT x) e
        rfl hmodelT x₀ hx₀
    change c₀ * oracleRate d n β γ ≤
      |responseOf PT hPTmem x₀ - responseOf PF hPFmem x₀|
    rw [hrespF, hrespT]
    have hsep := pairSuccess_oracle_separation (n := n) x₀ β B L γ a c hc.le
    dsimp [pF, pT, h, c₀]
    rw [← mul_sub]
    rw [hsep]
    simpa [mul_assoc] using
      (le_abs_self (B * a * c ^ β * oracleRate d n β γ))
  · have hprobF : IsProbabilityMeasure
        (lowerPairCompletion d n β B L γ a c x₀ false) := by
      simpa [PcF, h, lowerPairCompletion] using
        (inferInstance : IsProbabilityMeasure PcF)
    have hprobT : IsProbabilityMeasure
        (lowerPairCompletion d n β B L γ a c x₀ true) := by
      simpa [PcT, h, lowerPairCompletion] using
        (inferInstance : IsProbabilityMeasure PcT)
    refine ⟨hprobF, hprobT, ?_, ?_⟩
    · simpa [PcF, pF, e, h, lowerPairCompletion] using hmodelF
    · simpa [PcT, pT, e, h, lowerPairCompletion] using hmodelT

/-- [The compatibility wrapper](goal) retaining the original lower-pair API for
[the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,x₀,hd,hβ,hγ,hB,hL,hC,hcf,hx₀). -/
-- @node: lem:bounded-lower-pair
lemma boundedLowerPair_spec (d : ℕ) (β B L C c_f γ : ℝ)
    (x₀ : Fin d → ℝ)
    (hd : 0 < d) (hβ : 1 < β) (hγ : 1 < γ)
    (hB : 0 < B) (hL : 0 < L) (hC : 1 ≤ C)
    (hcf : 0 < c_f ∧ c_f ≤ 1)
    (hx₀ : x₀ ∈ cube d) :
    ∃ a c c₀ : ℝ, ∃ ha : 0 < a, ∃ hc : 0 < c, 0 < c₀ ∧
      boundedLowerPairAdmissible d β B L γ a c x₀ ∧
      ∀ n : ℕ, 1 ≤ n →
        let P₀ := boundedLowerPair d β B L γ a c x₀ ha hc false n
        let P₁ := boundedLowerPair d β B L γ a c x₀ ha hc true n
        ∃ (hP₀ : P₀ ∈ ModelClass d β B L C c_f γ)
          (hP₁ : P₁ ∈ ModelClass d β B L C c_f γ),
          (∀ j : Bool, ∀ᵐ ω ∂lowerPairCompletion d n β B L γ a c x₀ j,
            ω.2.2.1 ∈ ({0, B} : Set ℝ) ∧
              ω.2.2.2.1 ∈ ({0, B} : Set ℝ)) ∧
          P₀ ≪ P₁ ∧ Integrable (llr P₀ P₁) P₀ ∧
          (n : ℝ) * (_root_.InformationTheory.klDiv P₀ P₁).toReal ≤ 1 / 8 ∧
          c₀ * oracleRate d n β γ ≤
            |responseOf P₁ hP₁ x₀ - responseOf P₀ hP₀ x₀| := by
  obtain ⟨a, c, c₀, ha, hc, hc₀, hadm, hall⟩ :=
    boundedLowerPair_spec_exact_completion d β B L C c_f γ x₀
      hd hβ hγ hB hL hC hcf hx₀
  refine ⟨a, c, c₀, ha, hc, hc₀, hadm, ?_⟩
  intro n hn
  obtain ⟨hP₀, hP₁, hsupp, hac, hint, hkl, hsep, -⟩ := hall n hn
  exact ⟨hP₀, hP₁, hsupp, hac, hint, hkl, hsep⟩
end CausalSmith.Stat.WeakOverlap

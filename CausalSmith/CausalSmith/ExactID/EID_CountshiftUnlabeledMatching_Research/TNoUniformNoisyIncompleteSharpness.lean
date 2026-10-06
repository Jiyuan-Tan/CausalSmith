module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.ChiSquaredObservation
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.GaussianLikelihood
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.NoisyIncompleteCommonKernel
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.NoisyIncompleteTargets
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.NoisyIncompleteStructural
public import Causalean.Stat.Minimax.ChiSquared
public import Causalean.Stat.Minimax.Mixture.Iid
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Duplicate-baseline lower bound for honest incomplete-cover target sets. -/

public section

open MeasureTheory ProbabilityTheory

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

-- @node: exp_log_sixteenth_ratio_le
lemma exp_log_sixteenth_ratio_le (p : ℕ) (hp : 4 ≤ p) (x : ℝ)
    (hx : x ≤ Real.log p / 16) :
    (Real.exp x - 1) / ((p : ℝ) - 1) ≤ 1 / 16 := by
  have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPos : (0 : ℝ) < p := by positivity
  have hden : (0 : ℝ) < p - 1 := by linarith
  have hpow : (p : ℝ) ^ (1 / 16 : ℝ) ≤
      1 + (1 / 16 : ℝ) * ((p : ℝ) - 1) := by
    convert rpow_one_add_le_one_add_mul_self
      (s := (p : ℝ) - 1) (p := (1 / 16 : ℝ)) (by linarith)
      (by norm_num) (by norm_num) using 1
    ring_nf
  have hexp : Real.exp x ≤ (p : ℝ) ^ (1 / 16 : ℝ) := by
    calc
      Real.exp x ≤ Real.exp (Real.log p / 16) := Real.exp_le_exp.mpr hx
      _ = (p : ℝ) ^ (1 / 16 : ℝ) := by
        rw [Real.rpow_def_of_pos hpPos]
        congr 1
        ring
  apply (div_le_iff₀ hden).2
  nlinarith

-- @node: small_rate_confidence_numeric
lemma small_rate_confidence_numeric (p n : ℕ) (h γ : ℝ)
    (hp : 4 ≤ p) (hγ : γ ≤ 1 / 8)
    (hrate : (n : ℝ) * h ^ 2 ≤ Real.log p / 16) :
    5 / 8 ≤ 1 - 2 * γ - (1 / 2) *
      Real.sqrt ((Real.exp ((n : ℝ) * h ^ 2) - 1) / ((p : ℝ) - 1)) := by
  have hratio := exp_log_sixteenth_ratio_le p hp ((n : ℝ) * h ^ 2) hrate
  have hsqrt := Real.sqrt_le_sqrt hratio
  have hsqrt' : Real.sqrt ((Real.exp ((n : ℝ) * h ^ 2) - 1) /
      ((p : ℝ) - 1)) ≤ 1 / 4 := by
    have hsqrt16 : Real.sqrt (16 : ℝ) = 4 := by
      convert Real.sqrt_sq (show (0 : ℝ) ≤ 4 by norm_num) using 1; norm_num
    simpa [hsqrt16] using hsqrt
  linarith

/-- The two coverage events force a nonsingleton event under the baseline. -/
-- @node: confidence_intersection_from_tv
lemma confidence_intersection_from_tv {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (A B G : Set α) (hB : MeasurableSet B)
    (hsub : A ∩ B ⊆ G) (γ t : ℝ)
    (hPA : 1 - γ ≤ P.real A) (hQB : 1 - γ ≤ Q.real B)
    (hTV : Causalean.Stat.tvDist Q P ≤ t) :
    1 - 2 * γ - t ≤ P.real G := by
  have hgap := Causalean.Stat.measureReal_sub_le_tvDist
    (μ := P) (ν := Q) hB
  rw [Causalean.Stat.tvDist_symm] at hgap
  have hBbase : 1 - γ - t ≤ P.real B := by linarith
  have hunion := measureReal_union_add_inter (μ := P) (s := A) (t := B) hB
  have hunionle : P.real (A ∪ B) ≤ 1 := by
    simpa only [probReal_univ] using
      (measureReal_mono (μ := P) (Set.subset_univ _) (measure_ne_top P _))
  have hinter : 1 - 2 * γ - t ≤ P.real (A ∩ B) := by linarith
  exact hinter.trans (measureReal_mono hsub (measure_ne_top P _))

/-- Baseline and mixture coverage, together with a chi-squared bound, force a
confidence set to contain at least two labels at the baseline. -/
-- @node: confidence_nonsingleton_of_chiSq
lemma confidence_nonsingleton_of_chiSq {α : Type*} [MeasurableSpace α]
    {p : ℕ} [NeZero p] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Ĉ : α → Finset (Fin p)) (hĈ : Measurable Ĉ)
    (γ R : ℝ) (hbase : P {y | (0 : Fin p) ∈ Ĉ y} ≥ ENNReal.ofReal (1 - γ))
    (halt : Q {y | ∃ j : Fin p, j ≠ 0 ∧ j ∈ Ĉ y} ≥ ENNReal.ofReal (1 - γ))
    (hac : Q ≪ P)
    (hint : Integrable (fun x => ((Q.rnDeriv P x).toReal - 1) ^ 2) P)
    (hchi : Causalean.Stat.chiSqDiv Q P ≤ R) :
    P {y | 2 ≤ (Ĉ y).card} ≥ ENNReal.ofReal (1 - 2 * γ - (1 / 2) * Real.sqrt R) := by
  let A : Set α := {y | (0 : Fin p) ∈ Ĉ y}
  let B : Set α := {y | ∃ j : Fin p, j ≠ 0 ∧ j ∈ Ĉ y}
  let G : Set α := {y | 2 ≤ (Ĉ y).card}
  have hB : MeasurableSet B := by
    change MeasurableSet (Ĉ ⁻¹' {s | ∃ j : Fin p, j ≠ 0 ∧ j ∈ s})
    exact hĈ (MeasurableSet.of_discrete)
  have hsub : A ∩ B ⊆ G := by
    intro y hy
    rcases hy with ⟨hy0, j, hj, hyj⟩
    exact Finset.one_lt_card.mpr ⟨0, hy0, j, hyj, Ne.symm hj⟩
  have htv := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv Q P hac hint
  have htvR : Causalean.Stat.tvDist Q P ≤ (1 / 2) * Real.sqrt R := by
    exact htv.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hchi) (by norm_num))
  have hPA : 1 - γ ≤ P.real A := by
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top P A)).mp hbase
  have hQB : 1 - γ ≤ Q.real B := by
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top Q B)).mp halt
  have h := confidence_intersection_from_tv P Q A B G hB hsub γ
    ((1 / 2) * Real.sqrt R) hPA hQB htvR
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top P G)).mpr h

/-- A uniform finite mixture inherits a coverage lower bound shared by every
nonbaseline component. -/
-- @node: uniformAltMixture_coverage
lemma uniformAltMixture_coverage {α : Type*} [MeasurableSpace α]
    {p : ℕ} [NeZero p] (P : Fin p → Measure α) (B : Set α)
    (c : ENNReal) (hp : 2 ≤ p)
    (h : ∀ j : Fin p, j ≠ 0 → c ≤ P j B) :
    c ≤ uniformAltMixture P B := by
  let s : Finset (Fin p) := Finset.univ.filter (· ≠ 0)
  have hs : s.card = p - 1 := by
    simp [s, Finset.filter_ne', Finset.card_erase_of_mem]
  have hcalc : uniformAltMixture P B =
      ∑ j ∈ s, (((p - 1 : ℕ) : ENNReal)⁻¹ * P j B) := by
    simp [uniformAltMixture, s, smul_eq_mul]
  rw [hcalc]
  calc
    c = ∑ j ∈ s, (((p - 1 : ℕ) : ENNReal)⁻¹ * c) := by
      simp only [ENNReal.natCast_sub, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, hs]
      have hne : ((p : ENNReal) - 1) ≠ 0 := by
        have hh : ((p - 1 : ℕ) : ENNReal) ≠ 0 := by
          exact_mod_cast (show p - 1 ≠ 0 by omega)
        simpa only [ENNReal.natCast_sub, Nat.cast_one] using hh
      exact (ENNReal.mul_inv_cancel_left hne
        (ENNReal.sub_ne_top (ENNReal.natCast_ne_top p))).symm
    _ ≤ ∑ j ∈ s, (((p - 1 : ℕ) : ENNReal)⁻¹ * P j B) := by
      apply Finset.sum_le_sum
      intro j hj
      gcongr
      exact h j ((Finset.mem_filter.mp hj).2)

/-- The uniform mixture of the nonbaseline experiments is a probability law. -/
-- @node: uniformAltMixture_probability
lemma uniformAltMixture_probability {α : Type*} [MeasurableSpace α]
    {p : ℕ} [NeZero p] (P : Fin p → Measure α)
    (hp : 2 ≤ p) (hP : ∀ j, IsProbabilityMeasure (P j)) :
    IsProbabilityMeasure (uniformAltMixture P) := by
  let s : Finset (Fin p) := Finset.univ.filter (· ≠ 0)
  have hs : s.card = p - 1 := by
    simp [s, Finset.filter_ne', Finset.card_erase_of_mem]
  refine ⟨?_⟩
  change (∑ j ∈ s, (((p - 1 : ℕ) : ENNReal)⁻¹) • P j) Set.univ = 1
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, (hP _).measure_univ, smul_eq_mul,
    mul_one, Finset.sum_const, hs, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast (show p - 1 ≠ 0 by omega))
    (ENNReal.natCast_ne_top (p - 1))

/-- Domination of each alternative passes to their finite uniform mixture. -/
-- @node: uniformAltMixture_absolutelyContinuous
lemma uniformAltMixture_absolutelyContinuous {α : Type*} [MeasurableSpace α]
    {p : ℕ} [NeZero p] (P : Fin p → Measure α) (Q : Measure α)
    (h : ∀ j, j ≠ 0 → P j ≪ Q) : uniformAltMixture P ≪ Q := by
  let s : Finset (Fin p) := Finset.univ.filter (· ≠ 0)
  have hsum (t : Finset (Fin p)) (ht : t ⊆ s) :
      (∑ j ∈ t, (((p - 1 : ℕ) : ENNReal)⁻¹) • P j) ≪ Q := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert j t hj ih =>
        have hjQ : P j ≪ Q := h j ((Finset.mem_filter.mp (ht (Finset.mem_insert_self j t))).2)
        have ht' : t ⊆ s := Finset.Subset.trans (Finset.subset_insert j t) ht
        simpa [Finset.sum_insert hj] using
          Measure.AbsolutelyContinuous.add_left
            (hjQ.smul_left (((p - 1 : ℕ) : ENNReal)⁻¹)) (ih ht')
  exact hsum s (Finset.Subset.refl s)

/-- The finite experiment's coverage and chi-squared conditions imply both
confidence-set lower bounds. -/
-- @node: noisyIncomplete_confidence_consequence
lemma noisyIncomplete_confidence_consequence
    (p n : ℕ) [NeZero p] (h : ℝ) (hp : 4 ≤ p)
    (P : Fin p → Measure (ObservedSample p n))
    (hP : ∀ j, IsProbabilityMeasure (P j))
    (hac : uniformAltMixture P ≪ P 0)
    (hint : Integrable (fun x =>
      (((uniformAltMixture P).rnDeriv (P 0) x).toReal - 1) ^ 2) (P 0))
    (hchi : Causalean.Stat.chiSqDiv (uniformAltMixture P) (P 0) ≤
      (Real.exp (n * h ^ 2) - 1) / (p - 1)) :
    (∀ γ : ℝ, 0 < γ → γ ≤ 1 / 8 →
      ∀ Ĉ : ObservedSample p n → Finset (Fin p), Measurable Ĉ →
        (∀ j : Fin p,
          P j {y | (if j = 0 then (0 : Fin p) else j) ∈ Ĉ y} ≥
            ENNReal.ofReal (1 - γ)) →
        P 0 {y | 2 ≤ (Ĉ y).card} ≥
          ENNReal.ofReal (1 - 2 * γ - (1 / 2) *
            Real.sqrt ((Real.exp (n * h ^ 2) - 1) / (p - 1)))) ∧
    ((n : ℝ) * h ^ 2 ≤ Real.log p / 16 →
      ∀ γ : ℝ, 0 < γ → γ ≤ 1 / 8 →
        ∀ Ĉ : ObservedSample p n → Finset (Fin p), Measurable Ĉ →
          (∀ j : Fin p,
            P j {y | (if j = 0 then (0 : Fin p) else j) ∈ Ĉ y} ≥
              ENNReal.ofReal (1 - γ)) →
          P 0 {y | 2 ≤ (Ĉ y).card} ≥ ENNReal.ofReal (5 / 8)) := by
  haveI := hP 0
  haveI := uniformAltMixture_probability P (by omega) hP
  have hmain : ∀ γ : ℝ, 0 < γ → γ ≤ 1 / 8 →
      ∀ Ĉ : ObservedSample p n → Finset (Fin p), Measurable Ĉ →
        (∀ j : Fin p,
          P j {y | (if j = 0 then (0 : Fin p) else j) ∈ Ĉ y} ≥
            ENNReal.ofReal (1 - γ)) →
        P 0 {y | 2 ≤ (Ĉ y).card} ≥
          ENNReal.ofReal (1 - 2 * γ - (1 / 2) *
            Real.sqrt ((Real.exp (n * h ^ 2) - 1) / (p - 1))) := by
    intro γ _ _ Ĉ hĈ hcov
    let B : Set (ObservedSample p n) :=
      {y | ∃ j : Fin p, j ≠ 0 ∧ j ∈ Ĉ y}
    have halt : (uniformAltMixture P) B ≥ ENNReal.ofReal (1 - γ) := by
      apply uniformAltMixture_coverage P B _ (by omega)
      intro j hj
      have hjcov := hcov j
      simp only [if_neg hj] at hjcov
      exact hjcov.trans (measure_mono (show {y | j ∈ Ĉ y} ⊆ B from by
        intro y hy
        exact ⟨j, hj, hy⟩))
    have hbase := hcov (0 : Fin p)
    simpa only [if_pos rfl] using
      (confidence_nonsingleton_of_chiSq (P 0) (uniformAltMixture P) Ĉ hĈ γ
        ((Real.exp (n * h ^ 2) - 1) / (p - 1)) hbase halt hac hint hchi)
  refine ⟨hmain, ?_⟩
  intro hrate γ hγ hγ' Ĉ hĈ hcov
  have hnum := small_rate_confidence_numeric p n h γ hp hγ' hrate
  exact (ENNReal.ofReal_le_ofReal hnum).trans (hmain γ hγ hγ' Ĉ hĈ hcov)

/-- The single directed edge in the alternative structural model is nilpotent. -/
-- @node: alternative_shear_square_zero
lemma alternative_shear_square_zero {p : ℕ} [NeZero p]
    (j : Fin p) (hj : j ≠ 0) (b : ℝ) :
    (Matrix.single 0 j b : Matrix (Fin p) (Fin p) ℝ) *
      Matrix.single 0 j b = 0 := by
  simpa using Matrix.single_mul_single_of_ne b 0 j 0 hj b

/-- The alternative's sole possible arrow runs from `j` to `0`, so it
cannot lie on a directed cycle. -/
-- @node: alternative_shear_acyclic
lemma alternative_shear_acyclic {p : ℕ} [NeZero p]
    (j : Fin p) (hj : j ≠ 0) (b : ℝ) :
    AcyclicMechanism (Matrix.single 0 j b : Matrix (Fin p) (Fin p) ℝ) := by
  constructor
  · intro i
    simp only [Matrix.single_apply]
    split_ifs with hi
    · exact False.elim (hj (hi.2.trans hi.1.symm))
    · rfl
  · intro i hcycle
    let R : Fin p → Fin p → Prop :=
      fun x y => (Matrix.single 0 j b : Matrix (Fin p) (Fin p) ℝ) y x ≠ 0
    have hedge {x y : Fin p} (hxy : R x y) : x = j ∧ y = 0 := by
      dsimp [R] at hxy
      by_cases he : 0 = y ∧ j = x
      · exact ⟨he.2.symm, he.1.symm⟩
      · simp [he] at hxy
    have hno : ∀ y, ¬ R 0 y := by
      intro y h
      exact hj (hedge h).1.symm
    obtain ⟨k, hik, hki⟩ := Relation.TransGen.head'_iff.mp hcycle
    obtain ⟨hi, hk⟩ := hedge hik
    have heq : j = (0 : Fin p) := by
      rw [hi, hk] at hki
      exact (Relation.reflTransGen_iff_eq hno).mp hki
    exact hj heq

/-- The inverse structural map for a single off-diagonal edge is its
identity-plus-shear total-effect matrix. -/
-- @node: alternative_shear_totalEffect
lemma alternative_shear_totalEffect {p : ℕ} [NeZero p]
    (j : Fin p) (hj : j ≠ 0) (b : ℝ) :
    totalEffect (Matrix.single 0 j b : Matrix (Fin p) (Fin p) ℝ) =
      1 + Matrix.single 0 j b := by
  let S : Matrix (Fin p) (Fin p) ℝ := Matrix.single 0 j b
  have hS : S * S = 0 := alternative_shear_square_zero j hj b
  have hprod : (1 - S) * (1 + S) = 1 := by
    calc
      (1 - S) * (1 + S) = 1 - S * S := by noncomm_ring
      _ = 1 := by rw [hS]; simp
  have hunit : IsUnit (1 - S).det := Matrix.isUnit_det_of_right_inverse hprod
  change (1 - S)⁻¹ = 1 + S
  calc
    (1 - S)⁻¹ = (1 - S)⁻¹ * ((1 - S) * (1 + S)) := by rw [hprod, mul_one]
    _ = ((1 - S)⁻¹ * (1 - S)) * (1 + S) := (mul_assoc ..).symm
    _ = 1 + S := by rw [Matrix.nonsing_inv_mul _ hunit, one_mul]

/-- The shear disturbance covariance is positive definite and becomes the
identity covariance after propagation through the structural inverse. -/
-- @node: alternative_shear_covariance
lemma alternative_shear_covariance {p : ℕ} [NeZero p]
    (j : Fin p) (hj : j ≠ 0) (b : ℝ) :
    let D : Matrix (Fin p) (Fin p) ℝ := 1 - Matrix.single 0 j b
    let B : Matrix (Fin p) (Fin p) ℝ := totalEffect (Matrix.single 0 j b)
    (D * D.transpose).PosDef ∧ B * (D * D.transpose) * B.transpose = 1 := by
  dsimp
  let S : Matrix (Fin p) (Fin p) ℝ := Matrix.single 0 j b
  have hS : S * S = 0 := alternative_shear_square_zero j hj b
  have hBD : (1 + S) * (1 - S) = 1 := by
    calc
      (1 + S) * (1 - S) = 1 - S * S := by noncomm_ring
      _ = 1 := by rw [hS]; simp
  have hDB : (1 - S) * (1 + S) = 1 := by
    calc
      (1 - S) * (1 + S) = 1 - S * S := by noncomm_ring
      _ = 1 := by rw [hS]; simp
  have hunit : IsUnit (1 - S) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse hDB)
  constructor
  · simpa [S, Matrix.star_eq_conjTranspose] using
      (Matrix.IsUnit.posDef_star_right_conjugate_iff hunit).mpr Matrix.PosDef.one
  · rw [alternative_shear_totalEffect j hj b]
    change (1 + S) * ((1 - S) * (1 - S).transpose) * (1 + S).transpose = 1
    rw [← mul_assoc, hBD, one_mul, ← Matrix.transpose_mul, hBD,
      Matrix.transpose_one]

/-- The alternative's total effect at the affected non-target coordinate
equals the reciprocal edge weight. -/
-- @node: alternative_shear_nontarget_effect
lemma alternative_shear_nontarget_effect {p : ℕ} [NeZero p]
    (j : Fin p) (hj : j ≠ 0) (b : ℝ) :
    totalEffect (Matrix.single 0 j b : Matrix (Fin p) (Fin p) ℝ) 0 j = b := by
  rw [alternative_shear_totalEffect j hj b]
  simp [Matrix.add_apply, eq_comm, hj]

/-- A shift of strength `h` at the new target produces the asserted
two-coordinate latent mean shift in the shear model. -/
-- @node: alternative_shear_shift
lemma alternative_shear_shift {p : ℕ} [NeZero p]
    (j : Fin p) (hj : j ≠ 0) (h : ℝ) (hh : h ≠ 0) :
    Matrix.mulVec (totalEffect (Matrix.single 0 j h⁻¹ : Matrix (Fin p) (Fin p) ℝ))
        (h • Pi.single j (1 : ℝ)) =
      Pi.single 0 1 + h • Pi.single j (1 : ℝ) := by
  rw [alternative_shear_totalEffect j hj h⁻¹, Matrix.add_mulVec]
  simp only [Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.single_mulVec_eq]
  rw [Pi.single_eq_same]
  simp only [mul_one, smul_smul, mul_inv_cancel₀ hh, one_smul]
  exact add_comm _ _

/-- The balanced observed sample law of a probability experiment is a probability law. -/
-- @node: boundedMoment_obsSample_probability
lemma boundedMoment_obsSample_probability {p n : ℕ} {ℓ v : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (𝒬 : BoundedMomentClass p n ℓ v Ω μ) (hμ : μ Set.univ = 1) :
    IsProbabilityMeasure (obsSampleLaw μ 𝒬) := by
  letI : IsProbabilityMeasure μ := ⟨hμ⟩
  have hS : AEMeasurable (fun ω => fun e r => 𝒬.S e r ω) μ := by
    apply aemeasurable_pi_lambda
    intro e
    apply aemeasurable_pi_lambda
    intro r
    exact (PoissonMeasurement.obs_aemeasurable μ 𝒬.poisson e r).fst
  have hX : AEMeasurable (fun ω => fun e r => 𝒬.X e r ω) μ := by
    apply aemeasurable_pi_lambda
    intro e
    apply aemeasurable_pi_lambda
    intro r
    exact (PoissonMeasurement.obs_aemeasurable μ 𝒬.poisson e r).snd
  exact Measure.isProbabilityMeasure_map (hS.prodMk hX)

-- @node: thm:no-uniform-noisy-incomplete-sharpness
theorem no_uniform_noisy_incomplete_sharpness
    (p n : ℕ) [NeZero p] (ℓ v h : ℝ)
    (hp : 4 ≤ p) (hn : 0 < n)
    (hℓ : 0 < ℓ ∧ ℓ ≤ Real.exp (1 / 2))
    (hv : v0 1 ≤ v) (hh : 0 < h ∧ h ≤ 1) :
    ∃ P : Fin p → Measure (ObservedSample p n),
      (∀ j : Fin p,
        ∃ (Ω : Type) (ms : MeasurableSpace Ω)
          (μ : Measure Ω),
          letI : MeasurableSpace Ω := ms
          ∃ (𝒬 : BoundedMomentClass p n ℓ v Ω μ)
            (𝔐 : AtomicCountModel p p Ω μ)
            (r : ProjectiveReduction (obsShift μ 𝔐)),
            μ Set.univ = 1 ∧ P j = obsSampleLaw μ 𝒬 ∧
            (∀ e r,
              μ.map (fun ω => (𝒬.S e r ω, 𝒬.X e r ω)) =
                obsLaw μ 𝔐 e) ∧
            (∀ e ω i, 𝔐.S e ω i = 1) ∧
            (if j = 0 then
              (∀ m, obsShift μ 𝔐 m = Pi.single 0 1 ∧ 𝔐.t m = 0) ∧
                targetSet r.v (r.κ 1) = {0}
             else
              obsShift μ 𝔐 1 =
                (fun i => (Pi.single 0 (1 : ℝ) : Fin p → ℝ) i +
                  h * (Pi.single j (1 : ℝ) : Fin p → ℝ) i) ∧
              𝔐.t 1 = j ∧ 𝔐.α 1 = h ∧
              totalEffect 𝔐.A 0 j = h⁻¹ ∧
              (∀ m, m ≠ 1 →
                obsShift μ 𝔐 m = Pi.single 0 1 ∧ 𝔐.t m = 0) ∧
              targetSet r.v (r.κ 1) = {j})) ∧
      uniformAltMixture P ≪ P 0 ∧
      Causalean.Stat.chiSqDiv (uniformAltMixture P) (P 0) ≤
        (Real.exp (n * h ^ 2) - 1) / (p - 1) ∧
      (∀ γ : ℝ, 0 < γ → γ ≤ 1 / 8 →
        ∀ Ĉ : ObservedSample p n → Finset (Fin p),
          Measurable Ĉ →
          (∀ j : Fin p,
            P j {y | (if j = 0 then (0 : Fin p) else j) ∈ Ĉ y} ≥
              ENNReal.ofReal (1 - γ)) →
          P 0 {y | 2 ≤ (Ĉ y).card} ≥
            ENNReal.ofReal
              (1 - 2 * γ - (1 / 2) *
                Real.sqrt ((Real.exp (n * h ^ 2) - 1) / (p - 1)))) ∧
      ((n : ℝ) * h ^ 2 ≤ Real.log p / 16 →
        ∀ γ : ℝ, 0 < γ → γ ≤ 1 / 8 →
          ∀ Ĉ : ObservedSample p n → Finset (Fin p),
            Measurable Ĉ →
            (∀ j : Fin p,
              P j {y | (if j = 0 then (0 : Fin p) else j) ∈ Ĉ y} ≥
                ENNReal.ofReal (1 - γ)) →
            P 0 {y | 2 ≤ (Ĉ y).card} ≥ ENNReal.ofReal (5 / 8)) := by
  -- The explicit structural experiment and moment membership are proved.
  -- Conditional Jensen contracts chi-squared through the observation kernel;
  -- projective reduction and the confidence consequence are assembled below.
  have hcore :
    ∃ P : Fin p → Measure (ObservedSample p n),
      (∀ j : Fin p,
        ∃ (Ω : Type) (ms : MeasurableSpace Ω)
          (μ : Measure Ω),
          letI : MeasurableSpace Ω := ms
          ∃ (𝒬 : BoundedMomentClass p n ℓ v Ω μ)
            (𝔐 : AtomicCountModel p p Ω μ),
            μ Set.univ = 1 ∧ P j = obsSampleLaw μ 𝒬 ∧
            (∀ e r,
              μ.map (fun ω => (𝒬.S e r ω, 𝒬.X e r ω)) =
                obsLaw μ 𝔐 e) ∧
            (∀ e ω i, 𝔐.S e ω i = 1) ∧
            (if j = 0 then
              (∀ m, obsShift μ 𝔐 m = Pi.single 0 1 ∧ 𝔐.t m = 0)
             else
              obsShift μ 𝔐 1 =
                (fun i => (Pi.single 0 (1 : ℝ) : Fin p → ℝ) i +
                  h * (Pi.single j (1 : ℝ) : Fin p → ℝ) i) ∧
              𝔐.t 1 = j ∧ 𝔐.α 1 = h ∧
              totalEffect 𝔐.A 0 j = h⁻¹ ∧
              (∀ m, m ≠ 1 →
                obsShift μ 𝔐 m = Pi.single 0 1 ∧ 𝔐.t m = 0))) ∧
      uniformAltMixture P ≪ P 0 ∧
      Integrable (fun x =>
        (((uniformAltMixture P).rnDeriv (P 0) x).toReal - 1) ^ 2) (P 0) ∧
      Causalean.Stat.chiSqDiv (uniformAltMixture P) (P 0) ≤
        (Real.exp (n * h ^ 2) - 1) / (p - 1) := by
    classical
    let S := {j : Fin p // j ≠ 0}
    have : Nonempty S := ⟨⟨1, by
      intro heq
      have hv := congrArg Fin.val heq
      simp at hv
      omega⟩⟩
    let f : S ↪ Fin p := ⟨Subtype.val, Subtype.val_injective⟩
    let Q := fun s : S => normalReplicateTiltLaw (n := n) (f s) h
    have hcard : Fintype.card S = p - 1 := by
      simp [S, Fintype.card_subtype_compl]
    have hlatent :
        Causalean.Stat.chiSqDiv (Causalean.Stat.Minimax.Mixture.uniformMixture Q)
          (normalReplicateReference p n) =
          (Real.exp (n * h ^ 2) - 1) / (p - 1) := by
      have hcalc := normalReplicateMixture_chiSq (n := n) f h
      simpa only [Q, hcard, Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one] using hcalc
    -- The observed family and all bounded-moment conditions are now explicit.
    let μj := fun j : Fin p =>
      unitGaussianExperimentMeasure (n := n) (noisyIncompleteMean j h)
    let 𝒬j := fun j : Fin p =>
      noisyIncompleteBoundedMomentClass (n := n) j h ℓ v
        (by omega) hn hh hℓ hv
    let P := fun j : Fin p => obsSampleLaw (μj j) (𝒬j j)
    have hmodels := fun j : Fin p =>
      noisyIncomplete_model_realization hp hn j h ℓ v hh hℓ hv
    have hRef : IsProbabilityMeasure (normalReplicateReference p n) := by
      unfold normalReplicateReference
      infer_instance
    have hQ : ∀ s : S, IsProbabilityMeasure (Q s) := fun s =>
      normalReplicateTiltLaw_probability (f s) h
    have hmix := Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability Q
    have hacQ : ∀ s : S, Q s ≪ normalReplicateReference p n := fun _ =>
      withDensity_absolutelyContinuous _ _
    have hpair (s t : S) : Integrable
        (fun x => ((Q s).rnDeriv (normalReplicateReference p n) x).toReal *
          ((Q t).rnDeriv (normalReplicateReference p n) x).toReal)
        (normalReplicateReference p n) := by
      have heq := (normalReplicateTiltLaw_rnDeriv (n := n) (f s) h).mul
        (normalReplicateTiltLaw_rnDeriv (n := n) (f t) h)
      exact (normalReplicate_overlap (n := n) (f s) (f t) h).1.congr heq.symm
    have hacLatent := Causalean.Stat.Minimax.Mixture.uniformMixture_absolutelyContinuous
      Q (normalReplicateReference p n) hacQ
    have hintLatent := uniformMixture_likelihood_deviation_integrable
      Q (normalReplicateReference p n) hacQ hpair
    -- Only the law identity remains: sample unchanged cells independently,
    -- add e₁ to the environment-2 latent replicates, then apply the Poisson kernel.
    have hkernel : ∃ κ : Kernel (Fin n → Fin p → ℝ) (ObservedSample p n),
        IsMarkovKernel κ ∧
        P 0 = ((normalReplicateReference p n) ⊗ₘ κ).map Prod.snd ∧
        uniformAltMixture P =
          ((Causalean.Stat.Minimax.Mixture.uniformMixture Q) ⊗ₘ κ).map Prod.snd := by
      let b := noisyIncompleteMean (0 : Fin p) h
      let e : Fin (p+1) := ⟨2, by omega⟩
      let κ := commonObservedKernel (n := n) b e
      have hnorm : shiftedGaussianLaw (0 : Fin p → ℝ) =
          Measure.pi (fun _ : Fin p => gaussianReal 0 1) := by
        rw [shiftedGaussianLaw_eq_pi]
        rfl
      have hmean0 : (fun i => if i = e then b e + 0 else b i) = b := by
        funext i
        split_ifs with hi
        · subst i; simp
        · rfl
      have hbase : P 0 = ((normalReplicateReference p n) ⊗ₘ κ).map Prod.snd := by
        change (unitGaussianExperimentMeasure (n := n) b).map
          (fun ω => (fun _ _ _ => (1 : ℝ), fun i r => (ω (i,r)).2)) = _
        simpa only [hmean0, hnorm, normalReplicateReference, κ] using
          (commonObservedKernel_law (n := n) b e 0).symm
      have halt (s : S) : P (f s) = ((Q s) ⊗ₘ κ).map Prod.snd := by
        have hmeans : noisyIncompleteMean (f s) h =
            (fun i => if i = e then b e + h • Pi.single (f s) 1 else b i) := by
          funext i
          have hj : f s ≠ 0 := s.property
          have he0 : e ≠ 0 := by intro hz; have := congrArg Fin.val hz; simp [e] at this
          by_cases hi : i = e
          · subst i
            simp [noisyIncompleteMean, b, he0, hj, e]
          · have hiv : i.val ≠ 2 := by
              intro hv
              apply hi
              exact Fin.ext hv
            simp [noisyIncompleteMean, b, hi, hiv]
        change (unitGaussianExperimentMeasure (n := n) (noisyIncompleteMean (f s) h)).map
          (fun ω => (fun _ _ _ => (1 : ℝ), fun i r => (ω (i,r)).2)) = _
        rw [hmeans]
        simpa only [κ, Q, normalReplicateTiltLaw_eq_pi_shifted] using
          (commonObservedKernel_law (n := n) b e (h • Pi.single (f s) 1)).symm
      refine ⟨κ, inferInstance, hbase, ?_⟩
      have hsum : uniformAltMixture P =
          ∑ s : S, (((p - 1 : ℕ) : ENNReal)⁻¹) • P (f s) := by
        unfold uniformAltMixture
        exact Finset.sum_subtype (Finset.univ.filter (fun j : Fin p => j ≠ 0))
          (p := fun j => j ≠ 0) (by simp)
          (fun j => (((p - 1 : ℕ) : ENNReal)⁻¹) • P j)
      rw [hsum]
      unfold Causalean.Stat.Minimax.Mixture.uniformMixture Causalean.Stat.mixture
      simp_rw [← Measure.sum_fintype]
      rw [Measure.compProd_sum_left, Measure.map_sum measurable_snd.aemeasurable]
      simp only [Measure.sum_fintype]
      apply Finset.sum_congr rfl
      intro s _
      rw [Measure.compProd_smul_left, Measure.map_smul]
      rw [halt s, hcard]
    obtain ⟨κ, hκ, hbase, halt⟩ := hkernel
    have htransfer :
        uniformAltMixture P ≪ P 0 ∧
        Integrable (fun x =>
          (((uniformAltMixture P).rnDeriv (P 0) x).toReal - 1) ^ 2) (P 0) ∧
        Causalean.Stat.chiSqDiv (uniformAltMixture P) (P 0) ≤
          Causalean.Stat.chiSqDiv (Causalean.Stat.Minimax.Mixture.uniformMixture Q)
            (normalReplicateReference p n) := by
      rw [hbase, halt]
      exact chiSq_common_kernel_observation
        (Causalean.Stat.Minimax.Mixture.uniformMixture Q)
        (normalReplicateReference p n) κ Prod.snd measurable_snd hacLatent hintLatent
    obtain ⟨hac, hint, hchi⟩ := htransfer
    refine ⟨P, ?_, hac, hint, hchi.trans_eq hlatent⟩
    intro j
    obtain ⟨𝔐, hobs, hunit, hshift⟩ := hmodels j
    refine ⟨PermutationOmega p n, inferInstance, μj j, 𝒬j j, 𝔐,
      ?_, rfl, hobs, hunit, hshift⟩
    exact measure_univ
  obtain ⟨P, hrawmodels, hac, hint, hchi⟩ := hcore
  have hmodels :
      (∀ j : Fin p,
        ∃ (Ω : Type) (ms : MeasurableSpace Ω)
          (μ : Measure Ω),
          letI : MeasurableSpace Ω := ms
          ∃ (𝒬 : BoundedMomentClass p n ℓ v Ω μ)
            (𝔐 : AtomicCountModel p p Ω μ)
            (r : ProjectiveReduction (obsShift μ 𝔐)),
            μ Set.univ = 1 ∧ P j = obsSampleLaw μ 𝒬 ∧
            (∀ e r,
              μ.map (fun ω => (𝒬.S e r ω, 𝒬.X e r ω)) =
                obsLaw μ 𝔐 e) ∧
            (∀ e ω i, 𝔐.S e ω i = 1) ∧
            (if j = 0 then
              (∀ m, obsShift μ 𝔐 m = Pi.single 0 1 ∧ 𝔐.t m = 0) ∧
                targetSet r.v (r.κ 1) = {0}
             else
              obsShift μ 𝔐 1 =
                (fun i => (Pi.single 0 (1 : ℝ) : Fin p → ℝ) i +
                  h * (Pi.single j (1 : ℝ) : Fin p → ℝ) i) ∧
              𝔐.t 1 = j ∧ 𝔐.α 1 = h ∧
              totalEffect 𝔐.A 0 j = h⁻¹ ∧
              (∀ m, m ≠ 1 →
                obsShift μ 𝔐 m = Pi.single 0 1 ∧ 𝔐.t m = 0) ∧
              targetSet r.v (r.κ 1) = {j})) := by
    intro j
    obtain ⟨Ω, ms, μ, 𝒬, 𝔐, hμ, hPj, hobs, hunit, hshift⟩ := hrawmodels j
    letI : MeasurableSpace Ω := ms
    have hshifts : if j = 0 then
        ∀ m, obsShift μ 𝔐 m = Pi.single 0 1
       else
        obsShift μ 𝔐 1 = (fun i =>
          (Pi.single 0 (1 : ℝ) : Fin p → ℝ) i + h * (Pi.single j (1 : ℝ) : Fin p → ℝ) i) ∧
        ∀ m, m ≠ 1 → obsShift μ 𝔐 m = Pi.single 0 1 := by
      by_cases hj : j = 0
      · simp only [if_pos hj] at hshift ⊢
        exact fun m => (hshift m).1
      · simp only [if_neg hj] at hshift ⊢
        exact ⟨hshift.1, fun m hm => (hshift.2.2.2.2 m hm).1⟩
    obtain ⟨r, hr⟩ := noisyIncomplete_projective_targets μ 𝔐 hp j h hh.1.ne' hshifts
    refine ⟨Ω, ms, μ, 𝒬, 𝔐, r, hμ, hPj, hobs, hunit, ?_⟩
    by_cases hj : j = 0
    · simp only [if_pos hj] at hshift hr ⊢
      exact ⟨hshift, hr⟩
    · simp only [if_neg hj] at hshift hr ⊢
      exact ⟨hshift.1, hshift.2.1, hshift.2.2.1, hshift.2.2.2.1,
        hshift.2.2.2.2, hr⟩
  have hP : ∀ j, IsProbabilityMeasure (P j) := by
    intro j
    obtain ⟨Ω, ms, μ, 𝒬, 𝔐, r, hμ, hPj, _⟩ := hmodels j
    letI : MeasurableSpace Ω := ms
    rw [hPj]
    exact boundedMoment_obsSample_probability μ 𝒬 hμ
  refine ⟨P, hmodels, hac, hchi, ?_⟩
  exact noisyIncomplete_confidence_consequence p n h hp P hP hac hint hchi

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching


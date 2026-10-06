module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.LocalizedConverse

/-!
# Gaussian-anchor square gaps on hypercube edges

This module bounds the cube-integrated squared score gap along one coordinate
of a regular-score hypercube.  The proof uses only the public side-cell,
locality, and Hölder properties bundled by `HypercubeFamily`.
-/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open Causalean.Stat.Nonparametric.HistogramRegression

variable {d K : ℕ}
  {β L cX CX cg Cg h c0 c1 C1 C2 κ ε A Bconst : ℝ}

/-- For [a positive-dimensional cube](hyp:hd), [a positive side length at
most one half](hyp:h,hh,hhsmall), [a side cube](hyp:Q,hQ), and [a point in that
side cube](hyp:x,hx), [there is a point of the unit cube outside the side cube
at Euclidean distance at most twice the side length](goal). -/
lemma exists_nearby_cube_point_not_mem_sideCube
    (hd : 1 ≤ d) (h : ℝ) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (Q : Set (XSpace d)) (hQ : IsSideCube h Q)
    (x : XSpace d) (hx : x ∈ Q) :
    ∃ y : XSpace d, y ∈ cube d ∧ y ∉ Q ∧ euclideanDistance x y ≤ 2 * h := by
  classical
  rcases hQ with ⟨a, ha, rfl⟩
  let i0 : Fin d := ⟨0, by omega⟩
  by_cases hu : a i0 + h < 1
  · let y : XSpace d := Function.update x i0 (a i0 + h)
    have hycube : y ∈ cube d := by
      intro i
      by_cases hi : i = i0
      · subst i
        simp only [y, Function.update_self]
        constructor <;> linarith [(ha i0).1]
      · simpa [y, hi] using hx.1 i
    have hynot : y ∉ {z : XSpace d | z ∈ cube d ∧ ∀ i, a i ≤ z i ∧
        (z i < a i + h ∨ (z i = 1 ∧ a i + h = 1))} := by
      intro hy
      have hi := (hy.2 i0).2
      simp only [y, Function.update_self] at hi
      rcases hi with hi | hi
      · linarith
      · linarith [hi.1]
    refine ⟨y, hycube, hynot, ?_⟩
    have hsum : (∑ i : Fin d, (x i - y i) ^ 2) =
        (x i0 - (a i0 + h)) ^ 2 := by
      apply Finset.sum_eq_single i0
      · intro i _ hi
        simp [y, hi]
      · simp
    unfold euclideanDistance
    rw [hsum, Real.sqrt_sq_eq_abs]
    have hxi0 := hx.2 i0
    have hle : x i0 ≤ a i0 + h := by
      rcases hxi0.2 with hlt | heq
      · exact hlt.le
      · linarith [heq.1, heq.2]
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith [hxi0.1]
  · have hueq : a i0 + h = 1 := le_antisymm (ha i0).2 (le_of_not_gt hu)
    let y : XSpace d := Function.update x i0 (a i0 - h)
    have hycube : y ∈ cube d := by
      intro i
      by_cases hi : i = i0
      · subst i
        simp only [y, Function.update_self]
        constructor <;> linarith [(ha i0).1]
      · simpa [y, hi] using hx.1 i
    have hynot : y ∉ {z : XSpace d | z ∈ cube d ∧ ∀ i, a i ≤ z i ∧
        (z i < a i + h ∨ (z i = 1 ∧ a i + h = 1))} := by
      intro hy
      have hi := (hy.2 i0).1
      simp only [y, Function.update_self] at hi
      linarith
    refine ⟨y, hycube, hynot, ?_⟩
    have hsum : (∑ i : Fin d, (x i - y i) ^ 2) =
        (x i0 - (a i0 - h)) ^ 2 := by
      apply Finset.sum_eq_single i0
      · intro i _ hi
        simp [y, hi]
      · simp
    unfold euclideanDistance
    rw [hsum, Real.sqrt_sq_eq_abs]
    have hxi0 := hx.2 i0
    rw [abs_of_nonneg (by linarith [hxi0.1])]
    have hle : x i0 ≤ a i0 + h := by
      rcases hxi0.2 with hlt | heq
      · exact hlt.le
      · linarith [heq.1, heq.2]
    linarith

/-- For [measurable side cells](hyp:Q,hQside), [scores local under coordinate
flips](hyp:g,hflip), [regular score models](hyp:hmodel), [their common uniform
covariate marginal](hyp:hcov), [valid positive-dimensional and smoothness
parameters](hyp:hd,hβ0,hβ1,hL), and [a positive side length at most one
half](hyp:hh,hhsmall), [every one-coordinate flip has an integrable squared gap
whose cube integral is at most `16 L² h^(d+2β)`](goal). -/
lemma hypercube_flip_sq_gap_integrable_and_integral_le_of_fields
    (Q : Fin K → Set (XSpace d))
    (g : (Fin K → Bool) → XSpace d → ℝ)
    (hQside : ∀ j, IsSideCube h (Q j))
    (hflip : ∀ θ j x, x ∉ Q j → g θ x = g (flipCoordinate θ j) x)
    (hmodel : ∀ θ, RegularScoreModel (bernoulliUnitLaw (g θ)) (g θ)
      L β cX CX cg Cg)
    (hcov : ∀ θ, (bernoulliUnitLaw (g θ)).map Prod.fst = cubeMeasure d)
    (hd : 1 ≤ d) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hL : 0 < L)
    (hh : 0 < h) (hhsmall : h ≤ 1 / 2) :
    ∀ θ j,
      Integrable (fun x => (g θ x - g (flipCoordinate θ j) x) ^ 2)
        (cubeMeasure d) ∧
      (∫ x, (g θ x - g (flipCoordinate θ j) x) ^ 2 ∂cubeMeasure d) ≤
        16 * L ^ 2 * h ^ ((d : ℝ) + 2 * β) := by
  classical
  intro θ j
  have hQmeas : MeasurableSet (Q j) := measurableSet_of_isSideCube (hQside j)
  have hmeasθ : Measurable (fun x : Cube d => g θ x.val.ofLp) :=
    measurable_paperCubeScore (g θ) hL hβ0 (hmodel θ).holder_score
  have hmeasflip : Measurable
      (fun x : Cube d => g (flipCoordinate θ j) x.val.ofLp) :=
    measurable_paperCubeScore (g (flipCoordinate θ j)) hL hβ0
      (hmodel (flipCoordinate θ j)).holder_score
  let clamp : XSpace d → Cube d := fun x =>
    ⟨WithLp.toLp 2 (fun i => min 1 (max 0 (x i))), fun i => ⟨by simp, by simp⟩⟩
  have hclamp : Measurable clamp := by dsimp [clamp]; fun_prop
  let F : XSpace d → ℝ := fun x =>
    (g θ (clamp x).val.ofLp - g (flipCoordinate θ j) (clamp x).val.ofLp) ^ 2
  have hFmeas : Measurable F := by
    exact ((hmeasθ.comp hclamp).sub (hmeasflip.comp hclamp)).pow_const 2
  have hcubeae : ∀ᵐ x ∂cubeMeasure d, x ∈ cube d := by
    unfold cubeMeasure
    exact ae_restrict_mem (by unfold cube; measurability)
  have hclamp_eq (x : XSpace d) (hx : x ∈ cube d) : (clamp x).val.ofLp = x := by
    funext i
    simp [clamp, max_eq_right (hx i).1, min_eq_right (hx i).2]
  have hgap_bound (x : XSpace d) (hx : x ∈ cube d) :
      (g θ x - g (flipCoordinate θ j) x) ^ 2 ≤
        (Q j).indicator (fun _ => 16 * L ^ 2 * h ^ (2 * β)) x := by
    by_cases hxQ : x ∈ Q j
    · rw [Set.indicator_of_mem hxQ]
      obtain ⟨y, hycube, hyQ, hxy⟩ :=
        exists_nearby_cube_point_not_mem_sideCube hd h hh hhsmall (Q j) (hQside j) x hxQ
      have hθy := hflip θ j y hyQ
      have hθholder := (hmodel θ).holder_score x hx y hycube
      have hflipholder := (hmodel (flipCoordinate θ j)).holder_score x hx y hycube
      have hdistpow : (euclideanDistance x y) ^ β ≤ (2 * h) ^ β :=
        Real.rpow_le_rpow (by unfold euclideanDistance; positivity) hxy hβ0.le
      have htwo : (2 : ℝ) ^ β ≤ 2 := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hβ1
      have hmul : (2 * h) ^ β ≤ 2 * h ^ β := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hh.le]
        exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hh.le β)
      have habs : |g θ x - g (flipCoordinate θ j) x| ≤ 4 * L * h ^ β := by
        calc
          |g θ x - g (flipCoordinate θ j) x| =
              |(g θ x - g θ y) +
                (g (flipCoordinate θ j) y - g (flipCoordinate θ j) x)| := by
                rw [hθy]
                ring_nf
          _ ≤ |g θ x - g θ y| +
              |g (flipCoordinate θ j) y - g (flipCoordinate θ j) x| := abs_add_le _ _
          _ ≤ L * (euclideanDistance x y) ^ β +
              L * (euclideanDistance x y) ^ β := by
                gcongr
                simpa [abs_sub_comm] using hflipholder
          _ ≤ 2 * L * (2 * h) ^ β := by
                have := mul_le_mul_of_nonneg_left hdistpow hL.le
                nlinarith
          _ ≤ 2 * L * (2 * h ^ β) :=
                mul_le_mul_of_nonneg_left hmul (mul_nonneg (by norm_num) hL.le)
          _ = 4 * L * h ^ β := by ring
      have hsquare := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 habs
      rw [sq_abs, mul_pow] at hsquare
      have hrpow : (h ^ β) ^ 2 = h ^ (2 * β) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
        congr 1
        ring
      nlinarith [hsquare]
    · rw [Set.indicator_of_notMem hxQ, hflip θ j x hxQ]
      norm_num
  have hbound_ae : ∀ᵐ x ∂cubeMeasure d,
      (g θ x - g (flipCoordinate θ j) x) ^ 2 ≤
        (Q j).indicator (fun _ => 16 * L ^ 2 * h ^ (2 * β)) x := by
    filter_upwards [hcubeae] with x hx
    exact hgap_bound x hx
  have hstrong : AEStronglyMeasurable
      (fun x => (g θ x - g (flipCoordinate θ j) x) ^ 2) (cubeMeasure d) := by
    apply hFmeas.aestronglyMeasurable.congr
    filter_upwards [hcubeae] with x hx
    simp only [F, hclamp_eq x hx]
  have hCnonneg : 0 ≤ 16 * L ^ 2 * h ^ (2 * β) := by positivity
  letI : IsProbabilityMeasure (bernoulliUnitLaw (g θ)) :=
    (hmodel θ).covariate_density.1
  letI : IsProbabilityMeasure (cubeMeasure d) := by
    rw [← hcov θ]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hindicatorInt : Integrable
      ((Q j).indicator (fun _ => 16 * L ^ 2 * h ^ (2 * β))) (cubeMeasure d) := by
    exact (integrable_const _).indicator hQmeas
  have hint : Integrable (fun x =>
      (g θ x - g (flipCoordinate θ j) x) ^ 2) (cubeMeasure d) :=
    hindicatorInt.mono' hstrong (hbound_ae.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (sq_nonneg (g θ x - g (flipCoordinate θ j) x))]
      exact hx)
  refine ⟨hint, ?_⟩
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg _)
    hindicatorInt hbound_ae
  have hmass := sideCube_cubeMeasure_toReal_le (hQside j) hh.le
  have hindicator :
      (∫ x, (Q j).indicator (fun _ => 16 * L ^ 2 * h ^ (2 * β)) x
        ∂cubeMeasure d) =
      (16 * L ^ 2 * h ^ (2 * β)) * (cubeMeasure d (Q j)).toReal := by
    rw [integral_indicator hQmeas]
    simp only [integral_const, Measure.restrict_apply_univ, measureReal_def]
    ring
  rw [hindicator] at hmono
  have hmulmass :
      (16 * L ^ 2 * h ^ (2 * β)) * (cubeMeasure d (Q j)).toReal ≤
        (16 * L ^ 2 * h ^ (2 * β)) * h ^ d :=
    mul_le_mul_of_nonneg_left hmass hCnonneg
  calc
    (∫ x, (g θ x - g (flipCoordinate θ j) x) ^ 2 ∂cubeMeasure d) ≤
        (16 * L ^ 2 * h ^ (2 * β)) * (cubeMeasure d (Q j)).toReal := hmono
    _ ≤ (16 * L ^ 2 * h ^ (2 * β)) * h ^ d := hmulmass
    _ = 16 * L ^ 2 * h ^ ((d : ℝ) + 2 * β) := by
      have hrpow : h ^ d * h ^ (2 * β) = h ^ ((d : ℝ) + 2 * β) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_add hh _ _).symm
      rw [← hrpow]
      ring

/-- For [a regular-score hypercube](hyp:hfam), [valid positive-dimensional and
smoothness parameters](hyp:hd,hβ0,hβ1,hL), and [a positive side length at most
one half](hyp:hh,hhsmall), [the family supplies scores whose every
one-coordinate flip has an integrable squared gap with cube integral at most
`16 L² h^(d+2β)`](goal). -/
-- keep: public bundled-family interface for reuse by future anchor converse arguments
lemma hypercube_flip_sq_gap_integrable_and_integral_le
    (hfam : HypercubeFamily d β L cX CX cg Cg h c0 c1 C1 C2 κ ε A Bconst)
    (hd : 1 ≤ d) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hL : 0 < L)
    (hh : 0 < h) (hhsmall : h ≤ 1 / 2) :
    ∃ K : ℕ, ∃ g : (Fin K → Bool) → XSpace d → ℝ,
      ∀ θ j,
        Integrable (fun x => (g θ x - g (flipCoordinate θ j) x) ^ 2)
          (cubeMeasure d) ∧
        (∫ x, (g θ x - g (flipCoordinate θ j) x) ^ 2 ∂cubeMeasure d) ≤
          16 * L ^ 2 * h ^ ((d : ℝ) + 2 * β) := by
  obtain ⟨K, Q, ψ, B, g, base, amplitude, hKlo, hKhi, hQside, hdisj,
    hB, hψ, hamp, hg, hflip, hfold, hmodel, hcov, hkl⟩ := hfam
  exact ⟨K, g,
    hypercube_flip_sq_gap_integrable_and_integral_le_of_fields
      Q g hQside hflip hmodel hcov hd hβ0 hβ1 hL hh hhsmall⟩

end CausalSmith.Experimentation.PilotscorePairingFrontier

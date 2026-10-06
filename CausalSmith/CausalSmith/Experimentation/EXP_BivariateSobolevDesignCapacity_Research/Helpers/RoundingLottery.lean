module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.RoundingMoments
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Exact direction-lottery moments

The half-open inverse-CDF sampler integrates finite rewards with their prescribed
weights. Applied to reciprocal boundary-distance weights, this supplies the
isotropic covariance of a boundary move before the phase energy argument.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
variable {n : ℕ}

/-- [ A nonnegative finite direction lottery integrates every reward on its full
weight interval, including zero weights and tied cumulative boundaries.](goal) Under [the stated conditions](hyp:hw). -/
-- @node: inverseCDF_interval_integral
lemma inverseCDF_interval_integral (xs : List ((Fin n → ℝ) × ℝ))
    (f : (Fin n → ℝ) → ℝ) (hw : ∀ x ∈ xs, 0 ≤ x.2) :
    IntervalIntegrable (fun t => f (inverseCDF xs t)) volume 0 (xs.map Prod.snd).sum ∧
    (∫ t in 0..(xs.map Prod.snd).sum, f (inverseCDF xs t)) =
      (xs.map (fun x => x.2 * f x.1)).sum := by
  induction xs with
  | nil => simp [inverseCDF]
  | cons x xs ih =>
    have hx : 0 ≤ x.2 := hw x (by simp)
    have htail : ∀ y ∈ xs, 0 ≤ y.2 := fun y hy => hw y (by simp [hy])
    obtain ⟨hi, he⟩ := ih htail
    cases xs with
    | nil => simp [inverseCDF, intervalIntegral.integral_const]
    | cons y ys =>
      let S : ℝ := ((y :: ys).map Prod.snd).sum
      have hS : 0 ≤ S := by
        change 0 ≤ ((y :: ys).map Prod.snd).sum
        have hnonneg (l : List ((Fin n → ℝ) × ℝ))
            (hl : ∀ z ∈ l, 0 ≤ z.2) : 0 ≤ (l.map Prod.snd).sum := by
          induction l with
          | nil => simp
          | cons z l ih =>
            simp only [List.map_cons, List.sum_cons]
            exact add_nonneg (hl z (by simp)) (ih (fun v hv => hl v (by simp [hv])))
        exact hnonneg _ htail
      have hleft : EqOn (fun _ : ℝ => f x.1)
          (fun t => f (inverseCDF (x :: y :: ys) t)) (uIoo 0 x.2) := by
        intro t ht
        rw [uIoo_of_le hx] at ht
        simp [inverseCDF, ht.2]
      have hright : EqOn (fun t => f (inverseCDF (y :: ys) (t - x.2)))
          (fun t => f (inverseCDF (x :: y :: ys) t)) (uIoo x.2 (x.2 + S)) := by
        intro t ht
        rw [uIoo_of_le (by linarith : x.2 ≤ x.2 + S)] at ht
        simp [inverseCDF, not_lt.mpr ht.1.le]
      have hil : IntervalIntegrable (fun t => f (inverseCDF (x :: y :: ys) t))
          volume 0 x.2 := intervalIntegrable_const.congr_uIoo hleft
      have hir : IntervalIntegrable (fun t => f (inverseCDF (x :: y :: ys) t))
          volume x.2 (x.2 + S) := by
        apply IntervalIntegrable.congr_uIoo _ hright
        simpa [S, add_comm] using hi.comp_sub_right x.2
      constructor
      · simpa [S] using hil.trans hir
      · change (∫ t in 0..x.2 + S, f (inverseCDF (x :: y :: ys) t)) = _
        rw [← intervalIntegral.integral_add_adjacent_intervals hil hir,
          ← intervalIntegral.integral_congr_uIoo hleft,
          ← intervalIntegral.integral_congr_uIoo hright,
          intervalIntegral.integral_const,
          intervalIntegral.integral_comp_sub_right (fun t => f (inverseCDF (y :: ys) t)) x.2]
        simp only [sub_self, add_sub_cancel_left, sub_zero, smul_eq_mul]
        rw [he]
        rfl

/-- [ A unit-mass finite direction lottery has precisely the expected weighted
reward under the uniform seed used by the rounding construction.](goal) Under [the stated conditions](hyp:hw,hs). -/
-- @node: inverseCDF_uniform_integral
lemma inverseCDF_uniform_integral (xs : List ((Fin n → ℝ) × ℝ))
    (f : (Fin n → ℝ) → ℝ) (hw : ∀ x ∈ xs, 0 ≤ x.2)
    (hs : (xs.map Prod.snd).sum = 1) :
    (∫ t, f (inverseCDF xs t) ∂volume.restrict (Icc (0 : ℝ) 1)) =
      (xs.map (fun x => x.2 * f x.1)).sum := by
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num), ← hs]
  exact (inverseCDF_interval_integral xs f hw).2

/-- Zipping each direction with its own weight keeps the ordered finite lottery. [The asserted mathematical result follows](goal). -/
-- @node: direction_lottery_zip
lemma direction_lottery_zip (bs : List (Fin n → ℝ)) (w : (Fin n → ℝ) → ℝ) :
    bs.zip (bs.map w) = bs.map (fun v => (v, w v)) := by
  induction bs with
  | nil => rfl
  | cons v bs ih => simp [ih]

/-- Dividing positive finite weights by their total gives the exact normalized
uniform-seed expectation, without independence of vector coordinates. Under [the stated conditions](hyp:hw,hS), [the asserted mathematical result follows](goal). -/
-- @node: inverseCDF_normalized_integral
lemma inverseCDF_normalized_integral (bs : List (Fin n → ℝ))
    (w f : (Fin n → ℝ) → ℝ) (hw : ∀ v ∈ bs, 0 ≤ w v)
    (hS : 0 < (bs.map w).sum) :
    (∫ t, f (inverseCDF (bs.map (fun v => (v, w v / (bs.map w).sum))) t)
      ∂volume.restrict (Icc (0 : ℝ) 1)) =
      (bs.map w).sum⁻¹ * (bs.map (fun v => w v * f v)).sum := by
  let S := (bs.map w).sum
  have hdivide (l : List (Fin n → ℝ)) :
      (l.map (fun v => w v / S)).sum = (l.map w).sum / S := by
    induction l with
    | nil => simp
    | cons v l ih => simp [ih, add_div]
  have hmass : ((bs.map (fun v => (v, w v / S))).map Prod.snd).sum = 1 := by
    simp only [List.map_map, Function.comp_def]
    rw [hdivide]
    exact div_self (ne_of_gt hS)
  have hweights : ∀ x ∈ bs.map (fun v => (v, w v / S)), 0 ≤ x.2 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    exact div_nonneg (hw v hv) hS.le
  rw [inverseCDF_uniform_integral _ f hweights hmass]
  simp only [List.map_map, Function.comp_def]
  change (bs.map (fun v => w v / S * f v)).sum =
    S⁻¹ * (bs.map (fun v => w v * f v)).sum
  have hscale (l : List (Fin n → ℝ)) :
      (l.map (fun v => w v / S * f v)).sum =
        S⁻¹ * (l.map (fun v => w v * f v)).sum := by
    induction l with
    | nil => simp
    | cons v l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, mul_add]
      congr 1
      ring
  exact hscale bs

/-- [ The actual direction lottery averages the direction-conditioned boundary
covariance to the reciprocal total weight times the basis outer-product sum.](goal) Under [the stated conditions](hyp:hne). -/
-- @node: roundingStep_lottery_covariance
lemma roundingStep_lottery_covariance (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u : Fin n → ℝ) (i j : Fin n) (hne : nullspaceBasis a q u ≠ []) :
    (∫ seed₁, ∫ seed₂, (roundingStep a q u seed₁ seed₂ i - u i) *
      (roundingStep a q u seed₁ seed₂ j - u j)
      ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) =
        ((nullspaceBasis a q u).map
          (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)).sum⁻¹ *
        ((nullspaceBasis a q u).map (fun v => v i * v j)).sum := by
  let bs := nullspaceBasis a q u
  let w := fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹
  have hS := nullspaceBasis_boundary_weight_sum_pos a q u hne
  have hw := nullspaceBasis_boundary_weight_pos a q u
  simp_rw [roundingStep_seed_covariance]
  change (∫ t, boundaryPlus u (inverseCDF (bs.zip ((bs.map w).map
    (fun z => z / (bs.map w).sum))) t) *
    boundaryMinus u (inverseCDF (bs.zip ((bs.map w).map
    (fun z => z / (bs.map w).sum))) t) *
    inverseCDF (bs.zip ((bs.map w).map (fun z => z / (bs.map w).sum))) t i *
    inverseCDF (bs.zip ((bs.map w).map (fun z => z / (bs.map w).sum))) t j
    ∂volume.restrict (Icc (0 : ℝ) 1)) = _
  simp only [List.map_map, Function.comp_def, direction_lottery_zip]
  rw [inverseCDF_normalized_integral bs w
    (fun v => boundaryPlus u v * boundaryMinus u v * v i * v j)
    (fun v hv => (hw v hv).le) hS]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro v hv
  have ht : boundaryPlus u v * boundaryMinus u v ≠ 0 :=
    ne_of_gt (inv_pos.mp (hw v hv))
  change (boundaryPlus u v * boundaryMinus u v)⁻¹ *
    (boundaryPlus u v * boundaryMinus u v * v i * v j) = v i * v j
  calc
    _ = ((boundaryPlus u v * boundaryMinus u v)⁻¹ *
        (boundaryPlus u v * boundaryMinus u v)) * (v i * v j) := by ring
    _ = v i * v j := by rw [inv_mul_cancel₀ ht, one_mul]

/-- [ Reciprocal boundary-product sampling cancels that product for any finite
basis reward. This is the common averaging step for row and norm energies.](goal) Under [the stated conditions](hyp:hne). -/
-- @node: rounding_direction_reward_integral
lemma rounding_direction_reward_integral (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ)
    (hne : nullspaceBasis a q u ≠ []) :
    let bs := nullspaceBasis a q u
    let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
    (∫ t, let v := inverseCDF (bs.zip (ws.map (fun z => z / ws.sum))) t
      boundaryPlus u v * boundaryMinus u v * f v
      ∂volume.restrict (Icc (0 : ℝ) 1)) = ws.sum⁻¹ * (bs.map f).sum := by
  dsimp only
  let bs := nullspaceBasis a q u
  let w := fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹
  have hw := nullspaceBasis_boundary_weight_pos a q u
  simp only [List.map_map, Function.comp_def, direction_lottery_zip]
  rw [inverseCDF_normalized_integral bs w
    (fun v => boundaryPlus u v * boundaryMinus u v * f v)
    (fun v hv => (hw v hv).le) (nullspaceBasis_boundary_weight_sum_pos a q u hne)]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro v hv
  have ht : boundaryPlus u v * boundaryMinus u v ≠ 0 :=
    ne_of_gt (inv_pos.mp (hw v hv))
  change (boundaryPlus u v * boundaryMinus u v)⁻¹ *
    (boundaryPlus u v * boundaryMinus u v * f v) = f v
  rw [← mul_assoc, inv_mul_cancel₀ ht, one_mul]

/-- The actual move's test-row increment has the exact conditional second
moment, with the asymmetric boundary coin rather than a symmetric surrogate. [The asserted mathematical result follows](goal). -/
-- @node: roundingStep_seed_row_variance
lemma roundingStep_seed_row_variance (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u c : Fin n → ℝ) (seed₁ : ℝ) :
    let bs := nullspaceBasis a q u
    let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
    let v := inverseCDF (bs.zip (ws.map (fun w => w / ws.sum))) seed₁
    (∫ seed₂, rowDot c (roundingStep a q u seed₁ seed₂ - u) ^ 2
      ∂volume.restrict (Icc (0 : ℝ) 1)) =
        boundaryPlus u v * boundaryMinus u v * rowDot c v ^ 2 := by
  dsimp only
  let bs := nullspaceBasis a q u
  let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
  let v := inverseCDF (bs.zip (ws.map (fun w => w / ws.sum))) seed₁
  by_cases he : bs = []
  · simp [roundingStep, show nullspaceBasis a q u = [] from he, inverseCDF, rowDot]
  · have hv : v ∈ bs := rounding_selected_direction_mem a q u seed₁ he
    have hs : ∀ k, v k ≠ 0 → |u k| < 1 := by
      intro k hk
      by_contra hn
      exact hk (nullspaceBasis_active_support a q u v hv k hn)
    have hn := orderedOrtho_nonzero _ v hv
    have hp := boundaryPlus_pos u v hs hn
    have hm := boundaryMinus_pos u v hs hn
    have hcoin := boundary_seed_covariance (rowDot c v) (rowDot c v)
      (boundaryPlus u v) (boundaryMinus u v) hp hm
    rw [pow_two, ← mul_assoc, ← hcoin]
    apply integral_congr_ae
    filter_upwards [] with t
    change dotProduct c ((if t < boundaryMinus u v / (boundaryPlus u v + boundaryMinus u v)
      then u + boundaryPlus u v • v else u - boundaryMinus u v • v) - u) ^ 2 = _
    split_ifs <;>
      simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul] <;>
      simp only [rowDot, dotProduct] <;> ring

/-- Averaging both fresh seeds gives the exact test-row quadratic form in the
constructed nullspace basis, the phase variance identity in the roadmap. Under [the stated conditions](hyp:hne), [the asserted mathematical result follows](goal). -/
-- @node: roundingStep_lottery_row_variance
lemma roundingStep_lottery_row_variance (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u c : Fin n → ℝ) (hne : nullspaceBasis a q u ≠ []) :
    (∫ seed₁, ∫ seed₂, rowDot c (roundingStep a q u seed₁ seed₂ - u) ^ 2
      ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) =
        ((nullspaceBasis a q u).map
          (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)).sum⁻¹ *
        ((nullspaceBasis a q u).map (fun v => rowDot c v ^ 2)).sum := by
  simp_rw [roundingStep_seed_row_variance]
  exact rounding_direction_reward_integral a q u (fun v => rowDot c v ^ 2) hne

/-- [ A single asymmetric boundary coin increases squared norm in expectation
by its distance product times the direction's squared norm.](goal) Under [the stated conditions](hyp:hp,hm). -/
-- @node: boundary_seed_energy_increment
lemma boundary_seed_energy_increment (u v : Fin n → ℝ) (dp dm : ℝ)
    (hp : 0 < dp) (hm : 0 < dm) :
    (∫ t, (if t < dm / (dp + dm) then
      rowDot (u + dp • v) (u + dp • v) - rowDot u u else
      rowDot (u - dm • v) (u - dm • v) - rowDot u u)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = dp * dm * rowDot v v := by
  rw [uniform_threshold_integral _ _ _
    ⟨(boundary_coin_probability dp dm hp hm).1.le,
      (boundary_coin_probability dp dm hp hm).2.le⟩]
  change dm / (dp + dm) * (dotProduct (u + dp • v) (u + dp • v) - dotProduct u u) +
    (1 - dm / (dp + dm)) * (dotProduct (u - dm • v) (u - dm • v) - dotProduct u u) = _
  simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  calc
    _ = (dm / (dp + dm) * dp + (1 - dm / (dp + dm)) * (-dm)) *
        (dotProduct u v + dotProduct v u) +
      (dm / (dp + dm) * dp ^ 2 + (1 - dm / (dp + dm)) * (-dm) ^ 2) *
        dotProduct v v := by ring
    _ = dp * dm * rowDot v v := by
      rw [boundary_coin_mean_zero dp dm hp hm,
        boundary_coin_second_moment dp dm hp hm, zero_mul, zero_add]
      rfl

/-- The squared-norm potential's conditional increase for the actual move is
its boundary-distance product, since every selected basis direction is a unit vector. [The asserted mathematical result follows](goal). -/
-- @node: roundingStep_seed_energy_increment
lemma roundingStep_seed_energy_increment (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u : Fin n → ℝ) (seed₁ : ℝ) :
    let bs := nullspaceBasis a q u
    let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
    let v := inverseCDF (bs.zip (ws.map (fun w => w / ws.sum))) seed₁
    (∫ seed₂, rowDot (roundingStep a q u seed₁ seed₂) (roundingStep a q u seed₁ seed₂) -
      rowDot u u ∂volume.restrict (Icc (0 : ℝ) 1)) =
        boundaryPlus u v * boundaryMinus u v * rowDot v v := by
  dsimp only
  let bs := nullspaceBasis a q u
  let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
  let v := inverseCDF (bs.zip (ws.map (fun w => w / ws.sum))) seed₁
  by_cases he : bs = []
  · simp [roundingStep, show nullspaceBasis a q u = [] from he, inverseCDF, rowDot]
  · have hv : v ∈ bs := rounding_selected_direction_mem a q u seed₁ he
    have hs : ∀ k, v k ≠ 0 → |u k| < 1 := by
      intro k hk
      by_contra hn
      exact hk (nullspaceBasis_active_support a q u v hv k hn)
    have hn := orderedOrtho_nonzero _ v hv
    have hcoin := boundary_seed_energy_increment u v (boundaryPlus u v) (boundaryMinus u v)
      (boundaryPlus_pos u v hs hn) (boundaryMinus_pos u v hs hn)
    rw [← hcoin]
    apply integral_congr_ae
    filter_upwards [] with t
    change rowDot (if t < boundaryMinus u v / (boundaryPlus u v + boundaryMinus u v)
      then u + boundaryPlus u v • v else u - boundaryMinus u v • v)
      (if t < boundaryMinus u v / (boundaryPlus u v + boundaryMinus u v)
      then u + boundaryPlus u v • v else u - boundaryMinus u v • v) - rowDot u u = _
    split_ifs <;> rfl

/-- The two-seed squared-norm increase is reciprocal total weight times the
actual basis size, giving the trace term needed for the phase energy budget. Under [the stated conditions](hyp:hne), [the asserted mathematical result follows](goal). -/
-- @node: roundingStep_lottery_energy_increment
lemma roundingStep_lottery_energy_increment (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u : Fin n → ℝ) (hne : nullspaceBasis a q u ≠ []) :
    (∫ seed₁, ∫ seed₂,
      rowDot (roundingStep a q u seed₁ seed₂) (roundingStep a q u seed₁ seed₂) - rowDot u u
      ∂volume.restrict (Icc (0 : ℝ) 1) ∂volume.restrict (Icc (0 : ℝ) 1)) =
        ((nullspaceBasis a q u).map
          (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)).sum⁻¹ *
        (nullspaceBasis a q u).length := by
  simp_rw [roundingStep_seed_energy_increment]
  rw [rounding_direction_reward_integral a q u (fun v => rowDot v v) hne]
  congr 1
  have hunit : (nullspaceBasis a q u).map (fun v => rowDot v v) =
      (nullspaceBasis a q u).map (fun _ => (1 : ℝ)) := by
    apply List.map_congr_left
    intro v hv
    exact orderedOrtho_unit_length _ v hv
  rw [hunit]
  simp

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

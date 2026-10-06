module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.RoundingTermination

/-! # Fresh-seed boundary moments

Half-open uniform threshold sampling realizes the asymmetric boundary coin.
Its coordinate mean and covariance are computed before integrating over the
selected nullspace direction or the preceding seed history.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
variable {n : ℕ}

/-- [ A half-open uniform threshold has the prescribed two-point expectation,
including thresholds at either endpoint of the unit interval.](goal) Under [the stated conditions](hyp:hp). -/
-- @node: uniform_threshold_integral
lemma uniform_threshold_integral (p x y : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    (∫ t, (if t < p then x else y) ∂volume.restrict (Icc (0 : ℝ) 1)) =
      p * x + (1 - p) * y := by
  have hleft : Iio p ∩ Icc (0 : ℝ) 1 = Ico 0 p := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨ht, h0, _⟩
      exact ⟨h0, ht⟩
    · rintro ⟨h0, ht⟩
      exact ⟨ht, h0, ht.le.trans hp.2⟩
  have hright : (Iio p)ᶜ ∩ Icc (0 : ℝ) 1 = Icc p 1 := by
    ext t
    simp only [mem_inter_iff, mem_compl_iff, mem_Iio, not_lt, mem_Icc]
    constructor
    · rintro ⟨ht, _, h1⟩
      exact ⟨ht, h1⟩
    · rintro ⟨ht, h1⟩
      exact ⟨ht, hp.1.trans ht, h1⟩
  change (∫ t, (Iio p).piecewise (fun _ => x) (fun _ => y) t
    ∂volume.restrict (Icc (0 : ℝ) 1)) = _
  rw [integral_piecewise measurableSet_Iio
    (integrable_const x).integrableOn (integrable_const y).integrableOn]
  rw [Measure.restrict_restrict measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio.compl, hleft, hright]
  simp [integral_const, measureReal_def, Real.volume_Ico, Real.volume_Icc,
    ENNReal.toReal_ofReal hp.1, ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2)]

/-- A finite threshold coin is integrable under its fresh uniform seed. [The asserted mathematical result follows](goal). -/
-- @node: uniform_threshold_integrable
lemma uniform_threshold_integrable (p x y : ℝ) :
    Integrable (fun t => if t < p then x else y)
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  classical
  exact Integrable.piecewise measurableSet_Iio
    (integrable_const x).integrableOn (integrable_const y).integrableOn

/-- The actual half-open asymmetric boundary coin preserves a coordinate mean. Under [the stated conditions](hyp:hp,hm), [the asserted mathematical result follows](goal). -/
-- @node: boundary_seed_mean
lemma boundary_seed_mean (u v dp dm : ℝ) (hp : 0 < dp) (hm : 0 < dm) :
    (∫ t, (if t < dm / (dp + dm) then u + dp * v else u - dm * v)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = u := by
  rw [uniform_threshold_integral _ _ _
    ⟨(boundary_coin_probability dp dm hp hm).1.le,
      (boundary_coin_probability dp dm hp hm).2.le⟩]
  have hzero := boundary_coin_mean_zero dp dm hp hm
  nlinarith [show (dm / (dp + dm) * dp +
    (1 - dm / (dp + dm)) * (-dm)) * v = 0 by rw [hzero, zero_mul]]

/-- [ The centered boundary increment has the roadmap's exact coordinate covariance.](goal) Under [the stated conditions](hyp:hp,hm). -/
-- @node: boundary_seed_covariance
lemma boundary_seed_covariance (v w dp dm : ℝ) (hp : 0 < dp) (hm : 0 < dm) :
    (∫ t, (if t < dm / (dp + dm) then (dp * v) * (dp * w)
      else (-dm * v) * (-dm * w)) ∂volume.restrict (Icc (0 : ℝ) 1)) =
      dp * dm * v * w := by
  rw [uniform_threshold_integral _ _ _
    ⟨(boundary_coin_probability dp dm hp hm).1.le,
      (boundary_coin_probability dp dm hp hm).2.le⟩]
  calc
    _ = (dm / (dp + dm) * dp ^ 2 +
      (1 - dm / (dp + dm)) * (-dm) ^ 2) * v * w := by ring
    _ = dp * dm * v * w := by rw [boundary_coin_second_moment dp dm hp hm]

/-- [ A fresh terminal coin preserves the current fractional coordinate.](goal) Under [the stated conditions](hyp:hu). -/
-- @node: terminal_seed_mean
lemma terminal_seed_mean (u : ℝ) (hu : |u| ≤ 1) :
    (∫ t, (if t < (1 + u) / 2 then (1 : ℝ) else -1)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = u := by
  have hp : (1 + u) / 2 ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨hl, hr⟩ := abs_le.mp hu
    constructor <;> linarith
  rw [uniform_threshold_integral _ _ _ hp]
  exact terminal_coin_mean u

/-- [ A fresh terminal increment has variance one minus the current square.](goal) Under [the stated conditions](hyp:hu). -/
-- @node: terminal_seed_increment_second_moment
lemma terminal_seed_increment_second_moment (u : ℝ) (hu : |u| ≤ 1) :
    (∫ t, (if t < (1 + u) / 2 then (1 - u) ^ 2 else (-1 - u) ^ 2)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = 1 - u ^ 2 := by
  have hp : (1 + u) / 2 ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨hl, hr⟩ := abs_le.mp hu
    constructor <;> linarith
  rw [uniform_threshold_integral _ _ _ hp]
  exact terminal_coin_increment_second_moment u

/-- [ The constructed finite sampler selects a genuine nullspace basis vector.](goal) Under [the stated conditions](hyp:hne). -/
-- @node: rounding_selected_direction_mem
lemma rounding_selected_direction_mem (a : Fin (n / 4) → Fin n → ℝ)
    (q : ℕ) (u : Fin n → ℝ) (seed : ℝ) (hne : nullspaceBasis a q u ≠ []) :
    let bs := nullspaceBasis a q u
    let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
    inverseCDF (bs.zip (ws.map (fun w => w / ws.sum))) seed ∈ bs := by
  dsimp only
  let bs := nullspaceBasis a q u
  let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
  let xs := bs.zip (ws.map (fun w => w / ws.sum))
  have hlen : (ws.map (fun w => w / ws.sum)).length = bs.length := by simp [ws]
  have hxne : xs ≠ [] := by
    intro hz
    have hl : xs.length = bs.length := by simp [xs, hlen]
    rw [hz] at hl
    exact hne (by simpa using hl.symm)
  have hfst : xs.map Prod.fst = bs := List.map_fst_zip hlen.ge
  change inverseCDF xs seed ∈ bs
  rw [← hfst]
  exact inverseCDF_mem_directions xs hxne seed

/-- The actual boundary step preserves each coordinate mean conditional on the
entire current state and the selected direction seed. [The asserted mathematical result follows](goal). -/
-- @node: roundingStep_seed_mean
lemma roundingStep_seed_mean (a : Fin (n / 4) → Fin n → ℝ) (q : ℕ)
    (u : Fin n → ℝ) (seed₁ : ℝ) (i : Fin n) :
    (∫ seed₂, roundingStep a q u seed₁ seed₂ i
      ∂volume.restrict (Icc (0 : ℝ) 1)) = u i := by
  let bs := nullspaceBasis a q u
  let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
  let v := inverseCDF (bs.zip (ws.map (fun w => w / ws.sum))) seed₁
  by_cases he : bs = []
  · simp [roundingStep, show nullspaceBasis a q u = [] from he, inverseCDF,
      integral_const, measureReal_def, Real.volume_Icc]
  · have hv : v ∈ bs := rounding_selected_direction_mem a q u seed₁ he
    have hs : ∀ j, v j ≠ 0 → |u j| < 1 := by
      intro j hj
      by_contra hn
      exact hj (nullspaceBasis_active_support a q u v hv j hn)
    have hn : v ≠ 0 := orderedOrtho_nonzero _ v hv
    simp only [roundingStep, ite_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    change (∫ t, (if t < boundaryMinus u v / (boundaryPlus u v + boundaryMinus u v)
      then u i + boundaryPlus u v * v i else u i - boundaryMinus u v * v i)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = u i
    exact boundary_seed_mean (u i) (v i) _ _
      (boundaryPlus_pos u v hs hn) (boundaryMinus_pos u v hs hn)

/-- [ Each coordinate of the actual boundary step is integrable over its coin seed.](goal) -/
-- @node: roundingStep_seed_integrable
lemma roundingStep_seed_integrable (a : Fin (n / 4) → Fin n → ℝ) (q : ℕ)
    (u : Fin n → ℝ) (seed₁ : ℝ) (i : Fin n) :
    Integrable (fun seed₂ => roundingStep a q u seed₁ seed₂ i)
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  simp only [roundingStep, ite_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact uniform_threshold_integrable _ _ _

/-- [ The actual direction-conditioned increment covariance is the boundary-distance
product times the selected direction's outer product.](goal) -/
-- @node: roundingStep_seed_covariance
lemma roundingStep_seed_covariance (a : Fin (n / 4) → Fin n → ℝ) (q : ℕ)
    (u : Fin n → ℝ) (seed₁ : ℝ) (i j : Fin n) :
    let bs := nullspaceBasis a q u
    let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
    let v := inverseCDF (bs.zip (ws.map (fun w => w / ws.sum))) seed₁
    (∫ seed₂, (roundingStep a q u seed₁ seed₂ i - u i) *
      (roundingStep a q u seed₁ seed₂ j - u j)
      ∂volume.restrict (Icc (0 : ℝ) 1)) =
        boundaryPlus u v * boundaryMinus u v * v i * v j := by
  dsimp only
  let bs := nullspaceBasis a q u
  let ws := bs.map (fun v => (boundaryPlus u v * boundaryMinus u v)⁻¹)
  let v := inverseCDF (bs.zip (ws.map (fun w => w / ws.sum))) seed₁
  change (∫ seed₂, (roundingStep a q u seed₁ seed₂ i - u i) *
    (roundingStep a q u seed₁ seed₂ j - u j)
    ∂volume.restrict (Icc (0 : ℝ) 1)) =
      boundaryPlus u v * boundaryMinus u v * v i * v j
  by_cases he : bs = []
  · have hv : v = 0 := by simp [v, ws, he, inverseCDF]
    simp [roundingStep, show nullspaceBasis a q u = [] from he, inverseCDF, hv]
  · have hv : v ∈ bs := rounding_selected_direction_mem a q u seed₁ he
    have hs : ∀ k, v k ≠ 0 → |u k| < 1 := by
      intro k hk
      by_contra hn
      exact hk (nullspaceBasis_active_support a q u v hv k hn)
    have hn : v ≠ 0 := orderedOrtho_nonzero _ v hv
    have hcoin := boundary_seed_covariance (v i) (v j) (boundaryPlus u v)
      (boundaryMinus u v) (boundaryPlus_pos u v hs hn) (boundaryMinus_pos u v hs hn)
    rw [← hcoin]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [roundingStep, ite_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    change ((if t < boundaryMinus u v / (boundaryPlus u v + boundaryMinus u v)
      then u i + boundaryPlus u v * v i else u i - boundaryMinus u v * v i) - u i) *
      ((if t < boundaryMinus u v / (boundaryPlus u v + boundaryMinus u v)
      then u j + boundaryPlus u v * v j else u j - boundaryMinus u v * v j) - u j) = _
    split_ifs <;> ring

/-- Every padded phase move preserves each fractional coordinate's mean under
its fresh coin seed, including terminal and already-finished branches. Under [the stated conditions](hyp:hu), [the asserted mathematical result follows](goal). -/
-- @node: phaseMove_seed_mean
lemma phaseMove_seed_mean (a : Fin (n / 4) → Fin n → ℝ)
    (st : RoundingState n) (seed₁ : ℝ) (j : Fin n)
    (hu : ∀ i, |st.1 i| ≤ 1) :
    (∫ seed₂, (phaseMove a st seed₁ seed₂).1 j
      ∂volume.restrict (Icc (0 : ℝ) 1)) = st.1 j := by
  by_cases hsmall : (activeIndices st.1).length ≤ st.2.1 ∧
      (activeIndices st.1).length ≤ 3
  · simp only [phaseMove, if_pos hsmall]
    cases ha : activeIndices st.1 with
    | nil =>
      simp [integral_const, measureReal_def, Real.volume_Icc]
    | cons i is =>
      by_cases hj : j = i
      · subst j
        simpa using
          terminal_seed_mean (st.1 i) (hu i)
      · simp [hj, integral_const, measureReal_def, Real.volume_Icc]
  · simpa only [phaseMove, if_neg hsmall] using
      roundingStep_seed_mean a
        (if (activeIndices st.1).length ≤ st.2.1 then (activeIndices st.1).length / 4
          else st.2.2) st.1 seed₁ j

/-- Every phase-move coordinate is integrable over its fresh coin seed. [The asserted mathematical result follows](goal). -/
-- @node: phaseMove_seed_integrable
lemma phaseMove_seed_integrable (a : Fin (n / 4) → Fin n → ℝ)
    (st : RoundingState n) (seed₁ : ℝ) (j : Fin n) :
    Integrable (fun seed₂ => (phaseMove a st seed₁ seed₂).1 j)
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  by_cases hsmall : (activeIndices st.1).length ≤ st.2.1 ∧
      (activeIndices st.1).length ≤ 3
  · simp only [phaseMove, if_pos hsmall]
    cases ha : activeIndices st.1 with
    | nil => simp
    | cons i is =>
      by_cases hj : j = i
      · subst j
        simpa using uniform_threshold_integrable ((1 + st.1 i) / 2) 1 (-1)
      · simp [hj]
  · simpa only [phaseMove, if_neg hsmall] using
      roundingStep_seed_integrable a
        (if (activeIndices st.1).length ≤ st.2.1 then (activeIndices st.1).length / 4
          else st.2.2) st.1 seed₁ j

/-- The first k moves depend only on their first 2k seeds. This is the
finite-history property needed when integrating the next independent coin. Under [the stated conditions](hyp:hseed), [the asserted mathematical result follows](goal). -/
-- @node: roundingIteration_eq_of_seed_prefix
lemma roundingIteration_eq_of_seed_prefix (a : Fin (n / 4) → Fin n → ℝ)
    (seeds seeds' : RoundingSeeds n) (k : ℕ)
    (hseed : ∀ h, h < 2 * k → roundingSeed seeds h = roundingSeed seeds' h) :
    roundingIteration a seeds k = roundingIteration a seeds' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hs := ih (fun h hh => hseed h (by omega))
    simp only [roundingIteration, hs, hseed (2 * k) (by omega),
      hseed (2 * k + 1) (by omega)]

/-- [ Changing a future seed cannot change the current fractional state.](goal) Under [the stated conditions](hyp:hj). -/
-- @node: roundingIteration_update_future
lemma roundingIteration_update_future (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k : ℕ) (j : Fin (3 * n)) (t : ℝ)
    (hj : 2 * k ≤ j.val) :
    roundingIteration a (Function.update seeds j t) k = roundingIteration a seeds k := by
  apply roundingIteration_eq_of_seed_prefix
  intro h hh
  by_cases hb : h < 3 * n
  · have hne : (⟨h, hb⟩ : Fin (3 * n)) ≠ j := by
      intro he
      have hv := congrArg Fin.val he
      dsimp at hv
      omega
    simp [roundingSeed, hb, hne]
  · simp [roundingSeed, hb]

/-- [ Integrating the next actual coin, while holding all other seeds fixed,
returns the preceding fractional coordinate.](goal) Under [the stated conditions](hyp:hk). -/
-- @node: roundingIteration_next_coin_mean
lemma roundingIteration_next_coin_mean (a : Fin (n / 4) → Fin n → ℝ)
    (seeds : RoundingSeeds n) (k : ℕ) (hk : k < n) (i : Fin n) :
    (∫ t, (roundingIteration a
      (Function.update seeds ⟨2 * k + 1, by omega⟩ t) (k + 1)).1 i
      ∂volume.restrict (Icc (0 : ℝ) 1)) = (roundingIteration a seeds k).1 i := by
  have hidx : 2 * k + 1 < 3 * n := by omega
  have hfirst : 2 * k < 3 * n := by omega
  have hne : (⟨2 * k, hfirst⟩ : Fin (3 * n)) ≠ ⟨2 * k + 1, hidx⟩ := by
    intro he
    have hv := congrArg Fin.val he
    dsimp at hv
    omega
  have hprev (t : ℝ) := roundingIteration_update_future a seeds k
    ⟨2 * k + 1, hidx⟩ t (by dsimp; omega)
  simp only [roundingIteration, hprev]
  simp only [roundingSeed, dif_pos hfirst, dif_pos hidx,
    Function.update_of_ne hne, Function.update_self]
  exact phaseMove_seed_mean a (roundingIteration a seeds k)
    (seeds ⟨2 * k, hfirst⟩) i (roundingIteration_cube_and_count a seeds k).1

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

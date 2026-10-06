module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalDeathPlugin

/-!
# Finite-grid control of the future-mark remaining mean

The remaining target has the model's Lipschitz envelope. Antitonicity of the
observable remaining mean then bounds its uniform error by errors at a finite
grid. This implements the pathwise part of roadmap equations (36)--(38),
without treating future recurrence marks as predictable.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The ordinary remaining target changes by at most the recurrence upper
bound times the elapsed time. -/
-- @node: remainingTarget_zero_increment_bound
lemma remainingTarget_zero_increment_bound (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (huv : u ≤ v) :
    |remainingTarget c P a 0 u - remainingTarget c P a 0 v| ≤
      c.lambdaMax * (v - u) := by
  have hi := modelClass_target_intervalIntegrable c P hP a
  have hiu := hi.mono_set (show uIcc u 1 ⊆ uIcc (0 : ℝ) 1 by
    rw [uIcc_of_le hu.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hu.1 le_rfl)
  have hiv := hi.mono_set (show uIcc v 1 ⊆ uIcc (0 : ℝ) 1 by
    rw [uIcc_of_le hv.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hv.1 le_rfl)
  simp only [remainingTarget, continuationWeight, if_true, sub_zero, one_mul]
  have heq : (∫ t in u..1, survival P a t * P.lam a t) -
      (∫ t in v..1, survival P a t * P.lam a t) =
      ∫ t in u..v, survival P a t * P.lam a t := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hiu.trans hiv.symm) hiv
    linarith
  rw [heq]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (C := c.lambdaMax)
    (f := fun t => survival P a t * P.lam a t) (by
      intro t ht
      rw [uIoc_of_le huv] at ht
      have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨hu.1.trans ht.1.le, ht.2.trans hv.2⟩
      have hs := survival_bounds_of_deathBounds c P hP.deathBounds a ht01
      have hl := hP.recurrenceBounds a t ht01
      have hn : 0 ≤ survival P a t * P.lam a t :=
        mul_nonneg (Real.exp_pos _).le (c.lambdaMin_pos.le.trans hl.1)
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      exact (mul_le_mul_of_nonneg_right hs.2 (c.lambdaMin_pos.le.trans hl.1)).trans
        (by simpa using hl.2))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huv)] using hb

/-- Every bounded nonnegative horizon admits a finite grid bracketing each
time with a prescribed mesh width, including both endpoints. -/
-- @node: exists_remainingMean_bracketing_grid
lemma exists_remainingMean_bracketing_grid {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) :
    ∃ G : Finset ℝ, (∀ t ∈ G, t ∈ Icc (0 : ℝ) T) ∧
      ∀ u ∈ Icc (0 : ℝ) T, ∃ l ∈ G, ∃ r ∈ G,
        l ≤ u ∧ u ≤ r ∧ r - l ≤ δ := by
  classical
  obtain ⟨m, hm⟩ := exists_nat_gt (T / δ)
  let g : ℕ → ℝ := fun j => min T ((j : ℝ) * δ)
  refine ⟨(Finset.range (m + 1)).image g, ?_, ?_⟩
  · intro t ht
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨le_min hT (mul_nonneg (Nat.cast_nonneg _) hδ.le), min_le_left _ _⟩
  · intro u hu
    let j := Nat.floor (u / δ)
    have hquot : 0 ≤ u / δ := div_nonneg hu.1 hδ.le
    have hj : (j : ℝ) ≤ u / δ := Nat.floor_le hquot
    have hjnext : u / δ < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hjm : j < m := by
      have hlt : (j : ℝ) < (m : ℝ) := hj.trans_lt
        ((div_le_div_of_nonneg_right hu.2 hδ.le).trans_lt hm)
      exact_mod_cast hlt
    have hlo : (j : ℝ) * δ ≤ u := (le_div_iff₀ hδ).mp hj
    have hhi : u ≤ ((j : ℝ) + 1) * δ := ((div_lt_iff₀ hδ).mp hjnext).le
    have hgl : g j = (j : ℝ) * δ := min_eq_right (hlo.trans hu.2)
    refine ⟨g j, Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩,
      g (j + 1), Finset.mem_image.mpr ⟨j + 1, Finset.mem_range.mpr (by omega), rfl⟩,
      ?_, ?_, ?_⟩
    · simpa only [hgl] using hlo
    · exact le_min hu.2 (by simpa using hhi)
    · have hgr : g (j + 1) ≤ ((j : ℝ) + 1) * δ := by
        simpa [g] using min_le_right T (((j + 1 : ℕ) : ℝ) * δ)
      rw [hgl]
      linarith

/-- Bracketing grid errors control the observable remaining mean everywhere
between the endpoints, using its antitonicity in time. -/
-- @node: remainingMeanHat_error_le_of_bracket
lemma remainingMeanHat_error_le_of_bracket (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory)
    {l u r ε δ : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1)
    (hlu : l ≤ u) (hur : u ≤ r) (hmesh : r - l ≤ δ)
    (hel : |remainingMeanHat c a s l - remainingTarget c P a 0 l| ≤ ε)
    (her : |remainingMeanHat c a s r - remainingTarget c P a 0 r| ≤ ε) :
    |remainingMeanHat c a s u - remainingTarget c P a 0 u| ≤
      ε + c.lambdaMax * δ := by
  have hu : u ∈ Icc (0 : ℝ) 1 := ⟨hl.1.trans hlu, hur.trans hr.2⟩
  have htL := remainingTarget_zero_increment_bound c P hP a hl hu hlu
  have htR := remainingTarget_zero_increment_bound c P hP a hu hr hur
  have hL : 0 ≤ c.lambdaMax := c.lambdaMin_pos.le.trans c.lambdaMin_lt.le
  have hlo := antitone_remainingMeanHat c a s hur
  have hhi := antitone_remainingMeanHat c a s hlu
  have hmL : c.lambdaMax * (u - l) ≤ c.lambdaMax * δ :=
    mul_le_mul_of_nonneg_left (by linarith) hL
  have hmR : c.lambdaMax * (r - u) ≤ c.lambdaMax * δ :=
    mul_le_mul_of_nonneg_left (by linarith) hL
  rw [abs_le] at hel her htL htR ⊢
  constructor <;> linarith

/-- A finite grid upgrades pointwise error bounds to a uniform bound on a
strict horizon. -/
-- @node: remainingMeanHat_uniform_error_le_of_grid
lemma remainingMeanHat_uniform_error_le_of_grid (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {n : ℕ} (s : Fin n → ObsHistory)
    {T ε δ : ℝ} (hT : T ≤ 1) (G : Finset ℝ)
    (hG : ∀ t ∈ G, t ∈ Icc (0 : ℝ) T)
    (hcover : ∀ u ∈ Icc (0 : ℝ) T, ∃ l ∈ G, ∃ r ∈ G,
      l ≤ u ∧ u ≤ r ∧ r - l ≤ δ)
    (he : ∀ t ∈ G, |remainingMeanHat c a s t - remainingTarget c P a 0 t| ≤ ε) :
    ∀ u ∈ Icc (0 : ℝ) T,
      |remainingMeanHat c a s u - remainingTarget c P a 0 u| ≤
        ε + c.lambdaMax * δ := by
  intro u hu
  obtain ⟨l, hl, r, hr, hlu, hur, hmesh⟩ := hcover u hu
  exact remainingMeanHat_error_le_of_bracket c P hP a s
    ⟨(hG l hl).1, (hG l hl).2.trans hT⟩
    ⟨(hG r hr).1, (hG r hr).2.trans hT⟩ hlu hur hmesh (he l hl) (he r hr)

/-- Uniform error events are contained in a finite union of grid error events.
This probability bound needs no independence among coefficients or grid points. -/
-- @node: remainingMeanHat_uniform_error_probability_le_grid
lemma remainingMeanHat_uniform_error_probability_le_grid
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (μ : Measure (Fin n → ObsHistory)) [IsFiniteMeasure μ]
    {T ε δ : ℝ} (hT : T ≤ 1) (G : Finset ℝ)
    (hG : ∀ t ∈ G, t ∈ Icc (0 : ℝ) T)
    (hcover : ∀ u ∈ Icc (0 : ℝ) T, ∃ l ∈ G, ∃ r ∈ G,
      l ≤ u ∧ u ≤ r ∧ r - l ≤ δ) :
    μ.real {s | ∃ u ∈ Icc (0 : ℝ) T,
      ε + c.lambdaMax * δ <
        |remainingMeanHat c a s u - remainingTarget c P a 0 u|} ≤
      ∑ t ∈ G, μ.real {s |
        ε < |remainingMeanHat c a s t - remainingTarget c P a 0 t|} := by
  classical
  apply (measureReal_mono (show {s | ∃ u ∈ Icc (0 : ℝ) T,
    ε + c.lambdaMax * δ <
      |remainingMeanHat c a s u - remainingTarget c P a 0 u|} ⊆
      ⋃ t ∈ G, {s | ε <
        |remainingMeanHat c a s t - remainingTarget c P a 0 t|} from ?_)
      (measure_ne_top μ _)).trans
    (measureReal_biUnion_finset_le G _)
  intro s hs
  by_contra hbad
  have he : ∀ t ∈ G,
      |remainingMeanHat c a s t - remainingTarget c P a 0 t| ≤ ε := by
    intro t ht
    by_contra herr
    apply hbad
    exact mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨ht, lt_of_not_ge herr⟩⟩
  obtain ⟨u, hu, herr⟩ := hs
  exact (not_lt_of_ge
    (remainingMeanHat_uniform_error_le_of_grid c P hP a s hT G hG hcover he u hu)) herr

/-- Pointwise convergence in probability of the actual remaining-mean
estimator implies uniform convergence on a strict horizon. The finite-grid
argument applies to its antitonicity in time, rather than in sample size. -/
-- @node: remainingMeanHat_uniform_probability_tendsto_of_pointwise
lemma remainingMeanHat_uniform_probability_tendsto_of_pointwise
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1)
    (hpoint : ∀ u ∈ Icc (0 : ℝ) T, ∀ η : ℝ, 0 < η →
      Tendsto (fun n => (sampleLaw P n).real {s |
        η < |remainingMeanHat c a s u - remainingTarget c P a 0 u|})
        atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (sampleLaw P n).real {s | ∃ u ∈ Icc (0 : ℝ) T,
        ε < |remainingMeanHat c a s u - remainingTarget c P a 0 u|})
        atTop (nhds 0) := by
  intro ε hε
  classical
  have hL : 0 < c.lambdaMax := c.lambdaMin_pos.trans c.lambdaMin_lt
  let δ := ε / (2 * c.lambdaMax)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hL)
  obtain ⟨G, hG, hcover⟩ := exists_remainingMean_bracketing_grid hT0 hδ
  have hmesh : ε / 2 + c.lambdaMax * δ = ε := by dsimp [δ]; field_simp; ring
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have hbound (n : ℕ) : (sampleLaw P n).real {s | ∃ u ∈ Icc (0 : ℝ) T,
      ε < |remainingMeanHat c a s u - remainingTarget c P a 0 u|} ≤
      ∑ t ∈ G, (sampleLaw P n).real {s |
        ε / 2 < |remainingMeanHat c a s t - remainingTarget c P a 0 t|} := by
    letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
    simpa only [hmesh] using remainingMeanHat_uniform_error_probability_le_grid
      c P hP a (sampleLaw P n) (ε := ε / 2) hT1 G hG hcover
  have hsum : Tendsto (fun n => ∑ t ∈ G, (sampleLaw P n).real {s |
      ε / 2 < |remainingMeanHat c a s t - remainingTarget c P a 0 t|})
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum G (fun t ht =>
      hpoint t (hG t ht) (ε / 2) (half_pos hε))
  exact squeeze_zero (fun n => measureReal_nonneg) hbound hsum

/-- Grid errors suffice for the pathwise future-mark death studentizer
comparison on a positive-risk event. -/
-- @node: localizedDeathVariation_plugin_error_le_of_grid
lemma localizedDeathVariation_plugin_error_le_of_grid
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P) (a : Arm)
    {n : ℕ} (hn : 0 < n) (s : Fin n → ObsHistory) {T ε δ q : ℝ}
    (hT : T ≤ 1) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hq : 0 < q)
    (hExit : ∀ i, 0 ≤ (s i).exit) (G : Finset ℝ)
    (hG : ∀ t ∈ G, t ∈ Icc (0 : ℝ) T)
    (hcover : ∀ u ∈ Icc (0 : ℝ) T, ∃ l ∈ G, ∃ r ∈ G,
      l ≤ u ∧ u ≤ r ∧ r - l ≤ δ)
    (he : ∀ t ∈ G, |remainingMeanHat c a s t - remainingTarget c P a 0 t| ≤ ε)
    (hr : ∀ i, (s i).treatment = a → (s i).deathInd → (s i).exit ≤ T →
      (n : ℝ) * q ≤ riskSet a s (s i).exit) :
    |localizedDeathVariation a s T (remainingMeanHat c a s) -
      localizedDeathVariation a s T (remainingTarget c P a 0)| ≤
      2 * c.lambdaMax * (ε + c.lambdaMax * δ) * q⁻¹ ^ 2 := by
  apply localizedDeathVariation_plugin_error_le_of_riskFraction_lower
    c P hP a hn s hT
    (add_nonneg hε (mul_nonneg (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) hδ))
    hq hExit
    (remainingMeanHat_uniform_error_le_of_grid c P hP a s hT G hG hcover he) hr

end CausalSmith.Stat.RecurrentEndpointCensorFrontier

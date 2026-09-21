/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Minimax.SideInformation.Finite.Comparison
public import Causalean.Stat.Minimax.SideInformation.Finite.Concentration
public import Causalean.Stat.Minimax.SideInformation.Finite.Selector

/-!
# Finite-cover achievability

This module packages the compact finite-cover selection argument and combines
it with empirical finite-category concentration to prove the upper asymptotic
comparison.
-/

public section

open Filter Topology Set

namespace Causalean.Stat.Minimax.FiniteSideInformation

variable {Theta X C : Type*} [TopologicalSpace Theta] [CompactSpace Theta]
  [Nonempty Theta] [Fintype X] [Fintype C] [DecidableEq C] [Nonempty C]

/-- On a [compact parameter space](hyp:Theta), under [continuous simplex-valid label and side
coordinates and a continuous bounded target](hyp:hp,hq,hpcont,hqcont,htau,hlu,htau_mem), every
[positive tolerance](hyp:hε) has a [finite family of local decisions](goal): smaller side-law
balls cover the model with a uniform positive margin, and each decision has risk within the
tolerance of the exact-side minimax value throughout its larger ball. -/
theorem finiteCover_approximateDecision
    (p : Theta → X → ℝ) (q : Theta → C → ℝ) (tau : Theta → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (hpcont : ∀ x, Continuous (fun theta ↦ p theta x))
    (hqcont : ∀ c, Continuous (fun theta ↦ q theta c)) (htau : Continuous tau)
    (hlu : l ≤ u) (htau_mem : ∀ theta, tau theta ∈ Set.Icc l u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (hk : 0 < k) (center : Fin k → Theta)
      (decision : Fin k → BoundedDecision X l u) (radius : Fin k → ℝ) (η : ℝ),
      0 < η ∧ (∀ i, η < radius i) ∧
      (∀ theta, ∃ i, dist (sidePmf q hq theta) (sidePmf q hq (center i)) < radius i - η) ∧
      (∀ i theta, dist (sidePmf q hq theta) (sidePmf q hq (center i)) < radius i →
        finiteSquaredRisk p tau (decision i) theta ≤
          exactSideMinimaxValue p q hq tau l u + ε) := by
  -- Proof plan: shrinking-fiber convergence yields one good radius and decision at each center;
  -- `exactSideMinimaxValue_eq_iSup_fiber` bounds every fiber value by the exact benchmark.
  -- For each center, apply `localMinimaxValue_tendsto_fiber` and then `ciInf_lt_iff` to choose
  -- a positive reciprocal radius and a decision whose worst-case risk on the corresponding closed
  -- side-law ball is strictly below the benchmark plus ε.  The open balls of half those radii cover
  -- `univ`; use `IsCompact.elim_finite_subcover` to obtain a nonempty `Finset` of centers, enumerate
  -- it by `Fin k`, and take η to be the minimum of their positive half-radii.  This gives both the
  -- strict cover margin and the larger-ball risk guarantee.  The risk bounds in `Risk.lean` discharge
  -- all finiteness hypotheses for the `toReal` bridge from the extended minimax value.
  classical
  letI : Nonempty (BoundedDecision X l u) :=
    ⟨fun _ ↦ ⟨l, le_rfl, hlu⟩⟩
  have hrisk (d : BoundedDecision X l u) (theta : Theta) :
      0 ≤ finiteSquaredRisk p tau d theta ∧
        finiteSquaredRisk p tau d theta ≤ (u - l) ^ 2 :=
    finiteSquaredRisk_bounds p tau (fun theta x ↦ (hp theta).1 x)
      (fun theta ↦ (hp theta).2) hlu htau_mem d theta
  let d0 : BoundedDecision X l u := fun _ ↦ ⟨l, le_rfl, hlu⟩
  have hfiber_bdd : BddAbove
      (Set.range (fun theta0 : Theta ↦ fiberMinimaxValue p tau q hq l u theta0)) := by
    refine ⟨(u - l) ^ 2, ?_⟩
    rintro _ ⟨theta0, rfl⟩
    let fiberRisk := fun (d : BoundedDecision X l u)
      (theta : {theta : Theta // sidePmf q hq theta = sidePmf q hq theta0}) ↦
        finiteSquaredRisk p tau d theta.1
    letI : Nonempty {theta : Theta //
        sidePmf q hq theta = sidePmf q hq theta0} := ⟨⟨theta0, rfl⟩⟩
    have hnonneg : ∀ (d : BoundedDecision X l u)
        (theta : {theta : Theta // sidePmf q hq theta = sidePmf q hq theta0}),
        0 ≤ fiberRisk d theta := fun d theta ↦ (hrisk d theta.1).1
    have hupper : ∀ theta : {theta : Theta //
        sidePmf q hq theta = sidePmf q hq theta0},
        fiberRisk d0 theta ≤ (u - l) ^ 2 :=
      fun theta ↦ (hrisk d0 theta.1).2
    have hbdd (d : BoundedDecision X l u) :
        BddAbove (Set.range (fiberRisk d)) := by
      refine ⟨(u - l) ^ 2, ?_⟩
      rintro _ ⟨theta, rfl⟩
      exact (hrisk d theta.1).2
    have hbridge := minimaxValueENNRealOfReal_toReal_of_nonneg_of_bddAbove hnonneg hbdd
    change (minimaxValueENNRealOfReal fiberRisk).toReal ≤ (u - l) ^ 2
    rw [hbridge]
    calc
      Causalean.Stat.minimaxValueReal fiberRisk ≤
          Causalean.Stat.worstCaseRiskReal fiberRisk d0 :=
        Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
          (risk := fiberRisk) hnonneg d0
      _ ≤ (u - l) ^ 2 :=
        Causalean.Stat.worstCaseRisk_le hupper
  have hfiber_le_exact (theta0 : Theta) :
      fiberMinimaxValue p tau q hq l u theta0 ≤
        exactSideMinimaxValue p q hq tau l u := by
    rw [exactSideMinimaxValue_eq_iSup_fiber p q tau hp hq hpcont hqcont htau hlu htau_mem]
    exact le_ciSup hfiber_bdd theta0
  have hlocal (theta0 : Theta) : ∃ (d : BoundedDecision X l u) (r : ℝ),
      0 < r ∧ ∀ theta,
        dist (sidePmf q hq theta) (sidePmf q hq theta0) < r →
          finiteSquaredRisk p tau d theta ≤
            exactSideMinimaxValue p q hq tau l u + ε := by
    have hconv := localMinimaxValue_tendsto_fiber p q tau hp hq hpcont hqcont htau
      hlu htau_mem theta0
    have heventually : ∀ᶠ n : ℕ in atTop,
        localMinimaxValue p tau q hq l u (1 / (n + 1 : ℝ)) theta0 <
          fiberMinimaxValue p tau q hq l u theta0 + ε / 2 :=
      hconv.eventually_lt_const (by linarith)
    obtain ⟨n, hn⟩ := heventually.exists
    let r : ℝ := 1 / (n + 1 : ℝ)
    have hr : 0 < r := by
      dsimp [r]
      positivity
    let localRisk := fun (d : BoundedDecision X l u)
      (theta : {theta : Theta //
          dist (sidePmf q hq theta) (sidePmf q hq theta0) ≤ r}) ↦
        finiteSquaredRisk p tau d theta.1
    letI : Nonempty {theta : Theta //
        dist (sidePmf q hq theta) (sidePmf q hq theta0) ≤ r} :=
      ⟨⟨theta0, by simp [hr.le]⟩⟩
    have hbddBelow : BddBelow
        (Set.range (Causalean.Stat.worstCaseRiskReal localRisk)) :=
      Causalean.Stat.bddBelow_range_worstCaseRisk
        (fun d theta ↦ (hrisk d theta.1).1)
    have hvalue : (⨅ d, Causalean.Stat.worstCaseRiskReal localRisk d) <
        exactSideMinimaxValue p q hq tau l u + ε := by
      have hn' : localMinimaxValue p tau q hq l u r theta0 <
          fiberMinimaxValue p tau q hq l u theta0 + ε / 2 := by
        simpa [r] using hn
      have hlocal_lt : localMinimaxValue p tau q hq l u r theta0 <
          exactSideMinimaxValue p q hq tau l u + ε := by
        linarith [hfiber_le_exact theta0]
      have hnonneg : ∀ d theta, 0 ≤ localRisk d theta :=
        fun d theta ↦ (hrisk d theta.1).1
      have hbdd (d : BoundedDecision X l u) :
          BddAbove (Set.range (localRisk d)) := by
        refine ⟨(u - l) ^ 2, ?_⟩
        rintro _ ⟨theta, rfl⟩
        exact (hrisk d theta.1).2
      have hbridge := minimaxValueENNRealOfReal_toReal_of_nonneg_of_bddAbove hnonneg hbdd
      have hlocal_lt' : minimaxValueReal localRisk <
          exactSideMinimaxValue p q hq tau l u + ε := by
        have : (minimaxValueENNRealOfReal localRisk).toReal <
            exactSideMinimaxValue p q hq tau l u + ε := by
          simpa [localMinimaxValue, localRisk] using hlocal_lt
        rw [hbridge] at this
        exact this
      simpa [minimaxValueReal] using hlocal_lt'
    obtain ⟨d, hd⟩ := (ciInf_lt_iff hbddBelow).1 hvalue
    refine ⟨d, r, hr, ?_⟩
    intro theta htheta
    have hbddAbove : BddAbove (Set.range (localRisk d)) := by
      refine ⟨(u - l) ^ 2, ?_⟩
      rintro _ ⟨theta', rfl⟩
      exact (hrisk d theta'.1).2
    have hpoint := Causalean.Stat.le_worstCaseRisk hbddAbove
      (⟨theta, htheta.le⟩ : {theta : Theta //
        dist (sidePmf q hq theta) (sidePmf q hq theta0) ≤ r})
    exact (hpoint.trans_lt hd).le
  let chosenDecision : Theta → BoundedDecision X l u :=
    fun theta ↦ Classical.choose (hlocal theta)
  let chosenRadius : Theta → ℝ :=
    fun theta ↦ Classical.choose (Classical.choose_spec (hlocal theta))
  have hchosen (theta0 : Theta) :
      0 < chosenRadius theta0 ∧ ∀ theta,
        dist (sidePmf q hq theta) (sidePmf q hq theta0) < chosenRadius theta0 →
          finiteSquaredRisk p tau (chosenDecision theta0) theta ≤
            exactSideMinimaxValue p q hq tau l u + ε :=
    Classical.choose_spec (Classical.choose_spec (hlocal theta0))
  let U : Theta → Set Theta := fun theta0 ↦
    (sidePmf q hq) ⁻¹' Metric.ball (sidePmf q hq theta0) (chosenRadius theta0 / 2)
  have hsideCont : Continuous (sidePmf q hq) := continuous_sidePmf q hq hqcont
  have hUopen (theta0 : Theta) : IsOpen (U theta0) :=
    Metric.isOpen_ball.preimage hsideCont
  have hUcover (theta : Theta) : theta ∈ U theta := by
    simp [U, hchosen theta |>.1]
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUopen
    (fun theta _ ↦ Set.mem_iUnion.mpr ⟨theta, hUcover theta⟩)
  have ht_nonempty : t.Nonempty := by
    let theta : Theta := Classical.choice inferInstance
    obtain ⟨theta0, htheta0t, _⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ theta))
    exact ⟨theta0, htheta0t⟩
  let halfRadius : Theta → ℝ := fun theta ↦ chosenRadius theta / 2
  obtain ⟨thetaMin, hthetaMin, hmin⟩ :=
    Finset.exists_min_image t halfRadius ht_nonempty
  refine ⟨t.card, Finset.card_pos.mpr ht_nonempty,
    fun i ↦ (t.equivFin.symm i).1,
    fun i ↦ chosenDecision (t.equivFin.symm i).1,
    fun i ↦ chosenRadius (t.equivFin.symm i).1,
    halfRadius thetaMin, ?_, ?_, ?_, ?_⟩
  · exact half_pos (hchosen thetaMin).1
  · intro i
    have hhalf_le := hmin (t.equivFin.symm i).1 (t.equivFin.symm i).2
    dsimp [halfRadius] at hhalf_le ⊢
    linarith [(hchosen (t.equivFin.symm i).1).1]
  · intro theta
    obtain ⟨theta0, htheta0t, hthetaU⟩ :=
      Set.mem_iUnion₂.mp (ht (Set.mem_univ theta))
    let i : Fin t.card := t.equivFin ⟨theta0, htheta0t⟩
    refine ⟨i, ?_⟩
    have hi : (t.equivFin.symm i).1 = theta0 := by
      exact congrArg Subtype.val (t.equivFin.symm_apply_apply ⟨theta0, htheta0t⟩)
    have hdist : dist (sidePmf q hq theta) (sidePmf q hq theta0) <
        chosenRadius theta0 / 2 := by
      simpa [U, Metric.mem_ball] using hthetaU
    have heta_le : halfRadius thetaMin ≤ chosenRadius theta0 / 2 := by
      exact hmin theta0 htheta0t
    dsimp [i]
    rw [hi]
    dsimp [halfRadius] at heta_le ⊢
    linarith
  · intro i theta htheta
    exact (hchosen (t.equivFin.symm i).1).2 theta htheta

/-- Under the [compact continuous finite-model assumptions](hyp:hp,hq,hpcont,hqcont,htau,hlu,htau_mem),
the [limsup of empirical-side minimax values is at most the exact-side minimax value](goal).
The proof uses a measurable finite-cover selector and the uniform empirical L1 Hoeffding tail. -/
theorem empiricalSideMinimax_limsup_le_exact
    (p : Theta → X → ℝ) (q : Theta → C → ℝ) (tau : Theta → ℝ)
    (hp : ∀ theta, p theta ∈ stdSimplex ℝ X)
    (hq : ∀ theta, q theta ∈ stdSimplex ℝ C)
    (hpcont : ∀ x, Continuous (fun theta ↦ p theta x))
    (hqcont : ∀ c, Continuous (fun theta ↦ q theta c)) (htau : Continuous tau)
    (hlu : l ≤ u) (htau_mem : ∀ theta, tau theta ∈ Set.Icc l u) :
    Filter.limsup (fun m : ℕ ↦ empiricalSideMinimaxValue p q hq tau l u m) atTop ≤
      exactSideMinimaxValue p q hq tau l u := by
  -- Proof plan: for a cover with margin η, run `exists_measurable_finiteCoverSelector` with radii
  -- `radius i - η / 2`, and select from `empiricalPmf C hm z`.  On `empiricalL1 < η / 2`, the cover
  -- margin makes the empirical law belong to a selector ball and the triangle inequality puts the
  -- true law in the selected larger ball.  Rewrite the empirical risk as a sum over samples of
  -- `finiteSquaredRisk`; bound good samples by the local guarantee, bad samples by `(u-l)^2`, and
  -- apply `empiricalL1_tail`.  The resulting uniform bound is the benchmark plus ε plus the squared
  -- width times `empiricalL1_tail_bound_tendsto_zero`; use `limsup_le_iff'` and the global risk bounds.
  classical
  let value := exactSideMinimaxValue p q hq tau l u
  let widthSq := (u - l) ^ 2
  have hwidthSq : 0 ≤ widthSq := by
    dsimp [widthSq]
    positivity
  have hemp_nonneg (m : ℕ) (d : EmpiricalSideProcedure X C m l u) (theta : Theta) :
      0 ≤ empiricalSideRisk p q hq tau m d theta :=
    empiricalSideRisk_nonneg p q hp hq tau m d theta
  have hemp_bdd (m : ℕ) (d : EmpiricalSideProcedure X C m l u) :
      BddAbove (Set.range (empiricalSideRisk p q hq tau m d)) := by
    refine ⟨widthSq, ?_⟩
    rintro _ ⟨theta, rfl⟩
    exact empiricalSideRisk_le p q hp hq tau hlu htau_mem m d theta
  have hemp_bridge (m : ℕ) :
      (minimaxValueENNRealOfReal (empiricalSideRisk p q hq tau m)).toReal =
        minimaxValueReal (empiricalSideRisk p q hq tau m) :=
    minimaxValueENNRealOfReal_toReal_of_nonneg_of_bddAbove (hemp_nonneg m) (hemp_bdd m)
  have hminimax_nonneg (m : ℕ) :
      0 ≤ empiricalSideMinimaxValue p q hq tau l u m := by
    unfold empiricalSideMinimaxValue
    change 0 ≤ Causalean.Stat.minimaxValueReal (empiricalSideRisk p q hq tau m)
    exact Causalean.Stat.minimaxValue_nonneg (hemp_nonneg m)
  have hminimax_le (m : ℕ) :
      empiricalSideMinimaxValue p q hq tau l u m ≤ widthSq := by
    let d0 : EmpiricalSideProcedure X C m l u := fun _ _ ↦ ⟨l, le_rfl, hlu⟩
    unfold empiricalSideMinimaxValue
    change Causalean.Stat.minimaxValueReal (empiricalSideRisk p q hq tau m) ≤ widthSq
    calc
      Causalean.Stat.minimaxValueReal (empiricalSideRisk p q hq tau m) ≤
          Causalean.Stat.worstCaseRiskReal (empiricalSideRisk p q hq tau m) d0 :=
        Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg (hemp_nonneg m) d0
      _ ≤ widthSq := Causalean.Stat.worstCaseRisk_le fun theta ↦ by
        exact empiricalSideRisk_le p q hp hq tau hlu htau_mem m d0 theta
  have hcobounded : Filter.IsCoboundedUnder (fun x y : ℝ ↦ x ≤ y) atTop
      (fun m : ℕ ↦ empiricalSideMinimaxValue p q hq tau l u m) :=
    Filter.isCoboundedUnder_le_of_le atTop hminimax_nonneg
  have hbounded : Filter.IsBoundedUnder (fun x y : ℝ ↦ x ≤ y) atTop
      (fun m : ℕ ↦ empiricalSideMinimaxValue p q hq tau l u m) :=
    Filter.isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall hminimax_le)
  apply (Filter.limsup_le_iff' hcobounded hbounded).2
  intro y hy
  let ε := (y - value) / 2
  have hε : 0 < ε := by
    dsimp [ε, value]
    linarith
  obtain ⟨k, hk, center, decision, radius, η, hη, hradius, hcover, hrisk⟩ :=
    finiteCover_approximateDecision p q tau hp hq hpcont hqcont htau hlu htau_mem hε
  have hselectorRadius (i : Fin k) : 0 < radius i - η / 2 := by
    linarith [hradius i]
  obtain ⟨select, _hselect_meas, hselect⟩ :=
    exists_measurable_finiteCoverSelector k hk
      (fun i ↦ sidePmf q hq (center i)) (fun i ↦ radius i - η / 2)
      hselectorRadius
  let tail : ℕ → ℝ := fun m ↦
    2 * Fintype.card C * Real.exp (-2 * m * ((η / 2) / Fintype.card C) ^ 2)
  have htail_zero : Tendsto (fun m ↦ widthSq * tail m) atTop (nhds 0) := by
    simpa [tail] using
      (empiricalL1_tail_bound_tendsto_zero C (half_pos hη)).const_mul widthSq
  have htail_small : ∀ᶠ m : ℕ in atTop, widthSq * tail m < ε :=
    htail_zero.eventually_lt_const hε
  filter_upwards [htail_small, eventually_atTop.2 ⟨1, fun m hm ↦ by omega⟩] with m htail_m hm
  let d : EmpiricalSideProcedure X C m l u := fun x z ↦
    decision (select (empiricalPmf C hm z)) x
  have hrisk_pointwise (theta : Theta) (z : Fin m → C) :
      finiteSquaredRisk p tau
          (decision (select (empiricalPmf C hm z))) theta ≤
        value + ε +
          (if η / 2 ≤ empiricalL1 C hm z (sidePmf q hq theta) then widthSq else 0) := by
    by_cases hbad : η / 2 ≤ empiricalL1 C hm z (sidePmf q hq theta)
    · rw [if_pos hbad]
      have hlocalUpper := finiteSquaredRisk_bounds p tau
        (fun theta x ↦ (hp theta).1 x) (fun theta ↦ (hp theta).2)
        hlu htau_mem (decision (select (empiricalPmf C hm z))) theta |>.2
      have hvalue_nonneg : 0 ≤ value := by
        dsimp [value]
        unfold exactSideMinimaxValue
        apply Causalean.Stat.minimaxValue_nonneg
        intro d theta
        unfold exactSideRisk
        exact Finset.sum_nonneg fun x _ ↦ mul_nonneg ((hp theta).1 x) (sq_nonneg _)
      linarith
    · rw [if_neg hbad, add_zero]
      have hgood : empiricalL1 C hm z (sidePmf q hq theta) < η / 2 :=
        lt_of_not_ge hbad
      obtain ⟨i, hi⟩ := hcover theta
      have hemp_center :
          dist (empiricalPmf C hm z) (sidePmf q hq (center i)) < radius i - η / 2 := by
        calc
          dist (empiricalPmf C hm z) (sidePmf q hq (center i)) ≤
              dist (empiricalPmf C hm z) (sidePmf q hq theta) +
                dist (sidePmf q hq theta) (sidePmf q hq (center i)) := dist_triangle _ _ _
          _ < η / 2 + (radius i - η) :=
            add_lt_add
              ((dist_empiricalPmf_le_empiricalL1 C hm z
                (sidePmf q hq theta)).trans_lt hgood) hi
          _ = radius i - η / 2 := by ring
      have hselected := hselect (empiricalPmf C hm z) ⟨i, hemp_center⟩
      have htrue_selected :
          dist (sidePmf q hq theta)
              (sidePmf q hq (center (select (empiricalPmf C hm z)))) <
            radius (select (empiricalPmf C hm z)) := by
        calc
          dist (sidePmf q hq theta)
              (sidePmf q hq (center (select (empiricalPmf C hm z)))) ≤
              dist (sidePmf q hq theta) (empiricalPmf C hm z) +
                dist (empiricalPmf C hm z)
                  (sidePmf q hq (center (select (empiricalPmf C hm z)))) := dist_triangle _ _ _
          _ < η / 2 + (radius (select (empiricalPmf C hm z)) - η / 2) := by
            apply add_lt_add
            · simpa [dist_comm] using
                (dist_empiricalPmf_le_empiricalL1 C hm z
                  (sidePmf q hq theta)).trans_lt hgood
            · exact hselected
          _ = radius (select (empiricalPmf C hm z)) := by ring
      simpa [value] using hrisk (select (empiricalPmf C hm z)) theta htrue_selected
  have hrisk_d (theta : Theta) :
      empiricalSideRisk p q hq tau m d theta ≤ value + ε + widthSq * tail m := by
    have hrearrange :
        empiricalSideRisk p q hq tau m d theta =
          ∑ z : Fin m → C, productProbability C (sidePmf q hq theta) z *
            finiteSquaredRisk p tau
              (decision (select (empiricalPmf C hm z))) theta := by
      unfold empiricalSideRisk finiteSquaredRisk
      simp only [d]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hrearrange]
    calc
      (∑ z : Fin m → C, productProbability C (sidePmf q hq theta) z *
          finiteSquaredRisk p tau
            (decision (select (empiricalPmf C hm z))) theta) ≤
          ∑ z : Fin m → C, productProbability C (sidePmf q hq theta) z *
            (value + ε +
              if η / 2 ≤ empiricalL1 C hm z (sidePmf q hq theta) then widthSq else 0) := by
        apply Finset.sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left (hrisk_pointwise theta z)
          (productProbability_nonneg C (sidePmf q hq theta) z)
      _ = value + ε + widthSq *
          (∑ z : Fin m → C,
            if η / 2 ≤ empiricalL1 C hm z (sidePmf q hq theta) then
              productProbability C (sidePmf q hq theta) z else 0) := by
        have hconst :
            (∑ z : Fin m → C,
              productProbability C (sidePmf q hq theta) z * (value + ε)) =
                value + ε := by
          rw [← Finset.sum_mul, sum_productProbability, one_mul]
        have hbadfactor :
            (∑ z : Fin m → C,
              productProbability C (sidePmf q hq theta) z *
                (if η / 2 ≤ empiricalL1 C hm z (sidePmf q hq theta) then
                  widthSq else 0)) =
              widthSq * (∑ z : Fin m → C,
                if η / 2 ≤ empiricalL1 C hm z (sidePmf q hq theta) then
                  productProbability C (sidePmf q hq theta) z else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          by_cases hz : η / 2 ≤ empiricalL1 C hm z (sidePmf q hq theta) <;>
            simp [hz, mul_comm]
        rw [show (∑ z : Fin m → C,
              productProbability C (sidePmf q hq theta) z *
                (value + ε +
                  if η / 2 ≤ empiricalL1 C hm z (sidePmf q hq theta) then
                    widthSq else 0)) =
              (∑ z : Fin m → C,
                productProbability C (sidePmf q hq theta) z * (value + ε)) +
              ∑ z : Fin m → C,
                productProbability C (sidePmf q hq theta) z *
                  (if η / 2 ≤ empiricalL1 C hm z (sidePmf q hq theta) then
                    widthSq else 0) by
              simp_rw [mul_add]
              exact Finset.sum_add_distrib]
        rw [hconst, hbadfactor]
      _ ≤ value + ε + widthSq * tail m := by
        simpa [tail, add_comm] using
          (add_le_add_left
            (mul_le_mul_of_nonneg_left
              (empiricalL1_tail C hm (sidePmf q hq theta) (half_pos hη)) hwidthSq)
            (value + ε))
  unfold empiricalSideMinimaxValue
  change Causalean.Stat.minimaxValueReal (empiricalSideRisk p q hq tau m) ≤ y
  calc
    Causalean.Stat.minimaxValueReal (empiricalSideRisk p q hq tau m) ≤
        Causalean.Stat.worstCaseRiskReal (empiricalSideRisk p q hq tau m) d :=
      Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg (hemp_nonneg m) d
    _ ≤ value + ε + widthSq * tail m := Causalean.Stat.worstCaseRisk_le hrisk_d
    _ ≤ y := by
      dsimp [ε, value] at htail_m ⊢
      linarith

end Causalean.Stat.Minimax.FiniteSideInformation

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Conditional / cross-fit `O_p` rate for centered empirical means

Paper-agnostic workhorse behind every cross-fit / DML
"remainder-is-negligible" step: the centered empirical mean of a (possibly
cross-fit / conditional) score is `O_p(n^{-1/2} · (second-moment)^{1/2})`.

The results use the fixed-law, sequence-indexed predicate
`Causalean.Stat.IsBigOp`.  The filter-general, row-varying interface lives in
`Stat/Limit/StochasticOrder.lean`; compatibility between those interfaces is a
separate migration concern.  The conditional second-moment estimate is the existing engine
`Causalean.Mathlib.iid_centered_sum_sq_lintegral_le` (which already kills the
cross terms via the conditional product law).  What this file adds is:

* a small `IsBigOp` rate-algebra API (`mono_rate`, `scale_rate`,
  `const_rate_collapse`, `const_mul`, `add'`);
* the **Markov primitive** `IsBigOp.of_sq_lintegral_le`: a deterministic
  `L²`-second-moment envelope `∫⁻ (Xₙ)² ≤ Vₙ` yields `Xₙ = O_p(√Vₙ)`.  This is
  the step previously inlined (privately) in
  `Estimation/OrthogonalMoments/DMLCrossFit.lean`;
* **Lemma B** `isBigOp_centered_crossFit_sum`: the conditional / cross-fit
  lift — eval fold independent of a sub-σ-field `m_A`, nuisance `m_A`-measurable
  ⇒ the centered fold sum is `O_p(√Vₙ)` for any deterministic envelope `Vₙ`
  dominating `∫_Ω ‖g_n ω‖²_{L²(P)} dμ`;
* **Lemma A** the unconditional i.i.d. corollary: `∫(ℙₙf − m)² ≤ E_P[f²]/n`,
  the Chebyshev tail, and `(ℙₙf − m) = O_p(√(E_P[f²]/n))`.

The file is estimand-agnostic; the weak-overlap clipped-AIPW upper rate is just
the first downstream consumer.
-/

module
public import Causalean.Stat.Limit.Convergence
public import Causalean.Stat.Sample
public import Causalean.Mathlib.Probability.IdentDistrib.CenteredSum
public import Mathlib.Probability.Independence.Basic

/-!
This file provides reusable stochastic-order algebra and centered empirical-mean
rate bounds.  It extends `IsBigOp` with monotonicity, scaling, sum, finite-sum,
and product rules; proves `IsBigOp.of_sq_lintegral_le`, a Markov/Chebyshev
primitive from deterministic second-moment envelopes; proves the cross-fit fold
rate `isBigOp_centered_crossFit_sum`; and gives the i.i.d. sample-mean
corollaries `IIDSample.sampleMean_sub_sq_lintegral_le`,
`IIDSample.sampleMean_sub_meas_ge_le`, and `IIDSample.sampleMean_sub_isBigOp`.
-/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

/-! ## Rate algebra for `IsBigOp`

Small reusable API on the existing `O_p` predicate: weaken to a larger rate,
absorb a positive constant rate factor, collapse a constant rate to `1`, pull a
constant multiple through, and add two `O_p` bounds at the sum of their rates.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {Xn Yn : ℕ → Ω → ℝ} {rn sn : ℕ → ℝ}

/-- **Weaken to a larger rate.**  `O_p(rₙ)` with `0 ≤ rₙ ≤ sₙ` is `O_p(sₙ)`:
a larger envelope is a weaker statement. -/
theorem IsBigOp.mono_rate (hrn : ∀ n, 0 ≤ rn n) (hle : ∀ n, rn n ≤ sn n)
    (h : IsBigOp Xn rn μ) : IsBigOp Xn sn μ := by
  intro δ hδ
  obtain ⟨M, hM, htail⟩ := h δ hδ
  refine ⟨M, hM, ?_⟩
  filter_upwards [htail] with n hn
  refine (measure_mono fun ω hω => ?_).trans hn
  exact (mul_le_mul_of_nonneg_left (hle n) hM.le).trans hω

/-- **Absorb a positive constant rate factor.**  `O_p(c · rₙ)` with `c > 0` is
`O_p(rₙ)`; the constant is absorbed into the witness `M`. -/
theorem IsBigOp.scale_rate {c : ℝ} (hc : 0 < c)
    (h : IsBigOp Xn (fun n => c * rn n) μ) : IsBigOp Xn rn μ := by
  intro δ hδ
  obtain ⟨M, hM, htail⟩ := h δ hδ
  refine ⟨M * c, mul_pos hM hc, ?_⟩
  simpa only [mul_assoc] using htail

/-- **Collapse a constant rate to `1`.**  For a *fixed* nonnegative `N`,
`O_p(fun _ => N)` is `O_p(fun _ => 1)`: a constant scale only changes the
witness `M`.  Used to normalize the fold-sum `O_p` bounds to the canonical
unit rate consumed by the cross-fitted DML proofs. -/
theorem IsBigOp.const_rate_collapse {N : ℝ} (hN : 0 ≤ N)
    (h : IsBigOp Xn (fun _ => N) μ) : IsBigOp Xn (fun _ => (1 : ℝ)) μ := by
  intro δ hδ
  obtain ⟨M, hM, htail⟩ := h δ hδ
  refine ⟨M * N + 1, by positivity, ?_⟩
  filter_upwards [htail] with n hn
  refine (measure_mono fun ω hω => ?_).trans hn
  change M * N ≤ ‖Xn n ω‖
  exact (by simpa using hω : M * N + 1 ≤ ‖Xn n ω‖).trans' (by linarith)

/-- **Constant multiple.**  If `Xₙ = O_p(rₙ)` then `c · Xₙ = O_p(rₙ)` for any
fixed scalar `c`. -/
theorem IsBigOp.const_mul (c : ℝ) (h : IsBigOp Xn rn μ) :
    IsBigOp (fun n ω => c * Xn n ω) rn μ := by
  intro δ hδ
  obtain ⟨M, hM, htail⟩ := h δ hδ
  by_cases hc : c = 0
  · refine ⟨M, hM, ?_⟩
    filter_upwards [htail] with n hn
    refine (measure_mono fun ω hω => ?_).trans hn
    have hω' : M * rn n ≤ 0 := by simpa [hc] using hω
    exact hω'.trans (norm_nonneg (Xn n ω))
  · refine ⟨|c| * M, mul_pos (abs_pos.mpr hc) hM, ?_⟩
    filter_upwards [htail] with n hn
    have hset :
        {ω | (|c| * M) * rn n ≤ ‖c * Xn n ω‖} =
          {ω | M * rn n ≤ ‖Xn n ω‖} := by
      ext ω
      simp only [Set.mem_setOf_eq, Real.norm_eq_abs, abs_mul]
      constructor <;> intro hω
      · nlinarith [abs_pos.mpr hc]
      · simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hω (abs_nonneg c)
    rw [hset]
    exact hn

/-- **Additivity at the sum rate.**  `O_p(rₙ) + O_p(sₙ) = O_p(rₙ + sₙ)`, for
nonnegative rates.  (`IsBigOp.add` is the special case `rₙ = sₙ`.) -/
theorem IsBigOp.add' (hrn : ∀ n, 0 ≤ rn n) (hsn : ∀ n, 0 ≤ sn n)
    (hX : IsBigOp Xn rn μ) (hY : IsBigOp Yn sn μ) :
    IsBigOp (fun n ω => Xn n ω + Yn n ω) (fun n => rn n + sn n) μ := by
  apply Modes.BoundedInProbability.add
  · exact IsBigOp.mono_rate hrn (fun n => by linarith [hsn n]) hX
  · exact IsBigOp.mono_rate hsn (fun n => by linarith [hrn n]) hY

/-- If `|Xₙ| ≤ |Yₙ|` pointwise and `Yₙ = O_p(rₙ)`, then `Xₙ = O_p(rₙ)`. -/
theorem IsBigOp.of_abs_le (h : ∀ n ω, |Xn n ω| ≤ |Yn n ω|)
    (hY : IsBigOp Yn rn μ) : IsBigOp Xn rn μ := by
  intro δ hδ
  obtain ⟨M, hM, htail⟩ := hY δ hδ
  refine ⟨M, hM, ?_⟩
  filter_upwards [htail] with n hn
  exact (measure_mono fun ω hω => hω.trans (h n ω)).trans hn

/-- The constant-zero sequence is `O_p(rₙ)` for an eventually positive rate. -/
theorem IsBigOp.zero (hrn : ∀ᶠ n in atTop, 0 < rn n) :
    IsBigOp (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) rn μ := by
  intro δ _hδ
  refine ⟨1, one_pos, ?_⟩
  filter_upwards [hrn] with n hn
  simp [not_le.mpr hn]

/-- A finite sum of `O_p(rₙ)` sequences is `O_p(rₙ)` (same rate; constants absorb). -/
theorem IsBigOp.finset_sum {ι : Type*} (s : Finset ι) {X : ι → ℕ → Ω → ℝ}
    (hrn : ∀ᶠ n in atTop, 0 < rn n)
    (h : ∀ i ∈ s, IsBigOp (X i) rn μ) :
    IsBigOp (fun n ω => ∑ i ∈ s, X i n ω) rn μ := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hcast : (fun (n : ℕ) (ω : Ω) => ∑ i ∈ (∅ : Finset ι), X i n ω)
          = fun _ _ => (0 : ℝ) := by ext n ω; simp
      rw [hcast]
      exact IsBigOp.zero hrn
  | insert i s hi ih =>
      have hisum : IsBigOp (fun n ω => X i n ω + ∑ j ∈ s, X j n ω) rn μ :=
        IsBigOp.add (h i (Finset.mem_insert_self i s))
          (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
      refine IsBigOp.of_abs_le
        (Yn := fun n ω => X i n ω + ∑ j ∈ s, X j n ω) ?_ hisum
      intro n ω
      rw [Finset.sum_insert hi]

/-- **Product rule for stochastic big-O.**  If `Xₙ = O_p(rₙ)` and
`Yₙ = O_p(sₙ)` for nonnegative rates, then `XₙYₙ = O_p(rₙsₙ)`. -/
theorem IsBigOp.mul (hrn : ∀ n, 0 ≤ rn n) (hsn : ∀ n, 0 ≤ sn n)
    (hX : IsBigOp Xn rn μ) (hY : IsBigOp Yn sn μ) :
    IsBigOp (fun n ω => Xn n ω * Yn n ω) (fun n => rn n * sn n) μ := by
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · exact ⟨1, one_pos, by simp [hδtop]⟩
  have hhalf : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨M, hM, hXM⟩ := hX (δ / 2) hhalf
  obtain ⟨N, hN, hYN⟩ := hY (δ / 2) hhalf
  refine ⟨M * N, mul_pos hM hN, ?_⟩
  filter_upwards [hXM, hYN] with n hXn hYn
  calc
    μ {ω | (M * N) * (rn n * sn n) ≤ ‖Xn n ω * Yn n ω‖}
        ≤ μ ({ω | M * rn n ≤ ‖Xn n ω‖} ∪
            {ω | N * sn n ≤ ‖Yn n ω‖}) := by
          refine measure_mono fun ω hω => ?_
          by_contra hnot
          have hnotX : ¬M * rn n ≤ ‖Xn n ω‖ := fun h => hnot (Or.inl h)
          have hnotY : ¬N * sn n ≤ ‖Yn n ω‖ := fun h => hnot (Or.inr h)
          have hprod : ‖Xn n ω * Yn n ω‖ < (M * N) * (rn n * sn n) := calc
            ‖Xn n ω * Yn n ω‖ ≤ ‖Xn n ω‖ * ‖Yn n ω‖ := norm_mul_le _ _
            _ < (M * rn n) * (N * sn n) :=
              mul_lt_mul'' (lt_of_not_ge hnotX) (lt_of_not_ge hnotY)
                (norm_nonneg _) (norm_nonneg _)
            _ = (M * N) * (rn n * sn n) := by ring
          exact (not_lt_of_ge hω) hprod
    _ ≤ μ {ω | M * rn n ≤ ‖Xn n ω‖} +
          μ {ω | N * sn n ≤ ‖Yn n ω‖} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hXn hYn
    _ = δ := ENNReal.add_halves δ

/-! ## The Markov primitive: `L²`-envelope ⇒ `O_p`

A deterministic bound on the conditional/unconditional second moment yields the
matching `O_p` rate.  This is the elementary Chebyshev/Markov step, isolated
once so every cross-fit rate proof reuses it instead of re-deriving it inline.
-/

/-- **Markov second-moment ⇒ `O_p`.**  If each `Xₙ` is `μ`-a.e.-measurable and
its second moment is bounded by a deterministic envelope,
`∫⁻ (Xₙ ω)² dμ ≤ Vₙ` with `0 ≤ Vₙ` and `Vₙ > 0` eventually, then
`Xₙ = O_p(√Vₙ)`.

Proof: Markov on `(Xₙ)²` gives `μ{M√Vₙ < |Xₙ|} ≤ μ{M²Vₙ ≤ (Xₙ)²} ≤
(∫⁻ (Xₙ)²)/(M²Vₙ) ≤ 1/M²`; take `M = 1/√ε`. -/
theorem IsBigOp.of_sq_lintegral_le {Vn : ℕ → ℝ}
    (hX : ∀ n, AEMeasurable (Xn n) μ)
    (hVn : ∀ n, 0 ≤ Vn n)
    (hVn_pos : ∀ᶠ n in atTop, 0 < Vn n)
    (hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal ((Xn n ω) ^ 2) ∂μ
        ≤ ENNReal.ofReal (Vn n)) :
    IsBigOp Xn (fun n => Real.sqrt (Vn n)) μ := by
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · exact ⟨1, one_pos, by simp [hδtop]⟩
  let ε : ℝ := δ.toReal
  have hε : 0 < ε := ENNReal.toReal_pos hδ.ne' hδtop
  set Mε : ℝ := Real.sqrt (1 / ε) with hMε_def
  have hMε_pos : 0 < Mε := by
    rw [hMε_def]
    exact Real.sqrt_pos.mpr (by positivity)
  have hMε_sq_pos : 0 < Mε ^ 2 := pow_pos hMε_pos 2
  have hMε_sq : Mε ^ 2 = 1 / ε := by
    rw [hMε_def, Real.sq_sqrt]
    positivity
  have hMε_inv_sq : 1 / (Mε ^ 2) = ε := by
    rw [hMε_sq]
    field_simp [hε.ne']
  refine ⟨Mε, hMε_pos, ?_⟩
  have hper_n :
      ∀ᶠ n in atTop,
        μ {ω | Mε * Real.sqrt (Vn n) ≤ |Xn n ω|} ≤
          ENNReal.ofReal ε := by
    filter_upwards [hVn_pos] with n hVpos
    set Y : Ω → ℝ := Xn n with hY_def
    have hY_aemeas : AEMeasurable Y μ := by
      simpa [Y] using hX n
    have hY_sq_aemeas : AEMeasurable (fun ω => ENNReal.ofReal ((Y ω) ^ 2)) μ := by
      fun_prop
    have hden_pos : 0 < Mε ^ 2 * Vn n := mul_pos hMε_sq_pos hVpos
    have hden_ne_zero : ENNReal.ofReal (Mε ^ 2 * Vn n) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]
      exact hden_pos
    have hden_ne_top : ENNReal.ofReal (Mε ^ 2 * Vn n) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hsubset :
        {ω | Mε * Real.sqrt (Vn n) ≤ |Y ω|} ⊆
          {ω | ENNReal.ofReal (Mε ^ 2 * Vn n) ≤
            ENNReal.ofReal ((Y ω) ^ 2)} := by
      intro ω hω
      have hleft_nonneg : 0 ≤ Mε * Real.sqrt (Vn n) :=
        mul_nonneg hMε_pos.le (Real.sqrt_nonneg _)
      have hsq' : (Mε * Real.sqrt (Vn n)) ^ 2 ≤ |Y ω| ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg hleft_nonneg] using hω
      have hsq : Mε ^ 2 * Vn n ≤ (Y ω) ^ 2 := by
        simpa [mul_pow, Real.sq_sqrt (hVn n), sq_abs, mul_assoc, mul_comm,
          mul_left_comm] using hsq'
      exact ENNReal.ofReal_le_ofReal hsq
    have hmarkov := MeasureTheory.meas_ge_le_lintegral_div hY_sq_aemeas
      hden_ne_zero hden_ne_top
    have hdiv_le :
        ENNReal.ofReal (Vn n) / ENNReal.ofReal (Mε ^ 2 * Vn n) ≤
          ENNReal.ofReal ε := by
      calc
        ENNReal.ofReal (Vn n) / ENNReal.ofReal (Mε ^ 2 * Vn n)
            = ENNReal.ofReal (Vn n / (Mε ^ 2 * Vn n)) := by
              rw [ENNReal.ofReal_div_of_pos hden_pos]
        _ = ENNReal.ofReal (1 / (Mε ^ 2)) := by
              congr 1
              field_simp [hVpos.ne', hMε_sq_pos.ne']
        _ = ENNReal.ofReal ε := by rw [hMε_inv_sq]
        _ ≤ ENNReal.ofReal ε := le_rfl
    rw [hY_def]
    calc
      μ {ω | Mε * Real.sqrt (Vn n) ≤ |Xn n ω|}
          = μ {ω | Mε * Real.sqrt (Vn n) ≤ |Y ω|} := by simp [Y]
      _ ≤ μ {ω | ENNReal.ofReal (Mε ^ 2 * Vn n) ≤ ENNReal.ofReal ((Y ω) ^ 2)} :=
            measure_mono hsubset
      _ ≤ (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂μ) /
            ENNReal.ofReal (Mε ^ 2 * Vn n) := hmarkov
      _ ≤ ENNReal.ofReal (Vn n) / ENNReal.ofReal (Mε ^ 2 * Vn n) := by
            gcongr
            simpa [Y] using hbound n
      _ ≤ ENNReal.ofReal ε := hdiv_le
  simpa only [Real.norm_eq_abs, ε, ENNReal.ofReal_toReal hδtop] using hper_n

/-! ## Lemma B — the conditional / cross-fit lift

The deliverable.  Given a per-`n` sub-σ-field `m_A n` (the training σ-field),
an evaluation index set `s n` whose observations are conditionally i.i.d. given
`m_A n` (independent of `m_A n` with i.i.d. product law), and a score
`g n : Ω → X → ℝ` that is `(m_A n ⊗ σ_X)`-measurable (the cross-fit case: a
fixed integrand evaluated at the `m_A n`-measurable nuisance) and lies in
`L²(P)` for each `ω`, the centered scaled fold sum

    Xₙ(ω) = (1/√|s n|) Σ_{i ∈ s n} (g n ω (W i ω) − ∫ g n ω dP)

is `O_p(√Vₙ)` for any deterministic `Vₙ` dominating `∫_Ω ‖g n ω‖²_{L²(P)} dμ`.

Here `∫ g n ω dP = 𝔼[g n (·, W) | m_A n](ω)` is the conditional mean (the eval
fold is independent of `m_A n`), so `Xₙ` is exactly `√|s n|·(ℙₙ g − 𝔼[g|m_A n])`.
The second-moment estimate is `Causalean.Mathlib.iid_centered_sum_sq_lintegral_le`;
the rate then follows from `IsBigOp.of_sq_lintegral_le`. -/
/-- **Cross-fit empirical-increment rate.** Given observations [`W i`, each of which is
measurable](hyp:hW_meas), grouped into evaluation folds [`s n`, each nonempty](hyp:hs_pos), and
training σ-algebras [`m_A n`, each contained in the ambient σ-algebra on the sample
space](hyp:hm_A_le) such that [the training σ-algebra `m_A n` is independent of the observations
indexed by the fold `s n`](hyp:hindep) and [those fold observations are, conditionally, i.i.d.
draws from `P`](hyp:hiid): for a score `g n` that [viewed jointly in the sample point and its
argument is measurable with respect to the training σ-algebra `m_A n` (the cross-fitting case of
a fixed integrand evaluated at a nuisance estimated on the other folds)](hyp:hg_meas) and [is
square-integrable under `P` at every sample point](hyp:hg_memLp), and for any [deterministic
sequence `Vn` that is nonnegative everywhere and eventually positive](hyp:hVn,hVn_pos) that
[dominates the average, over the training draw, of the squared `L²(P)`-norm of `g n`](hyp:hVbound),
[the centered and rescaled evaluation-fold average of `g n` is stochastically bounded at the rate
$\sqrt{V_n}$](goal). -/
theorem isBigOp_centered_crossFit_sum
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    {μ : Measure Ω} {P : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (W : ℕ → Ω → X) (hW_meas : ∀ i, Measurable (W i))
    (s : ℕ → Finset ℕ) (hs_pos : ∀ n, 0 < (s n).card)
    (m_A : ℕ → MeasurableSpace Ω) (hm_A_le : ∀ n, m_A n ≤ mΩ)
    (hindep : ∀ n,
      Indep (m_A n)
        (MeasurableSpace.comap
          (fun ω (i : s n) => W i.val ω) (inferInstance : MeasurableSpace _)) μ)
    (hiid : ∀ n,
      (μ.map (fun ω (i : s n) => W i.val ω)) = Measure.pi (fun _ : s n => P))
    (g : ℕ → Ω → X → ℝ)
    (hg_meas : ∀ n, Measurable[(m_A n).prod mX] (Function.uncurry (g n)))
    (hg_memLp : ∀ n ω, MemLp (g n ω) 2 P)
    {Vn : ℕ → ℝ} (hVn : ∀ n, 0 ≤ Vn n)
    (hVn_pos : ∀ᶠ n in atTop, 0 < Vn n)
    (hVbound : ∀ n,
      ∫⁻ ω, ENNReal.ofReal ((eLpNorm (g n ω) 2 P).toReal ^ 2) ∂μ
        ≤ ENNReal.ofReal (Vn n)) :
    IsBigOp
      (fun n ω => (Real.sqrt ((s n).card : ℝ))⁻¹ *
        ∑ i ∈ s n, (g n ω (W i ω) - ∫ x, g n ω x ∂P))
      (fun n => Real.sqrt (Vn n)) μ := by
  refine IsBigOp.of_sq_lintegral_le ?hX hVn hVn_pos ?hbound
  · intro n
    have hcenter_meas : Measurable
        (fun ω => ∑ i ∈ s n, (g n ω (W i ω) - ∫ x, g n ω x ∂P)) := by
      refine Finset.measurable_sum _ ?_
      intro i hi
      have hfirst : @Measurable Ω Ω mΩ (m_A n) id :=
        measurable_id.mono le_rfl (hm_A_le n)
      have hpair : @Measurable Ω (Ω × X) mΩ ((m_A n).prod mX)
          (fun ω => (ω, W i ω)) :=
        hfirst.prodMk (hW_meas i)
      have hgi : Measurable (fun ω => g n ω (W i ω)) := by
        simpa [Function.uncurry, Function.comp_def] using (hg_meas n).comp hpair
      have hint_A : Measurable[m_A n] (fun ω => ∫ x, g n ω x ∂P) := by
        letI : MeasurableSpace Ω := m_A n
        have hsm : StronglyMeasurable (Function.uncurry (g n)) :=
          (show Measurable (Function.uncurry (g n)) from hg_meas n).stronglyMeasurable
        exact hsm.integral_prod_right.measurable
      have hint : Measurable (fun ω => ∫ x, g n ω x ∂P) :=
        hint_A.mono (hm_A_le n) le_rfl
      exact hgi.sub hint
    exact (measurable_const.mul hcenter_meas).aemeasurable
  · intro n
    have hraw := Causalean.Mathlib.iid_centered_sum_sq_lintegral_le
      (s := s n) (hs_pos n) (W := W) (fun i _ => hW_meas i)
      (m_A n) (hm_A_le n) (hindep n) (hiid n)
      (g n) (hg_meas n) (hg_memLp n)
    exact hraw.trans (hVbound n)

/-! ## Lemma A — the unconditional i.i.d. corollary

Special case of the engine with the trivial training σ-field `⊥` and a fixed
integrand `f`.  This is the form the `(ℙₙ − P)φ^bd` term consumes. -/

namespace IIDSample

variable {X : Type*} [MeasurableSpace X] {P : Measure X}

/-- **Centered sample-mean second moment.**  For an i.i.d. sample and a
square-integrable statistic `f`, the centered sample mean over the first `n`
points has second moment bounded by `E_P[f²]/n`:

    ∫⁻ ω, ((ℙₙf)(ω) − ∫ f dP)² dμ ≤ E_P[f²] / n.

Proof: `(1/√n) Σ_{i<n} (f(Zᵢ) − m) = √n (ℙₙf − m)`, so the engine's bound
`∫⁻ (√n (ℙₙf − m))² ≤ E_P[f²]` divides to the claim. -/
theorem sampleMean_sub_sq_lintegral_le
    (S : IIDSample Ω X μ P) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {f : X → ℝ} (hf_meas : Measurable f) (hf : MemLp f 2 P) {n : ℕ} (hn : 0 < n) :
    ∫⁻ ω, ENNReal.ofReal ((S.sampleMean f n ω - ∫ x, f x ∂P) ^ 2) ∂μ
      ≤ ENNReal.ofReal ((∫ x, (f x) ^ 2 ∂P) / n) := by
  classical
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hiid :
      μ.map (fun ω (i : Finset.range n) => S.Z i.val ω) =
        Measure.pi (fun _ : Finset.range n => P) := by
    have hindep_s : iIndepFun (fun i : Finset.range n => S.Z i) μ := by
      exact S.indep.precomp Subtype.val_injective
    have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Finset.range n => (S.meas i).aemeasurable)).mp hindep_s
    calc
      μ.map (fun ω (i : Finset.range n) => S.Z i.val ω)
          = Measure.pi (fun i : Finset.range n => μ.map (S.Z i)) := hmap
      _ = Measure.pi (fun _ : Finset.range n => P) := by
          congr with i
          rw [← (S.identDist i).map_eq, S.law]
  have hindep :
      Indep (⊥ : MeasurableSpace Ω)
        (MeasurableSpace.comap
          (fun ω (i : Finset.range n) => S.Z i.val ω) inferInstance) μ := by
    exact ProbabilityTheory.indep_bot_left _
  have hraw := Causalean.Mathlib.iid_centered_sum_sq_lintegral_le
    (s := Finset.range n) (by simpa [Finset.card_range] using hn) (W := S.Z)
    (fun i _ => S.meas i)
    (⊥ : MeasurableSpace Ω) bot_le hindep hiid
    (fun _ x => f x)
    (by
      change Measurable[(⊥ : MeasurableSpace Ω).prod (inferInstance : MeasurableSpace X)]
        (fun p : Ω × X => f p.2)
      exact hf_meas.comp measurable_snd)
    (fun _ => hf)
  have heLp_sq :
      ENNReal.ofReal ((eLpNorm f 2 P).toReal ^ 2) =
        ENNReal.ofReal (∫ x, (f x) ^ 2 ∂P) := by
    have h_eLp := hf.eLpNorm_eq_integral_rpow_norm
      (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)
    rw [h_eLp]
    simp only [ENNReal.toReal_ofNat]
    have hroot_nonneg : 0 ≤ (∫ a, ‖f a‖ ^ (2 : ℝ) ∂P) ^ (2 : ℝ)⁻¹ := by
      exact Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
    rw [ENNReal.toReal_ofReal hroot_nonneg]
    have hsq : ((∫ a, ‖f a‖ ^ (2 : ℝ) ∂P) ^ (2 : ℝ)⁻¹) ^ 2 =
        ∫ x, f x ^ 2 ∂P := by
      have hint_eq : (∫ a, ‖f a‖ ^ (2 : ℝ) ∂P) = ∫ x, f x ^ 2 ∂P := by
        congr with x
        norm_num [sq_abs]
      rw [hint_eq]
      rw [show ((∫ x, f x ^ 2 ∂P) ^ (2 : ℝ)⁻¹) ^ 2 =
          ((∫ x, f x ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 by norm_num]
      rw [show ((∫ x, f x ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 =
          ((∫ x, f x ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) by
        norm_num [Real.rpow_two]]
      rw [← Real.rpow_mul]
      · norm_num
      · exact integral_nonneg fun x => sq_nonneg _
    rw [hsq]
  have hscaled_bound :
      ∫⁻ ω, ENNReal.ofReal
          (((Real.sqrt (n : ℝ))⁻¹ *
            ∑ i ∈ Finset.range n, (f (S.Z i ω) - ∫ x, f x ∂P)) ^ 2) ∂μ
        ≤ ENNReal.ofReal (∫ x, (f x) ^ 2 ∂P) := by
    have hraw' :
        ∫⁻ ω, ENNReal.ofReal
            (((Real.sqrt ((Finset.range n).card : ℝ))⁻¹ *
              ∑ i ∈ Finset.range n,
                ((fun _ x => f x) ω (S.Z i ω) - ∫ x, (fun _ x => f x) ω x ∂P)) ^ 2) ∂μ
          ≤ ENNReal.ofReal (∫ x, (f x) ^ 2 ∂P) := by
      calc
        ∫⁻ ω, ENNReal.ofReal
            (((Real.sqrt ((Finset.range n).card : ℝ))⁻¹ *
              ∑ i ∈ Finset.range n,
                ((fun _ x => f x) ω (S.Z i ω) - ∫ x, (fun _ x => f x) ω x ∂P)) ^ 2) ∂μ
            ≤ ∫⁻ ω, ENNReal.ofReal ((eLpNorm ((fun _ x => f x) ω) 2 P).toReal ^ 2) ∂μ :=
              hraw
        _ = ENNReal.ofReal (∫ x, (f x) ^ 2 ∂P) := by
              simp [heLp_sq]
    simpa [Finset.card_range] using hraw'
  let Z : Ω → ℝ := fun ω =>
    (Real.sqrt (n : ℝ))⁻¹ *
      ∑ i ∈ Finset.range n, (f (S.Z i ω) - ∫ x, f x ∂P)
  let D : Ω → ℝ := fun ω => S.sampleMean f n ω - ∫ x, f x ∂P
  have hZ_eq : ∀ ω, Z ω = Real.sqrt (n : ℝ) * D ω := by
    intro ω
    have hsum_sub :
        (∑ i ∈ Finset.range n, (f (S.Z i ω) - ∫ x, f x ∂P)) =
          (∑ i ∈ Finset.range n, f (S.Z i ω)) - (n : ℝ) * (∫ x, f x ∂P) := by
      rw [Finset.sum_sub_distrib]
      simp [Finset.card_range, nsmul_eq_mul]
    dsimp [Z, D, IIDSample.sampleMean]
    rw [hsum_sub]
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnR)
    field_simp [hsqrt_ne, hnR.ne']
    rw [Real.sq_sqrt hnR.le]
  have hD_sq : ∀ ω, D ω ^ 2 = (n : ℝ)⁻¹ * Z ω ^ 2 := by
    intro ω
    rw [hZ_eq ω, mul_pow, Real.sq_sqrt hnR.le]
    field_simp [hnR.ne']
  have hn_inv_nonneg : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hnR.le
  calc
    ∫⁻ ω, ENNReal.ofReal ((S.sampleMean f n ω - ∫ x, f x ∂P) ^ 2) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (D ω ^ 2) ∂μ := by rfl
    _ = ∫⁻ ω, ENNReal.ofReal ((n : ℝ)⁻¹ * Z ω ^ 2) ∂μ := by
          simp_rw [hD_sq]
    _ = ∫⁻ ω, ENNReal.ofReal ((n : ℝ)⁻¹) * ENNReal.ofReal (Z ω ^ 2) ∂μ := by
          simp_rw [ENNReal.ofReal_mul hn_inv_nonneg]
    _ = ENNReal.ofReal ((n : ℝ)⁻¹) * ∫⁻ ω, ENNReal.ofReal (Z ω ^ 2) ∂μ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal ((n : ℝ)⁻¹) *
          ENNReal.ofReal (∫ x, (f x) ^ 2 ∂P) := by
          exact mul_le_mul_right (by simpa [Z] using hscaled_bound) _
    _ = ENNReal.ofReal ((∫ x, (f x) ^ 2 ∂P) / n) := by
          rw [← ENNReal.ofReal_mul hn_inv_nonneg]
          congr 1
          field_simp [hnR.ne']

/-- **Chebyshev tail for the centered sample mean.**  For `t > 0`,

    μ{ω | t ≤ |(ℙₙf)(ω) − ∫ f dP|} ≤ E_P[f²] / (n · t²). -/
theorem sampleMean_sub_meas_ge_le
    (S : IIDSample Ω X μ P) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {f : X → ℝ} (hf_meas : Measurable f) (hf : MemLp f 2 P) {n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht : 0 < t) :
    μ {ω | t ≤ |S.sampleMean f n ω - ∫ x, f x ∂P|}
      ≤ ENNReal.ofReal ((∫ x, (f x) ^ 2 ∂P) / (n * t ^ 2)) := by
  classical
  let D : Ω → ℝ := fun ω => S.sampleMean f n ω - ∫ x, f x ∂P
  have hD_meas : Measurable D := by
    dsimp [D, IIDSample.sampleMean]
    exact (measurable_const.mul
      (Finset.measurable_sum _ fun i _ => hf_meas.comp (S.meas i))).sub measurable_const
  have hD_sq_aemeas : AEMeasurable (fun ω => ENNReal.ofReal ((D ω) ^ 2)) μ := by
    fun_prop
  have ht_sq_pos : 0 < t ^ 2 := pow_pos ht 2
  have ht_sq_ne_zero : ENNReal.ofReal (t ^ 2) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact ht_sq_pos
  have ht_sq_ne_top : ENNReal.ofReal (t ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsubset :
      {ω | t ≤ |D ω|} ⊆
        {ω | ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal ((D ω) ^ 2)} := by
    intro ω hω
    apply ENNReal.ofReal_le_ofReal
    have hs : t ^ 2 ≤ (D ω) ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_pos ht] using hω
    exact hs
  have hmarkov := MeasureTheory.meas_ge_le_lintegral_div hD_sq_aemeas
    ht_sq_ne_zero ht_sq_ne_top
  have hsecond := sampleMean_sub_sq_lintegral_le S hf_meas hf hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    μ {ω | t ≤ |S.sampleMean f n ω - ∫ x, f x ∂P|}
        = μ {ω | t ≤ |D ω|} := by rfl
    _ ≤ μ {ω | ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal ((D ω) ^ 2)} :=
          measure_mono hsubset
    _ ≤ (∫⁻ ω, ENNReal.ofReal ((D ω) ^ 2) ∂μ) / ENNReal.ofReal (t ^ 2) :=
          hmarkov
    _ ≤ ENNReal.ofReal ((∫ x, (f x) ^ 2 ∂P) / n) / ENNReal.ofReal (t ^ 2) := by
          gcongr
    _ = ENNReal.ofReal (((∫ x, (f x) ^ 2 ∂P) / n) / (t ^ 2)) := by
          rw [ENNReal.ofReal_div_of_pos ht_sq_pos]
    _ = ENNReal.ofReal ((∫ x, (f x) ^ 2 ∂P) / (n * t ^ 2)) := by
          congr 1
          field_simp [hnR.ne', ht.ne']

/-- **Unconditional `O_p` rate (Lemma A).** For an i.i.d. sample `S` and [a statistic `f` that is
measurable and square-integrable under the sampling distribution `P`, with strictly positive
second moment](hyp:hf_meas,hf,hf_sq_pos), [the
sample mean over the first `n` observations, centered at the population mean $\int f\,dP$, is
stochastically bounded at the rate $\sqrt{E_P[f^2]/n}$: it is
$O_p(n^{-1/2}(E_P[f^2])^{1/2})$](goal):

    (ℙₙf − ∫ f dP) = O_p( √(E_P[f²] / n) ).

Feeding the centered statistic `f − ∫ f dP` (whose `E_P[(·)²] = Var_P f`) gives
the sharp `O_p(√(Var_P f / n))` form. -/
theorem sampleMean_sub_isBigOp
    (S : IIDSample Ω X μ P) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {f : X → ℝ} (hf_meas : Measurable f) (hf : MemLp f 2 P)
    (hf_sq_pos : 0 < ∫ x, (f x) ^ 2 ∂P) :
    IsBigOp (fun n ω => S.sampleMean f n ω - ∫ x, f x ∂P)
      (fun n => Real.sqrt ((∫ x, (f x) ^ 2 ∂P) / n)) μ := by
  classical
  let A : ℝ := ∫ x, (f x) ^ 2 ∂P
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun x => sq_nonneg _
  have hA_pos : 0 < A := by simpa [A] using hf_sq_pos
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · exact ⟨1, one_pos, by simp [hδtop]⟩
  let ε : ℝ := δ.toReal
  have hε : 0 < ε := ENNReal.toReal_pos hδ.ne' hδtop
  set Mε : ℝ := Real.sqrt (1 / ε) with hMε_def
  have hMε_pos : 0 < Mε := by
    rw [hMε_def]
    exact Real.sqrt_pos.mpr (by positivity)
  have hMε_sq_pos : 0 < Mε ^ 2 := pow_pos hMε_pos 2
  have hMε_sq : Mε ^ 2 = 1 / ε := by
    rw [hMε_def, Real.sq_sqrt]
    positivity
  have hMε_inv_sq : 1 / (Mε ^ 2) = ε := by
    rw [hMε_sq]
    field_simp [hε.ne']
  refine ⟨Mε, hMε_pos, ?_⟩
  have hper_n :
      ∀ᶠ n : ℕ in atTop,
        μ {ω | Mε * Real.sqrt (A / n) ≤
            |S.sampleMean f n ω - ∫ x, f x ∂P|} ≤ ENNReal.ofReal ε := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hrate_pos : 0 < Real.sqrt (A / n) :=
      Real.sqrt_pos.mpr (div_pos hA_pos hnR)
    have ht_pos : 0 < Mε * Real.sqrt (A / n) := mul_pos hMε_pos hrate_pos
    have htail := sampleMean_sub_meas_ge_le S hf_meas hf hn ht_pos
    have hreal :
        A / (n * (Mε * Real.sqrt (A / n)) ^ 2) = 1 / (Mε ^ 2) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hA_nonneg hnR.le)]
      field_simp [hA_pos.ne', hnR.ne', hMε_sq_pos.ne']
    calc
      μ {ω | Mε * Real.sqrt (A / n) ≤
          |S.sampleMean f n ω - ∫ x, f x ∂P|}
          ≤ ENNReal.ofReal
            ((∫ x, (f x) ^ 2 ∂P) /
              (n * (Mε * Real.sqrt (A / n)) ^ 2)) := htail
      _ = ENNReal.ofReal (A / (n * (Mε * Real.sqrt (A / n)) ^ 2)) := by rfl
      _ = ENNReal.ofReal (1 / (Mε ^ 2)) := by rw [hreal]
      _ = ENNReal.ofReal ε := by rw [hMε_inv_sq]
  simpa only [Real.norm_eq_abs, A, ε, ENNReal.ofReal_toReal hδtop] using hper_n

end IIDSample

end Causalean.Stat

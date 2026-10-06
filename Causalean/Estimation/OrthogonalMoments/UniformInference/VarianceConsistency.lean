module
public import Causalean.Estimation.OrthogonalMoments.UniformInference.EmpiricalScoreMoments
public import Causalean.Estimation.OrthogonalMoments.UniformInference.ScoreMean

/-! # Uniform feasible score variance

Uniform second-moment approximation and a vanishing empirical mean imply
consistency of the feasible cross-fitted variance and a positive variance floor.
-/

public section

namespace Causalean.Estimation.OrthogonalMoments.UniformInference

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
open scoped ENNReal

variable {ι Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  {K : ℕ} (F : Family ι Ω Z K)

namespace Family

/-- The empirical cross-fitted score variance is uniformly consistent for
the law-specific oracle influence-score variance. -/
theorem scoreVar_uniform_consistent
    {r a b : ℕ → ℝ} {C : ℝ} {δ : ℕ → ℝ≥0∞}
    {B vmin M3 : ℝ}
    (R : RateConditions F r a b C δ) (O : OracleConditions F B vmin M3) :
    F.UniformOP (fun n p ω => F.scoreVar n p ω - F.oracleVar p) := by
  have h₁ := F.score_secondMoment_approx_uniformOP R O
  have h₂ := F.oracle_secondMoment_uniformOP O
  have h₃ := F.scoreMean_uniformOP R O
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hsqrt : 0 < Real.sqrt (ε / 3) := Real.sqrt_pos.2 hε3
  have hsum : Tendsto (fun n =>
      (⨆ (p : ι) (_hp : p ∈ F.lawClass n), F.sampleLaw p
        {ω | ε / 3 ≤ |(n : ℝ)⁻¹ *
          (∑ k : Fin K, ∑ i ∈ (F.split p).fold n k,
            (F.score n p k ω ((F.sample p).Z i ω)) ^ 2) -
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            (F.oracle p ((F.sample p).Z i ω)) ^ 2|}) +
      (⨆ (p : ι) (_hp : p ∈ F.lawClass n), F.sampleLaw p
        {ω | ε / 3 ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          (F.oracle p ((F.sample p).Z i ω)) ^ 2 - F.oracleVar p|}) +
      (⨆ (p : ι) (_hp : p ∈ F.lawClass n), F.sampleLaw p
        {ω | Real.sqrt (ε / 3) ≤ |F.scoreMean n p ω|})) atTop (𝓝 0) :=
    by simpa only [zero_add] using
      ((h₁ (ε / 3) hε3).add (h₂ (ε / 3) hε3)).add (h₃ _ hsqrt)
  rw [ENNReal.tendsto_nhds_zero] at hsum ⊢
  intro ζ hζ
  filter_upwards [hsum ζ hζ] with n hn
  apply le_trans _ hn
  refine iSup_le fun p => iSup_le fun hp => ?_
  let T : Ω → ℝ := fun ω => (n : ℝ)⁻¹ *
    ∑ k : Fin K, ∑ i ∈ (F.split p).fold n k,
      (F.score n p k ω ((F.sample p).Z i ω)) ^ 2
  let U : Ω → ℝ := fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
    (F.oracle p ((F.sample p).Z i ω)) ^ 2
  have hpoint : {ω | ε ≤ |F.scoreVar n p ω - F.oracleVar p|} ⊆
      {ω | ε / 3 ≤ |T ω - U ω|} ∪
      {ω | ε / 3 ≤ |U ω - F.oracleVar p|} ∪
      {ω | Real.sqrt (ε / 3) ≤ |F.scoreMean n p ω|} := by
    intro ω hω
    by_contra hh
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hh
    have hsq : (F.scoreMean n p ω) ^ 2 < ε / 3 := by
      have h : |F.scoreMean n p ω| < Real.sqrt (ε / 3) := lt_of_not_ge hh.2
      have hs := Real.sq_sqrt hε3.le
      rcases abs_lt.mp h with ⟨hl, hr⟩
      simpa only [hs] using (sq_lt_sq' hl hr)
    have htri := abs_add_le (T ω - U ω) (U ω - F.oracleVar p)
    have htri2 : |T ω - F.oracleVar p| ≤
        |T ω - U ω| + |U ω - F.oracleVar p| := by
      calc
        _ = |(T ω - U ω) + (U ω - F.oracleVar p)| := by congr 1; ring
        _ ≤ _ := htri
    have htri' : |(T ω - F.oracleVar p) - (F.scoreMean n p ω) ^ 2| ≤
        |T ω - F.oracleVar p| + |(F.scoreMean n p ω) ^ 2| := by
      calc
        _ = |(T ω - F.oracleVar p) + (-(F.scoreMean n p ω) ^ 2)| := by
          congr 1
        _ ≤ _ := by simpa only [abs_neg] using
          (abs_add_le (T ω - F.oracleVar p) (-(F.scoreMean n p ω) ^ 2))
    have hid : F.scoreVar n p ω - F.oracleVar p =
        (T ω - F.oracleVar p) - (F.scoreMean n p ω) ^ 2 := by
      simp only [scoreVar, T]; ring
    change ε ≤ |F.scoreVar n p ω - F.oracleVar p| at hω
    rw [hid] at hω
    have habs : |(F.scoreMean n p ω) ^ 2| = (F.scoreMean n p ω) ^ 2 :=
      abs_of_nonneg (sq_nonneg _)
    rw [habs] at htri'
    nlinarith [hh.1.1, hh.1.2]
  have hfirst : F.sampleLaw p {ω | ε / 3 ≤ |T ω - U ω|} ≤
      ⨆ (q : ι) (_hq : q ∈ F.lawClass n), F.sampleLaw q
        {ω | ε / 3 ≤ |(n : ℝ)⁻¹ *
          (∑ k : Fin K, ∑ i ∈ (F.split q).fold n k,
            (F.score n q k ω ((F.sample q).Z i ω)) ^ 2) -
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            (F.oracle q ((F.sample q).Z i ω)) ^ 2|} :=
    le_iSup_of_le p (le_iSup_of_le hp le_rfl)
  have hsecond : F.sampleLaw p {ω | ε / 3 ≤ |U ω - F.oracleVar p|} ≤
      ⨆ (q : ι) (_hq : q ∈ F.lawClass n), F.sampleLaw q
        {ω | ε / 3 ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          (F.oracle q ((F.sample q).Z i ω)) ^ 2 - F.oracleVar q|} :=
    le_iSup_of_le p (le_iSup_of_le hp le_rfl)
  have hthird : F.sampleLaw p
      {ω | Real.sqrt (ε / 3) ≤ |F.scoreMean n p ω|} ≤
      ⨆ (q : ι) (_hq : q ∈ F.lawClass n), F.sampleLaw q
        {ω | Real.sqrt (ε / 3) ≤ |F.scoreMean n q ω|} :=
    le_iSup_of_le p (le_iSup_of_le hp le_rfl)
  calc
    _ ≤ F.sampleLaw p ({ω | ε / 3 ≤ |T ω - U ω|} ∪
        {ω | ε / 3 ≤ |U ω - F.oracleVar p|} ∪
        {ω | Real.sqrt (ε / 3) ≤ |F.scoreMean n p ω|}) := measure_mono hpoint
    _ ≤ F.sampleLaw p {ω | ε / 3 ≤ |T ω - U ω|} +
        F.sampleLaw p {ω | ε / 3 ≤ |U ω - F.oracleVar p|} +
        F.sampleLaw p {ω | Real.sqrt (ε / 3) ≤ |F.scoreMean n p ω|} := by
          exact le_trans (measure_union_le _ _) (add_le_add_left (measure_union_le _ _) _)
    _ ≤ _ := add_le_add (add_le_add hfirst hsecond) hthird

/-- For [a cross-fitting family](hyp:F) satisfying [the foldwise rate conditions](hyp:R) and
[the oracle-score conditions with oracle variance floor vmin](hyp:O), [the largest probability
over the law class that the empirical score variance is at most vmin/2 tends to zero](goal).

This follows from uniform consistency of the feasible score variance and the positive oracle
variance floor. -/
theorem scoreVar_small_uniformly_rare
    {r a b : ℕ → ℝ} {C : ℝ} {δ : ℕ → ℝ≥0∞}
    {B vmin M3 : ℝ}
    (R : RateConditions F r a b C δ) (O : OracleConditions F B vmin M3) :
    Tendsto (fun n => ⨆ (p : ι) (_hp : p ∈ F.lawClass n),
      F.sampleLaw p {ω | F.scoreVar n p ω ≤ vmin / 2}) atTop (𝓝 0) := by
  /- On the displayed event, `oracleVar p ≥ vmin` implies
  `vmin / 2 ≤ |scoreVar n p ω - oracleVar p|`. Apply
  `scoreVar_uniform_consistent` at threshold `vmin / 2`. This also handles
  the zero feasible-variance event used in Wald coverage. -/
  have hvmin : 0 < vmin / 2 := by linarith [O.vmin_pos]
  have hcons := F.scoreVar_uniform_consistent R O (vmin / 2) hvmin
  rw [ENNReal.tendsto_nhds_zero] at hcons ⊢
  intro ε hε
  filter_upwards [hcons ε hε] with n hn
  calc
    (⨆ (p : ι) (_hp : p ∈ F.lawClass n),
      F.sampleLaw p {ω | F.scoreVar n p ω ≤ vmin / 2}) ≤
        ⨆ (p : ι) (_hp : p ∈ F.lawClass n),
          F.sampleLaw p {ω | vmin / 2 ≤
            |F.scoreVar n p ω - F.oracleVar p|} := by
      refine iSup_le fun p => iSup_le fun hp => ?_
      apply le_iSup_of_le p
      apply le_iSup_of_le hp
      apply measure_mono
      intro ω hω
      have hvar := O.variance_lower n p hp
      have hdiff : vmin / 2 ≤ F.oracleVar p - F.scoreVar n p ω := by
        dsimp at hω ⊢
        linarith
      exact le_trans hdiff (by
        simpa only [abs_sub_comm] using
          (le_abs_self (F.oracleVar p - F.scoreVar n p ω)))
    _ ≤ ε := hn


end Family
end Causalean.Estimation.OrthogonalMoments.UniformInference

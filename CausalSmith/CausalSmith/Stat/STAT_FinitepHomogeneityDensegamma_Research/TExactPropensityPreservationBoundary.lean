module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PhaseAlgebra
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.THeavyTailComparison
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TOracleFrontierResolved

/-! Finite-moment homogeneity testing: TExactPropensityPreservationBoundary. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Preservationcompactuniformity: the displayed mathematical construction or bound. [This is the stated defined object](goal). -/
def PreservationCompactUniformity : Prop :=
  ∀ K : Set Params, IsCompact K → (∀ v ∈ K, v.Valid) → ∃ c C : ℝ, 0 < c ∧
    ∀ v ∈ K, c ≤ cLower v/COr ∧ 64*Real.sqrt 3*CAtt v ≤ C
/-- The preservation exponent is the oracle exponent minus the matched minimum. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: preservation_gap_identity
lemma preservation_gap_identity (v : Params) (hv : v.Valid) :
    gapExp v = E0 v-Eexp v ∧
    gapExp v = (2*v.γ*qExp v/((2*v.γ+qExp v)*Dp v))*max 0 (1-Fphase v) := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
  have hf : 0 < 2*v.γ*qExp v/((2*v.γ+qExp v)*Dp v) := by positivity
  have hid := phase_channel_difference v hv
  have hsel := phase_channel_selection v hv
  by_cases h : 1 ≤ Fphase v
  · have hdiff : E0 v-E4 v ≤ 0 := by
      have := mul_nonneg hf.le (sub_nonneg.mpr h)
      linarith
    simp only [gapExp, max_eq_left hdiff, hsel.1 h, sub_self,
      max_eq_left (sub_nonpos.mpr h), mul_zero, and_self]
  · have hlt : Fphase v < 1 := lt_of_not_ge h
    have hdiff : 0 < E0 v-E4 v := by
      have := mul_neg_of_pos_of_neg hf (sub_neg.mpr hlt)
      linarith
    simp only [gapExp, max_eq_right hdiff.le, hsel.2 hlt,
      max_eq_right (sub_nonneg.mpr hlt.le)]
    constructor
    · exact True.intro
    · linarith

/-- Dividing the two matched frontiers gives the all-sample preservation comparison. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: preservation_ratio_bounds
lemma preservation_ratio_bounds (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    (cLower v/COr)*(n:ℝ)^gapExp v ≤ criticalRadius n v/oracleCriticalRadius n v ∧
    criticalRadius n v/oracleCriticalRadius n v ≤ (CAtt v/cOracle v)*(n:ℝ)^gapExp v := by
  have hf := heavy_tail_comparison.1 v hv
  obtain ⟨hc, hC, hfrest⟩ := hf
  have hfn := hfrest.1 n hn
  have ho := oracle_frontier_resolved.1 v hv
  have hOr := ho.2.1
  have hco : 0 < cOracle v := lt_of_lt_of_le (by positivity) ho.1
  have hon := ho.2.2.1 n hn
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hrho : 0 < rho n v := Real.rpow_pos_of_pos hnpos _
  have hro : 0 < rhoOracle n v := Real.rpow_pos_of_pos hnpos _
  have horad : 0 < oracleCriticalRadius n v := (mul_pos hco hro).trans_le hon.1
  have hrad : 0 < criticalRadius n v := (mul_pos hc hrho).trans_le hfn.2.2.1
  have hscale : rho n v/rhoOracle n v = (n:ℝ)^gapExp v := by
    rw [(preservation_gap_identity v hv).1]
    simp only [rho, rhoOracle, ← Real.rpow_sub hnpos]
    congr 1
    ring
  have hlo := div_le_div₀ hrad.le hfn.2.2.1
    horad hon.2.1
  have hhi := div_le_div₀ (mul_nonneg hC.le hrho.le) hfn.2.2.2.1
    (mul_pos hco hro) hon.1
  have hscale' (c d : ℝ) : (c*rho n v)/(d*rhoOracle n v) = (c/d)*(n:ℝ)^gapExp v := by
    rw [mul_div_mul_comm, hscale]
  rw [hscale'] at hlo hhi
  exact ⟨hlo,hhi⟩

/-- A strictly positive preservation gap makes the radius ratio diverge. This statement assumes [the hv condition](hyp:hv), [the h condition](hyp:h). [This is the stated conclusion](goal). -/
-- @node: preservation_ratio_tendsto
lemma preservation_ratio_tendsto (v : Params) (hv : v.Valid) (h : Fphase v < 1) :
    Filter.Tendsto (fun n : ℕ => criticalRadius n v/oracleCriticalRadius n v)
      Filter.atTop Filter.atTop := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
  have hf : 0 < 2*v.γ*qExp v/((2*v.γ+qExp v)*Dp v) := by positivity
  have hgpos : 0 < gapExp v := by
    rw [(preservation_gap_identity v hv).2, max_eq_right (sub_nonneg.mpr h.le)]
    exact mul_pos hf (sub_pos.mpr h)
  have hc := (heavy_tail_comparison.1 v hv).1
  have hOr := (oracle_frontier_resolved.1 v hv).2.1
  have hpow : Filter.Tendsto (fun n : ℕ => (n:ℝ)^gapExp v) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hgpos).comp tendsto_natCast_atTop_atTop
  apply Filter.tendsto_atTop_mono' Filter.atTop _ (hpow.const_mul_atTop (div_pos hc hOr))
  filter_upwards [Filter.eventually_ge_atTop (2:ℕ)] with n hn
  exact (preservation_ratio_bounds v hv n hn).1

/-- [Exact propensity preservation boundary](goal).
For \(v=(p,\alpha,\beta,\gamma)\in\mathcal V\), define \[  q=\frac{p-1}{p},\qquad
S=\alpha+\beta,\qquad  D_p=1+2\alpha+\frac\beta q+\frac S{2\gamma}, \] \[  E_0(p)=\frac{2\gamma
q}{2\gamma+q},\qquad  E_4(p)=\frac{2S}{D_p},\qquad  F(p)=\frac{2\alpha}{p-1}+\frac\beta q+\frac
S{2\gamma}, \] \[  G(v)=\max\{0,E_0(p)-E_4(p)\}      =\frac{2\gamma
q}{(2\gamma+q)D_p}\max\{0,1-F(p)\}. \] Keep the unchanged multipliers \(c_v,C_v\) of Definition
\(\mathrm{def:sharp\mbox{-}frontier\mbox{-}scales}\), and put \[  c^{\mathrm
e}_v=\frac{4^{-\gamma}}{16\sqrt3},\qquad  C^{\mathrm e}_v=3\{120+128\sqrt{160\sqrt2}\}. \] For
the unknown- and supplied-propensity experiments on the same entire class \(\mathcal M_v\), for
every \(n\ge2\), \[  \frac{c_v}{C^{\mathrm e}_v}n^{G(v)}  \le \frac{r_n^*(v)}{r_n^{*,\mathrm
e}(v)}  \le \frac{C_v}{c^{\mathrm e}_v}n^{G(v)}. \] Consequently the exact preservation region
is \[  \mathcal R=  \left\{v\in\mathcal V:  \frac{2\alpha}{p-1}+\frac\beta q+
\frac{\alpha+\beta}{2\gamma}\ge1\right\}. \] At every equality point \(F(p)=1\), the ratio is
bounded above and below by positive constants independent of \(n\), with no necessary
logarithmic factor. If \(F(p)<1\), then \[  \frac{r_n^*(v)}{r_n^{*,\mathrm e}(v)}  \asymp_v
n^{E_0(p)-E_4(p)}\longrightarrow\infty. \] The displayed comparison constants are locally
uniform on every compact subset of \(\mathcal V\), including compact sets crossing \(F(p)=1\)
and touching \(p=2\) or \(\gamma=1/4\). These are comparisons of capped critical radii for every
sample size; they do not assert power at an empty alternative in a saturated small-sample
regime. The boundary is a corollary of the two established matched frontiers, rather than a new
identifying functional or an estimator-rate condition.
-/
-- @node: thm:exact-propensity-preservation-boundary
theorem exact_propensity_preservation_boundary :
    (∀ v : Params, v.Valid →
      gapExp v=(2*v.γ*qExp v/((2*v.γ+qExp v)*Dp v))*max 0 (1-Fphase v) ∧
      (∀ n : ℕ, 2 ≤ n →
        (cLower v/COr)*(n:ℝ)^gapExp v ≤ criticalRadius n v/oracleCriticalRadius n v ∧
        criticalRadius n v/oracleCriticalRadius n v ≤ (CAtt v/cOracle v)*(n:ℝ)^gapExp v) ∧
      (Fphase v=1 → 0 < cLower v/COr ∧ 0 < CAtt v/cOracle v ∧
        ∀ n : ℕ, 2 ≤ n → cLower v/COr ≤ criticalRadius n v/oracleCriticalRadius n v ∧ criticalRadius n v/oracleCriticalRadius n v ≤ CAtt v/cOracle v) ∧
      (Fphase v < 1 → Filter.Tendsto (fun n : ℕ => criticalRadius n v/oracleCriticalRadius n v) Filter.atTop Filter.atTop ∧
        ∀ n : ℕ, 2 ≤ n → (cLower v/COr)*(n:ℝ)^(E0 v-E4 v) ≤ criticalRadius n v/oracleCriticalRadius n v ∧
          criticalRadius n v/oracleCriticalRadius n v ≤ (CAtt v/cOracle v)*(n:ℝ)^(E0 v-E4 v))) ∧
    preservationRegion={v | v.Valid ∧ 1 ≤ Fphase v} ∧ PreservationCompactUniformity := by
  have hconstants (v : Params) (hv : v.Valid) : 0 < cLower v/COr ∧ 0 < CAtt v/cOracle v := by
    have hf := heavy_tail_comparison.1 v hv
    have ho := oracle_frontier_resolved.1 v hv
    have hc : 0 < cOracle v := lt_of_lt_of_le (by positivity) ho.1
    exact ⟨div_pos hf.1 ho.2.1, div_pos hf.2.1 hc⟩
  have hzero (v : Params) (hv : v.Valid) (h : 1 ≤ Fphase v) : gapExp v=0 := by
    rw [(preservation_gap_identity v hv).2, max_eq_left (sub_nonpos.mpr h), mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    refine ⟨(preservation_gap_identity v hv).2, preservation_ratio_bounds v hv, ?_, ?_⟩
    · intro heq
      refine ⟨(hconstants v hv).1, (hconstants v hv).2, ?_⟩
      intro n hn
      simpa only [hzero v hv heq.ge, Real.rpow_zero, mul_one] using preservation_ratio_bounds v hv n hn
    · intro hlt
      refine ⟨preservation_ratio_tendsto v hv hlt, ?_⟩
      have hgap : gapExp v=E0 v-E4 v := by
        rw [(preservation_gap_identity v hv).1, (phase_channel_selection v hv).2 hlt]
      intro n hn
      simpa only [hgap] using preservation_ratio_bounds v hv n hn
  · ext v
    change (v.Valid ∧ BddAbove ((fun n : ℕ => criticalRadius n v/oracleCriticalRadius n v) '' {n | 2 ≤ n})) ↔
      v.Valid ∧ 1 ≤ Fphase v
    constructor
    · rintro ⟨hv, B, hB⟩
      refine ⟨hv, ?_⟩
      by_contra h
      have ht := preservation_ratio_tendsto v hv (lt_of_not_ge h)
      have hevent := ht.eventually (Filter.eventually_gt_atTop B)
      obtain ⟨n, hn, hbig⟩ := (Filter.eventually_ge_atTop (2:ℕ)).and hevent |>.exists
      have hbound := hB ⟨n,hn,rfl⟩
      exact (not_lt_of_ge hbound) hbig
    · rintro ⟨hv,h⟩
      refine ⟨hv, CAtt v/cOracle v, ?_⟩
      rintro r ⟨n,hn,rfl⟩
      simpa only [hzero v hv h, Real.rpow_zero, mul_one] using (preservation_ratio_bounds v hv n hn).2
  · intro K hK hvalid
    obtain ⟨c,C,N,hc,hbounds⟩ := heavy_tail_comparison.2.2.2.2.1 K hK hvalid
    have hOr : 0 < COr := by unfold COr; positivity
    refine ⟨c/COr,64*Real.sqrt 3*C,div_pos hc hOr,?_⟩
    intro v hv
    exact ⟨div_le_div_of_nonneg_right (hbounds v hv).1 hOr.le,
      mul_le_mul_of_nonneg_left (hbounds v hv).2.1 (by positivity)⟩

end CausalSmith.Stat.FinitepHomogeneityDensegamma

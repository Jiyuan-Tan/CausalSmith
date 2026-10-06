module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.BinaryComparison
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.LedgerRate
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TwoPrior
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TCausalNonempty
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TWholeNullCalibrationResolved

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Order.Compact

/-! Finite-moment homogeneity testing: TOriginalRecordAttainableRate. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Attainmentcompactuniformity: the displayed mathematical construction or bound. [This is the stated defined object](goal). -/
def AttainmentCompactUniformity : Prop :=
  ∀ K : Set Params, IsCompact K → (∀ v ∈ K, v.Valid) → ∃ C N e : ℝ,
    0 < e ∧ ∀ v ∈ K, CAtt v ≤ C ∧ (NAtt v:ℝ) ≤ N ∧ e ≤ Eexp v
/-- The explicit attainment multiplier is at least its approximation-only contribution. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: CAtt_ge_256
lemma CAtt_ge_256 (v : Params) (hv : v.Valid) : 256 ≤ CAtt v := by
  have hgeo (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Ageo x := by
    unfold Ageo
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (neg_nonpos.mpr hx)
    simp only [Real.rpow_zero] at hh
    positivity
  have hα := hgeo v.α hv.2.1.1.le
  have hl := hgeo (lam0 v) (by
    unfold lam0
    have hp : 0 < v.p := by linarith [hv.1.1]
    positivity)
  have hB : 0 ≤ Bstar v := by unfold Bstar; positivity
  unfold CAtt
  nlinarith [Real.sqrt_nonneg (Astar v)]

/-- Every valid matched exponent is at most one. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: Eexp_le_one
lemma Eexp_le_one (v : Params) (hv : v.Valid) : Eexp v ≤ 1 := by
  have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
  have h := (div_le_iff₀ hg).mp (exponent_phase_algebra v hv).2.2.2.2.2.2.1
  linarith [hv.2.2.2.2]

/-- At sample sizes two and three the displayed level exceeds the model cap. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn), [the hsmall condition](hyp:hsmall). [This is the stated conclusion](goal). -/
-- @node: attainment_small_sample_saturated
lemma attainment_small_sample_saturated (v : Params) (hv : v.Valid) (n : ℕ)
    (hn : 2 ≤ n) (hsmall : n < 4) : maxDist v ≤ CAtt v*rho n v := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn3 : (n:ℝ) ≤ 3 := by exact_mod_cast (by omega : n ≤ 3)
  have hr : (n:ℝ)⁻¹ ≤ rho n v := by
    simpa [rho, Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hn1
      (show (-1:ℝ) ≤ -Eexp v by linarith [Eexp_le_one v hv])
  have hh : (1/3:ℝ) ≤ (n:ℝ)⁻¹ := by
    simpa using one_div_le_one_div_of_le hnpos hn3
  have hc := CAtt_ge_256 v hv
  have hp : 0 ≤ CAtt v := by linarith
  have hlevel : 256*(1/3:ℝ) ≤ CAtt v*rho n v :=
    mul_le_mul hc (hh.trans hr) (by norm_num) hp
  have hD := (model_distance_upper v separatedWitness (separatedWitness_inModel v hv)).2
  linarith

/-- Calibration and the proved deterministic ledger rates give the finite-sample attainable bounds. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: original_record_attainment_finite
lemma original_record_attainment_finite (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    (∀ law, InNull v law → rejectProb n law.P (ledgerTest n v) ≤ 0.0075) ∧
    (CAtt v*rho n v < maxDist v → ∀ law, InModel v law →
      CAtt v*rho n v ≤ hetDist law → 1-rejectProb n law.P (ledgerTest n v) ≤ 0.0075) ∧
    criticalRadius n v ≤ CAtt v*rho n v := by
  have hcal := whole_null_calibration_resolved v hv n hn
  have hpower : CAtt v*rho n v < maxDist v → ∀ law, InModel v law →
      CAtt v*rho n v ≤ hetDist law → 1-rejectProb n law.P (ledgerTest n v) ≤ 0.0075 := by
    intro hsep law hm hd
    have hn4 : 4 ≤ n := by
      by_contra hh
      have hs := attainment_small_sample_saturated v hv n hn (by omega)
      linarith
    have hrate := (ledger_rate_bounds n v hn4 hv).2.2.1
    exact hcal.2.2.2.1 hn4 (hrate.trans_lt hsep) law hm (hrate.trans hd)
  refine ⟨hcal.2.2.1, hpower, ?_⟩
  unfold criticalRadius testingRisk
  apply cappedRadius_le_of_test n _ _ _ _
    ((by unfold d0; positivity : (0:ℝ) ≤ d0).trans (model_distance_lower v hv))
    (mul_pos (by linarith [CAtt_ge_256 v hv]) (by unfold rho; positivity)) (ledgerTest n v)
  · intro law hm
    exact (hcal.2.2.1 law hm).trans (by norm_num)
  · intro hsep law hm hd
    exact (hpower hsep law hm hd).trans (by norm_num)

/-- The public ceiling threshold makes the attained separation strictly below the witness distance. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: attainment_threshold
lemma attainment_threshold (v : Params) (hv : v.Valid) (n : ℕ) (hn : NAtt v ≤ n) :
    CAtt v*rho n v < d0 := by
  have he : 0 < Eexp v := (exponent_phase_algebra v hv).2.2.1
  have hc : 0 < CAtt v := by linarith [CAtt_ge_256 v hv]
  have hd : 0 < d0 := by unfold d0; positivity
  have ht : 0 < 2*CAtt v/d0 := by positivity
  have hceil : max 4 ((2*CAtt v/d0)^(1/Eexp v)) ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hnpos : 0 < (n:ℝ) := by linarith [le_max_left (4:ℝ) ((2*CAtt v/d0)^(1/Eexp v))]
  have htarget := (le_max_right (4:ℝ) ((2*CAtt v/d0)^(1/Eexp v))).trans hceil
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (2*CAtt v/d0)^(1/Eexp v))
    htarget (neg_nonpos.mpr he.le)
  rw [← Real.rpow_mul ht.le] at hp
  have hid : (1/Eexp v)*(-Eexp v) = -1 := by field_simp
  rw [hid, Real.rpow_neg_one] at hp
  have hb : CAtt v*rho n v ≤ d0/2 := by
    calc
      _ ≤ CAtt v*(2*CAtt v/d0)⁻¹ := mul_le_mul_of_nonneg_left hp hc.le
      _ = d0/2 := by field_simp
  linarith

/-- Inserting moment exponent two gives exactly the two bounded-model exponents. This statement assumes [the hw condition](hyp:hw). [This is the stated conclusion](goal). -/
-- @node: bounded_attainment_exponent
lemma bounded_attainment_exponent (w : Smooth3) (hw : w.Valid) :
    Eexp (Params.ofBounded w) = min (2*w.γ/(4*w.γ+1))
      (2*(w.α+w.β)/(1+2*(w.α+w.β)+(w.α+w.β)/(2*w.γ))) := by
  have hg : 0 < w.γ := by linarith [hw.2.2.1]
  unfold Eexp E0 E4 Dp qExp sumReg Params.ofBounded
  congr 1
  · norm_num
    field_simp
    ring
  · norm_num
    congr 1; ring

/-- The moment-two ledger rule attains the bounded-model upper rate. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: bounded_record_attainment_finite
lemma bounded_record_attainment_finite (w : Smooth3) (hw : w.Valid) (n : ℕ) (hn : 2 ≤ n) :
    (∀ law, InBoundedNull w law → rejectProb n law.P (phistarBounded n w) ≤ 0.0075) ∧
    (CAttBounded w*rhoBounded n w < maxDistBounded w → ∀ law, InBoundedModel w law →
      CAttBounded w*rhoBounded n w ≤ hetDist law →
        1-rejectProb n law.P (phistarBounded n w) ≤ 0.0075) ∧
    boundedCriticalRadius n w ≤ CAttBounded w*rhoBounded n w := by
  have hv : (Params.ofBounded w).Valid := ⟨by norm_num [Params.ofBounded], hw⟩
  have hcal := original_record_attainment_finite (Params.ofBounded w) hv n hn
  have hnull {law : ObservedLaw} (hm : InBoundedNull w law) : InNull (Params.ofBounded w) law :=
    ⟨hm.uniform, hm.overlap, hm.propensitySmooth, hm.baselineSmooth,
      hm.effectSmooth, hm.baselineCap, hm.effectCap, hm.rawMoment, hm.nullConstancy⟩
  have hsize : ∀ law, InBoundedNull w law → rejectProb n law.P (phistarBounded n w) ≤ 0.0075 :=
    fun law hm => hcal.1 law (hnull hm)
  have hpower : CAttBounded w*rhoBounded n w < maxDistBounded w →
      ∀ law, InBoundedModel w law → CAttBounded w*rhoBounded n w ≤ hetDist law →
        1-rejectProb n law.P (phistarBounded n w) ≤ 0.0075 := by
    intro hsep law hm hd
    have hD : maxDistBounded w = maxDist (Params.ofBounded w) := by
      simpa [Params.toSmooth3, Params.ofBounded] using maxDistBounded_eq_maxDist (Params.ofBounded w)
    rw [hD] at hsep
    exact hcal.2.1 hsep law hm.toInModel hd
  have hD : maxDistBounded w = maxDist (Params.ofBounded w) := by
    simpa [Params.toSmooth3, Params.ofBounded] using maxDistBounded_eq_maxDist (Params.ofBounded w)
  refine ⟨hsize, hpower, ?_⟩
  unfold boundedCriticalRadius boundedTestingRisk
  apply cappedRadius_le_of_test n _ _ _ _
    (by rw [hD]; exact (by unfold d0; positivity : (0:ℝ) ≤ d0).trans (model_distance_lower _ hv))
    (mul_pos (by simpa [CAttBounded] using (show 0 < CAtt (Params.ofBounded w) by
      linarith [CAtt_ge_256 (Params.ofBounded w) hv]))
      (by unfold rhoBounded rho; positivity)) (phistarBounded n w)
  · intro law hm
    exact (hsize law hm).trans (by norm_num)
  · intro hsep law hm hd
    exact (hpower hsep law hm hd).trans (by norm_num)

/-- Continuity of the indicated public coordinate or explicit rate function. [This is the stated conclusion](goal). -/
-- @node: continuous_params_coordinates
lemma continuous_params_coordinates : Continuous (fun v : Params => (v.p,v.α,v.β,v.γ)) :=
  continuous_induced_dom
/-- Continuity of the indicated public coordinate or explicit rate function. [This is the stated conclusion](goal). -/
-- @node: continuous_params_p
@[fun_prop] lemma continuous_params_p : Continuous (fun v : Params => v.p) :=
  continuous_params_coordinates.fst
/-- Continuity of the indicated public coordinate or explicit rate function. [This is the stated conclusion](goal). -/
-- @node: continuous_params_alpha
@[fun_prop] lemma continuous_params_alpha : Continuous (fun v : Params => v.α) :=
  continuous_params_coordinates.snd.fst
/-- Continuity of the indicated public coordinate or explicit rate function. [This is the stated conclusion](goal). -/
-- @node: continuous_params_beta
@[fun_prop] lemma continuous_params_beta : Continuous (fun v : Params => v.β) :=
  continuous_params_coordinates.snd.snd.fst
/-- Continuity of the indicated public coordinate or explicit rate function. [This is the stated conclusion](goal). -/
-- @node: continuous_params_gamma
@[fun_prop] lemma continuous_params_gamma : Continuous (fun v : Params => v.γ) :=
  continuous_params_coordinates.snd.snd.snd
/-- Continuity of the indicated public coordinate or explicit rate function. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: continuousAt_Eexp
lemma continuousAt_Eexp (v : Params) (hv : v.Valid) : ContinuousAt Eexp v := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
  simp only [qExp, Dp, sumReg] at hq he hd
  unfold Eexp E0 E4 Dp qExp sumReg
  fun_prop (disch := positivity)
/-- Continuity of the indicated public coordinate or explicit rate function. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: continuousAt_CAtt
lemma continuousAt_CAtt (v : Params) (hv : v.Valid) : ContinuousAt CAtt v := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
  have hα := hv.2.1.1
  have hβ := hv.2.2.1.1
  have hlam : 0 < lam0 v := by unfold lam0; positivity
  have hη : 0 < eta0 v := by unfold eta0; positivity
  have hs0 : 0 < s0 v := lt_min hα (lt_min hβ hg)
  have hgeo (x : ℝ) (hx : 0 < x) : 1-(2:ℝ)^(-x) ≠ 0 := by
    have hh : (2:ℝ)^(-x) < 1 := by
      simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
        (show -x < 0 by linarith)
    linarith
  have ha := hgeo v.α hα
  have hl := hgeo (lam0 v) hlam
  have hsmall := hgeo (s0 v) hs0
  have heta := hgeo (eta0 v/2) (by positivity)
  have hhalf := hgeo (1/2) (by norm_num)
  simp only [lam0] at hl
  simp only [s0] at hsmall
  simp only [eta0] at heta
  unfold CAtt Bstar Astar Lstar Gstar Dstar Ageo s0 tExp eta0 lam0 sumReg
  fun_prop (disch := first | positivity | assumption)
/-- Continuity of the indicated public coordinate or explicit rate function. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: continuousAt_attainment_threshold_target
lemma continuousAt_attainment_threshold_target (v : Params) (hv : v.Valid) :
    ContinuousAt (fun v => max 4 ((2*CAtt v/d0)^(1/Eexp v))) v := by
  have hC := continuousAt_CAtt v hv
  have hE := continuousAt_Eexp v hv
  have he : 0 < Eexp v := (exponent_phase_algebra v hv).2.2.1
  have hc : 0 < CAtt v := by linarith [CAtt_ge_256 v hv]
  have hd : 0 < d0 := by unfold d0; positivity
  apply continuousAt_const.max
  apply ContinuousAt.rpow
  · fun_prop
  · fun_prop (disch := positivity)
  · left
    positivity
/-- The continuous explicit constants and positive exponent are uniformly bounded on compact exponent sets. [This is the stated conclusion](goal). -/
-- @node: attainment_compact_uniformity
lemma attainment_compact_uniformity : AttainmentCompactUniformity := by
  intro K hK hv
  by_cases hne : K.Nonempty
  · obtain ⟨vC, hvC, hC⟩ := hK.exists_isMaxOn hne
      (fun v hv' => (continuousAt_CAtt v (hv v hv')).continuousWithinAt)
    obtain ⟨vE, hvE, hE⟩ := hK.exists_isMinOn hne
      (fun v hv' => (continuousAt_Eexp v (hv v hv')).continuousWithinAt)
    obtain ⟨vN, hvN, hN⟩ := hK.exists_isMaxOn hne
      (fun v hv' => (continuousAt_attainment_threshold_target v (hv v hv')).continuousWithinAt)
    refine ⟨CAtt vC, max 4 ((2*CAtt vN/d0)^(1/Eexp vN))+1, Eexp vE,
      (exponent_phase_algebra vE (hv vE hvE)).2.2.1, ?_⟩
    intro v hv'
    refine ⟨hC hv', ?_, hE hv'⟩
    unfold NAtt
    exact (Nat.ceil_lt_add_one (by positivity :
      0 ≤ max (4:ℝ) ((2*CAtt v/d0)^(1/Eexp v)))).le.trans
      (by have hh := hN hv'; dsimp at hh; linarith)
  · refine ⟨0, 0, 1, by norm_num, ?_⟩
    intro v hv'
    exact (hne ⟨v, hv'⟩).elim

/-- [Original record attainable rate](goal).
For every public tuple define \[  q=(p-1)/p,\quad S=\alpha+\beta,\quad t=(2-p)/(p-1),\quad
E_0=2\gamma q/(2\gamma+q),\quad  E_4=\frac{2S}{1+2\alpha+\beta/q+S/(2\gamma)},\quad
E=\min\{E_0,E_4\}. \] The explicit original-record rule in Definition
\(\mathrm{def:explicit\mbox{-}score\mbox{-}ledger}\) attains separation at most
\(C^{\mathrm{att}}_v n^{-E}\), with exactly finite-sample size and type-II error at most
\(0.0075\), the latter whenever \(C^{\mathrm{att}}_v n^{-E}<D_v\). A fully evaluable choice is
the following. Put \(s_0=\min\{\alpha,\beta,\gamma\}\), \(\lambda_0=(p-1)^2/(4p)\),
\(\eta_0=(p-1)(p+6)/(4p)\), and \(A(x)=(1-2^{-x})^{-1}\) for \(x>0\). Define \[  \begin{split}
B_*&=420+800\{A(\alpha)+A(\lambda_0)\},\\  D_*&=1+\{\exp(1)S\log2\}^{-1},\\
L_*&=16+880A(s_0)+160D_*+960A(\alpha),\\  G_*&=\sqrt{64}\{2^{t/2}A(1/2)+A(\eta_0/2)\},\\
A_*&=\sqrt2\{24576+64L_*^2+16384+256G_*^2\},\\
C^{\mathrm{att}}_v&=16\{16+5B_*+1024\sqrt{A_*}\},\\
N^{\mathrm{att}}_v&=\left\lceil\max\{4,(2C^{\mathrm{att}}_v/d_0)^{1/E}\}\right\rceil.
\end{split} \] Then \(r_n^*(v)\le C^{\mathrm{att}}_vn^{-E}\) for every \(n\ge2\), and the
displayed power level is below \(d_0\) for every \(n\ge N^{\mathrm{att}}_v\). These public
constants are locally bounded on compact subsets of the entire exponent domain, including
equality regimes. No logarithm in \(n\) is present in this attainable rate. For
\(n<N^{\mathrm{att}}_v\) the same rule remains size valid, with its zero branch at \(n=2,3\); a
level at or above \(D_v\) gives only the capped upper comparison, not empty-alternative power.
Applying the same rule with \(p=2\) to the bounded model gives the corresponding attainable
bounded exponent \[  E_{\mathrm b}=\min\left\{\frac{2\gamma}{4\gamma+1},
\frac{2S}{1+2S+S/(2\gamma)}\right\}. \]
-/
-- @node: thm:original-record-attainable-rate
theorem original_record_attainable_rate :
    (∀ v : Params, v.Valid → 0 < CAtt v ∧
      (∀ n : ℕ, 2 ≤ n →
        (∀ law, InNull v law → rejectProb n law.P (ledgerTest n v) ≤ 0.0075) ∧
        (CAtt v*rho n v < maxDist v → ∀ law, InModel v law → CAtt v*rho n v ≤ hetDist law → 1-rejectProb n law.P (ledgerTest n v) ≤ 0.0075) ∧
        criticalRadius n v ≤ CAtt v*rho n v) ∧
      (∀ n : ℕ, NAtt v ≤ n → CAtt v*rho n v < d0) ∧
      (∀ n : ℕ, 4 ≤ n → ledgerM n v ≤ 2*blockSize n ∧ ledgerK n v ≤ 2*blockSize n^2 ∧
        1 ≤ ledgerT0 n v ∧ ledgerT0 n v ≤ 2*blockSize n ∧
        ∀ j : Fin (ledgerL n v), 1 ≤ ledgerT n v (j.val+1) ∧ ledgerT n v (j.val+1) ≤ ledgerT0 n v)) ∧
    AttainmentCompactUniformity ∧
    (∀ w : Smooth3, w.Valid → Eexp (Params.ofBounded w)=min (2*w.γ/(4*w.γ+1)) (2*(w.α+w.β)/(1+2*(w.α+w.β)+(w.α+w.β)/(2*w.γ))) ∧
      ∀ n : ℕ, 2 ≤ n →
        (∀ law, InBoundedNull w law → rejectProb n law.P (phistarBounded n w) ≤ 0.0075) ∧
        (CAttBounded w*rhoBounded n w < maxDistBounded w → ∀ law, InBoundedModel w law → CAttBounded w*rhoBounded n w ≤ hetDist law → 1-rejectProb n law.P (phistarBounded n w) ≤ 0.0075) ∧
        boundedCriticalRadius n w ≤ CAttBounded w*rhoBounded n w) := by
  refine ⟨?_, attainment_compact_uniformity, ?_⟩
  · intro v hv
    refine ⟨by linarith [CAtt_ge_256 v hv],
      fun n hn => original_record_attainment_finite v hv n hn,
      fun n hn => attainment_threshold v hv n hn, ?_⟩
    intro n hn
    exact (ledger_rate_bounds n v hn hv).2.2.2
  · intro w hw
    exact ⟨bounded_attainment_exponent w hw,
      fun n hn => bounded_record_attainment_finite w hw n hn⟩

end CausalSmith.Stat.FinitepHomogeneityDensegamma

module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.CellMoments
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.IntervalEvents
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.PartnerVariance
/-! Uniform private scalar-risk, coverage and length guarantees for the total single-release
construction and its public tuning, over the full unknown measurable-density model. -/
public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign
/-- The positive public budget normalizes the everywhere-defined noisy pair release.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon,h,he). -/
-- @node: privateRatioRelease_markov
lemma privateRatioRelease_markov (n k : ℕ) (epsilon h : ℝ) (he : 0 < epsilon) :
    IsMarkovKernel (privateRatioRelease n epsilon h k) := by
  constructor
  intro D
  exact Causalean.Stat.Privacy.laplaceMechPi_isProbabilityMeasure
    (12 / epsilon) (by positivity) (pairQuery n h k) D

/-- The all-count sensitivity bound gives pure privacy for the single joint release.  [the theorem's stated inputs and assumptions](hyp:he,hh,hk), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon). -/
-- @node: privateRatioRelease_private
lemma privateRatioRelease_private (n k : ℕ) (epsilon h : ℝ)
    (he : 0 < epsilon) (hh : 0 < h) (hk : 0 < k) :
    PrivateKernel n epsilon (privateRatioRelease n epsilon h k) := by
  refine ⟨privateRatioRelease_markov n k epsilon h he, ?_⟩
  apply Causalean.Stat.Privacy.laplaceMechPi_pure_dp
    (fun D D' => dHam n D D' = 1) (pairQuery n h k) (by norm_num) he
  intro D D' hadj
  simpa [pairQuery, Fin.sum_univ_two] using
    statistic_hamming_sensitivity n k h hh hk D D' hadj

/-- Measurable postprocessing preserves normalization and replacement privacy for any output
carrier.  [the theorem's stated inputs and assumptions](hyp:B,C,M,hM,f,hf), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon). -/
-- @node: privateKernel_mapOfMeasurable
lemma privateKernel_mapOfMeasurable {n : ℕ} {epsilon : ℝ}
    {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    (M : Kernel (Dataset n) B) (hM : PrivateKernel n epsilon M)
    (f : B → C) (hf : Measurable f) :
    PrivateKernel n epsilon (M.mapOfMeasurable f hf) := by
  let := hM.markov
  refine ⟨?_, ?_⟩
  · rw [Kernel.mapOfMeasurable_eq_map]
    exact Kernel.IsMarkovKernel.map M hf
  · intro D D' hadj E hE
    change ((M D).map f E).toReal ≤ Real.exp epsilon * ((M D').map f E).toReal
    rw [Measure.map_apply hf hE, Measure.map_apply hf hE]
    exact hM.pure_privacy D D' hadj (f ⁻¹' E) (hE.preimage hf)

/-- The clipped, floored ratio inherits pure privacy on all datasets.  [the theorem's stated inputs and assumptions](hyp:he,hh,hk), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon). -/
-- @node: Thk_private
lemma Thk_private (n k : ℕ) (epsilon h : ℝ)
    (he : 0 < epsilon) (hh : 0 < h) (hk : 0 < k) :
    PrivateKernel n epsilon (Thk n epsilon h k) := by
  exact privateKernel_mapOfMeasurable _
    (privateRatioRelease_private n k epsilon h he hh hk) _ (measurable_ratioMap n h k)

/-- The conservative interval inherits pure privacy from the same joint release.  [the theorem's stated inputs and assumptions](hyp:he,hh,hk), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon). -/
-- @node: Ihk_private
lemma Ihk_private (n k : ℕ) (epsilon h : ℝ)
    (he : 0 < epsilon) (hh : 0 < h) (hk : 0 < k) :
    PrivateKernel n epsilon (Ihk n epsilon h k) := by
  exact privateKernel_mapOfMeasurable _
    (privateRatioRelease_private n k epsilon h he hh hk) _
    (measurable_intervalMap n epsilon h k)

/-- A data-independent probability release is private at every nonnegative budget.  [the theorem's stated inputs and assumptions](hyp:epsilon,he,mu), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,B). -/
-- @node: privateKernel_const
lemma privateKernel_const {n : ℕ} {B : Type*} [MeasurableSpace B]
    (epsilon : ℝ) (he : 0 ≤ epsilon) (mu : Measure B) [IsProbabilityMeasure mu] :
    PrivateKernel n epsilon (Kernel.const (Dataset n) mu) := by
  refine ⟨inferInstance, ?_⟩
  intro D D' hadj E hE
  change mu.real E ≤ Real.exp epsilon * mu.real E
  exact le_mul_of_one_le_left (measureReal_nonneg) (Real.one_le_exp_iff.mpr he)

/-- Public tuning preserves privacy, including its data-independent fallback.  [the theorem's stated inputs and assumptions](hyp:hn,he), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon). -/
-- @node: publicTunedRelease_private
lemma publicTunedRelease_private (n : ℕ) (epsilon : ℝ)
    (hn : 2 ≤ n) (he : 0 < epsilon ∧ epsilon ≤ 1) :
    PrivateKernel n epsilon (publicTunedRelease n epsilon) := by
  classical
  unfold publicTunedRelease
  split_ifs with hr
  · exact privateKernel_const epsilon he.1.le _
  · have hp := public_tuning_parameters n epsilon hn he (lt_of_not_ge hr)
    exact Thk_private n _ epsilon _ he.1 hp.1 (by omega)

/-- The tuned interval remains private in both public branches.  [the theorem's stated inputs and assumptions](hyp:hn,he), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon). -/
-- @node: publicTunedInterval_private
lemma publicTunedInterval_private (n : ℕ) (epsilon : ℝ)
    (hn : 2 ≤ n) (he : 0 < epsilon ∧ epsilon ≤ 1) :
    PrivateKernel n epsilon (publicTunedInterval n epsilon) := by
  classical
  unfold publicTunedInterval
  split_ifs with hr
  · exact privateKernel_const epsilon he.1.le _
  · have hp := public_tuning_parameters n epsilon hn he (lt_of_not_ge hr)
    exact Ihk_private n _ epsilon _ he.1 hp.1 (by omega)

/-- Finite closed endpoint codes denote the usual real closed interval.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:l,u). -/
-- @node: closedInterval_toSet
lemma closedInterval_toSet (l u : ℝ) :
    (closedInterval l u).toSet = Set.Icc l u := by
  ext x
  simp [closedInterval, IntervalCode.toSet]

/-- The length of a finite closed interval is its nonnegative endpoint difference.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:l,u). -/
-- @node: closedInterval_leb
lemma closedInterval_leb (l u : ℝ) :
    (closedInterval l u).leb = ENNReal.ofReal (u - l) := by
  rw [IntervalCode.leb, closedInterval_toSet, Real.volume_Icc]

/-- The ratio center always belongs to the target range, even on arbitrary datasets. [The displayed conclusion](goal) follows. -/
-- @node: ratioMap_mem_Icc
lemma ratioMap_mem_Icc (n k : ℕ) (h : ℝ) (v : Fin 2 → ℝ) :
    ratioMap n h k v ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold ratioMap clip
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- A nonnegative radius around a center in the target range has ordered truncated endpoints. The result uses [the stated assumptions](hyp:hz,hr) and establishes [the displayed conclusion](goal). -/
-- @node: truncated_interval_endpoints
lemma truncated_interval_endpoints (z r : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1)
    (hr : 0 ≤ r) : max (-1) (z - r) ≤ z ∧ z ≤ min 1 (z + r) := by
  constructor
  · exact max_le hz.1 (by linarith)
  · exact le_min hz.2 (by linarith)

/-- The released conservative interval is nonempty and contains its clipped center.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon,h,v). -/
-- @node: ratioMap_mem_intervalMap
lemma ratioMap_mem_intervalMap (n k : ℕ) (epsilon h : ℝ) (v : Fin 2 → ℝ) :
    ratioMap n h k v ∈ (intervalMap n epsilon h k v).toSet := by
  rw [intervalMap, closedInterval_toSet]
  exact truncated_interval_endpoints _ _ (ratioMap_mem_Icc n k h v)
    (Real.sqrt_nonneg _)

/-- Truncation bounds each interval by the target diameter and twice its public radius.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon,h,v). -/
-- @node: intervalMap_leb_le
lemma intervalMap_leb_le (n k : ℕ) (epsilon h : ℝ) (v : Fin 2 → ℝ) :
    (intervalMap n epsilon h k v).leb ≤
      ENNReal.ofReal (min 2 (2 * Real.sqrt (10 * Vbound n epsilon h k))) := by
  rw [intervalMap, closedInterval_leb]
  apply ENNReal.ofReal_le_ofReal
  apply le_min
  · have hl := le_max_left (-1 : ℝ)
      (ratioMap n h k v - Real.sqrt (10 * Vbound n epsilon h k))
    have hu := min_le_left (1 : ℝ)
      (ratioMap n h k v + Real.sqrt (10 * Vbound n epsilon h k))
    linarith
  · have hl := le_max_right (-1 : ℝ)
      (ratioMap n h k v - Real.sqrt (10 * Vbound n epsilon h k))
    have hu := min_le_right (1 : ℝ)
      (ratioMap n h k v + Real.sqrt (10 * Vbound n epsilon h k))
    linarith

/-- Integrating the deterministic interval-length bound gives the finite-sample guarantee.  [the theorem's stated inputs and assumptions](hyp:P), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon,h,he). -/
-- @node: Ihk_expectedLength_le
lemma Ihk_expectedLength_le (n k : ℕ) (epsilon h : ℝ) (he : 0 < epsilon)
    (P : CausalLaw) :
    expectedLength n (Ihk n epsilon h k) P ≤
      ENNReal.ofReal (min 2 (2 * Real.sqrt (10 * Vbound n epsilon h k))) := by
  letI : IsProbabilityMeasure (Pobs P) := by
    unfold Pobs
    exact Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (dataLaw n P) := by
    unfold dataLaw
    infer_instance
  letI := privateRatioRelease_markov n k epsilon h he
  unfold expectedLength Ihk
  rw [Kernel.mapOfMeasurable_eq_map, ← Measure.map_comp _ _
    (measurable_intervalMap n epsilon h k)]
  exact (lintegral_map_le _ _).trans
    (lintegral_le_const (Filter.Eventually.of_forall (intervalMap_leb_le n k epsilon h)))

/-- Projection to the target range cannot increase distance to a target in that range.  the asserted conclusion follows. The result uses [the stated assumptions](hyp:ht) and establishes [the displayed conclusion](goal). -/
-- @node: clip_abs_sub_le
lemma clip_abs_sub_le (z t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |clip (-1) 1 z - t| ≤ |z - t| := by
  unfold clip
  apply abs_le.mpr
  constructor
  · have hz := neg_abs_le (z - t)
    have hl : t - |z - t| ≤ min 1 z := le_min (by linarith [abs_nonneg (z-t), ht.1, ht.2])
      (by linarith)
    have hm := hl.trans (le_max_right (-1 : ℝ) (min 1 z))
    linarith
  · have hz := le_abs_self (z - t)
    have hu : max (-1) (min 1 z) ≤ t + |z - t| :=
      max_le (by linarith [abs_nonneg (z-t), ht.1, ht.2])
        ((min_le_right 1 z).trans (by linarith))
    linarith

/-- The denominator floor fixes the population denominator and contracts its perturbation.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:d,y,D,hD). -/
-- @node: floor_denominator_abs_sub_le
lemma floor_denominator_abs_sub_le (d y D : ℝ) (hD : d ≤ D) :
    |max d y - D| ≤ |y - D| := by
  have h := abs_max_sub_max_le_abs y D d
  simpa only [max_comm y d, max_eq_left hD] using h

/-- The raw floored ratio is controlled by the two coordinate perturbations over the floor.  [the theorem's stated inputs and assumptions](hyp:hD,hN), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:d,x,y,N,D,hd). -/
-- @node: floored_ratio_perturbation
lemma floored_ratio_perturbation (d x y N D : ℝ) (hd : 0 < d)
    (hD : d ≤ D) (hN : |N / D| ≤ 1) :
    |x / max d y - N / D| ≤ (|x - N| + |y - D|) / d := by
  have hDp : 0 < D := hd.trans_le hD
  have hBp : 0 < max d y := hd.trans_le (le_max_left _ _)
  have hfloor := floor_denominator_abs_sub_le d y D hD
  have hid : x / max d y - N / D =
      ((x - N) + (N / D) * (D - max d y)) / max d y := by
    field_simp
    <;> ring
  calc
    |x / max d y - N / D| =
        |(x - N) + (N / D) * (D - max d y)| / max d y := by
      rw [hid, abs_div, abs_of_pos hBp]
    _ ≤ (|x - N| + |y - D|) / max d y := by
      apply div_le_div_of_nonneg_right _ hBp.le
      calc
        |(x - N) + (N / D) * (D - max d y)| ≤
            |x - N| + |N / D| * |D - max d y| := by
          simpa only [abs_mul] using abs_add_le (x-N) ((N/D)*(D-max d y))
        _ ≤ |x - N| + |D - max d y| := by
          exact add_le_add_right (by
            simpa using mul_le_mul_of_nonneg_right hN (abs_nonneg (D - max d y))) _
        _ ≤ |x - N| + |y - D| := by
          rw [abs_sub_comm D]
          exact add_le_add_right hfloor _
    _ ≤ (|x - N| + |y - D|) / d :=
      div_le_div_of_nonneg_left (by positivity) hd (le_max_left _ _)

/-- Bias plus the two released coordinate perturbations controls the clipped estimator error. The result uses [the stated assumptions](hyp:hd,hD,hN,ht,hb) and establishes [the displayed conclusion](goal). -/
-- @node: ratioMap_error_le
lemma ratioMap_error_le (n k : ℕ) (h N D t b : ℝ) (v : Fin 2 → ℝ)
    (hd : 0 < d0 n h k) (hD : d0 n h k ≤ D) (hN : |N / D| ≤ 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hb : |N / D - t| ≤ b) :
    |ratioMap n h k v - t| ≤ b + (|v 0 - N| + |v 1 - D|) / d0 n h k := by
  calc
    |ratioMap n h k v - t| ≤ |v 0 / max (d0 n h k) (v 1) - t| :=
      clip_abs_sub_le _ _ ht
    _ ≤ |v 0 / max (d0 n h k) (v 1) - N / D| + |N / D - t| :=
      abs_sub_le _ _ _
    _ ≤ (|v 0 - N| + |v 1 - D|) / d0 n h k + b :=
      add_le_add (floored_ratio_perturbation _ _ _ _ _ hd hD hN) hb
    _ = b + (|v 0 - N| + |v 1 - D|) / d0 n h k := add_comm _ _

/-- Nonnegative occupancy weights preserve the binary pair numerator domination.  [the theorem's stated inputs and assumptions](hyp:hn,hk,hh,P,hP), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k). -/
-- @node: population_numerator_abs_le_denominator
lemma population_numerator_abs_le_denominator (n k : ℕ) (h : ℝ)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hh : 0 < h ∧ h ≤ 1 / 4)
    (P : CausalLaw) (hP : CompleteModel P) :
    |Nbar n h k (dataLaw n P)| ≤ Dbar n h k (dataLaw n P) := by
  have hc := occupancy_cancellation n k h hn hk hh P (dataLaw n P) rfl hP
  rw [hc.1, hc.2.1]
  calc
    |∑ j : Fin k, occupancyWeight n h k P j * nu h k P j| ≤
        ∑ j : Fin k, |occupancyWeight n h k P j * nu h k P j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin k, occupancyWeight n h k P j * dj h k P j := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (occupancyWeight_nonneg n k h P j)]
      exact mul_le_mul_of_nonneg_left
        (conditional_cell_numerator_abs_le_denominator k h (by omega) hh P hP j)
        (occupancyWeight_nonneg n k h P j)

/-- The population comparison ratio belongs to the target range.  [the theorem's stated inputs and assumptions](hyp:hn,hk,hh,P,hP), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k). -/
-- @node: population_ratio_abs_le_one
lemma population_ratio_abs_le_one (n k : ℕ) (h : ℝ)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hh : 0 < h ∧ h ≤ 1 / 4)
    (P : CausalLaw) (hP : CompleteModel P) :
    |Nbar n h k (dataLaw n P) / Dbar n h k (dataLaw n P)| ≤ 1 := by
  have hc := occupancy_cancellation n k h hn hk hh P (dataLaw n P) rfl hP
  have hpos : 0 < Dbar n h k (dataLaw n P) :=
    (info_d0_pos n k h (by omega) (by omega) hh.1).2.trans_le hc.2.2.2.2.2.1
  rw [abs_div, abs_of_pos hpos, div_le_one hpos]
  exact population_numerator_abs_le_denominator n k h hn hk hh P hP

/-- Two applications of the quadratic sum bound give the roadmap's pointwise squared error. The result uses [the stated assumptions](hyp:hd,hD,hN,ht,hb) and establishes [the displayed conclusion](goal). -/
-- @node: ratioMap_squared_error_le
lemma ratioMap_squared_error_le (n k : ℕ) (h N D t b : ℝ) (v : Fin 2 → ℝ)
    (hd : 0 < d0 n h k) (hD : d0 n h k ≤ D) (hN : |N / D| ≤ 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hb : |N / D - t| ≤ b) :
    (ratioMap n h k v - t)^2 ≤
      2*b^2 + 4/(d0 n h k)^2 * ((v 0-N)^2 + (v 1-D)^2) := by
  have hbpos : 0 ≤ b := (abs_nonneg _).trans hb
  have herr := ratioMap_error_le n k h N D t b v hd hD hN ht hb
  have hsquare : (ratioMap n h k v - t)^2 ≤
      (b + (|v 0-N| + |v 1-D|) / d0 n h k)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) herr 2
  have hsum : (|v 0-N| + |v 1-D|)^2 ≤ 2*((v 0-N)^2 + (v 1-D)^2) := by
    simpa only [sq_abs] using (add_sq_le (a := |v 0-N|) (b := |v 1-D|))
  have hdiv : ((|v 0-N| + |v 1-D|) / d0 n h k)^2 ≤
      2/(d0 n h k)^2 * ((v 0-N)^2 + (v 1-D)^2) := by
    rw [div_pow]
    calc
      (|v 0-N| + |v 1-D|)^2 / (d0 n h k)^2 ≤
          (2*((v 0-N)^2 + (v 1-D)^2)) / (d0 n h k)^2 :=
        div_le_div_of_nonneg_right hsum (sq_nonneg _)
      _ = _ := by ring
  have hquad := add_sq_le (a := b) (b := (|v 0-N| + |v 1-D|) / d0 n h k)
  calc
    (ratioMap n h k v - t)^2 ≤
        2 * (b^2 + ((|v 0-N| + |v 1-D|) / d0 n h k)^2) := hsquare.trans hquad
    _ ≤ 2 * (b^2 + 2/(d0 n h k)^2 * ((v 0-N)^2 + (v 1-D)^2)) := by
      gcongr
    _ = _ := by ring

/-- For each model law, only the public bias and released centered coordinate squares are needed.  [the theorem's stated inputs and assumptions](hyp:hn,hk,hh,P,hP,v), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k). -/
-- @node: ratioMap_model_squared_error_le
lemma ratioMap_model_squared_error_le (n k : ℕ) (h : ℝ)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hh : 0 < h ∧ h ≤ 1 / 4)
    (P : CausalLaw) (hP : CompleteModel P) (v : Fin 2 → ℝ) :
    (ratioMap n h k v - theta P)^2 ≤
      2*(bias h k)^2 + 4/(d0 n h k)^2 *
        ((v 0-Nbar n h k (dataLaw n P))^2 + (v 1-Dbar n h k (dataLaw n P))^2) := by
  have hc := occupancy_cancellation n k h hn hk hh P (dataLaw n P) rfl hP
  exact ratioMap_squared_error_le n k h _ _ _ _ v
    (info_d0_pos n k h (by omega) (by omega) hh.1).2 hc.2.2.2.2.2.1
    (population_ratio_abs_le_one n k h hn hk hh P hP) (theta_mem_Icc P hP)
    hc.2.2.2.2.2.2

/-- Squaring the roughness term converts its fifth-root power to the two-fifths power. The result uses [the stated assumptions](hyp:hh) and establishes [the displayed conclusion](goal). -/
-- @node: cellWidth_fifth_power_sq
lemma cellWidth_fifth_power_sq (k : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    ((cellWidth h k)^(1/5 : ℝ))^2 = (cellWidth h k)^(2/5 : ℝ) := by
  have hw : 0 ≤ cellWidth h k := by unfold cellWidth; positivity
  have hp := Real.rpow_mul_natCast hw (1/5 : ℝ) 2
  norm_num at hp
  exact hp.symm

/-- The quadratic sum inequality bounds the two contributions to the public bias. The result uses [the stated assumptions](hyp:hh) and establishes [the displayed conclusion](goal). -/
-- @node: bias_squared_le
lemma bias_squared_le (k : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    2*(bias h k)^2 ≤ 36*h^2 + 2304*(cellWidth h k)^(2/5 : ℝ) := by
  have hquad := add_sq_le (a := 3*h) (b := 24*(cellWidth h k)^(1/5 : ℝ))
  have hp := cellWidth_fifth_power_sq k h hh
  unfold bias
  nlinarith [hp]

/-- Substitution of the public floor converts the occupancy and noise terms to inverse scales.  [the theorem's stated inputs and assumptions](hyp:ha,he,hW), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon,W). -/
-- @node: variance_floor_envelope_le
lemma variance_floor_envelope_le (n k : ℕ) (epsilon h W : ℝ)
    (ha : 0 < info n h k) (he : 0 < epsilon)
    (hW : W ≤ 9 / 2 * info n h k) :
    144*W/(d0 n h k)^2 + 2304/(epsilon^2*(d0 n h k)^2) ≤
      294912*(info n h k)⁻¹ + 1048576*(epsilon*info n h k)^(-2 : ℤ) := by
  have hocc : 144*W/(d0 n h k)^2 ≤ 294912*(info n h k)⁻¹ := by
    calc
      144*W/(d0 n h k)^2 ≤ 144*(9/2*info n h k)/(d0 n h k)^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by norm_num))
          (sq_nonneg _)
      _ = _ := by
        unfold d0
        field_simp [ha.ne']
        ring
  have hnoise : 2304/(epsilon^2*(d0 n h k)^2) =
      1048576*(epsilon*info n h k)^(-2 : ℤ) := by
    unfold d0
    simp only [zpow_neg, zpow_ofNat]
    field_simp [ha.ne', he.ne']
    ring
  rw [hnoise]
  exact add_le_add hocc le_rfl

/-- The roadmap's bias, occupancy variance and independent Laplace variance fit the public
envelope.  [the theorem's stated inputs and assumptions](hyp:hn,hk,he,hh,P,hP), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon). -/
-- @node: model_variance_envelope_le
lemma model_variance_envelope_le (n k : ℕ) (epsilon h : ℝ)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (he : 0 < epsilon)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) :
    2*(bias h k)^2 + 144*Wocc n h k P/(d0 n h k)^2 +
      2304/(epsilon^2*(d0 n h k)^2) ≤ Vbound n epsilon h k := by
  have ha := (info_d0_pos n k h (by omega) (by omega) hh.1).1
  have hc := occupancy_cancellation n k h hn hk hh P (dataLaw n P) rfl hP
  have hv := variance_floor_envelope_le n k epsilon h (Wocc n h k P) ha he
    (by linarith [hc.2.2.2.2.1])
  have hb := bias_squared_le k h hh.1.le
  have hcell : 0 ≤ (cellWidth h k)^(2/5 : ℝ) := Real.rpow_nonneg (by
    unfold cellWidth; exact div_nonneg (by linarith) (Nat.cast_nonneg _)) _
  have hi : 0 ≤ (info n h k)⁻¹ := inv_nonneg.mpr ha.le
  have heps : 0 ≤ (epsilon*info n h k)^(-2 : ℤ) := by
    simp only [zpow_neg, zpow_ofNat]
    positivity
  unfold Vbound
  norm_num only [zpow_neg, zpow_ofNat, pow_succ, pow_zero, mul_one, OfNat.ofNat] at hv heps ⊢
  nlinarith [sq_nonneg h]

/-- Truncation retains any target in the model range within the public radius of the center. The result uses [the stated assumptions](hyp:ht,herr) and establishes [the displayed conclusion](goal). -/
-- @node: target_mem_intervalMap_of_error_le
lemma target_mem_intervalMap_of_error_le (n k : ℕ) (epsilon h t : ℝ)
    (v : Fin 2 → ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (herr : |ratioMap n h k v - t| ≤ Real.sqrt (10 * Vbound n epsilon h k)) :
    t ∈ (intervalMap n epsilon h k v).toSet := by
  rw [intervalMap, closedInterval_toSet]
  have he := abs_le.mp herr
  exact ⟨max_le ht.1 (by linarith), le_min ht.2 (by linarith)⟩

/-- The public variance envelope is strictly positive on admissible radii and cell counts.  [the theorem's stated inputs and assumptions](hyp:hh), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon,hn,hk). -/
-- @node: Vbound_pos
lemma Vbound_pos (n k : ℕ) (epsilon h : ℝ) (hn : 0 < n) (hk : 0 < k)
    (hh : 0 < h) : 0 < Vbound n epsilon h k := by
  have ha := (info_d0_pos n k h hn hk hh).1
  have hw : 0 ≤ cellWidth h k := by unfold cellWidth; positivity
  unfold Vbound
  have hc := Real.rpow_nonneg hw (2/5 : ℝ)
  have hi := inv_pos.mpr ha
  have he : 0 ≤ (epsilon*info n h k)^(-2 : ℤ) := by
    simp only [zpow_neg, zpow_ofNat]
    positivity
  positivity

/-- Markov's inequality turns a second-moment envelope into a one-tenth radius-tail bound.  [the theorem's stated inputs and assumptions](hyp:Q,f,hf,t,V,hV,hmse), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:B). -/
-- @node: squared_error_radius_tail_le
lemma squared_error_radius_tail_le {B : Type*} [MeasurableSpace B]
    (Q : Measure B) (f : B → ℝ) (hf : Measurable f) (t V : ℝ) (hV : 0 < V)
    (hmse : (∫⁻ x, ENNReal.ofReal ((f x-t)^2) ∂Q) ≤ ENNReal.ofReal V) :
    Q {x | Real.sqrt (10*V) < |f x-t|} ≤ ENNReal.ofReal (1/10 : ℝ) := by
  have hmeas : Measurable (fun x => ENNReal.ofReal ((f x-t)^2)) := by fun_prop
  have ht := meas_ge_le_lintegral_div (μ := Q) hmeas.aemeasurable
    (ne_of_gt (by positivity : 0 < ENNReal.ofReal (10*V))) ENNReal.ofReal_ne_top
  have hsub : {x | Real.sqrt (10*V) < |f x-t|} ⊆
      {x | ENNReal.ofReal (10*V) ≤ ENNReal.ofReal ((f x-t)^2)} := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 10*V)
    have hr := Real.sqrt_nonneg (10*V)
    have ha := abs_nonneg (f x-t)
    have habs := sq_abs (f x-t)
    change Real.sqrt (10*V) < |f x-t| at hx
    nlinarith
  calc
    Q {x | Real.sqrt (10*V) < |f x-t|} ≤
        Q {x | ENNReal.ofReal (10*V) ≤ ENNReal.ofReal ((f x-t)^2)} := measure_mono hsub
    _ ≤ (∫⁻ x, ENNReal.ofReal ((f x-t)^2) ∂Q) / ENNReal.ofReal (10*V) := ht
    _ ≤ ENNReal.ofReal V / ENNReal.ofReal (10*V) := ENNReal.div_le_div_right hmse _
    _ = ENNReal.ofReal (1/10 : ℝ) := by
      rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < 10*V)]
      congr 1
      field_simp

/-- The truncated interval misses a model-range target only on the radius-tail event. The result uses [the stated assumptions](hyp:ht,hV,hmse) and establishes [the displayed conclusion](goal). -/
-- @node: intervalMap_miss_probability_le
lemma intervalMap_miss_probability_le (n k : ℕ) (epsilon h t : ℝ)
    (Q : Measure (Fin 2 → ℝ)) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hV : 0 < Vbound n epsilon h k)
    (hmse : (∫⁻ v, ENNReal.ofReal ((ratioMap n h k v - t) ^ 2) ∂Q) ≤
      ENNReal.ofReal (Vbound n epsilon h k)) :
    Q {v | t ∉ (intervalMap n epsilon h k v).toSet} ≤ ENNReal.ofReal (1/10 : ℝ) := by
  refine (measure_mono ?_).trans
    (squared_error_radius_tail_le Q _ (measurable_ratioMap n h k) t _ hV hmse)
  intro v hv
  exact lt_of_not_ge (fun herr => hv
    (target_mem_intervalMap_of_error_le n k epsilon h t v ht herr))

/-- Scalar postprocessing expresses the mean-square error as an integral over the joint release.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon,h,t,P). -/
-- @node: Thk_squared_error_eq
lemma Thk_squared_error_eq (n k : ℕ) (epsilon h t : ℝ) (P : CausalLaw) :
    (∫⁻ u, ENNReal.ofReal ((u-t)^2) ∂(Thk n epsilon h k ∘ₘ dataLaw n P)) =
      ∫⁻ v, ENNReal.ofReal ((ratioMap n h k v-t)^2)
        ∂(privateRatioRelease n epsilon h k ∘ₘ dataLaw n P) := by
  unfold Thk
  rw [Kernel.mapOfMeasurable_eq_map, ← Measure.map_comp _ _ (measurable_ratioMap n h k)]
  exact lintegral_map (by fun_prop) (measurable_ratioMap n h k)

/-- The finite-sample second-moment guarantee implies coverage for the interval from the same
joint release, including targets on the boundary of the model range.  [the theorem's stated inputs and assumptions](hyp:hn,hk,he,hh,P,hP,hmse), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon). -/
-- @node: Ihk_coverage_of_squared_error_le
lemma Ihk_coverage_of_squared_error_le (n k : ℕ) (epsilon h : ℝ)
    (hn : 0 < n) (hk : 0 < k) (he : 0 < epsilon) (hh : 0 < h)
    (P : CausalLaw) (hP : CompleteModel P)
    (hmse : (∫⁻ u, ENNReal.ofReal ((u-theta P)^2)
      ∂(Thk n epsilon h k ∘ₘ dataLaw n P)) ≤ ENNReal.ofReal (Vbound n epsilon h k)) :
    9/10 ≤ coverage n (Ihk n epsilon h k) P := by
  letI : IsProbabilityMeasure (Pobs P) := by
    unfold Pobs
    exact Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  letI := privateRatioRelease_markov n k epsilon h he
  let Q := privateRatioRelease n epsilon h k ∘ₘ dataLaw n P
  let E : Set (Fin 2 → ℝ) := {v | theta P ∈ (intervalMap n epsilon h k v).toSet}
  have hE : MeasurableSet E :=
    (measurableSet_interval_contains (theta P)).preimage (measurable_intervalMap n epsilon h k)
  have hmiss : Q Eᶜ ≤ ENNReal.ofReal (1/10 : ℝ) := by
    exact intervalMap_miss_probability_le n k epsilon h (theta P) Q
      (theta_mem_Icc P hP) (Vbound_pos n k epsilon h hn hk hh)
      ((Thk_squared_error_eq n k epsilon h (theta P) P) ▸ hmse)
  have hmissReal : Q.real Eᶜ ≤ 1/10 := by
    simpa [Measure.real] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hmiss
  have hsum := probReal_compl_eq_one_sub (μ := Q) hE
  have hcov : coverage n (Ihk n epsilon h k) P = Q.real E := by
    unfold coverage Ihk Measure.real
    rw [Kernel.mapOfMeasurable_eq_map, ← Measure.map_comp _ _
      (measurable_intervalMap n epsilon h k), Measure.map_apply
      (measurable_intervalMap n epsilon h k) (measurableSet_interval_contains (theta P))]
    rfl
  rw [hcov]
  linarith

/-- The public fallback interval covers every law in the complete model with probability one.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,P,hP). -/
-- @node: full_interval_coverage
lemma full_interval_coverage (n : ℕ) (P : CausalLaw) (hP : CompleteModel P) :
    coverage n (Kernel.const (Dataset n) (Measure.dirac (closedInterval (-1) 1))) P = 1 := by
  letI : IsProbabilityMeasure (Pobs P) := by
    unfold Pobs
    exact Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  have ht : theta P ∈ (closedInterval (-1) 1).toSet := by
    rw [closedInterval_toSet]
    exact theta_mem_Icc P hP
  unfold coverage Measure.real
  change ((dataLaw n P).bind (fun _ => Measure.dirac (closedInterval (-1) 1))
    {c | theta P ∈ c.toSet}).toReal = 1
  rw [Measure.bind_const]
  simp [Measure.dirac_apply' _ (measurableSet_interval_contains (theta P)), ht]

/-- Coverage of the tuned interval follows from the tuned second moment on its active branch
and full-range coverage on its fallback branch.  [the theorem's stated inputs and assumptions](hyp:hn,he,P,hP,hmse), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon). -/
-- @node: publicTunedInterval_coverage_of_squared_error_le
lemma publicTunedInterval_coverage_of_squared_error_le (n : ℕ) (epsilon : ℝ)
    (hn : 2 ≤ n) (he : 0 < epsilon ∧ epsilon ≤ 1) (P : CausalLaw) (hP : CompleteModel P)
    (hmse : rate n epsilon < 1/8 →
      (∫⁻ u, ENNReal.ofReal ((u-theta P)^2)
        ∂(Thk n epsilon (tunedH n epsilon) (tunedK n epsilon) ∘ₘ dataLaw n P)) ≤
          ENNReal.ofReal (Vbound n epsilon (tunedH n epsilon) (tunedK n epsilon))) :
    9/10 ≤ coverage n (publicTunedInterval n epsilon) P := by
  classical
  unfold publicTunedInterval
  split_ifs with hr
  · rw [full_interval_coverage n P hP]
    norm_num
  · have hp := public_tuning_parameters n epsilon hn he (lt_of_not_ge hr)
    exact Ihk_coverage_of_squared_error_le n _ epsilon _ (by omega) (by omega)
      he.1 hp.1 P hP (hmse (lt_of_not_ge hr))

end CausalSmith.Stat.PrivateCateRoughdesign

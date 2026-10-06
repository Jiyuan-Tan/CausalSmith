module
public import Causalean.Mathlib.Probability.LimitTheorems.Approximation.CharFunBound
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.BernsteinKernel
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.UniformOrderMoments
public import Causalean.Stat.Quantile.Transport

/-!
# Adjacent order-statistic coupling for power approximation

Order-statistic moments, the randomized adjacent-statistic coupling, and its
threshold-indicator L1 estimate. The power-density approximation is assembled
in `PowerL1`.

The mixture includes deterministic endpoints. Its moments follow from the
single-statistic formulas, and its threshold error is controlled by the
centered second moment.
-/

@[expose] public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open Causalean.Stat.OrderStatistic

noncomputable section

/-- For a [power](hyp:s), the [power density](goal) at a real argument is `s(1-u)^(s-1)`. -/
def powerDensity (s u : ℝ) : ℝ := s * (1 - u) ^ (s - 1)

/-- A [sample size](hyp:N), [adjacent order index](hyp:k), and
 [interpolation fraction](hyp:δ) determine
 [the randomized adjacent order-statistic law](goal), which mixes the adjacent statistics of
 `N-1` uniforms with deterministic endpoints. -/
def adjacentOrderMix (N k : ℕ) (δ : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (1 - δ)) • (iidSample uniform01 (N - 1)).map
      (fun x => if h : k = 0 then (0 : ℝ)
        else if h' : k ≤ N - 1 then sortedSample (N - 1) x ⟨k - 1, by omega⟩
        else 1) +
    (ENNReal.ofReal δ) • (iidSample uniform01 (N - 1)).map
      (fun x => if h : k + 1 = N then (1 : ℝ)
        else if h' : k < N - 1 then sortedSample (N - 1) x ⟨k, h'⟩
        else 1)

private theorem sortedSample_aemeasurable_local (n : ℕ) :
    AEMeasurable (sortedSample n) (iidSample uniform01 n) := by
  classical
  let s (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
    {x | Monotone (x ∘ σ)}
  have hs (σ : Equiv.Perm (Fin n)) : MeasurableSet (s σ) := by
    have hc : Continuous (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
    exact (isClosed_monotone.preimage hc).measurableSet
  have hcover : (⋃ σ, s σ) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨Tuple.sort x, Tuple.monotone_sort x⟩
  have hpiece (σ : Equiv.Perm (Fin n)) :
      AEMeasurable (sortedSample n) (volume.restrict (s σ)) := by
    have hp : Measurable (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
    apply hp.aemeasurable.congr
    exact ae_restrict_of_forall_mem (hs σ) (fun x hx =>
      (show (fun x => x ∘ σ) x = sortedSample n x from
        (Tuple.comp_sort_eq_comp_iff_monotone (f := x) (σ := σ)).2 hx))
  have hsort : AEMeasurable (sortedSample n) (volume : Measure (Fin n → ℝ)) := by
    simpa only [hcover, Measure.restrict_univ] using (AEMeasurable.iUnion hpiece)
  rw [iid_uniform_cube_law]
  exact hsort.restrict

private theorem integrable_endpoint_moments {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {g : α → ℝ}
    (hg : AEMeasurable g μ) (hb : ∀ᵐ x ∂μ, g x ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun u : ℝ => u) (μ.map g) ∧
      Integrable (fun u : ℝ => u ^ 2) (μ.map g) := by
  have hgi : Integrable g μ := by
    apply Integrable.of_bound hg.aestronglyMeasurable 1
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have hg2 : Integrable (fun x => (g x) ^ 2) μ := by
    apply Integrable.of_bound (hg.pow_const 2).aestronglyMeasurable 1
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  constructor
  · exact (integrable_map_measure measurable_id.aestronglyMeasurable hg).2 hgi
  · exact (integrable_map_measure (measurable_id.pow_const 2).aestronglyMeasurable hg).2 hg2

private def orderEndpoint (n r : ℕ) (x : Fin n → ℝ) : ℝ :=
  if h : r = 0 then 0
  else if h' : r ≤ n then sortedSample n x ⟨r - 1, by omega⟩
  else 1

set_option maxHeartbeats 1000000 in
-- Expanding tuple sorting through its finite chamber cover requires extra elaboration time.
private theorem orderEndpoint_aemeasurable (n r : ℕ) :
    AEMeasurable (orderEndpoint n r) (iidSample uniform01 n) := by
  unfold orderEndpoint
  split_ifs with h h'
  · exact aemeasurable_const
  · exact (measurable_pi_apply ⟨r - 1, by omega⟩).comp_aemeasurable
      (sortedSample_aemeasurable_local n)
  · exact aemeasurable_const

private theorem orderEndpoint_mem_Icc (n r : ℕ) :
    ∀ᵐ x ∂iidSample uniform01 n, orderEndpoint n r x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [iid_uniform_cube_law]
  apply ae_restrict_of_forall_mem
  · have h : MeasurableSet (⋂ i : Fin n,
        (fun x : Fin n → ℝ => x i) ⁻¹' Set.Icc (0 : ℝ) 1) := by
      exact MeasurableSet.iInter (fun i => measurableSet_Icc.preimage (measurable_pi_apply i))
    have heq : unitCube n = ⋂ i : Fin n,
        (fun x : Fin n → ℝ => x i) ⁻¹' Set.Icc (0 : ℝ) 1 := by
      ext x
      simp [unitCube]
    rw [heq]
    exact h
  intro x hx
  unfold orderEndpoint
  split_ifs with h h'
  · exact ⟨le_refl 0, zero_le_one⟩
  · exact hx (Tuple.sort x ⟨r - 1, by omega⟩)
  · exact ⟨zero_le_one, le_refl 1⟩

private theorem orderEndpoint_mean (n r : ℕ) (hr : r ≤ n + 1) :
    (∫ u, u ∂(iidSample uniform01 n).map (orderEndpoint n r)) =
      (r : ℝ) / (n + 1) := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
  haveI : IsProbabilityMeasure (iidSample uniform01 n) := by
    dsimp [iidSample]
    infer_instance
  change (∫ u, id u ∂(iidSample uniform01 n).map (orderEndpoint n r)) = _
  rw [integral_map (orderEndpoint_aemeasurable n r)
    measurable_id.aestronglyMeasurable]
  simp only [id_eq, Function.comp_apply]
  by_cases h0 : r = 0
  · subst r
    simp [orderEndpoint]
  by_cases hn : r ≤ n
  · have hn0 : 0 < n := by omega
    have hj : r - 1 < n := by omega
    simp only [orderEndpoint, h0, ↓reduceDIte, hn]
    rw [uniform_order_mean hn0 ⟨r - 1, hj⟩]
    have hr0 : 0 < r := by omega
    simp only [Fin.val_mk]
    congr 1
    exact_mod_cast (show r - 1 + 1 = r by omega)
  · have htop : r = n + 1 := by omega
    subst r
    simp [orderEndpoint, integral_const]
    have hne : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp

private theorem orderEndpoint_second_moment (n r : ℕ) (hr : r ≤ n + 1) :
    (∫ u, u ^ 2 ∂(iidSample uniform01 n).map (orderEndpoint n r)) =
      (r : ℝ) * (r + 1) / ((n + 1) * (n + 2)) := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
  haveI : IsProbabilityMeasure (iidSample uniform01 n) := by
    dsimp [iidSample]
    infer_instance
  change (∫ u, (id u) ^ 2 ∂(iidSample uniform01 n).map (orderEndpoint n r)) = _
  rw [integral_map (orderEndpoint_aemeasurable n r)
    (measurable_id.pow_const 2).aestronglyMeasurable]
  simp only [id_eq]
  by_cases h0 : r = 0
  · subst r
    simp [orderEndpoint]
  by_cases hn : r ≤ n
  · have hn0 : 0 < n := by omega
    have hj : r - 1 < n := by omega
    simp only [orderEndpoint, h0, ↓reduceDIte, hn]
    rw [uniform_order_second_moment hn0 ⟨r - 1, hj⟩]
    simp only [Fin.val_mk]
    have hrsub : r - 1 + 1 = r := by omega
    have hrsub2 : r - 1 + 2 = r + 1 := by omega
    have h1 : ((r - 1 : ℕ) : ℝ) + 1 = r := by exact_mod_cast hrsub
    have h2 : ((r - 1 : ℕ) : ℝ) + 2 = (r : ℝ) + 1 := by exact_mod_cast hrsub2
    rw [h1, h2]
  · have htop : r = n + 1 := by omega
    subst r
    simp [orderEndpoint, integral_const]
    have hne1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hne2 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring

private theorem adjacentOrderMix_eq_endpoints {N k : ℕ} (hN : 0 < N) (hk : k < N)
    (δ : ℝ) :
    adjacentOrderMix N k δ =
      (ENNReal.ofReal (1 - δ)) •
        (iidSample uniform01 (N - 1)).map (orderEndpoint (N - 1) k) +
      (ENNReal.ofReal δ) •
        (iidSample uniform01 (N - 1)).map (orderEndpoint (N - 1) (k + 1)) := by
  have hL : (fun x : Fin (N - 1) → ℝ =>
      if h : k = 0 then (0 : ℝ)
      else if h' : k ≤ N - 1 then sortedSample (N - 1) x ⟨k - 1, by omega⟩
      else 1) = orderEndpoint (N - 1) k := rfl
  have hU : (fun x : Fin (N - 1) → ℝ =>
      if h : k + 1 = N then (1 : ℝ)
      else if h' : k < N - 1 then sortedSample (N - 1) x ⟨k, h'⟩
      else 1) = orderEndpoint (N - 1) (k + 1) := by
    funext x
    by_cases ht : k + 1 = N
    · have hnot : ¬k + 1 ≤ N - 1 := by omega
      have hNnot : N ≠ 0 := by omega
      have hNle : ¬N ≤ N - 1 := by omega
      simp [orderEndpoint, ht, hNnot, hNle]
    · have hi : k < N - 1 := by omega
      have hle : k + 1 ≤ N - 1 := by omega
      simp [orderEndpoint, ht, hi, hle]
  simp only [adjacentOrderMix, hL, hU]

private theorem adjacentOrderMix_integral {N k : ℕ} (hN : 0 < N) (hk : k < N)
    {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (f : ℝ → ℝ)
    (hlo : Integrable f ((iidSample uniform01 (N - 1)).map (orderEndpoint (N - 1) k)))
    (hhi : Integrable f ((iidSample uniform01 (N - 1)).map (orderEndpoint (N - 1) (k + 1)))) :
    (∫ u, f u ∂adjacentOrderMix N k δ) =
      (1 - δ) * (∫ u, f u ∂(iidSample uniform01 (N - 1)).map (orderEndpoint (N - 1) k)) +
      δ * (∫ u, f u ∂(iidSample uniform01 (N - 1)).map (orderEndpoint (N - 1) (k + 1))) := by
  have hδ0 : 0 ≤ δ := hδ.1
  have hδ1 : 0 ≤ 1 - δ := by linarith [hδ.2]
  rw [adjacentOrderMix_eq_endpoints hN hk,
    integral_add_measure (hlo.smul_measure (by simp)) (hhi.smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure]
  simp [ENNReal.toReal_ofReal hδ0, ENNReal.toReal_ofReal hδ1, smul_eq_mul]

/-- For a [positive sample size](hyp:hN), [interpolation index](hyp:hk), and
 [unit interpolation fraction](hyp:hδ),
 [the adjacent order-statistic mixture has mean `(k+δ)/N`](goal). -/
theorem adjacentOrderMix_mean {N k : ℕ} (hN : 0 < N) (hk : k < N)
    {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    ∫ u, u ∂adjacentOrderMix N k δ = (k + δ) / N := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
  haveI : IsProbabilityMeasure (iidSample uniform01 (N - 1)) := by
    dsimp [iidSample]
    infer_instance
  have hlo := (integrable_endpoint_moments
    (orderEndpoint_aemeasurable (N - 1) k)
    (orderEndpoint_mem_Icc (N - 1) k)).1
  have hhi := (integrable_endpoint_moments
    (orderEndpoint_aemeasurable (N - 1) (k + 1))
    (orderEndpoint_mem_Icc (N - 1) (k + 1))).1
  rw [adjacentOrderMix_integral hN hk hδ (fun u : ℝ => u) hlo hhi,
    orderEndpoint_mean (N - 1) k (by omega),
    orderEndpoint_mean (N - 1) (k + 1) (by omega)]
  have hcast : ((N - 1 : ℕ) : ℝ) + 1 = N := by
    exact_mod_cast (show N - 1 + 1 = N by omega)
  rw [hcast]
  have hne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
  push_cast
  ring

private theorem adjacentOrderMix_second_moment {N k : ℕ} (hN : 0 < N) (hk : k < N)
    {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    (∫ u, u ^ 2 ∂adjacentOrderMix N k δ) =
      (1 - δ) * ((k : ℝ) * (k + 1) / (N * (N + 1))) +
      δ * (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) / (N * (N + 1))) := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
  haveI : IsProbabilityMeasure (iidSample uniform01 (N - 1)) := by
    dsimp [iidSample]
    infer_instance
  have hlo := (integrable_endpoint_moments
    (orderEndpoint_aemeasurable (N - 1) k)
    (orderEndpoint_mem_Icc (N - 1) k)).2
  have hhi := (integrable_endpoint_moments
    (orderEndpoint_aemeasurable (N - 1) (k + 1))
    (orderEndpoint_mem_Icc (N - 1) (k + 1))).2
  rw [adjacentOrderMix_integral hN hk hδ (fun u : ℝ => u ^ 2) hlo hhi,
    orderEndpoint_second_moment (N - 1) k (by omega),
    orderEndpoint_second_moment (N - 1) (k + 1) (by omega)]
  have hcast : ((N - 1 : ℕ) : ℝ) + 1 = N := by
    exact_mod_cast (show N - 1 + 1 = N by omega)
  have hcast2 : ((N - 1 : ℕ) : ℝ) + 2 = (N : ℝ) + 1 := by
    exact_mod_cast (show N - 1 + 2 = N + 1 by omega)
  rw [hcast, hcast2]

/-- For a [positive sample size](hyp:hN), [interpolation index](hyp:hk), and
 [unit interpolation fraction](hyp:hδ),
 [the adjacent order-statistic mixture has the stated centered second moment](goal). -/
theorem adjacentOrderMix_variance {N k : ℕ} (hN : 0 < N) (hk : k < N)
    {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    (∫ u, (u - ((k + δ) / N)) ^ 2 ∂adjacentOrderMix N k δ) =
      ((k + δ) / N) * (1 - (k + δ) / N) / (N + 1) +
        δ * (1 - δ) / (N * (N + 1)) := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
  haveI : IsProbabilityMeasure (iidSample uniform01 (N - 1)) := by
    dsimp [iidSample]
    infer_instance
  let μ := adjacentOrderMix N k δ
  let m : ℝ := (k + δ) / N
  have hmass : (∫ _u : ℝ, (1 : ℝ) ∂μ) = 1 := by
    have hmap (r : ℕ) :
        (∫ _u : ℝ, (1 : ℝ) ∂(iidSample uniform01 (N - 1)).map
          (orderEndpoint (N - 1) r)) = 1 := by
      rw [integral_map (orderEndpoint_aemeasurable (N - 1) r)
        measurable_const.aestronglyMeasurable]
      simp
    change (∫ _u : ℝ, (1 : ℝ) ∂adjacentOrderMix N k δ) = 1
    rw [adjacentOrderMix_integral hN hk hδ (fun _ : ℝ => (1 : ℝ))
      (integrable_const _) (integrable_const _), hmap k, hmap (k + 1)]
    ring
  have hμfinite : IsFiniteMeasure μ := by
    have hm : (μ Set.univ).toReal = 1 := by
      simpa [integral_const, Measure.real] using hmass
    have hne : μ Set.univ ≠ ⊤ := (ENNReal.toReal_ne_zero.mp (by rw [hm]; norm_num)).2
    exact ⟨lt_top_iff_ne_top.mpr hne⟩
  have hlo1 := (integrable_endpoint_moments
    (orderEndpoint_aemeasurable (N - 1) k)
    (orderEndpoint_mem_Icc (N - 1) k)).1
  have hhi1 := (integrable_endpoint_moments
    (orderEndpoint_aemeasurable (N - 1) (k + 1))
    (orderEndpoint_mem_Icc (N - 1) (k + 1))).1
  have hlo2 := (integrable_endpoint_moments
    (orderEndpoint_aemeasurable (N - 1) k)
    (orderEndpoint_mem_Icc (N - 1) k)).2
  have hhi2 := (integrable_endpoint_moments
    (orderEndpoint_aemeasurable (N - 1) (k + 1))
    (orderEndpoint_mem_Icc (N - 1) (k + 1))).2
  have hI1 : Integrable (fun u : ℝ => u) μ := by
    change Integrable (fun u : ℝ => u) (adjacentOrderMix N k δ)
    rw [adjacentOrderMix_eq_endpoints hN hk]
    exact (hlo1.smul_measure (by simp)).add_measure (hhi1.smul_measure (by simp))
  have hI2 : Integrable (fun u : ℝ => u ^ 2) μ := by
    change Integrable (fun u : ℝ => u ^ 2) (adjacentOrderMix N k δ)
    rw [adjacentOrderMix_eq_endpoints hN hk]
    exact (hlo2.smul_measure (by simp)).add_measure (hhi2.smul_measure (by simp))
  have hcenter :
      (∫ u, (u - m) ^ 2 ∂μ) =
        (∫ u, u ^ 2 ∂μ) - 2 * m * (∫ u, u ∂μ) + m ^ 2 := by
    calc
      (∫ u, (u - m) ^ 2 ∂μ) =
          ∫ u, (u ^ 2 - (2 * m) * u + m ^ 2) ∂μ := by
            congr 1
            funext u
            ring
      _ = (∫ u, u ^ 2 ∂μ) - 2 * m * (∫ u, u ∂μ) + m ^ 2 := by
        have hmul : Integrable (fun u : ℝ => (2 * m) * u) μ := hI1.const_mul _
        have hsub : Integrable (fun u : ℝ => u ^ 2 - (2 * m) * u) μ := hI2.sub hmul
        rw [integral_add hsub (integrable_const (m ^ 2)),
          integral_sub hI2 hmul, integral_const_mul]
        have hmreal : μ.real Set.univ = 1 := by simpa [integral_const] using hmass
        simp [integral_const, hmreal]
  rw [hcenter, adjacentOrderMix_mean hN hk hδ,
    adjacentOrderMix_second_moment hN hk hδ]
  dsimp [m]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hNr1 : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- For a probability law supported on the unit interval and a threshold in
that interval, the integrated absolute difference between its CDF and the
threshold step equals its mean absolute displacement from that threshold. -/
theorem integral_abs_cdf_sub_step_eq_mean_abs (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (hsupp : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ u in Set.Icc (0 : ℝ) 1,
      |(ν (Set.Iic u)).toReal - (if t ≤ u then (1 : ℝ) else 0)| ∂volume) =
      ∫ x, |x - t| ∂ν := by
  have hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0 := (ae_iff).mp hsupp
  have hδ : (Measure.dirac t) (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    simp [ht]
  have hq : ∀ᵐ u ∂Causalean.Stat.unifOI,
      Causalean.Stat.quantile (Measure.dirac t) u = t := by
    filter_upwards [Causalean.Stat.Quantile.Transport.quantile_mem_Icc_ae
      (Measure.dirac t) (by simp : (Measure.dirac t) (Set.Icc t t)ᶜ = 0)]
      with u hu
    exact (Set.mem_Icc.mp hu).2.antisymm (Set.mem_Icc.mp hu).1
  have hcost :
      (∫ u in (0 : ℝ)..1,
        |Causalean.Stat.quantile ν u -
          Causalean.Stat.quantile (Measure.dirac t) u|) =
      ∫ x, |x - t| ∂ν := by
    have hrest : volume.restrict (Set.Ioc (0 : ℝ) 1) = Causalean.Stat.unifOI := by
      rw [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Ioc]
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hrest]
    have hcongr :
        (∫ u, |Causalean.Stat.quantile ν u -
          Causalean.Stat.quantile (Measure.dirac t) u| ∂Causalean.Stat.unifOI) =
        ∫ u, |Causalean.Stat.quantile ν u - t| ∂Causalean.Stat.unifOI := by
      apply integral_congr_ae
      filter_upwards [hq] with u hu
      rw [hu]
    calc
      _ = ∫ u, |Causalean.Stat.quantile ν u - t| ∂Causalean.Stat.unifOI := hcongr
      _ = ∫ x, |x - t| ∂(Causalean.Stat.unifOI.map (Causalean.Stat.quantile ν)) := by
        exact (integral_map (Causalean.Stat.aemeasurable_quantile_unifOI ν)
          (show AEStronglyMeasurable (fun x : ℝ => |x - t|)
            (Causalean.Stat.unifOI.map (Causalean.Stat.quantile ν)) from by fun_prop)).symm
      _ = ∫ x, |x - t| ∂ν := by rw [Causalean.Stat.quantile_map_uniform]
  have htransport := Causalean.Stat.Quantile.Transport.quantile_transport_eq_cdf_distance
    ν (Measure.dirac t) (by norm_num : (0 : ℝ) ≤ 1) hν hδ
  rw [hcost] at htransport
  rw [htransport]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  congr 1
  funext u
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
  by_cases h : t ≤ u <;> simp [Measure.real, Set.mem_Iic, h]

/-- The mean absolute displacement of an adjacent order-statistic mixture from
its interpolation threshold is bounded by its root mean-square displacement. -/
theorem adjacentOrderMix_abs_deviation_le_sqrt {N k : ℕ}
    (hN : 0 < N) (hk : k < N)
    {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, |x - ((k + δ) / N)| ∂adjacentOrderMix N k δ) ≤
      Real.sqrt (((k + δ) / N) * (1 - (k + δ) / N) / (N + 1) +
        δ * (1 - δ) / (N * (N + 1))) := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
  haveI : IsProbabilityMeasure (iidSample uniform01 (N - 1)) := by
    dsimp [iidSample]
    infer_instance
  let μ := adjacentOrderMix N k δ
  let m : ℝ := (k + δ) / N
  have hmass : (∫ _u : ℝ, (1 : ℝ) ∂μ) = 1 := by
    have hmap (r : ℕ) :
        (∫ _u : ℝ, (1 : ℝ) ∂(iidSample uniform01 (N - 1)).map
          (orderEndpoint (N - 1) r)) = 1 := by
      rw [integral_map (orderEndpoint_aemeasurable (N - 1) r)
        measurable_const.aestronglyMeasurable]
      simp
    change (∫ _u : ℝ, (1 : ℝ) ∂adjacentOrderMix N k δ) = 1
    rw [adjacentOrderMix_integral hN hk hδ (fun _ : ℝ => (1 : ℝ))
      (integrable_const _) (integrable_const _), hmap k, hmap (k + 1)]
    ring
  haveI : IsProbabilityMeasure μ := by
    have hreal : (μ Set.univ).toReal = 1 := by
      simpa [integral_const, Measure.real] using hmass
    exact isProbabilityMeasure_iff_real.mpr hreal
  have hlo1 := (integrable_endpoint_moments
    (orderEndpoint_aemeasurable (N - 1) k)
    (orderEndpoint_mem_Icc (N - 1) k)).1
  have hhi1 := (integrable_endpoint_moments
    (orderEndpoint_aemeasurable (N - 1) (k + 1))
    (orderEndpoint_mem_Icc (N - 1) (k + 1))).1
  have hlo2 := (integrable_endpoint_moments
    (orderEndpoint_aemeasurable (N - 1) k)
    (orderEndpoint_mem_Icc (N - 1) k)).2
  have hhi2 := (integrable_endpoint_moments
    (orderEndpoint_aemeasurable (N - 1) (k + 1))
    (orderEndpoint_mem_Icc (N - 1) (k + 1))).2
  have hI1 : Integrable (fun u : ℝ => u) μ := by
    change Integrable (fun u : ℝ => u) (adjacentOrderMix N k δ)
    rw [adjacentOrderMix_eq_endpoints hN hk]
    exact (hlo1.smul_measure (by simp)).add_measure (hhi1.smul_measure (by simp))
  have hI2 : Integrable (fun u : ℝ => u ^ 2) μ := by
    change Integrable (fun u : ℝ => u ^ 2) (adjacentOrderMix N k δ)
    rw [adjacentOrderMix_eq_endpoints hN hk]
    exact (hlo2.smul_measure (by simp)).add_measure (hhi2.smul_measure (by simp))
  have hsq : Integrable (fun u : ℝ => (u - m) ^ 2) μ := by
    have h := (hI2.sub (hI1.const_mul (2 * m))).add (integrable_const (m ^ 2))
    have hfun : (fun u : ℝ => (u - m) ^ 2) =
        (fun u : ℝ => u ^ 2 - (2 * m) * u + m ^ 2) := by
      funext u
      ring
    rw [hfun]
    exact h
  have hmeas : AEStronglyMeasurable (fun u : ℝ => u - m) μ := by fun_prop
  have hL2 : MemLp (fun u : ℝ => u - m) 2 μ :=
    (memLp_two_iff_integrable_sq hmeas).2 hsq
  have hbound := Causalean.Mathlib.Probability.ConvergingTogether.integral_abs_le_sqrt_integral_sq
    μ (fun u : ℝ => u - m) hL2
  have hsquared : (∫ u, |u - m| ^ 2 ∂μ) =
      m * (1 - m) / (N + 1) + δ * (1 - δ) / (N * (N + 1)) := by
    simpa only [sq_abs, m, μ] using adjacentOrderMix_variance hN hk hδ
  simp only [Real.norm_eq_abs, hsquared, m, μ] at hbound
  exact hbound

/-- A [positive sample size](hyp:hN), [valid adjacent index](hyp:hk), and
[unit-interval interpolation fraction](hyp:hδ) give [an integrated indicator
error bounded by the mixture's root mean-square displacement](goal). -/
theorem adjacentOrderMix_indicator_L1 {N k : ℕ} (hN : 0 < N) (hk : k < N)
    {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    (∫ u in Set.Icc (0 : ℝ) 1,
      |((adjacentOrderMix N k δ) (Set.Iic u)).toReal -
        (if (k + δ) / N ≤ u then (1 : ℝ) else 0)| ∂volume) ≤
      Real.sqrt (((k + δ) / N) * (1 - (k + δ) / N) / (N + 1) +
        δ * (1 - δ) / (N * (N + 1))) := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩
  haveI : IsProbabilityMeasure (iidSample uniform01 (N - 1)) := by
    dsimp [iidSample]
    infer_instance
  let μ := adjacentOrderMix N k δ
  have hmass : (∫ _u : ℝ, (1 : ℝ) ∂μ) = 1 := by
    have hmap (r : ℕ) :
        (∫ _u : ℝ, (1 : ℝ) ∂(iidSample uniform01 (N - 1)).map
          (orderEndpoint (N - 1) r)) = 1 := by
      rw [integral_map (orderEndpoint_aemeasurable (N - 1) r)
        measurable_const.aestronglyMeasurable]
      simp
    change (∫ _u : ℝ, (1 : ℝ) ∂adjacentOrderMix N k δ) = 1
    rw [adjacentOrderMix_integral hN hk hδ (fun _ : ℝ => (1 : ℝ))
      (integrable_const _) (integrable_const _), hmap k, hmap (k + 1)]
    ring
  haveI : IsProbabilityMeasure μ := by
    have hreal : (μ Set.univ).toReal = 1 := by
      simpa [integral_const, Measure.real] using hmass
    exact isProbabilityMeasure_iff_real.mpr hreal
  have hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1 := by
    change ∀ᵐ x ∂adjacentOrderMix N k δ, x ∈ Set.Icc (0 : ℝ) 1
    rw [adjacentOrderMix_eq_endpoints hN hk, ae_add_measure_iff]
    constructor
    · exact Measure.ae_smul_measure
        ((ae_map_iff (orderEndpoint_aemeasurable (N - 1) k)
          measurableSet_Icc).2 (orderEndpoint_mem_Icc (N - 1) k)) _
    · exact Measure.ae_smul_measure
        ((ae_map_iff (orderEndpoint_aemeasurable (N - 1) (k + 1))
          measurableSet_Icc).2 (orderEndpoint_mem_Icc (N - 1) (k + 1))) _
  have ht : (k + δ) / N ∈ Set.Icc (0 : ℝ) 1 := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hkr : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    constructor
    · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) hδ.1) (le_of_lt hNr)
    · apply (div_le_iff₀ hNr).2
      linarith [hδ.2]
  calc
    (∫ u in Set.Icc (0 : ℝ) 1,
      |((adjacentOrderMix N k δ) (Set.Iic u)).toReal -
        (if (k + δ) / N ≤ u then (1 : ℝ) else 0)| ∂volume) =
        ∫ x, |x - ((k + δ) / N)| ∂μ := by
          exact integral_abs_cdf_sub_step_eq_mean_abs μ hsupp ht
    _ ≤ _ := adjacentOrderMix_abs_deviation_le_sqrt hN hk hδ

/-- For a [positive sample size](hyp:hN), [adjacent index](hyp:hk), and
 [interpolation fraction](hyp:hδ) in the unit interval, [the threshold-indicator
 error is at most the square root of twice the threshold divided by `N`](goal).
 This coarse bound isolates the algebra needed to integrate the coupling error
 against the power curvature, including the deterministic endpoint cases. -/
theorem adjacentOrderMix_indicator_L1_le_sqrt_two_t_over_N {N k : ℕ}
    (hN : 0 < N) (hk : k < N) {δ : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    (∫ u in Set.Icc (0 : ℝ) 1,
      |((adjacentOrderMix N k δ) (Set.Iic u)).toReal -
        (if (k + δ) / N ≤ u then (1 : ℝ) else 0)| ∂volume) ≤
      Real.sqrt (2 * ((k + δ) / N) / N) := by
  -- Use `adjacentOrderMix_indicator_L1`, then bound its exact variance by
  -- `2 * t / N`: the first term is at most `t / N`, and the interpolation
  -- term is at most `t / N` because `δ ≤ k + δ`.
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNr1 : (0 : ℝ) < N + 1 := by positivity
  have ht0 : 0 ≤ (k + δ) / (N : ℝ) := by
    apply div_nonneg _ (le_of_lt hNr)
    exact add_nonneg (Nat.cast_nonneg _) hδ.1
  have ht1 : (k + δ) / (N : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hNr).2
    have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    linarith [hδ.2]
  have hδk : δ ≤ (k : ℝ) + δ := by
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hfirst :
      ((k + δ) / N) * (1 - (k + δ) / N) / (N + 1) ≤
        ((k + δ) / N) / N := by
    calc
      _ ≤ ((k + δ) / N) / (N + 1) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hNr1)
        nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
      _ ≤ ((k + δ) / N) / N := by
        apply div_le_div_of_nonneg_left ht0 hNr
        linarith
  have hsecond : δ * (1 - δ) / (N * (N + 1)) ≤ ((k + δ) / N) / N := by
    calc
      _ ≤ δ / (N * (N + 1)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg δ]
      _ ≤ (k + δ) / (N * (N + 1)) := by
        apply div_le_div_of_nonneg_right hδk (by positivity)
      _ ≤ (k + δ) / (N * N) := by
        apply div_le_div_of_nonneg_left
          (add_nonneg (Nat.cast_nonneg _) hδ.1) (by positivity)
        nlinarith [sq_nonneg (N : ℝ)]
      _ = ((k + δ) / N) / N := by ring
  calc
    _ ≤ Real.sqrt (((k + δ) / N) * (1 - (k + δ) / N) / (N + 1) +
        δ * (1 - δ) / (N * (N + 1))) :=
      adjacentOrderMix_indicator_L1 hN hk hδ
    _ ≤ _ := by
      apply Real.sqrt_le_sqrt
      have htwo : ((k + δ) / (N : ℝ)) / N + ((k + δ) / N) / N =
          2 * ((k + δ) / N) / N := by ring
      rw [← htwo]
      exact add_le_add hfirst hsecond

/-- For a [real power](hyp:hs) at least one,
 [the power density integrates to one over the unit interval](goal). -/
theorem integral_powerDensity {s : ℝ} (hs : 1 ≤ s) :
    (∫ u in Set.Icc (0 : ℝ) 1, powerDensity s u ∂volume) = 1 := by
  have h := powerCell_eq_integral (N := 1) (by omega) hs (0 : Fin 1)
  have hcell : powerCell 1 s (0 : Fin 1) = 1 := by
    simp [powerCell, Real.zero_rpow (by linarith : s ≠ 0)]
  rw [hcell] at h
  simpa [powerDensity, intervalIntegral.integral_of_le,
    ← integral_Icc_eq_integral_Ioc] using h.symm

end
end Causalean.Stat.OrderStatistic.WeightedConcomitant

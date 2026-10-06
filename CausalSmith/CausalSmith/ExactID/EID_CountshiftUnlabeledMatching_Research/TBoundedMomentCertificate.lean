module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.TDeterministicCertificate
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.OffsetVariance
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.MedianOfMeans
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.LogClip

/-! Finite-sample robust shift estimation and correct-or-abstain labels. -/

public section

open MeasureTheory ProbabilityTheory

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- Both observable factorial statistics have the square-integrability needed
for the median-of-means deviation theorem. -/
-- @node: balanced_factorial_memLp
lemma balanced_factorial_memLp {p n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ℓ v : ℝ} (𝒬 : BoundedMomentClass p n ℓ v Ω μ)
    (m : Fin (p + 1)) (r : Fin n) (j : Fin p) :
    MemLp (fun ω => firstFactorial (𝒬.X m r ω) (𝒬.S m r ω) j) 2 μ ∧
    MemLp (fun ω => secondFactorial (𝒬.X m r ω) (𝒬.S m r ω) j) 2 μ := by
  have hp : PoissonMeasurement μ
      (fun _ : Unit => fun _ : Unit => 𝒬.Z m r)
      (fun _ _ => 𝒬.S m r) (fun _ _ => 𝒬.X m r) := by
    intro _ _
    exact 𝒬.poisson m r
  obtain ⟨h1, _, h2, _, _, _, _⟩ := 𝒬.varBound.1 m r j
  obtain ⟨hU2, hW2⟩ := offset_exogeneity_raw_moments_integrable
    μ 𝒬.Z 𝒬.S 𝒬.exog v 𝒬.varBound m r j
  have hraw := poisson_mixture_adjusted_factorial_raw_moments μ
    (𝒬.S m r) (𝒬.Z m r) (𝒬.X m r) hp j h1 h2 hU2 hW2
  exact ⟨hraw.2.2.2.2.1, hraw.2.2.2.2.2⟩

/-- The two raw median-of-means estimates obey the same one-cell deviation
bound, before taking the finite union over environments and coordinates. -/
-- @node: balanced_factorial_mom_deviation
lemma balanced_factorial_mom_deviation {p n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ℓ v : ℝ} (𝒬 : BoundedMomentClass p n ℓ v Ω μ)
    (r₀ : Fin n) (e : Fin (p + 1)) (j : Fin p)
    (η : ℝ) (hη : 0 < η ∧ η < 1) (hn : 8 * momBlocks η ≤ n) :
    let τ := 8 * Real.sqrt v * Real.sqrt (Real.log (2 / η) / n)
    (μ {ω | |medianOfMeans (momBlocks η)
      (fun r => firstFactorial (𝒬.X e r ω) (𝒬.S e r ω) j) -
      ∫ ω, firstFactorial (𝒬.X e r₀ ω) (𝒬.S e r₀ ω) j ∂μ| ≤ τ} ≥
        ENNReal.ofReal (1 - η)) ∧
    (μ {ω | |medianOfMeans (momBlocks η)
      (fun r => secondFactorial (𝒬.X e r ω) (𝒬.S e r ω) j) -
      ∫ ω, secondFactorial (𝒬.X e r₀ ω) (𝒬.S e r₀ ω) j ∂μ| ≤ τ} ≥
        ENNReal.ofReal (1 - η)) := by
  have hvar := random_offset_variance μ 𝒬.Z 𝒬.S 𝒬.X v
    𝒬.poisson 𝒬.iid 𝒬.exog 𝒬.varBound
  let Y : Fin n → Ω → ℝ × ℝ := fun r ω =>
    (firstFactorial (𝒬.X e r ω) (𝒬.S e r ω) j,
     secondFactorial (𝒬.X e r ω) (𝒬.S e r ω) j)
  have hIndFirst : iIndepFun (fun r ω => (Y r ω).1) μ :=
    (hvar.1 e j).comp (fun _ x => x.1) (fun _ => measurable_fst)
  have hIndSecond : iIndepFun (fun r ω => (Y r ω).2) μ :=
    (hvar.1 e j).comp (fun _ x => x.2) (fun _ => measurable_snd)
  have hMeanFirst (r s : Fin n) :
      (∫ ω, (Y r ω).1 ∂μ) = ∫ ω, (Y s ω).1 ∂μ := by
    simpa only [Function.comp_def, Y] using
      ((hvar.2.1 e j r s).comp measurable_fst).integral_eq
  have hMeanSecond (r s : Fin n) :
      (∫ ω, (Y r ω).2 ∂μ) = ∫ ω, (Y s ω).2 ∂μ := by
    simpa only [Function.comp_def, Y] using
      ((hvar.2.1 e j r s).comp measurable_snd).integral_eq
  have hLpFirst (r : Fin n) : MemLp (fun ω => (Y r ω).1) 2 μ := by
    simpa only [Y] using (balanced_factorial_memLp μ 𝒬 e r j).1
  have hLpSecond (r : Fin n) : MemLp (fun ω => (Y r ω).2) 2 μ := by
    simpa only [Y] using (balanced_factorial_memLp μ 𝒬 e r j).2
  have hvFirst (r : Fin n) :
      variance (fun ω => (Y r ω).1) μ ≤ (Real.sqrt v) ^ 2 := by
    rw [Real.sq_sqrt (le_of_lt 𝒬.v_pos)]
    simpa only [Y] using (hvar.2.2.2.2 e r j).1
  have hvSecond (r : Fin n) :
      variance (fun ω => (Y r ω).2) μ ≤ (Real.sqrt v) ^ 2 := by
    rw [Real.sq_sqrt (le_of_lt 𝒬.v_pos)]
    simpa only [Y] using (hvar.2.2.2.2 e r j).2
  constructor
  · simpa only [Y] using medianOfMeans_deviation μ
      (fun r ω => (Y r ω).1) r₀ η (Real.sqrt v)
      hη (Real.sqrt_nonneg _) hIndFirst hLpFirst hMeanFirst hvFirst hn
  · simpa only [Y] using medianOfMeans_deviation μ
      (fun r ω => (Y r ω).2) r₀ η (Real.sqrt v)
      hη (Real.sqrt_nonneg _) hIndSecond hLpSecond hMeanSecond hvSecond hn

/-- A sample-size bound linear in the log factor supplies enough observations
for every median-of-means block. -/
-- @node: momBlocks_le_of_sample_log_bound
lemma momBlocks_le_of_sample_log_bound {n : ℕ} {η L : ℝ}
    (hη : 0 < η ∧ η < 1) (hL : 1 ≤ L)
    (hlog : Real.log (2 / η) = L) (hn : 100 * L ≤ (n : ℝ)) :
    8 * momBlocks η ≤ n := by
  have hk := momBlocks_real_upper hη
  rw [hlog] at hk
  have hcast : (8 : ℝ) * (momBlocks η : ℝ) ≤ (n : ℝ) := by
    linarith
  exact_mod_cast hcast

/-- The second adjusted factorial moment inherits the square of the first-moment floor. -/
-- @node: balanced_second_factorial_floor
lemma balanced_second_factorial_floor {p n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ℓ v : ℝ} (𝒬 : BoundedMomentClass p n ℓ v Ω μ)
    (m : Fin (p + 1)) (r : Fin n) (j : Fin p) :
    ℓ ^ 2 ≤ ∫ ω, secondFactorial (𝒬.X m r ω) (𝒬.S m r ω) j ∂μ := by
  let E : Ω → ℝ := fun ω => Real.exp (𝒬.Z m r ω j)
  obtain ⟨hEint, hELp, hE2int, _, _, _, _⟩ := 𝒬.varBound.1 m r j
  have hp : PoissonMeasurement μ
      (fun _ : Unit => fun _ : Unit => 𝒬.Z m r)
      (fun _ _ => 𝒬.S m r) (fun _ _ => 𝒬.X m r) := by
    intro _ _
    exact 𝒬.poisson m r
  have hdiag : Integrable (fun ω => Real.exp (𝒬.Z m r ω j + 𝒬.Z m r ω j)) μ := by
    convert hE2int using 1
    funext ω
    congr 1
    ring
  obtain ⟨hfirst, hsecond⟩ := poisson_mixture_factorial_moment_transfer μ
    (𝒬.S m r) (𝒬.Z m r) (𝒬.X m r) hp j j hEint hdiag
  have hsq : (∫ ω, E ω ^ 2 ∂μ) =
      ∫ ω, Real.exp (𝒬.Z m r ω j + 𝒬.Z m r ω j) ∂μ := by
    congr 1
    funext ω
    dsimp [E]
    rw [pow_two, Real.exp_add]
  have hvar : (∫ ω, E ω ∂μ) ^ 2 ≤ ∫ ω, E ω ^ 2 ∂μ := by
    have hv := variance_nonneg E μ
    rw [variance_eq_sub hELp] at hv
    simpa only [Pi.pow_apply] using (sub_nonneg.mp hv)
  have hfloor : ℓ ≤ ∫ ω, E ω ∂μ := by
    simpa only [E, ← hfirst] using 𝒬.firstMoment m r j
  calc
    ℓ ^ 2 ≤ (∫ ω, E ω ∂μ) ^ 2 := pow_le_pow_left₀ (le_of_lt 𝒬.ell_pos) hfloor _
    _ ≤ ∫ ω, E ω ^ 2 ∂μ := hvar
    _ = ∫ ω, secondFactorial (𝒬.X m r ω) (𝒬.S m r ω) j ∂μ := by
      rw [hsq]
      simpa only [crossFactorial, ite_true] using hsecond.symm

/-- Matching observed count-offset laws identify the log-factorial shifts. -/
-- @node: balancedObsShift_eq_obsShift_of_law
lemma balancedObsShift_eq_obsShift_of_law {p n : ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (μ' : Measure Ω')
    (𝒬 : BoundedMomentClass p n ℓ v Ω μ)
    (𝔐 : AtomicCountModel p p Ω' μ') (r₀ : Fin n)
    (hLaw : ∀ e r,
      μ.map (fun ω => (𝒬.S e r ω, 𝒬.X e r ω)) = obsLaw μ' 𝔐 e) :
    ∀ m i, balancedObsShift μ 𝒬 r₀ m i = obsShift μ' 𝔐 m i := by
  have hmean : ∀ e i, balancedObsMean μ 𝒬 r₀ e i = obsMean μ' 𝔐 e i := by
    intro e i
    have hpair : IdentDistrib
        (fun ω => (𝒬.S e r₀ ω, 𝒬.X e r₀ ω))
        (fun ω => (𝔐.S e ω, 𝔐.X e ω)) μ μ' :=
      ⟨𝒬.poisson.obs_aemeasurable μ e r₀,
        𝔐.poisson.obs_aemeasurable μ' e (), hLaw e r₀⟩
    have hfirst := (hpair.comp (by
      dsimp [firstFactorial]
      fun_prop : Measurable (fun sx : (Fin p → ℝ) × (Fin p → ℕ) =>
        firstFactorial sx.2 sx.1 i))).integral_eq
    have hsecond := (hpair.comp (by
      dsimp [secondFactorial]
      fun_prop : Measurable (fun sx : (Fin p → ℝ) × (Fin p → ℕ) =>
        secondFactorial sx.2 sx.1 i))).integral_eq
    simpa only [balancedObsMean, obsMean, Function.comp_def] using
      congrArg₂ (fun x y : ℝ => 2 * Real.log x - (1 / 2 : ℝ) * Real.log y)
        hfirst hsecond
  intro m i
  simpa only [balancedObsShift, obsShift] using
    congrArg₂ (fun x y : ℝ => x - y) (hmean m.succ i) (hmean 0 i)

/-- The per-statistic failure probability matches the logarithm in the
simultaneous deviation radius. -/
-- @node: balanced_moment_failure_log
lemma balanced_moment_failure_log (p : ℕ) (δ : ℝ)
    (hp : 0 < p) (hδpos : 0 < δ) (hδlt : δ < 1 / 2) :
    let η := δ / (2 * (p : ℝ) * (p + 1))
    0 < η ∧ η < 1 ∧
      Real.log (2 / η) = Real.log (4 * (p : ℝ) * (p + 1) / δ) := by
  dsimp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : 0 < (2 : ℝ) * p * (p + 1) := by positivity
  have hηpos : 0 < δ / (2 * (p : ℝ) * (p + 1)) := div_pos hδpos hden
  have hηlt : δ / (2 * (p : ℝ) * (p + 1)) < 1 := by
    rw [div_lt_iff₀ hden]
    nlinarith [sq_nonneg ((p : ℝ) - 1)]
  refine ⟨hηpos, hηlt, ?_⟩
  congr 1
  field_simp
  ring

/-- The simultaneous failure-level logarithm exceeds one, uniformly in the
number of intervention environments. -/
-- @node: balanced_moment_log_one_le
lemma balanced_moment_log_one_le (p : ℕ) (δ : ℝ)
    (hp : 0 < p) (hδpos : 0 < δ) (hδlt : δ < 1 / 2) :
    1 ≤ Real.log (4 * (p : ℝ) * (p + 1) / δ) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have harg : (3 : ℝ) ≤ 4 * (p : ℝ) * (p + 1) / δ := by
    apply (le_div_iff₀ hδpos).2
    nlinarith [sq_nonneg ((p : ℝ) - 1)]
  have hlog : Real.log 3 ≤ Real.log (4 * (p : ℝ) * (p + 1) / δ) :=
    Real.log_le_log (by norm_num) harg
  have hthree : 1 ≤ Real.log (3 : ℝ) := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_le_log (Real.exp_pos _) Real.exp_one_lt_three.le
  exact hthree.trans hlog

/-- A measurable full-probability core of the median-of-means deviation event.
This packages the measurable modifications supplied by `MemLp`, so later
finite union bounds do not require pointwise measurability of the observations. -/
lemma medianOfMeans_measurable_core {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Fin n → Ω → ℝ) (r₀ : Fin n) (η σ : ℝ)
    (hη : 0 < η ∧ η < 1) (hσ : 0 < σ)
    (hiid : iIndepFun Y μ) (hLp : ∀ r, MemLp (Y r) 2 μ)
    (hmeans : ∀ r s, ∫ ω, Y r ω ∂μ = ∫ ω, Y s ω ∂μ)
    (hvar : ∀ r, variance (Y r) μ ≤ σ ^ 2)
    (hn : 8 * momBlocks η ≤ n) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ G ≥ ENNReal.ofReal (1 - η) ∧
      G ⊆ {ω | |medianOfMeans (momBlocks η) (fun r => Y r ω) -
        ∫ ω, Y r₀ ω ∂μ| ≤
          8 * σ * Real.sqrt (Real.log (2 / η) / n)} := by
  classical
  let Y' : Fin n → Ω → ℝ := fun r => (hLp r).1.mk (Y r)
  have hYY' : ∀ r, Y r =ᵐ[μ] Y' r := fun r => (hLp r).1.ae_eq_mk
  have hY'meas : ∀ r, Measurable (Y' r) := fun r => (hLp r).1.measurable_mk
  have hY'Lp : ∀ r, MemLp (Y' r) 2 μ := fun r =>
    (memLp_congr_ae (hYY' r)).mp (hLp r)
  have hY'ind : iIndepFun Y' μ := hiid.congr hYY'
  have hY'means : ∀ r s, ∫ ω, Y' r ω ∂μ = ∫ ω, Y' s ω ∂μ := by
    intro r s
    rw [integral_congr_ae (hYY' r).symm, integral_congr_ae (hYY' s).symm]
    exact hmeans r s
  have hY'var : ∀ r, variance (Y' r) μ ≤ σ ^ 2 := by
    intro r
    rw [variance_congr (hYY' r).symm]
    exact hvar r
  let k := momBlocks η
  let a := ∫ ω, Y' r₀ ω ∂μ
  let t := 8 * σ * Real.sqrt (Real.log (2 / η) / n)
  let Z : Fin k → Ω → ℝ := fun s ω => blockMean k (fun r => Y' r ω) s
  have hkpos : 0 < k := by
    have hkreal : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le
      (mul_pos (by norm_num : (0 : ℝ) < 8) (mom_log_pos hη))
      (by simpa [k] using momBlocks_real_lower hη)
    exact_mod_cast hkreal
  have hk : k ≤ n := le_trans (by omega : k ≤ 8 * k) (by simpa [k] using hn)
  have hZmeas : ∀ s, Measurable (Z s) := by
    intro s
    dsimp only [Z]
    simp_rw [blockMean_eq_sum_momBlock]
    exact (Finset.measurable_sum _ fun r _ => hY'meas r).div_const _
  have hZind : iIndepFun Z μ := by
    simpa only [Z, k] using iIndepFun_blockMean μ Y' hY'meas hY'ind
      (k := momBlocks η)
  have hprob : ∀ s, μ.real {ω | t < |Z s ω - a|} ≤ 1 / 4 := by
    intro s
    simpa only [t, Z, k, a] using blockMean_bad_real_le_quarter μ Y' hY'ind hY'Lp
      (∫ ω, Y' r₀ ω ∂μ) η σ hη hσ (fun r => hY'means r r₀) hY'var hn s
  let A : Set Ω := {ω | k / 2 <
    (Finset.univ.filter fun s : Fin k => t < |Z s ω - a|).card}
  have hAmeas : MeasurableSet A := by
    let N : Ω → ℕ := fun ω =>
      ∑ s : Fin k, if t < |Z s ω - a| then 1 else 0
    have hN : Measurable N := by
      dsimp only [N]
      apply Finset.measurable_sum
      intro s _
      exact Measurable.ite
        (measurableSet_lt measurable_const ((hZmeas s).sub_const _).abs)
        measurable_const measurable_const
    have hset : A = {ω | k / 2 < N ω} := by
      ext ω
      simp only [A, N, Set.mem_setOf_eq]
      have hsum := Finset.sum_boole (R := ℕ)
        (fun s : Fin k => t < |Z s ω - a|) Finset.univ
      exact (congrArg (fun z : ℕ => k / 2 < z) hsum.symm).to_iff
    rw [hset]
    exact measurableSet_lt measurable_const hN
  have hAreal : μ.real A ≤ η := by
    have hmajor := majority_bad_measureReal_le_exp μ Z hZmeas hZind a t hprob
    have hexp : Real.exp (-(k : ℝ) / 8) ≤ η := by
      have hklo : 8 * Real.log (2 / η) ≤ (k : ℝ) := by
        simpa only [k] using momBlocks_real_lower hη
      calc
        Real.exp (-(k : ℝ) / 8) ≤ Real.exp (-Real.log (2 / η)) := by
          rw [Real.exp_le_exp]
          linarith
        _ = η / 2 := by
          rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hη.1)]
          field_simp
        _ ≤ η := by linarith
    have hmajor' : μ.real A ≤ Real.exp (-(k : ℝ) / 8) := by
      simpa only [A] using hmajor
    exact hmajor'.trans hexp
  let H : Set Ω := {ω | ∀ r, Y r ω = Y' r ω}
  have hHall : ∀ᵐ ω ∂μ, ω ∈ H := by
    simpa only [H, Set.mem_setOf_eq] using (ae_all_iff.2 hYY')
  have hHnull : NullMeasurableSet H μ := by
    rw [nullMeasurableSet_iff_eventuallyMeasurableSet]
    exact eventuallyMeasurableSet_of_mem_filter hHall
  obtain ⟨Hm, hHmH, hHmmeas, hHmEq⟩ := hHnull.exists_measurable_subset_ae_eq
  let G := Aᶜ ∩ Hm
  refine ⟨G, hAmeas.compl.inter hHmmeas, ?_, ?_⟩
  · have hGae : G =ᵐ[μ] Aᶜ := by
      filter_upwards [hHmEq, hHall] with ω hEq hH
      change (ω ∈ G) = (ω ∈ Aᶜ)
      dsimp only [G]
      simp only [Set.mem_inter_iff]
      apply propext
      constructor
      · exact fun h => h.1
      · intro hA
        refine ⟨hA, ?_⟩
        exact hEq.mpr hH
    rw [measure_congr hGae]
    have hcomp := measureReal_add_measureReal_compl (μ := μ) hAmeas
    rw [probReal_univ] at hcomp
    have hreal : 1 - η ≤ μ.real Aᶜ := by linarith
    have hof : ENNReal.ofReal (1 - η) ≤ ENNReal.ofReal (μ.real Aᶜ) :=
      ENNReal.ofReal_le_ofReal hreal
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ Aᶜ)] at hof
    exact hof
  · intro ω hω
    have hnotA : ω ∉ A := hω.1
    have hsame : ∀ r, Y r ω = Y' r ω := hHmH hω.2
    have hbad : (Finset.univ.filter fun s : Fin k => t < |Z s ω - a|).card ≤ k / 2 := by
      simpa only [A, Set.mem_setOf_eq, not_lt] using hnotA
    let good := Finset.univ.filter fun s : Fin k => |Z s ω - a| ≤ t
    let bad := Finset.univ.filter fun s : Fin k => t < |Z s ω - a|
    have hdisj : Disjoint good bad := by
      rw [Finset.disjoint_left]
      intro s hsg hsb
      exact (not_lt_of_ge (Finset.mem_filter.mp hsg).2) (Finset.mem_filter.mp hsb).2
    have hunion : good ∪ bad = Finset.univ := by
      ext s
      simp only [good, bad, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun _ => trivial, fun _ => le_or_gt _ _⟩
    have hsum : good.card + bad.card = k := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
      simp
    have hkodd : k % 2 = 1 := by simp [k, momBlocks]
    have hgood : k / 2 < good.card := by
      have hbad' : bad.card ≤ k / 2 := by simpa only [bad, Z] using hbad
      omega
    have hm := medianOfMeans_mem_interval_of_majority hkpos (fun r => Y' r ω) a t
      (by positivity) (by simpa only [good, Z] using hgood)
    have hfun : (fun r => Y r ω) = (fun r => Y' r ω) := funext hsame
    have hcenter : ∫ x, Y r₀ x ∂μ = a := by
      dsimp only [a]
      exact integral_congr_ae (hYY' r₀)
    change |medianOfMeans (momBlocks η) (fun r => Y r ω) -
      ∫ x, Y r₀ x ∂μ| ≤ 8 * σ * Real.sqrt (Real.log (2 / η) / n)
    rw [hfun, hcenter]
    simpa only [k, t] using hm

/-- A finite family of measurable events admits simultaneous coverage when
the sum of its individual failure budgets is at most the desired error. -/
-- @node: balanced_simultaneous_coverage
lemma balanced_simultaneous_coverage {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : ι → Set Ω)
    (η δ : ℝ) (hG : ∀ i, MeasurableSet (G i))
    (hprob : ∀ i, μ (G i) ≥ ENNReal.ofReal (1 - η))
    (hsum : (Fintype.card ι : ℝ) * η ≤ δ) :
    μ (⋂ i, G i) ≥ ENNReal.ofReal (1 - δ) := by
  have hgood (i : ι) : 1 - η ≤ μ.real (G i) := by
    have hh := ENNReal.toReal_mono (measure_ne_top μ (G i)) (hprob i)
    by_cases h : 0 ≤ 1 - η
    · simpa only [ENNReal.toReal_ofReal h, measureReal_def] using hh
    · have := measureReal_nonneg (μ := μ) (s := G i)
      linarith
  have hbad (i : ι) : μ.real (G i)ᶜ ≤ η := by
    have hc := measureReal_add_measureReal_compl (μ := μ) (hG i)
    rw [probReal_univ] at hc
    linarith [hgood i]
  have hunion : μ.real (⋃ i, (G i)ᶜ) ≤ δ := by
    calc
      μ.real (⋃ i, (G i)ᶜ) ≤ ∑ i, μ.real (G i)ᶜ := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _ : ι, η := Finset.sum_le_sum (fun i _ => hbad i)
      _ = (Fintype.card ι : ℝ) * η := by simp [mul_comm]
      _ ≤ δ := hsum
  have hinter : μ.real (⋂ i, G i) ≥ 1 - δ := by
    have hc := measureReal_add_measureReal_compl (μ := μ)
      (show MeasurableSet (⋂ i, G i) from MeasurableSet.iInter hG)
    rw [probReal_univ] at hc
    have hcomp : (⋂ i, G i)ᶜ = ⋃ i, (G i)ᶜ := Set.compl_iInter G
    rw [hcomp] at hc
    linarith
  have hreal : ENNReal.ofReal (1 - δ) ≤ ENNReal.ofReal (μ.real (⋂ i, G i)) :=
    ENNReal.ofReal_le_ofReal hinter
  simpa [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)] using hreal

-- @node: thm:bounded-moment-certificate
theorem bounded_moment_certificate :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p n : ℕ) (ℓ v δ : ℝ), 0 < p → 0 < n →
      0 < ℓ → ℓ ≤ Real.exp (1 / 2) → 0 < v →
      (hδpos : 0 < δ) → (hδlt : δ < 1 / 2) →
      (n : ℝ) ≥ C * max 1 (v * ℓ⁻¹ ^ 4) *
        Real.log (4 * p * (p + 1) / δ) →
      ∀ (Ω : Type) (ms : MeasurableSpace Ω)
        (μ : Measure Ω),
        letI : MeasurableSpace Ω := ms
        ∀ (𝒬 : BoundedMomentClass p n ℓ v Ω μ) (r₀ : Fin n),
        μ Set.univ = 1 →
        μ {ω | ∀ m i,
          |robustShiftEstimator ℓ ⟨δ, hδpos, hδlt⟩
              (fun e r => 𝒬.S e r ω) (fun e r => 𝒬.X e r ω) m i -
            balancedObsShift μ 𝒬 r₀ m i| ≤ epsN C p n v ℓ δ} ≥
          ENNReal.ofReal (1 - δ) ∧
        ∃ hεn : 0 < epsN C p n v ℓ δ,
        ∀ (Ω' : Type) (ms' : MeasurableSpace Ω')
          (μ' : Measure Ω'),
          letI : MeasurableSpace Ω' := ms'
          ∀ 𝔐 : AtomicCountModel p p Ω' μ',
          ∀ ht : Function.Bijective 𝔐.t,
          (∀ e r,
            μ.map (fun ω => (𝒬.S e r ω, 𝒬.X e r ω)) =
              obsLaw μ' 𝔐 e) →
          μ {ω | oneSidedCertificate
              (robustShiftEstimator ℓ ⟨δ, hδpos, hδlt⟩
                (fun e r => 𝒬.S e r ω) (fun e r => 𝒬.X e r ω))
              ⟨epsN C p n v ℓ δ, hεn⟩ = some (Equiv.ofBijective 𝔐.t ht) ∨
              oneSidedCertificate
                (robustShiftEstimator ℓ ⟨δ, hδpos, hδlt⟩
                  (fun e r => 𝒬.S e r ω) (fun e r => 𝒬.X e r ω))
                ⟨epsN C p n v ℓ δ, hεn⟩ = none} ≥ ENNReal.ofReal (1 - δ) ∧
          (2 * epsN C p n v ℓ δ < minStrength μ' 𝔐 →
            μ {ω | oneSidedCertificate
              (robustShiftEstimator ℓ ⟨δ, hδpos, hδlt⟩
                (fun e r => 𝒬.S e r ω) (fun e r => 𝒬.X e r ω))
              ⟨epsN C p n v ℓ δ, hεn⟩ = some (Equiv.ofBijective 𝔐.t ht)} ≥
                ENNReal.ofReal (1 - δ)) := by
  refine ⟨100000, by norm_num, ?_⟩
  intro p n ℓ v δ hp hn hℓ hℓle hv hδpos hδlt hnlarge
  intro Ω ms μ
  letI : MeasurableSpace Ω := ms
  intro 𝒬 r₀ hμ
  let ε := epsN 100000 p n v ℓ δ
  let dhat : Ω → Fin p → Fin p → ℝ := fun ω =>
    robustShiftEstimator ℓ ⟨δ, hδpos, hδlt⟩
      (fun e r => 𝒬.S e r ω) (fun e r => 𝒬.X e r ω)
  let E : Set Ω := {ω | ∀ m i, |dhat ω m i - balancedObsShift μ 𝒬 r₀ m i| ≤ ε}
  have hε : 0 < ε := by
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have harg : 1 < 4 * (p : ℝ) * (p + 1) / δ := by
      apply (lt_div_iff₀ hδpos).2
      nlinarith [sq_nonneg ((p : ℝ) - 1)]
    dsimp [ε, epsN]
    have hlog : 0 < Real.log (4 * (p : ℝ) * (p + 1) / δ) := Real.log_pos harg
    positivity
  have hdev : μ E ≥ ENNReal.ofReal (1 - δ) := by
    letI : IsProbabilityMeasure μ := ⟨hμ⟩
    let u : Fin (p + 1) → Fin p → ℝ := fun e j =>
      ∫ ω, firstFactorial (𝒬.X e r₀ ω) (𝒬.S e r₀ ω) j ∂μ
    let w : Fin (p + 1) → Fin p → ℝ := fun e j =>
      ∫ ω, secondFactorial (𝒬.X e r₀ ω) (𝒬.S e r₀ ω) j ∂μ
    have hfloor : ∀ e j, ℓ ≤ u e j ∧ ℓ ^ 2 ≤ w e j := by
      intro e j
      exact ⟨𝒬.firstMoment e r₀ j,
        balanced_second_factorial_floor μ 𝒬 e r₀ j⟩
    let η : ℝ := δ / (2 * (p : ℝ) * (p + 1))
    let L : ℝ := Real.log (4 * (p : ℝ) * (p + 1) / δ)
    have hη : 0 < η ∧ η < 1 ∧ Real.log (2 / η) = L := by
      simpa only [η, L] using balanced_moment_failure_log p δ hp hδpos hδlt
    have hL : 1 ≤ L := by
      simpa only [L] using balanced_moment_log_one_le p δ hp hδpos hδlt
    have hsample : 100 * L ≤ (n : ℝ) := by
      calc
        100 * L ≤ 100000 * max 1 (v * ℓ⁻¹ ^ 4) * L := by
          have hm : (1 : ℝ) ≤ max 1 (v * ℓ⁻¹ ^ 4) := le_max_left _ _
          nlinarith [mul_nonneg (sub_nonneg.mpr hm) (le_trans (by norm_num) hL)]
        _ ≤ (n : ℝ) := hnlarge
    have hblocks : 8 * momBlocks η ≤ n :=
      momBlocks_le_of_sample_log_bound ⟨hη.1, hη.2.1⟩ hL hη.2.2 hsample
    let τ : ℝ := 8 * Real.sqrt v * Real.sqrt (L / n)
    have hcell (e : Fin (p + 1)) (j : Fin p) :
        (μ {ω | |medianOfMeans (momBlocks η)
          (fun r => firstFactorial (𝒬.X e r ω) (𝒬.S e r ω) j) - u e j| ≤ τ} ≥
            ENNReal.ofReal (1 - η)) ∧
        (μ {ω | |medianOfMeans (momBlocks η)
          (fun r => secondFactorial (𝒬.X e r ω) (𝒬.S e r ω) j) - w e j| ≤ τ} ≥
            ENNReal.ofReal (1 - η)) := by
      simpa only [u, w, τ, hη.2.2] using
        balanced_factorial_mom_deviation μ 𝒬 r₀ e j η
          ⟨hη.1, hη.2.1⟩ hblocks
    let Y₁ : Fin (p + 1) → Fin p → Fin n → Ω → ℝ := fun e j r ω =>
      firstFactorial (𝒬.X e r ω) (𝒬.S e r ω) j
    let Y₂ : Fin (p + 1) → Fin p → Fin n → Ω → ℝ := fun e j r ω =>
      secondFactorial (𝒬.X e r ω) (𝒬.S e r ω) j
    have hcore₁ (e : Fin (p + 1)) (j : Fin p) :
        ∃ G : Set Ω, MeasurableSet G ∧ μ G ≥ ENNReal.ofReal (1 - η) ∧
          G ⊆ {ω | |medianOfMeans (momBlocks η) (fun r => Y₁ e j r ω) - u e j| ≤ τ} := by
      have hvar := random_offset_variance μ 𝒬.Z 𝒬.S 𝒬.X v
        𝒬.poisson 𝒬.iid 𝒬.exog 𝒬.varBound
      have hmean (r s : Fin n) : (∫ ω, Y₁ e j r ω ∂μ) = ∫ ω, Y₁ e j s ω ∂μ := by
        simpa only [Y₁, Function.comp_def] using
          ((hvar.2.1 e j r s).comp measurable_fst).integral_eq
      have hlp (r : Fin n) : MemLp (Y₁ e j r) 2 μ := by
        simpa only [Y₁] using (balanced_factorial_memLp μ 𝒬 e r j).1
      have hv' (r : Fin n) : variance (Y₁ e j r) μ ≤ (Real.sqrt v) ^ 2 := by
        rw [Real.sq_sqrt (le_of_lt hv)]
        simpa only [Y₁] using (hvar.2.2.2.2 e r j).1
      simpa only [Y₁, u, τ, hη.2.2] using
        medianOfMeans_measurable_core μ (Y₁ e j) r₀ η (Real.sqrt v)
          ⟨hη.1, hη.2.1⟩ (Real.sqrt_pos.2 hv)
          ((hvar.1 e j).comp (fun _ x => x.1) (fun _ => measurable_fst))
          hlp hmean hv' hblocks
    have hcore₂ (e : Fin (p + 1)) (j : Fin p) :
        ∃ G : Set Ω, MeasurableSet G ∧ μ G ≥ ENNReal.ofReal (1 - η) ∧
          G ⊆ {ω | |medianOfMeans (momBlocks η) (fun r => Y₂ e j r ω) - w e j| ≤ τ} := by
      have hvar := random_offset_variance μ 𝒬.Z 𝒬.S 𝒬.X v
        𝒬.poisson 𝒬.iid 𝒬.exog 𝒬.varBound
      have hmean (r s : Fin n) : (∫ ω, Y₂ e j r ω ∂μ) = ∫ ω, Y₂ e j s ω ∂μ := by
        simpa only [Y₂, Function.comp_def] using
          ((hvar.2.1 e j r s).comp measurable_snd).integral_eq
      have hlp (r : Fin n) : MemLp (Y₂ e j r) 2 μ := by
        simpa only [Y₂] using (balanced_factorial_memLp μ 𝒬 e r j).2
      have hv' (r : Fin n) : variance (Y₂ e j r) μ ≤ (Real.sqrt v) ^ 2 := by
        rw [Real.sq_sqrt (le_of_lt hv)]
        simpa only [Y₂] using (hvar.2.2.2.2 e r j).2
      simpa only [Y₂, w, τ, hη.2.2] using
        medianOfMeans_measurable_core μ (Y₂ e j) r₀ η (Real.sqrt v)
          ⟨hη.1, hη.2.1⟩ (Real.sqrt_pos.2 hv)
          ((hvar.1 e j).comp (fun _ x => x.2) (fun _ => measurable_snd))
          hlp hmean hv' hblocks
    let G₁ (e : Fin (p + 1)) (j : Fin p) : Set Ω := Classical.choose (hcore₁ e j)
    let G₂ (e : Fin (p + 1)) (j : Fin p) : Set Ω := Classical.choose (hcore₂ e j)
    have hG₁ (e : Fin (p + 1)) (j : Fin p) :
        MeasurableSet (G₁ e j) ∧ μ (G₁ e j) ≥ ENNReal.ofReal (1 - η) ∧
          G₁ e j ⊆ {ω | |medianOfMeans (momBlocks η) (fun r => Y₁ e j r ω) - u e j| ≤ τ} :=
      Classical.choose_spec (hcore₁ e j)
    have hG₂ (e : Fin (p + 1)) (j : Fin p) :
        MeasurableSet (G₂ e j) ∧ μ (G₂ e j) ≥ ENNReal.ofReal (1 - η) ∧
          G₂ e j ⊆ {ω | |medianOfMeans (momBlocks η) (fun r => Y₂ e j r ω) - w e j| ≤ τ} :=
      Classical.choose_spec (hcore₂ e j)
    let I := (Fin (p + 1) × Fin p) ⊕ (Fin (p + 1) × Fin p)
    let G : I → Set Ω := fun z => match z with
      | Sum.inl ej => G₁ ej.1 ej.2
      | Sum.inr ej => G₂ ej.1 ej.2
    have hsum : (Fintype.card I : ℝ) * η ≤ δ := by
      simp only [I, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      dsimp only [η]
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp
      push_cast
      field_simp
      norm_num
    have hcover : μ (⋂ z, G z) ≥ ENNReal.ofReal (1 - δ) := by
      apply balanced_simultaneous_coverage μ G η δ
      · intro z
        rcases z with ej | ej
        · exact (hG₁ ej.1 ej.2).1
        · exact (hG₂ ej.1 ej.2).1
      · intro z
        rcases z with ej | ej
        · exact (hG₁ ej.1 ej.2).2.1
        · exact (hG₂ ej.1 ej.2).2.1
      · exact hsum
    apply le_trans hcover
    apply measure_mono
    intro ω hω
    have hraw : ∀ e j,
        |medianOfMeans (momBlocks η) (fun r => Y₁ e j r ω) - u e j| ≤ τ ∧
        |medianOfMeans (momBlocks η) (fun r => Y₂ e j r ω) - w e j| ≤ τ := by
      intro e j
      constructor
      · apply (hG₁ e j).2.2
        exact Set.mem_iInter.mp hω (Sum.inl (e, j))
      · apply (hG₂ e j).2.2
        exact Set.mem_iInter.mp hω (Sum.inr (e, j))
    have hτnonneg : 0 ≤ τ := by positivity
    have hτstrong : τ ≤ ℓ ^ 2 / 8 := by
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hmax : v * ℓ⁻¹ ^ 4 ≤ max 1 (v * ℓ⁻¹ ^ 4) := le_max_right _ _
      have hsamp : 4096 * (v * ℓ⁻¹ ^ 4) * L ≤ (n : ℝ) := by
        have hL0 : 0 ≤ L := le_trans (by norm_num) hL
        nlinarith [mul_nonneg (sub_nonneg.mpr hmax) hL0]
      have hinv : ℓ⁻¹ ^ 4 * ℓ ^ 4 = 1 := by
        field_simp
      have hsamp' : 4096 * v * L ≤ (n : ℝ) * ℓ ^ 4 := by
        have hmul := mul_le_mul_of_nonneg_right hsamp (by positivity : 0 ≤ ℓ ^ 4)
        calc
          4096 * v * L =
              (4096 * (v * ℓ⁻¹ ^ 4) * L) * ℓ ^ 4 := by
                symm
                calc
                  _ = 4096 * v * L * (ℓ⁻¹ ^ 4 * ℓ ^ 4) := by ring
                  _ = _ := by rw [hinv]; ring
          _ ≤ (n : ℝ) * ℓ ^ 4 := hmul
      have hratio : v * (L / n) ≤ ℓ ^ 4 / 4096 := by
        rw [show v * (L / (n : ℝ)) = v * L / n by ring]
        apply (div_le_iff₀ hnR).2
        nlinarith [hsamp']
      have hsqrt : Real.sqrt (v * (L / n)) ≤ ℓ ^ 2 / 64 := by
        apply (Real.sqrt_le_left (by positivity : 0 ≤ ℓ ^ 2 / 64)).2
        norm_num at *
        nlinarith
      have hsqrt_mul : Real.sqrt v * Real.sqrt (L / n) = Real.sqrt (v * (L / n)) := by
        rw [Real.sqrt_mul (le_of_lt hv)]
      dsimp only [τ]
      calc
        8 * Real.sqrt v * Real.sqrt (L / n) =
            8 * (Real.sqrt v * Real.sqrt (L / n)) := by ring
        _ = 8 * Real.sqrt (v * (L / n)) := by rw [hsqrt_mul]
        _ ≤ ℓ ^ 2 / 8 := by nlinarith
    have hτsq : τ ≤ ℓ ^ 2 / 2 := by nlinarith [hτstrong]
    have hℓlt3 : ℓ < 3 := lt_of_le_of_lt hℓle
      ((Real.exp_lt_exp.mpr (by norm_num : (1 / 2 : ℝ) < 1)).trans Real.exp_one_lt_three)
    have hτlin : τ ≤ ℓ / 2 := by
      nlinarith [mul_pos hℓ (sub_pos.mpr hℓlt3), hτstrong]
    intro m j
    have herr := robustShift_error_of_raw_moments ℓ τ
      ⟨δ, hδpos, hδlt⟩ (fun e r => 𝒬.S e r ω) (fun e r => 𝒬.X e r ω)
      u w hℓ ⟨hτnonneg, hτlin, hτsq⟩ hfloor (by simpa only [Y₁, Y₂] using hraw) m j
    have htarget :
        ((2 * Real.log (u m.succ j) - (1 / 2 : ℝ) * Real.log (w m.succ j)) -
         (2 * Real.log (u 0 j) - (1 / 2 : ℝ) * Real.log (w 0 j))) =
          balancedObsShift μ 𝒬 r₀ m j := rfl
    rw [htarget] at herr
    change |dhat ω m j - balancedObsShift μ 𝒬 r₀ m j| ≤ ε
    change |robustShiftEstimator ℓ ⟨δ, hδpos, hδlt⟩
      (fun e r => 𝒬.S e r ω) (fun e r => 𝒬.X e r ω) m j -
        balancedObsShift μ 𝒬 r₀ m j| ≤ epsN 100000 p n v ℓ δ
    apply herr.trans
    dsimp only [τ, ε, epsN, L]
    have hsqrt_mul : Real.sqrt v * Real.sqrt
        (Real.log (4 * (p : ℝ) * (p + 1) / δ) / n) =
        Real.sqrt (v * Real.log (4 * (p : ℝ) * (p + 1) / δ) / n) := by
      rw [← Real.sqrt_mul (le_of_lt hv)]
      congr 1
      ring
    have htauRewrite : 8 * Real.sqrt v * Real.sqrt
        (Real.log (4 * (p : ℝ) * (p + 1) / δ) / n) =
        8 * Real.sqrt (v * Real.log (4 * (p : ℝ) * (p + 1) / δ) / n) := by
      calc
        _ = 8 * (Real.sqrt v * Real.sqrt
            (Real.log (4 * (p : ℝ) * (p + 1) / δ) / n)) := by ring
        _ = _ := by rw [hsqrt_mul]
    simp_rw [htauRewrite]
    have hsqrt0 : 0 ≤ Real.sqrt
        (v * Real.log (4 * (p : ℝ) * (p + 1) / δ) / n) := Real.sqrt_nonneg _
    have hellinv : 0 < ℓ⁻¹ := inv_pos.mpr hℓ
    field_simp
    nlinarith [sq_nonneg (ℓ⁻¹ - 1)]
  refine ⟨hdev, ⟨hε, ?_⟩⟩
  intro Ω' ms' μ'
  letI : MeasurableSpace Ω' := ms'
  intro 𝔐 ht hLaw
  have hshift := balancedObsShift_eq_obsShift_of_law μ μ' 𝒬 𝔐 r₀ hLaw
  have hcert : ∀ ω ∈ E,
      (oneSidedCertificate (dhat ω) ⟨ε, hε⟩ =
          some (Equiv.ofBijective 𝔐.t ht) ∨
        oneSidedCertificate (dhat ω) ⟨ε, hε⟩ = none) ∧
      (2 * ε < minStrength μ' 𝔐 →
        oneSidedCertificate (dhat ω) ⟨ε, hε⟩ =
          some (Equiv.ofBijective 𝔐.t ht)) := by
    intro ω hω
    have ha : ∀ m i, |dhat ω m i - obsShift μ' 𝔐 m i| ≤ (⟨ε, hε⟩ : {x : ℝ // 0 < x}) := by
      intro m i
      simpa [hshift m i] using hω m i
    have hc := deterministic_certificate μ' 𝔐 ht (dhat ω) ⟨ε, hε⟩ ha
    exact ⟨hc.1, hc.2.1⟩
  constructor
  · exact le_trans hdev (measure_mono (by
      intro ω hω
      exact (hcert ω hω).1))
  · intro hmargin
    exact le_trans hdev (measure_mono (by
      intro ω hω
      exact (hcert ω hω).2 hmargin))

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

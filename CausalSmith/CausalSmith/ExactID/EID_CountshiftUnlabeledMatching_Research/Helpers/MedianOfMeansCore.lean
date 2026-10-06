module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Defs.Estimator
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Probability.Moments.SubGaussian

/-! Deterministic and probabilistic ingredients for median-of-means bounds. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

lemma mom_log_pos {η : ℝ} (hη : 0 < η ∧ η < 1) : 0 < Real.log (2 / η) := by
  apply Real.log_pos
  rw [one_lt_div hη.1]
  linarith

lemma mom_log_lower {η : ℝ} (hη : 0 < η ∧ η < 1) :
    (1 / 2 : ℝ) < Real.log (2 / η) := by
  have hratio : (2 : ℝ) < 2 / η := by
    rw [lt_div_iff₀ hη.1]
    nlinarith
  have hlog : Real.log 2 < Real.log (2 / η) :=
    Real.strictMonoOn_log (by norm_num) (Set.mem_Ioi.mpr (div_pos (by norm_num) hη.1)) hratio
  exact lt_trans (by linarith [Real.log_two_gt_d9]) hlog

lemma momBlocks_real_lower {η : ℝ} (hη : 0 < η ∧ η < 1) :
    8 * Real.log (2 / η) ≤ (momBlocks η : ℝ) := by
  let x := (8 * Real.log (2 / η) - 1) / 2
  have hx : 0 ≤ x := by
    dsimp only [x]
    nlinarith [mom_log_lower hη]
  have hc := Nat.le_ceil x
  rw [momBlocks]
  push_cast
  dsimp only [x] at hc
  nlinarith

lemma momBlocks_real_upper {η : ℝ} (hη : 0 < η ∧ η < 1) :
    (momBlocks η : ℝ) < 8 * Real.log (2 / η) + 2 := by
  let x := (8 * Real.log (2 / η) - 1) / 2
  have hx : 0 ≤ x := by
    dsimp only [x]
    nlinarith [mom_log_lower hη]
  have hc := Nat.ceil_lt_add_one hx
  rw [momBlocks]
  push_cast
  dsimp only [x] at hc
  nlinarith

/-- The sample indices used by one block of `blockMean`. -/
@[no_expose]
def momBlock {n : ℕ} (k : ℕ) (s : Fin k) : Finset (Fin n) :=
  Finset.univ.filter fun r => r.val / (n / k) = s.val ∧ r.val < k * (n / k)

lemma blockMean_eq_sum_momBlock {n k : ℕ} (Y : Fin n → ℝ) (s : Fin k) :
    blockMean k Y s = (∑ r ∈ momBlock k s, Y r) / (momBlock (n := n) k s).card := by
  rfl

lemma momBlock_disjoint {n k : ℕ} {s t : Fin k} (hst : s ≠ t) :
    Disjoint (momBlock (n := n) k s) (momBlock k t) := by
  rw [Finset.disjoint_left]
  intro r hrs hrt
  simp only [momBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hrs hrt
  exact hst (Fin.ext (hrs.1.symm.trans hrt.1))

lemma momBlock_card_pos {n k : ℕ} (hk : k ≤ n) (hk0 : 0 < k) (s : Fin k) :
    0 < (momBlock (n := n) k s).card := by
  have hm : 0 < n / k := Nat.div_pos (by omega) hk0
  have hslt : s.val * (n / k) < n := by
    calc
      s.val * (n / k) < k * (n / k) :=
        (Nat.mul_lt_mul_right (Nat.div_pos (by omega) hk0)).2 s.isLt
      _ ≤ n := Nat.mul_div_le n k
  let r : Fin n := ⟨s.val * (n / k), hslt⟩
  have hr : r ∈ momBlock (n := n) k s := by
    simp only [momBlock, Finset.mem_filter, Finset.mem_univ, true_and, r]
    constructor
    · exact Nat.mul_div_left s.val hm
    · exact (Nat.mul_lt_mul_right hm).2 s.isLt
  exact Finset.card_pos.mpr ⟨r, hr⟩

lemma momBlock_card_ge_div {n k : ℕ} (hk : k ≤ n) (hk0 : 0 < k) (s : Fin k) :
    n / k ≤ (momBlock (n := n) k s).card := by
  let f : Fin (n / k) → Fin n := fun t =>
    ⟨s.val * (n / k) + t.val, by
      calc
        s.val * (n / k) + t.val < (s.val + 1) * (n / k) := by
          rw [Nat.add_mul]
          omega
        _ ≤ k * (n / k) := Nat.mul_le_mul_right (n / k) (Nat.succ_le_iff.2 s.isLt)
        _ ≤ n := Nat.mul_div_le n k⟩
  have hf_mem : ∀ t, f t ∈ momBlock (n := n) k s := by
    intro t
    simp only [momBlock, Finset.mem_filter, Finset.mem_univ, true_and, f]
    constructor
    · rw [Nat.mul_comm s.val, Nat.mul_add_div (Nat.div_pos hk hk0),
        Nat.div_eq_of_lt t.isLt, Nat.add_zero]
    · calc
        s.val * (n / k) + t.val < (s.val + 1) * (n / k) := by
          rw [Nat.add_mul]
          omega
        _ ≤ k * (n / k) := Nat.mul_le_mul_right (n / k) (Nat.succ_le_iff.2 s.isLt)
  let e : Fin (n / k) ↪ {r // r ∈ momBlock (n := n) k s} :=
    ⟨fun t => ⟨f t, hf_mem t⟩, fun a b h => Fin.ext (by simpa [f] using congrArg (fun x => x.1.val) h)⟩
  simpa using Fintype.card_le_of_injective e e.injective

/-- More than half of the entries in a symmetric interval force the lower median into it. -/
lemma medianOfMeans_mem_interval_of_majority {n k : ℕ} (hk : 0 < k)
    (Y : Fin n → ℝ) (a t : ℝ) (ht : 0 ≤ t)
    (hgood : k / 2 < (Finset.univ.filter fun s : Fin k => |blockMean k Y s - a| ≤ t).card) :
    |medianOfMeans k Y - a| ≤ t := by
  classical
  let good := Finset.univ.filter fun s : Fin k => |blockMean k Y s - a| ≤ t
  let upperSet : Set ℝ := {x | (k + 1) / 2 ≤
    (Finset.univ.filter fun s : Fin k => blockMean k Y s ≤ x).card}
  have hkodd_threshold : (k + 1) / 2 ≤ good.card := by
    dsimp only [good]
    omega
  have hu_mem : a + t ∈ upperSet := by
    change (k + 1) / 2 ≤ (Finset.univ.filter fun s : Fin k => blockMean k Y s ≤ a + t).card
    refine hkodd_threshold.trans (Finset.card_le_card ?_)
    intro s hs
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    linarith [(abs_le.mp hs).2]
  have hbounded : BddBelow upperSet := by
    let s0 : Fin k := ⟨0, hk⟩
    have hU : (Finset.univ : Finset (Fin k)).Nonempty := ⟨s0, Finset.mem_univ _⟩
    let L := Finset.univ.inf' hU (fun s : Fin k => blockMean k Y s)
    refine ⟨L, ?_⟩
    intro x hx
    change (k + 1) / 2 ≤ (Finset.univ.filter fun s : Fin k => blockMean k Y s ≤ x).card at hx
    have hcard : 0 < (Finset.univ.filter fun s : Fin k => blockMean k Y s ≤ x).card := by
      have : 0 < (k + 1) / 2 := by omega
      omega
    obtain ⟨s, hs⟩ := Finset.card_pos.mp hcard
    dsimp only [L]
    exact le_trans (Finset.inf'_le (fun z : Fin k => blockMean k Y z) (Finset.mem_univ s))
      (Finset.mem_filter.mp hs).2
  have hu : medianOfMeans k Y ≤ a + t := by
    exact csInf_le hbounded hu_mem
  have hnonempty : upperSet.Nonempty := ⟨a + t, hu_mem⟩
  have hl_each : ∀ x ∈ upperSet, a - t ≤ x := by
    intro x hx
    by_contra hnot
    have hxlt : x < a - t := lt_of_not_ge hnot
    have hdisj : Disjoint good (Finset.univ.filter fun s : Fin k => blockMean k Y s ≤ x) := by
      rw [Finset.disjoint_left]
      intro s hsg hsx
      have hlow := (abs_le.mp (Finset.mem_filter.mp hsg).2).1
      have hsx' := (Finset.mem_filter.mp hsx).2
      linarith
    have hleK : good.card + (Finset.univ.filter fun s : Fin k => blockMean k Y s ≤ x).card ≤ k := by
      rw [← Finset.card_union_of_disjoint hdisj]
      simpa using Finset.card_le_univ (good ∪
        (Finset.univ.filter fun s : Fin k => blockMean k Y s ≤ x))
    change (k + 1) / 2 ≤ (Finset.univ.filter fun s : Fin k => blockMean k Y s ≤ x).card at hx
    dsimp only [good] at hleK
    omega
  have hl : a - t ≤ medianOfMeans k Y := le_csInf hnonempty hl_each
  rw [abs_le]
  constructor <;> linarith

lemma blockMean_memLp {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Fin n → Ω → ℝ) (hLp : ∀ r, MemLp (Y r) 2 μ)
    (s : Fin k) : MemLp (fun ω => blockMean k (fun r => Y r ω) s) 2 μ := by
  simp_rw [blockMean_eq_sum_momBlock]
  convert (memLp_finsetSum (momBlock (n := n) k s) (fun r _ => hLp r)).mul_const
    ((momBlock (n := n) k s).card : ℝ)⁻¹ using 1 <;> simp [div_eq_mul_inv]

lemma integral_blockMean {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Fin n → Ω → ℝ)
    (hLp : ∀ r, MemLp (Y r) 2 μ) (a : ℝ) (hmeans : ∀ r, ∫ ω, Y r ω ∂μ = a)
    (hk : k ≤ n) (hk0 : 0 < k) (s : Fin k) :
    ∫ ω, blockMean k (fun r => Y r ω) s ∂μ = a := by
  simp_rw [blockMean_eq_sum_momBlock]
  rw [integral_div,
    integral_finset_sum _ (fun r _ => (hLp r).integrable one_le_two)]
  simp_rw [hmeans]
  have hc := momBlock_card_pos (n := n) hk hk0 s
  simp [hc.ne']

lemma variance_blockMean_le {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Fin n → Ω → ℝ)
    (hiid : iIndepFun Y μ) (hLp : ∀ r, MemLp (Y r) 2 μ) (σ : ℝ)
    (hvar : ∀ r, variance (Y r) μ ≤ σ ^ 2)
    (hk : k ≤ n) (hk0 : 0 < k) (s : Fin k) :
    variance (fun ω => blockMean k (fun r => Y r ω) s) μ ≤
      σ ^ 2 / (momBlock (n := n) k s).card := by
  let B := momBlock (n := n) k s
  have hBpos : 0 < B.card := momBlock_card_pos hk hk0 s
  have hpair : (B : Set (Fin n)).Pairwise fun i j => (Y i) ⟂ᵢ[μ] (Y j) := by
    intro i hi j hj hij
    exact hiid.indepFun hij
  have hvsum : variance (fun ω => ∑ r ∈ B, Y r ω) μ = ∑ r ∈ B, variance (Y r) μ := by
    have heq : (fun ω => ∑ r ∈ B, Y r ω) = ∑ r ∈ B, Y r := by
      funext ω
      simp
    rw [heq]
    exact IndepFun.variance_sum (fun r _ => hLp r) hpair
  simp_rw [blockMean_eq_sum_momBlock]
  change variance (fun ω => ((∑ r ∈ B, Y r ω) * (B.card : ℝ)⁻¹)) μ ≤ _
  rw [variance_mul_const, hvsum]
  have hsum : ∑ r ∈ B, variance (Y r) μ ≤ B.card * σ ^ 2 := by
    calc
      _ ≤ ∑ _r ∈ B, σ ^ 2 := Finset.sum_le_sum fun r _ => hvar r
      _ = B.card * σ ^ 2 := by simp
  calc
    (∑ r ∈ B, variance (Y r) μ) * ((B.card : ℝ)⁻¹) ^ 2
        ≤ (B.card * σ ^ 2) * ((B.card : ℝ)⁻¹) ^ 2 := by
          gcongr
    _ = σ ^ 2 / B.card := by
      field_simp

lemma blockMean_bad_measure_le {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Fin n → Ω → ℝ)
    (hiid : iIndepFun Y μ) (hLp : ∀ r, MemLp (Y r) 2 μ)
    (a σ t : ℝ) (hσ : 0 ≤ σ) (ht : 0 < t)
    (hmeans : ∀ r, ∫ ω, Y r ω ∂μ = a)
    (hvar : ∀ r, variance (Y r) μ ≤ σ ^ 2)
    (hk : k ≤ n) (hk0 : 0 < k) (s : Fin k) :
    μ {ω | t ≤ |blockMean k (fun r => Y r ω) s - a|} ≤
      ENNReal.ofReal ((σ ^ 2 / (momBlock (n := n) k s).card) / t ^ 2) := by
  have hmem := blockMean_memLp μ Y hLp s
  have hcheb := meas_ge_le_variance_div_sq hmem ht
  rw [integral_blockMean μ Y hLp a hmeans hk hk0 s] at hcheb
  exact hcheb.trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (variance_blockMean_le μ Y hiid hLp σ hvar hk hk0 s)
      (sq_nonneg t)))

lemma blockMean_bad_real_le_quarter {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Fin n → Ω → ℝ)
    (hiid : iIndepFun Y μ) (hLp : ∀ r, MemLp (Y r) 2 μ)
    (a η σ : ℝ) (hη : 0 < η ∧ η < 1) (hσ : 0 < σ)
    (hmeans : ∀ r, ∫ ω, Y r ω ∂μ = a)
    (hvar : ∀ r, variance (Y r) μ ≤ σ ^ 2)
    (hn : 8 * momBlocks η ≤ n) (s : Fin (momBlocks η)) :
    μ.real {ω | 8 * σ * Real.sqrt (Real.log (2 / η) / n) <
      |blockMean (momBlocks η) (fun r => Y r ω) s - a|} ≤ 1 / 4 := by
  let k := momBlocks η
  let L := Real.log (2 / η)
  let t := 8 * σ * Real.sqrt (L / n)
  have hL : 0 < L := mom_log_pos hη
  have hkreal_pos : 0 < (k : ℝ) := lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8) hL)
    (by simpa [k, L] using momBlocks_real_lower hη)
  have hk0 : 0 < k := by exact_mod_cast hkreal_pos
  have hk : k ≤ n := le_trans (by omega : k ≤ 8 * k) hn
  have hn0 : 0 < n := lt_of_lt_of_le hk0 hk
  have hm8 : 8 ≤ n / k := (Nat.le_div_iff_mul_le hk0).2 hn
  have hcard := momBlock_card_ge_div (n := n) hk hk0 s
  have hnlt : n < k * (n / k + 1) := Nat.lt_mul_div_succ n hk0
  have hkupper : (k : ℝ) < 8 * L + 2 := by
    simpa [k, L] using momBlocks_real_upper hη
  have hLlower : (1 / 2 : ℝ) < L := by simpa [L] using mom_log_lower hη
  have hncard : (n : ℝ) ≤ 16 * L * (momBlock (n := n) k s).card := by
    have hm8r : (8 : ℝ) ≤ (n / k : ℕ) := by exact_mod_cast hm8
    have hcardr : (n / k : ℕ) ≤ (momBlock (n := n) k s).card := by exact_mod_cast hcard
    have hnltr : (n : ℝ) < (k : ℝ) * ((n / k : ℕ) + 1) := by exact_mod_cast hnlt
    have hmstep : ((n / k : ℕ) : ℝ) + 1 ≤ (9 / 8 : ℝ) * (n / k : ℕ) := by
      linarith
    have hkstep : (k : ℝ) * (9 / 8 : ℝ) ≤ 16 * L := by
      nlinarith
    calc
      (n : ℝ) ≤ (k : ℝ) * (((n / k : ℕ) : ℝ) + 1) := hnltr.le
      _ ≤ (k : ℝ) * ((9 / 8 : ℝ) * (n / k : ℕ)) := by gcongr
      _ = ((k : ℝ) * (9 / 8 : ℝ)) * (n / k : ℕ) := by ring
      _ ≤ (16 * L) * (n / k : ℕ) := by gcongr
      _ ≤ (16 * L) * (momBlock (n := n) k s).card := by gcongr
  have ht : 0 < t := by
    dsimp only [t]
    have hdiv : 0 < L / (n : ℝ) := div_pos hL (by exact_mod_cast hn0)
    exact mul_pos (mul_pos (by norm_num) hσ) (Real.sqrt_pos.2 hdiv)
  have hcheb := blockMean_bad_measure_le μ Y hiid hLp a σ t hσ.le ht hmeans hvar hk hk0 s
  have ht_sq : t ^ 2 = 64 * σ ^ 2 * (L / n) := by
    dsimp only [t]
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hL.le (by positivity))]
    ring
  have hratio : (σ ^ 2 / (momBlock (n := n) k s).card) / t ^ 2 ≤ 1 / 4 := by
    rw [ht_sq]
    have hs2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
    have hc0 : (0 : ℝ) < (momBlock (n := n) k s).card := by
      exact_mod_cast momBlock_card_pos hk hk0 s
    have hn0r : (0 : ℝ) < n := by positivity
    have hL0 : 0 < L := hL
    field_simp
    nlinarith
  have hinc : {ω | t < |blockMean k (fun r => Y r ω) s - a|} ⊆
      {ω | t ≤ |blockMean k (fun r => Y r ω) s - a|} := by
    intro ω hω
    change t < |blockMean k (fun r => Y r ω) s - a| at hω
    change t ≤ |blockMean k (fun r => Y r ω) s - a|
    exact hω.le
  calc
    μ.real {ω | 8 * σ * Real.sqrt (Real.log (2 / η) / n) <
        |blockMean (momBlocks η) (fun r => Y r ω) s - a|}
        = μ.real {ω | t < |blockMean k (fun r => Y r ω) s - a|} := rfl
    _ ≤ μ.real {ω | t ≤ |blockMean k (fun r => Y r ω) s - a|} := measureReal_mono hinc
    _ ≤ (ENNReal.ofReal ((σ ^ 2 / (momBlock (n := n) k s).card) / t ^ 2)).toReal := by
      rw [Measure.real_def]
      exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
    _ ≤ 1 / 4 := by rw [ENNReal.toReal_ofReal (by positivity)]; exact hratio

/-- Block means over the disjoint blocks are mutually independent. -/
lemma iIndepFun_blockMean {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Fin n → Ω → ℝ) (hY : ∀ r, Measurable (Y r))
    (hiid : iIndepFun Y μ) :
    iIndepFun (fun s : Fin k => fun ω => blockMean k (fun r => Y r ω) s) μ := by
  classical
  let m : Fin k → MeasurableSpace Ω := fun s =>
    ⨆ r ∈ (momBlock (n := n) k s : Set (Fin n)), (borel ℝ).comap (Y r)
  have hm_le : ∀ s, m s ≤ ‹MeasurableSpace Ω› := by
    intro s
    exact iSup₂_le fun r _ => (measurable_iff_comap_le.mp (hY r))
  have hblock_meas : ∀ s, Measurable[m s] (fun ω => blockMean k (fun r => Y r ω) s) := by
    intro s
    simp_rw [blockMean_eq_sum_momBlock]
    apply (Finset.measurable_sum _ fun r hr => ?_).div_const
    exact (measurable_iff_comap_le.mpr
      (le_iSup_of_le r (le_iSup_of_le
        (show r ∈ (momBlock (n := n) k s : Set (Fin n)) by simpa using hr) le_rfl)))
  rw [iIndepFun_iff_iIndep]
  have hmindep : iIndep m μ := by
    letI : IsProbabilityMeasure μ := hiid.isProbabilityMeasure
    rw [iIndep_iff]
    intro S f hf
    induction S using Finset.induction_on with
    | empty => simpa using (measure_univ : μ Set.univ = 1)
    | @insert a S ha ih =>
      have hsource_disj : Disjoint (momBlock (n := n) k a)
          (Finset.univ.filter fun r : Fin n => ∃ s ∈ S, r ∈ momBlock k s) := by
        rw [Finset.disjoint_left]
        intro r hra hrs
        obtain ⟨_, ⟨s, hsS, hrs⟩⟩ := Finset.mem_filter.mp hrs
        exact (Finset.disjoint_left.mp (momBlock_disjoint (n := n)
          (show a ≠ s by intro h; subst s; exact ha hsS))) hra hrs
      let T : Finset (Fin n) := Finset.univ.filter fun r : Fin n =>
        ∃ s ∈ S, r ∈ momBlock k s
      have hind := indep_iSup_of_disjoint
        (m := fun r : Fin n => (borel ℝ).comap (Y r))
        (fun r => measurable_iff_comap_le.mp (hY r)) hiid.iIndep
        (show Disjoint ((momBlock (n := n) k a : Finset (Fin n)) : Set (Fin n))
          (T : Set (Fin n))
          from Set.disjoint_left.2 fun r hra hrs => Finset.disjoint_left.mp hsource_disj hra hrs)
      have hma : m a = ⨆ r ∈ (momBlock (n := n) k a : Set (Fin n)),
          (borel ℝ).comap (Y r) := rfl
      have hprev_le : (⨆ s ∈ (S : Set (Fin k)), m s) ≤
          ⨆ r ∈ (T : Set (Fin n)), (borel ℝ).comap (Y r) := by
        refine iSup₂_le fun s hs => iSup₂_le fun r hr => ?_
        have hrT : r ∈ (T : Set (Fin n)) := by
          change r ∈ T
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Exists.intro s ⟨hs, hr⟩
        exact le_iSup_of_le r (le_iSup_of_le hrT le_rfl)
      have hind' : Indep (m a) (⨆ s ∈ (S : Set (Fin k)), m s) μ := by
        rw [hma]
        exact indep_of_indep_of_le_right hind hprev_le
      have hfa : MeasurableSet[m a] (f a) := hf a (Finset.mem_insert_self _ _)
      have hrest : MeasurableSet[⨆ s ∈ (S : Set (Fin k)), m s] (⋂ s ∈ S, f s) := by
        apply Finset.measurableSet_biInter
        intro s hs
        have hle : m s ≤ (⨆ z ∈ (S : Set (Fin k)), m z) :=
          le_iSup_of_le s (le_iSup_of_le (show s ∈ (S : Set (Fin k)) from hs) le_rfl)
        exact hle (f s)
          (show MeasurableSet[m s] (f s) from hf s (Finset.mem_insert_of_mem hs))
      rw [Finset.set_biInter_insert, Finset.prod_insert ha]
      rw [(Indep_iff _ _ μ).mp hind' (f a) (⋂ s ∈ S, f s) hfa hrest,
        ih (fun s hs => hf s (Finset.mem_insert_of_mem hs))]
  apply iIndep_of_iIndep_of_le hmindep
  intro s
  exact measurable_iff_comap_le.mp (hblock_meas s)

/-- Hoeffding bound for a strict majority of independent bad events of probability at most `1/4`. -/
lemma majority_bad_measureReal_le_exp {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Fin k → Ω → ℝ)
    (hZ : ∀ s, Measurable (Z s)) (hInd : iIndepFun Z μ) (a t : ℝ)
    (hprob : ∀ s, μ.real {ω | t < |Z s ω - a|} ≤ 1 / 4) :
    μ.real {ω | k / 2 <
      (Finset.univ.filter fun s : Fin k => t < |Z s ω - a|).card} ≤
      Real.exp (-(k : ℝ) / 8) := by
  classical
  let B : Fin k → Set Ω := fun s => {ω | t < |Z s ω - a|}
  let X : Fin k → Ω → ℝ := fun s ω => if t < |Z s ω - a| then 1 else 0
  have hB : ∀ s, MeasurableSet (B s) := by
    intro s
    exact measurableSet_lt measurable_const ((hZ s).sub measurable_const).abs
  have hXmeas : ∀ s, Measurable (X s) := by
    intro s
    exact Measurable.ite (hB s) measurable_const measurable_const
  have hXind : iIndepFun X μ := by
    apply hInd.comp (fun _ z => if t < |z - a| then (1 : ℝ) else 0)
    intro s
    exact Measurable.ite (measurableSet_lt measurable_const
      (measurable_id.sub measurable_const).abs) measurable_const measurable_const
  have hXint : ∀ s, ∫ ω, X s ω ∂μ = μ.real (B s) := by
    intro s
    simpa [X, B, Set.indicator] using integral_indicator_one (μ := μ) (hB s)
  have hsub : ∀ s, HasSubgaussianMGF (fun ω => X s ω - ∫ x, X s x ∂μ)
      (((1 : NNReal) / 2) ^ 2) μ := by
    intro s
    convert hasSubgaussianMGF_of_mem_Icc (μ := μ) (a := 0) (b := 1)
      (hXmeas s).aemeasurable (ae_of_all _ fun ω => by
        simp only [X]; split_ifs <;> simp) using 1 <;> norm_num
  let C : Fin k → Ω → ℝ := fun s ω => X s ω - ∫ x, X s x ∂μ
  have hCind : iIndepFun C μ := by
    apply hXind.comp (fun s x => x - ∫ ω, X s ω ∂μ)
    exact fun _ => measurable_id.sub measurable_const
  have htail := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hCind
    (s := Finset.univ) (c := fun _ => ((1 : NNReal) / 2) ^ 2)
    (h_subG := fun s _ => hsub s)
    (ε := (k : ℝ) / 4) (by positivity)
  calc
    μ.real {ω | k / 2 <
        (Finset.univ.filter fun s : Fin k => t < |Z s ω - a|).card}
        ≤ μ.real {ω | (k : ℝ) / 4 ≤
            ∑ s ∈ Finset.univ, (X s ω - ∫ x, X s x ∂μ)} := by
          apply measureReal_mono (h₂ := measure_ne_top μ _)
          intro ω hω
          have hsumX : ∑ s ∈ Finset.univ, X s ω =
              ((Finset.univ.filter fun s : Fin k => t < |Z s ω - a|).card : ℝ) := by
            simp [X, Finset.sum_ite_irrel]
          have hsumE : ∑ s ∈ Finset.univ, ∫ x, X s x ∂μ ≤ (k : ℝ) / 4 := by
            calc
              _ ≤ ∑ _s : Fin k, (1 / 4 : ℝ) := by
                gcongr with s
                rw [hXint]
                exact hprob s
              _ = (k : ℝ) / 4 := by simp; ring
          have hsumC : ∑ s ∈ Finset.univ, (X s ω - ∫ x, X s x ∂μ) =
              (∑ s ∈ Finset.univ, X s ω) - ∑ s ∈ Finset.univ, ∫ x, X s x ∂μ := by
            rw [Finset.sum_sub_distrib]
          change (k : ℝ) / 4 ≤ ∑ s ∈ Finset.univ, (X s ω - ∫ x, X s x ∂μ)
          rw [hsumC, hsumX]
          change k / 2 < (Finset.univ.filter fun s : Fin k => t < |Z s ω - a|).card at hω
          have hn : k < 2 * (Finset.univ.filter fun s : Fin k => t < |Z s ω - a|).card := by
            omega
          have hc : (k : ℝ) / 2 <
              ((Finset.univ.filter fun s : Fin k => t < |Z s ω - a|).card : ℝ) := by
            exact (div_lt_iff₀' (by norm_num)).2 (by exact_mod_cast hn)
          linarith
    _ ≤ Real.exp (-((k : ℝ) / 4) ^ 2 /
          (2 * ∑ _s : Fin k, (((1 : NNReal) / 2) ^ 2 : ℝ))) := by
            simpa [C] using htail
    _ = Real.exp (-(k : ℝ) / 8) := by
      congr 1
      by_cases hk : k = 0
      · simp [hk]
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp
        ring

lemma medianOfMeans_deviation_measurable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Fin n → Ω → ℝ) (r0 : Fin n) (η σ : ℝ)
    (hη : 0 < η ∧ η < 1) (hσ : 0 < σ)
    (hY : ∀ r, Measurable (Y r))
    (hiid : iIndepFun Y μ)
    (hLp : ∀ r, MemLp (Y r) 2 μ)
    (hmeans : ∀ r s, ∫ ω, Y r ω ∂μ = ∫ ω, Y s ω ∂μ)
    (hvar : ∀ r, variance (Y r) μ ≤ σ ^ 2)
    (hn : 8 * momBlocks η ≤ n) :
    μ {ω | |medianOfMeans (momBlocks η) (fun r => Y r ω) -
      ∫ ω, Y r0 ω ∂μ| ≤
      8 * σ * Real.sqrt (Real.log (2 / η) / n)} ≥ ENNReal.ofReal (1 - η) := by
  classical
  let k := momBlocks η
  let a := ∫ ω, Y r0 ω ∂μ
  let t := 8 * σ * Real.sqrt (Real.log (2 / η) / n)
  let Z : Fin k → Ω → ℝ := fun s ω => blockMean k (fun r => Y r ω) s
  have hkodd : k % 2 = 1 := by simp [k, momBlocks]
  have hkpos : 0 < k := by
    have := momBlocks_real_lower hη
    have hL := mom_log_pos hη
    have hkreal : (0 : ℝ) < (k : ℝ) :=
      lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8) hL) (by simpa [k] using this)
    exact_mod_cast hkreal
  have hZmeas : ∀ s, Measurable (Z s) := by
    intro s
    dsimp only [Z]
    simp_rw [blockMean_eq_sum_momBlock]
    exact (Finset.measurable_sum _ fun r _ => hY r).div_const _
  have hZind : iIndepFun Z μ := by
    simpa only [Z, k] using iIndepFun_blockMean μ Y hY hiid (k := momBlocks η)
  have hprob : ∀ s, μ.real {ω | t < |Z s ω - a|} ≤ 1 / 4 := by
    intro s
    simpa only [t, Z, k, a] using blockMean_bad_real_le_quarter μ Y hiid hLp
      (∫ ω, Y r0 ω ∂μ) η σ hη hσ (fun r => hmeans r r0) hvar hn s
  have hmajor := majority_bad_measureReal_le_exp μ Z hZmeas hZind a t hprob
  have hexp : Real.exp (-(k : ℝ) / 8) ≤ η := by
    have hklo : 8 * Real.log (2 / η) ≤ (k : ℝ) := by
      simpa only [k] using momBlocks_real_lower hη
    have hmono : Real.exp (-(k : ℝ) / 8) ≤ Real.exp (-Real.log (2 / η)) := by
      rw [Real.exp_le_exp]
      linarith
    calc
      _ ≤ Real.exp (-Real.log (2 / η)) := hmono
      _ = η / 2 := by
        rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hη.1)]
        field_simp
      _ ≤ η := by linarith
  let G : Set Ω := {ω | |medianOfMeans k (fun r => Y r ω) - a| ≤ t}
  let D : Set Ω := {ω | t < |medianOfMeans k (fun r => Y r ω) - a|}
  let A : Set Ω := {ω | k / 2 <
    (Finset.univ.filter fun s : Fin k => t < |Z s ω - a|).card}
  have hDA : D ⊆ A := by
    intro ω hD
    change t < |medianOfMeans k (fun r => Y r ω) - a| at hD
    change k / 2 < (Finset.univ.filter fun s : Fin k => t < |Z s ω - a|).card
    by_contra hnot
    have hbad : (Finset.univ.filter fun s : Fin k => t < |Z s ω - a|).card ≤ k / 2 :=
      Nat.le_of_not_gt hnot
    let good := Finset.univ.filter fun s : Fin k => |Z s ω - a| ≤ t
    let bad := Finset.univ.filter fun s : Fin k => t < |Z s ω - a|
    have hdisj : Disjoint good bad := by
      rw [Finset.disjoint_left]
      intro s hsg hsb
      exact (not_lt_of_ge (Finset.mem_filter.mp hsg).2) (Finset.mem_filter.mp hsb).2
    have hunion : good ∪ bad = Finset.univ := by
      ext s
      simp only [good, bad, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro _; trivial
      · intro _; exact le_or_gt _ _
    have hsum : good.card + bad.card = k := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
      simp
    have hgood : k / 2 < good.card := by
      have hbad' : bad.card ≤ k / 2 := by simpa only [bad, Z] using hbad
      omega
    have hm := medianOfMeans_mem_interval_of_majority hkpos (fun r => Y r ω) a t
      (by positivity) (by simpa only [good, Z] using hgood)
    exact (not_lt_of_ge hm) hD
  have hDreal : μ.real D ≤ η := by
    calc
      μ.real D ≤ μ.real A := measureReal_mono hDA
      _ ≤ Real.exp (-(k : ℝ) / 8) := by simpa only [A] using hmajor
      _ ≤ η := hexp
  have huniv : Set.univ = G ∪ D := by
    ext ω
    simp only [Set.mem_univ, Set.mem_union, G, D, true_iff]
    exact (le_or_gt |medianOfMeans k (fun r => Y r ω) - a| t)
  have hmeasure : μ Set.univ ≤ μ G + μ D := by
    rw [huniv]
    exact measure_union_le G D
  have hreal : 1 ≤ μ.real G + μ.real D := by
    have htr := ENNReal.toReal_mono (by finiteness : μ G + μ D ≠ ⊤) hmeasure
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at htr
    simpa [Measure.real_def] using htr
  have hGreal : 1 - η ≤ μ.real G := by linarith
  have hfinal : ENNReal.ofReal (1 - η) ≤ μ G := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ G)]
    exact ENNReal.ofReal_le_ofReal hGreal
  simpa only [G, k, a, t] using hfinal

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

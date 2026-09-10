import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Basic
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.FiniteCategoricalCounts
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Causalean.Experimentation.DesignBased.Designs.Bernoulli
import Causalean.Experimentation.DesignBased.TwoStage

set_option linter.style.openClassical false

/-!
# Exact-hit factorization

The statements here concern only the finite label/assignment coordinate.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section
open Classical

private lemma assignmentMass_eq_pow {n : ℕ} (pi : ℝ) (z : Assignment n) :
    assignmentMass pi z =
      pi ^ treatedCount z * (1 - pi) ^ (n - treatedCount z) := by
  have hc : (Finset.univ.filter fun j => z j = false).card =
      n - (Finset.univ.filter fun j => z j = true).card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun j => z j = true)
    simp only [Bool.not_eq_true] at h
    simp at h ⊢
    omega
  rw [assignmentMass, Finset.prod_ite]
  simp [treatedCount, Finset.prod_const, hc]

private lemma mem_exactSlice_treatedCount {n r : ℕ} {z : Assignment n}
    (hz : z ∈ exactSlice n r) : treatedCount z = r := by
  simpa [exactSlice] using hz

private def assignmentSupport {n : ℕ} (z : Assignment n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ z j = true

private lemma sliceCard_eq_choose (n r : ℕ) : sliceCard n r = Nat.choose n r := by
  classical
  unfold sliceCard exactSlice
  calc
    (Finset.univ.filter fun z : Assignment n ↦ treatedCount z = r).card =
        ((Finset.univ : Finset (Fin n)).powersetCard r).card := by
      apply Finset.card_bij (fun z _ ↦ assignmentSupport z)
      · intro z hz
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.subset_univ _, ?_⟩
        simpa [assignmentSupport, treatedCount] using (Finset.mem_filter.1 hz).2
      · intro z hz v hv heq
        funext j
        apply Bool.eq_iff_iff.mpr
        have hj := Finset.ext_iff.mp heq j
        simpa [assignmentSupport] using hj
      · intro s hs
        let z : Assignment n := fun j ↦ decide (j ∈ s)
        refine ⟨z, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hcard := (Finset.mem_powersetCard.1 hs).2
          simpa [treatedCount, z] using hcard
        · ext j
          simp [assignmentSupport, z, (Finset.mem_powersetCard.1 hs).1]
    _ = Nat.choose ((Finset.univ : Finset (Fin n)).card) r :=
      Finset.card_powersetCard r _
    _ = Nat.choose n r := by simp

private lemma assignmentMass_on_exactSlice {n r : ℕ} (pi : ℝ)
    {z : Assignment n} (hz : z ∈ exactSlice n r) :
    assignmentMass pi z = pi ^ r * (1 - pi) ^ (n - r) := by
  rw [assignmentMass_eq_pow, mem_exactSlice_treatedCount hz]

private lemma sum_assignmentMass {n : ℕ} (pi : ℝ) :
    ∑ z : Assignment n, assignmentMass pi z = 1 := by
  unfold assignmentMass
  calc
    (∑ z : Fin n → Bool, ∏ j, if z j = true then pi else 1 - pi) =
        ∏ j : Fin n, ∑ b : Bool, if b = true then pi else 1 - pi :=
      (Fintype.prod_sum (fun _j : Fin n ↦ fun b : Bool ↦
        if b = true then pi else 1 - pi)).symm
    _ = 1 := by simp

/-- Exact-hit counts in an array of observed records; the final coordinate is
the nontarget residual count. -/
def targetHitCounts (m : Fin K → ℕ) (O : Fin C → Record K n) : Fin (K + 1) → ℕ :=
  fun i => if h : (i : ℕ) < K then
    (Finset.univ.filter fun c => (O c).2.1 ∈ exactSlice n (m ⟨i, h⟩)).card
  else (Finset.univ.filter fun c => ∀ k, (O c).2.1 ∉ exactSlice n (m k)).card

private def hitCategory {K n : ℕ} (m : Fin K → ℕ) (z : Assignment n) : Fin (K + 1) :=
  if h : ∃ k, z ∈ exactSlice n (m k) then Fin.castSucc h.choose else Fin.last K

private lemma hitCategory_eq_castSucc {K n : ℕ} (m : Fin K → ℕ)
    (hm : StrictMono m) (z : Assignment n) (k : Fin K) :
    hitCategory m z = Fin.castSucc k ↔ z ∈ exactSlice n (m k) := by
  classical
  unfold hitCategory
  split_ifs with h
  · constructor
    · intro heq
      have hk : h.choose = k := Fin.castSucc_inj.mp heq
      simpa [hk] using h.choose_spec
    · intro hz
      exact Fin.castSucc_inj.mpr <| hm.injective <| by
        rw [← mem_exactSlice_treatedCount h.choose_spec,
          ← mem_exactSlice_treatedCount hz]
  · constructor
    · intro heq
      exact ((Fin.castSucc_ne_last k) heq.symm).elim
    · intro hz
      exact (h ⟨k, hz⟩).elim

private lemma hitCategory_eq_last {K n : ℕ} (m : Fin K → ℕ)
    (z : Assignment n) :
    hitCategory m z = Fin.last K ↔ ∀ k, z ∉ exactSlice n (m k) := by
  classical
  unfold hitCategory
  split_ifs with h
  · constructor
    · intro heq
      exact ((Fin.castSucc_ne_last h.choose) heq).elim
    · intro hz
      exact (hz h.choose h.choose_spec).elim
  · exact ⟨fun _ k hz ↦ h ⟨k, hz⟩, fun _ ↦ rfl⟩

private lemma targetHitCounts_eq_categoricalCounts {C K n : ℕ}
    (m : Fin K → ℕ) (hm : StrictMono m) (O : Fin C → Record K n) :
    targetHitCounts m O = categoricalCounts (fun c ↦ hitCategory m (O c).2.1) := by
  funext i
  unfold targetHitCounts categoricalCounts
  split_ifs with hi
  · let k : Fin K := ⟨i, hi⟩
    apply congrArg Finset.card
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hitCategory_eq_castSucc m hm (O c).2.1 k).symm.trans <| by rfl
  · have hilast : i = Fin.last K := by
      apply Fin.ext
      simp only [Fin.last, Fin.val_mk]
      omega
    subst i
    apply congrArg Finset.card
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hitCategory_eq_last m (O c).2.1).symm

private lemma measurable_hitCategory {K n : ℕ} (m : Fin K → ℕ) :
    Measurable (fun o : Record K n ↦ hitCategory m o.2.1) := by
  apply Measurable.comp (measurable_of_finite (f := hitCategory m))
  fun_prop

private lemma bernoulliObservedLaw_assignmentEvent {K n : ℕ}
    (P : Measure (Schedule n)) [IsProbabilityMeasure P]
    (p : Fin K → ℝ) (m : Fin K → ℕ) (S : Finset (Assignment n)) :
    bernoulliObservedLaw P p m {o | o.2.1 ∈ S} =
      ∑ l, ENNReal.ofReal (p l) * ∑ z ∈ S,
        ENNReal.ofReal (assignmentMass (saturation n m l) z) := by
  have hs : MeasurableSet {o : Record K n | o.2.1 ∈ S} := by
    exact S.measurableSet.preimage (by fun_prop)
  have hk : Measurable (fun Y : Schedule n => ∑ l, ENNReal.ofReal (p l) •
      ∑ z, ENNReal.ofReal (assignmentMass (saturation n m l) z) •
        Measure.dirac (l, z, Y z)) := by
    have hw (a : ℝ≥0∞) (l : Fin K) (z : Assignment n) :
        Measurable (fun Y : Schedule n ↦ a • Measure.dirac (l, z, Y z)) := by
      refine Measure.measurable_of_measurable_coe _ (fun s hs' ↦ ?_)
      simp only [Measure.smul_apply, Measure.dirac_apply' _ hs', smul_eq_mul]
      exact measurable_const.mul (measurable_one.indicator
        (hs'.preimage (by fun_prop)))
    simp_rw [Finset.smul_sum, smul_smul]
    simpa only [Finset.sum_apply] using
      Finset.measurable_fun_sum Finset.univ (fun l _ ↦
        Finset.measurable_fun_sum Finset.univ (fun z _ ↦
          hw (ENNReal.ofReal (p l) *
            ENNReal.ofReal (assignmentMass (saturation n m l) z)) l z))
  rw [bernoulliObservedLaw, Measure.bind_apply hs hk.aemeasurable]
  have hpoint (Y : Schedule n) :
      (∑ l, ENNReal.ofReal (p l) •
        ∑ z, ENNReal.ofReal (assignmentMass (saturation n m l) z) •
          Measure.dirac (l, z, Y z)) {o | o.2.1 ∈ S} =
        ∑ l, ENNReal.ofReal (p l) * ∑ z ∈ S,
          ENNReal.ofReal (assignmentMass (saturation n m l) z) := by
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hs]
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    simp [Set.indicator]
  simp_rw [hpoint]
  simp

/-- Multinomial mass on `K` target-hit cells plus the residual cell. -/
def multinomialMass (C : ℕ) (prob : Fin (K + 1) → ℝ)
    (x : Fin (K + 1) → ℕ) : ℝ :=
  if ∑ i, x i = C then
    (Nat.factorial C : ℝ) / (∏ i, (Nat.factorial (x i) : ℝ)) *
      ∏ i, (prob i) ^ (x i)
  else 0

-- @node: lem:exact-hit-factorization
/-- Under the Bernoulli-label regime, joint and marginal exact-hit masses factor
as `p_l B_kl/M_k` and `q_k/M_k`; Bayes inversion follows, target assignments are
conditionally uniform, and the `C` target-hit counts are multinomial. -/
lemma exact_hit_factorization {C n K : ℕ} [NeZero n] [NeZero K]
    (P : Measure (Schedule n)) (sampleLaw : Measure (Fin C → Schedule n))
    (scheduleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n)
    (p : Fin K → ℝ) (m : Fin K → ℕ)
    (h_menu : WellFormedMenu n K m) (hP : IsProbabilityMeasure P)
    (h_iid : IidSchedules P sampleLaw)
    (h_labels : BernoulliLabelIid p labelLaw)
    (h_indep : BernoulliLabelScheduleIndep sampleLaw labelLaw jointLaw)
    (h_units : BernoulliUnits m P labelLaw assignmentLaw) :
    let B := (hitMatrix n m p).1
    let q := (hitMatrix n m p).2
    (∀ k l z, z ∈ exactSlice n (m k) →
      p l * assignmentMass (saturation n m l) z =
        p l * B k l / sliceCard n (m k)) ∧
    (∀ k z, z ∈ exactSlice n (m k) →
      (∑ l, p l * assignmentMass (saturation n m l) z) =
        q k / sliceCard n (m k)) ∧
    (∀ k l z, z ∈ exactSlice n (m k) → 0 < q k →
      (p l * assignmentMass (saturation n m l) z) /
          (∑ j, p j * assignmentMass (saturation n m j) z) = p l * B k l / q k) ∧
    (∀ k z z', z ∈ exactSlice n (m k) → z' ∈ exactSlice n (m k) →
      ∑ l, p l * assignmentMass (saturation n m l) z =
        ∑ l, p l * assignmentMass (saturation n m l) z') ∧
    (∀ x : Fin (K + 1) → ℕ,
      (Measure.pi fun _ : Fin C => bernoulliObservedLaw P p m)
        {O | targetHitCounts m O = x} = ENNReal.ofReal
          (multinomialMass C (fun i => if h : (i : ℕ) < K then q ⟨i, h⟩
            else 1 - ∑ k, q k) x)) := by
  dsimp only
  have hfactor : ∀ k l z, z ∈ exactSlice n (m k) →
      p l * assignmentMass (saturation n m l) z =
        p l * (hitMatrix n m p).1 k l / sliceCard n (m k) := by
    intro k l z hz
    have hmk : m k ≤ n := by
      have := (h_menu.2.2.2.1 k).2
      omega
    have hchoose : (Nat.choose n (m k) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hmk).ne'
    rw [assignmentMass_on_exactSlice (saturation n m l) hz,
      sliceCard_eq_choose]
    dsimp [hitMatrix]
    field_simp
  have hmarg : ∀ k z, z ∈ exactSlice n (m k) →
      (∑ l, p l * assignmentMass (saturation n m l) z) =
        (hitMatrix n m p).2 k / sliceCard n (m k) := by
    intro k z hz
    simp_rw [hfactor k _ z hz]
    rw [← Finset.sum_div]
    dsimp [hitMatrix]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    ring
  rcases h_labels with ⟨_, mu, _, hp, _⟩
  letI : IsProbabilityMeasure P := hP
  have hsat (l : Fin K) : saturation n m l ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · unfold saturation
      positivity
    · unfold saturation
      rw [div_le_one (by exact_mod_cast (show 0 < n by
        have := h_menu.1
        omega))]
      exact_mod_cast (show m l ≤ n by
        have := (h_menu.2.2.2.1 l).2
        omega)
  have hmass_nonneg (l : Fin K) (z : Assignment n) :
      0 ≤ assignmentMass (saturation n m l) z := by
    unfold assignmentMass
    exact Finset.prod_nonneg fun j _ ↦ by
      split <;> linarith [(hsat l).1, (hsat l).2]
  have hprobObs : IsProbabilityMeasure (bernoulliObservedLaw P p m) := by
    constructor
    have hzall (l : Fin K) :
        (∑ z ∈ (Finset.univ : Finset (Assignment n)),
          ENNReal.ofReal (assignmentMass (saturation n m l) z)) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ ↦ hmass_nonneg l z)]
      simp [sum_assignmentMass]
    rw [← show {o : Record K n | o.2.1 ∈
        (Finset.univ : Finset (Assignment n))} = Set.univ by ext; simp]
    simpa only [hzall, mul_one,
      ← ENNReal.ofReal_sum_of_nonneg (fun l _ ↦ hp.1 l), hp.2.1,
      ENNReal.ofReal_one] using
      (bernoulliObservedLaw_assignmentEvent P p m
        (Finset.univ : Finset (Assignment n)))
  letI : IsProbabilityMeasure (bernoulliObservedLaw P p m) := hprobObs
  have hcell (k : Fin K) :
      bernoulliObservedLaw P p m
          ((fun o : Record K n ↦ hitCategory m o.2.1) ⁻¹' {Fin.castSucc k}) =
        ENNReal.ofReal ((hitMatrix n m p).2 k) := by
    have hset : ((fun o : Record K n ↦ hitCategory m o.2.1) ⁻¹'
        {Fin.castSucc k}) = {o | o.2.1 ∈ exactSlice n (m k)} := by
      ext o
      exact hitCategory_eq_castSucc m h_menu.2.2.2.2 o.2.1 k
    rw [hset, bernoulliObservedLaw_assignmentEvent]
    have hzsum (l : Fin K) :
        (∑ z ∈ exactSlice n (m k),
          ENNReal.ofReal (assignmentMass (saturation n m l) z)) =
          ENNReal.ofReal ((hitMatrix n m p).1 k l) := by
      rw [Finset.sum_congr rfl (fun z hz ↦ by
        rw [assignmentMass_on_exactSlice (saturation n m l) hz])]
      rw [Finset.sum_const, nsmul_eq_mul,
        show (exactSlice n (m k)).card = Nat.choose n (m k) from
          sliceCard_eq_choose n (m k),
        ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg (Nat.choose n (m k)))]
      congr 1
      dsimp [hitMatrix]
      ring
    simp_rw [hzsum]
    simp_rw [← ENNReal.ofReal_mul (hp.1 _)]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 2
      dsimp [hitMatrix]
      apply Finset.sum_congr rfl
      intro l _
      ring
    · intro l _
      exact mul_nonneg (hp.1 l) <| by
        dsimp [hitMatrix]
        exact mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hsat l).1 _))
          (pow_nonneg (sub_nonneg.mpr (hsat l).2) _)
  have hqpos : ∀ k, (hitMatrix n m p).2 k ∈ Set.Ioo (0 : ℝ) 1 :=
    hitMatrix_rate_mem_Ioo n m p h_menu ⟨hp.1, hp.2.1⟩
  have hresData :
      bernoulliObservedLaw P p m
          ((fun o : Record K n ↦ hitCategory m o.2.1) ⁻¹' {Fin.last K}) =
        ENNReal.ofReal (1 - ∑ k, (hitMatrix n m p).2 k) ∧
      ∑ k, (hitMatrix n m p).2 k ≤ 1 := by
    let g : Record K n → Fin (K + 1) := fun o ↦ hitCategory m o.2.1
    let A : Set (Record K n) := ⋃ k : Fin K, g ⁻¹' {Fin.castSucc k}
    have hAmeas : MeasurableSet A := by
      simpa [A, g] using Finset.measurableSet_biUnion Finset.univ (fun k _ ↦
        (measurableSet_singleton (Fin.castSucc k)).preimage (measurable_hitCategory m)
      )
    have hAdisj : Pairwise (Function.onFun Disjoint
        (fun k : Fin K ↦ g ⁻¹' {Fin.castSucc k})) := by
      intro k l hkl
      apply Set.disjoint_left.2
      intro o hko hlo
      exact hkl (Fin.castSucc_inj.mp (hko.symm.trans hlo))
    have hAmeasure : bernoulliObservedLaw P p m A =
        ∑ k, ENNReal.ofReal ((hitMatrix n m p).2 k) := by
      rw [show A = ⋃ k ∈ (Finset.univ : Finset (Fin K)),
          g ⁻¹' {Fin.castSucc k} by simp [A],
        measure_biUnion_finset
          (fun k _ l _ hkl ↦ hAdisj hkl)
          (fun k _ ↦ (measurableSet_singleton (Fin.castSucc k)).preimage
            (measurable_hitCategory m))]
      exact Finset.sum_congr rfl fun k _ ↦ hcell k
    have hlast : g ⁻¹' {Fin.last K} = Aᶜ := by
      ext o
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff,
        Set.mem_iUnion, A]
      constructor
      · intro ho
        rintro ⟨k, hk⟩
        exact Fin.castSucc_ne_last k (hk.symm.trans ho)
      · intro ho
        have hall (i : Fin (K + 1)) :
            (¬ ∃ k : Fin K, i = Fin.castSucc k) → i = Fin.last K := by
          refine Fin.lastCases (fun _ ↦ rfl) (fun k hk ↦ ?_) i
          exact (hk ⟨k, rfl⟩).elim
        exact hall (g o) ho
    have hsum_nonneg : 0 ≤ ∑ k, (hitMatrix n m p).2 k :=
      Finset.sum_nonneg fun k _ ↦ (hqpos k).1.le
    have hsum_le : ∑ k, (hitMatrix n m p).2 k ≤ 1 := by
      rw [← ENNReal.ofReal_le_ofReal_iff (by norm_num)]
      rw [ENNReal.ofReal_one,
        ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ (hqpos k).1.le),
        ← hAmeasure]
      calc
        bernoulliObservedLaw P p m A ≤
            bernoulliObservedLaw P p m Set.univ := measure_mono (Set.subset_univ A)
        _ = 1 := measure_univ
    refine ⟨?_, hsum_le⟩
    rw [show (fun o : Record K n ↦ hitCategory m o.2.1) = g from rfl,
      hlast, measure_compl hAmeas (by
        rw [hAmeasure]
        exact ENNReal.sum_ne_top.2 fun k _ ↦ ENNReal.ofReal_ne_top),
      hAmeasure, measure_univ]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ (hqpos k).1.le),
      ENNReal.ofReal_sub 1 hsum_nonneg]
    simp
  have hres := hresData.1
  have hsum_le := hresData.2
  refine ⟨hfactor, hmarg, ?_, ?_, ?_⟩
  · intro k l z hz hq
    rw [hmarg k z hz, hfactor k l z hz]
    have hslice : (sliceCard n (m k) : ℝ) ≠ 0 := by
      rw [sliceCard_eq_choose]
      exact_mod_cast (Nat.choose_pos (by
        have := (h_menu.2.2.2.1 k).2
        omega)).ne'
    field_simp
  · intro k z z' hz hz'
    rw [hmarg k z hz, hmarg k z' hz']
  · -- The iid finite-categorical substrate below discharges this count law.
    intro x
    let g : Record K n → Fin (K + 1) := fun o ↦ hitCategory m o.2.1
    let prob : Fin (K + 1) → ℝ := fun i ↦
      if h : (i : ℕ) < K then (hitMatrix n m p).2 ⟨i, h⟩
      else 1 - ∑ k, (hitMatrix n m p).2 k
    have hprobCell (i : Fin (K + 1)) :
        bernoulliObservedLaw P p m (g ⁻¹' {i}) = ENNReal.ofReal (prob i) := by
      by_cases hi : (i : ℕ) < K
      · let k : Fin K := ⟨i, hi⟩
        change bernoulliObservedLaw P p m (g ⁻¹' {Fin.castSucc k}) = _
        rw [show g = (fun o : Record K n ↦ hitCategory m o.2.1) from rfl,
          hcell k]
        simp [prob, hi, k]
      · have hieq : i = Fin.last K := by
          apply Fin.ext
          simp only [Fin.last, Fin.val_mk]
          omega
        subst i
        simpa [g, prob] using hres
    have hprobNonneg (i : Fin (K + 1)) : 0 ≤ prob i := by
      by_cases hi : (i : ℕ) < K
      · simp [prob, hi, (hqpos ⟨i, hi⟩).1.le]
      · simp [prob, hi, sub_nonneg.mpr hsum_le]
    have hm := iid_finiteCategorical_counts_multinomial (C := C) g
      (measurable_hitCategory m) (bernoulliObservedLaw P p m) prob
      hprobNonneg hprobCell x
    have hevent : {O : Fin C → Record K n | targetHitCounts m O = x} =
        {O | categoricalCounts (g ∘ O) = x} := by
      ext O
      have hc := targetHitCounts_eq_categoricalCounts m h_menu.2.2.2.2 O
      simpa [g, Function.comp_def] using congrArg (fun y ↦ y = x) hc
    rw [hevent]
    by_cases hx : ∑ i, x i = C
    · rw [if_pos hx] at hm
      simpa [multinomialMass, hx, g, prob] using hm
    · rw [if_neg hx] at hm
      simpa [multinomialMass, hx, g, prob] using hm

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

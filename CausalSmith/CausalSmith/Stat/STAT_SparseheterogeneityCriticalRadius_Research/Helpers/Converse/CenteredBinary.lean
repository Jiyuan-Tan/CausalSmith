module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.FixedSampleTransfer
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.SharedDesignConstruction
public import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.ParametricLower
public import Causalean.Stat.Minimax.MarkovKernelTransport

/-! A centered binary observation channel for homogeneous converse witnesses. -/

@[expose] public section
namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius
open MeasureTheory ProbabilityTheory Set
open SharedDesignConstruction
open CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
open scoped ENNReal

instance {d : ℕ} : MeasurableSingletonClass (Obs d) where
  measurableSet_singleton o := by
    rw [show ({o} : Set (Obs d)) =
      (fun z : Obs d => (z.x, z.a, z.y)) ⁻¹' {(o.x, o.a, o.y)} by
        ext z
        constructor
        · intro h
          subst z
          simp
        · intro h
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at h
          rcases z with ⟨x, a, y⟩
          simp only at h
          rcases h with ⟨rfl, rfl, rfl⟩
          rfl]
    change ∃ t, MeasurableSet t ∧
      (fun z : Obs d => (z.x, z.a, z.y)) ⁻¹' t =
        (fun z : Obs d => (z.x, z.a, z.y)) ⁻¹' {(o.x, o.a, o.y)}
    exact ⟨{(o.x, o.a, o.y)},
      (show MeasurableSet ({(o.x, o.a, o.y)} : Set (Fin d × Bool × ℝ)) from
        measurableSet_singleton _), rfl⟩

noncomputable def centeredControlKernel {d : ℕ} (k : Fin d) (M : ℝ) : Kernel (Obs d) (Obs d) := by
  let f : Obs d → Measure (Obs d) := fun o => if o.a then Measure.dirac o else
    (2 : ℝ≥0∞)⁻¹ • Measure.dirac ⟨o.x, false, -(M / 2)⟩ +
      (2 : ℝ≥0∞)⁻¹ • Measure.dirac ⟨o.x, false, M / 2⟩
  let s : Set (Obs d) := {testObsAtom k false 0,
    testObsAtom k true (M / 2), testObsAtom k true (-(M / 2))}
  exact finiteSupportKernel f s (by simp [s]) (testObsAtom k false 0)

instance {d : ℕ} (k : Fin d) (M : ℝ) : IsMarkovKernel (centeredControlKernel k M) := by
  let f : Obs d → Measure (Obs d) := fun o => if o.a then Measure.dirac o else
    (2 : ℝ≥0∞)⁻¹ • Measure.dirac ⟨o.x, false, -(M / 2)⟩ +
      (2 : ℝ≥0∞)⁻¹ • Measure.dirac ⟨o.x, false, M / 2⟩
  let s : Set (Obs d) := {testObsAtom k false 0,
    testObsAtom k true (M / 2), testObsAtom k true (-(M / 2))}
  have hf : ∀ o, IsProbabilityMeasure (f o) := by
    intro o
    cases h : o.a
    · rw [isProbabilityMeasure_iff]
      simp [f, h]
      rw [← two_mul]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    · simp [f, h]
      infer_instance
  exact ⟨finiteSupportKernel_isProbabilityMeasure f s (by simp [s])
    (testObsAtom k false 0)⟩

lemma centeredControlKernel_apply_control {d : ℕ} (k : Fin d) (M : ℝ) :
    centeredControlKernel k M (testObsAtom k false 0) =
      (2 : ℝ≥0∞)⁻¹ • Measure.dirac (testObsAtom k false (-(M / 2))) +
        (2 : ℝ≥0∞)⁻¹ • Measure.dirac (testObsAtom k false (M / 2)) := by
  simp [centeredControlKernel, finiteSupportKernel_apply, testObsAtom]

lemma centeredControlKernel_apply_treated {d : ℕ} (k : Fin d) (M y : ℝ)
    (hy : y = M / 2 ∨ y = -(M / 2)) :
    centeredControlKernel k M (testObsAtom k true y) =
      Measure.dirac (testObsAtom k true y) := by
  rcases hy with rfl | rfl <;>
    simp [centeredControlKernel, finiteSupportKernel_apply, testObsAtom]

lemma centeredControlKernel_bind_testObservedLaw_explicit {d : ℕ} (k : Fin d) (M u : ℝ)
    (hM : 0 < M) (hu : |u| ≤ M / 2) :
    centeredControlKernel k M ∘ₘ testObservedLaw k (M / 2) u =
      ((2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹) •
        Measure.dirac (testObsAtom k false (-(M / 2))) +
      ((2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹) •
        Measure.dirac (testObsAtom k false (M / 2)) +
      (2 : ℝ≥0∞)⁻¹ • Measure.map (testObsAtom k true)
        (Causalean.Mathlib.Probability.twoPointMean (M / 2) u) := by
  let μ := Causalean.Mathlib.Probability.twoPointMean (M / 2) u
  have hsupp : ∀ᵐ y ∂μ, y = M / 2 ∨ y = -(M / 2) := by
    unfold μ Causalean.Mathlib.Probability.twoPointMean
    rw [ae_add_measure_iff]
    constructor <;> apply Measure.ae_smul_measure <;> simp
  have hae : ∀ᵐ o ∂Measure.map (testObsAtom k true) μ,
      centeredControlKernel k M o = Measure.dirac o := by
    let s : Set (Obs d) := {testObsAtom k true (M / 2),
      testObsAtom k true (-(M / 2))}
    have hmem : ∀ᵐ o ∂Measure.map (testObsAtom k true) μ, o ∈ s := by
      rw [ae_map_iff (measurable_testObsAtom k true).aemeasurable
        (Set.Finite.measurableSet (by
          exact Set.Finite.insert _ (Set.finite_singleton _)))]
      filter_upwards [hsupp] with y hy
      rcases hy with rfl | rfl <;> simp [s]
    filter_upwards [hmem] with o ho
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    rcases ho with rfl | rfl
    · exact centeredControlKernel_apply_treated k M (M / 2) (Or.inl rfl)
    · exact centeredControlKernel_apply_treated k M (-(M / 2)) (Or.inr rfl)
  have htreat : centeredControlKernel k M ∘ₘ
      Measure.map (testObsAtom k true) μ = Measure.map (testObsAtom k true) μ := by
    calc
      _ = (fun o => Measure.dirac o) ∘ₘ Measure.map (testObsAtom k true) μ :=
        Measure.bind_congr_right hae
      _ = _ := Measure.bind_dirac
  ext t ht
  rw [Measure.bind_apply ht (Kernel.measurable (centeredControlKernel k M)).aemeasurable]
  simp only [testObservedLaw, lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac, Measure.add_apply, Measure.smul_apply]
  rw [centeredControlKernel_apply_control]
  rw [← Measure.bind_apply ht
    (Kernel.measurable (centeredControlKernel k M)).aemeasurable, htreat]
  simp only [Measure.add_apply, Measure.smul_apply]
  change (2 : ℝ≥0∞)⁻¹ *
        ((2 : ℝ≥0∞)⁻¹ * (Measure.dirac (testObsAtom k false (-(M / 2)))) t +
          (2 : ℝ≥0∞)⁻¹ * (Measure.dirac (testObsAtom k false (M / 2))) t) +
      (2 : ℝ≥0∞)⁻¹ * (Measure.map (testObsAtom k true) μ) t =
    ((2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹) *
        (Measure.dirac (testObsAtom k false (-(M / 2)))) t +
      ((2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹) *
        (Measure.dirac (testObsAtom k false (M / 2))) t +
      (2 : ℝ≥0∞)⁻¹ * (Measure.map (testObsAtom k true) μ) t
  rw [mul_add]
  ac_rfl

noncomputable def centeredOneCellLaw {d : ℕ} (k : Fin d) (M u : ℝ)
    (hM : 0 < M) (hu : |u| ≤ M / 2) : Law d :=
  prescribedFiniteRealLaw M (fun j => if j = k then 1 else 0) (fun _ => 1 / 2)
    (fun a _ => if a then 1 / 2 + u / M else 1 / 2)
    (by intro j; split_ifs <;> norm_num) (by intro; norm_num)
    (by intro; norm_num) (by intro; norm_num)
    (by
      intro a j
      cases a
      · norm_num
      · simp only [ite_true]
        rw [abs_le] at hu
        constructor
        · have hsum : 0 ≤ M / 2 + u := by linarith
          rw [show 1 / 2 + u / M = (M / 2 + u) / M by
            field_simp [hM.ne']]
          exact div_nonneg hsum hM.le
        · rw [show 1 / 2 + u / M ≤ 1 ↔ u ≤ M / 2 by
            constructor <;> intro h <;> field_simp at h ⊢ <;> nlinarith]
          exact hu.2)
    (by classical simp)

lemma centeredOneCellLaw_observedLaw {d : ℕ} (k : Fin d) (M u : ℝ)
    (hM : 0 < M) (hu : |u| ≤ M / 2) :
    (centeredOneCellLaw k M u hM hu).observedLaw =
      ((2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹) •
        Measure.dirac (testObsAtom k false (-(M / 2))) +
      ((2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹) •
        Measure.dirac (testObsAtom k false (M / 2)) +
      (2 : ℝ≥0∞)⁻¹ • Measure.map (testObsAtom k true)
        (Causalean.Mathlib.Probability.twoPointMean (M / 2) u) := by
  ext t ht
  simp only [centeredOneCellLaw, prescribedFiniteRealLaw, affineBinaryRealLaw]
  rw [← PMF.toMeasure_map _ _ (by fun_prop)]
  rw [Measure.map_apply_of_aemeasurable (by fun_prop) ht]
  rw [PMF.toMeasure_apply_fintype]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [
    PMF.ofFintype_apply, Set.indicator,
    sharedDesignBinaryLaw, sharedDesignBinaryAtom,
    Causalean.Mathlib.Probability.twoPointMean, testObsAtom, ht]
  rw [Finset.sum_eq_single k]
  · simp [affineObserved, Causalean.Mathlib.Probability.twoPointMean,
      Measure.map_apply (measurable_testObsAtom k true) ht,
      Measure.add_apply, Measure.smul_apply]
    rw [abs_le] at hu
    have hp : 0 ≤ 1 / 2 + u / M := by
      rw [show 1 / 2 + u / M = (M / 2 + u) / M by field_simp [hM.ne']]
      exact div_nonneg (by linarith) hM.le
    have hm : 0 ≤ 1 / 2 - u / M := by
      rw [show 1 / 2 - u / M = (M / 2 - u) / M by field_simp [hM.ne']]
      exact div_nonneg (by linarith) hM.le
    have hpform : (1 + u / (M / 2)) / 2 = 1 / 2 + u / M := by
      field_simp [hM.ne']
    have hmform : (1 - u / (M / 2)) / 2 = 1 / 2 - u / M := by
      field_simp [hM.ne']
    rw [hpform, hmform]
    have hone : 1 - (1 / 2 + u / M) = 1 / 2 - u / M := by ring
    have hquarter : ENNReal.ofReal (1 / 4) =
        (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num),
        show ENNReal.ofReal 4 = (4 : ℝ≥0∞) by norm_num,
        show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
      exact ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by simp))
    have hquarter₁ : ENNReal.ofReal ((1 - (2 : ℝ)⁻¹) * (2 : ℝ)⁻¹) =
        (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ := by
      convert hquarter using 1 <;> norm_num
    have hquarter₂ : ENNReal.ofReal ((1 - (2 : ℝ)⁻¹) * (1 - (2 : ℝ)⁻¹)) =
        (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ := by
      convert hquarter using 1 <;> norm_num
    have hTT : (k, true, true) ∈ affineObserved M ⁻¹' t ↔
        testObsAtom k true (M / 2) ∈ t := by
      change (⟨k, true, M * (1 - 1 / 2)⟩ : Obs d) ∈ t ↔
        (⟨k, true, M / 2⟩ : Obs d) ∈ t
      congr 2 <;> ring
    have hTF : (k, true, false) ∈ affineObserved M ⁻¹' t ↔
        testObsAtom k true (-(M / 2)) ∈ t := by
      change (⟨k, true, M * (0 - 1 / 2)⟩ : Obs d) ∈ t ↔
        (⟨k, true, -(M / 2)⟩ : Obs d) ∈ t
      congr 2 <;> ring
    have hFT : (k, false, true) ∈ affineObserved M ⁻¹' t ↔
        testObsAtom k false (M / 2) ∈ t := by
      change (⟨k, false, M * (1 - 1 / 2)⟩ : Obs d) ∈ t ↔
        (⟨k, false, M / 2⟩ : Obs d) ∈ t
      congr 2 <;> ring
    have hFF : (k, false, false) ∈ affineObserved M ⁻¹' t ↔
        testObsAtom k false (-(M / 2)) ∈ t := by
      change (⟨k, false, M * (0 - 1 / 2)⟩ : Obs d) ∈ t ↔
        (⟨k, false, -(M / 2)⟩ : Obs d) ∈ t
      congr 2 <;> ring
    by_cases qTT : testObsAtom k true (M / 2) ∈ t <;>
      by_cases qTF : testObsAtom k true (-(M / 2)) ∈ t <;>
      by_cases qFT : testObsAtom k false (M / 2) ∈ t <;>
      by_cases qFF : testObsAtom k false (-(M / 2)) ∈ t
    all_goals
      simp_all [testObsAtom, Set.indicator, hp, hm]
      try rw [hone]
      try simp only [hquarter₁, hquarter₂]
      try rw [mul_add]
      try ac_rfl
  · intro j hj hne
    simp [hne]
  · simp

lemma centeredControlKernel_bind_testObservedLaw {d : ℕ} (k : Fin d) (M u : ℝ)
    (hM : 0 < M) (hu : |u| ≤ M / 2) :
    centeredControlKernel k M ∘ₘ testObservedLaw k (M / 2) u =
      (centeredOneCellLaw k M u hM hu).observedLaw := by
  rw [centeredControlKernel_bind_testObservedLaw_explicit k M u hM hu,
    centeredOneCellLaw_observedLaw k M u hM hu]

lemma centeredOneCellLaw_endpoint_support {d : ℕ} (k : Fin d) (M u : ℝ)
    (hM : 0 < M) (hu : |u| ≤ M / 2) (hM1 : M = 1) :
    (centeredOneCellLaw k M u hM hu).fullLaw
        {z | z.y0 ∉ ({-1 / 2, 1 / 2} : Set ℝ) ∨
          z.y1 ∉ ({-1 / 2, 1 / 2} : Set ℝ)} = 0 ∧
      ∀ a j, 0 < (centeredOneCellLaw k M u hM hu).cellMass j →
        (centeredOneCellLaw k M u hM hu).outcomeLaw a j
          (({-1 / 2, 1 / 2} : Set ℝ)ᶜ) = 0 := by
  subst M
  let p : Fin d → ℝ := fun j => if j = k then 1 else 0
  let pi : Fin d → ℝ := fun _ => 1 / 2
  let mu : Bool → Fin d → ℝ := fun a _ => if a then 1 / 2 + u / 1 else 1 / 2
  have hp : ∀ j, p j ∈ Icc (0 : ℝ) 1 := by
    intro j; simp only [p]; split_ifs <;> norm_num
  have hpi : ∀ j, pi j ∈ Icc (0 : ℝ) 1 := by intro; norm_num [pi]
  have hpi0 : ∀ j, 0 < pi j := by intro; simp [pi]
  have hpi1 : ∀ j, pi j < 1 := by intro; norm_num [pi]
  have hmu : ∀ a j, mu a j ∈ Icc (0 : ℝ) 1 := by
    intro a j
    cases a
    · norm_num [mu]
    · simp only [mu, ite_true]
      rw [abs_le] at hu
      constructor <;> norm_num at hu ⊢ <;> linarith
  have hpsum : ∑ j, p j = 1 := by classical simp [p]
  change (prescribedFiniteRealLaw 1 p pi mu hp hpi hpi0 hpi1 hmu hpsum).fullLaw
        {z | z.y0 ∉ ({-1 / 2, 1 / 2} : Set ℝ) ∨
          z.y1 ∉ ({-1 / 2, 1 / 2} : Set ℝ)} = 0 ∧
      ∀ a j, 0 < (prescribedFiniteRealLaw 1 p pi mu hp hpi hpi0 hpi1 hmu hpsum).cellMass j →
        (prescribedFiniteRealLaw 1 p pi mu hp hpi hpi0 hpi1 hmu hpsum).outcomeLaw a j
          (({-1 / 2, 1 / 2} : Set ℝ)ᶜ) = 0
  constructor
  · convert prescribedFiniteRealLaw_fullSupport 1 p pi mu hp hpi hpi0 hpi1 hmu hpsum using 1 <;>
      norm_num
  · intro a j hj
    convert prescribedFiniteRealLaw_support 1 p pi mu hp hpi hpi0 hpi1 hmu hpsum a j using 1 <;>
      norm_num

/-- Applying the centered channel independently to the old parametric product
experiment gives the centered prescribed product law. -/
lemma centeredOneCell_productLaw_eq_bind {d n : ℕ} (k : Fin d) (M u : ℝ)
    (hM : 0 < M) (hu : |u| ≤ M / 2) :
    DiscreteAteHeterogeneityFrontier.productLaw n
        (centeredOneCellLaw k M u hM hu) =
      Causalean.Stat.finProductKernel n (centeredControlKernel k M) ∘ₘ
        Measure.pi (fun _ : Fin n => testObservedLaw k (M / 2) u) := by
  letI : IsProbabilityMeasure (testObservedLaw k (M / 2) u) :=
    testObservedLaw_prob k (by positivity) hu
  rw [Causalean.Stat.finProductKernel_comp_pi]
  change Measure.pi (fun _ : Fin n =>
      (centeredOneCellLaw k M u hM hu).observedLaw) =
    Measure.pi (fun _ : Fin n =>
      centeredControlKernel k M ∘ₘ testObservedLaw k (M / 2) u)
  congr 1
  funext i
  exact (centeredControlKernel_bind_testObservedLaw k M u hM hu).symm

/-- Total variation contracts when both parametric product experiments pass
through the common centered channel. -/
lemma centeredOneCell_product_tv_le {d n : ℕ} (k : Fin d) (M u₀ u₁ : ℝ)
    (hM : 0 < M) (hu₀ : |u₀| ≤ M / 2) (hu₁ : |u₁| ≤ M / 2) :
    Causalean.Stat.tvDist
        (DiscreteAteHeterogeneityFrontier.productLaw n
          (centeredOneCellLaw k M u₀ hM hu₀))
        (DiscreteAteHeterogeneityFrontier.productLaw n
          (centeredOneCellLaw k M u₁ hM hu₁)) ≤
      Causalean.Stat.tvDist
        (Measure.pi (fun _ : Fin n => testObservedLaw k (M / 2) u₀))
        (Measure.pi (fun _ : Fin n => testObservedLaw k (M / 2) u₁)) := by
  letI : IsProbabilityMeasure (testObservedLaw k (M / 2) u₀) :=
    testObservedLaw_prob k (by positivity) hu₀
  letI : IsProbabilityMeasure (testObservedLaw k (M / 2) u₁) :=
    testObservedLaw_prob k (by positivity) hu₁
  rw [centeredOneCell_productLaw_eq_bind k M u₀ hM hu₀,
    centeredOneCell_productLaw_eq_bind k M u₁ hM hu₁]
  exact Causalean.Stat.tvDist_bind_le _ _ _

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

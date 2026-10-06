module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.BoundedRisk

/-! Zero-mass padding for the finite Zeng experiment. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- For [the specified inputs and assumptions](hyp:r,d,h,z), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def padZengRecord {r d : ℕ} (h : r ≤ d) (z : ZengRecord r) : ZengRecord d :=
  (Fin.castLE h z.1, z.2.1, z.2.2)

/-- For [the specified inputs and assumptions](hyp:r,d,h,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def padZengLaw {r d : ℕ} (h : r ≤ d) (P : ZengLaw r) : ZengLaw d :=
  ⟨P.1.map (padZengRecord h), by
    letI : IsProbabilityMeasure P.1 := P.2
    exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable⟩

/-- Given [the specified inputs and assumptions](hyp:r,d,h,P,x), [the stated mathematical conclusion holds](goal). -/
lemma padZengLaw_category_castLE {r d : ℕ} (h : r ≤ d)
    (P : ZengLaw r) (x : Fin r) :
    zengCategory (padZengLaw h P) (Fin.castLE h x) = zengCategory P x := by
  rw [zengCategory, zengCategory, Measure.real, padZengLaw,
    Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  apply congrArg ENNReal.toReal
  congr 1
  ext z
  exact Fin.castLE_injective h |>.eq_iff

/-- Given [the specified inputs and assumptions](hyp:r,d,h,P,x,a), [the stated mathematical conclusion holds](goal). -/
lemma padZengLaw_arm_castLE {r d : ℕ} (h : r ≤ d)
    (P : ZengLaw r) (x : Fin r) (a : Bool) :
    zengArm (padZengLaw h P) (Fin.castLE h x) a = zengArm P x a := by
  rw [zengArm, zengArm, Measure.real, padZengLaw,
    Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  apply congrArg ENNReal.toReal
  congr 1
  ext z
  simp [padZengRecord, Fin.castLE_injective h |>.eq_iff]

/-- Given [the specified inputs and assumptions](hyp:r,d,h,P,x,a), [the stated mathematical conclusion holds](goal). -/
lemma padZengLaw_success_castLE {r d : ℕ} (h : r ≤ d)
    (P : ZengLaw r) (x : Fin r) (a : Bool) :
    (padZengLaw h P).1.real
        {z | z.1 = Fin.castLE h x ∧ z.2.1 = a ∧ z.2.2 = true} =
      P.1.real {z | z.1 = x ∧ z.2.1 = a ∧ z.2.2 = true} := by
  rw [Measure.real, padZengLaw,
    Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  apply congrArg ENNReal.toReal
  congr 1
  ext z
  simp [padZengRecord, Fin.castLE_injective h |>.eq_iff]

/-- Given [the specified inputs and assumptions](hyp:r,d,h,P,x,hx), [the stated mathematical conclusion holds](goal). -/
lemma padZengLaw_category_new {r d : ℕ} (h : r ≤ d)
    (P : ZengLaw r) (x : Fin d) (hx : r ≤ x) :
    zengCategory (padZengLaw h P) x = 0 := by
  rw [zengCategory, Measure.real, padZengLaw,
    Measure.map_apply (measurable_of_finite _) MeasurableSet.of_discrete]
  have hpre : padZengRecord h ⁻¹' {z : ZengRecord d | z.1 = x} = ∅ := by
    ext z
    constructor
    · intro hz
      have hv := congrArg (fun w : Fin d => (w : ℕ)) hz
      simp [padZengRecord] at hv
      omega
    · simp
  rw [hpre]
  simp

/-- Given [the specified inputs and assumptions](hyp:r,d,q,h,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma padZengLaw_mem_class {r d : ℕ} {q : ℝ} (h : r ≤ d)
    (P : ZengLaw r) (hP : P ∈ zengDiscreteClass r q) :
    padZengLaw h P ∈ zengDiscreteClass d q := by
  refine ⟨hP.1, hP.2.1, hP.2.2.1.trans h, ?_⟩
  intro x hx
  by_cases hxold : (x : ℕ) < r
  · let x₀ : Fin r := ⟨x, hxold⟩
    have he : Fin.castLE h x₀ = x := Fin.ext (by rfl)
    rw [← he, padZengLaw_category_castLE] at hx
    rw [← he, padZengLaw_category_castLE, padZengLaw_arm_castLE]
    exact hP.2.2.2 x₀ hx
  · rw [padZengLaw_category_new h P x (Nat.le_of_not_gt hxold)] at hx
    linarith

private lemma sum_fin_pad {r d : ℕ} (h : r ≤ d) (f : Fin r → ℝ) :
    (∑ x : Fin d, if hx : (x : ℕ) < r then f ⟨x, hx⟩ else 0) = ∑ x : Fin r, f x := by
  classical
  calc
    _ = ∑ j ∈ Finset.range d, if hj : j < r then f ⟨j, hj⟩ else 0 := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj]
    _ = ∑ j ∈ Finset.range r, if hj : j < r then f ⟨j, hj⟩ else 0 := by
      exact (Finset.sum_subset (Finset.range_mono h)
        (by intro j hj hnot; simp [Finset.mem_range] at hnot; simp [hnot])).symm
    _ = _ := by rw [Finset.sum_fin_eq_sum_range]

/-- Given [the specified inputs and assumptions](hyp:r,d,h,P), [the stated mathematical conclusion holds](goal). -/
lemma padZengLaw_ate {r d : ℕ} (h : r ≤ d) (P : ZengLaw r) :
    zengATE (padZengLaw h P) = zengATE P := by
  unfold zengATE
  rw [← sum_fin_pad h (fun x => if hx : 0 < zengCategory P x then
    zengCategory P x * (zengMean P x true hx - zengMean P x false hx) else 0)]
  apply Fintype.sum_congr
  intro x
  by_cases hxold : (x : ℕ) < r
  · let x₀ : Fin r := ⟨x, hxold⟩
    have he : Fin.castLE h x₀ = x := Fin.ext (by rfl)
    simp only [hxold, dite_true]
    have hterm :
        (if hp : 0 < zengCategory (padZengLaw h P) (Fin.castLE h x₀) then
          zengCategory (padZengLaw h P) (Fin.castLE h x₀) *
            (zengMean (padZengLaw h P) (Fin.castLE h x₀) true hp -
              zengMean (padZengLaw h P) (Fin.castLE h x₀) false hp) else 0) =
        if hp : 0 < zengCategory P x₀ then
          zengCategory P x₀ *
            (zengMean P x₀ true hp - zengMean P x₀ false hp) else 0 := by
      by_cases hp : 0 < zengCategory P x₀
      · have hppad : 0 < zengCategory (padZengLaw h P) (Fin.castLE h x₀) := by
          rwa [padZengLaw_category_castLE]
        rw [dif_pos hp, dif_pos hppad, padZengLaw_category_castLE]
        unfold zengMean
        rw [padZengLaw_arm_castLE, padZengLaw_arm_castLE,
          padZengLaw_success_castLE, padZengLaw_success_castLE]
      · have hppad : ¬0 < zengCategory (padZengLaw h P) (Fin.castLE h x₀) := by
          rwa [padZengLaw_category_castLE]
        rw [dif_neg hp, dif_neg hppad]
    simpa only [he] using hterm
  · simp only [hxold, dite_false]
    have hz := padZengLaw_category_new h P x (Nat.le_of_not_gt hxold)
    rw [dif_neg (by rw [hz]; linarith)]

/-- For [the specified inputs and assumptions](hyp:n,r,d,h,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def padZengSample {n r d : ℕ} (h : r ≤ d)
    (s : Fin n → ZengRecord r) : Fin n → ZengRecord d :=
  fun i => padZengRecord h (s i)

/-- Given [the specified inputs and assumptions](hyp:n,r,d,h,P), [the stated mathematical conclusion holds](goal). -/
lemma padZengLaw_sample_map {n r d : ℕ} (h : r ≤ d) (P : ZengLaw r) :
    (zengSampleLaw n P).map (padZengSample h) =
      zengSampleLaw n (padZengLaw h P) := by
  unfold zengSampleLaw padZengSample
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsProbabilityMeasure ((padZengLaw h P).1) := (padZengLaw h P).2
  rw [Measure.pi_map_pi (fun _ => (measurable_of_finite _).aemeasurable)]
  congr 1

/-- For [the specified inputs and assumptions](hyp:n,r,d,h,T), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def pullbackZengEstimator {n r d : ℕ} (h : r ≤ d)
    (T : ZengEstimator n d) : ZengEstimator n r := by
  letI : IsMarkovKernel T.1 := T.2.1
  let K := T.1.comap (padZengSample h) (measurable_of_finite _)
  have hK : IsMarkovKernel K := Kernel.IsMarkovKernel.comap T.1 (measurable_of_finite _)
  refine ⟨K, hK, ?_⟩
  intro s
  rw [Kernel.comap_apply]
  exact T.2.2 _

/-- Given [the specified inputs and assumptions](hyp:n,r,d,h,T,P), [the stated mathematical conclusion holds](goal). -/
lemma zengSquaredRisk_pullback_padding {n r d : ℕ} (h : r ≤ d)
    (T : ZengEstimator n d) (P : ZengLaw r) :
    zengSquaredRisk (pullbackZengEstimator h T) P =
      zengSquaredRisk T (padZengLaw h P) := by
  unfold zengSquaredRisk
  rw [padZengLaw_ate]
  let g : (Fin n → ZengRecord d) → ℝ := fun s =>
    ∫ t, (t - zengATE P) ^ 2 ∂(T.1 s)
  have hg : Measurable g := by fun_prop
  have hi := MeasureTheory.integral_map
    (μ := zengSampleLaw n P)
    (measurable_of_finite (padZengSample h)).aemeasurable
    hg.aestronglyMeasurable
  rw [padZengLaw_sample_map h P] at hi
  simpa [g, pullbackZengEstimator, Kernel.comap_apply] using hi.symm

-- @node: zengMinimaxRisk_mono_dimension
/-- Given [the specified inputs and assumptions](hyp:n,r,d,hr,h,q), [the stated mathematical conclusion holds](goal). -/
lemma zengMinimaxRisk_mono_dimension {n r d : ℕ} (hr : 1 ≤ r) (h : r ≤ d)
    (q : ℝ) : zengMinimaxRisk n r q ≤ zengMinimaxRisk n d q := by
  let T₀ : ZengEstimator n d :=
    ⟨Kernel.const _ (Measure.dirac 0), inferInstance, by intro s; simp [Kernel.const_apply]⟩
  letI : Nonempty (ZengEstimator n d) := ⟨T₀⟩
  unfold zengMinimaxRisk
  apply Causalean.Stat.minimaxValue_le_minimaxValue
    (Causalean.Stat.bddBelow_range_worstCaseRisk fun _ _ => by
      unfold zengSquaredRisk
      positivity)
  intro T
  refine ⟨pullbackZengEstimator h T, ?_⟩
  change Causalean.Stat.worstCaseRiskReal
      (fun (_ : Unit) (P : {P : ZengLaw r // P ∈ zengDiscreteClass r q}) =>
        zengSquaredRisk (pullbackZengEstimator h T) P.1) () ≤
    Causalean.Stat.worstCaseRiskReal
      (fun (_ : Unit) (P : {P : ZengLaw d // P ∈ zengDiscreteClass d q}) =>
        zengSquaredRisk T P.1) ()
  apply Causalean.Stat.worstCaseRisk_mono_class_of_nonneg
    (fun P : {P : ZengLaw r // P ∈ zengDiscreteClass r q} =>
      ⟨padZengLaw h P.1, padZengLaw_mem_class h P.1 P.2⟩)
  · refine ⟨4, ?_⟩
    rintro y ⟨Q, rfl⟩
    exact (zeng_squaredRisk_bounds q T Q.1 Q.2).2
  · intro Q
    exact (zeng_squaredRisk_bounds q T Q.1 Q.2).1
  · rintro ⟨P, hP⟩
    exact (zengSquaredRisk_pullback_padding h T P).le

end CausalSmith.Stat.MarRareqLogfrontier

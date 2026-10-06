module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.PermutationExperiment

/-! Construction and information bounds for the Gaussian--Poisson permutation lower bound. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

abbrev permutationAtomicModel {p n : ℕ} (hp : 0 < p) (r₀ : Fin n)
    (π : Equiv.Perm (Fin p)) (a : ℝ) (ha : 0 < a) :
    AtomicCountModel p p (PermutationOmega p n)
      (permutationExperimentMeasure π a) where
  p_pos := hp
  M_pos := hp
  A := 0
  η := permutationEta π a
  Ωc := fun _ => 1
  α := fun _ => a
  t := π
  ξ := fun e ω => permutationZ e r₀ ω - permutationEta π a e
  S := fun e ω => permutationS e r₀ ω
  X := fun e ω => permutationX e r₀ ω
  acyclic := by
    constructor
    · simp
    · intro i h
      have hempty : ∀ {x y : Fin p},
          Relation.TransGen (fun _ _ => False) x y → False := by
        intro x y hxy
        induction hxy with
        | single h => exact h
        | tail _ h _ => exact h
      apply hempty
      simpa using h
  atomic := by
    intro m
    funext i
    simp
  nonvanishing := fun _ => ha.ne'
  gaussian := by
    intro e
    exact ⟨Matrix.PosDef.one,
      permutationExperiment_disturbance_hasLaw (n := n) π a e r₀⟩
  poisson := by
    intro e _
    have hlatent (ω : PermutationOmega p n) :
        latentState (0 : Matrix (Fin p) (Fin p) ℝ) (permutationEta π a)
          (fun e ω => permutationZ e r₀ ω - permutationEta π a e) e ω =
          permutationZ e r₀ ω := by
      ext i
      simp [latentState, totalEffect]
    simpa only [hlatent] using
      (permutationExperiment_poisson (n := n) π a e r₀)

lemma permutation_bounded_model_obsLaw {p n : ℕ} {ℓ v a : ℝ}
    (hp : 0 < p) (hn : 0 < n) (hℓ : 0 < ℓ)
    (hℓle : ℓ ≤ Real.exp (1 / 2)) (hv : 0 < v) (ha : 0 < a)
    (hav : v0 a ≤ v) (π : Equiv.Perm (Fin p)) (r₀ : Fin n) :
    let μ := permutationExperimentMeasure (n := n) π a
    let 𝒬 := permutationBoundedMomentClass π hp hn ha.le hℓ hℓle hv hav
    let 𝔐 := permutationAtomicModel hp r₀ π a ha
    ∀ e r, μ.map (fun ω => (𝒬.S e r ω, 𝒬.X e r ω)) =
      obsLaw μ 𝔐 e := by
  dsimp
  intro e r
  change (permutationExperimentMeasure π a).map
      (fun ω => (permutationS e r ω, permutationX e r ω)) =
    (permutationExperimentMeasure π a).map
      (fun ω => (permutationS e r₀ ω, permutationX e r₀ ω))
  exact ((permutationExperiment_iid (n := n) π a e).2 r r₀).map_eq

lemma klDiv_pi_finite_toReal_sum {α : Type*} [MeasurableSpace α]
    (k : ℕ) (P Q : Fin k → Measure α)
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)]
    (hfin : ∀ i, InformationTheory.klDiv (P i) (Q i) ≠ ⊤) :
    InformationTheory.klDiv (Measure.pi P) (Measure.pi Q) ≠ ⊤ ∧
      (InformationTheory.klDiv (Measure.pi P) (Measure.pi Q)).toReal =
        ∑ i, (InformationTheory.klDiv (P i) (Q i)).toReal := by
  induction k with
  | zero =>
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
      simp
  | succ k ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) 0
      let Pt : Fin k → Measure α := fun i => P (Fin.succAbove 0 i)
      let Qt : Fin k → Measure α := fun i => Q (Fin.succAbove 0 i)
      have htail := ih Pt Qt (fun i => hfin (Fin.succAbove 0 i))
      obtain ⟨hac0, hint0⟩ := InformationTheory.klDiv_ne_top_iff.mp (hfin 0)
      obtain ⟨hact, hintt⟩ := InformationTheory.klDiv_ne_top_iff.mp htail.1
      have hmapP : Measure.map e (Measure.pi P) =
          (P 0).prod (Measure.pi Pt) := by
        simpa [e, Pt] using (measurePreserving_piFinSuccAbove P 0).map_eq
      have hmapQ : Measure.map e (Measure.pi Q) =
          (Q 0).prod (Measure.pi Qt) := by
        simpa [e, Qt] using (measurePreserving_piFinSuccAbove Q 0).map_eq
      have hprodFin : InformationTheory.klDiv
          ((P 0).prod (Measure.pi Pt)) ((Q 0).prod (Measure.pi Qt)) ≠ ⊤ := by
        apply InformationTheory.klDiv_ne_top_iff.mpr
        exact ⟨hac0.prod hact,
          Causalean.Mathlib.InformationTheory.ProductKL.llr_prod_integrable
            (P 0) (Q 0) (Measure.pi Pt) (Measure.pi Qt)
            hac0 hact hint0 hintt⟩
      have hrelab := Causalean.Mathlib.InformationTheory.Measure.klDiv_map_measurableEmbedding
          (μ := Measure.pi P) (ν := Measure.pi Q) e.measurableEmbedding
      rw [hmapP, hmapQ] at hrelab
      have horigFin : InformationTheory.klDiv
          (Measure.pi P) (Measure.pi Q) ≠ ⊤ := by
        rw [← hrelab]
        exact hprodFin
      refine ⟨horigFin, ?_⟩
      rw [← hrelab]
      rw [Causalean.Mathlib.InformationTheory.ProductKL.klDiv_prod_toReal_add
        (P 0) (Q 0) (Measure.pi Pt) (Measure.pi Qt)
        hac0 hact hint0 hintt, htail.2]
      rw [Fin.sum_univ_succAbove _ 0]

lemma klDiv_pi_fintype_finite_toReal_sum {I α : Type*}
    [Fintype I] [MeasurableSpace α] (P Q : I → Measure α)
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)]
    (hfin : ∀ i, InformationTheory.klDiv (P i) (Q i) ≠ ⊤) :
    InformationTheory.klDiv (Measure.pi P) (Measure.pi Q) ≠ ⊤ ∧
      (InformationTheory.klDiv (Measure.pi P) (Measure.pi Q)).toReal =
        ∑ i, (InformationTheory.klDiv (P i) (Q i)).toReal := by
  let equiv := Fintype.equivFin I
  let P' : Fin (Fintype.card I) → Measure α := fun i => P (equiv.symm i)
  let Q' : Fin (Fintype.card I) → Measure α := fun i => Q (equiv.symm i)
  have hfin' : ∀ i, InformationTheory.klDiv (P' i) (Q' i) ≠ ⊤ :=
    fun i => hfin (equiv.symm i)
  have hcore := klDiv_pi_finite_toReal_sum _ P' Q' hfin'
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card I) => α) equiv
  have hmapP : Measure.map E (Measure.pi P) = Measure.pi P' := by
    simpa [E, P'] using Measure.pi_map_piCongrLeft equiv P'
  have hmapQ : Measure.map E (Measure.pi Q) = Measure.pi Q' := by
    simpa [E, Q'] using Measure.pi_map_piCongrLeft equiv Q'
  have hrelab := Causalean.Mathlib.InformationTheory.Measure.klDiv_map_measurableEmbedding
    (μ := Measure.pi P) (ν := Measure.pi Q) E.measurableEmbedding
  rw [hmapP, hmapQ] at hrelab
  constructor
  · rw [← hrelab]
    exact hcore.1
  · rw [← hrelab, hcore.2]
    exact equiv.symm.sum_comp
      (fun i => (InformationTheory.klDiv (P i) (Q i)).toReal)

lemma shiftedGaussianLaw_permutationEta_kl {p : ℕ}
    (π : Equiv.Perm (Fin p)) (a : ℝ) (m : Fin p) :
    InformationTheory.klDiv
        (shiftedGaussianLaw (permutationEta π a m.succ))
        (shiftedGaussianLaw (permutationEta π a 0)) =
      ENNReal.ofReal (a ^ 2 / 2) := by
  cases p with
  | zero => exact Fin.elim0 m
  | succ p =>
    let j := π m
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℝ) j
    let R : Measure (Fin p → ℝ) :=
      Measure.pi (fun _ : Fin p => gaussianReal 0 1)
    have hmapAlt : Measure.map e
        (Measure.pi (fun i : Fin (p + 1) =>
          gaussianReal (permutationEta π a m.succ i) 1)) =
        (gaussianReal a 1).prod R := by
      rw [(measurePreserving_piFinSuccAbove
        (fun i : Fin (p + 1) => gaussianReal (permutationEta π a m.succ i) 1) j).map_eq]
      congr 2
      · simp [j]
      · congr 1
        funext k
        have hne : j.succAbove k ≠ j := Fin.succAbove_ne j k
        simp [j, Pi.single_apply, hne]
    have hmapZero : Measure.map e
        (Measure.pi (fun i : Fin (p + 1) =>
          gaussianReal (permutationEta π a 0 i) 1)) =
        (gaussianReal 0 1).prod R := by
      rw [(measurePreserving_piFinSuccAbove
        (fun i : Fin (p + 1) => gaussianReal (permutationEta π a 0 i) 1) j).map_eq]
      simp [R]
    rw [shiftedGaussianLaw_eq_pi, shiftedGaussianLaw_eq_pi]
    have hrelab := Causalean.Mathlib.InformationTheory.Measure.klDiv_map_measurableEmbedding
      (μ := Measure.pi (fun i : Fin (p + 1) =>
        gaussianReal (permutationEta π a m.succ i) 1))
      (ν := Measure.pi (fun i : Fin (p + 1) =>
        gaussianReal (permutationEta π a 0 i) 1)) e.measurableEmbedding
    rw [hmapAlt, hmapZero] at hrelab
    rw [← hrelab, ← Measure.compProd_const, ← Measure.compProd_const,
      InformationTheory.klDiv_compProd_left]
    simpa using Causalean.Mathlib.InformationTheory.gaussianKL_eq a 0
      (by norm_num : (0 : NNReal) < 1)

lemma permutationExperiment_kl_reference {p n : ℕ}
    (π : Equiv.Perm (Fin p)) (a : ℝ) (ha : 0 ≤ a) :
    InformationTheory.klDiv
        (permutationExperimentMeasure (n := n) π a)
        (permutationExperimentMeasure (n := n) π 0) ≤
      ENNReal.ofReal ((n : ℝ) * p * a ^ 2 / 2) := by
  classical
  let P : Fin (p + 1) × Fin n → Measure (PermutationCell p) :=
    fun er => permutationCellLaw (permutationEta π a er.1)
  let Q : Fin (p + 1) × Fin n → Measure (PermutationCell p) :=
    fun er => permutationCellLaw (permutationEta π 0 er.1)
  have hcell (e : Fin (p + 1)) (r : Fin n) :
      InformationTheory.klDiv (P (e, r)) (Q (e, r)) =
        Fin.cases 0 (fun _ => ENNReal.ofReal (a ^ 2 / 2)) e := by
    refine Fin.cases ?_ (fun m => ?_) e
    · simp [P, Q]
    · rw [show P (m.succ, r) =
          permutationCellLaw (permutationEta π a m.succ) by rfl,
        show Q (m.succ, r) =
          permutationCellLaw (permutationEta π 0 m.succ) by rfl,
        permutationCellLaw_kl_eq,
        show permutationEta π 0 m.succ = permutationEta π a 0 by simp,
        shiftedGaussianLaw_permutationEta_kl]
      rfl
  have hfin (er : Fin (p + 1) × Fin n) :
      InformationTheory.klDiv (P er) (Q er) ≠ ⊤ := by
    rw [hcell er.1 er.2]
    cases er.1 using Fin.cases <;> simp
  have hpi := klDiv_pi_fintype_finite_toReal_sum P Q hfin
  rw [permutationExperimentMeasure_eq_pi,
    permutationExperimentMeasure_eq_pi]
  have hsum :
      ∑ er : Fin (p + 1) × Fin n,
          (InformationTheory.klDiv (P er) (Q er)).toReal =
        (n : ℝ) * p * a ^ 2 / 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [hcell]
    rw [Fin.sum_univ_succ]
    simp [ENNReal.toReal_ofReal (by positivity : 0 ≤ a ^ 2 / 2)]
    ring
  apply (ENNReal.toReal_le_toReal hpi.1 ENNReal.ofReal_ne_top).mp
  rw [hpi.2, hsum, ENNReal.toReal_ofReal]
  positivity

lemma permutationExperiment_target_variances {p n : ℕ}
    (π : Equiv.Perm (Fin p)) (a v : ℝ) (ha : 0 ≤ a) (hav : v0 a ≤ v) :
    (∀ m (r : Fin n), variance (fun ω =>
        firstFactorial (permutationX m.succ r ω)
          (permutationS m.succ r ω) (π m))
        (permutationExperimentMeasure π a) =
      Real.exp (a + 1 / 2) +
        (Real.exp 1 - 1) * Real.exp (2 * a + 1)) ∧
    (∀ m (r : Fin n), variance (fun ω =>
        secondFactorial (permutationX m.succ r ω)
          (permutationS m.succ r ω) (π m))
        (permutationExperimentMeasure π a) =
      4 * Real.exp (3 * a + 9 / 2) + 2 * Real.exp (2 * a + 2) +
        Real.exp (4 * a + 8) - Real.exp (4 * a + 4)) := by
  have hvar := random_offset_variance
    (permutationExperimentMeasure (n := n) π a)
    permutationZ permutationS permutationX v
    (permutationExperiment_poisson π a)
    (permutationExperiment_iid π a)
    (permutationExperiment_exog π a)
    (permutationExperiment_varBound π ha hav)
  constructor
  · intro m r
    rw [hvar.2.2.1]
    have hZ := permutationExperiment_Z_coord_law
      (n := n) π a m.succ r (π m)
    have hmean : permutationEta π a m.succ (π m) = a := by simp
    have hV := variance_exp_of_gaussian_law _
      (fun ω => permutationZ m.succ r ω (π m)) _ 1 hZ
    rw [show variance (fun ω => Real.exp (permutationZ m.succ r ω (π m)))
          (permutationExperimentMeasure π a) =
        Real.exp (2 * a + 2) - Real.exp (a + 1 / 2) ^ 2 by
      rw [hmean] at hV
      norm_num at hV ⊢
      exact hV]
    rw [show (∫ ω, Real.exp (permutationZ m.succ r ω (π m))
          ∂permutationExperimentMeasure π a) = Real.exp (a + 1 / 2) by
      have h := integral_exp_of_gaussian_law _
        (fun ω => permutationZ m.succ r ω (π m)) _ 1 hZ
      rw [hmean] at h
      norm_num at h ⊢
      exact h]
    have hmass : (permutationExperimentMeasure (n := n) π a).real Set.univ = 1 := by
      simp [Measure.real_def]
    simp only [permutationS_apply, inv_one, integral_const, measure_univ,
      ENNReal.toReal_one, one_smul]
    rw [hmass]
    rw [show Real.exp (a + 1 / 2) ^ 2 = Real.exp (2 * a + 1) by
      rw [pow_two, ← Real.exp_add]; congr 1 <;> ring,
      show Real.exp (2 * a + 2) = Real.exp 1 * Real.exp (2 * a + 1) by
        rw [← Real.exp_add]; congr 1 <;> ring]
    ring

  · intro m r
    rw [hvar.2.2.2.1]
    have hZ := permutationExperiment_Z_coord_law
      (n := n) π a m.succ r (π m)
    have hmean : permutationEta π a m.succ (π m) = a := by simp
    rw [variance_exp_of_gaussian_law _
      (fun ω => permutationZ m.succ r ω (π m)) _ 2 hZ]
    have hi2 := integral_exp_of_gaussian_law _
      (fun ω => permutationZ m.succ r ω (π m)) _ 2 hZ
    have hi3 := integral_exp_of_gaussian_law _
      (fun ω => permutationZ m.succ r ω (π m)) _ 3 hZ
    rw [hmean] at hi2 hi3 ⊢
    rw [hi2, hi3]
    have hmass : (permutationExperimentMeasure (n := n) π a).real Set.univ = 1 := by
      simp [Measure.real_def]
    simp only [permutationS_apply, inv_one, integral_const, measure_univ,
      ENNReal.toReal_one, one_smul, one_pow]
    rw [hmass]
    norm_num
    rw [show Real.exp (a * 2 + 2) ^ 2 = Real.exp (4 * a + 4) by
      rw [pow_two, ← Real.exp_add]; congr 1 <;> ring]
    rw [show Real.exp (2 * a * 2 + 8) = Real.exp (4 * a + 8) by
          congr 1 <;> ring,
      show Real.exp (a * 3 + 9 / 2) = Real.exp (3 * a + 9 / 2) by
          congr 1 <;> ring,
      show Real.exp (a * 2 + 2) = Real.exp (2 * a + 2) by
          congr 1 <;> ring]
    ring

lemma obsSampleLaw_eq_map {p n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ℓ v : ℝ} (𝒬 : BoundedMomentClass p n ℓ v Ω μ) :
    obsSampleLaw μ 𝒬 = μ.map (fun ω =>
      (fun e r => 𝒬.S e r ω, fun e r => 𝒬.X e r ω)) := by
  rfl

lemma permutationExperimentMeasure_zero_eq {p n : ℕ}
    (π ρ : Equiv.Perm (Fin p)) :
    permutationExperimentMeasure (n := n) π 0 =
      permutationExperimentMeasure (n := n) ρ 0 := by
  rw [permutationExperimentMeasure_eq_pi, permutationExperimentMeasure_eq_pi]
  congr 1
  funext er
  congr 1
  cases er.1 using Fin.cases <;> simp


end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

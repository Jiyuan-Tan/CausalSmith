module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Witnesses
public import Causalean.Stat.Minimax.MinimaxValue
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Scope of Dorn's Theorem 1

The printed pointwise lower clause is obstructed by a known-regression
singleton family. The source upper clause is kept as a cited, explicit gate.
-/
@[expose] public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A fixed, known-regression Gaussian experiment on Dorn's cube. For [the stated inputs and conditions](hyp:d), [the `dornCanonicalLaw` object being defined](goal). -/
noncomputable def dornCanonicalLaw (d : ℕ) : Measure (Obs d) :=
  (((ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ • volume.restrict (dornCube d)).prod
    ((realBernoulli (1 / 2)).prod (gaussianReal 0 ⟨1, by norm_num⟩)))

/-- The canonical experiment has the stated uniform covariate law. [For the stated inputs and conditions](hyp:d), [the asserted conclusion holds](goal). -/
lemma dornCanonicalLaw_covariate (d : ℕ) :
    covariateLaw (dornCanonicalLaw d) =
      (ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ • volume.restrict (dornCube d) := by
  have hbern : IsProbabilityMeasure (realBernoulli (1 / 2)) := by
    apply isProbabilityMeasure_iff.mpr
    simp [realBernoulli]
    rw [show (1 : ℝ) - 2⁻¹ = 1 / 2 by norm_num]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    rw [one_div]
    calc
      (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = (2 : ℝ≥0∞)⁻¹ * 2 := by ring
      _ = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (realBernoulli (1 / 2)) := hbern
  letI : IsProbabilityMeasure (gaussianReal 0 ⟨1, by norm_num⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 ⟨1, by norm_num⟩
  haveI : IsProbabilityMeasure
      ((realBernoulli (1 / 2)).prod (gaussianReal 0 ⟨1, by norm_num⟩)) :=
    Measure.prod.instIsProbabilityMeasure _ _
  have huniv : ((realBernoulli (1 / 2)).prod
      (gaussianReal 0 ⟨1, by norm_num⟩)) Set.univ = 1 := measure_univ
  simp only [covariateLaw, dornCanonicalLaw, Measure.map_fst_prod, huniv, one_smul]

/-- The independent half-treated arm has constant selected propensity. [For the stated inputs and conditions](hyp:d), [the asserted conclusion holds](goal). -/
lemma dornCanonicalLaw_propensity_ae (d : ℕ)
    [IsProbabilityMeasure (dornCanonicalLaw d)] :
    ∀ᵐ x ∂covariateLaw (dornCanonicalLaw d),
      propensity (dornCanonicalLaw d) x = 1 / 2 := by
  let μx : Measure (Fin d → ℝ) :=
    (ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ • volume.restrict (dornCube d)
  let μa : Measure Bool := realBernoulli (1 / 2)
  let μy : Measure ℝ := gaussianReal 0 ⟨1, by norm_num⟩
  have hcube : IsProbabilityMeasure μx := by
    apply isProbabilityMeasure_iff.mpr
    have hvol : volume (dornCube d) = ENNReal.ofReal ((2 : ℝ) ^ d) := by
      rw [dornCube, Set.pi_univ_Icc, Real.volume_Icc_pi]
      simp [Finset.prod_const, ENNReal.ofReal_pow]
      norm_num
    simp only [μx, Measure.smul_apply, Measure.restrict_apply, MeasurableSet.univ,
      Set.univ_inter, hvol, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by positivity) (by simp)
  letI : IsProbabilityMeasure μx := hcube
  haveI : IsProbabilityMeasure μa := by
    apply isProbabilityMeasure_iff.mpr
    simp [μa, realBernoulli]
    rw [show (1 : ℝ) - 2⁻¹ = 1 / 2 by norm_num]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    rw [one_div]
    calc
      (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = (2 : ℝ≥0∞)⁻¹ * 2 := by ring
      _ = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  haveI : IsProbabilityMeasure μy := by
    dsimp [μy]
    exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 ⟨1, by norm_num⟩
  have hmap : (dornCanonicalLaw d).map (fun z : Obs d => (z.1, z.2.1)) =
      μx.prod μa := by
    change (μx.prod (μa.prod μy)).map (Prod.map id Prod.fst) = μx.prod μa
    rw [← Measure.map_prod_map μx (μa.prod μy) measurable_id measurable_fst]
    simp
  have hae := ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd
    (μ := dornCanonicalLaw d) (X := fun z : Obs d => z.1)
    (Y := fun z : Obs d => z.2.1) (by fun_prop)
    (κ := Kernel.const (Fin d → ℝ) μa) (by
      rw [hmap]
      change μx.prod μa = covariateLaw (dornCanonicalLaw d) ⊗ₘ
        Kernel.const (Fin d → ℝ) μa
      rw [dornCanonicalLaw_covariate]
      change μx.prod μa = μx ⊗ₘ Kernel.const (Fin d → ℝ) μa
      simp)
  filter_upwards [hae] with x hx
  have hx' := congrArg (fun ν : Measure Bool => ν {true}) hx
  change (condDistrib (fun z : Obs d => z.2.1) (fun z => z.1)
      (dornCanonicalLaw d) x {true}).toReal = 1 / 2
  rw [hx']
  norm_num [μa, realBernoulli, Kernel.const_apply]

/-- Both conditional response arms of the canonical experiment are standard Gaussian. [For the stated inputs and conditions](hyp:d), [the asserted conclusion holds](goal). -/
lemma dornCanonicalLaw_armKernel_ae (d : ℕ)
    [IsProbabilityMeasure (dornCanonicalLaw d)] :
    ∀ᵐ x ∂covariateLaw (dornCanonicalLaw d),
      ∀ a : Bool, armKernel (dornCanonicalLaw d) x a =
        gaussianReal 0 ⟨1, by norm_num⟩ := by
  let μx : Measure (Fin d → ℝ) :=
    (ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ • volume.restrict (dornCube d)
  let μa : Measure Bool := realBernoulli (1 / 2)
  let μy : Measure ℝ := gaussianReal 0 ⟨1, by norm_num⟩
  haveI : IsProbabilityMeasure μa := by
    apply isProbabilityMeasure_iff.mpr
    simp [μa, realBernoulli]
    rw [show (1 : ℝ) - 2⁻¹ = 1 / 2 by norm_num]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    rw [one_div]
    calc
      (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = (2 : ℝ≥0∞)⁻¹ * 2 := by ring
      _ = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  haveI : IsProbabilityMeasure μy :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 ⟨1, by norm_num⟩
  have hpair : (dornCanonicalLaw d).map
      (fun z : Obs d => (z.1, z.2.1)) = μx.prod μa := by
    change (μx.prod (μa.prod μy)).map (Prod.map id Prod.fst) = μx.prod μa
    rw [← Measure.map_prod_map μx (μa.prod μy) measurable_id measurable_fst]
    simp
  have hmap : (dornCanonicalLaw d).map
      (fun z : Obs d => ((z.1, z.2.1), z.2.2)) = (μx.prod μa).prod μy := by
    change (μx.prod (μa.prod μy)).map
      (fun z => ((z.1, z.2.1), z.2.2)) = _
    rw [← MeasurableEquiv.prodAssoc.map_measurableEquiv_injective.eq_iff]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have hf : (MeasurableEquiv.prodAssoc :
        ((Fin d → ℝ) × Bool) × ℝ ≃ᵐ (Fin d → ℝ) × Bool × ℝ) ∘
        (fun z : (Fin d → ℝ) × Bool × ℝ => ((z.1, z.2.1), z.2.2)) = id := by
      funext z
      rcases z with ⟨x, a, y⟩
      rfl
    rw [hf, Measure.map_id]
    exact (Measure.prodAssoc_prod (μ := μx) (ν := μa) (τ := μy)).symm
  have hae := ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd
    (μ := dornCanonicalLaw d) (X := fun z : Obs d => (z.1, z.2.1))
    (Y := fun z : Obs d => z.2.2) (by fun_prop)
    (κ := Kernel.const ((Fin d → ℝ) × Bool) μy) (by
      rw [hmap]
      change (μx.prod μa).prod μy =
        ((dornCanonicalLaw d).map (fun z : Obs d => (z.1, z.2.1))) ⊗ₘ
          Kernel.const ((Fin d → ℝ) × Bool) μy
      rw [hpair]
      simp)
  have hae' : ∀ᵐ xa ∂μx.prod μa,
      armKernel (dornCanonicalLaw d) xa.1 xa.2 = μy := by
    rw [← hpair]
    filter_upwards [hae] with xa hxa
    simpa [armKernel, Kernel.const_apply] using hxa
  have hae'' := Measure.ae_ae_of_ae_prod hae'
  rw [dornCanonicalLaw_covariate]
  filter_upwards [hae''] with x hx
  intro a
  have ha : μa {a} ≠ 0 := by
    cases a <;> norm_num [μa, realBernoulli]
  exact (ae_iff_of_countable.mp hx) a ha

/-- Pointwise miss probability, as an extended nonnegative risk. For [the stated inputs and conditions](hyp:𝔓,x₀,c,r,T,z), [the `dornPointwiseMissRisk` object being defined](goal). -/
noncomputable def dornPointwiseMissRisk {d n : ℕ}
    (𝔓 : Set (DornSourceLaw d)) (x₀ : Fin d → ℝ) (c r : ℝ)
    (T : {T : (Fin n → Obs d) → ℝ // Measurable T})
    (z : {z : DornSourceLaw d // z ∈ 𝔓}) : ℝ≥0∞ :=
  ENNReal.ofReal ((Measure.pi (fun _ : Fin n => z.1.1)).real
    {ω | c * r < |T.1 ω - z.1.2.1 x₀|})

/-- If the regression curve is known across a family, its pointwise
minimax miss probability vanishes for every positive threshold. [For the stated inputs and conditions](hyp:d,n,𝔓,μref,x₀,c,r,hc,hr,hμ), [the asserted conclusion holds](goal). -/
lemma knownRegression_minimax_miss_zero {d n : ℕ}
    (𝔓 : Set (DornSourceLaw d)) (μref : (Fin d → ℝ) → ℝ)
    (x₀ : Fin d → ℝ) (c r : ℝ) (hc : 0 < c) (hr : 0 < r)
    (hμ : ∀ z ∈ 𝔓, ∀ x, z.2.1 x = μref x) :
    Causalean.Stat.minimaxValueENNReal
      (dornPointwiseMissRisk (n := n) 𝔓 x₀ c r) = 0 := by
  unfold Causalean.Stat.minimaxValueENNReal Causalean.Stat.worstCaseRiskENNReal
  apply le_antisymm
  · let T₀ : {T : (Fin n → Obs d) → ℝ // Measurable T} :=
      ⟨fun _ => μref x₀, measurable_const⟩
    apply (iInf_le (fun T : {T : (Fin n → Obs d) → ℝ // Measurable T} =>
      ⨆ z : {z : DornSourceLaw d // z ∈ 𝔓},
        dornPointwiseMissRisk 𝔓 x₀ c r T z) T₀).trans
    apply iSup_le
    intro z
    have hz := hμ z.1 z.2 x₀
    have hcr : ¬ c * r < 0 := not_lt.mpr (le_of_lt (mul_pos hc hr))
    simp [dornPointwiseMissRisk, T₀, hz, hcr]
  · exact bot_le

/-- A constant half propensity has the global polynomial tail with coefficient
`2 ^ (γ - 1)` under any probability design. [For the stated inputs and conditions](hyp:α,μ,γ,hγ), [the asserted conclusion holds](goal). -/
lemma constantHalf_globalTailInequality {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (γ : ℝ) (hγ : 1 < γ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      μ.real {_x : α | (1 / 2 : ℝ) ≤ t} ≤
        (2 : ℝ) ^ (γ - 1) * t ^ (γ - 1) := by
  intro t ht
  by_cases h : (1 / 2 : ℝ) ≤ t
  · have hpow : (1 / 2 : ℝ) ^ (γ - 1) ≤ t ^ (γ - 1) :=
      Real.rpow_le_rpow (by norm_num) h (by linarith)
    have hcoeff : 0 ≤ (2 : ℝ) ^ (γ - 1) := Real.rpow_nonneg (by norm_num) _
    have hone : (2 : ℝ) ^ (γ - 1) * (1 / 2 : ℝ) ^ (γ - 1) = 1 := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)]
      norm_num
    have hbound : (1 : ℝ) ≤ (2 : ℝ) ^ (γ - 1) * t ^ (γ - 1) := by
      calc
        (1 : ℝ) = (2 : ℝ) ^ (γ - 1) * (1 / 2 : ℝ) ^ (γ - 1) := hone.symm
        _ ≤ (2 : ℝ) ^ (γ - 1) * t ^ (γ - 1) :=
          mul_le_mul_of_nonneg_left hpow hcoeff
    have huniv : {x : α | (1 / 2 : ℝ) ≤ t} = Set.univ := by
      ext x
      change ((1 / 2 : ℝ) ≤ t) ↔ True
      exact iff_true_intro h
    rw [huniv]
    simpa using hbound
  · have hzero : {x : α | (1 / 2 : ℝ) ≤ t} = ∅ := by
      ext x
      change ((1 / 2 : ℝ) ≤ t) ↔ False
      exact iff_false_intro h
    rw [hzero]
    simp only [measureReal_empty]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg ht.1 _)

/-- A Euclidean ball centered in Dorn's closed cube has positive volume in the cube. [For the stated inputs and conditions](hyp:d,x₀,hx₀,h,hh), [the asserted conclusion holds](goal). -/
lemma dornCube_ball2_volume_pos {d : ℕ} (x₀ : Fin d → ℝ)
    (hx₀ : x₀ ∈ dornCube d) {h : ℝ} (hh : 0 < h) :
    0 < volume (ball2 x₀ h ∩ dornCube d) := by
  have hclosure : dornCube d ⊆ closure (interior (dornCube d)) := by
    intro y hy
    change y ∈ closure (interior (Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1)))
    rw [interior_pi_set Set.finite_univ, closure_pi_set]
    intro i hi
    rw [closure_interior_Icc (by norm_num : (-1 : ℝ) ≠ 1)]
    exact (show y ∈ Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1) from hy) i hi
  let U : Set (Fin d → ℝ) := {x | (∑ i, (x i - x₀ i) ^ 2) < h ^ 2}
  have hUopen : IsOpen U := by
    dsimp [U]
    have hcont : Continuous (fun x : Fin d → ℝ => ∑ i, (x i - x₀ i) ^ 2) := by
      fun_prop
    exact isOpen_lt hcont continuous_const
  have hxU : x₀ ∈ U := by
    simp [U, sq_pos_of_pos hh]
  have hnonempty : (U ∩ interior (dornCube d)).Nonempty :=
    (mem_closure_iff.mp (hclosure hx₀)) U hUopen hxU
  have hopen : IsOpen (U ∩ interior (dornCube d)) :=
    hUopen.inter isOpen_interior
  have hpos : 0 < volume (U ∩ interior (dornCube d)) :=
    hopen.measure_pos volume hnonempty
  exact lt_of_lt_of_le hpos (measure_mono (by
    intro x hx
    change x ∈ U ∧ x ∈ interior (dornCube d) at hx
    change x ∈ ball2 x₀ h ∧ x ∈ dornCube d
    exact ⟨le_of_lt (show (∑ i, (x i - x₀ i) ^ 2) < h ^ 2 from hx.1),
      interior_subset hx.2⟩))

/-- The known zero regression has zero spatial variance under the canonical design. [For the stated inputs and conditions](hyp:d,M,hM), [the asserted conclusion holds](goal). -/
lemma dornCanonicalLaw_zeroVariance (d : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    (∫ x, ((fun _ : Fin d → ℝ => (0 : ℝ)) x -
      ∫ y, (fun _ : Fin d → ℝ => (0 : ℝ)) y ∂covariateLaw (dornCanonicalLaw d)) ^ 2
      ∂covariateLaw (dornCanonicalLaw d)) ≤ M := by
  simpa using hM

/-- The zero regression belongs to every positive-radius Dorn seminorm class. [For the stated inputs and conditions](hyp:d,β,L₀,hL₀), [the asserted conclusion holds](goal). -/
lemma dornZero_topDerivativeSeminorm (d : ℕ) (β L₀ : ℝ) (hL₀ : 0 ≤ L₀) :
    DornTopDerivativeSeminorm (d := d) β L₀ (fun _ => 0) := by
  unfold DornTopDerivativeSeminorm
  constructor
  · fun_prop
  · intro α hα f hf x hx y hy
    simp [Causalean.Mathlib.Analysis.Calculus.CubeExtension.coordJetOn]
    exact mul_nonneg hL₀ (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

-- @node: lem:arbitrary-family-lower-obstruction
/-- A known-regression family has zero pointwise minimax error. In particular,
the explicit uniform-design, half-treated, centered Gaussian singleton obeys
Dorn's per-law conditions and common A3, yet has zero minimax error. [For the stated inputs and conditions](hyp:d,hd,β,γ,L₀,hβ,hγ,hL₀), [the asserted conclusion holds](goal). -/
lemma arbitraryFamily_lower_obstruction (d : ℕ) (hd : 1 ≤ d)
    (β γ L₀ : ℝ) (hβ : 0 < β) (hγ : 1 < γ) (hL₀ : 0 < L₀) :
    (∀ (𝔓 : Set (DornSourceLaw d)) (μref : (Fin d → ℝ) → ℝ)
      (x₀ : Fin d → ℝ), 𝔓.Nonempty →
      (∀ z ∈ 𝔓, ∀ x, z.2.1 x = μref x) →
      ∀ (n : ℕ) (c r : ℝ), 0 < c → 0 < r →
        Causalean.Stat.minimaxValueENNReal
          (dornPointwiseMissRisk (n := n) 𝔓 x₀ c r) = 0) ∧
    (∃ q M C : ℝ, 3 < q ∧ 0 < M ∧ 0 < C ∧
      ∃ hP : IsProbabilityMeasure (dornCanonicalLaw d),
        @DornRemainingModel d β q M 1 C L₀ γ (dornCanonicalLaw d) hP
          (fun _ => 0) (fun _ => 0) (fun _ => 1 / 2) ∧
        DornA3OnOriginalClass
          ({(dornCanonicalLaw d, (fun _ => 0), (fun _ => 0),
            (fun _ => 1 / 2))} : Set (DornSourceLaw d)) ∧
        ∀ (n : ℕ) (c r : ℝ), 0 < c → 0 < r →
          Causalean.Stat.minimaxValueENNReal
            (dornPointwiseMissRisk (n := n)
              ({(dornCanonicalLaw d, (fun _ => 0), (fun _ => 0),
                (fun _ => 1 / 2))} : Set (DornSourceLaw d))
              (fun _ => 0) c r) = 0) := by
  constructor
  · intro 𝔓 μref x₀ _ hμ n c r hc hr
    exact knownRegression_minimax_miss_zero 𝔓 μref x₀ c r hc hr hμ
  · let P := dornCanonicalLaw d
    have hP : IsProbabilityMeasure P := by
      have hvol : volume (dornCube d) = ENNReal.ofReal ((2 : ℝ) ^ d) := by
        rw [dornCube, Set.pi_univ_Icc, Real.volume_Icc_pi]
        simp [Finset.prod_const, ENNReal.ofReal_pow]
        norm_num
      have hcube : IsProbabilityMeasure
          ((ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ • volume.restrict (dornCube d)) := by
        apply isProbabilityMeasure_iff.mpr
        simp only [Measure.smul_apply, Measure.restrict_apply, MeasurableSet.univ,
          Set.univ_inter, hvol, smul_eq_mul]
        exact ENNReal.inv_mul_cancel (by positivity) (by simp)
      haveI : IsProbabilityMeasure
          ((ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ • volume.restrict (dornCube d)) := hcube
      have hbern : IsProbabilityMeasure (realBernoulli (1 / 2)) := by
        apply isProbabilityMeasure_iff.mpr
        simp [realBernoulli]
        rw [show (1 : ℝ) - 2⁻¹ = 1 / 2 by norm_num]
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
        rw [one_div]
        calc
          (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = (2 : ℝ≥0∞)⁻¹ * 2 := by ring
          _ = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
      haveI : IsProbabilityMeasure (realBernoulli (1 / 2)) := hbern
      have hgauss : IsProbabilityMeasure (gaussianReal 0 ⟨1, by norm_num⟩) := by
        exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 ⟨1, by norm_num⟩
      haveI : IsProbabilityMeasure (gaussianReal 0 ⟨1, by norm_num⟩) := hgauss
      have hinner : IsProbabilityMeasure
          ((realBernoulli (1 / 2)).prod (gaussianReal 0 ⟨1, by norm_num⟩)) := by
        exact Measure.prod.instIsProbabilityMeasure _ _
      haveI : IsProbabilityMeasure
          ((realBernoulli (1 / 2)).prod (gaussianReal 0 ⟨1, by norm_num⟩)) := hinner
      dsimp [P, dornCanonicalLaw]
      infer_instance
    letI : IsProbabilityMeasure P := hP
    let μy : Measure ℝ := gaussianReal 0 ⟨1, by norm_num⟩
    haveI : IsProbabilityMeasure μy :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 ⟨1, by norm_num⟩
    have hInt : Integrable (fun y : ℝ => |y| ^ 4) μy := by
      have hm := ProbabilityTheory.memLp_id_gaussianReal' (μ := (0 : ℝ))
        (v := ⟨1, by norm_num⟩) 4 (by norm_num)
      simpa [μy, Real.norm_eq_abs] using hm.integrable_norm_pow' (p := 4)
    let M₀ : ℝ := max 1 |∫ y : ℝ, |y| ^ 4 ∂μy|
    have hM₀ : 1 ≤ M₀ := le_max_left _ _
    have hMomentBound : (∫ y : ℝ, |y| ^ 4 ∂μy) ≤ M₀ ^ 4 := by
      have hle : (∫ y : ℝ, |y| ^ 4 ∂μy) ≤ M₀ :=
        (le_abs_self _).trans (le_max_right _ _)
      have hpow : M₀ ≤ M₀ ^ 4 := by
        calc
          M₀ = M₀ ^ 1 := by ring
          _ ≤ M₀ ^ 4 := by
            simpa [Real.rpow_natCast] using
              (Real.rpow_le_rpow_of_exponent_le hM₀ (show (1 : ℝ) ≤ 4 by norm_num))
      exact hle.trans hpow
    have hWitness : ∃ q M C : ℝ, 3 < q ∧ 0 < M ∧ 0 < C ∧
        DornRemainingModel d β q M 1 C L₀ γ P
          (fun _ => 0) (fun _ => 0) (fun _ => 1 / 2) := by
      refine ⟨4, M₀, 2 ^ (γ - 1), by norm_num, by linarith,
        Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
      have hSelected : DornSelectedPropensity (dornCube d) P (fun _ => 1 / 2) := by
        refine ⟨hP, measurable_const, ?_, ?_⟩
        · intro x hx
          norm_num
        · filter_upwards [dornCanonicalLaw_propensity_ae d] with x hx
          exact ⟨hx.symm, by norm_num, by norm_num⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change covariateLaw P = _
        simpa [P] using dornCanonicalLaw_covariate d
      · exact hSelected.toA12
      · filter_upwards [dornCanonicalLaw_armKernel_ae d] with x hx
        rw [show armKernel P x true = μy by simpa [P, μy] using hx true]
        exact ⟨by simpa [Real.rpow_natCast] using hInt, by simpa [Real.rpow_natCast] using hMomentBound⟩
      · simpa [P] using dornCanonicalLaw_zeroVariance d M₀ (by linarith)
      · exact dornZero_topDerivativeSeminorm d β L₀ hL₀.le
      · exact dornZero_topDerivativeSeminorm d β L₀ hL₀.le
      · refine ⟨?_, ?_⟩
        · rcases hSelected with ⟨_, _, _, hae⟩
          filter_upwards [hae] with x hx
          exact hx.1
        · haveI : IsProbabilityMeasure (covariateLaw P) := by
            unfold covariateLaw
            exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
          exact constantHalf_globalTailInequality (covariateLaw P) γ hγ
      · filter_upwards [dornCanonicalLaw_armKernel_ae d] with x hx
        constructor <;> simpa [P] using hx _
    obtain ⟨q, M, C, hq, hM, hC, hModel⟩ := hWitness
    have hA3 : DornA3OnOriginalClass
        ({(P, (fun _ => 0), (fun _ => 0),
          (fun _ => 1 / 2))} : Set (DornSourceLaw d)) := by
      change DornA3 (dornCube d)
        ({(P, (fun _ => 0), (fun _ => 0),
          (fun _ => 1 / 2))} : Set (DornSourceLaw d))
      refine ⟨Set.singleton_nonempty _, ?_, ?_, 1, 1 / 2, 1,
        by norm_num, by norm_num, by norm_num, ?_⟩
      · intro z hz
        have hz' : z = (P, (fun _ => 0), (fun _ => 0),
            (fun _ => 1 / 2)) := Set.mem_singleton_iff.mp hz
        subst z
        rw [covariateLaw, hModel.1]
        have hvol : volume (dornCube d) = ENNReal.ofReal ((2 : ℝ) ^ d) := by
          rw [dornCube, Set.pi_univ_Icc, Real.volume_Icc_pi]
          simp [Finset.prod_const, ENNReal.ofReal_pow]
          norm_num
        have hcubeMeas : MeasurableSet (dornCube d) := by
          unfold dornCube
          exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
        rw [Measure.smul_apply, Measure.restrict_apply' hcubeMeas,
          Set.inter_self, hvol]
        simp only [smul_eq_mul]
        exact ENNReal.inv_mul_cancel (by positivity) (by simp)
      · intro z hz
        have hz' : z = (P, (fun _ => 0), (fun _ => 0),
            (fun _ => 1 / 2)) := Set.mem_singleton_iff.mp hz
        subst z
        refine ⟨hP, measurable_const, ?_, ?_⟩
        · intro x hx
          norm_num
        · obtain ⟨_, _, hae⟩ := hModel.2.1
          exact hae
      · intro z hz x₀ hx₀ h hh
        have hz' : z = (P, (fun _ => 0), (fun _ => 0),
            (fun _ => 1 / 2)) := Set.mem_singleton_iff.mp hz
        subst z
        have hball : (ball2 x₀ h ∩ dornCube d).Nonempty := by
          refine ⟨x₀, ?_, hx₀⟩
          simp [ball2, sq_nonneg]
        have hsup : sSup ((fun _ : Fin d → ℝ => (1 / 2 : ℝ)) ''
            (ball2 x₀ h ∩ dornCube d)) = 1 / 2 := by
          rw [hball.image_const]
          simp
        have hmeasure : 0 < (covariateLaw P).real (ball2 x₀ h) := by
          have hvol := dornCube_ball2_volume_pos x₀ hx₀ hh.1
          have hmass : 0 < (covariateLaw P) (ball2 x₀ h) := by
            rw [covariateLaw, hModel.1]
            have hcubeMeas : MeasurableSet (dornCube d) := by
              unfold dornCube
              exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
            rw [Measure.smul_apply, Measure.restrict_apply' hcubeMeas]
            exact ENNReal.mul_pos (by simp) (ne_of_gt hvol)
          haveI : IsProbabilityMeasure (covariateLaw P) := by
            unfold covariateLaw
            exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
          have hne : (covariateLaw P).real (ball2 x₀ h) ≠ 0 :=
            (measureReal_ne_zero_iff (measure_ne_top (covariateLaw P) _)).mpr
              (ne_of_gt hmass)
          exact lt_of_le_of_ne (measureReal_nonneg) (Ne.symm hne)
        simp only [hsup, one_mul]
        have hevent : {x | (1 / 2 : ℝ) ≥ 1 / 2} ∩ ball2 x₀ h =
            ball2 x₀ h := by simp
        rw [hevent, div_self (ne_of_gt hmeasure)]
        norm_num
    refine ⟨q, M, C, hq, hM, hC, hP, hModel, hA3, ?_⟩
    intro n c r hc hr
    apply knownRegression_minimax_miss_zero
      ({(P, (fun _ => 0), (fun _ => 0),
        (fun _ => 1 / 2))} : Set (DornSourceLaw d))
      (fun _ => 0) (fun _ => 0) c r hc hr
    intro z hz x
    have hz' : z = (P, (fun _ => 0), (fun _ => 0),
        (fun _ => 1 / 2)) := Set.mem_singleton_iff.mp hz
    subst z
    rfl

-- @node: lem:dorn-rate-scope
/-- Dorn's Theorem 1(ii) gives a no-log `L∞(P_X)` upper rate after the
source family, all common constants including gamma, and the selected
propensity representatives have been fixed. The source comparison is supplied
by the cited gate, including measurability of every displayed `L∞(P_X)`
exceedance event and hence its ordinary probability. The second conclusion gives the known-regression
obstruction to the printed lower clause, including its Gaussian witness. [For the stated inputs and conditions](hyp:d,hd,β,q,M,σ,C,L₀,hβ,hq,hM,hσ,hC,hL₀,_of_gate), [the asserted conclusion holds](goal). -/
lemma dornTheorem1_scope (d : ℕ) (hd : 1 ≤ d)
    (β q M σ C L₀ : ℝ) (hβ : 0 < β) (hq : 3 < q)
    (hM : 0 < M) (hσ : 0 < σ) (hC : 0 < C) (hL₀ : 0 < L₀)
    (_of_gate : DornSourceRateTranscription) :
    (∀ (γ : ℝ) (𝔓 : Set (DornSourceLaw d)),
      1 < γ → DornA12Family d β q M σ C L₀ γ 𝔓 →
      DornA3OnOriginalClass 𝔓 →
      ∃ T : ∀ n : ℕ, (Fin n → Obs d) → (Fin d → ℝ) → ℝ,
      (∀ (n : ℕ) (z : {z : DornSourceLaw d // z ∈ 𝔓}) (R : ℝ),
        MeasurableSet
          {ω | ENNReal.ofReal
              (R * (n : ℝ) ^ (-β / (2 * β + effectiveDimension d γ))) <
            eLpNorm (fun x => T n ω x - z.1.2.1 x) ⊤
              (covariateLaw z.1.1)}) ∧
      (∀ n x, Measurable (fun ω => T n ω x)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
        Filter.limsup (fun n : ℕ =>
          ⨆ (z : {z : DornSourceLaw d // z ∈ 𝔓}),
            (Measure.pi (fun _ : Fin n => z.1.1)).real
              {ω | ENNReal.ofReal
                (R * (n : ℝ) ^ (-β / (2 * β + effectiveDimension d γ))) <
                eLpNorm (fun x => T n ω x - z.1.2.1 x) ⊤
                  (covariateLaw z.1.1)}) Filter.atTop ≤ ε) ∧
    (∀ γ : ℝ, 1 < γ →
      (∀ (𝔓 : Set (DornSourceLaw d)) (μref : (Fin d → ℝ) → ℝ)
        (x₀ : Fin d → ℝ), 𝔓.Nonempty →
        (∀ z ∈ 𝔓, ∀ x, z.2.1 x = μref x) →
        ∀ (n : ℕ) (c r : ℝ), 0 < c → 0 < r →
          Causalean.Stat.minimaxValueENNReal
            (dornPointwiseMissRisk (n := n) 𝔓 x₀ c r) = 0) ∧
      (∃ q' M' C' : ℝ, 3 < q' ∧ 0 < M' ∧ 0 < C' ∧
        ∃ hP : IsProbabilityMeasure (dornCanonicalLaw d),
          @DornRemainingModel d β q' M' 1 C' L₀ γ
            (dornCanonicalLaw d) hP
            (fun _ => 0) (fun _ => 0) (fun _ => 1 / 2) ∧
          DornA3OnOriginalClass
            ({(dornCanonicalLaw d, (fun _ => 0), (fun _ => 0),
              (fun _ => 1 / 2))} : Set (DornSourceLaw d)) ∧
          ∀ (n : ℕ) (c r : ℝ), 0 < c → 0 < r →
            Causalean.Stat.minimaxValueENNReal
              (dornPointwiseMissRisk (n := n)
                ({(dornCanonicalLaw d, (fun _ => 0), (fun _ => 0),
                  (fun _ => 1 / 2))} : Set (DornSourceLaw d))
                (fun _ => 0) c r) = 0)) := by
  constructor
  · intro γ 𝔓 hγ hA12 hA3
    exact _of_gate d β q M σ C L₀ γ 𝔓 hd hβ hq hM hσ hC hL₀
      hγ hA12 hA3
  · intro γ hγ
    exact arbitraryFamily_lower_obstruction d hd β γ L₀ hβ hγ hL₀

end CausalSmith.Stat.WeakOverlap

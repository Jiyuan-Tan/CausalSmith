module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Coefficients
public import Causalean.Stat.Nonparametric.Approximation.HolderTaylorMonomial
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Affine
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Extension
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Identification
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Fibre
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.OrderedMass.Geometry

/-! # Deterministic selected-cell bias bounds -/
public section
namespace CausalSmith.Stat.WeakOverlap
open Causalean.Stat.Nonparametric
open MeasureTheory
open Causalean.Mathlib.Analysis.Calculus.CubeExtension
open scoped BigOperators

/-- The identified Hölder representative agrees with the treated regression
at every coordinate of an IID sample, outside one design-null set. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,Pc,μ,e,hparams,hγ,hmodel,Q,hIID), [the asserted conclusion holds](goal). -/
lemma holderRepresentative_on_iid_sample {d n : ℕ} {β B L C c_f γ : ℝ}
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ e : (Fin d → ℝ) → ℝ)
    (hparams : ModelParameterDomain d β B L C c_f) (hγ : 1 < γ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ e)
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (hIID : IIDSampleLaw Q (Pc.map observed)) :
    ∀ᵐ ω ∂Q, ∀ i : Fin n,
      μ (ω i).1 = treatedRegression (Pc.map observed) (ω i).1 := by
  let P := Pc.map observed
  letI : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map
    (μ := Pc) (f := observed) (by unfold observed; fun_prop)
  have hbase : ∀ᵐ x ∂covariateLaw P, μ x = treatedRegression P x := by
    simpa [P] using (mu1_eq_treatedRegression β B L C c_f γ Pc μ e
      hparams hγ hmodel).2.1
  have hobs : ∀ᵐ z ∂P, μ z.1 = treatedRegression P z.1 :=
    ae_of_ae_map measurable_fst.aemeasurable hbase
  have hi : ∀ i : Fin n, ∀ᵐ ω ∂Q,
      μ (ω i).1 = treatedRegression P (ω i).1 := by
    intro i
    have hmap : Q.map (fun ω : Fin n → Obs d => ω i) = P := by
      rw [hIID]
      simpa [P] using Measure.pi_map_eval (fun _ : Fin n => P) i
    have hobs' : ∀ᵐ z ∂Q.map (fun ω : Fin n → Obs d => ω i),
        μ z.1 = treatedRegression P z.1 := by simpa only [hmap] using hobs
    exact ae_of_ae_map (μ := Q) (f := fun ω : Fin n → Obs d => ω i)
      (measurable_pi_apply i).aemeasurable hobs'
  simpa [P] using ae_all_iff.mpr hi

/-- Rescaling any point of a dyadic macro-cell by its lower corner and width
lands in the unit covariate cube, including the global right boundary. [For the stated inputs and conditions](hyp:d,j,k,x,hx), [the asserted conclusion holds](goal). -/
lemma dyadicCube_normalized_mem_cube {d j : ℕ}
    (k : Fin d → Fin (2 ^ j)) {x : Fin d → ℝ}
    (hx : x ∈ dyadicCube d j k) :
    (fun i => (x i - cubeCorner d j k i) / meshWidth j) ∈ cube d := by
  have hh : 0 < meshWidth j := by unfold meshWidth; positivity
  have hscale := orderedMass_meshWidth_mul_pow j
  apply Set.mem_univ_pi.mpr
  intro i
  have hi := hx.2 i
  constructor
  · exact div_nonneg (sub_nonneg.mpr hi.1) hh.le
  · apply (div_le_one hh).2
    rcases hi.2 with hlt | ⟨hk, hx1⟩
    · linarith
    · have hkcast : ((k i).val : ℝ) = (2 : ℝ) ^ j - 1 := by
        have hk' : ((k i).val : ℝ) = ((2 ^ j - 1 : ℕ) : ℝ) := by
          exact_mod_cast hk
        have hp : 1 ≤ 2 ^ j := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
        rw [Nat.cast_sub hp, Nat.cast_pow] at hk'
        norm_num at hk' ⊢
        exact hk'
      rw [hx1]
      change 1 - (k i).val * meshWidth j ≤ meshWidth j
      rw [hkcast]
      nlinarith

/-- The capped floor index assigns every cube point to its corresponding
half-open dyadic macro-cell. [For the stated inputs and conditions](hyp:d,j,x,hx), [the asserted conclusion holds](goal). -/
lemma cubeIndex_mem_dyadicCube {d j : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ cube d) : x ∈ dyadicCube d j (cubeIndex d j x) := by
  refine ⟨hx, ?_⟩
  intro i
  have hh : 0 < meshWidth j := by unfold meshWidth; positivity
  have hscale := orderedMass_meshWidth_mul_pow j
  let N : ℕ := 2 ^ j
  have hN : 0 < N := by dsimp [N]; positivity
  have hxi := Set.mem_univ_pi.mp hx i
  by_cases hx1 : x i = 1
  · rw [hx1]
    have hk : (cubeIndex d j x i).val = N - 1 := by
      change min (Nat.floor ((N : ℝ) * x i)) (N - 1) % N = N - 1
      rw [hx1]
      simp only [mul_one, Nat.floor_natCast]
      rw [min_eq_right (Nat.sub_le _ _), Nat.mod_eq_of_lt (Nat.sub_lt hN (by omega))]
    constructor
    · change ((cubeIndex d j x i).val : ℝ) * meshWidth j ≤ 1
      have hk' : ((cubeIndex d j x i).val : ℝ) = (N - 1 : ℕ) := by exact_mod_cast hk
      rw [hk']
      have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN.ne')]
        norm_num
      rw [hcast]
      have hscale' : meshWidth j * (N : ℝ) = 1 := by simpa [N] using hscale
      nlinarith
    · exact Or.inr ⟨by simpa [N] using hk, rfl⟩
  · have hxl : x i < 1 := lt_of_le_of_ne hxi.2 hx1
    have hqnonneg : 0 ≤ (N : ℝ) * x i := mul_nonneg (by positivity) hxi.1
    have hq_lt : (N : ℝ) * x i < N := by
      norm_num
      exact mul_lt_of_lt_one_right (by positivity) hxl
    have hfloor_lt : Nat.floor ((N : ℝ) * x i) < N :=
      (Nat.floor_lt hqnonneg).2 hq_lt
    have hk : (cubeIndex d j x i).val = Nat.floor ((N : ℝ) * x i) := by
      change min (Nat.floor ((N : ℝ) * x i)) (N - 1) % N =
        Nat.floor ((N : ℝ) * x i)
      have hle : Nat.floor ((N : ℝ) * x i) ≤ N - 1 := by omega
      rw [min_eq_left hle, Nat.mod_eq_of_lt hfloor_lt]
    constructor
    · change ((cubeIndex d j x i).val : ℝ) * meshWidth j ≤ x i
      rw [hk]
      have hf := Nat.floor_le hqnonneg
      have hscale' : meshWidth j * (N : ℝ) = 1 := by simpa [N] using hscale
      nlinarith [mul_le_mul_of_nonneg_right hf hh.le]
    · apply Or.inl
      change x i < ((cubeIndex d j x i).val : ℝ) * meshWidth j + meshWidth j
      rw [hk]
      have hf := Nat.lt_floor_add_one ((N : ℝ) * x i)
      have hscale' : meshWidth j * (N : ℝ) = 1 := by simpa [N] using hscale
      nlinarith [mul_lt_mul_of_pos_right hf hh]

/-- The normalized coordinates selected by `cubeIndex` lie in the unit cube. [For the stated inputs and conditions](hyp:d,j,x,hx), [the asserted conclusion holds](goal). -/
lemma cubeIndex_normalized_mem_cube {d j : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ cube d) :
    (fun i => (x i - cubeCorner d j (cubeIndex d j x) i) / meshWidth j) ∈ cube d :=
  dyadicCube_normalized_mem_cube (cubeIndex d j x) (cubeIndex_mem_dyadicCube hx)

/-- Replacing treated outcomes by the identified regression preserves a
local polynomial approximation and hence controls every fitted coefficient. [For the stated inputs and conditions](hyp:d,n,m,j,P,μ,ω,hrepresentative,k,θ,hcount,r,hr,happrox,α), [the asserted conclusion holds](goal). -/
lemma conditionalMeanSample_sub_polynomial_coordinate_le {d n : ℕ} (m j : ℕ)
    (P : Measure (Obs d)) [IsFiniteMeasure P]
    (μ : (Fin d → ℝ) → ℝ) (ω : Fin n → Obs d)
    (hrepresentative : ∀ i : Fin n,
      μ (ω i).1 = treatedRegression P (ω i).1)
    (k : Fin d → Fin (2 ^ j)) (θ : MonoIndex d m → ℝ)
    (hcount : ∀ ℓ : Fin d → Fin (m + 1), 0 < treatedCount m j ω k ℓ)
    (r : ℝ) (hr : 0 ≤ r)
    (happrox : ∀ (ℓ : Fin d → Fin (m + 1)) (i : Fin n),
      (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ →
      |μ (ω i).1 - ∑ α : MonoIndex d m,
        monoVec d m
          (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α * θ α| ≤ r)
    (α : MonoIndex d m) :
    |coefHat m j (conditionalMeanSample P ω) k α - θ α| ≤
      (2 / templateLambda d m) *
        (Real.sqrt (Fintype.card (MonoIndex d m) : ℝ) * r) := by
  have hdesign : ∀ i,
      ((conditionalMeanSample P ω) i).1 = (ω i).1 ∧
      ((conditionalMeanSample P ω) i).2.1 = (ω i).2.1 := by
    intro i
    exact ⟨rfl, rfl⟩
  have hcount' : ∀ ℓ : Fin d → Fin (m + 1),
      0 < treatedCount m j (conditionalMeanSample P ω) k ℓ := by
    intro ℓ
    rw [treatedCount_eq_of_design_eq m j ω (conditionalMeanSample P ω) k ℓ hdesign]
    exact hcount ℓ
  apply coefHat_sub_polynomial_coordinate_le m j
    (conditionalMeanSample P ω) k θ hcount' r hr
  intro ℓ i hi
  have hi' : (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ := by
    simpa only [conditionalMeanSample] using hi
  simpa only [conditionalMeanSample, hi'.1, ↓reduceIte, hrepresentative i] using
    happrox ℓ i hi'

/-- Almost surely over an IID sample, the conditional coefficient centre
inherits any pointwise local-polynomial approximation of the selected design. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,Pc,μ,e,hparams,hγ,hmodel,Q,hIID), [the asserted conclusion holds](goal). -/
lemma conditionalCoefCentre_sub_polynomial_coordinate_le
    {d n : ℕ} {β B L C c_f γ : ℝ}
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ e : (Fin d → ℝ) → ℝ)
    (hparams : ModelParameterDomain d β B L C c_f) (hγ : 1 < γ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ e)
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (hIID : IIDSampleLaw Q (Pc.map observed)) :
    ∀ᵐ ω ∂Q, ∀ (m j : ℕ) (k : Fin d → Fin (2 ^ j))
      (θ : MonoIndex d m → ℝ) (r : ℝ), 0 ≤ r →
      (∀ ℓ : Fin d → Fin (m + 1), 0 < treatedCount m j ω k ℓ) →
      (∀ (ℓ : Fin d → Fin (m + 1)) (i : Fin n),
        (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ →
        |μ (ω i).1 - ∑ α : MonoIndex d m,
          monoVec d m
            (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α * θ α| ≤ r) →
      ∀ α : MonoIndex d m,
        |conditionalCoefCentre Q m j ω k α - θ α| ≤
          (2 / templateLambda d m) *
            (Real.sqrt (Fintype.card (MonoIndex d m) : ℝ) * r) := by
  let P := Pc.map observed
  letI : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map
    (μ := Pc) (f := observed) (by unfold observed; fun_prop)
  filter_upwards [holderRepresentative_on_iid_sample Pc μ e hparams hγ hmodel Q hIID,
    conditionalCoefCentre_eq_conditionalMeanSample P Q hIID hmodel.outcome]
    with ω hrepresentative hcentre
  intro m j k θ r hr hcount happrox α
  rw [hcentre m j k α]
  exact conditionalMeanSample_sub_polynomial_coordinate_le m j P μ ω
    hrepresentative k θ hcount r hr happrox α

/-- The local Hölder Taylor constant can be chosen before the centre and
domain. This is the centre-uniform form needed by the selected mesh. [For the stated inputs and conditions](hyp:d,p,β,L,r,hβ,hL,hr,expo,hcover), [the asserted conclusion holds](goal). -/
theorem holder_taylor_monomial_approx_uniform_center {d p : ℕ}
    {β L r : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (hr : 0 < r)
    (expo : Fin p → (Fin d → ℕ))
    (hcover : ∀ e : Fin d → ℕ,
      (∑ j, e j) ≤ ⌈β⌉₊ - 1 → ∃ k, expo k = e) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧
      ∀ (x₀ : Fin d → ℝ) (S : Set (Fin d → ℝ)),
        {x : Fin d → ℝ | ∀ i, |x i - x₀ i| ≤ r} ⊆ S →
        ∀ f : (Fin d → ℝ) → ℝ, HolderBallStd f β L S →
          ∀ h : ℝ, 0 < h → h < r →
            ∃ θ : Fin p → ℝ,
              ∀ u : Fin d → ℝ, (∀ j, |u j| ≤ 1) →
                |f (x₀ + h • u) -
                    ∑ k, θ k * ∏ j, (u j) ^ (expo k j)| ≤
                  Cb * L * h ^ β :=
  Causalean.Stat.Nonparametric.holder_taylor_monomial_approx_uniform_center
    hβ hL expo hcover

/-- One approximation constant works for every response in the intrinsic
Holder ball. [For the stated inputs and conditions](hyp:d,β,L,hβ,hL), [the asserted conclusion holds](goal). -/
lemma exists_uniform_holderBall_local_monoVec_approx (d : ℕ) {β L : ℝ}
    (hβ : 0 < β) (hL : 0 < L) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (μ : (Fin d → ℝ) → ℝ), HolderBall β L μ →
      ∀ (x₀ : Fin d → ℝ) (h : ℝ), 0 < h → h ≤ 1 →
      ∃ θ : MonoIndex d (polynomialDegree β) → ℝ,
        ∀ u : Fin d → ℝ, (∀ i, |u i| ≤ 1) → x₀ + h • u ∈ cube d →
          |μ (x₀ + h • u) -
              ∑ α, monoVec d (polynomialDegree β) u α * θ α| ≤
            Cb * L * h ^ β := by
  classical
  let m := polynomialDegree β
  let s := β - (m : ℝ)
  have hceil : 1 ≤ ⌈β⌉₊ := Nat.one_le_ceil_iff.mpr hβ
  have hmcast : (m : ℝ) = (⌈β⌉₊ : ℝ) - 1 := by
    simp only [m, polynomialDegree]
    rw [Nat.cast_sub hceil, Nat.cast_one]
  have hs : 0 < s := by
    dsimp [s]
    rw [hmcast]
    linarith [Nat.ceil_lt_add_one hβ.le]
  have hs1 : s ≤ 1 := by
    dsimp [s]
    rw [hmcast]
    linarith [Nat.le_ceil β]
  obtain ⟨D, hD, htransport⟩ := unit_holder_affine_transport d m s hs
  obtain ⟨A, hA, hExt⟩ := exists_global_holder_extension d m s hs hs1
  let e : MonoIndex d m ≃ Fin (Fintype.card (MonoIndex d m)) := Fintype.equivFin _
  let expo : Fin (Fintype.card (MonoIndex d m)) → (Fin d → ℕ) :=
    fun q i => (((e.symm q).1 i).val)
  have hcover : ∀ a : Fin d → ℕ, (∑ i, a i) ≤ ⌈β⌉₊ - 1 → ∃ q, expo q = a := by
    intro a ha
    have hai (i : Fin d) : a i < m + 1 := by
      have hi := (Finset.single_le_sum (fun q _ => Nat.zero_le (a q))
        (Finset.mem_univ i)).trans ha
      simpa [m, polynomialDegree] using Nat.lt_succ_of_le hi
    let α : MonoIndex d m := ⟨fun i => ⟨a i, hai i⟩, by
      simp only [monoIdx, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [m, polynomialDegree] using ha⟩
    exact ⟨e α, by funext i; simp [expo, e, α]⟩
  obtain ⟨C₀, hC₀, hApprox⟩ := holder_taylor_monomial_approx_uniform_center
      hβ (by positivity : 0 < A * (D * L)) (by norm_num : (0 : ℝ) < 3)
      expo hcover
  refine ⟨C₀ * A * D * (2 : ℝ) ^ β, by positivity, ?_⟩
  intro μ hμ x₀ h hh hh1
  have hμunit : Causalean.Mathlib.Analysis.Calculus.CubeExtension.HolderBallOn
      (Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.unitCube d)
      m s L μ := by
    simpa [m, s, cube,
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.unitCube] using hμ.toIntrinsic
  have hμa : CubeHolderBall d m s (D * L) (fun z => μ (cubeAffineInv z)) :=
    htransport μ L hL.le hμunit
  obtain ⟨U, hUeq, hUsmooth, hUbounds, hUmod⟩ :=
    hExt (fun z => μ (cubeAffineInv z)) (D * L) (mul_nonneg hD.le hL.le) hμa
  have hUstd : HolderBallStd U β (A * (D * L)) Set.univ := by
    refine ⟨by change ContDiffOn ℝ m U Set.univ; exact hUsmooth.contDiffOn, ?_, ?_⟩
    · intro q hq z hz
      exact hUbounds q (by change q ≤ m at hq; exact hq) z
    · intro z hz w hw
      change ‖iteratedFDeriv ℝ m U z - iteratedFDeriv ℝ m U w‖ ≤
        A * (D * L) * ‖z - w‖ ^ s
      exact hUmod z w
  let x₀' := Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cubeAffine x₀
  have hsubset : {z : Fin d → ℝ | ∀ i, |z i - x₀' i| ≤ 3} ⊆ Set.univ := by
    intro z hz
    trivial
  obtain ⟨c, hc⟩ := hApprox x₀' Set.univ hsubset U hUstd
    (2 * h) (by positivity) (by linarith)
  let θ : MonoIndex d m → ℝ := fun α => c (e α)
  refine ⟨θ, ?_⟩
  intro u hu hxu
  have harg : Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cubeAffine
      (x₀ + h • u) = x₀' + (2 * h) • u := by
    ext i
    simp [x₀', Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cubeAffine,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hmem : Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cubeAffine
      (x₀ + h • u) ∈ Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cube d :=
    Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cubeAffine_mem_cube
      (by simpa [cube,
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.unitCube] using hxu)
  have hagree : U (x₀' + (2 * h) • u) = μ (x₀ + h • u) := by
    rw [← harg, hUeq hmem]
    exact congrArg μ (by
      ext i
      simp [Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cubeAffine,
        cubeAffineInv])
  have hsum : (∑ q, c q * ∏ i, u i ^ expo q i) =
      ∑ α, monoVec d m u α * θ α := by
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro α _
    simp [expo, θ, monoVec, e, mul_comm]
  rw [← hsum, ← hagree]
  calc
    _ ≤ C₀ * (A * (D * L)) * (2 * h) ^ β := hc u hu
    _ ≤ (C₀ * A * D * (2 : ℝ) ^ β) * L * h ^ β := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hh.le]
      ring_nf
      exact le_rfl

/-- Intrinsic `[0,1]^d` Hölder regularity supplies a fixed-cell polynomial in
the exact `MonoIndex` basis. [For the stated inputs and conditions](hyp:d,β,L,hβ,hL,μ,hμ), [the asserted conclusion holds](goal). -/
lemma holderBall_exists_local_monoVec_approx (d : ℕ) {β L : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (μ : (Fin d → ℝ) → ℝ)
    (hμ : HolderBall β L μ) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (x₀ : Fin d → ℝ) (h : ℝ), 0 < h → h ≤ 1 →
      ∃ θ : MonoIndex d (polynomialDegree β) → ℝ,
        ∀ u : Fin d → ℝ, (∀ i, |u i| ≤ 1) → x₀ + h • u ∈ cube d →
          |μ (x₀ + h • u) -
              ∑ α, monoVec d (polynomialDegree β) u α * θ α| ≤
            Cb * L * h ^ β := by
  classical
  let m := polynomialDegree β
  let s := β - (m : ℝ)
  have hceil : 1 ≤ ⌈β⌉₊ := Nat.one_le_ceil_iff.mpr hβ
  have hmcast : (m : ℝ) = (⌈β⌉₊ : ℝ) - 1 := by
    simp only [m, polynomialDegree]
    rw [Nat.cast_sub hceil, Nat.cast_one]
  have hs : 0 < s := by dsimp [s]; rw [hmcast]; linarith [Nat.ceil_lt_add_one hβ.le]
  have hs1 : s ≤ 1 := by dsimp [s]; rw [hmcast]; linarith [Nat.le_ceil β]
  obtain ⟨D, hD, htransport⟩ := unit_holder_affine_transport d m s hs
  have hμunit : Causalean.Mathlib.Analysis.Calculus.CubeExtension.HolderBallOn
      (Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.unitCube d)
      m s L μ := by
    simpa [m, s, cube,
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.unitCube] using hμ.toIntrinsic
  have hμa : CubeHolderBall d m s (D * L) (fun z => μ (cubeAffineInv z)) :=
    htransport μ L hL.le hμunit
  obtain ⟨A, hA, hExt⟩ := exists_global_holder_extension d m s hs hs1
  obtain ⟨U, hUeq, hUsmooth, hUbounds, hUmod⟩ :=
    hExt (fun z => μ (cubeAffineInv z)) (D * L) (mul_nonneg hD.le hL.le) hμa
  have hUstd : HolderBallStd U β (A * (D * L)) Set.univ := by
    refine ⟨by change ContDiffOn ℝ m U Set.univ; exact hUsmooth.contDiffOn, ?_, ?_⟩
    · intro q hq z hz
      exact hUbounds q (by change q ≤ m at hq; exact hq) z
    · intro z hz w hw
      change ‖iteratedFDeriv ℝ m U z - iteratedFDeriv ℝ m U w‖ ≤
        A * (D * L) * ‖z - w‖ ^ s
      exact hUmod z w
  let e : MonoIndex d m ≃ Fin (Fintype.card (MonoIndex d m)) := Fintype.equivFin _
  let expo : Fin (Fintype.card (MonoIndex d m)) → (Fin d → ℕ) :=
    fun q i => (((e.symm q).1 i).val)
  have hcover : ∀ a : Fin d → ℕ, (∑ i, a i) ≤ ⌈β⌉₊ - 1 → ∃ q, expo q = a := by
    intro a ha
    have hai (i : Fin d) : a i < m + 1 := by
      have hi := (Finset.single_le_sum (fun q _ => Nat.zero_le (a q))
        (Finset.mem_univ i)).trans ha
      simpa [m, polynomialDegree] using Nat.lt_succ_of_le hi
    let α : MonoIndex d m := ⟨fun i => ⟨a i, hai i⟩, by
      simp only [monoIdx, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [m, polynomialDegree] using ha⟩
    exact ⟨e α, by funext i; simp [expo, e, α]⟩
  obtain ⟨C₀, hC₀, hApprox⟩ := holder_taylor_monomial_approx_uniform_center
      hβ (by positivity : 0 < A * (D * L)) (by norm_num : (0 : ℝ) < 3)
      expo hcover
  refine ⟨C₀ * A * D * (2 : ℝ) ^ β, by positivity, ?_⟩
  intro x₀ h hh hh1
  let x₀' := Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cubeAffine x₀
  have hsubset : {z : Fin d → ℝ | ∀ i, |z i - x₀' i| ≤ 3} ⊆ Set.univ := by
    intro z hz
    trivial
  obtain ⟨c, hc⟩ := hApprox x₀' Set.univ hsubset U hUstd
    (2 * h) (by positivity) (by linarith)
  let θ : MonoIndex d m → ℝ := fun α => c (e α)
  refine ⟨θ, ?_⟩
  intro u hu hxu
  have harg : Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cubeAffine
      (x₀ + h • u) = x₀' + (2 * h) • u := by
    ext i
    simp [x₀', Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cubeAffine,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hmem : Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cubeAffine
      (x₀ + h • u) ∈ Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cube d :=
    Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cubeAffine_mem_cube
      (by simpa [cube,
        Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.unitCube] using hxu)
  have hagree : U (x₀' + (2 * h) • u) = μ (x₀ + h • u) := by
    rw [← harg, hUeq hmem]
    exact congrArg μ (by
      ext i
      simp [Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cubeAffine,
        cubeAffineInv])
  have hsum : (∑ q, c q * ∏ i, u i ^ expo q i) =
      ∑ α, monoVec d m u α * θ α := by
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro α _
    simp [expo, θ, monoVec, e, mul_comm]
  rw [← hsum, ← hagree]
  calc
    _ ≤ C₀ * (A * (D * L)) * (2 * h) ^ β := hc u hu
    _ ≤ (C₀ * A * D * (2 : ℝ) ^ β) * L * h ^ β := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hh.le]
      ring_nf
      exact le_rfl

/-- Every dyadic mesh width lies in `(0,1]`. [For the stated inputs and conditions](hyp:j), [the asserted conclusion holds](goal). -/
lemma meshWidth_pos_le_one (j : ℕ) : 0 < meshWidth j ∧ meshWidth j ≤ 1 := by
  constructor
  · unfold meshWidth
    positivity
  · unfold meshWidth
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    exact (inv_le_one₀ (by positivity)).2
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

/-- The cell-bias constant is uniform over every model completion and
response in the stated Holder ball. [For the stated inputs and conditions](hyp:d,β,L,hβ,hL), [the asserted conclusion holds](goal). -/
lemma exists_uniform_conditionalCoefCentre_holder_cell_bias
    (d : ℕ) (β L : ℝ) (hβ : 0 < β) (hL : 0 < L) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧
      ∀ {n : ℕ} {B C c_f γ : ℝ}
        (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
        (μ e : (Fin d → ℝ) → ℝ)
        (hparams : ModelParameterDomain d β B L C c_f) (hγ : 1 < γ)
        (hmodel : GlobalTailModel β B L C c_f γ Pc μ e)
        (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
        (hIID : IIDSampleLaw Q (Pc.map observed)),
      ∀ᵐ ω ∂Q, ∀ (j : ℕ) (k : Fin d → Fin (2 ^ j)),
        (∀ ℓ : Fin d → Fin (polynomialDegree β + 1),
          0 < treatedCount (polynomialDegree β) j ω k ℓ) →
        ∃ θ : MonoIndex d (polynomialDegree β) → ℝ,
          (∀ x ∈ dyadicCube d j k,
            |μ x - ∑ α, monoVec d (polynomialDegree β)
              (fun a => (x a - cubeCorner d j k a) / meshWidth j) α * θ α| ≤
                Cb * L * meshWidth j ^ β) ∧
          ∀ α,
            |conditionalCoefCentre Q (polynomialDegree β) j ω k α - θ α| ≤
              (2 / templateLambda d (polynomialDegree β)) *
                (Real.sqrt (Fintype.card
                  (MonoIndex d (polynomialDegree β)) : ℝ) *
                    (Cb * L * meshWidth j ^ β)) := by
  obtain ⟨Cb, hCb, hTaylor⟩ :=
    exists_uniform_holderBall_local_monoVec_approx d hβ hL
  refine ⟨Cb, hCb, ?_⟩
  intro n B C c_f γ Pc _ μ e hparams hγ hmodel Q _ hIID
  have hTaylorμ := hTaylor μ hmodel.smooth.1
  filter_upwards [conditionalCoefCentre_sub_polynomial_coordinate_le
    Pc μ e hparams hγ hmodel Q hIID] with ω hcentre
  intro j k hcount
  obtain ⟨θ, hθ⟩ := hTaylorμ (cubeCorner d j k) (meshWidth j)
    (meshWidth_pos_le_one j).1 (meshWidth_pos_le_one j).2
  refine ⟨θ, ?_, ?_⟩
  · intro x hx
    let u : Fin d → ℝ := fun a =>
      (x a - cubeCorner d j k a) / meshWidth j
    have huCube : u ∈ cube d := dyadicCube_normalized_mem_cube k hx
    have huAbs : ∀ a, |u a| ≤ 1 := by
      intro a
      have ha := Set.mem_univ_pi.mp huCube a
      rw [abs_of_nonneg ha.1]
      exact ha.2
    have hreconstruct : cubeCorner d j k + meshWidth j • u = x := by
      ext a
      dsimp [u]
      field_simp [(meshWidth_pos_le_one j).1.ne']
      ring
    simpa only [hreconstruct] using hθ u huAbs
      (by simpa [hreconstruct] using hx.1)
  · apply hcentre (polynomialDegree β) j k θ
      (Cb * L * meshWidth j ^ β)
      (mul_nonneg (mul_nonneg hCb hparams.2.2.2.1.le)
        (Real.rpow_nonneg (meshWidth_pos_le_one j).1.le _)) hcount
    intro ℓ i hi
    have hxi := orderedMass_scaledMicroCell_inside_dyadicCube
      d (polynomialDegree β) j k ℓ hi.2
    have huAbs : ∀ a, |((ω i).1 a - cubeCorner d j k a) / meshWidth j| ≤ 1 := fun a => by
      have ha := Set.mem_univ_pi.mp
        (dyadicCube_normalized_mem_cube k hxi) a
      rw [abs_of_nonneg ha.1]
      exact ha.2
    have hreconstruct : cubeCorner d j k + meshWidth j •
        (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) = (ω i).1 := by
      ext a
      change cubeCorner d j k a + meshWidth j *
        (((ω i).1 a - cubeCorner d j k a) / meshWidth j) = (ω i).1 a
      field_simp [(meshWidth_pos_le_one j).1.ne']
      ring
    have ht := hθ _ huAbs (by rw [hreconstruct]; exact hxi.1)
    rw [hreconstruct] at ht
    exact ht

/-- Uniformly over cells, the conditional coefficient centre is close to a
Taylor polynomial which approximates the Hölder representative throughout
the whole dyadic cell. [For the stated inputs and conditions](hyp:d,n,β,B,L,C,c_f,γ,Pc,μ,e,hparams,hγ,hmodel,Q,hIID), [the asserted conclusion holds](goal). -/
lemma conditionalCoefCentre_holder_cell_bias
    {d n : ℕ} {β B L C c_f γ : ℝ}
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ e : (Fin d → ℝ) → ℝ)
    (hparams : ModelParameterDomain d β B L C c_f) (hγ : 1 < γ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ e)
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (hIID : IIDSampleLaw Q (Pc.map observed)) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧
      ∀ᵐ ω ∂Q, ∀ (j : ℕ) (k : Fin d → Fin (2 ^ j)),
        (∀ ℓ : Fin d → Fin (polynomialDegree β + 1),
          0 < treatedCount (polynomialDegree β) j ω k ℓ) →
        ∃ θ : MonoIndex d (polynomialDegree β) → ℝ,
          (∀ x ∈ dyadicCube d j k,
            |μ x - ∑ α, monoVec d (polynomialDegree β)
              (fun a => (x a - cubeCorner d j k a) / meshWidth j) α * θ α| ≤
                Cb * L * meshWidth j ^ β) ∧
          ∀ α,
            |conditionalCoefCentre Q (polynomialDegree β) j ω k α - θ α| ≤
              (2 / templateLambda d (polynomialDegree β)) *
                (Real.sqrt (Fintype.card
                  (MonoIndex d (polynomialDegree β)) : ℝ) *
                    (Cb * L * meshWidth j ^ β)) := by
  obtain ⟨Cb, hCb, hTaylor⟩ := holderBall_exists_local_monoVec_approx
    d (zero_lt_one.trans hparams.2.1) hparams.2.2.2.1 μ hmodel.smooth.1
  refine ⟨Cb, hCb, ?_⟩
  filter_upwards [conditionalCoefCentre_sub_polynomial_coordinate_le
    Pc μ e hparams hγ hmodel Q hIID] with ω hcentre
  intro j k hcount
  obtain ⟨θ, hθ⟩ := hTaylor (cubeCorner d j k) (meshWidth j)
    (meshWidth_pos_le_one j).1 (meshWidth_pos_le_one j).2
  refine ⟨θ, ?_, ?_⟩
  · intro x hx
    let u : Fin d → ℝ := fun a =>
      (x a - cubeCorner d j k a) / meshWidth j
    have huCube : u ∈ cube d := dyadicCube_normalized_mem_cube k hx
    have huAbs : ∀ a, |u a| ≤ 1 := by
      intro a
      have ha := Set.mem_univ_pi.mp huCube a
      rw [abs_of_nonneg ha.1]
      exact ha.2
    have hreconstruct : cubeCorner d j k + meshWidth j • u = x := by
      ext a
      dsimp [u]
      field_simp [(meshWidth_pos_le_one j).1.ne']
      ring
    simpa only [hreconstruct] using hθ u huAbs (by simpa [hreconstruct] using hx.1)
  · apply hcentre (polynomialDegree β) j k θ
      (Cb * L * meshWidth j ^ β)
      (mul_nonneg (mul_nonneg hCb hparams.2.2.2.1.le)
        (Real.rpow_nonneg (meshWidth_pos_le_one j).1.le _)) hcount
    intro ℓ i hi
    have hxi := orderedMass_scaledMicroCell_inside_dyadicCube
      d (polynomialDegree β) j k ℓ hi.2
    have huAbs : ∀ a, |((ω i).1 a - cubeCorner d j k a) / meshWidth j| ≤ 1 := fun a => by
      have ha := Set.mem_univ_pi.mp
        (dyadicCube_normalized_mem_cube k hxi) a
      rw [abs_of_nonneg ha.1]
      exact ha.2
    have hreconstruct : cubeCorner d j k + meshWidth j •
        (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) = (ω i).1 := by
      ext a
      change cubeCorner d j k a + meshWidth j *
        (((ω i).1 a - cubeCorner d j k a) / meshWidth j) = (ω i).1 a
      field_simp [(meshWidth_pos_le_one j).1.ne']
      ring
    have ht := hθ _ huAbs (by rw [hreconstruct]; exact hxi.1)
    rw [hreconstruct] at ht
    exact ht

/-- The continuous Hölder representative inherits the treated-mean bound at
every cube point, rather than only almost everywhere. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,Pc,μ,e,hparams,hγ,hmodel), [the asserted conclusion holds](goal). -/
lemma holderResponse_abs_le_on_cube
    {d : ℕ} {β B L C c_f γ : ℝ}
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ e : (Fin d → ℝ) → ℝ)
    (hparams : ModelParameterDomain d β B L C c_f)
    (hγ : 1 < γ) (hmodel : GlobalTailModel β B L C c_f γ Pc μ e) :
    ∀ x ∈ cube d, |μ x| ≤ B := by
  let g : (Fin d → ℝ) → ℝ := fun x => max (-B) (min B (μ x))
  have hμcont : ContinuousOn μ (cube d) :=
    hmodel.smooth.1.regularity.continuousOn
  have hclip : Continuous (fun y : ℝ => max (-B) (min B y)) := by fun_prop
  have hgcont : ContinuousOn g (cube d) := by
    simpa [g, Function.comp_def] using
      hclip.continuousOn.comp hμcont (Set.mapsTo_univ μ (cube d))
  have hid := mu1_eq_treatedRegression β B L C c_f γ Pc μ e hparams hγ hmodel
  have hgae : ∀ᵐ x ∂covariateLaw (Pc.map observed),
      g x = treatedRegression (Pc.map observed) x := by
    filter_upwards [hid.2.1, hmodel.outcome] with x hx hbound
    have hμbound : |μ x| ≤ B := by simpa [hx] using hbound.1
    have hb := abs_le.mp hμbound
    dsimp [g]
    rw [min_eq_right hb.2, max_eq_right hb.1]
    exact hx
  intro x hx
  have hgeq : g x = μ x := hid.2.2 g hgcont hgae x hx
  have hBle : 0 ≤ B := hparams.2.2.1.le
  have hglo : -B ≤ g x := by dsimp [g]; exact le_max_left _ _
  have hghi : g x ≤ B := by
    dsimp [g]
    exact max_le (by linarith) (min_le_left _ _)
  rw [← hgeq]
  exact abs_le.mpr ⟨hglo, hghi⟩

/-- A cellwise conditional-centre bias bound and the realized coefficient
envelope give a uniform pointwise bound for the clipped selected estimator. [For the stated inputs and conditions](hyp:d,n,β,B,r,εb,Q,μ,ω,hselected,hwidth,hB,hμB,hr,hεb,hcell), [the asserted conclusion holds](goal). -/
lemma equalCellEstimator_error_le_conditional_envelope
    {d n : ℕ} {β B r εb : ℝ}
    (Q : Measure (Fin n → Obs d)) [IsFiniteMeasure Q]
    (μ : (Fin d → ℝ) → ℝ) (ω : Fin n → Obs d)
    (hselected : 0 < countSelectedMesh (polynomialDegree β) β ω)
    (hwidth : countSelectedMesh (polynomialDegree β) β ω =
      meshWidth ((feasibleIndices (polynomialDegree β) β ω).sup id))
    (hB : 0 ≤ B) (hμB : ∀ x ∈ cube d, |μ x| ≤ B)
    (hr : 0 ≤ r) (hεb : 0 ≤ εb)
    (hcell : ∀ k : Fin d → Fin
        (2 ^ ((feasibleIndices (polynomialDegree β) β ω).sup id)),
      ∃ θ : MonoIndex d (polynomialDegree β) → ℝ,
        (∀ x ∈ dyadicCube d
            ((feasibleIndices (polynomialDegree β) β ω).sup id) k,
          |μ x - ∑ α, monoVec d (polynomialDegree β)
            (fun a => (x a - cubeCorner d
              ((feasibleIndices (polynomialDegree β) β ω).sup id) k a) /
                countSelectedMesh (polynomialDegree β) β ω) α * θ α| ≤ r) ∧
        ∀ α,
          |conditionalCoefCentre Q (polynomialDegree β)
            ((feasibleIndices (polynomialDegree β) β ω).sup id) ω k α - θ α| ≤ εb) :
    ∀ x ∈ cube d,
      |equalCellEstimator β B ω x - μ x| ≤
        (Fintype.card (MonoIndex d (polynomialDegree β)) : ℝ) *
          (sSup ((fun k : Fin d → Fin
            (2 ^ ((feasibleIndices (polynomialDegree β) β ω).sup id)) =>
              ‖fun α : MonoIndex d (polynomialDegree β) =>
                coefHat (polynomialDegree β)
                  ((feasibleIndices (polynomialDegree β) β ω).sup id) ω k α -
                conditionalCoefCentre Q (polynomialDegree β)
                  ((feasibleIndices (polynomialDegree β) β ω).sup id) ω k α‖) ''
                    Set.univ) + εb) + r := by
  classical
  intro x hx
  let j := (feasibleIndices (polynomialDegree β) β ω).sup id
  let k := cubeIndex d j x
  obtain ⟨θ, hbias, hcentre⟩ := hcell k
  let S : ℝ := sSup ((fun k' : Fin d → Fin (2 ^ j) =>
    ‖fun α : MonoIndex d (polynomialDegree β) =>
      coefHat (polynomialDegree β) j ω k' α -
        conditionalCoefCentre Q (polynomialDegree β) j ω k' α‖) '' Set.univ)
  have hbdd : BddAbove ((fun k' : Fin d → Fin (2 ^ j) =>
      ‖fun α : MonoIndex d (polynomialDegree β) =>
        coefHat (polynomialDegree β) j ω k' α -
          conditionalCoefCentre Q (polynomialDegree β) j ω k' α‖) '' Set.univ) := by
    simpa only [Set.image_univ] using
      (Set.finite_range (fun k' : Fin d → Fin (2 ^ j) =>
        ‖fun α : MonoIndex d (polynomialDegree β) =>
          coefHat (polynomialDegree β) j ω k' α -
            conditionalCoefCentre Q (polynomialDegree β) j ω k' α‖)).bddAbove
  have hcoef : ∀ α,
      |coefHat (polynomialDegree β) j ω k α - θ α| ≤ S + εb := by
    intro α
    have hcoord :
        |coefHat (polynomialDegree β) j ω k α -
            conditionalCoefCentre Q (polynomialDegree β) j ω k α| ≤ S := by
      calc
        _ = ‖(fun a : MonoIndex d (polynomialDegree β) =>
              coefHat (polynomialDegree β) j ω k a -
                conditionalCoefCentre Q (polynomialDegree β) j ω k a) α‖ := by
              simp [Real.norm_eq_abs]
        _ ≤ ‖fun a : MonoIndex d (polynomialDegree β) =>
              coefHat (polynomialDegree β) j ω k a -
                conditionalCoefCentre Q (polynomialDegree β) j ω k a‖ :=
              norm_le_pi_norm (fun a : MonoIndex d (polynomialDegree β) =>
                coefHat (polynomialDegree β) j ω k a -
                  conditionalCoefCentre Q (polynomialDegree β) j ω k a) α
        _ ≤ S := le_csSup hbdd ⟨k, Set.mem_univ _, rfl⟩
    rw [show coefHat (polynomialDegree β) j ω k α - θ α =
        (coefHat (polynomialDegree β) j ω k α -
          conditionalCoefCentre Q (polynomialDegree β) j ω k α) +
        (conditionalCoefCentre Q (polynomialDegree β) j ω k α - θ α) by ring]
    exact (abs_add_le _ _).trans (add_le_add hcoord (hcentre α))
  apply equalCellEstimator_error_le_of_selected_coefficients ω x θ hselected
  · rw [hwidth]
    exact cubeIndex_normalized_mem_cube hx
  · exact hB
  · exact hμB x hx
  · simpa [j, k, S] using hcoef
  · have hxcell : x ∈ dyadicCube d j k := cubeIndex_mem_dyadicCube hx
    have hb := hbias x (by simpa [j, k] using hxcell)
    rw [abs_sub_comm]
    simpa [j, k] using hb

/-- [For the stated inputs and conditions](hyp:d,n,m,β,ω,ξ,hdesign), [the asserted conclusion holds](goal). -/

lemma feasibleIndices_eq_of_design_eq {d n : ℕ} (m : ℕ) (β : ℝ)
    (ω ξ : Fin n → Obs d) (hdesign : sampleDesign ξ = sampleDesign ω) :
    feasibleIndices m β ξ = feasibleIndices m β ω := by
  classical
  have hpoint : ∀ i, (ω i).1 = (ξ i).1 ∧ (ω i).2.1 = (ξ i).2.1 := by
    intro i
    have hi := congrFun hdesign i
    exact ⟨congrArg (fun z : (Fin d → ℝ) × Bool => z.1) hi.symm,
      congrArg (fun z : (Fin d → ℝ) × Bool => z.2) hi.symm⟩
  unfold feasibleIndices
  ext j
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hj, _hj', hcounts⟩
    refine ⟨hj, hj, fun k ℓ => ?_⟩
    simpa only [treatedCount_eq_of_design_eq m j ξ ω k ℓ hpoint] using
      hcounts k ℓ
  · rintro ⟨hj, _hj', hcounts⟩
    refine ⟨hj, hj, fun k ℓ => ?_⟩
    simpa only [treatedCount_eq_of_design_eq m j ξ ω k ℓ hpoint] using
      hcounts k ℓ

/-- [For the stated inputs and conditions](hyp:d,n,m,β,ω,ξ,hdesign), [the asserted conclusion holds](goal). -/

lemma countSelectedMesh_eq_of_design_eq {d n : ℕ} (m : ℕ) (β : ℝ)
    (ω ξ : Fin n → Obs d) (hdesign : sampleDesign ξ = sampleDesign ω) :
    countSelectedMesh m β ξ = countSelectedMesh m β ω := by
  simp only [countSelectedMesh,
    feasibleIndices_eq_of_design_eq m β ω ξ hdesign]

/-- The deterministic estimator bound can use the conditional centre and
cell-bias witnesses at any representative of the same complete-design fibre. [For the stated inputs and conditions](hyp:d,n,β,B,r,εb,Q,μ,ω,ξ,hdesign,hselected,hwidth,hB,hμB,hr,hεb,hcell), [the asserted conclusion holds](goal). -/
lemma equalCellEstimator_error_le_conditional_envelope_of_design_eq
    {d n : ℕ} {β B r εb : ℝ}
    (Q : Measure (Fin n → Obs d)) [IsFiniteMeasure Q]
    (μ : (Fin d → ℝ) → ℝ) (ω ξ : Fin n → Obs d)
    (hdesign : sampleDesign ξ = sampleDesign ω)
    (hselected : 0 < countSelectedMesh (polynomialDegree β) β ω)
    (hwidth : countSelectedMesh (polynomialDegree β) β ω =
      meshWidth ((feasibleIndices (polynomialDegree β) β ω).sup id))
    (hB : 0 ≤ B) (hμB : ∀ x ∈ cube d, |μ x| ≤ B)
    (hr : 0 ≤ r) (hεb : 0 ≤ εb)
    (hcell : ∀ k : Fin d → Fin
        (2 ^ ((feasibleIndices (polynomialDegree β) β ω).sup id)),
      ∃ θ : MonoIndex d (polynomialDegree β) → ℝ,
        (∀ x ∈ dyadicCube d
            ((feasibleIndices (polynomialDegree β) β ω).sup id) k,
          |μ x - ∑ α, monoVec d (polynomialDegree β)
            (fun a => (x a - cubeCorner d
              ((feasibleIndices (polynomialDegree β) β ω).sup id) k a) /
                countSelectedMesh (polynomialDegree β) β ω) α * θ α| ≤ r) ∧
        ∀ α,
          |conditionalCoefCentre Q (polynomialDegree β)
            ((feasibleIndices (polynomialDegree β) β ω).sup id) ω k α - θ α| ≤ εb) :
    ∀ x ∈ cube d,
      |equalCellEstimator β B ξ x - μ x| ≤
        (Fintype.card (MonoIndex d (polynomialDegree β)) : ℝ) *
          (sSup ((fun k : Fin d → Fin
            (2 ^ ((feasibleIndices (polynomialDegree β) β ξ).sup id)) =>
              ‖fun α : MonoIndex d (polynomialDegree β) =>
                coefHat (polynomialDegree β)
                  ((feasibleIndices (polynomialDegree β) β ξ).sup id) ξ k α -
                conditionalCoefCentre Q (polynomialDegree β)
                  ((feasibleIndices (polynomialDegree β) β ξ).sup id) ω k α‖) ''
                    Set.univ) + εb) + r := by
  have hfi := feasibleIndices_eq_of_design_eq
    (polynomialDegree β) β ω ξ hdesign
  have hcount := countSelectedMesh_eq_of_design_eq
    (polynomialDegree β) β ω ξ hdesign
  have hcentre : ∀ j k α,
      conditionalCoefCentre Q (polynomialDegree β) j ξ k α =
        conditionalCoefCentre Q (polynomialDegree β) j ω k α := by
    intro j k α
    simp only [conditionalCoefCentre, hdesign]
  have hselectedξ : 0 < countSelectedMesh (polynomialDegree β) β ξ := by
    rw [hcount]
    exact hselected
  have hwidthξ : countSelectedMesh (polynomialDegree β) β ξ =
      meshWidth ((feasibleIndices (polynomialDegree β) β ξ).sup id) := by
    rw [hcount, hfi]
    exact hwidth
  have hcellξ : ∀ k : Fin d → Fin
      (2 ^ ((feasibleIndices (polynomialDegree β) β ξ).sup id)),
      ∃ θ : MonoIndex d (polynomialDegree β) → ℝ,
        (∀ x ∈ dyadicCube d
            ((feasibleIndices (polynomialDegree β) β ξ).sup id) k,
          |μ x - ∑ α, monoVec d (polynomialDegree β)
            (fun a => (x a - cubeCorner d
              ((feasibleIndices (polynomialDegree β) β ξ).sup id) k a) /
                countSelectedMesh (polynomialDegree β) β ξ) α * θ α| ≤ r) ∧
        ∀ α,
          |conditionalCoefCentre Q (polynomialDegree β)
            ((feasibleIndices (polynomialDegree β) β ξ).sup id) ξ k α - θ α| ≤ εb := by
    rw [hfi, hcount]
    intro k
    simpa only [hcentre] using hcell k
  have hb := equalCellEstimator_error_le_conditional_envelope
    (β := β) (B := B) (r := r) (εb := εb)
    Q μ ξ hselectedξ hwidthξ hB hμB hr hεb hcellξ
  simpa only [hcentre] using hb

/-- A uniform real loss bound on the cube lifts directly to the ENNReal
cube supremum used by the minimax risk. [For the stated inputs and conditions](hyp:d,loss,R,hR,h), [the asserted conclusion holds](goal). -/
lemma cube_iSup_ofReal_loss_le {d : ℕ} (loss : (Fin d → ℝ) → ℝ)
    (R : ℝ) (hR : 0 ≤ R)
    (h : ∀ x ∈ cube d, |loss x| ≤ R) :
    (⨆ x, ⨆ _hx : x ∈ cube d, ENNReal.ofReal |loss x|) ≤ ENNReal.ofReal R := by
  refine iSup_le fun x => iSup_le fun hx => ?_
  exact ENNReal.ofReal_le_ofReal (h x hx)

/-- Clipping bounds every estimator error by twice the outcome envelope. [For the stated inputs and conditions](hyp:d,n,β,B,ω,x,y,hB,hy), [the asserted conclusion holds](goal). -/
lemma equalCellEstimator_error_le_two_mul {d n : ℕ} (β B : ℝ)
    (ω : Fin n → Obs d) (x : Fin d → ℝ) (y : ℝ)
    (hB : 0 ≤ B) (hy : |y| ≤ B) :
    |equalCellEstimator β B ω x - y| ≤ 2 * B := by
  have hyb := abs_le.mp hy
  by_cases hz : countSelectedMesh (polynomialDegree β) β ω = 0
  · simp [equalCellEstimator, hz]
    exact hy.trans (by linarith)
  · let u := ∑ α, monoVec d (polynomialDegree β)
        (fun a => (x a - cubeCorner d
          ((feasibleIndices (polynomialDegree β) β ω).sup id)
          (cubeIndex d ((feasibleIndices (polynomialDegree β) β ω).sup id) x) a) /
            countSelectedMesh (polynomialDegree β) β ω) α *
        coefHat (polynomialDegree β)
          ((feasibleIndices (polynomialDegree β) β ω).sup id) ω
          (cubeIndex d ((feasibleIndices (polynomialDegree β) β ω).sup id) x) α
    have hlo : -B ≤ max (-B) (min B u) := le_max_left _ _
    have hhi : max (-B) (min B u) ≤ B :=
      max_le (by linarith) (min_le_left _ _)
    unfold equalCellEstimator
    simp only [hz, ↓reduceIte]
    rw [abs_le]
    constructor <;> linarith

end CausalSmith.Stat.WeakOverlap

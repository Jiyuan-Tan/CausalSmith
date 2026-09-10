import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.TriangularArray
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.RegularBenchmark
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.TwoSampleProductTV
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmTensorization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Explicit binary models used by the studentized-Wald nonadaptation argument. -/

open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Finset Matrix MeasureTheory ProbabilityTheory

namespace CausalSmith.SCM.ProxyTargetspanTransport

private noncomputable def fair : Fin 2 → ℝ := ![1 / 2, 1 / 2]

private noncomputable def baselineProxy : Matrix (Fin 2) (Fin 2) ℝ :=
  !![3 / 4, 1 / 4; 1 / 4, 3 / 4]

/-- The fixed binary rank-one baseline has uniform observed cells and a fair target proxy law. -/
noncomputable def studentizedBaseline :
    LatentShiftSCM (Fin 2) (Fin 2) (Fin 2) (Fin 1) (Fin 2) where
  environment_nonempty := inferInstance
  treatment_nonempty := inferInstance
  latent_card := by decide
  proxy_card := by decide
  outcome_card := by decide
  pi := fair
  S := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]
  M := baselineProxy
  a := fun _ _ => 1
  f := fun _ _ _ _ => 1 / 2
  q := fair
  PM := fun e u w x y => fair e * (1 / 2) * baselineProxy w u * 1 * (1 / 2)
  QM := fun u w x y => fair u * baselineProxy w u * 1 * (1 / 2)
  pi_nonneg := by intro e; fin_cases e <;> norm_num [fair]
  pi_sum := by norm_num [fair, Fin.sum_univ_two]
  S_nonneg := by intro u e; fin_cases u <;> fin_cases e <;> norm_num
  S_col := by intro e; fin_cases e <;> norm_num [Fin.sum_univ_two]
  M_nonneg := by intro w u; fin_cases w <;> fin_cases u <;> norm_num [baselineProxy]
  M_col := by intro u; fin_cases u <;> norm_num [baselineProxy, Fin.sum_univ_two]
  a_nonneg := by intros; norm_num
  a_col := by intros; simp
  f_nonneg := by intros; norm_num
  f_col := by intros; norm_num [Fin.sum_univ_two]
  q_nonneg := by intro u; fin_cases u <;> norm_num [fair]
  q_sum := by norm_num [fair, Fin.sum_univ_two]
  PM_nonneg := by
    intro e u w x y
    fin_cases e <;> fin_cases u <;> fin_cases w <;> fin_cases x <;> fin_cases y <;>
      norm_num [fair, baselineProxy]
  PM_sum := by norm_num [fair, baselineProxy, Fin.sum_univ_two]
  QM_nonneg := by
    intro u w x y
    fin_cases u <;> fin_cases w <;> fin_cases x <;> fin_cases y <;>
      norm_num [fair, baselineProxy]
  QM_sum := by norm_num [fair, baselineProxy, Fin.sum_univ_two]

/-- [the studentized baseline satisfies the positive latent-shift model assumptions](goal). -/
theorem studentizedBaseline_positive : PositiveLatentShiftClass studentizedBaseline := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [LatentShiftFactorization, studentizedBaseline]
  · simp [TargetMechanismInvariance, studentizedBaseline]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e; fin_cases e <;> norm_num [studentizedBaseline, fair]
    · intro u e; fin_cases u <;> fin_cases e <;> norm_num [studentizedBaseline]
    · intro w u; fin_cases w <;> fin_cases u <;>
        norm_num [studentizedBaseline, baselineProxy]
    · intros; norm_num [studentizedBaseline]
    · intros; norm_num [studentizedBaseline]
    · intro u; fin_cases u <;> norm_num [studentizedBaseline, fair]
  · change baselineProxy.rank = 2
    apply Matrix.rank_of_det_ne_zero
    norm_num [baselineProxy, Matrix.det_fin_two]

/-- [every full observed-law cell of the studentized baseline equals the stated constant](goal). -/
theorem studentizedBaseline_observedLaw (e : Fin 2) (w : Fin 2) (x : Fin 1)
    (y : Fin 2) : observedLaw studentizedBaseline e w x y = 1 / 8 := by
  fin_cases e <;> fin_cases w <;> fin_cases x <;> fin_cases y <;>
    norm_num [observedLaw, studentizedBaseline, fair, baselineProxy, Fin.sum_univ_two]

/-- [every coordinate of the baseline target proxy vector equals one half](goal). -/
theorem studentizedBaseline_targetProxy (w : Fin 2) :
    targetProxyVector studentizedBaseline w = 1 / 2 := by
  fin_cases w <;>
    norm_num [targetProxyVector, studentizedBaseline, fair, baselineProxy, Fin.sum_univ_two]

/-- [the selected baseline interventional probability equals one half](goal). -/
theorem studentizedBaseline_interventional :
    interventionalProb studentizedBaseline 0 1 = 1 / 2 := by
  norm_num [interventionalProb, studentizedBaseline, fair, baselineProxy, Fin.sum_univ_two]

/-- [every baseline proxy-moment matrix entry equals the stated constant](goal). -/
theorem studentizedBaseline_proxyMoment (w e : Fin 2) :
    proxyMomentMatrix studentizedBaseline 0 w e = 1 / 4 := by
  simp [proxyMomentMatrix, studentizedBaseline_observedLaw, Fin.sum_univ_two]
  norm_num

/-- [every baseline outcome-moment coordinate equals the stated constant](goal). -/
theorem studentizedBaseline_outcomeMoment (e : Fin 2) :
    outcomeMomentVector studentizedBaseline 0 1 e = 1 / 4 := by
  simp [outcomeMomentVector, unconditionalBalancingMoments,
    studentizedBaseline_observedLaw, Fin.sum_univ_two]
  norm_num

/-- [the studentized baseline satisfies the regular target-span restriction](goal). -/
theorem studentizedBaseline_unconditionalTargetSpan :
    RegularTargetSpan studentizedBaseline 0 := by
  refine ⟨![1, 1], ?_⟩
  ext w
  fin_cases w <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      studentizedBaseline_proxyMoment, studentizedBaseline_targetProxy]
  all_goals norm_num

/-- [every observed-law cell of the studentized baseline is bounded below by the stated positive constant](goal). -/
theorem studentizedBaseline_cellFloor :
    RegularCellFloor studentizedBaseline (1 / 16) := by
  constructor
  · intro e w x y
    rw [studentizedBaseline_observedLaw]
    norm_num
  · intro w
    rw [studentizedBaseline_targetProxy]
    norm_num

private theorem studentizedBaseline_leftGram (i j : Fin 2) :
    Causalean.Mathlib.Analysis.leftGram (proxyMomentMatrix studentizedBaseline 0) i j =
      1 / 8 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Causalean.Mathlib.Analysis.leftGram, Matrix.mul_apply,
      Fin.sum_univ_two, studentizedBaseline_proxyMoment]

/-- [the first displayed vector is an exact balancing vector for the studentized baseline](goal). -/
theorem studentizedBaseline_lambda₁ :
    Causalean.Mathlib.Analysis.lambda₁
      (Causalean.Mathlib.Analysis.leftGram (proxyMomentMatrix studentizedBaseline 0)) =
      1 / 4 := by
  have hsqrt : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  norm_num [Causalean.Mathlib.Analysis.lambda₁,
    Causalean.Mathlib.Analysis.rootDiscriminant, studentizedBaseline_leftGram, hsqrt]

/-- [the second displayed vector is an exact balancing vector for the studentized baseline](goal). -/
theorem studentizedBaseline_lambda₂ :
    Causalean.Mathlib.Analysis.lambda₂
      (Causalean.Mathlib.Analysis.leftGram (proxyMomentMatrix studentizedBaseline 0)) =
      0 := by
  have hsqrt : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  norm_num [Causalean.Mathlib.Analysis.lambda₂,
    Causalean.Mathlib.Analysis.rootDiscriminant, studentizedBaseline_leftGram, hsqrt]

/-- [the baseline proxy, outcome, and target moment triple lies in the algebraic Wald regularity set](goal). -/
theorem studentizedBaseline_waldRegular :
    (proxyMomentMatrix studentizedBaseline 0,
      outcomeMomentVector studentizedBaseline 0 1,
      targetProxyVector studentizedBaseline) ∈
        Causalean.Mathlib.Analysis.waldRegularSet := by
  constructor
  · change Causalean.Mathlib.Analysis.lambda₂ _ <
      Causalean.Mathlib.Analysis.lambda₁ _
    rw [studentizedBaseline_lambda₁, studentizedBaseline_lambda₂]
    norm_num
  · rw [studentizedBaseline_lambda₁]
    norm_num

/-- [the studentized baseline has conditional proxy rank one](goal). -/
theorem studentizedBaseline_fixedRank :
    RegularFixedRank studentizedBaseline 0 1 := by
  let H := proxyMomentMatrix studentizedBaseline 0
  have houter : H = Matrix.vecMulVec (![1, 1] : Fin 2 → ℝ) (![1 / 4, 1 / 4] : Fin 2 → ℝ) := by
    ext w e
    fin_cases w <;> fin_cases e <;> norm_num [H, Matrix.vecMulVec,
      studentizedBaseline_proxyMoment]
  have hupp : H.rank ≤ 1 := by
    rw [houter]
    exact Matrix.rank_vecMulVec_le _ _
  have hlow : 1 ≤ H.rank := by
    rw [Matrix.rank_eq_finrank_span_cols]
    let v : Fin 2 → ℝ := ![1 / 4, 1 / 4]
    have hvcol : v ∈ Set.range H.col := by
      refine ⟨0, ?_⟩
      ext w
      fin_cases w <;> norm_num [v, H, Matrix.col_apply,
        studentizedBaseline_proxyMoment]
    have hvspan : v ∈ Submodule.span ℝ (Set.range H.col) :=
      Submodule.subset_span hvcol
    let vv : Submodule.span ℝ (Set.range H.col) := ⟨v, hvspan⟩
    have hvv : vv ≠ 0 := by
      intro hz
      have hz0 := congrArg (fun q : Submodule.span ℝ (Set.range H.col) => q.1 0) hz
      norm_num [vv, v] at hz0
    letI : Nontrivial (Submodule.span ℝ (Set.range H.col)) := ⟨⟨vv, 0, hvv⟩⟩
    exact Module.finrank_pos
  change H.rank = 1
  omega

/-- [at the baseline proxy matrix, the selected rank-one Wald functional agrees with the algebraic Wald functional](goal). -/
theorem studentizedBaseline_regularWaldFunctional_eq_algebraic
    (z : Fin 2 → ℝ) (b : Fin 2 → ℝ) :
    regularWaldFunctional (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
        (proxyMomentMatrix studentizedBaseline 0) z b =
      Causalean.Mathlib.Analysis.algebraicWaldFunctional
        (proxyMomentMatrix studentizedBaseline 0, z, b) := by
  apply regularWaldFunctional_one_eq_algebraic _ rfl
  · exact studentizedBaseline_waldRegular.1
  · rw [studentizedBaseline_lambda₁]
    norm_num

private theorem studentizedBaseline_algebraicPseudoInverse (e w : Fin 2) :
    Causalean.Mathlib.Analysis.algebraicRankOnePseudoInverse
        (proxyMomentMatrix studentizedBaseline 0) e w = 1 := by
  fin_cases e <;> fin_cases w <;>
    simp [Causalean.Mathlib.Analysis.algebraicRankOnePseudoInverse,
      Causalean.Mathlib.Analysis.topProjector, Matrix.mul_apply,
      Fin.sum_univ_two, studentizedBaseline_lambda₁,
      studentizedBaseline_lambda₂, studentizedBaseline_leftGram,
      studentizedBaseline_proxyMoment] <;> norm_num

/-- [at the baseline proxy matrix, the rank-one Wald functional equals the sum of the outcome-vector coordinates](goal). -/
theorem studentizedBaseline_regularWaldFunctional (z : Fin 2 → ℝ) :
    regularWaldFunctional (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
        (proxyMomentMatrix studentizedBaseline 0) z
        (targetProxyVector studentizedBaseline) = ∑ e, z e := by
  rw [studentizedBaseline_regularWaldFunctional_eq_algebraic]
  simp only [Causalean.Mathlib.Analysis.algebraicWaldFunctional, dotProduct,
    Matrix.mulVec, studentizedBaseline_targetProxy]
  apply Finset.sum_congr rfl
  intro e _
  rw [show (∑ w : Fin 2,
      Causalean.Mathlib.Analysis.algebraicRankOnePseudoInverse
          (proxyMomentMatrix studentizedBaseline 0) e w * (1 / 2 : ℝ)) = 1 by
    simp [studentizedBaseline_algebraicPseudoInverse, Fin.sum_univ_two]]
  ring_nf

private theorem studentizedBaseline_sourceDerivative_pureZ (dz : Fin 2 → ℝ) :
    let H := proxyMomentMatrix studentizedBaseline 0
    let z := outcomeMomentVector studentizedBaseline 0 1
    let b := targetProxyVector studentizedBaseline
    let dSource := fderiv ℝ
      (fun hz : (Matrix (Fin 2) (Fin 2) ℝ) × (Fin 2 → ℝ) =>
        regularWaldFunctional (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
          hz.1 hz.2 b) (H, z)
    dSource (0, dz) = ∑ e, dz e := by
  dsimp only
  let H := proxyMomentMatrix studentizedBaseline 0
  let z := outcomeMomentVector studentizedBaseline 0 1
  let b := targetProxyVector studentizedBaseline
  let F := fun hz : (Matrix (Fin 2) (Fin 2) ℝ) × (Fin 2 → ℝ) =>
    regularWaldFunctional (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) hz.1 hz.2 b
  let ins := fun z' : Fin 2 → ℝ => (H, z')
  have hF : DifferentiableAt ℝ F (H, z) := by
    have hfull := contDiffAt_regularWaldFunctional_one
      (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) rfl
      studentizedBaseline_waldRegular
    have hcomp : ContDiffAt ℝ 1
        ((fun q : Causalean.Mathlib.Analysis.WaldInput (Fin 2) =>
            regularWaldFunctional (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
              q.1 q.2.1 q.2.2) ∘
          fun hz : (Matrix (Fin 2) (Fin 2) ℝ) × (Fin 2 → ℝ) =>
            (hz.1, hz.2, b)) (H, z) :=
      hfull.comp (H, z) (by fun_prop)
    exact hcomp.differentiableAt (by norm_num)
  have hins : HasFDerivAt ins
      ((0 : (Fin 2 → ℝ) →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ).prod
        (ContinuousLinearMap.id ℝ (Fin 2 → ℝ))) z := by
    exact (hasFDerivAt_const H z).prodMk (hasFDerivAt_id z)
  have hcomp := hF.hasFDerivAt.comp z hins
  have hfun : F ∘ ins = fun z' : Fin 2 → ℝ => ∑ e, z' e := by
    funext z'
    exact studentizedBaseline_regularWaldFunctional z'
  rw [hfun] at hcomp
  have hsum : HasFDerivAt (fun z' : Fin 2 → ℝ => ∑ e, z' e)
      ((∑ e : Fin 2, ContinuousLinearMap.proj (R := ℝ) e) :
        (Fin 2 → ℝ) →L[ℝ] ℝ) z := by
    simp only [Fin.sum_univ_two]
    exact (hasFDerivAt_apply 0 z).add (hasFDerivAt_apply 1 z)
  have heq := hcomp.unique hsum
  have happ := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L dz) heq
  have hinsapp :
      ((0 : (Fin 2 → ℝ) →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ).prod
        (ContinuousLinearMap.id ℝ (Fin 2 → ℝ))) dz = (0, dz) := by
    ext <;> simp
  have happ' : (fderiv ℝ F (H, z))
      (((0 : (Fin 2 → ℝ) →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ).prod
        (ContinuousLinearMap.id ℝ (Fin 2 → ℝ))) dz) =
      ((∑ e : Fin 2, ContinuousLinearMap.proj (R := ℝ) e) :
        (Fin 2 → ℝ) →L[ℝ] ℝ) dz := happ
  rw [hinsapp] at happ'
  change (fderiv ℝ F (H, z)) (0, dz) = ∑ e, dz e
  simpa [Fin.sum_univ_two] using happ'

private theorem studentizedBaseline_sourceDerivative_outcomeGap (e w : Fin 2) :
    let H := proxyMomentMatrix studentizedBaseline 0
    let z := outcomeMomentVector studentizedBaseline 0 1
    let b := targetProxyVector studentizedBaseline
    let dSource := fderiv ℝ
      (fun hz : (Matrix (Fin 2) (Fin 2) ℝ) × (Fin 2 → ℝ) =>
        regularWaldFunctional (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
          hz.1 hz.2 b) (H, z)
    dSource (sourceStatisticDirection (0 : Fin 1) (1 : Fin 2) (e, w, 0, 1)) -
      dSource (sourceStatisticDirection (0 : Fin 1) (1 : Fin 2) (e, w, 0, 0)) = 1 := by
  dsimp only
  let dSource := fderiv ℝ
    (fun hz : (Matrix (Fin 2) (Fin 2) ℝ) × (Fin 2 → ℝ) =>
      regularWaldFunctional (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
        hz.1 hz.2 (targetProxyVector studentizedBaseline))
    (proxyMomentMatrix studentizedBaseline 0,
      outcomeMomentVector studentizedBaseline 0 1)
  rw [← map_sub]
  have hdir :
      sourceStatisticDirection (E := Fin 2) (W := Fin 2) (0 : Fin 1) (1 : Fin 2)
          (e, w, 0, 1) -
          sourceStatisticDirection (E := Fin 2) (W := Fin 2) (0 : Fin 1) (1 : Fin 2)
            (e, w, 0, 0) =
        (0, fun e' => if e = e' then 1 else 0) := by
    apply Prod.ext
    · simp only [Prod.fst_sub, sourceStatisticDirection]
      exact sub_self _
    · ext e'
      fin_cases e <;> fin_cases e' <;> simp [sourceStatisticDirection]
  rw [hdir]
  rw [studentizedBaseline_sourceDerivative_pureZ]
  fin_cases e <;> norm_num [Fin.sum_univ_two]

private theorem quadForm_multinomial_eq_moments
    {I : Type*} [Fintype I] [DecidableEq I] (v d : I → ℝ) :
    quadForm (multinomialCov v) d =
      ∑ i, v i * d i ^ 2 - (∑ i, v i * d i) ^ 2 := by
  change (∑ i, d i * ∑ j,
      ((if i = j then v i else 0) - v i * v j) * d j) = _
  simp_rw [sub_mul, Finset.sum_sub_distrib, mul_sub]
  simp [eq_comm, Finset.mul_sum]
  rw [show (∑ x, ∑ i, d x * (v x * v i * d i)) =
      (∑ x, v x * d x) * (∑ i, v i * d i) by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring]
  have hsquares : (∑ i, v i * d i ^ 2) = ∑ i, d i ^ 2 * v i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsquares]
  ring

private theorem eightPointPairVarianceLowerBound
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℝ)
    (h₀ : b₀ - a₀ = 1) (h₁ : b₁ - a₁ = 1)
    (h₂ : b₂ - a₂ = 1) (h₃ : b₃ - a₃ = 1) :
    1 / 4 ≤
      (1 / 8) * (a₀ ^ 2 + b₀ ^ 2 + a₁ ^ 2 + b₁ ^ 2 +
        a₂ ^ 2 + b₂ ^ 2 + a₃ ^ 2 + b₃ ^ 2) -
      ((1 / 8) * (a₀ + b₀ + a₁ + b₁ + a₂ + b₂ + a₃ + b₃)) ^ 2 := by
  have hb₀ : b₀ = a₀ + 1 := by linarith
  have hb₁ : b₁ = a₁ + 1 := by linarith
  have hb₂ : b₂ = a₂ + 1 := by linarith
  have hb₃ : b₃ = a₃ + 1 := by linarith
  rw [hb₀, hb₁, hb₂, hb₃]
  nlinarith [sq_nonneg (a₀ - a₁), sq_nonneg (a₀ - a₂),
    sq_nonneg (a₀ - a₃), sq_nonneg (a₁ - a₂),
    sq_nonneg (a₁ - a₃), sq_nonneg (a₂ - a₃)]

private theorem studentizedBaseline_sourceVarianceLowerBound :
    let H := proxyMomentMatrix studentizedBaseline 0
    let z := outcomeMomentVector studentizedBaseline 0 1
    let b := targetProxyVector studentizedBaseline
    let dSource := fderiv ℝ
      (fun hz : (Matrix (Fin 2) (Fin 2) ℝ) × (Fin 2 → ℝ) =>
        regularWaldFunctional (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
          hz.1 hz.2 b) (H, z)
    1 / 4 ≤ quadForm (multinomialCov (sourceCellVector (observedLaw studentizedBaseline)))
      (fun o => dSource (sourceStatisticDirection 0 1 o)) := by
  dsimp only
  let dSource := fderiv ℝ
    (fun hz : (Matrix (Fin 2) (Fin 2) ℝ) × (Fin 2 → ℝ) =>
      regularWaldFunctional (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
        hz.1 hz.2 (targetProxyVector studentizedBaseline))
    (proxyMomentMatrix studentizedBaseline 0,
      outcomeMomentVector studentizedBaseline 0 1)
  let d := fun o : Fin 2 × Fin 2 × Fin 1 × Fin 2 =>
    dSource (sourceStatisticDirection 0 1 o)
  have hgap (e w : Fin 2) : d (e, w, 0, 1) - d (e, w, 0, 0) = 1 :=
    by simpa only [d] using studentizedBaseline_sourceDerivative_outcomeGap e w
  rw [quadForm_multinomial_eq_moments]
  simp only [sourceCellVector, studentizedBaseline_observedLaw,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_unique]
  have h00 := hgap 0 0
  have h01 := hgap 0 1
  have h10 := hgap 1 0
  have h11 := hgap 1 1
  dsimp only [d] at h00 h01 h10 h11 ⊢
  simp only [show (default : Fin 1) = 0 by rfl] at *
  have hbound := eightPointPairVarianceLowerBound
    (dSource (sourceStatisticDirection (0 : Fin 1) (1 : Fin 2) (0, 0, 0, 0)))
    (dSource (sourceStatisticDirection (0 : Fin 1) (1 : Fin 2) (0, 1, 0, 0)))
    (dSource (sourceStatisticDirection (0 : Fin 1) (1 : Fin 2) (1, 0, 0, 0)))
    (dSource (sourceStatisticDirection (0 : Fin 1) (1 : Fin 2) (1, 1, 0, 0)))
    (dSource (sourceStatisticDirection (0 : Fin 1) (1 : Fin 2) (0, 0, 0, 1)))
    (dSource (sourceStatisticDirection (0 : Fin 1) (1 : Fin 2) (0, 1, 0, 1)))
    (dSource (sourceStatisticDirection (0 : Fin 1) (1 : Fin 2) (1, 0, 0, 1)))
    (dSource (sourceStatisticDirection (0 : Fin 1) (1 : Fin 2) (1, 1, 0, 1)))
    h00 h01 h10 h11
  convert hbound using 1 <;> ring

/-- [the baseline rank-one delta-method variance exceeds the stated positive lower bound](goal). -/
theorem studentizedBaseline_waldVarianceLowerBound (p : Set.Ioo (0 : ℝ) 1) :
    1 / 16 < waldDeltaVariance
      (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) p
      (observedLaw studentizedBaseline) 0 1 (targetProxyVector studentizedBaseline) := by
  let H := proxyMomentMatrix studentizedBaseline 0
  let z := outcomeMomentVector studentizedBaseline 0 1
  let b := targetProxyVector studentizedBaseline
  let dSource := fderiv ℝ
    (fun hz : (Matrix (Fin 2) (Fin 2) ℝ) × (Fin 2 → ℝ) =>
      regularWaldFunctional (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
        hz.1 hz.2 b) (H, z)
  let dTarget := fderiv ℝ
    (fun b' : Fin 2 → ℝ =>
      regularWaldFunctional (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) H z b') b
  let sourceVar := quadForm
    (multinomialCov (sourceCellVector (observedLaw studentizedBaseline)))
    (fun o => dSource (sourceStatisticDirection 0 1 o))
  let targetVar := quadForm (multinomialCov b) (fun w => dTarget (targetDirection w))
  have hs : 1 / 4 ≤ sourceVar := by
    simpa only [sourceVar, dSource, H, z, b] using
      studentizedBaseline_sourceVarianceLowerBound
  have ht : 0 ≤ targetVar := by
    apply multinomialCov_quadForm_nonneg
    · intro w
      simp [b, studentizedBaseline_targetProxy]
    · simp [b, studentizedBaseline_targetProxy, Fin.sum_univ_two]
  have hpInv : 1 ≤ (p : ℝ)⁻¹ := by
    exact (one_le_inv₀ p.2.1).2 (le_of_lt p.2.2)
  have hsourceNonneg : 0 ≤ sourceVar := le_trans (by norm_num) hs
  have hscaled : 1 / 4 ≤ (p : ℝ)⁻¹ * sourceVar := by
    calc
      1 / 4 ≤ 1 * sourceVar := by simpa using hs
      _ ≤ (p : ℝ)⁻¹ * sourceVar :=
        mul_le_mul_of_nonneg_right hpInv hsourceNonneg
  have htargetScaled : 0 ≤ (1 - (p : ℝ))⁻¹ * targetVar :=
    mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt p.2.2))) ht
  change 1 / 16 < (p : ℝ)⁻¹ * sourceVar + (1 - (p : ℝ))⁻¹ * targetVar
  linarith

/-- [the studentized baseline satisfies the stated rank-one singular-gap condition](goal). -/
theorem studentizedBaseline_singularGap :
    RegularSingularGap studentizedBaseline 0 1 (1 / 4) := by
  let H := proxyMomentMatrix studentizedBaseline 0
  let T := Matrix.toEuclideanLin H
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 1]
  have hvne : v ≠ 0 := by
    intro hv
    have hv0 := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hv
    norm_num [v] at hv0
  have hadj : T.adjoint = Matrix.toEuclideanLin H.transpose := by
    dsimp only [T]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rfl
  have hveig : (T.adjoint ∘ₗ T) v = (1 / 4 : ℝ) • v := by
    rw [hadj]
    apply PiLp.ext
    intro i
    fin_cases i <;>
      norm_num [T, H, v, Matrix.toEuclideanLin_apply, Matrix.mulVec,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
        Matrix.vecHead, Matrix.vecTail, studentizedBaseline_proxyMoment]
  have hvEigvec : Module.End.HasEigenvector (T.adjoint ∘ₗ T) (1 / 4 : ℝ) v :=
    ⟨Module.End.mem_eigenspace_iff.mpr hveig, hvne⟩
  have hvEigval : Module.End.HasEigenvalue (T.adjoint ∘ₗ T) (1 / 4 : ℝ) :=
    Module.End.hasEigenvalue_of_hasEigenvector hvEigvec
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  obtain ⟨i, hi⟩ := T.isSymmetric_adjoint_comp_self.exists_eigenvalues_eq hdim hvEigval
  have htop : (1 / 4 : ℝ) ≤
      T.isSymmetric_adjoint_comp_self.eigenvalues hdim (0 : Fin 2) := by
    rw [← hi]
    exact T.isSymmetric_adjoint_comp_self.eigenvalues_antitone hdim (Fin.zero_le i)
  have hsq := T.sq_singularValues_fin hdim (0 : Fin 2)
  have hsq' : T.singularValues 0 ^ 2 =
      T.isSymmetric_adjoint_comp_self.eigenvalues hdim (0 : Fin 2) := by
    simpa using hsq
  have hnonneg := T.singularValues_nonneg 0
  have hsquare : (1 / 4 : ℝ) ≤ T.singularValues 0 ^ 2 := by
    rw [hsq']
    exact htop
  have hhalf : (1 / 2 : ℝ) ≤ T.singularValues 0 := by
    nlinarith
  change 1 / 4 ≤ sigmaAt 1 H
  rw [sigmaAt_succ]
  exact (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) |>.trans hhalf

/-- [the studentized baseline belongs to the strongly identified regular submodel at the stated gap, variance floor, allocation fraction, treatment, and outcome](goal). -/
theorem studentizedBaseline_stronglyIdentified (p : Set.Ioo (0 : ℝ) 1) :
    studentizedBaseline ∈ stronglyIdentifiedSubmodelSet
      (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) (1 / 4) (1 / 16) p 0 1 := by
  refine ⟨studentizedBaseline_positive, by norm_num, by norm_num,
    studentizedBaseline_fixedRank, studentizedBaseline_singularGap,
    studentizedBaseline_unconditionalTargetSpan, studentizedBaseline_cellFloor, ?_⟩
  exact le_of_lt (studentizedBaseline_waldVarianceLowerBound p)

/-- The positive perturbation size used in row `n`. -/
noncomputable def weakRadius (n : ℕ) : ℝ := (n : ℝ)⁻¹ ^ 2

private theorem weakRadius_nonneg (n : ℕ) : 0 ≤ weakRadius n := by
  simp [weakRadius]

private theorem weakRadius_pos {n : ℕ} (hn : 2 ≤ n) : 0 < weakRadius n := by
  rw [weakRadius]
  positivity

private theorem weakRadius_le_quarter {n : ℕ} (hn : 2 ≤ n) : weakRadius n ≤ 1 / 4 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hi : (n : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hn'
  have hin : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  rw [weakRadius]
  nlinarith [sq_nonneg ((n : ℝ)⁻¹), sq_nonneg ((n : ℝ)⁻¹ - 1 / 2)]

private noncomputable def weakKernel (d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / 2 + d, 1 / 2 - d; 1 / 2 - d, 1 / 2 + d]

private noncomputable def weakOutcome (y u : Fin 2) : ℝ :=
  if y = 1 then (if u = 1 then 3 / 4 else 1 / 4)
  else (if u = 1 then 1 / 4 else 3 / 4)

private theorem weakKernel_col (d : ℝ) (u : Fin 2) : ∑ w, weakKernel d w u = 1 := by
  fin_cases u <;> norm_num [weakKernel, Fin.sum_univ_two]

private theorem weakOutcome_col (u : Fin 2) : ∑ y, weakOutcome y u = 1 := by
  fin_cases u <;> norm_num [weakOutcome, Fin.sum_univ_two]

private theorem fair_sum : ∑ e, fair e = 1 := by
  norm_num [fair, Fin.sum_univ_two]

/-- The full-rank weak row at index `n≥2`; outside that range it is merely a normalized SCM. -/
noncomputable def studentizedWeakModel (n : ℕ) :
    LatentShiftSCM (Fin 2) (Fin 2) (Fin 2) (Fin 1) (Fin 2) :=
  if hn : 2 ≤ n then
    let d := weakRadius n
    { environment_nonempty := inferInstance
      treatment_nonempty := inferInstance
      latent_card := by decide
      proxy_card := by decide
      outcome_card := by decide
      pi := fair
      S := weakKernel d
      M := weakKernel d
      a := fun _ _ => 1
      f := fun _ y u _ => weakOutcome y u
      q := ![1 / 4, 3 / 4]
      PM := fun e u w x y =>
        fair e * weakKernel d u e * weakKernel d w u * 1 * weakOutcome y u
      QM := fun u w x y =>
        (![1 / 4, 3 / 4] : Fin 2 → ℝ) u * weakKernel d w u * 1 * weakOutcome y u
      pi_nonneg := by intro e; fin_cases e <;> norm_num [fair]
      pi_sum := by norm_num [fair, Fin.sum_univ_two]
      S_nonneg := by
        intro u e; fin_cases u <;> fin_cases e <;> simp [weakKernel, d]
        all_goals linarith [weakRadius_nonneg n, weakRadius_le_quarter hn]
      S_col := by intro e; fin_cases e <;> norm_num [weakKernel, Fin.sum_univ_two]
      M_nonneg := by
        intro w u; fin_cases w <;> fin_cases u <;> simp [weakKernel, d]
        all_goals linarith [weakRadius_nonneg n, weakRadius_le_quarter hn]
      M_col := by intro u; fin_cases u <;> norm_num [weakKernel, Fin.sum_univ_two]
      a_nonneg := by intros; norm_num
      a_col := by intros; simp
      f_nonneg := by intros; simp [weakOutcome]; split_ifs <;> norm_num
      f_col := by intro x u w; fin_cases u <;> norm_num [weakOutcome, Fin.sum_univ_two]
      q_nonneg := by intro u; fin_cases u <;> norm_num
      q_sum := by norm_num [Fin.sum_univ_two]
      PM_nonneg := by
        intro e u w x y
        apply mul_nonneg
        · apply mul_nonneg
          · apply mul_nonneg
            · exact mul_nonneg (by fin_cases e <;> norm_num [fair])
                (by
                  fin_cases u <;> fin_cases e <;> simp [weakKernel, d]
                  all_goals linarith [weakRadius_nonneg n, weakRadius_le_quarter hn])
            · fin_cases w <;> fin_cases u <;> simp [weakKernel, d]
              all_goals linarith [weakRadius_nonneg n, weakRadius_le_quarter hn]
          · norm_num
        · simp [weakOutcome]; split_ifs <;> norm_num
      PM_sum := by
        norm_num [Fin.sum_univ_two, Fintype.sum_unique, fair, weakKernel, weakOutcome]
        <;> ring
      QM_nonneg := by
        intro u w x y
        apply mul_nonneg
        · apply mul_nonneg
          · apply mul_nonneg
            · fin_cases u <;> norm_num
            · fin_cases w <;> fin_cases u <;> simp [weakKernel, d]
              all_goals linarith [weakRadius_nonneg n, weakRadius_le_quarter hn]
          · norm_num
        · simp [weakOutcome]; split_ifs <;> norm_num
      QM_sum := by
        norm_num [Fin.sum_univ_two, Fintype.sum_unique, weakKernel, weakOutcome]
        <;> ring }
  else studentizedBaseline

/-- Given [the genuine-row or nonnegative-size condition](hyp:hn), [every genuine weak model satisfies the positive latent-shift assumptions](goal). -/
theorem studentizedWeakModel_positive (n : ℕ) (hn : 2 ≤ n) :
    PositiveLatentShiftClass (studentizedWeakModel n) := by
  rw [studentizedWeakModel, dif_pos hn]
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [LatentShiftFactorization]
  · simp [TargetMechanismInvariance]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e; fin_cases e <;> norm_num [fair]
    · intro u e; fin_cases u <;> fin_cases e <;> simp [weakKernel]
      all_goals linarith [weakRadius_nonneg n, weakRadius_le_quarter hn]
    · intro w u; fin_cases w <;> fin_cases u <;> simp [weakKernel]
      all_goals linarith [weakRadius_pos hn, weakRadius_le_quarter hn]
    · intros; norm_num
    · intros; simp [weakOutcome]; split_ifs <;> norm_num
    · intro u; fin_cases u <;> norm_num
  · change (weakKernel (weakRadius n)).rank = 2
    apply Matrix.rank_of_det_ne_zero
    rw [Matrix.det_fin_two]
    norm_num [weakKernel]
    exact ne_of_gt (by nlinarith [weakRadius_pos hn])

/-- Given [the genuine-row or nonnegative-size condition](hyp:hn), [every genuine weak model has causal value five eighths](goal). -/
theorem studentizedWeakModel_interventional (n : ℕ) (hn : 2 ≤ n) :
    interventionalProb (studentizedWeakModel n) 0 1 = 5 / 8 := by
  rw [studentizedWeakModel, dif_pos hn]
  norm_num [interventionalProb, weakOutcome, weakKernel, Fin.sum_univ_two]
  ring

/-- Given [the genuine-row or nonnegative-size condition](hyp:hn), [the weak model's conditional proxy matrix has the stated diagonal and off-diagonal entries](goal). -/
theorem studentizedWeakModel_condProxy (n : ℕ) (hn : 2 ≤ n) (w e : Fin 2) :
    condProxyMatrix (studentizedWeakModel n) 0 w e =
      if w = e then 1 / 2 + 2 * weakRadius n ^ 2
      else 1 / 2 - 2 * weakRadius n ^ 2 := by
  rw [studentizedWeakModel, dif_pos hn]
  fin_cases w <;> fin_cases e <;>
    norm_num [condProxyMatrix, observedLaw, fair, weakKernel, weakOutcome,
      Fin.sum_univ_two, Fintype.sum_unique]
  all_goals ring

/-- Given [the genuine-row or nonnegative-size condition](hyp:hn), [the weak model's target proxy vector has the stated oppositely shifted coordinates](goal). -/
theorem studentizedWeakModel_targetProxy (n : ℕ) (hn : 2 ≤ n) (w : Fin 2) :
    targetProxyVector (studentizedWeakModel n) w =
      if w = 0 then 1 / 2 - weakRadius n / 2 else 1 / 2 + weakRadius n / 2 := by
  rw [studentizedWeakModel, dif_pos hn]
  fin_cases w <;>
    norm_num [targetProxyVector, weakKernel, Fin.sum_univ_two]
  all_goals ring

/-- Given [the genuine-row or nonnegative-size condition](hyp:hn), [every observed-law cell of a genuine weak row is within the weak radius of its baseline counterpart](goal). -/
theorem studentizedWeakModel_observedLaw_close (n : ℕ) (hn : 2 ≤ n)
    (e w : Fin 2) (x : Fin 1) (y : Fin 2) :
    |observedLaw (studentizedWeakModel n) e w x y -
      observedLaw studentizedBaseline e w x y| ≤ weakRadius n := by
  have hdprod : 0 ≤ weakRadius n * (1 / 4 - weakRadius n) :=
    mul_nonneg (weakRadius_nonneg n) (sub_nonneg.mpr (weakRadius_le_quarter hn))
  have hd0 := weakRadius_nonneg n
  have hd4 := weakRadius_le_quarter hn
  rw [studentizedBaseline_observedLaw, studentizedWeakModel, dif_pos hn]
  fin_cases e <;> fin_cases w <;> fin_cases x <;> fin_cases y <;>
    norm_num [observedLaw, fair, weakKernel, weakOutcome,
      Fin.sum_univ_two, Fintype.sum_unique, abs_le]
  all_goals constructor <;> nlinarith

/-- Given [the genuine-row or nonnegative-size condition](hyp:hn), [the observed-data law of a genuine weak row is within eight weak radii of the baseline law in total variation](goal). -/
theorem studentizedWeakModel_observedMeasure_tv_le (n : ℕ) (hn : 2 ≤ n) :
    Causalean.Stat.tvDist (observedMeasure (studentizedWeakModel n))
      (observedMeasure studentizedBaseline) ≤ 8 * weakRadius n := by
  have htv :=
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.tvDist_pmf_toMeasure_le_tsum_abs
      (observedPMF (studentizedWeakModel n)) (observedPMF studentizedBaseline)
  refine htv.trans ?_
  rw [tsum_fintype]
  calc
    (∑ o : Fin 2 × Fin 2 × Fin 1 × Fin 2,
        |(observedPMF (studentizedWeakModel n) o).toReal -
          (observedPMF studentizedBaseline o).toReal|)
        = ∑ o, |observedLaw (studentizedWeakModel n) o.1 o.2.1 o.2.2.1 o.2.2.2 -
            observedLaw studentizedBaseline o.1 o.2.1 o.2.2.1 o.2.2.2| := by
          apply Finset.sum_congr rfl
          intro o _
          simp [observedPMF,
            ENNReal.toReal_ofReal (observedLaw_nonneg (studentizedWeakModel n) _ _ _ _),
            ENNReal.toReal_ofReal (observedLaw_nonneg studentizedBaseline _ _ _ _)]
    _ ≤ ∑ _o : Fin 2 × Fin 2 × Fin 1 × Fin 2, weakRadius n :=
      Finset.sum_le_sum fun o _ => studentizedWeakModel_observedLaw_close n hn
        o.1 o.2.1 o.2.2.1 o.2.2.2
    _ = 8 * weakRadius n := by norm_num [Fintype.card_prod]

/-- Given [the genuine-row or nonnegative-size condition](hyp:hn), [the target-proxy law of a genuine weak row is within one weak radius of the baseline law in total variation](goal). -/
theorem studentizedWeakModel_targetMeasure_tv_le (n : ℕ) (hn : 2 ≤ n) :
    Causalean.Stat.tvDist (targetProxyMeasure (studentizedWeakModel n))
      (targetProxyMeasure studentizedBaseline) ≤ weakRadius n := by
  have htv :=
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.tvDist_pmf_toMeasure_le_tsum_abs
      (targetProxyPMF (studentizedWeakModel n)) (targetProxyPMF studentizedBaseline)
  refine htv.trans ?_
  rw [tsum_fintype]
  calc
    (∑ w : Fin 2, |(targetProxyPMF (studentizedWeakModel n) w).toReal -
        (targetProxyPMF studentizedBaseline w).toReal|)
        = ∑ w : Fin 2, |targetProxyVector (studentizedWeakModel n) w -
            targetProxyVector studentizedBaseline w| := by
          apply Finset.sum_congr rfl
          intro w _
          simp [targetProxyPMF,
            ENNReal.toReal_ofReal (targetProxyVector_nonneg (studentizedWeakModel n) _),
            ENNReal.toReal_ofReal (targetProxyVector_nonneg studentizedBaseline _)]
    _ = weakRadius n := by
      rw [Fin.sum_univ_two, studentizedBaseline_targetProxy,
        studentizedBaseline_targetProxy, studentizedWeakModel_targetProxy n hn,
        studentizedWeakModel_targetProxy n hn]
      simp only [if_pos (show (0 : Fin 2) = 0 from rfl),
        if_neg (show (1 : Fin 2) ≠ 0 by decide), if_true]
      have hd0 := weakRadius_nonneg n
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      ring
    _ ≤ weakRadius n := le_rfl

/-- Given [the genuine-row or nonnegative-size condition](hyp:hn), [every genuine weak model satisfies the target-span restriction](goal). -/
theorem studentizedWeakModel_targetSpan (n : ℕ) (hn : 2 ≤ n) :
    (balancingFiber (condProxyMatrix (studentizedWeakModel n) 0)
      (targetProxyVector (studentizedWeakModel n))).Nonempty := by
  let d := weakRadius n
  have hd : d ≠ 0 := ne_of_gt (weakRadius_pos hn)
  have hd' : weakRadius n ≠ 0 := ne_of_gt (weakRadius_pos hn)
  let k : Fin 2 → ℝ := ![1 / 2 - 1 / (8 * d), 1 / 2 + 1 / (8 * d)]
  refine ⟨k, ?_⟩
  ext w
  rw [studentizedWeakModel_targetProxy n hn]
  simp only [Matrix.mulVec, Fin.sum_univ_two]
  simp_rw [studentizedWeakModel_condProxy n hn]
  fin_cases w
  · simp [dotProduct, Fin.sum_univ_two, k, d]
    field_simp [hd']
    ring
  · simp [dotProduct, Fin.sum_univ_two, k, d]
    field_simp [hd']
    ring

/-- The weak models equipped with their canonical finite two-sample product laws. -/
noncomputable def studentizedWeakArray (ns nt : ℕ → ℕ) :
    TwoSampleArray (Fin 2) (Fin 2) (Fin 2) (Fin 1) (Fin 2) ns nt where
  Mn := studentizedWeakModel
  rowLaw := fun n => twoSampleLaw (studentizedWeakModel n) (ns n) (nt n)
  rows_positive := studentizedWeakModel_positive

/-- Given [the admissible allocation condition](hyp:halloc), [the canonical weak triangular array belongs to the unrestricted target-span array class](goal). -/
theorem studentizedWeakArray_mem (p : Set.Ioo (0 : ℝ) 1) (ns nt : ℕ → ℕ)
    (halloc : TriangularAllocation ns nt p) :
    studentizedWeakArray ns nt ∈
      studentizedArrayClassSet p (0 : Fin 1) ns nt := by
  refine ⟨halloc, ?_, ?_, ?_⟩
  · intro n hn
    exact ⟨rfl, twoSampleLaw_sourceBlock _ _ _⟩
  · intro n hn
    exact ⟨rfl, twoSampleLaw_targetBlock _ _ _⟩
  · intro n hn
    exact studentizedWeakModel_targetSpan n hn

/-- Given [the genuine-row or nonnegative-size condition](hyp:hn), [every genuine row of the weak triangular array has causal value five eighths](goal). -/
theorem studentizedWeakArray_interventional (ns nt : ℕ → ℕ) (n : ℕ) (hn : 2 ≤ n) :
    rowInterventionalProb (studentizedWeakArray ns nt) n 0 1 = 5 / 8 := by
  exact studentizedWeakModel_interventional n hn

/-- Given [the genuine-row or nonnegative-size condition](hyp:hn), [the weak model's full two-sample law is within the stated sample-size multiple of the weak radius of the baseline row law](goal). -/
theorem studentizedWeakModel_twoSample_tv_le (ns nt n : ℕ) (hn : 2 ≤ n) :
    Causalean.Stat.tvDist (twoSampleLaw (studentizedWeakModel n) ns nt)
      (twoSampleLaw studentizedBaseline ns nt) ≤
        (8 * (ns : ℝ) + nt) * weakRadius n := by
  unfold twoSampleLaw
  calc
    Causalean.Stat.tvDist
        ((Measure.pi fun _ : Fin ns => observedMeasure (studentizedWeakModel n)).prod
          (Measure.pi fun _ : Fin nt => targetProxyMeasure (studentizedWeakModel n)))
        ((Measure.pi fun _ : Fin ns => observedMeasure studentizedBaseline).prod
          (Measure.pi fun _ : Fin nt => targetProxyMeasure studentizedBaseline))
        ≤ Causalean.Stat.tvDist
            (Measure.pi fun _ : Fin ns => observedMeasure (studentizedWeakModel n))
            (Measure.pi fun _ : Fin ns => observedMeasure studentizedBaseline) +
          Causalean.Stat.tvDist
            (Measure.pi fun _ : Fin nt => targetProxyMeasure (studentizedWeakModel n))
            (Measure.pi fun _ : Fin nt => targetProxyMeasure studentizedBaseline) :=
              tvDist_prod_le_add _ _ _ _
    _ ≤ (ns : ℝ) * (8 * weakRadius n) + (nt : ℝ) * weakRadius n := by
      gcongr
      · exact CausalSmith.Stat.DiscreteAteMinimaxLoggap.tvDist_pi_le_card_mul
          (observedMeasure (studentizedWeakModel n))
          (observedMeasure studentizedBaseline) ns |>.trans
            (mul_le_mul_of_nonneg_left (studentizedWeakModel_observedMeasure_tv_le n hn)
              (Nat.cast_nonneg ns))
      · exact CausalSmith.Stat.DiscreteAteMinimaxLoggap.tvDist_pi_le_card_mul
          (targetProxyMeasure (studentizedWeakModel n))
          (targetProxyMeasure studentizedBaseline) nt |>.trans
            (mul_le_mul_of_nonneg_left (studentizedWeakModel_targetMeasure_tv_le n hn)
              (Nat.cast_nonneg nt))
    _ = (8 * (ns : ℝ) + nt) * weakRadius n := by ring

/-- Given [the admissible allocation condition](hyp:halloc), [under an admissible allocation, the weak two-sample row laws converge in total variation to the fixed baseline row laws](goal). -/
theorem studentizedWeakArray_rowLaw_tendsto_tv_zero
    (p : Set.Ioo (0 : ℝ) 1) (ns nt : ℕ → ℕ)
    (halloc : TriangularAllocation ns nt p) :
    Filter.Tendsto (fun n => Causalean.Stat.tvDist
      ((studentizedWeakArray ns nt).rowLaw n)
      (twoSampleLaw studentizedBaseline (ns n) (nt n)))
      Filter.atTop (nhds 0) := by
  have hupper : ∀ᶠ n in Filter.atTop,
      Causalean.Stat.tvDist ((studentizedWeakArray ns nt).rowLaw n)
          (twoSampleLaw studentizedBaseline (ns n) (nt n)) ≤ 9 / (n : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    rw [show (studentizedWeakArray ns nt).rowLaw n =
      twoSampleLaw (studentizedWeakModel n) (ns n) (nt n) by rfl]
    calc
      Causalean.Stat.tvDist (twoSampleLaw (studentizedWeakModel n) (ns n) (nt n))
          (twoSampleLaw studentizedBaseline (ns n) (nt n))
          ≤ (8 * (ns n : ℝ) + nt n) * weakRadius n :=
            studentizedWeakModel_twoSample_tv_le (ns n) (nt n) n hn
      _ ≤ (9 * (n : ℝ)) * weakRadius n := by
        have hsum := (halloc.2.2.1 n hn).2.2
        have hns : (ns n : ℝ) ≤ n := by
          exact_mod_cast (Nat.le_of_add_right_le (le_of_eq hsum))
        have hnt : (nt n : ℝ) ≤ n := by
          exact_mod_cast (Nat.le_of_add_left_le (le_of_eq hsum))
        have hd0 := weakRadius_nonneg n
        gcongr
        linarith
      _ = 9 / (n : ℝ) := by
        rw [weakRadius]
        have hn0 : (n : ℝ) ≠ 0 := by positivity
        field_simp
  apply squeeze_zero'
  · apply Filter.Eventually.of_forall
    intro n
    change 0 ≤ Causalean.Stat.tvDist
      (twoSampleLaw (studentizedWeakModel n) (ns n) (nt n))
      (twoSampleLaw studentizedBaseline (ns n) (nt n))
    exact Causalean.Stat.tvDist_nonneg
  · exact hupper
  · have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have hconst : Filter.Tendsto (fun _ : ℕ => (9 : ℝ)) Filter.atTop (nhds 9) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv, Function.comp_def] using
      hconst.mul (tendsto_inv_atTop_zero.comp hcast)

end CausalSmith.SCM.ProxyTargetspanTransport

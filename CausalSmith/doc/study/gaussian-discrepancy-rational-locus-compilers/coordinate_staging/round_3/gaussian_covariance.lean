import Mathlib.Analysis.Matrix.Order
import Causalean.Stat.Limit.ContinuousMapping
import Causalean.Stat.MEstimation.FiniteModelSelection
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# Gaussian covariance discrepancy and finite model selection

This module defines the Gaussian covariance discrepancy on finite positive-definite matrices and
derives its compact-model attainment, strict separation, perturbation stability, and
finite-model-selection interfaces.  The model assumptions are stated separately from the matrix
inequality, so the results can be reused for any finite family of covariance models.
-/

open Filter MeasureTheory Set Topology
open scoped Matrix MatrixOrder

namespace Causalean.Stat

variable {V : Type*}

/-- For a [finite coordinate type](hyp:V), the [positive covariance matrices](goal) are real
square matrices equipped with a proof of positive definiteness. -/
abbrev PositiveCovariance (V : Type*) [Fintype V] :=
  {K : Matrix V V ℝ // Matrix.PosDef K}

/-- For a [candidate covariance matrix and target second-moment matrix](hyp:K,T), the [Gaussian
covariance discrepancy](goal) is log determinant plus inverse-weighted trace. -/
noncomputable def gaussianCovarianceDiscrepancy [Fintype V] [DecidableEq V]
    (K T : Matrix V V ℝ) : ℝ :=
  Real.log K.det + Matrix.trace (K⁻¹ * T)

/-- For [positive-definite candidate and target covariances](hyp:K,T), the [normalized Gaussian
covariance discrepancy](goal) subtracts the criterion's value at the target. -/
noncomputable def normalizedCovarianceDiscrepancy [Fintype V] [DecidableEq V]
    (K T : PositiveCovariance V) : ℝ :=
  gaussianCovarianceDiscrepancy (K : Matrix V V ℝ) T -
    gaussianCovarianceDiscrepancy (T : Matrix V V ℝ) T

/-- The [Gaussian covariance discrepancy varies continuously with its positive-definite candidate
and target matrix](goal). -/
theorem continuous_gaussianCovarianceDiscrepancy [Fintype V] [DecidableEq V] :
    Continuous (fun p : PositiveCovariance V × Matrix V V ℝ =>
      gaussianCovarianceDiscrepancy (p.1 : Matrix V V ℝ) p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  unfold gaussianCovarianceDiscrepancy
  apply ContinuousAt.add
  · apply ContinuousAt.log
    · fun_prop
    · exact ne_of_gt p.1.property.det_pos
  · apply (continuous_id.matrix_trace.continuousAt.comp)
    apply ContinuousAt.mul
    · have hinv : ContinuousAt (fun x : ℝ => Ring.inverse x) (p.1.1.det) := by
        simpa [Ring.inverse_eq_inv] using
          continuousAt_inv₀ (ne_of_gt p.1.property.det_pos)
      simpa [Function.comp_def] using
        (continuousAt_matrix_inv _ hinv).comp (x := p)
          ((continuous_subtype_val.comp continuous_fst).continuousAt)
    · fun_prop

/- Proof route for the matrix core below: whiten the candidate relative to the target, rewrite the
gap as a sum over the positive eigenvalues λ of the whitened matrix of
`log λ + λ⁻¹ - 1`, and use the scalar strict inequality.  Conjugation must preserve both the
determinant and the cyclic trace, and equality of every eigenvalue to one must be transported back
through the positive square root.  Do not assume the desired log-det inequality as a hypothesis. -/

/-- The [normalized Gaussian covariance discrepancy varies continuously with both
positive-definite covariances](goal). -/
theorem continuous_normalizedCovarianceDiscrepancy [Fintype V] [DecidableEq V] :
    Continuous (fun p : PositiveCovariance V × PositiveCovariance V =>
      normalizedCovarianceDiscrepancy p.1 p.2) := by
  unfold normalizedCovarianceDiscrepancy
  apply Continuous.sub
  · have h : Continuous (fun p : PositiveCovariance V × PositiveCovariance V =>
        (p.1, (p.2 : Matrix V V ℝ))) := by fun_prop
    exact continuous_gaussianCovarianceDiscrepancy.comp h
  · have h : Continuous (fun p : PositiveCovariance V × PositiveCovariance V =>
        (p.2, (p.2 : Matrix V V ℝ))) := by fun_prop
    exact continuous_gaussianCovarianceDiscrepancy.comp h

private theorem posDef_logdet_trace_gap_repr [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.PosDef) :
    -Real.log A.det + A.trace - (Fintype.card V : ℝ) =
      ∑ i, (hA.isHermitian.eigenvalues i - 1 -
        Real.log (hA.isHermitian.eigenvalues i)) := by
  have hlog : Real.log (∏ i, hA.isHermitian.eigenvalues i) =
      ∑ i, Real.log (hA.isHermitian.eigenvalues i) := by
    simpa using Real.log_prod
      (s := Finset.univ) (fun i _ => ne_of_gt (hA.eigenvalues_pos i))
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  change -Real.log (∏ i, hA.isHermitian.eigenvalues i) +
    A.trace - (Fintype.card V : ℝ) = _
  rw [hlog, hA.isHermitian.trace_eq_sum_eigenvalues]
  change -(∑ i, Real.log (hA.isHermitian.eigenvalues i)) +
    (∑ i, hA.isHermitian.eigenvalues i) - (Fintype.card V : ℝ) = _
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    mul_one, Finset.card_univ]
  ring

private theorem posDef_logdet_trace_gap_nonneg [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.PosDef) :
    0 ≤ -Real.log A.det + A.trace - (Fintype.card V : ℝ) := by
  rw [posDef_logdet_trace_gap_repr A hA]
  apply Finset.sum_nonneg
  intro i _
  linarith [Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i)]

private theorem posDef_logdet_trace_gap_eq_zero_iff [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.PosDef) :
    -Real.log A.det + A.trace - (Fintype.card V : ℝ) = 0 ↔ A = 1 := by
  constructor
  · intro h
    rw [posDef_logdet_trace_gap_repr A hA] at h
    have hnonneg : ∀ i ∈ Finset.univ,
        0 ≤ hA.isHermitian.eigenvalues i - 1 -
          Real.log (hA.isHermitian.eigenvalues i) := by
      intro i _
      linarith [Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i)]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h
    have heig : ∀ i, hA.isHermitian.eigenvalues i = 1 := by
      intro i
      have hi := hz i (Finset.mem_univ i)
      by_contra hne
      have hlt := Real.log_lt_sub_one_of_pos (hA.eigenvalues_pos i) hne
      linarith
    have hdiag : Matrix.diagonal
        (RCLike.ofReal ∘ hA.isHermitian.eigenvalues) = (1 : Matrix V V ℝ) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [heig]
      · simp [Matrix.diagonal, hij]
    rw [hA.isHermitian.spectral_theorem, hdiag]
    simp
  · rintro rfl
    simp

private theorem normalizedCovarianceDiscrepancy_whiten [Fintype V] [DecidableEq V]
    (K T : PositiveCovariance V) :
    let S := CFC.sqrt ((K : Matrix V V ℝ)⁻¹)
    let A := S * (T : Matrix V V ℝ) * S
    A.PosDef ∧
      normalizedCovarianceDiscrepancy K T =
        -Real.log A.det + A.trace - (Fintype.card V : ℝ) ∧
      (A = 1 ↔ K = T) := by
  dsimp
  let S := CFC.sqrt ((K : Matrix V V ℝ)⁻¹)
  have hKinv : ((K : Matrix V V ℝ)⁻¹).PosDef := K.property.inv
  have hSunit : IsUnit S := by
    apply (CFC.isUnit_sqrt_iff _ hKinv.posSemidef.nonneg).2
    exact hKinv.isUnit
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSunit
  have hSself : star S = S := (CFC.sqrt_nonneg _).star_eq
  have hSS : S * S = (K : Matrix V V ℝ)⁻¹ := by
    simpa [pow_two] using CFC.sq_sqrt ((K : Matrix V V ℝ)⁻¹)
      hKinv.posSemidef.nonneg
  have hA : (S * (T : Matrix V V ℝ) * S).PosDef := by
    simpa only [← Matrix.star_eq_conjTranspose, hSself] using
      T.property.conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_of_isUnit hSunit)
  have hdetA : (S * (T : Matrix V V ℝ) * S).det = K.1.det⁻¹ * T.1.det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    calc
      S.det * T.1.det * S.det = (S.det * S.det) * T.1.det := by ring
      _ = (S * S).det * T.1.det := by rw [Matrix.det_mul]
      _ = K.1⁻¹.det * T.1.det := by rw [hSS]
      _ = K.1.det⁻¹ * T.1.det := by
        rw [Matrix.det_nonsing_inv]
        simp [Ring.inverse_eq_inv]
  have htraceA : (S * (T : Matrix V V ℝ) * S).trace =
      (K.1⁻¹ * T.1).trace := by
    rw [Matrix.trace_mul_cycle, hSS]
  have hTinvT : T.1⁻¹ * T.1 = 1 := by
    apply Matrix.nonsing_inv_mul
    exact (Matrix.isUnit_iff_isUnit_det T.1).mp T.property.isUnit
  have hlogA : Real.log (S * (T : Matrix V V ℝ) * S).det =
      -Real.log K.1.det + Real.log T.1.det := by
    rw [hdetA, Real.log_mul]
    · rw [Real.log_inv]
    · exact inv_ne_zero (ne_of_gt K.property.det_pos)
    · exact ne_of_gt T.property.det_pos
  refine ⟨hA, ?_, ?_⟩
  · unfold normalizedCovarianceDiscrepancy gaussianCovarianceDiscrepancy
    rw [htraceA, hTinvT, Matrix.trace_one, hlogA]
    ring
  · constructor
    · intro hAone
      apply Subtype.ext
      have hSleft : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet
      have hSright : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
      symm
      calc
        T.1 = (S⁻¹ * S) * T.1 * (S * S⁻¹) := by
          rw [hSleft, hSright, one_mul, mul_one]
        _ = S⁻¹ * (S * T.1 * S) * S⁻¹ := by noncomm_ring
        _ = S⁻¹ * S⁻¹ := by rw [hAone, mul_one]
        _ = (S * S)⁻¹ := by rw [Matrix.mul_inv_rev]
        _ = K.1⁻¹⁻¹ := by rw [hSS]
        _ = K.1 := Matrix.nonsing_inv_nonsing_inv K.1
          ((Matrix.isUnit_iff_isUnit_det K.1).mp K.property.isUnit)
    · intro hKT
      have hSinvSq : S⁻¹ * S⁻¹ = K.1 := by
        rw [← Matrix.mul_inv_rev, hSS]
        exact Matrix.nonsing_inv_nonsing_inv K.1
          ((Matrix.isUnit_iff_isUnit_det K.1).mp K.property.isUnit)
      have hSleft : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet
      have hSright : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
      have hvals : T.1 = K.1 := (congrArg Subtype.val hKT).symm
      change S * T.1 * S = 1
      rw [hvals, ← hSinvSq]
      calc
        S * (S⁻¹ * S⁻¹) * S = (S * S⁻¹) * (S⁻¹ * S) := by
          noncomm_ring
        _ = 1 := by rw [hSright, hSleft, one_mul]

/-- For [positive-definite candidate and target covariances](hyp:K,T), the [normalized Gaussian
covariance discrepancy is nonnegative](goal). -/
theorem normalizedCovarianceDiscrepancy_nonneg [Fintype V] [DecidableEq V]
    (K T : PositiveCovariance V) :
    0 ≤ normalizedCovarianceDiscrepancy K T := by
  let S := CFC.sqrt ((K : Matrix V V ℝ)⁻¹)
  let A := S * (T : Matrix V V ℝ) * S
  obtain ⟨hA, hgap, -⟩ := normalizedCovarianceDiscrepancy_whiten K T
  rw [hgap]
  exact posDef_logdet_trace_gap_nonneg A hA

/-- For [positive-definite candidate and target covariances](hyp:K,T), the [normalized Gaussian
covariance discrepancy is zero exactly when the two covariances agree](goal). -/
theorem normalizedCovarianceDiscrepancy_eq_zero_iff [Fintype V] [DecidableEq V]
    (K T : PositiveCovariance V) :
    normalizedCovarianceDiscrepancy K T = 0 ↔ K = T := by
  let S := CFC.sqrt ((K : Matrix V V ℝ)⁻¹)
  let A := S * (T : Matrix V V ℝ) * S
  obtain ⟨hA, hgap, hAone⟩ := normalizedCovarianceDiscrepancy_whiten K T
  rw [hgap, posDef_logdet_trace_gap_eq_zero_iff A hA, hAone]

/-- For [positive-definite candidate and target covariances](hyp:K,T), the [candidate has no
larger Gaussian discrepancy than the truth exactly when it is the truth](goal). -/
theorem gaussianCovarianceDiscrepancy_le_truth_iff [Fintype V] [DecidableEq V]
    (K T : PositiveCovariance V) :
    gaussianCovarianceDiscrepancy (K : Matrix V V ℝ) T ≤
        gaussianCovarianceDiscrepancy (T : Matrix V V ℝ) T ↔
      K = T := by
  constructor
  · intro hle
    apply (normalizedCovarianceDiscrepancy_eq_zero_iff K T).mp
    have hnonneg := normalizedCovarianceDiscrepancy_nonneg K T
    unfold normalizedCovarianceDiscrepancy at hnonneg ⊢
    linarith
  · rintro rfl
    exact le_rfl

variable {V I Ω : Type*}

/-- For a [covariance model](hyp:M) and [target matrix](hyp:T), [discrepancy attainment](goal)
means that one model member has no larger Gaussian discrepancy than every other member. -/
def IsDiscrepancyAttainedOn [Fintype V] [DecidableEq V]
    (M : Set (PositiveCovariance V)) (T : Matrix V V ℝ) : Prop :=
  ∃ K ∈ M, ∀ L ∈ M,
    gaussianCovarianceDiscrepancy (K : Matrix V V ℝ) T ≤
      gaussianCovarianceDiscrepancy (L : Matrix V V ℝ) T

/-- For a [covariance model](hyp:M) and [target matrix](hyp:T), a [compact discrepancy
sublevel](goal) is a nonempty compact cut of the model below some criterion value. -/
def HasCompactDiscrepancySublevel [Fintype V] [DecidableEq V]
    (M : Set (PositiveCovariance V)) (T : Matrix V V ℝ) : Prop :=
  ∃ c : ℝ,
    (M ∩ {K | gaussianCovarianceDiscrepancy (K : Matrix V V ℝ) T ≤ c}).Nonempty ∧
    IsCompact (M ∩ {K | gaussianCovarianceDiscrepancy (K : Matrix V V ℝ) T ≤ c})

/-- Given a [compact covariance model](hyp:hM), [a nonempty model](hyp:hne), and [a target
matrix](hyp:T), the [Gaussian discrepancy minimum is attained](goal). -/
theorem discrepancyAttainedOn_of_isCompact [Fintype V] [DecidableEq V]
    {M : Set (PositiveCovariance V)} (hM : IsCompact M) (hne : M.Nonempty)
    (T : Matrix V V ℝ) :
    IsDiscrepancyAttainedOn M T := by
  have hcont : Continuous (fun K : PositiveCovariance V =>
      gaussianCovarianceDiscrepancy (K : Matrix V V ℝ) T) :=
    continuous_gaussianCovarianceDiscrepancy.comp
      (continuous_id.prodMk continuous_const)
  obtain ⟨K, hKM, _, hKmin⟩ :=
    hM.exists_sInf_image_eq_and_le hne hcont.continuousOn
  exact ⟨K, hKM, hKmin⟩

/-- Given [a covariance model with a nonempty compact discrepancy sublevel](hyp:hM), the [global
Gaussian discrepancy minimum is attained](goal). -/
theorem discrepancyAttainedOn_of_compactSublevel [Fintype V] [DecidableEq V]
    {M : Set (PositiveCovariance V)} {T : Matrix V V ℝ}
    (hM : HasCompactDiscrepancySublevel M T) :
    IsDiscrepancyAttainedOn M T := by
  rcases hM with ⟨c, hne, hcompact⟩
  let S : Set (PositiveCovariance V) :=
    M ∩ {K | gaussianCovarianceDiscrepancy (K : Matrix V V ℝ) T ≤ c}
  have hatt := discrepancyAttainedOn_of_isCompact (M := S) hcompact hne T
  rcases hatt with ⟨K, hKS, hKmin⟩
  refine ⟨K, hKS.1, ?_⟩
  intro L hLM
  by_cases hLc : gaussianCovarianceDiscrepancy (L : Matrix V V ℝ) T ≤ c
  · exact hKmin L ⟨hLM, hLc⟩
  · exact hKS.2.trans (le_of_lt (lt_of_not_ge hLc))

/-- Given [an attained covariance-model discrepancy](hyp:hatt) that [omits the positive-definite
truth](hyp:hT), [every model covariance has a common strictly positive normalized gap](goal). -/
theorem exists_positive_gap_of_attained [Fintype V] [DecidableEq V]
    {M : Set (PositiveCovariance V)} {T : PositiveCovariance V}
    (hatt : IsDiscrepancyAttainedOn M T) (hT : T ∉ M) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ K ∈ M, gap ≤ normalizedCovarianceDiscrepancy K T := by
  rcases hatt with ⟨K, hKM, hKmin⟩
  refine ⟨normalizedCovarianceDiscrepancy K T, ?_, ?_⟩
  · have hKT : K ≠ T := fun h => hT (h ▸ hKM)
    have hzero : normalizedCovarianceDiscrepancy K T ≠ 0 :=
      fun h => hKT ((normalizedCovarianceDiscrepancy_eq_zero_iff K T).mp h)
    exact lt_of_le_of_ne (normalizedCovarianceDiscrepancy_nonneg K T) hzero.symm
  · intro L hLM
    unfold normalizedCovarianceDiscrepancy
    linarith [hKmin L hLM]

/-- Given [a compact covariance model](hyp:hM), [a nonempty model](hyp:hne), and [a truth outside
the model](hyp:hT), the [model is separated from the truth by a strictly positive population
gap](goal). -/
theorem exists_positive_gap_of_isCompact [Fintype V] [DecidableEq V]
    {M : Set (PositiveCovariance V)} (hM : IsCompact M) (hne : M.Nonempty)
    {T : PositiveCovariance V} (hT : T ∉ M) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ K ∈ M, gap ≤ normalizedCovarianceDiscrepancy K T := by
  exact exists_positive_gap_of_attained
    (discrepancyAttainedOn_of_isCompact hM hne T) hT

/-- Given [a compact covariance model](hyp:hM), [a nonempty model](hyp:hne), and [a truth outside
the model](hyp:hT), the [strict positive population gap persists for nearby positive-definite
truths](goal). -/
theorem exists_stable_positive_gap [Fintype V] [DecidableEq V]
    {M : Set (PositiveCovariance V)} (hM : IsCompact M) (hne : M.Nonempty)
    {T : PositiveCovariance V} (hT : T ∉ M) :
    ∃ gap : ℝ, 0 < gap ∧ ∃ U ∈ nhds T,
      ∀ T' ∈ U, ∀ K ∈ M, gap ≤ normalizedCovarianceDiscrepancy K T' := by
  let m : PositiveCovariance V → ℝ := fun T' =>
    sInf ((fun K : PositiveCovariance V =>
      normalizedCovarianceDiscrepancy K T') '' M)
  have hjoint : Continuous (fun p : PositiveCovariance V × PositiveCovariance V =>
      normalizedCovarianceDiscrepancy p.2 p.1) :=
    continuous_normalizedCovarianceDiscrepancy.comp continuous_swap
  have hm : Continuous m := hM.continuous_sInf hjoint
  obtain ⟨delta, hdelta, hdelta_le⟩ :=
    exists_positive_gap_of_isCompact hM hne hT
  have hcontT : Continuous (fun K : PositiveCovariance V =>
      normalizedCovarianceDiscrepancy K T) :=
    continuous_normalizedCovarianceDiscrepancy.comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : PositiveCovariance V => T))
  obtain ⟨K0, hK0M, hm_eq, _⟩ :=
    hM.exists_sInf_image_eq_and_le hne hcontT.continuousOn
  have hhalf : 0 < delta / 2 := half_pos hdelta
  have hhalf_m : delta / 2 < m T := by
    dsimp [m]
    rw [hm_eq]
    exact lt_of_lt_of_le (half_lt_self hdelta) (hdelta_le K0 hK0M)
  refine ⟨delta / 2, hhalf, {T' | delta / 2 < m T'}, ?_, ?_⟩
  · exact (isOpen_lt continuous_const hm).mem_nhds hhalf_m
  · intro T' hT' K hKM
    exact hT'.le.trans (csInf_le
      (hM.image_of_continuousOn
        ((continuous_normalizedCovarianceDiscrepancy.comp
          (continuous_id.prodMk continuous_const)).continuousOn)).bddBelow
      (mem_image_of_mem _ hKM))

/-- For a [covariance model](hyp:M) and [target matrix](hyp:T), the [population loss](goal) is
the infimum Gaussian discrepancy over positive-definite model covariances. -/
noncomputable def covarianceModelLoss [Fintype V] [DecidableEq V]
    (M : Set (PositiveCovariance V)) (T : Matrix V V ℝ) : ℝ :=
  sInf ((fun K : PositiveCovariance V =>
    gaussianCovarianceDiscrepancy (K : Matrix V V ℝ) T) '' M)

/-- Given [a compact covariance model](hyp:hM) that is [nonempty](hyp:hne), the [population
loss is continuous in the target second-moment matrix](goal). -/
theorem continuous_covarianceModelLoss [Fintype V] [DecidableEq V]
    {M : Set (PositiveCovariance V)} (hM : IsCompact M) (hne : M.Nonempty) :
    Continuous (covarianceModelLoss M) := by
  unfold covarianceModelLoss
  have hjoint : Continuous (fun p : Matrix V V ℝ × PositiveCovariance V =>
      gaussianCovarianceDiscrepancy (p.2 : Matrix V V ℝ) p.1) :=
    continuous_gaussianCovarianceDiscrepancy.comp continuous_swap
  exact hM.continuous_sInf hjoint

private theorem covarianceModelLoss_ge_truth [Fintype V] [DecidableEq V]
    {M : Set (PositiveCovariance V)} (hM : IsCompact M) (hne : M.Nonempty)
    (T : PositiveCovariance V) :
    gaussianCovarianceDiscrepancy (T : Matrix V V ℝ) T ≤ covarianceModelLoss M T := by
  have hcontT : Continuous (fun K : PositiveCovariance V =>
      gaussianCovarianceDiscrepancy (K : Matrix V V ℝ) T) :=
    continuous_gaussianCovarianceDiscrepancy.comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : PositiveCovariance V =>
        (T : Matrix V V ℝ)))
  obtain ⟨K, hKM, hval, _⟩ :=
    hM.exists_sInf_image_eq_and_le hne hcontT.continuousOn
  rw [covarianceModelLoss, hval]
  have hnonneg := normalizedCovarianceDiscrepancy_nonneg K T
  unfold normalizedCovarianceDiscrepancy at hnonneg
  linarith

private theorem covarianceModelLoss_eq_truth_iff [Fintype V] [DecidableEq V]
    {M : Set (PositiveCovariance V)} (hM : IsCompact M) (hne : M.Nonempty)
    (T : PositiveCovariance V) :
    covarianceModelLoss M T = gaussianCovarianceDiscrepancy (T : Matrix V V ℝ) T ↔ T ∈ M := by
  have hcontT : Continuous (fun K : PositiveCovariance V =>
      gaussianCovarianceDiscrepancy (K : Matrix V V ℝ) T) :=
    continuous_gaussianCovarianceDiscrepancy.comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : PositiveCovariance V =>
        (T : Matrix V V ℝ)))
  obtain ⟨K, hKM, hval, _⟩ :=
    hM.exists_sInf_image_eq_and_le hne hcontT.continuousOn
  constructor
  · intro h
    have hKT : K = T := (gaussianCovarianceDiscrepancy_le_truth_iff K T).mp (by
        rw [← h, covarianceModelLoss, hval])
    simpa [hKT] using hKM
  · intro hTM
    apply le_antisymm
    · rw [covarianceModelLoss]
      exact csInf_le
        (hM.image_of_continuousOn
          ((continuous_gaussianCovarianceDiscrepancy.comp
            (continuous_id.prodMk continuous_const)).continuousOn)).bddBelow
        (mem_image_of_mem _ hTM)
    · exact covarianceModelLoss_ge_truth hM hne T

/-- Given [covariance models](hyp:models) that are [compact](hyp:hcompact) and
[nonempty](hyp:hne), a [positive-definite truth](hyp:T) contained in [some model](hyp:hcontains),
and [a model index](hyp:i), the [population minimizers are exactly the indices whose models
contain the truth](goal). -/
theorem populationMinimizers_covarianceModelLoss_iff [Fintype V] [DecidableEq V]
    [Fintype I] [Nonempty I]
    (models : I → Set (PositiveCovariance V))
    (hcompact : ∀ i, IsCompact (models i)) (hne : ∀ i, (models i).Nonempty)
    (T : PositiveCovariance V) (hcontains : ∃ i, T ∈ models i) (i : I) :
    i ∈ Causalean.Stat.populationMinimizers
        (fun j => covarianceModelLoss (models j) T) ↔
      T ∈ models i := by
  rcases hcontains with ⟨j0, hj0⟩
  rw [Causalean.Stat.populationMinimizers]
  constructor
  · intro hi
    apply (covarianceModelLoss_eq_truth_iff (hcompact i) (hne i) T).mp
    apply le_antisymm
    · calc
        covarianceModelLoss (models i) T ≤ covarianceModelLoss (models j0) T := hi j0
        _ = gaussianCovarianceDiscrepancy (T : Matrix V V ℝ) T :=
          (covarianceModelLoss_eq_truth_iff (hcompact j0) (hne j0) T).2 hj0
    · exact covarianceModelLoss_ge_truth (hcompact i) (hne i) T
  · intro hi j
    rw [(covarianceModelLoss_eq_truth_iff (hcompact i) (hne i) T).2 hi]
    exact covarianceModelLoss_ge_truth (hcompact j) (hne j) T

/-- Given [a finite family of covariance models](hyp:models) whose members are
[compact](hyp:hcompact) and [nonempty](hyp:hne), and a [positive-definite true covariance](hyp:T)
contained in [at least one model](hyp:hcontains), the [population losses have the positive gap
required by finite penalized model selection](goal). -/
theorem finiteCovarianceModel_populationGap [Fintype V] [DecidableEq V]
    [Fintype I] [Nonempty I]
    (models : I → Set (PositiveCovariance V))
    (hcompact : ∀ i, IsCompact (models i)) (hne : ∀ i, (models i).Nonempty)
    (T : PositiveCovariance V) (hcontains : ∃ i, T ∈ models i) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ i ∈ Causalean.Stat.populationMinimizers
          (fun j => covarianceModelLoss (models j) T),
        ∀ j ∉ Causalean.Stat.populationMinimizers
          (fun k => covarianceModelLoss (models k) T),
          covarianceModelLoss (models i) T + gap ≤
            covarianceModelLoss (models j) T := by
  classical
  let minimizers := Causalean.Stat.populationMinimizers
    (fun j => covarianceModelLoss (models j) T)
  let bad : Finset I := Finset.univ.filter fun j => j ∉ minimizers
  by_cases hbad : bad.Nonempty
  · obtain ⟨j0, hj0bad, hj0min⟩ := Finset.exists_min_image bad
      (fun j => covarianceModelLoss (models j) T) hbad
    have hj0not : j0 ∉ minimizers := (Finset.mem_filter.mp hj0bad).2
    have hj0T : T ∉ models j0 := by
      simpa [minimizers, populationMinimizers_covarianceModelLoss_iff
        models hcompact hne T hcontains j0] using hj0not
    have hbase_lt : gaussianCovarianceDiscrepancy (T : Matrix V V ℝ) T <
        covarianceModelLoss (models j0) T :=
      lt_of_le_of_ne (covarianceModelLoss_ge_truth (hcompact j0) (hne j0) T)
        (fun h => hj0T ((covarianceModelLoss_eq_truth_iff
          (hcompact j0) (hne j0) T).mp h.symm))
    refine ⟨covarianceModelLoss (models j0) T -
        gaussianCovarianceDiscrepancy (T : Matrix V V ℝ) T, sub_pos.mpr hbase_lt, ?_⟩
    intro i hi j hj
    have hiT : T ∈ models i := by
      exact (populationMinimizers_covarianceModelLoss_iff
        models hcompact hne T hcontains i).mp hi
    have hjbad : j ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    rw [(covarianceModelLoss_eq_truth_iff (hcompact i) (hne i) T).2 hiT]
    linarith [hj0min j hjbad]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro i hi j hj
    exfalso
    exact hbad ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

/-- Given [covariance models](hyp:models) that are [compact](hyp:hcompact) and
[nonempty](hyp:hne), an [empirical covariance sequence](hyp:Sn), a [target matrix](hyp:T), a
[sampling measure](hyp:P), and [entrywise convergence in probability](hyp:hSn), the [model losses
converge coordinatewise in probability](goal). -/
theorem tendstoInProb_covarianceModelLoss [MeasurableSpace Ω]
    [Fintype V] [DecidableEq V] [Fintype I]
    (models : I → Set (PositiveCovariance V))
    (hcompact : ∀ i, IsCompact (models i)) (hne : ∀ i, (models i).Nonempty)
    (Sn : ℕ → Ω → Matrix V V ℝ) (T : Matrix V V ℝ) (P : Measure Ω)
    (hSn : ∀ a b, Causalean.Stat.Tendsto_inProb
      (fun n ω => Sn n ω a b) (fun _ => T a b) P) :
    ∀ i, Causalean.Stat.Tendsto_inProb
      (fun n ω => covarianceModelLoss (models i) (Sn n ω))
      (fun _ => covarianceModelLoss (models i) T) P := by
  classical
  intro i
  let uncurryMatrix : ((V × V) → ℝ) → Matrix V V ℝ :=
    fun x a b => x (a, b)
  let Yn : ℕ → Ω → ((V × V) → ℝ) := fun n ω ab => Sn n ω ab.1 ab.2
  let c : (V × V) → ℝ := fun ab => T ab.1 ab.2
  let g : ((V × V) → ℝ) → ℝ := fun x =>
    covarianceModelLoss (models i) (uncurryMatrix x)
  have huncurry : Continuous uncurryMatrix := by
    fun_prop
  have hg : ContinuousAt g c :=
    ((continuous_covarianceModelLoss (hcompact i) (hne i)).comp huncurry).continuousAt
  have hcoord : ∀ ab, Causalean.Stat.Tendsto_inProb
      (fun n ω => Yn n ω ab) (fun _ => c ab) P := by
    rintro ⟨a, b⟩
    exact hSn a b
  simpa [Yn, c, g, uncurryMatrix] using
    Causalean.Stat.Tendsto_inProb.pi_comp_continuousAt hg hcoord


end Causalean.Stat


module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.NoisyIncompleteExperiment
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.SameLawCompletionRealization

/-! Structural realization of the duplicate Gaussian–Poisson experiment. The
single edge from the alternative target to coordinate zero changes the direct
strength while preserving identity latent covariance. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
noncomputable section
namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
variable {p n : ℕ} [NeZero p]

/-- The alternative mechanism has just the edge from `j` to zero; the baseline is zero. -/
-- @node: noisyIncompleteA
def noisyIncompleteA (j : Fin p) (h : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i k => if i = 0 ∧ k = j ∧ j ≠ 0 then h⁻¹ else 0

/-- Applying the one-edge mechanism reads just the target coordinate. -/
-- @node: noisyIncompleteA_mulVec
lemma noisyIncompleteA_mulVec (j : Fin p) (h : ℝ) (x : Fin p → ℝ) (i : Fin p) :
    (noisyIncompleteA j h *ᵥ x) i = if i = 0 ∧ j ≠ 0 then h⁻¹ * x j else 0 := by
  classical
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j]
  · by_cases hi : i = 0 ∧ j ≠ 0
    · simp [noisyIncompleteA, hi.1, hi.2]
    · simp only [noisyIncompleteA, Matrix.of_apply]
      split_ifs with hk <;> simp_all
  · intro k _ hk
    simp [noisyIncompleteA, hk]
  · simp

/-- Two consecutive edges are impossible, so the mechanism is square-zero. -/
-- @node: noisyIncompleteA_square
lemma noisyIncompleteA_square (j : Fin p) (h : ℝ) :
    noisyIncompleteA j h * noisyIncompleteA j h = 0 := by
  ext i k
  change (noisyIncompleteA j h *ᵥ (fun t => noisyIncompleteA j h t k)) i = 0
  rw [noisyIncompleteA_mulVec]
  split_ifs with hi
  · simp [noisyIncompleteA, hi.2]
  · rfl

/-- The one-edge support is acyclic, including at the duplicate baseline. -/
-- @node: noisyIncompleteA_acyclic
lemma noisyIncompleteA_acyclic (j : Fin p) (h : ℝ) :
    AcyclicMechanism (noisyIncompleteA j h) := by
  have hedge : ∀ a b, noisyIncompleteA j h b a ≠ 0 → a = j ∧ b = 0 ∧ j ≠ 0 := by
    intro a b hab
    by_cases hc : b = 0 ∧ a = j ∧ j ≠ 0
    · exact ⟨hc.2.1, hc.1, hc.2.2⟩
    · simp [noisyIncompleteA, hc] at hab
  have hpath : ∀ {a b}, Relation.TransGen (fun a b => noisyIncompleteA j h b a ≠ 0) a b →
      a = j ∧ b = 0 ∧ j ≠ 0 := by
    intro a b hab
    induction hab with
    | single hab => exact hedge _ _ hab
    | tail hab hbc ih =>
      obtain ⟨hc, _, hj⟩ := hedge _ _ hbc
      exact (hj (hc.symm.trans ih.2.1)).elim
  constructor
  · intro i
    simp only [noisyIncompleteA, Matrix.of_apply]
    split_ifs with hi
    · exact (hi.2.2 (hi.2.1.symm.trans hi.1)).elim
    · rfl
  · intro i hi
    obtain ⟨hij, hi0, hj⟩ := hpath hi
    exact hj (hij.symm.trans hi0)

/-- The explicit inverse of `I-A` is `I+A`. -/
-- @node: noisyIncompleteA_inverse_identity
lemma noisyIncompleteA_inverse_identity (j : Fin p) (h : ℝ) :
    (1 - noisyIncompleteA j h) * (1 + noisyIncompleteA j h) = 1 := by
  rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul,
    Matrix.one_mul, Matrix.mul_one, noisyIncompleteA_square, add_zero]
  abel

/-- The total-effect matrix is the identity plus the single edge. -/
-- @node: noisyIncomplete_totalEffect
lemma noisyIncomplete_totalEffect (j : Fin p) (h : ℝ) :
    totalEffect (noisyIncompleteA j h) = 1 + noisyIncompleteA j h :=
  Matrix.inv_eq_right_inv (noisyIncompleteA_inverse_identity j h)

/-- The inverse total-effect matrix acts on each environment mean by removing
its non-target effect, leaving an atomic intercept. -/
-- @node: noisyIncomplete_intercept
lemma noisyIncomplete_intercept (j : Fin p) (h : ℝ) (hh : h ≠ 0) (m : Fin p) :
    (1 - noisyIncompleteA j h) *ᵥ noisyIncompleteMean j h m.succ =
      (if j ≠ 0 ∧ m.val = 1 then h else 1) •
        Pi.single (if j ≠ 0 ∧ m.val = 1 then j else 0) 1 := by
  classical
  ext i
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [Pi.sub_apply, noisyIncompleteA_mulVec]
  have hm : m.succ ≠ 0 := Fin.succ_ne_zero m
  by_cases hc : j ≠ 0 ∧ m.val = 1
  · have hs : m.succ.val = 2 := by simp; omega
    simp only [noisyIncompleteMean, if_neg hm, if_pos (show j ≠ 0 ∧ m.succ.val = 2 from ⟨hc.1, hs⟩),
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_pos hc]
    by_cases hi : i = 0
    · subst i
      simp [hc.1, hc.1.symm, hc.2, hh]
    · simp [hi, hc.1, hc.2, Pi.single_apply]
  · have hs : ¬ (j ≠ 0 ∧ m.succ.val = 2) := by simpa using hc
    simp only [noisyIncompleteMean, if_neg hm, if_neg hs, add_zero, if_neg hc,
      Pi.smul_apply, smul_eq_mul, one_mul]
    split_ifs with hi
    · simp [Pi.single_apply, hi.2]
    · simp

/-- The inverse total effect is nonsingular. -/
-- @node: noisyIncomplete_inverse_isUnit
lemma noisyIncomplete_inverse_isUnit (j : Fin p) (h : ℝ) :
    IsUnit (1 - noisyIncompleteA j h) := by
  exact isUnit_iff_exists_inv.mpr ⟨1 + noisyIncompleteA j h,
    noisyIncompleteA_inverse_identity j h⟩

/-- Centering the latent cell gives a standard multivariate Gaussian. -/
-- @node: unitGaussianExperiment_centered_hasLaw
lemma unitGaussianExperiment_centered_hasLaw (ν : Fin (p + 1) → Fin p → ℝ)
    (e : Fin (p + 1)) (r : Fin n) :
    HasLaw (fun ω : PermutationOmega p n =>
      WithLp.toLp 2 (unitGaussianZ e r ω - ν e))
      (multivariateGaussian 0 (1 : Matrix (Fin p) (Fin p) ℝ))
      (unitGaussianExperimentMeasure ν) := by
  refine ⟨?_, ?_⟩
  · exact (show Measurable (fun ω : PermutationOmega p n =>
        WithLp.toLp 2 (unitGaussianZ e r ω - ν e)) by
      unfold unitGaussianZ
      fun_prop).aemeasurable
  · rw [show (fun ω : PermutationOmega p n =>
        WithLp.toLp 2 (unitGaussianZ e r ω - ν e)) =
        (fun z => WithLp.toLp 2 (z - ν e)) ∘ unitGaussianZ e r by rfl,
      ← Measure.map_map (by fun_prop) (by unfold unitGaussianZ; fun_prop),
      unitGaussianExperiment_Z_law, shiftedGaussianLaw_map_sub]

/-- Transforming the centered latent state by `I-A` provides a positive definite
Gaussian disturbance with the covariance specified in the construction. -/
-- @node: noisyIncomplete_gaussian
lemma noisyIncomplete_gaussian (j : Fin p) (h : ℝ) (r : Fin n) :
    GaussianDisturbance
      (unitGaussianExperimentMeasure (noisyIncompleteMean j h))
      (fun _ => (1 - noisyIncompleteA j h) * 1 * (1 - noisyIncompleteA j h).transpose)
      (fun e ω => (1 - noisyIncompleteA j h) *ᵥ
        (unitGaussianZ e r ω - noisyIncompleteMean j h e)) := by
  intro e
  constructor
  · exact Matrix.PosDef.one.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.mpr (noisyIncomplete_inverse_isUnit j h))
  · exact (multivariateGaussian_matrix_image_hasLaw (1 - noisyIncompleteA j h) 1
      Matrix.PosSemidef.one).comp
      (unitGaussianExperiment_centered_hasLaw (noisyIncompleteMean j h) e r)

/-- The structural latent state agrees pointwise with the Gaussian cell. -/
-- @node: noisyIncomplete_latentState
lemma noisyIncomplete_latentState (j : Fin p) (h : ℝ) (r : Fin n)
    (e : Fin (p + 1)) (ω : PermutationOmega p n) :
    latentState (noisyIncompleteA j h)
      (fun e => (1 - noisyIncompleteA j h) *ᵥ noisyIncompleteMean j h e)
      (fun e ω => (1 - noisyIncompleteA j h) *ᵥ
        (unitGaussianZ e r ω - noisyIncompleteMean j h e)) e ω =
      unitGaussianZ e r ω := by
  unfold latentState
  change totalEffect (noisyIncompleteA j h) *ᵥ
    ((1 - noisyIncompleteA j h) *ᵥ noisyIncompleteMean j h e +
      (1 - noisyIncompleteA j h) *ᵥ (unitGaussianZ e r ω - noisyIncompleteMean j h e)) = _
  rw [← Matrix.mulVec_add, add_sub_cancel, Matrix.mulVec_mulVec]
  rw [noisyIncomplete_totalEffect]
  have hinv : (1 + noisyIncompleteA j h) * (1 - noisyIncompleteA j h) = 1 :=
    mul_eq_one_comm.mp (noisyIncompleteA_inverse_identity j h)
  rw [hinv, Matrix.one_mulVec]

/-- Explicit invariant acyclic atomic model on the already constructed experiment. -/
-- @node: noisyIncompleteAtomicModel
def noisyIncompleteAtomicModel (j : Fin p) (h : ℝ) (hh : h ≠ 0) (r : Fin n) :
    AtomicCountModel p p (PermutationOmega p n)
      (unitGaussianExperimentMeasure (noisyIncompleteMean j h)) where
  p_pos := NeZero.pos p
  M_pos := NeZero.pos p
  A := noisyIncompleteA j h
  η := fun e => (1 - noisyIncompleteA j h) *ᵥ noisyIncompleteMean j h e
  Ωc := fun _ => (1 - noisyIncompleteA j h) * 1 * (1 - noisyIncompleteA j h).transpose
  α := fun m => if j ≠ 0 ∧ m.val = 1 then h else 1
  t := fun m => if j ≠ 0 ∧ m.val = 1 then j else 0
  ξ := fun e ω => (1 - noisyIncompleteA j h) *ᵥ
    (unitGaussianZ e r ω - noisyIncompleteMean j h e)
  S := fun e ω => unitGaussianS e r ω
  X := fun e ω => unitGaussianX e r ω
  acyclic := noisyIncompleteA_acyclic j h
  atomic := by
    intro m
    have hz : noisyIncompleteMean j h 0 = 0 := by simp [noisyIncompleteMean]
    simpa only [hz, Matrix.mulVec_zero, Pi.zero_apply, sub_zero] using
      noisyIncomplete_intercept j h hh m
  nonvanishing := by
    intro m
    dsimp
    split_ifs
    · exact hh
    · exact one_ne_zero
  gaussian := noisyIncomplete_gaussian j h r
  poisson := by
    intro e _
    simpa only [noisyIncomplete_latentState] using
      unitGaussianExperiment_poisson (noisyIncompleteMean j h) e r

/-- The observable mean of the structural realization is the prescribed cell mean. -/
-- @node: noisyIncompleteAtomicModel_obsMean
lemma noisyIncompleteAtomicModel_obsMean (j : Fin p) (h : ℝ) (hh : h ≠ 0)
    (r : Fin n) (e : Fin (p + 1)) :
    obsMean (unitGaussianExperimentMeasure (noisyIncompleteMean j h))
      (noisyIncompleteAtomicModel j h hh r) e = noisyIncompleteMean j h e := by
  rw [obsMean_eq_structural_mean]
  change totalEffect (noisyIncompleteA j h) *ᵥ
    ((1 - noisyIncompleteA j h) *ᵥ noisyIncompleteMean j h e) = _
  rw [noisyIncomplete_totalEffect, Matrix.mulVec_mulVec,
    mul_eq_one_comm.mp (noisyIncompleteA_inverse_identity j h), Matrix.one_mulVec]

/-- Observable intervention shifts equal the specified noncontrol means. -/
-- @node: noisyIncompleteAtomicModel_obsShift
lemma noisyIncompleteAtomicModel_obsShift (j : Fin p) (h : ℝ) (hh : h ≠ 0)
    (r : Fin n) (m : Fin p) :
    obsShift (unitGaussianExperimentMeasure (noisyIncompleteMean j h))
      (noisyIncompleteAtomicModel j h hh r) m = noisyIncompleteMean j h m.succ := by
  funext i
  rw [obsShift, noisyIncompleteAtomicModel_obsMean, noisyIncompleteAtomicModel_obsMean]
  simp [noisyIncompleteMean]

/-- The bounded-moment sample cells have exactly the realized structural model's
observable environment laws. -/
-- @node: noisyIncomplete_bounded_model_obsLaw
lemma noisyIncomplete_bounded_model_obsLaw (j : Fin p) (h ℓ v : ℝ)
    (hp : 0 < p) (hn : 0 < n) (hh : 0 < h ∧ h ≤ 1)
    (hℓ : 0 < ℓ ∧ ℓ ≤ Real.exp (1 / 2)) (hv : v0 1 ≤ v)
    (r₀ : Fin n) (e : Fin (p + 1)) (r : Fin n) :
    let μ := unitGaussianExperimentMeasure (n := n) (noisyIncompleteMean j h)
    let 𝒬 := noisyIncompleteBoundedMomentClass j h ℓ v hp hn hh hℓ hv
    μ.map (fun ω => (𝒬.S e r ω, 𝒬.X e r ω)) =
      obsLaw μ (noisyIncompleteAtomicModel j h hh.1.ne' r₀) e := by
  change (unitGaussianExperimentMeasure (noisyIncompleteMean j h)).map
      (fun ω => (unitGaussianS e r ω, unitGaussianX e r ω)) =
    (unitGaussianExperimentMeasure (noisyIncompleteMean j h)).map
      (fun ω => (unitGaussianS e r₀ ω, unitGaussianX e r₀ ω))
  exact ((unitGaussianExperiment_iid (noisyIncompleteMean j h) e).2 r r₀).map_eq

/-- The finite family has the claimed shifts, targets, strengths and amplified
non-target total effect, on the explicit bounded-moment experiment. -/
-- @node: noisyIncomplete_model_realization
lemma noisyIncomplete_model_realization (hp : 4 ≤ p) (hn : 0 < n)
    (j : Fin p) (h ℓ v : ℝ) (hh : 0 < h ∧ h ≤ 1)
    (hℓ : 0 < ℓ ∧ ℓ ≤ Real.exp (1 / 2)) (hv : v0 1 ≤ v) :
    let μ := unitGaussianExperimentMeasure (n := n) (noisyIncompleteMean j h)
    let 𝒬 := noisyIncompleteBoundedMomentClass j h ℓ v (by omega) hn hh hℓ hv
    ∃ 𝔐 : AtomicCountModel p p (PermutationOmega p n) μ,
      (∀ e r, μ.map (fun ω => (𝒬.S e r ω, 𝒬.X e r ω)) = obsLaw μ 𝔐 e) ∧
      (∀ e ω i, 𝔐.S e ω i = 1) ∧
      (if j = 0 then
        (∀ m, obsShift μ 𝔐 m = Pi.single 0 1 ∧ 𝔐.t m = 0)
       else
        obsShift μ 𝔐 1 = (fun i =>
          (Pi.single 0 (1 : ℝ) : Fin p → ℝ) i +
            h * (Pi.single j (1 : ℝ) : Fin p → ℝ) i) ∧
        𝔐.t 1 = j ∧ 𝔐.α 1 = h ∧ totalEffect 𝔐.A 0 j = h⁻¹ ∧
        (∀ m, m ≠ 1 → obsShift μ 𝔐 m = Pi.single 0 1 ∧ 𝔐.t m = 0)) := by
  classical
  have hmod : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  let r₀ : Fin n := ⟨0, hn⟩
  refine ⟨noisyIncompleteAtomicModel j h hh.1.ne' r₀, ?_, ?_, ?_⟩
  · exact noisyIncomplete_bounded_model_obsLaw j h ℓ v (by omega) hn hh hℓ hv r₀
  · intro e ω i
    rfl
  · by_cases hj : j = 0
    · simp only [if_pos hj]
      intro m
      constructor
      · rw [noisyIncompleteAtomicModel_obsShift]
        simp [noisyIncompleteMean, hj, Fin.succ_ne_zero]
      · simp [noisyIncompleteAtomicModel, hj]
    · simp only [if_neg hj]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [noisyIncompleteAtomicModel_obsShift]
        have henv : (1 : Fin p).succ ≠ 0 := Fin.succ_ne_zero _
        have hval : ((1 : Fin p).succ).val = 2 := by simp [hmod]
        ext i
        simp [noisyIncompleteMean, henv, hval, hmod, hj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      · simp [noisyIncompleteAtomicModel, hj, Fin.val_one, hmod]
      · simp [noisyIncompleteAtomicModel, hj, Fin.val_one, hmod]
      · change totalEffect (noisyIncompleteA j h) 0 j = _
        rw [noisyIncomplete_totalEffect]
        simp [noisyIncompleteA, hj, Ne.symm hj, Matrix.one_apply]
      · intro m hm
        have hmval : m.val ≠ 1 := by
          intro hv
          apply hm
          apply Fin.ext
          simpa [Fin.val_one, hmod] using hv
        constructor
        · rw [noisyIncompleteAtomicModel_obsShift]
          have henv : m.succ.val ≠ 2 := by simp; omega
          simp [noisyIncompleteMean, Fin.succ_ne_zero, henv, hmval]
        · simp [noisyIncompleteAtomicModel, hmval]

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.PermutationExperiment

/-! Unit-offset Gaussian–Poisson experiments with arbitrary environment means.
The coordinatewise mean bounds prove the moment-class conditions needed by the
noisy incomplete-cover construction. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

variable {p n : ℕ}

/-- The latent state in each independent environment-replicate cell. -/
-- @node: unitGaussianZ
def unitGaussianZ (e : Fin (p + 1)) (r : Fin n)
    (ω : PermutationOmega p n) : Fin p → ℝ := (ω (e, r)).1

/-- All observation offsets equal one. -/
-- @node: unitGaussianS
def unitGaussianS (_e : Fin (p + 1)) (_r : Fin n)
    (_ω : PermutationOmega p n) : Fin p → ℝ := fun _ => 1

/-- The observed counts in each independent cell. -/
-- @node: unitGaussianX
def unitGaussianX (e : Fin (p + 1)) (r : Fin n)
    (ω : PermutationOmega p n) : Fin p → ℕ := (ω (e, r)).2

/-- Independent Gaussian–Poisson cells share the specified mean within each environment. -/
-- @node: unitGaussianExperimentMeasure
def unitGaussianExperimentMeasure (ν : Fin (p + 1) → Fin p → ℝ) :
    Measure (PermutationOmega p n) :=
  Measure.pi fun er : Fin (p + 1) × Fin n =>
    permutationCellLaw (ν er.1)

/-- The experiment measure is the product of its environment-replicate cell laws. -/
-- @node: unitGaussianExperimentMeasure_eq_pi
lemma unitGaussianExperimentMeasure_eq_pi (ν : Fin (p + 1) → Fin p → ℝ) :
    unitGaussianExperimentMeasure (n := n) ν =
      Measure.pi (fun er : Fin (p + 1) × Fin n =>
        permutationCellLaw (ν er.1)) := rfl

/-- The independent cell experiment is a probability law. -/
-- @node: unitGaussianExperimentMeasure_probability
instance unitGaussianExperimentMeasure_probability
    (ν : Fin (p + 1) → Fin p → ℝ) :
    IsProbabilityMeasure (unitGaussianExperimentMeasure (n := n) ν) := by
  unfold unitGaussianExperimentMeasure
  infer_instance

/-- Each cell has its prescribed Gaussian–Poisson marginal law. -/
-- @node: unitGaussianExperiment_eval_law
lemma unitGaussianExperiment_eval_law (ν : Fin (p + 1) → Fin p → ℝ)
    (e : Fin (p + 1)) (r : Fin n) :
    (unitGaussianExperimentMeasure (n := n) ν).map (fun ω => ω (e, r)) =
      permutationCellLaw (ν e) := by
  exact (measurePreserving_eval
    (fun er : Fin (p + 1) × Fin n =>
      permutationCellLaw (ν er.1)) (e, r)).map_eq

/-- The latent vector in each cell has identity covariance and the specified mean. -/
-- @node: unitGaussianExperiment_Z_law
lemma unitGaussianExperiment_Z_law (ν : Fin (p + 1) → Fin p → ℝ)
    (e : Fin (p + 1)) (r : Fin n) :
    (unitGaussianExperimentMeasure (n := n) ν).map (unitGaussianZ e r) =
      shiftedGaussianLaw (ν e) := by
  rw [show unitGaussianZ e r = Prod.fst ∘ (fun ω : PermutationOmega p n => ω (e, r)) by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), unitGaussianExperiment_eval_law,
    permutationCellLaw_fst]

/-- Every cell obeys the conditional independent Poisson measurement model. -/
-- @node: unitGaussianExperiment_poisson
lemma unitGaussianExperiment_poisson (ν : Fin (p + 1) → Fin p → ℝ) :
    PoissonMeasurement (unitGaussianExperimentMeasure (n := n) ν)
      unitGaussianZ unitGaussianS unitGaussianX := by
  intro e r
  refine ⟨Filter.Eventually.of_forall (fun _ _ => by simp [unitGaussianS]),
    ?_, ?_, ?_⟩
  · have hZ : Measurable (unitGaussianZ e r) := by unfold unitGaussianZ; fun_prop
    exact (measurable_const.prodMk hZ).aemeasurable
  · have hZ : Measurable (unitGaussianZ e r) := by unfold unitGaussianZ; fun_prop
    have hX : Measurable (unitGaussianX e r) := by unfold unitGaussianX; fun_prop
    exact ((measurable_const.prodMk hZ).prodMk hX).aemeasurable
  have hcell := (permutationCell_poisson (ν e) () ()).2.2.2
  have hEval := unitGaussianExperiment_eval_law (n := n) ν e r
  have hSZ : (unitGaussianExperimentMeasure (n := n) ν).map
        (fun ω => (unitGaussianS e r ω, unitGaussianZ e r ω)) =
      (permutationCellLaw (ν e)).map
        (fun y => ((fun _ : Fin p => (1 : ℝ)), y.1)) := by
    rw [show (fun ω : PermutationOmega p n =>
        (unitGaussianS e r ω, unitGaussianZ e r ω)) =
        (fun y : PermutationCell p => ((fun _ : Fin p => (1 : ℝ)), y.1)) ∘
          (fun ω => ω (e, r)) by rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), hEval]
  have hfull : (unitGaussianExperimentMeasure (n := n) ν).map
        (fun ω => ((unitGaussianS e r ω, unitGaussianZ e r ω), unitGaussianX e r ω)) =
      (permutationCellLaw (ν e)).map
        (fun y => (((fun _ : Fin p => (1 : ℝ)), y.1), y.2)) := by
    rw [show (fun ω : PermutationOmega p n =>
        ((unitGaussianS e r ω, unitGaussianZ e r ω), unitGaussianX e r ω)) =
        (fun y : PermutationCell p => (((fun _ : Fin p => (1 : ℝ)), y.1), y.2)) ∘
          (fun ω => ω (e, r)) by rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), hEval]
  rw [hfull, hSZ]
  exact hcell

/-- Observed offset-count pairs are independent and identically distributed
within each environment. -/
-- @node: unitGaussianExperiment_iid
lemma unitGaussianExperiment_iid (ν : Fin (p + 1) → Fin p → ℝ) :
    IIDWithinEnvironment (unitGaussianExperimentMeasure (n := n) ν)
      unitGaussianS unitGaussianX := by
  intro e
  constructor
  · have hall : iIndepFun
        (fun er : Fin (p + 1) × Fin n =>
          fun ω : PermutationOmega p n => ω er)
        (unitGaussianExperimentMeasure (n := n) ν) := by
      unfold unitGaussianExperimentMeasure
      exact iIndepFun_pi
        (μ := fun er : Fin (p + 1) × Fin n =>
          permutationCellLaw (ν er.1))
        (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
    have heval := hall.precomp (g := fun r : Fin n => (e, r)) (by
      intro r s h
      exact congrArg Prod.snd h)
    let F : PermutationCell p → (Fin p → ℝ) × (Fin p → ℕ) :=
      fun y => ((fun _ => 1), y.2)
    have h := heval.comp (fun _ => F) (fun _ => by
      dsimp [F]
      fun_prop)
    change iIndepFun (fun r ω => ((fun _ : Fin p => (1 : ℝ)), (ω (e, r)).2))
      (unitGaussianExperimentMeasure (n := n) ν)
    simpa only [Function.comp_def, F] using h
  · intro r s
    refine IdentDistrib.mk
      ((measurable_const.prodMk ((measurable_pi_apply (e, r)).snd)).aemeasurable)
      ((measurable_const.prodMk ((measurable_pi_apply (e, s)).snd)).aemeasurable) ?_
    let F : PermutationCell p → (Fin p → ℝ) × (Fin p → ℕ) :=
      fun y => ((fun _ => 1), y.2)
    rw [show (fun ω : PermutationOmega p n =>
        (unitGaussianS e r ω, unitGaussianX e r ω)) =
        F ∘ (fun ω => ω (e, r)) by rfl,
      show (fun ω : PermutationOmega p n =>
        (unitGaussianS e s ω, unitGaussianX e s ω)) =
        F ∘ (fun ω => ω (e, s)) by rfl,
      ← Measure.map_map (by dsimp [F]; fun_prop) (by fun_prop),
      ← Measure.map_map (by dsimp [F]; fun_prop) (by fun_prop),
      unitGaussianExperiment_eval_law, unitGaussianExperiment_eval_law]

/-- Each latent coordinate has a normal law with its specified mean and unit variance. -/
-- @node: unitGaussianExperiment_Z_coord_law
lemma unitGaussianExperiment_Z_coord_law (ν : Fin (p + 1) → Fin p → ℝ)
    (e : Fin (p + 1)) (r : Fin n) (j : Fin p) :
    HasLaw (fun ω : PermutationOmega p n => unitGaussianZ e r ω j)
      (gaussianReal (ν e j) 1)
      (unitGaussianExperimentMeasure (n := n) ν) := by
  refine ⟨((measurable_pi_apply j).comp
    (measurable_fst.comp (measurable_pi_apply (e, r)))).aemeasurable, ?_⟩
  rw [show (fun ω : PermutationOmega p n => unitGaussianZ e r ω j) =
      (fun z => z j) ∘ unitGaussianZ e r by rfl,
    ← Measure.map_map (by fun_prop) (by unfold unitGaussianZ; fun_prop),
    unitGaussianExperiment_Z_law, shiftedGaussianLaw_eq_pi]
  exact (measurePreserving_eval (fun i => gaussianReal (ν e i) 1) j).map_eq

/-- Constant unit offsets are independent of the latent state. -/
-- @node: unitGaussianExperiment_exog
lemma unitGaussianExperiment_exog (ν : Fin (p + 1) → Fin p → ℝ) :
    OffsetExogeneity (unitGaussianExperimentMeasure (n := n) ν)
      unitGaussianS unitGaussianZ := by
  intro e r
  change IndepFun (fun _ : PermutationOmega p n => fun _ : Fin p => (1 : ℝ))
    (unitGaussianZ e r) (unitGaussianExperimentMeasure ν)
  exact
    (indepFun_const_right (unitGaussianZ e r)
      (fun _ : Fin p => (1 : ℝ))).symm

/-- Coordinate means at most one imply the stated factorial variance envelope. -/
-- @node: unitGaussianExperiment_varBound
lemma unitGaussianExperiment_varBound (ν : Fin (p + 1) → Fin p → ℝ) {v : ℝ}
    (hν : ∀ e j, ν e j ≤ 1) (hav : v0 1 ≤ v) :
    FactorialVarianceBound (unitGaussianExperimentMeasure (n := n) ν)
      unitGaussianZ unitGaussianS v := by
  constructor
  · intro e r j
    let b := ν e j
    have hZ := unitGaussianExperiment_Z_coord_law (n := n) ν e r j
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [one_mul] using integrable_exp_of_gaussian_law
        _ (fun ω => unitGaussianZ e r ω j) b 1 hZ
    · simpa only [one_mul] using memLp_exp_of_gaussian_law
        _ (fun ω => unitGaussianZ e r ω j) b 1 hZ
    · exact integrable_exp_of_gaussian_law
        _ (fun ω => unitGaussianZ e r ω j) b 2 hZ
    · exact memLp_exp_of_gaussian_law
        _ (fun ω => unitGaussianZ e r ω j) b 2 hZ
    · exact integrable_exp_of_gaussian_law
        _ (fun ω => unitGaussianZ e r ω j) b 3 hZ
    · simp [unitGaussianS]
    · simp [unitGaussianS]
  · intro e r j
    let b := ν e j
    have hZ := unitGaussianExperiment_Z_coord_law (n := n) ν e r j
    have hb := hν e j
    have henv := permutation_unit_offset_variance_envelope b 1 hb
    have h1 := variance_exp_of_gaussian_law
      _ (fun ω => unitGaussianZ e r ω j) b 1 hZ
    have h2 := variance_exp_of_gaussian_law
      _ (fun ω => unitGaussianZ e r ω j) b 2 hZ
    have hi1 := integral_exp_of_gaussian_law
      _ (fun ω => unitGaussianZ e r ω j) b 1 hZ
    have hi2 := integral_exp_of_gaussian_law
      _ (fun ω => unitGaussianZ e r ω j) b 2 hZ
    have hi3 := integral_exp_of_gaussian_law
      _ (fun ω => unitGaussianZ e r ω j) b 3 hZ
    have h1' : variance (fun ω => Real.exp (unitGaussianZ e r ω j))
        (unitGaussianExperimentMeasure ν) =
        Real.exp (2 * b * 1 + 2 * 1 ^ 2) -
          Real.exp (b * 1 + 1 ^ 2 / 2) ^ 2 := by
      simpa only [one_mul] using h1
    have hi1' : (∫ ω, Real.exp (unitGaussianZ e r ω j)
          ∂unitGaussianExperimentMeasure ν) =
        Real.exp (b * 1 + 1 ^ 2 / 2) := by
      simpa only [one_mul] using hi1
    have hmass : (unitGaussianExperimentMeasure (n := n) ν).real Set.univ = 1 := by
      simp [Measure.real_def]
    simp only [unitGaussianS, inv_one, integral_const, one_pow]
    rw [hmass]
    simp only [one_smul]
    rw [h1', h2, hi1', hi2, hi3]
    apply (max_le_iff.mpr ⟨?_, ?_⟩)
    · calc
        _ = Real.exp (b + 1 / 2) +
            (Real.exp 1 - 1) * Real.exp (2 * b + 1) := by
          norm_num
          rw [show Real.exp (2 * b + 2) =
              Real.exp 1 * Real.exp (2 * b + 1) by
                rw [← Real.exp_add]; congr 1; ring,
            show Real.exp (b + 1 / 2) ^ 2 = Real.exp (2 * b + 1) by
              rw [pow_two, ← Real.exp_add]; congr 1; ring]
          ring
        _ ≤ v0 1 := henv.1
        _ ≤ v := hav
    · calc
        _ = 4 * Real.exp (3 * b + 9 / 2) + 2 * Real.exp (2 * b + 2) +
            Real.exp (4 * b + 8) - Real.exp (4 * b + 4) := by
          norm_num
          rw [show Real.exp (b * 2 + 2) ^ 2 = Real.exp (4 * b + 4) by
            rw [pow_two, ← Real.exp_add]; congr 1; ring]
          rw [show Real.exp (2 * b * 2 + 8) = Real.exp (4 * b + 8) by
                congr 1; ring,
            show Real.exp (b * 3 + 9 / 2) = Real.exp (3 * b + 9 / 2) by
                congr 1; ring,
            show Real.exp (b * 2 + 2) = Real.exp (2 * b + 2) by
                congr 1; ring]
          ring
        _ ≤ v0 1 := henv.2
        _ ≤ v := hav

/-- Nonnegative latent means imply the required first factorial moment floor. -/
-- @node: unitGaussianExperiment_firstMoment
lemma unitGaussianExperiment_firstMoment (ν : Fin (p + 1) → Fin p → ℝ) {ℓ : ℝ}
    (hν : ∀ e j, 0 ≤ ν e j) (hℓ : ℓ ≤ Real.exp (1 / 2)) :
    FirstMomentNondegeneracy (unitGaussianExperimentMeasure (n := n) ν)
      unitGaussianS unitGaussianX ℓ := by
  intro e r j
  have hZ := unitGaussianExperiment_Z_coord_law (n := n) ν e r j
  have hP : PoissonMeasurement (unitGaussianExperimentMeasure (n := n) ν)
      (fun _ : Unit => fun _ : Unit => unitGaussianZ e r)
      (fun _ _ => unitGaussianS e r) (fun _ _ => unitGaussianX e r) := by
    intro _ _
    exact unitGaussianExperiment_poisson ν e r
  have h1 := integrable_exp_of_gaussian_law _
    (fun ω => unitGaussianZ e r ω j) (ν e j) 1 hZ
  have hdiag : Integrable
      (fun ω => Real.exp (unitGaussianZ e r ω j + unitGaussianZ e r ω j))
      (unitGaussianExperimentMeasure ν) := by
    convert integrable_exp_of_gaussian_law _
      (fun ω => unitGaussianZ e r ω j) (ν e j) 2 hZ using 1
    funext ω
    congr 1
    ring
  obtain ⟨hfirst, _⟩ := poisson_mixture_factorial_moment_transfer
    (unitGaussianExperimentMeasure ν) (unitGaussianS e r) (unitGaussianZ e r)
      (unitGaussianX e r) hP j j (by simpa only [one_mul] using h1) hdiag
  rw [hfirst]
  have hm := integral_exp_of_gaussian_law _
    (fun ω => unitGaussianZ e r ω j) (ν e j) 1 hZ
  simp only [one_mul] at hm
  rw [hm]
  norm_num
  exact hℓ.trans (Real.exp_le_exp.mpr (by
    have := hν e j
    linarith))

/-- Coordinate means between zero and one give an explicit bounded-moment experiment. -/
-- @node: unitGaussianBoundedMomentClass
def unitGaussianBoundedMomentClass (ν : Fin (p + 1) → Fin p → ℝ) {ℓ v : ℝ}
    (hp : 0 < p) (hn : 0 < n) (hν : ∀ e j, 0 ≤ ν e j ∧ ν e j ≤ 1)
    (hℓ : 0 < ℓ) (hℓle : ℓ ≤ Real.exp (1 / 2))
    (hv : 0 < v) (hav : v0 1 ≤ v) :
    BoundedMomentClass p n ℓ v (PermutationOmega p n)
      (unitGaussianExperimentMeasure ν) where
  p_pos := hp
  n_pos := hn
  ell_pos := hℓ
  ell_le := hℓle
  v_pos := hv
  Z := unitGaussianZ
  S := unitGaussianS
  X := unitGaussianX
  poisson := unitGaussianExperiment_poisson ν
  iid := unitGaussianExperiment_iid ν
  exog := unitGaussianExperiment_exog ν
  varBound := unitGaussianExperiment_varBound ν (fun e j => (hν e j).2) hav
  firstMoment := unitGaussianExperiment_firstMoment ν (fun e j => (hν e j).1) hℓle


/-- The baseline has duplicate means; alternative `j` adds `h` only in
coordinate `j` of environment two. The control mean is zero. -/
-- @node: noisyIncompleteMean
def noisyIncompleteMean [NeZero p] (j : Fin p) (h : ℝ)
    (e : Fin (p + 1)) : Fin p → ℝ :=
  if e = 0 then 0 else
    Pi.single 0 1 + if j ≠ 0 ∧ e.val = 2 then h • Pi.single j 1 else 0

/-- Every coordinate mean in the constructed finite family lies in `[0,1]`. -/
-- @node: noisyIncompleteMean_bounds
lemma noisyIncompleteMean_bounds [NeZero p] (j : Fin p) (h : ℝ)
    (hh : 0 ≤ h ∧ h ≤ 1) (e : Fin (p + 1)) (i : Fin p) :
    0 ≤ noisyIncompleteMean j h e i ∧ noisyIncompleteMean j h e i ≤ 1 := by
  by_cases he : e = 0
  · simp [noisyIncompleteMean, he]
  by_cases hj : j ≠ 0 ∧ e.val = 2
  · by_cases hi : i = 0
    · subst i
      simp [noisyIncompleteMean, he, hj]
    · by_cases hij : i = j
      · subst i
        simpa [noisyIncompleteMean, he, hj, Pi.single_apply, hj.1] using hh
      · simp [noisyIncompleteMean, he, hj, hi, hij]
  · by_cases hi : i = 0
    · subst i; simp [noisyIncompleteMean, he, hj]
    · simp [noisyIncompleteMean, he, hj, hi]

/-- The envelope bound supplies the positivity required by the moment class. -/
-- @node: noisyIncomplete_variance_pos
lemma noisyIncomplete_variance_pos (v : ℝ) (hv : v0 1 ≤ v) : 0 < v := by
  have he : 0 ≤ Real.exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  have hpos : 0 < Real.exp (1 + 1 / 2 : ℝ) +
      (Real.exp 1 - 1) * Real.exp (2 * 1 + 1) :=
    add_pos_of_pos_of_nonneg (Real.exp_pos _) (mul_nonneg he (Real.exp_nonneg _))
  exact hpos.trans_le ((le_max_left _ _).trans hv)

/-- The explicit unit-offset baseline and alternatives belong to the claimed
bounded-moment class without any additional moment assumptions. -/
-- @node: noisyIncompleteBoundedMomentClass
def noisyIncompleteBoundedMomentClass [NeZero p] (j : Fin p) (h ℓ v : ℝ)
    (hp : 0 < p) (hn : 0 < n) (hh : 0 < h ∧ h ≤ 1)
    (hℓ : 0 < ℓ ∧ ℓ ≤ Real.exp (1 / 2)) (hv : v0 1 ≤ v) :
    BoundedMomentClass p n ℓ v (PermutationOmega p n)
      (unitGaussianExperimentMeasure (noisyIncompleteMean j h)) :=
  unitGaussianBoundedMomentClass (noisyIncompleteMean j h) hp hn
    (noisyIncompleteMean_bounds j h ⟨hh.1.le, hh.2⟩) hℓ.1 hℓ.2
    (noisyIncomplete_variance_pos v hv) hv

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

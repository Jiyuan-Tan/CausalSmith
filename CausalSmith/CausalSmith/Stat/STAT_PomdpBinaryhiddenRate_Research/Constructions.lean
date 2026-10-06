module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Basic
public import Causalean.Stat.Minimax.MinimaxValue
public import Causalean.Stat.Minimax.MinimaxRisk

/-!
# Finite grid and positive testing constructions

The exhaustive rational grid, observable-data minimax functional, and finite
four-state testing family are defined from the binary POMDP carrier.
-/

@[expose] public section

set_option linter.style.longLine false

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- Grid resolution in the estimator construction. -/
noncomputable def gridSize (T : Nat) (alpha : ℝ) : Nat :=
  Nat.ceil ((22 + 36 / alpha) * T)
  -- @realizes \(M\)(ceiling grid resolution)

/-- Unfiltered finite tuple carrying an initial law, four transition rows, and rewards. -/
abbrev GridCode (M : Nat) :=
  (Fin 4 → Fin (M + 1)) × (Fin 4 → Fin 4 → Fin (M + 1)) ×
    (Fin 4 → Fin (M + 1))

/-- A simplex grid row is a nonnegative integer tuple summing to `M`. -/
def IsGridRow (M : Nat) (u : Fin 4 → Fin (M + 1)) : Prop :=
  ∑ i, (u i).val = M

/-- Enumerate just the four-coordinate simplex rows. -/
noncomputable def simplexGrid (M : Nat) : Finset (Fin 4 → Fin (M + 1)) := by
  classical
  exact Finset.univ.filter (IsGridRow M)

/-- Enumerate four simplex rows as a transition matrix. -/
noncomputable def gridMatrixRows (M : Nat) :
    Finset (Fin 4 → Fin 4 → Fin (M + 1)) := by
  classical
  let rows : Finset ((i : Fin 4) →
      i ∈ (Finset.univ : Finset (Fin 4)) → Fin 4 → Fin (M + 1)) :=
    Finset.pi Finset.univ (fun _ ↦ simplexGrid M)
  exact rows.image (fun R i ↦ R i (Finset.mem_univ i))

/-- Cartesian enumeration before the Dobrushin filter. -/
noncomputable def gridCandidateUniverse (M : Nat) : Finset (GridCode M) := by
  classical
  exact (simplexGrid M).biUnion (fun nu ↦
    (gridMatrixRows M).biUnion (fun R ↦
      (Finset.univ : Finset (Fin 4 → Fin (M + 1))).image
        (fun r ↦ (nu, R, r))))

/-- The grid code's initial distribution. -/
noncomputable def gridNu {M : Nat} (c : GridCode M) : Fin 4 → ℝ :=
  fun i ↦ (c.1 i).val / (M : ℝ)

/-- The grid code's stochastic matrix before the stability filter. -/
noncomputable def gridR {M : Nat} (c : GridCode M) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j ↦ (c.2.1 i j).val / (M : ℝ)

/-- The grid code's reward vector. -/
noncomputable def gridReward {M : Nat} (c : GridCode M) : Fin 4 → ℝ :=
  fun i ↦ (c.2.2 i).val / (M : ℝ)

/-- The stable transition matrix is mixed with the uniform reset kernel. -/
noncomputable def stabilizedGridMatrix (alpha : ℝ) {M : Nat}
    (c : GridCode M) : Matrix (Fin 4) (Fin 4) ℝ :=
  let lambda := alpha / (alpha + 6 / (M : ℝ))
  fun i j ↦ lambda * gridR c i j + (1 - lambda) / 4

/-- A four-point version of the Dobrushin coefficient for grid rows. -/
noncomputable def gridDobrushin (R : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ⨆ i : Fin 4, ⨆ j : Fin 4,
    (1 / 2 : ℝ) * ∑ s, |R i s - R j s|

/-- The finite candidate set, before fitting observable moments. -/
noncomputable def gridCandidates (M : Nat) (alpha : ℝ) : Finset (GridCode M) :=
  by
    classical
    exact (gridCandidateUniverse M).filter (fun c ↦
      gridDobrushin (gridR c) ≤ alpha + 6 / (M : ℝ))

/-- Seven-moment worst residual of a stable candidate. -/
noncomputable def gridObjective {T M : Nat} (alpha : ℝ)
    (b e : Policy 2) (w : ObsView T 2) (c : GridCode M) : ℝ :=
  ⨆ k : Fin 7,
    |empiricalMoment k.val b e w -
      ∑ s : Fin 4,
        (Matrix.vecMul (gridNu c) ((stabilizedGridMatrix alpha c) ^ k.val)) s *
          gridReward c s|

/-- A base-`M+1` code supplies a fixed lexicographic tie break. -/
def gridLexCode {M : Nat} (c : GridCode M) : Nat :=
  let digits : List Nat :=
    (List.ofFn fun i : Fin 4 ↦ (c.1 i).val) ++
    (List.ofFn fun i : Fin 4 ↦ (List.ofFn fun j : Fin 4 ↦ (c.2.1 i j).val)).flatten ++
    (List.ofFn fun i : Fin 4 ↦ (c.2.2 i).val)
  digits.foldl (fun n d ↦ n * (M + 1) + d) 0

/-- Select a minimum-residual candidate, then the least grid code among ties. -/
noncomputable def selectGridCode {T M : Nat} (alpha : ℝ)
    (b e : Policy 2) (w : ObsView T 2) : GridCode M :=
  let candidates := gridCandidates M alpha
  if h : candidates.Nonempty then
    let c0 := Classical.choose (Finset.exists_min_image candidates
      (gridObjective alpha b e w) h)
    let minima := candidates.filter (fun c ↦
      gridObjective alpha b e w c = gridObjective alpha b e w c0)
    if hm : minima.Nonempty then
      Classical.choose (Finset.exists_min_image minima gridLexCode hm)
    else c0
  else default

-- @node: def:stable-grid-estimator
/-- Finite stable-grid estimator selected by seven observable moments. -/
noncomputable def stableGridEstimator (T : Nat) (t0 : ℝ)
    (b e : Policy 2) (w : ObsView T 2) : ℝ :=
  let alpha := mixingAlpha t0
  let c := selectGridCode (M := gridSize T alpha) alpha b e w
  ∑ s : Fin 4,
    stationaryLaw (stabilizedGridMatrix alpha c) s * gridReward c s
  -- @realizes \(\widehat\theta_T\)(stationary reward of selected stable grid matrix)

/-- Raw procedures see only policies and the observed trajectory. -/
abbrev RawEstimator (T : Nat) := Policy 2 → Policy 2 → ObsView T 2 → ℝ

/-- Bounded measurable observable estimators; clipping to `[0,1]` is loss reducing. -/
def ObservableEstimator (T : Nat) : Type :=
  {est : RawEstimator T //
    (∀ b e w, est b e w ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ b e, Measurable (est b e))}

/-- A fixed binary model index carries exactly the six law conditions. -/
structure ModelIndex (T : Nat) (t0 zeta : ℝ) where
  raw : RawPomdpExperiment T 2 2
  mem : BinaryPomdpClass t0 zeta raw -- @realizes \(\mathcal M_T^{(2)}(t_0,\zeta)\)(model membership)

/-- Observed-data squared risk at a binary POMDP law. -/
noncomputable def observedRisk {T : Nat} {t0 zeta : ℝ}
    (est : ObservableEstimator T) (m : ModelIndex T t0 zeta) : ℝ :=
  Causalean.Stat.sqRisk (obsLaw m.raw) (est.1 m.raw.b m.raw.e)
    (targetValue m.raw)

-- @env: S3
variable (est : ObservableEstimator T)

-- @node: def:minimax-risk
/-- Observable-data minimax squared risk over the fixed binary class. -/
noncomputable def minimaxRisk (T : Nat) (t0 zeta : ℝ) : ℝ :=
  Causalean.Stat.minimaxValueReal
    (observedRisk (T := T) (t0 := t0) (zeta := zeta))
  -- @realizes \(R_T^{(2)}(t_0,\zeta)\)(infimum of worst-case squared risk)

/-- Perturbation amplitude for the two testing laws. -/
noncomputable def vT (T : Nat) : ℝ := 1 / (16 * Real.sqrt T)

/-- On the theorem's positive-horizon domain, the testing amplitude has the paper's range. [Under the listed formal conditions](hyp:hTpos), [the stated conclusion holds](goal).-/
lemma vT_mem_Ioc (T : Nat) (hTpos : 0 < T) :
    vT T ∈ Set.Ioc (0 : ℝ) (1 / 16) := by
  -- @realizes \(v_T\)(positive-horizon formula and range)
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hTpos
  have hsqrt : (1 : ℝ) ≤ Real.sqrt T := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hT'
  have hpos : 0 < Real.sqrt T := lt_of_lt_of_le (by norm_num) hsqrt
  unfold vT
  constructor
  · exact one_div_pos.mpr (by positivity)
  · apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * Real.sqrt T)
      (by norm_num : (0 : ℝ) < 16)).mpr
    nlinarith

/-- Positive Bernoulli probability for a reward under hidden state `h`. -/
noncomputable def testingRewardProb (v : ℝ) (h : Fin 2) : ℝ :=
  1 / 2 + (if h = 1 then 1 / 8 else -(1 / 8)) + v

/-- Hidden-state successor probability controlled by the action. -/
noncomputable def testingHiddenProb (a : Bool) : ℝ :=
  if a then 3 / 4 else 1 / 4

/-- Observed-state emission probability given the successor hidden state. -/
noncomputable def testingEmission (x h : Fin 2) : ℝ :=
  if x = h then 3 / 5 else 2 / 5

-- @node: testingStepMass_sum
/-- The successor hidden-state and emission factors form a probability row. [the stated conclusion holds](goal).-/
lemma testingStepMass_sum (a : Bool) :
    ∑ sp : JointState 2 2,
      (if sp.2 = 1 then testingHiddenProb a else 1 - testingHiddenProb a) *
        testingEmission sp.1 sp.2 = 1 := by
  cases a <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, testingHiddenProb,
      testingEmission] <;> norm_num

-- @node: testingInitialMass_sum
/-- The stationary initialization weights sum to one. [the stated conclusion holds](goal).-/
lemma testingInitialMass_sum :
    ∑ s : JointState 2 2, (1 / 2 : ℝ) * testingEmission s.1 s.2 = 1 := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, testingEmission]
  norm_num

-- @node: testingRewardMass_sum
/-- The two conditional reward masses sum to one. [Under the listed formal conditions](hyp:h), [the stated conclusion holds](goal).-/
lemma testingRewardMass_sum (v : ℝ) (h : Fin 2) :
    ∑ y : Bool, (if y then testingRewardProb v h else 1 - testingRewardProb v h) = 1 := by
  simp

-- @node: testingOneStepMass_sum
/-- Summing a complete action, reward, and successor block gives unit mass. [the stated conclusion holds](goal).-/
lemma testingOneStepMass_sum (v : ℝ) (s : JointState 2 2) :
    ∑ a : Bool, ∑ y : Bool, ∑ sp : JointState 2 2,
      (1 / 2 : ℝ) *
      (if y then testingRewardProb v s.2 else 1 - testingRewardProb v s.2) *
      (if sp.2 = 1 then testingHiddenProb a else 1 - testingHiddenProb a) *
      testingEmission sp.1 sp.2 = 1 := by
  simp_rw [mul_assoc]
  simp_rw [← Finset.mul_sum]
  simp_rw [testingStepMass_sum]
  simp_rw [mul_one]
  simp_rw [testingRewardMass_sum]
  simp

-- @node: testingStateMass_sum
/-- A normalized successor law at each epoch and the stationary initial law
give a normalized sequence of joint states. [Under the listed formal conditions](hyp:hq), [the stated conclusion holds](goal).-/
lemma testingStateMass_sum (T : Nat) (q : JointState 2 2 → ℝ)
    (hq : ∑ s : JointState 2 2, q s = 1) :
    ∑ xs : Fin (T + 1) → JointState 2 2,
      ((1 / 2 : ℝ) * testingEmission (xs 0).1 (xs 0).2) *
        ∏ t : Fin T, q (xs t.succ) = 1 := by
  let e := Fin.consEquiv (fun _ : Fin (T + 1) => JointState 2 2)
  have he :
      (∑ xs : Fin (T + 1) → JointState 2 2,
        ((1 / 2 : ℝ) * testingEmission (xs 0).1 (xs 0).2) *
          ∏ t : Fin T, q (xs t.succ)) =
      ∑ z : JointState 2 2 × (Fin T → JointState 2 2),
        ((1 / 2 : ℝ) * testingEmission z.1.1 z.1.2) *
          ∏ t : Fin T, q (z.2 t) := by
    exact (Fintype.sum_equiv e _ _ (by intro z; simp [e])).symm
  rw [he, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  have hp : (∑ f : Fin T → JointState 2 2, ∏ t : Fin T, q (f t)) = 1 := by
    simpa [Fintype.piFinset_univ, hq] using
      (Finset.sum_prod_piFinset (Finset.univ : Finset (JointState 2 2))
        (fun (_ : Fin T) s => q s))
  rw [hp]
  simpa using testingInitialMass_sum

-- @node: testingNextStateMass
/-- The successor-state mass after averaging over a fair action. -/
noncomputable def testingNextStateMass (sp : JointState 2 2) : ℝ :=
  ∑ a : Bool, (1 / 2 : ℝ) *
    (if sp.2 = 1 then testingHiddenProb a else 1 - testingHiddenProb a) *
    testingEmission sp.1 sp.2

/-- For the testing construction, the conditional next-state mass function sums to one. [the stated conclusion holds](goal).
-/
-- @node: testingNextStateMass_sum
lemma testingNextStateMass_sum :
    ∑ sp : JointState 2 2, testingNextStateMass sp = 1 := by
  simp only [testingNextStateMass]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, testingStepMass_sum]
  norm_num

-- @node: testingStepMarginal_sum
/-- Summing a reward and action block leaves the successor-state mass. [the stated conclusion holds](goal).-/
lemma testingStepMarginal_sum (v : ℝ) (s sp : JointState 2 2) :
    ∑ ay : Bool × Bool,
      (1 / 2 : ℝ) *
        (if ay.2 then testingRewardProb v s.2 else 1 - testingRewardProb v s.2) *
        (if sp.2 = 1 then testingHiddenProb ay.1 else 1 - testingHiddenProb ay.1) *
        testingEmission sp.1 sp.2 = testingNextStateMass sp := by
  simp only [Fintype.sum_prod_type, testingNextStateMass]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = (1 / 2 : ℝ) *
        ((if sp.2 = 1 then testingHiddenProb a else 1 - testingHiddenProb a) *
          testingEmission sp.1 sp.2) *
        (∑ y : Bool, if y then testingRewardProb v s.2 else 1 - testingRewardProb v s.2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = _ := by rw [testingRewardMass_sum, mul_one, mul_assoc]

/-- The positive four-state testing reward/successor kernel. -/
noncomputable def testingKernel (v : ℝ) (s : JointState 2 2) (_a : Bool) :
    Measure (Step 2 2) :=
  ∑ y : Bool, ∑ sp : JointState 2 2,
    ENNReal.ofReal
      ((if y then testingRewardProb v s.2 else 1 - testingRewardProb v s.2) *
       (if sp.2 = 1 then testingHiddenProb _a else 1 - testingHiddenProb _a) *
       testingEmission sp.1 sp.2) •
      Measure.dirac ((if y then (1 : ℝ) else 0), sp)
  -- @realizes \(K_v^{(T)}\)(Bernoulli reward, successor hidden state, and emission)

/-- A finite testing trajectory with Boolean rewards. -/
abbrev TestingPath (T : Nat) :=
  (Fin (T + 1) → JointState 2 2) × (Fin T → Bool × Bool)

/-- Embed a Boolean-reward path into the real-reward trajectory carrier. -/
def decodeTestingPath {T : Nat} (c : TestingPath T) : FullTrajectory T 2 2 :=
  (c.1, fun t ↦ ((c.2 t).1, if (c.2 t).2 then 1 else 0))

/-- Product mass of one path under the testing kernel and fair behavior policy. -/
noncomputable def testingPathWeight {T : Nat} (v : ℝ) (c : TestingPath T) : ℝ :=
  ((1 / 2 : ℝ) * testingEmission (c.1 0).1 (c.1 0).2) *
    ∏ t : Fin T,
      (1 / 2 : ℝ) *
      (if (c.2 t).2 then testingRewardProb v (c.1 t.castSucc).2
        else 1 - testingRewardProb v (c.1 t.castSucc).2) *
      (if (c.1 t.succ).2 = 1 then testingHiddenProb (c.2 t).1
        else 1 - testingHiddenProb (c.2 t).1) *
      testingEmission (c.1 t.succ).1 (c.1 t.succ).2

-- @node: testingPathWeight_nonneg
/-- Every atom of the finite testing law has nonnegative mass. [Under the listed formal conditions](hyp:hv), [the stated conclusion holds](goal).-/
lemma testingPathWeight_nonneg {T : Nat} (v : ℝ) (hv : |v| ≤ 1 / 16)
    (c : TestingPath T) : 0 ≤ testingPathWeight v c := by
  have hv' := abs_le.mp hv
  have hreward (h : Fin 2) :
      0 ≤ testingRewardProb v h ∧ testingRewardProb v h ≤ 1 := by
    fin_cases h <;> simp [testingRewardProb] <;> constructor <;> linarith [hv'.1, hv'.2]
  have hhidden (a : Bool) :
      0 ≤ testingHiddenProb a ∧ testingHiddenProb a ≤ 1 := by
    cases a <;> norm_num [testingHiddenProb]
  have hemission (x h : Fin 2) : 0 ≤ testingEmission x h := by
    fin_cases x <;> fin_cases h <;> norm_num [testingEmission]
  unfold testingPathWeight
  apply mul_nonneg
  · exact mul_nonneg (by norm_num) (hemission _ _)
  · apply Finset.prod_nonneg
    intro t _
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg (by norm_num)
        split_ifs with hy
        · exact (hreward (c.1 t.castSucc).2).1
        · linarith [(hreward (c.1 t.castSucc).2).2]
      · split_ifs with hs
        · exact (hhidden (c.2 t).1).1
        · linarith [(hhidden (c.2 t).1).2]
    · exact hemission _ _

-- @node: testingPathWeight_sum
/-- The explicit finite path coefficients sum to one. [the stated conclusion holds](goal).-/
lemma testingPathWeight_sum (T : Nat) (v : ℝ) :
    ∑ c : TestingPath T, testingPathWeight v c = 1 := by
  let step (xs : Fin (T + 1) → JointState 2 2)
      (t : Fin T) (ay : Bool × Bool) : ℝ :=
    (1 / 2 : ℝ) *
      (if ay.2 then testingRewardProb v (xs t.castSucc).2
        else 1 - testingRewardProb v (xs t.castSucc).2) *
      (if (xs t.succ).2 = 1 then testingHiddenProb ay.1
        else 1 - testingHiddenProb ay.1) *
      testingEmission (xs t.succ).1 (xs t.succ).2
  have hpi (xs : Fin (T + 1) → JointState 2 2) :
      (∑ ys : Fin T → Bool × Bool, ∏ t : Fin T, step xs t (ys t)) =
        ∏ t : Fin T, ∑ ay : Bool × Bool, step xs t ay := by
    simpa [Fintype.piFinset_univ] using
      (Finset.sum_prod_piFinset (Finset.univ : Finset (Bool × Bool)) (step xs))
  calc
    _ = ∑ xs : Fin (T + 1) → JointState 2 2,
          ((1 / 2 : ℝ) * testingEmission (xs 0).1 (xs 0).2) *
            ∏ t : Fin T, testingNextStateMass (xs t.succ) := by
      simp only [Fintype.sum_prod_type, testingPathWeight]
      apply Finset.sum_congr rfl
      intro xs _
      rw [← Finset.mul_sum]
      congr 1
      rw [hpi xs]
      apply Finset.prod_congr rfl
      intro t _
      exact testingStepMarginal_sum v (xs t.castSucc) (xs t.succ)
    _ = 1 := testingStateMass_sum T testingNextStateMass testingNextStateMass_sum

/-- The finite mixture of path Dirac laws for the testing experiment. -/
noncomputable def testingTrajectoryLaw (T : Nat) (v : ℝ) :
    Measure (FullTrajectory T 2 2) :=
  ∑ c : TestingPath T,
    ENNReal.ofReal (testingPathWeight v c) • Measure.dirac (decodeTestingPath c)

/-- Normalization of the explicit finite testing trajectory law. [Under the listed formal conditions](hyp:hv), [the stated conclusion holds](goal).-/
lemma testingTrajectoryLaw_isProbability (T : Nat) (v : ℝ)
    (hv : |v| ≤ 1 / 16) :
    IsProbabilityMeasure (testingTrajectoryLaw T v) := by
  constructor
  have hu : (testingTrajectoryLaw T v) Set.univ =
      ∑ c : TestingPath T, ENNReal.ofReal (testingPathWeight v c) := by
    simp [testingTrajectoryLaw]
  rw [hu, ← ENNReal.ofReal_sum_of_nonneg]
  · rw [testingPathWeight_sum]
    norm_num
  · intro c _
    exact testingPathWeight_nonneg v hv c

-- @node: def:four-state-testing-family
/-- Testing experiment with equal fair policies and the explicit finite trajectory law. -/
noncomputable def testingExperiment (T : Nat) (v : ℝ)
    (_hvFamily : v = vT T ∨ v = -(vT T)) (hv : |v| ≤ 1 / 16) :
    BinaryPomdpExperiment T where
  K := testingKernel v
  b := fun _ _ ↦ 1 / 2
  e := fun _ _ ↦ 1 / 2
  init := fun s ↦ (1 / 2) * testingEmission s.1 s.2
  law := testingTrajectoryLaw T v
  law_isProbability := testingTrajectoryLaw_isProbability T v hv
  -- @realizes \(K_v^{(T)}\)(testing kernel and stationary path construction)

end CausalSmith.Stat.PomdpBinaryhiddenRate

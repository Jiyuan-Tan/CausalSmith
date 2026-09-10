import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Causalean.Experimentation.DesignBased.DesignCore
import Causalean.Experimentation.DesignBased.Designs.Bernoulli
import Causalean.Experimentation.DesignBased.Designs.CompleteRandomization
import Causalean.Experimentation.DesignBased.Product
import Causalean.Experimentation.DesignBased.TwoStage

set_option linter.unusedVariables false
set_option linter.style.openClassical false

/-!
# Exact-hit saturation designs: shared finite/measure-theoretic world

This file fixes the finite assignment geometry, bounded schedule law, randomization
assumptions, observed-record laws, and the common analytic predicates used by the
paper's theorem scaffolds.  Finite designs are used only for labels and assignments;
outcomes and schedule laws remain measure-theoretic.
-/

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Filter Set

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section
open Classical

/-! ## Environment S1: finite saturation menu -/

-- @env: S1
variable {C n K : ℕ} [NeZero n] [NeZero K]

/-- The within-cluster binary assignment cube. -/
abbrev Assignment (n : ℕ) := Fin n → Bool
-- @realizes \mathcal Z_n(carrier Fin n → Bool = {0,1}^n)

/-- A bounded-schedule carrier before imposing its `[0,1]` range predicate. -/
abbrev Schedule (n : ℕ) := Assignment n → Fin n → ℝ
-- @realizes Y(carrier n × Z_n → ℝ; range by BoundedSchedule)
-- @realizes Y_j(z)(coordinate Y z j; range by BoundedSchedule)

/-- A potential-outcome schedule indexed by the full vector of cluster assignments. -/
abbrev GlobalSchedule (C n : ℕ) := (Fin C → Assignment n) → Fin C → Fin n → ℝ

/-- The observed record `(label, assignment, realized outcome vector)`. -/
abbrev Record (K n : ℕ) := Fin K × Assignment n × (Fin n → ℝ)
-- @realizes O_c(carrier K × Z_n × ℝ^n; [0,1]^n by BoundedSchedule)
-- @realizes L_c(first coordinate Fin K = mathcal K)
-- @realizes Z_c(second coordinate Assignment n = mathcal Z_n)

/-- The target-hit record replaces a nontarget outcome vector by the `Unit`
branch of the standard-Borel sum, the canonical measurable realization of an
optional outcome vector. -/
abbrev HitRecord (K n : ℕ) := Fin K × Assignment n × ((Fin n → ℝ) ⊕ Unit)
-- @realizes O_c^{\mathrm{hit}}(carrier K × Z_n × (outcome ∪ {star}))

/-- Target-hit record after deleting the nominal label. -/
abbrev LabelDeletedHitRecord (n : ℕ) := Assignment n × ((Fin n → ℝ) ⊕ Unit)

/-- Number of treated units in an assignment. -/
def treatedCount (z : Assignment n) : ℕ := ∑ j, if z j then 1 else 0

/-- Exact-count slice `S_k = {z : sum_j z_j = m_k}`. -/
def exactSlice (n m : ℕ) : Finset (Assignment n) :=
  Finset.univ.filter fun z => treatedCount z = m
-- @realizes \mathcal S_k(exact slice z with treatedCount z = m_k)

/-- Known exact-slice cardinality. -/
def sliceCard (n m : ℕ) : ℕ := (exactSlice n m).card
-- @realizes M_k(cardinality |S_k|; equals Nat.choose n m_k)

/-- Cluster welfare, the unit average of a schedule at assignment `z`. -/
def welfare (Y : Schedule n) (z : Assignment n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j, Y z j
-- @realizes W(z)(n⁻¹ sum_j Y_j(z))

/-- Schedule boundedness pins every potential-outcome coordinate to `[0,1]`. -/
def BoundedSchedule (Y : Schedule n) : Prop := ∀ z j, Y z j ∈ Icc (0 : ℝ) 1
-- @realizes Y(range [0,1]^(n×Z_n)) @realizes Y_j(z)(range [0,1])

/-- A schedule law is a probability law supported on the bounded schedule cube. -/
def WellFormedScheduleLaw (P : Measure (Schedule n)) : Prop :=
  IsProbabilityMeasure P ∧ ∀ᵐ Y ∂P, BoundedSchedule Y
-- @realizes P(probability law supported on [0,1] schedules)

/-- Welfare remains in `[0,1]` on the bounded schedule carrier. -/
lemma welfare_mem_Icc (Y : Schedule n) (z : Assignment n) (hY : BoundedSchedule Y) :
    welfare Y z ∈ Icc (0 : ℝ) 1 := by
  constructor
  · unfold welfare
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      (Finset.sum_nonneg fun j _ => (hY z j).1)
  · unfold welfare
    calc
      (n : ℝ)⁻¹ * ∑ j, Y z j ≤ (n : ℝ)⁻¹ * ∑ _j : Fin n, 1 := by
        gcongr
        exact (hY z _).2
      _ = 1 := by simp [NeZero.ne n]
-- @realizes W(z)(range [0,1] under BoundedSchedule)

/-- A policy menu is well formed when `4 ≤ n`, `2 ≤ K ≤ n-1`, and its treated
counts are strictly increasing interior counts. -/
def WellFormedMenu (n K : ℕ) (m : Fin K → ℕ) : Prop :=
  4 ≤ n ∧ 2 ≤ K ∧ K ≤ n - 1 ∧
    (∀ k, 1 ≤ m k ∧ m k ≤ n - 1) ∧ StrictMono m
-- @realizes n(space {4,5,...})
-- @realizes K(space {2,...,n-1})
-- @realizes \mathcal K(Fin K = {1,...,K} up to zero-based encoding)
-- @realizes \mathcal A(deployment action set Fin K = mathcal K)
-- @realizes m_k(distinct increasing interior treated counts)

/-- Rational target saturation `pi_k = m_k / n`. -/
def saturation (n : ℕ) (m : Fin K → ℕ) (k : Fin K) : ℝ := (m k : ℝ) / n
-- @realizes \pi_k(pi_k = m_k / n; interior via WellFormedMenu)

/-- Bernoulli mass of one assignment under saturation `pi`. -/
def assignmentMass (pi : ℝ) (z : Assignment n) : ℝ :=
  ∏ j, if z j then pi else 1 - pi

/-- Categorical mass predicate for a finite label law. -/
def IsCategorical (p : Fin K → ℝ) (mu : Measure (Fin K)) : Prop :=
  (∀ k, 0 ≤ p k) ∧ (∑ k, p k = 1) ∧
    ∀ k, mu {k} = ENNReal.ofReal (p k)
-- @realizes p(simplex Delta_K, boundary allowed)

/-- A fixed label vector has the prescribed number of copies of every label. -/
def HasLabelCounts (counts : Fin K → ℕ) (L : Fin C → Fin K) : Prop :=
  ∀ k, (Finset.univ.filter fun c => L c = k).card = counts k
-- @realizes C_{C,k}(fixed label counts summing to C on inhabited fibres)

/-- The empirical share attached to a count sequence. -/
def empiricalShare (counts : ℕ → Fin K → ℕ) (C : ℕ) (k : Fin K) : ℝ :=
  (counts C k : ℝ) / C
-- @realizes \alpha(limit of C_{C,k}/C)

/-! ## Environment S2: bounded schedule laws and welfare functionals -/

-- @env: S2
variable (P : Measure (Schedule n))

/-- Assignment-specific welfare mean. -/
def assignmentMean (P : Measure (Schedule n)) (z : Assignment n) : ℝ :=
  ∫ Y, welfare Y z ∂P
-- @realizes \mu_z(E_P[W(z)]) @realizes P(schedule-law argument)

/-- A bounded probability schedule law has assignment means in `[0,1]`. -/
lemma assignmentMean_mem_Icc (P : Measure (Schedule n)) (z : Assignment n)
    (hP : WellFormedScheduleLaw P) : assignmentMean P z ∈ Icc (0 : ℝ) 1 := by
  rcases hP with ⟨hprob, hbounded⟩
  letI : IsProbabilityMeasure P := hprob
  have hmeas : AEStronglyMeasurable (fun Y : Schedule n => welfare Y z) P := by
    unfold welfare
    have hm : Measurable (fun Y : Schedule n => (n : ℝ)⁻¹ * ∑ j, Y z j) := by
      fun_prop
    exact hm.aestronglyMeasurable
  have hnorm : ∀ᵐ Y ∂P, ‖welfare Y z‖ ≤ (1 : ℝ) := hbounded.mono fun Y hY => by
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [(welfare_mem_Icc Y z hY).1],
      (welfare_mem_Icc Y z hY).2⟩
  have hint : Integrable (fun Y : Schedule n => welfare Y z) P :=
    (integrable_const (1 : ℝ)).mono' hmeas hnorm
  constructor
  · exact integral_nonneg_of_ae (hbounded.mono fun Y hY => (welfare_mem_Icc Y z hY).1)
  · unfold assignmentMean
    calc
      (∫ Y, welfare Y z ∂P) ≤ ∫ _Y : Schedule n, (1 : ℝ) ∂P :=
        integral_mono_ae hint (integrable_const (1 : ℝ))
          (hbounded.mono fun Y hY => (welfare_mem_Icc Y z hY).2)
      _ = 1 := by simp
-- @realizes \mu_z(range [0,1] under probability and bounded support)

/-- Assignment-specific welfare variance. -/
def assignmentVariance (P : Measure (Schedule n)) (z : Assignment n) : ℝ :=
  ∫ Y, (welfare Y z - assignmentMean P z) ^ 2 ∂P

/-- Slice-average calibrated variance. -/
def sliceVariance (P : Measure (Schedule n)) (m : ℕ) : ℝ :=
  ((sliceCard n m : ℝ)⁻¹) * ∑ z ∈ exactSlice n m, assignmentVariance P z
-- @realizes \tau_k^2(M_k⁻¹ sum_{z∈S_k} Var_P(W(z)))

-- @node: def:exact-slice-welfare
/-- Exact-slice welfare vector `U_k = M_k⁻¹ sum_{z∈S_k} E_P W(z)`. -/
def exactSliceWelfare (P : Measure (Schedule n)) (m : Fin K → ℕ) : Fin K → ℝ :=
  fun k => ((sliceCard n (m k) : ℝ)⁻¹) *
    ∑ z ∈ exactSlice n (m k), assignmentMean P z
-- @realizes U_k(exact slice average of mu_z)
-- @realizes U(vector (U_1,...,U_K))

/-- Between-assignment variance of the slice means. -/
def betweenAssignmentVariance (P : Measure (Schedule n)) (m : Fin K → ℕ)
    (k : Fin K) : ℝ :=
  ((sliceCard n (m k) : ℝ)⁻¹) *
    ∑ z ∈ exactSlice n (m k), (assignmentMean P z - exactSliceWelfare P m k) ^ 2
-- @realizes b_k^2(M_k⁻¹ sum_{z∈S_k} (mu_z-U_k)^2)

/-- Raw exact-hit variance `rho² = tau² + b²`. -/
def rawSliceVariance (P : Measure (Schedule n)) (m : Fin K → ℕ) (k : Fin K) : ℝ :=
  sliceVariance P (m k) + betweenAssignmentVariance P m k
-- @realizes \rho_k^2(tau_k² + b_k²)

/-- A bounded target-only loss. -/
def TargetOnlyLoss (loss : (Fin K → ℝ) → Fin K → ℝ) : Prop :=
  (∀ U a, 0 ≤ loss U a) ∧ ∃ b : ℝ, 0 ≤ b ∧ ∀ U a, loss U a ≤ b
-- @realizes \mathcal L(bounded nonnegative loss depending only on U and action)

/-- Bounded nonnegative target-only loss on an arbitrary action space. -/
def BoundedTargetLoss {Action : Type*} (loss : (Fin K → ℝ) → Action → ℝ) : Prop :=
  (∀ U a, 0 ≤ loss U a) ∧ ∃ b : ℝ, 0 ≤ b ∧ ∀ U a, loss U a ≤ b

/-! ## Assumption atoms -/

-- @node: ass:iid-schedules
/-- The sampled schedule-array law is the `C`-fold product of `P`. -/
def IidSchedules (P : Measure (Schedule n))
    (sampleLaw : Measure (Fin C → Schedule n)) : Prop :=
  WellFormedScheduleLaw P ∧ IsProbabilityMeasure sampleLaw ∧
    sampleLaw = Measure.pi fun _ => P
-- @realizes Y_c(iid coordinate schedule) @realizes C(number of cluster coordinates)

-- @node: ass:isolated-clusters
/-- Partial interference is built into the sampled carrier: coordinate `c` is itself a schedule
indexed only by cluster `c`'s assignment.  This atom also records that those actual sampled
schedules, rather than an unrelated global array, lie in the bounded schedule model. -/
def IsolatedClusters (sampleLaw : Measure (Fin C → Schedule n)) : Prop :=
  IsProbabilityMeasure sampleLaw ∧
    ∀ᵐ Ys ∂sampleLaw, ∀ c, BoundedSchedule (Ys c)

-- @node: ass:bernoulli-label-iid
/-- I.i.d. categorical first-stage labels. -/
def BernoulliLabelIid (p : Fin K → ℝ) (labelLaw : Measure (Fin C → Fin K)) : Prop :=
  IsProbabilityMeasure labelLaw ∧
    ∃ mu : Measure (Fin K), IsProbabilityMeasure mu ∧ IsCategorical p mu ∧
      labelLaw = Measure.pi fun _ => mu
-- @realizes \mathsf B(p)(iid categorical first stage)

-- @node: ass:bernoulli-label-schedule-independence
/-- The Bernoulli label vector and schedule array have their product law. -/
def BernoulliLabelScheduleIndep (scheduleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K))) : Prop :=
  IsProbabilityMeasure scheduleLaw ∧ IsProbabilityMeasure labelLaw ∧
    IsProbabilityMeasure jointLaw ∧ jointLaw = scheduleLaw.prod labelLaw

/-- A schedule-conditioned within-cluster assignment kernel. -/
abbrev AssignmentKernel (C K n : ℕ) :=
  Fin C → Fin K → Schedule n → Measure (Assignment n)

-- @node: ass:bernoulli-units
/-- Conditional on label `l`, every assignment has the independent Bernoulli mass
`prod_j pi_l^{z_j}(1-pi_l)^{1-z_j}`. -/
def BernoulliUnits (m : Fin K → ℕ)
    (P : Measure (Schedule n)) (labelLaw : Measure (Fin C → Fin K))
    (assignmentLaw : AssignmentKernel C K n) : Prop :=
  ∀ c l, labelLaw {L | L c = l} ≠ 0 →
    ∀ᵐ Y ∂P, IsProbabilityMeasure (assignmentLaw c l Y) ∧
      ∀ z, assignmentLaw c l Y {z} =
        ENNReal.ofReal (assignmentMass (saturation n m l) z)

-- @node: ass:cr-label-vector
/-- The CR label law is uniform on the fibre with the prescribed label counts. -/
def CrLabelVector (counts : Fin K → ℕ) (labelLaw : Measure (Fin C → Fin K)) : Prop :=
  IsProbabilityMeasure labelLaw ∧ (∑ k, counts k = C) ∧ ∀ L,
    labelLaw {L} = if HasLabelCounts counts L then
      (Fintype.card {L : Fin C → Fin K // HasLabelCounts counts L} : ℝ≥0∞)⁻¹ else 0
-- @realizes \mathsf{CR}(\alpha)(uniform fixed-count first-stage labels)

-- @node: ass:cr-label-schedule-independence
/-- The fixed-count label vector and schedule array have their product law. -/
def CrLabelScheduleIndep (scheduleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K))) : Prop :=
  IsProbabilityMeasure scheduleLaw ∧ IsProbabilityMeasure labelLaw ∧
    IsProbabilityMeasure jointLaw ∧ jointLaw = scheduleLaw.prod labelLaw

-- @node: ass:cr-shares
/-- Active fixed-count shares converge to positive limits. -/
def CrActiveShares (counts : ℕ → Fin K → ℕ) (alpha : Fin K → ℝ)
    (A : Finset (Fin K)) : Prop :=
  ∀ k ∈ A, Tendsto (fun C => empiricalShare counts C k) atTop (nhds (alpha k)) ∧ 0 < alpha k

-- @node: ass:cr-exact-slices
/-- CR second-stage assignments are uniform on their label's exact-count slice. -/
def CrExactSlices (m : Fin K → ℕ) (P : Measure (Schedule n))
    (labelLaw : Measure (Fin C → Fin K)) (assignmentLaw : AssignmentKernel C K n) : Prop :=
  ∀ c k, labelLaw {L | L c = k} ≠ 0 →
    ∀ᵐ Y ∂P, IsProbabilityMeasure (assignmentLaw c k Y) ∧
      ∀ z, assignmentLaw c k Y {z} = if z ∈ exactSlice n (m k) then
        (sliceCard n (m k) : ℝ≥0∞)⁻¹ else 0

-- @node: ass:nondegenerate-active-slices
/-- Active calibrated slice variances have the common positive lower bound.
@realizes \underline\tau(space (0,1/2] and active variance floor) -/
def NondegenerateActiveSlices (P0 : Measure (Schedule n)) (m : Fin K → ℕ)
    (A : Finset (Fin K)) (tauLower : ℝ) : Prop :=
  WellFormedScheduleLaw P0 ∧
    0 < tauLower ∧ -- @realizes \underline\tau(strictly positive)
    tauLower ≤ 1 / 2 ∧ -- @realizes \underline\tau(at most one half)
    ∀ k ∈ A, tauLower ^ 2 ≤ sliceVariance P0 (m k)
      -- @realizes \underline\tau(active calibrated standard-deviation floor)
-- @realizes P_0(regular baseline schedule law)
-- @realizes A(active tied-best face carrier Finset (Fin K))
-- @realizes \underline\tau(space (0,1/2] and variance floor)

-- @node: ass:cr-all-shares
/-- Every fixed-count share converges to a positive limit. -/
def CrAllShares (counts : ℕ → Fin K → ℕ) (alpha : Fin K → ℝ) : Prop :=
  ∀ k, Tendsto (fun C => empiricalShare counts C k) atTop (nhds (alpha k)) ∧ 0 < alpha k

-- @node: ass:nondegenerate-all-slices
/-- All reported calibrated slice variances have the common lower bound. -/
def NondegenerateAllSlices (P : Measure (Schedule n)) (m : Fin K → ℕ)
    (tauLower : ℝ) : Prop :=
  WellFormedScheduleLaw P ∧ 0 < tauLower ∧ tauLower ≤ 1 / 2 ∧
    ∀ k, tauLower ^ 2 ≤ sliceVariance P (m k)

/-! ## Regime and observed-law constructions -/

-- @env: S3
variable (p alpha : Fin K → ℝ) (counts : Fin K → ℕ)

-- @node: def:two-regimes
/-- Exactly one of the two actual randomization specifications is active. -/
def Regime (P : Measure (Schedule n)) (sampleLaw : Measure (Fin C → Schedule n))
    (labelLaw : Measure (Fin C → Fin K))
    (jointLaw : Measure ((Fin C → Schedule n) × (Fin C → Fin K)))
    (assignmentLaw : AssignmentKernel C K n) (p alpha : Fin K → ℝ)
    (counts : ℕ → Fin K → ℕ) (m : Fin K → ℕ) : Prop :=
  Xor
    (IidSchedules P sampleLaw ∧ BernoulliLabelIid p labelLaw ∧
      BernoulliLabelScheduleIndep sampleLaw labelLaw jointLaw ∧
      BernoulliUnits m P labelLaw assignmentLaw)
    (IidSchedules P sampleLaw ∧ CrLabelVector (counts C) labelLaw ∧
      CrLabelScheduleIndep sampleLaw labelLaw jointLaw ∧
      CrExactSlices m P labelLaw assignmentLaw ∧
      (∀ N, ∑ k, counts N k = N) ∧
      ∀ k, Tendsto (fun N => empiricalShare counts N k) atTop (nhds (alpha k)))

/-- One-cluster Bernoulli observed-record law, formed by integrating the finite
label/assignment randomization against the schedule law. -/
def bernoulliObservedLaw (P : Measure (Schedule n)) (p : Fin K → ℝ)
    (m : Fin K → ℕ) : Measure (Record K n) :=
  P.bind fun Y => ∑ l, ENNReal.ofReal (p l) •
    ∑ z, ENNReal.ofReal (assignmentMass (saturation n m l) z) •
      Measure.dirac (l, z, Y z)
-- @realizes R_{B,p}(finite label/assignment kernel from schedules to records)
-- @realizes Q^B_{P,p}(P composed with R_{B,p})

/-- Fixed-count observed-array law.  The outer finite sum is the uniform
fixed-count label fibre and the inner finite sum is uniform over each exact slice. -/
def crObservedLaw (P : Measure (Schedule n)) (counts : Fin K → ℕ)
    (m : Fin K → ℕ) : Measure (Fin C → Record K n) :=
  (Measure.pi fun _ : Fin C => P).bind fun Ys =>
    ∑ L : Fin C → Fin K,
      (if HasLabelCounts counts L then
        (Fintype.card {L : Fin C → Fin K // HasLabelCounts counts L} : ℝ≥0∞)⁻¹ else 0) •
      ∑ Z : Fin C → Assignment n,
        (∏ c, if Z c ∈ exactSlice n (m (L c)) then
          (sliceCard n (m (L c)) : ℝ≥0∞)⁻¹ else 0) •
        Measure.dirac (fun c => (L c, Z c, Ys c (Z c)))
-- @realizes R^{CR}_{C_C}(fixed-count randomization kernel)
-- @realizes Q^{CR}_{P,C_C}(P^C composed with fixed-count kernel)

-- @node: def:observed-law-kernels
/-- The Bernoulli one-cluster law and the CR joint observed law. -/
def observedLaw (P : Measure (Schedule n)) (p : Fin K → ℝ)
    (counts : Fin K → ℕ) (m : Fin K → ℕ) :
    Measure (Record K n) × Measure (Fin C → Record K n) :=
  (bernoulliObservedLaw P p m, crObservedLaw P counts m)

-- @node: def:hit-map
/-- The binomial hit matrix `B` together with `q = Bp`. -/
def hitMatrix (n : ℕ) (m : Fin K → ℕ) (p : Fin K → ℝ) :
    (Fin K → Fin K → ℝ) × (Fin K → ℝ) :=
  let B := fun k l => (Nat.choose n (m k) : ℝ) *
    (saturation n m l) ^ (m k) * (1 - saturation n m l) ^ (n - m k)
  (B, fun k => ∑ l, B k l * p l)
-- @realizes B(binomial exact-hit matrix B_{k ell})
-- @realizes q(target-hit rate vector q = Bp)

/-- Under a well-formed menu and a simplex label law, every target hit rate is interior. -/
lemma hitMatrix_rate_mem_Ioo (n : ℕ) (m : Fin K → ℕ) (p : Fin K → ℝ)
    (hmenu : WellFormedMenu n K m) (hp : (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1) :
    ∀ k, (hitMatrix n m p).2 k ∈ Ioo (0 : ℝ) 1 := by
  intro k
  have hn : 0 < n := lt_of_lt_of_le (by decide) hmenu.1
  have hm : ∀ i, 1 ≤ m i ∧ m i ≤ n - 1 := hmenu.2.2.2.1
  have hsaturation : ∀ l, saturation n m l ∈ Ioo (0 : ℝ) 1 := by
    intro l
    constructor
    · rw [saturation]
      exact div_pos (by exact_mod_cast (hm l).1) (by exact_mod_cast hn)
    · rw [saturation, div_lt_one (by positivity)]
      exact_mod_cast (show m l < n by have := (hm l).2; omega)
  let B := (hitMatrix n m p).1
  have hB : ∀ l, B k l ∈ Ioo (0 : ℝ) 1 := by
    intro l
    have hmk : m k ≤ n := by have := (hm k).2; omega
    have hs := hsaturation l
    let theta : ℝ≥0 := ⟨saturation n m l, hs.1.le⟩
    have htheta : theta ≤ 1 := by exact_mod_cast hs.2.le
    let i : Fin (n + 1) := Fin.ofNat (n + 1) (m k)
    have hi_val : (i : ℕ) = m k := by
      simp [i, Nat.mod_eq_of_lt (Nat.lt_succ_of_le hmk)]
    have hmass0 := PMF.binomial_apply_of_le hmk htheta
    have htheta_real : (theta : ℝ) = saturation n m l := rfl
    have hmass : ENNReal.ofReal (B k l) = PMF.binomial theta htheta n i := by
      rw [htheta_real] at hmass0
      simpa [B, hitMatrix, i] using hmass0
    have hBpos : 0 < B k l := by
      dsimp [B, hitMatrix]
      have hchoose : 0 < Nat.choose n (m k) := Nat.choose_pos hmk
      exact mul_pos (mul_pos (by exact_mod_cast hchoose) (pow_pos hs.1 _))
        (pow_pos (sub_pos.mpr hs.2) _)
    refine ⟨hBpos, ?_⟩
    rw [← ENNReal.ofReal_lt_one]
    rw [hmass]
    apply lt_of_le_of_ne (PMF.coe_le_one _ _)
    intro heq
    have hsupp : (PMF.binomial theta htheta n).support = {i} :=
      (PMF.apply_eq_one_iff _ _).1 heq
    have hzero_pos : 0 < PMF.binomial theta htheta n 0 := by
      rw [PMF.binomial_apply_zero]
      have : 0 < (1 - theta : ℝ≥0∞) := by
        rw [tsub_pos_iff_lt]
        exact_mod_cast hs.2
      positivity
    have hzero_mem : (0 : Fin (n + 1)) ∈ (PMF.binomial theta htheta n).support :=
      (PMF.apply_pos_iff _ _).1 hzero_pos
    rw [hsupp] at hzero_mem
    have hi_ne : i ≠ 0 := by
      apply Fin.ne_of_val_ne
      simp [hi_val]
      have := (hm k).1
      omega
    exact hi_ne (Set.mem_singleton_iff.mp hzero_mem).symm
  have hp_exists : ∃ l : Fin K, 0 < p l := by
    by_contra h
    push_neg at h
    have : ∑ l, p l ≤ 0 := Finset.sum_nonpos fun l _ => h l
    linarith [hp.2]
  constructor
  · dsimp [hitMatrix]
    apply Finset.sum_pos'
    · intro l hl
      exact mul_nonneg (hB l).1.le (hp.1 l)
    · obtain ⟨l, hl⟩ := hp_exists
      exact ⟨l, Finset.mem_univ l, mul_pos (hB l).1 hl⟩
  · dsimp [hitMatrix]
    calc
      ∑ l, ((Nat.choose n (m k) : ℝ) * saturation n m l ^ m k *
          (1 - saturation n m l) ^ (n - m k)) * p l < ∑ l, 1 * p l := by
        apply Finset.sum_lt_sum
        · intro l hl
          exact mul_le_mul_of_nonneg_right (hB l).2.le (hp.1 l)
        · obtain ⟨l, hl⟩ := hp_exists
          exact ⟨l, Finset.mem_univ l, mul_lt_mul_of_pos_right (hB l).2 hl⟩
      _ = 1 := by simpa using hp.2
-- @realizes q(range (0,1)^K under WellFormedMenu and p∈Delta_K)

/-- Target-hit reduction of one record. -/
def reduceToHit (m : Fin K → ℕ) (o : Record K n) : HitRecord K n :=
  (o.1, o.2.1, if ∃ k, o.2.1 ∈ exactSlice n (m k) then Sum.inl o.2.2 else Sum.inr ())

/-- The target-hit reduction is measurable for the natural finite-product,
Euclidean, and `Option` measurable structures. -/
lemma measurable_reduceToHit (m : Fin K → ℕ) : Measurable (reduceToHit (n := n) m) := by
  unfold reduceToHit
  have hs : MeasurableSet {z : Assignment n | ∃ k, z ∈ exactSlice n (m k)} := by
    exact (Set.toFinite _).measurableSet
  have hp : MeasurableSet {o : Record K n | ∃ k, o.2.1 ∈ exactSlice n (m k)} := by
    have hproj : Measurable (fun o : Record K n => o.2.1) := by fun_prop
    exact hproj hs
  have hlabel : Measurable (fun o : Record K n => o.1) := by fun_prop
  have hassignment : Measurable (fun o : Record K n => o.2.1) := by fun_prop
  have hbranch : Measurable (fun o : Record K n =>
      if ∃ k, o.2.1 ∈ exactSlice n (m k) then Sum.inl o.2.2 else Sum.inr ()) :=
    Measurable.ite hp (by fun_prop) (by fun_prop)
  exact hlabel.prodMk (hassignment.prodMk hbranch)

/-- Label deletion retains the assignment and realized outcome. -/
def deleteLabel (o : Record K n) : Assignment n × (Fin n → ℝ) := (o.2.1, o.2.2)

/-- Label deletion from a target-hit record keeps the hit/miss marker and keeps
the outcome vector exactly on realized target hits. -/
def deleteHitLabel (o : HitRecord K n) : LabelDeletedHitRecord n :=
  (o.2.1, o.2.2)

/-- Label deletion is measurable for the natural product/`Option` Borel structures. -/
lemma measurable_deleteHitLabel :
    Measurable (deleteHitLabel : HitRecord K n → LabelDeletedHitRecord n) := by
  unfold deleteHitLabel
  fun_prop

/-- Coordinatewise label deletion on an observed array law. -/
def deleteLabelsExperimentLaw (mu : Measure (Fin C → Record K n)) :
    Measure (Fin C → (Assignment n × (Fin n → ℝ))) :=
  mu.map fun O c => deleteLabel (O c)

/-- The label-deleted target-hit experiment required by the Bernoulli deletion
claim; unlike `deleteLabelsExperimentLaw`, it does not retain nontarget outcomes. -/
def deleteLabelsFromHitExperimentLaw (mu : Measure (Fin C → HitRecord K n)) :
    Measure (Fin C → LabelDeletedHitRecord n) :=
  mu.map fun O c => deleteHitLabel (O c)

-- @node: def:regime-experiments
/-- Full/reduced experiments in both regimes, represented as the source law and
its coordinatewise measurable image. -/
def regimeExperiment (P : Measure (Schedule n)) (p alpha : Fin K → ℝ)
    (counts : Fin K → ℕ) (m : Fin K → ℕ) :
    (Measure (Fin C → Record K n) × Measure (Fin C → HitRecord K n)) ×
      (Measure (Fin C → Record K n) ×
        Measure (Fin C → (Assignment n × (Fin n → ℝ)))) :=
  let fullB := Measure.pi fun _ : Fin C => bernoulliObservedLaw P p m
  let fullCR := crObservedLaw P counts m
  ((fullB, fullB.map fun O c => reduceToHit m (O c)),
    (fullCR, fullCR.map fun O c => deleteLabel (O c)))
-- @realizes \mathcal E_{C,B}^{\mathrm{full}}(p)(C-fold Q^B law)
-- @realizes \mathcal E_{C,B}^{\mathrm{hit}}(p)(target-hit image)
-- @realizes \mathcal E_{C,CR}^{\mathrm{full}}(\alpha)(Q^CR full experiment)
-- @realizes \mathcal E_{C,CR}^{\mathrm{hit}}(\alpha)(label-deleted image)

/-! ## Generic decision and asymptotic predicates used in theorem statements -/

/-- A measurable randomized finite-action rule. -/
def RandomizedRule {O : Type*} [MeasurableSpace O] (delta : O → Fin K → ℝ) : Prop :=
  (∀ a, Measurable fun o => delta o a) ∧
    (∀ o a, 0 ≤ delta o a) ∧ ∀ o, ∑ a, delta o a = 1
-- @realizes \mathfrak D_C(all measurable randomized deployment rules)

/-- Risk of a randomized rule under one experiment law. -/
def ruleRisk {O : Type*} [MeasurableSpace O] (mu : Measure O)
    (U : Fin K → ℝ) (loss : (Fin K → ℝ) → Fin K → ℝ)
    (delta : O → Fin K → ℝ) : ℝ :=
  ∫ o, ∑ a, delta o a * loss U a ∂mu

/-- Minimax risk over all measurable randomized rules and a class of schedule laws. -/
def experimentMinimaxRisk {O : Type*} [MeasurableSpace O]
    (laws : Set (Measure (Schedule n))) (experiment : Measure (Schedule n) → Measure O)
    (target : Measure (Schedule n) → Fin K → ℝ)
    (loss : (Fin K → ℝ) → Fin K → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ delta : O → Fin K → ℝ, RandomizedRule delta ∧
    r = ⨆ P ∈ laws, ruleRisk (experiment P) (target P) loss delta}

/-- The unrestricted paper domain of bounded probability schedule laws. -/
def BoundedScheduleLawClass (n : ℕ) : Set (Measure (Schedule n)) :=
  {P | WellFormedScheduleLaw P}

/-- Risk of a Markov-kernel randomized rule on an arbitrary standard-Borel action space. -/
def kernelRuleRisk {O Action : Type*} [MeasurableSpace O] [MeasurableSpace Action]
    (mu : Measure O) (U : Fin K → ℝ) (loss : (Fin K → ℝ) → Action → ℝ)
    (delta : ProbabilityTheory.Kernel O Action) : ℝ :=
  ∫ o, ∫ a, loss U a ∂(delta o) ∂mu

/-- Minimax risk over all measurable randomized rules into a standard-Borel action space. -/
def standardBorelExperimentMinimaxRisk {O Action : Type*}
    [MeasurableSpace O] [MeasurableSpace Action]
    (laws : Set (Measure (Schedule n))) (experiment : Measure (Schedule n) → Measure O)
    (target : Measure (Schedule n) → Fin K → ℝ)
    (loss : (Fin K → ℝ) → Action → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ delta : ProbabilityTheory.Kernel O Action,
    ProbabilityTheory.IsMarkovKernel delta ∧
      r = ⨆ P ∈ laws, kernelRuleRisk (experiment P) (target P) loss delta}

/-- Characteristic-function definition of multivariate asymptotic normality. -/
def AsymptoticNormal {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℕ → Measure Omega) (X center : ℕ → Omega → (Fin K → ℝ))
    (Sigma : Fin K → Fin K → ℝ) : Prop :=
  ∀ t : Fin K → ℝ,
    Tendsto (fun C => ∫ w, Real.cos (∑ i, t i * (Real.sqrt C *
      (X C w i - center C w i))) ∂(mu C)) atTop
      (nhds (Real.exp (-((∑ i, ∑ j, t i * Sigma i j * t j) / 2)))) ∧
    Tendsto (fun C => ∫ w, Real.sin (∑ i, t i * (Real.sqrt C *
      (X C w i - center C w i))) ∂(mu C)) atTop (nhds 0)

/-- Entrywise convergence in probability of a covariance estimator. -/
def CovarianceConsistent {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℕ → Measure Omega) (hatSigma : ℕ → Omega → Fin K → Fin K → ℝ)
    (Sigma : Fin K → Fin K → ℝ) : Prop :=
  ∀ eps > 0, Tendsto (fun C => mu C {w | ∃ i j,
    eps < |hatSigma C w i j - Sigma i j|}) atTop (nhds 0)

/-- LAN likelihood-ratio expansion with a remainder vanishing in probability. -/
def LikelihoodLAN {Omega : ℕ → Type*} [∀ N, MeasurableSpace (Omega N)]
    (nullLaw localLaw : ∀ N, Measure (Omega N)) (central : ∀ N, Omega N → ℝ)
    (quadratic : ℝ) : Prop :=
  ∃ remainder : ∀ N, Omega N → ℝ,
    (∀ eps > 0, Tendsto (fun N => nullLaw N {o | eps < |remainder N o|})
      atTop (nhds 0)) ∧
    ∀ N, ∀ᵐ o ∂nullLaw N,
      Real.log (((localLaw N).rnDeriv (nullLaw N) o).toReal) =
        central N o - quadratic / 2 + remainder N o

/-- Characteristic-function formulation of a Gaussian shift limit. -/
def GaussianShiftLimit {Omega : ℕ → Type*} [∀ N, MeasurableSpace (Omega N)]
    (mu : ∀ N, Measure (Omega N)) (X : ∀ N, Omega N → (Fin K → ℝ))
    (mean : Fin K → ℝ) (Sigma : Fin K → Fin K → ℝ) : Prop :=
  ∀ t : Fin K → ℝ,
    Tendsto (fun N => ∫ o, Real.cos (∑ i, t i * X N o i) ∂(mu N)) atTop
      (nhds (Real.exp (-((∑ i, ∑ j, t i * Sigma i j * t j) / 2)) *
        Real.cos (∑ i, t i * mean i))) ∧
    Tendsto (fun N => ∫ o, Real.sin (∑ i, t i * X N o i) ∂(mu N)) atTop
      (nhds (Real.exp (-((∑ i, ∑ j, t i * Sigma i j * t j) / 2)) *
        Real.sin (∑ i, t i * mean i)))

/-- Diagonal covariance with the specified diagonal. -/
def IsDiagonalCovariance (Sigma : Fin K → Fin K → ℝ) (d : Fin K → ℝ) : Prop :=
  ∀ i j, Sigma i j = if i = j then d i else 0

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

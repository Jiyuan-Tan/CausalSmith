import Causalean.Experimentation.DesignBased.Risk
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.BigOperators

/-!
Shared finite-population objects for the multi-arm second-order minimax frontier.

The paper works with complete binary response schedules and arbitrary finite
assignment designs.  This module contains only the common carriers and exact
finite-sum constructions; theorem claims live in the planned theorem files.
-/

open scoped BigOperators
open Finset Set

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

/-- The treatment-arm set in a $K$-arm experiment consists of the $K$ arm labels. -/
abbrev Arm (K : ℕ) := Fin K -- @realizes \mathcal A_K(carrier {1,…,K})
/-- The unit set in a population of size $n$ consists of the $n$ unit labels. -/
abbrev Unit (n : ℕ) := Fin n -- @realizes i(carrier {1,…,n})
/-- A binary response type assigns a potential-outcome bit to every treatment arm. -/
abbrev RespType (K : ℕ) := Arm K → Bool -- @realizes t(binary response-type carrier) @realizes \mathcal T_K(carrier {0,1}^{A_K})
/-- A complete binary response schedule assigns a response type to every unit. -/
abbrev Schedule (K n : ℕ) := Unit n → RespType K -- @realizes z(carrier T_K^n)
/-- An assignment allocates one treatment arm to every unit. -/
abbrev Assign (K n : ℕ) := Unit n → Arm K -- @realizes A(carrier A_K^n)
/-- An observed-outcome vector records one binary outcome for every unit. -/
abbrev ObservedOutcome (n : ℕ) := Unit n → Bool -- @realizes Y_i^{\mathrm{obs}}(binary carrier)

/-- A nonzero, zero-sum contrast. -/
structure Contrast (F : Type*) [Zero F] [AddCommMonoid F] (K : ℕ) where
  coeff : Arm K → F
  nonzero : coeff ≠ 0
  sum_zero : ∑ a, coeff a = 0

/-- The contrast forall arm object can be evaluated as its underlying function. -/
instance {F K} [AddCommMonoid F] : CoeFun (Contrast F K) (fun _ => Arm K → F) :=
  ⟨Contrast.coeff⟩

/-- The paper's standing arm-count domain. -/
def AdmissibleArmCount (K : ℕ) : Prop := 2 ≤ K
-- @realizes K(standing constraint 2≤K)

/-- Positive natural indices used by the paper's finite-population LPs. -/
def PositiveNat := {m : ℕ // 0 < m}

/-- A positive nat nat value has its natural numerical representation. -/
instance : Coe PositiveNat ℕ := ⟨Subtype.val⟩

/-- Real nonzero zero-sum contrasts, as opposed to the generic algebraic helper. -/
abbrev RealContrast (K : ℕ) := Contrast ℝ K
-- @realizes c(carrier ℝ^K; nonzero and zero-sum fields)

-- @env: S1
variable {K n : ℕ} (c : Contrast ℝ K)
-- @realizes n(finite-population size)
-- @realizes a(generic element of Arm K)

/-- The active support of a contrast. -/
noncomputable def Sc (c : Contrast ℝ K) : Finset (Arm K) :=
  Finset.univ.filter fun a => c a ≠ 0
-- @realizes S_c({a | c_a ≠ 0})

/-- The contrast ℓ1 norm. -/
def Lc (c : Contrast ℝ K) : ℝ := ∑ a, |c a|
-- @realizes L_c(sum_a |c_a|)

/-- Contrast-weighted arm allocation. -/
noncomputable def qStar (c : Contrast ℝ K) (a : Arm K) : ℝ := |c a| / Lc c
-- @realizes q^\star(q_a=|c_a|/L_c; zero off S_c)

/-- The fixed potential outcome of unit `i` under arm `a`. -/
def potentialOutcome (z : Schedule K n) (i : Unit n) (a : Arm K) : Bool := z i a
-- @realizes Y_i(a)(Y_i(a)=t_{i,a})

/-- Observed outcomes under a realized assignment. -/
def obsOutcome (z : Schedule K n) (A : Assign K n) : ObservedOutcome n :=
  fun i => potentialOutcome z i (A i)
-- @realizes Y_i^{\mathrm{obs}}(Y_i(A_i))

/-- The finite-population contrast target. -/
noncomputable def tauC (c : Contrast ℝ K) (z : Schedule K n) : ℝ :=
  ((n : ℝ)⁻¹) * ∑ i, ∑ a, c a * if z i a then 1 else 0
-- @realizes \tau_c(z)(n⁻¹ ∑_i ∑_a c_a t_{i,a})

/-- Clipping to the natural contrast range. -/
noncomputable def clip (c : Contrast ℝ K) (x : ℝ) : ℝ :=
  max (-Lc c / 2) (min (Lc c / 2) x)

/-- [the clipped estimate lies in the natural closed interval from minus one half to one half of the contrast norm](goal). -/
lemma clip_mem (c : Contrast ℝ K) (x : ℝ) :
    clip c x ∈ Set.Icc (-Lc c / 2) (Lc c / 2) := by
  have hLc : 0 ≤ Lc c := Finset.sum_nonneg fun _ _ => abs_nonneg _
  constructor
  · exact le_max_left _ _
  · apply max_le
    · rw [neg_div]
      exact neg_le_self (div_nonneg hLc (by norm_num))
    · exact min_le_left _ _

/-- An arbitrary clipped, possibly biased estimator. -/
abbrev Estimator (K n : ℕ) (c : Contrast ℝ K) :=
  Assign K n → ObservedOutcome n → Set.Icc (-Lc c / 2) (Lc c / 2)
-- @realizes \widehat\tau(arbitrary clipped map of observed assignment/outcomes)

/-- A decision procedure pairs an arbitrary assignment law and a clipped estimator. -/
abbrev Procedure (K n : ℕ) (c : Contrast ℝ K) :=
  Causalean.Experimentation.DesignBased.FiniteDesign (Assign K n) × Estimator K n c
-- @realizes \mathcal D(arbitrary law on A_K^n)

/-- Design-based squared error of a procedure at a fixed schedule. -/
noncomputable def labeledRisk (p : Procedure K n c) (z : Schedule K n) : ℝ :=
  p.1.mse (fun A => p.2 A (obsOutcome z A)) (tauC c z)
-- @realizes R_n(\mathcal D,\widehat\tau;z)(assignment-only mean squared error)

/-- First-order risk constant. -/
noncomputable def C0 (c : Contrast ℝ K) : ℝ := Lc c ^ 2 / 4
-- @realizes C_0(c)(L_c²/4)

/-- A response-type count vector with total population size `n`. -/
def CountVec (K n : ℕ) :=
  {m : RespType K → Fin (n + 1) // ∑ t, (m t : ℕ) = n}
-- @realizes m(nonnegative response-type counts)
-- @realizes \mathcal M_{n,K}(sum_t m_t=n)

/-- An arm-allocation count vector with total population size `n`. -/
def AllocVec (K n : ℕ) :=
  {r : Arm K → Fin (n + 1) // ∑ a, (r a : ℕ) = n}
-- @realizes r(nonnegative arm-allocation counts)
-- @realizes \mathcal R_{n,K}(sum_a r_a=n)

/-- Arm-specific observed-success counts compatible with `r`. -/
def ObsVec {K n : ℕ} (r : AllocVec K n) :=
  {x : Arm K → Fin (n + 1) // ∀ a, (x a : ℕ) ≤ (r.1 a : ℕ)}
-- @realizes x(0≤x_a≤r_a)

/-- A response-type by arm contingency table. -/
abbrev Contingency (K n : ℕ) := RespType K → Arm K → Fin (n + 1)
-- @realizes h(nonnegative T_K×A_K contingency table)

/-- The count vec collection has a finite enumeration. -/
instance (K n : ℕ) : Fintype (CountVec K n) := by
  unfold CountVec
  infer_instance

/-- The alloc vec collection has a finite enumeration. -/
instance (K n : ℕ) : Fintype (AllocVec K n) := by
  unfold AllocVec
  infer_instance

/-- The obs vec collection has a finite enumeration. -/
instance {K n : ℕ} (r : AllocVec K n) : Fintype (ObsVec r) := by
  unfold ObsVec
  infer_instance

/-- The exact feasible contingency-table fiber. -/
def contingencyFiber (m : CountVec K n) (r : AllocVec K n) (x : ObsVec r) :
    Finset (Contingency K n) :=
  Finset.univ.filter fun h =>
    (∀ t, ∑ a, (h t a : ℕ) = (m.1 t : ℕ)) ∧
    (∀ a, ∑ t, (h t a : ℕ) = (r.1 a : ℕ)) ∧
    (∀ a, ∑ t with t a = true, (h t a : ℕ) = (x.1 a : ℕ))
-- @realizes \mathcal H(m,r,x)(row, column, and success marginals)

/-- Orbit form of the contrast target. -/
noncomputable def tauCount (c : Contrast ℝ K) (m : CountVec K n) : ℝ :=
  ((n : ℝ)⁻¹) * ∑ t, (m.1 t : ℝ) * ∑ a, c a * if t a then 1 else 0
-- @realizes \tau_c(m)(n⁻¹ ∑_t m_t ∑_a c_a t_a)

/-- The raw schedule count is the number of units having a specified response type. -/
def rawScheduleCount (z : Schedule K n) (t : RespType K) : Fin (n + 1) :=
  ⟨(Finset.univ.filter fun i => z i = t).card,
    Nat.lt_succ_iff.mpr (by
      simpa using Finset.card_le_card (Finset.filter_subset (fun i => z i = t) Finset.univ))⟩

/-- [the raw schedule count sums](goal). -/
lemma rawScheduleCount_sum (z : Schedule K n) :
    ∑ t, ((rawScheduleCount z t : Fin (n + 1)) : ℕ) = n := by
  symm
  simpa [rawScheduleCount] using
    (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Unit n)))
      (t := (Finset.univ : Finset (RespType K))) (f := z) (by simp))

/-- The response-type orbit of a labeled schedule. -/
def scheduleCounts (z : Schedule K n) : CountVec K n :=
  ⟨rawScheduleCount z, rawScheduleCount_sum z⟩

-- @env: S2
variable {K n : ℕ} (m : CountVec K n) (r : AllocVec K n) (x : ObsVec r)

/-- An invariant estimator is indexed by allocation and success-count orbits. -/
abbrev OrbitEstimator (K n : ℕ) (c : Contrast ℝ K) :=
  ∀ r : AllocVec K n, ObsVec r → Set.Icc (-Lc c / 2) (Lc c / 2)
-- @realizes \delta(map (r,x) into [-L_c/2,L_c/2])

/-- An orbit procedure is a mixture over allocation orbits and an invariant estimator. -/
abbrev OrbitProcedure (K n : ℕ) (c : Contrast ℝ K) :=
  Causalean.Experimentation.DesignBased.FiniteDesign (AllocVec K n) × OrbitEstimator K n c
-- @realizes \pi(probability mixture over allocation-count orbits)

/-- Rational contrasts used by the exact grid programs. -/
abbrev RatContrast (K : ℕ) := Contrast ℚ K

/-- [the rat contrast nonzero real property holds](goal). -/
lemma ratContrast_nonzero_real (c : RatContrast K) :
    (fun a => (c a : ℝ)) ≠ 0 := by
  intro h
  apply c.nonzero
  funext a
  have ha := congrFun h a
  norm_num at ha ⊢
  exact ha

/-- [the rat contrast sums zero real](goal). -/
lemma ratContrast_sum_zero_real (c : RatContrast K) :
    ∑ a, (c a : ℝ) = 0 := by
  rw [← Rat.cast_sum Finset.univ]
  norm_num [c.sum_zero]

/-- A rational contrast is embedded into the real contrast space by interpreting each coefficient as a real number. -/
noncomputable def ratContrastToReal (c : RatContrast K) : Contrast ℝ K where
  coeff a := c a
  nonzero := ratContrast_nonzero_real c
  sum_zero := ratContrast_sum_zero_real c

/-- Rational ℓ1 norm and half-range. -/
def LcRat (c : RatContrast K) : ℚ := ∑ a, |c a|
/-- The rational half-range is one half of the rational contrast norm. -/
def hRat (c : RatContrast K) : ℚ := LcRat c / 2

-- @env: S3
variable {K n : ℕ} (M : ℕ) (cq : RatContrast K)
-- @realizes M(positive grid resolution in theorem hypotheses)

/-- Contrast-scaled rational action grid. -/
-- @realizes \Gamma_M(specialization gammaMC M cDaggerQ)
def gammaMC (M : ℕ) (c : RatContrast K) (j : Fin (2 * M + 1)) : ℚ :=
  -hRat c + (j : ℚ) * hRat c / M
-- @realizes j(grid index 0,…,2M)
-- @realizes \Gamma_{M,c}({-h_c+jh_c/M})
-- @realizes g(generic grid-valued estimate)

/-- A rational grid design assigns a rational mass to every allocation-count vector. -/
abbrev GridPi (K n : ℕ) := AllocVec K n → ℚ
/-- A grid weight assigns a real joint design-and-action mass to every allocation count, compatible success count, and grid action. -/
abbrev GridWeight (K n M : ℕ) :=
  ∀ r : AllocVec K n, ObsVec r → Fin (2 * M + 1) → ℝ
-- @realizes w_{r,x,g}(paper-facing real joint design--action weight)

/-- Rational coordinates used to certify a paper-facing real grid weight. -/
abbrev RationalGridWeight (K n M : ℕ) :=
  ∀ r : AllocVec K n, ObsVec r → Fin (2 * M + 1) → ℚ

/-- Coordinatewise cast from an exact rational certificate to the paper-facing weight. -/
def rationalGridWeightToReal (w : RationalGridWeight K n M) : GridWeight K n M :=
  fun r x g => (w r x g : ℝ)

/-- Every joint design--action coordinate lies in the paper's unit interval. -/
def GridWeightInRange (w : GridWeight K n M) : Prop :=
  ∀ r x g, 0 ≤ w r x g ∧ w r x g ≤ 1
-- @realizes w_{r,x,g}(coordinate range 0≤w≤1)

/-- The rational certificate representation only needs the sign row explicitly;
the occupancy equations and simplex constraint imply the upper bound. -/
def RationalGridWeightNonnegative (w : RationalGridWeight K n M) : Prop :=
  ∀ r x g, 0 ≤ w r x g

-- @env: S4
/-- The two-arm response type `(1,0)`. -/
def twoArmPositiveEffectType : RespType 2 := fun a => a == 0

/-- The two-arm response type `(0,1)`. -/
def twoArmNegativeEffectType : RespType 2 := fun a => a == 1

/-- The positive-effect coordinate of the full four-count orbit vector. -/
def pPlus (m : CountVec 2 n) : Fin (n + 1) := m.1 twoArmPositiveEffectType
-- @realizes p_+(m_(1,0), hence a member of {0,…,n})

/-- The negative-effect coordinate of the full four-count orbit vector. -/
def pMinus (m : CountVec 2 n) : Fin (n + 1) := m.1 twoArmNegativeEffectType
-- @realizes p_-(m_(0,1), hence a member of {0,…,n})

/-- The zero-effect count, represented as the complement of the two distinct
effect coordinates in the complete four-count orbit vector. -/
-- keep: public carrier for the frozen paper symbol r_0 and its CountVec relation.
def rZero (m : CountVec 2 n) : Fin (n + 1) :=
  ⟨n - (pPlus m : ℕ) - (pMinus m : ℕ),
    Nat.lt_succ_of_le ((Nat.sub_le _ (pMinus m : ℕ)).trans
      (Nat.sub_le n (pPlus m : ℕ)))⟩
-- @realizes r_0(m_(0,0)+m_(1,1)=n-p_+-p_-, hence a member of {0,…,n})

/-- Positive normalizers used in conditional second-order statements. -/
def PositiveSequence := {a : ℕ → ℝ // ∀ n, 0 < a n}
-- @realizes a_n(positive function ℕ→(0,∞))

/-- The positive sequence forall nat real object can be evaluated as its underlying function. -/
instance : CoeFun PositiveSequence (fun _ => ℕ → ℝ) := ⟨fun a => a.1⟩

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

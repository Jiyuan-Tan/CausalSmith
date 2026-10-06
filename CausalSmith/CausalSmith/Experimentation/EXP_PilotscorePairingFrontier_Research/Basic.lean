module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Pilot-score pairing frontier: shared world

The covariate carrier is a finite real coordinate vector, with the unit cube imposed
by the covariate law. Euclidean distance is written explicitly. The matched-pair
design and PO substrate concern fixed finite potential-outcome schedules or a
single unit; the iid two-wave law here is a measure-theoretic object
(`bypass-justified` for `Experimentation/DesignBased`, `MatchedPairDesign`, and
`PO`). The fixed-pair coin calculations in `MatchedPairDesign` are used by the
variance helper.
-/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory Set
open scoped BigOperators ENNReal

-- @env: S1
variable {d m N : ℕ} {β L cX CX cg Cg : ℝ}
-- @realizes d(positive dimension; positivity in theorem hypotheses)
-- @realizes beta(smoothness 0 < beta ≤ 1 in theorem hypotheses)
-- @realizes m(pilot size m ≥ 1 in theorem hypotheses)
-- @realizes N(even main size N ≥ 2 in theorem hypotheses)
-- @realizes L(positive Hölder radius in theorem hypotheses)
-- @realizes cX(positive lower density bound in theorem hypotheses)
-- @realizes CX(finite upper density bound in theorem hypotheses)
-- @realizes cg(positive lower score density bound in theorem hypotheses)
-- @realizes Cg(finite upper score density bound in theorem hypotheses)

abbrev XSpace (d : ℕ) := Fin d → ℝ
-- @realizes Xspace(carrier ℝ^d; cube support imposed by CovariateDensity)

def cube (d : ℕ) : Set (XSpace d) := {x | ∀ i, x i ∈ Icc (0 : ℝ) 1}
-- @realizes Xspace(range [0,1]^d)

def scoreInterval : Set ℝ := Icc (1 / 4 : ℝ) (3 / 4 : ℝ)
-- @realizes I(fixed interval [1/4,3/4])

def ValidClassParameters (d : ℕ) (β L cX CX cg Cg : ℝ) : Prop :=
  1 ≤ d ∧ -- @realizes d(positive covariate dimension)
  0 < β ∧ β ≤ 1 ∧ -- @realizes beta(range (0,1])
  0 < L ∧ -- @realizes L(range (0,∞))
  0 < cX ∧ cX ≤ 1 ∧ -- @realizes cX(range (0,1])
  1 ≤ CX ∧ -- @realizes CX(range [1,∞))
  0 < cg ∧ cg < 2 ∧ -- @realizes cg(range (0,2))
  2 < Cg -- @realizes Cg(range (2,∞))

def ValidAnchorParameters (d : ℕ) (β cX CX : ℝ) : Prop :=
  1 ≤ d ∧ 0 < β ∧ β ≤ 1 ∧ -- @realizes beta(range (0,1])
    0 < cX ∧ cX ≤ 1 ∧ -- @realizes cX(range (0,1])
    1 ≤ CX -- @realizes CX(range [1,∞))

def ValidMainSize (N : ℕ) : Prop :=
  Even N ∧ 2 ≤ N -- @realizes N(even and at least two)

noncomputable def euclideanDistance (x y : XSpace d) : ℝ :=
  Real.sqrt (∑ i, (x i - y i) ^ 2)

abbrev UnitRecord (d : ℕ) := XSpace d × ℝ × ℝ
-- @realizes P(one-unit law is Measure (X × ℝ × ℝ))
-- @realizes X(first coordinate of UnitRecord)
-- @realizes Y0(second coordinate of UnitRecord; bounded by BoundedOutcomes)
-- @realizes Y1(third coordinate of UnitRecord; bounded by BoundedOutcomes)

noncomputable def cubeMeasure (d : ℕ) : Measure (XSpace d) :=
  (Measure.pi fun _ : Fin d => (volume : Measure ℝ)).restrict (cube d)

noncomputable def regression0 (P : Measure (UnitRecord d)) : UnitRecord d → ℝ :=
  condExp (MeasurableSpace.comap Prod.fst inferInstance) P (fun u => u.2.1)
-- @realizes mu0(conditional expectation of Y0 given X)

noncomputable def regression1 (P : Measure (UnitRecord d)) : UnitRecord d → ℝ :=
  condExp (MeasurableSpace.comap Prod.fst inferInstance) P (fun u => u.2.2)
-- @realizes mu1(conditional expectation of Y1 given X)

def IsHalfSumVersion (P : Measure (UnitRecord d)) (g : XSpace d → ℝ) : Prop :=
  ∀ᵐ u ∂P, g u.1 = (regression1 P u + regression0 P u) / 2
-- @realizes g(half-sum conditional regression version)

-- @node: ass:covariate-density
def CovariateDensity (P : Measure (UnitRecord d)) (cX CX : ℝ) : Prop :=
  IsProbabilityMeasure P ∧ -- @realizes P(probability law)
    (P.map Prod.fst) ≪ cubeMeasure d ∧
    (∀ᵐ x ∂cubeMeasure d,
      cX ≤ ((P.map Prod.fst).rnDeriv (cubeMeasure d) x).toReal ∧
      ((P.map Prod.fst).rnDeriv (cubeMeasure d) x).toReal ≤ CX)
-- @realizes pX(rnDeriv of X law relative to cube Lebesgue measure; bounds cX,CX)
-- @realizes Xspace(law supported on cube)

-- @node: ass:bounded-outcomes
def BoundedOutcomes (P : Measure (UnitRecord d)) : Prop :=
  ∀ᵐ u ∂P, u.2.1 ∈ Icc (0 : ℝ) 1 ∧ u.2.2 ∈ Icc (0 : ℝ) 1
-- @realizes Y0(range [0,1] almost surely)
-- @realizes Y1(range [0,1] almost surely)

-- @node: ass:holder-score
def HolderScore (g : XSpace d → ℝ) (L β : ℝ) : Prop :=
  ∀ x ∈ cube d, ∀ y ∈ cube d,
    |g x - g y| ≤ L * (euclideanDistance x y) ^ β
-- @realizes g(Euclidean Hölder score)

-- @node: ass:regular-score-pushforward
def RegularScorePushforward (P : Measure (UnitRecord d))
    (g : XSpace d → ℝ) (cg Cg : ℝ) : Prop :=
  let ν := P.map (fun u => g u.1)
  ν ≪ (volume : Measure ℝ).restrict scoreInterval ∧
    (∀ᵐ t ∂(volume : Measure ℝ).restrict scoreInterval,
      cg ≤ (ν.rnDeriv ((volume : Measure ℝ).restrict scoreInterval) t).toReal ∧
      (ν.rnDeriv ((volume : Measure ℝ).restrict scoreInterval) t).toReal ≤ Cg)
-- @realizes pg(score-pushforward density, with bounds cg,Cg)
-- @realizes I(score law supported on [1/4,3/4])

-- @node: def:model-class
structure RegularScoreClass (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (L β cX CX cg Cg : ℝ) : Prop where
  parameters : ValidClassParameters d β L cX CX cg Cg
    -- @realizes beta(carries ValidClassParameters range)
    -- @realizes cX(carries ValidClassParameters range)
    -- @realizes CX(carries ValidClassParameters range)
  half_sum_version : IsHalfSumVersion P g
  covariate_density : CovariateDensity P cX CX
  bounded_outcomes : BoundedOutcomes P
  holder_score : HolderScore g L β
  regular_score_pushforward : RegularScorePushforward P g cg Cg

def RegularScoreModel (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (L β cX CX cg Cg : ℝ) : Prop :=
  RegularScoreClass P g L β cX CX cg Cg

abbrev PilotRecord (d : ℕ) := XSpace d × Bool × ℝ
-- @realizes Pilot(carrier Fin m → X × Bool × ℝ)
-- @realizes A(Boolean pilot treatment)
-- @realizes Y(observed response, selected from Y0 or Y1)

def observedPilot (u : UnitRecord d) (a : Bool) : PilotRecord d :=
  (u.1, a, if a then u.2.2 else u.2.1)
-- @realizes Y(Y=A Y1+(1-A)Y0)

noncomputable def fairCoin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true

noncomputable def pilotUnitLaw (P : Measure (UnitRecord d)) : Measure (PilotRecord d) :=
  (P.prod fairCoin).map (fun ua => observedPilot ua.1 ua.2)

abbrev PilotSample (m d : ℕ) := Fin m → PilotRecord d
abbrev MainSample (N d : ℕ) := Fin N → UnitRecord d
abbrev MainCovariates (N d : ℕ) := Fin N → XSpace d
-- @realizes Xmain(carrier Fin N → XSpace d)

abbrev WaveInput (m N d : ℕ) := (PilotSample m d × MainSample N d) × ℝ
-- @realizes U(real carrier; range pinned by randomizerLaw)

noncomputable def randomizerLaw : Measure ℝ :=
  (volume : Measure ℝ).restrict (Icc 0 1)
-- @realizes U(law supported on [0,1])

-- @node: ass:independent-iid-waves
def IndependentIIDWaves (P : Measure (UnitRecord d))
    (μ : Measure ((Fin m → UnitRecord d) × (Fin N → UnitRecord d))) : Prop :=
  μ = (Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin N => P)

-- @node: ass:pilot-half-randomized
def PilotHalfRandomized
    (μ : Measure (((Fin m → UnitRecord d) × (Fin N → UnitRecord d)) ×
      (Fin m → Bool))) : Prop :=
  ∀ r : Fin m,
    μ.map (fun v => (v.1.1 r, v.2 r)) =
      (μ.map (fun v => v.1.1 r)).prod fairCoin

noncomputable def latentTwoWaveLaw (P : Measure (UnitRecord d)) : Measure (WaveInput m N d) :=
  ((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
    (Measure.pi fun _ : Fin N => P)).prod
    randomizerLaw
-- @realizes U(latent wave product uses the [0,1] randomizer law)

abbrev Match (N : ℕ) :=
  {σ : Equiv.Perm (Fin N) // (∀ i, σ (σ i) = i) ∧ ∀ i, σ i ≠ i}
-- @realizes Match(fixed-point-free involution on Fin N)

instance (N : ℕ) : MeasurableSpace (Match N) := ⊤

def paired (M : Match N) (z : Fin N → Bool) : Prop :=
  ∀ i, z (M.val i) = !z i
-- @realizes Z(opposite treatment signs on each matched edge)

noncomputable def pairedCoinLaw (M : Match N) : Measure (Fin N → Bool) :=
  letI : DecidablePred (paired M) := Classical.decPred _
  ∑ z : Fin N → Bool,
    if paired M z then
      (ENNReal.ofReal ((2 : ℝ) ^ (-(N : ℝ) / 2))) • Measure.dirac z
    else 0
-- @realizes Z(each valid sign vector has mass 2^(-N/2))

abbrev Design (m N d : ℕ) :=
  PilotSample m d × MainCovariates N d × ℝ → Match N
-- @realizes Design(rule from pilot, main covariates, U to a matching)

def designDomain (m N d : ℕ) :
    Set (PilotSample m d × MainCovariates N d × ℝ) :=
  {input | (∀ r, (input.1 r).1 ∈ cube d) ∧
    (∀ i, input.2.1 i ∈ cube d) ∧ input.2.2 ∈ Icc (0 : ℝ) 1}
-- @realizes Design(pilot and main covariates in cube; randomizer in [0,1])
-- @realizes U(design input restricted to [0,1])

def designInput (w : WaveInput m N d) : PilotSample m d × MainCovariates N d × ℝ :=
  (w.1.1, fun i => (w.1.2 i).1, w.2)

-- @node: ass:paired-randomization
def PairedRandomization (P : Measure (UnitRecord d)) (D : Design m N d)
    (ZLaw : WaveInput m N d → Measure (Fin N → Bool)) : Prop :=
  (latentTwoWaveLaw (m := m) (N := N) P).bind (fun w =>
    (ZLaw w).map (fun z => (D (designInput w), z))) =
    ((latentTwoWaveLaw (m := m) (N := N) P).map
      (fun w => D (designInput w))).bind (fun M =>
        (pairedCoinLaw M).map (fun z => (M, z)))

-- @node: def:matching-design-class
def MatchingDesignClass (D : Design m N d) : Prop :=
  ValidMainSize N ∧ -- @realizes N(admissible designs require even N ≥ 2)
    Measurable (fun input : designDomain m N d => D input.val) ∧
    ∀ P : Measure (UnitRecord d),
    IsProbabilityMeasure P →
      PairedRandomization P D (fun w => pairedCoinLaw (D (designInput w)))
-- @realizes Dclass(measurable matching rules with fair paired assignment conditional on matching)

def observedMain (w : WaveInput m N d) (z : Fin N → Bool) : Fin N → PilotRecord d :=
  fun i => observedPilot (w.1.2 i) (z i)

-- @node: def:data-structure
noncomputable def twoWaveLaw (P : Measure (UnitRecord d)) (D : Design m N d) :
    Measure ((PilotSample m d × (Fin N → PilotRecord d)) × ℝ) :=
  (latentTwoWaveLaw (m := m) (N := N) P).bind fun w =>
    (pairedCoinLaw (D (designInput w))).map fun z =>
      ((w.1.1, observedMain w z), w.2)
-- @realizes Z(main assignment sampled from fair within-pair coins)
-- @realizes Y(main outcomes revealed only by observedMain through paired assignment)

noncomputable def experimentLaw (P : Measure (UnitRecord d))
    (ZLaw : WaveInput m N d → Measure (Fin N → Bool)) :
    Measure (WaveInput m N d × (Fin N → Bool)) :=
  (latentTwoWaveLaw (m := m) (N := N) P).bind fun w =>
    (ZLaw w).map fun z => (w, z)

def signed (b : Bool) : ℝ := if b then 1 else -1

noncomputable def pairedEstimator (N : ℕ)
    (wz : WaveInput m N d × (Fin N → Bool)) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i : Fin N,
    ((1 + signed (wz.2 i)) * (wz.1.1.2 i).2.2 -
      (1 - signed (wz.2 i)) * (wz.1.1.2 i).2.1)
-- @realizes tauhat(paired difference-in-means estimator)

noncomputable def ate (P : Measure (UnitRecord d)) : ℝ :=
  ∫ u, (u.2.2 - u.2.1) ∂P
-- @realizes tau(E[Y1-Y0])

noncomputable def realVariance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) : ℝ :=
  ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ

noncomputable def efficiencyBound (P : Measure (UnitRecord d)) : ℝ :=
  realVariance P (fun u => regression1 P u - regression0 P u) +
    2 * ∫ u, ((u.2.2 - regression1 P u) ^ 2 +
      (u.2.1 - regression0 P u) ^ 2) ∂P
-- @realizes Veff(Var(mu1-mu0)+2 expected conditional residual variances)

-- @node: def:pair-loss
noncomputable def pairLoss (g : XSpace d → ℝ) (x : MainCovariates N d) (M : Match N) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin N, (g (x i) - g (x (M.val i))) ^ 2
-- @realizes Closs(sum of squared score gaps, each edge counted once)

noncomputable def risk (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (D : Design m N d) : ℝ :=
  ∫ w, pairLoss g (fun i => (w.1.2 i).1) (D (designInput w)) / (N : ℝ)
    ∂latentTwoWaveLaw (m := m) (N := N) P
-- @realizes Risk(expected normalized pair loss under twoWaveLaw)

-- @node: def:minimax-risk
noncomputable def minimaxRisk (d m N : ℕ) (L β cX CX cg Cg : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ D : Design m N d, MatchingDesignClass D ∧
    v = sSup {r : ℝ | ∃ P : Measure (UnitRecord d), ∃ g : XSpace d → ℝ,
      RegularScoreModel P g L β cX CX cg Cg ∧ r = risk P g D}}
-- @realizes Rstar(infimum over designs of supremum over fixed-constant class)

-- @node: def:joint-frontier
noncomputable def jointFrontier (d m N : ℕ) (β : ℝ) : ℝ :=
  min ((N : ℝ) ^ (-2 * β / d))
    ((N : ℝ) ^ (-2 : ℝ) + (m : ℝ) ^ (-2 * β / (2 * β + d)))
-- @realizes Phi(minimum of geometric and pilot-oracle rates)

noncomputable def oracleLoss (P : Measure (UnitRecord d))
    (g : XSpace d → ℝ) (N : ℕ) (M : MainCovariates N d → Match N) : ℝ :=
  ∫ us, pairLoss g (fun i => (us i).1) (M (fun i => (us i).1)) / (N : ℝ)
    ∂(Measure.pi fun _ : Fin N => P)

def AdjSortSpec (s : Fin N → ℝ) (M : Match N) : Prop :=
  ∃ π : Equiv.Perm (Fin N),
    (∀ i j : Fin N, i < j →
      s (π i) < s (π j) ∨
        (s (π i) = s (π j) ∧ (π i).val < (π j).val)) ∧
    (∀ i j : Fin N, i.val + 1 = j.val → Even i.val → M.val (π i) = π j)

-- @node: exists_adjSortMatching
lemma exists_adjSortMatching (s : Fin N → ℝ) (hN : Even N) (hN2 : 2 ≤ N) :
    ∃ M : Match N, AdjSortSpec s M := by
  obtain ⟨k, hk⟩ := hN
  let e : Fin N ≃ Fin k × Fin 2 :=
    (Fin.castOrderIso (show N = k * 2 by omega)).toEquiv.trans
      (finProdFinEquiv (m := k) (n := 2)).symm
  let flip : Equiv.Perm (Fin k × Fin 2) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.swap (0 : Fin 2) 1)
  have flipflip (p : Fin k × Fin 2) : flip (flip p) = p := by
    rcases p with ⟨a, b⟩
    fin_cases b <;> simp [flip]
  let τ : Equiv.Perm (Fin N) := e.trans (flip.trans e.symm)
  have ττ (i : Fin N) : τ (τ i) = i := by
    simp [τ, flipflip]
  have τne (i : Fin N) : τ i ≠ i := by
    intro hi
    have he := congrArg e hi
    have hf : flip (e i) = e i := by simpa [τ] using he
    have hfin : (Equiv.swap (0 : Fin 2) 1) (e i).2 = (e i).2 :=
      congrArg Prod.snd hf
    have hcases : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide
    rcases hcases (e i).2 with h | h <;> simp [h, flip] at hfin
  let π : Equiv.Perm (Fin N) := Tuple.sort s
  let M : Match N := ⟨π.symm.trans (τ.trans π), by
    constructor
    · intro i
      change π (τ (π.symm (π (τ (π.symm i))))) = i
      simp [ττ]
    · intro i hi
      have hh : τ (π.symm i) = π.symm i := by
        have := congrArg π.symm hi
        simpa using this
      exact τne (π.symm i) hh⟩
  refine ⟨M, π, ?_, ?_⟩
  · intro i j hij
    have hsort := (Tuple.eq_sort_iff (σ := π) (f := s)).mp rfl
    rcases (hsort.1 hij.le).eq_or_lt with h | h
    · exact Or.inr ⟨h, hsort.2 i j hij h⟩
    · exact Or.inl h
  · intro i j hij heven
    obtain ⟨r, hr⟩ := heven
    have hi0 : i.val % 2 = 0 := by omega
    have hi0' : (Fin.cast (show N = k * 2 by omega) i).modNat = (0 : Fin 2) := by
      apply Fin.ext
      simpa using hi0
    have ht : τ i = j := by
      have ht' : flip (e i) = e j := by
        apply Prod.ext
        · simp [e, finProdFinEquiv, flip, Fin.ext_iff]
          omega
        · simp [e, finProdFinEquiv, flip, Fin.ext_iff, hi0']
          omega
      apply e.injective
      simpa [τ] using ht'
    simpa [M, ht]


-- @node: def:oracle-pairing
noncomputable def adjSortMatching (s : Fin N → ℝ) (hN : Even N)
    (hN2 : 2 ≤ N) : Match N :=
  Classical.choose (exists_adjSortMatching s hN hN2)
-- @realizes Moracle(adjacent sorted score matching, ties by label)

noncomputable def oracleMatching (g : XSpace d → ℝ)
    (x : MainCovariates N d) (hN : Even N) (hN2 : 2 ≤ N) : Match N :=
  adjSortMatching (fun i => g (x i)) hN hN2

noncomputable def geometricCost (x : MainCovariates N d) (M : Match N) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin N, (euclideanDistance (x i) (x (M.val i))) ^ 2

def matchingCode (M : Match N) : ℕ :=
  ∑ i : Fin N, (M.val i).val * (N + 1) ^ i.val

lemma exists_geometricMatching (x : MainCovariates N d)
    (hN : Even N) (hN2 : 2 ≤ N) :
    ∃ M : Match N, ∀ M' : Match N,
      geometricCost x M ≤ geometricCost x M' ∧
      (geometricCost x M = geometricCost x M' → matchingCode M ≤ matchingCode M') := by
  have : Nonempty (Match N) := ⟨(exists_adjSortMatching (fun _ => 0) hN hN2).choose⟩
  obtain ⟨M₀, hM₀⟩ := Finite.exists_min (geometricCost x)
  let S := {M : Match N // geometricCost x M = geometricCost x M₀}
  have : Nonempty S := ⟨⟨M₀, rfl⟩⟩
  obtain ⟨M₁, hM₁⟩ := Finite.exists_min (fun M : S => matchingCode M.val)
  refine ⟨M₁.val, fun M' => ⟨?_, ?_⟩⟩
  · rw [M₁.property]
    exact hM₀ M'
  · intro heq
    have hmem : geometricCost x M' = geometricCost x M₀ := heq.symm.trans M₁.property
    exact hM₁ ⟨M', hmem⟩

noncomputable def geometricMatching (x : MainCovariates N d)
    (hN : Even N) (hN2 : 2 ≤ N) : Match N :=
  Classical.choose (exists_geometricMatching x hN hN2)
-- @realizes Mgeo(minimum squared Euclidean matching, deterministic choice)

noncomputable def histogramBins (m d : ℕ) (β : ℝ) : ℕ :=
  max 1 (Nat.ceil ((m : ℝ) ^ (1 / (2 * β + d))))

noncomputable def histogramCell (m d : ℕ) (β : ℝ) (x : XSpace d) : Fin d → ℕ :=
  fun i => min (histogramBins m d β - 1)
    (Nat.floor ((histogramBins m d β : ℝ) * x i))

noncomputable def clip01 (t : ℝ) : ℝ := min 1 (max 0 t)

-- @node: def:histogram-score
noncomputable def histogramScore (β : ℝ) (pilot : PilotSample m d)
    (x : XSpace d) : ℝ :=
  let cell := (Finset.univ : Finset (Fin m)).filter
    (fun r => histogramCell m d β (pilot r).1 = histogramCell m d β x)
  if cell.card = 0 then 1 / 2
  else clip01 ((∑ r ∈ cell, (pilot r).2.2) / cell.card)
-- @realizes ghat(clipped cell average, 1/2 on empty cells)

noncomputable def plugInMatching (β : ℝ) (pilot : PilotSample m d)
    (x : MainCovariates N d) (hN : Even N) (hN2 : 2 ≤ N) : Match N :=
  adjSortMatching (fun i => histogramScore β pilot (x i)) hN hN2
-- @realizes Mplug(adjacent matching by histogram-estimated scores)

-- @node: def:selector-design
noncomputable def selectorDesign (β : ℝ) (hN : Even N) (hN2 : 2 ≤ N) :
    Design m N d :=
  fun input =>
    if (N : ℝ) ^ (-2 * β / d) ≤
        (N : ℝ) ^ (-2 : ℝ) + (m : ℝ) ^ (-2 * β / (2 * β + d)) then
      geometricMatching input.2.1 hN hN2
    else
      plugInMatching β input.1 input.2.1 hN hN2
-- @realizes Dsel(rate selector between Mgeo and Mplug)

noncomputable def triangularWave (t : ℝ) : ℝ :=
  let r := t - Int.floor t
  if r ≤ 1 / 4 then 4 * r
  else if r ≤ 3 / 4 then 2 - 4 * r
  else 4 * r - 4

noncomputable def triangularFold (t : ℝ) : ℝ :=
  |t - 2 * Int.floor ((t + 1) / 2)|

noncomputable def localSign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def foldedFirstBump (t : ℝ) : ℝ :=
  max 0 (min 1 (min (32 * (t - 13 / 32)) (32 * (19 / 32 - t))))

noncomputable def foldedTransverseBump (t : ℝ) : ℝ :=
  max 0 (min 1 (min (16 * (t - 3 / 16)) (16 * (13 / 16 - t))))

noncomputable def meshBump (hd : 0 < d) (h : ℝ)
    (k : Fin d → ℕ) (x : XSpace d) : ℝ :=
  foldedFirstBump (x ⟨0, hd⟩ / h - k ⟨0, hd⟩) *
    ∏ i : Fin d, if i.val = 0 then (1 : ℝ)
      else foldedTransverseBump (x i / h - k i)

def activeMeshCell (hd : 0 < d) (q : ℕ) (k : Fin d → ℕ) : Prop :=
  (∀ i, k i < q) ∧
    (1 / 3 : ℝ) ≤ (k ⟨0, hd⟩ : ℝ) / q ∧
    ((k ⟨0, hd⟩ : ℝ) + 1) / q ≤ (2 / 3 : ℝ)

def meshCube (h : ℝ) (k : Fin d → ℕ) : Set (XSpace d) :=
  {x | x ∈ cube d ∧ ∀ i, (k i : ℝ) * h ≤ x i ∧
    (x i < ((k i : ℝ) + 1) * h ∨
      (x i = 1 ∧ ((k i : ℝ) + 1) * h = 1))}

def meshCore (hd : 0 < d) (h : ℝ) (k : Fin d → ℕ) : Set (XSpace d) :=
  {x | x ∈ cube d ∧
    (k ⟨0, hd⟩ + 7 / 16 : ℝ) * h ≤ x ⟨0, hd⟩ ∧
    x ⟨0, hd⟩ ≤ (k ⟨0, hd⟩ + 9 / 16 : ℝ) * h ∧
    ∀ i : Fin d, i.val ≠ 0 →
      (k i + 1 / 4 : ℝ) * h ≤ x i ∧ x i ≤ (k i + 3 / 4 : ℝ) * h}

def FoldedGeometry (hd : 0 < d) (q K : ℕ)
    (Q : Fin K → Set (XSpace d)) (ψ : Fin K → XSpace d → ℝ)
    (B : Fin K → Set (XSpace d)) : Prop :=
  0 < q ∧ ∃ k : Fin K → Fin d → ℕ,
    Function.Injective k ∧
    (∀ v, activeMeshCell hd q v ↔ ∃ j, k j = v) ∧
    ∀ j, Q j = meshCube ((q : ℝ)⁻¹) (k j) ∧
      ψ j = meshBump hd ((q : ℝ)⁻¹) (k j) ∧
      B j = meshCore hd ((q : ℝ)⁻¹) (k j)

noncomputable def foldedRawScore (hd : 0 < d) (β h κ ε : ℝ)
    (K : ℕ) (ψ : Fin K → XSpace d → ℝ) (θ : Fin K → Bool)
    (x : XSpace d) : ℝ :=
  let x1 := x ⟨0, hd⟩
  let a := κ * h ^ β
  let perturb := ∑ j : Fin K, localSign (θ j) * ψ j x
  if β < 1 then
    1 / 4 + (1 / 2) * triangularFold (x1 + a * triangularWave (x1 / h) + ε * a * perturb)
  else
    1 / 4 + x1 / 2 + ε * h * perturb

noncomputable def bernoulliOutcomeLaw (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.dirac 0 +
    ENNReal.ofReal p • Measure.dirac 1

noncomputable def bernoulliUnitLaw (g : XSpace d → ℝ) : Measure (UnitRecord d) :=
  (cubeMeasure d).bind fun x =>
    ((bernoulliOutcomeLaw (g x)).prod (bernoulliOutcomeLaw (g x))).map
      fun ys => (x, ys.1, ys.2)

def flipCoordinate (θ : Fin K → Bool) (j : Fin K) : Fin K → Bool :=
  fun k => if k = j then !θ k else θ k

def FoldedParameterConditions (q : ℕ)
    (β L cg Cg h κ ε A Bconst : ℝ) : Prop :=
  0 < q ∧ h = (q : ℝ)⁻¹ ∧ 0 < β ∧ β < 1 ∧
    0 < κ ∧ 0 < ε ∧ 0 < A ∧ 0 < Bconst ∧
    Bconst * ε ≤ 1 ∧
    A * ε ≤ (min (1 - cg / 2) (Cg / 2 - 1)) / 4 ∧
    1 / 2 + A * κ < L ∧ 4 ≤ κ * h ^ β / h ∧
    κ * h ^ β * (1 + ε) ≤ 1 / 12

-- @node: def:folded-hypercube-handle
noncomputable def foldedHypercube (hd : 0 < d) (β h κ ε : ℝ)
    (K : ℕ) (ψ : Fin K → XSpace d → ℝ)
    (θ : Fin K → Bool) (x : XSpace d) : ℝ :=
  foldedRawScore hd β h κ ε K ψ θ x
-- @realizes Hfold(folded triangular score formula)
-- @realizes h(mesh width in folded formula)
-- @realizes theta(hypercube sign vector)
-- @realizes psij(localized perturbation functions in folded formula)

-- @node: def:pilot-augmented-anchor-class
structure AnchorClass (P : Measure (UnitRecord d))
    (β cX CX : ℝ) : Prop where
  parameters : ValidAnchorParameters d β cX CX
    -- @realizes beta(anchor range (0,1])
    -- @realizes cX(anchor range (0,1])
    -- @realizes CX(anchor range [1,∞))
  covariate_density : CovariateDensity P cX CX
  second_moment0 : Integrable (fun u : UnitRecord d => u.2.1 ^ 2) P
  second_moment1 : Integrable (fun u : UnitRecord d => u.2.2 ^ 2) P
  score_version : ∃ g : XSpace d → ℝ,
    IsHalfSumVersion P g ∧ HolderScore g 1 β
-- @realizes Hanchor(pilot-augmented radius-one Hölder class)

def IsSideCube (h : ℝ) (Q : Set (XSpace d)) : Prop :=
  ∃ a : XSpace d,
    (∀ i, 0 ≤ a i ∧ a i + h ≤ 1) ∧
      Q = {x | x ∈ cube d ∧ ∀ i, a i ≤ x i ∧
        (x i < a i + h ∨ (x i = 1 ∧ a i + h = 1))}

def HypercubeFamily (d : ℕ) (β L cX CX cg Cg h c0 c1 C1 C2 κ ε _A _Bconst : ℝ) : Prop :=
  ∃ K : ℕ, ∃ Q : Fin K → Set (XSpace d),
    ∃ ψ : Fin K → XSpace d → ℝ, ∃ B : Fin K → Set (XSpace d),
    ∃ g : (Fin K → Bool) → XSpace d → ℝ,
    ∃ base : XSpace d → ℝ, ∃ amplitude : ℝ,
    -- @realizes K(number of active cells, comparable to h^(-d))
    c0 * h ^ (-(d : ℝ)) ≤ K ∧ K ≤ C1 * h ^ (-(d : ℝ)) ∧
    -- @realizes Qj(disjoint side-h active cubes)
    (∀ j, IsSideCube h (Q j)) ∧
    (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧
    -- @realizes Bj(large cores inside Qj)
    (∀ j, B j ⊆ Q j ∧ c0 * h ^ (d : ℝ) ≤ ((cubeMeasure d) (B j)).toReal) ∧
    -- @realizes psij([0,1]-valued bump, supported in Qj and equal to 1 on Bj)
    (∀ j x, 0 ≤ ψ j x ∧ ψ j x ≤ 1 ∧ (x ∉ Q j → ψ j x = 0) ∧
      (x ∈ B j → ψ j x = 1)) ∧
    c1 * h ^ β ≤ amplitude ∧
    -- @realizes theta(signs index the laws)
    (∀ θ x, g θ x = base x + amplitude * ∑ j : Fin K, localSign (θ j) * ψ j x) ∧
    (∀ θ j x, x ∉ Q j → g θ x = g (flipCoordinate θ j) x) ∧
    (∀ hd : 0 < d, β < 1 →
      ∀ θ x, g θ x = foldedHypercube hd β h κ ε K ψ θ x) ∧
    (∀ θ, RegularScoreModel (bernoulliUnitLaw (g θ)) (g θ) L β cX CX cg Cg) ∧
    (∀ θ, (bernoulliUnitLaw (g θ)).map Prod.fst = cubeMeasure d) ∧
    (∀ m : ℕ, 1 ≤ m → ∀ θ j,
      InformationTheory.klDiv
        (Measure.pi fun _ : Fin m => pilotUnitLaw (bernoulliUnitLaw (g θ)))
        (Measure.pi fun _ : Fin m =>
          pilotUnitLaw (bernoulliUnitLaw (g (flipCoordinate θ j)))) ≤
        ENNReal.ofReal (C2 * m * h ^ ((d : ℝ) + 2 * β)))
-- @realizes pg(common prescribed density bounds via RegularScoreModel)

-- @node: oeq:regular-density-hypercube
def RegularDensityHypercubeIntermediateQuestion (_d : ℕ)
    (_β _L _cX _CX _cg _Cg : ℝ) : _root_.String :=
  "For the nonempty regular-score class with (2 d^(beta/2))^(-1) <= L <= 1/2, \
    determine whether every sufficiently small reciprocal-integer mesh h admits a \
    regular-density likelihood hypercube in the fixed class with K comparable to \
    h^(-d), each core volume comparable to h^d, score separation of order h^beta, \
    and one-coordinate randomized-pilot KL at most a constant times m h^(d+2 beta); \
    or prove that the fixed Holder radius or score-density envelope forbids such a \
    family in part or all of this intermediate regime. The necessary radius bound and \
    the construction for L > 1/2 are separate settled results. Neither alternative \
    is asserted here."

end CausalSmith.Experimentation.PilotscorePairingFrontier

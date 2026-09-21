module
public import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! Explicit finite two-class witness laws and local experiments. -/

@[expose] public section

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators ENNReal
open MeasureTheory Set

/-- For [the supplied parameters](hyp:p,b), [bernoulli Mass](goal) is given by [its defining clause](step:1). -/
def bernoulliMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

-- @node: bernoulliMass_nonneg
/-- Bernoulli mass nonneg: under [the stated inputs and assumptions](hyp:p,b,hp0,hp1), [the stated conclusion](goal) holds. -/
lemma bernoulliMass_nonneg (p : ℝ) (b : Bool) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ bernoulliMass p b := by
  cases b <;> simp [bernoulliMass] <;> linarith

-- @node: sum_bernoulliMass
/-- Sum bernoulli mass: under [the stated inputs and assumptions](hyp:p), [the stated conclusion](goal) holds. -/
lemma sum_bernoulliMass (p : ℝ) : ∑ b : Bool, bernoulliMass p b = 1 := by
  simp [bernoulliMass]

-- @node: sum_mul_bernoulliMass
/-- Sum mul bernoulli mass: under [the stated inputs and assumptions](hyp:a,p), [the stated conclusion](goal) holds. -/
lemma sum_mul_bernoulliMass (a p : ℝ) :
    ∑ b : Bool, a * bernoulliMass p b = a := by
  rw [← Finset.mul_sum, sum_bernoulliMass, mul_one]
/-- For [the supplied parameters](hyp:a,b), [vec2](goal) is given by [its defining clause](step:1). -/
def vec2 (a b : ℝ) : Fin 2 → ℝ := fun i => if i.val = 0 then a else b
/-- For [the supplied parameters](hyp:b), [bool Real](goal) is given by [its defining clause](step:1). -/
def boolReal (b : Bool) : ℝ := if b then 1 else 0

/-- For [the supplied parameters](hyp:A), [det2](goal) is given by [its defining clause](step:1). -/
def det2 (A : RectMatrix 2 2) : ℝ := A 0 0 * A 1 1 - A 0 1 * A 1 0

/-- For [the supplied parameters](hyp:u,t,x,z,y0,y1), [witness Point](goal) is given by [its defining clause](step:1). -/
def witnessPoint (u : Fin 2) (t x z y0 y1 : Bool) : FullData 2 2 2 where
  U := u
  T := t
  X := vec2 1 (boolReal x)
  Z := vec2 1 (boolReal z)
  Y0 := boolReal y0
  Y1 := boolReal y1
  Y := if t then boolReal y1 else boolReal y0

/-- For [the supplied parameters](hyp:eps,u,t,x,z,y0,y1), [witness Weight](goal) is given by [its defining clause](step:1). -/
noncomputable def witnessWeight (eps : ℝ) (u : Fin 2) (t x z y0 y1 : Bool) : ℝ :=
  let pu := if u.val = 0 then 2 / 5 else 3 / 5
  let pt := if u.val = 0 then 2 / 5 else 3 / 5
  let px := if u.val = 0 then 1 / 5 else 4 / 5
  let pz := if t then (if u.val = 0 then 7 / 20 else 3 / 4)
    else (if u.val = 0 then 3 / 10 else 7 / 10)
  let py0 := 1 / 4
  let py1 := if u.val = 0 then 1 / 2 - eps else 1 / 2 + eps
  pu * bernoulliMass pt t * bernoulliMass px x * bernoulliMass pz z *
    bernoulliMass py0 y0 * bernoulliMass py1 y1

/-- Every elementary weight in the admissible witness family is nonnegative.     Under [the stated inputs and assumptions](hyp:eps,hlo,hhi,u,t,x,z,y0,y1), [the stated conclusion](goal) holds. -/
-- @node: witnessWeight_nonneg
lemma witnessWeight_nonneg (eps : ℝ) (hlo : 0 ≤ eps) (hhi : eps ≤ 1 / 8)
    (u : Fin 2) (t x z y0 y1 : Bool) :
    0 ≤ witnessWeight eps u t x z y0 y1 := by
  fin_cases u <;> cases t <;> cases x <;> cases z <;> cases y0 <;> cases y1 <;>
    simp [witnessWeight, bernoulliMass] <;> nlinarith

/-- Latent-arm cylinders are measurable in the witness full-data space.     Under [the stated inputs and assumptions](hyp:u,t), [the stated conclusion](goal) holds. -/
-- @node: measurableSet_witness_latentCell
lemma measurableSet_witness_latentCell (u : Fin 2) (t : Bool) :
    MeasurableSet (latentCell (dx := 2) (dz := 2) u t) := by
  have hcoord : Measurable (@FullData.toCoordinates 2 2 2) :=
    continuous_induced_dom.measurable
  have hUT : Measurable (fun w : FullData 2 2 2 => (w.U, w.T)) := by
    change Measurable (fun w => ((FullData.toCoordinates w).1,
      (FullData.toCoordinates w).2.1))
    exact hcoord.fst.prodMk hcoord.snd.fst
  have hpre := hUT (measurableSet_singleton (u, t))
  simpa [latentCell, Set.preimage] using hpre

/-- Latent-class cylinders are measurable in the witness full-data space.     Under [the stated inputs and assumptions](hyp:u), [the stated conclusion](goal) holds. -/
-- @node: measurableSet_witness_latentClass
lemma measurableSet_witness_latentClass (u : Fin 2) :
    MeasurableSet (latentClass (dx := 2) (dz := 2) u) := by
  have hcoord : Measurable (@FullData.toCoordinates 2 2 2) :=
    continuous_induced_dom.measurable
  have hU : Measurable (fun w : FullData 2 2 2 => w.U) := by
    change Measurable (fun w => (FullData.toCoordinates w).1)
    exact hcoord.fst
  have hpre := hU (measurableSet_singleton u)
  simpa [latentClass, Set.preimage] using hpre

/-- Domain of the collision-witness perturbation.     For [the supplied parameters](hyp:eps), [the defined object](goal) is given by [its defining clause](step:1). -/
def WitnessPerturbationDomain (eps : ℝ) : Prop :=
  0 ≤ eps ∧ -- @realizes \(\varepsilon\)(nonnegative witness perturbation)
  eps ≤ 1 / 8 -- @realizes \(\varepsilon\)(witness perturbation at most one eighth)

/-- Explicit two-class Bernoulli collision law.
    @realizes \(P_{\varepsilon}^{\mathrm{wit}}\)(finite Dirac law)
    @realizes \(\varepsilon\)(real carrier; range via WitnessPerturbationDomain)        For [the supplied parameters](hyp:eps), [the defined object](goal) is given by [its defining clause](step:1). -/
-- @node: def:two-class-witness
noncomputable def witnessLaw (eps : ℝ) : Measure (FullData 2 2 2) :=
  ∑ u : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
    ENNReal.ofReal (witnessWeight eps u t x z y0 y1) •
      Measure.dirac (witnessPoint u t x z y0 y1)

set_option maxHeartbeats 1000000 in
-- Expanding the six binary coordinates produces 128 elementary nonnegativity goals.
/-- Witness law is probability measure: under [the stated inputs and assumptions](hyp:eps,hlo,hhi), [the stated conclusion](goal) holds. -/
lemma witnessLaw_isProbabilityMeasure (eps : ℝ) (hlo : 0 ≤ eps) (hhi : eps ≤ 1 / 8) :
    IsProbabilityMeasure (witnessLaw eps) := by
  have hw : ∀ (u : Fin 2) (t x z y0 y1 : Bool),
      0 ≤ witnessWeight eps u t x z y0 y1 := by
    intro u t x z y0 y1
    fin_cases u <;> cases t <;> cases x <;> cases z <;> cases y0 <;> cases y1 <;>
      simp [witnessWeight, bernoulliMass] <;> nlinarith
  constructor
  rw [show (witnessLaw eps) Set.univ =
      ∑ u : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        ENNReal.ofReal (witnessWeight eps u t x z y0 y1) by simp [witnessLaw]]
  calc
    _ = ENNReal.ofReal (∑ u : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool,
        ∑ y0 : Bool, ∑ y1 : Bool, witnessWeight eps u t x z y0 y1) := by
      symm
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro u _
        rw [ENNReal.ofReal_sum_of_nonneg]
        · apply Finset.sum_congr rfl
          intro t _
          rw [ENNReal.ofReal_sum_of_nonneg]
          · apply Finset.sum_congr rfl
            intro x _
            rw [ENNReal.ofReal_sum_of_nonneg]
            · apply Finset.sum_congr rfl
              intro z _
              rw [ENNReal.ofReal_sum_of_nonneg]
              · apply Finset.sum_congr rfl
                intro y0 _
                rw [ENNReal.ofReal_sum_of_nonneg]
                exact fun y1 _ => hw u t x z y0 y1
              · exact fun y0 _ => Finset.sum_nonneg fun y1 _ => hw u t x z y0 y1
            · exact fun z _ => Finset.sum_nonneg fun y0 _ =>
                Finset.sum_nonneg fun y1 _ => hw u t x z y0 y1
          · exact fun x _ => Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun y0 _ =>
              Finset.sum_nonneg fun y1 _ => hw u t x z y0 y1
        · exact fun t _ => Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun z _ =>
            Finset.sum_nonneg fun y0 _ => Finset.sum_nonneg fun y1 _ => hw u t x z y0 y1
      · exact fun u _ => Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun x _ =>
          Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun y0 _ =>
            Finset.sum_nonneg fun y1 _ => hw u t x z y0 y1
    _ = 1 := by
      simp [witnessWeight, bernoulliMass]
      ring

/-- Summing out the four Bernoulli nuisance coordinates leaves the prescribed latent-class and
treatment masses.  This is the finite-factorization calculation used by the witness-validity
proof for its class and arm marginals.        Under [the stated inputs and assumptions](hyp:eps,u,t), [the stated conclusion](goal) holds. -/
-- @node: witnessWeight_sum_nuisance
lemma witnessWeight_sum_nuisance (eps : ℝ) (u : Fin 2) (t : Bool) :
    ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      witnessWeight eps u t x z y0 y1 =
      (if u.val = 0 then 2 / 5 else 3 / 5) *
        bernoulliMass (if u.val = 0 then 2 / 5 else 3 / 5) t := by
  simp only [witnessWeight, sum_mul_bernoulliMass]

/-- Restricted integrals under the finite witness law reduce to its explicit 128-point sum.     Under [the stated inputs and assumptions](hyp:eps,A,hA,f), [the stated conclusion](goal) holds. -/
-- @node: integral_witnessLaw_restrict
lemma integral_witnessLaw_restrict (eps : ℝ) (A : Set (FullData 2 2 2))
    [DecidablePred (· ∈ A)] (hA : MeasurableSet A)
    (f : FullData 2 2 2 → ℝ) :
    ∫ w in A, f w ∂witnessLaw eps =
      ∑ u : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        (ENNReal.ofReal (witnessWeight eps u t x z y0 y1)).toReal *
          if witnessPoint u t x z y0 y1 ∈ A then f (witnessPoint u t x z y0 y1) else 0 := by
  classical
  let c : Fin 2 × Bool × Bool × Bool × Bool × Bool → ℝ≥0∞ := fun i =>
    ENNReal.ofReal (witnessWeight eps i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2)
  let p : Fin 2 × Bool × Bool × Bool × Bool × Bool → FullData 2 2 2 := fun i =>
    witnessPoint i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2
  have hwitness : witnessLaw eps = ∑ i, c i • Measure.dirac (p i) := by
    simp only [witnessLaw, c, p, Fintype.sum_prod_type]
  rw [← integral_indicator hA, hwitness, integral_finsetSum_measure]
  · simp only [c, p, Fintype.sum_prod_type, integral_smul_measure, integral_dirac,
      smul_eq_mul, Set.indicator_apply]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure (by simp [c])

/-- Event masses under the finite witness law reduce to its explicit 128-point sum.     Under [the stated inputs and assumptions](hyp:eps,A,hA), [the stated conclusion](goal) holds. -/
-- @node: witnessLaw_real
lemma witnessLaw_real (eps : ℝ) (A : Set (FullData 2 2 2))
    [DecidablePred (· ∈ A)] (hA : MeasurableSet A) :
    (witnessLaw eps).real A =
      ∑ u : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        (ENNReal.ofReal (witnessWeight eps u t x z y0 y1)).toReal *
          if witnessPoint u t x z y0 y1 ∈ A then 1 else 0 := by
  classical
  simpa using integral_witnessLaw_restrict eps A hA (fun _ => (1 : ℝ))

/-- Conditional means under the witness law are ratios of two explicit 128-point sums.     Under [the stated inputs and assumptions](hyp:eps,A,hA,f), [the stated conclusion](goal) holds. -/
-- @node: conditionalMean_witnessLaw
lemma conditionalMean_witnessLaw (eps : ℝ) (A : Set (FullData 2 2 2))
    [DecidablePred (· ∈ A)] (hA : MeasurableSet A)
    (f : FullData 2 2 2 → ℝ) :
    conditionalMean (witnessLaw eps) A f =
      (∑ u : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        (ENNReal.ofReal (witnessWeight eps u t x z y0 y1)).toReal *
          if witnessPoint u t x z y0 y1 ∈ A then 1 else 0)⁻¹ *
      (∑ u : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        (ENNReal.ofReal (witnessWeight eps u t x z y0 y1)).toReal *
          if witnessPoint u t x z y0 y1 ∈ A then f (witnessPoint u t x z y0 y1) else 0) := by
  rw [conditionalMean, witnessLaw_real eps A hA, integral_witnessLaw_restrict eps A hA]

-- @node: ass:local-quotient-neighborhood
/-- For [the supplied parameters](hyp:P), [Local Quotient Neighborhood](goal) is given by [its defining clause](step:1). -/
def LocalQuotientNeighborhood {n : ℕ} {cLoc : ℝ}
    (P : Measure (FullData 2 2 2)) [IsProbabilityMeasure P] : Prop :=
  letI : IsProbabilityMeasure (witnessLaw 0) :=
    witnessLaw_isProbabilityMeasure 0 (by norm_num) (by norm_num)
  InformationTheory.klDiv (obsLaw P) (obsLaw (witnessLaw 0)) ≤ ENNReal.ofReal (cLoc / n)

-- @node: ass:local-weight-neighborhood
/-- For [the supplied parameters](hyp:P), [Local Weight Neighborhood](goal) is given by [its defining clause](step:1). -/
def LocalWeightNeighborhood {n : ℕ} {g cLoc : ℝ}
    (P : Measure (FullData 2 2 2)) [IsProbabilityMeasure P] : Prop :=
  let eps := g / 2
  InformationTheory.klDiv (obsLaw P)
    ((witnessLaw eps).map obsMap) ≤ ENNReal.ofReal (cLoc / n)

/-- Local quotient-law KL experiment. @realizes \(\mathcal L_{n}^{\nu}\)(model KL neighborhood)     It uses [the supplied parameters](hyp:P). -/
-- @node: def:local-quotient-experiment
structure LocalQuotientExperiment {n : ℕ} {L pi0 sigma0 cLoc : ℝ}
    (P : Measure (FullData 2 2 2)) [IsProbabilityMeasure P] : Prop where
  toUCVMWModel : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P
  cLoc_pos : 0 < cLoc -- @realizes \(c_{\mathrm{loc}}\)(positive local radius)
  cLoc_lt_one : cLoc < 1 -- @realizes \(c_{\mathrm{loc}}\)(local radius below one)
  neighborhood : LocalQuotientNeighborhood (n := n) (cLoc := cLoc) P

/-- Local separated labeled-weight experiment.
    @realizes \(\mathcal L_{n,g}^{p}\)(gap model KL neighborhood)        It uses [the supplied parameters](hyp:P). -/
-- @node: def:local-weight-experiment
structure LocalWeightExperiment {n : ℕ} {L pi0 sigma0 cLoc g : ℝ}
    (P : Measure (FullData 2 2 2)) [IsProbabilityMeasure P] : Prop where
  toGapStratum : GapStratum (L := L) (pi0 := pi0) (sigma0 := sigma0) (g := g) P
  cLoc_pos : 0 < cLoc -- @realizes \(c_{\mathrm{loc}}\)(positive local radius)
  cLoc_lt_one : cLoc < 1 -- @realizes \(c_{\mathrm{loc}}\)(local radius below one)
  neighborhood : LocalWeightNeighborhood (n := n) (g := g) (cLoc := cLoc) P

/-- A complex spectral point of a real square compressed operator.     For [the supplied parameters](hyp:D,z), [the defined object](goal) is given by [its defining clause](step:1). -/
def MatrixEigenvalue {k : ℕ} (D : RectMatrix k k) (z : ℂ) : Prop :=
  ∃ v : Fin k → ℂ, v ≠ 0 ∧
    ∀ i, ∑ j, (D i j : ℂ) * v j = z * v i

/-- For [the supplied parameters](hyp:D,z,v), [Matrix Eigenvector](goal) is given by [its defining clause](step:1). -/
def MatrixEigenvector {k : ℕ} (D : RectMatrix k k) (z : ℂ) (v : Fin k → ℂ) : Prop :=
  v ≠ 0 ∧ ∀ i, ∑ j, (D i j : ℂ) * v j = z * v i

/-- For [the supplied parameters](hyp:D), [complexify Matrix](goal) is given by [its defining clause](step:1). -/
def complexifyMatrix {k : ℕ} (D : RectMatrix k k) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => (D i j : ℂ)

/-- A polynomial aggregate projector used by the separate structured-lattice algebra.  The
constructive repair handle below deliberately does not use it: empirical clusters use Riesz
contour projectors instead.        For [the supplied parameters](hyp:D,eigenvalue,i), [the defined object](goal) is given by [its defining clause](step:1). -/
noncomputable def polynomialAggregateProjector {k : ℕ} (D : RectMatrix k k)
    (eigenvalue : Fin k → ℝ) (i : Fin k) : RectMatrix k k :=
  (Finset.univ.filter (fun j => eigenvalue j ≠ eigenvalue i)).toList.foldl
    (fun E j => E * ((eigenvalue i - eigenvalue j)⁻¹ •
      (D - eigenvalue j • (1 : RectMatrix k k)))) 1

/-- For [the supplied parameters](hyp:C), [aggregate Mass](goal) is given by [its defining clause](step:1). -/
noncomputable def aggregateMass {k : ℕ} {radius : ℝ}
    (ν : AtomicLaw k radius) (C : Set ℂ) : ℝ := by
  classical
  exact ∑ i, if (ν.atom i : ℂ) ∈ C then ν.weight i else 0

/-- For [the supplied parameters](hyp:m), [moment Discrepancy](goal) is given by [its defining clause](step:1). -/
noncomputable def momentDiscrepancy {k : ℕ} {radius : ℝ}
    (m : Fin (2 * k) → ℝ) (ν : AtomicLaw k radius) : ℝ :=
  ∑ j, |m j - ∑ i, ν.weight i * ν.atom i ^ (j : ℕ)|

/-- The identifying moment vector computed from a compressed operator and its summary anchors.     For [the supplied parameters](hyp:deltaQ,s,basis), [the defined object](goal) is given by [its defining clause](step:1). -/
noncomputable def summarySpectralMoments {k dx dz : ℕ}
    (deltaQ : RectMatrix k k) (s : SummarySpace dx dz) (basis : SignalBasis dx k) :
    Fin (2 * k) → ℝ := fun j =>
  ∑ a, leftAnchor s basis a *
    (∑ b, (deltaQ ^ (j : ℕ)) a b * rightAnchor basis b)

/-- Full pairwise diameter of the effect cluster specified by the overlap relation.     For [the supplied parameters](hyp:effect,sameCluster,i), [the defined object](goal) is given by [its defining clause](step:1). -/
noncomputable def effectClusterDiameter {k : ℕ} (effect : Fin k → ℝ)
    (sameCluster : Fin k → Fin k → Bool) (i : Fin k) : ℝ :=
  sSup {d : ℝ | ∃ u v, sameCluster i u = true ∧ sameCluster i v = true ∧
    d = |effect u - effect v|}

/-- The compressed operator computed from the one empirical summary generated by `sample`.     For [the supplied parameters](hyp:sample,basis), [the defined object](goal) is given by [its defining clause](step:1). -/
noncomputable def repairEmpiricalCompressedOperator {k dx dz n : ℕ} {pi0 sigma0 : ℝ}
    (sample : Fin n → Obs dx dz) (basis : SignalBasis dx k) : RectMatrix k k :=
  let sHat := empSummary sample
  let threshold := pi0 * sigma0 ^ 2 / 2
  thresholdedPenroseInverse threshold (sHat.M1 * basis.V) * (sHat.N1 * basis.V) -
    thresholdedPenroseInverse threshold (sHat.M0 * basis.V) * (sHat.N0 * basis.V)

/-- The complex resolvent appearing in the Kato/Riesz contour projector.     For [the supplied parameters](hyp:D,z), [the defined object](goal) is given by [its defining clause](step:1). -/
noncomputable def matrixResolvent {k : ℕ} (D : RectMatrix k k) (z : ℂ) :
    Matrix (Fin k) (Fin k) ℂ :=
  (z • (1 : Matrix (Fin k) (Fin k) ℂ) - complexifyMatrix D)⁻¹

/-- The Kato/Riesz contour integral of the resolvent of a real empirical operator.  Contours are
parametrized on `[0,1]`; certification that they close and avoid the spectrum is carried by
`RepairHandle`.        For [the supplied parameters](hyp:D,contour), [the defined object](goal) is given by [its defining clause](step:1). -/
noncomputable def rieszContourProjector {k : ℕ} (D : RectMatrix k k)
    (contour : ℝ → ℂ) : Matrix (Fin k) (Fin k) ℂ := fun a b =>
  (2 * Real.pi * Complex.I)⁻¹ *
    ∫ t in Set.Icc (0 : ℝ) 1, (matrixResolvent D (contour t)) a b * deriv contour t

/-- The winding index used to tie the certified interior to its contour.     For [the supplied parameters](hyp:contour,z), [the defined object](goal) is given by [its defining clause](step:1). -/
noncomputable def contourWindingIndex (contour : ℝ → ℂ) (z : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    ∫ t in Set.Icc (0 : ℝ) 1, (contour t - z)⁻¹ * deriv contour t

/-- One empirical-summary carrier generated from the observed product law of `P`.  Both its law
and its summary are pinned, so neither can be chosen independently of the common DGP.        It uses [the supplied parameters](hyp:P). -/
structure PGeneratedEmpiricalSummary {k dx dz n : ℕ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P] where
  carrierLaw : Measure (Fin n → Obs dx dz)
  carrierLaw_eq : carrierLaw = sampleLaw (n := n) P
  sample : Fin n → Obs dx dz
  summary : SummarySpace dx dz
  summary_eq : summary = empSummary sample

/-- Total empirical spectral mass carried by the eigenvalues enclosed by one cluster contour.     For [the supplied parameters](hyp:location,mass,interior), [the defined object](goal) is given by [its defining clause](step:1). -/
noncomputable def enclosedSpectralMass {k : ℕ} (location : Fin k → ℂ)
    (mass : Fin k → ℝ) (interior : Set ℂ) : ℂ := by
  classical
  exact ∑ r, if location r ∈ interior then (mass r : ℂ) else 0

/-- A positive finite-atomic law is a moment-cone projection of one specified moment vector when
it is valid and minimizes the fixed finite-moment discrepancy among valid laws.  This relation is
used only at the realized empirical summary; it does not choose projections for other inputs. -/
def IsPositiveMomentConeProjection {k : ℕ} {radius : ℝ}
    (m : Fin (2 * k) → ℝ) (projected : AtomicLaw k radius) : Prop :=
  AtomicLaw.Valid projected ∧
    ∀ candidate : AtomicLaw k radius, AtomicLaw.Valid candidate →
      momentDiscrepancy m projected ≤ momentDiscrepancy m candidate

/-- A cluster-level constructive repair certificate indexed by one data-generating probability
law, its model witness, one sample from its observed product carrier, and the corresponding
population signal basis.  No population operator, target law, empirical summary, or basis floats
free: all clauses refer definitionally to this single package.

The cluster projectors are Kato/Riesz projectors of the empirical compressed operator around the
connected components of overlapping Bauer--Fike discs.  The last field certifies projection of
this realized empirical spectral-moment vector onto the positive finite-atomic moment cone; it
does not require a total selector on arbitrary moment vectors.        It uses [the supplied parameters](hyp:k,dx,dz,n,L,pi0,sigma0,P,hModel). -/
structure RepairHandle (k dx dz n : ℕ) (L pi0 sigma0 : ℝ)
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hModel : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (data : PGeneratedEmpiricalSummary (n := n) P) (basis : SignalBasis dx k)
    (hBasis : basis.SpansSignal (obsSummary P)) where
  diagonalizer : RectMatrix k k
  population_diagonalization :
    compressedOperator (obsSummary P) basis hBasis = diagonalizer⁻¹ *
      Matrix.diagonal (latentEffect P) * diagonalizer
  conditionNumber : ℝ
  conditionNumber_eq :
    conditionNumber = ‖matrixCLM diagonalizer‖ * ‖matrixCLM diagonalizer⁻¹‖
  localizationRadius : ℝ
  localizationRadius_eq : localizationRadius = conditionNumber *
    ‖matrixCLM
      (repairEmpiricalCompressedOperator (pi0 := pi0) (sigma0 := sigma0) data.sample basis -
        compressedOperator (obsSummary P) basis hBasis)‖
  spectralDisc : Fin k → Set ℂ
  spectralDisc_eq : ∀ i,
    spectralDisc i = {z | ‖z - (latentEffect P i : ℂ)‖ ≤ localizationRadius}
  sameCluster : Fin k → Fin k → Bool
  sameCluster_iff : ∀ i j, sameCluster i j = true ↔
    Relation.ReflTransGen (fun a b => (spectralDisc a ∩ spectralDisc b).Nonempty) i j
  bauerFike_localization : ∀ z,
    MatrixEigenvalue (repairEmpiricalCompressedOperator (pi0 := pi0) (sigma0 := sigma0)
      data.sample basis) z →
    ∃ i, z ∈ spectralDisc i
  contour : Fin k → ℝ → ℂ
  contour_closed : ∀ i, contour i 0 = contour i 1
  contour_differentiable : ∀ i t, t ∈ Set.Icc (0 : ℝ) 1 →
    DifferentiableAt ℝ (contour i) t
  contour_winding_integrable : ∀ i z,
    (∀ t ∈ Set.Icc (0 : ℝ) 1, contour i t ≠ z) →
      MeasureTheory.IntegrableOn
        (fun t => (contour i t - z)⁻¹ * deriv (contour i) t) (Set.Icc (0 : ℝ) 1)
  contour_avoids_empirical_spectrum : ∀ i t, t ∈ Set.Icc (0 : ℝ) 1 →
    ¬ MatrixEigenvalue (repairEmpiricalCompressedOperator (pi0 := pi0) (sigma0 := sigma0)
      data.sample basis) (contour i t)
  contourInterior : Fin k → Set ℂ
  contourInterior_eq : ∀ i,
    contourInterior i = {z | contourWindingIndex (contour i) z ≠ 0}
  cluster_discs_inside_contour : ∀ i j, sameCluster i j = true →
    spectralDisc j ⊆ contourInterior i
  other_discs_outside_contour : ∀ i j, sameCluster i j = false →
    Disjoint (spectralDisc j) (contourInterior i)
  enclosedEmpiricalSpectrum : Fin k → Set ℂ
  enclosedEmpiricalSpectrum_eq : ∀ i,
    enclosedEmpiricalSpectrum i =
      {z | MatrixEigenvalue (repairEmpiricalCompressedOperator (pi0 := pi0) (sigma0 := sigma0)
        data.sample basis) z ∧ z ∈ contourInterior i}
  aggregateProjector : Fin k → Matrix (Fin k) (Fin k) ℂ
  aggregateProjector_riesz_identity : ∀ i, aggregateProjector i =
    rieszContourProjector
      (repairEmpiricalCompressedOperator (pi0 := pi0) (sigma0 := sigma0) data.sample basis)
      (contour i)
  aggregateProjector_functional_calculus_inside : ∀ i z v,
    MatrixEigenvector
      (repairEmpiricalCompressedOperator (pi0 := pi0) (sigma0 := sigma0) data.sample basis) z v →
      z ∈ enclosedEmpiricalSpectrum i → Matrix.mulVec (aggregateProjector i) v = v
  aggregateProjector_functional_calculus_outside : ∀ i z v,
    MatrixEigenvector
      (repairEmpiricalCompressedOperator (pi0 := pi0) (sigma0 := sigma0) data.sample basis) z v →
      z ∉ enclosedEmpiricalSpectrum i → Matrix.mulVec (aggregateProjector i) v = 0
  empiricalSpectralLocation : Fin k → ℂ
  empiricalSpectralLocation_is_eigenvalue : ∀ r,
    MatrixEigenvalue
      (repairEmpiricalCompressedOperator (pi0 := pi0) (sigma0 := sigma0) data.sample basis)
      (empiricalSpectralLocation r)
  empiricalSpectralMass : Fin k → ℝ
  empiricalSpectralMass_nonneg : ∀ r, 0 ≤ empiricalSpectralMass r
  empiricalProjectorMass : Fin k → ℂ
  empiricalProjectorMass_eq : ∀ i, empiricalProjectorMass i =
    ∑ a, (leftAnchor data.summary basis a : ℂ) *
      (∑ b, aggregateProjector i a b * (rightAnchor basis b : ℂ))
  empiricalProjectorMass_spectral_sum : ∀ i,
    empiricalProjectorMass i = enclosedSpectralMass empiricalSpectralLocation
      empiricalSpectralMass (enclosedEmpiricalSpectrum i)
  populationClusterMass : Fin k → ℝ
  populationClusterMass_eq : ∀ i, populationClusterMass i =
    aggregateMass (quotientLawRaw P (effectRadius dz L sigma0))
      {z | ∃ j, sameCluster i j = true ∧ z = (latentEffect P j : ℂ)}
  clusterDiameter : Fin k → ℝ
  clusterDiameter_eq : ∀ i,
    clusterDiameter i = effectClusterDiameter (latentEffect P) sameCluster i
  clusterTransportPlan : Fin k → Fin k → Fin k → ℝ
  clusterTransportPlan_nonneg : ∀ i u r, 0 ≤ clusterTransportPlan i u r
  clusterTransport_source_marginal : ∀ i u,
    ∑ r, clusterTransportPlan i u r =
      if sameCluster i u = true then latentMass P u else 0
  clusterTransport_target_marginal_inside : ∀ i r,
    empiricalSpectralLocation r ∈ enclosedEmpiricalSpectrum i →
      ∑ u, clusterTransportPlan i u r = empiricalSpectralMass r
  clusterTransport_target_marginal_outside : ∀ i r,
    empiricalSpectralLocation r ∉ enclosedEmpiricalSpectrum i →
      ∑ u, clusterTransportPlan i u r = 0
  clusterTransport_support : ∀ i u r,
    0 < clusterTransportPlan i u r →
      sameCluster i u = true ∧
      empiricalSpectralLocation r ∈ enclosedEmpiricalSpectrum i ∧
      ‖empiricalSpectralLocation r - (latentEffect P u : ℂ)‖ ≤
        localizationRadius + effectClusterDiameter (latentEffect P) sameCluster i
  repairedLaw : AtomicLaw k (effectRadius dz L sigma0)
  repairedLaw_isProjection : IsPositiveMomentConeProjection
    (summarySpectralMoments
      (repairEmpiricalCompressedOperator (pi0 := pi0) (sigma0 := sigma0) data.sample basis)
      data.summary basis) repairedLaw

/-- For [the supplied parameters](hyp:h), [path Target Feature](goal) is given by [its defining clause](step:1). -/
noncomputable def pathTargetFeature (h : ℝ) : RectMatrix 2 2 := fun i u =>
  if i.val = 0 then 1 else if u.val = 0 then 1 / 5 else (12 / 25 - h / 5) / (3 / 5 - h)

/-- For [the supplied parameters](hyp:t), [path Arm Totals](goal) is given by [its defining clause](step:1). -/
noncomputable def pathArmTotals (t : Bool) : Fin 2 → ℝ := fun j =>
  if j.val = 0 then (if t then 13 / 25 else 12 / 25)
  else if t then 8 / 25 else 6 / 25

/-- For [the supplied parameters](hyp:t,h), [path Arm Weights](goal) is given by [its defining clause](step:1). -/
noncomputable def pathArmWeights (t : Bool) (h : ℝ) : Fin 2 → ℝ := fun u =>
  ∑ j, pathArmTotals t j * ((pathTargetFeature h).transpose)⁻¹ j u

-- @node: pathArmWeights_formula
/-- Path arm weights formula: under [the stated inputs and assumptions](hyp:t,h,u,hh), [the stated conclusion](goal) holds. -/
lemma pathArmWeights_formula (t : Bool) (h : ℝ) (u : Fin 2) (hh : |h| ≤ 1 / 100) :
    pathArmWeights t h u =
      if t then (if u.val = 0 then 4 / 25 + 3 * h / 5 else 9 / 25 - 3 * h / 5)
      else (if u.val = 0 then 6 / 25 + 2 * h / 5 else 6 / 25 - 2 * h / 5) := by
  have hne : 3 - h * 5 ≠ 0 := by
    intro heq
    have : h = 3 / 5 := by linarith
    rw [this] at hh
    norm_num at hh
  have hdet : -25 - h * (3 - h * 5)⁻¹ * 125 + (3 - h * 5)⁻¹ * 300 ≠ 0 := by
    intro heq
    field_simp [hne] at heq
    linarith
  fin_cases u <;> cases t <;>
    simp [pathArmWeights, pathArmTotals, pathTargetFeature, Matrix.inv_def,
      Matrix.det_fin_two, Matrix.adjugate_fin_two] <;>
    field_simp [hne, hdet] <;> ring

-- @node: pathTargetTransposeInverse_formula
/-- Path target transpose inverse formula: under [the stated inputs and assumptions](hyp:h,hh), [the stated conclusion](goal) holds. -/
lemma pathTargetTransposeInverse_formula (h : ℝ) (hh : |h| ≤ 1 / 100) :
    ((pathTargetFeature h).transpose)⁻¹ =
      !![4 / 3 - 5 * h / 9, 5 * h / 9 - 1 / 3;
         25 * h / 9 - 5 / 3, 5 / 3 - 25 * h / 9] := by
  have hne : 3 - h * 5 ≠ 0 := by
    intro heq
    have : h = 3 / 5 := by linarith
    rw [this] at hh
    norm_num at hh
  have hdet : -25 - h * (3 - h * 5)⁻¹ * 125 + (3 - h * 5)⁻¹ * 300 ≠ 0 := by
    intro heq
    field_simp [hne] at heq
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pathTargetFeature, Matrix.inv_def, Matrix.det_fin_two,
      Matrix.adjugate_fin_two] <;>
    field_simp [hne, hdet] <;> ring

/-- For [the supplied parameters](hyp:t), [base Reference Feature](goal) is given by [its defining clause](step:1). -/
noncomputable def baseReferenceFeature (t : Bool) : RectMatrix 2 2 := fun i u =>
  if i.val = 0 then 1
  else if t then (if u.val = 0 then 7 / 20 else 3 / 4)
  else if u.val = 0 then 3 / 10 else 7 / 10

/-- For [the supplied parameters](hyp:t), [path Joint Proxy Moment](goal) is given by [its defining clause](step:1). -/
noncomputable def pathJointProxyMoment (t : Bool) : RectMatrix 2 2 :=
  baseReferenceFeature t * Matrix.diagonal (pathArmWeights t 0) * (pathTargetFeature 0).transpose

/-- For [the supplied parameters](hyp:t,h), [path Reference Feature](goal) is given by [its defining clause](step:1). -/
noncomputable def pathReferenceFeature (t : Bool) (h : ℝ) : RectMatrix 2 2 :=
  pathJointProxyMoment t * ((pathTargetFeature h).transpose)⁻¹ *
    (Matrix.diagonal (pathArmWeights t h))⁻¹

-- @node: pathReferenceFeature_second_formula
/-- Path reference feature second formula: under [the stated inputs and assumptions](hyp:t,h,u,hh), [the stated conclusion](goal) holds. -/
lemma pathReferenceFeature_second_formula (t : Bool) (h : ℝ) (u : Fin 2)
    (hh : |h| ≤ 1 / 100) :
    pathReferenceFeature t h 1 u =
      if t then (if u.val = 0 then (225 * h + 28) / (20 * (15 * h + 4)) else 3 / 4)
      else (if u.val = 0 then (35 * h + 9) / (10 * (5 * h + 3)) else 7 / 10) := by
  have hne : 3 - h * 5 ≠ 0 := by
    intro heq
    have : h = 3 / 5 := by linarith
    rw [this] at hh
    norm_num at hh
  have h4 : 15 * h + 4 ≠ 0 := by
    intro heq
    have : h = -4 / 15 := by linarith
    rw [this] at hh
    norm_num at hh
  have h4' : 4 + h * 15 ≠ 0 := by nlinarith [abs_le.mp hh |>.1, abs_le.mp hh |>.2]
  have h3 : 5 * h + 3 ≠ 0 := by
    intro heq
    have : h = -3 / 5 := by linarith
    rw [this] at hh
    norm_num at hh
  have hbounds := abs_le.mp hh
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  change (pathJointProxyMoment t * ((pathTargetFeature h).transpose)⁻¹ *
    (Matrix.diagonal (pathArmWeights t h))⁻¹) (1 : Fin 2) u = _
  rw [pathTargetTransposeInverse_formula h hh]
  have hweights : pathArmWeights t h = fun u =>
      if t then (if u.val = 0 then 4 / 25 + 3 * h / 5 else 9 / 25 - 3 * h / 5)
      else (if u.val = 0 then 6 / 25 + 2 * h / 5 else 6 / 25 - 2 * h / 5) :=
    funext fun u => pathArmWeights_formula t h u hh
  have hweights0 : pathArmWeights t 0 = fun u =>
      if t then (if u.val = 0 then 4 / 25 else 9 / 25)
      else (if u.val = 0 then 6 / 25 else 6 / 25) := by
    funext u
    simpa using pathArmWeights_formula t 0 u (by norm_num : |(0 : ℝ)| ≤ 1 / 100)
  have hunit : IsUnit (fun u : Fin 2 =>
      if t then (if u.val = 0 then 4 / 25 + 3 * h / 5 else 9 / 25 - 3 * h / 5)
      else (if u.val = 0 then 6 / 25 + 2 * h / 5 else 6 / 25 - 2 * h / 5)) := by
    rw [Pi.isUnit_iff]
    intro u
    rw [isUnit_iff_ne_zero]
    fin_cases u <;> cases t <;> simp <;> nlinarith [hbounds.1, hbounds.2]
  have h30p : 30 + h * 50 ≠ 0 := by nlinarith [hbounds.1, hbounds.2]
  have h20p : 20 + h * 75 ≠ 0 := by nlinarith [hbounds.1, hbounds.2]
  have h30m : 30 - h * 50 ≠ 0 := by nlinarith [hbounds.1, hbounds.2]
  have h45m : 45 - h * 75 ≠ 0 := by nlinarith [hbounds.1, hbounds.2]
  have hw0f : 6 * 5 + 25 * h * 2 ≠ 0 := by nlinarith [hbounds.1, hbounds.2]
  have hw0t : 4 * 5 + 25 * 3 * h ≠ 0 := by nlinarith [hbounds.1, hbounds.2]
  have hw1f : 6 * 5 - 25 * h * 2 ≠ 0 := by nlinarith [hbounds.1, hbounds.2]
  have hw1t : 9 * 5 - 25 * 3 * h ≠ 0 := by nlinarith [hbounds.1, hbounds.2]
  rw [hweights]
  unfold pathJointProxyMoment
  rw [hweights0]
  rw [Matrix.inv_diagonal]
  fin_cases u <;> cases t <;>
    simp_all [baseReferenceFeature, pathTargetFeature, Matrix.mul_apply, Ring.inverse] <;>
    field_simp [h4, h4', h3, h30p, h20p, h30m, h45m, hw0f, hw0t, hw1f, hw1t] <;>
    norm_num <;> try field_simp [h4'] <;> ring

/-- For [the supplied parameters](hyp:u,t,x,z,y0,y1), [path Point](goal) is given by [its defining clause](step:1). -/
def pathPoint (u : Fin 2) (t x z y0 y1 : Bool) : FullData 2 2 2 :=
  witnessPoint u t x z y0 y1

/-- For [the supplied parameters](hyp:g,h,u,t,x,z,y0,y1), [path Weight](goal) is given by [its defining clause](step:1). -/
noncomputable def pathWeight (g h : ℝ) (u : Fin 2) (t x z y0 y1 : Bool) : ℝ :=
  let pu := if u.val = 0 then 2 / 5 + h else 3 / 5 - h
  let pt := pathArmWeights true h u / pu
  let px := pathTargetFeature h 1 u
  let pz := pathReferenceFeature t h 1 u
  let py0 := 1 / 4
  let py1 := if u.val = 0 then 1 / 2 - g / 2 else 1 / 2 + g / 2
  pu * bernoulliMass pt t * bernoulliMass px x * bernoulliMass pz z *
    bernoulliMass py0 y0 * bernoulliMass py1 y1

/-- Exact domain of the generic tangent amplitude used by the labelled path.     For [the supplied parameters](hyp:h), [the defined object](goal) is given by [its defining clause](step:1). -/
def TangentAmplitudeDomain (h : ℝ) : Prop :=
  h ∈ Set.Icc (-1 : ℝ) 1 -- @realizes \(h\)(h in [-1,1])

/-- The factorization-preserving Bernoulli path of equations (68)--(72).  Every theorem and
certificate using its second argument carries `TangentAmplitudeDomain`.        For [the supplied parameters](hyp:g,h), [the defined object](goal) is given by [its defining clause](step:1). -/
noncomputable def pathLaw (g h : ℝ) : Measure (FullData 2 2 2) :=
  ∑ u : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
    ENNReal.ofReal (pathWeight g h u t x z y0 y1) •
      Measure.dirac (pathPoint u t x z y0 y1)

/-- Path law is probability measure: under [the stated inputs and assumptions](hyp:g,h,hg0,hg1,hDomain,hh), [the stated conclusion](goal) holds. -/
lemma pathLaw_isProbabilityMeasure (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hDomain : TangentAmplitudeDomain h) (hh : |h| ≤ 1 / 100) :
    IsProbabilityMeasure (pathLaw g h) := by
  have hbounds := abs_le.mp hh
  have hpu : ∀ u : Fin 2,
      0 ≤ (if u.val = 0 then 2 / 5 + h else 3 / 5 - h : ℝ) ∧
      (if u.val = 0 then 2 / 5 + h else 3 / 5 - h : ℝ) ≤ 1 := by
    intro u
    fin_cases u <;> simp <;> constructor <;> nlinarith [hbounds.1, hbounds.2]
  have hpt : ∀ u : Fin 2,
      0 ≤ pathArmWeights true h u /
        (if u.val = 0 then 2 / 5 + h else 3 / 5 - h) ∧
      pathArmWeights true h u /
        (if u.val = 0 then 2 / 5 + h else 3 / 5 - h) ≤ 1 := by
    intro u
    rw [pathArmWeights_formula true h u hh]
    fin_cases u <;> simp
    all_goals constructor
    all_goals first
      | apply div_nonneg <;> nlinarith [hbounds.1, hbounds.2]
      | rw [div_le_one] <;> nlinarith [hbounds.1, hbounds.2]
  have hpx : ∀ u : Fin 2, 0 ≤ pathTargetFeature h 1 u ∧ pathTargetFeature h 1 u ≤ 1 := by
    intro u
    fin_cases u
    · norm_num [pathTargetFeature]
    · simp [pathTargetFeature]
      constructor
      · apply div_nonneg <;> nlinarith [hbounds.1, hbounds.2]
      · rw [div_le_one] <;> nlinarith [hbounds.1, hbounds.2]
  have hpz : ∀ (t : Bool) (u : Fin 2),
      0 ≤ pathReferenceFeature t h 1 u ∧ pathReferenceFeature t h 1 u ≤ 1 := by
    intro t u
    rw [pathReferenceFeature_second_formula t h u hh]
    fin_cases u <;> cases t <;> simp
    all_goals constructor
    all_goals first
      | apply div_nonneg <;> nlinarith [hbounds.1, hbounds.2]
      | rw [div_le_one] <;> nlinarith [hbounds.1, hbounds.2]
  have hpy1 : ∀ u : Fin 2,
      0 ≤ (if u.val = 0 then 1 / 2 - g / 2 else 1 / 2 + g / 2 : ℝ) ∧
      (if u.val = 0 then 1 / 2 - g / 2 else 1 / 2 + g / 2 : ℝ) ≤ 1 := by
    intro u
    fin_cases u <;> simp <;> constructor <;> nlinarith
  have hw : ∀ (u : Fin 2) (t x z y0 y1 : Bool),
      0 ≤ pathWeight g h u t x z y0 y1 := by
    intro u t x z y0 y1
    unfold pathWeight
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (hpu u).1
              (bernoulliMass_nonneg _ t (hpt u).1 (hpt u).2))
            (bernoulliMass_nonneg _ x (hpx u).1 (hpx u).2))
          (bernoulliMass_nonneg _ z (hpz t u).1 (hpz t u).2))
        (bernoulliMass_nonneg (1 / 4) y0 (by norm_num) (by norm_num)))
      (bernoulliMass_nonneg _ y1 (hpy1 u).1 (hpy1 u).2)
  constructor
  rw [show (pathLaw g h) Set.univ =
      ∑ u : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        ENNReal.ofReal (pathWeight g h u t x z y0 y1) by simp [pathLaw]]
  calc
    _ = ENNReal.ofReal (∑ u : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool,
        ∑ y0 : Bool, ∑ y1 : Bool, pathWeight g h u t x z y0 y1) := by
      symm
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro u _
        rw [ENNReal.ofReal_sum_of_nonneg]
        · apply Finset.sum_congr rfl
          intro t _
          rw [ENNReal.ofReal_sum_of_nonneg]
          · apply Finset.sum_congr rfl
            intro x _
            rw [ENNReal.ofReal_sum_of_nonneg]
            · apply Finset.sum_congr rfl
              intro z _
              rw [ENNReal.ofReal_sum_of_nonneg]
              · apply Finset.sum_congr rfl
                intro y0 _
                rw [ENNReal.ofReal_sum_of_nonneg]
                exact fun y1 _ => hw u t x z y0 y1
              · exact fun y0 _ => Finset.sum_nonneg fun y1 _ => hw u t x z y0 y1
            · exact fun z _ => Finset.sum_nonneg fun y0 _ =>
                Finset.sum_nonneg fun y1 _ => hw u t x z y0 y1
          · exact fun x _ => Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun y0 _ =>
              Finset.sum_nonneg fun y1 _ => hw u t x z y0 y1
        · exact fun t _ => Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun z _ =>
            Finset.sum_nonneg fun y0 _ => Finset.sum_nonneg fun y1 _ => hw u t x z y0 y1
      · exact fun u _ => Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun x _ =>
          Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun y0 _ =>
            Finset.sum_nonneg fun y1 _ => hw u t x z y0 y1
    _ = 1 := by
      simp only [pathWeight, sum_mul_bernoulliMass]
      rw [Fin.sum_univ_two]
      simp
      ring

/-- A labelled-path certificate for the explicit rational Bernoulli factorization used by the
converse.  The first four equalities tie every supplied path component to `pathLaw` and its proxy
and weight primitives, so the remaining factorization, displacement, and score fields cannot be
realized by an unrelated family of full-data laws.  The coordinatewise derivative clause records
the score-cancellation equations for `Aₜ(h) diag(wₜ(h)) B(h)ᵀ`. -/
structure FactorizationPathHandle where
  path : ℝ → ℝ → Measure (FullData 2 2 2)
  referenceFeaturePath : Bool → ℝ → RectMatrix 2 2
  targetFeaturePath : ℝ → RectMatrix 2 2
  armWeightsPath : Bool → ℝ → Fin 2 → ℝ
  path_eq_explicit : ∀ g h, path g h = pathLaw g h
  referenceFeaturePath_eq_explicit : ∀ t h,
    referenceFeaturePath t h = pathReferenceFeature t h
  targetFeaturePath_eq_explicit : ∀ h, targetFeaturePath h = pathTargetFeature h
  armWeightsPath_eq_explicit : ∀ t h, armWeightsPath t h = pathArmWeights t h
  basePath : ∀ g, 0 ≤ g → g ≤ 1 / 4 → path g 0 = witnessLaw (g / 2)
  pathFactorization : ∀ g h, TangentAmplitudeDomain h →
    0 ≤ g → g ≤ 1 / 4 → |h| ≤ 1 / 100 →
    ∃ hP : IsProbabilityMeasure (path g h),
      letI := hP
      ReferenceProxySeparation (path g h) ∧
      TargetProxySeparation (path g h) ∧
      ∀ t : Bool,
        observedProxyMoment (obsSummary (path g h)) t =
          referenceFeaturePath t h * Matrix.diagonal (armWeightsPath t h) *
            (targetFeaturePath h).transpose
  proxyMomentPreserved : ∀ t g h, TangentAmplitudeDomain h →
    0 ≤ g → g ≤ 1 / 4 → |h| ≤ 1 / 100 →
    referenceFeaturePath t h * Matrix.diagonal (armWeightsPath t h) *
        (targetFeaturePath h).transpose =
      referenceFeaturePath t 0 * Matrix.diagonal (armWeightsPath t 0) *
        (targetFeaturePath 0).transpose
  proxyMomentDerivativeCancellation : ∀ t i j,
    deriv (fun h =>
      (referenceFeaturePath t h * Matrix.diagonal (armWeightsPath t h) *
        (targetFeaturePath h).transpose) i j) 0 = 0
  observedScore : ℝ → ℝ → Obs 2 2 → ℝ
  observedScore_eq : ∀ g h o,
    observedScore g h o =
      (path g h).real (obsMap ⁻¹' ({o} : Set (Obs 2 2))) -
        (path g 0).real (obsMap ⁻¹' ({o} : Set (Obs 2 2)))
  observedScore_order : ∃ Cscore : ℝ, 0 < Cscore ∧ ∀ g h o,
    TangentAmplitudeDomain h → |h| ≤ 1 / 100 →
      |observedScore g h o| ≤ Cscore * |g * h|
  weightDisplacement : ∀ g h, TangentAmplitudeDomain h →
    0 ≤ g → g ≤ 1 / 4 → |h| ≤ 1 / 100 →
    ∃ hP : IsProbabilityMeasure (path g h),
      letI := hP
      latentMass (path g h) 0 = 2 / 5 + h ∧ latentMass (path g h) 1 = 3 / 5 - h

/-- The open constructive object requested by the note.  It does not assert existence of a repair
algorithm or prove a headline theorem: an inhabitant must supply both the empirical contour/moment
certificate tied to `P` and `sample`, and the separate factorization-preserving labelled path
certificate.        For [the supplied parameters](hyp:P,hModel,pi0,sigma0), [the defined object](goal) is given by [its defining clause](step:1). -/
-- @node: def:constructive-repair-handle
def repairHandle {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hModel : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (data : PGeneratedEmpiricalSummary (n := n) P) (basis : SignalBasis dx k)
    (hBasis : basis.SpansSignal (obsSummary P)) : Type :=
  RepairHandle k dx dz n L pi0 sigma0 P hModel data basis hBasis × FactorizationPathHandle

/-- Calibrated positive path displacement. @realizes \(h(n,g)\)(a min(1,(sqrt n g)^-1))     For [the supplied parameters](hyp:a,n,g), [the defined object](goal) is given by [its defining clause](step:1). -/
noncomputable def calibratedDisplacement (a : ℝ) (n : ℕ) (g : ℝ) : ℝ :=
  a * min 1 (Real.sqrt n * g)⁻¹

/-- Calibrated displacement mem: under [the stated inputs and assumptions](hyp:a,n,g,ha,haMax,hn,hg), [the stated conclusion](goal) holds. -/
lemma calibratedDisplacement_mem (a : ℝ) (n : ℕ) (g : ℝ)
    (ha : 0 < a) (haMax : a ≤ 1 / 8) (hn : 0 < n) (hg : 0 < g) :
    0 < calibratedDisplacement a n g ∧ calibratedDisplacement a n g ≤ a := by
  unfold calibratedDisplacement
  constructor
  · positivity
  · have hmin : min 1 (Real.sqrt ↑n * g)⁻¹ ≤ 1 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_left hmin (le_of_lt ha)]
  -- @realizes \(h(n,g)\)(positive and at most a)

/-- Range of the universal local-experiment radius.     For [the supplied parameters](hyp:cLoc), [the defined object](goal) is given by [its defining clause](step:1). -/
def LocalRadiusDomain (cLoc : ℝ) : Prop :=
  0 < cLoc ∧ cLoc < 1 -- @realizes \(c_{\mathrm{loc}}\)(cLoc in (0,1))

-- @env: S5
-- @realizes \(c_{\mathrm{loc}}\)(local KL radius constant)
-- @realizes \(\mathcal V_n^\nu\)(generic comparator law class)
-- @realizes \(\mathcal V_{n,g}^{p}\)(generic separated comparator class)
variable {cLoc : ℝ}

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

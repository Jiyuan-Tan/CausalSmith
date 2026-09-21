module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.ChebyshevCalibration
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Causalean.Stat.UStatistic.OrderM.Basic

/-! The finite mixed-information hybrid estimator and its calibration data. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open ProbabilityTheory
open scoped BigOperators

/-- Explicit factorial-moment constant.  [the stated conclusion](goal). -/
def starA : Nat := 7056

/-- Degree calibration constant.  [the stated conclusion](goal). -/
noncomputable def cCirc : Real := 1 / 256

/-- Least dyadic index whose inverse power is below the overlap constant.  [the stated conditions](hyp:eps) [the stated conclusion](goal). -/
noncomputable def dyadicIndex (eps : Real) : Nat :=
  sInf {j : Nat | 1 ≤ j ∧ (2 : Real) ^ (-(j : Int)) ≤ eps}

/-- Dyadic lower approximation to the overlap constant.  [the stated conditions](hyp:eps) [the stated conclusion](goal). -/
noncomputable def barEps (eps : Real) : Real :=
  (2 : Real) ^ (-(dyadicIndex eps : Int))

/-- Least integer satisfying the four numerical inequalities in (C1).  [the stated conditions](hyp:eps) [the stated conclusion](goal). -/
noncomputable def Hconst (eps : Real) : Nat :=
  sInf {H : Nat | 4 ≤ H ∧
    15 + 24 / cCirc ≤ (H : Real) / 4 ∧
    672 ≤ (H : Real) * cCirc * barEps eps ∧
    24 ≤ (H : Real) * cCirc * barEps eps}

/-- Deterministic labeled/auxiliary block sizes from (C2). -/
structure BlockSizes where
  M0 : Nat
  np : Nat
  nf : Nat
  mp : Nat
  mf : Nat

/-- The ordered split sizes used by the estimator.  [the stated conditions](hyp:n,m) [the stated conclusion](goal). -/
def blockSizes (n m : Nat) : BlockSizes :=
  let M0 := n / 3
  let np := (n - M0) / 2
  { M0 := M0, np := np, nf := n - M0 - np, mp := m / 2, mf := m - m / 2 }

/-- Binary length `1+clog₂ n`.  [the stated conditions](hyp:n) [the stated conclusion](goal). -/
def binLen (n : Nat) : Nat := 1 + Nat.clog 2 n

/-- Polynomial degree in (C3).  [the stated conditions](hyp:n) [the stated conclusion](goal). -/
noncomputable def Ldeg (n : Nat) : Nat :=
  max 2 (Int.toNat ⌊cCirc * binLen n⌋)

/-- Pilot/factorial bandwidth in (C3).  [the stated conditions](hyp:n,m,eps) [the stated conclusion](goal). -/
noncomputable def Bscale (n m : Nat) (eps : Real) : Real :=
  let bs := blockSizes n m
  let tp : Real := (bs.np + bs.mp : Nat) / 8
  let t : Real := (bs.nf + bs.mf : Nat) / 8
  Hconst eps * Ldeg n / min tp t

/-- Pilot heavy-cell threshold in (C3).  [the stated conditions](hyp:n,m,eps) [the stated conclusion](goal). -/
noncomputable def k0 (n m : Nat) (eps : Real) : Nat :=
  let bs := blockSizes n m
  Int.toNat ⌊((bs.np + bs.mp : Nat) / 8 : Real) * Bscale n m eps / 4⌋

/-- The exact finite conjunction (C4)--(C6).  [the stated conditions](hyp:n,m,eps) [the stated conclusion](goal). -/
noncomputable def calibrationPredicate (n m : Nat) (eps : Real) : Prop :=
  let bs := blockSizes n m
  let N : Nat := n + m
  let u : Real := bs.M0 / 8
  let tp : Real := (bs.np + bs.mp : Nat) / 8
  let t : Real := (bs.nf + bs.mf : Nat) / 8
  let L : Nat := Ldeg n
  let B := Bscale n m eps
  24 ≤ n ∧
  1 / 32 ≤ u / n ∧ u / n ≤ 1 / 24 ∧
  1 / 32 ≤ tp / N ∧ tp / N ≤ 3 / 32 ∧
  1 / 32 ≤ t / N ∧ t / N ≤ 3 / 32 ∧
  1 / 3 ≤ t / tp ∧ t / tp ≤ 3 ∧
  cCirc * binLen n / 2 ≤ L ∧
  8 ≤ tp * B ∧ (L : Real) ≤ t * B ∧
  (L : Real) ^ 4 * starA ^ (2 * L) ≤ n ∧
  (L : Real) ^ 6 * starA ^ (2 * L) ≤ n ∧
  15 * L + 12 * binLen n ≤ tp * B / 4 ∧
  (n : Real) ^ 12 ≤ (1 + barEps eps * t / tp) ^ k0 n m eps ∧
  12 * binLen n ≤ barEps eps * t * B
/-- [the stated conditions](hyp:n,m,eps) defines [the specified object](goal). -/

noncomputable instance (n m : Nat) (eps : Real) : Decidable (calibrationPredicate n m eps) :=
  Classical.propDecidable _

/-- Count complete records in a prefix of the block beginning at `offset`.  [the stated conditions](hyp:sample,offset,r,x,a,y) [the stated conclusion](goal). -/
def labeledBlockCount {n d : Nat} (sample : Fin n → Obs d) (offset r : Nat)
    (x : Fin d) (a y : Bool) : Nat :=
  ((Finset.univ.filter fun i =>
    offset ≤ i.1 ∧ i.1 < offset + r ∧ sample i = (x, a, y))).card

/-- Count auxiliary records in a prefix of the block beginning at `offset`.  [the stated conditions](hyp:sample,offset,r,x,a) [the stated conclusion](goal). -/
def auxiliaryBlockCount {m d : Nat} (sample : Fin m → AuxObs d) (offset r : Nat)
    (x : Fin d) (a : Bool) : Nat :=
  ((Finset.univ.filter fun i =>
    offset ≤ i.1 ∧ i.1 < offset + r ∧ sample i = (x, a))).card

/-- Arm count in a labeled block, summing over the binary outcome mark.  [the stated conditions](hyp:sample,offset,r,x,a) [the stated conclusion](goal). -/
def labeledArmBlockCount {n d : Nat} (sample : Fin n → Obs d) (offset r : Nat)
    (x : Fin d) (a : Bool) : Nat :=
  labeledBlockCount sample offset r x a false +
    labeledBlockCount sample offset r x a true

/-- Count one arm in a pooled block ordered as its labeled part followed by its
auxiliary part.  This makes pilot and factorial prefixes disjoint.  [the stated conditions](hyp:sample,labeledOffset,labeledSize,auxiliaryOffset,r,x,a) [the stated conclusion](goal). -/
def pooledArmCount {n m d : Nat} (sample : Sample n m d)
    (labeledOffset labeledSize auxiliaryOffset r : Nat)
    (x : Fin d) (a : Bool) : Nat :=
  labeledArmBlockCount sample.1 labeledOffset (min r labeledSize) x a +
    auxiliaryBlockCount sample.2 auxiliaryOffset (r - labeledSize) x a

/-- Clip a real number to `[-1,1]`.  [the stated conditions](hyp:z) [the stated conclusion](goal). -/
def clipUnit (z : Real) : Real := max (-1) (min 1 z)

/-- A finite valid-prefix output using separate outcome, pilot, and factorial pools.  [the stated conditions](hyp:eps,sample,r0,rp,rf) [the stated conclusion](goal). -/
noncomputable def prefixOutput {n m d : Nat} (eps : Real)
    (sample : Sample n m d) (r0 rp rf : Nat) : Real :=
  let bs := blockSizes n m
  let u : Real := bs.M0 / 8
  let t : Real := (bs.nf + bs.mf : Nat) / 8
  clipUnit <| ∑ x : Fin d,
    let j0 := pooledArmCount sample bs.M0 bs.np 0 rp x false
    let j1 := pooledArmCount sample bs.M0 bs.np 0 rp x true
    let jx := j0 + j1
    let s1 : Real := labeledBlockCount sample.1 0 r0 x true true
    let s0 : Real := labeledBlockCount sample.1 0 r0 x false true
    let k1 := pooledArmCount sample (bs.M0 + bs.np) bs.nf bs.mp rf x true
    let k0' := pooledArmCount sample (bs.M0 + bs.np) bs.nf bs.mp rf x false
    if jx ≤ k0 n m eps then
      s1 / u * factorialLift true (Ldeg n) (Bscale n m eps) t k0' k1 -
      s0 / u * factorialLift false (Ldeg n) (Bscale n m eps) t k0' k1
    else
      s1 / u * (k0' + k1 + 1 : Nat) / (k1 + 1 : Nat) -
      s0 / u * (k0' + k1 + 1 : Nat) / (k0' + 1 : Nat)

-- @node: def:mixed-estimator-handle
/-- Conditional finite Poisson-prefix average of the clipped mixed statistic.  [the stated conditions](hyp:n,m,d,eps) [the stated conclusion](goal). -/
noncomputable def mixedEstimator (n m d : Nat) (eps : Real) : Sample n m d → Real :=
  fun sample =>
    if calibrationPredicate n m eps then
      let bs := blockSizes n m
      let u : Real := bs.M0 / 8
      let tp : Real := (bs.np + bs.mp : Nat) / 8
      let t : Real := (bs.nf + bs.mf : Nat) / 8
      ∑ r0 ∈ Finset.range (bs.M0 + 1),
        ∑ rp ∈ Finset.range (bs.np + bs.mp + 1),
          ∑ rf ∈ Finset.range (bs.nf + bs.mf + 1),
            (poissonMeasure (Real.toNNReal u)).real {r0} *
              (poissonMeasure (Real.toNNReal tp)).real {rp} *
              (poissonMeasure (Real.toNNReal t)).real {rf} *
              prefixOutput eps sample r0 rp rf
    else 0
  -- @realizes \widehat\tau^{\mathrm{mix}}_{n,m,d}(finite conditional Poisson-prefix hybrid)
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma measurable_mixedEstimator (n m d : Nat) (eps : Real) :
    Measurable (mixedEstimator n m d eps) := by
  fun_prop

-- @node: poissonPrefixMass_le_one
/-- The retained mass of a finite Poisson prefix is at most one.  [the stated conclusion](goal). -/
lemma poissonPrefixMass_le_one (lam : NNReal) (N : Nat) :
    ∑ r ∈ Finset.range N, (poissonMeasure lam).real {r} ≤ 1 := by
  let mu := poissonMeasure lam
  change ∑ r ∈ Finset.range N, mu.real {r} ≤ 1
  simp only [MeasureTheory.measureReal_def]
  rw [← ENNReal.toReal_sum (fun r _ => MeasureTheory.measure_ne_top mu {r})]
  rw [MeasureTheory.sum_measure_singleton]
  change mu.real (↑(Finset.range N) : Set Nat) ≤ 1
  calc
    mu.real (↑(Finset.range N) : Set Nat) ≤ mu.real Set.univ :=
      MeasureTheory.measureReal_mono (Set.subset_univ _)
        (MeasureTheory.measure_ne_top mu _)
    _ = 1 := by simp [MeasureTheory.measureReal_def]

-- keep: public estimator range API explicitly promised by the F1 plan
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma mixedEstimator_mem_Icc_neg_one_one (n m d : Nat) (eps : Real)
    (z : Sample n m d) : mixedEstimator n m d eps z ∈ Set.Icc (-1 : Real) 1 := by
  by_cases hcal : calibrationPredicate n m eps
  · simp only [mixedEstimator, hcal, if_pos]
    let bs := blockSizes n m
    let u : Real := bs.M0 / 8
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    let t : Real := (bs.nf + bs.mf : Nat) / 8
    let w0 : Nat → Real := fun r => (poissonMeasure (Real.toNNReal u)).real {r}
    let wp : Nat → Real := fun r => (poissonMeasure (Real.toNNReal tp)).real {r}
    let wf : Nat → Real := fun r => (poissonMeasure (Real.toNNReal t)).real {r}
    have hw0 (r : Nat) : 0 ≤ w0 r := MeasureTheory.measureReal_nonneg
    have hwp (r : Nat) : 0 ≤ wp r := MeasureTheory.measureReal_nonneg
    have hwf (r : Nat) : 0 ≤ wf r := MeasureTheory.measureReal_nonneg
    have hout (r0 rp rf : Nat) :
        prefixOutput eps z r0 rp rf ∈ Set.Icc (-1 : Real) 1 := by
      dsimp [prefixOutput, clipUnit]
      constructor
      · exact le_max_left _ _
      · exact max_le (by norm_num) (min_le_left _ _)
    change (∑ r0 ∈ Finset.range (bs.M0 + 1),
      ∑ rp ∈ Finset.range (bs.np + bs.mp + 1),
      ∑ rf ∈ Finset.range (bs.nf + bs.mf + 1),
        w0 r0 * wp rp * wf rf * prefixOutput eps z r0 rp rf) ∈
          Set.Icc (-1 : Real) 1
    have hmass0 : ∑ r0 ∈ Finset.range (bs.M0 + 1), w0 r0 ≤ 1 :=
      poissonPrefixMass_le_one _ _
    have hmassp : ∑ rp ∈ Finset.range (bs.np + bs.mp + 1), wp rp ≤ 1 :=
      poissonPrefixMass_le_one _ _
    have hmassf : ∑ rf ∈ Finset.range (bs.nf + bs.mf + 1), wf rf ≤ 1 :=
      poissonPrefixMass_le_one _ _
    have hweight_eq :
        (∑ r0 ∈ Finset.range (bs.M0 + 1),
          ∑ rp ∈ Finset.range (bs.np + bs.mp + 1),
          ∑ rf ∈ Finset.range (bs.nf + bs.mf + 1),
            w0 r0 * wp rp * wf rf * (1 : Real)) =
          (∑ r0 ∈ Finset.range (bs.M0 + 1), w0 r0) *
          (∑ rp ∈ Finset.range (bs.np + bs.mp + 1), wp rp) *
          (∑ rf ∈ Finset.range (bs.nf + bs.mf + 1), wf rf) := by
      symm
      calc
        (∑ r0 ∈ Finset.range (bs.M0 + 1), w0 r0) *
            (∑ rp ∈ Finset.range (bs.np + bs.mp + 1), wp rp) *
            (∑ rf ∈ Finset.range (bs.nf + bs.mf + 1), wf rf) =
          (∑ r0 ∈ Finset.range (bs.M0 + 1), w0 r0) *
            ((∑ rp ∈ Finset.range (bs.np + bs.mp + 1), wp rp) *
              (∑ rf ∈ Finset.range (bs.nf + bs.mf + 1), wf rf)) := by ring
        _ = ∑ r0 ∈ Finset.range (bs.M0 + 1), w0 r0 *
            ((∑ rp ∈ Finset.range (bs.np + bs.mp + 1), wp rp) *
              (∑ rf ∈ Finset.range (bs.nf + bs.mf + 1), wf rf)) :=
          Finset.sum_mul _ _ _
        _ = ∑ r0 ∈ Finset.range (bs.M0 + 1),
            ∑ rp ∈ Finset.range (bs.np + bs.mp + 1),
              w0 r0 * (wp rp *
                (∑ rf ∈ Finset.range (bs.nf + bs.mf + 1), wf rf)) := by
          apply Finset.sum_congr rfl
          intro r0 _
          rw [Finset.sum_mul, Finset.mul_sum]
        _ = ∑ r0 ∈ Finset.range (bs.M0 + 1),
            ∑ rp ∈ Finset.range (bs.np + bs.mp + 1),
            ∑ rf ∈ Finset.range (bs.nf + bs.mf + 1),
              w0 r0 * wp rp * wf rf * (1 : Real) := by
          apply Finset.sum_congr rfl
          intro r0 _
          apply Finset.sum_congr rfl
          intro rp _
          rw [Finset.mul_sum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro rf _
          ring
    have hweight_le :
        (∑ r0 ∈ Finset.range (bs.M0 + 1), w0 r0) *
          (∑ rp ∈ Finset.range (bs.np + bs.mp + 1), wp rp) *
          (∑ rf ∈ Finset.range (bs.nf + bs.mf + 1), wf rf) ≤ 1 := by
      have hs0 : 0 ≤ ∑ r0 ∈ Finset.range (bs.M0 + 1), w0 r0 :=
        Finset.sum_nonneg fun _ _ => hw0 _
      have hsp : 0 ≤ ∑ rp ∈ Finset.range (bs.np + bs.mp + 1), wp rp :=
        Finset.sum_nonneg fun _ _ => hwp _
      have hsf : 0 ≤ ∑ rf ∈ Finset.range (bs.nf + bs.mf + 1), wf rf :=
        Finset.sum_nonneg fun _ _ => hwf _
      calc
        (∑ r0 ∈ Finset.range (bs.M0 + 1), w0 r0) *
            (∑ rp ∈ Finset.range (bs.np + bs.mp + 1), wp rp) *
            (∑ rf ∈ Finset.range (bs.nf + bs.mf + 1), wf rf)
            ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by norm_num
    constructor
    · calc
        (-1 : Real) ≤ -((∑ r0 ∈ Finset.range (bs.M0 + 1), w0 r0) *
            (∑ rp ∈ Finset.range (bs.np + bs.mp + 1), wp rp) *
            (∑ rf ∈ Finset.range (bs.nf + bs.mf + 1), wf rf)) :=
          neg_le_neg hweight_le
        _ = ∑ r0 ∈ Finset.range (bs.M0 + 1),
            ∑ rp ∈ Finset.range (bs.np + bs.mp + 1),
            ∑ rf ∈ Finset.range (bs.nf + bs.mf + 1),
              w0 r0 * wp rp * wf rf * (-1 : Real) := by
          rw [← hweight_eq]
          simp only [mul_neg, mul_one, Finset.sum_neg_distrib]
        _ ≤ ∑ r0 ∈ Finset.range (bs.M0 + 1),
            ∑ rp ∈ Finset.range (bs.np + bs.mp + 1),
            ∑ rf ∈ Finset.range (bs.nf + bs.mf + 1),
              w0 r0 * wp rp * wf rf * prefixOutput eps z r0 rp rf := by
          gcongr
          exact (hout _ _ _).1
    · calc
        (∑ r0 ∈ Finset.range (bs.M0 + 1),
            ∑ rp ∈ Finset.range (bs.np + bs.mp + 1),
            ∑ rf ∈ Finset.range (bs.nf + bs.mf + 1),
              w0 r0 * wp rp * wf rf * prefixOutput eps z r0 rp rf)
            ≤ ∑ r0 ∈ Finset.range (bs.M0 + 1),
              ∑ rp ∈ Finset.range (bs.np + bs.mp + 1),
              ∑ rf ∈ Finset.range (bs.nf + bs.mf + 1),
                w0 r0 * wp rp * wf rf * (1 : Real) := by
          gcongr
          exact (hout _ _ _).2
        _ = (∑ r0 ∈ Finset.range (bs.M0 + 1), w0 r0) *
            (∑ rp ∈ Finset.range (bs.np + bs.mp + 1), wp rp) *
            (∑ rf ∈ Finset.range (bs.nf + bs.mf + 1), wf rf) := hweight_eq
        _ ≤ 1 := hweight_le
  · simp [mixedEstimator, hcal]

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

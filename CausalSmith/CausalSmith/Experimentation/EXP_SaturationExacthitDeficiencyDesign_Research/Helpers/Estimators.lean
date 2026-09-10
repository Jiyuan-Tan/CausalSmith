import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Basic
import Causalean.Experimentation.DesignBased.RatioLinearization
import Causalean.Experimentation.DesignBased.HT.Estimator
import Causalean.Experimentation.DesignBased.HT.Unbiased
import Causalean.Mathlib.Probability.StdNormalCDF

set_option linter.unusedVariables false
set_option linter.style.openClassical false

/-!
# Exact-hit estimators and tie-aware rank sets

All definitions act on continuum-valued records.  The design-based ratio module
is imported only for its real-algebra remainder bound.
-/

open scoped BigOperators
open Filter MeasureTheory Set

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section
open Classical

-- @env: S4
variable (O : Fin C → Record K n) (m : Fin K → ℕ)

/-- Realized assignment-cell count. -/
def cellCount (O : Fin C → Record K n) (z : Assignment n) : ℕ :=
  (Finset.univ.filter fun c => (O c).2.1 = z).card
-- @realizes N_z(sum_c 1{Z_c=z})

/-- Welfare computed from an observed outcome vector. -/
def recordWelfare (n : ℕ) (o : Record K n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j, o.2.2 j

/-- Every observed outcome coordinate lies in `[0,1]`. -/
def BoundedRecord (o : Record K n) : Prop := ∀ j, o.2.2 j ∈ Icc (0 : ℝ) 1

/-- Every record in an observed array is bounded. -/
def BoundedRecordArray (O : Fin C → Record K n) : Prop := ∀ c, BoundedRecord (O c)

-- @node: finsetAverage_mem_Icc
/-- An average of finitely many values in `[0,1]` again lies in `[0,1]`. -/
lemma finsetAverage_mem_Icc {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, f x ∈ Icc (0 : ℝ) 1) :
    (s.card : ℝ)⁻¹ * ∑ x ∈ s, f x ∈ Icc (0 : ℝ) 1 := by
  by_cases hs : s.Nonempty
  · have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hcard.le)
        (Finset.sum_nonneg fun x hx => (hf x hx).1)
    · rw [inv_mul_eq_div, div_le_iff₀ hcard]
      simpa using Finset.sum_le_sum fun x hx => (hf x hx).2
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

-- @node: recordWelfare_mem_Icc
/-- A bounded observed outcome vector has welfare in `[0,1]`. -/
lemma recordWelfare_mem_Icc (o : Record K n) (ho : BoundedRecord o) :
    recordWelfare n o ∈ Icc (0 : ℝ) 1 := by
  simpa [recordWelfare] using
    (finsetAverage_mem_Icc Finset.univ (fun j => o.2.2 j) (fun j _ => ho j))

/-- Assignment-cell mean, with fallback `1/2` on an empty cell. -/
def cellMean (O : Fin C → Record K n) (z : Assignment n) : ℝ :=
  if h : cellCount O z = 0 then 1 / 2 else
    (cellCount O z : ℝ)⁻¹ *
      ∑ c with (O c).2.1 = z, recordWelfare n (O c)
-- @realizes \overline W_z(cell mean; fallback 1/2 when N_z=0)

/-- Bounded records make every nonempty-cell mean and its fallback lie in `[0,1]`. -/
lemma cellMean_mem_Icc (O : Fin C → Record K n) (z : Assignment n)
    (hO : BoundedRecordArray O) : cellMean O z ∈ Icc (0 : ℝ) 1 := by
  by_cases h : cellCount O z = 0
  · simp [cellMean, h]
    norm_num
  · rw [cellMean, dif_neg h]
    apply finsetAverage_mem_Icc
    intro c hc
    exact recordWelfare_mem_Icc (O c) (hO c)
-- @realizes \overline W_z(range [0,1] under bounded records)

-- @node: def:calibrated-estimator
/-- Assignment-calibrated slice means, returned together with their active-face
restriction. -/
def calibratedEstimator (O : Fin C → Record K n) (m : Fin K → ℕ)
    (A : Finset (Fin K)) : (Fin K → ℝ) × ({k // k ∈ A} → ℝ) :=
  let full := fun k => (sliceCard n (m k) : ℝ)⁻¹ *
    ∑ z ∈ exactSlice n (m k), cellMean O z
  (full, fun k => full k.1)
-- @realizes \widetilde U_{C,k}(M_k⁻¹ sum_{z∈S_k} bar W_z)
-- @realizes \widetilde U_C(full K-vector)
-- @realizes \widetilde U_{C,A}(active restriction)

/-- Bounded records keep every calibrated slice average in `[0,1]`. -/
lemma calibratedEstimator_mem_Icc (O : Fin C → Record K n) (m : Fin K → ℕ)
    (A : Finset (Fin K)) (hO : BoundedRecordArray O) :
    ∀ k, (calibratedEstimator O m A).1 k ∈ Icc (0 : ℝ) 1 := by
  intro k
  simpa [calibratedEstimator, sliceCard] using
    (finsetAverage_mem_Icc (exactSlice n (m k)) (cellMean O)
      (fun z _ => cellMean_mem_Icc O z hO))
-- @realizes \widetilde U_{C,k}(range [0,1] under bounded records)

-- @node: def:raw-estimator
/-- Raw pooled exact-hit mean, with fallback `1/2` on no hit. -/
def rawPooledEstimator (O : Fin C → Record K n) (m : Fin K → ℕ) (k : Fin K) : ℝ :=
  let hits := Finset.univ.filter fun c => (O c).2.1 ∈ exactSlice n (m k)
  if hits.card = 0 then 1 / 2 else
    (hits.card : ℝ)⁻¹ * ∑ c ∈ hits, recordWelfare n (O c)
-- @realizes \widehat U^{\mathrm{raw}}_{C,k}(pooled-hit ratio with fallback)

/-- Bounded records keep the raw pooled estimator in `[0,1]`. -/
lemma rawPooledEstimator_mem_Icc (O : Fin C → Record K n) (m : Fin K → ℕ)
    (k : Fin K) (hO : BoundedRecordArray O) :
    rawPooledEstimator O m k ∈ Icc (0 : ℝ) 1 := by
  let hits := Finset.univ.filter fun c => (O c).2.1 ∈ exactSlice n (m k)
  by_cases h : hits.card = 0
  · simp [rawPooledEstimator, hits, h]
    norm_num
  · simpa [rawPooledEstimator, hits, h] using
      (finsetAverage_mem_Icc hits (fun c => recordWelfare n (O c))
        (fun c _ => recordWelfare_mem_Icc (O c) (hO c)))
-- @realizes \widehat U^{\mathrm{raw}}_{C,k}(range [0,1] under bounded records)

/-- Exact-slice target assignment mass. -/
def gammaMass (n : ℕ) (m : Fin K → ℕ) (k : Fin K) (z : Assignment n) : ℝ :=
  if z ∈ exactSlice n (m k) then (sliceCard n (m k) : ℝ)⁻¹ else 0
-- @realizes \gamma_k(M_k⁻¹ indicator{z∈S_k})

/-- Nominal Bernoulli assignment mass. -/
def betaMass (m : Fin K → ℕ) (k : Fin K) (z : Assignment n) : ℝ :=
  assignmentMass (saturation n m k) z
-- @realizes \beta_k(product Bernoulli mass)

/-- A well-formed menu makes every Bernoulli assignment mass interior. -/
lemma betaMass_mem_Ioo (m : Fin K → ℕ) (k : Fin K) (z : Assignment n)
    (hmenu : WellFormedMenu n K m) : betaMass m k z ∈ Ioo (0 : ℝ) 1 := by
  have hn4 : 4 ≤ n := hmenu.1
  have hm : ∀ i, 1 ≤ m i ∧ m i ≤ n - 1 := hmenu.2.2.2.1
  have hn : 0 < n := by omega
  have hmk_pos : 0 < m k := lt_of_lt_of_le Nat.zero_lt_one (hmenu.2.2.2.1 k).1
  have hmk_lt : m k < n := by have := (hm k).2; omega
  have hpi : saturation n m k ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (Nat.cast_pos.mpr hmk_pos) (Nat.cast_pos.mpr hn)
    · exact (div_lt_one (Nat.cast_pos.mpr hn)).2 (by exact_mod_cast hmk_lt)
  unfold betaMass assignmentMass
  constructor
  · apply Finset.prod_pos
    intro j hj
    split
    · exact hpi.1
    · linarith [hpi.2]
  · calc
      (∏ j, if z j then saturation n m k else 1 - saturation n m k) <
          ∏ _j : Fin n, (1 : ℝ) := by
        apply Finset.prod_lt_prod
        · intro j hj
          split
          · exact hpi.1
          · linarith [hpi.2]
        · intro j hj
          split
          · exact hpi.2.le
          · linarith [hpi.1]
        · let j : Fin n := ⟨0, hn⟩
          have hj : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
          refine ⟨j, hj, ?_⟩
          split
          · exact hpi.2
          · linarith [hpi.1]
      _ = 1 := by simp
-- @realizes \beta_k(range (0,1) under WellFormedMenu)

/-- Nominal-label exact-hit rate `eta_k = p_k B_kk`. -/
def nominalHitRate (n : ℕ) (p : Fin K → ℝ) (m : Fin K → ℕ) (k : Fin K) : ℝ :=
  p k * (hitMatrix n m p).1 k k
-- @realizes \eta_k(p_k B_kk)

/-- Nominal hit rates lie in `[0,1]` on the simplex and well-formed menu. -/
lemma nominalHitRate_mem_Icc (n : ℕ) (p : Fin K → ℝ) (m : Fin K → ℕ) (k : Fin K)
    (hmenu : WellFormedMenu n K m) (hp : (∀ l, 0 ≤ p l) ∧ ∑ l, p l = 1) :
    nominalHitRate n p m k ∈ Icc (0 : ℝ) 1 := by
  have hn4 : 4 ≤ n := hmenu.1
  have hK2 : 2 ≤ K := hmenu.2.1
  have hm : ∀ i, 1 ≤ m i ∧ m i ≤ n - 1 := hmenu.2.2.2.1
  letI : NeZero n := ⟨by omega⟩
  letI : NeZero K := ⟨by omega⟩
  let B := (hitMatrix n m p).1
  let q := (hitMatrix n m p).2
  have hq := (hitMatrix_rate_mem_Ioo n m p hmenu hp k)
  have hsat_nonneg : 0 ≤ saturation n m k := by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsat_le : saturation n m k ≤ 1 := by
    rw [saturation, div_le_one (by positivity)]
    exact_mod_cast (show m k ≤ n by have := (hm k).2; omega)
  have hB_nonneg : 0 ≤ B k k := by
    dsimp [B, hitMatrix]
    positivity
  have hterm_le : p k * B k k ≤ q k := by
    have hsum : p k * B k k ≤ ∑ l, p l * B k l :=
      Finset.single_le_sum (fun l _ => mul_nonneg (hp.1 l) (by
        dsimp [B, hitMatrix]
        have hs0 : 0 ≤ saturation n m l := by
          exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        have hs1 : saturation n m l ≤ 1 := by
          rw [saturation, div_le_one (by positivity)]
          exact_mod_cast (show m l ≤ n by have := (hm l).2; omega)
        positivity)) (Finset.mem_univ k)
    calc
      p k * B k k ≤ ∑ l, p l * B k l := hsum
      _ = q k := by simp [q, B, hitMatrix, mul_comm]
  constructor
  · simpa [nominalHitRate, B] using mul_nonneg (hp.1 k) hB_nonneg
  · calc
      nominalHitRate n p m k = p k * B k k := by rfl
      _ ≤ q k := hterm_le
      _ ≤ 1 := hq.2.le
-- @realizes \eta_k(range [0,1] under p∈Delta_K and WellFormedMenu)

-- @node: def:han-appendix-estimator
/-- Han--Owusu--Shin Appendix-B estimator and the efficient nominal-label
influence function. -/
def hosEstimator (P0 : Measure (Schedule n)) (O : Fin C → Record K n)
    (p : Fin K → ℝ) (m : Fin K → ℕ) :
    (Fin K → ℝ) × (Fin K → Record K n → ℝ) × (Fin K → Record K n → ℝ) :=
  let est := fun k => ((C : ℝ) * p k)⁻¹ * ∑ c,
    if (O c).1 = k then gammaMass n m k (O c).2.1 / betaMass m k (O c).2.1 *
      recordWelfare n (O c) else 0
  let hosInfluence := fun k o =>
    (nominalHitRate n p m k)⁻¹ *
      (if o.1 = k ∧ o.2.1 ∈ exactSlice n (m k) then recordWelfare n o else 0) -
        exactSliceWelfare P0 m k
  let nominalInfluence := fun k o => if o.1 = k ∧ o.2.1 ∈ exactSlice n (m k) then
    (nominalHitRate n p m k)⁻¹ * (recordWelfare n o - assignmentMean P0 o.2.1) else 0
  (est, hosInfluence, nominalInfluence)
-- @realizes \widehat U^{HOS}_{C,k}(Appendix-B HT estimator)
-- @realizes \phi_k^{nom}(nominal-label calibrated canonical gradient)
-- @realizes \phi_k^{HOS}(centered HOS influence coordinate)

/-- Assignment-cell calibrated estimator formed inside nominal label `k` only.
It is the regular estimator that attains the nominal-subexperiment bound. -/
def nominalCalibratedEstimator (O : Fin C → Record K n) (m : Fin K → ℕ)
    (k : Fin K) : ℝ :=
  (sliceCard n (m k) : ℝ)⁻¹ * ∑ z ∈ exactSlice n (m k),
    let hits := Finset.univ.filter fun c => (O c).1 = k ∧ (O c).2.1 = z
    if hits.card = 0 then 1 / 2 else
      (hits.card : ℝ)⁻¹ * ∑ c ∈ hits, recordWelfare n (O c)

/-- A sequence of record estimators is asymptotically linear with the displayed
influence function under the actual triangular product laws. -/
def RecordAsymptoticallyLinear
    (law : ∀ N, Measure (Fin N → Record K n))
    (estimator : ∀ N, (Fin N → Record K n) → ℝ)
    (target : ℝ) (influence : Record K n → ℝ) : Prop :=
  (∀ N, IsProbabilityMeasure (law N)) ∧
    (∀ N, AEMeasurable (estimator N) (law N)) ∧
    (∫ o, influence o ∂(law 1).map (fun O => O 0)) = 0 ∧
    Integrable (fun o => influence o ^ 2) ((law 1).map (fun O => O 0)) ∧
    ∀ tolerance > 0, Tendsto (fun N => (law N)
      {O | tolerance < |Real.sqrt N * (estimator N O - target) -
        (Real.sqrt N)⁻¹ * ∑ c, influence (O c)|}) atTop (nhds 0)

/-- Calibrated Bernoulli influence coordinate. -/
def bernoulliInfluence (m : Fin K → ℕ) (q : Fin K → ℝ)
    (mu : Assignment n → ℝ) (k : Fin K) (o : Record K n) : ℝ :=
  if o.2.1 ∈ exactSlice n (m k) then
    (q k)⁻¹ * (recordWelfare n o - mu o.2.1) else 0
-- @realizes \phi_k^B(q_k⁻¹ 1{Z∈S_k}(W-mu_Z))

/-- Raw-pooling influence coordinate. -/
def rawInfluence (m : Fin K → ℕ) (q U : Fin K → ℝ)
    (k : Fin K) (o : Record K n) : ℝ :=
  if o.2.1 ∈ exactSlice n (m k) then
    (q k)⁻¹ * (recordWelfare n o - U k) else 0
-- @realizes \psi_k(q_k⁻¹ 1{Z∈S_k}(W-U_k))

/-- Fixed-stratum CR influence coordinate. -/
def crInfluence (counts : Fin K → ℕ) (m : Fin K → ℕ)
    (mu : Assignment n → ℝ) (c : Fin C) (k : Fin K) (o : Record K n) : ℝ :=
  if o.1 = k then (C : ℝ) / counts k * (recordWelfare n o - mu o.2.1) else 0
-- @realizes \phi_{c,k}^{CR}((C/C_Ck)1{L=k}(W-mu_Z))

/-- Full empirical second-moment covariance of influence coordinates. -/
def empiricalCovariance (phi : Fin K → Record K n → ℝ)
    (O : Fin C → Record K n) : Fin K → Fin K → ℝ :=
  fun i j => (C : ℝ)⁻¹ * ∑ c, phi i (O c) * phi j (O c)
-- @realizes \widehat\Sigma_C^{(K)}(empirical second moment of calibrated scores)
-- @realizes \widehat\Sigma_{C,A}(active principal restriction)

/-- Lower tie-aware rank endpoint. -/
def lowerRank (U : Fin K → ℝ) (k : Fin K) : ℕ :=
  1 + (Finset.univ.filter fun j => j ≠ k ∧ U k < U j).card
-- @realizes r_k^-(U)(1 + number strictly above k)

/-- Upper tie-aware rank endpoint. -/
def upperRank (U : Fin K → ℝ) (k : Fin K) : ℕ :=
  K - (Finset.univ.filter fun j => j ≠ k ∧ U j < U k).card
-- @realizes r_k^+(U)(K - number strictly below k)

/-- A conservative pairwise-inversion rank set at a supplied max-t critical value. -/
def invertedRankSet (C : ℕ) (Uhat : Fin K → ℝ) (SigmaHat : Fin K → Fin K → ℝ)
    (critical : ℝ) (emptyCell : Bool) (k : Fin K) : Finset ℕ :=
  if emptyCell then Finset.Icc 1 K else
    let above := (Finset.univ.filter fun j => j ≠ k ∧
      critical * Real.sqrt (max 0 ((SigmaHat j j + SigmaHat k k - 2 * SigmaHat j k) / C)) <
        Uhat j - Uhat k).card
    let below := (Finset.univ.filter fun j => j ≠ k ∧
      critical * Real.sqrt (max 0 ((SigmaHat j j + SigmaHat k k - 2 * SigmaHat j k) / C)) <
        Uhat k - Uhat j).card
    Finset.Icc (1 + above) (K - below)

/-- Covariance-dependent simultaneous max-t critical value, represented as the
least threshold having Gaussian coverage at least `1-gamma`. -/
def simultaneousMaxTCritical (Sigma : Fin K → Fin K → ℝ) (gamma : ℝ) : ℝ :=
  sInf {c : ℝ | ∃ gaussianLaw : Measure (Fin K → ℝ), IsProbabilityMeasure gaussianLaw ∧
    (∀ t : Fin K → ℝ,
      ∫ x, Real.cos (∑ i, t i * x i) ∂gaussianLaw =
        Real.exp (-((∑ i, ∑ j, t i * Sigma i j * t j) / 2)) ∧
      ∫ x, Real.sin (∑ i, t i * x i) ∂gaussianLaw = 0) ∧
    ENNReal.ofReal (1 - gamma) ≤ gaussianLaw {x | ∀ i j, i ≠ j →
      |x i - x j| ≤ c * Real.sqrt (max 0 (Sigma i i + Sigma j j - 2 * Sigma i j))}}

-- @node: def:rank-target-and-set
/-- Population tie-aware rank targets and calibrated simultaneous confidence sets. -/
def rankTargetAndSet (C : ℕ) (U Uhat : Fin K → ℝ) (SigmaHat : Fin K → Fin K → ℝ)
    (gamma : ℝ) (emptyCell : Bool) :
    (Fin K → Finset ℕ) × (Fin K → Finset ℕ) :=
  (fun k => Finset.Icc (lowerRank U k) (upperRank U k),
    fun k => invertedRankSet C Uhat SigmaHat
      (simultaneousMaxTCritical SigmaHat gamma) emptyCell k)
-- @realizes \operatorname{Rank}_k(U)(Icc(r_k^-,r_k^+))
-- @realizes \mathcal R_{C,k}(\gamma)(simultaneous pairwise inversion; full fallback)

/-! ## Shared record-law asymptotic statement predicates -/

/-- Canonical-gradient representation on a specified observed-law tangent set. -/
def IsCanonicalGradient (Q : Measure (Record K n))
    (tangent : Set (Record K n → ℝ)) (derivative : (Record K n → ℝ) → ℝ)
    (phi : Record K n → ℝ) : Prop :=
  Integrable phi Q ∧ (∫ o, phi o ∂Q) = 0 ∧
    ∀ score ∈ tangent, derivative score = ∫ o, phi o * score o ∂Q

/-- Membership in the centered square-integrable observed-law space. -/
def InL2Zero (Q : Measure (Record K n)) (f : Record K n → ℝ) : Prop :=
  MemLp f 2 Q ∧ (∫ o, f o ∂Q) = 0

/-- Closure in the actual `L²(Q)` seminorm, rather than the pointwise
function-space topology. -/
def InL2Closure (Q : Measure (Record K n)) (tangent : Set (Record K n → ℝ))
    (f : Record K n → ℝ) : Prop :=
  InL2Zero Q f ∧ ∀ epsilon > 0, ∃ score ∈ tangent,
    InL2Zero Q score ∧ ∫ o, (f o - score o) ^ 2 ∂Q ≤ epsilon

/-- Quadratic-mean differentiability of a dominated observed-law path with
the displayed `L²` score. -/
def QuadraticMeanDifferentiablePath (Q0 : Measure (Record K n))
    (Q : ℝ → Measure (Record K n)) (score : Record K n → ℝ) : Prop :=
  (∀ t, Q t ≪ Q0) ∧
    (∀ t, AEMeasurable (fun o => ((Q t).rnDeriv Q0 o).toReal) Q0) ∧
    Tendsto (fun t => (t ^ 2)⁻¹ * ∫ o,
      (Real.sqrt (((Q t).rnDeriv Q0 o).toReal) - 1 - t / 2 * score o) ^ 2 ∂Q0)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0)

/-- A regular Bernoulli observed-law path with score equal to its log-density derivative. -/
def BernoulliRegularPath (P0 : Measure (Schedule n)) (p : Fin K → ℝ)
    (m : Fin K → ℕ) (path : ℝ → Measure (Schedule n))
    (score : Record K n → ℝ) : Prop :=
  path 0 = P0 ∧
    (∃ radius > 0, ∀ t, |t| < radius → WellFormedScheduleLaw (path t)) ∧
    InL2Zero (bernoulliObservedLaw P0 p m) score ∧
    QuadraticMeanDifferentiablePath (bernoulliObservedLaw P0 p m)
      (fun t => bernoulliObservedLaw (path t) p m) score

/-- Missing-event law of the nominal-label-`k` target-hit subexperiment.  It is
the unnormalised event restriction of the Bernoulli record law, so the event
mass `eta_k` remains in all `L²` inner products. -/
def nominalTargetHitLaw (P : Measure (Schedule n)) (p : Fin K → ℝ)
    (m : Fin K → ℕ) (k : Fin K) : Measure (Record K n) :=
  (bernoulliObservedLaw P p m).restrict
    {o | o.1 = k ∧ o.2.1 ∈ exactSlice n (m k)}

/-- Regular paths and scores are formed inside the nominal target-hit
subexperiment itself. -/
def NominalRegularPath (P0 : Measure (Schedule n)) (p : Fin K → ℝ)
    (m : Fin K → ℕ) (k : Fin K) (path : ℝ → Measure (Schedule n))
    (score : Record K n → ℝ) : Prop :=
  path 0 = P0 ∧
    (∃ radius > 0, ∀ t, |t| < radius → WellFormedScheduleLaw (path t)) ∧
    InL2Zero (nominalTargetHitLaw P0 p m k) score ∧
    QuadraticMeanDifferentiablePath (nominalTargetHitLaw P0 p m k)
      (fun t => nominalTargetHitLaw (path t) p m k) score

/-- Regularity links an influence function to all differentiable nominal paths,
rather than merely naming a bundled function. -/
def RegularNominalInfluence (P0 : Measure (Schedule n)) (p : Fin K → ℝ)
    (m : Fin K → ℕ) (k : Fin K) (influence : Record K n → ℝ) : Prop :=
  InL2Closure (nominalTargetHitLaw P0 p m k)
      {score | ∃ path, NominalRegularPath P0 p m k path score} influence ∧
    ∀ path score, NominalRegularPath P0 p m k path score →
      HasDerivAt (fun t => exactSliceWelfare (path t) m k)
        (∫ o, influence o * score o ∂(nominalTargetHitLaw P0 p m k)) 0

/-- Observable, assignment-cell-centered Bernoulli score using empirical hit rates. -/
def feasibleBernoulliInfluence (O : Fin C → Record K n) (m : Fin K → ℕ)
    (k : Fin K) (o : Record K n) : ℝ :=
  let hits := (Finset.univ.filter fun c => (O c).2.1 ∈ exactSlice n (m k)).card
  if hits = 0 then 0 else if o.2.1 ∈ exactSlice n (m k) then
    (C : ℝ) / hits * (recordWelfare n o - cellMean O o.2.1) else 0

/-- Pilot-computable fixed-stratum influence coordinate, with the empirical
assignment-cell centering used by the CR covariance estimator. -/
def feasibleCrInfluence (O : Fin C → Record K n) (counts : Fin K → ℕ)
    (m : Fin K → ℕ) (k : Fin K) (o : Record K n) : ℝ :=
  if o.1 = k then (C : ℝ) / counts k *
    (recordWelfare n o - cellMean O o.2.1) else 0

/-- Characteristic-function statement of the full Bernoulli calibrated-vector CLT. -/
def BernoulliCalibratedCLT (P : Measure (Schedule n)) (p : Fin K → ℝ)
    (m : Fin K → ℕ) (Sigma : Fin K → Fin K → ℝ) : Prop :=
  ∀ t : Fin K → ℝ,
    Tendsto (fun C => ∫ O : Fin C → Record K n,
      Real.cos (∑ k, t k * (Real.sqrt C *
        ((calibratedEstimator O m Finset.univ).1 k - exactSliceWelfare P m k)))
        ∂(Measure.pi fun _ : Fin C => bernoulliObservedLaw P p m)) atTop
      (nhds (Real.exp (-((∑ i, ∑ j, t i * Sigma i j * t j) / 2)))) ∧
    Tendsto (fun C => ∫ O : Fin C → Record K n,
      Real.sin (∑ k, t k * (Real.sqrt C *
        ((calibratedEstimator O m Finset.univ).1 k - exactSliceWelfare P m k)))
        ∂(Measure.pi fun _ : Fin C => bernoulliObservedLaw P p m)) atTop (nhds 0)

/-- Characteristic-function statement of the full fixed-count calibrated-vector CLT. -/
def CrCalibratedCLT (P : Measure (Schedule n)) (counts : ℕ → Fin K → ℕ)
    (m : Fin K → ℕ) (Sigma : Fin K → Fin K → ℝ) : Prop :=
  ∀ t : Fin K → ℝ,
    Tendsto (fun C => ∫ O : Fin C → Record K n,
      Real.cos (∑ k, t k * (Real.sqrt C *
        ((calibratedEstimator O m Finset.univ).1 k - exactSliceWelfare P m k)))
        ∂(crObservedLaw P (counts C) m)) atTop
      (nhds (Real.exp (-((∑ i, ∑ j, t i * Sigma i j * t j) / 2)))) ∧
    Tendsto (fun C => ∫ O : Fin C → Record K n,
      Real.sin (∑ k, t k * (Real.sqrt C *
        ((calibratedEstimator O m Finset.univ).1 k - exactSliceWelfare P m k)))
        ∂(crObservedLaw P (counts C) m)) atTop (nhds 0)

/-- Convergence in probability of a covariance statistic under Bernoulli records. -/
def BernoulliCovarianceConsistent (P : Measure (Schedule n)) (p : Fin K → ℝ)
    (m : Fin K → ℕ) (hatSigma : ∀ C, (Fin C → Record K n) → Fin K → Fin K → ℝ)
    (Sigma : Fin K → Fin K → ℝ) : Prop :=
  ∀ eps > 0, Tendsto (fun C => (Measure.pi fun _ : Fin C => bernoulliObservedLaw P p m)
    {O | ∃ i j, eps < |hatSigma C O i j - Sigma i j|}) atTop (nhds 0)

/-- Convergence in probability of a covariance statistic under fixed-count records. -/
def CrCovarianceConsistent (P : Measure (Schedule n)) (counts : ℕ → Fin K → ℕ)
    (m : Fin K → ℕ) (hatSigma : ∀ C, (Fin C → Record K n) → Fin K → Fin K → ℝ)
    (Sigma : Fin K → Fin K → ℝ) : Prop :=
  ∀ eps > 0, Tendsto (fun C => crObservedLaw P (counts C) m
    {O | ∃ i j, eps < |hatSigma C O i j - Sigma i j|}) atTop (nhds 0)

/-- Convergence in probability restricted to the active principal covariance block. -/
def CrActiveCovarianceConsistent (P : Measure (Schedule n))
    (counts : ℕ → Fin K → ℕ) (m : Fin K → ℕ) (A : Finset (Fin K))
    (hatSigma : ∀ C, (Fin C → Record K n) → Fin K → Fin K → ℝ)
    (Sigma : Fin K → Fin K → ℝ) : Prop :=
  ∀ eps > 0, Tendsto (fun C => crObservedLaw P (counts C) m
    {O | ∃ i ∈ A, ∃ j ∈ A, eps < |hatSigma C O i j - Sigma i j|}) atTop (nhds 0)

/-- Whether at least one required exact assignment cell is empty. -/
def hasEmptyTargetCell (O : Fin C → Record K n) (m : Fin K → ℕ) : Bool :=
  decide (∃ k z, z ∈ exactSlice n (m k) ∧ cellCount O z = 0)

/-- Simultaneous event that every population tie-aware rank set is contained in
its calibrated pairwise-inversion confidence set. -/
def rankCoverageEvent (P : Measure (Schedule n)) (m : Fin K → ℕ)
    (gamma : ℝ) (hatSigma : (Fin C → Record K n) → Fin K → Fin K → ℝ)
    (O : Fin C → Record K n) : Prop :=
  let U := exactSliceWelfare P m
  let Uhat := (calibratedEstimator O m Finset.univ).1
  let sets := rankTargetAndSet C U Uhat (hatSigma O) gamma (hasEmptyTargetCell O m)
  ∀ k, sets.1 k ⊆ sets.2 k

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

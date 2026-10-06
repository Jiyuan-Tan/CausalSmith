module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Estimator

/-! # Finite sign-mixture full-data construction -/

@[expose] public section
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

-- @env: S6
variable (cStar τ : ℝ)
/-- [The lower cells object](goal) is defined from [the supplied inputs](hyp:n). -/
noncomputable def lowerCells (n : ℕ) : ℕ :=
  Nat.ceil ((n : ℝ) ^ ((4 : ℝ) / 3))
  -- @realizes K_{\mathrm L}(ceil n^(4/3))
/-- [The bump object](goal) is defined from [the supplied inputs](hyp:t). -/
noncomputable def bump (t : ℝ) : ℝ := Real.sin (2 * Real.pi * t)
  -- @realizes B(sinusoidal bump on [0,1], bounded by one)
/-- [The lower height object](goal) is defined from [the supplied inputs](hyp:cStar,n). -/
noncomputable def lowerHeight (cStar : ℝ) (n : ℕ) : ℝ :=
  cStar * (lowerCells n : ℝ) ^ (-(1 / 8 : ℝ))
  -- @realizes h_n(cStar times lowerCells^(-1/8), lower-mixture amplitude)
/-- [The sign object](goal) is defined from [the supplied inputs](hyp:b). -/
def sign (b : Bool) : ℝ := if b then 1 else -1
  -- @realizes \lambda(sign value map on Bool vectors)
/-- [The tiled perturbation object](goal) is defined from [the supplied inputs](hyp:cStar,n,sgn,x). -/
noncomputable def tiledPerturbation (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (x : ℝ) : ℝ := by
  classical
  exact ∑ ℓ : Fin (lowerCells n),
    if x ∈ cell (lowerCells n) ℓ then
      lowerHeight cStar n * sign (sgn ℓ) *
        bump ((lowerCells n : ℝ) * x - ℓ.val)
    else 0
  -- @realizes u_{\lambda}(tiled perturbation)
/-- [The coupled perturbation object](goal) is defined from [the supplied inputs](hyp:cStar,n,sgn,x). -/
noncomputable def coupledPerturbation (cStar τ : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (x : ℝ) : ℝ :=
  τ * tiledPerturbation cStar n sgn x
  -- @realizes v_{\lambda,\tau}(tau times tiled bump)
/-- [The actual strength object](goal) is defined from [the supplied inputs](hyp:a,n). -/
noncomputable def actualStrength (a : ℝ) (n : ℕ) : ℝ :=
  max a ((n : ℝ) ^ (-(1 / 3 : ℝ)))
/-- [The lower admissible object](goal) is defined from [the supplied inputs](hyp:n,a,cStar). -/
def LowerAdmissible (n : ℕ) (a cStar : ℝ) : Prop :=
  0 < cStar ∧ -- @realizes h_n(positive amplitude) @realizes J_n(positive amplitude)
  lowerHeight cStar n ≤ 3 / 16 ∧ -- @realizes h_n(upper bound) @realizes J_n(upper bound)
  lowerHeight cStar n ^ 2 ≤
    actualStrength a n * (1 / 4 - lowerHeight cStar n ^ 2)
  -- @realizes \operatorname{Adm}_{n,a}(c_{\star})(exact lower-family domain)

/-- The standing lower-experiment domain combines positive sample size with the
paper's exact amplitude admissibility condition. Height and separation are
interpreted on this domain; their range properties are derived below.  For [the displayed assumptions and inputs](hyp:n,a,cStar), [the stated object is defined](goal). -/
def LowerExperimentDomain (n : ℕ) (a cStar : ℝ) : Prop :=
  0 < n ∧ -- @realizes h_n(n>0) @realizes J_n(n>0)
  LowerAdmissible n a cStar -- @realizes h_n(standing Adm) @realizes J_n(standing Adm)
/-- [The receipt base object](goal) is defined from [the supplied inputs](hyp:a,z). -/

noncomputable def receiptBase (a : ℝ) (z : Bool) : ℝ :=
  (1 + sign z * a) / 2 -- @realizes r_z^{(a)}(baseline receipt probability)
/-- [The receipt outcome cell object](goal) is defined from [the supplied inputs](hyp:a,z,d,_y). -/
noncomputable def receiptOutcomeCell (a : ℝ) (z d _y : Bool) : ℝ :=
  if d then receiptBase a z / 2 else (1 - receiptBase a z) / 2 -- @realizes R_z^{(a)}(receipt-outcome probability mass function)
/-- [The assignment weight object](goal) is defined from [the supplied inputs](hyp:u,z). -/
noncomputable def assignmentWeight (u : ℝ) (z : Bool) : ℝ :=
  if z then 1 / 2 + u else 1 / 2 - u -- @realizes e_z^{(\lambda)}(assignment mass composed with tiledPerturbation)

/-- The paper's strength domain makes the baseline receipt a probability.  Under [the displayed assumptions and inputs](hyp:a,ha,z), [the stated conclusion holds](goal). -/
-- @node: receiptBase_mem_Icc
lemma receiptBase_mem_Icc (a : ℝ) (ha : 0 < a ∧ a ≤ 1 / 4) (z : Bool) :
    receiptBase a z ∈ Icc (0 : ℝ) 1 := by -- @realizes r_z^{(a)}(domain (0,1/4] and range [0,1]) @realizes R_z^{(a)}(baseline probability domain)
  cases z <;> simp only [receiptBase, sign, Bool.false_eq_true,
    ↓reduceIte, Set.mem_Icc] <;> constructor <;> linarith [ha.1, ha.2]

/-- Each baseline receipt-outcome cell is nonnegative.  Under [the displayed assumptions and inputs](hyp:a,ha,z,d,y), [the stated conclusion holds](goal). -/
-- @node: receiptOutcomeCell_nonneg
lemma receiptOutcomeCell_nonneg (a : ℝ) (ha : 0 < a ∧ a ≤ 1 / 4)
    (z d y : Bool) :
    0 ≤ receiptOutcomeCell a z d y := by -- @realizes R_z^{(a)}(nonnegative masses on paper strength domain)
  have hb := receiptBase_mem_Icc a ha z
  cases d <;> simp only [receiptOutcomeCell, Bool.false_eq_true, ↓reduceIte]
  · exact div_nonneg (sub_nonneg.mpr hb.2) (by norm_num)
  · exact div_nonneg hb.1 (by norm_num)

/-- For each encouragement, the four baseline cells have total mass one.  Under [the displayed assumptions and inputs](hyp:a,ha,z), [the stated conclusion holds](goal). -/
-- @node: receiptOutcomeCell_sum_eq_one
lemma receiptOutcomeCell_sum_eq_one (a : ℝ) (ha : 0 < a ∧ a ≤ 1 / 4) (z : Bool) :
    (∑ d : Bool, ∑ y : Bool, receiptOutcomeCell a z d y) = 1 := by -- @realizes R_z^{(a)}(normalized probability mass function)
  simp only [Fintype.sum_bool, receiptOutcomeCell, Bool.false_eq_true, ↓reduceIte]
  ring
/-- Given [the supplied inputs](hyp:u,hu,z), [the stated result about assignment weight mem icc holds](goal). -/

lemma assignmentWeight_mem_Icc (u : ℝ)
    (hu : u ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) (z : Bool) :
    assignmentWeight u z ∈ Icc (0 : ℝ) 1 := by -- @realizes e_z^{(\lambda)}(range [0,1] for |u|≤1/2)
  rcases hu with ⟨hlo, hhi⟩
  cases z <;> simp [assignmentWeight, Set.mem_Icc] <;>
    constructor <;> linarith
/-- [The complier margin object](goal) is defined from [the supplied inputs](hyp:a,u,v,d,y). -/
noncomputable def complierMargin (a u v : ℝ) (d y : Bool) : ℝ :=
  if d then a / 2 - sign y * u * v / (2 * (1 / 4 - u ^ 2))
  else a / 2 + sign y * u * v / (2 * (1 / 4 - u ^ 2))
/-- [The primitive mass object](goal) is defined from [the supplied inputs](hyp:a,u,v,d0,d1,y0,y1). -/

noncomputable def primitiveMass (a u v : ℝ)
    (d0 d1 y0 y1 : Bool) : ℝ :=
  if !d0 && d1 then
    complierMargin a u v false y0 * complierMargin a u v true y1 / a
  else if d0 && d1 && !y0 then
    receiptBase a false / 2 + v * sign y1 / (4 * assignmentWeight u false)
  else if !d0 && !d1 && !y1 then
    (1 - receiptBase a true) / 2 +
      v * sign y0 / (4 * assignmentWeight u true)
  else 0
/-- [The primitive kernel object](goal) is defined from [the supplied inputs](hyp:s,x,mass). -/

noncomputable def primitiveKernel (s : Bool) (x : ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ) : Measure FullData :=
  ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
    ENNReal.ofReal (mass x d0 d1 y0 y1) •
      Measure.dirac (s, x, d0, d1, boolReal y0, boolReal y1)
/-- [The primitive population object](goal) is defined from [the supplied inputs](hyp:s,density,mass). -/

noncomputable def primitivePopulation (s : Bool) (density : ℝ → ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ) : Measure FullData :=
  ((volume.restrict covariateSpace).withDensity
    (fun x => ENNReal.ofReal (density x))).bind
    (fun x => primitiveKernel s x mass)
/-- [The assigned from object](goal) is defined from [the supplied inputs](hyp:e). -/

noncomputable def assignedFrom (μ : Measure FullData) (e : ℝ → ℝ) :
    Measure Assigned :=
  μ.bind (fun o =>
    ENNReal.ofReal (e (covariate o)) •
      Measure.dirac (o, true, potentialReceipt o true,
        potentialOutcome o (potentialReceipt o true)) +
    ENNReal.ofReal (1 - e (covariate o)) •
      Measure.dirac (o, false, potentialReceipt o false,
        potentialOutcome o (potentialReceipt o false)))
/-- [The arm mean from object](goal) is defined from [the supplied inputs](hyp:mass,A,z,x). -/

noncomputable def armMeanFrom (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    (A z : Bool) (x : ℝ) : ℝ :=
  ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
    mass x d0 d1 y0 y1 *
      (if A then boolReal (if (if z then d1 else d0) then y1 else y0)
       else boolReal (if z then d1 else d0))
/-- [The law from mass object](goal) is defined from [the supplied inputs](hyp:fS,fT,e,mass). -/

noncomputable def lawFromMass (fS fT e : ℝ → ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ) : TransportLaw :=
  let source := primitivePopulation true fS mass
  let target := primitivePopulation false fT mass
  let full := (1 / 2 : ℝ≥0∞) • source + (1 / 2 : ℝ≥0∞) • target
  let assigned := assignedFrom source e
  let observed := assigned.map observeSource
  let targetX := (ProbabilityTheory.cond full {o | population o = false}).map covariate
  { fullLaw := full
    assignedLaw := assigned
    sampleLaw := fun nS nT =>
      (Measure.pi (fun _ : Fin nS => observed)).prod
        (Measure.pi (fun _ : Fin nT => targetX))
    fS := fS
    fT := fT
    e := e
    m := armMeanFrom mass
    assignmentPotentialOutcome := fun z o =>
      potentialOutcome o (potentialReceipt o z) }
/-- [The lower mass object](goal) is defined from [the supplied inputs](hyp:a,n,cStar,sgn,x). -/

noncomputable def lowerMass (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool) (x : ℝ) :=
  primitiveMass (actualStrength a n)
    (tiledPerturbation cStar n sgn x)
    (coupledPerturbation cStar τ n sgn x)
/-- [The lower pointwise mean object](goal) is defined from [the supplied inputs](hyp:a,n,cStar,sgn,s,f,x). -/

noncomputable def lowerPointwiseMean (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool) (s : Bool)
    (f : FullData → ℝ) (x : ℝ) : ℝ :=
  ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
    lowerMass a n cStar τ sgn x d0 d1 y0 y1 *
      f (s, x, d0, d1, boolReal y0, boolReal y1)
/-- [The legal ivcomponent object](goal) is defined from [the supplied inputs](hyp:a,n,cStar,sgn). -/

noncomputable def legalIVComponent (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool) : TransportLaw :=
  lawFromMass (fun _ => 1)
    (fun x => 1 + tiledPerturbation cStar n sgn x)
    (fun x => 1 / 2 + tiledPerturbation cStar n sgn x)
    (lowerMass a n cStar τ sgn)
/-- [The mixture center object](goal) is defined from [the supplied inputs](hyp:a,n). -/

noncomputable def mixtureCenter (a : ℝ) (n : ℕ) : TransportLaw :=
  lawFromMass (fun _ => 1) (fun _ => 1) (fun _ => 1 / 2)
    (fun _ => primitiveMass (actualStrength a n) 0 0)
/-- [The lower mixture object](goal) is defined from [the supplied inputs](hyp:a,n,cStar). -/

noncomputable def lowerMixture (a : ℝ) (n : ℕ) (cStar τ : ℝ) :
    Measure (TwoSample n n) :=
  (1 / (2 ^ (lowerCells n) : ℝ≥0∞)) •
    ∑ sgn : Fin (lowerCells n) → Bool,
      dataLaw (legalIVComponent a n cStar τ sgn) n n

-- @node: def:legal-iv-mixture
/-- [The legal ivmixture object](goal) is defined from [the supplied inputs](hyp:a,n,cStar,_hn,_ha,_hDomain,_hcStar,sgn). -/
noncomputable def legalIVMixture (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (_hn : threshold ≤ n) (_ha : 0 < a ∧ a ≤ 1 / 4)
    (_hDomain : LowerExperimentDomain n a cStar) -- @realizes c_{\star}(positive amplitude via standing Adm)
    (_hcStar : cStar < 1) -- @realizes c_{\star}(standing upper bound; amplitude in (0,1))
    (_hτ : τ ∈ Icc (-1 : ℝ) 1)
    (sgn : Fin (lowerCells n) → Bool) :
    TransportLaw × Measure (TwoSample n n) × TransportLaw :=
  (legalIVComponent a n cStar τ sgn,
    lowerMixture a n cStar τ, mixtureCenter a n)
  -- @realizes Q_{\lambda,\tau}(component) @realizes M_{\tau}(uniform mixture)
  -- @realizes P_{\star}(unperturbed center)
  -- @realizes c_{\star}(amplitude on the exact Adm domain) @realizes \tau(index in [-1,1])
  -- @realizes \lambda(Bool sign vector on Fin (lowerCells n))
/-- [The separation object](goal) is defined from [the supplied inputs](hyp:cStar,n). -/

noncomputable def separation (cStar : ℝ) (n : ℕ) : ℝ :=
  let h := lowerHeight cStar n
  h ^ 2 * ∫ t in (0 : ℝ)..1,
    bump t ^ 2 / (1 / 4 - h ^ 2 * bump t ^ 2)
  -- @realizes J_n(height squared times the sinusoidal separation integral)

-- @node: lower_admissible_of_small_amplitude
/-- Given [the supplied inputs](hyp:n,a,cStar,hn,ha,hc), [the stated result about lower admissible of small amplitude holds](goal). -/
lemma lower_admissible_of_small_amplitude (n : ℕ) (a cStar : ℝ)
    (hn : threshold ≤ n) (ha : 0 < a ∧ a ≤ 1 / 4)
    (hc : 0 < cStar ∧ cStar ≤ 1 / 100) :
    LowerAdmissible n a cStar := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by have : 256 ≤ n := hn; omega)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hbase : (n : ℝ) ^ ((4 : ℝ) / 3) ≤ lowerCells n := by
    unfold lowerCells
    exact Nat.le_ceil _
  have hKpos : (0 : ℝ) < lowerCells n := by
    have := Real.one_le_rpow hn1 (by norm_num : (0 : ℝ) ≤ 4 / 3)
    linarith
  have hpow : (lowerCells n : ℝ) ^ (-(1 / 4 : ℝ)) ≤
      (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos hnpos _)
      hbase (by norm_num : (-(1 / 4 : ℝ)) ≤ 0)
    rw [← Real.rpow_mul hnpos.le] at h
    convert h using 1 <;> congr 1 <;> ring
  have hsq : lowerHeight cStar n ^ 2 =
      cStar ^ 2 * (lowerCells n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    unfold lowerHeight
    rw [mul_pow, ← Real.rpow_mul_natCast hKpos.le]
    norm_num
  have hsmall : lowerHeight cStar n ≤ 1 / 100 := by
    unfold lowerHeight
    have hKone : (1 : ℝ) ≤ lowerCells n := by
      exact le_trans (Real.one_le_rpow hn1 (by norm_num : (0 : ℝ) ≤ 4 / 3)) hbase
    have hfac := Real.rpow_le_one_of_one_le_of_nonpos hKone
      (by norm_num : (-(1 / 8 : ℝ)) ≤ 0)
    have hfac0 : 0 ≤ (lowerCells n : ℝ) ^ (-(1 / 8 : ℝ)) :=
      (Real.rpow_pos_of_pos hKpos _).le
    nlinarith [mul_le_mul_of_nonneg_left hfac hc.1.le]
  have hbpos : 0 < actualStrength a n := by
    unfold actualStrength
    exact lt_of_lt_of_le ha.1 (le_max_left _ _)
  have hpowpos : 0 ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) :=
    (Real.rpow_pos_of_pos hnpos _).le
  have hbound : lowerHeight cStar n ^ 2 ≤
      (1 / 10000 : ℝ) * actualStrength a n := by
    rw [hsq]
    have hc2 : cStar ^ 2 ≤ (1 / 10000 : ℝ) := by nlinarith
    have hp := mul_le_mul_of_nonneg_left hpow (sq_nonneg cStar)
    have hp2 := mul_le_mul_of_nonneg_right hc2 hpowpos
    have hb : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ actualStrength a n :=
      le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 1 / 10000)]
  have hsqsmall : lowerHeight cStar n ^ 2 ≤ (1 / 10000 : ℝ) := by
    have hnonneg : 0 ≤ lowerHeight cStar n := by
      unfold lowerHeight
      exact mul_nonneg hc.1.le (Real.rpow_pos_of_pos hKpos _).le
    nlinarith
  constructor
  · exact hc.1
  constructor
  · linarith
  · nlinarith [mul_nonneg (le_of_lt hbpos)
      (show 0 ≤ (1 / 4 : ℝ) - lowerHeight cStar n ^ 2 by linarith)]

/-- Admissibility and positive sample size imply the paper's strict height range.  Under [the displayed assumptions and inputs](hyp:n,a,cStar,hDomain), [the stated conclusion holds](goal). -/
-- keep: certifies the frozen h_n ∈ (0,1) realization for the F2.5 faithfulness review
lemma lowerHeight_bounds_of_domain (n : ℕ) (a cStar : ℝ)
    (hDomain : LowerExperimentDomain n a cStar) :
    0 < lowerHeight cStar n ∧ lowerHeight cStar n ≤ 3 / 16 ∧
      lowerHeight cStar n < 1 := by
  have hn := hDomain.1
  have hK : 0 < lowerCells n := by
    unfold lowerCells
    exact Nat.ceil_pos.mpr (by positivity)
  have hhpos : 0 < lowerHeight cStar n := by
    unfold lowerHeight
    exact mul_pos hDomain.2.1 (Real.rpow_pos_of_pos (by exact_mod_cast hK) _)
  exact ⟨hhpos, hDomain.2.2.1, lt_of_le_of_lt hDomain.2.2.1 (by norm_num)⟩
/-- [The mix constant object](goal) is defined without additional inputs. -/

noncomputable def mixConstant : ℝ := 19321 / 1800
  -- @realizes C_{\mathrm{mix}}(chi-squared exponent)
/-- [The witness direction object](goal) is defined from [the supplied inputs](hyp:x). -/

noncomputable def witnessDirection (x : ℝ) : ℝ :=
  |x - 1 / 2| ^ holderExponent -
    ∫ u in (0 : ℝ)..1, |u - 1 / 2| ^ holderExponent
  -- @realizes g_{\dagger}(centered continuous Hölder direction)
/-- [The witness amplitude object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,L). -/

noncomputable def witnessAmplitude (c_f C_f L : ℝ) : ℝ :=
  min (1 - c_f) (min (C_f - 1) (min (1 / 4) (L - 1))) / 4
  -- @realizes \varepsilon_{\dagger}(deterministic positive small amplitude)
/-- [The simple primitive kernel object](goal) is defined from [the supplied inputs](hyp:s,x). -/

noncomputable def simplePrimitiveKernel (s : Bool) (x : ℝ) :
    Measure FullData :=
  (1 / 8 : ℝ≥0∞) • Measure.dirac (s, x, false, true, (1 / 2 : ℝ), 1 / 2) +
  (7 / 16 : ℝ≥0∞) • Measure.dirac (s, x, true, true, (1 / 2 : ℝ), 1 / 2) +
  (7 / 16 : ℝ≥0∞) • Measure.dirac (s, x, false, false, (1 / 2 : ℝ), 1 / 2)
/-- [The simple primitive population object](goal) is defined from [the supplied inputs](hyp:s,density). -/

noncomputable def simplePrimitivePopulation (s : Bool) (density : ℝ → ℝ) :
    Measure FullData :=
  ((volume.restrict covariateSpace).withDensity
    (fun x => ENNReal.ofReal (density x))).bind
    (simplePrimitiveKernel s)

-- @node: def:continuous-geometry-witness
/-- [The continuous geometry witness object](goal) is defined from [the supplied inputs](hyp:_n,c_f,C_f,L). -/
noncomputable def continuousGeometryWitness (σ : Bool) (_n : ℕ)
    (c_f C_f L : ℝ) : TransportLaw :=
  let ε := witnessAmplitude c_f C_f L
  let s := sign σ
  let fS := fun x => 1 + s * ε * witnessDirection x
  let fT := fun x => 1 - s * ε * witnessDirection x
  let e := fun x => 1 / 2 + s * ε * witnessDirection x
  let source := simplePrimitivePopulation true fS
  let target := simplePrimitivePopulation false fT
  let full := (1 / 2 : ℝ≥0∞) • source + (1 / 2 : ℝ≥0∞) • target
  let assigned := assignedFrom source e
  let observed := assigned.map observeSource
  let targetX := (ProbabilityTheory.cond full {o | population o = false}).map covariate
  { fullLaw := full
    assignedLaw := assigned
    sampleLaw := fun nS nT =>
      (Measure.pi (fun _ : Fin nS => observed)).prod
        (Measure.pi (fun _ : Fin nT => targetX))
    fS := fS
    fT := fT
    e := e
    m := fun A z _ => if A then 1 / 2 else
      if z then (9 / 16 : ℝ) else 7 / 16
    assignmentPotentialOutcome := fun z o =>
      potentialOutcome o (potentialReceipt o z) }
  -- @realizes P_{\sigma}^{\dagger}(continuous geometry law)
  -- @realizes \sigma(sign) @realizes \varepsilon_{\dagger}(small fixed amplitude)

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

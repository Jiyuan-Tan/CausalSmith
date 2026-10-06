module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-! Public inverse pairs, deterministic dictionary selection and the split clipped estimator. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators FourierTransform
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]

/-- A public latent weight paired with its observable inverse. -/
structure WeightPair where
  q : ℝ → ℝ -- @realizes q(real weight carrier; nonnegativity in PairAdmissible)
  ell : ℝ → ℝ -- @realizes ellq(real inverse-weight carrier)
-- @env: S3
variable (beta kappa sigma : ℝ) (n : ℕ)

/-- Lebesgue moment of a public latent weight against an absolute power of the centered dose. -/
def weightMoment (s : ℝ) (q : ℝ → ℝ) : ℝ :=
  ∫ t in Icc (-1/2 : ℝ) (1/2), |t| ^ s * q t -- @realizes Iq(weighted Lebesgue moment)
/-- Reference denominator floor at the unit constants (stratum mass one quarter, lower envelope one quarter), used only to calibrate the dictionary tuning. -/
def unitbq (kappa : ℝ) (q : ℝ → ℝ) : ℝ := weightMoment kappa q / 16
/-- Reference localization-bias bound at the unit envelope constants, used only to calibrate the dictionary tuning. -/
def unitBq (beta kappa : ℝ) (q : ℝ → ℝ) : ℝ :=
  64 * weightMoment (kappa+beta) q / weightMoment kappa q
/-- Public lower bound for the unmarked weighted denominator: the minimum stratum mass times the lower envelope constant times the weighted moment. -/
def bq (K : ClassConstants) (kappa : ℝ) (q : ℝ → ℝ) : ℝ := K.pmin * K.clo * weightMoment kappa q -- @realizes bq(pmin clo I_kappa)
/-- Public localization-bias bound: the envelope ratio times the ratio of the higher to the base weighted moment. -/
def Bq (K : ClassConstants) (beta kappa : ℝ) (q : ℝ → ℝ) : ℝ :=
  K.chi / K.clo * weightMoment (kappa+beta) q / weightMoment kappa q -- @realizes Bq(public localization bias)
/-- Extended Gaussian inverse-weight second moment; infinite values are retained. -/
def VqENN (kappa sigma : ℝ) (ell : ℝ → ℝ) : ℝ≥0∞ :=
  16 * ∫⁻ t in Icc (-1/2 : ℝ) (1/2), ENNReal.ofReal (|t| ^ kappa) *
    (∫⁻ z, ENNReal.ofReal ((ell (t+sigma*z))^2) ∂gaussianReal 0 1) -- @realizes Vq(extended second-moment integral; finiteness explicit)
/-- Real value of the reference second moment, used only after its finiteness is established. -/
def Vq (kappa sigma : ℝ) (ell : ℝ → ℝ) : ℝ := (VqENN kappa sigma ell).toReal
/-- Public extended second-moment bound: the reference moment rescaled from the reference upper envelope sixteen to the public upper envelope constant. -/
def pubVqENN (K : ClassConstants) (kappa sigma : ℝ) (ell : ℝ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (K.chi / 16) * VqENN kappa sigma ell
/-- Real value of the public second-moment bound. -/
def pubVq (K : ClassConstants) (kappa sigma : ℝ) (ell : ℝ → ℝ) : ℝ := (pubVqENN K kappa sigma ell).toReal
/-- Public sum of localization bias, denominator-scaled second-moment error and stratum-frequency error. -/
def Aq (K : ClassConstants) (beta kappa : ℝ) (n : ℕ) (sigma : ℝ) (q : WeightPair) : ℝ :=
  Bq K beta kappa q.q + 12 / bq K kappa q.q * Real.sqrt (pubVq K kappa sigma q.ell / n) +
    2 * Real.sqrt (3 / n) -- @realizes Aq(public expected-error certificate)
/-- Reference error certificate at the unit constants, used only to calibrate the dictionary tuning. -/
def unitAq (beta kappa : ℝ) (n : ℕ) (sigma : ℝ) (q : WeightPair) : ℝ :=
  unitBq beta kappa q.q + 12 / unitbq kappa q.q * Real.sqrt (Vq kappa sigma q.ell / n) +
    2 * Real.sqrt (3 / n)

/-- [The public second-moment bound for class constants K](hyp:K) [is finite whenever the reference moment is](hyp:hV), [so it is a real number](goal). -/
lemma pubVqENN_lt_top (K : ClassConstants) (kappa sigma : ℝ) (ell : ℝ → ℝ)
    (hV : VqENN kappa sigma ell < ⊤) : pubVqENN K kappa sigma ell < ⊤ :=
  ENNReal.mul_lt_top ENNReal.ofReal_lt_top hV

/-- [The real public second-moment bound](goal) [for class constants K](hyp:K) equals the upper envelope constant over sixteen times the real reference moment. -/
lemma pubVq_eq (K : ClassConstants) (kappa sigma : ℝ) (ell : ℝ → ℝ) :
    pubVq K kappa sigma ell = K.chi / 16 * Vq kappa sigma ell := by
  rw [pubVq, pubVqENN, ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (div_nonneg (K.clo_pos.le.trans K.clo_le_chi) (by norm_num))]
  rfl

/-- Exact, finite pointwise Gaussian inversion and a positive finite weighted moment. -/
def PairAdmissible (kappa sigma : ℝ) (q : WeightPair) : Prop :=
  Measurable q.q ∧ Measurable q.ell ∧
  (∀ t ∈ Icc (-1/2 : ℝ) (1/2), 0 ≤ q.q t) ∧ -- @realizes q(nonnegative on latent support)
  Integrable (fun t => |t| ^ kappa * q.q t) (volume.restrict (Icc (-1/2 : ℝ) (1/2))) ∧
  0 < weightMoment kappa q.q ∧
  (∀ t ∈ Icc (-1/2 : ℝ) (1/2), Integrable (fun z => q.ell (t+sigma*z)) (gaussianReal 0 1)) ∧
  (∀ t ∈ Icc (-1/2 : ℝ) (1/2), ∫ z, q.ell (t+sigma*z) ∂gaussianReal 0 1 = q.q t)
/-- Absolute integrability of the inverse weight under the structural law’s observed centered dose. -/
def LawAdmissible (sigma : ℝ) (P : Measure (StructSpace S)) (q : WeightPair) : Prop :=
  Integrable (fun w => q.ell (observedCentered sigma w)) P

/-- The sixth power of sinc, with its continuous value at zero. -/
def sincSix (u : ℝ) : ℝ := if u = 0 then 1 else (Real.sin u / u)^6 -- @realizes Qkernel(sinc^6 with continuous value at zero)
/-- Positive Fourier localization weight at the specified bandwidth. -/
def qF (h t : ℝ) : ℝ := sincSix (t/h) -- @realizes qF(Q(t/h))
/-- Mathlib's Fourier convention uses exp(-2π i ξt); the multiplier uses ω=2πξ. -/
def ellF (sigma h v : ℝ) : ℝ :=
  (Fourier.fourierIntegral Real.fourierChar volume (fun xi : ℝ =>
    Fourier.fourierIntegral Real.fourierChar volume (fun t : ℝ => (qF h t : ℂ)) xi *
      (Real.exp (sigma^2 * (2*Real.pi*xi)^2 / 2) : ℂ)) (-v)).re -- @realizes ellF(exact inverse Fourier multiplier)
/-- Polynomial extension of the odd-degree sinc-of-arcsine weight, through even U coefficients. -/
def qMPoly (m : ℕ) : Polynomial ℝ :=
  (∑ k ∈ Finset.range m,
    Polynomial.C ((Polynomial.Chebyshev.U ℝ (m-1 : ℕ)).coeff (2*k) / (m : ℝ)) *
      (1 - Polynomial.C 4 * Polynomial.X^2)^k)^6
/-- Evaluation of the polynomial extension of the positive odd-degree localization weight. -/
def qM (m : ℕ) (t : ℝ) : ℝ := (qMPoly m).eval t -- @realizes qM(polynomial extension; odd-m trig identity proved below)
/-- Finite polynomial inverse-heat sum of the even derivatives of the latent weight. -/
def ellM (sigma : ℝ) (m : ℕ) (v : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (3*(m-1)+1), (-sigma^2/2)^j / (j.factorial : ℝ) *
    ((Polynomial.derivative^[2*j]) (qMPoly m)).eval v -- @realizes ellM(finite inverse-heat derivative sum)
/-- Reflection multiplies the nth polynomial coefficient by its parity sign. [This is the stated conclusion](goal). [This is the stated conclusion](goal). [This is the stated conclusion](goal). [This is the stated conclusion](goal). -/
-- @node: polynomial_coeff_reflection
lemma polynomial_coeff_reflection (p : Polynomial ℝ) (n : ℕ) :
    (p.comp (-Polynomial.X)).coeff n = (-1 : ℝ)^n * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial j a =>
      rw [Polynomial.monomial_comp]
      rw [show (-Polynomial.X : Polynomial ℝ)^j = (-1 : ℝ)^j • Polynomial.X^j by
        rw [show (-Polynomial.X : Polynomial ℝ) = (-1 : ℝ) • Polynomial.X by simp,
          smul_pow]]
      by_cases h : j = n
      · subst j; simp
      · simp [Polynomial.coeff_monomial, h, Ne.symm h]

/-- An even-degree second-kind Chebyshev polynomial has no odd coefficients. [Under the stated conditions](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: chebyshevU_odd_coeff_zero
lemma chebyshevU_odd_coeff_zero (n : ℕ) (hn : Even n) (k : ℕ) :
    (Polynomial.Chebyshev.U ℝ n).coeff (2*k+1) = 0 := by
  have hp : (Polynomial.Chebyshev.U ℝ n).comp (-Polynomial.X) =
      Polynomial.Chebyshev.U ℝ n := by
    apply Polynomial.funext
    intro x
    simpa [Polynomial.eval_comp, hn.neg_one_pow] using
      Polynomial.Chebyshev.U_eval_neg (R := ℝ) n x
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff (2*k+1)) hp
  rw [polynomial_coeff_reflection] at hc
  simp only [pow_add, pow_mul] at hc
  norm_num at hc
  linarith

/-- Splitting a finite sum into its even and odd indices. [Under the stated conditions](hyp:f). [This is the stated conclusion](goal). -/
-- @node: sum_range_double_parity
lemma sum_range_double_parity (f : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range (2*m), f i) =
      ∑ k ∈ Finset.range m, (f (2*k) + f (2*k+1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2*(m+1) = (2*m+1)+1 by omega]
      simp only [Finset.sum_range_succ]
      rw [ih]
      ring

/-- The polynomial weight is the sixth power of the normalized Chebyshev evaluation. [Under the stated conditions](hyp:hm,hmpos,hc). [This is the stated conclusion](goal). -/
-- @node: qM_eq_chebyshev_even_eval
lemma qM_eq_chebyshev_even_eval (m : ℕ) (hm : Odd m) (hmpos : 0 < m)
    (t c : ℝ) (hc : c^2 = 1-4*t^2) :
    qM m t = ((Polynomial.Chebyshev.U ℝ (m-1 : ℕ)).eval c / (m : ℝ))^6 := by
  have heven : Even (m-1) := by
    obtain ⟨s, hs⟩ := hm
    exact ⟨s, by omega⟩
  have heval := Polynomial.eval_eq_sum_range'
    (p := Polynomial.Chebyshev.U ℝ (m-1 : ℕ)) (n := 2*m)
    (by rw [Polynomial.Chebyshev.natDegree_U_natCast]; omega) c
  rw [sum_range_double_parity] at heval
  simp only [chebyshevU_odd_coeff_zero (m-1) heven, zero_mul, add_zero] at heval
  simp only [qM, qMPoly, Polynomial.eval_pow, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, Finset.sum_div, heval]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_mul, hc]
  ring

/-- Odd polynomial weights agree with their continuous trigonometric formula. [Under the stated conditions](hyp:hm,hmpos,ht). [This is the stated conclusion](goal). -/
-- @node: qM_trig
lemma qM_trig (m : ℕ) (hm : Odd m) (hmpos : 0 < m) (t : ℝ)
    (ht : t ∈ Icc (-1/2 : ℝ) (1/2)) :
    qM m t = if t = 0 then 1 else (Real.sin (m * Real.arcsin (2*t)) / (2*m*t))^6 := by
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
  have hcast : ((m-1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    simp
  by_cases ht0 : t = 0
  · subst t
    rw [qM_eq_chebyshev_even_eval m hm hmpos 0 1 (by norm_num)]
    simp [Polynomial.Chebyshev.U_eval_one, hcast, hmne]
  · have hsin : Real.sin (Real.arcsin (2*t)) = 2*t :=
      Real.sin_arcsin (by linarith [ht.1]) (by linarith [ht.2])
    have hcos : (Real.cos (Real.arcsin (2*t)))^2 = 1-4*t^2 := by
      have h := Real.sin_sq_add_cos_sq (Real.arcsin (2*t))
      rw [hsin] at h
      nlinarith
    rw [qM_eq_chebyshev_even_eval m hm hmpos t _ hcos, if_neg ht0]
    have hU := Polynomial.Chebyshev.U_real_cos (Real.arcsin (2*t)) (m-1 : ℕ)
    rw [hsin] at hU
    push_cast at hU
    rw [hcast] at hU
    congr 1
    apply (eq_div_iff (by positivity : (2 : ℝ)*m*t ≠ 0)).2
    field_simp
    nlinarith [hU]

/-- Public family and degree tags, with constant tags first, then Fourier indices, then polynomial indices. -/
inductive DictTag where
  | const
  | fourier (k : ℕ)
  | poly (j : ℕ)
  deriving DecidableEq

attribute [inherit_doc DictTag] instDecidableEqDictTag

/-- Dyadic localization bandwidth indexed by a nonnegative integer. -/
def dyadicBandwidth (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℤ))
/-- Finite candidate list in the fixed deterministic tie-breaking order. -/
def dictionaryList (n : ℕ) : List DictTag :=
  [DictTag.const] ++
    ((List.range (n^2+1)).filter (fun k =>
      (n : ℝ)^(-2 : ℝ) ≤ dyadicBandwidth k ∧ dyadicBandwidth k ≤ 1/4)).map DictTag.fourier ++
    ((List.range (n^2+1)).filter (fun j => Odd (2^j+1) ∧ 2^j+1 ≤ n^2)).map DictTag.poly
/-- The finite public Fourier, polynomial and constant dictionary with increasing-index tie order. -/
-- @node: def:weight-dictionary
def weightDictionary (n : ℕ) (sigma : ℝ) : Finset DictTag :=
  (dictionaryList n).toFinset -- @realizes Ddict(public finite dyadic/odd polynomial dictionary)
/-- Latent weight and observable inverse associated with a public dictionary tag. -/
def pairOf (sigma : ℝ) : DictTag → WeightPair
  | .const => ⟨fun _ => 1, fun _ => 1⟩
  | .fourier k => ⟨qF (dyadicBandwidth k), ellF sigma (dyadicBandwidth k)⟩
  | .poly j => ⟨qM (2^j+1), ellM sigma (2^j+1)⟩
/-- Expected-error certificate of the pair associated with a dictionary tag. -/
def score (K : ClassConstants) (beta kappa : ℝ) (n : ℕ) (sigma : ℝ) (tag : DictTag) : ℝ :=
  Aq K beta kappa n sigma (pairOf sigma tag)
/-- Reference certificate of a dictionary tag at the unit constants, used only to calibrate the dictionary tuning. -/
def unitScore (beta kappa : ℝ) (n : ℕ) (sigma : ℝ) (tag : DictTag) : ℝ :=
  unitAq beta kappa n sigma (pairOf sigma tag)
/-- Minimum-score public tag, retaining the first tag in the fixed order when scores tie. -/
def selectedTag (K : ClassConstants) (beta kappa : ℝ) (n : ℕ) (sigma : ℝ) : DictTag :=
  (dictionaryList n).foldl (fun best tag =>
    if score K beta kappa n sigma tag < score K beta kappa n sigma best then tag else best) .const -- @realizes qhat(public argmin with const<Fourier<poly tie order)

/-- Deterministic modulo-three sample block. -/
def splitBlock (n r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val % 3 = r) -- @realizes Iblocks(deterministic modulo-three partition)
/-- All three deterministic split blocks contain at least one observed record. -/
def blocksNonempty (n : ℕ) : Prop := ∀ r < 3, (splitBlock n r).Nonempty

/-- Block-zero empirical frequency of a confounder stratum. -/
def phat (n : ℕ) (data : Fin n → Obs) (x : Bool) : ℝ :=
  (∑ i ∈ splitBlock n 0, if (data i).1 = x then (1 : ℝ) else 0) /
    (splitBlock n 0).card -- @realizes phatx(block-zero frequency)
/-- Block-one empirical inverse-weight denominator in a confounder stratum. -/
def Dhat (n : ℕ) (data : Fin n → Obs) (x : Bool) (q : WeightPair) : ℝ :=
  (∑ i ∈ splitBlock n 1, if (data i).1 = x then q.ell ((data i).2.1-a0) else 0) /
    (splitBlock n 1).card -- @realizes Dhatx(block-one inverse-weight denominator)
/-- Block-two empirical outcome-marked inverse-weight numerator in a confounder stratum. -/
def Mhat (n : ℕ) (data : Fin n → Obs) (x : Bool) (q : WeightPair) : ℝ :=
  (∑ i ∈ splitBlock n 2, if (data i).1 = x then (data i).2.2*q.ell ((data i).2.1-a0) else 0) /
    (splitBlock n 2).card -- @realizes Mhatx(block-two marked numerator)
/-- Empirical stratum ratio with the public denominator floor and projection to the unit outcome interval. -/
def muhat (K : ClassConstants) (kappa : ℝ) (n : ℕ) (data : Fin n → Obs) (x : Bool) (q : WeightPair) : ℝ :=
  max 0 (min 1 (Mhat n data x q / max (Dhat n data x q) (bq K kappa q.q/2))) -- @realizes muhatx(public floor followed by projection)
/-- Stratum-frequency weighted sum of the clipped empirical stratum ratios. -/
def weightEstimator (K : ClassConstants) (kappa : ℝ) (n : ℕ) (q : WeightPair) (data : Fin n → Obs) : ℝ :=
  ∑ x : Bool, phat n data x * muhat K kappa n data x q -- @realizes thetahatq(stratum-weighted clipped ratio)
/-- Population stratum-restricted inverse-weight denominator. -/
def populationD (sigma : ℝ) (P : Measure (StructSpace S)) (x : Bool) (q : WeightPair) : ℝ :=
  ∫ w, (if sX w = x then q.ell (observedCentered sigma w) else 0) ∂P
/-- Population stratum-restricted outcome-marked inverse-weight numerator. -/
def populationM (sigma : ℝ) (P : Measure (StructSpace S)) (x : Bool) (q : WeightPair) : ℝ :=
  ∫ w, (if sX w = x then sY w*q.ell (observedCentered sigma w) else 0) ∂P
/-- Population localized marked-to-unmarked ratio. -/
def localizedRatio (sigma : ℝ) (P : Measure (StructSpace S)) (x : Bool) (q : WeightPair) : ℝ :=
  populationM sigma P x q / populationD sigma P x q -- @realizes mxq(population marked/unmarked ratio)

/-- Total selected estimator with the midpoint fallback for empty split blocks. -/
-- @node: def:total-estimator
def totalEstimator (K : ClassConstants) (beta kappa : ℝ) (n : ℕ) (sigma : ℝ) (data : Fin n → Obs) : ℝ :=
  if blocksNonempty n then weightEstimator K kappa n (pairOf sigma (selectedTag K beta kappa n sigma)) data
  else 1/2 -- @realizes thetahat(selected observable estimator and empty-block fallback)
/-- [The confidence interval](goal) for [the public class constants](hyp:K) at [smoothness exponent](hyp:beta), [design exponent](hyp:kappa), [noncoverage level](hyp:alpha), [sample size](hyp:n) and [error scale](hyp:sigma), computed from [the observed records](hyp:data): the total estimate plus or minus its public error score divided by the noncoverage level, clipped to the unit interval, with the whole unit interval as the small-sample fallback. -/
-- @node: def:honest-interval
def honestInterval (K : ClassConstants) (beta kappa alpha : ℝ) (n : ℕ) (sigma : ℝ) (data : Fin n → Obs) : Set ℝ :=
  if blocksNonempty n then
    Icc (max 0 (totalEstimator K beta kappa n sigma data - score K beta kappa n sigma (selectedTag K beta kappa n sigma) / alpha))
      (min 1 (totalEstimator K beta kappa n sigma data + score K beta kappa n sigma (selectedTag K beta kappa n sigma) / alpha))
  else Icc 0 1 -- @realizes Cn(connected clipped interval with full-range fallback)

/-- The selected tag is a dictionary member with score no larger than any other member. [This is the stated conclusion](goal). [This is the stated conclusion](goal). [This is the stated conclusion](goal). [This is the stated conclusion](goal). -/
-- @node: selectedTag_minimizes
lemma selectedTag_minimizes (K : ClassConstants) (beta kappa : ℝ) (n : ℕ) (sigma : ℝ) :
    selectedTag K beta kappa n sigma ∈ weightDictionary n sigma ∧
    ∀ tag ∈ weightDictionary n sigma, score K beta kappa n sigma (selectedTag K beta kappa n sigma) ≤
      score K beta kappa n sigma tag := by
  let f := score K beta kappa n sigma
  have hfold : ∀ (l : List DictTag) (best : DictTag),
      l.foldl (fun b t => if f t < f b then t else b) best ∈ best :: l ∧
      f (l.foldl (fun b t => if f t < f b then t else b) best) ≤ f best ∧
      ∀ t ∈ l, f (l.foldl (fun b t => if f t < f b then t else b) best) ≤ f t := by
    intro l
    induction l with
    | nil => intro best; simp
    | cons t l ih =>
      intro best
      simp only [List.foldl_cons]
      by_cases h : f t < f best
      · simp only [if_pos h]
        obtain ⟨hmem, hle, hall⟩ := ih t
        refine ⟨?_, hle.trans h.le, ?_⟩
        · exact List.mem_cons_of_mem best hmem
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact hle
          · exact hall a ha
      · simp only [if_neg h]
        obtain ⟨hmem, hle, hall⟩ := ih best
        refine ⟨?_, hle, ?_⟩
        · rcases List.mem_cons.mp hmem with heq | hmem
          · exact List.mem_cons.mpr (Or.inl heq)
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem)
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact hle.trans (le_of_not_gt h)
          · exact hall a ha
  obtain ⟨hmem, _, hall⟩ := hfold (dictionaryList n) .const
  have hc : DictTag.const ∈ dictionaryList n := by simp [dictionaryList]
  have hm : selectedTag K beta kappa n sigma ∈ dictionaryList n := by
    rcases List.mem_cons.mp hmem with hmem | hmem
    · simpa [selectedTag, f, hmem] using hc
    · exact hmem
  refine ⟨by simpa [weightDictionary] using hm, ?_⟩
  intro tag htag
  exact hall tag (by simpa [weightDictionary] using htag)
/-- The totalized real Fourier integral is continuous: nonintegrable inputs give the zero function. [Under the stated conditions](hyp:f). [This is the stated conclusion](goal). -/
-- @node: realFourierIntegral_continuous
lemma realFourierIntegral_continuous (f : ℝ → ℂ) :
    Continuous (Fourier.fourierIntegral Real.fourierChar volume f) := by
  by_cases hf : Integrable f
  · exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) hf
  · have hz : Fourier.fourierIntegral Real.fourierChar volume f = fun _ => 0 := by
      funext w
      rw [Fourier.fourierIntegral_def]
      apply integral_undef
      exact fun h => hf ((VectorFourier.fourierIntegral_convergent_iff
        (L := LinearMap.mul ℝ ℝ) Real.continuous_fourierChar (by fun_prop) w).mp h)
    rw [hz]
    exact continuous_const

/-- The real inverse Fourier weight is Borel measurable for every public scale and bandwidth. [This is the stated conclusion](goal). -/
-- @node: ellF_measurable
@[fun_prop] lemma ellF_measurable (sigma h : ℝ) : Measurable (ellF sigma h) := by
  unfold ellF
  have hc := realFourierIntegral_continuous (fun xi : ℝ =>
    Fourier.fourierIntegral Real.fourierChar volume (fun t : ℝ => (qF h t : ℂ)) xi *
      (Real.exp (sigma^2 * (2*Real.pi*xi)^2 / 2) : ℂ))
  exact (Complex.continuous_re.comp (hc.comp continuous_neg)).measurable

/-- The finite inverse-heat polynomial weight is Borel measurable. [This is the stated conclusion](goal). -/
-- @node: ellM_measurable
@[fun_prop] lemma ellM_measurable (sigma : ℝ) (m : ℕ) : Measurable (ellM sigma m) := by
  unfold ellM
  fun_prop

/-- Every public dictionary tag supplies a Borel measurable inverse weight. [This is the stated conclusion](goal). -/
-- @node: pairOf_ell_measurable
@[fun_prop] lemma pairOf_ell_measurable (sigma : ℝ) (tag : DictTag) :
    Measurable (pairOf sigma tag).ell := by
  cases tag with
  | const => exact measurable_const
  | fourier k => exact ellF_measurable sigma (dyadicBandwidth k)
  | poly j => exact ellM_measurable sigma (2^j+1)

/-- The empirical stratum frequency is Borel measurable in the records. [This is the stated conclusion](goal). -/
-- @node: phat_measurable
@[fun_prop] lemma phat_measurable (n : ℕ) (x : Bool) :
    Measurable (fun data : Fin n → Obs => phat n data x) := by
  have hm (i : Fin n) : Measurable (fun data : Fin n → Obs =>
      if (data i).1 = x then (1 : ℝ) else 0) := by
    exact Measurable.ite ((measurableSet_singleton x).preimage (by fun_prop))
      (by fun_prop) measurable_const
  unfold phat
  fun_prop

/-- The empirical denominator is measurable whenever the public inverse weight is measurable. [Under the stated conditions](hyp:hq). [This is the stated conclusion](goal). -/
-- @node: Dhat_measurable
@[fun_prop] lemma Dhat_measurable (n : ℕ) (x : Bool) (q : WeightPair)
    (hq : Measurable q.ell) : Measurable (fun data : Fin n → Obs => Dhat n data x q) := by
  have hm (i : Fin n) : Measurable (fun data : Fin n → Obs =>
      if (data i).1 = x then q.ell ((data i).2.1-a0) else 0) := by
    exact Measurable.ite ((measurableSet_singleton x).preimage (by fun_prop))
      (by fun_prop) measurable_const
  unfold Dhat
  fun_prop

/-- The empirical marked numerator is measurable whenever the public inverse weight is measurable. [Under the stated conditions](hyp:hq). [This is the stated conclusion](goal). -/
-- @node: Mhat_measurable
@[fun_prop] lemma Mhat_measurable (n : ℕ) (x : Bool) (q : WeightPair)
    (hq : Measurable q.ell) : Measurable (fun data : Fin n → Obs => Mhat n data x q) := by
  have hm (i : Fin n) : Measurable (fun data : Fin n → Obs =>
      if (data i).1 = x then (data i).2.2*q.ell ((data i).2.1-a0) else 0) := by
    exact Measurable.ite ((measurableSet_singleton x).preimage (by fun_prop))
      (by fun_prop) measurable_const
  unfold Mhat
  fun_prop

/-- The floored and clipped stratum ratio is a measurable function of the records. [Under the stated conditions](hyp:hq). [This is the stated conclusion](goal). -/
-- @node: muhat_measurable
@[fun_prop] lemma muhat_measurable (K : ClassConstants) (kappa : ℝ) (n : ℕ) (x : Bool) (q : WeightPair)
    (hq : Measurable q.ell) : Measurable (fun data : Fin n → Obs => muhat K kappa n data x q) := by
  unfold muhat
  fun_prop

/-- The weighted estimator is measurable whenever its public inverse weight is measurable. [Under the stated conditions](hyp:hq). [This is the stated conclusion](goal). -/
-- @node: weightEstimator_measurable
@[fun_prop] lemma weightEstimator_measurable (K : ClassConstants) (kappa : ℝ) (n : ℕ) (q : WeightPair)
    (hq : Measurable q.ell) : Measurable (weightEstimator K kappa n q) := by
  unfold weightEstimator
  fun_prop

/-- The total public selected estimator is a measurable function of the observed records. [This is the stated conclusion](goal). -/
-- @node: totalEstimator_measurable
@[fun_prop] lemma totalEstimator_measurable (K : ClassConstants) (beta kappa : ℝ) (n : ℕ) (sigma : ℝ) :
    Measurable (totalEstimator K beta kappa n sigma) := by
  unfold totalEstimator
  by_cases h : blocksNonempty n
  · simp only [if_pos h]
    exact weightEstimator_measurable K kappa n _
      (pairOf_ell_measurable sigma (selectedTag K beta kappa n sigma))
  · simp only [if_neg h]
    exact measurable_const
/-- The declared clipped confidence interval is connected, including its small-sample fallback. [This is the stated conclusion](goal). -/
-- @node: honestInterval_connected
lemma honestInterval_connected (K : ClassConstants) (beta kappa alpha : ℝ) (n : ℕ) (sigma : ℝ) (z : Fin n → Obs) :
    (honestInterval K beta kappa alpha n sigma z).OrdConnected := by
  unfold honestInterval
  split <;> exact ordConnected_Icc
/-- Membership in the declared confidence interval is jointly measurable in observed records and candidate target. [This is the stated conclusion](goal). -/
-- @node: honestInterval_membership_measurable
lemma honestInterval_membership_measurable (K : ClassConstants) (beta kappa alpha : ℝ) (n : ℕ) (sigma : ℝ) :
    MeasurableSet {p : (Fin n → Obs) × ℝ | p.2 ∈ honestInterval K beta kappa alpha n sigma p.1} := by
  have ht : Measurable (fun p : (Fin n → Obs) × ℝ =>
      totalEstimator K beta kappa n sigma p.1) := by fun_prop
  unfold honestInterval
  by_cases h : blocksNonempty n
  · simp only [if_pos h, mem_Icc]
    exact (measurableSet_le (by fun_prop) measurable_snd).inter
      (measurableSet_le measurable_snd (by fun_prop))
  · simp only [if_neg h, mem_Icc]
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)

/-- The declared confidence interval packaged as a measurable connected procedure based solely on the observed records. -/
def honestIntervalProcedure (K : ClassConstants) (beta kappa alpha : ℝ) (n : ℕ) (sigma : ℝ) : IntervalProcedure n :=
  ⟨honestInterval K beta kappa alpha n sigma,
    honestInterval_connected K beta kappa alpha n sigma,
    honestInterval_membership_measurable K beta kappa alpha n sigma⟩
end CausalSmith.Stat.NoisydoseWeakdesignTransition

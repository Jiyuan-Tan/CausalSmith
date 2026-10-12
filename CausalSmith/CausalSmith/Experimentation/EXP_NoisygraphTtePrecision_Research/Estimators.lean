module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Decision procedures, extended risks, and explicit attaining rules

Cold scaffold: definitions are complete; proof obligations are reserved for Stage 3.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

-- @env: S3
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Total Borel seeded estimators taking values in the closed unit interval. -/
abbrev Estimator (V : Type*) : Type _ :=
  {T : Record V × ℝ → ℝ // Measurable T ∧ ∀ x, T x ∈ Set.Icc (-1) 1}
-- @realizes T(total Borel estimator with range [-1,1], evaluated under a seed supported on [0,1])
/-- Total Borel endpoints of nonempty closed connected intervals in [-1,1]. -/
abbrev IntervalProc (V : Type*) : Type _ :=
  {I : Record V × ℝ → ℝ × ℝ // Measurable I ∧ ∀ x, -1 ≤ (I x).1 ∧ (I x).1 ≤ (I x).2 ∧ (I x).2 ≤ 1}
-- @realizes I(total Borel endpoint pair with -1≤l≤u≤1)
/-- Expected squared error with complete-lattice semantics. -/
def sqLoss (D : Design V) (η : Schedule V) (T : Estimator V) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((T.1 x - CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η)^2) ∂recordLaw D η
/-- Worst-case squared risk over the complete fixed-schedule class. -/
def worstRisk (D : Design V) (d : ℕ) (T : Estimator V) : ℝ≥0∞ :=
  Causalean.Stat.worstCaseRiskENNReal
    (fun (T : Estimator V) (η : {η : Schedule V // ScheduleClass η d}) => sqLoss D η.1 T) T
/-- Minimax squared risk over all total Borel seeded estimators. -/
-- @node: def:risk
def minimaxRisk (D : Design V) (d : ℕ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal
    (fun (T : Estimator V) (η : {η : Schedule V // ScheduleClass η d}) => sqLoss D η.1 T)
/-- The public-parameter canonical minimax risk. -/
abbrev R (n d : ℕ) (q r : ℝ) : ℝ≥0∞ := minimaxRisk (noisyDesign (V := Fin n) q r) d -- @realizes R(infimum of worst-case squared error)
/-- Population-wise ninety-percent coverage. -/
def Honest (D : Design V) (d : ℕ) (I : IntervalProc V) : Prop :=
  ∀ η, ScheduleClass η d → ENNReal.ofReal (9/10) ≤
    recordLaw D η {x | CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η ∈ Set.Icc (I.1 x).1 (I.1 x).2}
/-- Expected connected interval length. -/
def expLength (D : Design V) (η : Schedule V) (I : IntervalProc V) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((I.1 x).2 - (I.1 x).1) ∂recordLaw D η
/-- Worst-case expected length of an endpoint procedure. -/
def worstLength (D : Design V) (d : ℕ) (I : IntervalProc V) : ℝ≥0∞ :=
  Causalean.Stat.worstCaseRiskENNReal
    (fun (I : IntervalProc V) (η : {η : Schedule V // ScheduleClass η d}) => expLength D η.1 I) I
/-- Minimax length over precisely the honest interval subtype. -/
-- @node: def:length
def minimaxLength (D : Design V) (d : ℕ) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal
    (fun (I : {I : IntervalProc V // Honest D d I}) (η : {η : Schedule V // ScheduleClass η d}) => expLength D η.1 I.1)
/-- The canonical public-parameter honest minimax length. -/
abbrev L (n d : ℕ) (q r : ℝ) : ℝ≥0∞ := minimaxLength (noisyDesign (V := Fin n) q r) d -- @realizes L(infimum over honest procedures of supremum expected length)
/-- Given [the stated assumptions](hyp:hD), [A probability design remains a probability law after adjoining the seed and record.](goal) -/
-- @node: recordLaw_probability
lemma recordLaw_probability (D : Design V) (η : Schedule V)
    (hD : IsProbabilityMeasure (D η)) : IsProbabilityMeasure (recordLaw D η) := by
  let : IsProbabilityMeasure (D η) := hD
  let : IsProbabilityMeasure seedLaw :=
    ⟨by simp [seedLaw, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.seedLaw,
      Real.volume_Icc]⟩
  have hr : Measurable (recordOf η) := by
    fun_prop (disch := exact Measurable.of_discrete)
  exact ((D η).prod seedLaw).isProbabilityMeasure_map
    ((hr.comp measurable_fst).prodMk measurable_snd).aemeasurable

/-- Given [the stated assumptions](hyp:hD), [The zero rule bounds minimax squared risk by one on probability designs.
@realizes R(finite nonnegative minimax risk, at most one on probability designs)](goal) -/
-- @node: minimaxRisk_le_one
lemma minimaxRisk_le_one (D : Design V) (hD : ∀ η, IsProbabilityMeasure (D η)) (d : ℕ) :
    minimaxRisk D d ≤ 1 := by
  let T : Estimator V := ⟨fun _ => 0, measurable_const, by intro x; norm_num⟩
  apply (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk T).trans
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro η
  let := recordLaw_probability D η.1 (hD η.1)
  have ht : (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η.1)^2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mpr (abs_tte_le_one η.2)
  unfold sqLoss
  calc
    _ ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂recordLaw D η.1 := by
      apply lintegral_mono
      intro x
      simpa [T] using ENNReal.ofReal_le_ofReal ht
    _ = 1 := by simp
/-- Given [the stated assumptions](hyp:hD), [The full interval bounds honest minimax length by two on probability designs.
@realizes L(finite nonnegative minimax length, at most two on probability designs)](goal) -/
-- @node: minimaxLength_le_two
lemma minimaxLength_le_two (D : Design V) (hD : ∀ η, IsProbabilityMeasure (D η)) (d : ℕ) :
    minimaxLength D d ≤ 2 := by
  let I : IntervalProc V :=
    ⟨fun _ => (-1, 1), measurable_const, by intro x; norm_num⟩
  have hI : Honest D d I := by
    intro η hη
    let := recordLaw_probability D η (hD η)
    have ht := abs_le.mp (abs_tte_le_one hη)
    have he : {x : Record V × ℝ |
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η ∈
          Set.Icc (I.1 x).1 (I.1 x).2} = Set.univ := by
      ext x
      simp [I, ht.1, ht.2]
    rw [he]
    norm_num
  apply (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk ⟨I, hI⟩).trans
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro η
  let := recordLaw_probability D η.1 (hD η.1)
  norm_num [expLength, I]
/-- The inherited supplied-graph score. -/
abbrev oracleScore (η : Schedule V) : Assign V → ℝ := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.oracleScore η
-- @realizes TG((2/n) sum_i Y_i(Z)(X_i+sum on incoming true arrows X_j))
/-- The inverse-channel score uses every off-diagonal report coordinate. -/
-- @node: def:score
def rawScore (q r : ℝ) (o : Record V) : ℝ :=
  if r < q then (2 / (Fintype.card V : ℝ)) * ∑ i,
    o.2.2 i * (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf (o.2.1 i) + ∑ j : V,
      if hji : j ≠ i then ((if o.1 ⟨(j,i), hji⟩ then 1 else 0) - r) *
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf (o.2.1 j) / (q-r) else 0) else 0
-- @realizes Traw(centered inverse-channel score for q>r, zero on the equality channel)
/-- [The inverse-channel score is Borel measurable.](goal) -/
-- @node: rawScore_measurable
@[fun_prop] lemma rawScore_measurable (q r : ℝ) : Measurable (rawScore (V := V) q r) := by
  unfold rawScore
  split_ifs
  · have hw (i : V) : Measurable (fun o : Record V =>
        signOf (o.2.1 i) + ∑ j : V,
          if hji : j ≠ i then ((if o.1 ⟨(j,i), hji⟩ then 1 else 0) - r) *
            signOf (o.2.1 j) / (q-r) else 0) := by
      exact (Measurable.of_discrete (f := fun hz : Acq V × Assign V =>
        signOf (hz.2 i) + ∑ j : V,
          if hji : j ≠ i then ((if hz.1 ⟨(j,i), hji⟩ then 1 else 0) - r) *
            signOf (hz.2 j) / (q-r) else 0)).comp
          (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      (measurable_snd.comp measurable_snd).eval.mul (hw i))
  · fun_prop
/-- The extended risk envelope is infinite on the equality channel.
@realizes u(extended-real explicit risk envelope, infinity when q=r) -/
-- @node: def:envelope
def upperEnvelope (n d : ℕ) (q r : ℝ) : ℝ≥0∞ :=
  if r < q then ENNReal.ofReal (5 * ((d : ℝ)+1)^2 / n +
    4 * (d*q*(1-q) + ((n : ℝ)-1)*r*(1-r)) / (n*(q-r)^2)) else ⊤
/-- The envelope clipped at one, converted to a finite real. -/
def boundedEnvelope (n d : ℕ) (q r : ℝ) : ℝ := (min 1 (upperEnvelope n d q r)).toReal
-- @realizes v(min{1,u})
/-- [The bounded envelope is in the closed unit interval.](goal) -/
-- @node: boundedEnvelope_mem_Icc
lemma boundedEnvelope_mem_Icc (n d : ℕ) (q r : ℝ) : boundedEnvelope n d q r ∈ Set.Icc 0 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · simpa [boundedEnvelope] using
      (ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤)
        (min_le_left (1 : ℝ≥0∞) (upperEnvelope n d q r)))
-- @realizes v(derived range [0,1])
/-- The observable clipped-or-zero rule. -/
-- @node: def:upper-rule
def upperRule (n d : ℕ) (q r : ℝ) (o : Record V) : ℝ :=
  if r < q ∧ upperEnvelope n d q r < 1 then max (-1) (min 1 (rawScore q r o)) else 0
-- @realizes Tzero(explicit original-record rule, clipped when the envelope is below one)
/-- [The clipped-or-zero rule is Borel measurable.](goal) -/
-- @node: upperRule_measurable
@[fun_prop] lemma upperRule_measurable (n d : ℕ) (q r : ℝ) :
    Measurable (upperRule (V := V) n d q r) := by
  unfold upperRule
  split_ifs <;> fun_prop
/-- [Every value of the explicit rule belongs to [-1,1].](goal) -/
-- @node: upperRule_mem_Icc
lemma upperRule_mem_Icc (n d : ℕ) (q r : ℝ) (o : Record V) :
    upperRule n d q r o ∈ Set.Icc (-1) 1 := by
  unfold upperRule
  split_ifs
  · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · norm_num
/-- [The explicit seed-independent estimator, with its Borel and range certificates.](goal) -/
-- @node: upperEstimator_valid
lemma upperEstimator_valid (n d : ℕ) (q r : ℝ) :
    Measurable (fun x : Record V × ℝ => upperRule n d q r x.1) ∧
    ∀ x : Record V × ℝ, upperRule n d q r x.1 ∈ Set.Icc (-1) 1 := by
  constructor
  · fun_prop
  · intro x
    exact upperRule_mem_Icc n d q r x.1
/-- The concrete bounded estimator. -/
def upperEstimator (n d : ℕ) (q r : ℝ) : Estimator V :=
  ⟨fun x => upperRule n d q r x.1, upperEstimator_valid n d q r⟩
/-- The explicit finite-calibrated interval endpoints. -/
-- @node: def:upper-interval
def upperInterval (n d : ℕ) (q r : ℝ) (o : Record V) : ℝ × ℝ :=
  (max (-1) (upperRule n d q r o - Real.sqrt (10 * boundedEnvelope n d q r)),
   min 1 (upperRule n d q r o + Real.sqrt (10 * boundedEnvelope n d q r)))
-- @realizes Izero(connected closed interval centered at Tzero, radius sqrt(10v), truncated to [-1,1])
/-- [The interval endpoint map is Borel measurable.](goal) -/
-- @node: upperInterval_measurable
@[fun_prop] lemma upperInterval_measurable (n d : ℕ) (q r : ℝ) :
    Measurable (upperInterval (V := V) n d q r) := by
  unfold upperInterval
  fun_prop
/-- [The endpoints enclose the center and are in the closed unit interval.](goal) -/
-- @node: upperInterval_order
lemma upperInterval_order (n d : ℕ) (q r : ℝ) (o : Record V) :
    -1 ≤ (upperInterval n d q r o).1 ∧
    (upperInterval n d q r o).1 ≤ upperRule n d q r o ∧
    upperRule n d q r o ≤ (upperInterval n d q r o).2 ∧
    (upperInterval n d q r o).2 ≤ 1 := by
  have hc := upperRule_mem_Icc n d q r o
  have hr := Real.sqrt_nonneg (10 * boundedEnvelope n d q r)
  change -1 ≤ max (-1) _ ∧ max (-1) _ ≤ _ ∧ _ ≤ min 1 _ ∧ min 1 _ ≤ 1
  refine ⟨le_max_left _ _, max_le hc.1 ?_, le_min hc.2 ?_, min_le_left _ _⟩
  · linarith
  · linarith
-- @realizes Izero(nonempty connected interval in [-1,1])
/-- [Validity certificate for the explicit seeded endpoints.](goal) -/
-- @node: upperIntervalProc_valid
lemma upperIntervalProc_valid (n d : ℕ) (q r : ℝ) :
    Measurable (fun x : Record V × ℝ => upperInterval n d q r x.1) ∧
    ∀ x : Record V × ℝ, -1 ≤ (upperInterval n d q r x.1).1 ∧
      (upperInterval n d q r x.1).1 ≤ (upperInterval n d q r x.1).2 ∧
      (upperInterval n d q r x.1).2 ≤ 1 := by
  constructor
  · fun_prop
  · intro x
    have h := upperInterval_order n d q r x.1
    exact ⟨h.1, h.2.1.trans h.2.2.1, h.2.2.2⟩
/-- The concrete seed-independent connected interval procedure. -/
def upperIntervalProc (n d : ℕ) (q r : ℝ) : IntervalProc V :=
  ⟨fun x => upperInterval n d q r x.1, upperIntervalProc_valid n d q r⟩
/-- The evaluated public squared-risk rate. -/
def rho (n d : ℕ) (q r : ℝ) : ℝ :=
  if 0 < q then min 1 ((d : ℝ)^2/n + d/(n*q) + r/q^2) else 1
-- @realizes rho(min{1,d²/n+d/(nq)+r/q²} for q>0, one at q=0)
/-- The independent honest-length rate. -/
def ell (n d : ℕ) (q r : ℝ) : ℝ := Real.sqrt (rho n d q r) -- @realizes ell(sqrt rho)
/-- The attaining estimator ignores the independent seed. -/
def Tstar (n d : ℕ) (q r : ℝ) : Estimator (Fin n) := upperEstimator n d q r
-- @realizes Tstar(Tstar(O,U)=Tzero(O))
/-- The attaining interval ignores the independent seed. -/
def Istar (n d : ℕ) (q r : ℝ) : IntervalProc (Fin n) := upperIntervalProc n d q r
-- @realizes Istar(Istar(O,U)=Izero(O))
/-- The rates and the two concrete attaining rules, without any inserted proved property. -/
-- @node: def:frontier-handle
def frontierHandle (n d : ℕ) (q r : ℝ) : (ℝ × ℝ) × (Estimator (Fin n) × IntervalProc (Fin n)) :=
  ((rho n d q r, ell n d q r), (Tstar n d q r, Istar n d q r))
/-- The absolute lower constant. -/
def cLower : ℝ := 1 / (10^10 * Real.pi^2) -- @realizes c(fixed universal constant 1/(10^10 π²))
/-- The absolute upper constant. -/
def CUpper : ℝ := 40 -- @realizes Cconstant(fixed universal upper constant forty)
/-- The fixed population cutoff. -/
def nZero : ℕ := 512 -- @realizes nzero(fixed universal cutoff 512)
/-- [The three constants satisfy their stated spaces.](goal) -/
-- @node: constants_valid
lemma constants_valid : 0 < cLower ∧ 0 < CUpper ∧ 4 ≤ nZero := by
  refine ⟨?_, ?_, ?_⟩
  · unfold cLower
    positivity
  · norm_num [CUpper]
  · norm_num [nZero]
/-- Admissibility along population-indexed public-parameter sequences. -/
def AdmissibleSequences (ds : ℕ → ℕ) (qs rs : ℕ → ℝ) : Prop :=
  ∀ n, 4 ≤ n → PopulationDomain n (ds n) ∧ ChannelDomain (qs n) (rs n)
/-- The extended degree cost. -/
def degRatio (n d : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ)^2/n)
/-- The missing-edge cost is infinite at q=0. -/
def missRatio (n d : ℕ) (q : ℝ) : ℝ≥0∞ :=
  if q = 0 then ⊤ else ENNReal.ofReal ((d : ℝ)/(n*q))
/-- The false-positive cost is infinite at q=0. -/
def falseRatio (q r : ℝ) : ℝ≥0∞ := if q = 0 then ⊤ else ENNReal.ofReal (r/q^2)

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr), [The stated rate is positive in the admitted finite-population regime.](goal) -/
-- @node: rho_pos
lemma rho_pos (n d : ℕ) (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n-1) (q r : ℝ)
    (hqr : ChannelDomain q r) : 0 < rho n d q r := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  unfold rho
  split_ifs with hq
  · apply lt_min (by norm_num)
    have hdeg : (0 : ℝ) < (d : ℝ)^2 / n := div_pos (sq_pos_of_pos hd') hn'
    have hmiss : (0 : ℝ) ≤ (d : ℝ) / (n*q) := le_of_lt (div_pos hd' (mul_pos hn' hq))
    have hfalse : (0 : ℝ) ≤ r / q^2 := div_nonneg hqr.1 (sq_nonneg q)
    linarith
  · norm_num
-- @realizes rho(positive evaluated rate for all admissible public parameters)
/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr), [The honest-length rate is positive in the same regime.](goal) -/
-- @node: ell_pos
lemma ell_pos (n d : ℕ) (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n-1) (q r : ℝ)
    (hqr : ChannelDomain q r) : 0 < ell n d q r := by
  exact Real.sqrt_pos.mpr (rho_pos n d hn hd hdu q r hqr)
-- @realizes ell(positive square-root rate for all admissible public parameters)

end CausalSmith.Experimentation.NoisygraphTtePrecision

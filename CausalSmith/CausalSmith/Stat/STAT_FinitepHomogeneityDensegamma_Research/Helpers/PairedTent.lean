module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.CopulaPriors
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Scales

/-! Finite-moment homogeneity testing: Helpers/PairedTent. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Tentrank: the displayed mathematical construction or bound. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def tentRank (n : ℕ) (v : Params) : ℕ := 2*Nat.ceil ((n:ℝ)^(2*qExp v/(2*v.γ+qExp v)))
/-- Tenth: the displayed mathematical construction or bound. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def tentH (n : ℕ) (v : Params) : ℝ := (tentRank n v:ℝ)⁻¹
/-- Tentrarity: the displayed mathematical construction or bound. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def tentRarity (n : ℕ) (v : Params) : ℝ := tentH n v^(v.γ/qExp v)
/-- Tentmagnitude: the displayed mathematical construction or bound. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def tentMagnitude (n : ℕ) (v : Params) : ℝ := tentH n v^(-v.γ/(v.p-1))
/-- Tenteffect: the displayed mathematical construction or bound. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the σ parameter](hyp:σ), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def tentEffect (n : ℕ) (v : Params) (σ : Fin (tentRank n v/2) → Bool) (x : unitInterval) : ℝ :=
  kappa0*tentH n v^v.γ*coarseTent (tentRank n v) σ x
/-- The paired-tent record table keeps control at zero and the treated three-point probabilities. The coordinate r gives treated masses ε(1 ± 2r)/2 at ±L and 1 − ε at zero. This statement assumes [the r parameter](hyp:r), [the ε parameter](hyp:ε), [the cat parameter](hyp:cat). [This is the stated defined object](goal). -/
def pairedTentTable (r ε : ℝ) (cat : Category) : ℝ :=
  if cat.1 then markedTable 0 r r ε cat
  else if cat.2.isNone then 1/2 else 0

/-- The paired-tent category probabilities are nonnegative on the valid construction domain. This statement assumes [the h condition](hyp:h). [This is the stated conclusion](goal). -/
lemma pairedTentTable_nonneg (r : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid (fun _ => 0) r r ε L) (x : unitInterval) (cat : Category) :
    0 ≤ pairedTentTable (r x) ε cat := by
  rcases cat with ⟨a, mark⟩
  cases a
  · cases mark <;> norm_num [pairedTentTable]
  · exact h.2.2.2.2.2.2 x (true,mark)

/-- Mix the paired-tent categories over the uniform covariate design. This statement assumes [the r parameter](hyp:r), [the ε parameter](hyp:ε), [the L parameter](hyp:L). [This is the stated defined object](goal). -/
def pairedTentRecordLaw (r : unitInterval → ℝ) (ε L : ℝ) : Measure Record :=
  design.bind (fun x => ∑ cat : Category,
    ENNReal.ofReal (pairedTentTable (r x) ε cat) •
      Measure.dirac (x,cat.1,markValue L cat.2))

/-- The treated row is unchanged; the control kernel is identically the point mass at zero. This statement assumes [the r parameter](hyp:r), [the ε parameter](hyp:ε), [the L parameter](hyp:L), [the h parameter](hyp:h), [the a parameter](hyp:a). [This is the stated defined object](goal). -/
def pairedTentArm (r : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid (fun _ => 0) r r ε L) (a : Bool) : Kernel unitInterval ℝ :=
  if a then tableArm (fun _ => 0) r r ε L h true
  else Kernel.const unitInterval (Measure.dirac (0:ℝ))

/-- Both paired-tent arms are normalized probability kernels. This statement assumes [the h condition](hyp:h). [This is the stated conclusion](goal). -/
lemma pairedTentArm_markov (r : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid (fun _ => 0) r r ε L) : ∀ a, IsMarkovKernel (pairedTentArm r ε L h a) := by
  intro a
  cases a
  · dsimp [pairedTentArm]; infer_instance
  · exact tableArm_markov _ _ _ _ _ h true

/-- The paired-tent table is Borel in the covariate. This statement assumes [the h condition](hyp:h). [This is the stated conclusion](goal). -/
@[fun_prop] lemma measurable_pairedTent_record_atoms (r : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid (fun _ => 0) r r ε L) :
    Measurable (fun x => ∑ cat : Category,
      ENNReal.ofReal (pairedTentTable (r x) ε cat) •
        Measure.dirac (x,cat.1,markValue L cat.2)) := by
  have hr := h.2.1.measurable
  apply Finset.measurable_sum
  intro cat _
  rcases cat with ⟨a, mark⟩
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul]
  apply Measurable.mul
  · cases a <;> cases mark <;> simp [pairedTentTable, markedTable] <;> fun_prop
  · exact (Measure.measurable_coe hs).comp
      (Measure.measurable_dirac.comp (measurable_id.prodMk measurable_const))

/-- Mixing the deterministic control atom and the normalized treated row recovers the paired table. This statement assumes [the h condition](hyp:h). [This is the stated conclusion](goal). -/
-- @node: pairedTent_recordMeasure
lemma pairedTent_recordMeasure (r : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid (fun _ => 0) r r ε L) (x : unitInterval) :
    recordMeasure (tableProp (fun _ => 0)) (pairedTentArm r ε L h) x =
      ∑ cat : Category, ENNReal.ofReal (pairedTentTable (r x) ε cat) •
        Measure.dirac (cat.1,markValue L cat.2) := by
  letI : IsMarkovKernel (tableArm (fun _ => 0) r r ε L h true) :=
    tableArm_markov _ _ _ _ _ h true
  have hp : (Measure.dirac true).prod (tableArm (fun _ => 0) r r ε L h true x) =
      ∑ mark : Option Bool, ENNReal.ofReal
        (2*markedTable 0 (r x) (r x) ε (true,mark)/(1+signVal true*0)) •
        Measure.dirac (true,markValue L mark) := by
    rw [Measure.dirac_prod]
    change (tableArmMeasure (fun _ => 0) r r ε L true x).map (Prod.mk true) = _
    simp only [tableArmMeasure, Fintype.sum_option, Fintype.sum_bool]
    simp [Measure.map_add _ _ measurable_prodMk_left, Measure.map_smul, Measure.map_dirac]
  simp only [recordMeasure, pairedTentArm, Bool.false_eq_true, if_true, if_false, Kernel.const_apply]
  rw [hp, Measure.dirac_prod_dirac]
  have hw (mark : Option Bool) :
      ENNReal.ofReal (tableProp (fun _ => 0) x) *
        ENNReal.ofReal (2*markedTable 0 (r x) (r x) ε (true,mark)/(1+signVal true*0)) =
      ENNReal.ofReal (markedTable 0 (r x) (r x) ε (true,mark)) := by
    simpa [tableProp, signVal] using table_row_weight_cancel (fun _ => 0) r r ε L h true x mark
  simp only [Finset.smul_sum, smul_smul, hw]
  simp [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_option,
    pairedTentTable, tableProp, markValue, add_comm]
  norm_num
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The category law equals the composition with the deterministic control and treated kernels. This statement assumes [the h condition](hyp:h). [This is the stated conclusion](goal). -/
-- @node: pairedTentRecordLaw_eq_compProd
lemma pairedTentRecordLaw_eq_compProd (r : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid (fun _ => 0) r r ε L) :
    pairedTentRecordLaw r ε L = design ⊗ₘ recordKernel (tableProp (fun _ => 0))
      (measurable_tableProp (fun _ => 0) r r ε L h) (pairedTentArm r ε L h) := by
  letI : IsProbabilityMeasure design := by
    change IsProbabilityMeasure (volume : Measure unitInterval)
    infer_instance
  letI : IsMarkovKernel (recordKernel (tableProp (fun _ => 0))
      (measurable_tableProp (fun _ => 0) r r ε L h) (pairedTentArm r ε L h)) :=
    recordKernel_markov _ _ _ (by intro x; norm_num [tableProp])
      (pairedTentArm_markov r ε L h)
  ext s hs
  rw [pairedTentRecordLaw,
    Measure.bind_apply hs (measurable_pairedTent_record_atoms r ε L h).aemeasurable,
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  change _ = recordMeasure (tableProp (fun _ => 0)) (pairedTentArm r ε L h) x
    (Prod.mk x ⁻¹' s)
  rw [pairedTent_recordMeasure]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro cat _
  rw [Measure.dirac_apply' _ hs,
    Measure.dirac_apply' _ (hs.preimage measurable_prodMk_left)]
  rfl

/-- The literal paired-tent law has the same continuous means as the treated-row table. This statement assumes [the h condition](hyp:h). [This is the stated conclusion](goal). -/
lemma pairedTent_certificate (r : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid (fun _ => 0) r r ε L) :
    IsProbabilityMeasure (pairedTentRecordLaw r ε L) ∧ Continuous (tableProp (fun _ => 0)) ∧
    (∀ x, 0 ≤ tableProp (fun _ => 0) x ∧ tableProp (fun _ => 0) x ≤ 1) ∧
    (∀ a, IsMarkovKernel (pairedTentArm r ε L h a)) ∧
    Continuous (tableM0 (fun _ => 0) r r ε L) ∧ Continuous (tableTau (fun _ => 0) r r ε L) ∧
    pairedTentRecordLaw r ε L = ((pairedTentRecordLaw r ε L).map X) ⊗ₘ
      recordKernel (tableProp (fun _ => 0))
        (measurable_tableProp (fun _ => 0) r r ε L h) (pairedTentArm r ε L h) ∧
    (∀ᵐ x ∂design, tableM0 (fun _ => 0) r r ε L x = ∫ y, y ∂pairedTentArm r ε L h false x) ∧
    (∀ᵐ x ∂design, tableM0 (fun _ => 0) r r ε L x + tableTau (fun _ => 0) r r ε L x =
      ∫ y, y ∂pairedTentArm r ε L h true x) := by
  have cert := table_certificate (fun _ => 0) r r ε L h
  let κ := recordKernel (tableProp (fun _ => 0))
    (measurable_tableProp (fun _ => 0) r r ε L h) (pairedTentArm r ε L h)
  haveI : IsMarkovKernel κ := recordKernel_markov _ _ _ cert.2.2.1 (pairedTentArm_markov r ε L h)
  haveI : IsProbabilityMeasure design := by
    change IsProbabilityMeasure (volume : Measure unitInterval)
    infer_instance
  refine ⟨?_, cert.2.1, cert.2.2.1, pairedTentArm_markov r ε L h,
    cert.2.2.2.2.1, cert.2.2.2.2.2.1, ?_, ?_, ?_⟩
  · rw [pairedTentRecordLaw_eq_compProd r ε L h]
    change IsProbabilityMeasure (design ⊗ₘ κ)
    infer_instance
  · have hmap : (pairedTentRecordLaw r ε L).map X = design := by
      rw [pairedTentRecordLaw_eq_compProd r ε L h]
      exact Measure.fst_compProd design κ
    rw [hmap]
    exact pairedTentRecordLaw_eq_compProd r ε L h
  · filter_upwards [] with x
    simp [pairedTentArm, tableM0]
  · simpa only [pairedTentArm, if_true] using cert.2.2.2.2.2.2.2.2

/-- Literal paired-tent constructor, with the same fixed law on invalid inputs. This statement assumes [the r parameter](hyp:r), [the ε parameter](hyp:ε), [the L parameter](hyp:L). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. -/
def pairedTentObservedLaw (r : unitInterval → ℝ) (ε L : ℝ) : ObservedLaw :=
  if h : TableValid (fun _ => 0) r r ε L then
    let cert := pairedTent_certificate r ε L h
    { P := pairedTentRecordLaw r ε L
      probability := cert.1
      e := ⟨tableProp (fun _ => 0),cert.2.1⟩
      e_range := cert.2.2.1
      Q := pairedTentArm r ε L h
      markov := cert.2.2.2.1
      m0 := ⟨tableM0 (fun _ => 0) r r ε L,cert.2.2.2.2.1⟩
      tau := ⟨tableTau (fun _ => 0) r r ε L,cert.2.2.2.2.2.1⟩
      record_version := cert.2.2.2.2.2.2.1
      mean0_version := cert.2.2.2.2.2.2.2.1
      mean1_version := cert.2.2.2.2.2.2.2.2 }
  else referenceLaw

/-- The paired-tent law has deterministic zero control and the specified treated three-point law. This statement assumes [the ν parameter](hyp:ν), [the n parameter](hyp:n), [the v parameter](hyp:v), [the σ parameter](hyp:σ). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. [Defining clause 3](step:3) is used. [Defining clause 4](step:4) is used. -/
def tentLaw (ν : Bool) (n : ℕ) (v : Params) (σ : Fin (tentRank n v/2) → Bool) : ObservedLaw :=
  let ε := tentRarity n v
  let L := tentMagnitude n v
  let δ := fun x => if ν then tentEffect n v σ x else 0
  pairedTentObservedLaw (fun x => δ x/(2*ε*L)) ε L
/-- Signed binary law realizing a continuous mean triple. This statement assumes [the m parameter](hyp:m), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def binaryArmMeasure (m : Nuisance) (x : unitInterval) : Measure ℝ :=
  ENNReal.ofReal ((1+m x)/2) • Measure.dirac (1:ℝ)+ENNReal.ofReal ((1-m x)/2) • Measure.dirac (-1:ℝ)
/-- The explicit binaryArm construction is Borel measurable. [This is the stated conclusion](goal). -/
-- @node: measurable_binaryArm
@[fun_prop] lemma measurable_binaryArm (m : Nuisance) : Measurable (binaryArmMeasure m) := by
  unfold binaryArmMeasure
  fun_prop
/-- Binaryarm: the displayed mathematical construction or bound. This statement assumes [the m parameter](hyp:m). [This is the stated defined object](goal). -/
def binaryArm (m : Nuisance) : Kernel unitInterval ℝ := ⟨binaryArmMeasure m,measurable_binaryArm m⟩
/-- The two sign probabilities sum to one when the prescribed mean lies in the unit interval. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: binaryArm_markov
lemma binaryArm_markov (m : Nuisance) (hm : ∀ x, |m x| ≤ 1) : IsMarkovKernel (binaryArm m) := by
  constructor
  intro x
  constructor
  have hx := abs_le.mp (hm x)
  change (binaryArmMeasure m x) Set.univ = 1
  simp only [binaryArmMeasure, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith : 0 ≤ (1+m x)/2)
    (by linarith : 0 ≤ (1-m x)/2)]
  convert ENNReal.ofReal_one using 1 <;> congr 1 <;> ring

/-- Integrating the signed binary kernel recovers its prescribed conditional mean. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: binaryArm_mean
lemma binaryArm_mean (m : Nuisance) (hm : ∀ x, |m x| ≤ 1) (x : unitInterval) :
    (∫ y, y ∂binaryArm m x) = m x := by
  have hx := abs_le.mp (hm x)
  change (∫ y, y ∂binaryArmMeasure m x) = m x
  rw [binaryArmMeasure, integral_add_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ (1+m x)/2),
      ENNReal.toReal_ofReal (by linarith : 0 ≤ (1-m x)/2)]
    ring
  · exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

/-- The literal finite-kernel constructor has normalized probability laws and the stated original conditional means. This statement assumes [the he condition](hyp:he), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: binary_certificate
lemma binary_certificate (e m0 τ : Nuisance) (he : ∀ x, 0 ≤ e x ∧ e x ≤ 1)
    (hm : ∀ x, |m0 x| ≤ 1 ∧ |m0 x+τ x| ≤ 1) :
    IsProbabilityMeasure (design ⊗ₘ recordKernel e e.continuous.measurable (fun a => binaryArm (if a then m0+τ else m0))) ∧
    (∀ a : Bool, IsMarkovKernel (binaryArm (if a then m0+τ else m0))) ∧
    (design ⊗ₘ recordKernel e e.continuous.measurable (fun a => binaryArm (if a then m0+τ else m0))) =
      ((design ⊗ₘ recordKernel e e.continuous.measurable (fun a => binaryArm (if a then m0+τ else m0))).map X) ⊗ₘ recordKernel e e.continuous.measurable (fun a => binaryArm (if a then m0+τ else m0)) ∧
    (∀ᵐ x ∂design, m0 x = ∫ y, y ∂binaryArm m0 x) ∧
    (∀ᵐ x ∂design, m0 x+τ x = ∫ y, y ∂binaryArm (m0+τ) x) := by
  have hm0 : ∀ x, |m0 x| ≤ 1 := fun x => (hm x).1
  have hm1 : ∀ x, |(m0+τ) x| ≤ 1 := fun x => (hm x).2
  let Q : Bool → Kernel unitInterval ℝ := fun a => binaryArm (if a then m0+τ else m0)
  have hQ : ∀ a, IsMarkovKernel (Q a) := by
    intro a
    cases a
    · exact binaryArm_markov m0 hm0
    · exact binaryArm_markov (m0+τ) hm1
  let κ := recordKernel e e.continuous.measurable Q
  letI : IsMarkovKernel κ := recordKernel_markov _ _ _ he hQ
  letI : IsProbabilityMeasure design := by
    change IsProbabilityMeasure (volume : Measure unitInterval)
    infer_instance
  refine ⟨?_, hQ, ?_, ?_, ?_⟩
  · change IsProbabilityMeasure (design ⊗ₘ κ)
    infer_instance
  · have hmap : (design ⊗ₘ κ).map X = design := Measure.fst_compProd design κ
    change design ⊗ₘ κ = ((design ⊗ₘ κ).map X) ⊗ₘ κ
    rw [hmap]
  · filter_upwards [] with x
    exact (binaryArm_mean m0 hm0 x).symm
  · filter_upwards [] with x
    exact (binaryArm_mean (m0+τ) hm1 x).symm

/-- Binaryrealization: the displayed mathematical construction or bound. This statement assumes [the e parameter](hyp:e), [the m0 parameter](hyp:m0), [the τ parameter](hyp:τ). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. -/
def binaryRealization (e m0 τ : Nuisance) : ObservedLaw :=
  if h : (∀ x, 0 ≤ e x ∧ e x ≤ 1) ∧ (∀ x, |m0 x| ≤ 1 ∧ |m0 x+τ x| ≤ 1) then
    let cert := binary_certificate e m0 τ h.1 h.2
    { P := design ⊗ₘ recordKernel e e.continuous.measurable (fun a => binaryArm (if a then m0+τ else m0))
      probability := cert.1
      e := e
      e_range := h.1
      Q := fun a => binaryArm (if a then m0+τ else m0)
      markov := cert.2.1
      m0 := m0
      tau := τ
      record_version := cert.2.2.1
      mean0_version := cert.2.2.2.1
      mean1_version := cert.2.2.2.2 }
  else referenceLaw
/-- The compactly supported tent is the positive part of its two affine slopes. [This is the stated conclusion](goal). -/
-- @node: tentBase_eq_max_min
lemma tentBase_eq_max_min (t : ℝ) : tentBase t = max 0 (2*min t (1-t)) := by
  unfold tentBase
  by_cases h : 0 ≤ t ∧ t ≤ 1
  · rw [if_pos h, max_eq_right]
    exact mul_nonneg (by norm_num) (le_min h.1 (sub_nonneg.mpr h.2))
  · rw [if_neg h, max_eq_left]
    by_cases ht : t < 0
    · exact le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
        (by linarith)
    · have ht1 : 1 < t := lt_of_not_ge (fun hle => h ⟨le_of_not_gt ht, hle⟩)
      exact le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
        (by linarith)

/-- The compactly supported piecewise affine tent is continuous, including both endpoints. [This is the stated conclusion](goal). -/
-- @node: continuous_tentBase
@[fun_prop] lemma continuous_tentBase : Continuous tentBase := by
  simp_rw [show tentBase = (fun t : ℝ => max 0 (2*min t (1-t))) from
    funext tentBase_eq_max_min]
  fun_prop

/-- Every finite signed sum of paired coarse tents is continuous. [This is the stated conclusion](goal). -/
-- @node: continuous_coarseTent
@[fun_prop] lemma continuous_coarseTent (M : ℕ) (σ : Fin (M/2) → Bool) :
    Continuous (coarseTent M σ) := by
  unfold coarseTent
  fun_prop

/-- The specified finite construction is continuous on its covariate domain. [This is the stated conclusion](goal). -/
-- @node: continuous_tentEffect
@[fun_prop] lemma continuous_tentEffect (n : ℕ) (v : Params) (σ : Fin (tentRank n v/2) → Bool) : Continuous (tentEffect n v σ) := by
  unfold tentEffect
  fun_prop
/-- Binarytentlaw: the displayed mathematical construction or bound. This statement assumes [the ν parameter](hyp:ν), [the n parameter](hyp:n), [the w parameter](hyp:w), [the σ parameter](hyp:σ). [This is the stated defined object](goal). -/
def binaryTentLaw (ν : Bool) (n : ℕ) (w : Smooth3) (σ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) : ObservedLaw :=
  binaryRealization (ContinuousMap.const unitInterval (1/2)) 0
    (if ν then ⟨tentEffect n (Params.ofBounded w) σ,continuous_tentEffect n (Params.ofBounded w) σ⟩ else 0)
/-- Tentprior: the displayed mathematical construction or bound. This statement assumes [the ν parameter](hyp:ν), [the n parameter](hyp:n), [the v parameter](hyp:v). [This is the stated defined object](goal). -/
def tentPrior (ν : Bool) (n : ℕ) (v : Params) : FinitePrior :=
  finitePriorOf (fun _ : Fin (tentRank n v/2) → Bool => (2:ℝ)^(-(tentRank n v/2:ℤ))) (tentLaw ν n v)
/-- Binarytentprior: the displayed mathematical construction or bound. This statement assumes [the ν parameter](hyp:ν), [the n parameter](hyp:n), [the w parameter](hyp:w). [This is the stated defined object](goal). -/
def binaryTentPrior (ν : Bool) (n : ℕ) (w : Smooth3) : FinitePrior :=
  finitePriorOf (fun _ : Fin (tentRank n (Params.ofBounded w)/2) → Bool => (2:ℝ)^(-(tentRank n (Params.ofBounded w)/2:ℤ))) (binaryTentLaw ν n w)

end CausalSmith.Stat.FinitepHomogeneityDensegamma

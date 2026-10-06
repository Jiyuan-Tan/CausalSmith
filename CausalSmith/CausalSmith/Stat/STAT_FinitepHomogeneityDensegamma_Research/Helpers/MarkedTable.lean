module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Basic
public import Causalean.Stat.Minimax.Mixture.FiniteCells

/-! Finite-moment homogeneity testing: Helpers/MarkedTable. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


-- @env: S5
variable (ε L : ℝ) -- @realizes epsilon(0<epsilon<1 on table domain) @realizes Lmark(positive mark magnitude on table domain)
/-- Boolean signs represent the two values minus one and one. This statement assumes [the a parameter](hyp:a). [This is the stated defined object](goal). -/
def signVal (a : Bool) : ℝ := if a then 1 else -1 -- @realizes treatmentSign(binary sign ±1) @realizes markSign(binary sign ±1)
/-- The six original mark categories retain both treatments and the zero or signed outcome mark. [This is the stated defined object](goal). -/
abbrev Category := Bool × Option Bool
/-- [Normalized full-record probability-table tool](goal). \[\begin{aligned}\mathsf T\bigl(A=(1+\ell)/2,Y=hL\mid X=x\bigr)&=\frac{\varepsilon}{4}(1+\ell\xi+h\upsilon+\ell h\zeta),\\ \mathsf T\bigl(A=(1+\ell)/2,Y=0\mid X=x\bigr)&=\frac{1-\varepsilon}{2}(1+\ell\xi),\qquad (\ell,h)\in\{-1,1\}^2.\end{aligned}\] Inputs \(\xi,\upsilon,\zeta\) may be Borel functions of the covariate; this table is evaluated on inputs making its displayed probabilities nonnegative. Retain all six record categories in likelihood products. This statement assumes [the ξ parameter](hyp:ξ), [the υ parameter](hyp:υ), [the ζ parameter](hyp:ζ), [the ε parameter](hyp:ε), [the cat parameter](hyp:cat). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. -/
-- @node: def:marked-table
def markedTable (ξ υ ζ ε : ℝ) (cat : Category) : ℝ :=
  match cat.2 with
  | some h => ε/4*(1+signVal cat.1*ξ+signVal h*υ+signVal cat.1*signVal h*ζ)
  | none => (1-ε)/2*(1+signVal cat.1*ξ) -- @realizes Cone(all six normalized categories)
/-- A missing sign denotes zero; a present sign selects the positive or negative mark magnitude. This statement assumes [the L parameter](hyp:L), [the h parameter](hyp:h). [This is the stated defined object](goal). -/
def markValue (L : ℝ) (h : Option Bool) : ℝ := match h with | none => 0 | some h => signVal h*L
/-- Mix all six conditional record categories over the uniform covariate design. This statement assumes [the ξ parameter](hyp:ξ), [the υ parameter](hyp:υ), [the ζ parameter](hyp:ζ), [the ε parameter](hyp:ε), [the L parameter](hyp:L). [This is the stated defined object](goal). -/
def tableLaw (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ) : Measure Record :=
  design.bind (fun x => ∑ cat : Category, ENNReal.ofReal (markedTable (ξ x) (υ x) (ζ x) ε cat) • Measure.dirac (x,cat.1,markValue L cat.2))
/-- Normalize each treatment row of the six-category table to obtain its conditional outcome law. This statement assumes [the ξ parameter](hyp:ξ), [the υ parameter](hyp:υ), [the ζ parameter](hyp:ζ), [the ε parameter](hyp:ε), [the L parameter](hyp:L), [the a parameter](hyp:a), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def tableArmMeasure (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ) (a : Bool) (x : unitInterval) : Measure ℝ :=
  ∑ h : Option Bool, ENNReal.ofReal (2*markedTable (ξ x) (υ x) (ζ x) ε (a,h)/(1+signVal a*ξ x)) • Measure.dirac (markValue L h)
/-- The table constructor requires continuous coordinates, interior propensity coordinates, positive rarity and magnitude, and nonnegative category probabilities. This statement assumes [the ξ parameter](hyp:ξ), [the υ parameter](hyp:υ), [the ζ parameter](hyp:ζ), [the ε parameter](hyp:ε), [the L parameter](hyp:L). [This is the stated defined object](goal). -/
def TableValid (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ) : Prop :=
  Continuous ξ ∧ -- @realizes xi(continuous/Borel coordinate carrier)
  Continuous υ ∧ -- @realizes upsilon(real continuous coordinate carrier)
  Continuous ζ ∧ -- @realizes zeta(real continuous coordinate carrier)
  (∀ x, |ξ x| < 1) ∧ -- @realizes xi(range (-1,1))
  (0 < ε ∧ ε < 1) ∧ -- @realizes epsilon(probability range)
  0 < L ∧ -- @realizes Lmark(positive range)
  ∀ x cat, 0 ≤ markedTable (ξ x) (υ x) (ζ x) ε cat
/-- The explicit tableArm construction is Borel measurable. [This is the stated conclusion](goal). -/
-- @node: measurable_tableArm
@[fun_prop] lemma measurable_tableArm (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid ξ υ ζ ε L) (a : Bool) : Measurable (tableArmMeasure ξ υ ζ ε L a) := by
  have hξ := h.1.measurable
  have hυ := h.2.1.measurable
  have hζ := h.2.2.1.measurable
  unfold tableArmMeasure
  apply Finset.measurable_sum
  intro mark _
  cases mark <;> simp only [markedTable] <;> fun_prop
/-- The explicit treatment-row measures form a Borel outcome kernel. This statement assumes [the ξ parameter](hyp:ξ), [the υ parameter](hyp:υ), [the ζ parameter](hyp:ζ), [the ε parameter](hyp:ε), [the L parameter](hyp:L), [the h parameter](hyp:h), [the a parameter](hyp:a). [This is the stated defined object](goal). -/
def tableArm (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ) (h : TableValid ξ υ ζ ε L) (a : Bool) : Kernel unitInterval ℝ :=
  ⟨tableArmMeasure ξ υ ζ ε L a,measurable_tableArm ξ υ ζ ε L h a⟩
/-- The treatment probability equals one half of one plus the propensity coordinate. This statement assumes [the ξ parameter](hyp:ξ), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def tableProp (ξ : unitInterval → ℝ) (x : unitInterval) : ℝ := (1+ξ x)/2
/-- The control mean is the normalized signed control-row mark average. This statement assumes [the ξ parameter](hyp:ξ), [the υ parameter](hyp:υ), [the ζ parameter](hyp:ζ), [the ε parameter](hyp:ε), [the L parameter](hyp:L), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def tableM0 (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ) (x : unitInterval) : ℝ := ε*L*(υ x-ζ x)/(1-ξ x)
/-- The original effect is the exact difference of the two normalized treatment-row means. This statement assumes [the ξ parameter](hyp:ξ), [the υ parameter](hyp:υ), [the ζ parameter](hyp:ζ), [the ε parameter](hyp:ε), [the L parameter](hyp:L), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def tableTau (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ) (x : unitInterval) : ℝ := 2*ε*L*(ζ x-ξ x*υ x)/(1-ξ x^2)
/-- The explicit tableProp construction is Borel measurable. [This is the stated conclusion](goal). -/
-- @node: measurable_tableProp
@[fun_prop] lemma measurable_tableProp (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ) (h : TableValid ξ υ ζ ε L) : Measurable (tableProp ξ) := by
  have hξ := h.1.measurable
  unfold tableProp
  fun_prop
/-- Summing the three outcome categories recovers the treatment-row mass. [This is the stated conclusion](goal). -/
-- @node: markedTable_row_sum
lemma markedTable_row_sum (ξ υ ζ ε : ℝ) (a : Bool) :
    ∑ h : Option Bool, markedTable ξ υ ζ ε (a,h) = (1+signVal a*ξ)/2 := by
  cases a <;> simp [markedTable, signVal, Fintype.sum_option, Fintype.sum_bool] <;> ring

/-- Interior propensity coordinates make both treatment-row denominators positive. [This is the stated conclusion](goal). -/
-- @node: table_row_den_pos
lemma table_row_den_pos (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid ξ υ ζ ε L) (a : Bool) (x : unitInterval) :
    0 < 1+signVal a*ξ x := by
  have hx := abs_lt.mp (h.2.2.2.1 x)
  cases a <;> simp [signVal] <;> linarith

/-- The normalized finite treatment rows are probability kernels. [This is the stated conclusion](goal). -/
-- @node: tableArm_markov
lemma tableArm_markov (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid ξ υ ζ ε L) (a : Bool) : IsMarkovKernel (tableArm ξ υ ζ ε L h a) := by
  constructor
  intro x
  constructor
  have hd := table_row_den_pos ξ υ ζ ε L h a x
  have hw (mark : Option Bool) : 0 ≤ 2*markedTable (ξ x) (υ x) (ζ x) ε (a,mark)/(1+signVal a*ξ x) :=
    div_nonneg (mul_nonneg (by norm_num) (h.2.2.2.2.2.2 x (a,mark))) hd.le
  change (tableArmMeasure ξ υ ζ ε L a x) Set.univ = 1
  simp only [tableArmMeasure, Measure.finsetSum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i)]
  have hsum : ∑ mark : Option Bool, 2*markedTable (ξ x) (υ x) (ζ x) ε (a,mark)/(1+signVal a*ξ x) = 1 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, markedTable_row_sum]
    field_simp
  rw [hsum, ENNReal.ofReal_one]

/-- Integrating the finite normalized treatment row gives its signed mark mean. [This is the stated conclusion](goal). -/
-- @node: tableArm_mean
lemma tableArm_mean (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid ξ υ ζ ε L) (a : Bool) (x : unitInterval) :
    (∫ y, y ∂tableArm ξ υ ζ ε L h a x) =
      ε*L*(υ x+signVal a*ζ x)/(1+signVal a*ξ x) := by
  have hd := table_row_den_pos ξ υ ζ ε L h a x
  have hw (mark : Option Bool) : 0 ≤ 2*markedTable (ξ x) (υ x) (ζ x) ε (a,mark)/(1+signVal a*ξ x) :=
    div_nonneg (mul_nonneg (by norm_num) (h.2.2.2.2.2.2 x (a,mark))) hd.le
  change (∫ y, y ∂tableArmMeasure ξ υ ζ ε L a x) = _
  rw [tableArmMeasure, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw _), smul_eq_mul]
    cases a <;> simp [Fintype.sum_option, Fintype.sum_bool, markedTable, markValue, signVal] <;> ring
  · intro mark _
    exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

/-- Multiplying a normalized row weight by its treatment probability restores the table entry. [This is the stated conclusion](goal). -/
-- @node: table_row_weight_cancel
lemma table_row_weight_cancel (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid ξ υ ζ ε L) (a : Bool) (x : unitInterval) (mark : Option Bool) :
    ENNReal.ofReal ((1+signVal a*ξ x)/2) *
      ENNReal.ofReal (2*markedTable (ξ x) (υ x) (ζ x) ε (a,mark)/(1+signVal a*ξ x)) =
      ENNReal.ofReal (markedTable (ξ x) (υ x) (ζ x) ε (a,mark)) := by
  have hd := table_row_den_pos ξ υ ζ ε L h a x
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- The mixture of normalized treatment rows equals the six original category atoms. [This is the stated conclusion](goal). -/
-- @node: table_recordMeasure
lemma table_recordMeasure (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid ξ υ ζ ε L) (x : unitInterval) :
    recordMeasure (tableProp ξ) (tableArm ξ υ ζ ε L h) x =
      ∑ cat : Category, ENNReal.ofReal (markedTable (ξ x) (υ x) (ζ x) ε cat) •
        Measure.dirac (cat.1,markValue L cat.2) := by
  letI (a : Bool) : IsMarkovKernel (tableArm ξ υ ζ ε L h a) := tableArm_markov ξ υ ζ ε L h a
  have hp (a : Bool) : (Measure.dirac a).prod (tableArm ξ υ ζ ε L h a x) =
      ∑ mark : Option Bool, ENNReal.ofReal
        (2*markedTable (ξ x) (υ x) (ζ x) ε (a,mark)/(1+signVal a*ξ x)) •
        Measure.dirac (a,markValue L mark) := by
    rw [Measure.dirac_prod]
    change (tableArmMeasure ξ υ ζ ε L a x).map (Prod.mk a) = _
    simp only [tableArmMeasure, Fintype.sum_option, Fintype.sum_bool]
    simp [Measure.map_add _ _ measurable_prodMk_left, Measure.map_smul, Measure.map_dirac]
  rw [recordMeasure, hp true, hp false]
  have hfalse : 1-tableProp ξ x = (1+signVal false*ξ x)/2 := by
    simp [tableProp, signVal]; ring
  have htrue : tableProp ξ x = (1+signVal true*ξ x)/2 := by simp [tableProp, signVal]
  rw [hfalse, htrue]
  simp only [Finset.smul_sum, smul_smul, table_row_weight_cancel ξ υ ζ ε L h]
  simp [Fintype.sum_prod_type, Fintype.sum_bool, add_comm]

/-- Mixing normalized arm kernels with a probability-valued propensity gives a Markov record kernel. This statement assumes [the he condition](hyp:he), [the he_range condition](hyp:he_range), [the hQ condition](hyp:hQ). [This is the stated conclusion](goal). -/
-- @node: recordKernel_markov
lemma recordKernel_markov (e : unitInterval → ℝ) (he : Measurable e)
    (Q : Bool → Kernel unitInterval ℝ) (he_range : ∀ x, 0 ≤ e x ∧ e x ≤ 1)
    (hQ : ∀ a, IsMarkovKernel (Q a)) : IsMarkovKernel (recordKernel e he Q) := by
  letI : ∀ a, IsMarkovKernel (Q a) := hQ
  constructor
  intro x
  constructor
  change (recordMeasure e Q x) Set.univ = 1
  simp only [recordMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.prod_prod, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (he_range x).1 (sub_nonneg.mpr (he_range x).2)]
  norm_num

/-- The original six-atom record mixture is Borel in its covariate. [This is the stated conclusion](goal). -/
-- @node: measurable_table_record_atoms
@[fun_prop] lemma measurable_table_record_atoms (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid ξ υ ζ ε L) :
    Measurable (fun x => ∑ cat : Category, ENNReal.ofReal (markedTable (ξ x) (υ x) (ζ x) ε cat) •
      Measure.dirac (x,cat.1,markValue L cat.2)) := by
  have hξ := h.1.measurable
  have hυ := h.2.1.measurable
  have hζ := h.2.2.1.measurable
  apply Finset.measurable_sum
  intro cat _
  rcases cat with ⟨a, mark⟩
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul]
  apply Measurable.mul
  · cases mark <;> simp only [markedTable] <;> fun_prop
  · exact (Measure.measurable_coe hs).comp
      (Measure.measurable_dirac.comp (measurable_id.prodMk measurable_const))

/-- The original category mixture equals the uniform-design composition with its normalized arm kernels. [This is the stated conclusion](goal). -/
-- @node: tableLaw_eq_compProd
lemma tableLaw_eq_compProd (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ)
    (h : TableValid ξ υ ζ ε L) :
    tableLaw ξ υ ζ ε L = design ⊗ₘ recordKernel (tableProp ξ)
      (measurable_tableProp ξ υ ζ ε L h) (tableArm ξ υ ζ ε L h) := by
  have he : ∀ x, 0 ≤ tableProp ξ x ∧ tableProp ξ x ≤ 1 := by
    intro x
    have hx := abs_lt.mp (h.2.2.2.1 x)
    dsimp [tableProp]
    constructor <;> linarith
  letI : IsProbabilityMeasure design := by
    change IsProbabilityMeasure (volume : Measure unitInterval)
    infer_instance
  letI : IsMarkovKernel (recordKernel (tableProp ξ) (measurable_tableProp ξ υ ζ ε L h)
      (tableArm ξ υ ζ ε L h)) :=
    recordKernel_markov _ _ _ he (tableArm_markov ξ υ ζ ε L h)
  ext s hs
  rw [tableLaw, Measure.bind_apply hs (measurable_table_record_atoms ξ υ ζ ε L h).aemeasurable,
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  change _ = recordMeasure (tableProp ξ) (tableArm ξ υ ζ ε L h) x (Prod.mk x ⁻¹' s)
  rw [table_recordMeasure]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro cat _
  rw [Measure.dirac_apply' _ hs, Measure.dirac_apply' _ (hs.preimage measurable_prodMk_left)]
  rfl

/-- The literal finite-kernel constructor has normalized probability laws and the stated original conditional means. [This is the stated conclusion](goal). -/
-- @node: table_certificate
lemma table_certificate (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ) (h : TableValid ξ υ ζ ε L) :
    IsProbabilityMeasure (tableLaw ξ υ ζ ε L) ∧ Continuous (tableProp ξ) ∧
    (∀ x, 0 ≤ tableProp ξ x ∧ tableProp ξ x ≤ 1) ∧
    (∀ a, IsMarkovKernel (tableArm ξ υ ζ ε L h a)) ∧
    Continuous (tableM0 ξ υ ζ ε L) ∧ Continuous (tableTau ξ υ ζ ε L) ∧
    tableLaw ξ υ ζ ε L = ((tableLaw ξ υ ζ ε L).map X) ⊗ₘ recordKernel (tableProp ξ) (measurable_tableProp ξ υ ζ ε L h) (tableArm ξ υ ζ ε L h) ∧
    (∀ᵐ x ∂design, tableM0 ξ υ ζ ε L x = ∫ y, y ∂tableArm ξ υ ζ ε L h false x) ∧
    (∀ᵐ x ∂design, tableM0 ξ υ ζ ε L x+tableTau ξ υ ζ ε L x = ∫ y, y ∂tableArm ξ υ ζ ε L h true x) := by
  have he : ∀ x, 0 ≤ tableProp ξ x ∧ tableProp ξ x ≤ 1 := by
    intro x
    have hx := abs_lt.mp (h.2.2.2.1 x)
    dsimp [tableProp]
    constructor <;> linarith
  have hd0 (x : unitInterval) : 1-ξ x ≠ 0 := by
    have hx := abs_lt.mp (h.2.2.2.1 x)
    linarith
  have hd1 (x : unitInterval) : 1+ξ x ≠ 0 := by
    have hx := abs_lt.mp (h.2.2.2.1 x)
    linarith
  have hd2 (x : unitInterval) : 1-ξ x^2 ≠ 0 := by
    have hx := abs_lt.mp (h.2.2.2.1 x)
    nlinarith
  have hξ := h.1
  have hυ := h.2.1
  have hζ := h.2.2.1
  have hc0 : Continuous (tableM0 ξ υ ζ ε L) := by
    unfold tableM0
    exact (continuous_const.mul (hυ.sub hζ)).div (continuous_const.sub hξ) hd0
  have hcτ : Continuous (tableTau ξ υ ζ ε L) := by
    unfold tableTau
    exact (continuous_const.mul (hζ.sub (hξ.mul hυ))).div
      (continuous_const.sub (hξ.pow 2)) hd2
  let κ := recordKernel (tableProp ξ) (measurable_tableProp ξ υ ζ ε L h) (tableArm ξ υ ζ ε L h)
  letI : IsMarkovKernel κ := recordKernel_markov _ _ _ he (tableArm_markov ξ υ ζ ε L h)
  letI : IsProbabilityMeasure design := by
    change IsProbabilityMeasure (volume : Measure unitInterval)
    infer_instance
  have hprob : IsProbabilityMeasure (tableLaw ξ υ ζ ε L) := by
    rw [tableLaw_eq_compProd ξ υ ζ ε L h]
    change IsProbabilityMeasure (design ⊗ₘ κ)
    infer_instance
  refine ⟨hprob, ?_, he, tableArm_markov ξ υ ζ ε L h, hc0, hcτ, ?_, ?_, ?_⟩
  · unfold tableProp
    fun_prop
  · have hmap : (tableLaw ξ υ ζ ε L).map X = design := by
      rw [tableLaw_eq_compProd ξ υ ζ ε L h]
      change (design ⊗ₘ κ).fst = design
      exact Measure.fst_compProd design κ
    rw [hmap]
    exact tableLaw_eq_compProd ξ υ ζ ε L h
  · filter_upwards [] with x
    rw [tableArm_mean ξ υ ζ ε L h false x]
    simp [tableM0, signVal, sub_eq_add_neg]
  · filter_upwards [] with x
    rw [tableArm_mean ξ υ ζ ε L h true x]
    simp only [tableM0, tableTau, signVal, ↓reduceIte, one_mul]
    field_simp [hd0 x, hd1 x, hd2 x]
    ring

/-- Zero law certificate: the displayed mathematical construction or bound. [This is the stated conclusion](goal). -/
-- @node: zero_law_certificate
lemma zero_law_certificate :
    IsProbabilityMeasure (design ⊗ₘ recordKernel (fun _ => 1/2) measurable_const (fun _ => Kernel.const unitInterval (Measure.dirac (0:ℝ)))) ∧
    (∀ x : unitInterval, 0 ≤ (1/2:ℝ) ∧ (1/2:ℝ) ≤ 1) ∧
    (∀ a : Bool, IsMarkovKernel (Kernel.const unitInterval (Measure.dirac (0:ℝ)))) ∧
    (design ⊗ₘ recordKernel (fun _ => 1/2) measurable_const (fun _ => Kernel.const unitInterval (Measure.dirac (0:ℝ)))) =
      ((design ⊗ₘ recordKernel (fun _ => 1/2) measurable_const (fun _ => Kernel.const unitInterval (Measure.dirac (0:ℝ)))).map X) ⊗ₘ recordKernel (fun _ => 1/2) measurable_const (fun _ => Kernel.const unitInterval (Measure.dirac (0:ℝ))) ∧
    (∀ᵐ x ∂design, (0:ℝ) = ∫ y, y ∂Kernel.const unitInterval (Measure.dirac (0:ℝ)) x) := by
  let Q : Bool → Kernel unitInterval ℝ := fun _ => Kernel.const unitInterval (Measure.dirac (0:ℝ))
  have hQ : ∀ a, IsMarkovKernel (Q a) := by intro a; dsimp [Q]; infer_instance
  have he : ∀ x : unitInterval, 0 ≤ (1/2:ℝ) ∧ (1/2:ℝ) ≤ 1 := by intro x; norm_num
  let κ := recordKernel (fun _ => (1/2:ℝ)) measurable_const Q
  letI : IsMarkovKernel κ := recordKernel_markov _ _ _ he hQ
  letI : IsProbabilityMeasure design := by
    change IsProbabilityMeasure (volume : Measure unitInterval)
    infer_instance
  refine ⟨?_, he, hQ, ?_, ?_⟩
  · change IsProbabilityMeasure (design ⊗ₘ κ)
    infer_instance
  · have hmap : (design ⊗ₘ κ).map X = design := Measure.fst_compProd design κ
    change design ⊗ₘ κ = ((design ⊗ₘ κ).map X) ⊗ₘ κ
    rw [hmap]
  · simp

/-- Zero mean1: the displayed mathematical construction or bound. [This is the stated conclusion](goal). -/
-- @node: zero_mean1
lemma zero_mean1 : ∀ᵐ x ∂design, (0:ℝ)+0 = ∫ y, y ∂Kernel.const unitInterval (Measure.dirac (0:ℝ)) x := by
  simp
/-- Referencelaw: the displayed mathematical construction or bound. [This is the stated defined object](goal). -/
def referenceLaw : ObservedLaw where
  P := design ⊗ₘ recordKernel (fun _ => 1/2) measurable_const (fun _ => Kernel.const unitInterval (Measure.dirac (0:ℝ)))
  probability := zero_law_certificate.1
  e := ContinuousMap.const unitInterval (1/2)
  e_range := zero_law_certificate.2.1
  Q := fun _ => Kernel.const unitInterval (Measure.dirac (0:ℝ))
  markov := zero_law_certificate.2.2.1
  m0 := 0
  tau := 0
  record_version := zero_law_certificate.2.2.2.1
  mean0_version := zero_law_certificate.2.2.2.2
  mean1_version := zero_mean1
/-- Literal six-category constructor; the invalid-input branch is a fixed law. This statement assumes [the ξ parameter](hyp:ξ), [the υ parameter](hyp:υ), [the ζ parameter](hyp:ζ), [the ε parameter](hyp:ε), [the L parameter](hyp:L). [This is the stated defined object](goal). [Defining clause 1](step:1) is used. [Defining clause 2](step:2) is used. -/
def tableObservedLaw (ξ υ ζ : unitInterval → ℝ) (ε L : ℝ) : ObservedLaw :=
  if h : TableValid ξ υ ζ ε L then
    let cert := table_certificate ξ υ ζ ε L h
    { P := tableLaw ξ υ ζ ε L
      probability := cert.1
      e := ⟨tableProp ξ,cert.2.1⟩
      e_range := cert.2.2.1
      Q := tableArm ξ υ ζ ε L h
      markov := cert.2.2.2.1
      m0 := ⟨tableM0 ξ υ ζ ε L,cert.2.2.2.2.1⟩
      tau := ⟨tableTau ξ υ ζ ε L,cert.2.2.2.2.2.1⟩
      record_version := cert.2.2.2.2.2.2.1
      mean0_version := cert.2.2.2.2.2.2.2.1
      mean1_version := cert.2.2.2.2.2.2.2.2 }
  else referenceLaw
/-- Finite weighted law families, represented without an additional structure. [This is the stated defined object](goal). -/
abbrev FinitePrior := Σ m : ℕ, (Fin m → ℝ) × (Fin m → ObservedLaw)
/-- Enumerate a finite weighted family through its finite-index equivalence. This statement assumes [the weight parameter](hyp:weight), [the laws parameter](hyp:laws). [This is the stated defined object](goal). -/
def finitePriorOf {ι : Type} [Fintype ι] (weight : ι → ℝ) (laws : ι → ObservedLaw) : FinitePrior :=
  ⟨Fintype.card ι,(fun i => weight ((Fintype.equivFin ι).symm i)),(fun i => laws ((Fintype.equivFin ι).symm i))⟩
/-- Read a finite family weight at its public index. This statement assumes [the π parameter](hyp:π). [This is the stated defined object](goal). -/
def priorWeight (π : FinitePrior) : Fin π.1 → ℝ := π.2.1
/-- Read the original-record law at a finite family index. This statement assumes [the π parameter](hyp:π). [This is the stated defined object](goal). -/
def priorLaw (π : FinitePrior) : Fin π.1 → ObservedLaw := π.2.2
/-- Mix the full original iid record laws using all finite family weights. This statement assumes [the n parameter](hyp:n), [the π parameter](hyp:π). [This is the stated defined object](goal). -/
def priorMixture (n : ℕ) (π : FinitePrior) : Measure (Dataset n) :=
  ∑ i : Fin π.1, ENNReal.ofReal (priorWeight π i) • Measure.pi (fun _ : Fin n => (priorLaw π i).P)
/-- A finite prior has nonnegative weights summing to one. This statement assumes [the π parameter](hyp:π). [This is the stated defined object](goal). -/
def PriorNormalized (π : FinitePrior) : Prop := (∀ i, 0 ≤ priorWeight π i) ∧ ∑ i, priorWeight π i = 1
/-- Every positive-weight law belongs to the specified class. This statement assumes [the π parameter](hyp:π), [the C parameter](hyp:C). [This is the stated defined object](goal). -/
def PriorSupported (π : FinitePrior) (C : Set ObservedLaw) : Prop :=
  ∀ i, 0 < priorWeight π i → priorLaw π i ∈ C

end CausalSmith.Stat.FinitepHomogeneityDensegamma

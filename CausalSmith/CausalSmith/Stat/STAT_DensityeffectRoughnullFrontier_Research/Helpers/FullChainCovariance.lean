module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.OperatorCovariance
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.SecondOrderCovariance
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ThirdOrderMoments

/-! Disjoint correction roles and arm subtraction assemble the full-chain covariance
quadratic-form bound (17), for every fixed training realization. -/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The three signed arm differences tested against a fixed histogram vector. -/
-- @node: correctionContrast
def correctionContrast {m : ℕ} (train : Fin m → Omega) (mx my L T J q : ℕ)
    (kt : ℕ → ℕ) (f : Hj J) : Fin 3 → EvalData m → ℝ :=
  ![fun eval => inner ℝ (Uone train mx my J eval 0 true) f -
      inner ℝ (Uone train mx my J eval 0 false) f,
    fun eval => inner ℝ (Utwo train mx my L T J kt eval 0 false) f -
      inner ℝ (Utwo train mx my L T J kt eval 0 true) f,
    fun eval => inner ℝ (Uthree train mx my J q eval 0 true) f -
      inner ℝ (Uthree train mx my J q eval 0 false) f]

/-- Measurable statistics depending on disjoint evaluation blocks are independent. -/
-- @node: indepFun_of_disjoint_eval_blocks
lemma indepFun_of_disjoint_eval_blocks (P : ObsLaw) (m : ℕ)
    (S T : Finset (Fin 12)) (hST : Disjoint S T) (g h : EvalData m → ℝ)
    (hg : Measurable g) (hh : Measurable h)
    (hgs : ∀ x y, (∀ r ∈ S, x r = y r) → g x = g y)
    (hht : ∀ x y, (∀ r ∈ T, x r = y r) → h x = h y) :
    IndepFun g h (evalLaw P m) := by
  classical
  let extend (s : Finset (Fin 12)) (x : s → Fin m → Omega) : EvalData m :=
    fun r => if hr : r ∈ s then x ⟨r, hr⟩ else fun _ => (0, false, 0)
  have he (s : Finset (Fin 12)) : Measurable (extend s) := by
    apply measurable_pi_lambda
    intro r
    dsimp [extend]
    split_ifs <;> fun_prop
  have hind : iIndepFun (fun r : Fin 12 => fun eval : EvalData m => eval r)
      (evalLaw P m) := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hi := (hind.indepFun_finset S T hST (fun _ => measurable_pi_apply _)).comp
    (hg.comp (he S)) (hh.comp (he T))
  have eg : (fun x : EvalData m => g (extend S (fun r => x r))) = g := by
    funext x
    apply hgs
    intro r hr
    simp [extend, hr]
  have eh : (fun x : EvalData m => h (extend T (fun r => x r))) = h := by
    funext x
    apply hht
    intro r hr
    simp [extend, hr]
  simpa only [Function.comp_def, eg, eh] using hi

/-- Each correction contrast depends only on its own evaluation roles. -/
-- @node: correctionContrast_dependsOn
lemma correctionContrast_dependsOn {m : ℕ} (train : Fin m → Omega)
    (mx my L T J q : ℕ) (kt : ℕ → ℕ) (f : Hj J) (i : Fin 3)
    (x y : EvalData m)
    (h : ∀ r ∈ (![{0}, {1, 2}, {3, 4, 5}] : Fin 3 → Finset (Fin 12)) i,
      x r = y r) :
    correctionContrast train mx my L T J q kt f i x =
      correctionContrast train mx my L T J q kt f i y := by
  fin_cases i
  · have h0 := h 0 (by simp)
    simp [correctionContrast, Uone, chainRole, chainOffset, h0]
  · have h1 := h 1 (by simp)
    have h2 := h 2 (by simp)
    dsimp [correctionContrast, Utwo, chainRole, chainOffset, Fin.ofNat]
    rw [h1, h2]
  · have h3 := h 3 (by simp)
    have h4 := h 4 (by simp)
    have h5 := h 5 (by simp)
    simp [correctionContrast, Uthree, chainRole, chainOffset, h3, h4, h5]

/-- Each scalar correction contrast is measurable. -/
-- @node: measurable_correctionContrast
@[fun_prop] lemma measurable_correctionContrast {m : ℕ} (train : Fin m → Omega)
    (mx my L T J q : ℕ) (kt : ℕ → ℕ) (f : Hj J) (i : Fin 3) :
    Measurable (correctionContrast train mx my L T J q kt f i) := by
  letI : MeasurableSpace (Hj J) := borel _
  letI : BorelSpace (Hj J) := ⟨rfl⟩
  fin_cases i <;> dsimp [correctionContrast] <;> fun_prop

/-- Fixed histogram corrections have finite range. -/
-- @node: finite_range_correctionContrast
lemma finite_range_correctionContrast {m : ℕ} (train : Fin m → Omega)
    (mx my L T J q : ℕ) (kt : ℕ → ℕ) (f : Hj J) (i : Fin 3) :
    (Set.range (correctionContrast train mx my L T J q kt f i)).Finite := by
  fin_cases i
  all_goals
    dsimp [correctionContrast]
    apply chain_finite_range_binary (op := (· - ·))
  · exact chain_finite_range_comp (finite_range_Uone train mx my J 0 true) (fun v => inner ℝ v f)
  · exact chain_finite_range_comp (finite_range_Uone train mx my J 0 false) (fun v => inner ℝ v f)
  · exact chain_finite_range_comp (finite_range_Utwo train mx my L T J kt 0 false) (fun v => inner ℝ v f)
  · exact chain_finite_range_comp (finite_range_Utwo train mx my L T J kt 0 true) (fun v => inner ℝ v f)
  · exact chain_finite_range_comp (finite_range_Uthree train mx my J q 0 true) (fun v => inner ℝ v f)
  · exact chain_finite_range_comp (finite_range_Uthree train mx my J q 0 false) (fun v => inner ℝ v f)

/-- A measurable finite-range scalar statistic has every finite-measure Lp moment. -/
-- @node: memLp_scalar_finite_range
lemma memLp_scalar_finite_range {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (g : E → ℝ) (hg : Measurable g)
    (hf : (Set.range g).Finite) : MemLp g 2 μ := by
  obtain ⟨C, hC⟩ := hf.isBounded.exists_norm_le
  exact MemLp.of_bound hg.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun x => hC _ ⟨x, rfl⟩))

/-- The first and second correction arm differences use disjoint roles. -/
-- @node: indepFun_correctionContrast_first_second
lemma indepFun_correctionContrast_first_second (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my L T J q : ℕ) (kt : ℕ → ℕ) (f : Hj J) :
    IndepFun (correctionContrast train mx my L T J q kt f 0)
      (correctionContrast train mx my L T J q kt f 1) (evalLaw P m) := by
  apply indepFun_of_disjoint_eval_blocks P m {0} {1, 2} (by decide)
    _ _ (measurable_correctionContrast train mx my L T J q kt f 0)
    (measurable_correctionContrast train mx my L T J q kt f 1)
  · exact correctionContrast_dependsOn train mx my L T J q kt f 0
  · exact correctionContrast_dependsOn train mx my L T J q kt f 1

/-- The sum of the first two corrections is independent of the third correction. -/
-- @node: indepFun_correctionContrast_sum_third
lemma indepFun_correctionContrast_sum_third (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my L T J q : ℕ) (kt : ℕ → ℕ) (f : Hj J) :
    IndepFun (correctionContrast train mx my L T J q kt f 0 +
      correctionContrast train mx my L T J q kt f 1)
      (correctionContrast train mx my L T J q kt f 2) (evalLaw P m) := by
  apply indepFun_of_disjoint_eval_blocks P m {0, 1, 2} {3, 4, 5} (by decide)
    _ _ (by fun_prop) (by fun_prop)
  · intro x y h
    have h0 := correctionContrast_dependsOn train mx my L T J q kt f 0 x y
      (fun r hr => h r (by simp at hr; subst r; simp))
    have h1 := correctionContrast_dependsOn train mx my L T J q kt f 1 x y
      (fun r hr => h r (Finset.mem_insert_of_mem hr))
    exact congrArg₂ (· + ·) h0 h1
  · exact correctionContrast_dependsOn train mx my L T J q kt f 2

/-- The pilot integral is constant, and the three signed corrections sum to the chain. -/
-- @node: inner_coefficientChain_eq_corrections
lemma inner_coefficientChain_eq_corrections {m : ℕ} (train : Fin m → Omega)
    (mx my L T J q : ℕ) (kt : ℕ → ℕ) (f : Hj J) (eval : EvalData m) :
    inner ℝ (coefficientChain train mx my L T J q kt eval 0) f =
      inner ℝ ((∫ x, pilotCoefficients train mx my J true x ∂unitVolume) -
        (∫ x, pilotCoefficients train mx my J false x ∂unitVolume)) f +
      (correctionContrast train mx my L T J q kt f 0 eval +
        correctionContrast train mx my L T J q kt f 1 eval +
        correctionContrast train mx my L T J q kt f 2 eval) := by
  simp [coefficientChain, correctionContrast, Fintype.sum_bool, inner_add_left,
    inner_sub_left, real_inner_smul_left]
  <;> ring

/-- All three correction variances are absorbed by the paper's fixed moment constant. -/
-- @node: contrastCovariance_form_le_multiband
lemma contrastCovariance_form_le_multiband (P : ObsLaw) (hModel : Model P)
    {m : ℕ} (hm : 1 ≤ m) (train : Fin m → Omega) (mx my L T q : ℕ)
    (hL : Dyadic L) (hq : 0 < q) (hqm : q ≤ m) (kt : ℕ → ℕ)
    (hkt : ∀ t, t ≤ T → 0 < kt t) (f : Hj (2 ^ T * L)) :
    covarianceForm (contrastCovariance P train mx my L T (2 ^ T * L) q kt) f ≤
      (2 : ℝ) ^ 24 * ((m : ℝ)⁻¹ * ‖f‖ ^ 2 + (m : ℝ) ^ (-2 : ℤ) *
        ∑ t ∈ Finset.range (T + 1), (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2) := by
  let J := 2 ^ T * L
  letI : MeasurableSpace (Hj J) := borel _
  letI : BorelSpace (Hj J) := ⟨rfl⟩
  letI : IsProbabilityMeasure (evalLaw P m) := by unfold evalLaw; infer_instance
  have hLpos : 0 < L := by obtain ⟨l, rfl⟩ := hL; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  let X := correctionContrast train mx my L T J q kt f 0
  let Y := correctionContrast train mx my L T J q kt f 1
  let Z := correctionContrast train mx my L T J q kt f 2
  have hLp (i : Fin 3) : MemLp (correctionContrast train mx my L T J q kt f i) 2
      (evalLaw P m) := memLp_scalar_finite_range _ _
        (measurable_correctionContrast train mx my L T J q kt f i)
        (finite_range_correctionContrast train mx my L T J q kt f i)
  have h1Lp (a : Bool) : MemLp (fun eval => inner ℝ (Uone train mx my J eval 0 a) f)
      2 (evalLaw P m) := memLp_scalar_finite_range _ _ (by fun_prop)
        (chain_finite_range_comp (finite_range_Uone train mx my J 0 a) (fun v => inner ℝ v f))
  have h2Lp (a : Bool) : MemLp (fun eval => inner ℝ (Utwo train mx my L T J kt eval 0 a) f)
      2 (evalLaw P m) := memLp_scalar_finite_range _ _ (by fun_prop)
        (chain_finite_range_comp (finite_range_Utwo train mx my L T J kt 0 a) (fun v => inner ℝ v f))
  have h3Lp (a : Bool) : MemLp (fun eval => inner ℝ (Uthree train mx my J q eval 0 a) f)
      2 (evalLaw P m) := memLp_scalar_finite_range _ _ (by fun_prop)
        (chain_finite_range_comp (finite_range_Uthree train mx my J q 0 a) (fun v => inner ℝ v f))
  have hfirst : variance X (evalLaw P m) ≤ 4 * 4096 * ((m : ℝ)⁻¹ * ‖f‖ ^ 2) := by
    have hd := arm_difference_variance_le (evalLaw P m) _ _ (h1Lp true) (h1Lp false)
    have ht := variance_inner_Uone_le P hModel train mx my J hJ 0 true f
    have hf := variance_inner_Uone_le P hModel train mx my J hJ 0 false f
    dsimp [X, correctionContrast]
    linarith
  have hsecond : variance Y (evalLaw P m) ≤ 4 * (2 : ℝ) ^ 16 *
      ((m : ℝ)⁻¹ * ‖f‖ ^ 2 + (m : ℝ) ^ (-2 : ℤ) *
        ∑ t ∈ Finset.range (T + 1), (kt t : ℝ) * ‖Qband L J t f‖ ^ 2) := by
    have hd := arm_difference_variance_le (evalLaw P m) _ _ (h2Lp false) (h2Lp true)
    have ht := variance_inner_Utwo_le P hModel hm train mx my L T hL kt hkt 0 true f
    have hf := variance_inner_Utwo_le P hModel hm train mx my L T hL kt hkt 0 false f
    dsimp [Y, correctionContrast]
    linarith
  have hthird : variance Z (evalLaw P m) ≤ 4 * (2 : ℝ) ^ 20 *
      ((m : ℝ)⁻¹ * ‖f‖ ^ 2) := by
    have hd := arm_difference_variance_le (evalLaw P m) _ _ (h3Lp true) (h3Lp false)
    have ht := variance_inner_Uthree_le P hModel hm train mx my J q hJ hq hqm 0 true f
    have hf := variance_inner_Uthree_le P hModel hm train mx my J q hJ hq hqm 0 false f
    dsimp [Z, correctionContrast]
    linarith
  rw [contrastCovariance_form_eq_variance]
  simp_rw [inner_coefficientChain_eq_corrections]
  let c := inner ℝ ((∫ x, pilotCoefficients train mx my J true x ∂unitVolume) -
    (∫ x, pilotCoefficients train mx my J false x ∂unitVolume)) f
  change variance (fun eval => c + (X + Y + Z) eval) (evalLaw P m) ≤ _
  rw [variance_const_add ((hLp 0).add (hLp 1) |>.add (hLp 2)).aestronglyMeasurable]
  exact independent_correction_variance_le (evalLaw P m) X Y Z (hLp 0) (hLp 1) (hLp 2)
    (indepFun_correctionContrast_first_second P train mx my L T J q kt f)
    (indepFun_correctionContrast_sum_third P train mx my L T J q kt f)
    _ _ (by positivity) (by positivity) hfirst hsecond hthird

end CausalSmith.Stat.DensityEffectRoughNull

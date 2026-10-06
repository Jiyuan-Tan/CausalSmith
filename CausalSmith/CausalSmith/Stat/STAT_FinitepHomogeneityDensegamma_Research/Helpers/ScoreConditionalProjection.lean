module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreSingletonBounds

/-! Conditional projection formulas for individual dyadic score corrections. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma
noncomputable section

/-- [The score Diff Leg object](goal) is defined from [the J parameter](hyp:J), [the R parameter](hyp:R), [the T parameter](hyp:T), [the r parameter](hyp:r), [the u parameter](hyp:u), [the o parameter](hyp:o), [the z parameter](hyp:z). -/
def scoreDiffLeg (J R : ℕ) (T : ℝ) (r : Bool) (u : Vec J)
    (o z : Record) : ℝ :=
  treatment o*diffKernel R (X o) (X z)*scoreMark T r z*
    inner ℝ u (featureMap J (X o))

/-- [The score Diff Pair object](goal) is defined from [the J parameter](hyp:J), [the R parameter](hyp:R), [the T parameter](hyp:T), [the r parameter](hyp:r), [the u parameter](hyp:u), [the o parameter](hyp:o), [the z parameter](hyp:z). -/
def scoreDiffPair (J R : ℕ) (T : ℝ) (r : Bool) (u : Vec J)
    (o z : Record) : ℝ :=
  (scoreDiffLeg J R T r u o z+scoreDiffLeg J R T r u z o)/2

/-- [the score Diff Leg measurable statement holds](goal). -/
@[fun_prop] lemma scoreDiffLeg_measurable (J R : ℕ) (T : ℝ) (r : Bool) (u : Vec J) :
    Measurable (fun z : Record × Record => scoreDiffLeg J R T r u z.1 z.2) := by
  cases r
  · simp only [scoreDiffLeg, scoreMark, Bool.false_eq_true, ↓reduceIte]
    unfold diffKernel clipY X Y
    fun_prop
  · simp only [scoreDiffLeg, scoreMark, ↓reduceIte]
    unfold diffKernel X
    fun_prop

/-- Under [the hR condition](hyp:hR), [the hT condition](hyp:hT), [the score Diff Leg abs le statement holds](goal). -/
lemma scoreDiffLeg_abs_le (J R : ℕ) (hR : 0 < R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) (o z : Record) :
    |scoreDiffLeg J R T r u o z| ≤
      (3*(R:ℝ))*T*‖u‖*Real.sqrt ((J:ℝ)*J) := by
  unfold scoreDiffLeg
  rw [abs_mul, abs_mul, abs_mul]
  have hd : |diffKernel R (X o) (X z)| ≤ 3*(R:ℝ) := by
    unfold diffKernel
    calc
      _ ≤ |projKernel (2*R) (X o) (X z)|+|projKernel R (X o) (X z)| := abs_sub _ _
      _ ≤ ((2*R:ℕ):ℝ)+(R:ℝ) := add_le_add
        (histogram_kernel_bounds (2*R) (by positivity) _ _).2
        (histogram_kernel_bounds R hR _ _).2
      _ = _ := by push_cast; ring
  have hi : |inner ℝ u (featureMap J (X o))| ≤ ‖u‖*Real.sqrt ((J:ℝ)*J) :=
    (abs_real_inner_le_norm u _).trans
      (mul_le_mul_of_nonneg_left (featureMap_norm_bound J _) (norm_nonneg u))
  have h1 : |treatment o| * |diffKernel R (X o) (X z)| ≤ 1*(3*(R:ℝ)) :=
    mul_le_mul (treatment_abs_le_one _) hd (abs_nonneg _) (by norm_num)
  have h2 : |treatment o| * |diffKernel R (X o) (X z)| * |scoreMark T r z| ≤
      (1*(3*(R:ℝ)))*T :=
    mul_le_mul h1 (scoreMark_abs_le' T hT r _) (abs_nonneg _) (by positivity)
  calc
    _ ≤ (1*(3*(R:ℝ))*T)*(‖u‖*Real.sqrt ((J:ℝ)*J)) :=
      mul_le_mul h2 hi (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- Under [the hR condition](hyp:hR), [the hT condition](hyp:hT), [the score Diff Leg slice integrable statement holds](goal). -/
lemma scoreDiffLeg_slice_integrable (law : ObservedLaw) (J R : ℕ) (hR : 0 < R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) (o : Record) :
    Integrable (fun z => scoreDiffLeg J R T r u o z) law.P := by
  let B := (3*(R:ℝ))*T*‖u‖*Real.sqrt ((J:ℝ)*J)
  have hm : Measurable (fun z => scoreDiffLeg J R T r u o z) :=
    (scoreDiffLeg_measurable J R T r u).comp
      (show Measurable (fun z : Record => (o,z)) from measurable_const.prodMk measurable_id)
  apply (integrable_const B).mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs]
    exact scoreDiffLeg_abs_le J R hR T hT r u o z)

/-- Under [the hu condition](hyp:hu), [the hJ condition](hyp:hJ), [the hR condition](hyp:hR), [the hJR condition](hyp:hJR), [the hT condition](hyp:hT), [the score Diff Pair conditional formula statement holds](goal). -/
lemma scoreDiffPair_conditional_formula (law : ObservedLaw) (hu : UniformDesign law)
    (J R : ℕ) (hJ : 0 < J) (hR : 0 < R) (hJR : J ∣ R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) (o : Record) :
    (∫ z, scoreDiffPair J R T r u o z ∂law.P) =
      (1/2)*inner ℝ u (featureMap J (X o))*
        (treatment o*(∫ x, diffKernel R (X o) x*recordMarkMean law (scoreMark T r) x ∂design)+
         scoreMark T r o*(∫ x, diffKernel R (X o) x*law.e x ∂design)) := by
  let q := scoreMark T r
  have hq : Measurable q := scoreMark_measurable' T r
  have hb : ∀ z, |q z| ≤ T := scoreMark_abs_le' T hT r
  have hfirst : (∫ z, scoreDiffLeg J R T r u o z ∂law.P) =
      treatment o*inner ℝ u (featureMap J (X o))*
        (∫ x, diffKernel R (X o) x*recordMarkMean law q x ∂design) := by
    unfold scoreDiffLeg
    rw [show (∫ z, treatment o*diffKernel R (X o) (X z)*q z*
        inner ℝ u (featureMap J (X o)) ∂law.P) =
      (treatment o*inner ℝ u (featureMap J (X o)))*
        ∫ z, diffKernel R (X o) (X z)*q z ∂law.P by
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact ae_of_all _ (fun z => by ring)]
    rw [diffKernel_recordMark_integral law hu R hR q hq T (by linarith) hb]
  have hsecond : (∫ z, scoreDiffLeg J R T r u z o ∂law.P) =
      q o*inner ℝ u (featureMap J (X o))*
        (∫ x, diffKernel R (X o) x*law.e x ∂design) := by
    have hc (z : Record) : scoreDiffLeg J R T r u z o =
        q o*inner ℝ u (featureMap J (X o))*
          (diffKernel R (X o) (X z)*treatment z) := by
      unfold scoreDiffLeg
      have hh := diffKernel_feature_inner_commute J R hJ hR hJR u (X z) (X o)
      dsimp [q]
      calc
        _ = treatment z*scoreMark T r o*
            (diffKernel R (X z) (X o)*inner ℝ u (featureMap J (X z))) := by ring
        _ = treatment z*scoreMark T r o*
            (diffKernel R (X o) (X z)*inner ℝ u (featureMap J (X o))) := by rw [hh]
        _ = _ := by ring
    simp_rw [hc]
    rw [integral_const_mul]
    rw [diffKernel_recordMark_integral law hu R hR treatment measurable_treatment 1
      (by norm_num) treatment_abs_le_one]
    rw [recordMarkMean_treatment]
  unfold scoreDiffPair
  rw [integral_div, integral_add]
  · rw [hfirst, hsecond]
    ring
  · exact scoreDiffLeg_slice_integrable law J R hR T hT r u o
  · have hm : Measurable (fun z => scoreDiffLeg J R T r u z o) :=
      (scoreDiffLeg_measurable J R T r u).comp (measurable_id.prodMk measurable_const)
    let B := (3*(R:ℝ))*T*‖u‖*Real.sqrt ((J:ℝ)*J)
    apply (integrable_const B).mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs]
      exact scoreDiffLeg_abs_le J R hR T hT r u z o)

/-- Under [the hu condition](hyp:hu), [the hJ condition](hyp:hJ), [the hR condition](hyp:hR), [the hJR condition](hyp:hJR), [the hT condition](hyp:hT), [the hD condition](hyp:hD), [the hA0 condition](hyp:hA0), [the hd condition](hyp:hd), [the ha condition](hyp:ha), [the score Diff Pair conditional abs le statement holds](goal). -/
lemma scoreDiffPair_conditional_abs_le (law : ObservedLaw) (hu : UniformDesign law)
    (J R : ℕ) (hJ : 0 < J) (hR : 0 < R) (hJR : J ∣ R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) (o : Record)
    (D A0 : ℝ) (hD : 0 ≤ D) (hA0 : 0 ≤ A0)
    (hd : |∫ x, diffKernel R (X o) x*recordMarkMean law (scoreMark T r) x ∂design| ≤ D)
    (ha : |∫ x, diffKernel R (X o) x*law.e x ∂design| ≤ A0) :
    |∫ z, scoreDiffPair J R T r u o z ∂law.P| ≤
      (1/2)*|inner ℝ u (featureMap J (X o))| *(D+A0*|scoreMark T r o|) := by
  rw [scoreDiffPair_conditional_formula law hu J R hJ hR hJR T hT r u o]
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  gcongr
  calc
    _ ≤ |treatment o*(∫ x, diffKernel R (X o) x*
          recordMarkMean law (scoreMark T r) x ∂design)|+
        |scoreMark T r o*(∫ x, diffKernel R (X o) x*law.e x ∂design)| := abs_add_le _ _
    _ ≤ 1*D+|scoreMark T r o| *A0 := by
      rw [abs_mul, abs_mul]
      exact add_le_add
        (mul_le_mul (treatment_abs_le_one o) hd (abs_nonneg _) (by norm_num))
        (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
    _ = D+A0*|scoreMark T r o| := by ring

/-- Under [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hR condition](hyp:hR), [the hJR condition](hyp:hJR), [the hT condition](hyp:hT), [the score Diff Pair conditional abs false le statement holds](goal). -/
lemma scoreDiffPair_conditional_abs_false_le (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law)
    (J R : ℕ) (hJ : 0 < J) (hR : 0 < R) (hJR : J ∣ R)
    (T : ℝ) (hT : 1 ≤ T) (u : Vec J) (o : Record) :
    |∫ z, scoreDiffPair J R T false u o z ∂law.P| ≤
      (1/2)*|inner ℝ u (featureMap J (X o))| *
        ((110*(R:ℝ)^(-min v.α (min v.β v.γ))+20*T^(1-v.p))+
          (40*(R:ℝ)^(-v.α))*|clipY T (Y o)|) := by
  apply scoreDiffPair_conditional_abs_le law hm.uniform J R hJ hR hJR T hT false u o
    _ _ (by positivity) (by positivity)
  · exact diffKernel_scoreMarkMean_false_bound v hv law hm T hT R hR (X o)
  · exact diffKernel_propensity_bound v hv law hm R hR (X o)

/-- Under [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hR condition](hyp:hR), [the hJR condition](hyp:hJR), [the hT condition](hyp:hT), [the score Diff Pair conditional abs true le statement holds](goal). -/
lemma scoreDiffPair_conditional_abs_true_le (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law)
    (J R : ℕ) (hJ : 0 < J) (hR : 0 < R) (hJR : J ∣ R)
    (T : ℝ) (hT : 1 ≤ T) (u : Vec J) (o : Record) :
    |∫ z, scoreDiffPair J R T true u o z ∂law.P| ≤
      (40*(R:ℝ)^(-v.α)) * |inner ℝ u (featureMap J (X o))| := by
  have ha := diffKernel_propensity_bound v hv law hm R hR (X o)
  have hmtrue : recordMarkMean law (scoreMark T true) = law.e := by
    rw [show scoreMark T true = treatment by funext z; simp [scoreMark]]
    exact recordMarkMean_treatment law
  have h := scoreDiffPair_conditional_abs_le law hm.uniform J R hJ hR hJR T hT true u o
    (40*(R:ℝ)^(-v.α)) (40*(R:ℝ)^(-v.α)) (by positivity) (by positivity)
    (by simpa only [hmtrue] using ha) ha
  simp only [scoreMark, if_true, treatment] at h
  have hAt : |if (o.2.1) then (1:ℝ) else 0| ≤ 1 := by split <;> norm_num
  calc
    _ ≤ (1/2)*|inner ℝ u (featureMap J (X o))| *
        ((40*(R:ℝ)^(-v.α))+(40*(R:ℝ)^(-v.α))*
          |if (o.2.1) then (1:ℝ) else 0|) := h
    _ ≤ (40*(R:ℝ)^(-v.α)) * |inner ℝ u (featureMap J (X o))| := by
      calc
        _ ≤ (1/2)*|inner ℝ u (featureMap J (X o))| *
            ((40*(R:ℝ)^(-v.α))+(40*(R:ℝ)^(-v.α))*1) := by gcongr
        _ = _ := by ring

/-- [The score Proj Leg object](goal) is defined from [the J parameter](hyp:J), [the R parameter](hyp:R), [the T parameter](hyp:T), [the r parameter](hyp:r), [the u parameter](hyp:u), [the o parameter](hyp:o), [the z parameter](hyp:z). -/
def scoreProjLeg (J R : ℕ) (T : ℝ) (r : Bool) (u : Vec J)
    (o z : Record) : ℝ :=
  treatment o*projKernel R (X o) (X z)*scoreMark T r z*
    inner ℝ u (featureMap J (X o))

/-- [The score Proj Pair object](goal) is defined from [the J parameter](hyp:J), [the R parameter](hyp:R), [the T parameter](hyp:T), [the r parameter](hyp:r), [the u parameter](hyp:u), [the o parameter](hyp:o), [the z parameter](hyp:z). -/
def scoreProjPair (J R : ℕ) (T : ℝ) (r : Bool) (u : Vec J)
    (o z : Record) : ℝ :=
  (scoreProjLeg J R T r u o z+scoreProjLeg J R T r u z o)/2

/-- [the multires Scalar Pair eq score Diff Pairs statement holds](goal). -/
lemma multiresScalarPair_eq_scoreDiffPairs (J L : ℕ) (T0 : ℝ) (T : Fin L → ℝ)
    (r : Bool) (u : Vec J) (o z : Record) :
    multiresScalarPair J L T0 T r u o z =
      -scoreProjPair J J T0 r u o z-
        ∑ j : Fin L, scoreDiffPair J (2^j.val*J) (T j) r u o z := by
  unfold multiresScalarPair multiresPairKernel scoreProjPair scoreProjLeg
    scoreDiffPair scoreDiffLeg scoreMark
  simp only [inner_smul_right, inner_neg_right, inner_add_right, inner_sub_right, inner_sum, smul_eq_mul]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  ring

/-- [the score Proj Leg measurable statement holds](goal). -/
@[fun_prop] lemma scoreProjLeg_measurable (J R : ℕ) (T : ℝ) (r : Bool) (u : Vec J) :
    Measurable (fun z : Record × Record => scoreProjLeg J R T r u z.1 z.2) := by
  cases r
  · simp only [scoreProjLeg, scoreMark, Bool.false_eq_true, ↓reduceIte]
    unfold clipY X Y
    fun_prop
  · simp only [scoreProjLeg, scoreMark, ↓reduceIte]
    unfold X
    fun_prop

/-- Under [the hR condition](hyp:hR), [the hT condition](hyp:hT), [the score Proj Leg abs le statement holds](goal). -/
lemma scoreProjLeg_abs_le (J R : ℕ) (hR : 0 < R) (T : ℝ) (hT : 1 ≤ T)
    (r : Bool) (u : Vec J) (o z : Record) :
    |scoreProjLeg J R T r u o z| ≤
      (R:ℝ)*T*‖u‖*Real.sqrt ((J:ℝ)*J) := by
  unfold scoreProjLeg
  rw [abs_mul, abs_mul, abs_mul]
  have hi : |inner ℝ u (featureMap J (X o))| ≤ ‖u‖*Real.sqrt ((J:ℝ)*J) :=
    (abs_real_inner_le_norm u _).trans
      (mul_le_mul_of_nonneg_left (featureMap_norm_bound J _) (norm_nonneg u))
  have h1 : |treatment o| *|projKernel R (X o) (X z)| ≤ 1*(R:ℝ) :=
    mul_le_mul (treatment_abs_le_one _) (histogram_kernel_bounds R hR _ _).2
      (abs_nonneg _) (by norm_num)
  have h2 : |treatment o| *|projKernel R (X o) (X z)| *|scoreMark T r z| ≤
      (1*(R:ℝ))*T :=
    mul_le_mul h1 (scoreMark_abs_le' T hT r _) (abs_nonneg _) (by positivity)
  calc
    _ ≤ (1*(R:ℝ)*T)*(‖u‖*Real.sqrt ((J:ℝ)*J)) :=
      mul_le_mul h2 hi (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- Under [the hR condition](hyp:hR), [the hT condition](hyp:hT), [the score Proj Leg slice integrable statement holds](goal). -/
lemma scoreProjLeg_slice_integrable (law : ObservedLaw) (J R : ℕ) (hR : 0 < R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) (o : Record) :
    Integrable (fun z => scoreProjLeg J R T r u o z) law.P := by
  let B := (R:ℝ)*T*‖u‖*Real.sqrt ((J:ℝ)*J)
  have hm : Measurable (fun z => scoreProjLeg J R T r u o z) :=
    (scoreProjLeg_measurable J R T r u).comp
      (show Measurable (fun z : Record => (o,z)) from measurable_const.prodMk measurable_id)
  apply (integrable_const B).mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact scoreProjLeg_abs_le J R hR T hT r u o z)

/-- Under [the hu condition](hyp:hu), [the hJ condition](hyp:hJ), [the hR condition](hyp:hR), [the hJR condition](hyp:hJR), [the hT condition](hyp:hT), [the score Proj Pair conditional formula statement holds](goal). -/
lemma scoreProjPair_conditional_formula (law : ObservedLaw) (hu : UniformDesign law)
    (J R : ℕ) (hJ : 0 < J) (hR : 0 < R) (hJR : J ∣ R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) (o : Record) :
    (∫ z, scoreProjPair J R T r u o z ∂law.P) =
      (1/2)*inner ℝ u (featureMap J (X o))*
        (treatment o*projOp R (recordMarkMean law (scoreMark T r)) (X o)+
          scoreMark T r o*projOp R law.e (X o)) := by
  let q := scoreMark T r
  have hq : Measurable q := scoreMark_measurable' T r
  have hb : ∀ z, |q z| ≤ T := scoreMark_abs_le' T hT r
  have hfirst : (∫ z, scoreProjLeg J R T r u o z ∂law.P) =
      treatment o*inner ℝ u (featureMap J (X o))*projOp R (recordMarkMean law q) (X o) := by
    unfold scoreProjLeg
    rw [show (∫ z, treatment o*projKernel R (X o) (X z)*q z*inner ℝ u (featureMap J (X o)) ∂law.P) =
      (treatment o*inner ℝ u (featureMap J (X o)))*∫ z, projKernel R (X o) (X z)*q z ∂law.P by
        rw [← integral_const_mul]; apply integral_congr_ae; exact ae_of_all _ (fun z => by ring)]
    rw [record_histogram_mark_integral law hu R hR (X o) q hq T (by linarith) hb]
  have hsecond : (∫ z, scoreProjLeg J R T r u z o ∂law.P) =
      q o*inner ℝ u (featureMap J (X o))*projOp R law.e (X o) := by
    have hc (z : Record) : scoreProjLeg J R T r u z o =
        q o*inner ℝ u (featureMap J (X o))*(projKernel R (X o) (X z)*treatment z) := by
      unfold scoreProjLeg
      have hh := congrArg (fun w : Vec J => inner ℝ u w)
        (histogram_feature_kernel_commute J R hJ hR hJR (X z) (X o))
      simp only [inner_smul_right, smul_eq_mul] at hh
      dsimp [q]
      calc
        _ = treatment z*scoreMark T r o*(projKernel R (X z) (X o)*inner ℝ u (featureMap J (X z))) := by ring
        _ = treatment z*scoreMark T r o*(projKernel R (X o) (X z)*inner ℝ u (featureMap J (X o))) := by rw [hh]
        _ = _ := by ring
    simp_rw [hc]
    rw [integral_const_mul, record_histogram_mark_integral law hu R hR (X o) treatment
      measurable_treatment 1 (by norm_num) treatment_abs_le_one, recordMarkMean_treatment]
  unfold scoreProjPair
  rw [integral_div, integral_add]
  · rw [hfirst, hsecond]; ring
  · exact scoreProjLeg_slice_integrable law J R hR T hT r u o
  · have hm : Measurable (fun z => scoreProjLeg J R T r u z o) :=
      (scoreProjLeg_measurable J R T r u).comp
        (show Measurable (fun z : Record => (z,o)) from measurable_id.prodMk measurable_const)
    let B := (R:ℝ)*T*‖u‖*Real.sqrt ((J:ℝ)*J)
    apply (integrable_const B).mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact scoreProjLeg_abs_le J R hR T hT r u z o)

end
end CausalSmith.Stat.FinitepHomogeneityDensegamma

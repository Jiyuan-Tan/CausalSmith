module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreConditionalProjection

/-! Second-moment bounds for scalar score kernels and their singleton projections. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- For real-valued functions, the square of the finite `L²` seminorm is the second moment. This statement assumes [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
lemma eLpNorm_two_toReal_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have hnon : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  rw [show (2:ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  simp [hnon]

/-- The ordinary real `L²` seminorm satisfies the triangle inequality. This statement assumes [the hf condition](hyp:hf), [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
lemma eLpNorm_two_add_toReal_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (eLpNorm (f + g) 2 μ).toReal ≤
      (eLpNorm f 2 μ).toReal + (eLpNorm g 2 μ).toReal := by
  have hle := eLpNorm_add_le hf.1 hg.1 (by norm_num : (1 : ENNReal) ≤ 2)
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (by finiteness) hle

/-- A second-moment estimate gives the corresponding real `L²` seminorm estimate. This statement assumes [the hf condition](hyp:hf), [the hB condition](hyp:hB), [the hN condition](hyp:hN), [the henergy condition](hyp:henergy). [This is the stated conclusion](goal). -/
lemma eLpNorm_two_toReal_le_of_energy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : MemLp f 2 μ) (B N : ℝ) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (henergy : (∫ x, f x ^ 2 ∂μ) ≤ B^2*N) :
    (eLpNorm f 2 μ).toReal ≤ B*Real.sqrt N := by
  apply (sq_le_sq₀ (ENNReal.toReal_nonneg) (mul_nonneg hB (Real.sqrt_nonneg _))).mp
  rw [eLpNorm_two_toReal_sq μ f hf, mul_pow, Real.sq_sqrt hN]
  exact henergy

/-- Second-moment envelopes add by the `L²` triangle inequality. This statement assumes [the hf condition](hyp:hf), [the hg condition](hyp:hg), [the hA condition](hyp:hA), [the hB condition](hyp:hB), [the hN condition](hyp:hN), [the hfenergy condition](hyp:hfenergy), [the hgenergy condition](hyp:hgenergy). [This is the stated conclusion](goal). -/
lemma energy_add_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (A B N : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hfenergy : (∫ x, f x ^ 2 ∂μ) ≤ A^2*N)
    (hgenergy : (∫ x, g x ^ 2 ∂μ) ≤ B^2*N) :
    (∫ x, (f x+g x)^2 ∂μ) ≤ (A+B)^2*N := by
  have hsum := eLpNorm_two_add_toReal_le μ f g hf hg
  have hf' := eLpNorm_two_toReal_le_of_energy μ f hf A N hA hN hfenergy
  have hg' := eLpNorm_two_toReal_le_of_energy μ g hg B N hB hN hgenergy
  have hnorm : (eLpNorm (f+g) 2 μ).toReal ≤ (A+B)*Real.sqrt N := by
    calc
      _ ≤ (eLpNorm f 2 μ).toReal+(eLpNorm g 2 μ).toReal := hsum
      _ ≤ A*Real.sqrt N+B*Real.sqrt N := add_le_add hf' hg'
      _ = _ := by ring
  have hsquare := (sq_le_sq₀ ENNReal.toReal_nonneg
    (mul_nonneg (add_nonneg hA hB) (Real.sqrt_nonneg _))).mpr hnorm
  rw [eLpNorm_two_toReal_sq μ (f+g) (hf.add hg), mul_pow, Real.sq_sqrt hN] at hsquare
  simpa only [Pi.add_apply] using hsquare

/-- A finite family of second-moment envelopes adds by repeated `L²` triangle inequalities. This statement assumes [the hf condition](hyp:hf), [the hA condition](hyp:hA), [the hN condition](hyp:hN), [the henergy condition](hyp:henergy). [This is the stated conclusion](goal). -/
lemma energy_finset_sum_le {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (s : Finset ι) (f : ι → Ω → ℝ) (hf : ∀ i ∈ s, MemLp (f i) 2 μ)
    (A : ι → ℝ) (N : ℝ) (hA : ∀ i ∈ s, 0 ≤ A i) (hN : 0 ≤ N)
    (henergy : ∀ i ∈ s, (∫ x, f i x ^ 2 ∂μ) ≤ (A i)^2*N) :
    (∫ x, (∑ i ∈ s, f i x)^2 ∂μ) ≤ (∑ i ∈ s, A i)^2*N := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hfi : MemLp (f i) 2 μ := hf i (Finset.mem_insert_self i s)
      have hfs : MemLp (fun x => ∑ j ∈ s, f j x) 2 μ := by
        apply memLp_finsetSum
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hiE := henergy i (Finset.mem_insert_self i s)
      have hsE := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hA j (Finset.mem_insert_of_mem hj))
        (fun j hj => henergy j (Finset.mem_insert_of_mem hj))
      have hadd := energy_add_le μ (f i) (fun x => ∑ j ∈ s, f j x) hfi hfs
        (A i) (∑ j ∈ s, A j) N (hA i (Finset.mem_insert_self i s))
        (Finset.sum_nonneg (fun j hj => hA j (Finset.mem_insert_of_mem hj))) hN hiE hsE
      simpa [Finset.sum_insert hi] using hadd

/-- A bounded scalar mark's conditional mean is dominated by its conditional second moment. This statement assumes [the hq condition](hyp:hq), [the hC condition](hyp:hC), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
lemma recordMarkMean_sq_le_conditional_sq (law : ObservedLaw)
    (q : Record → ℝ) (hq : Measurable q) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ o, |q o| ≤ C) (x : unitInterval) :
    recordMarkMean law q x ^ 2 ≤
      law.e x*(∫ y, q (x,true,y)^2 ∂law.Q true x)+
        (1-law.e x)*(∫ y, q (x,false,y)^2 ∂law.Q false x) := by
  have hmean (a : Bool) : (∫ y, q (x,a,y) ∂law.Q a x)^2 ≤
      ∫ y, q (x,a,y)^2 ∂law.Q a x := by
    have hm : Measurable (fun y => q (x,a,y)) :=
      hq.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have htop : MemLp (fun y => q (x,a,y)) ∞ (law.Q a x) :=
      memLp_top_of_bound hm.aestronglyMeasurable C
        (ae_of_all _ (fun y => by simpa [Real.norm_eq_abs] using hb (x,a,y)))
    have hv := variance_nonneg (μ := law.Q a x) (fun y => q (x,a,y))
    rw [variance_eq_sub (htop.mono_exponent le_top)] at hv
    simpa only [Pi.pow_apply] using sub_nonneg.mp hv
  have he0 := (law.e_range x).1
  have he1 := (law.e_range x).2
  have hconv : recordMarkMean law q x ^ 2 ≤
      law.e x*(∫ y, q (x,true,y) ∂law.Q true x)^2+
        (1-law.e x)*(∫ y, q (x,false,y) ∂law.Q false x)^2 := by
    unfold recordMarkMean
    have hz : 0 ≤ law.e x*(1-law.e x)*
        ((∫ y, q (x,true,y) ∂law.Q true x)-
          (∫ y, q (x,false,y) ∂law.Q false x))^2 := by positivity
    nlinarith
  exact hconv.trans (add_le_add
    (mul_le_mul_of_nonneg_left (hmean true) he0)
    (mul_le_mul_of_nonneg_left (hmean false) (sub_nonneg.mpr he1)))

/-- The conditional mean of either affine mark is bounded by the square root of its public second-moment envelope. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
lemma scoreMarkMean_abs_le_sqrt (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (T : ℝ) (hT : 1 ≤ T) (r : Bool) :
    ∀ᵐ x ∂design, |recordMarkMean law (scoreMark T r) x| ≤
      Real.sqrt (32*T^(2-v.p)) := by
  have hs := scoreMark_conditional_sq_le v hv law hm T hT r
  filter_upwards [hs] with x hx
  have hsq := recordMarkMean_sq_le_conditional_sq law (scoreMark T r)
    (scoreMark_measurable' T r) T (by linarith) (scoreMark_abs_le' T hT r) x
  have hnon : 0 ≤ 32*T^(2-v.p) := by positivity
  have hh : |recordMarkMean law (scoreMark T r) x|^2 ≤
      (Real.sqrt (32*T^(2-v.p)))^2 := by
    rw [sq_abs, Real.sq_sqrt hnon]
    exact hsq.trans hx
  exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp hh

/-- A pointwise conditional-pair envelope integrates against the exact feature isometry. This statement assumes [the hu condition](hyp:hu), [the hJ condition](hyp:hJ), [the hq condition](hyp:hq), [the hH condition](hyp:hH), [the hC condition](hyp:hC), [the hD condition](hyp:hD), [the hA condition](hyp:hA), [the hV condition](hyp:hV), [the hqbound condition](hyp:hqbound), [the hmoment condition](hyp:hmoment), [the henv condition](hyp:henv). [This is the stated conclusion](goal). -/
lemma conditional_pair_energy_of_envelope (law : ObservedLaw) (hu : UniformDesign law)
    (J : ℕ) (hJ : 0 < J) (u : Vec J) (q H : Record → ℝ)
    (hq : Measurable q) (hH : Measurable H) (C D A V : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (hqbound : ∀ o, |q o| ≤ C)
    (hmoment : ∀ᵐ x ∂design,
      law.e x*(∫ y, q (x,true,y)^2 ∂law.Q true x)+
        (1-law.e x)*(∫ y, q (x,false,y)^2 ∂law.Q false x) ≤ V)
    (henv : ∀ o, |H o| ≤ (1/2) * |inner ℝ u (featureMap J (X o))| * (D+A*|q o|)) :
    (∫ o, H o^2 ∂law.P) ≤ (1/2)*(D^2+A^2*V)*‖u‖^2 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let F : Record → ℝ := fun o => H o^2
  have hFm : Measurable F := hH.pow_const 2
  let B := ((1/2)*(‖u‖*Real.sqrt ((J:ℝ)*J))*(D+A*C))^2
  have hFb : ∀ o, ‖F o‖ ≤ B := by
    intro o
    have hi : |inner ℝ u (featureMap J (X o))| ≤
        ‖u‖*Real.sqrt ((J:ℝ)*J) :=
      (abs_real_inner_le_norm u _).trans
        (mul_le_mul_of_nonneg_left (featureMap_norm_bound J _) (norm_nonneg u))
    have hr : D+A*|q o| ≤ D+A*C := by
      simpa [add_comm] using add_le_add_left
        (mul_le_mul_of_nonneg_left (hqbound o) hA) D
    have hh := henv o
    have htot : |H o| ≤ (1/2)*(‖u‖*Real.sqrt ((J:ℝ)*J))*(D+A*C) := by
      calc
        _ ≤ (1/2) * |inner ℝ u (featureMap J (X o))| * (D+A*|q o|) := hh
        _ ≤ _ := by gcongr
    simp only [F, Real.norm_eq_abs, abs_sq]
    simpa only [F, B, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) htot 2
  rw [original_record_integral_arms law hu F hFm B hFb]
  have hpoint : ∀ᵐ x ∂design,
      law.e x*(∫ y, F (x,true,y) ∂law.Q true x)+
          (1-law.e x)*(∫ y, F (x,false,y) ∂law.Q false x) ≤
        (1/2)*(inner ℝ u (featureMap J x))^2*(D^2+A^2*V) := by
    filter_upwards [hmoment] with x hx
    have hqi (a : Bool) : Integrable (fun y => q (x,a,y)^2) (law.Q a x) := by
      have hm : Measurable (fun y => q (x,a,y)) :=
        hq.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
      exact ((memLp_top_of_bound hm.aestronglyMeasurable C
        (ae_of_all _ (fun y => by simpa [Real.norm_eq_abs] using hqbound (x,a,y)))).mono_exponent
          le_top).integrable_sq
    have hFi (a : Bool) : Integrable (fun y => F (x,a,y)) (law.Q a x) := by
      apply (integrable_const B).mono' (hFm.comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
      exact ae_of_all _ (fun y => hFb (x,a,y))
    have harm (a : Bool) : (∫ y, F (x,a,y) ∂law.Q a x) ≤
        (1/2)*(inner ℝ u (featureMap J x))^2*
          (D^2+A^2*(∫ y, q (x,a,y)^2 ∂law.Q a x)) := by
      let G : ℝ → ℝ := fun y => (1/2)*(inner ℝ u (featureMap J x))^2*
        (D^2+A^2*q (x,a,y)^2)
      have hGi : Integrable G (law.Q a x) := by
        have he : G = fun y =>
          ((1/2)*(inner ℝ u (featureMap J x))^2*D^2)+
            ((1/2)*(inner ℝ u (featureMap J x))^2*A^2)*q (x,a,y)^2 := by
          funext y
          dsimp [G]
          ring
        rw [he]
        exact (integrable_const _).add
          ((hqi a).const_mul ((1/2)*(inner ℝ u (featureMap J x))^2*A^2))
      calc
        _ ≤ ∫ y, G y ∂law.Q a x := by
          apply integral_mono (hFi a) hGi
          intro y
          have hh := henv (x,a,y)
          have hs : H (x,a,y)^2 ≤
              (1/2)*(inner ℝ u (featureMap J x))^2*(D^2+A^2*q (x,a,y)^2) := by
            rw [show X (x,a,y) = x by rfl] at hh
            have hp := pow_le_pow_left₀ (abs_nonneg _) hh 2
            rw [sq_abs, mul_pow, mul_pow, sq_abs] at hp
            have hscalar : (1/2)^2*(D+A*|q (x,a,y)|)^2 ≤
                (1/2)*(D^2+A^2*q (x,a,y)^2) := by
              have habs : |q (x,a,y)|^2 = q (x,a,y)^2 := sq_abs _
              nlinarith [sq_nonneg (D-A*|q (x,a,y)|)]
            have hmul := mul_le_mul_of_nonneg_left hscalar
              (sq_nonneg (inner ℝ u (featureMap J x)))
            nlinarith
          exact hs
        _ = _ := by
          have he : G = fun y =>
              ((1/2)*(inner ℝ u (featureMap J x))^2*D^2)+
                ((1/2)*(inner ℝ u (featureMap J x))^2*A^2)*q (x,a,y)^2 := by
            funext y
            dsimp [G]
            ring
          rw [he, integral_add (integrable_const _) ((hqi a).const_mul _),
            integral_const, integral_const_mul]
          simp
          ring
    have he0 := (law.e_range x).1
    have he1 := (law.e_range x).2
    have hh := add_le_add
      (mul_le_mul_of_nonneg_left (harm true) he0)
      (mul_le_mul_of_nonneg_left (harm false) (sub_nonneg.mpr he1))
    nlinarith [sq_nonneg (inner ℝ u (featureMap J x)),
      mul_nonneg (sq_nonneg A) (show
        0 ≤ V-(law.e x*(∫ y, q (x,true,y)^2 ∂law.Q true x)+
          (1-law.e x)*(∫ y, q (x,false,y)^2 ∂law.Q false x)) by linarith)]
  calc
    _ ≤ ∫ x, (1/2)*(inner ℝ u (featureMap J x))^2*(D^2+A^2*V) ∂design := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun x => add_nonneg
          (mul_nonneg (law.e_range x).1 (integral_nonneg (fun _ => sq_nonneg _)))
          (mul_nonneg (sub_nonneg.mpr (law.e_range x).2)
            (integral_nonneg (fun _ => sq_nonneg _))))
      · have hi := (((featureMap_memLp_top design J id measurable_id).const_inner u).mono_exponent
          le_top).integrable_sq.const_mul ((1/2)*(D^2+A^2*V))
        have he : (fun x => (1/2)*(inner ℝ u (featureMap J x))^2*(D^2+A^2*V)) =
            fun x => ((1/2)*(D^2+A^2*V))*(inner ℝ u (featureMap J (id x)))^2 := by
          funext x
          simp only [id_eq]
          ring
        rw [he]
        exact hi
      · exact hpoint
    _ = _ := by
      have he : (fun x => (1/2)*(inner ℝ u (featureMap J x))^2*(D^2+A^2*V)) =
          fun x => ((1/2)*(D^2+A^2*V))*(inner ℝ u (featureMap J x))^2 := by
        funext x
        ring
      rw [he, integral_const_mul, feature_isometry J hJ u]

/-- [the score Diff Pair measurable statement holds](goal). -/
@[fun_prop] lemma scoreDiffPair_measurable (J R : ℕ) (T : ℝ) (r : Bool) (u : Vec J) :
    Measurable (fun z : Record × Record => scoreDiffPair J R T r u z.1 z.2) := by
  unfold scoreDiffPair
  exact ((scoreDiffLeg_measurable J R T r u).add
    ((scoreDiffLeg_measurable J R T r u).comp measurable_swap)).div_const 2

/-- [the score Proj Pair measurable statement holds](goal). -/
@[fun_prop] lemma scoreProjPair_measurable (J R : ℕ) (T : ℝ) (r : Bool) (u : Vec J) :
    Measurable (fun z : Record × Record => scoreProjPair J R T r u z.1 z.2) := by
  unfold scoreProjPair
  exact ((scoreProjLeg_measurable J R T r u).add
    ((scoreProjLeg_measurable J R T r u).comp measurable_swap)).div_const 2

/-- The dyadic pair's one-record projection obeys the public smoothness and mark budgets. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hR condition](hyp:hR), [the hJR condition](hyp:hJR), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
lemma scoreDiffPair_conditional_energy_false_le (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law)
    (J R : ℕ) (hJ : 0 < J) (hR : 0 < R) (hJR : J ∣ R)
    (T : ℝ) (hT : 1 ≤ T) (u : Vec J) :
    (∫ o, (∫ z, scoreDiffPair J R T false u o z ∂law.P)^2 ∂law.P) ≤
      (1/2)*((110*(R:ℝ)^(-min v.α (min v.β v.γ))+20*T^(1-v.p))^2+
        (40*(R:ℝ)^(-v.α))^2*(32*T^(2-v.p)))*‖u‖^2 := by
  let H : Record → ℝ := fun o => ∫ z, scoreDiffPair J R T false u o z ∂law.P
  have hHm : Measurable H :=
    (scoreDiffPair_measurable J R T false u).stronglyMeasurable.integral_prod_right.measurable
  apply conditional_pair_energy_of_envelope law hm.uniform J hJ u (scoreMark T false) H
    (scoreMark_measurable' T false) hHm T
    (110*(R:ℝ)^(-min v.α (min v.β v.γ))+20*T^(1-v.p))
    (40*(R:ℝ)^(-v.α)) (32*T^(2-v.p))
    (by linarith) (by positivity) (by positivity) (by positivity)
    (scoreMark_abs_le' T hT false) (scoreMark_conditional_sq_le v hv law hm T hT false)
  intro o
  exact scoreDiffPair_conditional_abs_false_le v hv law hm J R hJ hR hJR T hT u o

/-- The treatment-mark dyadic projection has a smaller deterministic singleton envelope. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hR condition](hyp:hR), [the hJR condition](hyp:hJR), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
lemma scoreDiffPair_conditional_energy_true_le (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law)
    (J R : ℕ) (hJ : 0 < J) (hR : 0 < R) (hJR : J ∣ R)
    (T : ℝ) (hT : 1 ≤ T) (u : Vec J) :
    (∫ o, (∫ z, scoreDiffPair J R T true u o z ∂law.P)^2 ∂law.P) ≤
      2*(40*(R:ℝ)^(-v.α))^2*‖u‖^2 := by
  let H : Record → ℝ := fun o => ∫ z, scoreDiffPair J R T true u o z ∂law.P
  have hHm : Measurable H :=
    (scoreDiffPair_measurable J R T true u).stronglyMeasurable.integral_prod_right.measurable
  have h := conditional_pair_energy_of_envelope law hm.uniform J hJ u (scoreMark T true) H
    (scoreMark_measurable' T true) hHm T (2*(40*(R:ℝ)^(-v.α))) 0
    (32*T^(2-v.p)) (by linarith) (by positivity) (by norm_num) (by positivity)
    (scoreMark_abs_le' T hT true) (scoreMark_conditional_sq_le v hv law hm T hT true)
    (fun o => by
      dsimp [H]
      have hh := scoreDiffPair_conditional_abs_true_le v hv law hm J R hJ hR hJR T hT u o
      calc
        _ ≤ (40*(R:ℝ)^(-v.α)) * |inner ℝ u (featureMap J (X o))| := hh
        _ = (1/2) * |inner ℝ u (featureMap J (X o))| *
            (2*(40*(R:ℝ)^(-v.α))+0*|scoreMark T true o|) := by ring)
  dsimp [H] at h
  convert h using 1 <;> ring

/-- The initial projection pair has conditional-projection energy at most its mark budget. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hR condition](hyp:hR), [the hJR condition](hyp:hJR), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
lemma scoreProjPair_conditional_energy_le (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law)
    (J R : ℕ) (hJ : 0 < J) (hR : 0 < R) (hJR : J ∣ R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) :
    (∫ o, (∫ z, scoreProjPair J R T r u o z ∂law.P)^2 ∂law.P) ≤
      (32*T^(2-v.p))*‖u‖^2 := by
  let V := 32*T^(2-v.p)
  let H : Record → ℝ := fun o => ∫ z, scoreProjPair J R T r u o z ∂law.P
  have hHm : Measurable H :=
    (scoreProjPair_measurable J R T r u).stronglyMeasurable.integral_prod_right.measurable
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hmmean : ∀ x, |projOp R (recordMarkMean law (scoreMark T r)) x| ≤ Real.sqrt V :=
    projOp_abs_le_ae_bound R hR _ _ (Real.sqrt_nonneg _)
      (scoreMarkMean_abs_le_sqrt v hv law hm T hT r)
  have he : ∀ x, |projOp R law.e x| ≤ 1 :=
    projOp_abs_le_ae_bound R hR law.e 1 (by norm_num)
      (ae_of_all _ (fun x => by simpa [abs_of_nonneg (law.e_range x).1] using (law.e_range x).2))
  have h := conditional_pair_energy_of_envelope law hm.uniform J hJ u (scoreMark T r) H
    (scoreMark_measurable' T r) hHm T (Real.sqrt V) 1 V
    (by linarith) (Real.sqrt_nonneg _) (by norm_num) hV
    (scoreMark_abs_le' T hT r) (scoreMark_conditional_sq_le v hv law hm T hT r)
    (fun o => by
      dsimp [H]
      rw [scoreProjPair_conditional_formula law hm.uniform J R hJ hR hJR T hT r u o]
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      gcongr
      calc
        _ ≤ |treatment o| * |projOp R (recordMarkMean law (scoreMark T r)) (X o)|+
            |scoreMark T r o| * |projOp R law.e (X o)| := by
          simpa only [abs_mul] using abs_add_le
            (treatment o*projOp R (recordMarkMean law (scoreMark T r)) (X o))
            (scoreMark T r o*projOp R law.e (X o))
        _ ≤ 1*Real.sqrt V+|scoreMark T r o| * 1 := by
          exact add_le_add
            (mul_le_mul (treatment_abs_le_one o) (hmmean (X o)) (abs_nonneg _) (by norm_num))
            (mul_le_mul_of_nonneg_left (he (X o)) (abs_nonneg _))
        _ = Real.sqrt V+1*|scoreMark T r o| := by ring)
  dsimp [V, H] at h
  dsimp [V] at hV ⊢
  rw [Real.sq_sqrt hV] at h
  convert h using 1 <;> ring

/-- Integrating a squared kernel row against either affine mark costs its row energy times the public conditional second-moment envelope. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hG condition](hyp:hG), [the hC condition](hyp:hC), [the hR condition](hyp:hR), [the hGb condition](hyp:hGb), [the hrow condition](hyp:hrow), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
lemma scoreMark_kernel_row_energy_le (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law) (G : unitInterval → unitInterval → ℝ)
    (hG : Measurable (fun z : unitInterval × unitInterval => G z.1 z.2))
    (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hGb : ∀ x z, |G x z| ≤ C)
    (hrow : ∀ x, (∫ z, G x z^2 ∂design) ≤ R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (x : unitInterval) :
    (∫ o, G x (X o)^2*scoreMark T r o^2 ∂law.P) ≤
      R*(32*T^(2-v.p)) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let f : Record → ℝ := fun o => G x (X o)^2*scoreMark T r o^2
  have hfm : Measurable f :=
    ((hG.comp (measurable_const.prodMk measurable_fst)).pow_const 2).mul
      ((scoreMark_measurable' T r).pow_const 2)
  have hfb : ∀ o, ‖f o‖ ≤ C^2*T^2 := by
    intro o
    rw [Real.norm_eq_abs, abs_mul, abs_sq, abs_sq]
    have h1 := pow_le_pow_left₀ (abs_nonneg _) (hGb x (X o)) 2
    have h2 := pow_le_pow_left₀ (abs_nonneg _) (scoreMark_abs_le' T hT r o) 2
    rw [sq_abs] at h1 h2
    exact mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
  rw [original_record_integral_arms law hm.uniform f hfm (C^2*T^2) hfb]
  have hs := scoreMark_conditional_sq_le v hv law hm T hT r
  have hp : ∀ᵐ z ∂design,
      law.e z*(∫ y, f (z,true,y) ∂law.Q true z)+
          (1-law.e z)*(∫ y, f (z,false,y) ∂law.Q false z) ≤
        G x z^2*(32*T^(2-v.p)) := by
    filter_upwards [hs] with z hz
    have hi (a : Bool) : Integrable (fun y => scoreMark T r (z,a,y)^2) (law.Q a z) := by
      have hmeas : Measurable (fun y => scoreMark T r (z,a,y)) :=
        (scoreMark_measurable' T r).comp
          (measurable_const.prodMk (measurable_const.prodMk measurable_id))
      exact ((memLp_top_of_bound hmeas.aestronglyMeasurable T
        (ae_of_all _ (fun y => by simpa [Real.norm_eq_abs] using
          (scoreMark_abs_le' T hT r (z,a,y))))).mono_exponent le_top).integrable_sq
    have he (a : Bool) : (∫ y, f (z,a,y) ∂law.Q a z) =
        G x z^2*(∫ y, scoreMark T r (z,a,y)^2 ∂law.Q a z) := by
      dsimp [f]
      simp only [X]
      rw [integral_const_mul]
    rw [he true, he false]
    nlinarith [mul_nonneg (sq_nonneg (G x z))
      (show 0 ≤ 32*T^(2-v.p)-
        (law.e z*(∫ y, scoreMark T r (z,true,y)^2 ∂law.Q true z)+
          (1-law.e z)*(∫ y, scoreMark T r (z,false,y)^2 ∂law.Q false z)) by linarith)]
  calc
    _ ≤ ∫ z, G x z^2*(32*T^(2-v.p)) ∂design := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun z => add_nonneg
          (mul_nonneg (law.e_range z).1 (integral_nonneg (fun _ => by dsimp [f]; positivity)))
          (mul_nonneg (sub_nonneg.mpr (law.e_range z).2)
            (integral_nonneg (fun _ => by dsimp [f]; positivity))))
      · have hi : Integrable (fun z => G x z^2) design := by
          apply (integrable_const (C^2)).mono'
            ((hG.comp (measurable_const.prodMk measurable_id)).pow_const 2).aestronglyMeasurable
          exact ae_of_all _ (fun z => by
            rw [Real.norm_eq_abs, abs_sq]
            simpa [Function.comp_apply, sq_abs] using
              pow_le_pow_left₀ (abs_nonneg _) (hGb x z) 2)
        exact hi.mul_const _
      · exact hp
    _ ≤ R*(32*T^(2-v.p)) := by
      rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right (hrow x) (by positivity)

/-- Uniform design transports the histogram feature isometry to the original record law. This statement assumes [the hu condition](hyp:hu), [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
lemma feature_inner_record_energy_eq (law : ObservedLaw) (hu : UniformDesign law)
    (J : ℕ) (hJ : 0 < J) (u : Vec J) :
    (∫ o, (inner ℝ u (featureMap J (X o)))^2 ∂law.P) = ‖u‖^2 := by
  let I : unitInterval → ℝ := fun x => inner ℝ u (featureMap J x)
  have hIm : Measurable I :=
    (continuous_const.inner continuous_id).measurable.comp (measurable_featureMap J)
  have hIb : ∀ x, |I x| ≤ ‖u‖*Real.sqrt ((J:ℝ)*J) := fun x =>
    (abs_real_inner_le_norm u _).trans
      (mul_le_mul_of_nonneg_left (featureMap_norm_bound J x) (norm_nonneg u))
  rw [original_record_integral_arms law hu (fun o => I (X o)^2)
    ((hIm.comp measurable_fst).pow_const 2) ((‖u‖*Real.sqrt ((J:ℝ)*J))^2)
    (fun o => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hIb (X o)) 2)]
  simp only [X, integral_const, probReal_univ, one_smul, smul_eq_mul]
  have he : (fun x => law.e x*(1*I x^2)+(1-law.e x)*(1*I x^2)) =
      fun x => (inner ℝ u (featureMap J x))^2 := by
    funext x
    dsimp [I]
    ring
  rw [he, feature_isometry J hJ u]

/-- One ordered projection leg has raw pair energy bounded by rank times mark variance. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hR condition](hyp:hR), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
lemma scoreProjLeg_energy_le (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (J R : ℕ) (hJ : 0 < J) (hR : 0 < R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) :
    (∫ z : Record × Record, scoreProjLeg J R T r u z.1 z.2^2 ∂law.P.prod law.P) ≤
      (R:ℝ)*(32*T^(2-v.p))*‖u‖^2 := by
  have hleg2 : Integrable (fun z : Record × Record =>
      scoreProjLeg J R T r u z.1 z.2^2) (law.P.prod law.P) := by
    have hm2 := (scoreProjLeg_measurable J R T r u).pow_const 2
    apply (integrable_const (((R:ℝ)*T*‖u‖*Real.sqrt ((J:ℝ)*J))^2)).mono'
      hm2.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
        (scoreProjLeg_abs_le J R hR T hT r u z.1 z.2) 2)
  rw [integral_prod _ hleg2]
  have hinner : ∀ o, (∫ z, scoreProjLeg J R T r u o z^2 ∂law.P) ≤
      (R:ℝ)*(32*T^(2-v.p))*(inner ℝ u (featureMap J (X o)))^2 := by
    intro o
    have hk := scoreMark_kernel_row_energy_le v hv law hm (projKernel R)
      (measurable_projKernel R) R R (by positivity) (by positivity)
      (fun x z => (histogram_kernel_bounds R hR x z).2)
      (fun x => le_of_eq (projection_rows R hR x).2) T hT r (X o)
    have ht : treatment o^2 ≤ 1 := by
      have := pow_le_pow_left₀ (abs_nonneg _) (treatment_abs_le_one o) 2
      simpa [sq_abs] using this
    have hn : 0 ≤ (R:ℝ)*(32*T^(2-v.p)) := by positivity
    have heq : (∫ z, scoreProjLeg J R T r u o z^2 ∂law.P) =
        (treatment o^2*(inner ℝ u (featureMap J (X o)))^2)*
          (∫ z, projKernel R (X o) (X z)^2*scoreMark T r z^2 ∂law.P) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by unfold scoreProjLeg; ring)
    rw [heq]
    calc
      _ ≤ (treatment o^2*(inner ℝ u (featureMap J (X o)))^2)*
          ((R:ℝ)*(32*T^(2-v.p))) :=
        mul_le_mul_of_nonneg_left hk
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ 1*(inner ℝ u (featureMap J (X o)))^2*((R:ℝ)*(32*T^(2-v.p))) := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ ∫ o, (R:ℝ)*(32*T^(2-v.p))*(inner ℝ u (featureMap J (X o)))^2 ∂law.P := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun _ => integral_nonneg (fun _ => sq_nonneg _))
      · have hi := (((featureMap_memLp_top law.P J X measurable_fst).const_inner u).mono_exponent
          le_top).integrable_sq.const_mul ((R:ℝ)*(32*T^(2-v.p)))
        convert hi using 1 <;> ring
      · exact ae_of_all _ hinner
    _ = _ := by
      rw [show (∫ o, (R:ℝ)*(32*T^(2-v.p))*(inner ℝ u (featureMap J (X o)))^2 ∂law.P) =
          (R:ℝ)*(32*T^(2-v.p))*∫ o, (inner ℝ u (featureMap J (X o)))^2 ∂law.P by
            rw [integral_const_mul]]
      rw [feature_inner_record_energy_eq law hm.uniform J hJ u]

/-- One ordered dyadic-difference leg has raw pair energy bounded by rank times mark variance. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hR condition](hyp:hR), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
lemma scoreDiffLeg_energy_le (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (J R : ℕ) (hJ : 0 < J) (hR : 0 < R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) :
    (∫ z : Record × Record, scoreDiffLeg J R T r u z.1 z.2^2 ∂law.P.prod law.P) ≤
      (R:ℝ)*(32*T^(2-v.p))*‖u‖^2 := by
  have hleg2 : Integrable (fun z : Record × Record =>
      scoreDiffLeg J R T r u z.1 z.2^2) (law.P.prod law.P) := by
    have hm2 := (scoreDiffLeg_measurable J R T r u).pow_const 2
    apply (integrable_const (((3*(R:ℝ))*T*‖u‖*Real.sqrt ((J:ℝ)*J))^2)).mono'
      hm2.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
        (scoreDiffLeg_abs_le J R hR T hT r u z.1 z.2) 2)
  rw [integral_prod _ hleg2]
  have hinner : ∀ o, (∫ z, scoreDiffLeg J R T r u o z^2 ∂law.P) ≤
      (R:ℝ)*(32*T^(2-v.p))*(inner ℝ u (featureMap J (X o)))^2 := by
    intro o
    have hk := scoreMark_kernel_row_energy_le v hv law hm (diffKernel R)
      ((measurable_projKernel (2*R)).sub (measurable_projKernel R)) (3*(R:ℝ)) R
      (by positivity) (by positivity)
      (fun x z => by
        unfold diffKernel
        calc
          _ ≤ |projKernel (2*R) x z|+|projKernel R x z| := abs_sub _ _
          _ ≤ ((2*R:ℕ):ℝ)+(R:ℝ) := add_le_add
            (histogram_kernel_bounds (2*R) (by positivity) x z).2
            (histogram_kernel_bounds R hR x z).2
          _ = _ := by push_cast; ring)
      (fun x => le_of_eq (diffKernel_row_energy R hR x)) T hT r (X o)
    have ht : treatment o^2 ≤ 1 := by
      have hh := pow_le_pow_left₀ (abs_nonneg _) (treatment_abs_le_one o) 2
      simpa [sq_abs] using hh
    have heq : (∫ z, scoreDiffLeg J R T r u o z^2 ∂law.P) =
        (treatment o^2*(inner ℝ u (featureMap J (X o)))^2)*
          (∫ z, diffKernel R (X o) (X z)^2*scoreMark T r z^2 ∂law.P) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by unfold scoreDiffLeg; ring)
    rw [heq]
    calc
      _ ≤ (treatment o^2*(inner ℝ u (featureMap J (X o)))^2)*
          ((R:ℝ)*(32*T^(2-v.p))) :=
        mul_le_mul_of_nonneg_left hk (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ 1*(inner ℝ u (featureMap J (X o)))^2*((R:ℝ)*(32*T^(2-v.p))) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∫ o, (R:ℝ)*(32*T^(2-v.p))*(inner ℝ u (featureMap J (X o)))^2 ∂law.P := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun _ => integral_nonneg (fun _ => sq_nonneg _))
      · have hi := (((featureMap_memLp_top law.P J X measurable_fst).const_inner u).mono_exponent
          le_top).integrable_sq.const_mul ((R:ℝ)*(32*T^(2-v.p)))
        convert hi using 1 <;> ring
      · exact ae_of_all _ hinner
    _ = _ := by
      rw [show (∫ o, (R:ℝ)*(32*T^(2-v.p))*(inner ℝ u (featureMap J (X o)))^2 ∂law.P) =
          (R:ℝ)*(32*T^(2-v.p))*∫ o, (inner ℝ u (featureMap J (X o)))^2 ∂law.P by
            rw [integral_const_mul]]
      rw [feature_inner_record_energy_eq law hm.uniform J hJ u]

/-- Symmetrizing an ordered square-integrable leg does not increase its second moment. This statement assumes [the hleg condition](hyp:hleg), [the hC condition](hyp:hC), [the hb condition](hyp:hb), [the henergy condition](hyp:henergy). [This is the stated conclusion](goal). -/
lemma symmetrized_leg_energy_le (law : ObservedLaw) (leg : Record → Record → ℝ)
    (hleg : Measurable (fun z : Record × Record => leg z.1 z.2))
    (C E : ℝ) (hC : 0 ≤ C) (hb : ∀ x y, |leg x y| ≤ C)
    (henergy : (∫ z : Record × Record, leg z.1 z.2^2 ∂law.P.prod law.P) ≤ E) :
    (∫ z : Record × Record, ((leg z.1 z.2+leg z.2 z.1)/2)^2 ∂law.P.prod law.P) ≤ E := by
  let μ := law.P.prod law.P
  have htop : MemLp (fun z : Record × Record => leg z.1 z.2) ∞ μ :=
    memLp_top_of_bound hleg.aestronglyMeasurable C
      (ae_of_all _ (fun z => by simpa [Real.norm_eq_abs] using hb z.1 z.2))
  have hsquare := (htop.mono_exponent le_top).integrable_sq
  have hswap : Integrable (fun z : Record × Record => leg z.2 z.1^2) μ := by
    have htopswap : MemLp (fun z : Record × Record => leg z.2 z.1) ∞ μ := by
      change MemLp ((fun z : Record × Record => leg z.1 z.2) ∘ Prod.swap) ∞ μ
      exact htop.comp_measurePreserving Measure.measurePreserving_swap
    exact (htopswap.mono_exponent le_top).integrable_sq
  calc
    _ ≤ ∫ z : Record × Record, (leg z.1 z.2^2+leg z.2 z.1^2)/2 ∂μ := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun _ => sq_nonneg _)
      · exact (hsquare.add hswap).div_const 2
      · exact ae_of_all _ (fun z => by nlinarith [sq_nonneg (leg z.1 z.2-leg z.2 z.1)])
    _ = (1/2)*((∫ z : Record × Record, leg z.1 z.2^2 ∂μ)+
        ∫ z : Record × Record, leg z.2 z.1^2 ∂μ) := by
      rw [integral_div, integral_add hsquare hswap]
      ring
    _ = ∫ z : Record × Record, leg z.1 z.2^2 ∂μ := by
      have he : (∫ z : Record × Record, leg z.2 z.1^2 ∂μ) =
          ∫ z : Record × Record, leg z.1 z.2^2 ∂μ := by
        change (∫ z : Record × Record,
          (fun w : Record × Record => leg w.1 w.2^2) (Prod.swap z) ∂μ) = _
        exact Measure.measurePreserving_swap.integral_comp
          (@MeasurableEquiv.prodComm Record Record _ _).measurableEmbedding
          (fun w : Record × Record => leg w.1 w.2^2)
      rw [he]
      ring
    _ ≤ E := henergy

/-- Under [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hR condition](hyp:hR), [the hT condition](hyp:hT), [the score Proj Pair energy le statement holds](goal). -/
lemma scoreProjPair_energy_le (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (J R : ℕ) (hJ : 0 < J) (hR : 0 < R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) :
    (∫ z : Record × Record, scoreProjPair J R T r u z.1 z.2^2 ∂law.P.prod law.P) ≤
      (R:ℝ)*(32*T^(2-v.p))*‖u‖^2 := by
  unfold scoreProjPair
  apply symmetrized_leg_energy_le law (scoreProjLeg J R T r u)
    (scoreProjLeg_measurable J R T r u)
    ((R:ℝ)*T*‖u‖*Real.sqrt ((J:ℝ)*J)) _ (by positivity)
  · exact fun x y => scoreProjLeg_abs_le J R hR T hT r u x y
  · exact scoreProjLeg_energy_le v hv law hm J R hJ hR T hT r u

/-- Under [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hR condition](hyp:hR), [the hT condition](hyp:hT), [the score Diff Pair energy le statement holds](goal). -/
lemma scoreDiffPair_energy_le (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (J R : ℕ) (hJ : 0 < J) (hR : 0 < R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) :
    (∫ z : Record × Record, scoreDiffPair J R T r u z.1 z.2^2 ∂law.P.prod law.P) ≤
      (R:ℝ)*(32*T^(2-v.p))*‖u‖^2 := by
  unfold scoreDiffPair
  apply symmetrized_leg_energy_le law (scoreDiffLeg J R T r u)
    (scoreDiffLeg_measurable J R T r u)
    ((3*(R:ℝ))*T*‖u‖*Real.sqrt ((J:ℝ)*J)) _ (by positivity)
  · exact fun x y => scoreDiffLeg_abs_le J R hR T hT r u x y
  · exact scoreDiffLeg_energy_le v hv law hm J R hJ hR T hT r u

end CausalSmith.Stat.FinitepHomogeneityDensegamma

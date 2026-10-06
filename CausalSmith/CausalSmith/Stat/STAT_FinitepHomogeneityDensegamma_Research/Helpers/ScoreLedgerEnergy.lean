module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreEnergyBounds
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.MeanErrorBounds

/-! Assembly of the public singleton and canonical energy ledgers. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Integrating one coordinate of an `L²` function over a probability law remains in `L²`. This statement assumes [the hH condition](hyp:hH). [This is the stated conclusion](goal). -/
lemma memLp_integral_prod_right {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : A × B → ℝ) (hH : MemLp H 2 (μ.prod ν)) :
    MemLp (fun a => ∫ b, H (a,b) ∂ν) 2 μ := by
  have hsq : Integrable (fun z => H z ^ 2) (μ.prod ν) := hH.integrable_sq
  have hm : AEStronglyMeasurable (fun a => ∫ b, H (a,b) ∂ν) μ :=
    hH.aestronglyMeasurable.integral_prod_right'
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  have hq : Integrable (fun a => ∫ b, H (a,b)^2 ∂ν) μ := hsq.integral_prod_left
  apply hq.mono_nonneg (hm.pow 2) (ae_of_all _ fun _ => sq_nonneg _)
  filter_upwards [hH.aestronglyMeasurable.prodMk_left, hsq.prod_right_ae]
    with a hameas hasq
  have ha : MemLp (fun b => H (a,b)) 2 ν :=
    (memLp_two_iff_integrable_sq hameas).2 hasq
  have hv := variance_nonneg (fun b => H (a,b)) ν
  rw [variance_eq_sub ha] at hv
  simpa only [Pi.pow_apply] using (sub_nonneg.mp hv)

/-- Centering and scaling a square-integrable variable costs at most the corresponding fraction of its uncentered second moment. This statement assumes [the hh condition](hyp:hh). [This is the stated conclusion](goal). -/
lemma centered_half_energy_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → ℝ) (hh : MemLp h 2 P) :
    (∫ x, ((h x-(∫ z, h z ∂P))/2)^2 ∂P) ≤ (1/4)*(∫ x, h x^2 ∂P) := by
  have hv := variance_le_expectation_sq hh.1
  have hcenter : (∫ x, (h x-(∫ z, h z ∂P))^2 ∂P) = variance h P := by
    rw [variance_eq_integral hh.1.aemeasurable]
  have he : (∫ x, ((h x-(∫ z, h z ∂P))/2)^2 ∂P) =
      (1/4)*(∫ x, (h x-(∫ z, h z ∂P))^2 ∂P) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  rw [he]
  rw [hcenter]
  exact mul_le_mul_of_nonneg_left hv (by norm_num)

/-- A pair singleton projection has no more energy than its uncentered one-record conditional mean. This statement assumes [the hg condition](hyp:hg), [the hL2 condition](hyp:hL2). [This is the stated conclusion](goal). -/
lemma singletonProjection_energy_le_conditional (law : ObservedLaw)
    (g : Record → Record → ℝ)
    (hg : Measurable (fun z : Record × Record => g z.1 z.2))
    (hL2 : MemLp (fun z : Record × Record => g z.1 z.2) 2 (law.P.prod law.P)) :
    (∫ x, singletonProjection law.P g x^2 ∂law.P) ≤
      ∫ x, (∫ y, g x y ∂law.P)^2 ∂law.P := by
  rw [← singletonProjection_variance law.P g hg hL2]
  unfold singletonProjection
  rw [variance_sub_const
    (hg.stronglyMeasurable.integral_prod_right.aestronglyMeasurable) (pairMean law.P g)]
  exact variance_le_expectation_sq
    hg.stronglyMeasurable.integral_prod_right.aestronglyMeasurable

/-- The single-correction pair is exactly the negative initial projection pair. [This is the stated conclusion](goal). -/
lemma singleScalarPair_eq_neg_scoreProjPair (J K : ℕ) (T : ℝ) (r : Bool)
    (u : Vec J) (o z : Record) :
    singleScalarPair J K T r u o z = -scoreProjPair J K T r u o z := by
  unfold singleScalarPair singlePairKernel scoreProjPair scoreProjLeg scoreMark
  simp only [inner_smul_right, inner_add_right, smul_eq_mul]
  ring

/-- Under [the hR condition](hyp:hR), [the hT condition](hyp:hT), [the score Proj Pair mem Lp two statement holds](goal). -/
lemma scoreProjPair_memLp_two (law : ObservedLaw) (J R : ℕ) (hR : 0 < R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) :
    MemLp (fun z : Record × Record => scoreProjPair J R T r u z.1 z.2)
      2 (law.P.prod law.P) := by
  apply (memLp_top_of_bound (scoreProjPair_measurable J R T r u).aestronglyMeasurable
    ((R:ℝ)*T*‖u‖*Real.sqrt ((J:ℝ)*J)) ?_).mono_exponent le_top
  exact ae_of_all _ (fun z => by
    unfold scoreProjPair
    rw [Real.norm_eq_abs]
    rw [abs_div]
    calc
      _ ≤ (|scoreProjLeg J R T r u z.1 z.2|+
          |scoreProjLeg J R T r u z.2 z.1|)/|2| := by gcongr; exact abs_add_le _ _
      _ ≤ (((R:ℝ)*T*‖u‖*Real.sqrt ((J:ℝ)*J))+((R:ℝ)*T*‖u‖*
          Real.sqrt ((J:ℝ)*J)))/|2| := by
        gcongr <;> exact scoreProjLeg_abs_le J R hR T hT r u _ _
      _ = _ := by norm_num)

/-- Under [the hR condition](hyp:hR), [the hT condition](hyp:hT), [the score Diff Pair mem Lp two statement holds](goal). -/
lemma scoreDiffPair_memLp_two (law : ObservedLaw) (J R : ℕ) (hR : 0 < R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) :
    MemLp (fun z : Record × Record => scoreDiffPair J R T r u z.1 z.2)
      2 (law.P.prod law.P) := by
  apply (memLp_top_of_bound (scoreDiffPair_measurable J R T r u).aestronglyMeasurable
    ((3*(R:ℝ))*T*‖u‖*Real.sqrt ((J:ℝ)*J)) ?_).mono_exponent le_top
  exact ae_of_all _ (fun z => by
    unfold scoreDiffPair
    rw [Real.norm_eq_abs]
    rw [abs_div]
    calc
      _ ≤ (|scoreDiffLeg J R T r u z.1 z.2|+
          |scoreDiffLeg J R T r u z.2 z.1|)/|2| := by gcongr; exact abs_add_le _ _
      _ ≤ (((3*(R:ℝ))*T*‖u‖*Real.sqrt ((J:ℝ)*J))+((3*(R:ℝ))*T*‖u‖*
          Real.sqrt ((J:ℝ)*J)))/|2| := by
        gcongr <;> exact scoreDiffLeg_abs_le J R hR T hT r u _ _
      _ = _ := by norm_num)

/-- Under [the hR condition](hyp:hR), [the hT condition](hyp:hT), [the score Proj Pair row integrable statement holds](goal). -/
lemma scoreProjPair_row_integrable (law : ObservedLaw) (J R : ℕ) (hR : 0 < R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) (o : Record) :
    Integrable (fun z => scoreProjPair J R T r u o z) law.P := by
  have hm : Measurable (fun z => scoreProjPair J R T r u o z) :=
    (scoreProjPair_measurable J R T r u).comp (measurable_const.prodMk measurable_id)
  apply (memLp_top_of_bound hm.aestronglyMeasurable
    ((R:ℝ)*T*‖u‖*Real.sqrt ((J:ℝ)*J)) ?_).integrable (by norm_num)
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs]
    unfold scoreProjPair
    rw [abs_div]
    calc
      _ ≤ (|scoreProjLeg J R T r u o z|+|scoreProjLeg J R T r u z o|)/|2| := by
        gcongr; exact abs_add_le _ _
      _ ≤ (((R:ℝ)*T*‖u‖*Real.sqrt ((J:ℝ)*J))+((R:ℝ)*T*‖u‖*
          Real.sqrt ((J:ℝ)*J)))/|2| := by
        gcongr <;> exact scoreProjLeg_abs_le J R hR T hT r u _ _
      _ = _ := by norm_num)

/-- Under [the hR condition](hyp:hR), [the hT condition](hyp:hT), [the score Diff Pair row integrable statement holds](goal). -/
lemma scoreDiffPair_row_integrable (law : ObservedLaw) (J R : ℕ) (hR : 0 < R)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) (o : Record) :
    Integrable (fun z => scoreDiffPair J R T r u o z) law.P := by
  have hm : Measurable (fun z => scoreDiffPair J R T r u o z) :=
    (scoreDiffPair_measurable J R T r u).comp (measurable_const.prodMk measurable_id)
  apply (memLp_top_of_bound hm.aestronglyMeasurable
    ((3*(R:ℝ))*T*‖u‖*Real.sqrt ((J:ℝ)*J)) ?_).integrable (by norm_num)
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs]
    unfold scoreDiffPair
    rw [abs_div]
    calc
      _ ≤ (|scoreDiffLeg J R T r u o z|+|scoreDiffLeg J R T r u z o|)/|2| := by
        gcongr; exact abs_add_le _ _
      _ ≤ (((3*(R:ℝ))*T*‖u‖*Real.sqrt ((J:ℝ)*J))+((3*(R:ℝ))*T*‖u‖*
          Real.sqrt ((J:ℝ)*J)))/|2| := by
        gcongr <;> exact scoreDiffLeg_abs_le J R hR T hT r u _ _
      _ = _ := by norm_num)

/-- Under [the hJ condition](hyp:hJ), [the hT0 condition](hyp:hT0), [the hT condition](hyp:hT), [the multires Scalar Pair conditional eq statement holds](goal). -/
lemma multiresScalarPair_conditional_eq (law : ObservedLaw)
    (J L : ℕ) (hJ : 0 < J) (T0 : ℝ) (hT0 : 1 ≤ T0) (T : Fin L → ℝ)
    (hT : ∀ j, 1 ≤ T j) (r : Bool) (u : Vec J) (o : Record) :
    (∫ z, multiresScalarPair J L T0 T r u o z ∂law.P) =
      -(∫ z, scoreProjPair J J T0 r u o z ∂law.P)-
        ∑ j : Fin L, ∫ z, scoreDiffPair J (2^j.val*J) (T j) r u o z ∂law.P := by
  rw [show (fun z => multiresScalarPair J L T0 T r u o z) =
      fun z => -scoreProjPair J J T0 r u o z-
        ∑ j : Fin L, scoreDiffPair J (2^j.val*J) (T j) r u o z by
      funext z; exact multiresScalarPair_eq_scoreDiffPairs J L T0 T r u o z]
  have hp : Integrable (fun z => -scoreProjPair J J T0 r u o z) law.P := by
    convert (scoreProjPair_row_integrable law J J hJ T0 hT0 r u o).neg using 1
    funext z
    simp
  have hs : Integrable (fun z => ∑ j : Fin L,
      scoreDiffPair J (2^j.val*J) (T j) r u o z) law.P := by
    exact integrable_finsetSum _ (fun j _ => scoreDiffPair_row_integrable law J
      (2^j.val*J) (by positivity) (T j) (hT j) r u o)
  rw [integral_sub hp hs, integral_neg, integral_finset_sum]
  intro j hj
  exact scoreDiffPair_row_integrable law J (2^j.val*J) (by positivity)
    (T j) (hT j) r u o

/-- The multiresolution pair's conditional mean obeys the sum of the main and levelwise public singleton envelopes. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hT0 condition](hyp:hT0), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
lemma multiresScalarPair_conditional_energy_le (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law) (J L : ℕ) (hJ : 0 < J)
    (T0 : ℝ) (hT0 : 1 ≤ T0) (T : Fin L → ℝ) (hT : ∀ j, 1 ≤ T j)
    (r : Bool) (u : Vec J) :
    (∫ o, (∫ z, multiresScalarPair J L T0 T r u o z ∂law.P)^2 ∂law.P) ≤
      (Real.sqrt (32*T0^(2-v.p))+
        ∑ j : Fin L, 2*((110*((2^j.val*J:ℕ):ℝ)^(-min v.α (min v.β v.γ))+
          20*(T j)^(1-v.p))+
          (40*((2^j.val*J:ℕ):ℝ)^(-v.α))*Real.sqrt (32*(T j)^(2-v.p))))^2*‖u‖^2 := by
  let μ := law.P
  let f0 : Record → ℝ := fun o => -(∫ z, scoreProjPair J J T0 r u o z ∂law.P)
  let fj : Fin L → Record → ℝ := fun j o =>
    -(∫ z, scoreDiffPair J (2^j.val*J) (T j) r u o z ∂law.P)
  let C : Fin L → ℝ := fun j => 2*((110*((2^j.val*J:ℕ):ℝ)^(-min v.α (min v.β v.γ))+
    20*(T j)^(1-v.p))+(40*((2^j.val*J:ℕ):ℝ)^(-v.α))*Real.sqrt (32*(T j)^(2-v.p)))
  have hV0 : 0 ≤ 32*T0^(2-v.p) := by positivity
  have hf0 : MemLp f0 2 μ := by
    have hb := memLp_integral_prod_right law.P law.P
      (fun z : Record × Record => scoreProjPair J J T0 r u z.1 z.2)
      (scoreProjPair_memLp_two law J J hJ T0 hT0 r u)
    dsimp [f0, μ]
    convert hb.neg using 1
    funext o
    simp
  have hfj : ∀ j : Fin L, MemLp (fj j) 2 μ := by
    intro j
    have hb := memLp_integral_prod_right law.P law.P
      (fun z : Record × Record => scoreDiffPair J (2^j.val*J) (T j) r u z.1 z.2)
      (scoreDiffPair_memLp_two law J (2^j.val*J) (by positivity) (T j) (hT j) r u)
    dsimp [fj, μ]
    convert hb.neg using 1
    funext o
    simp
  have hf0e : (∫ o, f0 o^2 ∂μ) ≤ (Real.sqrt (32*T0^(2-v.p)))^2*‖u‖^2 := by
    have hb := scoreProjPair_conditional_energy_le v hv law hm J J hJ hJ
      (dvd_refl J) T0 hT0 r u
    dsimp [f0, μ]
    rw [Real.sq_sqrt hV0]
    simpa only [neg_sq] using hb
  have hCe (j : Fin L) : 0 ≤ C j := by
    dsimp [C]
    have htj : 0 ≤ T j := le_trans (by norm_num) (hT j)
    exact mul_nonneg (by norm_num) (add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
        (mul_nonneg (by norm_num) (Real.rpow_nonneg htj _)))
      (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
        (Real.sqrt_nonneg _)))
  have hfje : ∀ j : Fin L, (∫ o, fj j o^2 ∂μ) ≤ (C j)^2*‖u‖^2 := by
    intro j
    let R : ℕ := 2^j.val*J
    let D : ℝ := 110*(R:ℝ)^(-min v.α (min v.β v.γ))+20*(T j)^(1-v.p)
    let A : ℝ := 40*(R:ℝ)^(-v.α)
    let V : ℝ := 32*(T j)^(2-v.p)
    have htj : 0 ≤ T j := le_trans (by norm_num) (hT j)
    have hD : 0 ≤ D := by
      dsimp [D]
      exact add_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
        (mul_nonneg (by norm_num) (Real.rpow_nonneg htj _))
    have hA : 0 ≤ A := by
      dsimp [A]
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)
    have hV : 0 ≤ V := by
      dsimp [V]
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg htj _)
    have hVone : 1 ≤ V := by
      have hp : 1 ≤ (T j)^(2-v.p) := Real.one_le_rpow (hT j) (by linarith [hv.1.2])
      dsimp [V]
      nlinarith
    have hsV : (Real.sqrt V)^2 = V := Real.sq_sqrt hV
    have hscalar_false : (1/2)*(D^2+A^2*V) ≤ (2*(D+A*Real.sqrt V))^2 := by
      have hX : 0 ≤ A*Real.sqrt V := mul_nonneg hA (Real.sqrt_nonneg _)
      calc
        _ = (1/2)*(D^2+(A*Real.sqrt V)^2) := by nlinarith [hsV]
        _ ≤ (2*(D+A*Real.sqrt V))^2 := by
          nlinarith [sq_nonneg D, sq_nonneg (A*Real.sqrt V), mul_nonneg hD hX]
    have hscalar_true : 2*A^2 ≤ (2*(D+A*Real.sqrt V))^2 := by
      have hAsq : A^2 ≤ A^2*V := by nlinarith [sq_nonneg A]
      have hX : 0 ≤ A*Real.sqrt V := mul_nonneg hA (Real.sqrt_nonneg _)
      calc
        _ ≤ 2*(A^2*V) := by linarith
        _ = 2*(A*Real.sqrt V)^2 := by nlinarith [hsV]
        _ ≤ (2*(D+A*Real.sqrt V))^2 := by
          nlinarith [sq_nonneg D, sq_nonneg (A*Real.sqrt V), mul_nonneg hD hX]
    cases r
    · have hb := scoreDiffPair_conditional_energy_false_le v hv law hm J R hJ
        (by dsimp [R]; positivity) (by dsimp [R]; exact dvd_mul_left J (2^j.val))
        (T j) (hT j) u
      dsimp [fj, μ]
      have hb' := hb.trans (mul_le_mul_of_nonneg_right hscalar_false (sq_nonneg ‖u‖))
      simpa only [neg_sq, R, D, A, V, C] using hb'
    · have hb := scoreDiffPair_conditional_energy_true_le v hv law hm J R hJ
        (by dsimp [R]; positivity) (by dsimp [R]; exact dvd_mul_left J (2^j.val))
        (T j) (hT j) u
      dsimp [fj, μ]
      have hb' := hb.trans (mul_le_mul_of_nonneg_right hscalar_true (sq_nonneg ‖u‖))
      simpa only [neg_sq, R, D, A, V, C] using hb'
  have hsum := energy_finset_sum_le μ Finset.univ fj (fun j _ => hfj j) C (‖u‖^2)
    (fun j _ => hCe j) (sq_nonneg ‖u‖) (fun j _ => hfje j)
  have hall := energy_add_le μ f0 (fun o => ∑ j : Fin L, fj j o) hf0
    (memLp_finsetSum Finset.univ fun j _ => hfj j) (Real.sqrt (32*T0^(2-v.p)))
    (∑ j : Fin L, C j) (‖u‖^2) (Real.sqrt_nonneg _)
    (Finset.sum_nonneg (fun j _ => hCe j)) (sq_nonneg ‖u‖) hf0e hsum
  have heq : (fun o => ∫ z, multiresScalarPair J L T0 T r u o z ∂law.P) =
      fun o => f0 o+∑ j : Fin L, fj j o := by
    funext o
    rw [multiresScalarPair_conditional_eq law J L hJ T0 hT0 T hT r u o]
    simp only [f0, fj]
    rw [Finset.sum_neg_distrib]
    ring
  simp_rw [congrFun heq]
  simpa only [μ, C] using hall

/-- The raw multiresolution pair energy is the square of the sum of the rank-weighted level budgets. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hT0 condition](hyp:hT0), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
lemma multiresScalarPair_energy_le (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law) (J L : ℕ) (hJ : 0 < J)
    (T0 : ℝ) (hT0 : 1 ≤ T0) (T : Fin L → ℝ) (hT : ∀ j, 1 ≤ T j)
    (r : Bool) (u : Vec J) :
    (∫ z : Record × Record, multiresScalarPair J L T0 T r u z.1 z.2^2
      ∂law.P.prod law.P) ≤
      (Real.sqrt ((J:ℝ)*(32*T0^(2-v.p)))+
        ∑ j : Fin L, Real.sqrt (((2^(j.val+1)*J:ℕ):ℝ)*(32*(T j)^(2-v.p))))^2*‖u‖^2 := by
  let μ := law.P.prod law.P
  let f0 : Record × Record → ℝ := fun z => -scoreProjPair J J T0 r u z.1 z.2
  let fj : Fin L → Record × Record → ℝ := fun j z =>
    -scoreDiffPair J (2^j.val*J) (T j) r u z.1 z.2
  let C : Fin L → ℝ := fun j =>
    Real.sqrt (((2^(j.val+1)*J:ℕ):ℝ)*(32*(T j)^(2-v.p)))
  have hV0 : 0 ≤ (J:ℝ)*(32*T0^(2-v.p)) := by positivity
  have hf0 : MemLp f0 2 μ := by
    dsimp [f0, μ]
    convert (scoreProjPair_memLp_two law J J hJ T0 hT0 r u).neg using 1
    funext z
    simp
  have hfj : ∀ j : Fin L, MemLp (fj j) 2 μ := by
    intro j
    dsimp [fj, μ]
    convert (scoreDiffPair_memLp_two law J (2^j.val*J) (by positivity)
      (T j) (hT j) r u).neg using 1
    funext z
    simp
  have hf0e : (∫ z, f0 z^2 ∂μ) ≤
      (Real.sqrt ((J:ℝ)*(32*T0^(2-v.p))))^2*‖u‖^2 := by
    have hb := scoreProjPair_energy_le v hv law hm J J hJ hJ T0 hT0 r u
    dsimp [f0, μ]
    rw [Real.sq_sqrt hV0]
    simpa only [neg_sq] using hb
  have hCe (j : Fin L) : 0 ≤ C j := Real.sqrt_nonneg _
  have hfje : ∀ j : Fin L, (∫ z, fj j z^2 ∂μ) ≤ (C j)^2*‖u‖^2 := by
    intro j
    have htj : 0 ≤ T j := le_trans (by norm_num) (hT j)
    let V := 32*(T j)^(2-v.p)
    have hV : 0 ≤ V := mul_nonneg (by norm_num) (Real.rpow_nonneg htj _)
    have hnon : 0 ≤ ((2^(j.val+1)*J:ℕ):ℝ)*V :=
      mul_nonneg (by positivity) (mul_nonneg (by norm_num) (Real.rpow_nonneg htj _))
    have hb := scoreDiffPair_energy_le v hv law hm J (2^j.val*J) hJ
      (by positivity) (T j) (hT j) r u
    have hrank : ((2^j.val*J:ℕ):ℝ) ≤ ((2^(j.val+1)*J:ℕ):ℝ) := by
      have hp : 2^j.val ≤ 2^(j.val+1) := by
        rw [pow_succ]
        omega
      exact_mod_cast Nat.mul_le_mul_right J hp
    have hb' := hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hrank hV) (sq_nonneg ‖u‖))
    dsimp [fj, μ, C]
    dsimp [V] at hnon hb'
    rw [Real.sq_sqrt hnon]
    simpa only [neg_sq] using hb'
  have hsum := energy_finset_sum_le μ Finset.univ fj (fun j _ => hfj j) C (‖u‖^2)
    (fun j _ => hCe j) (sq_nonneg ‖u‖) (fun j _ => hfje j)
  have hall := energy_add_le μ f0 (fun z => ∑ j : Fin L, fj j z) hf0
    (memLp_finsetSum Finset.univ fun j _ => hfj j)
    (Real.sqrt ((J:ℝ)*(32*T0^(2-v.p)))) (∑ j : Fin L, C j) (‖u‖^2)
    (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun j _ => hCe j)) (sq_nonneg ‖u‖)
    hf0e hsum
  have heq : (fun z : Record × Record => multiresScalarPair J L T0 T r u z.1 z.2) =
      fun z => f0 z+∑ j : Fin L, fj j z := by
    funext z
    rw [multiresScalarPair_eq_scoreDiffPairs J L T0 T r u z.1 z.2]
    simp only [f0, fj]
    rw [Finset.sum_neg_distrib]
    ring
  simp_rw [congrFun heq]
  simpa only [μ, C] using hall

/-- Under [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hK condition](hyp:hK), [the hJK condition](hyp:hJK), [the hT condition](hyp:hT), [the single Scalar Pair conditional energy le statement holds](goal). -/
lemma singleScalarPair_conditional_energy_le (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law) (J K : ℕ)
    (hJ : 0 < J) (hK : 0 < K) (hJK : J ∣ K)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) :
    (∫ o, (∫ z, singleScalarPair J K T r u o z ∂law.P)^2 ∂law.P) ≤
      (32*T^(2-v.p))*‖u‖^2 := by
  have heq (o : Record) : (∫ z, singleScalarPair J K T r u o z ∂law.P) =
      -(∫ z, scoreProjPair J K T r u o z ∂law.P) := by
    rw [show (fun z => singleScalarPair J K T r u o z) =
        fun z => -scoreProjPair J K T r u o z by
      funext z; exact singleScalarPair_eq_neg_scoreProjPair J K T r u o z]
    rw [integral_neg]
  simp_rw [heq]
  simpa only [neg_sq] using
    scoreProjPair_conditional_energy_le v hv law hm J K hJ hK hJK T hT r u

/-- Under [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hK condition](hyp:hK), [the hT condition](hyp:hT), [the single Scalar Pair energy le statement holds](goal). -/
lemma singleScalarPair_energy_le (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law) (J K : ℕ)
    (hJ : 0 < J) (hK : 0 < K) (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) :
    (∫ z : Record × Record, singleScalarPair J K T r u z.1 z.2^2
      ∂law.P.prod law.P) ≤ (K:ℝ)*(32*T^(2-v.p))*‖u‖^2 := by
  have heq : (fun z : Record × Record => singleScalarPair J K T r u z.1 z.2) =
      fun z => -scoreProjPair J K T r u z.1 z.2 := by
    funext z
    exact singleScalarPair_eq_neg_scoreProjPair J K T r u z.1 z.2
  simp_rw [congrFun heq]
  simpa only [neg_sq] using scoreProjPair_energy_le v hv law hm J K hJ hK T hT r u

/-- The one-record summand has energy controlled by the main clipped second moment. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
lemma multiresScalarSingle_energy_le (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law) (J : ℕ) (hJ : 0 < J)
    (T : ℝ) (hT : 1 ≤ T) (r : Bool) (u : Vec J) :
    (∫ o, multiresScalarSingle J T r u o^2 ∂law.P) ≤
      2*(32*T^(2-v.p))*‖u‖^2 := by
  have h := conditional_pair_energy_of_envelope law hm.uniform J hJ u (scoreMark T r)
    (multiresScalarSingle J T r u) (scoreMark_measurable' T r)
    (multiresScalarSingle_measurable J T r u) T 0 2 (32*T^(2-v.p))
    (by linarith) (by norm_num) (by norm_num) (by positivity)
    (scoreMark_abs_le' T hT r) (scoreMark_conditional_sq_le v hv law hm T hT r)
    (fun o => by
      unfold multiresScalarSingle multiresSingleKernel scoreMark
      simp only [inner_smul_right, smul_eq_mul]
      cases r
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [abs_mul, abs_mul]
        calc
          _ ≤ 1 * |clipY T (Y o)| * |inner ℝ u (featureMap J (X o))| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (treatment_abs_le_one o)
                (abs_nonneg (clipY T (Y o))))
              (abs_nonneg (inner ℝ u (featureMap J (X o))))
          _ = _ := by ring
      · simp only [↓reduceIte, mul_one]
        rw [abs_mul]
        simpa [mul_comm, mul_left_comm, mul_assoc])
  convert h using 1 <;> ring

/-- The singleton channel of an augmented pair is controlled by the one-record energy and the uncentered conditional-pair energy. This statement assumes [the hhm condition](hyp:hhm), [the hgm condition](hyp:hgm), [the hh condition](hyp:hh), [the hg condition](hyp:hg), [the hBh condition](hyp:hBh), [the hBg condition](hyp:hBg), [the hN condition](hyp:hN), [the hhenergy condition](hyp:hhenergy), [the hgconditional condition](hyp:hgconditional). [This is the stated conclusion](goal). -/
lemma singletonAugmentedPair_variance_le (law : ObservedLaw)
    (h : Record → ℝ) (g : Record → Record → ℝ)
    (hhm : Measurable h) (hgm : Measurable (fun z : Record × Record => g z.1 z.2))
    (hh : MemLp h 2 law.P)
    (hg : MemLp (fun z : Record × Record => g z.1 z.2) 2 (law.P.prod law.P))
    (Bh Bg N : ℝ) (hBh : 0 ≤ Bh) (hBg : 0 ≤ Bg) (hN : 0 ≤ N)
    (hhenergy : (∫ x, h x^2 ∂law.P) ≤ Bh^2*N)
    (hgconditional : (∫ x, (∫ y, g x y ∂law.P)^2 ∂law.P) ≤ Bg^2*N) :
    4*variance (singletonProjection law.P (singletonAugmentedPair h g)) law.P ≤
      (Bh+2*Bg)^2*N := by
  let hc : Record → ℝ := fun x => (h x-(∫ z, h z ∂law.P))/2
  let sg : Record → ℝ := singletonProjection law.P g
  have hhci : MemLp hc 2 law.P := by
    dsimp [hc]
    convert (hh.sub (memLp_const (μ := law.P) (∫ z, h z ∂law.P))).const_mul (1/2) using 1
    funext x
    simp only [Pi.sub_apply]
    ring
  have hsgi : MemLp sg 2 law.P := singletonProjection_memLp law.P g hgm hg
  have hhce : (∫ x, hc x^2 ∂law.P) ≤ (Bh/2)^2*N := by
    calc
      _ ≤ (1/4)*(∫ x, h x^2 ∂law.P) := centered_half_energy_le law.P h hh
      _ ≤ (1/4)*(Bh^2*N) := mul_le_mul_of_nonneg_left hhenergy (by norm_num)
      _ = _ := by ring
  have hsge : (∫ x, sg x^2 ∂law.P) ≤ Bg^2*N :=
    (singletonProjection_energy_le_conditional law g hgm hg).trans hgconditional
  have hadd := energy_add_le law.P hc sg hhci hsgi (Bh/2) Bg N
    (div_nonneg hBh (by norm_num)) hBg hN hhce hsge
  have hae := singletonProjection_singletonAugmentedPair_ae law h g
    (hh.integrable (by norm_num)) (hg.integrable (by norm_num))
  have heq : variance (singletonProjection law.P (singletonAugmentedPair h g)) law.P =
      ∫ x, (hc x+sg x)^2 ∂law.P := by
    rw [singletonProjection_variance law.P (singletonAugmentedPair h g)
      (singletonAugmentedPair_measurable h g hhm hgm)
      (singletonAugmentedPair_memLp law h g hh hg)]
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  rw [heq]
  nlinarith

/-- The canonical channel of an augmented pair is bounded by the raw energy of its pair part. This statement assumes [the hhm condition](hyp:hhm), [the hgm condition](hyp:hgm), [the hsym condition](hyp:hsym), [the hh condition](hyp:hh), [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
lemma singletonAugmentedPair_canonical_energy_le (law : ObservedLaw)
    (h : Record → ℝ) (g : Record → Record → ℝ)
    (hhm : Measurable h) (hgm : Measurable (fun z : Record × Record => g z.1 z.2))
    (hsym : ∀ x y, g x y = g y x)
    (hh : MemLp h 2 law.P)
    (hg : MemLp (fun z : Record × Record => g z.1 z.2) 2 (law.P.prod law.P)) :
    (∫ z : Record × Record,
      canonicalProjection law.P (singletonAugmentedPair h g) z.1 z.2^2
        ∂law.P.prod law.P) ≤
      ∫ z : Record × Record, g z.1 z.2^2 ∂law.P.prod law.P := by
  rw [canonicalProjection_singletonAugmentedPair_energy law h g hhm hgm
    (hh.integrable (by norm_num)) (hg.integrable (by norm_num))]
  exact canonicalProjection_energy_le law.P g hgm hsym hg

/-- The selected public kernel satisfies the declared singleton variance ledger. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
lemma ledgerScalarKernel_singleton_variance_le (v : Params) (hv : v.Valid)
    (n : ℕ) (hn : 4 ≤ n) (law : ObservedLaw) (hm : InModel v law)
    (r : Bool) (u : Vec (ledgerM n v)) :
    4*variance (singletonProjection law.P (ledgerScalarKernel n v r u)) law.P ≤
      ledgerL1 n v^2*‖u‖^2 := by
  have hn' : ¬n < 4 := by omega
  have hM : 0 < ledgerM n v := by
    simp only [ledgerM, if_neg hn', leastPow2Ge]
    positivity
  have hK : 0 < ledgerK n v := by
    simp only [ledgerK, if_neg hn', leastPow2Ge]
    positivity
  have hT0 := ledgerT0_ge_one n v
  have hV0 : 0 ≤ ledgerV0 n v := by unfold ledgerV0; positivity
  let Bh := 2*Real.sqrt (ledgerV0 n v)
  have hBh : 0 ≤ Bh := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hhenergy : (∫ o, multiresScalarSingle (ledgerM n v) (ledgerT0 n v) r u o^2
      ∂law.P) ≤ Bh^2*‖u‖^2 := by
    have hb := multiresScalarSingle_energy_le v hv law hm (ledgerM n v) hM
      (ledgerT0 n v) hT0 r u
    have hs := Real.sq_sqrt hV0
    have hb' : (∫ o, multiresScalarSingle (ledgerM n v) (ledgerT0 n v) r u o^2
        ∂law.P) ≤ 2*ledgerV0 n v*‖u‖^2 := by simpa only [ledgerV0] using hb
    have hscalar : 2*ledgerV0 n v ≤ Bh^2 := by dsimp [Bh]; nlinarith
    exact hb'.trans (mul_le_mul_of_nonneg_right hscalar (sq_nonneg ‖u‖))
  by_cases hbranch : singleBranch v
  · let Bg := Real.sqrt (ledgerV0 n v)
    have hBg : 0 ≤ Bg := Real.sqrt_nonneg _
    have hgcond : (∫ o, (∫ z, singleScalarPair (ledgerM n v) (ledgerK n v)
        (ledgerT0 n v) r u o z ∂law.P)^2 ∂law.P) ≤ Bg^2*‖u‖^2 := by
      have hb := singleScalarPair_conditional_energy_le v hv law hm
        (ledgerM n v) (ledgerK n v) hM hK (ledger_coarse_dvd_fine n v hn)
        (ledgerT0 n v) hT0 r u
      dsimp [Bg]
      rw [Real.sq_sqrt hV0]
      simpa only [ledgerV0] using hb
    have h := singletonAugmentedPair_variance_le law
      (multiresScalarSingle (ledgerM n v) (ledgerT0 n v) r u)
      (singleScalarPair (ledgerM n v) (ledgerK n v) (ledgerT0 n v) r u)
      (multiresScalarSingle_measurable _ _ _ _) (singleScalarPair_measurable _ _ _ _ _)
      (multiresScalarSingle_memLp law _ _ _ _) (singleScalarPair_memLp law _ _ _ _ _)
      Bh Bg (‖u‖^2) hBh hBg (sq_nonneg ‖u‖) hhenergy hgcond
    simp only [ledgerScalarKernel, if_pos hbranch, singleScalarKernel] at h ⊢
    simp only [ledgerL1, if_neg hn', if_pos hbranch, add_zero]
    dsimp [Bh, Bg] at h
    have hs : (0:ℝ) ≤ Real.sqrt (ledgerV0 n v) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg ‖u‖]
  · let S := ∑ j : Fin (ledgerL n v),
        (dLev n v (j.val+1)+aLev n v (j.val+1)*Real.sqrt (ledgerV n v (j.val+1)))
    let Bg := Real.sqrt (ledgerV0 n v)+∑ j : Fin (ledgerL n v),
      2*(dLev n v (j.val+1)+aLev n v (j.val+1)*Real.sqrt (ledgerV n v (j.val+1)))
    have hterm (j : Fin (ledgerL n v)) : 0 ≤
        dLev n v (j.val+1)+aLev n v (j.val+1)*Real.sqrt (ledgerV n v (j.val+1)) := by
      unfold dLev aLev ledgerV
      have ht : 0 ≤ ledgerT n v (j.val+1) := le_trans (by norm_num) (ledgerT_ge_one n v _)
      exact add_nonneg
        (add_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
          (mul_nonneg (by norm_num) (Real.rpow_nonneg ht _)))
        (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
          (Real.sqrt_nonneg _))
    have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => hterm j)
    have hBg : 0 ≤ Bg := add_nonneg (Real.sqrt_nonneg _)
      (Finset.sum_nonneg (fun j _ => mul_nonneg (by norm_num) (hterm j)))
    have hgcond : (∫ o, (∫ z, multiresScalarPair (ledgerM n v) (ledgerL n v)
        (ledgerT0 n v) (fun j => ledgerT n v (j.val+1)) r u o z ∂law.P)^2 ∂law.P) ≤
        Bg^2*‖u‖^2 := by
      have hb := multiresScalarPair_conditional_energy_le v hv law hm
        (ledgerM n v) (ledgerL n v) hM (ledgerT0 n v) hT0
        (fun j => ledgerT n v (j.val+1)) (fun j => ledgerT_ge_one n v _) r u
      dsimp [Bg, S]
      simpa only [ledgerV0, ledgerV, dLev, aLev, ledgerR, Nat.add_sub_cancel] using hb
    have h := singletonAugmentedPair_variance_le law
      (multiresScalarSingle (ledgerM n v) (ledgerT0 n v) r u)
      (multiresScalarPair (ledgerM n v) (ledgerL n v) (ledgerT0 n v)
        (fun j => ledgerT n v (j.val+1)) r u)
      (multiresScalarSingle_measurable _ _ _ _) (multiresScalarPair_measurable _ _ _ _ _ _)
      (multiresScalarSingle_memLp law _ _ _ _) (multiresScalarPair_memLp law _ _ _ _ _ _)
      Bh Bg (‖u‖^2) hBh hBg (sq_nonneg ‖u‖) hhenergy hgcond
    simp only [ledgerScalarKernel, if_neg hbranch, multiresScalarKernel] at h ⊢
    simp only [ledgerL1, if_neg hn', if_neg hbranch]
    dsimp [Bh, Bg, S] at h ⊢
    have hsqrt : 0 ≤ Real.sqrt (ledgerV0 n v) := Real.sqrt_nonneg _
    have hsum2 : (∑ j : Fin (ledgerL n v),
        2*(dLev n v (j.val+1)+aLev n v (j.val+1)*Real.sqrt (ledgerV n v (j.val+1)))) =
        2*∑ j : Fin (ledgerL n v),
          (dLev n v (j.val+1)+aLev n v (j.val+1)*Real.sqrt (ledgerV n v (j.val+1))) := by
      rw [Finset.mul_sum]
    rw [hsum2] at h
    have hc : (2*Real.sqrt (ledgerV0 n v)+
        2*(Real.sqrt (ledgerV0 n v)+2*S))^2 ≤
        (16*Real.sqrt (ledgerV0 n v)+8*S)^2 := by nlinarith
    exact h.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖u‖))

/-- The selected public kernel satisfies the declared canonical-pair energy ledger. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
lemma ledgerScalarKernel_canonical_energy_le (v : Params) (hv : v.Valid)
    (n : ℕ) (hn : 4 ≤ n) (law : ObservedLaw) (hm : InModel v law)
    (r : Bool) (u : Vec (ledgerM n v)) :
    (∫ z : Record × Record,
      canonicalProjection law.P (ledgerScalarKernel n v r u) z.1 z.2^2
        ∂law.P.prod law.P) ≤ ledgerL2 n v^2*‖u‖^2 := by
  have hn' : ¬n < 4 := by omega
  have hM : 0 < ledgerM n v := by
    simp only [ledgerM, if_neg hn', leastPow2Ge]
    positivity
  have hK : 0 < ledgerK n v := by
    simp only [ledgerK, if_neg hn', leastPow2Ge]
    positivity
  have hT0 := ledgerT0_ge_one n v
  by_cases hbranch : singleBranch v
  · have hcan := singletonAugmentedPair_canonical_energy_le law
      (multiresScalarSingle (ledgerM n v) (ledgerT0 n v) r u)
      (singleScalarPair (ledgerM n v) (ledgerK n v) (ledgerT0 n v) r u)
      (multiresScalarSingle_measurable _ _ _ _) (singleScalarPair_measurable _ _ _ _ _)
      (singleScalarPair_symmetric _ _ _ _ _)
      (multiresScalarSingle_memLp law _ _ _ _) (singleScalarPair_memLp law _ _ _ _ _)
    have hraw := singleScalarPair_energy_le v hv law hm (ledgerM n v) (ledgerK n v)
      hM hK (ledgerT0 n v) hT0 r u
    have hbase := hcan.trans hraw
    have hV0 : 0 ≤ ledgerV0 n v := by unfold ledgerV0; positivity
    have hKV : 0 ≤ (ledgerK n v:ℝ)*ledgerV0 n v :=
      mul_nonneg (by positivity) hV0
    have hs := Real.sq_sqrt hKV
    simp only [ledgerScalarKernel, if_pos hbranch, singleScalarKernel] at hbase ⊢
    simp only [ledgerL2, if_neg hn', if_pos hbranch]
    have hbase' : (∫ z : Record × Record,
        canonicalProjection law.P
          (singletonAugmentedPair (multiresScalarSingle (ledgerM n v) (ledgerT0 n v) r u)
            (singleScalarPair (ledgerM n v) (ledgerK n v) (ledgerT0 n v) r u))
          z.1 z.2^2 ∂law.P.prod law.P) ≤
        ((ledgerK n v:ℝ)*ledgerV0 n v)*‖u‖^2 := by
      simpa only [ledgerV0] using hbase
    have hc : (ledgerK n v:ℝ)*ledgerV0 n v ≤
        (4*Real.sqrt ((ledgerK n v:ℝ)*ledgerV0 n v))^2 := by nlinarith
    exact hbase'.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖u‖))
  · let B := Real.sqrt ((ledgerM n v:ℝ)*ledgerV0 n v)+
        ∑ j : Fin (ledgerL n v),
          Real.sqrt ((ledgerR n v (j.val+1):ℝ)*ledgerV n v (j.val+1))
    have hB : 0 ≤ B := add_nonneg (Real.sqrt_nonneg _)
      (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _))
    have hcan := singletonAugmentedPair_canonical_energy_le law
      (multiresScalarSingle (ledgerM n v) (ledgerT0 n v) r u)
      (multiresScalarPair (ledgerM n v) (ledgerL n v) (ledgerT0 n v)
        (fun j => ledgerT n v (j.val+1)) r u)
      (multiresScalarSingle_measurable _ _ _ _) (multiresScalarPair_measurable _ _ _ _ _ _)
      (multiresScalarPair_symmetric _ _ _ _ _ _)
      (multiresScalarSingle_memLp law _ _ _ _) (multiresScalarPair_memLp law _ _ _ _ _ _)
    have hraw := multiresScalarPair_energy_le v hv law hm (ledgerM n v) (ledgerL n v)
      hM (ledgerT0 n v) hT0 (fun j => ledgerT n v (j.val+1))
      (fun j => ledgerT_ge_one n v _) r u
    have hbase := hcan.trans hraw
    have hbase' : (∫ z : Record × Record,
        canonicalProjection law.P
          (singletonAugmentedPair (multiresScalarSingle (ledgerM n v) (ledgerT0 n v) r u)
            (multiresScalarPair (ledgerM n v) (ledgerL n v) (ledgerT0 n v)
              (fun j => ledgerT n v (j.val+1)) r u)) z.1 z.2^2
          ∂law.P.prod law.P) ≤ B^2*‖u‖^2 := by
      dsimp [B]
      simpa only [ledgerV0, ledgerV, ledgerR] using hbase
    simp only [ledgerScalarKernel, if_neg hbranch, multiresScalarKernel] at hbase' ⊢
    simp only [ledgerL2, if_neg hn', if_neg hbranch]
    dsimp [B] at hB hbase' ⊢
    have hc : (Real.sqrt ((ledgerM n v:ℝ)*ledgerV0 n v)+
        ∑ j : Fin (ledgerL n v),
          Real.sqrt ((ledgerR n v (j.val+1):ℝ)*ledgerV n v (j.val+1)))^2 ≤
        (4*(Real.sqrt ((ledgerM n v:ℝ)*ledgerV0 n v)+
          ∑ j : Fin (ledgerL n v),
            Real.sqrt ((ledgerR n v (j.val+1):ℝ)*ledgerV n v (j.val+1))))^2 := by
      nlinarith
    exact hbase'.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖u‖))


end CausalSmith.Stat.FinitepHomogeneityDensegamma

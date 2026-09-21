module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.PhiwHistory

set_option linter.style.longLine false

/-! # Observable PHIW window moments -/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- For [the k input](hyp:k), [the t input](hyp:t), [this defines the phiw Window object](goal). -/
def phiwWindow {T : Nat} (k : Nat) (t : Fin T) : Finset (Fin T) :=
  Finset.univ.filter (fun j : Fin T ↦ j.val ≤ t.val ∧ t.val - j.val ≤ k)

/-- The carrier-level block is the ordinary chronological product on a full trajectory. [the hlo condition](hyp:hlo). [the stated conclusion](goal). -/
lemma actionHistoryRatioBlock_histActionPair {T nX nH : Nat}
    (M : RawPomdpExperiment T nX nH) (lo : Nat) (t : Fin T)
    (hlo : lo ≤ t.val) (tau : FullTrajectory T nX nH) :
    actionHistoryRatioBlock M lo t (histActionPair t tau) =
      ∏ j ∈ Finset.univ.filter (fun j : Fin T ↦ lo ≤ j.val ∧ j.val ≤ t.val),
        ratio M.b M.e (curState j tau).1 (actionAt j tau) := by
  classical
  unfold actionHistoryRatioBlock stateHistoryRatioBlock
  change (∏ j : Fin t.val, if lo ≤ j.val then
      ratio M.b M.e (curState (prefixIndex t j) tau).1
        (actionAt (prefixIndex t j) tau) else 1) *
      ratio M.b M.e (curState t tau).1 (actionAt t tau) = _
  calc
    _ = (∏ j : Fin (t.val + 1), if lo ≤ j.val then
        ratio M.b M.e (curState (⟨j.val, by omega⟩ : Fin T) tau).1
          (actionAt (⟨j.val, by omega⟩ : Fin T) tau) else 1) := by
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, hlo, if_true]
      simp [prefixIndex]
    _ = _ := by
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one, one_pow, mul_one]
      apply Finset.prod_bij (fun j _ ↦ (⟨j.val, by omega⟩ : Fin T))
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact ⟨hj, by omega⟩
      · intro i _ j _ hij
        apply Fin.ext
        exact congrArg (fun x : Fin T ↦ x.val) hij
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        refine ⟨⟨j.val, by omega⟩, ?_, Fin.ext rfl⟩
        simpa using hj.1
      · intro j _
        rfl

/-- For a mature window, the subtraction-based PHIW index predicate is exactly a contiguous
interval ending at the current epoch. [the htk condition](hyp:htk). [the stated conclusion](goal). -/
lemma phiwWindow_eq_interval {T k : Nat} (t : Fin T) (htk : k ≤ t.val) :
    phiwWindow k t =
      Finset.univ.filter (fun j : Fin T ↦ t.val - k ≤ j.val ∧ j.val ≤ t.val) := by
  ext j
  simp only [phiwWindow, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hjt, hdist⟩
    exact ⟨by omega, hjt⟩
  · rintro ⟨hlo, hjt⟩
    exact ⟨hjt, by omega⟩

/-- The normalized contiguous block underlying a mature PHIW score has mean one. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the htk condition](hyp:htk). [the stated conclusion](goal). -/
lemma integral_phiwWindowProduct_eq_one {T nX nH k : Nat}
    {M : RawPomdpExperiment T nX nH} {L : ℝ}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (hK : PomdpKernelLaw M) (t : Fin T) (htk : k ≤ t.val) :
    ∫ tau, (∏ j ∈ phiwWindow k t,
        ratio M.b M.e (curState j tau).1 (actionAt j tau)) ∂M.law = 1 := by
  have hm := integral_actionHistoryRatioBlock_eq_one
    hign hoverlap hL hK (t.val - k) t
  have hmap :
      (∫ z, actionHistoryRatioBlock M (t.val - k) t z
          ∂(M.law.map (histActionPair t))) =
        ∫ tau, actionHistoryRatioBlock M (t.val - k) t (histActionPair t tau) ∂M.law :=
    MeasureTheory.integral_map (measurable_histActionPair t).aemeasurable
      (measurable_actionHistoryRatioBlock M (t.val - k) t).aestronglyMeasurable
  rw [hmap] at hm
  simpa [actionHistoryRatioBlock_histActionPair M (t.val - k) t (Nat.sub_le _ _),
    phiwWindow_eq_interval t htk] using hm

/-- Normalization of an arbitrary contiguous interval of chronological ratios. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the hlo condition](hyp:hlo). [the stated conclusion](goal). -/
lemma integral_intervalRatioProduct_eq_one {T nX nH : Nat}
    {M : RawPomdpExperiment T nX nH} {L : ℝ}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (hK : PomdpKernelLaw M) (lo : Nat) (t : Fin T)
    (hlo : lo ≤ t.val) :
    ∫ tau, (∏ j ∈ Finset.univ.filter
        (fun j : Fin T ↦ lo ≤ j.val ∧ j.val ≤ t.val),
        ratio M.b M.e (curState j tau).1 (actionAt j tau)) ∂M.law = 1 := by
  have hm := integral_actionHistoryRatioBlock_eq_one hign hoverlap hL hK lo t
  have hmap :
      (∫ z, actionHistoryRatioBlock M lo t z ∂(M.law.map (histActionPair t))) =
        ∫ tau, actionHistoryRatioBlock M lo t (histActionPair t tau) ∂M.law :=
    MeasureTheory.integral_map (measurable_histActionPair t).aemeasurable
      (measurable_actionHistoryRatioBlock M lo t).aestronglyMeasurable
  rw [hmap] at hm
  simpa [actionHistoryRatioBlock_histActionPair M lo t hlo] using hm

/-- Multiplicity bookkeeping for products over two finite sets. [the stated conclusion](goal). -/
lemma prod_mul_prod_eq_union_mul_inter {ι : Type*} [DecidableEq ι]
    (f : ι → ℝ) (A B : Finset ι) :
    (∏ i ∈ A, f i) * (∏ i ∈ B, f i) =
      (∏ i ∈ A ∪ B, f i) * (∏ i ∈ A ∩ B, f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
      by_cases hab : a ∈ B
      · have hainter : a ∉ A ∩ B := by simp [ha]
        have hunion : insert a A ∪ B = A ∪ B := by
          ext x
          simp only [Finset.mem_union, Finset.mem_insert]
          constructor
          · rintro ((rfl | hxA) | hxB)
            · exact Or.inr hab
            · exact Or.inl hxA
            · exact Or.inr hxB
          · rintro (hxA | hxB)
            · exact Or.inl (Or.inr hxA)
            · exact Or.inr hxB
        rw [Finset.prod_insert ha, hunion, Finset.insert_inter_of_mem hab,
          Finset.prod_insert hainter]
        calc
          (f a * ∏ i ∈ A, f i) * ∏ i ∈ B, f i =
              f a * ((∏ i ∈ A, f i) * ∏ i ∈ B, f i) := by ring
          _ = f a * ((∏ i ∈ A ∪ B, f i) * ∏ i ∈ A ∩ B, f i) := by rw [ih]
          _ = (∏ i ∈ A ∪ B, f i) * (f a * ∏ i ∈ A ∩ B, f i) := by ring
      · have haunion : a ∉ A ∪ B := by simp [ha, hab]
        have hinter : insert a A ∩ B = A ∩ B := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨hx | hxa, hxb⟩
            · subst x
              exact False.elim (hab hxb)
            · exact ⟨hxa, hxb⟩
          · exact fun hx ↦ ⟨Or.inr hx.1, hx.2⟩
        rw [Finset.prod_insert ha, Finset.insert_union,
          Finset.prod_insert haunion, hinter]
        calc
          (f a * ∏ i ∈ A, f i) * ∏ i ∈ B, f i =
              f a * ((∏ i ∈ A, f i) * ∏ i ∈ B, f i) := by ring
          _ = f a * ((∏ i ∈ A ∪ B, f i) * ∏ i ∈ A ∩ B, f i) := by rw [ih]
          _ = (f a * ∏ i ∈ A ∪ B, f i) * ∏ i ∈ A ∩ B, f i := by ring

/-- Two mature windows separated by at most `k` epochs have a contiguous union. [the htk condition](hyp:htk); and [the hu condition](hyp:hu); and [the hhk condition](hyp:hhk). [the stated conclusion](goal). -/
lemma phiwWindow_union_eq_interval {T k h : Nat} (t u : Fin T)
    (htk : k ≤ t.val) (hu : u.val = t.val + h) (hhk : h ≤ k) :
    phiwWindow k t ∪ phiwWindow k u =
      Finset.univ.filter
        (fun j : Fin T ↦ t.val - k ≤ j.val ∧ j.val ≤ u.val) := by
  ext j
  simp only [phiwWindow, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨hjt, hd⟩ | ⟨hju, hd⟩)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, hju⟩
  · rintro ⟨hlo, hju⟩
    by_cases hjt : j.val ≤ t.val
    · left
      exact ⟨hjt, by omega⟩
    · right
      exact ⟨hju, by omega⟩

/-- The overlap of two windows `h` epochs apart contains at most `k+1-h` epochs. [the htk condition](hyp:htk); and [the hu condition](hyp:hu); and [the hhk condition](hyp:hhk). [the stated conclusion](goal). -/
lemma card_phiwWindow_inter_le {T k h : Nat} (t u : Fin T)
    (htk : k ≤ t.val) (hu : u.val = t.val + h) (hhk : h ≤ k) :
    (phiwWindow k t ∩ phiwWindow k u).card ≤ k + 1 - h := by
  classical
  let f : Fin T → Nat := fun j ↦ t.val - j.val
  calc
    _ ≤ (Finset.range (k + 1 - h)).card := by
      apply Finset.card_le_card_of_injOn f
      · intro j hj
        change j ∈ phiwWindow k t ∩ phiwWindow k u at hj
        rw [Finset.mem_inter] at hj
        simp only [phiwWindow, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rcases hj with ⟨⟨hjt, hdt⟩, hju, hdu⟩
        apply Finset.mem_range.mpr
        change t.val - j.val < k + 1 - h
        have heq : u.val - j.val = (t.val - j.val) + h := by omega
        omega
      · intro i hi j hj hij
        change i ∈ phiwWindow k t ∩ phiwWindow k u at hi
        change j ∈ phiwWindow k t ∩ phiwWindow k u at hj
        rw [Finset.mem_inter] at hi hj
        simp only [phiwWindow, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        apply Fin.ext
        change t.val - i.val = t.val - j.val at hij
        omega
    _ = _ := Finset.card_range _

/-- A PHIW score is a measurable function of the observed path. [the stated conclusion](goal). -/
lemma phiwScore_measurable {T nX k : Nat} (b e : Policy nX) (t : Fin T) :
    Measurable (phiwScore k b e · t : ObsView T nX → ℝ) := by
  unfold phiwScore
  fun_prop

/-- [the phiw Window Product measurable assertion holds](goal). -/
lemma phiwWindowProduct_measurable {T nX k : Nat} (b e : Policy nX) (t : Fin T) :
    Measurable (fun w : ObsView T nX ↦
      ∏ j ∈ phiwWindow k t, ratio b e (w j).1 (w j).2.1) := by
  classical
  apply Finset.measurable_prod
  intro j _
  exact (measurable_of_finite (fun xa : Fin nX × Bool ↦ ratio b e xa.1 xa.2)).comp
    (((measurable_pi_apply j).fst).prodMk ((measurable_pi_apply j).snd.fst))

/-- Pulling a PHIW score back along the observation projection only replaces observed
coordinates by their defining full-trajectory coordinates. [the stated conclusion](goal). -/
lemma phiwScore_obsProj {T nX nH k : Nat} (b e : Policy nX)
    (tau : FullTrajectory T nX nH) (t : Fin T) :
    phiwScore k b e (obsProj tau) t =
      rewardAt t tau * ∏ j ∈ phiwWindow k t,
        ratio b e (curState j tau).1 (actionAt j tau) := by
  rfl

/-- Every ratio product in a PHIW window is nonnegative. [the hb condition](hyp:hb); and [the he condition](hyp:he); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL). [the stated conclusion](goal). -/
lemma phiwWindowProduct_nonneg {T nX k : Nat} {b e : Policy nX} {L : ℝ}
    (hb : PolicyVector b) (he : PolicyVector e)
    (hoverlap : ∀ x a, e x a ≤ L * b x a) (hL : 0 ≤ L)
    (w : ObsView T nX) (t : Fin T) :
    0 ≤ ∏ j ∈ phiwWindow k t, ratio b e (w j).1 (w j).2.1 := by
  exact Finset.prod_nonneg fun j _ ↦ (ratio_mem hb he hoverlap hL _ _).1

/-- The ratio product is bounded by one factor `L` per member of its window. [the hb condition](hyp:hb); and [the he condition](hyp:he); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL). [the stated conclusion](goal). -/
lemma phiwWindowProduct_le_pow_card {T nX k : Nat} {b e : Policy nX} {L : ℝ}
    (hb : PolicyVector b) (he : PolicyVector e)
    (hoverlap : ∀ x a, e x a ≤ L * b x a) (hL : 0 ≤ L)
    (w : ObsView T nX) (t : Fin T) :
    ∏ j ∈ phiwWindow k t, ratio b e (w j).1 (w j).2.1 ≤
      L ^ (phiwWindow k t).card := by
  calc
    _ ≤ ∏ _j ∈ phiwWindow k t, L := Finset.prod_le_prod
      (fun j _ ↦ (ratio_mem hb he hoverlap hL _ _).1)
      (fun j _ ↦ (ratio_mem hb he hoverlap hL _ _).2)
    _ = _ := by simp

/-- A PHIW window contains at most `k+1` epochs. [the stated conclusion](goal). -/
lemma card_phiwWindow_le {T k : Nat} (t : Fin T) :
    (phiwWindow k t).card ≤ k + 1 := by
  classical
  let f : Fin T → Nat := fun j ↦ t.val - j.val
  have hinj : Set.InjOn f ↑(phiwWindow k t) := by
    intro i hi j hj hij
    change i ∈ phiwWindow k t at hi
    change j ∈ phiwWindow k t at hj
    have hit : i.val ≤ t.val := (Finset.mem_filter.mp hi).2.1
    have hjt : j.val ≤ t.val := (Finset.mem_filter.mp hj).2.1
    dsimp [f] at hij
    apply Fin.ext
    omega
  calc
    (phiwWindow k t).card ≤ (Finset.range (k + 1)).card := by
      apply Finset.card_le_card_of_injOn f
      · intro j hj
        change j ∈ phiwWindow k t at hj
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hj).2.2)
      · exact hinj
    _ = k + 1 := Finset.card_range _

/-- Under policy overlap and bounded rewards, each score is essentially bounded by the crude
pathwise envelope `L^(k+1)`.  Chronological cancellation improves its second moment to the same
power rather than its square. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h Y condition](hyp:hY). [the stated conclusion](goal). -/
lemma ae_abs_phiwScore_le {T nX nH k : Nat} {L : ℝ}
    {M : RawPomdpExperiment T nX nH} (hign : SequentialIgnorability M)
    (hoverlap : PolicyOverlap L M) (hL : 1 ≤ L) (hY : BoundedReward M)
    (t : Fin T) :
    ∀ᵐ w ∂obsLaw M, |phiwScore k M.b M.e w t| ≤ L ^ (k + 1) := by
  rw [obsLaw]
  have hs : MeasurableSet
      {w : ObsView T nX | |phiwScore k M.b M.e w t| ≤ L ^ (k + 1)} :=
    measurableSet_le
      (continuous_abs.measurable.comp (phiwScore_measurable M.b M.e t)) measurable_const
  apply (MeasureTheory.ae_map_iff
    (measurable_obsProj (T := T) (nX := nX) (nH := nH)).aemeasurable hs).2
  filter_upwards [boundedReward_law_ae hY t] with tau htau
  rw [phiwScore_obsProj, abs_mul]
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hprod0 : 0 ≤ ∏ j ∈ phiwWindow k t,
      ratio M.b M.e (curState j tau).1 (actionAt j tau) := by
    simpa [obsProj] using
      phiwWindowProduct_nonneg hign.1 hoverlap.1 hoverlap.2 hL0 (obsProj tau) t
  rw [abs_of_nonneg hprod0]
  have hprod : (∏ j ∈ phiwWindow k t,
      ratio M.b M.e (curState j tau).1 (actionAt j tau)) ≤
      L ^ (phiwWindow k t).card := by
    simpa [obsProj] using
      phiwWindowProduct_le_pow_card hign.1 hoverlap.1 hoverlap.2 hL0 (obsProj tau) t
  have hpow := pow_le_pow_right₀ hL (card_phiwWindow_le (k := k) t)
  calc
    _ ≤ |rewardAt t tau| * L ^ (k + 1) :=
      mul_le_mul_of_nonneg_left (hprod.trans hpow) (abs_nonneg _)
    _ ≤ 1 * L ^ (k + 1) :=
      mul_le_mul_of_nonneg_right htau (pow_nonneg hL0 _)
    _ = _ := one_mul _

/-- Every PHIW score has all finite moments under the model assumptions. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h Y condition](hyp:hY). [the stated conclusion](goal). -/
lemma phiwScore_memLp {T nX nH k : Nat} {L : ℝ}
    {M : RawPomdpExperiment T nX nH} (hign : SequentialIgnorability M)
    (hoverlap : PolicyOverlap L M) (hL : 1 ≤ L) (hY : BoundedReward M)
    (p : ENNReal) (t : Fin T) :
    MemLp (phiwScore k M.b M.e · t) p (obsLaw M) := by
  letI : IsProbabilityMeasure (obsLaw M) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_obsProj (T := T) (nX := nX) (nH := nH)).aemeasurable
  apply MemLp.of_bound (phiwScore_measurable M.b M.e t).aestronglyMeasurable
    (L ^ (k + 1))
  filter_upwards [ae_abs_phiwScore_le hign hoverlap hL hY t] with w hw
  simpa [Real.norm_eq_abs] using hw

/-- Equation (18), first part: the absolute first moment of every mature PHIW summand is at
most one. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the h Y condition](hyp:hY); and [the htk condition](hyp:htk). [the stated conclusion](goal). -/
lemma integral_abs_phiwScore_le_one {T nX nH k : Nat} {L : ℝ}
    {M : RawPomdpExperiment T nX nH} (hign : SequentialIgnorability M)
    (hoverlap : PolicyOverlap L M) (hL : 1 ≤ L) (hK : PomdpKernelLaw M)
    (hY : BoundedReward M) (t : Fin T) (htk : k ≤ t.val) :
    ∫ w, |phiwScore k M.b M.e w t| ∂obsLaw M ≤ 1 := by
  letI : IsProbabilityMeasure (obsLaw M) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_obsProj (T := T) (nX := nX) (nH := nH)).aemeasurable
  let P : ObsView T nX → ℝ := fun w ↦
    ∏ j ∈ phiwWindow k t, ratio M.b M.e (w j).1 (w j).2.1
  have hPint : ∫ w, P w ∂obsLaw M = 1 := by
    unfold obsLaw
    rw [MeasureTheory.integral_map (measurable_obsProj (T := T) (nX := nX)
      (nH := nH)).aemeasurable (phiwWindowProduct_measurable M.b M.e t).aestronglyMeasurable]
    simpa [P, obsProj] using
      integral_phiwWindowProduct_eq_one hign hoverlap hL hK t htk
  have hscore : Integrable (fun w ↦ |phiwScore k M.b M.e w t|) (obsLaw M) := by
    exact (phiwScore_memLp hign hoverlap hL hY 2 t).integrable one_le_two |>.abs
  have hP : Integrable P (obsLaw M) := by
    apply Integrable.of_bound (phiwWindowProduct_measurable M.b M.e t).aestronglyMeasurable
      (L ^ (k + 1))
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg
      (phiwWindowProduct_nonneg hign.1 hoverlap.1 hoverlap.2
        (zero_le_one.trans hL) w t)]
    exact (phiwWindowProduct_le_pow_card hign.1 hoverlap.1 hoverlap.2
      (zero_le_one.trans hL) w t).trans
      (pow_le_pow_right₀ hL (card_phiwWindow_le (k := k) t))
  have hyobs : ∀ᵐ w ∂obsLaw M, |(w t).2.2| ≤ 1 := by
    unfold obsLaw
    let S : Set (ObsView T nX) := {w | |(w t).2.2| ≤ 1}
    have hS : MeasurableSet S := measurableSet_le
      (continuous_abs.measurable.comp ((measurable_pi_apply t).snd.snd)) measurable_const
    change ∀ᵐ w ∂M.law.map obsProj, w ∈ S
    apply (MeasureTheory.ae_map_iff
      (measurable_obsProj (T := T) (nX := nX) (nH := nH)).aemeasurable hS).2
    simpa [S, obsProj, rewardAt] using boundedReward_law_ae hY t
  calc
    _ ≤ ∫ w, P w ∂obsLaw M := by
      apply integral_mono_ae hscore hP
      filter_upwards [hyobs] with w hw
      rw [phiwScore, abs_mul]
      have hP0 : 0 ≤ P w := by
        exact phiwWindowProduct_nonneg (k := k) hign.1 hoverlap.1 hoverlap.2
          (zero_le_one.trans hL) _ _
      change |(w t).2.2| * |P w| ≤ P w
      rw [abs_of_nonneg hP0]
      nlinarith
    _ = 1 := hPint

/-- Equation (18), second part: one factor of the pointwise overlap envelope cancels against
the normalized likelihood-ratio block. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the h Y condition](hyp:hY); and [the htk condition](hyp:htk). [the stated conclusion](goal). -/
lemma integral_sq_phiwScore_le {T nX nH k : Nat} {L : ℝ}
    {M : RawPomdpExperiment T nX nH} (hign : SequentialIgnorability M)
    (hoverlap : PolicyOverlap L M) (hL : 1 ≤ L) (hK : PomdpKernelLaw M)
    (hY : BoundedReward M) (t : Fin T) (htk : k ≤ t.val) :
    ∫ w, phiwScore k M.b M.e w t ^ 2 ∂obsLaw M ≤ L ^ (k + 1) := by
  letI : IsProbabilityMeasure (obsLaw M) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_obsProj (T := T) (nX := nX) (nH := nH)).aemeasurable
  let P : ObsView T nX → ℝ := fun w ↦
    ∏ j ∈ phiwWindow k t, ratio M.b M.e (w j).1 (w j).2.1
  have hPint : ∫ w, P w ∂obsLaw M = 1 := by
    unfold obsLaw
    rw [MeasureTheory.integral_map (measurable_obsProj (T := T) (nX := nX)
      (nH := nH)).aemeasurable (phiwWindowProduct_measurable M.b M.e t).aestronglyMeasurable]
    simpa [P, obsProj] using
      integral_phiwWindowProduct_eq_one hign hoverlap hL hK t htk
  have hs : Integrable (fun w ↦ phiwScore k M.b M.e w t ^ 2) (obsLaw M) := by
    simpa only [Pi.pow_apply] using
      (phiwScore_memLp hign hoverlap hL hY 2 t).integrable_sq
  have hP : Integrable (fun w ↦ L ^ (k + 1) * P w) (obsLaw M) := by
    apply Integrable.const_mul
    apply Integrable.of_bound (phiwWindowProduct_measurable M.b M.e t).aestronglyMeasurable
      (L ^ (k + 1))
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg
      (phiwWindowProduct_nonneg hign.1 hoverlap.1 hoverlap.2
        (zero_le_one.trans hL) w t)]
    exact (phiwWindowProduct_le_pow_card hign.1 hoverlap.1 hoverlap.2
      (zero_le_one.trans hL) w t).trans
      (pow_le_pow_right₀ hL (card_phiwWindow_le (k := k) t))
  have hyobs : ∀ᵐ w ∂obsLaw M, |(w t).2.2| ≤ 1 := by
    unfold obsLaw
    let S : Set (ObsView T nX) := {w | |(w t).2.2| ≤ 1}
    have hS : MeasurableSet S := measurableSet_le
      (continuous_abs.measurable.comp ((measurable_pi_apply t).snd.snd)) measurable_const
    change ∀ᵐ w ∂M.law.map obsProj, w ∈ S
    apply (MeasureTheory.ae_map_iff
      (measurable_obsProj (T := T) (nX := nX) (nH := nH)).aemeasurable hS).2
    simpa [S, obsProj, rewardAt] using boundedReward_law_ae hY t
  calc
    _ ≤ ∫ w, L ^ (k + 1) * P w ∂obsLaw M := by
      apply integral_mono_ae hs hP
      filter_upwards [hyobs] with w hw
      change ((w t).2.2 * P w) ^ 2 ≤ L ^ (k + 1) * P w
      have hP0 : 0 ≤ P w := by
        exact phiwWindowProduct_nonneg (k := k) hign.1 hoverlap.1 hoverlap.2
          (zero_le_one.trans hL) w t
      have hPle := (phiwWindowProduct_le_pow_card hign.1 hoverlap.1 hoverlap.2
        (zero_le_one.trans hL) w t).trans
        (pow_le_pow_right₀ hL (card_phiwWindow_le (k := k) t))
      have hy2 : (w t).2.2 ^ 2 ≤ 1 := by
        nlinarith [sq_abs ((w t).2.2), abs_nonneg ((w t).2.2),
          sq_nonneg (1 - |(w t).2.2|)]
      calc
        _ = (w t).2.2 ^ 2 * P w ^ 2 := by ring
        _ ≤ 1 * P w ^ 2 := mul_le_mul_of_nonneg_right hy2 (sq_nonneg _)
        _ ≤ _ := by nlinarith
    _ = _ := by rw [integral_const_mul, hPint, mul_one]

/-- Absolute covariance is controlled by an absolute cross moment and the two absolute first
moments.  This is the algebraic last step used for both window regimes. [the h X condition](hyp:hX); and [the h Y condition](hyp:hY). [the stated conclusion](goal). -/
lemma abs_covariance_le_cross_add_first {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {X Y : Omega → ℝ}
    (hX : MemLp X 2 mu) (hY : MemLp Y 2 mu) :
    |covariance X Y mu| ≤
      ∫ w, |X w * Y w| ∂mu + (∫ w, |X w| ∂mu) * (∫ w, |Y w| ∂mu) := by
  rw [covariance_eq_sub hX hY]
  have hXint : Integrable X mu := hX.integrable one_le_two
  have hYint : Integrable Y mu := hY.integrable one_le_two
  have hXY : Integrable (X * Y) mu := hX.integrable_mul hY
  calc
    |∫ w, X w * Y w ∂mu - (∫ w, X w ∂mu) * ∫ w, Y w ∂mu| ≤
        |∫ w, X w * Y w ∂mu| +
          |∫ w, X w ∂mu| * |∫ w, Y w ∂mu| := by
            calc
              _ = |(∫ w, X w * Y w ∂mu) +
                  (-((∫ w, X w ∂mu) * ∫ w, Y w ∂mu))| := by rw [sub_eq_add_neg]
              _ ≤ |∫ w, X w * Y w ∂mu| +
                  |-((∫ w, X w ∂mu) * ∫ w, Y w ∂mu)| := abs_add_le _ _
              _ = _ := by rw [abs_neg, abs_mul]
    _ ≤ ∫ w, |X w * Y w| ∂mu +
          (∫ w, |X w| ∂mu) * (∫ w, |Y w| ∂mu) := by
      gcongr
      · exact abs_integral_le_integral_abs
      · exact abs_integral_le_integral_abs
      · exact abs_integral_le_integral_abs

/-- If both absolute first moments are at most one and the absolute cross moment is at most
`B ≥ 1`, then the covariance is at most `2B`.  This is the final algebraic passage in the
overlapping-window estimate (19). [the h X condition](hyp:hX); and [the h Y condition](hyp:hY); and [the h Xone condition](hyp:hXone); and [the h Yone condition](hyp:hYone); and [the hcross condition](hyp:hcross); and [the h B condition](hyp:hB). [the stated conclusion](goal). -/
lemma abs_covariance_le_two_mul {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {X Y : Omega → ℝ} {B : ℝ}
    (hX : MemLp X 2 mu) (hY : MemLp Y 2 mu)
    (hXone : ∫ w, |X w| ∂mu ≤ 1) (hYone : ∫ w, |Y w| ∂mu ≤ 1)
    (hcross : ∫ w, |X w * Y w| ∂mu ≤ B) (hB : 1 ≤ B) :
    |covariance X Y mu| ≤ 2 * B := by
  have hX0 : 0 ≤ ∫ w, |X w| ∂mu := integral_nonneg fun _ ↦ abs_nonneg _
  have hY0 : 0 ≤ ∫ w, |Y w| ∂mu := integral_nonneg fun _ ↦ abs_nonneg _
  have hprod : (∫ w, |X w| ∂mu) * (∫ w, |Y w| ∂mu) ≤ 1 := by
    nlinarith [mul_nonneg hX0 (sub_nonneg.mpr hYone),
      mul_nonneg hY0 (sub_nonneg.mpr hXone)]
  calc
    _ ≤ ∫ w, |X w * Y w| ∂mu +
        (∫ w, |X w| ∂mu) * (∫ w, |Y w| ∂mu) :=
      abs_covariance_le_cross_add_first mu hX hY
    _ ≤ B + 1 := add_le_add hcross hprod
    _ ≤ 2 * B := by linarith

/-- Equation (19), cross-moment form.  The union of the two windows is normalized, while each
ratio in their intersection contributes only one uncancelled factor `L`. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the h Y condition](hyp:hY); and [the htk condition](hyp:htk); and [the hu condition](hyp:hu); and [the hhk condition](hyp:hhk). [the stated conclusion](goal). -/
lemma integral_abs_phiwScore_mul_le_overlapDecay {T nX nH k h : Nat} {L : ℝ}
    {M : RawPomdpExperiment T nX nH} (hign : SequentialIgnorability M)
    (hoverlap : PolicyOverlap L M) (hL : 1 ≤ L) (hK : PomdpKernelLaw M)
    (hY : BoundedReward M) (t u : Fin T) (htk : k ≤ t.val)
    (hu : u.val = t.val + h) (hhk : h ≤ k) :
    ∫ w, |phiwScore k M.b M.e w t * phiwScore k M.b M.e w u| ∂obsLaw M ≤
      L ^ (k + 1 - h) := by
  letI : IsProbabilityMeasure (obsLaw M) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_obsProj (T := T) (nX := nX) (nH := nH)).aemeasurable
  let U : Finset (Fin T) := phiwWindow k t ∪ phiwWindow k u
  let PU : ObsView T nX → ℝ := fun w ↦
    ∏ j ∈ U, ratio M.b M.e (w j).1 (w j).2.1
  have hPUmeas : Measurable PU := by
    dsimp [PU]
    apply Finset.measurable_prod
    intro j _
    exact (measurable_of_finite (fun xa : Fin nX × Bool ↦ ratio M.b M.e xa.1 xa.2)).comp
      (((measurable_pi_apply j).fst).prodMk ((measurable_pi_apply j).snd.fst))
  have hPUint : ∫ w, PU w ∂obsLaw M = 1 := by
    unfold obsLaw
    rw [MeasureTheory.integral_map
      (measurable_obsProj (T := T) (nX := nX) (nH := nH)).aemeasurable
      hPUmeas.aestronglyMeasurable]
    have hlo : t.val - k ≤ u.val := by omega
    simpa [PU, U, obsProj, phiwWindow_union_eq_interval t u htk hu hhk] using
      integral_intervalRatioProduct_eq_one hign hoverlap hL hK (t.val - k) u hlo
  have hPU0 : ∀ w, 0 ≤ PU w := by
    intro w
    exact Finset.prod_nonneg fun j _ ↦
      (ratio_mem hign.1 hoverlap.1 hoverlap.2 (zero_le_one.trans hL) _ _).1
  have hPU : Integrable PU (obsLaw M) := by
    apply Integrable.of_bound hPUmeas.aestronglyMeasurable (L ^ U.card)
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (hPU0 w)]
    calc
      _ ≤ ∏ _j ∈ U, L := Finset.prod_le_prod
        (fun j _ ↦ (ratio_mem hign.1 hoverlap.1 hoverlap.2
          (zero_le_one.trans hL) _ _).1)
        (fun j _ ↦ (ratio_mem hign.1 hoverlap.1 hoverlap.2
          (zero_le_one.trans hL) _ _).2)
      _ = _ := by simp
  have hcross : Integrable (fun w ↦
      |phiwScore k M.b M.e w t * phiwScore k M.b M.e w u|) (obsLaw M) := by
    exact ((phiwScore_memLp (k := k) hign hoverlap hL hY 2 t).integrable_mul
      (phiwScore_memLp (k := k) hign hoverlap hL hY 2 u)).abs
  have hy (r : Fin T) : ∀ᵐ w ∂obsLaw M, |(w r).2.2| ≤ 1 := by
    unfold obsLaw
    let S : Set (ObsView T nX) := {w | |(w r).2.2| ≤ 1}
    have hS : MeasurableSet S := measurableSet_le
      (continuous_abs.measurable.comp ((measurable_pi_apply r).snd.snd)) measurable_const
    change ∀ᵐ w ∂M.law.map obsProj, w ∈ S
    apply (MeasureTheory.ae_map_iff
      (measurable_obsProj (T := T) (nX := nX) (nH := nH)).aemeasurable hS).2
    simpa [S, obsProj, rewardAt] using boundedReward_law_ae hY r
  calc
    _ ≤ ∫ w, L ^ (k + 1 - h) * PU w ∂obsLaw M := by
      apply integral_mono_ae hcross (hPU.const_mul _)
      filter_upwards [hy t, hy u] with w hyt hyu
      let R : Fin T → ℝ := fun j ↦ ratio M.b M.e (w j).1 (w j).2.1
      have hR0 (j : Fin T) : 0 ≤ R j :=
        (ratio_mem hign.1 hoverlap.1 hoverlap.2 (zero_le_one.trans hL) _ _).1
      have hRI : (∏ j ∈ phiwWindow k t ∩ phiwWindow k u, R j) ≤
          L ^ (k + 1 - h) := by
        calc
          _ ≤ ∏ _j ∈ phiwWindow k t ∩ phiwWindow k u, L :=
            Finset.prod_le_prod (fun j _ ↦ hR0 j)
              (fun j _ ↦ (ratio_mem hign.1 hoverlap.1 hoverlap.2
                (zero_le_one.trans hL) _ _).2)
          _ = L ^ (phiwWindow k t ∩ phiwWindow k u).card := by simp
          _ ≤ _ := pow_le_pow_right₀ hL (card_phiwWindow_inter_le t u htk hu hhk)
      have hA0 : 0 ≤ ∏ j ∈ phiwWindow k t, R j := Finset.prod_nonneg fun j _ ↦ hR0 j
      have hB0 : 0 ≤ ∏ j ∈ phiwWindow k u, R j := Finset.prod_nonneg fun j _ ↦ hR0 j
      have hU0 : 0 ≤ ∏ j ∈ phiwWindow k t ∪ phiwWindow k u, R j :=
        Finset.prod_nonneg fun j _ ↦ hR0 j
      rw [phiwScore, phiwScore, abs_mul, abs_mul, abs_mul]
      change |(w t).2.2| * |∏ j ∈ phiwWindow k t, R j| *
          (|(w u).2.2| * |∏ j ∈ phiwWindow k u, R j|) ≤
        L ^ (k + 1 - h) * PU w
      rw [abs_of_nonneg hA0, abs_of_nonneg hB0]
      change |(w t).2.2| * (∏ j ∈ phiwWindow k t, R j) *
          (|(w u).2.2| * ∏ j ∈ phiwWindow k u, R j) ≤
        L ^ (k + 1 - h) * PU w
      calc
        _ ≤ (∏ j ∈ phiwWindow k t, R j) *
            ∏ j ∈ phiwWindow k u, R j := by
          have hyt0 := abs_nonneg ((w t).2.2)
          have hyu0 := abs_nonneg ((w u).2.2)
          have hyp : |(w t).2.2| * |(w u).2.2| ≤ 1 :=
            mul_le_one₀ hyt hyu0 hyu
          calc
            _ = (|(w t).2.2| * |(w u).2.2|) *
                ((∏ j ∈ phiwWindow k t, R j) *
                  ∏ j ∈ phiwWindow k u, R j) := by ring
            _ ≤ 1 * ((∏ j ∈ phiwWindow k t, R j) *
                  ∏ j ∈ phiwWindow k u, R j) :=
              mul_le_mul_of_nonneg_right hyp (mul_nonneg hA0 hB0)
            _ = _ := one_mul _
        _ = (∏ j ∈ phiwWindow k t ∪ phiwWindow k u, R j) *
            ∏ j ∈ phiwWindow k t ∩ phiwWindow k u, R j :=
          prod_mul_prod_eq_union_mul_inter R _ _
        _ ≤ (∏ j ∈ phiwWindow k t ∪ phiwWindow k u, R j) *
            L ^ (k + 1 - h) := mul_le_mul_of_nonneg_left hRI hU0
        _ = _ := by simp [PU, U, R, mul_comm]
    _ = _ := by rw [integral_const_mul, hPUint, mul_one]

/-- Equation (19), covariance form. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the h Y condition](hyp:hY); and [the htk condition](hyp:htk); and [the hu condition](hyp:hu); and [the hhpos condition](hyp:hhpos); and [the hhk condition](hyp:hhk). [the stated conclusion](goal). -/
lemma abs_covariance_phiwScore_le_overlapDecay {T nX nH k h : Nat} {L : ℝ}
    {M : RawPomdpExperiment T nX nH} (hign : SequentialIgnorability M)
    (hoverlap : PolicyOverlap L M) (hL : 1 ≤ L) (hK : PomdpKernelLaw M)
    (hY : BoundedReward M) (t u : Fin T) (htk : k ≤ t.val)
    (hu : u.val = t.val + h) (hhpos : 1 ≤ h) (hhk : h ≤ k) :
    |covariance (phiwScore k M.b M.e · t) (phiwScore k M.b M.e · u) (obsLaw M)| ≤
      2 * L ^ (k + 1 - h) := by
  letI : IsProbabilityMeasure (obsLaw M) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_obsProj (T := T) (nX := nX) (nH := nH)).aemeasurable
  have huk : k ≤ u.val := by omega
  apply abs_covariance_le_two_mul (obsLaw M)
    (phiwScore_memLp (k := k) hign hoverlap hL hY 2 t)
    (phiwScore_memLp (k := k) hign hoverlap hL hY 2 u)
    (integral_abs_phiwScore_le_one hign hoverlap hL hK hY t htk)
    (integral_abs_phiwScore_le_one hign hoverlap hL hK hY u huk)
    (integral_abs_phiwScore_mul_le_overlapDecay
      hign hoverlap hL hK hY t u htk hu hhk)
  exact one_le_pow₀ hL

end CausalSmith.Stat.PomdpLatentOverlapMinimax

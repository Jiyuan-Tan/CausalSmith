module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.CountVector

/-!
# Fixed-word laws for labeled Poisson samples

The unshuffled marked Poisson sample has independent label streams. Capping a
fixed iid pool preserves the corresponding nonoverflow law, and averaging the
cap has an explicit finite count-and-label expansion.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteMeasurablePartition

variable {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
  [Fintype I] [MeasurableSingletonClass I]

/-- [Unshuffling finite labeled samples into ordered label streams is measurable](goal). -/
@[fun_prop] theorem measurable_unshuffle :
    Measurable (unshuffle (X := X) (I := I)) := by
  classical
  apply measurable_pi_lambda
  intro i t ht
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet
    {z : Fin n → X × I | unshuffle (⟨n, z⟩ : FiniteSample (X × I)) i ∈ t}
  have hsection :
      {z : Fin n → X × I | unshuffle (⟨n, z⟩ : FiniteSample (X × I)) i ∈ t} =
        ⋃ w : Fin n → I,
          {z | (fun k => (z k).2) = w} ∩
            {z | (⟨wordHistogram w i,
              gatherWord w (fun k => (z k).1) i⟩ : FiniteSample X) ∈ t} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hz
      refine ⟨fun k => (z k).2, rfl, ?_⟩
      exact hz
    · rintro ⟨w, hw, hz⟩
      subst w
      exact hz
  rw [hsection]
  apply MeasurableSet.iUnion
  intro w
  apply MeasurableSet.inter
  · exact (measurable_pi_lambda _ fun k => measurable_snd.comp (measurable_pi_apply k))
      (measurableSet_singleton w)
  · exact ((measurable_fixedSizeEmbed (wordHistogram w i)).comp
      ((measurable_pi_apply i).comp
        ((measurable_gatherWord w).comp
          (measurable_pi_lambda _ fun k => measurable_fst.comp (measurable_pi_apply k))))) ht

/-- For [a fixed finite label word](hyp:w), regrouping iid observations by that word
has the product law of iid tuples in its label cells, with each tuple length given by
[the number of occurrences of its label](goal). -/
theorem map_gatherWord_iid_pi
    {m : ℕ} (w : Fin m → I) (P : Measure X) [IsProbabilityMeasure P] :
    Measure.map (gatherWord w) (Measure.pi (fun _ : Fin m => P)) =
      Measure.pi (fun i : I =>
        Measure.pi (fun _ : Fin (wordHistogram w i) => P)) := by
  let e := (wordUnshuffleEquiv w).symm
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : Σ i : I, Fin (wordHistogram w i) => X) e
  have hreindex : Measure.map reindex (Measure.pi fun _ : Fin m => P) =
      Measure.pi fun _ : Σ i : I, Fin (wordHistogram w i) => P := by
    exact Measure.pi_map_piCongrLeft e
      (fun _ : Σ i : I, Fin (wordHistogram w i) => P)
  have hfun : gatherWord (Y := X) w =
      MeasurableEquiv.piCurry
        (fun i : I => fun _ : Fin (wordHistogram w i) => X) ∘ reindex := by
    funext z i k
    simp only [Function.comp_apply]
    rw [MeasurableEquiv.piCurry_apply]
    change z (wordUnshuffleEquiv w ⟨i, k⟩) =
      (Equiv.piCongrLeft
        (fun _ : Σ i : I, Fin (wordHistogram w i) => X) e) z ⟨i, k⟩
    rw [Equiv.piCongrLeft_apply]
    simp [e]
  rw [hfun, ← Measure.map_map
    (MeasurableEquiv.piCurry _).measurable reindex.measurable,
    hreindex]
  simpa only [Measure.infinitePi_eq_pi] using
    Measure.infinitePi_map_piCurry
      (fun i : I => fun _ : Fin (wordHistogram w i) => P)

/-- Given [an observation probability law](hyp:P), [finite label masses](hyp:p,hp),
and [a fixed label word](hyp:w), [the law of iid marked observations restricted
to that word, then unshuffled, is its word probability times the product of
the corresponding fixed-length iid observation streams](goal). -/
theorem map_unshuffle_restrict_labelWord
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1)
    {m : ℕ} (w : Fin m → I) :
    Measure.map
      (fun z : Fin m → X × I => unshuffle (⟨m, z⟩ : FiniteSample (X × I)))
      ((Measure.pi (fun _ : Fin m => P.prod (labelLaw p hp))).restrict
        {z | (fun k => (z k).2) = w}) =
      (∏ k, (p (w k) : ℝ≥0∞)) •
        Measure.pi (fun i : I =>
          Measure.map (fixedSizeEmbed (wordHistogram w i))
            (Measure.pi (fun _ : Fin (wordHistogram w i) => P))) := by
  classical
  letI := labelLaw_isProbabilityMeasure p hp
  let e := MeasurableEquiv.arrowProdEquivProdArrow X I (Fin m)
  let μ : Measure (Fin m → X) := Measure.pi (fun _ => P)
  let ν : Measure (Fin m → I) := Measure.pi (fun _ => labelLaw p hp)
  have hmass (i : I) : labelLaw p hp {i} = (p i : ℝ≥0∞) := by
    unfold labelLaw
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i), PMF.ofFintype_apply]
  have hν : ν {w} = ∏ k, (p (w k) : ℝ≥0∞) := by
    simp only [ν, Measure.pi_singleton, hmass]
  have hpre : e ⁻¹' (Set.univ ×ˢ {w}) =
      {z : Fin m → X × I | (fun k => (z k).2) = w} := by
    ext z
    simp [e, MeasurableEquiv.arrowProdEquivProdArrow,
      Equiv.arrowProdEquivProdArrow]
  have hsource : Measure.map e
      ((Measure.pi (fun _ : Fin m => P.prod (labelLaw p hp))).restrict
        {z | (fun k => (z k).2) = w}) =
      (∏ k, (p (w k) : ℝ≥0∞)) • Measure.map (fun x : Fin m → X => (x, w)) μ := by
    rw [← hpre, ← Measure.restrict_map e.measurable (MeasurableSet.univ.prod
      (measurableSet_singleton w)),
      (measurePreserving_arrowProdEquivProdArrow X I (Fin m)
        (fun _ => P) (fun _ => labelLaw p hp)).map_eq]
    change (μ.prod ν).restrict (Set.univ ×ˢ {w}) = _
    rw [← Measure.prod_restrict, Measure.restrict_univ,
      Measure.restrict_singleton, hν, Measure.prod_smul_right,
      Measure.prod_dirac]
  have htarget : Measure.map
      (fun x : Fin m → X =>
        fun i => fixedSizeEmbed (wordHistogram w i) (gatherWord w x i)) μ =
      Measure.pi (fun i : I =>
        Measure.map (fixedSizeEmbed (wordHistogram w i))
          (Measure.pi (fun _ : Fin (wordHistogram w i) => P))) := by
    change Measure.map
      ((fun y i => fixedSizeEmbed (wordHistogram w i) (y i)) ∘ gatherWord w) μ = _
    calc
      _ = Measure.map (fun y => fun i =>
            fixedSizeEmbed (wordHistogram w i) (y i))
            (Measure.map (gatherWord w) μ) :=
          (Measure.map_map
            (measurable_pi_lambda _ fun i =>
              (measurable_fixedSizeEmbed _).comp (measurable_pi_apply i))
            (measurable_gatherWord w)).symm
      _ = _ := by
        rw [map_gatherWord_iid_pi w P]
        exact Measure.pi_map_pi (fun i => (measurable_fixedSizeEmbed _).aemeasurable)
  calc
    _ = Measure.map
        (fun q : (Fin m → X) × (Fin m → I) =>
          unshuffle (⟨m, fun k => (q.1 k, q.2 k)⟩ : FiniteSample (X × I)))
        (Measure.map e
          ((Measure.pi (fun _ : Fin m => P.prod (labelLaw p hp))).restrict
            {z | (fun k => (z k).2) = w})) := by
          rw [Measure.map_map]
          · rfl
          · exact measurable_unshuffle.comp (measurable_fixedSizeEmbed m |>.comp
              (measurable_pi_lambda _ fun k =>
                ((measurable_pi_apply k).comp measurable_fst).prodMk
                  ((measurable_pi_apply k).comp measurable_snd)))
          · exact e.measurable
    _ = _ := by
      rw [hsource, Measure.map_smul]
      congr 1
      calc
        Measure.map (fun q : (Fin m → X) × (Fin m → I) =>
          unshuffle (⟨m, fun k => (q.1 k, q.2 k)⟩ : FiniteSample (X × I)))
          (Measure.map (fun x : Fin m → X => (x, w)) μ) =
            Measure.map (fun x : Fin m → X =>
              unshuffle (⟨m, fun k => (x k, w k)⟩ : FiniteSample (X × I))) μ := by
                rw [Measure.map_map]
                · rfl
                · exact measurable_unshuffle.comp (measurable_fixedSizeEmbed m |>.comp
                    (measurable_pi_lambda _ fun k =>
                      ((measurable_pi_apply k).comp measurable_fst).prodMk
                        ((measurable_pi_apply k).comp measurable_snd)))
                · fun_prop
        _ = _ := by
          convert htarget using 1
          congr 1

/-- Given [an observation probability law](hyp:P), [finite label masses](hyp:p,hp),
and [a prescribed label-count vector](hyp:c), restricting an iid marked tuple
of the matching total length to that histogram and unshuffling it gives [the
sum of the matching label-word weights times independent fixed-length iid
observation streams](goal). -/
theorem map_unshuffle_restrict_histogram_eq
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (c : I → ℕ) :
    Measure.map
      (fun z : Fin (∑ i, c i) → X × I =>
        unshuffle (⟨∑ i, c i, z⟩ : FiniteSample (X × I)))
      ((Measure.pi (fun _ : Fin (∑ i, c i) => P.prod (labelLaw p hp))).restrict
        {z | ∀ i, wordHistogram (fun k => (z k).2) i = c i}) =
      (∑ w : Fin (∑ i, c i) → I,
        if ∀ i, wordHistogram w i = c i then
          ∏ k, (p (w k) : ℝ≥0∞) else 0) •
        Measure.pi (fun i : I =>
          Measure.map (fixedSizeEmbed (c i))
            (Measure.pi (fun _ : Fin (c i) => P))) := by
  -- The histogram event is the disjoint union of its finite label-word
  -- fibres. Map each restricted fibre with
  -- `map_unshuffle_restrict_labelWord`; all matching words have identical
  -- target product laws, so factor that measure out of the finite sum.
  classical
  let m := ∑ i, c i
  let μ : Measure (Fin m → X × I) :=
    Measure.pi (fun _ : Fin m => P.prod (labelLaw p hp))
  let f : (Fin m → X × I) → (I → FiniteSample X) :=
    fun z => unshuffle (⟨m, z⟩ : FiniteSample (X × I))
  let good : (Fin m → I) → Prop := fun w => ∀ i, wordHistogram w i = c i
  let fibre : (Fin m → I) → Set (Fin m → X × I) :=
    fun w => {z | (fun k => (z k).2) = w}
  let cell : (Fin m → I) → Set (Fin m → X × I) :=
    fun w => if good w then fibre w else ∅
  have hmeas (w : Fin m → I) : MeasurableSet (cell w) := by
    dsimp [cell]
    split
    · exact (measurable_pi_lambda _ fun k =>
        measurable_snd.comp (measurable_pi_apply k)) (measurableSet_singleton w)
    · exact MeasurableSet.empty
  have hdisj : ((Finset.univ : Finset (Fin m → I)) : Set (Fin m → I)).Pairwise
      (fun w v => Disjoint (cell w) (cell v)) := by
    intro w _ v _ hne
    apply Set.disjoint_left.mpr
    intro z hzw hzv
    dsimp [cell] at hzw hzv
    split_ifs at hzw hzv <;> try simp_all
    exact hne (hzw.symm.trans hzv)
  have hunion : (⋃ w ∈ (Finset.univ : Finset (Fin m → I)), cell w) =
      {z | good (fun k => (z k).2)} := by
    ext z
    simp only [Set.mem_iUnion, Finset.mem_univ, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨w, _, hw⟩
      dsimp [cell] at hw
      split_ifs at hw with h
      · exact (show (fun k => (z k).2) = w from hw) ▸ h
      · simpa using hw
    · intro hz
      refine ⟨fun k => (z k).2, by simp, ?_⟩
      simp [cell, hz, fibre]
  have hpartition : μ.restrict {z | good (fun k => (z k).2)} =
      ∑ w : Fin m → I, μ.restrict (cell w) := by
    rw [← hunion, Measure.restrict_biUnion_finset hdisj hmeas,
      Measure.sum_fintype]
    simpa [Finset.sum_coe_sort]
  have hfixed (w : Fin m → I) :
      Measure.map f (μ.restrict (cell w)) =
        (if good w then ∏ k, (p (w k) : ℝ≥0∞) else 0) •
          Measure.pi (fun i : I =>
            Measure.map (fixedSizeEmbed (c i))
              (Measure.pi (fun _ : Fin (c i) => P))) := by
    by_cases hw : good w
    · simp only [cell, if_pos hw]
      rw [map_unshuffle_restrict_labelWord P p hp w]
      congr 1
      change ∀ i, wordHistogram w i = c i at hw
      exact congrArg Measure.pi (funext fun i => by rw [hw i])
    · simp [cell, hw]
  change Measure.map f (μ.restrict {z | good (fun k => (z k).2)}) = _
  rw [hpartition, Measure.map_finset_sum]
  · simp_rw [hfixed]
    rw [Finset.sum_smul]
  · exact measurable_unshuffle.comp (measurable_fixedSizeEmbed m) |>.aemeasurable

/-- For [an iid observation law](hyp:P), [label masses](hyp:p) [summing to
one](hyp:hp), [a pool size](hyp:n), and [a shorter prefix length](hyp:h),
[pairing the observation and label prefixes gives iid marked observations](goal). -/
theorem map_joint_prefix_pi
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1)
    {n m : ℕ} (h : m ≤ n) :
    Measure.map
      (fun z : (Fin n → X) × (Fin n → I) =>
        fun k : Fin m =>
          (z.1 ⟨k.val, lt_of_lt_of_le k.isLt h⟩,
            z.2 ⟨k.val, lt_of_lt_of_le k.isLt h⟩))
      ((fixedPoolLaw P n).prod (Measure.pi (fun _ : Fin n => labelLaw p hp))) =
      Measure.pi (fun _ : Fin m => P.prod (labelLaw p hp)) := by
  classical
  letI := labelLaw_isProbabilityMeasure p hp
  let Q := labelLaw p hp
  let μ := P.prod Q
  let pair : (Fin n → X) × (Fin n → I) → (Fin n → X × I) :=
    fun z k => (z.1 k, z.2 k)
  let pref : (Fin n → X × I) → (Fin m → X × I) :=
    fun z k => z ⟨k.val, lt_of_lt_of_le k.isLt h⟩
  have hpair : Measure.map pair
      ((fixedPoolLaw P n).prod (Measure.pi (fun _ : Fin n => Q))) =
        Measure.pi (fun _ : Fin n => μ) := by
    have he : pair = (MeasurableEquiv.arrowProdEquivProdArrow X I (Fin n)).symm := by
      funext z k
      rfl
    rw [he]
    exact (measurePreserving_arrowProdEquivProdArrow X I (Fin n)
      (fun _ => P) (fun _ => Q)).symm.map_eq
  have hprefix : Measure.map pref (Measure.pi (fun _ : Fin n => μ)) =
      Measure.pi (fun _ : Fin m => μ) := by
    symm
    refine Measure.pi_eq (fun s hs => ?_)
    rw [Measure.map_apply (by fun_prop) (.univ_pi hs)]
    have hpre : pref ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun j : Fin n =>
          if hj : j.val < m then s ⟨j.val, hj⟩ else Set.univ) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro hz j
        split
        · exact hz ⟨j.val, ‹j.val < m›⟩
        · trivial
      · intro hz k
        simpa [pref] using hz ⟨k.val, lt_of_lt_of_le k.isLt h⟩
    rw [hpre, Measure.pi_pi]
    let t : Finset (Fin n) := Finset.univ.filter fun j => j.val < m
    have ht (j : t) : j.val.val < m := by
      simpa only [t, Finset.mem_filter, Finset.mem_univ, true_and] using j.property
    let e : Fin m ≃ t :=
      { toFun := fun k => ⟨⟨k.val, lt_of_lt_of_le k.isLt h⟩, by simp [t, k.isLt]⟩
        invFun := fun j => ⟨j.val.val, ht j⟩
        left_inv := fun k => by rfl
        right_inv := fun j => by ext; rfl }
    calc
      (∏ j : Fin n, μ
          (if hj : j.val < m then s ⟨j.val, hj⟩ else Set.univ)) =
          ∏ j : Fin n, if hj : j.val < m then
            μ (s ⟨j.val, hj⟩) else 1 := by
            apply Fintype.prod_congr
            intro j
            split <;> simp
      _ = ∏ j : t, μ (s ⟨j.val.val, ht j⟩) := by
        rw [Finset.prod_dite]
        simp only [Finset.prod_const_one, mul_one]
        apply Fintype.prod_congr
        intro j
        congr 2
      _ = ∏ k : Fin m, μ (s k) := by
        symm
        apply Fintype.prod_equiv e
        intro k
        rfl
  calc
    Measure.map (fun z : (Fin n → X) × (Fin n → I) =>
      fun k : Fin m =>
        (z.1 ⟨k.val, lt_of_lt_of_le k.isLt h⟩,
          z.2 ⟨k.val, lt_of_lt_of_le k.isLt h⟩))
        ((fixedPoolLaw P n).prod (Measure.pi (fun _ : Fin n => Q))) =
        Measure.map pref (Measure.map pair
          ((fixedPoolLaw P n).prod (Measure.pi (fun _ : Fin n => Q)))) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
    _ = Measure.pi (fun _ : Fin m => μ) := by rw [hpair, hprefix]

/-- [The total length of the ordered label streams](goal) equals the length of
[the original labeled sample](hyp:s). -/
theorem unshuffle_total_count (s : FiniteSample (X × I)) :
    ∑ i, ((unshuffle s) i).count = s.count := by
  classical
  let w : Fin s.count → I := fun k => (s.2 k).2
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin s.count)))
    (t := (Finset.univ : Finset I)) (f := w)
    (fun k _ => Finset.mem_univ (w k))
  change ∑ i, wordHistogram w i = s.count
  simpa [wordHistogram, w] using h.symm

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

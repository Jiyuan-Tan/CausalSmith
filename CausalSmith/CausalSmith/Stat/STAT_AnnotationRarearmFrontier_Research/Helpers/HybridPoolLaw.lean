module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.BaselinePoolStatistic
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridFiniteEncoding

/-!
Exact independent laws of the three disjoint original-record hybrid pools.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- [Under the stated hypotheses](hyp:hn), Three consecutive blocks of an iid array retain their independent iid laws.  This gives [the stated result](goal). -/
-- @node: hybrid_split_three_iid_law
lemma hybrid_split_three_iid_law {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (h p f n : Nat) (hn : n = h + (p + f)) :
    MeasurePreserving
      (fun s : Fin n → X =>
        (fun i : Fin h => s ⟨i.val, by omega⟩,
         fun i : Fin p => s ⟨h + i.val, by omega⟩,
         fun i : Fin f => s ⟨h + p + i.val, by omega⟩))
      (Measure.pi (fun _ : Fin n => P))
      ((Measure.pi (fun _ : Fin h => P)).prod
        ((Measure.pi (fun _ : Fin p => P)).prod (Measure.pi (fun _ : Fin f => P)))) := by
  have hfirst := baseline_split_iid_law_of_eq P h (p + f) n hn
  have hlast := (MeasurePreserving.id (Measure.pi (fun _ : Fin h => P))).prod
    (baseline_split_iid_law P p f)
  convert hlast.comp hfirst using 1
  funext s
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · funext i
      change s ⟨h + p + i.val, _⟩ = s ⟨h + (p + i.val), _⟩
      exact congrArg s (Fin.ext (Nat.add_assoc h p i.val))

/-- Under the stated inputs and conditions, Regroup four independent pools to pair the pilot blocks and the factorial blocks.  This gives [the stated result](goal). -/
-- @node: hybrid_regroup_four_pools_law
lemma hybrid_regroup_four_pools_law {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (pa : Measure A) (pb : Measure B) (pc : Measure C) (pd : Measure D)
    [IsProbabilityMeasure pa] [IsProbabilityMeasure pb]
    [IsProbabilityMeasure pc] [IsProbabilityMeasure pd] :
    MeasurePreserving (fun z : (A × B) × (C × D) => ((z.1.1,z.2.1),(z.1.2,z.2.2)))
      ((pa.prod pb).prod (pc.prod pd)) ((pa.prod pc).prod (pb.prod pd)) := by
  have h1 := measurePreserving_prodAssoc pa pb (pc.prod pd)
  have h2 := (MeasurePreserving.id pa).prod (measurePreserving_prodAssoc pb pc pd).symm
  have h3 := (MeasurePreserving.id pa).prod
    ((Measure.measurePreserving_swap (μ := pb) (ν := pc)).prod (MeasurePreserving.id pd))
  have h4 := (MeasurePreserving.id pa).prod (measurePreserving_prodAssoc pc pb pd)
  have h5 := (measurePreserving_prodAssoc pa pc (pb.prod pd)).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

/-- [Under the stated hypotheses](hyp:hk), Rewriting a pool capacity preserves its iid law and ordered coordinates.  This gives [the stated result](goal). -/
-- @node: hybrid_cast_iid_law
lemma hybrid_cast_iid_law {X : Type*} [MeasurableSpace X]
    (P : Measure X) (h k : Nat) (hk : k = h) :
    MeasurePreserving (fun s : Fin h → X => fun i : Fin k => s (Fin.cast hk i))
      (Measure.pi (fun _ : Fin h => P)) (Measure.pi (fun _ : Fin k => P)) := by
  subst k
  exact MeasurePreserving.id _

/-- Complete outcomes, pilot marginals, and factorial marginals use disjoint ordered blocks. -/
-- @node: hybridFixedPools
noncomputable def hybridFixedPools {n m d : Nat} (eps : Real) (s : Sample n m d) :
    (Fin (hybridTuning n m eps).h0 → Obs d) ×
      (Fin (hybridTuning n m eps).Mp → AuxObs d) ×
      (Fin (hybridTuning n m eps).Mf → AuxObs d) :=
  let tun := hybridTuning n m eps
  (fun i => s.1 ⟨i.val, by dsimp [tun, hybridTuning] at i ⊢; omega⟩,
   Fin.append (fun i : Fin tun.hp =>
     let z := s.1 ⟨tun.h0 + i.val, by dsimp [tun, hybridTuning] at i ⊢; omega⟩
     (z.1,z.2.1)) (fun i : Fin (m / 2) => s.2 ⟨i.val, by omega⟩),
   fun i : Fin tun.Mf => (Fin.append (fun i : Fin tun.hf =>
     let z := s.1 ⟨tun.h0 + tun.hp + i.val, by dsimp [tun, hybridTuning] at i ⊢; omega⟩
     (z.1,z.2.1)) (fun i : Fin (m - m / 2) => s.2 ⟨m / 2 + i.val, by omega⟩))
     (Fin.cast (by dsimp [tun, hybridTuning]; omega) i))

/-- Extracting the three finite pools is measurable. This gives [the stated conclusion](goal). -/
@[fun_prop]
-- @node: hybridFixedPools_measurable
lemma hybridFixedPools_measurable (n m d : Nat) (eps : Real) :
    Measurable (hybridFixedPools (n := n) (m := m) (d := d) eps) := by
  unfold hybridFixedPools
  apply Measurable.prodMk
  · fun_prop
  · apply Measurable.prodMk
    all_goals
      apply measurable_pi_lambda
      intro i
      first
      | refine Fin.addCases ?_ ?_ i
      | refine Fin.addCases ?_ ?_ (Fin.cast _ i)
      · intro j
        simp only [Fin.append_left]
        fun_prop
      · intro j
        simp only [Fin.append_right]
        fun_prop

/-- [Under the stated inputs and conditions](hyp:eps,P,n,m,d), Under the original data law, the extracted hybrid pools are mutually independent.
The two marginal pools concatenate projected complete records with auxiliary records.  This gives [the stated result](goal).-/
-- @node: hybrid_fixed_pools_law
lemma hybrid_fixed_pools_law {n m d : Nat} (eps : Real) (P : DiscreteLaw d) :
    MeasurePreserving (hybridFixedPools (n := n) (m := m) eps)
      (annotationLaw P n m)
      ((labeledProductLaw P (hybridTuning n m eps).h0).prod
        ((auxProductLaw P (hybridTuning n m eps).Mp).prod
          (auxProductLaw P (hybridTuning n m eps).Mf))) := by
  let tun := hybridTuning n m eps
  let auxprob (k : Nat) : IsProbabilityMeasure (auxProductLaw P k) := by
    unfold auxProductLaw
    infer_instance
  have hsplit := hybrid_split_three_iid_law (obsLaw P) tun.h0 tun.hp tun.hf n
    (by dsimp [tun, hybridTuning]; omega)
  have haux := baseline_split_iid_law_of_eq (auxMarginal P).toMeasure
    (m / 2) (m - m / 2) m (by omega)
  have hproj := (MeasurePreserving.id (labeledProductLaw P tun.h0)).prod
    ((baseline_project_iid_law P tun.hp).prod (baseline_project_iid_law P tun.hf))
  have hfirst := (hproj.comp hsplit).prod haux
  have hassoc := measurePreserving_prodAssoc (labeledProductLaw P tun.h0)
    ((auxProductLaw P tun.hp).prod (auxProductLaw P tun.hf))
    ((auxProductLaw P (m / 2)).prod (auxProductLaw P (m - m / 2)))
  have hshuffle := (MeasurePreserving.id (labeledProductLaw P tun.h0)).prod
    (hybrid_regroup_four_pools_law (auxProductLaw P tun.hp) (auxProductLaw P tun.hf)
      (auxProductLaw P (m / 2)) (auxProductLaw P (m - m / 2)))
  have happ := (MeasurePreserving.id (labeledProductLaw P tun.h0)).prod
    ((baseline_append_iid_law (auxMarginal P).toMeasure tun.hp (m / 2)).prod
      (baseline_append_iid_law (auxMarginal P).toMeasure tun.hf (m - m / 2)))
  have hcast : MeasurePreserving
      (fun s : Fin (tun.hf + (m - m / 2)) → AuxObs d =>
        fun i : Fin tun.Mf => s (Fin.cast (by dsimp [tun, hybridTuning]; omega) i))
      (auxProductLaw P (tun.hf + (m - m / 2))) (auxProductLaw P tun.Mf) := by
    exact hybrid_cast_iid_law (auxMarginal P).toMeasure _ _
      (by dsimp [tun, hybridTuning]; omega)
  have hlast := (MeasurePreserving.id (labeledProductLaw P tun.h0)).prod
    ((MeasurePreserving.id (auxProductLaw P tun.Mp)).prod hcast)
  convert hlast.comp (happ.comp (hshuffle.comp (hassoc.comp hfirst))) using 1
  · funext s
    rfl
  · rfl

/-- [Under the stated inputs and conditions](hyp:eps,P,T,hT,theta,n,m,d), Any measurable statistic of the three extracted pools has the independent-pool risk.  This gives [the stated result](goal).-/
-- @node: hybrid_fixed_pools_sqRisk
lemma hybrid_fixed_pools_sqRisk {n m d : Nat} (eps : Real) (P : DiscreteLaw d)
    (T : ((Fin (hybridTuning n m eps).h0 → Obs d) ×
      (Fin (hybridTuning n m eps).Mp → AuxObs d) ×
      (Fin (hybridTuning n m eps).Mf → AuxObs d)) → Real)
    (hT : Measurable T) (theta : Real) :
    Causalean.Stat.sqRisk (annotationLaw P n m) (T ∘ hybridFixedPools eps) theta =
      Causalean.Stat.sqRisk
        ((labeledProductLaw P (hybridTuning n m eps).h0).prod
          ((auxProductLaw P (hybridTuning n m eps).Mp).prod
            (auxProductLaw P (hybridTuning n m eps).Mf))) T theta := by
  unfold Causalean.Stat.sqRisk
  rw [← (hybrid_fixed_pools_law eps P).map_eq]
  exact (integral_map (hybridFixedPools_measurable n m d eps).aemeasurable
    ((hT.sub measurable_const).pow_const 2).aestronglyMeasurable).symm

/-- [Under the stated inputs and conditions](hyp:eps,s,r,hr,n,m,d), The outcome prefix keeps exactly the first requested complete records.  This gives [the stated result](goal).-/
-- @node: hybrid_fixed_complete_prefix_eq
lemma hybrid_fixed_complete_prefix_eq {n m d : Nat} (eps : Real) (s : Sample n m d)
    (r : Nat) (hr : r ≤ (hybridTuning n m eps).h0) :
    prefixOfLE (hybridFixedPools eps s).1 r hr =
      baselineBlockPrefix s.1 0 r (by dsimp [hybridTuning] at hr; omega) := by
  simp [prefixOfLE, hybridFixedPools, baselineBlockPrefix]

/-- [Under the stated inputs and conditions](hyp:eps,s,r,hr,n,m,d), The pilot prefix uses the pilot complete block before its auxiliary block.  This gives [the stated result](goal).-/
-- @node: hybrid_fixed_pilot_prefix_eq
lemma hybrid_fixed_pilot_prefix_eq {n m d : Nat} (eps : Real) (s : Sample n m d)
    (r : Nat) (hr : r ≤ (hybridTuning n m eps).Mp) :
    prefixOfLE (hybridFixedPools eps s).2.1 r hr =
      baselineAuxiliaryPrefix s (hybridTuning n m eps).h0
        (hybridTuning n m eps).hp 0 r
        (by dsimp [hybridTuning]; omega)
        (by dsimp [hybridTuning] at hr ⊢; omega) := by
  dsimp [hybridFixedPools, hybridTuning] at hr ⊢
  rw [baseline_prefix_append_eq]
  simp only [baselineAuxiliaryPrefix, baselineBlockPrefix, FiniteSample.points,
    FiniteSample.count, Nat.zero_add]

/-- [Under the stated hypotheses](hyp:hk,hr), Casting an array capacity does not change any retained ordered prefix.  This gives [the stated result](goal). -/
-- @node: hybrid_prefix_cast_eq
lemma hybrid_prefix_cast_eq {X : Type*} [MeasurableSpace X] {h k : Nat}
    (hk : k = h) (s : Fin h → X) (r : Nat) (hr : r ≤ k) :
    prefixOfLE (fun i : Fin k => s (Fin.cast hk i)) r hr =
      prefixOfLE s r (by omega) := by
  subst k
  rfl

/-- [Under the stated inputs and conditions](hyp:eps,s,r,hr,n,m,d), The factorial prefix uses the final complete block before the final auxiliary block.  This gives [the stated result](goal).-/
-- @node: hybrid_fixed_factorial_prefix_eq
lemma hybrid_fixed_factorial_prefix_eq {n m d : Nat} (eps : Real) (s : Sample n m d)
    (r : Nat) (hr : r ≤ (hybridTuning n m eps).Mf) :
    prefixOfLE (hybridFixedPools eps s).2.2 r hr =
      baselineAuxiliaryPrefix s
        ((hybridTuning n m eps).h0 + (hybridTuning n m eps).hp)
        (hybridTuning n m eps).hf (m / 2) r
        (by dsimp [hybridTuning]; omega)
        (by dsimp [hybridTuning] at hr ⊢; omega) := by
  dsimp only [hybridFixedPools]
  rw [hybrid_prefix_cast_eq]
  rw [baseline_prefix_append_eq]
  rfl

/-- [Under the stated inputs and conditions](hyp:eps,s,hr0,hrp,hrf,n,m,d,r0,rp,rf), Every retained triple computes the same clipped statistic in the array and pool forms.  This gives [the stated result](goal).-/
-- @node: hybrid_fixed_prefix_statistic_eq
lemma hybrid_fixed_prefix_statistic_eq {n m d : Nat} (eps : Real) (s : Sample n m d)
    (r0 rp rf : Nat)
    (hr0 : r0 ≤ (hybridTuning n m eps).h0)
    (hrp : rp ≤ (hybridTuning n m eps).Mp)
    (hrf : rf ≤ (hybridTuning n m eps).Mf) :
    hybridPrefixStatistic eps r0 rp rf s =
      hybridOrderedPrefixStatistic (hybridTuning n m eps)
        (prefixOfLE (hybridFixedPools eps s).1 r0 hr0,
         prefixOfLE (hybridFixedPools eps s).2.1 rp hrp,
         prefixOfLE (hybridFixedPools eps s).2.2 rf hrf) := by
  rw [hybrid_fixed_complete_prefix_eq, hybrid_fixed_pilot_prefix_eq,
    hybrid_fixed_factorial_prefix_eq]
  exact hybrid_prefix_statistic_eq_ordered eps s r0 rp rf _ _ _ _ _

/-- The independent fixed-pool statistic returns zero whenever any request overflows. -/
-- @node: hybridCappedFixedStatistic
noncomputable def hybridCappedFixedStatistic {n m d : Nat} (eps : Real)
    (s : (Fin (hybridTuning n m eps).h0 → Obs d) ×
      (Fin (hybridTuning n m eps).Mp → AuxObs d) ×
      (Fin (hybridTuning n m eps).Mf → AuxObs d)) (k : Nat × Nat × Nat) : Real :=
  if hk : k.1 ≤ (hybridTuning n m eps).h0 ∧
      k.2.1 ≤ (hybridTuning n m eps).Mp ∧ k.2.2 ≤ (hybridTuning n m eps).Mf then
    hybridOrderedPrefixStatistic (hybridTuning n m eps)
      (prefixOfLE s.1 k.1 hk.1, prefixOfLE s.2.1 k.2.1 hk.2.1,
        prefixOfLE s.2.2 k.2.2 hk.2.2)
  else 0

/-- [Under the stated inputs and conditions](hyp:eps,s,k,n,m,d), Valid requests agree by count readback, and both forms reset overflow to zero.  This gives [the stated result](goal).-/
-- @node: hybrid_capped_array_eq_fixed
lemma hybrid_capped_array_eq_fixed {n m d : Nat} (eps : Real) (s : Sample n m d)
    (k : Nat × Nat × Nat) :
    hybridCappedArrayStatistic eps s k =
      hybridCappedFixedStatistic eps (hybridFixedPools eps s) k := by
  by_cases hk : k.1 ≤ (hybridTuning n m eps).h0 ∧
      k.2.1 ≤ (hybridTuning n m eps).Mp ∧ k.2.2 ≤ (hybridTuning n m eps).Mf
  · simp only [hybridCappedArrayStatistic, hybridCappedFixedStatistic, hk, ite_true, dif_pos]
    exact hybrid_fixed_prefix_statistic_eq eps s k.1 k.2.1 k.2.2 hk.1 hk.2.1 hk.2.2
  · simp [hybridCappedArrayStatistic, hybridCappedFixedStatistic, hk]

/-- [Under the stated inputs and conditions](hyp:eps,P,n,m,d), Extraction of disjoint pools preserves the independent request law as well.  This gives [the stated result](goal).-/
-- @node: hybrid_fixed_pools_request_law
lemma hybrid_fixed_pools_request_law {n m d : Nat} (eps : Real) (P : DiscreteLaw d) :
    MeasurePreserving (Prod.map (hybridFixedPools (n := n) (m := m) eps) id)
      ((annotationLaw P n m).prod (hybridRequestLaw n m eps))
      (((labeledProductLaw P (hybridTuning n m eps).h0).prod
        ((auxProductLaw P (hybridTuning n m eps).Mp).prod
          (auxProductLaw P (hybridTuning n m eps).Mf))).prod (hybridRequestLaw n m eps)) :=
  (hybrid_fixed_pools_law eps P).prod (MeasurePreserving.id _)

/-- [Under the stated inputs and conditions](hyp:eps,P,n,m,d), The capped array risk is exactly its independent three-pool risk.  This gives [the stated result](goal).-/
-- @node: hybrid_capped_array_risk_eq_fixed
lemma hybrid_capped_array_risk_eq_fixed {n m d : Nat} (eps : Real) (P : DiscreteLaw d) :
    Causalean.Stat.sqRisk ((annotationLaw P n m).prod (hybridRequestLaw n m eps))
      (fun z => hybridCappedArrayStatistic eps z.1 z.2) (ateFunctional P) =
    Causalean.Stat.sqRisk
      (((labeledProductLaw P (hybridTuning n m eps).h0).prod
        ((auxProductLaw P (hybridTuning n m eps).Mp).prod
          (auxProductLaw P (hybridTuning n m eps).Mf))).prod (hybridRequestLaw n m eps))
      (fun z => hybridCappedFixedStatistic eps z.1 z.2) (ateFunctional P) := by
  have hmap := hybrid_fixed_pools_request_law (n := n) (m := m) eps P
  have hm : Measurable (fun z : ((Fin (hybridTuning n m eps).h0 → Obs d) ×
      (Fin (hybridTuning n m eps).Mp → AuxObs d) ×
      (Fin (hybridTuning n m eps).Mf → AuxObs d)) × (Nat × Nat × Nat) =>
      (hybridCappedFixedStatistic (n := n) (m := m) (d := d) eps z.1 z.2 -
        ateFunctional P) ^ 2) := by fun_prop
  unfold Causalean.Stat.sqRisk
  rw [← hmap.map_eq, integral_map hmap.measurable.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with z
  simp only [hybrid_capped_array_eq_fixed]
  rfl

/-- [Under the stated inputs and conditions](hyp:eps,P,hS,n,m,d), Conditional averaging bounds original-record risk by the independent capped-pool risk.  This gives [the stated result](goal).-/
-- @node: hybrid_ruleRisk_le_capped_fixed_risk
lemma hybrid_ruleRisk_le_capped_fixed_risk {n m d : Nat} (eps : Real) (P : DiscreteLaw d)
    (hS : Real.exp 4096 ≤ (n : Real) * eps) :
    ruleRisk (liftRule (hybridEstimator n m d eps)) P ≤
    Causalean.Stat.sqRisk
      (((labeledProductLaw P (hybridTuning n m eps).h0).prod
        ((auxProductLaw P (hybridTuning n m eps).Mp).prod
          (auxProductLaw P (hybridTuning n m eps).Mf))).prod (hybridRequestLaw n m eps))
      (fun z => hybridCappedFixedStatistic eps z.1 z.2) (ateFunctional P) := by
  rw [← hybrid_capped_array_risk_eq_fixed]
  exact hybrid_ruleRisk_le_capped_array_risk eps P hS

end CausalSmith.Stat.AnnotationRarearmFrontier

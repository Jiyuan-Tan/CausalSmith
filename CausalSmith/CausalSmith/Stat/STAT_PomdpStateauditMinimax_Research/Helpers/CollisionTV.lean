module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.CloneClass
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.CollisionEnvelope
public import Causalean.Stat.Minimax.OverlapCoupling
public import Mathlib.Data.Fintype.CardEmbedding

/-! # Overflow-safe comparison of fixed-permutation mixtures and fresh labels. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory

/-- Two audited epochs query the same complete cloned state. -/
def CloneCollision {T n k m : Nat} (mask : AuditMask T)
    (w : FullPath T 1 (n * m) k) : Prop :=
  ∃ (t u : Fin T), t ≠ u ∧ mask t = true ∧ mask u = true ∧
    currentState w t = currentState w u

-- @node: cloneCollision_implies_coordinateCollision
/-- A repeated audited cloned state must reuse a clone coordinate. This is the
pathwise containment used in the occupancy bound, independent of the base law. -/
lemma cloneCollision_implies_coordinateCollision {T n k m : Nat}
    (π : Fin n × Fin m ≃ Fin (n * m))
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m)
    (mask : AuditMask T)
    (h : CloneCollision mask (clonePath π w coords)) :
    ∃ (t u : Fin T), t ≠ u ∧ mask t = true ∧ mask u = true ∧
      coords t.castSucc = coords u.castSucc := by
  rcases h with ⟨t, u, htu, ht, hu, heq⟩
  refine ⟨t, u, htu, ht, hu, ?_⟩
  have hlabel := congrArg Prod.snd heq
  change π ((currentState w t).2, coords t.castSucc) =
    π ((currentState w u).2, coords u.castSucc) at hlabel
  exact congrArg Prod.snd (π.injective hlabel)

-- @node: auditedIndex
/-- The finite subtype of epochs selected by an audit mask. -/
abbrev auditedIndex {T : Nat} (mask : AuditMask T) :=
  {t : Fin T // mask t = true}

-- @node: card_injective_audited_assignments
/-- There are exactly `m.descFactorial r` collision-free assignments of clone
coordinates to a mask selecting `r` epochs. -/
lemma card_injective_audited_assignments {T m : Nat} (mask : AuditMask T) :
    Fintype.card {f : auditedIndex mask → Fin m // Function.Injective f} =
      Nat.descFactorial m (Fintype.card (auditedIndex mask)) := by
  classical
  rw [show Fintype.card {f : auditedIndex mask → Fin m // Function.Injective f} =
      Fintype.card (auditedIndex mask ↪ Fin m) by
        exact Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _)]
  simpa using
    (Fintype.card_embedding_eq (α := auditedIndex mask) (β := Fin m))

-- @node: uniformPi_atomic
/-- A finite product of uniform coordinate laws is the uniform atomic law on
all coordinate assignments. -/
private lemma uniformPi_atomic {I : Type} [Fintype I] [DecidableEq I]
    (m : Nat) (hm : 1 ≤ m) :
    Measure.pi (fun _ : I => uniformFin m) =
      ∑ f : I → Fin m,
        ENNReal.ofReal (1 / (m : ℝ)) ^ Fintype.card I • Measure.dirac f := by
  letI : IsProbabilityMeasure (uniformFin m) := uniformFin_prob m hm
  apply Measure.ext_of_singleton
  intro f
  rw [Measure.pi_singleton]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply',
    MeasurableSet.singleton, smul_eq_mul]
  simp_rw [uniformFin_singleton]
  simp only [Finset.prod_const]
  rw [Fintype.sum_eq_single f]
  · simp
  · intro g hgf
    simp [Set.indicator, hgf]

-- @node: uniformPi_injective_mass
/-- Under a finite uniform product, the mass of injective assignments is the
number of such assignments times the common atomic mass. -/
private lemma uniformPi_injective_mass {I : Type} [Fintype I] [DecidableEq I]
    (m : Nat) (hm : 1 ≤ m) :
    (Measure.pi (fun _ : I => uniformFin m)) {f | Function.Injective f} =
      ENNReal.ofReal (1 / (m : ℝ)) ^ Fintype.card I *
        Fintype.card {f : I → Fin m // Function.Injective f} := by
  rw [uniformPi_atomic m hm, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply',
    MeasurableSet.of_discrete]
  rw [← Finset.mul_sum]
  congr 1
  simp only [Set.indicator, Pi.one_apply, Set.mem_ofPred_eq]
  rw [Finset.sum_boole]
  exact_mod_cast
    (Fintype.card_subtype (fun f : I → Fin m => Function.Injective f)).symm

-- @node: uniformPi_predicate_mass
/-- Every predicate under a finite uniform product has mass equal to its number
of satisfying assignments times the common atomic mass. -/
private lemma uniformPi_predicate_mass {I : Type} [Fintype I] [DecidableEq I]
    (m : Nat) (hm : 1 ≤ m) (P : (I → Fin m) → Prop) [DecidablePred P] :
    (Measure.pi (fun _ : I => uniformFin m)) {f | P f} =
      ENNReal.ofReal (1 / (m : ℝ)) ^ Fintype.card I *
        Fintype.card {f : I → Fin m // P f} := by
  rw [uniformPi_atomic m hm, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply',
    MeasurableSet.of_discrete]
  rw [← Finset.mul_sum]
  congr 1
  simp only [Set.indicator, Pi.one_apply, Set.mem_ofPred_eq]
  rw [Finset.sum_boole]
  exact_mod_cast (Fintype.card_subtype P).symm

-- @node: auditMaskFinsetEquiv
/-- Audit masks are equivalent to finite subsets of epochs via their true bits. -/
private def auditMaskFinsetEquiv (T : Nat) : AuditMask T ≃ Finset (Fin T) where
  toFun mask := Finset.univ.filter fun t => mask t = true
  invFun s t := decide (t ∈ s)
  left_inv mask := by
    funext t
    cases h : mask t <;> simp [h]
  right_inv s := by
    ext t
    simp

-- @node: card_auditMasks_of_card
/-- Exactly `T.choose r` audit masks select `r` epochs. -/
private lemma card_auditMasks_of_card (T r : Nat) :
    Fintype.card {mask : AuditMask T // Fintype.card (auditedIndex mask) = r} =
      Nat.choose T r := by
  classical
  let e : {mask : AuditMask T // Fintype.card (auditedIndex mask) = r} ≃
      {s : Finset (Fin T) // s.card = r} :=
    Equiv.subtypeEquiv (auditMaskFinsetEquiv T) (by
      intro mask
      rw [Fintype.card_subtype]
      rfl)
  rw [Fintype.card_congr e]
  let ep : {s : Finset (Fin T) // s.card = r} ≃
      {s : Finset (Fin T) // s ∈ Finset.univ.powersetCard r} := {
    toFun s := ⟨s, by simp [s.2]⟩
    invFun s := ⟨s, by
      have hs := s.2
      simp only [Finset.mem_powersetCard] at hs
      exact hs.2⟩
    left_inv s := rfl
    right_inv s := rfl }
  rw [Fintype.card_congr ep, Fintype.card_subtype]
  simp

-- @node: auditMask_sum_by_card
/-- A sum over audit masks of a function of the number of true bits is the
corresponding binomial-cardinality sum. -/
private lemma auditMask_sum_by_card {R : Type} [AddCommMonoid R]
    (T : Nat) (F : Nat → R) :
    ∑ mask : AuditMask T, F (Fintype.card (auditedIndex mask)) =
      ∑ r ∈ Finset.range (T + 1), Nat.choose T r • F r := by
  classical
  let rank : AuditMask T → Fin (T + 1) := fun mask =>
    ⟨Fintype.card (auditedIndex mask), by
      have h := Fintype.card_le_of_injective Subtype.val
        (Subtype.val_injective : Function.Injective
          (Subtype.val : auditedIndex mask → Fin T))
      simpa using Nat.lt_succ_of_le h⟩
  rw [← Finset.sum_fiberwise Finset.univ rank
    (fun mask => F (Fintype.card (auditedIndex mask)))]
  change (∑ j : Fin (T + 1), ∑ mask with rank mask = j,
      F (Fintype.card (auditedIndex mask))) = _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r hr
  have hinner : (∑ mask with rank mask = r,
      F (Fintype.card (auditedIndex mask))) =
      (Finset.univ.filter fun mask : AuditMask T => rank mask = r).card • F r := by
    calc
      _ = ∑ mask with rank mask = r, F r := by
        apply Finset.sum_congr rfl
        intro mask hmask
        have heq := (Finset.mem_filter.mp hmask).2
        have heq' : Fintype.card (auditedIndex mask) = r.val := by
          exact congrArg Fin.val heq
        rw [heq']
      _ = _ := by rw [Finset.sum_const]
  rw [hinner]
  congr 1
  rw [show (Finset.univ.filter fun mask : AuditMask T => rank mask = r).card =
      Fintype.card {mask : AuditMask T //
        Fintype.card (auditedIndex mask) = r.val} by
    rw [Fintype.card_subtype]
    congr 1
    ext mask
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      exact Fin.ext h]
  exact card_auditMasks_of_card T r.val

-- @node: auditBitLaw_singletons
/-- The two atoms of an admissible Bernoulli audit bit have their defining
probabilities. -/
private lemma auditBitLaw_singletons (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    auditBitLaw eta {true} = ENNReal.ofReal eta ∧
      auditBitLaw eta {false} = ENNReal.ofReal (1 - eta) := by
  constructor <;> simp [auditBitLaw, heta.1, heta.2]

-- @node: auditMaskLaw_singleton
/-- A mask with `r` audited epochs has Bernoulli product mass
`eta^r * (1-eta)^(T-r)`. -/
private lemma auditMaskLaw_singleton {T : Nat} (eta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (mask : AuditMask T) :
    auditMaskLaw T eta {mask} =
      ENNReal.ofReal eta ^ Fintype.card (auditedIndex mask) *
        ENNReal.ofReal (1 - eta) ^
          (T - Fintype.card (auditedIndex mask)) := by
  classical
  unfold auditMaskLaw
  letI : IsProbabilityMeasure (auditBitLaw eta) := by
    constructor
    simp [auditBitLaw]
    rw [← ENNReal.ofReal_add heta.1 (by linarith [heta.2] : 0 ≤ 1 - eta)]
    norm_num
  rw [Measure.pi_singleton]
  have hbit (t : Fin T) : auditBitLaw eta {mask t} =
      if mask t = true then ENNReal.ofReal eta else ENNReal.ofReal (1 - eta) := by
    cases h : mask t <;> simp [h, (auditBitLaw_singletons eta heta).1,
      (auditBitLaw_singletons eta heta).2]
  simp_rw [hbit]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  rw [show (Finset.univ.filter fun t : Fin T => mask t = true).card =
      Fintype.card (auditedIndex mask) by
    rw [Fintype.card_subtype]]
  congr 2
  rw [← Fintype.card_subtype]
  simpa using Fintype.card_subtype_compl (fun t : Fin T => mask t = true)

-- @node: card_full_assignments_injective_on_audit
/-- A collision-free assignment on the audited coordinates has arbitrary values
on every remaining coordinate, including the unused terminal coordinate. -/
private lemma card_full_assignments_injective_on_audit {T m : Nat}
    (mask : AuditMask T) :
    Fintype.card {coords : Fin (T + 1) → Fin m //
      Function.Injective (fun t : auditedIndex mask => coords t.1.castSucc)} =
      Nat.descFactorial m (Fintype.card (auditedIndex mask)) *
        m ^ (T + 1 - Fintype.card (auditedIndex mask)) := by
  classical
  let A := auditedIndex mask
  let e : A → Fin (T + 1) := fun t => t.1.castSucc
  have he : Function.Injective e := by
    intro t u h
    exact Subtype.ext (Fin.castSucc_inj.mp h)
  let p : Fin (T + 1) → Prop := fun i => i ∈ Set.range e
  let K := {i : Fin (T + 1) // ¬p i}
  let ei : A ⊕ K ≃ Fin (T + 1) :=
    (Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl K)).trans (Equiv.sumCompl p)
  let ef : (Fin (T + 1) → Fin m) ≃ (A → Fin m) × (K → Fin m) :=
    (Equiv.piCongrLeft (fun _ : Fin (T + 1) => Fin m) ei).symm.trans
      (Equiv.sumPiEquivProdPi (fun _ : A ⊕ K => Fin m))
  have hef (coords : Fin (T + 1) → Fin m) :
      (ef coords).1 = fun t : A => coords (e t) := by
    funext t
    rfl
  let es : {coords : Fin (T + 1) → Fin m //
      Function.Injective (fun t : A => coords (e t))} ≃
      {q : (A → Fin m) × (K → Fin m) // Function.Injective q.1} :=
    Equiv.subtypeEquiv ef (by intro coords; rw [hef])
  rw [Fintype.card_congr es, Fintype.card_congr Equiv.prodSubtypeFstEquivSubtypeProd,
    Fintype.card_prod, Fintype.card_fun, card_injective_audited_assignments mask]
  simp only [Fintype.card_fin]
  congr 1
  apply congrArg (fun x : Nat => m ^ x)
  change Fintype.card K = T + 1 - Fintype.card A
  rw [show Fintype.card K = Fintype.card (Fin (T + 1)) -
      Fintype.card {i : Fin (T + 1) // p i} by
    exact Fintype.card_subtype_compl p]
  congr 1
  · simp
  · exact Fintype.card_congr (Equiv.ofInjective e he).symm

-- @node: auditedCoordinateCollision_real
/-- For a fixed mask, independent uniform clone coordinates collide on the
audited epochs with the descending-factorial occupancy probability. -/
private lemma auditedCoordinateCollision_real {T m : Nat} (hm : 1 ≤ m)
    (mask : AuditMask T) :
    ((Measure.pi fun _ : Fin (T + 1) => uniformFin m)
      {coords | ¬Function.Injective
        (fun t : auditedIndex mask => coords t.1.castSucc)}).toReal =
      1 - (Nat.descFactorial m (Fintype.card (auditedIndex mask)) : ℝ) /
        (m : ℝ) ^ Fintype.card (auditedIndex mask) := by
  classical
  let μ := Measure.pi fun _ : Fin (T + 1) => uniformFin m
  let S : Set (Fin (T + 1) → Fin m) :=
    {coords | Function.Injective (fun t : auditedIndex mask => coords t.1.castSucc)}
  letI : IsProbabilityMeasure (uniformFin m) := uniformFin_prob m hm
  have hS : MeasurableSet S := MeasurableSet.of_discrete
  have hmass : μ S =
      ENNReal.ofReal (1 / (m : ℝ)) ^ (T + 1) *
        (Nat.descFactorial m (Fintype.card (auditedIndex mask)) *
          m ^ (T + 1 - Fintype.card (auditedIndex mask))) := by
    unfold μ S
    rw [uniformPi_predicate_mass m hm]
    rw [card_full_assignments_injective_on_audit mask]
    simp
  have hle : μ S ≤ 1 := by
    rw [← measure_univ (μ := μ)]
    exact measure_mono (Set.subset_univ S)
  change (μ Sᶜ).toReal = _
  rw [measure_compl hS (measure_ne_top μ S), measure_univ,
    ENNReal.toReal_sub_of_le hle (by simp), ENNReal.toReal_one, hmass]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (m : ℝ))]
  have hr : Fintype.card (auditedIndex mask) ≤ T + 1 := by
    calc
      Fintype.card (auditedIndex mask) ≤ Fintype.card (Fin T) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ ≤ T + 1 := by simp
  congr 1
  rw [one_div, inv_pow]
  field_simp
  calc
    (Nat.descFactorial m (Fintype.card (auditedIndex mask)) : ℝ) *
          (m : ℝ) ^ (T + 1 - Fintype.card (auditedIndex mask)) *
          (m : ℝ) ^ Fintype.card (auditedIndex mask) =
        (Nat.descFactorial m (Fintype.card (auditedIndex mask)) : ℝ) *
          ((m : ℝ) ^ (T + 1 - Fintype.card (auditedIndex mask)) *
            (m : ℝ) ^ Fintype.card (auditedIndex mask)) := by ring
    _ = (Nat.descFactorial m (Fintype.card (auditedIndex mask)) : ℝ) *
          (m : ℝ) ^ ((T + 1 - Fintype.card (auditedIndex mask)) +
            Fintype.card (auditedIndex mask)) := by rw [pow_add]
    _ = _ := by rw [Nat.sub_add_cancel hr]; ring

-- @node: fixedPermutationCoupling_coordinateMask
/-- Projecting the fixed-permutation coupling to clone coordinates and the audit
mask leaves their independent product law. -/
lemma fixedPermutationCoupling_coordinateMask {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m) (eta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    (fixedPermutationCoupling (m := m) M eta).map
        (fun q => (q.1.2, q.2.2)) =
      (Measure.pi fun _ : Fin (T + 1) => uniformFin m).prod
        (auditMaskLaw T eta) := by
  letI : IsProbabilityMeasure (uniformFin m) := uniformFin_prob m hm
  letI : IsProbabilityMeasure (auditMaskLaw T eta) := by
    unfold auditMaskLaw
    letI : IsProbabilityMeasure (auditBitLaw eta) := by
      constructor
      simp [auditBitLaw]
      rw [← ENNReal.ofReal_add heta.1 (by linarith [heta.2] : 0 ≤ 1 - eta)]
      norm_num
    infer_instance
  letI : IsProbabilityMeasure (uniformRelabeling n m) := by
    letI : Nonempty (Fin n × Fin m ≃ Fin (n * m)) := ⟨finProdFinEquiv⟩
    constructor
    simp [uniformRelabeling]
    rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast
      (Fintype.card_pos : 0 < Fintype.card (Fin n × Fin m ≃ Fin (n * m)))),
      ENNReal.ofReal_natCast]
    exact ENNReal.mul_inv_cancel
      (by exact_mod_cast (Nat.ne_of_gt
        (Fintype.card_pos : 0 < Fintype.card (Fin n × Fin m ≃ Fin (n * m))))) (by simp)
  unfold fixedPermutationCoupling
  rw [show (fun q : (FullPath T 1 n k × (Fin (T + 1) → Fin m)) ×
      ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T) => (q.1.2, q.2.2)) =
      Prod.map Prod.snd Prod.snd by rfl]
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  simp

-- @node: coordinateMaskCollision_real
/-- Averaging the fixed-mask occupancy probability over Bernoulli audit masks
is exactly the binomial collision envelope. -/
lemma coordinateMaskCollision_real {T m : Nat} (hm : 1 ≤ m)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    (((Measure.pi fun _ : Fin (T + 1) => uniformFin m).prod
      (auditMaskLaw T eta))
        {q | ¬Function.Injective
          (fun t : auditedIndex q.2 => q.1 t.1.castSucc)}).toReal =
      collisionEnvelope T eta m := by
  classical
  letI : IsProbabilityMeasure (uniformFin m) := uniformFin_prob m hm
  letI : IsProbabilityMeasure (auditMaskLaw T eta) := by
    unfold auditMaskLaw
    letI : IsProbabilityMeasure (auditBitLaw eta) := by
      constructor
      simp [auditBitLaw]
      rw [← ENNReal.ofReal_add heta.1 (by linarith [heta.2] : 0 ≤ 1 - eta)]
      norm_num
    infer_instance
  have hset : MeasurableSet
      {q : (Fin (T + 1) → Fin m) × AuditMask T |
        ¬Function.Injective (fun t : auditedIndex q.2 => q.1 t.1.castSucc)} :=
    MeasurableSet.of_discrete
  rw [Measure.prod_apply_symm hset, lintegral_fintype]
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
    change (∑ mask : AuditMask T,
      ((Measure.pi fun _ : Fin (T + 1) => uniformFin m)
        {coords | ¬Function.Injective
          (fun t : auditedIndex mask => coords t.1.castSucc)}).toReal *
        (auditMaskLaw T eta {mask}).toReal) = _
    simp_rw [auditedCoordinateCollision_real hm,
      auditMaskLaw_singleton eta heta]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow]
    simp_rw [← mul_assoc]
    rw [auditMask_sum_by_card T (fun r =>
      (1 - (Nat.descFactorial m r : ℝ) / (m : ℝ) ^ r) *
        (ENNReal.ofReal eta).toReal ^ r *
        (ENNReal.ofReal (1 - eta)).toReal ^ (T - r))]
    rw [ENNReal.toReal_ofReal heta.1,
      ENNReal.toReal_ofReal (by linarith [heta.2] : 0 ≤ 1 - eta)]
    unfold collisionEnvelope
    apply Finset.sum_congr rfl
    intro r hr
    simp only [nsmul_eq_mul]
    ring
  · intro mask hmask
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

/-- Strip the audit bits and labels from an audited record. -/
def auditedProjection {T nX nH k : Nat}
    (w : AuditedRecord T nX nH k) : ObsPath T nX k :=
  fun t => ((w t).1, (w t).2.1, (w t).2.2.1)

-- @node: freshRecord_projection
/-- A fresh audited record retains every coordinate of the observed path. -/
lemma freshRecord_projection {T n k m : Nat} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (w : ObsPath T 1 k) (mask : AuditMask T)
    (σ : Equiv.Perm (Fin (n * m))) :
    auditedProjection (freshRecord hn hm w mask σ) = w := by
  funext t
  rfl

-- @node: uniformPermutation_prob
/-- The uniform law on relabelings has total mass one. -/
lemma uniformPermutation_prob (r : Nat) :
    IsProbabilityMeasure (uniformPermutation r) := by
  constructor
  simp [uniformPermutation]
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast
    (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Fin r)))), ENNReal.ofReal_natCast]
  exact ENNReal.mul_inv_cancel
    (by exact_mod_cast (Nat.ne_of_gt
      (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Fin r))))) (by simp)

-- @node: auditBitLaw_prob
/-- A Bernoulli audit bit has total mass one at every admissible rate. -/
lemma auditBitLaw_prob (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (auditBitLaw eta) := by
  constructor
  simp [auditBitLaw]
  rw [← ENNReal.ofReal_add heta.1 (by linarith [heta.2] : 0 ≤ 1 - eta)]
  norm_num

-- @node: auditMaskLaw_prob
/-- The independent audit mask has total mass one. -/
lemma auditMaskLaw_prob (T : Nat) (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (auditMaskLaw T eta) := by
  unfold auditMaskLaw
  letI : IsProbabilityMeasure (auditBitLaw eta) := auditBitLaw_prob eta heta
  infer_instance

-- @node: auditedLaw_prob
/-- Independent admissible audit bits give a probability law on audited records. -/
lemma auditedLaw_prob {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (auditedLaw eta M) := by
  letI : IsProbabilityMeasure (auditMaskLaw T eta) :=
    auditMaskLaw_prob T eta heta
  unfold auditedLaw auditJointLaw
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  show Measurable (fun q : FullPath T nX nH k × AuditMask T => auditRecord q.1 q.2)
  ·
    unfold auditRecord currentState actionAt rewardAt
    apply measurable_pi_lambda
    intro t
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.ite
    · exact (((measurable_pi_apply t).comp measurable_snd)
        (measurableSet_singleton true) :
          MeasurableSet ((fun q : FullPath T nX nH k × AuditMask T => q.2 t) ⁻¹' {true}))
    · fun_prop
    · fun_prop

-- @node: permutationMixture_prob
/-- The uniform mixture over legal fixed relabelings has unit mass. -/
lemma permutationMixture_prob {T n k m : Nat} (M : PomdpModel T 1 n k)
    (hm : 1 ≤ m) (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (permutationMixture M hm eta) := by
  constructor
  simp only [permutationMixture, Measure.finsetSum_apply, Measure.smul_apply]
  have hmass (π : Fin n × Fin m ≃ Fin (n * m)) :
      (auditedLaw eta (cloneModel M hm π)) Set.univ = 1 :=
    (auditedLaw_prob _ eta heta).measure_univ
  simp only [hmass, mul_one, Finset.sum_const]
  letI : Nonempty (Fin n × Fin m ≃ Fin (n * m)) := ⟨finProdFinEquiv⟩
  simp only [nsmul_eq_mul, mul_one, Finset.card_univ, one_div, ENNReal.smul_one]
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast
    (Fintype.card_pos : 0 < Fintype.card (Fin n × Fin m ≃ Fin (n * m)))),
    ENNReal.ofReal_natCast]
  simp only [smul_eq_mul, mul_one]
  exact ENNReal.mul_inv_cancel
    (by exact_mod_cast (Nat.ne_of_gt
      (Fintype.card_pos : 0 < Fintype.card (Fin n × Fin m ≃ Fin (n * m))))) (by simp)

-- @node: auditRecord_atomic_labels
/-- The concrete audit record reports exactly the sampled bit and the atomic
state label and is equivariant under a fixed relabeling. -/
lemma auditRecord_atomic_labels {T nX nH k : Nat} :
    AtomicAuditLabels (auditRecord (T := T) (nX := nX) (nH := nH) (k := k)) := by
  constructor
  · intro w mask t
    simp [auditRecord]
  · intro σ w mask t
    simp [relabelAudit, auditRecord]

-- @node: auditedLaw_projection
/-- Erasing the audit bits and labels recovers the unaudited observation law. -/
lemma auditedLaw_projection {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (eta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    (auditedLaw eta M).map auditedProjection = obsLaw M := by
  have hmask : IsProbabilityMeasure (auditMaskLaw T eta) :=
    auditMaskLaw_prob T eta heta
  letI : IsProbabilityMeasure (auditMaskLaw T eta) := hmask
  have hrecord : Measurable (fun q : FullPath T nX nH k × AuditMask T =>
      auditRecord q.1 q.2) := by
    unfold auditRecord currentState actionAt rewardAt
    apply measurable_pi_lambda
    intro t
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.ite
    · exact (((measurable_pi_apply t).comp measurable_snd)
        (measurableSet_singleton true) :
          MeasurableSet ((fun q : FullPath T nX nH k × AuditMask T => q.2 t) ⁻¹' {true}))
    · fun_prop
    · fun_prop
  have hprojection : Measurable (auditedProjection (T := T) (nX := nX)
      (nH := nH) (k := k)) := by
    unfold auditedProjection
    fun_prop
  unfold auditedLaw auditJointLaw obsLaw
  rw [Measure.map_map hprojection hrecord]
  have hfun : (fun q : FullPath T nX nH k × AuditMask T =>
      auditedProjection (auditRecord q.1 q.2)) = fun q => obsProj q.1 := by
    funext q t
    rfl
  change Measure.map (fun q : FullPath T nX nH k × AuditMask T =>
      auditedProjection (auditRecord q.1 q.2)) _ = _
  rw [hfun]
  have hobs : Measurable (obsProj (T := T) (nX := nX) (nH := nH) (k := k)) := by
    unfold obsProj currentState actionAt rewardAt
    fun_prop
  calc
    (M.law.prod (auditMaskLaw T eta)).map (fun q => obsProj q.1) =
        ((M.law.prod (auditMaskLaw T eta)).map Prod.fst).map obsProj :=
      (Measure.map_map hobs measurable_fst).symm
    _ = M.law.map obsProj := by simp

-- @node: freshKernel_projection_mass
/-- Projection of the fresh-label kernel is concentrated at its input path. -/
lemma freshKernel_projection_mass {T n k m : Nat} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (eta : ℝ) (w : ObsPath T 1 k) :
    ((freshKernel hn hm eta) w).map auditedProjection =
      ((auditMaskLaw T eta).prod (uniformPermutation (n * m))) Set.univ •
        Measure.dirac w := by
  have hrecord : Measurable (fun q : AuditMask T × Equiv.Perm (Fin (n * m)) =>
      freshRecord hn hm w q.1 q.2) := by
    fun_prop
  have hprojection : Measurable (auditedProjection (T := T) (nX := 1)
      (nH := n * m) (k := k)) := by
    unfold auditedProjection
    fun_prop
  change (((auditMaskLaw T eta).prod (uniformPermutation (n * m))).map
      (fun q => freshRecord hn hm w q.1 q.2)).map auditedProjection = _
  rw [Measure.map_map hprojection hrecord]
  have hfun : (fun q : AuditMask T × Equiv.Perm (Fin (n * m)) =>
      auditedProjection (freshRecord hn hm w q.1 q.2)) = fun _ => w := by
    funext q
    exact freshRecord_projection hn hm w q.1 q.2
  change Measure.map (fun q : AuditMask T × Equiv.Perm (Fin (n * m)) =>
      auditedProjection (freshRecord hn hm w q.1 q.2)) _ = _
  rw [hfun, Measure.map_const]

-- @node: freshLabelLaw_projection
/-- Erasing the fresh audit labels recovers the observed-path law. -/
lemma freshLabelLaw_projection {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    (freshLabelLaw M hn hm eta).map auditedProjection = obsLaw M := by
  have hmask : IsProbabilityMeasure (auditMaskLaw T eta) :=
    auditMaskLaw_prob T eta heta
  have hperm : IsProbabilityMeasure (uniformPermutation (n * m)) :=
    uniformPermutation_prob (n * m)
  letI : IsProbabilityMeasure (auditMaskLaw T eta) := hmask
  letI : IsProbabilityMeasure (uniformPermutation (n * m)) := hperm
  have hmass : ((auditMaskLaw T eta).prod (uniformPermutation (n * m))) Set.univ = 1 :=
    measure_univ
  have hprojection : Measurable (auditedProjection (T := T) (nX := 1)
      (nH := n * m) (k := k)) := by
    unfold auditedProjection
    fun_prop
  unfold freshLabelLaw
  rw [Measure.map_comp _ _ hprojection]
  have hker : (freshKernel hn hm eta).map auditedProjection =
      (Kernel.id : Kernel (ObsPath T 1 k) (ObsPath T 1 k)) := by
    ext w
    rw [Kernel.map_apply, freshKernel_projection_mass hn hm eta w, hmass]
    · simp only [one_smul, Kernel.id_apply, Measure.dirac_apply]
    · exact hprojection
  rw [hker, Measure.id_comp]

-- @node: freshKernel_markov
/-- The common fresh-label channel has unit mass. -/
lemma freshKernel_markov {T n k m : Nat} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    IsMarkovKernel (freshKernel (T := T) (k := k) hn hm eta) := by
  have hmask : IsProbabilityMeasure (auditMaskLaw T eta) :=
    auditMaskLaw_prob T eta heta
  have hperm : IsProbabilityMeasure (uniformPermutation (n * m)) :=
    uniformPermutation_prob (n * m)
  letI : IsProbabilityMeasure (auditMaskLaw T eta) := hmask
  letI : IsProbabilityMeasure (uniformPermutation (n * m)) := hperm
  constructor
  intro w
  change IsProbabilityMeasure
    (((auditMaskLaw T eta).prod (uniformPermutation (n * m))).map
      (fun q => freshRecord hn hm w q.1 q.2))
  exact Measure.isProbabilityMeasure_map (by fun_prop)

-- @node: tvDist_map_le_audited
/-- Erasing a measurable augmentation cannot increase total variation. -/
lemma tvDist_map_le_audited {T n k m : Nat}
    (μ ν : Measure (AuditedRecord T 1 (n * m) k))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Causalean.Stat.tvDist (μ.map auditedProjection) (ν.map auditedProjection) ≤
      Causalean.Stat.tvDist μ ν := by
  have hproj : Measurable (auditedProjection (T := T) (nX := 1)
      (nH := n * m) (k := k)) := by
    unfold auditedProjection
    fun_prop
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨B, hB⟩
  rw [Measure.real, Measure.real]
  simp only [Measure.map_apply hproj hB]
  exact Causalean.Stat.abs_measureReal_sub_le_tvDist (hproj hB)

-- @node: freshLabelLaw_tv_eq_obsLaw
/-- The fresh-label experiment preserves exactly the testing distance between
two unaudited observed-path laws. -/
lemma freshLabelLaw_tv_eq_obsLaw {T n k m : Nat}
    (Mp Mm : PomdpModel T 1 n k) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    Causalean.Stat.tvDist (freshLabelLaw Mp hn hm eta)
      (freshLabelLaw Mm hn hm eta) =
    Causalean.Stat.tvDist (obsLaw Mp) (obsLaw Mm) := by
  letI : IsProbabilityMeasure (obsLaw Mp) :=
    Measure.isProbabilityMeasure_map (by unfold obsProj currentState actionAt rewardAt; fun_prop)
  letI : IsProbabilityMeasure (obsLaw Mm) :=
    Measure.isProbabilityMeasure_map (by unfold obsProj currentState actionAt rewardAt; fun_prop)
  letI : IsMarkovKernel (freshKernel (T := T) (k := k) hn hm eta) :=
    freshKernel_markov hn hm eta heta
  letI : IsProbabilityMeasure (freshLabelLaw Mp hn hm eta) := by
    unfold freshLabelLaw
    infer_instance
  letI : IsProbabilityMeasure (freshLabelLaw Mm hn hm eta) := by
    unfold freshLabelLaw
    infer_instance
  have hforward := Causalean.Stat.tvDist_bind_le
    (obsLaw Mp) (obsLaw Mm) (freshKernel hn hm eta)
  have hbackward := tvDist_map_le_audited
    (freshLabelLaw Mp hn hm eta) (freshLabelLaw Mm hn hm eta)
  rw [freshLabelLaw_projection Mp hn hm eta heta,
    freshLabelLaw_projection Mm hn hm eta heta] at hbackward
  exact le_antisymm (by simpa [freshLabelLaw] using hforward) hbackward

-- @node: auditRank_strictMono_on_true
private lemma auditRank_strictMono_on_true {T : Nat} (mask : AuditMask T)
    {t u : Fin T} (htu : t < u) (ht : mask t = true) :
    auditRank mask t < auditRank mask u := by
  unfold auditRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨lt_trans hj.1 htu, hj.2⟩
  · intro heq
    have hmemu : t ∈ Finset.univ.filter (fun j : Fin T => j.val < u.val ∧ mask j) := by
      simp [htu, ht]
    have hmemt : t ∈ Finset.univ.filter (fun j : Fin T => j.val < t.val ∧ mask j) :=
      heq.symm ▸ hmemu
    simp at hmemt

-- @node: auditRank_injective_on_true
private lemma auditRank_injective_on_true {T : Nat} (mask : AuditMask T) :
    Function.Injective (fun t : {t : Fin T // mask t = true} => auditRank mask t) := by
  intro t u h
  apply Subtype.ext
  rcases lt_trichotomy t.1 u.1 with hlt | heq | hgt
  · exact False.elim (Nat.ne_of_lt (auditRank_strictMono_on_true mask hlt t.2) h)
  · exact heq
  · exact False.elim (Nat.ne_of_gt (auditRank_strictMono_on_true mask hgt u.2) h)

-- @node: auditRank_lt_card_true
private lemma auditRank_lt_card_true {T : Nat} (mask : AuditMask T)
    (t : Fin T) (ht : mask t = true) :
    auditRank mask t < (Finset.univ.filter fun j : Fin T => mask j).card := by
  unfold auditRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hj.2
  · intro heq
    have hmem : t ∈ Finset.univ.filter (fun j : Fin T => mask j) := by simp [ht]
    have : t ∈ Finset.univ.filter (fun j : Fin T => j.val < t.val ∧ mask j) :=
      heq ▸ hmem
    simp at this

-- @node: auditedStateFin
private def auditedStateFin {T n k m : Nat}
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m)
    (t : Fin T) : Fin (n * m) :=
  finProdFinEquiv ((currentState w t).2, coords t.castSucc)

-- @node: relabelingToPermutation
private def relabelingToPermutation {n m : Nat} (rho : Equiv.Perm (Fin (n * m))) :
    (Fin n × Fin m ≃ Fin (n * m)) ≃ Equiv.Perm (Fin (n * m)) where
  toFun pi := rho.trans (finProdFinEquiv.symm.trans pi)
  invFun sigma := finProdFinEquiv.trans (rho.symm.trans sigma)
  left_inv pi := by ext x; simp
  right_inv sigma := by
    ext x
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

-- @node: uniformRelabeling_map_relabelingToPermutation
private lemma uniformRelabeling_map_relabelingToPermutation {n m : Nat}
    (rho : Equiv.Perm (Fin (n * m))) :
    (uniformRelabeling n m).map (relabelingToPermutation rho) =
      uniformPermutation (n * m) := by
  classical
  ext s hs
  simp only [uniformRelabeling, uniformPermutation, Measure.map_apply
    (Measurable.of_discrete : Measurable (relabelingToPermutation rho)) hs,
    Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply']
  rw [Fintype.card_congr (relabelingToPermutation rho)]
  simp only [Measure.smul_apply, smul_eq_mul]
  simp_rw [MeasureTheory.Measure.dirac_apply]
  simpa [Set.indicator, Set.mem_preimage] using
    (relabelingToPermutation rho).sum_comp
      (fun sigma => ENNReal.ofReal
        (1 / (Fintype.card (Equiv.Perm (Fin (n * m))) : ℝ)) * s.indicator 1 sigma)

-- @node: PrelabelCollision
private def PrelabelCollision {T n k m : Nat} (mask : AuditMask T)
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m) : Prop :=
  ∃ (t u : Fin T), t ≠ u ∧ mask t = true ∧ mask u = true ∧
    ((currentState w t).2, coords t.castSucc) =
      ((currentState w u).2, coords u.castSucc)

-- @node: prelabelCollision_iff_cloneCollision
private lemma prelabelCollision_iff_cloneCollision {T n k m : Nat}
    (pi : Fin n × Fin m ≃ Fin (n * m)) (mask : AuditMask T)
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m) :
    PrelabelCollision mask w coords ↔ CloneCollision mask (clonePath pi w coords) := by
  constructor
  · rintro ⟨t, u, htu, ht, hu, heq⟩
    refine ⟨t, u, htu, ht, hu, ?_⟩
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact congrArg pi heq
  · rintro ⟨t, u, htu, ht, hu, heq⟩
    refine ⟨t, u, htu, ht, hu, ?_⟩
    exact pi.injective (congrArg Prod.snd heq)

-- @node: auditedStateFin_injective_of_noPrelabelCollision
private lemma auditedStateFin_injective_of_noPrelabelCollision {T n k m : Nat}
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m)
    (mask : AuditMask T) (hcol : ¬ PrelabelCollision mask w coords) :
    Function.Injective (fun t : {t : Fin T // mask t = true} =>
      auditedStateFin w coords t.1) := by
  intro t u heq
  apply Subtype.ext
  by_contra htu
  apply hcol
  exact ⟨t.1, u.1, htu, t.2, u.2, finProdFinEquiv.injective heq⟩

-- @node: auditRank_lt_mul_of_noPrelabelCollision
private lemma auditRank_lt_mul_of_noPrelabelCollision {T n k m : Nat}
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m)
    (mask : AuditMask T) (hcol : ¬ PrelabelCollision mask w coords)
    (t : Fin T) (ht : mask t = true) : auditRank mask t < n * m := by
  let A := {t : Fin T // mask t = true}
  have hinj : Function.Injective (fun t : A => auditedStateFin w coords t.1) :=
    auditedStateFin_injective_of_noPrelabelCollision w coords mask hcol
  have hcard : Fintype.card A ≤ n * m := by
    simpa using Fintype.card_le_of_injective _ hinj
  have hrank := auditRank_lt_card_true mask t ht
  have hcardA : Fintype.card A = (Finset.univ.filter fun j : Fin T => mask j).card := by
    apply Fintype.card_of_subtype
    simp
  rw [← hcardA] at hrank
  exact lt_of_lt_of_le hrank hcard

-- @node: auditedRankFin
private def auditedRankFin {T n k m : Nat}
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m)
    (mask : AuditMask T) (hcol : ¬ PrelabelCollision mask w coords)
    (t : {t : Fin T // mask t = true}) : Fin (n * m) :=
  ⟨auditRank mask t.1,
    auditRank_lt_mul_of_noPrelabelCollision w coords mask hcol t.1 t.2⟩

-- @node: rankStatePermutation
private noncomputable def rankStatePermutation {T n k m : Nat}
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m)
    (mask : AuditMask T) (hcol : ¬ PrelabelCollision mask w coords) :
    Equiv.Perm (Fin (n * m)) :=
  Classical.choose (Equiv.Perm.exists_extending_pair
    (auditedRankFin w coords mask hcol)
    (fun t : {t : Fin T // mask t = true} => auditedStateFin w coords t.1)
    (fun _ _ h => auditRank_injective_on_true mask (congrArg Fin.val h))
    (auditedStateFin_injective_of_noPrelabelCollision w coords mask hcol))

-- @node: rankStatePermutation_apply
private lemma rankStatePermutation_apply {T n k m : Nat}
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m)
    (mask : AuditMask T) (hcol : ¬ PrelabelCollision mask w coords)
    (t : Fin T) (ht : mask t = true) :
    rankStatePermutation w coords mask hcol
      ⟨auditRank mask t,
        auditRank_lt_mul_of_noPrelabelCollision w coords mask hcol t ht⟩ =
      auditedStateFin w coords t := by
  change rankStatePermutation w coords mask hcol
      (auditedRankFin w coords mask hcol ⟨t, ht⟩) = auditedStateFin w coords t
  exact Classical.choose_spec (Equiv.Perm.exists_extending_pair
    (auditedRankFin w coords mask hcol)
    (fun t : {t : Fin T // mask t = true} => auditedStateFin w coords t.1)
    (fun _ _ h => auditRank_injective_on_true mask (congrArg Fin.val h))
    (auditedStateFin_injective_of_noPrelabelCollision w coords mask hcol)) ⟨t, ht⟩

-- @node: sampleRankPermutation
private noncomputable def sampleRankPermutation {T n k m : Nat}
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m)
    (mask : AuditMask T) : Equiv.Perm (Fin (n * m)) := by
  classical
  exact if hcol : PrelabelCollision mask w coords then Equiv.refl _
    else rankStatePermutation w coords mask hcol

-- @node: sampleRankPermutation_apply_of_noCollision
private lemma sampleRankPermutation_apply_of_noCollision {T n k m : Nat}
    (pi : Fin n × Fin m ≃ Fin (n * m))
    (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m)
    (mask : AuditMask T) (hcol : ¬ CloneCollision mask (clonePath pi w coords))
    (t : Fin T) (ht : mask t = true) :
    sampleRankPermutation w coords mask
      ⟨auditRank mask t, auditRank_lt_mul_of_noPrelabelCollision w coords mask
        ((prelabelCollision_iff_cloneCollision pi mask w coords).not.mpr hcol) t ht⟩ =
      auditedStateFin w coords t := by
  have hpre := (prelabelCollision_iff_cloneCollision pi mask w coords).not.mpr hcol
  rw [sampleRankPermutation, dif_neg hpre]
  exact rankStatePermutation_apply w coords mask hpre t ht

-- @node: coupledFreshRecord
private noncomputable def coupledFreshRecord {T n k m : Nat}
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (q : (FullPath T 1 n k × (Fin (T + 1) → Fin m)) ×
      ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T)) :
    AuditedRecord T 1 (n * m) k :=
  freshRecord hn hm (obsProj q.1.1) q.2.2
    (relabelingToPermutation (sampleRankPermutation q.1.1 q.1.2 q.2.2) q.2.1)

-- @node: coupledFreshRecord_eq_fixed_of_noCollision
private lemma coupledFreshRecord_eq_fixed_of_noCollision {T n k m : Nat}
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (q : (FullPath T 1 n k × (Fin (T + 1) → Fin m)) ×
      ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T))
    (hcol : ¬ CloneCollision q.2.2 (clonePath q.2.1 q.1.1 q.1.2)) :
    fixedPermutationRecord q = coupledFreshRecord hn hm q := by
  funext t
  by_cases ht : q.2.2 t = true
  · have hpre :=
      (prelabelCollision_iff_cloneCollision q.2.1 q.2.2 q.1.1 q.1.2).not.mpr hcol
    have hrank := auditRank_lt_mul_of_noPrelabelCollision q.1.1 q.1.2 q.2.2 hpre t ht
    have hrho : sampleRankPermutation q.1.1 q.1.2 q.2.2
        ⟨auditRank q.2.2 t, hrank⟩ = auditedStateFin q.1.1 q.1.2 t := by
      convert sampleRankPermutation_apply_of_noCollision
        q.2.1 q.1.1 q.1.2 q.2.2 hcol t ht using 1
    have hlabel :
        relabelingToPermutation (sampleRankPermutation q.1.1 q.1.2 q.2.2) q.2.1
          ⟨auditRank q.2.2 t, hrank⟩ =
        q.2.1 ((currentState q.1.1 t).2, q.1.2 t.castSucc) := by
      change q.2.1 (finProdFinEquiv.symm
        (sampleRankPermutation q.1.1 q.1.2 q.2.2 ⟨auditRank q.2.2 t, hrank⟩)) = _
      rw [hrho]
      simp [auditedStateFin]
    simp [fixedPermutationRecord, coupledFreshRecord, freshRecord, auditRecord,
      ht, hrank, hlabel, clonePath, obsProj, currentState, actionAt, rewardAt]
    exact Subsingleton.elim _ _
  · have htf : q.2.2 t = false := Bool.eq_false_of_not_eq_true ht
    simp [fixedPermutationRecord, coupledFreshRecord, freshRecord, auditRecord,
      htf, clonePath, obsProj, currentState, actionAt, rewardAt]

-- @node: coupledFreshRecord_measurable
private lemma coupledFreshRecord_measurable {T n k m : Nat}
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Measurable (coupledFreshRecord (T := T) (k := k) hn hm) := by
  unfold coupledFreshRecord freshRecord obsProj currentState actionAt rewardAt
  apply measurable_pi_lambda
  intro t
  apply Measurable.prodMk
  · fun_prop
  apply Measurable.prodMk
  · fun_prop
  apply Measurable.prodMk
  · fun_prop
  apply Measurable.prodMk
  · fun_prop
  let d := fun q : (FullPath T 1 n k × (Fin (T + 1) → Fin m)) ×
      ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T) =>
    (((fun u : Fin (T + 1) => (q.1.1.1 u).2), q.1.2),
      ((fun u : Fin T => (q.1.1.2 u).1), q.2))
  have hd : Measurable d := by
    dsimp [d]
    fun_prop
  exact (Measurable.of_discrete : Measurable (fun z :
      ((Fin (T + 1) → Fin n) × (Fin (T + 1) → Fin m)) ×
        ((Fin T → Fin k) × ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T)) =>
      let w : FullPath T 1 n k :=
        (fun u => (0, z.1.1 u), fun u => (z.2.1 u, 0))
      let label : Fin (n * m) :=
        if h : auditRank z.2.2.2 t < n * m then
          relabelingToPermutation (sampleRankPermutation w z.1.2 z.2.2.2) z.2.2.1
            ⟨auditRank z.2.2.2 t, h⟩
        else relabelingToPermutation (sampleRankPermutation w z.1.2 z.2.2.2) z.2.2.1
          ⟨0, Nat.mul_pos hn hm⟩
      if z.2.2.2 t then some ((⟨0, by decide⟩ : Fin 1), label) else none)).comp hd

-- @node: fixedPermutationRecord_measurable
private lemma fixedPermutationRecord_measurable {T n k m : Nat} :
    Measurable (fixedPermutationRecord :
      ((FullPath T 1 n k × (Fin (T + 1) → Fin m)) ×
        ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T)) →
          AuditedRecord T 1 (n * m) k) := by
  unfold fixedPermutationRecord auditRecord clonePath currentState actionAt rewardAt
  apply measurable_pi_lambda
  intro t
  apply Measurable.prodMk
  · fun_prop
  apply Measurable.prodMk
  · fun_prop
  apply Measurable.prodMk
  · fun_prop
  apply Measurable.prodMk
  · fun_prop
  apply Measurable.ite
  · exact (((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd))
      (measurableSet_singleton true) : MeasurableSet
        ((fun q : (FullPath T 1 n k × (Fin (T + 1) → Fin m)) ×
          ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T) => q.2.2 t) ⁻¹' {true}))
  · fun_prop
  · fun_prop

-- @node: uniformRelabeling_prob
private lemma uniformRelabeling_prob (n m : Nat) :
    IsProbabilityMeasure (uniformRelabeling n m) := by
  letI : Nonempty (Fin n × Fin m ≃ Fin (n * m)) := ⟨finProdFinEquiv⟩
  constructor
  simp [uniformRelabeling]
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast
    (Fintype.card_pos : 0 < Fintype.card (Fin n × Fin m ≃ Fin (n * m)))),
    ENNReal.ofReal_natCast]
  exact ENNReal.mul_inv_cancel
    (by exact_mod_cast (Nat.ne_of_gt
      (Fintype.card_pos : 0 < Fintype.card (Fin n × Fin m ≃ Fin (n * m))))) (by simp)

-- @node: fixedPermutationCoupling_prob
private lemma fixedPermutationCoupling_prob {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hm : 1 ≤ m) (eta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (fixedPermutationCoupling (m := m) M eta) := by
  letI : IsProbabilityMeasure (uniformFin m) := uniformFin_prob m hm
  letI : IsProbabilityMeasure (uniformRelabeling n m) := uniformRelabeling_prob n m
  letI : IsProbabilityMeasure (auditMaskLaw T eta) := auditMaskLaw_prob T eta heta
  unfold fixedPermutationCoupling
  infer_instance

-- @node: fixedPermutationCoupling_map_coupledFreshRecord
private lemma fixedPermutationCoupling_map_coupledFreshRecord {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    (fixedPermutationCoupling (m := m) M eta).map (coupledFreshRecord hn hm) =
      freshLabelLaw M hn hm eta := by
  letI : IsProbabilityMeasure (uniformFin m) := uniformFin_prob m hm
  letI : IsProbabilityMeasure (auditMaskLaw T eta) := auditMaskLaw_prob T eta heta
  letI : IsProbabilityMeasure (uniformRelabeling n m) := uniformRelabeling_prob n m
  ext s hs
  rw [Measure.map_apply (coupledFreshRecord_measurable hn hm) hs]
  unfold fixedPermutationCoupling freshLabelLaw obsLaw
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  rw [Measure.prod_apply ((coupledFreshRecord_measurable hn hm) hs)]
  rw [lintegral_map (Kernel.measurable_coe _ hs)
    (by unfold obsProj currentState actionAt rewardAt; fun_prop)]
  have hinner (w : FullPath T 1 n k) (coords : Fin (T + 1) → Fin m) :
      ((uniformRelabeling n m).prod (auditMaskLaw T eta))
          (Prod.mk (w, coords) ⁻¹' coupledFreshRecord hn hm ⁻¹' s) =
        (freshKernel hn hm eta (obsProj w)) s := by
    have hset : MeasurableSet
        (Prod.mk (w, coords) ⁻¹' coupledFreshRecord hn hm ⁻¹' s) :=
      (coupledFreshRecord_measurable hn hm hs).preimage measurable_prodMk_left
    rw [Measure.prod_apply_symm hset]
    change _ = (((auditMaskLaw T eta).prod (uniformPermutation (n * m))).map
      (fun q => freshRecord hn hm (obsProj w) q.1 q.2)) s
    rw [Measure.map_apply (by fun_prop) hs,
      Measure.prod_apply ((by fun_prop : Measurable
        (fun q => freshRecord hn hm (obsProj w) q.1 q.2)) hs)]
    apply lintegral_congr
    intro mask
    rw [← uniformRelabeling_map_relabelingToPermutation
      (sampleRankPermutation w coords mask)]
    change _ = (Measure.map
      (relabelingToPermutation (sampleRankPermutation w coords mask))
      (uniformRelabeling n m))
        ((fun sigma => freshRecord hn hm (obsProj w) mask sigma) ⁻¹' s)
    rw [Measure.map_apply (Measurable.of_discrete : Measurable
      (relabelingToPermutation (sampleRankPermutation w coords mask)))
        ((by fun_prop : Measurable
          (fun sigma => freshRecord hn hm (obsProj w) mask sigma)) hs)]
    rfl
  simp_rw [hinner]
  let f : FullPath T 1 n k → ENNReal := fun w => (freshKernel hn hm eta (obsProj w)) s
  have hf : AEMeasurable f M.law :=
    (Kernel.measurable_coe (freshKernel hn hm eta) hs).comp_aemeasurable
      (by unfold obsProj currentState actionAt rewardAt; fun_prop)
  have hone : AEMeasurable (fun _ : Fin (T + 1) → Fin m => (1 : ENNReal))
      (Measure.pi fun _ : Fin (T + 1) => uniformFin m) := by fun_prop
  simpa [f] using (lintegral_prod_mul hf hone)

-- @node: tvDist_le_coupling_disagreement
private lemma tvDist_le_coupling_disagreement
    {X Omega : Type*} [MeasurableSpace X] [MeasurableEq X] [MeasurableSpace Omega]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (gamma : Measure Omega) [IsProbabilityMeasure gamma]
    (f g : Omega → X) (hf : Measurable f) (hg : Measurable g)
    (hfst : gamma.map f = mu) (hsnd : gamma.map g = nu) :
    Causalean.Stat.tvDist mu nu ≤ gamma.real {z | f z ≠ g z} := by
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  let S : Set Omega := f ⁻¹' A
  let U : Set Omega := g ⁻¹' A
  have hS : MeasurableSet S := hA.preimage hf
  have hU : MeasurableSet U := hA.preimage hg
  have hmu : mu.real A = gamma.real S := by
    rw [← hfst, map_measureReal_apply hf hA]
  have hnu : nu.real A = gamma.real U := by
    rw [← hsnd, map_measureReal_apply hg hA]
  rw [hmu, hnu]
  refine (abs_measureReal_sub_le_measureReal_symmDiff hS.nullMeasurableSet
    hU.nullMeasurableSet).trans ?_
  apply measureReal_mono
  · intro z hz
    simp only [Set.mem_symmDiff, Set.mem_preimage, S, U] at hz
    change f z ≠ g z
    rintro hfg
    rcases hz with ⟨hfA, hgA⟩ | ⟨hgA, hfA⟩
    · exact hgA (hfg ▸ hfA)
    · exact hfA (hfg.symm ▸ hgA)
  · exact measure_ne_top gamma _

-- @node: permutationMixture_tv_fresh_le_collision
private lemma permutationMixture_tv_fresh_le_collision {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1)
    (hleft : (fixedPermutationCoupling (m := m) M eta).map fixedPermutationRecord =
      permutationMixture M hm eta) :
    Causalean.Stat.tvDist (permutationMixture M hm eta) (freshLabelLaw M hn hm eta) ≤
      ((fixedPermutationCoupling (m := m) M eta)
        {q | CloneCollision q.2.2 (clonePath q.2.1 q.1.1 q.1.2)}).toReal := by
  letI : IsProbabilityMeasure (permutationMixture M hm eta) :=
    permutationMixture_prob M hm eta heta
  letI : IsProbabilityMeasure (freshLabelLaw M hn hm eta) := by
    rw [← fixedPermutationCoupling_map_coupledFreshRecord M hn hm eta heta]
    letI : IsProbabilityMeasure (fixedPermutationCoupling (m := m) M eta) :=
      fixedPermutationCoupling_prob M hm eta heta
    exact Measure.isProbabilityMeasure_map (coupledFreshRecord_measurable hn hm).aemeasurable
  letI : IsProbabilityMeasure (fixedPermutationCoupling (m := m) M eta) :=
    fixedPermutationCoupling_prob M hm eta heta
  have htv := tvDist_le_coupling_disagreement
    (permutationMixture M hm eta) (freshLabelLaw M hn hm eta)
    (fixedPermutationCoupling (m := m) M eta)
    fixedPermutationRecord (coupledFreshRecord hn hm)
    fixedPermutationRecord_measurable
    (coupledFreshRecord_measurable hn hm) hleft
    (fixedPermutationCoupling_map_coupledFreshRecord M hn hm eta heta)
  refine htv.trans ?_
  apply ENNReal.toReal_mono
  · exact measure_ne_top _ _
  apply measure_mono
  intro q hne
  by_contra hcol
  exact hne (coupledFreshRecord_eq_fixed_of_noCollision hn hm q hcol)

-- @node: lem:overflow-safe-fixed-permutation-tv
/-- For every positive base size and clone multiplicity, the fixed-permutation mixture
is within the audited clone-collision probability of the fresh-label law, with no
cardinality feasibility floor. The fresh law is a sign-independent kernel extension
of the observed path and projects back to it. -/
lemma overflow_safe_fixed_permutation_tv {T n k m : Nat}
    (M : PomdpModel T 1 n k) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hK : FullFiltrationPomdp M) (hA : FullFiltrationRandomization M)
    (hStart : StationaryStart M)
    (eta : ℝ) (hAudit : BernoulliAudits eta M (auditJointLaw eta M))
    (hLabels : AtomicAuditLabels (auditRecord (T := T) (nX := 1) (nH := n) (k := k))) :
    M.law = generatedPathLaw M ∧
    (fixedPermutationCoupling (m := m) M eta).map fixedPermutationRecord =
      permutationMixture M hm eta ∧
    Causalean.Stat.tvDist (permutationMixture M hm eta) (freshLabelLaw M hn hm eta) ≤
      ((fixedPermutationCoupling (m := m) M eta)
        {q | CloneCollision q.2.2 (clonePath q.2.1 q.1.1 q.1.2)}).toReal ∧
    ((fixedPermutationCoupling (m := m) M eta)
      {q | CloneCollision q.2.2 (clonePath q.2.1 q.1.1 q.1.2)}).toReal ≤
        collisionEnvelope T eta m ∧
    collisionEnvelope T eta m ≤ eta ^ 2 * T * (T - 1) / (2 * m : ℝ) ∧
    Causalean.Stat.tvDist (permutationMixture M hm eta) (freshLabelLaw M hn hm eta) ≤
      collisionEnvelope T eta m ∧
    (∃ Γ : Kernel (ObsPath T 1 k) (AuditedRecord T 1 (n * m) k),
      ∀ M' : PomdpModel T 1 n k,
        freshLabelLaw M' hn hm eta = (obsLaw M').bind Γ) ∧
    (freshLabelLaw M hn hm eta).map auditedProjection = obsLaw M := by
  have hpath : M.law = generatedPathLaw M := by
    have hLaw := full_history_generated_law M hK hA hStart
    have hGenerated : GeneratedPathLaw M (generatedPathLaw M) := by
      exact Classical.epsilon_spec
        (show ∃ μ, GeneratedPathLaw M μ from ⟨M.law, hLaw⟩)
    exact generated_path_law_unique M hLaw hGenerated
  have hmixture : (fixedPermutationCoupling (m := m) M eta).map
      fixedPermutationRecord = permutationMixture M hm eta := by
    classical
    unfold fixedPermutationCoupling uniformRelabeling
    rw [← Measure.sum_fintype, Measure.prod_sum_left, Measure.prod_sum_right]
    rw [Measure.map_sum fixedPermutationRecord_measurable.aemeasurable,
      Measure.sum_fintype]
    apply Finset.sum_congr rfl
    intro π _
    rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul]
    congr 1
    rw [Measure.dirac_prod]
    unfold auditedLaw auditJointLaw cloneModel clonePathLaw
    letI : IsProbabilityMeasure (uniformFin m) := uniformFin_prob m hm
    letI : IsProbabilityMeasure (auditMaskLaw T eta) := auditMaskLaw_prob T eta hAudit.1
    rw [show (M.law.prod (Measure.pi fun _ : Fin (T + 1) => uniformFin m)).prod
        (Measure.map (Prod.mk π) (auditMaskLaw T eta)) =
        Measure.map (Prod.map id (Prod.mk π))
          ((M.law.prod (Measure.pi fun _ : Fin (T + 1) => uniformFin m)).prod
            (auditMaskLaw T eta)) from by
          simpa using (Measure.map_prod_map
            (M.law.prod (Measure.pi fun _ : Fin (T + 1) => uniformFin m))
            (auditMaskLaw T eta) measurable_id
            (show Measurable (Prod.mk π : AuditMask T → _ × AuditMask T) by fun_prop))]
    rw [Measure.map_map fixedPermutationRecord_measurable (by fun_prop)]
    change Measure.map (fixedPermutationRecord ∘ Prod.map id (Prod.mk π))
        ((M.law.prod (Measure.pi fun _ : Fin (T + 1) => uniformFin m)).prod
          (auditMaskLaw T eta)) =
      Measure.map (fun q => auditRecord q.1 q.2)
        ((clonePathLaw M π).prod (auditMaskLaw T eta))
    rw [clonePathLaw]
    have hcloneMeas : Measurable
        (fun q : FullPath T 1 n k × (Fin (T + 1) → Fin m) => clonePath π q.1 q.2) := by
      unfold clonePath
      fun_prop
    have hprod2 :
        (Measure.map (fun q => clonePath π q.1 q.2)
          (M.law.prod (Measure.pi fun _ : Fin (T + 1) => uniformFin m))).prod
            (auditMaskLaw T eta) =
        Measure.map (Prod.map (fun q => clonePath π q.1 q.2) id)
          ((M.law.prod (Measure.pi fun _ : Fin (T + 1) => uniformFin m)).prod
            (auditMaskLaw T eta)) := by
      simpa using (Measure.map_prod_map
        (M.law.prod (Measure.pi fun _ : Fin (T + 1) => uniformFin m))
        (auditMaskLaw T eta) hcloneMeas measurable_id)
    have hrecord : Measurable (fun q : FullPath T 1 (n * m) k × AuditMask T =>
        auditRecord q.1 q.2) := by
      unfold auditRecord currentState actionAt rewardAt
      apply measurable_pi_lambda
      intro t
      apply Measurable.prodMk
      · fun_prop
      apply Measurable.prodMk
      · fun_prop
      apply Measurable.prodMk
      · fun_prop
      apply Measurable.prodMk
      · fun_prop
      apply Measurable.ite
      · exact (((measurable_pi_apply t).comp measurable_snd)
          (measurableSet_singleton true) :
            MeasurableSet ((fun q : FullPath T 1 (n * m) k × AuditMask T =>
              q.2 t) ⁻¹' {true}))
      · fun_prop
      · fun_prop
    rw [hprod2, Measure.map_map hrecord (by fun_prop)]
    congr 1
  have htv : Causalean.Stat.tvDist (permutationMixture M hm eta)
      (freshLabelLaw M hn hm eta) ≤
      ((fixedPermutationCoupling (m := m) M eta)
        {q | CloneCollision q.2.2 (clonePath q.2.1 q.1.1 q.1.2)}).toReal := by
    exact permutationMixture_tv_fresh_le_collision M hn hm eta hAudit.1 hmixture
  have hcol : ((fixedPermutationCoupling (m := m) M eta)
      {q | CloneCollision q.2.2 (clonePath q.2.1 q.1.1 q.1.2)}).toReal ≤
      collisionEnvelope T eta m := by
    classical
    let E : Set ((FullPath T 1 n k × (Fin (T + 1) → Fin m)) ×
        ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T)) :=
      {q | CloneCollision q.2.2 (clonePath q.2.1 q.1.1 q.1.2)}
    let C : Set ((Fin (T + 1) → Fin m) × AuditMask T) :=
      {q | ¬Function.Injective
        (fun t : auditedIndex q.2 => q.1 t.1.castSucc)}
    have hsubset : E ⊆ (fun q => (q.1.2, q.2.2)) ⁻¹' C := by
      intro q hq hinj
      rcases cloneCollision_implies_coordinateCollision q.2.1 q.1.1 q.1.2 q.2.2 hq with
        ⟨t, u, htu, ht, hu, hcoords⟩
      let ti : auditedIndex q.2.2 := ⟨t, ht⟩
      let ui : auditedIndex q.2.2 := ⟨u, hu⟩
      have heq : ti = ui := hinj hcoords
      exact htu (congrArg Subtype.val heq)
    have hC : MeasurableSet C := MeasurableSet.of_discrete
    have hproj : Measurable (fun q :
        (FullPath T 1 n k × (Fin (T + 1) → Fin m)) ×
          ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T) =>
        (q.1.2, q.2.2)) := by fun_prop
    have hmono : (fixedPermutationCoupling (m := m) M eta) E ≤
        ((Measure.pi fun _ : Fin (T + 1) => uniformFin m).prod
          (auditMaskLaw T eta)) C := by
      calc
        (fixedPermutationCoupling (m := m) M eta) E ≤
            (fixedPermutationCoupling (m := m) M eta)
              ((fun q => (q.1.2, q.2.2)) ⁻¹' C) := measure_mono hsubset
        _ = ((fixedPermutationCoupling (m := m) M eta).map
              (fun q => (q.1.2, q.2.2))) C :=
          (Measure.map_apply hproj hC).symm
        _ = _ := by rw [fixedPermutationCoupling_coordinateMask M hm eta hAudit.1]
    change ((fixedPermutationCoupling (m := m) M eta) E).toReal ≤ _
    letI : IsProbabilityMeasure (uniformFin m) := uniformFin_prob m hm
    letI : IsProbabilityMeasure (auditMaskLaw T eta) := auditMaskLaw_prob T eta hAudit.1
    calc
      ((fixedPermutationCoupling (m := m) M eta) E).toReal ≤
          (((Measure.pi fun _ : Fin (T + 1) => uniformFin m).prod
            (auditMaskLaw T eta)) C).toReal := by
        exact ENNReal.toReal_mono (measure_ne_top _ _) hmono
      _ = collisionEnvelope T eta m := by
        exact coordinateMaskCollision_real hm eta hAudit.1
  have henv : collisionEnvelope T eta m ≤
      eta ^ 2 * T * (T - 1) / (2 * m : ℝ) := by
    exact collisionEnvelope_pair_bound T m hm eta hAudit.1
  refine ⟨hpath, hmixture, htv, hcol, henv, le_trans htv hcol, ?_, ?_⟩
  · refine ⟨freshKernel hn hm eta, ?_⟩
    intro M'
    rfl
  · exact freshLabelLaw_projection M hn hm eta hAudit.1

end CausalSmith.Stat.PomdpStateauditMinimax

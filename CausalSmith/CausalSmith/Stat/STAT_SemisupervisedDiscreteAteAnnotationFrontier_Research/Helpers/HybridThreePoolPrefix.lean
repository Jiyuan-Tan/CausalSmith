module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.PoissonHybridRisk
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.IndependentOuterBlocks
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.IndependentPoissonHistogram
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.ProductPools.ThreePool

/-! The paper's fixed blocks and finite-prefix statistic in the generic three-pool format. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory Causalean.Stat
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily

/-- Forget the dependent-function presentation of three coordinates.  [the stated conditions](hyp:z) [the stated conclusion](goal). -/
def unpackThreePool {X : ThreePoolIndex → Type*}
    (z : (i : ThreePoolIndex) → X i) :
    X .complete × (X .sharedLeft × X .sharedRight) :=
  (z .complete, z .sharedLeft, z .sharedRight)

/-- [Converting a dependent three-pool family to a nested product is measurable](goal). -/
@[fun_prop] lemma measurable_unpackThreePool
    {X : ThreePoolIndex → Type*} [∀ i, MeasurableSpace (X i)] :
    Measurable (unpackThreePool (X := X)) := by
  exact (measurable_pi_apply ThreePoolIndex.complete).prodMk
    ((measurable_pi_apply ThreePoolIndex.sharedLeft).prodMk
      (measurable_pi_apply ThreePoolIndex.sharedRight))

/-- A three-coordinate product measure becomes a nested ordinary product.  [the stated conclusion](goal). -/
lemma map_unpackThreePool_pi
    {X : ThreePoolIndex → Type*} [∀ i, MeasurableSpace (X i)]
    (mu : (i : ThreePoolIndex) → Measure (X i))
    [∀ i, IsProbabilityMeasure (mu i)] :
    Measure.map unpackThreePool (Measure.pi mu) =
      (mu .complete).prod ((mu .sharedLeft).prod (mu .sharedRight)) := by
  let J := Unit ⊕ (Unit ⊕ Unit)
  let e : J ≃ ThreePoolIndex :=
    { toFun := fun j => match j with
        | .inl _ => .complete
        | .inr (.inl _) => .sharedLeft
        | .inr (.inr _) => .sharedRight
      invFun := fun i => match i with
        | .complete => .inl ()
        | .sharedLeft => .inr (.inl ())
        | .sharedRight => .inr (.inr ())
      left_inv := by intro j; rcases j with _ | (_ | _) <;> rfl
      right_inv := by intro i; cases i <;> rfl }
  let reindex := MeasurableEquiv.piCongrLeft X e
  let split0 := MeasurableEquiv.sumPiEquivProdPi (fun j : J => X (e j))
  let split1 := MeasurableEquiv.sumPiEquivProdPi
    (fun j : Unit ⊕ Unit => X (e (.inr j)))
  let one0 := MeasurableEquiv.piUnique (fun _ : Unit => X .complete)
  let one1 := MeasurableEquiv.piUnique (fun _ : Unit => X .sharedLeft)
  let one2 := MeasurableEquiv.piUnique (fun _ : Unit => X .sharedRight)
  let finish := MeasurableEquiv.prodCongr one0
    (MeasurableEquiv.prodCongr one1 one2)
  let total := reindex.symm.trans <| split0.trans <|
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      split1).trans finish
  have htotal : MeasurePreserving total (Measure.pi mu)
      ((mu .complete).prod ((mu .sharedLeft).prod (mu .sharedRight))) := by
    have hr := (measurePreserving_piCongrLeft mu e).symm
    have hs0 := measurePreserving_sumPiEquivProdPi (fun j : J => mu (e j))
    have hs1 := measurePreserving_sumPiEquivProdPi
      (fun j : Unit ⊕ Unit => mu (e (.inr j)))
    have hu0 := measurePreserving_piUnique (fun _ : Unit => mu .complete)
    have hu1 := measurePreserving_piUnique (fun _ : Unit => mu .sharedLeft)
    have hu2 := measurePreserving_piUnique (fun _ : Unit => mu .sharedRight)
    exact (hu0.prod (hu1.prod hu2)).comp
      (((MeasurePreserving.id _).prod hs1).comp (hs0.comp hr))
  have hfun : (total : ((i : ThreePoolIndex) → X i) → _) =
      unpackThreePool := by
    funext z
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> rfl
  rw [← hfun]
  exact htotal.map_eq

/-- Split an array into three consecutive blocks.  [the stated conditions](hyp:a,b,c,z) [the stated conclusion](goal). -/
def splitThreeBlocks {X : Type*} (a b c : Nat)
    (z : Fin (a + (b + c)) → X) :
    (Fin a → X) × ((Fin b → X) × (Fin c → X)) :=
  let e : Fin a ⊕ (Fin b ⊕ Fin c) ≃ Fin (a + (b + c)) :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
  (fun i ↦ z (e (.inl i)),
    fun i ↦ z (e (.inr (.inl i))),
    fun i ↦ z (e (.inr (.inr i))))

/-- For lengths [a, b, and c](hyp:a,b,c), the first block of [an array](hyp:z) at [an index](hyp:i) [is its entry at that index](goal). -/
@[simp] lemma splitThreeBlocks_fst_apply {X : Type*} (a b c : Nat)
    (z : Fin (a + (b + c)) → X) (i : Fin a) :
    (splitThreeBlocks a b c z).1 i = z ⟨i.1, by omega⟩ := by
  rfl

/-- For lengths [a, b, and c](hyp:a,b,c), the middle block of [an array](hyp:z) at [an index](hyp:i) [is its entry offset by the first block length](goal). -/
@[simp] lemma splitThreeBlocks_mid_apply {X : Type*} (a b c : Nat)
    (z : Fin (a + (b + c)) → X) (i : Fin b) :
    (splitThreeBlocks a b c z).2.1 i = z ⟨a + i.1, by omega⟩ := by
  rfl

/-- For lengths [a, b, and c](hyp:a,b,c), the last block of [an array](hyp:z) at [an index](hyp:i) [is its entry offset by the first two block lengths](goal). -/
@[simp] lemma splitThreeBlocks_last_apply {X : Type*} (a b c : Nat)
    (z : Fin (a + (b + c)) → X) (i : Fin c) :
    (splitThreeBlocks a b c z).2.2 i = z ⟨a + b + i.1, by omega⟩ := by
  change z (((Equiv.sumCongr (Equiv.refl (Fin a)) finSumFinEquiv).trans
    finSumFinEquiv) (.inr (.inr i))) = _
  apply congrArg z
  apply Fin.ext
  simp
  omega

/-- Splitting an array into blocks of [lengths a, b, and c](hyp:a,b,c) [is measurable](goal). -/
@[fun_prop] lemma measurable_splitThreeBlocks {X : Type*}
    [MeasurableSpace X] (a b c : Nat) :
    Measurable (splitThreeBlocks (X := X) a b c) := by
  unfold splitThreeBlocks
  fun_prop

/-- Three consecutive blocks of an iid array are independent iid arrays.  [the stated conclusion](goal). -/
lemma map_pi_splitThreeBlocks {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (a b c : Nat) :
    Measure.map (splitThreeBlocks (X := X) a b c)
        (Measure.pi fun _ : Fin (a + (b + c)) ↦ mu) =
      (Measure.pi fun _ : Fin a ↦ mu).prod
        ((Measure.pi fun _ : Fin b ↦ mu).prod
          (Measure.pi fun _ : Fin c ↦ mu)) := by
  let I := Fin a ⊕ (Fin b ⊕ Fin c)
  let e : I ≃ Fin (a + (b + c)) :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
  let reindex := MeasurableEquiv.piCongrLeft (fun _ : Fin (a + (b + c)) ↦ X) e
  let splitA := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin a ⊕ (Fin b ⊕ Fin c) ↦ X)
  let splitBC := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin b ⊕ Fin c ↦ X)
  let total := reindex.symm.trans <| splitA.trans <|
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) splitBC
  have htotal : MeasurePreserving total
      (Measure.pi fun _ : Fin (a + (b + c)) ↦ mu)
      ((Measure.pi fun _ : Fin a ↦ mu).prod
        ((Measure.pi fun _ : Fin b ↦ mu).prod
          (Measure.pi fun _ : Fin c ↦ mu))) := by
    exact ((MeasurePreserving.id _).prod
      (measurePreserving_sumPiEquivProdPi
        (fun _ : Fin b ⊕ Fin c ↦ mu))).comp
      ((measurePreserving_sumPiEquivProdPi
        (fun _ : Fin a ⊕ (Fin b ⊕ Fin c) ↦ mu)).comp
        (measurePreserving_piCongrLeft
          (fun _ : Fin (a + (b + c)) ↦ mu) e).symm)
  have hfun : (total : (Fin (a + (b + c)) → X) → _) =
      splitThreeBlocks a b c := by
    funext z
    apply Prod.ext
    · funext i
      rfl
    · apply Prod.ext <;> funext i
      · rfl
      · rfl
  rw [← hfun]
  exact htotal.map_eq

/-- Regroup two independent families by pool and apply each pool map.  [the stated conditions](hyp:hf1,hf2) [the stated conclusion](goal). -/
lemma map_pairByPool
    {A0 A1 A2 B1 B2 C1 C2 : Type*}
    [MeasurableSpace A0] [MeasurableSpace A1] [MeasurableSpace A2]
    [MeasurableSpace B1] [MeasurableSpace B2]
    [MeasurableSpace C1] [MeasurableSpace C2]
    (mu0 : Measure A0) (mu1 : Measure A1) (mu2 : Measure A2)
    (nu1 : Measure B1) (nu2 : Measure B2)
    [IsProbabilityMeasure mu0] [IsProbabilityMeasure mu1]
    [IsProbabilityMeasure mu2] [IsProbabilityMeasure nu1]
    [IsProbabilityMeasure nu2]
    (f1 : A1 × B1 → C1) (f2 : A2 × B2 → C2)
    {rho1 : Measure C1} {rho2 : Measure C2}
    (hf1 : MeasurePreserving f1 (mu1.prod nu1) rho1)
    (hf2 : MeasurePreserving f2 (mu2.prod nu2) rho2) :
    Measure.map
        (fun z : (A0 × (A1 × A2)) × (B1 × B2) ↦
          (z.1.1, f1 (z.1.2.1, z.2.1), f2 (z.1.2.2, z.2.2)))
        ((mu0.prod (mu1.prod mu2)).prod (nu1.prod nu2)) =
      mu0.prod (rho1.prod rho2) := by
  let hInner0 := measurePreserving_prodAssoc mu1 mu2 (nu1.prod nu2)
  let hMove0 := (measurePreserving_prodAssoc mu2 nu1 nu2).symm
  let hSwap : MeasurePreserving Prod.swap (mu2.prod nu1) (nu1.prod mu2) :=
    Measure.measurePreserving_swap
  let hMove1 := measurePreserving_prodAssoc nu1 mu2 nu2
  let hMiddle := hMove1.comp
    (((hSwap.prod (MeasurePreserving.id nu2))).comp hMove0)
  let hInner1 := ((MeasurePreserving.id mu1).prod hMiddle).comp hInner0
  let hInner := (measurePreserving_prodAssoc mu1 nu1
    (mu2.prod nu2)).symm.comp hInner1
  let hOuter := ((MeasurePreserving.id mu0).prod hInner).comp
    (measurePreserving_prodAssoc mu0 (mu1.prod mu2) (nu1.prod nu2))
  let hFinal := ((MeasurePreserving.id mu0).prod (hf1.prod hf2)).comp hOuter
  let g := fun z : (A0 × (A1 × A2)) × (B1 × B2) ↦
    (z.1.1, f1 (z.1.2.1, z.2.1), f2 (z.1.2.2, z.2.2))
  change MeasurePreserving g
    ((mu0.prod (mu1.prod mu2)).prod (nu1.prod nu2))
      (mu0.prod (rho1.prod rho2)) at hFinal
  exact hFinal.map_eq

/-- Explicit tuple projection for the paper's three fixed pool sizes.  [the stated conditions](hyp:z) [the stated conclusion](goal). -/
def unpackHybridPools {n m d : Nat}
    (z : FixedPools (ThreePoolAlphabet (Obs d) (AuxObs d))
      (threePoolCapacity (blockSizes n m).M0
        ((blockSizes n m).np + (blockSizes n m).mp)
        ((blockSizes n m).nf + (blockSizes n m).mf))) :
    (Fin (blockSizes n m).M0 → Obs d) ×
      ((Fin ((blockSizes n m).np + (blockSizes n m).mp) → AuxObs d) ×
        (Fin ((blockSizes n m).nf + (blockSizes n m).mf) → AuxObs d)) :=
  (z .complete, z .sharedLeft, z .sharedRight)

/-- Unpacking hybrid pools for [labeled size, auxiliary size, and dimension](hyp:n,m,d) [is measurable](goal). -/
@[fun_prop] lemma measurable_unpackHybridPools (n m d : Nat) :
    Measurable (unpackHybridPools (n := n) (m := m) (d := d)) := by
  exact (measurable_pi_apply ThreePoolIndex.complete).prodMk
    ((measurable_pi_apply ThreePoolIndex.sharedLeft).prodMk
      (measurable_pi_apply ThreePoolIndex.sharedRight))
/-- This declaration defines [the specified object](goal). -/

def unpackHybridPoolsEquiv {n m d : Nat} :
    FixedPools (ThreePoolAlphabet (Obs d) (AuxObs d))
      (threePoolCapacity (blockSizes n m).M0
        ((blockSizes n m).np + (blockSizes n m).mp)
        ((blockSizes n m).nf + (blockSizes n m).mf)) ≃ᵐ
    (Fin (blockSizes n m).M0 → Obs d) ×
      ((Fin ((blockSizes n m).np + (blockSizes n m).mp) → AuxObs d) ×
        (Fin ((blockSizes n m).nf + (blockSizes n m).mf) → AuxObs d)) where
  toFun := unpackHybridPools
  invFun z i := by
    cases i with
    | complete => exact z.1
    | sharedLeft => exact z.2.1
    | sharedRight => exact z.2.2
  left_inv z := by funext i; cases i <;> rfl
  right_inv z := by rcases z with ⟨z0, z1, z2⟩; rfl
  measurable_toFun := measurable_unpackHybridPools _ _ _
  measurable_invFun := by
    apply measurable_pi_lambda
    intro i
    cases i
    · exact measurable_fst
    · exact measurable_fst.comp measurable_snd
    · exact measurable_snd.comp measurable_snd
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma map_unpackHybridPools_fixedPoolsLaw {n m d : Nat} (P : DiscreteLaw d) :
    Measure.map unpackHybridPools
      (fixedPoolsLaw
        (threePoolObservationLaw (obsLaw P) (auxMarginal P).toMeasure)
        (threePoolCapacity (blockSizes n m).M0
          ((blockSizes n m).np + (blockSizes n m).mp)
          ((blockSizes n m).nf + (blockSizes n m).mf))) =
      (Measure.pi fun _ : Fin (blockSizes n m).M0 ↦ obsLaw P).prod
        ((Measure.pi fun _ : Fin
            ((blockSizes n m).np + (blockSizes n m).mp) ↦
              (auxMarginal P).toMeasure).prod
          (Measure.pi fun _ : Fin
            ((blockSizes n m).nf + (blockSizes n m).mf) ↦
              (auxMarginal P).toMeasure)) := by
  let X := fun i ↦
    Fin (threePoolCapacity (blockSizes n m).M0
      ((blockSizes n m).np + (blockSizes n m).mp)
      ((blockSizes n m).nf + (blockSizes n m).mf) i) →
        ThreePoolAlphabet (Obs d) (AuxObs d) i
  have hfun : (unpackHybridPools (n := n) (m := m) (d := d)) =
      unpackThreePool (X := X) := by rfl
  rw [hfun]
  unfold fixedPoolsLaw
  exact map_unpackThreePool_pi (mu := fun i ↦
      Measure.pi fun _ : Fin
        (threePoolCapacity (blockSizes n m).M0
          ((blockSizes n m).np + (blockSizes n m).mp)
          ((blockSizes n m).nf + (blockSizes n m).mf) i) ↦
            threePoolObservationLaw (obsLaw P) (auxMarginal P).toMeasure i)

/-- The complete, pilot, and factorial fixed blocks extracted from the two samples.  [the stated conditions](hyp:sample) [the stated conclusion](goal). -/
def hybridFixedPools {n m d : Nat} (sample : Sample n m d) :
    FixedPools (ThreePoolAlphabet (Obs d) (AuxObs d))
      (threePoolCapacity (blockSizes n m).M0
        ((blockSizes n m).np + (blockSizes n m).mp)
        ((blockSizes n m).nf + (blockSizes n m).mf)) := by
  let bs := blockSizes n m
  have hn : bs.M0 + (bs.np + bs.nf) = n := by
    dsimp [bs, blockSizes]
    omega
  have hm : 0 + (bs.mp + bs.mf) = m := by
    dsimp [bs, blockSizes]
    omega
  let labeled := splitThreeBlocks bs.M0 bs.np bs.nf
    (fun i ↦ sample.1 (Fin.cast hn i))
  let auxiliary := splitThreeBlocks 0 bs.mp bs.mf
    (fun i ↦ sample.2 (Fin.cast hm i))
  let project : Obs d → AuxObs d := fun z ↦ (z.1, z.2.1)
  intro i
  cases i with
  | complete =>
      change Fin bs.M0 → Obs d
      exact labeled.1
  | sharedLeft =>
      change Fin (bs.np + bs.mp) → AuxObs d
      exact Fin.append (fun j ↦ project (labeled.2.1 j)) auxiliary.2.1
  | sharedRight =>
      change Fin (bs.nf + bs.mf) → AuxObs d
      exact Fin.append (fun j ↦ project (labeled.2.2 j)) auxiliary.2.2

/-- Selecting the three hybrid pools for [labeled size, auxiliary size, and dimension](hyp:n,m,d) [is measurable](goal). -/
@[fun_prop] lemma measurable_hybridFixedPools (n m d : Nat) :
    Measurable (hybridFixedPools (n := n) (m := m) (d := d)) := by
  apply measurable_pi_lambda
  intro i
  cases i <;> simp only [hybridFixedPools]
  all_goals fun_prop

/-- Histograms of a three-pool finite prefix, arranged as the hybrid count tensor.  [the stated conditions](hyp:s) [the stated conclusion](goal). -/
def hybridPrefixCounts {d : Nat}
    (s : PrefixFamily (ThreePoolAlphabet (Obs d) (AuxObs d))) :
    HybridPoissonCounts d :=
  let h0 := finiteSampleHistogram (s .complete).points
  let hp := finiteSampleHistogram (s .sharedLeft).points
  let hf := finiteSampleHistogram (s .sharedRight).points
  fun x a => (h0 (x, a, true), hp (x, a), hf (x, a))

/-- [Forming hybrid count tensors from three finite prefixes is measurable](goal). -/
@[fun_prop] lemma measurable_hybridPrefixCounts {d : Nat} :
    Measurable (hybridPrefixCounts (d := d)) := by
  have h0 : Measurable (fun s :
      PrefixFamily (ThreePoolAlphabet (Obs d) (AuxObs d)) ↦
      finiteSampleHistogram (s ThreePoolIndex.complete).points) :=
    measurable_finiteSampleHistogram.comp
      (measurable_pi_apply ThreePoolIndex.complete)
  have hp : Measurable (fun s :
      PrefixFamily (ThreePoolAlphabet (Obs d) (AuxObs d)) ↦
      finiteSampleHistogram (s ThreePoolIndex.sharedLeft).points) :=
    measurable_finiteSampleHistogram.comp
      (measurable_pi_apply ThreePoolIndex.sharedLeft)
  have hf : Measurable (fun s :
      PrefixFamily (ThreePoolAlphabet (Obs d) (AuxObs d)) ↦
      finiteSampleHistogram (s ThreePoolIndex.sharedRight).points) :=
    measurable_finiteSampleHistogram.comp
      (measurable_pi_apply ThreePoolIndex.sharedRight)
  exact measurable_pi_lambda _ fun x ↦ measurable_pi_lambda _ fun a ↦
    ((measurable_pi_apply (x, a, true)).comp h0).prodMk
      (((measurable_pi_apply (x, a)).comp hp).prodMk
        ((measurable_pi_apply (x, a)).comp hf))

/-- The clipped hybrid statistic viewed as a statistic of three finite prefixes.  [the stated conditions](hyp:n,m,eps,s) [the stated conclusion](goal). -/
noncomputable def finitePrefixHybridStatistic {d : Nat}
    (n m : Nat) (eps : Real)
    (s : PrefixFamily (ThreePoolAlphabet (Obs d) (AuxObs d))) : Real :=
  let bs := blockSizes n m
  hybridPoissonStatistic n m eps (bs.M0 / 8)
    ((bs.nf + bs.mf : Nat) / 8) (hybridPrefixCounts s)

/-- The finite-prefix hybrid statistic at [labeled size](hyp:n), [auxiliary size](hyp:m), and [overlap level](hyp:eps) [is measurable](goal). -/
@[fun_prop] lemma measurable_finitePrefixHybridStatistic {d : Nat}
    (n m : Nat) (eps : Real) :
    Measurable (finitePrefixHybridStatistic (d := d) n m eps) := by
  unfold finitePrefixHybridStatistic
  have hs : Measurable (hybridPoissonStatistic (d := d) n m eps
      ((blockSizes n m).M0 / 8)
      (((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8)) :=
    measurable_of_countable _
  exact hs.comp measurable_hybridPrefixCounts
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma finitePrefixHybridStatistic_mem_Icc {d : Nat}
    (n m : Nat) (eps : Real)
    (s : PrefixFamily (ThreePoolAlphabet (Obs d) (AuxObs d))) :
    finitePrefixHybridStatistic n m eps s ∈ Set.Icc (-1 : Real) 1 := by
  exact hybridPoissonStatistic_mem_Icc n m eps _ _ _

/-- The extracted fixed blocks have exactly the generic three-pool iid law.  [the stated conclusion](goal). -/
lemma hybridFixedPools_map_annotationLaw {n m d : Nat} (P : DiscreteLaw d) :
    Measure.map (hybridFixedPools (n := n) (m := m) (d := d))
        (annotationLaw P n m) =
      fixedPoolsLaw
        (threePoolObservationLaw (obsLaw P) (auxMarginal P).toMeasure)
        (threePoolCapacity (blockSizes n m).M0
          ((blockSizes n m).np + (blockSizes n m).mp)
          ((blockSizes n m).nf + (blockSizes n m).mf)) := by
  let bs := blockSizes n m
  have hn : bs.M0 + (bs.np + bs.nf) = n := by
    dsimp [bs, blockSizes]
    omega
  have hm : 0 + (bs.mp + bs.mf) = m := by
    dsimp [bs, blockSizes]
    omega
  let castL : (Fin n → Obs d) → Fin (bs.M0 + (bs.np + bs.nf)) → Obs d :=
    fun z i ↦ z (Fin.cast hn i)
  let castA : (Fin m → AuxObs d) → Fin (0 + (bs.mp + bs.mf)) → AuxObs d :=
    fun z i ↦ z (Fin.cast hm i)
  let lab := splitThreeBlocks bs.M0 bs.np bs.nf ∘ castL
  let aux := (fun z ↦ z.2) ∘ splitThreeBlocks 0 bs.mp bs.mf ∘ castA
  let mu0 := Measure.pi fun _ : Fin bs.M0 ↦ obsLaw P
  let muP := Measure.pi fun _ : Fin bs.np ↦ obsLaw P
  let muF := Measure.pi fun _ : Fin bs.nf ↦ obsLaw P
  let nuP := Measure.pi fun _ : Fin bs.mp ↦ (auxMarginal P).toMeasure
  let nuF := Measure.pi fun _ : Fin bs.mf ↦ (auxMarginal P).toMeasure
  let rhoP := Measure.pi fun _ : Fin (bs.np + bs.mp) ↦ (auxMarginal P).toMeasure
  let rhoF := Measure.pi fun _ : Fin (bs.nf + bs.mf) ↦ (auxMarginal P).toMeasure
  have hcastL : Measure.map castL (labeledProductLaw P n) =
      Measure.pi fun _ : Fin (bs.M0 + (bs.np + bs.nf)) ↦ obsLaw P :=
    (measurePreserving_piCongrLeft
      (fun _ : Fin (bs.M0 + (bs.np + bs.nf)) ↦ obsLaw P)
      (finCongr hn).symm).map_eq
  have hcastA : Measure.map castA (auxProductLaw P m) =
      Measure.pi fun _ : Fin (0 + (bs.mp + bs.mf)) ↦
        (auxMarginal P).toMeasure :=
    (measurePreserving_piCongrLeft
      (fun _ : Fin (0 + (bs.mp + bs.mf)) ↦ (auxMarginal P).toMeasure)
      (finCongr hm).symm).map_eq
  have hlab : Measure.map lab (labeledProductLaw P n) =
      mu0.prod (muP.prod muF) := by
    rw [show Measure.map lab (labeledProductLaw P n) =
        Measure.map (splitThreeBlocks bs.M0 bs.np bs.nf)
          (Measure.map castL (labeledProductLaw P n)) by
      rw [Measure.map_map (measurable_splitThreeBlocks _ _ _) (by fun_prop)]
      ]
    rw [hcastL, map_pi_splitThreeBlocks]
  have haux : Measure.map aux (auxProductLaw P m) = nuP.prod nuF := by
    rw [show Measure.map aux (auxProductLaw P m) =
        Measure.map Prod.snd
          (Measure.map (splitThreeBlocks 0 bs.mp bs.mf)
            (Measure.map castA (auxProductLaw P m))) by
      rw [Measure.map_map (measurable_splitThreeBlocks _ _ _) (by fun_prop),
        Measure.map_map measurable_snd
          ((measurable_splitThreeBlocks _ _ _).comp (by fun_prop))]
      ]
    rw [hcastA, map_pi_splitThreeBlocks]
    exact MeasureTheory.measurePreserving_snd.map_eq
  let project : Obs d → AuxObs d := fun z ↦ (z.1, z.2.1)
  have hproject : Measure.map project (obsLaw P) = (auxMarginal P).toMeasure :=
    PMF.toMeasure_map (p := P.pmf) (f := project) (by fun_prop)
  let fP : (Fin bs.np → Obs d) × (Fin bs.mp → AuxObs d) →
      (Fin (bs.np + bs.mp) → AuxObs d) :=
    fun z ↦ Fin.append (fun i ↦ project (z.1 i)) z.2
  let fF : (Fin bs.nf → Obs d) × (Fin bs.mf → AuxObs d) →
      (Fin (bs.nf + bs.mf) → AuxObs d) :=
    fun z ↦ Fin.append (fun i ↦ project (z.1 i)) z.2
  have hfpMap : Measure.map fP (muP.prod nuP) = rhoP := by
    let coord := fun z : Fin bs.np → Obs d ↦ fun i ↦ project (z i)
    have hc : Measure.map coord muP =
        Measure.pi fun _ : Fin bs.np ↦ (auxMarginal P).toMeasure := by
      rw [Causalean.Stat.map_pi_finCoordinatewise bs.np (obsLaw P) (by fun_prop)]
      simp [hproject]
    rw [show Measure.map fP (muP.prod nuP) =
        Measure.map (fun z ↦ Fin.append z.1 z.2)
          (Measure.map (Prod.map coord id) (muP.prod nuP)) by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl]
    rw [← Measure.map_prod_map _ _ (by fun_prop : Measurable coord) measurable_id,
      hc, Measure.map_id, map_prod_finAppend]
  have hffMap : Measure.map fF (muF.prod nuF) = rhoF := by
    let coord := fun z : Fin bs.nf → Obs d ↦ fun i ↦ project (z i)
    have hc : Measure.map coord muF =
        Measure.pi fun _ : Fin bs.nf ↦ (auxMarginal P).toMeasure := by
      rw [Causalean.Stat.map_pi_finCoordinatewise bs.nf (obsLaw P) (by fun_prop)]
      simp [hproject]
    rw [show Measure.map fF (muF.prod nuF) =
        Measure.map (fun z ↦ Fin.append z.1 z.2)
          (Measure.map (Prod.map coord id) (muF.prod nuF)) by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl]
    rw [← Measure.map_prod_map _ _ (by fun_prop : Measurable coord) measurable_id,
      hc, Measure.map_id, map_prod_finAppend]
  have hfp : MeasurePreserving fP (muP.prod nuP) rhoP :=
    ⟨by fun_prop, hfpMap⟩
  have hff : MeasurePreserving fF (muF.prod nuF) rhoF :=
    ⟨by fun_prop, hffMap⟩
  let stage := Prod.map lab aux
  let finish := fun z :
      ((Fin bs.M0 → Obs d) ×
        ((Fin bs.np → Obs d) × (Fin bs.nf → Obs d))) ×
        ((Fin bs.mp → AuxObs d) × (Fin bs.mf → AuxObs d)) ↦
      (z.1.1, fP (z.1.2.1, z.2.1), fF (z.1.2.2, z.2.2))
  have hsource : Measure.map stage (annotationLaw P n m) =
      (mu0.prod (muP.prod muF)).prod (nuP.prod nuF) := by
    unfold annotationLaw
    rw [← Measure.map_prod_map _ _ (by fun_prop : Measurable lab)
      (by fun_prop : Measurable aux), hlab, haux]
  have hfinish : Measure.map finish
      ((mu0.prod (muP.prod muF)).prod (nuP.prod nuF)) =
      mu0.prod (rhoP.prod rhoF) :=
    map_pairByPool mu0 muP muF nuP nuF fP fF hfp hff
  have hlhs : Measure.map
      (unpackHybridPools (n := n) (m := m) (d := d))
      (Measure.map hybridFixedPools (annotationLaw P n m)) =
      mu0.prod (rhoP.prod rhoF) := by
    have hmap0 : Measure.map unpackHybridPools
        (Measure.map hybridFixedPools (annotationLaw P n m)) =
        Measure.map (unpackHybridPools ∘ hybridFixedPools)
          (annotationLaw P n m) :=
      Measure.map_map (measurable_unpackHybridPools n m d)
        (measurable_hybridFixedPools n m d)
    calc
      _ = Measure.map (unpackHybridPools ∘ hybridFixedPools)
          (annotationLaw P n m) := hmap0
      _ = Measure.map (finish ∘ stage) (annotationLaw P n m) := by rfl
      _ = Measure.map finish (Measure.map stage (annotationLaw P n m)) :=
        (Measure.map_map (by fun_prop : Measurable finish)
          (by fun_prop : Measurable stage)).symm
      _ = Measure.map finish
          ((mu0.prod (muP.prod muF)).prod (nuP.prod nuF)) := by rw [hsource]
      _ = _ := hfinish
  apply ((unpackHybridPoolsEquiv (n := n) (m := m) (d := d)).measurableEmbedding.map_injective)
  change Measure.map unpackHybridPools
      (Measure.map hybridFixedPools (annotationLaw P n m)) =
    Measure.map unpackHybridPools
      (fixedPoolsLaw
        (threePoolObservationLaw (obsLaw P) (auxMarginal P).toMeasure)
        (threePoolCapacity (blockSizes n m).M0
          ((blockSizes n m).np + (blockSizes n m).mp)
          ((blockSizes n m).nf + (blockSizes n m).mf)))
  rw [hlhs]
  simpa only [mu0, rhoP, rhoF] using
    (map_unpackHybridPools_fixedPoolsLaw (n := n) (m := m) P).symm

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

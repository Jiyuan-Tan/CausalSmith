module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Decoder
public import CausalSmith.Substrate.PositiveDensityCondindepIntersection.FiniteCoordinates
public import Causalean.Mathlib.Probability.Independence.Conditional.CondExp
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.ProductMeasure

/-!
# Conditional-independence bridges for parent pruning

This file scaffolds the positivity-based graphoid intersection step and the
finite-coordinate product bridge used with Causalean's generic weak-union lemma.
-/

@[expose] public section

open Causalean.Graph


open MeasureTheory ProbabilityTheory
open Causalean

noncomputable section

open Causalean.Mathlib.MeasureTheory

open Causalean.Mathlib.Probability.Independence.Conditional

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- The latent coordinate targeted by an environment label, expressed on observed space. -/
def observedLatentCoordinate
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (e : Fin n) : LatentState n → ℝ :=
  by
    classical
    exact (observedSupport G W).piecewise
      (fun x => W.unmix x (W.targetPerm e)) (fun _ => 0)

-- @node: measurable_observedLatentCoordinate
/-- The support-restricted version of an observed latent coordinate is measurable; on the
observed support it is exactly the corresponding coordinate of the inverse mixing map.  Given [the stated inputs and conditions](hyp:hmix), [the stated conclusion](goal) follows. -/
lemma measurable_observedLatentCoordinate
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hmix : SharedDiffeomorphicMixing G θ W) (e : Fin n) :
    Measurable (observedLatentCoordinate W e) := by
  classical
  have hcube : IsCompact (latentCube n) := by
    rw [latentCube]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hs : IsClosed (observedSupport G W) :=
    (hcube.image_of_continuousOn hmix.1.continuousOn).isClosed
  unfold observedLatentCoordinate
  exact ((continuous_apply (W.targetPerm e)).comp_continuousOn hmix.2.1.continuousOn)
    |>.measurable_piecewise continuous_const.continuousOn hs.measurableSet

-- @node: observedLatentCoordinate_mix
/-- On the latent cube, the measurable observed coordinate version recovers the targeted
latent coordinate after applying the mixing map.  Given [the stated inputs and conditions](hyp:hmix,hv), [the stated conclusion](goal) follows. -/
lemma observedLatentCoordinate_mix
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hmix : SharedDiffeomorphicMixing G θ W)
    (e : Fin n) (v : LatentState n) (hv : v ∈ latentCube n) :
    observedLatentCoordinate W e (W.mix v) = v (W.targetPerm e) := by
  classical
  rw [observedLatentCoordinate, Set.piecewise_eq_of_mem]
  · exact congrFun (hmix.2.2.1 v hv) (W.targetPerm e)
  · exact ⟨v, hv, rfl⟩

-- @node: condIndepFun_map_iff
/-- Conditional independence is equivalent before and after transporting the ambient law
along a measurable map.  Given [the stated inputs and conditions](hyp:hphi,hf,hg,hk), [the stated conclusion](goal) follows. -/
lemma condIndepFun_map_iff
    {A B X Y Z : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace Z]
    {phi : A → B} (hphi : Measurable phi)
    {f : B → X} (hf : Measurable f) {g : B → Y} (hg : Measurable g)
    {k : B → Z} (hk : Measurable k)
    {mu : Measure A} [IsFiniteMeasure mu] [IsFiniteMeasure (mu.map phi)] :
    CondIndepFun (MeasurableSpace.comap (k ∘ phi) inferInstance)
        (hk.comp hphi).comap_le (f ∘ phi) (g ∘ phi) mu ↔
      CondIndepFun (MeasurableSpace.comap k inferInstance)
        hk.comap_le f g (mu.map phi) := by
  have hcd1 : condDistrib (g ∘ phi) (k ∘ phi) mu =
      condDistrib g k (mu.map phi) := by
    simp only [condDistrib]
    congr 1
    exact (Measure.map_map (hk.prodMk hg) hphi).symm
  have hcd2 : condDistrib (g ∘ phi) (fun a ↦ ((k ∘ phi) a, (f ∘ phi) a)) mu =
      condDistrib g (fun b ↦ (k b, f b)) (mu.map phi) := by
    simp only [condDistrib]
    congr 1
    exact (Measure.map_map ((hk.prodMk hf).prodMk hg) hphi).symm
  have hmap : mu.map (fun a ↦ ((k ∘ phi) a, (f ∘ phi) a)) =
      (mu.map phi).map (fun b ↦ (k b, f b)) :=
    (Measure.map_map (hk.prodMk hf) hphi).symm
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
        (hg.comp hphi) (hf.comp hphi) (hk.comp hphi),
      condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hg hf hk,
      hcd2, hcd1, hmap]

-- @node: condIndepGiven_map_iff
/-- Pulling three measurable variables back along a measurable map preserves and reflects
conditional independence when the target law is the corresponding pushforward.  Given [the stated inputs and conditions](hyp:hphi,hf,hg,hk), [the stated conclusion](goal) follows. -/
lemma condIndepGiven_map_iff
    {A B X Y Z : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace Z]
    {phi : A → B} (hphi : Measurable phi)
    {f : B → X} (hf : Measurable f) {g : B → Y} (hg : Measurable g)
    {k : B → Z} (hk : Measurable k)
    {mu : Measure A} [IsFiniteMeasure mu] [IsFiniteMeasure (mu.map phi)] :
    CondIndepGiven mu (f ∘ phi) (g ∘ phi) (k ∘ phi) ↔
      CondIndepGiven (mu.map phi) f g k := by
  constructor
  · rintro ⟨_, _, _, _, hCI⟩
    refine ⟨inferInstance, hf, hg, hk, ?_⟩
    exact (condIndepFun_map_iff hphi hf hg hk).1 hCI
  · rintro ⟨_, _, _, _, hCI⟩
    refine ⟨inferInstance, hf.comp hphi, hg.comp hphi, hk.comp hphi, ?_⟩
    exact (condIndepFun_map_iff hphi hf hg hk).2 hCI

-- @node: condIndepGiven_measurableEquiv_comp
/-- Applying bimeasurable bijections separately to the two variables and the conditioning
variable preserves conditional independence.  [the stated conclusion](goal) follows. -/
lemma condIndepGiven_measurableEquiv_comp
    {Ω X Y Z X' Y' Z' : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace X'] [MeasurableSpace Y'] [MeasurableSpace Z']
    {μ : Measure Ω} (UX : Ω → X) (UY : Ω → Y) (UZ : Ω → Z)
    (eX : X ≃ᵐ X') (eY : Y ≃ᵐ Y') (eZ : Z ≃ᵐ Z') :
    CondIndepGiven μ (eX ∘ UX) (eY ∘ UY) (eZ ∘ UZ) ↔
      CondIndepGiven μ UX UY UZ := by
  constructor
  · rintro ⟨hμ, hX, hY, hZ, hCI⟩
    letI := hμ
    have hX' : Measurable UX := by
      convert eX.symm.measurable.comp hX using 1
      funext ω
      exact (eX.symm_apply_apply (UX ω)).symm
    have hY' : Measurable UY := by
      convert eY.symm.measurable.comp hY using 1
      funext ω
      exact (eY.symm_apply_apply (UY ω)).symm
    have hZ' : Measurable UZ := by
      convert eZ.symm.measurable.comp hZ using 1
      funext ω
      exact (eZ.symm_apply_apply (UZ ω)).symm
    refine ⟨hμ, hX', hY', hZ', ?_⟩
    have hraw := hCI.comp eX.symm.measurable eY.symm.measurable
    have hs : CondIndepFun (MeasurableSpace.comap (eZ ∘ UZ) inferInstance)
        hZ.comap_le UX UY μ := by
      simpa only [Function.comp_def, eX.symm_apply_apply,
        eY.symm_apply_apply] using hraw
    simpa only [← MeasurableSpace.comap_comp,
      eZ.measurableEmbedding.comap_eq] using hs
  · rintro ⟨hμ, hX, hY, hZ, hCI⟩
    letI := hμ
    refine ⟨hμ, eX.measurable.comp hX, eY.measurable.comp hY,
      eZ.measurable.comp hZ, ?_⟩
    have hraw := hCI.comp eX.measurable eY.measurable
    simpa only [← MeasurableSpace.comap_comp,
      eZ.measurableEmbedding.comap_eq] using hraw

-- @node: condIndepGiven_congr_ae_forward
/-- Replacing all three measurable coordinates by almost-everywhere equal versions preserves
conditional independence.  Given [the stated inputs and conditions](hyp:hX₁,hX₂,hY₁,hY₂,hZ₁,hZ₂,hX,hY,hZ), [the stated conclusion](goal) follows. -/
lemma condIndepGiven_congr_ae_forward
    {Ω X Y Z : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace Z]
    {μ : Measure Ω} {X₁ X₂ : Ω → X} {Y₁ Y₂ : Ω → Y} {Z₁ Z₂ : Ω → Z}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂)
    (hZ₁ : Measurable Z₁) (hZ₂ : Measurable Z₂)
    (hX : X₁ =ᵐ[μ] X₂) (hY : Y₁ =ᵐ[μ] Y₂) (hZ : Z₁ =ᵐ[μ] Z₂) :
    CondIndepGiven μ X₁ Y₁ Z₁ → CondIndepGiven μ X₂ Y₂ Z₂ := by
  rintro ⟨hμ, _, _, _, hCI⟩
  letI := hμ
  refine ⟨hμ, hX₂, hY₂, hZ₂, ?_⟩
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY₂ hX₂ hZ₂]
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY₁ hX₁ hZ₁] at hCI
  have hZY : (fun ω => (Z₁ ω, Y₁ ω)) =ᵐ[μ] fun ω => (Z₂ ω, Y₂ ω) :=
    hZ.prodMk hY
  have hZX : (fun ω => (Z₁ ω, X₁ ω)) =ᵐ[μ] fun ω => (Z₂ ω, X₂ ω) :=
    hZ.prodMk hX
  have hZXY := (hZ.prodMk hX).prodMk hY
  simpa only [condDistrib, Measure.map_congr hZY, Measure.map_congr hZX,
    Measure.map_congr hZXY] using hCI

-- @node: condIndepGiven_congr_ae
/-- Conditional independence is invariant under almost-everywhere replacement of each of
its three measurable coordinates.  Given [the stated inputs and conditions](hyp:hX₁,hX₂,hY₁,hY₂,hZ₁,hZ₂,hX,hY,hZ), [the stated conclusion](goal) follows. -/
lemma condIndepGiven_congr_ae
    {Ω X Y Z : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace Z]
    {μ : Measure Ω} {X₁ X₂ : Ω → X} {Y₁ Y₂ : Ω → Y} {Z₁ Z₂ : Ω → Z}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂)
    (hZ₁ : Measurable Z₁) (hZ₂ : Measurable Z₂)
    (hX : X₁ =ᵐ[μ] X₂) (hY : Y₁ =ᵐ[μ] Y₂) (hZ : Z₁ =ᵐ[μ] Z₂) :
    CondIndepGiven μ X₁ Y₁ Z₁ ↔ CondIndepGiven μ X₂ Y₂ Z₂ := by
  constructor
  · exact condIndepGiven_congr_ae_forward hX₁ hX₂ hY₁ hY₂ hZ₁ hZ₂ hX hY hZ
  · exact condIndepGiven_congr_ae_forward hX₂ hX₁ hY₂ hY₁ hZ₂ hZ₁
      hX.symm hY.symm hZ.symm

private lemma condIndepGiven_intersection_of_equivalent_fourBlock
    {A X Y V Z : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]
    [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    {mu : Measure A} [IsFiniteMeasure mu]
    (UX : A → X) (UY : A → Y) (UV : A → V) (UZ : A → Z)
    (hUX : Measurable UX) (hUY : Measurable UY)
    (hUV : Measurable UV) (hUZ : Measurable UZ)
    (muX : Measure X) (muY : Measure Y) (muV : Measure V) (muZ : Measure Z)
    [SigmaFinite muX] [SigmaFinite muY] [SigmaFinite muV] [SigmaFinite muZ]
    (hforward : mu.map (fun a ↦ (UX a, (UY a, (UV a, UZ a)))) ≪
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockReference
        muX muY muV muZ)
    (hreverse : CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockReference
        muX muY muV muZ ≪
      mu.map (fun a ↦ (UX a, (UY a, (UV a, UZ a)))))
    (hXY : CondIndepGiven mu UX UY (fun a ↦ (UZ a, UV a)))
    (hXV : CondIndepGiven mu UX UV (fun a ↦ (UZ a, UY a))) :
    CondIndepGiven mu UX UY UZ ∧
      CondIndepGiven mu UX (fun a ↦ (UY a, UV a)) UZ := by
  let F : A → CausalSmith.Substrate.PositiveDensityCondindepIntersection.FourBlock X Y V Z :=
    fun a ↦ (UX a, (UY a, (UV a, UZ a)))
  have hF : Measurable F := by
    exact hUX.prodMk (hUY.prodMk (hUV.prodMk hUZ))
  let rho := mu.map F
  letI : IsFiniteMeasure rho := by
    dsimp only [rho]
    exact Measure.isFiniteMeasure_map mu F
  let ref := CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockReference
    muX muY muV muZ
  letI : SigmaFinite ref := by
    dsimp only [ref, CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockReference]
    infer_instance
  letI : rho.HaveLebesgueDecomposition ref := inferInstance
  let d := rho.rnDeriv ref
  have hrho : ref.withDensity d = rho := by
    exact Measure.withDensity_rnDeriv_eq rho ref hforward
  have hd : Measurable d := Measure.measurable_rnDeriv _ _
  have hdpos : ∀ᵐ q ∂ref, 0 < d q := by
    exact hreverse.ae_le (Measure.rnDeriv_pos hforward)
  rcases hXY with ⟨_, _, _, _, hXY⟩
  rcases hXV with ⟨_, _, _, _, hXV⟩
  have hXYrho : CondIndepFun
      (MeasurableSpace.comap
        (@CausalSmith.Substrate.PositiveDensityCondindepIntersection.zvCoord X Y V Z)
        inferInstance)
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.measurable_zvCoord.comap_le
      (@CausalSmith.Substrate.PositiveDensityCondindepIntersection.xCoord X Y V Z)
      (@CausalSmith.Substrate.PositiveDensityCondindepIntersection.yCoord X Y V Z) rho := by
    apply (condIndepFun_map_iff hF
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.measurable_xCoord
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.measurable_yCoord
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.measurable_zvCoord).1
    convert hXY using 1 <;> rfl
  have hXVrho : CondIndepFun
      (MeasurableSpace.comap
        (@CausalSmith.Substrate.PositiveDensityCondindepIntersection.zyCoord X Y V Z)
        inferInstance)
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.measurable_zyCoord.comap_le
      (@CausalSmith.Substrate.PositiveDensityCondindepIntersection.xCoord X Y V Z)
      (@CausalSmith.Substrate.PositiveDensityCondindepIntersection.vCoord X Y V Z) rho := by
    apply (condIndepFun_map_iff hF
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.measurable_xCoord
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.measurable_vCoord
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.measurable_zyCoord).1
    convert hXV using 1 <;> rfl
  have hinter :=
    CausalSmith.Substrate.PositiveDensityCondindepIntersection.condIndepFun_intersection_of_eq_withDensity
      muX muY muV muZ hd hrho.symm hdpos hXYrho hXVrho
  have hdecomp :=
    CausalSmith.Substrate.PositiveDensityCondindepIntersection.condIndepFun_decomposition_of_eq_withDensity
      muX muY muV muZ hd hrho.symm hdpos hXYrho hXVrho
  constructor
  · refine ⟨inferInstance, hUX, hUY, hUZ, ?_⟩
    apply (condIndepFun_map_iff hF
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.measurable_xCoord
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.measurable_yCoord
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.measurable_zCoord).2
    exact hdecomp
  · refine ⟨inferInstance, hUX, hUY.prodMk hUV, hUZ, ?_⟩
    apply (condIndepFun_map_iff hF
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.measurable_xCoord
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.measurable_yvCoord
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.measurable_zCoord).2
    exact hinter

private theorem valuesEquivOfEq_apply_local
    {M : Type*} {Omega : M → Type*} [∀ i, MeasurableSpace (Omega i)]
    {A B : Finset M} (h : A = B) (x : ValuesOn A Omega)
    (i : M) (hi : i ∈ A) (hi' : i ∈ B) :
    valuesEquivOfEq h x ⟨i, hi'⟩ = x ⟨i, hi⟩ := by
  subst B
  rfl

private noncomputable def fourBlockValuesEquiv_local
    {M : Type*} [DecidableEq M]
    {Omega : M → Type*} [∀ i, MeasurableSpace (Omega i)]
    (I J K L : Finset M)
    (hKL : Disjoint K L) (hJ_KL : Disjoint J (K ∪ L))
    (hI_JKL : Disjoint I (J ∪ (K ∪ L))) :
    CausalSmith.Substrate.PositiveDensityCondindepIntersection.FourBlock
        (ValuesOn I Omega) (ValuesOn J Omega) (ValuesOn K Omega) (ValuesOn L Omega) ≃ᵐ
      ValuesOn
        (CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockIndices I J K L)
        Omega := by
  let eKL := MeasurableEquiv.piFinsetUnion Omega hKL
  let eJKL :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (ValuesOn J Omega)) eKL).trans
      (MeasurableEquiv.piFinsetUnion Omega hJ_KL)
  let e0 :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (ValuesOn I Omega)) eJKL).trans
      (MeasurableEquiv.piFinsetUnion Omega hI_JKL)
  have hu : I ∪ (J ∪ (K ∪ L)) =
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockIndices I J K L := by
    simp only [CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockIndices,
      Finset.union_assoc]
  exact e0.trans (valuesEquivOfEq hu)

private theorem measurePreserving_fourBlockValuesEquiv_local
    {M : Type*} [DecidableEq M]
    {Omega : M → Type*} [∀ i, MeasurableSpace (Omega i)]
    (I J K L : Finset M)
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hIL : Disjoint I L)
    (hJK : Disjoint J K) (hJL : Disjoint J L) (hKL : Disjoint K L)
    (mu : ∀ i, Measure (Omega i)) [∀ i, SigmaFinite (mu i)] :
    MeasurePreserving
      (fourBlockValuesEquiv_local I J K L hKL
        (Finset.disjoint_union_right.mpr ⟨hJK, hJL⟩)
        (Finset.disjoint_union_right.mpr
          ⟨hIJ, Finset.disjoint_union_right.mpr ⟨hIK, hIL⟩⟩))
      (CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockReference
        (Measure.pi fun i : I ↦ mu i) (Measure.pi fun i : J ↦ mu i)
        (Measure.pi fun i : K ↦ mu i) (Measure.pi fun i : L ↦ mu i))
      (CausalSmith.Substrate.PositiveDensityCondindepIntersection.finiteBlockReference
        I J K L mu) := by
  have hJ_KL : Disjoint J (K ∪ L) :=
    Finset.disjoint_union_right.mpr ⟨hJK, hJL⟩
  have hI_JKL : Disjoint I (J ∪ (K ∪ L)) :=
    Finset.disjoint_union_right.mpr
      ⟨hIJ, Finset.disjoint_union_right.mpr ⟨hIK, hIL⟩⟩
  have hKL' := measurePreserving_piFinsetUnion hKL mu
  have hJKL := (measurePreserving_piFinsetUnion hJ_KL mu).comp
    ((MeasurePreserving.id (Measure.pi fun i : J ↦ mu i)).prod hKL')
  have h0 := (measurePreserving_piFinsetUnion hI_JKL mu).comp
    ((MeasurePreserving.id (Measure.pi fun i : I ↦ mu i)).prod hJKL)
  have hu : I ∪ (J ∪ (K ∪ L)) =
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockIndices I J K L := by
    simp only [CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockIndices,
      Finset.union_assoc]
  have hu' := measurePreserving_valuesEquivOfEq hu
    (fun i : {i // i ∈ I ∪ (J ∪ (K ∪ L))} ↦ mu i)
  change MeasurePreserving
    (fourBlockValuesEquiv_local I J K L hKL hJ_KL hI_JKL)
    (CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockReference
      (Measure.pi fun i : I ↦ mu i) (Measure.pi fun i : J ↦ mu i)
      (Measure.pi fun i : K ↦ mu i) (Measure.pi fun i : L ↦ mu i))
    (CausalSmith.Substrate.PositiveDensityCondindepIntersection.finiteBlockReference I J K L mu)
  convert hu'.comp h0 using 1 <;> rfl

private theorem fourBlockValuesEquiv_local_apply
    {M : Type*} [DecidableEq M]
    {Omega : M → Type*} [∀ i, MeasurableSpace (Omega i)]
    (I J K L : Finset M)
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hIL : Disjoint I L)
    (hJK : Disjoint J K) (hJL : Disjoint J L) (hKL : Disjoint K L)
    (q : CausalSmith.Substrate.PositiveDensityCondindepIntersection.FourBlock
      (ValuesOn I Omega) (ValuesOn J Omega) (ValuesOn K Omega) (ValuesOn L Omega)) :
    (∀ i (hi : i ∈ I),
      fourBlockValuesEquiv_local I J K L hKL
        (Finset.disjoint_union_right.mpr ⟨hJK, hJL⟩)
        (Finset.disjoint_union_right.mpr
          ⟨hIJ, Finset.disjoint_union_right.mpr ⟨hIK, hIL⟩⟩) q
        ⟨i, CausalSmith.Substrate.PositiveDensityCondindepIntersection.first_subset_fourBlock
          (I := I) (J := J) (K := K) (L := L) hi⟩ =
      q.1 ⟨i, hi⟩) ∧
    (∀ i (hi : i ∈ J),
      fourBlockValuesEquiv_local I J K L hKL
        (Finset.disjoint_union_right.mpr ⟨hJK, hJL⟩)
        (Finset.disjoint_union_right.mpr
          ⟨hIJ, Finset.disjoint_union_right.mpr ⟨hIK, hIL⟩⟩) q
        ⟨i, CausalSmith.Substrate.PositiveDensityCondindepIntersection.second_subset_fourBlock
          (I := I) (J := J) (K := K) (L := L) hi⟩ =
      q.2.1 ⟨i, hi⟩) ∧
    (∀ i (hi : i ∈ K),
      fourBlockValuesEquiv_local I J K L hKL
        (Finset.disjoint_union_right.mpr ⟨hJK, hJL⟩)
        (Finset.disjoint_union_right.mpr
          ⟨hIJ, Finset.disjoint_union_right.mpr ⟨hIK, hIL⟩⟩) q
        ⟨i, CausalSmith.Substrate.PositiveDensityCondindepIntersection.third_subset_fourBlock
          (I := I) (J := J) (K := K) (L := L) hi⟩ =
      q.2.2.1 ⟨i, hi⟩) ∧
    (∀ i (hi : i ∈ L),
      fourBlockValuesEquiv_local I J K L hKL
        (Finset.disjoint_union_right.mpr ⟨hJK, hJL⟩)
        (Finset.disjoint_union_right.mpr
          ⟨hIJ, Finset.disjoint_union_right.mpr ⟨hIK, hIL⟩⟩) q
        ⟨i, CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourth_subset_fourBlock
          (I := I) (J := J) (K := K) (L := L) hi⟩ =
      q.2.2.2 ⟨i, hi⟩) := by
  have hJ_KL : Disjoint J (K ∪ L) := Finset.disjoint_union_right.mpr ⟨hJK, hJL⟩
  have hI_JKL : Disjoint I (J ∪ (K ∪ L)) :=
    Finset.disjoint_union_right.mpr
      ⟨hIJ, Finset.disjoint_union_right.mpr ⟨hIK, hIL⟩⟩
  constructor
  · intro i hi
    unfold fourBlockValuesEquiv_local
    simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.prodCongr]
    rw [valuesEquivOfEq_apply_local]
    change (Equiv.piFinsetUnion Omega hI_JKL)
      (q.1, (Equiv.piFinsetUnion Omega hJ_KL)
        (q.2.1, (Equiv.piFinsetUnion Omega hKL) (q.2.2.1, q.2.2.2)))
      ⟨i, Finset.mem_union_left _ hi⟩ = q.1 ⟨i, hi⟩
    exact Equiv.piFinsetUnion_left Omega hI_JKL hi _
  constructor
  · intro i hi
    unfold fourBlockValuesEquiv_local
    simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.prodCongr]
    rw [valuesEquivOfEq_apply_local]
    change (Equiv.piFinsetUnion Omega hI_JKL)
      (q.1, (Equiv.piFinsetUnion Omega hJ_KL)
        (q.2.1, (Equiv.piFinsetUnion Omega hKL) (q.2.2.1, q.2.2.2)))
      ⟨i, Finset.mem_union_right I (Finset.mem_union_left _ hi)⟩ = q.2.1 ⟨i, hi⟩
    calc
      _ = (Equiv.piFinsetUnion Omega hJ_KL)
          (q.2.1, (Equiv.piFinsetUnion Omega hKL) (q.2.2.1, q.2.2.2))
          ⟨i, Finset.mem_union_left _ hi⟩ :=
        Equiv.piFinsetUnion_right Omega hI_JKL (Finset.mem_union_left _ hi) _
      _ = q.2.1 ⟨i, hi⟩ := Equiv.piFinsetUnion_left Omega hJ_KL hi _
  constructor
  · intro i hi
    unfold fourBlockValuesEquiv_local
    simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.prodCongr]
    rw [valuesEquivOfEq_apply_local]
    change (Equiv.piFinsetUnion Omega hI_JKL)
      (q.1, (Equiv.piFinsetUnion Omega hJ_KL)
        (q.2.1, (Equiv.piFinsetUnion Omega hKL) (q.2.2.1, q.2.2.2)))
      ⟨i, Finset.mem_union_right I
        (Finset.mem_union_right J (Finset.mem_union_left L hi))⟩ = q.2.2.1 ⟨i, hi⟩
    calc
      _ = (Equiv.piFinsetUnion Omega hJ_KL)
          (q.2.1, (Equiv.piFinsetUnion Omega hKL) (q.2.2.1, q.2.2.2))
          ⟨i, Finset.mem_union_right J (Finset.mem_union_left L hi)⟩ :=
        Equiv.piFinsetUnion_right Omega hI_JKL
          (Finset.mem_union_right J (Finset.mem_union_left L hi)) _
      _ = (Equiv.piFinsetUnion Omega hKL) (q.2.2.1, q.2.2.2)
          ⟨i, Finset.mem_union_left L hi⟩ :=
        Equiv.piFinsetUnion_right Omega hJ_KL (Finset.mem_union_left L hi) _
      _ = q.2.2.1 ⟨i, hi⟩ := Equiv.piFinsetUnion_left Omega hKL hi _
  · intro i hi
    unfold fourBlockValuesEquiv_local
    simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.prodCongr]
    rw [valuesEquivOfEq_apply_local]
    change (Equiv.piFinsetUnion Omega hI_JKL)
      (q.1, (Equiv.piFinsetUnion Omega hJ_KL)
        (q.2.1, (Equiv.piFinsetUnion Omega hKL) (q.2.2.1, q.2.2.2)))
      ⟨i, Finset.mem_union_right I
        (Finset.mem_union_right J (Finset.mem_union_right K hi))⟩ = q.2.2.2 ⟨i, hi⟩
    calc
      _ = (Equiv.piFinsetUnion Omega hJ_KL)
          (q.2.1, (Equiv.piFinsetUnion Omega hKL) (q.2.2.1, q.2.2.2))
          ⟨i, Finset.mem_union_right J (Finset.mem_union_right K hi)⟩ :=
        Equiv.piFinsetUnion_right Omega hI_JKL
          (Finset.mem_union_right J (Finset.mem_union_right K hi)) _
      _ = (Equiv.piFinsetUnion Omega hKL) (q.2.2.1, q.2.2.2)
          ⟨i, Finset.mem_union_right K hi⟩ :=
        Equiv.piFinsetUnion_right Omega hJ_KL (Finset.mem_union_right K hi) _
      _ = q.2.2.2 ⟨i, hi⟩ := Equiv.piFinsetUnion_right Omega hKL hi _

private theorem map_permuted_fourBlockProjection_pi
    {n : ℕ} (I J K L : Finset (Fin n))
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hIL : Disjoint I L)
    (hJK : Disjoint J K) (hJL : Disjoint J L) (hKL : Disjoint K L)
    (pi : Equiv.Perm (Fin n)) (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    (Measure.pi fun _ : Fin n ↦ mu).map
        (fun v ↦
          (familyProjection (fun e w ↦ w (pi e)) I v,
            (familyProjection (fun e w ↦ w (pi e)) J v,
              (familyProjection (fun e w ↦ w (pi e)) K v,
                familyProjection (fun e w ↦ w (pi e)) L v)))) =
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockReference
        (Measure.pi fun _ : I ↦ mu) (Measure.pi fun _ : J ↦ mu)
        (Measure.pi fun _ : K ↦ mu) (Measure.pi fun _ : L ↦ mu) := by
  let S := CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockIndices I J K L
  let e := fourBlockValuesEquiv_local (Omega := fun _ : Fin n ↦ ℝ) I J K L hKL
    (Finset.disjoint_union_right.mpr ⟨hJK, hJL⟩)
    (Finset.disjoint_union_right.mpr
      ⟨hIJ, Finset.disjoint_union_right.mpr ⟨hIK, hIL⟩⟩)
  let F : (Fin n → ℝ) → CausalSmith.Substrate.PositiveDensityCondindepIntersection.FourBlock
      (ValuesOn I (fun _ ↦ ℝ)) (ValuesOn J (fun _ ↦ ℝ))
      (ValuesOn K (fun _ ↦ ℝ)) (ValuesOn L (fun _ ↦ ℝ)) :=
    fun v ↦
      (familyProjection (fun a w ↦ w (pi a)) I v,
        (familyProjection (fun a w ↦ w (pi a)) J v,
          (familyProjection (fun a w ↦ w (pi a)) K v,
            familyProjection (fun a w ↦ w (pi a)) L v)))
  let R : (Fin n → ℝ) → ValuesOn S (fun _ ↦ ℝ) :=
    fun v a ↦ v (pi a)
  have hF : Measurable F := by
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ fun a ↦ measurable_pi_apply _
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ fun a ↦ measurable_pi_apply _
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ fun a ↦ measurable_pi_apply _
    · exact measurable_pi_lambda _ fun a ↦ measurable_pi_apply _
  have hR : Measurable R := measurable_pi_lambda _ fun a ↦ measurable_pi_apply _
  have heF : e ∘ F = R := by
    funext v
    ext a
    have happ := fourBlockValuesEquiv_local_apply I J K L hIJ hIK hIL hJK hJL hKL (F v)
    by_cases haI : (a : Fin n) ∈ I
    · simpa only [e, F, R, Function.comp_apply, familyProjection] using happ.1 a haI
    by_cases haJ : (a : Fin n) ∈ J
    · simpa only [e, F, R, Function.comp_apply, familyProjection] using happ.2.1 a haJ
    by_cases haK : (a : Fin n) ∈ K
    · simpa only [e, F, R, Function.comp_apply, familyProjection] using happ.2.2.1 a haK
    · have haL : (a : Fin n) ∈ L := by
        simpa only [S,
          CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockIndices,
          Finset.mem_union, haI, haJ, haK, false_or] using a.2
      simpa only [e, F, R, Function.comp_apply, familyProjection] using happ.2.2.2 a haL
  have hperm : (Measure.pi fun _ : Fin n ↦ mu).map
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) pi) =
        Measure.pi fun _ : Fin n ↦ mu := by
    simpa using Measure.pi_map_piCongrLeft pi (fun _ : Fin n ↦ mu)
  have hrestrict : (Measure.pi fun _ : Fin n ↦ mu).map S.restrict =
      Measure.pi fun _ : S ↦ mu := by
    simpa [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_restrict (μ := fun _ : Fin n ↦ mu) (I := S))
  have hRmap : (Measure.pi fun _ : Fin n ↦ mu).map R = Measure.pi fun _ : S ↦ mu := by
    let p := MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) pi
    have hp : Measurable p := p.measurable
    have hcomp : R ∘ p = S.restrict := by
      funext v
      ext a
      simp only [R, p, Function.comp_apply, Finset.restrict]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
      simp
    calc
      (Measure.pi fun _ : Fin n ↦ mu).map R =
          ((Measure.pi fun _ : Fin n ↦ mu).map p).map R := by rw [hperm]
      _ = (Measure.pi fun _ : Fin n ↦ mu).map (R ∘ p) :=
        Measure.map_map hR hp
      _ = (Measure.pi fun _ : Fin n ↦ mu).map S.restrict := by rw [hcomp]
      _ = Measure.pi fun _ : S ↦ mu := hrestrict
  have hepres := measurePreserving_fourBlockValuesEquiv_local
    I J K L hIJ hIK hIL hJK hJL hKL (fun _ ↦ mu)
  change (Measure.pi fun _ : Fin n ↦ mu).map F = _
  apply e.measurableEmbedding.map_injective
  rw [Measure.map_map e.measurable hF, heF, hRmap, hepres.map_eq]
  rfl

private noncomputable def singletonValuesEquiv (n : ℕ) (i : Fin n) :
    ValuesOn ({i} : Finset (Fin n)) (fun _ ↦ ℝ) ≃ᵐ ℝ where
  toFun x := x ⟨i, Finset.mem_singleton_self i⟩
  invFun r := fun _ ↦ r
  left_inv x := by
    ext a
    exact congrArg x (Subsingleton.elim ⟨i, Finset.mem_singleton_self i⟩ a)
  right_inv _ := rfl
  measurable_toFun := measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ ↦ measurable_id

private theorem map_permuted_scalar_fourBlockProjection_pi
    {n : ℕ} (i b : Fin n) (C Z : Finset (Fin n))
    (hib : i ≠ b) (hiC : i ∉ C) (hiZ : i ∉ Z)
    (hbC : b ∉ C) (hbZ : b ∉ Z) (hCZ : Disjoint C Z)
    (pi : Equiv.Perm (Fin n)) (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    (Measure.pi fun _ : Fin n ↦ mu).map
        (fun v ↦
          (v (pi i), (v (pi b),
            (familyProjection (fun e w ↦ w (pi e)) C v,
              familyProjection (fun e w ↦ w (pi e)) Z v)))) =
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockReference
        mu mu (Measure.pi fun _ : C ↦ mu) (Measure.pi fun _ : Z ↦ mu) := by
  let I : Finset (Fin n) := {i}
  let J : Finset (Fin n) := {b}
  have hIJ : Disjoint I J := by simp [I, J, hib]
  have hIC : Disjoint I C := by simp [I, hiC]
  have hIZ : Disjoint I Z := by simp [I, hiZ]
  have hJC : Disjoint J C := by simp [J, hbC]
  have hJZ : Disjoint J Z := by simp [J, hbZ]
  have hblock := map_permuted_fourBlockProjection_pi I J C Z
    hIJ hIC hIZ hJC hJZ hCZ pi mu
  let eI := singletonValuesEquiv n i
  let eJ := singletonValuesEquiv n b
  let e := MeasurableEquiv.prodCongr eI
    (MeasurableEquiv.prodCongr eJ
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl (ValuesOn C (fun _ ↦ ℝ)))
        (MeasurableEquiv.refl (ValuesOn Z (fun _ ↦ ℝ)))))
  have heI : MeasurePreserving eI (Measure.pi fun _ : I ↦ mu) mu := by
    simpa [eI, I, singletonValuesEquiv] using
      (measurePreserving_eval (fun _ : I ↦ mu) ⟨i, Finset.mem_singleton_self i⟩)
  have heJ : MeasurePreserving eJ (Measure.pi fun _ : J ↦ mu) mu := by
    simpa [eJ, J, singletonValuesEquiv] using
      (measurePreserving_eval (fun _ : J ↦ mu) ⟨b, Finset.mem_singleton_self b⟩)
  have he : MeasurePreserving e
      (CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockReference
        (Measure.pi fun _ : I ↦ mu) (Measure.pi fun _ : J ↦ mu)
        (Measure.pi fun _ : C ↦ mu) (Measure.pi fun _ : Z ↦ mu))
      (CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockReference
        mu mu (Measure.pi fun _ : C ↦ mu) (Measure.pi fun _ : Z ↦ mu)) := by
    exact heI.prod (heJ.prod
      ((MeasurePreserving.id (Measure.pi fun _ : C ↦ mu)).prod
        (MeasurePreserving.id (Measure.pi fun _ : Z ↦ mu))))
  rw [← he.map_eq, ← hblock, Measure.map_map]
  · congr 1
  · exact e.measurable
  · exact
      (measurable_pi_lambda _ fun _ : I ↦ measurable_pi_apply _).prodMk
        ((measurable_pi_lambda _ fun _ : J ↦ measurable_pi_apply _).prodMk
          ((measurable_pi_lambda _ fun _ : C ↦ measurable_pi_apply _).prodMk
            (measurable_pi_lambda _ fun _ : Z ↦ measurable_pi_apply _)))

/-- Positivity-based graphoid intersection for four disjoint latent-coordinate blocks on the
paper's full product support.  The disjointness hypotheses are the internal DAG bookkeeping used
in equations (15)--(18); they are not assumptions of the delivered decoder theorem.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hib,hiC,hiZ,hbC,hbZ,hCZ,h₁,h₂), [the stated conclusion](goal) follows. -/
-- @node: condIndep_intersection_of_pos
lemma condIndep_intersection_of_pos
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (i b : Fin n) (C Z : Finset (Fin n))
    (hib : i ≠ b) (hiC : i ∉ C) (hiZ : i ∉ Z)
    (hbC : b ∉ C) (hbZ : b ∉ Z) (hCZ : Disjoint C Z)
    (h₁ : CondIndepGiven (W.law 0)
      (observedLatentCoordinate W i)
      (observedLatentCoordinate W b)
      (fun x =>
        (familyProjection (observedLatentCoordinate W) Z x,
          familyProjection (observedLatentCoordinate W) C x)))
    (h₂ : CondIndepGiven (W.law 0)
      (observedLatentCoordinate W i)
      (familyProjection (observedLatentCoordinate W) C)
      (fun x =>
        (familyProjection (observedLatentCoordinate W) Z x,
          observedLatentCoordinate W b x))) :
    CondIndepGiven (W.law 0)
        (observedLatentCoordinate W i)
        (observedLatentCoordinate W b)
        (familyProjection (observedLatentCoordinate W) Z) ∧
      CondIndepGiven (W.law 0)
        (observedLatentCoordinate W i)
        (fun x =>
          (observedLatentCoordinate W b x,
            familyProjection (observedLatentCoordinate W) C x))
        (familyProjection (observedLatentCoordinate W) Z) := by
  classical
  let unit : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  letI : IsProbabilityMeasure unit := ⟨by simp [unit, Real.volume_Icc]⟩
  let ref := CausalSmith.Substrate.PositiveDensityCondindepIntersection.fourBlockReference
    unit unit (Measure.pi fun _ : C ↦ unit) (Measure.pi fun _ : Z ↦ unit)
  let Fobs : LatentState n →
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.FourBlock
        ℝ ℝ (ValuesOn C (fun _ ↦ ℝ)) (ValuesOn Z (fun _ ↦ ℝ)) :=
    fun x ↦ (observedLatentCoordinate W i x, (observedLatentCoordinate W b x,
      (familyProjection (observedLatentCoordinate W) C x,
        familyProjection (observedLatentCoordinate W) Z x)))
  let Flat : LatentState n →
      CausalSmith.Substrate.PositiveDensityCondindepIntersection.FourBlock
        ℝ ℝ (ValuesOn C (fun _ ↦ ℝ)) (ValuesOn Z (fun _ ↦ ℝ)) :=
    fun v ↦ (v (W.targetPerm i), (v (W.targetPerm b),
      (familyProjection (fun e w ↦ w (W.targetPerm e)) C v,
        familyProjection (fun e w ↦ w (W.targetPerm e)) Z v)))
  rcases h₁ with ⟨hfinite, hUi, hUb, hZC, hCI₁⟩
  letI : IsFiniteMeasure (W.law 0) := hfinite
  rcases h₂ with ⟨_, _, hUC, hZb, hCI₂⟩
  have hUZ : Measurable (familyProjection (observedLatentCoordinate W) Z) :=
    measurable_fst.comp hZC
  have hUC' : Measurable (familyProjection (observedLatentCoordinate W) C) :=
    measurable_snd.comp hZC
  have hFobs : Measurable Fobs := hUi.prodMk (hUb.prodMk (hUC'.prodMk hUZ))
  have hFlat : Measurable Flat :=
    (measurable_pi_apply _).prodMk ((measurable_pi_apply _).prodMk
      ((measurable_pi_lambda _ fun _ : C ↦ measurable_pi_apply _).prodMk
        (measurable_pi_lambda _ fun _ : Z ↦ measurable_pi_apply _)))
  let fullRef : Measure (LatentState n) := Measure.pi fun _ : Fin n ↦ unit
  have hcubeRef : volume.restrict (latentCube n) = fullRef := by
    change volume.restrict (Set.univ.pi fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1) = _
    rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
  let dens : LatentState n → ENNReal := fun v ↦ ENNReal.ofReal (observationalDensity θ v)
  have hdensOn : ContinuousOn dens (latentCube n) := by
    apply ENNReal.continuous_ofReal.comp_continuousOn
    unfold observationalDensity
    exact continuousOn_finset_prod _ fun k _ ↦ (hpos.2.2.1 k).continuousOn
  have hcube : MeasurableSet (latentCube n) := by
    rw [latentCube]
    measurability
  have hdensAE : AEMeasurable dens (volume.restrict (latentCube n)) :=
    aemeasurable_restrict_of_measurable_subtype hcube hdensOn.restrict.measurable
  have hdens_ne : ∀ᵐ v ∂volume.restrict (latentCube n), dens v ≠ 0 := by
    filter_upwards [ae_restrict_mem hcube] with v hv
    have hp : 0 < observationalDensity θ v := by
      unfold observationalDensity
      exact Finset.prod_pos fun k _ ↦ hpos.1 k v hv
    exact (ENNReal.ofReal_pos.mpr hp).ne'
  have hobs_forward : observationalLaw θ ≪ fullRef := by
    rw [← hcubeRef]
    exact withDensity_absolutelyContinuous _ _
  have hobs_reverse : fullRef ≪ observationalLaw θ := by
    rw [← hcubeRef]
    exact withDensity_absolutelyContinuous' hdensAE hdens_ne
  have hFlatRef : Measure.map Flat fullRef = ref := by
    simpa only [Flat, fullRef, ref] using
      (map_permuted_scalar_fourBlockProjection_pi i b C Z hib hiC hiZ hbC hbZ hCZ
        W.targetPerm unit)
  have hlatent_forward : Measure.map Flat (observationalLaw θ) ≪ ref := by
    rw [← hFlatRef]
    exact @Measure.AbsolutelyContinuous.map _ _ _ _ _ _ hobs_forward Flat hFlat
  have hlatent_reverse : ref ≪ Measure.map Flat (observationalLaw θ) := by
    rw [← hFlatRef]
    exact @Measure.AbsolutelyContinuous.map _ _ _ _ _ _ hobs_reverse Flat hFlat
  have hobs_cube : observationalLaw θ (latentCube n)ᶜ = 0 :=
    hobs_forward (by
      rw [← hcubeRef, Measure.restrict_apply hcube.compl]
      simp)
  have hcube_ae : ∀ᵐ v ∂observationalLaw θ, v ∈ latentCube n := by
    rw [ae_iff]
    change observationalLaw θ (latentCube n)ᶜ = 0
    exact hobs_cube
  let mix' : LatentState n → LatentState n :=
    (latentCube n).piecewise W.mix (fun _ ↦ 0)
  have hmix' : Measurable mix' := by
    exact hmix.1.continuousOn.measurable_piecewise continuous_const.continuousOn hcube
  have hmix_eq : W.mix =ᵐ[observationalLaw θ] mix' := by
    filter_upwards [hcube_ae] with v hv
    simp [mix', Set.piecewise, hv]
  have hcomp : Fobs ∘ mix' =ᵐ[observationalLaw θ] Flat := by
    filter_upwards [hmix_eq, hcube_ae] with v hmv hv
    change Fobs (mix' v) = Flat v
    rw [← hmv]
    have hinv := hmix.2.2.1 v hv
    simp only [Fobs, Flat, Function.comp_apply, familyProjection]
    apply Prod.ext
    · exact observedLatentCoordinate_mix W hmix i v hv
    apply Prod.ext
    · exact observedLatentCoordinate_mix W hmix b v hv
    apply Prod.ext
    · funext a
      exact observedLatentCoordinate_mix W hmix a v hv
    · funext a
      exact observedLatentCoordinate_mix W hmix a v hv
  have hlaw : W.law 0 = Measure.map mix' (observationalLaw θ) := by
    rw [hone.1]
    exact Measure.map_congr hmix_eq
  have hjoint : Measure.map Fobs (W.law 0) = Measure.map Flat (observationalLaw θ) := by
    rw [hlaw]
    calc
      Measure.map Fobs (Measure.map mix' (observationalLaw θ)) =
          Measure.map (Fobs ∘ mix') (observationalLaw θ) :=
        Measure.map_map hFobs hmix'
      _ = Measure.map Flat (observationalLaw θ) := Measure.map_congr hcomp
  have hforward : Measure.map Fobs (W.law 0) ≪ ref := by
    rw [hjoint]
    exact hlatent_forward
  have hreverse : ref ≪ Measure.map Fobs (W.law 0) := by
    rw [hjoint]
    exact hlatent_reverse
  apply condIndepGiven_intersection_of_equivalent_fourBlock
    (observedLatentCoordinate W i) (observedLatentCoordinate W b)
    (familyProjection (observedLatentCoordinate W) C)
    (familyProjection (observedLatentCoordinate W) Z)
    hUi hUb hUC' hUZ unit unit (Measure.pi fun _ : C ↦ unit)
      (Measure.pi fun _ : Z ↦ unit) hforward hreverse
  · exact ⟨hfinite, hUi, hUb, hZC, hCI₁⟩
  · exact ⟨hfinite, hUi, hUC, hZb, hCI₂⟩

/-- Coordinate-pair presentation of generic weak union for a finite family of measurable maps.  Given [the stated inputs and conditions](hyp:hU,hA,hb,hbA,hCI), [the stated conclusion](goal) follows. -/
-- @node: condIndep_coordSplit_prodMk
lemma condIndep_coordSplit_prodMk
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {n : ℕ} (U : Fin n → Ω → ℝ) (i b : Fin n) (A S : Finset (Fin n))
    (hU : ∀ c, Measurable (U c))
    (hA : A ⊆ S) (hb : b ∈ S) (hbA : b ∉ A)
    (hCI : CondIndepGiven μ (U i)
      (familyProjection U (S \ A)) (familyProjection U A)) :
    (MeasurableSpace.comap (familyProjection U A) inferInstance ⊔
        MeasurableSpace.comap (familyProjection U ((S \ A).erase b)) inferInstance =
      MeasurableSpace.comap (familyProjection U (S.erase b)) inferInstance) ∧
    CondIndepGiven μ (U i) (U b) (familyProjection U (S.erase b)) := by
  have hproj (T : Finset (Fin n)) : Measurable (familyProjection U T) := by
    apply measurable_pi_lambda
    intro j
    exact hU j
  have hbDiff : b ∈ S \ A := Finset.mem_sdiff.mpr ⟨hb, hbA⟩
  let split : ((j : {j // j ∈ S \ A}) → ℝ) →
      ℝ × ((j : {j // j ∈ (S \ A).erase b}) → ℝ) :=
    fun x => (x ⟨b, hbDiff⟩, fun j => x ⟨j, Finset.mem_sdiff.mpr
      (Finset.mem_sdiff.mp (Finset.mem_erase.mp j.2).2)⟩)
  have hsplit : Measurable split := by
    apply Measurable.prod
    · exact measurable_pi_apply _
    · apply measurable_pi_lambda
      intro j
      exact measurable_pi_apply _
  have hCIpair : CondIndepGiven μ (U i)
      (fun ω => (U b ω, familyProjection U ((S \ A).erase b) ω))
      (familyProjection U A) := by
    rcases hCI with ⟨hμ, hXi, hY, hZA, hCI⟩
    refine ⟨hμ, hXi, (hU b).prod (hproj _), hZA, ?_⟩
    convert hCI.comp measurable_id hsplit using 1 <;>
      ext ω j <;> rfl
  have hsigma :
      MeasurableSpace.comap (familyProjection U A) inferInstance ⊔
          MeasurableSpace.comap (familyProjection U ((S \ A).erase b)) inferInstance =
        MeasurableSpace.comap (familyProjection U (S.erase b)) inferInstance := by
    apply le_antisymm
    · apply sup_le
      · have hm : @Measurable Ω _
            (MeasurableSpace.comap (familyProjection U (S.erase b)) inferInstance)
            inferInstance (familyProjection U A) := by
          letI : MeasurableSpace Ω :=
            MeasurableSpace.comap (familyProjection U (S.erase b)) inferInstance
          refine measurable_pi_lambda _ (fun j => ?_)
          have hjS : (j : Fin n) ∈ S.erase b := Finset.mem_erase.mpr
            ⟨by intro h; subst b; exact hbA j.2, hA j.2⟩
          have heval : Measurable (fun x : ((j : {j // j ∈ S.erase b}) → ℝ) =>
              x ⟨j, hjS⟩) := measurable_pi_apply _
          convert heval.comp (Measurable.of_comap_le le_rfl) using 1
          funext c
          rfl
        exact hm.comap_le
      · have hm : @Measurable Ω _
            (MeasurableSpace.comap (familyProjection U (S.erase b)) inferInstance)
            inferInstance (familyProjection U ((S \ A).erase b)) := by
          letI : MeasurableSpace Ω :=
            MeasurableSpace.comap (familyProjection U (S.erase b)) inferInstance
          refine measurable_pi_lambda _ (fun j => ?_)
          have hjS : (j : Fin n) ∈ S.erase b := by
            rcases Finset.mem_erase.mp j.2 with ⟨hjb, hjSA⟩
            exact Finset.mem_erase.mpr ⟨hjb, (Finset.mem_sdiff.mp hjSA).1⟩
          have heval : Measurable (fun x : ((j : {j // j ∈ S.erase b}) → ℝ) =>
              x ⟨j, hjS⟩) := measurable_pi_apply _
          convert heval.comp (Measurable.of_comap_le le_rfl) using 1
          funext c
          rfl
        exact hm.comap_le
    · have hm : @Measurable Ω _
          (MeasurableSpace.comap (familyProjection U A) inferInstance ⊔
            MeasurableSpace.comap (familyProjection U ((S \ A).erase b)) inferInstance)
          inferInstance (familyProjection U (S.erase b)) := by
        letI : MeasurableSpace Ω :=
          MeasurableSpace.comap (familyProjection U A) inferInstance ⊔
            MeasurableSpace.comap (familyProjection U ((S \ A).erase b)) inferInstance
        refine measurable_pi_lambda _ (fun j => ?_)
        rcases Finset.mem_erase.mp j.2 with ⟨hjb, hjS⟩
        by_cases hjA : (j : Fin n) ∈ A
        · have heval : Measurable (fun x : ((j : {j // j ∈ A}) → ℝ) =>
              x ⟨j, hjA⟩) := measurable_pi_apply _
          convert heval.comp (Measurable.of_comap_le le_sup_left) using 1
          funext c
          rfl
        · have hjRest : (j : Fin n) ∈ (S \ A).erase b :=
            Finset.mem_erase.mpr ⟨hjb, Finset.mem_sdiff.mpr ⟨hjS, hjA⟩⟩
          have heval : Measurable
              (fun x : ((j : {j // j ∈ (S \ A).erase b}) → ℝ) =>
                x ⟨j, hjRest⟩) := measurable_pi_apply _
          convert heval.comp (Measurable.of_comap_le le_sup_right) using 1
          funext c
          rfl
      exact hm.comap_le
  refine ⟨hsigma, ?_⟩
  rcases hCIpair with ⟨hμ, hXi, hPair, hZA, hCIpair⟩
  refine ⟨hμ, hXi, hU b, hproj _, ?_⟩
  have hraw := condIndepFun_weak_union_of_prodMk hZA.comap_le
    (hU i) (hU b) (hproj ((S \ A).erase b)) hCIpair
  simpa only [hsigma] using hraw

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

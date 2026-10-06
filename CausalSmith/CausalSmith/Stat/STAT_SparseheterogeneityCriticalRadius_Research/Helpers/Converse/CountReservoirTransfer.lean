module
public import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.FinitePoissonHistogram
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.FixedSampleTransfer
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction.Reconstruction
public import Causalean.Stat.Minimax.MarkovKernelTransport
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Product

/-! Common-reservoir augmentation and reconstruction contraction. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer
open scoped ENNReal NNReal

/-- The reservoir has four hypothesis-independent marks, each with Poisson
mean `n/2` under exposure `2n` and raw reservoir mass one. -/
@[no_expose]
noncomputable def reservoirSignedScoreLaw (n : ℕ) : Measure SignedScoreCounts :=
  signedScorePoissonLaw (fun _ => (n : ℝ) / 2)

instance reservoirSignedScoreLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (reservoirSignedScoreLaw n) := by
  unfold reservoirSignedScoreLaw
  exact signedScorePoissonLaw_isProbabilityMeasure _

/-- Read one of the four scalar counts from the paired representation used by
the chi-square calculation. -/
@[no_expose]
def signedScoreCountAt (z : SignedScoreCounts) (i : Fin 4) : ℕ :=
  if i = 0 then z.1.1
  else if i = 1 then z.1.2
  else if i = 2 then z.2.1
  else z.2.2

/-- Singleton probabilities of the nested four-count representation factor
coordinatewise. -/
lemma signedScorePoissonLaw_singleton (v : Fin 4 → ℝ)
    (z : SignedScoreCounts) :
    signedScorePoissonLaw v {z} =
      ∏ i : Fin 4,
        poissonMeasure (Real.toNNReal (v i)) {signedScoreCountAt z i} := by
  rcases z with ⟨⟨z0, z1⟩, ⟨z2, z3⟩⟩
  rw [signedScorePoissonLaw_singleton_expanded]
  rw [Fin.prod_univ_four]
  simp [signedScoreCountAt]

/-- Reshape all rare four-count blocks and the last reservoir block into the
histogram indexed by cell and mark. -/
@[no_expose]
def signedScoreReservoirHistogram (n : ℕ) :
    ((Fin (n - 1) → SignedScoreCounts) × SignedScoreCounts) →
      (Fin n × Fin 4 → ℕ) := fun z ki =>
  if hk : ki.1.val < n - 1 then
    signedScoreCountAt (z.1 ⟨ki.1.val, hk⟩) ki.2
  else signedScoreCountAt z.2 ki.2

/-- Embed a rare-cell index in the full design, whose final cell is reserved
for the common reservoir. -/
@[no_expose]
def rareCellEmbedding (n : ℕ) (k : Fin (n - 1)) : Fin n :=
  ⟨k.val, by omega⟩

/-- The final design cell is the unit-mass common reservoir. -/
@[no_expose]
def reservoirCell (n : ℕ) (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

/-- Reassemble the nested four-count representation from four coordinates. -/
@[no_expose]
def signedScoreCountsOf (c : Fin 4 → ℕ) : SignedScoreCounts :=
  ((c 0, c 1), (c 2, c 3))

/-- Inverse reshape for a positive-dimensional rare-plus-reservoir histogram. -/
@[no_expose]
def signedScoreReservoirHistogramInv (n : ℕ) (hn : 0 < n)
    (c : Fin n × Fin 4 → ℕ) :
    (Fin (n - 1) → SignedScoreCounts) × SignedScoreCounts :=
  (fun k => signedScoreCountsOf (fun i => c (rareCellEmbedding n k, i)),
    signedScoreCountsOf (fun i => c (reservoirCell n hn, i)))

lemma signedScoreCountAt_countsOf (c : Fin 4 → ℕ) (i : Fin 4) :
    signedScoreCountAt (signedScoreCountsOf c) i = c i := by
  fin_cases i <;> simp [signedScoreCountAt, signedScoreCountsOf]

lemma signedScoreReservoirHistogram_leftInverse (n : ℕ) (hn : 0 < n) :
    Function.LeftInverse (signedScoreReservoirHistogramInv n hn)
      (signedScoreReservoirHistogram n) := by
  intro z
  rcases z with ⟨zr, zR⟩
  apply Prod.ext
  · funext k
    rcases h : zr k with ⟨⟨z0, z1⟩, ⟨z2, z3⟩⟩
    simp [signedScoreReservoirHistogramInv, signedScoreCountsOf,
      signedScoreReservoirHistogram, rareCellEmbedding,
      signedScoreCountAt]
  · rcases zR with ⟨⟨z0, z1⟩, ⟨z2, z3⟩⟩
    simp [signedScoreReservoirHistogramInv, signedScoreCountsOf,
      signedScoreReservoirHistogram, reservoirCell, signedScoreCountAt]

lemma signedScoreReservoirHistogram_rightInverse (n : ℕ) (hn : 0 < n) :
    Function.RightInverse (signedScoreReservoirHistogramInv n hn)
      (signedScoreReservoirHistogram n) := by
  intro c
  funext ki
  rcases ki with ⟨k, i⟩
  by_cases hk : k.val < n - 1
  · let kr : Fin (n - 1) := ⟨k.val, hk⟩
    have hemb : rareCellEmbedding n kr = k := Fin.ext rfl
    simp [signedScoreReservoirHistogram, signedScoreReservoirHistogramInv,
      hk, kr, hemb, signedScoreCountAt_countsOf]
  · have hres : k = reservoirCell n hn := by
      apply Fin.ext
      simp [reservoirCell]
      omega
    subst k
    simp [signedScoreReservoirHistogram, signedScoreReservoirHistogramInv,
      reservoirCell, signedScoreCountAt_countsOf]

@[fun_prop] lemma signedScoreReservoirHistogram_measurable (n : ℕ) :
    Measurable (signedScoreReservoirHistogram n) := measurable_of_countable _

/-- Conditional rare-plus-reservoir count law before mixing the latent
intensities. -/
@[no_expose]
noncomputable def signedScoreConditionalHistogramLaw (n : ℕ)
    (v : Fin (n - 1) → Fin 4 → ℝ) : Measure (Fin n × Fin 4 → ℕ) :=
  Measure.map (signedScoreReservoirHistogram n)
    ((Measure.pi fun k : Fin (n - 1) => signedScorePoissonLaw (v k)).prod
      (reservoirSignedScoreLaw n))

/-- Coordinate intensity vector of the preceding conditional count law. -/
@[no_expose]
noncomputable def signedScoreConditionalFullIntensity (n : ℕ)
    (v : Fin (n - 1) → Fin 4 → ℝ) : Fin n × Fin 4 → ℝ := fun ki =>
  if hk : ki.1.val < n - 1 then v ⟨ki.1.val, hk⟩ ki.2
  else (n : ℝ) / 2

/-- The deterministic reshape of independent rare blocks and the reservoir is
the independent Poisson histogram with the concatenated intensity vector. -/
lemma signedScoreConditionalHistogramLaw_eq_pi (n : ℕ) (hn : 0 < n)
    (v : Fin (n - 1) → Fin 4 → ℝ) :
    signedScoreConditionalHistogramLaw n v =
      Measure.pi (fun ki : Fin n × Fin 4 =>
        poissonMeasure
          (Real.toNNReal (signedScoreConditionalFullIntensity n v ki))) := by
  let _ (k : Fin (n - 1)) : IsProbabilityMeasure
      (signedScorePoissonLaw (v k)) := signedScorePoissonLaw_isProbabilityMeasure _
  apply Measure.ext_of_singleton
  intro c
  rw [signedScoreConditionalHistogramLaw,
    Measure.map_apply (signedScoreReservoirHistogram_measurable n)
      (MeasurableSet.singleton c)]
  have hpre : signedScoreReservoirHistogram n ⁻¹' {c} =
      {signedScoreReservoirHistogramInv n hn c} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      rw [← hz]
      exact (signedScoreReservoirHistogram_leftInverse n hn z).symm
    · rintro rfl
      exact signedScoreReservoirHistogram_rightInverse n hn c
  rw [hpre]
  have hpair : ({signedScoreReservoirHistogramInv n hn c} : Set
      ((Fin (n - 1) → SignedScoreCounts) × SignedScoreCounts)) =
      {((signedScoreReservoirHistogramInv n hn c).1)} ×ˢ
        {((signedScoreReservoirHistogramInv n hn c).2)} := by
    ext z
    simp
  rw [hpair, Measure.prod_prod]
  rw [show ({(signedScoreReservoirHistogramInv n hn c).1} :
      Set (Fin (n - 1) → SignedScoreCounts)) =
      Set.univ.pi (fun k =>
        {(signedScoreReservoirHistogramInv n hn c).1 k}) by
      exact (Set.univ_pi_singleton _).symm,
    Measure.pi_pi]
  simp_rw [signedScorePoissonLaw_singleton]
  rw [show ({c} : Set (Fin n × Fin 4 → ℕ)) =
      Set.univ.pi (fun ki => {c ki}) by
      exact (Set.univ_pi_singleton _).symm,
    Measure.pi_pi]
  rw [reservoirSignedScoreLaw, signedScorePoissonLaw_singleton]
  cases n with
  | zero => omega
  | succ m =>
    simp only [Nat.succ_sub_one]
    rw [Fintype.prod_prod_type]
    have hsplit :
        (∏ x : Fin (m + 1), ∏ y : Fin 4,
          poissonMeasure
            (Real.toNNReal
              (signedScoreConditionalFullIntensity (m + 1) v (x, y)))
            {c (x, y)}) =
        (∏ x : Fin m, ∏ y : Fin 4,
          poissonMeasure
            (Real.toNNReal
              (signedScoreConditionalFullIntensity
                (m + 1) v (x.castSucc, y)))
            {c (x.castSucc, y)}) *
        ∏ y : Fin 4,
          poissonMeasure
            (Real.toNNReal
              (signedScoreConditionalFullIntensity
                (m + 1) v (Fin.last m, y)))
            {c (Fin.last m, y)} := Fin.prod_univ_castSucc _
    rw [hsplit]
    congr 1
    · apply Finset.prod_congr rfl
      intro k hk
      rw [Fin.prod_univ_four]
      simp [signedScoreConditionalFullIntensity,
        signedScoreReservoirHistogramInv, rareCellEmbedding,
        signedScoreCountAt_countsOf]
      rw [Fin.prod_univ_four]
      have hcell : (⟨k.val, by omega⟩ : Fin (m + 1)) = k.castSucc :=
        Fin.ext rfl
      rw [hcell]
    · rw [Fin.prod_univ_four]
      simp [signedScoreConditionalFullIntensity,
        signedScoreReservoirHistogramInv, reservoirCell,
        signedScoreCountAt_countsOf]
      rw [Fin.prod_univ_four]
      have hlast : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m :=
        Fin.ext rfl
      rw [hlast]

/-- Mixing a coordinatewise product kernel against a finite product prior is
the product of the one-coordinate predictive laws.  This is the arbitrary
latent-space version of the scalar theorem in `MomentMatched.Product`. -/
-- keep: generic product-kernel mixing identity used to audit latent predictive laws
lemma bind_productPrior_eq_pi_bind
    {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (d : ℕ) (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ X) [∀ theta, IsProbabilityMeasure (K theta)]
    (productKernel : Kernel (Fin d → Θ) (Fin d → X))
    (hfiber : ∀ theta, productKernel theta =
      Measure.pi fun i : Fin d => K (theta i)) :
    (Measure.pi (fun _ : Fin d => π)).bind productKernel =
      Measure.pi (fun _ : Fin d => π.bind K) := by
  let _ : IsProbabilityMeasure (π.bind K) :=
    isProbabilityMeasure_bind K.aemeasurable (ae_of_all _ fun theta => inferInstance)
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.bind_apply
    (MeasurableSet.pi Set.countable_univ fun i _ => hs i)
    productKernel.aemeasurable]
  simp_rw [hfiber, Measure.pi_pi]
  have hcoord_le (i : Fin d) (theta : Θ) : K theta (s i) ≤ 1 := by
    let _ : IsProbabilityMeasure (K theta) := inferInstance
    exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  have hfun_meas (i : Fin d) : Measurable fun theta => K theta (s i) :=
    K.measurable_coe (hs i)
  have hfun_top (i : Fin d) : ∀ theta, K theta (s i) < ⊤ := fun theta => by
    let _ : IsProbabilityMeasure (K theta) := inferInstance
    exact measure_lt_top _ _
  have hprod_meas : Measurable
      (fun theta : Fin d → Θ => ∏ i, K (theta i) (s i)) :=
    Finset.univ.measurable_prod fun i _ =>
      (hfun_meas i).comp (measurable_pi_apply i)
  have hprod_top : ∀ theta : Fin d → Θ,
      (∏ i, K (theta i) (s i)) < ⊤ := fun theta =>
    ENNReal.prod_lt_top fun i _ => hfun_top i (theta i)
  have hlhs_ne :
      (∫⁻ theta : Fin d → Θ, ∏ i, K (theta i) (s i)
        ∂Measure.pi fun _ : Fin d => π) ≠ ⊤ := by
    apply ne_of_lt
    refine (lintegral_le_const (c := 1) ?_).trans_lt ENNReal.one_lt_top
    exact Filter.Eventually.of_forall fun theta =>
      Finset.prod_le_one' fun i _ => hcoord_le i (theta i)
  have hrhs_ne : (∏ i, (π.bind K) (s i)) ≠ ⊤ :=
    (ENNReal.prod_lt_top fun i _ => measure_lt_top _ _).ne
  have hfactor :
      (∫ theta : Fin d → Θ, ∏ i, (K (theta i) (s i)).toReal
        ∂Measure.pi fun _ : Fin d => π) =
        ∏ i, ∫ x, (K x (s i)).toReal ∂π := by
    exact integral_fintype_prod_eq_prod
      (fun i theta => (K theta (s i)).toReal)
  have hcoord_int (i : Fin d) :
      (∫ theta, (K theta (s i)).toReal ∂π) =
        ((π.bind K) (s i)).toReal := by
    rw [Measure.bind_apply (hs i) K.aemeasurable]
    exact integral_toReal (hfun_meas i).aemeasurable
      (Filter.Eventually.of_forall (hfun_top i))
  apply (ENNReal.toReal_eq_toReal_iff' hlhs_ne hrhs_ne).mp
  rw [← integral_toReal hprod_meas.aemeasurable
    (Filter.Eventually.of_forall hprod_top)]
  simp_rw [ENNReal.toReal_prod]
  rw [hfactor]
  exact Finset.prod_congr rfl fun i _ => hcoord_int i

/-- Binding after a measurable pushforward equals binding the pulled-back
kernel; only almost-everywhere measurability on the pushed law is needed. -/
lemma bind_map_eq_bind_comp_ae
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (f : A → B)
    (κ : B → Measure C) (hf : Measurable f)
    (hκ : AEMeasurable κ (Measure.map f μ)) :
    (Measure.map f μ).bind κ = μ.bind (κ ∘ f) := by
  apply Measure.ext
  intro s hs
  have hκs : AEMeasurable (fun b => κ b s) (Measure.map f μ) :=
    (Measure.measurable_coe hs).comp_aemeasurable hκ
  rw [Measure.bind_apply hs hκ,
    Measure.bind_apply hs (hκ.comp_aemeasurable hf.aemeasurable)]
  exact lintegral_map' hκs hf.aemeasurable

/-- The existing one-cell signed-score mixture is equivalently the latent
one-cell prior bound directly through its conditional count law. -/
lemma signedScoreMixtureLaw_intensityPrior_eq_oneCell_bind
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    signedScoreMixtureLaw
        (signedScoreIntensityPrior kappa gamma rho a J D h) =
      (oneCellPrior a J D h).bind
        (fun z => signedScorePoissonLaw
          (signedScoreIntensity kappa gamma rho J z)) := by
  rw [signedScoreMixtureLaw_eq_bind, signedScoreIntensityPrior_eq_map]
  exact bind_map_eq_bind_comp_ae
    (oneCellPrior a J D h)
    (signedScoreIntensity kappa gamma rho J) signedScorePoissonLaw
    (signedScoreIntensity_measurable kappa gamma rho J)
    (signedScorePoissonLaw_aemeasurable_intensityPrior
      kappa gamma rho a J D h hkappa hgamma hrho ha hJ)

/-- The rare-cell product predictive law is the latent product prior mixed
through the coordinatewise conditional signed-score count law. -/
lemma signedScoreProductMixtureLaw_eq_latent_bind
    (n : ℕ) (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    signedScoreProductMixtureLaw (n - 1)
        (signedScoreIntensityPrior kappa gamma rho a J D h) =
      (latentProductPrior n a J D h).bind (fun theta =>
        Measure.pi fun k : Fin (n - 1) =>
          signedScorePoissonLaw
            (signedScoreIntensity kappa gamma rho J (theta k))) := by
  let π := oneCellPrior a J D h
  let f : LatentCell → Measure SignedScoreCounts := fun z =>
    signedScorePoissonLaw (signedScoreIntensity kappa gamma rho J z)
  obtain ⟨s, hs, hmem⟩ := oneCellPrior_ae_mem_finite a J D h
  let K := finiteSupportKernel f s hs referenceLatent
  let _ : ∀ z, IsProbabilityMeasure (f z) := fun z =>
    signedScorePoissonLaw_isProbabilityMeasure _
  let _ : IsProbabilityMeasure π :=
    oneCellPrior_isProbabilityMeasure a J D h ha hJ
  let _ : ∀ z, IsProbabilityMeasure (K z) :=
    finiteSupportKernel_isProbabilityMeasure f s hs referenceLatent
  let _ : IsMarkovKernel K := ⟨fun z => inferInstance⟩
  have hKf : K =ᵐ[π] f := hmem.mono fun z hz =>
    finiteSupportKernel_apply f s hs referenceLatent z hz
  have hone : π.bind K = signedScoreMixtureLaw
      (signedScoreIntensityPrior kappa gamma rho a J D h) := by
    calc
      π.bind K = π.bind f := Measure.bind_congr_right hKf
      _ = _ := (signedScoreMixtureLaw_intensityPrior_eq_oneCell_bind
        kappa gamma rho a J D h hkappa hgamma hrho ha hJ).symm
  have hall : ∀ᵐ theta ∂Measure.pi (fun _ : Fin (n - 1) => π),
      ∀ k, theta k ∈ s := by
    apply ae_all_iff.mpr
    intro k
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin (n - 1) => π) (i := k)).eventually hmem
  have hprod := Causalean.Stat.finProductKernel_comp_pi (n - 1) π K
  rw [signedScoreProductMixtureLaw_eq_pi]
  simp_rw [← hone]
  calc
    Measure.pi (fun _ : Fin (n - 1) => π.bind K) =
        Causalean.Stat.finProductKernel (n - 1) K ∘ₘ
          Measure.pi (fun _ : Fin (n - 1) => π) := hprod.symm
    _ = (Measure.pi (fun _ : Fin (n - 1) => π)).bind
        (fun theta => Measure.pi fun k : Fin (n - 1) => K (theta k)) := by
      apply Measure.bind_congr_right
      filter_upwards [] with theta
      exact Causalean.Stat.finProductKernel_apply (n - 1) K theta
    _ = (latentProductPrior n a J D h).bind (fun theta =>
        Measure.pi fun k : Fin (n - 1) => f (theta k)) := by
      rw [latentProductPrior_eq_pi]
      apply Measure.bind_congr_right
      filter_upwards [hall] with theta htheta
      congr 1
      funext k
      exact finiteSupportKernel_apply f s hs referenceLatent
        (theta k) (htheta k)

/-- Taking an independent product with a fixed probability measure commutes
with mixing a probability kernel. -/
lemma bind_prod_eq_bind_prod_kernel
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (K : Kernel A B)
    [IsProbabilityMeasure μ] [IsMarkovKernel K]
    (ν : Measure C) [IsProbabilityMeasure ν] :
    (K ∘ₘ μ).prod ν = (K ×ₖ Kernel.const A ν) ∘ₘ μ := by
  rw [← Measure.compProd_const, Measure.compProd_eq_comp_prod,
    Measure.comp_assoc, Kernel.prod_const_comp, Kernel.id_comp]

/-- A measurable deterministic postprocessing commutes with mixing a
probability kernel. -/
lemma map_bind_kernel
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (K : Kernel A B)
    [IsMarkovKernel K] (f : B → C) (hf : Measurable f) :
    Measure.map f (K ∘ₘ μ) = (K.map f) ∘ₘ μ := by
  exact Measure.map_comp μ K hf

@[fun_prop] lemma rawMassTotal_measurable (n J : ℕ) (kappa : ℝ) :
    Measurable (rawMassTotal n J kappa) := by
  unfold rawMassTotal rawRareMass
  apply Finset.measurable_sum
  intro k hk
  by_cases hki : k.val < n - 1
  · simp only [hki, dite_true]
    exact measurable_const.mul
      ((measurable_pi_apply (⟨k.val, hki⟩ : Fin (n - 1))).snd.fst)
  · simp only [hki, dite_false]
    exact measurable_const

/-- The actual common-reservoir count experiment, expressed on the finite
histogram carrier consumed by the reconstruction kernel. -/
@[no_expose]
noncomputable def signedScoreReservoirCountLaw (n : ℕ)
    (π : Measure (Fin 4 → ℝ)) : Measure (Fin n × Fin 4 → ℕ) :=
  Measure.map (signedScoreReservoirHistogram n)
    ((signedScoreProductMixtureLaw (n - 1) π).prod (reservoirSignedScoreLaw n))

/-- The rare-count mixture with its independent common reservoir is exactly
the latent mixture of the corresponding full histograms. -/
lemma signedScoreReservoirCountLaw_eq_latent_bind
    (n : ℕ) (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    signedScoreReservoirCountLaw n
        (signedScoreIntensityPrior kappa gamma rho a J D h) =
      (latentProductPrior n a J D h).bind (fun theta =>
        signedScoreConditionalHistogramLaw n (fun k =>
          signedScoreIntensity kappa gamma rho J (theta k))) := by
  let μ := latentProductPrior n a J D h
  let f : (Fin (n - 1) → LatentCell) →
      Measure (Fin (n - 1) → SignedScoreCounts) := fun theta =>
    Measure.pi fun k : Fin (n - 1) =>
      signedScorePoissonLaw
        (signedScoreIntensity kappa gamma rho J (theta k))
  obtain ⟨s, hs, hmem⟩ := latentProductPrior_ae_mem_finite
    n a J D h ha hJ
  let K := finiteSupportKernel f s hs (fun _ => referenceLatent)
  let _ : IsProbabilityMeasure μ :=
    latentProductPrior_isProbabilityMeasure n a J D h ha hJ
  let _ : ∀ theta, IsProbabilityMeasure (f theta) := fun theta => by
    let _ (k : Fin (n - 1)) : IsProbabilityMeasure
        (signedScorePoissonLaw
          (signedScoreIntensity kappa gamma rho J (theta k))) :=
      signedScorePoissonLaw_isProbabilityMeasure _
    infer_instance
  let _ : ∀ theta, IsProbabilityMeasure (K theta) :=
    finiteSupportKernel_isProbabilityMeasure f s hs (fun _ => referenceLatent)
  let _ : IsMarkovKernel K := ⟨fun theta => inferInstance⟩
  have hKf : K =ᵐ[μ] f := hmem.mono fun theta htheta =>
    finiteSupportKernel_apply f s hs (fun _ => referenceLatent) theta htheta
  have hrare : signedScoreProductMixtureLaw (n - 1)
      (signedScoreIntensityPrior kappa gamma rho a J D h) = K ∘ₘ μ := by
    rw [signedScoreProductMixtureLaw_eq_latent_bind
      n kappa gamma rho a J D h hkappa hgamma hrho ha hJ]
    exact (Measure.bind_congr_right hKf).symm
  rw [signedScoreReservoirCountLaw, hrare]
  rw [bind_prod_eq_bind_prod_kernel μ K (reservoirSignedScoreLaw n)]
  rw [map_bind_kernel μ (K ×ₖ Kernel.const _ (reservoirSignedScoreLaw n))
    (signedScoreReservoirHistogram n)
    (signedScoreReservoirHistogram_measurable n)]
  apply Measure.bind_congr_right
  filter_upwards [hKf] with theta htheta
  rw [Kernel.map_apply _ (signedScoreReservoirHistogram_measurable n),
    Kernel.prod_apply, Kernel.const_apply, htheta]
  rfl

/-- Decode the four count marks as control/treated observations with lower and
upper outcomes.  Marks `0,1` are control and `2,3` are treated. -/
@[no_expose]
noncomputable def signedScoreObservedMark (M : ℝ) {n : ℕ} :
    Fin n × Fin 4 → SampleObs n := fun ki =>
  { x := ki.1
    a := ki.2 = 2 ∨ ki.2 = 3
    y := if ki.2 = 0 ∨ ki.2 = 2 then -(M / 2) else M / 2 }

@[fun_prop] lemma signedScoreObservedMark_measurable (M : ℝ) (n : ℕ) :
    Measurable (signedScoreObservedMark M : Fin n × Fin 4 → SampleObs n) := by
  exact measurable_of_finite _

/-- Uniformly order a finite cell-by-mark histogram and decode its four marks
as observed records. -/
@[no_expose]
noncomputable def signedScoreHistogramReconstructionKernel (n : ℕ) (M : ℝ) :
    Kernel (Fin n × Fin 4 → ℕ) (FiniteSample (SampleObs n)) :=
  (Kernel.deterministic
      (finiteSampleMap (signedScoreObservedMark M))
      (measurable_finiteSampleMap _ (signedScoreObservedMark_measurable M n))) ∘ₖ
    histogramReconstructionKernel (Fin n × Fin 4)

instance signedScoreHistogramReconstructionKernel_isMarkovKernel
    (n : ℕ) (M : ℝ) :
    IsMarkovKernel (signedScoreHistogramReconstructionKernel n M) := by
  unfold signedScoreHistogramReconstructionKernel
  infer_instance

/-- The common reconstruction kernel promised in equation (78): reshape the
augmented counts and then apply the histogram reconstruction kernel. -/
@[no_expose]
noncomputable def signedScoreReservoirReconstructionKernel (n : ℕ) (M : ℝ) :
    Kernel ((Fin (n - 1) → SignedScoreCounts) × SignedScoreCounts)
      (FiniteSample (SampleObs n)) :=
  signedScoreHistogramReconstructionKernel n M ∘ₖ
      Kernel.deterministic (signedScoreReservoirHistogram n)
        (signedScoreReservoirHistogram_measurable n)

instance signedScoreReservoirReconstructionKernel_isMarkovKernel
    (n : ℕ) (M : ℝ) :
    IsMarkovKernel (signedScoreReservoirReconstructionKernel n M) := by
  unfold signedScoreReservoirReconstructionKernel
  infer_instance

/-- A probability law supported on the two endpoints is uniquely determined
at those endpoints by its mean. -/
lemma twoPoint_support_singleton_realMass
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (M m : ℝ) (hM : 0 < M)
    (hsupport : μ (({-(M / 2), M / 2} : Set ℝ)ᶜ) = 0)
    (hmean : ∫ y, y ∂μ = m) :
    μ.real {M / 2} = 1 / 2 + m / M ∧
      μ.real {-(M / 2)} = 1 / 2 - m / M := by
  have hne : -(M / 2) ≠ M / 2 := by linarith
  have hne' : M / 2 ≠ -(M / 2) := hne.symm
  have hmem : ∀ᵐ y ∂μ, y ∈ ({-(M / 2), M / 2} : Set ℝ) :=
    mem_ae_iff.mpr hsupport
  have htotal : μ.real {-(M / 2)} + μ.real {M / 2} = 1 := by
    rw [← measureReal_union (Set.disjoint_singleton.2 hne)
      (MeasurableSet.singleton _)]
    have hfull : μ ({-(M / 2), M / 2} : Set ℝ) = 1 := by
      have hadd := measure_add_measure_compl
        (μ := μ) (by measurability : MeasurableSet ({-(M / 2), M / 2} : Set ℝ))
      rw [hsupport, add_zero, measure_univ] at hadd
      exact hadd
    have hunion : ({-(M / 2)} : Set ℝ) ∪ {M / 2} =
        ({-(M / 2), M / 2} : Set ℝ) := by
      ext x
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hunion]
    change (μ ({-(M / 2), M / 2} : Set ℝ)).toReal = 1
    rw [hfull]
    norm_num
  have hmean' :
      m = -(M / 2) * μ.real {-(M / 2)} +
        (M / 2) * μ.real {M / 2} := by
    rw [← hmean]
    have hae : (fun y : ℝ => y) =ᵐ[μ]
        fun y => ({-(M / 2)} : Set ℝ).indicator (fun _ => -(M / 2)) y +
          ({M / 2} : Set ℝ).indicator (fun _ => M / 2) y := by
      filter_upwards [hmem] with y hy
      rcases hy with rfl | rfl
      · simp [hne]
      · simp [hne]
    rw [integral_congr_ae hae, integral_add]
    · rw [integral_indicator_const (-(M / 2)) (MeasurableSet.singleton _),
        integral_indicator_const (M / 2) (MeasurableSet.singleton _)]
      simp only [Measure.real, smul_eq_mul]
      ring
    · exact (integrable_const (c := -(M / 2))).indicator (MeasurableSet.singleton _)
    · exact (integrable_const (c := M / 2)).indicator (MeasurableSet.singleton _)
  constructor <;> field_simp [hM.ne'] <;> nlinarith

/-- Observable singleton mass in a finite real law factors into cell mass,
treatment probability, and the corresponding outcome singleton mass. -/
lemma observedLaw_singleton_realMass {d : ℕ}
    (P : DiscreteAteHeterogeneityFrontier.RealLaw d)
    (k : Fin d) (a : Bool) (y : ℝ) :
    P.observedLaw.real {{ x := k, a := a, y := y }} =
      P.cellMass k * (if a then P.propensity k else 1 - P.propensity k) *
        (P.outcomeLaw a k).real {y} := by
  have h := P.arm_outcome_factorization a k ({y} : Set ℝ)
    (MeasurableSet.singleton y)
  have hset : ({{ x := k, a := a, y := y }} : Set
      (DiscreteAteHeterogeneityFrontier.Obs d)) =
      {o | o.x = k ∧ o.a = a ∧ o.y ∈ ({y} : Set ℝ)} := by
    ext o
    simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro rfl
      simp
    · rintro ⟨hx, ha, hy⟩
      cases o
      simp_all
  rw [hset]
  simpa only [DiscreteAteHeterogeneityFrontier.realMass, Measure.real] using h.symm

/-- Under the selected latent-law specification, the support and conditional
mean determine both endpoint probabilities in every cell and arm. -/
lemma latentLawSpec_outcome_endpoint_realMass
    {n : ℕ} {M rho kappa gamma : ℝ} {J : ℕ}
    {theta : Fin (n - 1) → LatentCell}
    (P : DiscreteAteHeterogeneityFrontier.RealLaw n)
    (hspec : LatentLawSpec n M rho kappa gamma J theta P)
    (hM : 0 < M) (a : Bool) (k : Fin n) :
    (P.outcomeLaw a k).real {M / 2} =
        1 / 2 + P.outcomeMean a k / M ∧
      (P.outcomeLaw a k).real {-(M / 2)} =
        1 / 2 - P.outcomeMean a k / M := by
  let _ := P.outcome_isProbability a k
  rcases hspec with ⟨_, _, _, _, hsupp, _⟩
  exact twoPoint_support_singleton_realMass
    (P.outcomeLaw a k) M (P.outcomeMean a k) hM (hsupp a k)
      (P.outcomeMean_eq a k).symm

/-- The endpoint observation selected by an arm and an upper/lower bit. -/
@[no_expose]
noncomputable def signedScoreEndpointObs (M : ℝ) {n : ℕ}
    (k : Fin n) (a upper : Bool) :
    DiscreteAteHeterogeneityFrontier.Obs n :=
  ⟨k, a, if upper then M / 2 else -(M / 2)⟩

/-- The observable mass of either endpoint, expressed only through the three
quantities fixed by `LatentLawSpec`. -/
lemma latentLawSpec_observed_endpoint_realMass
    {n : ℕ} {M rho kappa gamma : ℝ} {J : ℕ}
    {theta : Fin (n - 1) → LatentCell}
    (P : DiscreteAteHeterogeneityFrontier.RealLaw n)
    (hspec : LatentLawSpec n M rho kappa gamma J theta P)
    (hM : 0 < M) (a : Bool) (k : Fin n) (upper : Bool) :
    P.observedLaw.real {signedScoreEndpointObs M k a upper} =
      P.cellMass k * (if a then P.propensity k else 1 - P.propensity k) *
        (if upper then 1 / 2 + P.outcomeMean a k / M
          else 1 / 2 - P.outcomeMean a k / M) := by
  unfold signedScoreEndpointObs
  rw [observedLaw_singleton_realMass]
  obtain ⟨hu, hl⟩ :=
    latentLawSpec_outcome_endpoint_realMass P hspec hM a k
  cases upper <;> simp_all

/-- The observed outcome itself is almost surely one of the two endpoint
marks.  This follows from the armwise support and factorization clauses, so it
does not inspect the chosen construction of the latent law. -/
lemma latentLawSpec_observed_ae_endpoint
    {n : ℕ} {M rho kappa gamma : ℝ} {J : ℕ}
    {theta : Fin (n - 1) → LatentCell}
    (P : DiscreteAteHeterogeneityFrontier.RealLaw n)
    (hspec : LatentLawSpec n M rho kappa gamma J theta P) :
    ∀ᵐ o ∂P.observedLaw, o.y ∈ ({-(M / 2), M / 2} : Set ℝ) := by
  rcases hspec with ⟨_, _, _, _, hsupp, _⟩
  let bad : Fin n → Bool → Set (DiscreteAteHeterogeneityFrontier.Obs n) :=
    fun k a => {o | o.x = k ∧ o.a = a ∧
      o.y ∈ ({-(M / 2), M / 2} : Set ℝ)ᶜ}
  have hbad (k : Fin n) (a : Bool) : P.observedLaw (bad k a) = 0 := by
    have hfac := P.arm_outcome_factorization a k
      (({-(M / 2), M / 2} : Set ℝ)ᶜ)
      ((by measurability) : MeasurableSet (({-(M / 2), M / 2} : Set ℝ)ᶜ))
    have hout : DiscreteAteHeterogeneityFrontier.realMass
        (P.outcomeLaw a k) (({-(M / 2), M / 2} : Set ℝ)ᶜ) = 0 := by
      simp [DiscreteAteHeterogeneityFrontier.realMass, hsupp a k]
    rw [hout, mul_zero] at hfac
    change P.observedLaw {o | o.x = k ∧ o.a = a ∧
      o.y ∈ ({-(M / 2), M / 2} : Set ℝ)ᶜ} = 0
    exact ((ENNReal.toReal_eq_zero_iff _).mp hfac.symm).resolve_right
      (MeasureTheory.measure_ne_top _ _)
  have hunion : P.observedLaw (⋃ k, ⋃ a, bad k a) = 0 :=
    measure_iUnion_null fun k => measure_iUnion_null fun a => hbad k a
  apply mem_ae_iff.mpr
  apply measure_mono_null _ hunion
  intro o ho
  simp only [Set.mem_compl_iff] at ho
  simp only [Set.mem_iUnion, bad]
  exact ⟨o.x, o.a, rfl, rfl, ho⟩

/-- Encode an endpoint-valued observation by its cell and one of four marks. -/
@[no_expose]
noncomputable def signedScoreObservedCode (M : ℝ) {n : ℕ} :
    SampleObs n → Fin n × Fin 4 := fun o =>
  (o.x, if o.a then
    if o.y = -(M / 2) then 2 else 3
  else if o.y = -(M / 2) then 0 else 1)

@[fun_prop] lemma signedScoreObservedCode_measurable (M : ℝ) (n : ℕ) :
    Measurable (signedScoreObservedCode M : SampleObs n → Fin n × Fin 4) := by
  have hcoord : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) := by
    rw [measurable_iff_comap_le]
    rfl
  have hx : Measurable (fun o : SampleObs n => o.x) := hcoord.fst
  have ha : Measurable (fun o : SampleObs n => o.a) := hcoord.snd.fst
  have hy : Measurable (fun o : SampleObs n => o.y) := hcoord.snd.snd
  have htreat : MeasurableSet {o : SampleObs n | o.a = true} :=
    ha (MeasurableSet.singleton true)
  have hlower : MeasurableSet {o : SampleObs n | o.y = -(M / 2)} :=
    hy (MeasurableSet.singleton (-(M / 2)))
  unfold signedScoreObservedCode
  exact hx.prodMk (Measurable.ite htreat
    (Measurable.ite hlower measurable_const measurable_const)
    (Measurable.ite hlower measurable_const measurable_const))

/-- On the endpoint support, decoding the four-mark code is the identity. -/
lemma signedScoreObservedMark_code_ae
    {n : ℕ} {M rho kappa gamma : ℝ} {J : ℕ}
    {theta : Fin (n - 1) → LatentCell}
    (P : DiscreteAteHeterogeneityFrontier.RealLaw n)
    (hspec : LatentLawSpec n M rho kappa gamma J theta P)
    (hM : 0 < M) :
    (fun o => signedScoreObservedMark M (signedScoreObservedCode M o))
      =ᵐ[P.observedLaw] id := by
  filter_upwards [latentLawSpec_observed_ae_endpoint P hspec] with o ho
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
  have hne : M / 2 ≠ -(M / 2) := by linarith
  rcases o with ⟨x, a, y⟩
  rcases ho with hy | hy
  · change y = -(M / 2) at hy
    subst y
    cases a <;> simp [signedScoreObservedCode, signedScoreObservedMark]
  · change y = M / 2 at hy
    subst y
    cases a <;> simp [signedScoreObservedCode, signedScoreObservedMark, hne]

/-- The finite mark law obtained by coding the selected observable law. -/
@[no_expose]
noncomputable def signedScoreObservedCodeLaw {n : ℕ} (M : ℝ)
    (P : DiscreteAteHeterogeneityFrontier.RealLaw n) :
    Measure (Fin n × Fin 4) :=
  Measure.map (signedScoreObservedCode M) P.observedLaw

instance signedScoreObservedCodeLaw_isProbabilityMeasure {n : ℕ} (M : ℝ)
    (P : DiscreteAteHeterogeneityFrontier.RealLaw n) :
    IsProbabilityMeasure (signedScoreObservedCodeLaw M P) := by
  unfold signedScoreObservedCodeLaw
  exact Measure.isProbabilityMeasure_map
    (signedScoreObservedCode_measurable M n).aemeasurable

/-- Decoding the finite mark law recovers the exact selected observable law. -/
lemma signedScoreObservedCodeLaw_map_decode
    {n : ℕ} {M rho kappa gamma : ℝ} {J : ℕ}
    {theta : Fin (n - 1) → LatentCell}
    (P : DiscreteAteHeterogeneityFrontier.RealLaw n)
    (hspec : LatentLawSpec n M rho kappa gamma J theta P)
    (hM : 0 < M) :
    Measure.map (signedScoreObservedMark M)
        (signedScoreObservedCodeLaw M P) = P.observedLaw := by
  rw [signedScoreObservedCodeLaw, Measure.map_map
    (signedScoreObservedMark_measurable M n)
    (signedScoreObservedCode_measurable M n)]
  calc
    Measure.map
        (signedScoreObservedMark M ∘ signedScoreObservedCode M) P.observedLaw =
        Measure.map id P.observedLaw := Measure.map_congr
          (signedScoreObservedMark_code_ae P hspec hM)
    _ = P.observedLaw := Measure.map_id

/-- Distinct four-marks decode to distinct observations when the two endpoints
are separated. -/
lemma signedScoreObservedMark_injective (n : ℕ) (M : ℝ) (hM : 0 < M) :
    Function.Injective
      (signedScoreObservedMark M : Fin n × Fin 4 → SampleObs n) := by
  have hne : -(M / 2) ≠ M / 2 := by linarith
  have hne' : M / 2 ≠ -(M / 2) := hne.symm
  apply (show Function.LeftInverse
    (signedScoreObservedCode M)
    (signedScoreObservedMark M : Fin n × Fin 4 → SampleObs n) by
      rintro ⟨k, i⟩
      fin_cases i <;>
        simp [signedScoreObservedCode, signedScoreObservedMark, hne']).injective

/-- Singleton masses of the finite code law are exactly the corresponding
observable singleton masses. -/
lemma signedScoreObservedCodeLaw_singleton_realMass
    {n : ℕ} {M rho kappa gamma : ℝ} {J : ℕ}
    {theta : Fin (n - 1) → LatentCell}
    (P : DiscreteAteHeterogeneityFrontier.RealLaw n)
    (hspec : LatentLawSpec n M rho kappa gamma J theta P)
    (hM : 0 < M) (ki : Fin n × Fin 4) :
    (signedScoreObservedCodeLaw M P).real {ki} =
      P.observedLaw.real {signedScoreObservedMark M ki} := by
  have hmap := signedScoreObservedCodeLaw_map_decode P hspec hM
  have happ := congrArg
    (fun μ : Measure (SampleObs n) => μ {signedScoreObservedMark M ki}) hmap
  have hcoord : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) := by
    rw [measurable_iff_comap_le]
    rfl
  have hsingle : MeasurableSet ({signedScoreObservedMark M ki} :
      Set (SampleObs n)) := by
    have heq : ({signedScoreObservedMark M ki} : Set (SampleObs n)) =
        (fun o : SampleObs n => (o.x, o.a, o.y)) ⁻¹'
          {((signedScoreObservedMark M ki).x,
            (signedScoreObservedMark M ki).a,
            (signedScoreObservedMark M ki).y)} := by
      ext o
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        rfl
      · intro ho
        rcases o with ⟨x, a, y⟩
        simp only at ho ⊢
        injection ho with hx hrest
        injection hrest with ha hy
        subst x
        subst a
        subst y
        rfl
    rw [heq]
    exact hcoord (MeasurableSet.singleton _)
  rw [Measure.map_apply (signedScoreObservedMark_measurable M n)
    hsingle] at happ
  have hpre : signedScoreObservedMark M ⁻¹'
      {signedScoreObservedMark M ki} = ({ki} : Set (Fin n × Fin 4)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (signedScoreObservedMark_injective n M hM).eq_iff
  rw [hpre] at happ
  exact congrArg ENNReal.toReal happ

/-- Poissonizing the finite code law and decoding every point gives the exact
Poisson sample from the selected observable law. -/
-- keep: exact decoding bridge from finite code counts to observable Poisson samples
lemma signedScoreObservedCode_finitePoisson_map_decode
    {n : ℕ} {M rho kappa gamma : ℝ} {J : ℕ}
    {theta : Fin (n - 1) → LatentCell}
    (P : DiscreteAteHeterogeneityFrontier.RealLaw n)
    (hspec : LatentLawSpec n M rho kappa gamma J theta P)
    (hM : 0 < M) (lam : ℝ≥0) :
    Measure.map (finiteSampleMap (signedScoreObservedMark M))
        (finitePoissonSampleLaw (signedScoreObservedCodeLaw M P) lam) =
      finitePoissonSampleLaw P.observedLaw lam := by
  have h :=
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.map_finitePoissonSampleLaw_finiteSampleMap_dense
      (signedScoreObservedCodeLaw M P) (signedScoreObservedMark M)
      (signedScoreObservedMark_measurable M n) lam
  simpa only [signedScoreObservedCodeLaw_map_decode P hspec hM] using h

/-- Each of the four observable atoms in a rare cell has, at exposure `2n`
and before normalization, exactly the intensity used by the signed-score
Poisson experiment. -/
lemma latentLawSpec_rare_observed_intensity
    {n J : ℕ} {M rho kappa gamma : ℝ}
    {theta : Fin (n - 1) → LatentCell}
    (P : DiscreteAteHeterogeneityFrontier.RealLaw n)
    (hspec : LatentLawSpec n M rho kappa gamma J theta P)
    (hn : 0 < n) (hM : 0 < M) (hkappa : 0 ≤ kappa)
    (hq : ∀ k, 0 ≤ latentIntensity (theta k))
    (k : Fin (n - 1)) (i : Fin 4) :
    (2 * (n : ℝ)) * rawMassTotal n J kappa theta *
        P.observedLaw.real
          {signedScoreObservedMark M (rareCellEmbedding n k, i)} =
      signedScoreIntensity kappa gamma rho J (theta k) i := by
  rcases hspec with ⟨hmass, hprop, hmean0, hmean1, hsupp⟩
  have htotal : rawMassTotal n J kappa theta ≠ 0 :=
    ne_of_gt (raw_mass_total_positive n J kappa theta hn hkappa hq)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hk : (rareCellEmbedding n k).val < n - 1 := k.isLt
  have hemb : (⟨(rareCellEmbedding n k).val, hk⟩ : Fin (n - 1)) = k :=
    Fin.ext rfl
  fin_cases i
  · change (2 * (n : ℝ)) * rawMassTotal n J kappa theta *
        P.observedLaw.real
          {signedScoreEndpointObs M (rareCellEmbedding n k) false false} = _
    rw [latentLawSpec_observed_endpoint_realMass P
      ⟨hmass, hprop, hmean0, hmean1, hsupp⟩ hM, hmass, hprop, hmean0]
    simp [rawRareMass, hk, hemb, signedScoreIntensity]
    field_simp [hnR, htotal]
  · change (2 * (n : ℝ)) * rawMassTotal n J kappa theta *
        P.observedLaw.real
          {signedScoreEndpointObs M (rareCellEmbedding n k) false true} = _
    rw [latentLawSpec_observed_endpoint_realMass P
      ⟨hmass, hprop, hmean0, hmean1, hsupp⟩ hM, hmass, hprop, hmean0]
    simp [rawRareMass, hk, hemb, signedScoreIntensity]
    field_simp [hnR, htotal]
  · change (2 * (n : ℝ)) * rawMassTotal n J kappa theta *
        P.observedLaw.real
          {signedScoreEndpointObs M (rareCellEmbedding n k) true false} = _
    rw [latentLawSpec_observed_endpoint_realMass P
      ⟨hmass, hprop, hmean0, hmean1, hsupp⟩ hM, hmass, hprop, hmean1]
    simp [rawRareMass, hk, hemb, signedScoreIntensity, latentSignValue]
    field_simp [hnR, hM.ne', htotal]
    split_ifs <;> ring
  · change (2 * (n : ℝ)) * rawMassTotal n J kappa theta *
        P.observedLaw.real
          {signedScoreEndpointObs M (rareCellEmbedding n k) true true} = _
    rw [latentLawSpec_observed_endpoint_realMass P
      ⟨hmass, hprop, hmean0, hmean1, hsupp⟩ hM, hmass, hprop, hmean1]
    simp [rawRareMass, hk, hemb, signedScoreIntensity, latentSignValue]
    field_simp [hnR, hM.ne', htotal]
    split_ifs <;> ring

/-- Every reservoir mark has intensity `n/2` at exposure `2n`. -/
lemma latentLawSpec_reservoir_observed_intensity
    {n J : ℕ} {M rho kappa gamma : ℝ}
    {theta : Fin (n - 1) → LatentCell}
    (P : DiscreteAteHeterogeneityFrontier.RealLaw n)
    (hspec : LatentLawSpec n M rho kappa gamma J theta P)
    (hn : 0 < n) (hM : 0 < M) (hkappa : 0 ≤ kappa)
    (hq : ∀ k, 0 ≤ latentIntensity (theta k)) (i : Fin 4) :
    (2 * (n : ℝ)) * rawMassTotal n J kappa theta *
        P.observedLaw.real
          {signedScoreObservedMark M (reservoirCell n hn, i)} =
      (n : ℝ) / 2 := by
  rcases hspec with ⟨hmass, hprop, hmean0, hmean1, hsupp⟩
  have htotal : rawMassTotal n J kappa theta ≠ 0 :=
    ne_of_gt (raw_mass_total_positive n J kappa theta hn hkappa hq)
  have hnot : ¬(reservoirCell n hn).val < n - 1 := by
    simp [reservoirCell]
  fin_cases i
  · change (2 * (n : ℝ)) * rawMassTotal n J kappa theta *
        P.observedLaw.real
          {signedScoreEndpointObs M (reservoirCell n hn) false false} = _
    rw [latentLawSpec_observed_endpoint_realMass P
      ⟨hmass, hprop, hmean0, hmean1, hsupp⟩ hM, hmass, hprop, hmean0]
    simp [rawRareMass, hnot]
    field_simp [htotal]
    norm_num
  · change (2 * (n : ℝ)) * rawMassTotal n J kappa theta *
        P.observedLaw.real
          {signedScoreEndpointObs M (reservoirCell n hn) false true} = _
    rw [latentLawSpec_observed_endpoint_realMass P
      ⟨hmass, hprop, hmean0, hmean1, hsupp⟩ hM, hmass, hprop, hmean0]
    simp [rawRareMass, hnot]
    field_simp [htotal]
    norm_num
  · change (2 * (n : ℝ)) * rawMassTotal n J kappa theta *
        P.observedLaw.real
          {signedScoreEndpointObs M (reservoirCell n hn) true false} = _
    rw [latentLawSpec_observed_endpoint_realMass P
      ⟨hmass, hprop, hmean0, hmean1, hsupp⟩ hM, hmass, hprop, hmean1]
    simp [rawRareMass, hnot]
    field_simp [hM.ne', htotal]
  · change (2 * (n : ℝ)) * rawMassTotal n J kappa theta *
        P.observedLaw.real
          {signedScoreEndpointObs M (reservoirCell n hn) true true} = _
    rw [latentLawSpec_observed_endpoint_realMass P
      ⟨hmass, hprop, hmean0, hmean1, hsupp⟩ hM, hmass, hprop, hmean1]
    simp [rawRareMass, hnot]
    field_simp [hM.ne', htotal]

/-- The complete rare-plus-reservoir histogram intensity vector. -/
@[no_expose]
noncomputable def signedScoreFullIntensity (n : ℕ)
    (kappa gamma rho : ℝ) (J : ℕ)
    (theta : Fin (n - 1) → LatentCell) : Fin n × Fin 4 → ℝ := fun ki =>
  if hk : ki.1.val < n - 1 then
    signedScoreIntensity kappa gamma rho J (theta ⟨ki.1.val, hk⟩) ki.2
  else (n : ℝ) / 2

/-- `LatentLawSpec` identifies every coordinate of the finite marked-Poisson
histogram, including the common reservoir coordinates. -/
lemma latentLawSpec_observed_histogram_intensity
    {n J : ℕ} {M rho kappa gamma : ℝ}
    {theta : Fin (n - 1) → LatentCell}
    (P : DiscreteAteHeterogeneityFrontier.RealLaw n)
    (hspec : LatentLawSpec n M rho kappa gamma J theta P)
    (hn : 0 < n) (hM : 0 < M) (hkappa : 0 ≤ kappa)
    (hq : ∀ k, 0 ≤ latentIntensity (theta k))
    (ki : Fin n × Fin 4) :
    (2 * (n : ℝ)) * rawMassTotal n J kappa theta *
        P.observedLaw.real {signedScoreObservedMark M ki} =
      signedScoreFullIntensity n kappa gamma rho J theta ki := by
  rcases ki with ⟨k, i⟩
  by_cases hk : k.val < n - 1
  · let kr : Fin (n - 1) := ⟨k.val, hk⟩
    have hemb : rareCellEmbedding n kr = k := Fin.ext rfl
    simpa [signedScoreFullIntensity, hk, kr, hemb] using
      latentLawSpec_rare_observed_intensity P hspec hn hM hkappa hq kr i
  · have hreservoir : k = reservoirCell n hn := by
      apply Fin.ext
      simp only [reservoirCell]
      omega
    subst k
    simpa [signedScoreFullIntensity, reservoirCell] using
      latentLawSpec_reservoir_observed_intensity P hspec hn hM hkappa hq i

/-- The same coordinate identity stated for the finite code law consumed by
the independent-Poisson histogram API. -/
lemma latentLawSpec_codeLaw_histogram_intensity
    {n J : ℕ} {M rho kappa gamma : ℝ}
    {theta : Fin (n - 1) → LatentCell}
    (P : DiscreteAteHeterogeneityFrontier.RealLaw n)
    (hspec : LatentLawSpec n M rho kappa gamma J theta P)
    (hn : 0 < n) (hM : 0 < M) (hkappa : 0 ≤ kappa)
    (hq : ∀ k, 0 ≤ latentIntensity (theta k))
    (ki : Fin n × Fin 4) :
    (2 * (n : ℝ)) * rawMassTotal n J kappa theta *
        (signedScoreObservedCodeLaw M P).real {ki} =
      signedScoreFullIntensity n kappa gamma rho J theta ki := by
  rw [signedScoreObservedCodeLaw_singleton_realMass P hspec hM]
  exact latentLawSpec_observed_histogram_intensity
    P hspec hn hM hkappa hq ki

/-- The scaled singleton identity also identifies the `NNReal` Poisson rate
used by `independentPoissonCountLaw`. -/
lemma latentLawSpec_codeLaw_poissonRate
    {n J : ℕ} {M rho kappa gamma : ℝ}
    {theta : Fin (n - 1) → LatentCell}
    (P : DiscreteAteHeterogeneityFrontier.RealLaw n)
    (hspec : LatentLawSpec n M rho kappa gamma J theta P)
    (hn : 0 < n) (hM : 0 < M) (hkappa : 0 ≤ kappa)
    (hq : ∀ k, 0 ≤ latentIntensity (theta k))
    (ki : Fin n × Fin 4) :
    (2 * (n : ℝ≥0) * Real.toNNReal (rawMassTotal n J kappa theta)) *
        ((signedScoreObservedCodeLaw M P) {ki}).toNNReal =
      Real.toNNReal
        (signedScoreFullIntensity n kappa gamma rho J theta ki) := by
  have htotal : 0 ≤ rawMassTotal n J kappa theta :=
    (one_le_rawMassTotal n J kappa theta hn hkappa hq).trans' (by norm_num)
  have hid := latentLawSpec_codeLaw_histogram_intensity
    P hspec hn hM hkappa hq ki
  have hfull : 0 ≤ signedScoreFullIntensity n kappa gamma rho J theta ki := by
    rw [← hid]
    positivity
  have hmass : (((signedScoreObservedCodeLaw M P) {ki}).toNNReal : ℝ) =
      ((signedScoreObservedCodeLaw M P) {ki}).toReal := by
    rw [← ENNReal.coe_toReal]
    rw [ENNReal.coe_toNNReal (MeasureTheory.measure_ne_top _ _)]
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_natCast,
    Real.coe_toNNReal _ htotal, Real.coe_toNNReal _ hfull]
  rw [hmass]
  simpa [DiscreteAteHeterogeneityFrontier.realMass, Measure.real,
    mul_assoc] using hid

/-- Conditional on one legal latent vector, the reshaped rare score counts and
common reservoir are exactly the independent-Poisson histogram of the coded
observable law at random scale `2n * rawMassTotal`. -/
lemma latentLawSpec_conditionalHistogram_eq_independentPoisson
    {n J : ℕ} {M rho kappa gamma : ℝ}
    {theta : Fin (n - 1) → LatentCell}
    (P : DiscreteAteHeterogeneityFrontier.RealLaw n)
    (hspec : LatentLawSpec n M rho kappa gamma J theta P)
    (hn : 0 < n) (hM : 0 < M) (hkappa : 0 ≤ kappa)
    (hq : ∀ k, 0 ≤ latentIntensity (theta k)) :
    signedScoreConditionalHistogramLaw n
        (fun k => signedScoreIntensity kappa gamma rho J (theta k)) =
      independentPoissonCountLaw (signedScoreObservedCodeLaw M P)
        (2 * (n : ℝ≥0) * Real.toNNReal
          (rawMassTotal n J kappa theta)) := by
  rw [signedScoreConditionalHistogramLaw_eq_pi n hn]
  unfold independentPoissonCountLaw
  congr with ki
  rw [latentLawSpec_codeLaw_poissonRate P hspec hn hM hkappa hq ki]
  rfl

/-- For either selected hypothesis, the common-reservoir count experiment is
exactly the latent mixture of independent Poisson histograms of the selected
observable laws. -/
lemma selectedSignedScoreReservoirCountLaw_eq_bind_independentPoisson
    (n : ℕ) (M rho : ℝ) (h : Bool)
    (hn : 3 ≤ n) (hM : 1 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2) :
    signedScoreReservoirCountLaw n
        (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
          (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
          (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
            (radiusDual n rho) h)) =
      (selectedLatentPrior n rho h).bind (fun theta =>
        independentPoissonCountLaw
          (signedScoreObservedCodeLaw M
            (latentToLaw n M rho converseKappa (selectedGamma n rho)
              (dualDegree n rho) theta (by omega)
              (by unfold dualDegree
                  exact lt_of_lt_of_le (by decide) (le_max_left _ _))
              (by linarith) hrho (by unfold converseKappa; norm_num)
              (selectedGamma_mem_Icc n rho hn)))
          (2 * (n : ℝ≥0) * Real.toNNReal
            (rawMassTotal n (dualDegree n rho) converseKappa theta))) := by
  have ha : 0 < dualInterval n rho := by
    unfold dualInterval
    have hdegree : 0 < (dualDegree n rho : ℝ) := by
      exact_mod_cast (show 0 < dualDegree n rho by
        unfold dualDegree
        omega)
    positivity
  have hJ : 1 ≤ dualDegree n rho := by
    unfold dualDegree
    exact le_trans (by decide : 1 ≤ 2) (le_max_left _ _)
  rw [signedScoreReservoirCountLaw_eq_latent_bind n converseKappa
    (selectedGamma n rho) rho (dualInterval n rho) (dualDegree n rho)
    (radiusDual n rho)
    (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
      (radiusDual n rho) h)
    (by unfold converseKappa; norm_num) (selectedGamma_mem_Icc n rho hn)
    ⟨hrho.1, hrho.2⟩ ha hJ]
  change (selectedLatentPrior n rho h).bind _ =
    (selectedLatentPrior n rho h).bind _
  apply Measure.bind_congr_right
  filter_upwards [selectedLatentPrior_ae_latentToLaw_spec n M rho h hn hM hrho,
    selectedLatentPrior_ae_admissible n rho h] with theta hspec hadm
  exact latentLawSpec_conditionalHistogram_eq_independentPoisson
    (latentToLaw n M rho converseKappa (selectedGamma n rho)
      (dualDegree n rho) theta (by omega)
      (by unfold dualDegree
          exact lt_of_lt_of_le (by decide) (le_max_left _ _))
      (by linarith) hrho (by unfold converseKappa; norm_num)
      (selectedGamma_mem_Icc n rho hn))
    hspec (by omega) (by linarith) (by unfold converseKappa; norm_num) hadm.1

/-- Histogram reconstruction followed by mark decoding turns an independent
Poisson count vector into the decoded finite-Poisson sample. -/
lemma signedScoreHistogramReconstructionKernel_comp_independentPoisson
    (n : ℕ) (M : ℝ) (Q : Measure (Fin n × Fin 4))
    [IsProbabilityMeasure Q] (lam : ℝ≥0) :
    signedScoreHistogramReconstructionKernel n M ∘ₘ
        independentPoissonCountLaw Q lam =
      Measure.map (finiteSampleMap (signedScoreObservedMark M))
        (finitePoissonSampleLaw Q lam) := by
  unfold signedScoreHistogramReconstructionKernel
  rw [← Measure.comp_assoc,
    independentPoissonCountLaw_comp_reconstruction,
    Measure.deterministic_comp_eq_map]

/-- The selected common-reservoir count experiment reconstructs exactly to
the latent mixture of decoded random-size observable samples. -/
lemma selectedSignedScoreHistogramReconstruction_comp
    (n : ℕ) (M rho : ℝ) (h : Bool)
    (hn : 3 ≤ n) (hM : 1 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2) :
    signedScoreHistogramReconstructionKernel n M ∘ₘ
        signedScoreReservoirCountLaw n
          (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
            (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
            (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
              (radiusDual n rho) h)) =
      (selectedLatentPrior n rho h).bind (fun theta =>
        Measure.map (finiteSampleMap (signedScoreObservedMark M))
          (finitePoissonSampleLaw
            (signedScoreObservedCodeLaw M
              (latentToLaw n M rho converseKappa (selectedGamma n rho)
                (dualDegree n rho) theta (by omega)
                (by unfold dualDegree
                    exact lt_of_lt_of_le (by decide) (le_max_left _ _))
                (by linarith) hrho (by unfold converseKappa; norm_num)
                (selectedGamma_mem_Icc n rho hn)))
            (2 * (n : ℝ≥0) * Real.toNNReal
              (rawMassTotal n (dualDegree n rho) converseKappa theta)))) := by
  let μ := selectedLatentPrior n rho h
  let f : (Fin (n - 1) → LatentCell) → Measure (Fin n × Fin 4 → ℕ) :=
    fun theta => independentPoissonCountLaw
      (signedScoreObservedCodeLaw M
        (latentToLaw n M rho converseKappa (selectedGamma n rho)
          (dualDegree n rho) theta (by omega)
          (by unfold dualDegree
              exact lt_of_lt_of_le (by decide) (le_max_left _ _))
          (by linarith) hrho (by unfold converseKappa; norm_num)
          (selectedGamma_mem_Icc n rho hn)))
      (2 * (n : ℝ≥0) * Real.toNNReal
        (rawMassTotal n (dualDegree n rho) converseKappa theta))
  have ha : 0 < dualInterval n rho := by
    unfold dualInterval
    have hdegree : 0 < (dualDegree n rho : ℝ) := by
      exact_mod_cast (show 0 < dualDegree n rho by
        unfold dualDegree
        omega)
    positivity
  have hJ : 1 ≤ dualDegree n rho := by
    unfold dualDegree
    exact le_trans (by decide : 1 ≤ 2) (le_max_left _ _)
  obtain ⟨s, hs, hmem⟩ := latentProductPrior_ae_mem_finite n
    (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
    (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
      (radiusDual n rho) h) ha hJ
  let _ : IsProbabilityMeasure μ :=
    latentProductPrior_isProbabilityMeasure n (dualInterval n rho)
      (dualDegree n rho) (radiusDual n rho)
      (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
        (radiusDual n rho) h) ha hJ
  let _ : ∀ theta, IsProbabilityMeasure (f theta) := fun theta => by
    dsimp [f]
    infer_instance
  let K := finiteSupportKernel f s hs (fun _ => referenceLatent)
  let _ : ∀ theta, IsProbabilityMeasure (K theta) :=
    finiteSupportKernel_isProbabilityMeasure f s hs (fun _ => referenceLatent)
  let _ : IsMarkovKernel K := ⟨fun theta => inferInstance⟩
  have hKf : K =ᵐ[μ] f := hmem.mono fun theta htheta =>
    finiteSupportKernel_apply f s hs (fun _ => referenceLatent) theta htheta
  have hcount : signedScoreReservoirCountLaw n
      (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
        (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
        (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
          (radiusDual n rho) h)) = K ∘ₘ μ := by
    rw [selectedSignedScoreReservoirCountLaw_eq_bind_independentPoisson
      n M rho h hn hM hrho]
    exact (Measure.bind_congr_right hKf).symm
  rw [hcount, Measure.comp_assoc]
  apply Measure.bind_congr_right
  filter_upwards [hKf] with theta htheta
  rw [Kernel.comp_apply, htheta]
  exact signedScoreHistogramReconstructionKernel_comp_independentPoisson
    n M _ _

/-- A genuine finite-support observable kernel packages the preceding decoded
mixture as the standard `rawMixture` used by ordered-prefix transfer. -/
lemma selectedSignedScoreHistogramReconstruction_exists_rawMixtureKernel
    (n : ℕ) (M rho : ℝ) (h : Bool)
    (hn : 3 ≤ n) (hM : 1 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2) :
    ∃ P : Kernel (Fin (n - 1) → LatentCell) (SampleObs n),
      ∃ hPprob : ∀ theta, IsProbabilityMeasure (P theta),
      P =ᵐ[selectedLatentPrior n rho h] (fun theta =>
        (latentToLaw n M rho converseKappa (selectedGamma n rho)
          (dualDegree n rho) theta (by omega)
          (by unfold dualDegree
              exact lt_of_lt_of_le (by decide) (le_max_left _ _))
          (by linarith) hrho (by unfold converseKappa; norm_num)
          (selectedGamma_mem_Icc n rho hn)).observedLaw) ∧
      let _ := hPprob
      signedScoreHistogramReconstructionKernel n M ∘ₘ
          signedScoreReservoirCountLaw n
            (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
              (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
              (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
                (radiusDual n rho) h)) =
        rawMixture (selectedLatentPrior n rho h) P
          (fun theta => Real.toNNReal
            (rawMassTotal n (dualDegree n rho) converseKappa theta))
          (2 * (n : ℝ≥0)) := by
  let μ := selectedLatentPrior n rho h
  let q : (Fin (n - 1) → LatentCell) → Measure (SampleObs n) := fun theta =>
    (latentToLaw n M rho converseKappa (selectedGamma n rho)
      (dualDegree n rho) theta (by omega)
      (by unfold dualDegree
          exact lt_of_lt_of_le (by decide) (le_max_left _ _))
      (by linarith) hrho (by unfold converseKappa; norm_num)
      (selectedGamma_mem_Icc n rho hn)).observedLaw
  have ha : 0 < dualInterval n rho := by
    unfold dualInterval
    have hdegree : 0 < (dualDegree n rho : ℝ) := by
      exact_mod_cast (show 0 < dualDegree n rho by
        unfold dualDegree
        omega)
    positivity
  have hJ : 1 ≤ dualDegree n rho := by
    unfold dualDegree
    exact le_trans (by decide : 1 ≤ 2) (le_max_left _ _)
  obtain ⟨s, hs, hmem⟩ := latentProductPrior_ae_mem_finite n
    (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
    (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
      (radiusDual n rho) h) ha hJ
  let _ : ∀ theta, IsProbabilityMeasure (q theta) := fun theta => by
    dsimp [q]
    infer_instance
  let P := finiteSupportKernel q s hs (fun _ => referenceLatent)
  have hPprob : ∀ theta, IsProbabilityMeasure (P theta) :=
    finiteSupportKernel_isProbabilityMeasure q s hs (fun _ => referenceLatent)
  let _ : ∀ theta, IsProbabilityMeasure (P theta) := hPprob
  let _ : IsMarkovKernel P := ⟨fun theta => inferInstance⟩
  have hP : P =ᵐ[μ] q := hmem.mono fun theta htheta =>
    finiteSupportKernel_apply q s hs (fun _ => referenceLatent) theta htheta
  refine ⟨P, hPprob, hP, ?_⟩
  rw [selectedSignedScoreHistogramReconstruction_comp
    n M rho h hn hM hrho]
  unfold rawMixture
  apply Measure.bind_congr_right
  filter_upwards [hP,
    selectedLatentPrior_ae_latentToLaw_spec n M rho h hn hM hrho]
      with theta hPtheta hspec
  rw [CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.map_finitePoissonSampleLaw_finiteSampleMap_dense
    (signedScoreObservedCodeLaw M
      (latentToLaw n M rho converseKappa (selectedGamma n rho)
        (dualDegree n rho) theta (by omega)
        (by unfold dualDegree
            exact lt_of_lt_of_le (by decide) (le_max_left _ _))
        (by linarith) hrho (by unfold converseKappa; norm_num)
        (selectedGamma_mem_Icc n rho hn)))
    (signedScoreObservedMark M) (signedScoreObservedMark_measurable M n)]
  have hbase : Measure.map (signedScoreObservedMark M)
      (signedScoreObservedCodeLaw M
        (latentToLaw n M rho converseKappa (selectedGamma n rho)
          (dualDegree n rho) theta (by omega)
          (by unfold dualDegree
              exact lt_of_lt_of_le (by decide) (le_max_left _ _))
          (by linarith) hrho (by unfold converseKappa; norm_num)
          (selectedGamma_mem_Icc n rho hn))) = P theta := by
    calc
      _ = (latentToLaw n M rho converseKappa (selectedGamma n rho)
          (dualDegree n rho) theta (by omega)
          (by unfold dualDegree
              exact lt_of_lt_of_le (by decide) (le_max_left _ _))
          (by linarith) hrho (by unfold converseKappa; norm_num)
          (selectedGamma_mem_Icc n rho hn)).observedLaw :=
        signedScoreObservedCodeLaw_map_decode _ hspec (by linarith)
      _ = P theta := by simpa only [q] using hPtheta.symm
  let Q₀ : {Q : Measure (SampleObs n) // IsProbabilityMeasure Q} :=
    ⟨Measure.map (signedScoreObservedMark M)
      (signedScoreObservedCodeLaw M
        (latentToLaw n M rho converseKappa (selectedGamma n rho)
          (dualDegree n rho) theta (by omega)
          (by unfold dualDegree
              exact lt_of_lt_of_le (by decide) (le_max_left _ _))
          (by linarith) hrho (by unfold converseKappa; norm_num)
          (selectedGamma_mem_Icc n rho hn))),
      Measure.isProbabilityMeasure_map
        (signedScoreObservedMark_measurable M n).aemeasurable⟩
  let Q₁ : {Q : Measure (SampleObs n) // IsProbabilityMeasure Q} :=
    ⟨P theta, inferInstance⟩
  have hQ : Q₀ = Q₁ := Subtype.ext hbase
  exact congrArg (fun Q : {Q : Measure (SampleObs n) // IsProbabilityMeasure Q} =>
    @finitePoissonSampleLaw (SampleObs n) _ Q.1 Q.2
      (2 * (n : ℝ≥0) * Real.toNNReal
        (rawMassTotal n (dualDegree n rho) converseKappa theta))) hQ

/-- The common kernel reconstructs the decoded finite-Poisson sample whenever
the augmented counts reshape to the appropriate independent histogram law.
This isolates the qid-specific work to one histogram distribution identity. -/
-- keep: common-kernel reconstruction theorem for the count-reservoir transfer
lemma signedScoreReservoirReconstructionKernel_comp
    (n : ℕ) (M : ℝ)
    (μ : Measure ((Fin (n - 1) → SignedScoreCounts) × SignedScoreCounts))
    (Q : Measure (Fin n × Fin 4)) [IsProbabilityMeasure Q] (lam : ℝ≥0)
    (hhist : Measure.map (signedScoreReservoirHistogram n) μ =
      independentPoissonCountLaw Q lam) :
    signedScoreReservoirReconstructionKernel n M ∘ₘ μ =
      Measure.map (finiteSampleMap (signedScoreObservedMark M))
        (finitePoissonSampleLaw Q lam) := by
  let H := Kernel.deterministic (signedScoreReservoirHistogram n)
    (signedScoreReservoirHistogram_measurable n)
  let U := histogramReconstructionKernel (Fin n × Fin 4)
  let G := Kernel.deterministic
    (finiteSampleMap (signedScoreObservedMark M))
    (measurable_finiteSampleMap _ (signedScoreObservedMark_measurable M n))
  have hH : H ∘ₘ μ = independentPoissonCountLaw Q lam := by
    rw [Measure.deterministic_comp_eq_map]
    exact hhist
  have hU : U ∘ₘ independentPoissonCountLaw Q lam =
      finitePoissonSampleLaw Q lam :=
    independentPoissonCountLaw_comp_reconstruction Q lam
  change (G ∘ₖ U ∘ₖ H) ∘ₘ μ = _
  rw [← Measure.comp_assoc, hH, ← Measure.comp_assoc, hU,
    Measure.deterministic_comp_eq_map]

/-- Adding the same independent reservoir count vector to both rare-count
experiments cannot increase their total-variation distance. -/
lemma signedScoreProductMixture_prod_reservoir_tv_le
    (n d : ℕ) (π₀ π₁ : Measure (Fin 4 → ℝ))
    [IsProbabilityMeasure (signedScoreProductMixtureLaw d π₀)]
    [IsProbabilityMeasure (signedScoreProductMixtureLaw d π₁)] :
    Causalean.Stat.tvDist
        ((signedScoreProductMixtureLaw d π₀).prod (reservoirSignedScoreLaw n))
        ((signedScoreProductMixtureLaw d π₁).prod (reservoirSignedScoreLaw n)) ≤
      Causalean.Stat.tvDist (signedScoreProductMixtureLaw d π₀)
        (signedScoreProductMixtureLaw d π₁) := by
  have h := Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_prod_le_add
    (signedScoreProductMixtureLaw d π₀)
    (signedScoreProductMixtureLaw d π₁)
    (reservoirSignedScoreLaw n) (reservoirSignedScoreLaw n)
  have hself : Causalean.Stat.tvDist
      (reservoirSignedScoreLaw n) (reservoirSignedScoreLaw n) = 0 := by
    simp [Causalean.Stat.tvDist]
  simpa [hself] using h

instance signedScoreReservoirCountLaw_isProbabilityMeasure
    (n : ℕ) (π : Measure (Fin 4 → ℝ))
    [IsProbabilityMeasure (signedScoreProductMixtureLaw (n - 1) π)] :
    IsProbabilityMeasure (signedScoreReservoirCountLaw n π) := by
  unfold signedScoreReservoirCountLaw
  exact Measure.isProbabilityMeasure_map
    (signedScoreReservoirHistogram_measurable n).aemeasurable

/-- Reshaping to the finite histogram and adding the common reservoir are both
data-processing steps, so the histogram experiment inherits the rare-count TV
bound unchanged. -/
lemma signedScoreReservoirCountLaw_tv_le
    (n : ℕ) (π₀ π₁ : Measure (Fin 4 → ℝ))
    [IsProbabilityMeasure (signedScoreProductMixtureLaw (n - 1) π₀)]
    [IsProbabilityMeasure (signedScoreProductMixtureLaw (n - 1) π₁)] :
    Causalean.Stat.tvDist (signedScoreReservoirCountLaw n π₀)
        (signedScoreReservoirCountLaw n π₁) ≤
      Causalean.Stat.tvDist (signedScoreProductMixtureLaw (n - 1) π₀)
        (signedScoreProductMixtureLaw (n - 1) π₁) := by
  let μ₀ := (signedScoreProductMixtureLaw (n - 1) π₀).prod
    (reservoirSignedScoreLaw n)
  let μ₁ := (signedScoreProductMixtureLaw (n - 1) π₁).prod
    (reservoirSignedScoreLaw n)
  have hmap : Causalean.Stat.tvDist
      (Measure.map (signedScoreReservoirHistogram n) μ₀)
      (Measure.map (signedScoreReservoirHistogram n) μ₁) ≤
      Causalean.Stat.tvDist μ₀ μ₁ := by
    simpa only [Measure.deterministic_comp_eq_map] using
      Causalean.Stat.tvDist_bind_le μ₀ μ₁
        (Kernel.deterministic (signedScoreReservoirHistogram n)
          (signedScoreReservoirHistogram_measurable n))
  exact hmap.trans
    (signedScoreProductMixture_prod_reservoir_tv_le n (n - 1) π₀ π₁)

/-- If one common reconstruction kernel sends two count experiments to their
raw marked-Poisson mixtures, the two-prior ordered-prefix theorem bounds the
fixed mixtures directly by count TV plus the two short-count tails. -/
lemma twoPrior_fixedMixture_tv_le_of_common_reconstruction
    {Θ₀ Θ₁ C X : Type*}
    [MeasurableSpace Θ₀] [MeasurableSpace Θ₁]
    [MeasurableSpace C] [MeasurableSpace X]
    (π₀ : Measure Θ₀) (π₁ : Measure Θ₁)
    [IsProbabilityMeasure π₀] [IsProbabilityMeasure π₁]
    (P₀ : Kernel Θ₀ X) (P₁ : Kernel Θ₁ X)
    [∀ θ, IsProbabilityMeasure (P₀ θ)]
    [∀ θ, IsProbabilityMeasure (P₁ θ)]
    (S₀ : Θ₀ → ℝ≥0) (S₁ : Θ₁ → ℝ≥0)
    (hS₀ : Measurable S₀) (hS₁ : Measurable S₁) (u : ℝ≥0)
    (n : ℕ) (fallback : Fin n → X)
    (hfixed₀ : AEMeasurable
      (fun θ => Measure.pi (fun _ : Fin n => P₀ θ)) π₀)
    (hfixed₁ : AEMeasurable
      (fun θ => Measure.pi (fun _ : Fin n => P₁ θ)) π₁)
    (hraw₀ : AEMeasurable
      (fun θ => finitePoissonSampleLaw (P₀ θ) (u * S₀ θ)) π₀)
    (hraw₁ : AEMeasurable
      (fun θ => finitePoissonSampleLaw (P₁ θ) (u * S₁ θ)) π₁)
    (ξ₀ ξ₁ : Measure C) [IsProbabilityMeasure ξ₀] [IsProbabilityMeasure ξ₁]
    (R : Kernel C (FiniteSample X)) [IsMarkovKernel R]
    (hrec₀ : R ∘ₘ ξ₀ = rawMixture π₀ P₀ S₀ u)
    (hrec₁ : R ∘ₘ ξ₁ = rawMixture π₁ P₁ S₁ u) :
    Causalean.Stat.tvDist (fixedMixture π₀ P₀ n) (fixedMixture π₁ P₁ n) ≤
      Causalean.Stat.tvDist ξ₀ ξ₁ +
      (∫ θ, (poissonMeasure (u * S₀ θ) (Set.Iio n)).toReal ∂π₀) +
      ∫ θ, (poissonMeasure (u * S₁ θ) (Set.Iio n)).toReal ∂π₁ := by
  have hprefix := twoPrior_fixedMixture_tv_le_randomScalePoisson
    π₀ π₁ P₀ P₁ S₀ S₁ hS₀ hS₁ u n fallback
    hfixed₀ hfixed₁ hraw₀ hraw₁
  have hcontract :
      Causalean.Stat.tvDist (rawMixture π₀ P₀ S₀ u)
          (rawMixture π₁ P₁ S₁ u) ≤ Causalean.Stat.tvDist ξ₀ ξ₁ := by
    rw [← hrec₀, ← hrec₁]
    exact Causalean.Stat.tvDist_bind_le ξ₀ ξ₁ R
  calc
    _ ≤ Causalean.Stat.tvDist (rawMixture π₀ P₀ S₀ u)
          (rawMixture π₁ P₁ S₁ u) +
        (∫ θ, (poissonMeasure (u * S₀ θ) (Set.Iio n)).toReal ∂π₀) +
        ∫ θ, (poissonMeasure (u * S₁ θ) (Set.Iio n)).toReal ∂π₁ := hprefix
    _ ≤ _ := by gcongr

/-- Combining common-reservoir reconstruction, tensor calibration, and the
ordered-prefix transfer gives the selected fixed-sample comparison, with only
the two explicit Poisson short-count tails remaining. -/
lemma selectedFixedMixture_tv_lt_one_quarter_add_tails
    (n : ℕ) (M rho : ℝ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (P₀ P₁ : Kernel (Fin (n - 1) → LatentCell) (SampleObs n))
    [∀ theta, IsProbabilityMeasure (P₀ theta)]
    [∀ theta, IsProbabilityMeasure (P₁ theta)]
    (hP₀ : P₀ =ᵐ[selectedLatentPrior n rho false] (fun theta =>
      (latentToLaw n M rho converseKappa (selectedGamma n rho)
        (dualDegree n rho) theta (by omega)
        (by unfold dualDegree
            exact lt_of_lt_of_le (by decide) (le_max_left _ _))
        (by linarith) hrho (by unfold converseKappa; norm_num)
        (selectedGamma_mem_Icc n rho hn)).observedLaw))
    (hP₁ : P₁ =ᵐ[selectedLatentPrior n rho true] (fun theta =>
      (latentToLaw n M rho converseKappa (selectedGamma n rho)
        (dualDegree n rho) theta (by omega)
        (by unfold dualDegree
            exact lt_of_lt_of_le (by decide) (le_max_left _ _))
        (by linarith) hrho (by unfold converseKappa; norm_num)
        (selectedGamma_mem_Icc n rho hn)).observedLaw))
    (hrec₀ : signedScoreHistogramReconstructionKernel n M ∘ₘ
        signedScoreReservoirCountLaw n
          (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
            (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
            (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
              (radiusDual n rho) false)) =
      rawMixture (selectedLatentPrior n rho false) P₀
        (fun theta => Real.toNNReal
          (rawMassTotal n (dualDegree n rho) converseKappa theta))
        (2 * (n : ℝ≥0)))
    (hrec₁ : signedScoreHistogramReconstructionKernel n M ∘ₘ
        signedScoreReservoirCountLaw n
          (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
            (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
            (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
              (radiusDual n rho) true)) =
      rawMixture (selectedLatentPrior n rho true) P₁
        (fun theta => Real.toNNReal
          (rawMassTotal n (dualDegree n rho) converseKappa theta))
        (2 * (n : ℝ≥0))) :
    Causalean.Stat.tvDist
        (fixedMixture (selectedLatentPrior n rho false) P₀ n)
        (fixedMixture (selectedLatentPrior n rho true) P₁ n) <
      1 / 4 +
        (∫ theta, (poissonMeasure
          (2 * (n : ℝ≥0) * Real.toNNReal
            (rawMassTotal n (dualDegree n rho) converseKappa theta))
          (Set.Iio n)).toReal ∂selectedLatentPrior n rho false) +
        ∫ theta, (poissonMeasure
          (2 * (n : ℝ≥0) * Real.toNNReal
            (rawMassTotal n (dualDegree n rho) converseKappa theta))
          (Set.Iio n)).toReal ∂selectedLatentPrior n rho true := by
  have ha : 0 < dualInterval n rho := by
    unfold dualInterval
    have hdegree : 0 < (dualDegree n rho : ℝ) := by
      exact_mod_cast (show 0 < dualDegree n rho by
        unfold dualDegree
        omega)
    positivity
  have hJ : 1 ≤ dualDegree n rho := by
    unfold dualDegree
    exact le_trans (by decide : 1 ≤ 2) (le_max_left _ _)
  let μ₀ := selectedLatentPrior n rho false
  let μ₁ := selectedLatentPrior n rho true
  let S : (Fin (n - 1) → LatentCell) → ℝ≥0 := fun theta =>
    Real.toNNReal (rawMassTotal n (dualDegree n rho) converseKappa theta)
  let _ : IsProbabilityMeasure μ₀ :=
    latentProductPrior_isProbabilityMeasure n (dualInterval n rho)
      (dualDegree n rho) (radiusDual n rho)
      (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
        (radiusDual n rho) false) ha hJ
  let _ : IsProbabilityMeasure μ₁ :=
    latentProductPrior_isProbabilityMeasure n (dualInterval n rho)
      (dualDegree n rho) (radiusDual n rho)
      (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
        (radiusDual n rho) true) ha hJ
  have hS : Measurable S := by
    exact measurable_real_toNNReal.comp
      (rawMassTotal_measurable n (dualDegree n rho) converseKappa)
  have hfixed₀ : AEMeasurable
      (fun theta => Measure.pi (fun _ : Fin n => P₀ theta)) μ₀ := by
    exact latentProductPrior_aemeasurable n (dualInterval n rho)
      (dualDegree n rho) (radiusDual n rho)
      (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
        (radiusDual n rho) false) ha hJ _
  have hfixed₁ : AEMeasurable
      (fun theta => Measure.pi (fun _ : Fin n => P₁ theta)) μ₁ := by
    exact latentProductPrior_aemeasurable n (dualInterval n rho)
      (dualDegree n rho) (radiusDual n rho)
      (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
        (radiusDual n rho) true) ha hJ _
  have hraw₀ : AEMeasurable
      (fun theta => finitePoissonSampleLaw (P₀ theta)
        (2 * (n : ℝ≥0) * S theta)) μ₀ := by
    exact latentProductPrior_aemeasurable n (dualInterval n rho)
      (dualDegree n rho) (radiusDual n rho)
      (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
        (radiusDual n rho) false) ha hJ _
  have hraw₁ : AEMeasurable
      (fun theta => finitePoissonSampleLaw (P₁ theta)
        (2 * (n : ℝ≥0) * S theta)) μ₁ := by
    exact latentProductPrior_aemeasurable n (dualInterval n rho)
      (dualDegree n rho) (radiusDual n rho)
      (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
        (radiusDual n rho) true) ha hJ _
  have hmixprob (b : Bool) : IsProbabilityMeasure
      (signedScoreProductMixtureLaw (n - 1)
        (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
          (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
          (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
            (radiusDual n rho) b))) := by
    let _ : IsProbabilityMeasure
        (signedScoreMixtureLaw
          (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
            (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
            (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
              (radiusDual n rho) b))) :=
      signedScoreMixtureLaw_intensityPrior_isProbabilityMeasure
        converseKappa (selectedGamma n rho) rho (dualInterval n rho)
        (dualDegree n rho) (radiusDual n rho)
        (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
          (radiusDual n rho) b)
        (by unfold converseKappa; norm_num) (selectedGamma_mem_Icc n rho hn)
        ⟨hrho.1, hrho.2⟩ ha hJ
    rw [signedScoreProductMixtureLaw_eq_pi]
    infer_instance
  let _ : IsProbabilityMeasure (signedScoreProductMixtureLaw (n - 1)
      (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
        (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
        (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
          (radiusDual n rho) false))) := hmixprob false
  let _ : IsProbabilityMeasure (signedScoreProductMixtureLaw (n - 1)
      (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
        (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
        (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
          (radiusDual n rho) true))) := hmixprob true
  have hprefix := twoPrior_fixedMixture_tv_le_of_common_reconstruction
    μ₀ μ₁ P₀ P₁ S S hS hS (2 * (n : ℝ≥0)) n
    (fun _ => { x := ⟨0, by omega⟩, a := false, y := 0 })
    hfixed₀ hfixed₁ hraw₀ hraw₁
    (signedScoreReservoirCountLaw n
      (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
        (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
        (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
          (radiusDual n rho) false)))
    (signedScoreReservoirCountLaw n
      (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
        (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
        (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
          (radiusDual n rho) true)))
    (signedScoreHistogramReconstructionKernel n M) hrec₀ hrec₁
  have hcount := signedScoreReservoirCountLaw_tv_le n
    (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
      (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
      (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
        (radiusDual n rho) false))
    (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
      (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
      (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
        (radiusDual n rho) true))
  have htensorBase := signedScoreProductMixture_intensityPrior_tv_lt_one_quarter
    n rho (selectedGamma n rho) hn ⟨hrho.1, hrho.2⟩
      (selectedGamma_mem_Icc n rho hn)
  have htensor : Causalean.Stat.tvDist
      (signedScoreProductMixtureLaw (n - 1)
        (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
          (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
          (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
            (radiusDual n rho) false)))
      (signedScoreProductMixtureLaw (n - 1)
        (signedScoreIntensityPrior converseKappa (selectedGamma n rho) rho
          (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
          (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
            (radiusDual n rho) true))) < 1 / 4 := by
    by_cases hgap : 0 ≤ dualTargetGap (dualInterval n rho)
        (dualDegree n rho) (radiusDual n rho)
    · simpa [orientedHypothesis, hgap, converseKappa,
        Causalean.Stat.tvDist, abs_sub_comm] using htensorBase
    · simpa [orientedHypothesis, hgap, converseKappa] using htensorBase
  exact lt_of_le_of_lt hprefix (by
    dsimp only [μ₀, μ₁, S]
    gcongr
    exact hcount.trans_lt htensor)

/-- Each selected latent prior pays at most the explicit doubled-mean Poisson
lower-tail bound after integrating over its random normalization scale. -/
lemma selectedPoissonLowerTail_integral_le_exp
    (n : ℕ) (rho : ℝ) (h : Bool) (hn : 3 ≤ n) :
    (∫ theta, (poissonMeasure
        (2 * (n : ℝ≥0) * Real.toNNReal
          (rawMassTotal n (dualDegree n rho) converseKappa theta))
        (Set.Iio n)).toReal ∂selectedLatentPrior n rho h) ≤
      Real.exp (-(n : ℝ) * (1 - Real.log 2)) := by
  have ha : 0 < dualInterval n rho := by
    unfold dualInterval
    have hdegree : 0 < (dualDegree n rho : ℝ) := by
      exact_mod_cast (show 0 < dualDegree n rho by
        unfold dualDegree
        omega)
    positivity
  have hJ : 1 ≤ dualDegree n rho := by
    unfold dualDegree
    exact le_trans (by decide : 1 ≤ 2) (le_max_left _ _)
  let μ := selectedLatentPrior n rho h
  let f : (Fin (n - 1) → LatentCell) → ℝ := fun theta =>
    (poissonMeasure
      (2 * (n : ℝ≥0) * Real.toNNReal
        (rawMassTotal n (dualDegree n rho) converseKappa theta))
      (Set.Iio n)).toReal
  let c := Real.exp (-(n : ℝ) * (1 - Real.log 2))
  let _ : IsProbabilityMeasure μ :=
    latentProductPrior_isProbabilityMeasure n (dualInterval n rho)
      (dualDegree n rho) (radiusDual n rho)
      (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
        (radiusDual n rho) h) ha hJ
  have hfmeas : AEMeasurable f μ := by
    exact latentProductPrior_aemeasurable n (dualInterval n rho)
      (dualDegree n rho) (radiusDual n rho)
      (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
        (radiusDual n rho) h) ha hJ _
  have hfc : ∀ᵐ theta ∂μ, f theta ≤ c := by
    filter_upwards [selectedLatentPrior_ae_admissible n rho h] with theta hadm
    have htail := rawMassTotal_poisson_lower_tail n (dualDegree n rho)
      converseKappa theta (by omega) (by unfold converseKappa; norm_num) hadm.1
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top htail
    simpa only [f, c, ENNReal.toReal_ofReal (Real.exp_pos _).le] using hreal
  have hfnorm : ∀ᵐ theta ∂μ, ‖f theta‖ ≤ c := by
    filter_upwards [hfc] with theta htheta
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact htheta
  have hfint : Integrable f μ :=
    (integrable_const c).mono' hfmeas.aestronglyMeasurable hfnorm
  have hcint : Integrable (fun _ : Fin (n - 1) → LatentCell => c) μ :=
    integrable_const c
  have hint := integral_mono_ae hfint hcint hfc
  simpa only [μ, f, c, integral_const, measureReal_def,
    IsProbabilityMeasure.measure_univ, ENNReal.toReal_one, one_smul] using hint

/-- Substituting the two integrated tail bounds gives the fully numerical
selected fixed-mixture comparison. -/
lemma selectedFixedMixture_tv_lt_one_quarter_add_two_exp
    (n : ℕ) (rho : ℝ) (hn : 3 ≤ n)
    (P₀ : Kernel (Fin (n - 1) → LatentCell) (SampleObs n))
    (P₁ : Kernel (Fin (n - 1) → LatentCell) (SampleObs n))
    [∀ theta, IsProbabilityMeasure (P₀ theta)]
    [∀ theta, IsProbabilityMeasure (P₁ theta)]
    (hTV : Causalean.Stat.tvDist
        (fixedMixture (selectedLatentPrior n rho false) P₀ n)
        (fixedMixture (selectedLatentPrior n rho true) P₁ n) <
      1 / 4 +
        (∫ theta, (poissonMeasure
          (2 * (n : ℝ≥0) * Real.toNNReal
            (rawMassTotal n (dualDegree n rho) converseKappa theta))
          (Set.Iio n)).toReal ∂selectedLatentPrior n rho false) +
        ∫ theta, (poissonMeasure
          (2 * (n : ℝ≥0) * Real.toNNReal
            (rawMassTotal n (dualDegree n rho) converseKappa theta))
          (Set.Iio n)).toReal ∂selectedLatentPrior n rho true) :
    Causalean.Stat.tvDist
        (fixedMixture (selectedLatentPrior n rho false) P₀ n)
        (fixedMixture (selectedLatentPrior n rho true) P₁ n) <
      1 / 4 + 2 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) := by
  have htail₀ := selectedPoissonLowerTail_integral_le_exp n rho false hn
  have htail₁ := selectedPoissonLowerTail_integral_le_exp n rho true hn
  exact hTV.trans_le (by linarith)

end CausalSmith.Stat.SparseheterogeneityCriticalRadius

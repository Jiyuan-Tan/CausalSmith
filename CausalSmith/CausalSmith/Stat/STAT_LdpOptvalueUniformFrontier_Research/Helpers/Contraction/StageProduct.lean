module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.StageTransition

/-!
# Sequential products of stage densities

A structural prefix construction carries row-level Radon–Nikodym densities through
adaptive history extension. The density is an explicit product of the stage factors.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Assume [the density or prior under consideration](hyp:p), [measurability of p](hyp:hp), [the function f](hyp:f), [measurability of f](hyp:hf), and [the stated hrow condition](hyp:hrow). [Weighting the preceding history and the conditional next-message law multiplies their densities, including for kernels depending on the whole history](goal). -/
-- @node: stage_density_compProd
lemma stage_density_compProd {H Z : Type*} [MeasurableSpace H] [MeasurableSpace Z]
    (mu : Measure H) [SFinite mu] (K L : Kernel H Z)
    [IsSFiniteKernel K] [IsSFiniteKernel L]
    (p : H → ℝ≥0∞) (hp : Measurable p) [SFinite (mu.withDensity p)]
    (f : H × Z → ℝ≥0∞) (hf : Measurable f)
    (hrow : ∀ h, (K h).withDensity (fun z => f (h,z)) = L h) :
    (mu.withDensity p) ⊗ₘ L =
      (mu ⊗ₘ K).withDensity (fun w => p w.1 * f w) := by
  ext E hE
  rw [Measure.compProd_apply hE,
    lintegral_withDensity_eq_lintegral_mul _ hp (Kernel.measurable_kernel_prodMk_left hE),
    withDensity_apply _ hE, ← lintegral_indicator hE,
    ]
  rw [Measure.lintegral_compProd]
  swap
  · exact (((hp.comp measurable_fst).mul hf).indicator hE)
  apply lintegral_congr
  intro h
  change p h * (L h) (Prod.mk h ⁻¹' E) = _
  rw [← hrow h, withDensity_apply _ (hE.preimage measurable_prodMk_left)]
  rw [← lintegral_indicator (hE.preimage measurable_prodMk_left)]
  rw [← lintegral_const_mul]
  rotate_left
  · exact ((hf.comp (measurable_prodMk_left (x := h))).indicator
      (hE.preimage measurable_prodMk_left))
  apply lintegral_congr
  intro z
  by_cases hw : (h,z) ∈ E <;> simp [Set.indicator, hw]

/-- Assume [measurability of g](hyp:hg), [the density or prior under consideration](hyp:p), and [measurability of p](hyp:hp). [A density which is measurable on the target space commutes with pushforward when pulled back along the history-extension map](goal). -/
-- @node: stage_density_map
lemma stage_density_map {H Z : Type*} [MeasurableSpace H] [MeasurableSpace Z]
    (mu : Measure H) (g : H → Z) (hg : Measurable g)
    (p : Z → ℝ≥0∞) (hp : Measurable p) :
    (mu.withDensity (fun h => p (g h))).map g = (mu.map g).withDensity p := by
  ext E hE
  rw [Measure.map_apply hg hE, withDensity_apply _ (hE.preimage hg),
    withDensity_apply _ hE, ← lintegral_indicator hE,
    lintegral_map (hp.indicator hE) hg,
    ← lintegral_indicator (hE.preimage hg)]
  apply lintegral_congr
  intro h
  rfl

/-- Fix [the function f](hyp:f), [the order](hyp:k), and [order no larger than the sample size](hyp:hk). [The prefix density is constructed structurally by multiplying the next factor by the density of the preceding prefix](goal). -/
-- @node: sequentialPrefixDensity
def sequentialPrefixDensity {n : ℕ} {Z : Fin n → Type*}
    (f : (i : Fin n) → History Z i.val (Nat.le_of_lt i.isLt) × Z i → ℝ≥0∞)
    (k : ℕ) (hk : k ≤ n) : History Z k hk → ℝ≥0∞ :=
  Nat.rec (motive := fun j => (hj : j ≤ n) → History Z j hj → ℝ≥0∞)
    (fun _ _ => 1)
    (fun _ prev hj u => prev (Nat.le_of_succ_le hj) (init hj u) *
      f (nextIndex hj) (init hj u, last hj u)) k hk

/-- [The prefix product formed from a stage-density family](hyp:f) [is measurable](goal) when [each stage density is measurable](hyp:hf) and [the prefix length does not exceed the horizon](hyp:hk). -/
-- @node: measurable_sequentialPrefixDensity
@[fun_prop] lemma measurable_sequentialPrefixDensity {n : ℕ} {Z : Fin n → Type*}
    [∀ i, MeasurableSpace (Z i)]
    (f : (i : Fin n) → History Z i.val (Nat.le_of_lt i.isLt) × Z i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (k : ℕ) (hk : k ≤ n) :
    Measurable (sequentialPrefixDensity f k hk) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact ((ih _).comp (measurable_fst.comp (measurable_init_last hk))).mul
      ((hf _).comp (measurable_init_last hk))

/-- Assume [the function f](hyp:f) and [one plus the stage index no larger than the sample size](hyp:hk). [Appending a message exposes exactly the preceding product and the new factor](goal). -/
-- @node: sequentialPrefixDensity_snoc
lemma sequentialPrefixDensity_snoc {n : ℕ} {Z : Fin n → Type*}
    (f : (i : Fin n) → History Z i.val (Nat.le_of_lt i.isLt) × Z i → ℝ≥0∞)
    (k : ℕ) (hk : k + 1 ≤ n)
    (u : History Z k (Nat.le_of_succ_le hk)) (z : Z (nextIndex hk)) :
    sequentialPrefixDensity f (k+1) hk (snoc hk u z) =
      sequentialPrefixDensity f k (Nat.le_of_succ_le hk) u * f (nextIndex hk) (u,z) := by
  have hi : init hk (snoc hk u z) = u := by
    exact Fin.init_snoc (α := fun j : Fin (k+1) => Z (Fin.castLE hk j)) (p := u) (x := z)
  have hl : last hk (snoc hk u z) = z := by
    exact Fin.snoc_last (α := fun j : Fin (k+1) => Z (Fin.castLE hk j)) (p := u) (x := z)
  change sequentialPrefixDensity f k _ (init hk (snoc hk u z)) *
    f (nextIndex hk) (init hk (snoc hk u z), last hk (snoc hk u z)) = _
  rw [hi, hl]

/-- Assume [the Markov kernel hK](hyp:hK), [the Markov kernel hL](hyp:hL), [the function f](hyp:f), [measurability of f](hyp:hf), [the stated hrow condition](hyp:hrow), and [order no larger than the sample size](hyp:hk). [Iterating the row density identities gives an explicit density for every finite prefix of the adaptive experiment. No transcript RN witness is chosen](goal). -/
-- @node: sequentialPrefixDensity_withDensity
lemma sequentialPrefixDensity_withDensity {n : ℕ} {X Y : Type*} {Z : Fin n → Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [∀ i, MeasurableSpace (Z i)]
    (K : KernelFamily X Z) (L : KernelFamily Y Z) (hK : ∀ i, IsMarkovKernel (K i))
    (hL : ∀ i, IsMarkovKernel (L i)) (x : Fin n → X) (y : Fin n → Y)
    (f : (i : Fin n) → History Z i.val (Nat.le_of_lt i.isLt) × Z i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i))
    (hrow : ∀ i u, (K i (x i,u)).withDensity (fun z => f i (u,z)) = L i (y i,u))
    (k : ℕ) (hk : k ≤ n) :
    (prefixLaw K x k hk).withDensity (sequentialPrefixDensity f k hk) =
      prefixLaw L y k hk := by
  induction k with
  | zero => change (Measure.dirac _).withDensity (fun _ => 1) = Measure.dirac _
            exact withDensity_one
  | succ k ih =>
    let i : Fin n := ⟨k, Nat.lt_of_succ_le hk⟩
    let K' := (K i).comap (fun u => (x i,u)) (by fun_prop)
    let L' := (L i).comap (fun u => (y i,u)) (by fun_prop)
    let mu := prefixLaw K x k (Nat.le_of_succ_le hk)
    let p := sequentialPrefixDensity f k (Nat.le_of_succ_le hk)
    have := hK i
    have := hL i
    have := isProbabilityMeasure_prefixLaw K hK x k (Nat.le_of_succ_le hk)
    have := isProbabilityMeasure_prefixLaw L hL y k (Nat.le_of_succ_le hk)
    have hprev : mu.withDensity p = prefixLaw L y k (Nat.le_of_succ_le hk) := ih _
    have : IsProbabilityMeasure (mu.withDensity p) := hprev ▸ inferInstance
    have : IsMarkovKernel K' := by dsimp [K']; infer_instance
    have : IsMarkovKernel L' := by dsimp [L']; infer_instance
    have hstep := stage_density_compProd mu K' L' p
      (measurable_sequentialPrefixDensity f hf _ _) (f i) (hf i) (hrow i)
    rw [prefixLaw_succ, prefixLaw_succ]
    change ((mu ⊗ₘ K').map (fun w => snoc hk w.1 w.2)).withDensity
      (sequentialPrefixDensity f (k+1) hk) =
      ((prefixLaw L y k _ ⊗ₘ L').map (fun w => snoc hk w.1 w.2))
    rw [← hprev, hstep]
    have hpull : (fun w => p w.1 * f i w) =
        (fun w => sequentialPrefixDensity f (k+1) hk (snoc hk w.1 w.2)) := by
      funext w
      exact (sequentialPrefixDensity_snoc f k hk w.1 w.2).symm
    rw [hpull]
    simpa only [i, nextIndex] using
      (stage_density_map (mu ⊗ₘ K') (fun w => snoc hk w.1 w.2)
        (measurable_snoc hk) _ (measurable_sequentialPrefixDensity f hf _ _)).symm

/-- Assume [the function f](hyp:f) and [order no larger than the sample size](hyp:hk). [The structural prefix construction is the finite product of the densities evaluated at their own stage message and preceding history](goal). -/
-- @node: sequentialPrefixDensity_eq_prod
lemma sequentialPrefixDensity_eq_prod {n : ℕ} {Z : Fin n → Type*}
    (f : (i : Fin n) → History Z i.val (Nat.le_of_lt i.isLt) × Z i → ℝ≥0∞)
    (k : ℕ) (hk : k ≤ n) (u : History Z k hk) :
    sequentialPrefixDensity f k hk u = ∏ i : Fin k,
      f (Fin.castLE hk i)
        (restrictHistory (Nat.le_of_lt (Fin.castLE hk i).isLt) hk (Nat.le_of_lt i.isLt) u, u i) := by
  induction k with
  | zero => simp [sequentialPrefixDensity]
  | succ k ih =>
    change sequentialPrefixDensity f k _ (init hk u) *
      f (nextIndex hk) (init hk u, last hk u) = _
    rw [ih, Fin.prod_univ_castSucc]
    congr 1

/-- Fix [the local protocol Q](hyp:Q) and [the public seed](hyp:r). [The uniform next-message kernels generate a fixed-seed reference chain](goal). -/
-- @node: stageReferenceTranscriptLaw
def stageReferenceTranscriptLaw {n d : ℕ} (Q : LocalProtocol n (ObsRecord d))
    (r : Q.Seed) : Measure (ProtocolTranscript Q) :=
  transcriptLaw (stageReferenceKernel Q) (fun _ => r)

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [positive dimension](hyp:hd), [a nonnegative privacy budget](hyp:heps), and [sequential local privacy of the protocol](hyp:hQ). [Repaired stage rows yield explicit product densities for every fixed paired input transcript, relative to the same uniform reference chain](goal). -/
-- @node: fixedPairedTranscript_product_density_of_gate
lemma fixedPairedTranscript_product_density_of_gate (hRN : MeasurableKernelRadonNikodym)
    {n d : ℕ} (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d)
    (eps : ℝ) (heps : 0 ≤ eps) (hQ : SequentialClass Q eps) :
    ∃ f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ,
      (∀ i, Measurable (f i)) ∧
      (∀ i w, Real.exp (-eps) ≤ f i w ∧ f i w ≤ Real.exp eps) ∧
      (∀ i r eta z, (∑ a : PairedSymbol d, f i (((a,r),eta),z)) = (2*d : ℝ)) ∧
      (∀ i a b r eta z,
        f i (((a,r),eta),z) ≤ Real.exp eps * f i (((b,r),eta),z)) ∧
      (∀ i a r eta, (stageReferenceKernel Q i (r,eta)).withDensity
        (fun z => ENNReal.ofReal (f i (((a,r),eta),z))) =
          averagedKernel Q i ((a,r),eta)) ∧
      ∀ (a : Fin n → PairedSymbol d) (r : Q.Seed),
        (stageReferenceTranscriptLaw Q r).withDensity (fun z =>
          ENNReal.ofReal (∏ i : Fin n,
            f i (((a i,r),take (Nat.le_of_lt i.isLt) z),z i))) =
          fixedTranscriptLaw (averagedProtocol Q) a r := by
  choose f hf hf0 hsum hpriv hbound hrep using
    (fun i => stage_density_repaired_of_gate hRN Q i hd eps heps hQ)
  refine ⟨f, hf, hbound, hsum, hpriv, hrep, ?_⟩
  intro a r
  let g := fun (i : Fin n) (w : ProtocolHistory Q i × Q.Message i) =>
    ENNReal.ofReal (f i (((a i,r),w.1),w.2))
  have hg : ∀ i, Measurable (g i) := fun i => (hf i |>.comp (by fun_prop)).ennreal_ofReal
  have hprod := sequentialPrefixDensity_withDensity (stageReferenceKernel Q)
    (averagedKernel Q) (fun i => stageReferenceKernel_markov Q i hd)
    (averagedKernel_markov Q) (fun _ => r) (fun i => (a i,r)) g hg
    (fun i eta => hrep i (a i) r eta) n le_rfl
  change (stageReferenceTranscriptLaw Q r).withDensity
    (sequentialPrefixDensity g n le_rfl) = _ at hprod
  have hfun : (fun z : ProtocolTranscript Q => ENNReal.ofReal (∏ i : Fin n,
      f i (((a i,r),take (Nat.le_of_lt i.isLt) z),z i))) =
      sequentialPrefixDensity g n le_rfl := by
    funext z
    rw [sequentialPrefixDensity_eq_prod]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hf0 i _)]
    rfl
  rw [hfun]
  exact hprod

/-- Assume [the stated htheta condition](hyp:htheta), [positive dimension](hyp:hd), [measurability of f](hyp:hf), [the stated hf0 condition](hyp:hf0), and [the function hrep](hyp:hrep). [The density of a paired iid transcript factors into the affine conditional message densities at its actual adaptive histories](goal). -/
-- @node: pairedTranscript_stageProduct_withDensity
lemma pairedTranscript_stageProduct_withDensity {n d : ℕ}
    (Q : LocalProtocol n (ObsRecord d)) (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (hd : 0 < d) (r : Q.Seed)
    (f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i w, 0 ≤ f i w)
    (hrep : ∀ (a : Fin n → PairedSymbol d),
      (stageReferenceTranscriptLaw Q r).withDensity (fun z =>
        ENNReal.ofReal (∏ i : Fin n,
          f i (((a i,r),take (Nat.le_of_lt i.isLt) z),z i))) =
        fixedTranscriptLaw (averagedProtocol Q) a r) :
    (stageReferenceTranscriptLaw Q r).withDensity (fun z => ENNReal.ofReal
      (∏ i : Fin n, stageMixtureDensity theta
        (fun a => f i (((a,r),take (Nat.le_of_lt i.isLt) z),z i)))) =
      (Measure.pi (fun _ : Fin n => pairedLaw theta)).bind
        (fun a => fixedTranscriptLaw (averagedProtocol Q) a r) := by
  let w := fun a : Fin n → PairedSymbol d => ∏ i : Fin n, stageInputWeight theta (a i)
  have hw : ∀ a, 0 ≤ w a := fun a =>
    Finset.prod_nonneg (fun i _ => stageInputWeight_nonneg theta htheta (a i))
  have hinput : atomLaw w = Measure.pi (fun _ : Fin n => pairedLaw theta) := by
    have : IsProbabilityMeasure (pairedLaw theta) := pairedFamily_subset_simplex hd (Set.mem_image_of_mem pairedLaw htheta)
    apply Measure.ext_of_singleton
    intro a
    have hatom {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
        (v : I → ℝ) (a : I) : atomLaw v {a} = ENNReal.ofReal (v a) := by
      classical
      simp [atomLaw, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply', Pi.single_apply]
    rw [hatom, Measure.pi_singleton]
    simp_rw [pairedLaw, hatom]
    exact ENNReal.ofReal_prod_of_nonneg (fun i _ =>
      stageInputWeight_nonneg theta htheta (a i))
  have hfinite := finite_weighted_density_bind (stageReferenceTranscriptLaw Q r) w hw
    (fun a z => ∏ i : Fin n, f i (((a i,r),take (Nat.le_of_lt i.isLt) z),z i))
    (fun a => by
      apply Finset.measurable_prod
      intro i _
      exact (hf i).comp (by
        apply Measurable.prodMk
        · apply Measurable.prodMk measurable_const
          exact measurable_restrictHistory _ _ _
        · exact measurable_pi_apply i))
    (fun a z => Finset.prod_nonneg (fun i _ => hf0 i _))
    (fun a => fixedTranscriptLaw (averagedProtocol Q) a r) (by fun_prop) hrep
  rw [hinput] at hfinite
  have hfactor (z : ProtocolTranscript Q) :
      (∑ a : Fin n → PairedSymbol d, w a *
        (∏ i : Fin n, f i (((a i,r),take (Nat.le_of_lt i.isLt) z),z i))) =
      ∏ i : Fin n, stageMixtureDensity theta
        (fun a => f i (((a,r),take (Nat.le_of_lt i.isLt) z),z i)) := by
    simp only [w, ← Finset.prod_mul_distrib, stageMixtureDensity]
    simpa using Finset.sum_prod_piFinset (Finset.univ : Finset (PairedSymbol d))
      (fun (i : Fin n) a => stageInputWeight theta a *
        f i (((a,r),take (Nat.le_of_lt i.isLt) z),z i))
  have heq : (fun z : ProtocolTranscript Q => ENNReal.ofReal
      (∑ a : Fin n → PairedSymbol d, w a *
        (∏ i : Fin n, f i (((a i,r),take (Nat.le_of_lt i.isLt) z),z i)))) =
      (fun z : ProtocolTranscript Q => ENNReal.ofReal (∏ i : Fin n,
        stageMixtureDensity theta (fun a => f i (((a,r),take (Nat.le_of_lt i.isLt) z),z i)))) :=
    funext (fun z => congrArg ENNReal.ofReal (hfactor z))
  have hmeasure := congrArg (fun p : ProtocolTranscript Q → ℝ≥0∞ =>
    (stageReferenceTranscriptLaw Q r).withDensity p) heq
  exact hmeasure.symm.trans hfinite

/-- Assume [positive dimension](hyp:hd), [measurability of f](hyp:hf), [the stated hf0 condition](hyp:hf0), [the stated hsum condition](hyp:hsum), and [the function hrep](hyp:hrep). [Exact uniform normalization identifies the reference chain as the zero-contrast iid paired experiment, at every seed](goal). -/
-- @node: stageReferenceTranscriptLaw_eq_zero_paired
lemma stageReferenceTranscriptLaw_eq_zero_paired {n d : ℕ}
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d) (r : Q.Seed)
    (f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i w, 0 ≤ f i w)
    (hsum : ∀ i eta z, (∑ a : PairedSymbol d, f i (((a,r),eta),z)) = (2*d : ℝ))
    (hrep : ∀ (a : Fin n → PairedSymbol d),
      (stageReferenceTranscriptLaw Q r).withDensity (fun z =>
        ENNReal.ofReal (∏ i : Fin n,
          f i (((a i,r),take (Nat.le_of_lt i.isLt) z),z i))) =
        fixedTranscriptLaw (averagedProtocol Q) a r) :
    stageReferenceTranscriptLaw Q r =
      (Measure.pi (fun _ : Fin n => pairedLaw (fun _ => 0))).bind
        (fun a => fixedTranscriptLaw (averagedProtocol Q) a r) := by
  have hcube : (fun _ : Fin d => (0 : ℝ)) ∈ parameterCube d := by
    intro j; constructor <;> norm_num
  have hzero (i : Fin n) (eta : ProtocolHistory Q i) (z : Q.Message i) :
      stageMixtureDensity (fun _ => 0) (fun a => f i (((a,r),eta),z)) = 1 := by
    rw [stageMixtureDensity_normalized hd _ _ (hsum i eta z)]
    simp
  have h := pairedTranscript_stageProduct_withDensity Q _ hcube hd r f hf hf0 hrep
  simp only [hzero, Finset.prod_const_one, ENNReal.ofReal_one] at h
  change (stageReferenceTranscriptLaw Q r).withDensity 1 = _ at h
  rw [withDensity_one] at h
  exact h

end CausalSmith.Stat.LdpOptvalueUniformFrontier

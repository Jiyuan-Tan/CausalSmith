module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PairVariance
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreExpectations
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreIntegrability
public import Causalean.Stat.Sample.PiTransport

/-! Exact transport and Hoeffding variance formulas for the two deterministic score blocks. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma
attribute [local instance] Classical.propDecidable

/-- Canonically enumerate the coordinates in one deterministic evaluation block. This statement assumes [the n parameter](hyp:n), [the b parameter](hyp:b). [This is the stated defined object](goal). -/
def evalBlockEquiv (n : ℕ) (b : Bool) : Fin (blockSize n) ≃ {i // i ∈ evalBlock n b} :=
  (Finset.orderIsoOfFin (evalBlock n b) (evalBlock_card n b)).toEquiv

/-- Extract one deterministic evaluation block as a sample indexed by its block size. This statement assumes [the n parameter](hyp:n), [the b parameter](hyp:b), [the data parameter](hyp:data). [This is the stated defined object](goal). -/
def extractEvalBlock (n : ℕ) (b : Bool) (data : Dataset n) : Fin (blockSize n) → Record :=
  fun i => data (evalBlockEquiv n b i).1

/-- A sum over a deterministic block is the corresponding sum over its canonical enumeration. [This is the stated conclusion](goal). -/
lemma evalBlock_sum_extract {E : Type*} [AddCommMonoid E]
    (n : ℕ) (b : Bool) (f : Fin n → E) :
    (∑ i ∈ evalBlock n b, f i) = ∑ k : Fin (blockSize n), f (evalBlockEquiv n b k).1 := by
  rw [Finset.sum_subtype (evalBlock n b) (fun _ => Iff.rfl)]
  symm
  exact Equiv.sum_comp (evalBlockEquiv n b) (fun i => f i.1)

/-- Ordered distinct-pair sums are preserved by the canonical block enumeration. [This is the stated conclusion](goal). -/
lemma evalBlock_pair_sum_extract {E : Type*} [AddCommMonoid E]
    (n : ℕ) (b : Bool) (f : Fin n → Fin n → E) :
    (∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i, f i j) =
      ∑ k : Fin (blockSize n), ∑ l ∈ Finset.univ.erase k,
        f (evalBlockEquiv n b k).1 (evalBlockEquiv n b l).1 := by
  classical
  rw [evalBlock_sum_extract]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_subtype (p := fun j : Fin n => j ∈
      (evalBlock n b).erase (evalBlockEquiv n b k).1)
    ((evalBlock n b).erase (evalBlockEquiv n b k).1) (fun _ => Iff.rfl)]
  let e : {j // j ∈ (evalBlock n b).erase (evalBlockEquiv n b k).1} ≃
      {l : Fin (blockSize n) // l ∈ Finset.univ.erase k} :=
    { toFun := fun j => ⟨(evalBlockEquiv n b).symm ⟨j.1, (Finset.mem_erase.mp j.2).2⟩,
        by simp only [Finset.mem_erase, Finset.mem_univ, and_true]
           intro h
           have h' : (evalBlockEquiv n b).symm ⟨j.1, (Finset.mem_erase.mp j.2).2⟩ = k := h
           have := congrArg (evalBlockEquiv n b) h'
           exact (Finset.mem_erase.mp j.2).1 (by simpa using congrArg Subtype.val this)⟩
      invFun := fun l => ⟨(evalBlockEquiv n b l.1).1,
        by simp only [Finset.mem_erase]
           refine ⟨?_, (evalBlockEquiv n b l.1).2⟩
           intro h
           have hh : (evalBlockEquiv n b l.1) = (evalBlockEquiv n b k) := Subtype.ext h
           have := congrArg (evalBlockEquiv n b).symm hh
           exact (Finset.mem_erase.mp l.2).1 (by simpa using this)⟩
      left_inv := fun j => by apply Subtype.ext; simp
      right_inv := fun l => by apply Subtype.ext; simp }
  rw [Finset.sum_subtype (p := fun l : Fin (blockSize n) => l ∈ Finset.univ.erase k)
    (Finset.univ.erase k) (fun _ => Iff.rfl)]
  exact Fintype.sum_equiv e _ _ (fun x => by simp [e])

/-- Extracting either evaluation block preserves the iid product law. [This is the stated conclusion](goal). -/
lemma extractEvalBlock_measurePreserving (n : ℕ) (b : Bool) (law : ObservedLaw) :
    MeasurePreserving (extractEvalBlock n b)
      (Measure.pi fun _ : Fin n => law.P)
      (Measure.pi fun _ : Fin (blockSize n) => law.P) := by
  let hr := Causalean.Stat.measurePreserving_pi_restrict_finset law.P (evalBlock n b)
  let he := MeasureTheory.measurePreserving_piCongrLeft
    (fun _ : Fin (blockSize n) => law.P) (evalBlockEquiv n b).symm
  convert he.comp hr using 1
  funext data i
  simp [extractEvalBlock, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]

/-- Average a scalar kernel over the ordered distinct pairs in one evaluation block. This statement assumes [the n parameter](hyp:n), [the b parameter](hyp:b), [the g parameter](hyp:g), [the data parameter](hyp:data). [This is the stated defined object](goal). -/
def evalBlockPairAverage (n : ℕ) (b : Bool) (g : Record → Record → ℝ)
    (data : Dataset n) : ℝ :=
  ((blockSize n:ℝ)*((blockSize n:ℝ)-1))⁻¹ *
    ∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i, g (data i) (data j)

/-- The block pair average is the standard ordered pair average of the extracted sample. [This is the stated conclusion](goal). -/
lemma evalBlockPairAverage_extract (n : ℕ) (b : Bool) (g : Record → Record → ℝ)
    (data : Dataset n) :
    evalBlockPairAverage n b g data =
      orderedPairAverage (blockSize n) g (extractEvalBlock n b data) := by
  unfold evalBlockPairAverage orderedPairAverage extractEvalBlock
  rw [evalBlock_pair_sum_extract]

/-- The exact Hoeffding variance identity holds on either deterministic evaluation block. This statement assumes [the hn condition](hyp:hn), [the hg condition](hyp:hg), [the hsym condition](hyp:hsym), [the hL2 condition](hyp:hL2). [This is the stated conclusion](goal). -/
lemma evalBlockPairAverage_variance (n : ℕ) (hn : 4 ≤ n) (b : Bool)
    (law : ObservedLaw) (g : Record → Record → ℝ)
    (hg : Measurable (fun z : Record × Record => g z.1 z.2))
    (hsym : ∀ x y, g x y = g y x)
    (hL2 : MemLp (fun z : Record × Record => g z.1 z.2) 2 (law.P.prod law.P)) :
    variance (evalBlockPairAverage n b g) (Measure.pi fun _ : Fin n => law.P) =
      4/(blockSize n:ℝ)*variance (singletonProjection law.P g) law.P+
      2/((blockSize n:ℝ)*((blockSize n:ℝ)-1))*
        (∫ z : Record × Record, canonicalProjection law.P g z.1 z.2^2 ∂law.P.prod law.P) := by
  have hs : 2 ≤ blockSize n := by unfold blockSize; omega
  have hmem := orderedPairAverage_memLp law.P g hL2 (blockSize n)
  have hp := extractEvalBlock_measurePreserving n b law
  have hv := hp.variance_fun_comp hmem.aemeasurable
  have he : (fun data => orderedPairAverage (blockSize n) g (extractEvalBlock n b data)) =
      evalBlockPairAverage n b g := by
    funext data
    exact (evalBlockPairAverage_extract n b g data).symm
  rw [he] at hv
  rw [hv]
  exact (hoeffding_pair_variance law.P g hg hsym hL2 (blockSize n) hs).2

/-- Singleton and canonical energy bounds imply the declared two-channel block variance bound. This statement assumes [the hn condition](hyp:hn), [the hg condition](hyp:hg), [the hsym condition](hyp:hsym), [the hL2 condition](hyp:hL2), [the h1 condition](hyp:h1), [the h2 condition](hyp:h2). [This is the stated conclusion](goal). -/
lemma evalBlockPairAverage_variance_le (n : ℕ) (hn : 4 ≤ n) (b : Bool)
    (law : ObservedLaw) (g : Record → Record → ℝ)
    (hg : Measurable (fun z : Record × Record => g z.1 z.2))
    (hsym : ∀ x y, g x y = g y x)
    (hL2 : MemLp (fun z : Record × Record => g z.1 z.2) 2 (law.P.prod law.P))
    (L1 L2 N : ℝ)
    (h1 : 4*variance (singletonProjection law.P g) law.P ≤ L1^2*N)
    (h2 : (∫ z : Record × Record,
      canonicalProjection law.P g z.1 z.2^2 ∂law.P.prod law.P) ≤ L2^2*N) :
    variance (evalBlockPairAverage n b g) (Measure.pi fun _ : Fin n => law.P) ≤
      (L1^2/(blockSize n:ℝ)+
        2*L2^2/((blockSize n:ℝ)*((blockSize n:ℝ)-1)))*N := by
  rw [evalBlockPairAverage_variance n hn b law g hg hsym hL2]
  have hs : (0:ℝ) < blockSize n := by
    exact_mod_cast (show 0 < blockSize n by unfold blockSize; omega)
  have hs1 : (0:ℝ) < (blockSize n:ℝ)-1 := by
    have : (2:ℝ) ≤ blockSize n := by
      exact_mod_cast (show 2 ≤ blockSize n by unfold blockSize; omega)
    linarith
  have h1' : 4/(blockSize n:ℝ)*variance (singletonProjection law.P g) law.P ≤
      1/(blockSize n:ℝ)*(L1^2*N) := by
    calc
      _ = 1/(blockSize n:ℝ)*(4*variance (singletonProjection law.P g) law.P) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  have h2' : 2/((blockSize n:ℝ)*((blockSize n:ℝ)-1))*
      (∫ z : Record × Record,
        canonicalProjection law.P g z.1 z.2^2 ∂law.P.prod law.P) ≤
      2/((blockSize n:ℝ)*((blockSize n:ℝ)-1))*(L2^2*N) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  calc
    _ ≤ 1/(blockSize n:ℝ)*(L1^2*N)+
        2/((blockSize n:ℝ)*((blockSize n:ℝ)-1))*(L2^2*N) := add_le_add h1' h2'
    _ = _ := by ring

/-- Add a one-record summand symmetrically to a pair kernel. This statement assumes [the h parameter](hyp:h), [the g parameter](hyp:g), [the o parameter](hyp:o), [the z parameter](hyp:z). [This is the stated defined object](goal). -/
def singletonAugmentedPair (h : Record → ℝ) (g : Record → Record → ℝ)
    (o z : Record) : ℝ := (h o+h z)/2+g o z

/-- Measurable one-record and pair summands give a measurable augmented pair kernel. This statement assumes [the hh condition](hyp:hh), [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
@[fun_prop] lemma singletonAugmentedPair_measurable (h : Record → ℝ)
    (g : Record → Record → ℝ) (hh : Measurable h)
    (hg : Measurable (fun z : Record × Record => g z.1 z.2)) :
    Measurable (fun z : Record × Record => singletonAugmentedPair h g z.1 z.2) := by
  exact (((hh.comp measurable_fst).add (hh.comp measurable_snd)).div_const 2).add hg

/-- Symmetry of the pair summand is preserved after adding the one-record summand. This statement assumes [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
lemma singletonAugmentedPair_symmetric (h : Record → ℝ) (g : Record → Record → ℝ)
    (hg : ∀ o z, g o z = g z o) :
    ∀ o z, singletonAugmentedPair h g o z = singletonAugmentedPair h g z o := by
  intro o z
  unfold singletonAugmentedPair
  rw [hg]
  ring

/-- Square integrability is preserved after symmetrically adding a one-record summand. This statement assumes [the hh condition](hyp:hh), [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
lemma singletonAugmentedPair_memLp (law : ObservedLaw) (h : Record → ℝ)
    (g : Record → Record → ℝ) (hh : MemLp h 2 law.P)
    (hg : MemLp (fun z : Record × Record => g z.1 z.2) 2 (law.P.prod law.P)) :
    MemLp (fun z : Record × Record => singletonAugmentedPair h g z.1 z.2) 2
      (law.P.prod law.P) := by
  unfold singletonAugmentedPair
  convert (((hh.comp_fst law.P).add (hh.comp_snd law.P)).const_mul (1/2)).add hg using 1
  funext z
  simp
  ring

/-- The pair mean of an augmented kernel is the sum of its one-record and pair means. This statement assumes [the hh condition](hyp:hh), [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
lemma pairMean_singletonAugmentedPair (law : ObservedLaw) (h : Record → ℝ)
    (g : Record → Record → ℝ) (hh : Integrable h law.P)
    (hg : Integrable (fun z : Record × Record => g z.1 z.2) (law.P.prod law.P)) :
    pairMean law.P (singletonAugmentedPair h g) =
      (∫ x, h x ∂law.P)+pairMean law.P g := by
  have hx : Integrable (fun z : Record × Record => h z.1) (law.P.prod law.P) :=
    hh.comp_fst law.P
  have hy : Integrable (fun z : Record × Record => h z.2) (law.P.prod law.P) :=
    hh.comp_snd law.P
  let a : Record × Record → ℝ := fun z => (h z.1+h z.2)/2
  have ha : Integrable a (law.P.prod law.P) := (hx.add hy).div_const 2
  have hai : (∫ z, a z ∂law.P.prod law.P) = ∫ x, h x ∂law.P := by
    dsimp [a]
    rw [integral_div, integral_add hx hy,
      integral_prod _ hx, integral_prod_symm _ hy]
    simp
  unfold pairMean
  change (∫ z : Record × Record, a z+g z.1 z.2 ∂law.P.prod law.P) = _
  rw [integral_add ha hg, hai]

/-- The singleton projection of an augmented kernel splits into its centered one-record term and the singleton projection of its pair term. This statement assumes [the hh condition](hyp:hh), [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
lemma singletonProjection_singletonAugmentedPair_ae (law : ObservedLaw)
    (h : Record → ℝ) (g : Record → Record → ℝ) (hh : Integrable h law.P)
    (hg : Integrable (fun z : Record × Record => g z.1 z.2) (law.P.prod law.P)) :
    ∀ᵐ x ∂law.P, singletonProjection law.P (singletonAugmentedPair h g) x =
      (h x-(∫ z, h z ∂law.P))/2+singletonProjection law.P g x := by
  filter_upwards [hg.prod_right_ae] with x hx
  let a : Record → ℝ := fun y => (h x+h y)/2
  have ha : Integrable a law.P := (integrable_const (h x)).add hh |>.div_const 2
  have hai : (∫ y, a y ∂law.P) = (h x+(∫ y, h y ∂law.P))/2 := by
    dsimp [a]
    rw [integral_div, integral_add (integrable_const (h x)) hh]
    simp
  unfold singletonProjection
  change (∫ y, singletonAugmentedPair h g x y ∂law.P)-
    pairMean law.P (singletonAugmentedPair h g) = _
  rw [pairMean_singletonAugmentedPair law h g hh hg]
  change (∫ y, a y+g x y ∂law.P)-_ = _
  rw [integral_add ha hx, hai]
  ring

/-- Adding a symmetrized one-record summand leaves the canonical pair projection unchanged almost everywhere. This statement assumes [the hhm condition](hyp:hhm), [the hgm condition](hyp:hgm), [the hh condition](hyp:hh), [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
lemma canonicalProjection_singletonAugmentedPair_ae (law : ObservedLaw)
    (h : Record → ℝ) (g : Record → Record → ℝ) (hhm : Measurable h)
    (hgm : Measurable (fun z : Record × Record => g z.1 z.2))
    (hh : Integrable h law.P)
    (hg : Integrable (fun z : Record × Record => g z.1 z.2) (law.P.prod law.P)) :
    ∀ᵐ z ∂law.P.prod law.P,
      canonicalProjection law.P (singletonAugmentedPair h g) z.1 z.2 =
        canonicalProjection law.P g z.1 z.2 := by
  have ham : Measurable (fun z : Record × Record =>
      singletonAugmentedPair h g z.1 z.2) :=
    singletonAugmentedPair_measurable h g hhm hgm
  have hsg : Measurable (singletonProjection law.P g) := by
    unfold singletonProjection
    exact hgm.stronglyMeasurable.integral_prod_right.measurable.sub measurable_const
  have hsa : Measurable (singletonProjection law.P (singletonAugmentedPair h g)) := by
    unfold singletonProjection
    exact ham.stronglyMeasurable.integral_prod_right.measurable.sub measurable_const
  have hcg : Measurable (fun z : Record × Record =>
      canonicalProjection law.P g z.1 z.2) := by
    unfold canonicalProjection
    exact ((hgm.sub measurable_const).sub (hsg.comp measurable_fst)).sub
      (hsg.comp measurable_snd)
  have hca : Measurable (fun z : Record × Record =>
      canonicalProjection law.P (singletonAugmentedPair h g) z.1 z.2) := by
    unfold canonicalProjection
    exact ((ham.sub measurable_const).sub (hsa.comp measurable_fst)).sub
      (hsa.comp measurable_snd)
  have hset : MeasurableSet {z : Record × Record |
      canonicalProjection law.P (singletonAugmentedPair h g) z.1 z.2 =
        canonicalProjection law.P g z.1 z.2} := by
    change MeasurableSet ((fun z : Record × Record =>
      (canonicalProjection law.P (singletonAugmentedPair h g) z.1 z.2,
        canonicalProjection law.P g z.1 z.2)) ⁻¹' Set.diagonal ℝ)
    exact measurableSet_diagonal.preimage (hca.prodMk hcg)
  have hs := singletonProjection_singletonAugmentedPair_ae law h g hh hg
  apply (MeasureTheory.Measure.ae_prod_iff_ae_ae hset).2
  filter_upwards [hs] with x hx
  filter_upwards [hs] with y hy
  unfold canonicalProjection
  change singletonAugmentedPair h g x y-pairMean law.P (singletonAugmentedPair h g)-
      singletonProjection law.P (singletonAugmentedPair h g) x-
      singletonProjection law.P (singletonAugmentedPair h g) y = _
  rw [pairMean_singletonAugmentedPair law h g hh hg, hx, hy]
  unfold singletonAugmentedPair
  ring

/-- Consequently the canonical energy of an augmented kernel is exactly the energy of its pair summand. This statement assumes [the hhm condition](hyp:hhm), [the hgm condition](hyp:hgm), [the hh condition](hyp:hh), [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
lemma canonicalProjection_singletonAugmentedPair_energy (law : ObservedLaw)
    (h : Record → ℝ) (g : Record → Record → ℝ) (hhm : Measurable h)
    (hgm : Measurable (fun z : Record × Record => g z.1 z.2))
    (hh : Integrable h law.P)
    (hg : Integrable (fun z : Record × Record => g z.1 z.2) (law.P.prod law.P)) :
    (∫ z : Record × Record,
      canonicalProjection law.P (singletonAugmentedPair h g) z.1 z.2^2
        ∂law.P.prod law.P) =
      ∫ z : Record × Record, canonicalProjection law.P g z.1 z.2^2
        ∂law.P.prod law.P := by
  apply integral_congr_ae
  filter_upwards [canonicalProjection_singletonAugmentedPair_ae law h g hhm hgm hh hg]
    with z hz
  rw [hz]

/-- A dyadic difference row has exact squared energy equal to its upper-minus-lower rank. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
lemma diffKernel_row_energy (K : ℕ) (hK : 0 < K) (x : unitInterval) :
    (∫ z, diffKernel K x z ^ 2 ∂design) = K := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hf : MemLp (fun z => projKernel (2*K) x z) 2 design :=
    (projKernel_memLp_top design (2*K) (fun _ => x) id measurable_const
      measurable_id).mono_exponent le_top
  have hc : MemLp (fun z => projKernel K x z) 2 design :=
    (projKernel_memLp_top design K (fun _ => x) id measurable_const
      measurable_id).mono_exponent le_top
  have hcross : Integrable (fun z =>
      projKernel (2*K) x z*projKernel K x z) design := hf.integrable_mul hc
  have hcross' : Integrable (fun z =>
      2*(projKernel K x z*projKernel (2*K) z x)) design := by
    convert hcross.const_mul 2 using 1
    funext z
    rw [(histogram_kernel_bounds (2*K) (by positivity) x z).1]
    ring
  have he (z : unitInterval) : diffKernel K x z ^ 2 =
      projKernel (2*K) x z^2+projKernel K x z^2-
        2*(projKernel K x z*projKernel (2*K) z x) := by
    unfold diffKernel
    rw [(histogram_kernel_bounds (2*K) (by positivity) x z).1]
    ring
  simp_rw [he]
  let F : unitInterval → ℝ := fun z =>
    projKernel (2*K) x z^2+projKernel K x z^2
  let G : unitInterval → ℝ := fun z =>
    2*(projKernel K x z*projKernel (2*K) z x)
  have hF : Integrable F design := hf.integrable_sq.add hc.integrable_sq
  have hG : Integrable G design := hcross'
  change (∫ z, F z-G z ∂design) = K
  rw [integral_sub hF hG]
  dsimp [F, G]
  change (∫ z, projKernel (2*K) x z^2+projKernel K x z^2 ∂design)-_ = K
  rw [integral_add hf.integrable_sq hc.integrable_sq,
    integral_const_mul,
    (projection_rows (2*K) (by positivity) x).2,
    (projection_rows K hK x).2,
    histogram_kernel_composition K (2*K) hK (by positivity) (by simp) x x]
  have hxx : projKernel K x x = K := by
    obtain ⟨j,hj,_⟩ := histogram_cell_unique K hK x
    rw [histogram_kernel_row K hK x j hj x, if_pos hj]
  rw [hxx]
  norm_num

/-- The common scalar mark used by both affine coefficients: clipped outcome for the intercept and treatment for the slope. This statement assumes [the T parameter](hyp:T), [the r parameter](hyp:r), [the o parameter](hyp:o). [This is the stated defined object](goal). -/
def scoreMark (T : ℝ) (r : Bool) (o : Record) : ℝ :=
  if r then treatment o else clipY T (Y o)

/-- Both affine marks obey the public conditional second-moment envelope. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
lemma scoreMark_conditional_sq_le (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (T : ℝ) (hT : 1 ≤ T) (r : Bool) :
    ∀ᵐ x ∂design,
      law.e x*(∫ y, scoreMark T r (x,true,y)^2 ∂law.Q true x)+
        (1-law.e x)*(∫ y, scoreMark T r (x,false,y)^2 ∂law.Q false x) ≤
          32*T^(2-v.p) := by
  have ht := conditional_truncation_moments v hv law hm.rawMoment T hT
  filter_upwards [ht true, ht false] with x hx1 hx0
  cases r
  · simp only [scoreMark, Bool.false_eq_true, ↓reduceIte, Y]
    have hn : 0 ≤ T^(2-v.p) := Real.rpow_nonneg (by linarith) _
    calc
      _ ≤ law.e x*(10*T^(2-v.p))+(1-law.e x)*(10*T^(2-v.p)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hx1.2.2 (law.e_range x).1)
          (mul_le_mul_of_nonneg_left hx0.2.2 (sub_nonneg.mpr (law.e_range x).2))
      _ ≤ 32*T^(2-v.p) := by ring_nf; nlinarith
  · simp only [scoreMark, ↓reduceIte, treatment, A, one_pow, integral_const,
      probReal_univ, one_smul, Bool.false_eq_true,
      zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, add_zero]
    have hpow : 1 ≤ T^(2-v.p) := Real.one_le_rpow hT (by linarith [hv.1.2])
    nlinarith [(law.e_range x).2]

/-- Averaging an augmented pair kernel exactly recovers its sample mean plus pair average. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
lemma evalBlockPairAverage_singletonAugmented (n : ℕ) (hn : 4 ≤ n) (b : Bool)
    (h : Record → ℝ) (g : Record → Record → ℝ) (data : Dataset n) :
    evalBlockPairAverage n b (singletonAugmentedPair h g) data =
      (blockSize n:ℝ)⁻¹*(∑ i ∈ evalBlock n b, h (data i))+
        evalBlockPairAverage n b g data := by
  classical
  have hsN : 2 ≤ blockSize n := by unfold blockSize; omega
  have hs : (blockSize n:ℝ) ≠ 0 := by exact_mod_cast (by omega : blockSize n ≠ 0)
  have hs1 : (blockSize n:ℝ)-1 ≠ 0 := by
    have : (2:ℝ) ≤ blockSize n := by exact_mod_cast hsN
    linarith
  have hrow (i : Fin n) (hi : i ∈ evalBlock n b) :
      (∑ j ∈ (evalBlock n b).erase i, h (data i)) =
        ((blockSize n:ℝ)-1)*h (data i) := by
    simp [Finset.card_erase_of_mem hi, evalBlock_card,
      Nat.cast_sub (by omega : 1 ≤ blockSize n)]
  have hswap :
      (∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i, h (data j)) =
      ∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i, h (data i) :=
    (score_pair_sum_swap (evalBlock n b) (fun _ j => h (data j))).symm
  have hdiv1 :
      (∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i, h (data i)/2) =
      (∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i, h (data i))/2 := by
    simp only [Finset.sum_div]
  have hdiv2 :
      (∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i, h (data j)/2) =
      (∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i, h (data j))/2 := by
    simp only [Finset.sum_div]
  have htotal :
      (∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i, h (data i)) =
      ((blockSize n:ℝ)-1)*(∑ i ∈ evalBlock n b, h (data i)) := by
    rw [Finset.sum_congr rfl hrow, ← Finset.mul_sum]
  unfold evalBlockPairAverage singletonAugmentedPair
  simp_rw [add_div]
  simp only [Finset.sum_add_distrib]
  rw [hdiv1, hdiv2, hswap, htotal]
  field_simp
  ring

/-- Scalarize the one-record part of a multiresolution affine coefficient. This statement assumes [the J parameter](hyp:J), [the T0 parameter](hyp:T0), [the r parameter](hyp:r), [the u parameter](hyp:u), [the o parameter](hyp:o). [This is the stated defined object](goal). -/
def multiresScalarSingle (J : ℕ) (T0 : ℝ) (r : Bool) (u : Vec J) (o : Record) : ℝ :=
  inner ℝ u (multiresSingleKernel J T0 r o)

/-- Scalarize the pair part of a multiresolution affine coefficient. This statement assumes [the J parameter](hyp:J), [the L parameter](hyp:L), [the T0 parameter](hyp:T0), [the T parameter](hyp:T), [the r parameter](hyp:r), [the u parameter](hyp:u), [the o parameter](hyp:o), [the z parameter](hyp:z). [This is the stated defined object](goal). -/
def multiresScalarPair (J L : ℕ) (T0 : ℝ) (T : Fin L → ℝ)
    (r : Bool) (u : Vec J) (o z : Record) : ℝ :=
  inner ℝ u (multiresPairKernel J L T0 T r o z)

/-- Package a scalar multiresolution coefficient as one symmetric pair kernel. This statement assumes [the J parameter](hyp:J), [the L parameter](hyp:L), [the T0 parameter](hyp:T0), [the T parameter](hyp:T), [the r parameter](hyp:r), [the u parameter](hyp:u). [This is the stated defined object](goal). -/
def multiresScalarKernel (J L : ℕ) (T0 : ℝ) (T : Fin L → ℝ)
    (r : Bool) (u : Vec J) : Record → Record → ℝ :=
  singletonAugmentedPair (multiresScalarSingle J T0 r u)
    (multiresScalarPair J L T0 T r u)

/-- The multiresolution coefficient is exactly the block average of its packaged pair kernel. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
lemma multiresScalarKernel_average (n J L : ℕ) (hn : 4 ≤ n) (b r : Bool)
    (T0 : ℝ) (T : Fin L → ℝ) (u : Vec J) (data : Dataset n) :
    evalBlockPairAverage n b (multiresScalarKernel J L T0 T r u) data =
      inner ℝ u (if r then
        multiresScore n b J L T0 T 0 data-multiresScore n b J L T0 T 1 data
        else multiresScore n b J L T0 T 0 data) := by
  unfold multiresScalarKernel
  rw [evalBlockPairAverage_singletonAugmented n hn]
  let A := fun c : ℝ =>
    (blockSize n:ℝ)⁻¹ • ∑ i ∈ evalBlock n b,
        (multiresSingleKernel J T0 false (data i)-c • multiresSingleKernel J T0 true (data i))+
      ((blockSize n:ℝ)*((blockSize n:ℝ)-1))⁻¹ •
        ∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i,
        (multiresPairKernel J L T0 T false (data i) (data j)-
          c • multiresPairKernel J L T0 T true (data i) (data j))
  have hA (c : ℝ) : A c = multiresScore n b J L T0 T c data :=
    multiresScore_kernel_average n J L T0 T c data b hn
  cases r
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← hA 0]
    simp [A, multiresScalarSingle, multiresScalarPair, evalBlockPairAverage,
      inner_add_right, inner_smul_right, inner_sum]
  · simp only [↓reduceIte]
    rw [← hA 0, ← hA 1]
    simp [A, multiresScalarSingle, multiresScalarPair, evalBlockPairAverage,
      inner_add_right, inner_sub_right, inner_smul_right, inner_sum]
    ring

/-- Scalarize the pair part of a single-correction affine coefficient. This statement assumes [the J parameter](hyp:J), [the K parameter](hyp:K), [the T0 parameter](hyp:T0), [the r parameter](hyp:r), [the u parameter](hyp:u), [the o parameter](hyp:o), [the z parameter](hyp:z). [This is the stated defined object](goal). -/
def singleScalarPair (J K : ℕ) (T0 : ℝ) (r : Bool) (u : Vec J)
    (o z : Record) : ℝ := inner ℝ u (singlePairKernel J K T0 r o z)

/-- Package a scalar single-correction coefficient as one symmetric pair kernel. This statement assumes [the J parameter](hyp:J), [the K parameter](hyp:K), [the T0 parameter](hyp:T0), [the r parameter](hyp:r), [the u parameter](hyp:u). [This is the stated defined object](goal). -/
def singleScalarKernel (J K : ℕ) (T0 : ℝ) (r : Bool) (u : Vec J) :
    Record → Record → ℝ :=
  singletonAugmentedPair (multiresScalarSingle J T0 r u)
    (singleScalarPair J K T0 r u)

/-- The single-correction coefficient is exactly the block average of its packaged pair kernel. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
lemma singleScalarKernel_average (n J K : ℕ) (hn : 4 ≤ n) (b r : Bool)
    (T0 : ℝ) (u : Vec J) (data : Dataset n) :
    evalBlockPairAverage n b (singleScalarKernel J K T0 r u) data =
      inner ℝ u (if r then
        (hScore n b J T0 0 data-uScore n b J (projKernel K) T0 0 data)-
          (hScore n b J T0 1 data-uScore n b J (projKernel K) T0 1 data)
        else hScore n b J T0 0 data-uScore n b J (projKernel K) T0 0 data) := by
  unfold singleScalarKernel
  rw [evalBlockPairAverage_singletonAugmented n hn]
  let A := fun c : ℝ =>
    (blockSize n:ℝ)⁻¹ • ∑ i ∈ evalBlock n b,
        (multiresSingleKernel J T0 false (data i)-c • multiresSingleKernel J T0 true (data i))+
      ((blockSize n:ℝ)*((blockSize n:ℝ)-1))⁻¹ •
        ∑ i ∈ evalBlock n b, ∑ j ∈ (evalBlock n b).erase i,
        (singlePairKernel J K T0 false (data i) (data j)-
          c • singlePairKernel J K T0 true (data i) (data j))
  have hA (c : ℝ) : A c = hScore n b J T0 c data-uScore n b J (projKernel K) T0 c data :=
    singleScore_kernel_average n J K T0 c data b hn
  cases r
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← hA 0]
    simp [A, multiresScalarSingle, singleScalarPair, evalBlockPairAverage,
      inner_add_right, inner_smul_right, inner_sum]
  · simp only [↓reduceIte]
    rw [← hA 0, ← hA 1]
    simp [A, multiresScalarSingle, singleScalarPair, evalBlockPairAverage,
      inner_add_right, inner_sub_right, inner_smul_right, inner_sum]
    ring

/-- Select the packaged scalar kernel belonging to the active public score branch. This statement assumes [the n parameter](hyp:n), [the v parameter](hyp:v), [the r parameter](hyp:r), [the u parameter](hyp:u). [This is the stated defined object](goal). -/
def ledgerScalarKernel (n : ℕ) (v : Params) (r : Bool) (u : Vec (ledgerM n v)) :
    Record → Record → ℝ :=
  if singleBranch v then singleScalarKernel (ledgerM n v) (ledgerK n v)
      (ledgerT0 n v) r u
  else multiresScalarKernel (ledgerM n v) (ledgerL n v) (ledgerT0 n v)
      (fun j => ledgerT n v (j.val+1)) r u

/-- The scalar single-correction pair summand is symmetric. [This is the stated conclusion](goal). -/
lemma singleScalarPair_symmetric (J K : ℕ) (T0 : ℝ) (r : Bool) (u : Vec J) :
    ∀ o z, singleScalarPair J K T0 r u o z = singleScalarPair J K T0 r u z o := by
  intro o z
  simp only [singleScalarPair, singlePairKernel]
  rw [add_comm]

/-- The scalar multiresolution pair summand is symmetric. [This is the stated conclusion](goal). -/
lemma multiresScalarPair_symmetric (J L : ℕ) (T0 : ℝ) (T : Fin L → ℝ)
    (r : Bool) (u : Vec J) :
    ∀ o z, multiresScalarPair J L T0 T r u o z =
      multiresScalarPair J L T0 T r u z o := by
  intro o z
  simp only [multiresScalarPair, multiresPairKernel]
  rw [add_comm]

/-- The selected scalar ledger kernel is symmetric in its two records. [This is the stated conclusion](goal). -/
lemma ledgerScalarKernel_symmetric (n : ℕ) (v : Params) (r : Bool)
    (u : Vec (ledgerM n v)) :
    ∀ o z, ledgerScalarKernel n v r u o z = ledgerScalarKernel n v r u z o := by
  unfold ledgerScalarKernel
  split
  · exact singletonAugmentedPair_symmetric _ _ (singleScalarPair_symmetric _ _ _ _ _)
  · exact singletonAugmentedPair_symmetric _ _ (multiresScalarPair_symmetric _ _ _ _ _ _)

/-- The scalar one-record summand is measurable. [This is the stated conclusion](goal). -/
@[fun_prop] lemma multiresScalarSingle_measurable (J : ℕ) (T0 : ℝ) (r : Bool)
    (u : Vec J) : Measurable (multiresScalarSingle J T0 r u) := by
  have hm : Measurable (fun o : Record => if r then (1:ℝ) else clipY T0 (Y o)) := by
    cases r
    · simp only [Bool.false_eq_true, ↓reduceIte]
      unfold clipY Y
      fun_prop
    · simp only [↓reduceIte]
      fun_prop
  have hv : Measurable (fun o : Record => multiresSingleKernel J T0 r o) := by
    unfold multiresSingleKernel
    exact (measurable_treatment.mul hm).smul ((measurable_featureMap J).comp measurable_fst)
  exact (continuous_const.inner continuous_id).measurable.comp hv

/-- The scalar pair summand in the single-correction branch is measurable. [This is the stated conclusion](goal). -/
@[fun_prop] lemma singleScalarPair_measurable (J K : ℕ) (T0 : ℝ) (r : Bool)
    (u : Vec J) : Measurable (fun z : Record × Record =>
      singleScalarPair J K T0 r u z.1 z.2) := by
  let q : Record → ℝ := fun o => if r then treatment o else clipY T0 (Y o)
  have hq : Measurable q := by
    cases r <;> simp only [q, Bool.false_eq_true, ↓reduceIte]
    · unfold clipY Y; fun_prop
    · exact measurable_treatment
  let leg : Record → Record → Vec J := fun o z =>
    (treatment o*projKernel K (X o) (X z)*q z) • featureMap J (X o)
  have hl : Measurable (fun z : Record × Record => leg z.1 z.2) := by
    dsimp [leg]
    exact (((measurable_treatment.comp measurable_fst).mul
      ((measurable_projKernel K).comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd)))).mul (hq.comp measurable_snd)).smul
          ((measurable_featureMap J).comp (measurable_fst.comp measurable_fst))
  have hv : Measurable (fun z : Record × Record => singlePairKernel J K T0 r z.1 z.2) := by
    change Measurable (fun z : Record × Record => (-1/2:ℝ) • (leg z.1 z.2+leg z.2 z.1))
    exact (hl.add (hl.comp measurable_swap)).const_smul (-1/2:ℝ)
  exact (continuous_const.inner continuous_id).measurable.comp hv

/-- The scalar pair summand in the multiresolution branch is measurable. [This is the stated conclusion](goal). -/
@[fun_prop] lemma multiresScalarPair_measurable (J L : ℕ) (T0 : ℝ)
    (T : Fin L → ℝ) (r : Bool) (u : Vec J) : Measurable (fun z : Record × Record =>
      multiresScalarPair J L T0 T r u z.1 z.2) := by
  let q : ℝ → Record → ℝ := fun t o => if r then treatment o else clipY t (Y o)
  have hq (t : ℝ) : Measurable (q t) := by
    cases r <;> simp only [q, Bool.false_eq_true, ↓reduceIte]
    · unfold clipY Y; fun_prop
    · exact measurable_treatment
  let leg := fun (G : unitInterval → unitInterval → ℝ) (t : ℝ) (o z : Record) =>
    (treatment o*G (X o) (X z)*q t z) • featureMap J (X o)
  have hl (G : unitInterval → unitInterval → ℝ)
      (hG : Measurable (fun z : unitInterval × unitInterval => G z.1 z.2)) (t : ℝ) :
      Measurable (fun z : Record × Record => leg G t z.1 z.2) := by
    dsimp [leg]
    exact (((measurable_treatment.comp measurable_fst).mul
      (hG.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd)))).mul ((hq t).comp measurable_snd)).smul
          ((measurable_featureMap J).comp (measurable_fst.comp measurable_fst))
  let ordered := fun o z => -leg (projKernel J) T0 o z-
    ∑ j : Fin L, leg (diffKernel (2^j.val*J)) (T j) o z
  have ho : Measurable (fun z : Record × Record => ordered z.1 z.2) := by
    dsimp [ordered]
    exact (hl _ (measurable_projKernel J) _).neg.sub
      (Finset.measurable_sum Finset.univ (fun j _ => hl _
        ((measurable_projKernel (2*(2^j.val*J))).sub
          (measurable_projKernel (2^j.val*J))) _))
  have hv : Measurable (fun z : Record × Record =>
      multiresPairKernel J L T0 T r z.1 z.2) := by
    change Measurable (fun z : Record × Record => (1/2:ℝ) •
      (ordered z.1 z.2+ordered z.2 z.1))
    convert (ho.add (ho.comp measurable_swap)).const_smul (1/2:ℝ) using 1
    ext z
    simp [Function.comp_def, smul_add]
  exact (continuous_const.inner continuous_id).measurable.comp hv

/-- The selected scalar ledger kernel is measurable on a pair of records. [This is the stated conclusion](goal). -/
@[fun_prop] lemma ledgerScalarKernel_measurable (n : ℕ) (v : Params) (r : Bool)
    (u : Vec (ledgerM n v)) : Measurable (fun z : Record × Record =>
      ledgerScalarKernel n v r u z.1 z.2) := by
  unfold ledgerScalarKernel singleScalarKernel multiresScalarKernel
  split
  · exact singletonAugmentedPair_measurable _ _
      (multiresScalarSingle_measurable _ _ _ _) (singleScalarPair_measurable _ _ _ _ _)
  · exact singletonAugmentedPair_measurable _ _
      (multiresScalarSingle_measurable _ _ _ _) (multiresScalarPair_measurable _ _ _ _ _ _)

/-- The scalar one-record summand is square integrable under every observed law. [This is the stated conclusion](goal). -/
lemma multiresScalarSingle_memLp (law : ObservedLaw) (J : ℕ) (T0 : ℝ) (r : Bool)
    (u : Vec J) : MemLp (multiresScalarSingle J T0 r u) 2 law.P := by
  have hq : MemLp (fun o : Record => if r then (1:ℝ) else clipY T0 (Y o)) ∞ law.P := by
    cases r
    · simpa using clippedOutcome_memLp_top law.P T0 id measurable_id
    · simp only [↓reduceIte]
      exact memLp_top_const 1
  have hv : MemLp (fun o : Record => multiresSingleKernel J T0 r o) ∞ law.P := by
    unfold multiresSingleKernel
    exact (featureMap_memLp_top law.P J X measurable_fst).smul
      (hq.mul (r := ∞) (treatment_memLp_top law.P id measurable_id))
  exact (hv.const_inner u).mono_exponent le_top

/-- The scalar pair summand in the single-correction branch is square integrable. [This is the stated conclusion](goal). -/
lemma singleScalarPair_memLp (law : ObservedLaw) (J K : ℕ) (T0 : ℝ) (r : Bool)
    (u : Vec J) : MemLp (fun z : Record × Record =>
      singleScalarPair J K T0 r u z.1 z.2) 2 (law.P.prod law.P) := by
  let μ := law.P.prod law.P
  have hq : MemLp (fun z : Record × Record =>
      if r then treatment z.2 else clipY T0 (Y z.2)) ∞ μ := by
    cases r
    · simpa [μ] using clippedOutcome_memLp_top μ T0 Prod.snd measurable_snd
    · simp only [↓reduceIte]
      exact treatment_memLp_top μ Prod.snd measurable_snd
  let leg : Record × Record → Vec J := fun z =>
    (treatment z.1*projKernel K (X z.1) (X z.2)*
      (if r then treatment z.2 else clipY T0 (Y z.2))) • featureMap J (X z.1)
  have hleg : MemLp leg ∞ μ := by
    exact (featureMap_memLp_top μ J (X ∘ Prod.fst)
      (measurable_fst.comp measurable_fst)).smul
      (hq.mul (r := ∞) ((projKernel_memLp_top μ K (X ∘ Prod.fst) (X ∘ Prod.snd)
        (measurable_fst.comp measurable_fst) (measurable_fst.comp measurable_snd)).mul
          (r := ∞) (treatment_memLp_top μ Prod.fst measurable_fst)))
  have hswap : MemLp (fun z : Record × Record => leg z.swap) ∞ μ := by
    change MemLp (leg ∘ Prod.swap) ∞ μ
    exact hleg.comp_measurePreserving (Measure.measurePreserving_swap)
  have hv : MemLp (fun z : Record × Record => singlePairKernel J K T0 r z.1 z.2) ∞ μ := by
    change MemLp (fun z : Record × Record => (-1/2:ℝ) • (leg z+leg z.swap)) ∞ μ
    exact (hleg.add hswap).const_smul (-1/2:ℝ)
  exact (hv.const_inner u).mono_exponent le_top

/-- The scalar pair summand in the multiresolution branch is square integrable. [This is the stated conclusion](goal). -/
lemma multiresScalarPair_memLp (law : ObservedLaw) (J L : ℕ) (T0 : ℝ)
    (T : Fin L → ℝ) (r : Bool) (u : Vec J) : MemLp (fun z : Record × Record =>
      multiresScalarPair J L T0 T r u z.1 z.2) 2 (law.P.prod law.P) := by
  let μ := law.P.prod law.P
  let q : ℝ → Record × Record → ℝ := fun t z =>
    if r then treatment z.2 else clipY t (Y z.2)
  have hq (t : ℝ) : MemLp (q t) ∞ μ := by
    cases r
    · simpa [q, μ] using clippedOutcome_memLp_top μ t Prod.snd measurable_snd
    · simp only [q, ↓reduceIte]
      exact treatment_memLp_top μ Prod.snd measurable_snd
  let leg := fun (G : unitInterval → unitInterval → ℝ) (t : ℝ) (z : Record × Record) =>
    (treatment z.1*G (X z.1) (X z.2)*q t z) • featureMap J (X z.1)
  have hl (G : unitInterval → unitInterval → ℝ) (t : ℝ)
      (hG : MemLp (fun z : Record × Record => G (X z.1) (X z.2)) ∞ μ) :
      MemLp (leg G t) ∞ μ := by
    exact (featureMap_memLp_top μ J (X ∘ Prod.fst)
      (measurable_fst.comp measurable_fst)).smul
      ((hq t).mul (r := ∞) (hG.mul (r := ∞)
        (treatment_memLp_top μ Prod.fst measurable_fst)))
  have hord : MemLp (fun z : Record × Record =>
      -leg (projKernel J) T0 z-
        ∑ j : Fin L, leg (diffKernel (2^j.val*J)) (T j) z) ∞ μ := by
    apply MemLp.sub
    · exact (hl _ _ (projKernel_memLp_top μ J (X ∘ Prod.fst) (X ∘ Prod.snd)
          (measurable_fst.comp measurable_fst) (measurable_fst.comp measurable_snd))).neg
    · apply memLp_finsetSum
      intro j hj
      exact hl _ _ (diffKernel_memLp_top μ _ (X ∘ Prod.fst) (X ∘ Prod.snd)
        (measurable_fst.comp measurable_fst) (measurable_fst.comp measurable_snd))
  have hv : MemLp (fun z : Record × Record =>
      multiresPairKernel J L T0 T r z.1 z.2) ∞ μ := by
    let ordered : Record × Record → Vec J := fun z =>
      -leg (projKernel J) T0 z-∑ j : Fin L, leg (diffKernel (2^j.val*J)) (T j) z
    have hord' : MemLp ordered ∞ μ := hord
    have hswap : MemLp (fun z : Record × Record => ordered z.swap) ∞ μ := by
      change MemLp (ordered ∘ Prod.swap) ∞ μ
      exact hord'.comp_measurePreserving (Measure.measurePreserving_swap)
    change MemLp (fun z : Record × Record => (1/2:ℝ) •
      (ordered z+ordered z.swap)) ∞ μ
    exact (hord'.add hswap).const_smul (1/2:ℝ)
  exact (hv.const_inner u).mono_exponent le_top

/-- The selected scalar ledger kernel is square integrable under the record product law. [This is the stated conclusion](goal). -/
lemma ledgerScalarKernel_memLp (n : ℕ) (v : Params) (r : Bool)
    (law : ObservedLaw) (u : Vec (ledgerM n v)) : MemLp (fun z : Record × Record =>
      ledgerScalarKernel n v r u z.1 z.2) 2 (law.P.prod law.P) := by
  unfold ledgerScalarKernel singleScalarKernel multiresScalarKernel
  split
  · exact singletonAugmentedPair_memLp law _ _
      (multiresScalarSingle_memLp law _ _ _ _) (singleScalarPair_memLp law _ _ _ _ _)
  · exact singletonAugmentedPair_memLp law _ _
      (multiresScalarSingle_memLp law _ _ _ _) (multiresScalarPair_memLp law _ _ _ _ _ _)

end CausalSmith.Stat.FinitepHomogeneityDensegamma

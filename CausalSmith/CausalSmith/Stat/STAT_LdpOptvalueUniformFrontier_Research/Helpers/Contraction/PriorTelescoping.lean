module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.PriorAverage
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Product-prior coordinate telescoping

Intervening product priors replace coordinates one at a time. Independent
coordinate replacement identifies each adjacent density difference with the
averaged coordinate difference, so the exact L1 costs add over the dimension.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- [Replacing a coordinate by an independent draw updates its product-law factor](goal). -/
-- @node: productPrior_update_map
lemma productPrior_update_map (mu : Fin d → Measure ℝ)
    [∀ j, IsProbabilityMeasure (mu j)] (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (j : Fin d) :
    ((Measure.pi mu).prod nu).map (fun w => Function.update w.1 j w.2) =
      Measure.pi (Function.update mu j nu) := by
  classical
  haveI : ∀ i, IsProbabilityMeasure (Function.update mu j nu i) := by
    intro i
    by_cases hi : i = j
    · subst i; simpa using (inferInstance : IsProbabilityMeasure nu)
    · simpa [Function.update_of_ne hi] using (inferInstance : IsProbabilityMeasure (mu i))
  apply (Measure.pi_eq (μ := Function.update mu j nu) (fun s hs => ?_)).symm
  let t : Fin d → Set ℝ := fun i => if i = j then Set.univ else s i
  have hpre : (fun w : (Fin d → ℝ) × ℝ => Function.update w.1 j w.2) ⁻¹'
      (Set.univ.pi s) = (Set.univ.pi t) ×ˢ s j := by
    ext w
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_prod, t]
    constructor
    · intro hw
      constructor
      · intro i
        by_cases hi : i = j
        · simp [hi]
        · simpa [hi] using hw i
      · simpa using hw j
    · rintro ⟨hw, hj⟩ i
      by_cases hi : i = j
      · simpa [hi] using hj
      · simpa [hi] using hw i
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs), hpre,
    Measure.prod_prod, Measure.pi_pi]
  rw [← Finset.prod_erase_mul (s := Finset.univ)
    (f := fun i => mu i (t i)) (a := j) (by simp)]
  simp only [t, if_true, measure_univ, mul_one]
  rw [← Finset.prod_erase_mul (s := Finset.univ)
    (f := fun i => Function.update mu j nu i (s i)) (a := j) (by simp),
    Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp [Finset.ne_of_mem_erase hi]

/-- Assume [the probability law hg](hyp:hg). [Fubini turns an independent coordinate replacement into an updated product integral](goal). -/
-- @node: productPrior_update_integral
lemma productPrior_update_integral (mu : Fin d → Measure ℝ)
    [∀ j, IsProbabilityMeasure (mu j)] (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (j : Fin d) (g : (Fin d → ℝ) → ℝ)
    (hg : Integrable g (Measure.pi (Function.update mu j nu))) :
    (∫ theta, ∫ u, g (Function.update theta j u) ∂nu ∂Measure.pi mu) =
      ∫ theta, g theta ∂Measure.pi (Function.update mu j nu) := by
  have hmp : MeasurePreserving (fun w : (Fin d → ℝ) × ℝ =>
      Function.update w.1 j w.2) ((Measure.pi mu).prod nu)
      (Measure.pi (Function.update mu j nu)) :=
    ⟨by fun_prop, productPrior_update_map mu nu j⟩
  calc
    _ = ∫ w, g (Function.update w.1 j w.2) ∂(Measure.pi mu).prod nu := by
      simpa only [Function.comp_def] using
        (integral_prod _ (hmp.integrable_comp_of_integrable hg)).symm
    _ = ∫ theta, g theta ∂Measure.pi (Function.update mu j nu) := by
      rw [← productPrior_update_map mu nu j]
      exact (integral_map (by fun_prop) (by
        rw [productPrior_update_map mu nu j]
        exact hg.aestronglyMeasurable)).symm

/-- Fix [the probability law nu0 and the probability law nu1](hyp:nu0,nu1), [the natural-number parameter v](hyp:v), and [the coordinate index](hyp:j). [The first `v` coordinates use the second prior and all others use the first](goal). -/
-- @node: hybridCoordinatePrior
def hybridCoordinatePrior (nu0 nu1 : Measure ℝ) (v : ℕ) (j : Fin d) : Measure ℝ :=
  if j.val < v then nu1 else nu0

/-- Assume [the stated hnu0 condition](hyp:hnu0) and [the stated hnu1 condition](hyp:hnu1). [All intervening coordinate laws remain supported probability measures](goal). -/
-- @node: hybridCoordinatePrior_amplitude
lemma hybridCoordinatePrior_amplitude (a : ℝ) (nu0 nu1 : Measure ℝ)
    (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1) (v : ℕ) (j : Fin d) :
    AmplitudePrior a (hybridCoordinatePrior nu0 nu1 v j) := by
  unfold hybridCoordinatePrior
  split <;> assumption

/-- Assume [the stated ha condition](hyp:ha), [the stated hnu0 condition](hyp:hnu0), and [the stated hnu1 condition](hyp:hnu1). [Intervening product laws give full mass to the parameter cube](goal). -/
-- @node: amplitude_hybridPrior_ae_cube
lemma amplitude_hybridPrior_ae_cube (a : ℝ) (ha : a ≤ (1 / 2 : ℝ))
    (nu0 nu1 : Measure ℝ) (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1)
    (v : ℕ) :
    ∀ᵐ theta ∂Measure.pi (hybridCoordinatePrior (d := d) nu0 nu1 v),
      theta ∈ parameterCube d := by
  haveI : ∀ j : Fin d, IsProbabilityMeasure (hybridCoordinatePrior nu0 nu1 v j) :=
    fun j => (hybridCoordinatePrior_amplitude a nu0 nu1 hnu0 hnu1 v j).1
  have hcoord (j : Fin d) : ∀ᵐ u ∂hybridCoordinatePrior nu0 nu1 v j,
      u ∈ Set.Icc (-a) a :=
    ae_iff.mpr (hybridCoordinatePrior_amplitude a nu0 nu1 hnu0 hnu1 v j).2
  have hall := Filter.eventually_all.mpr (fun j : Fin d =>
    Measure.tendsto_eval_ae_ae.eventually (hcoord j))
  filter_upwards [hall] with theta htheta
  intro j
  exact ⟨by linarith [(htheta j).1], (htheta j).2.trans ha⟩

/-- Assume [the stated hv condition](hyp:hv). [The next hybrid law changes exactly the next coordinate](goal). -/
-- @node: hybridCoordinatePrior_succ
lemma hybridCoordinatePrior_succ (nu0 nu1 : Measure ℝ) (v : ℕ) (hv : v < d) :
    hybridCoordinatePrior (d := d) nu0 nu1 (v + 1) =
      Function.update (hybridCoordinatePrior nu0 nu1 v) ⟨v, hv⟩ nu1 := by
  classical
  funext j
  by_cases hj : j = ⟨v, hv⟩
  · subst j; simp [hybridCoordinatePrior]
  · have hval : j.val ≠ v := fun h => hj (Fin.ext h)
    simp only [Function.update_of_ne hj, hybridCoordinatePrior]
    have heq : (j.val < v + 1) ↔ (j.val < v) := by omega
    rw [if_congr heq rfl rfl]

/-- Assume [the stated hv condition](hyp:hv). [Resampling the next coordinate from the first prior leaves the current hybrid law unchanged](goal). -/
-- @node: hybridCoordinatePrior_update_first
lemma hybridCoordinatePrior_update_first (nu0 nu1 : Measure ℝ) (v : ℕ) (hv : v < d) :
    Function.update (hybridCoordinatePrior (d := d) nu0 nu1 v) ⟨v, hv⟩ nu0 =
      hybridCoordinatePrior nu0 nu1 v := by
  classical
  apply Function.update_eq_self_iff.mpr
  simp [hybridCoordinatePrior]


/-- Assume [positive dimension](hyp:hd) and [the function hpi](hyp:hpi). [A cube-supported probability law integrates every affine sample mass](goal). -/
-- @node: integrable_iidAffineMass_cube_prior
lemma integrable_iidAffineMass_cube_prior (hd : 0 < d)
    (pi : Measure (Fin d → ℝ)) [IsProbabilityMeasure pi]
    (hpi : ∀ᵐ theta ∂pi, theta ∈ parameterCube d) (o : Fin n → ObsRecord d) :
    Integrable (fun theta => iidAffineMass theta o) pi := by
  apply Integrable.of_bound (by
    have hm : Measurable (fun theta => iidAffineMass theta o) := by
      unfold iidAffineMass observedAffineMass
      fun_prop
    exact hm.aestronglyMeasurable) 1
  filter_upwards [hpi] with theta htheta
  exact iidAffineMass_abs_le_one hd theta htheta o

/-- Assume [positive dimension](hyp:hd) and [the function hpi](hyp:hpi). [Canonical densities are integrable in the prior parameter at every transcript](goal). -/
-- @node: integrable_canonicalTranscriptDensity_prior
lemma integrable_canonicalTranscriptDensity_prior {Q : LocalProtocol n (ObsRecord d)} (hd : 0 < d)
    (f : ((Fin n → ObsRecord d) × Q.Seed) × ProtocolTranscript Q → ℝ)
    (pi : Measure (Fin d → ℝ)) [IsProbabilityMeasure pi]
    (hpi : ∀ᵐ theta ∂pi, theta ∈ parameterCube d)
    (r : Q.Seed) (z : ProtocolTranscript Q) :
    Integrable (fun theta => canonicalTranscriptDensity f (theta, r, z)) pi := by
  unfold canonicalTranscriptDensity
  apply integrable_finsetSum
  intro o _
  exact (integrable_iidAffineMass_cube_prior hd pi hpi o).mul_const (f ((o,r),z))

/-- Assume [positive dimension](hyp:hd), [measurability of f](hyp:hf), [the function hf0](hyp:hf0), [the function hrow](hyp:hrow), and [the function hpi](hyp:hpi). [The finite-row representation makes each prior-averaged density integrable in the transcript](goal). -/
-- @node: integrable_canonicalTranscriptDensity_average
lemma integrable_canonicalTranscriptDensity_average
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d)
    (f : ((Fin n → ObsRecord d) × Q.Seed) × ProtocolTranscript Q → ℝ)
    (hf : Measurable f) (hf0 : ∀ w, 0 ≤ f w)
    (hrow : ∀ o r, (referenceLaw Q r).withDensity
      (fun z => ENNReal.ofReal (f ((o, r), z))) = fixedTranscriptLaw Q o r)
    (pi : Measure (Fin d → ℝ)) [IsProbabilityMeasure pi]
    (hpi : ∀ᵐ theta ∂pi, theta ∈ parameterCube d) (r : Q.Seed) :
    Integrable (fun z => ∫ theta, canonicalTranscriptDensity f (theta, r, z) ∂pi)
      (referenceLaw Q r) := by
  have heq (z : ProtocolTranscript Q) :
      (∫ theta, canonicalTranscriptDensity f (theta, r, z) ∂pi) =
      ∑ o, (∫ theta, iidAffineMass theta o ∂pi) * f ((o,r),z) := by
    unfold canonicalTranscriptDensity
    rw [integral_finsetSum]
    · simp_rw [integral_mul_const]
    · intro o _
      exact (integrable_iidAffineMass_cube_prior hd pi hpi o).mul_const (f ((o,r),z))
  simp_rw [heq]
  apply integrable_finsetSum
  intro o _
  exact (integrable_fixedTranscript_row_density Q f hf hf0 hrow o r).const_mul _

/-- Assume [the stated h condition](hyp:hH) and [the stated hstep condition](hyp:hstep). [The L1 triangle inequality adds the costs along a finite chain of densities](goal). -/
-- @node: integral_abs_chain_le
lemma integral_abs_chain_le {Z : Type*} [MeasurableSpace Z] (mu : Measure Z)
    (H : ℕ → Z → ℝ) (hH : ∀ v, Integrable (H v) mu) (D : ℕ) (B : ℝ)
    (hstep : ∀ v < D, (∫ z, |H v z - H (v+1) z| ∂mu) ≤ B) :
    (∫ z, |H 0 z - H D z| ∂mu) ≤ D * B := by
  have hchain : ∀ v ≤ D, (∫ z, |H 0 z - H v z| ∂mu) ≤ v * B := by
    intro v
    induction v with
    | zero => intro _; simp
    | succ v ih =>
      intro hv
      calc
        _ ≤ ∫ z, |H 0 z - H v z| + |H v z - H (v+1) z| ∂mu := by
          apply integral_mono ((hH 0).sub (hH (v+1))).abs
            (((hH 0).sub (hH v)).abs.add ((hH v).sub (hH (v+1))).abs)
          intro z
          change |H 0 z - H (v+1) z| ≤ |H 0 z - H v z| + |H v z - H (v+1) z|
          have heq : H 0 z - H (v+1) z = (H 0 z - H v z) + (H v z - H (v+1) z) := by ring
          rw [heq]
          exact abs_add_le _ _
        _ = (∫ z, |H 0 z - H v z| ∂mu) +
            ∫ z, |H v z - H (v+1) z| ∂mu :=
          integral_add ((hH 0).sub (hH v)).abs ((hH v).sub (hH (v+1))).abs
        _ ≤ v * B + B := add_le_add (ih (by omega)) (hstep v (by omega))
        _ = (v+1 : ℕ) * B := by push_cast; ring
  exact hchain D le_rfl

/-- Assume [a nonnegative privacy budget](hyp:heps), [positive dimension](hyp:hd), [measurability of f](hyp:hf), [the function hf0](hyp:hf0), [the function hrow](hyp:hrow), [the stated hcert condition](hyp:hcert), [amplitude between zero and one half](hyp:ha), [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), [the stated hk condition](hyp:hk), [order no larger than the sample size](hyp:hkn), and [the stated hmom condition](hyp:hmom). [Coordinate replacement and the exact averaged-coordinate bound telescope to an L1 bound for the two full product-prior densities at each fixed seed](goal). -/
-- @node: canonical_density_product_matching_L1
lemma canonical_density_product_matching_L1
    (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ) (heps : 0 ≤ eps) (hd : 0 < d)
    (f : ((Fin n → ObsRecord d) × Q.Seed) × ProtocolTranscript Q → ℝ)
    (hf : Measurable f) (hf0 : ∀ w, 0 ≤ f w)
    (hrow : ∀ o r, (referenceLaw Q r).withDensity
      (fun z => ENNReal.ofReal (f ((o, r), z))) = fixedTranscriptLaw Q o r)
    (hcert : DensityCertificate Q eps (canonicalTranscriptDensity f))
    (r : Q.Seed) (a : ℝ) (ha : a ∈ Set.Ioc 0 (1 / 2 : ℝ))
    (nu0 nu1 : Measure ℝ) (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hmom : MatchingMoments k nu0 nu1) :
    (∫ z, |(∫ theta, canonicalTranscriptDensity f (theta,r,z) ∂productPrior d nu0) -
      (∫ theta, canonicalTranscriptDensity f (theta,r,z) ∂productPrior d nu1)|
        ∂referenceLaw Q r) ≤
      2 * d * a^k * Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k := by
  classical
  letI := hnu0.1
  letI := hnu1.1
  let mu := hybridCoordinatePrior (d := d) nu0 nu1
  haveI hprob : ∀ v j, IsProbabilityMeasure (mu v j) :=
    fun v j => (hybridCoordinatePrior_amplitude a nu0 nu1 hnu0 hnu1 v j).1
  have hcube (v : ℕ) : ∀ᵐ theta ∂Measure.pi (mu v), theta ∈ parameterCube d :=
    amplitude_hybridPrior_ae_cube a ha.2 nu0 nu1 hnu0 hnu1 v
  let H := fun v z => ∫ theta, canonicalTranscriptDensity f (theta,r,z) ∂Measure.pi (mu v)
  have hH (v : ℕ) : Integrable (H v) (referenceLaw Q r) :=
    integrable_canonicalTranscriptDensity_average Q hd f hf hf0 hrow _ (hcube v) r
  have hstep (v : ℕ) (hv : v < d) :
      (∫ z, |H v z - H (v+1) z| ∂referenceLaw Q r) ≤
        2 * a^k * Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k := by
    let j : Fin d := ⟨v,hv⟩
    have heq (z : ProtocolTranscript Q) : H v z - H (v+1) z =
        ∫ theta, ((∫ u, canonicalTranscriptDensity f (Function.update theta j u,r,z) ∂nu0) -
          (∫ u, canonicalTranscriptDensity f (Function.update theta j u,r,z) ∂nu1))
            ∂Measure.pi (mu v) := by
      have h0 : Function.update (mu v) j nu0 = mu v :=
        hybridCoordinatePrior_update_first nu0 nu1 v hv
      have h1 : Function.update (mu v) j nu1 = mu (v+1) :=
        (hybridCoordinatePrior_succ nu0 nu1 v hv).symm
      have hi0 := integrable_canonicalTranscriptDensity_prior (Q := Q) hd f _ (hcube v) r z
      have hi1 := integrable_canonicalTranscriptDensity_prior (Q := Q) hd f _ (hcube (v+1)) r z
      have hp0 := productPrior_update_integral (mu v) nu0 j
        (fun theta => canonicalTranscriptDensity f (theta,r,z)) (h0.symm ▸ hi0)
      have hp1 := productPrior_update_integral (mu v) nu1 j
        (fun theta => canonicalTranscriptDensity f (theta,r,z)) (h1.symm ▸ hi1)
      have hmp0 : MeasurePreserving (fun w : (Fin d → ℝ) × ℝ => Function.update w.1 j w.2)
          ((Measure.pi (mu v)).prod nu0) (Measure.pi (mu v)) :=
        ⟨by fun_prop, by rw [productPrior_update_map, h0]⟩
      have hmp1 : MeasurePreserving (fun w : (Fin d → ℝ) × ℝ => Function.update w.1 j w.2)
          ((Measure.pi (mu v)).prod nu1) (Measure.pi (mu (v+1))) :=
        ⟨by fun_prop, by rw [productPrior_update_map, h1]⟩
      have hInt0 : Integrable (fun theta => ∫ u,
          canonicalTranscriptDensity f (Function.update theta j u,r,z) ∂nu0)
          (Measure.pi (mu v)) := by
        simpa only [Function.comp_def] using
          (hmp0.integrable_comp_of_integrable hi0).integral_prod_left
      have hInt1 : Integrable (fun theta => ∫ u,
          canonicalTranscriptDensity f (Function.update theta j u,r,z) ∂nu1)
          (Measure.pi (mu v)) := by
        simpa only [Function.comp_def] using
          (hmp1.integrable_comp_of_integrable hi1).integral_prod_left
      rw [integral_sub hInt0 hInt1, hp0, hp1, h0, h1]
    simp_rw [heq]
    exact canonical_density_averaged_coordinate_matching_L1 Q eps heps hd f hf hf0 hrow hcert
      (Measure.pi (mu v)) (hcube v) r j a ha nu0 nu1 hnu0 hnu1 k hk hkn hmom
  have hbound := integral_abs_chain_le (referenceLaw Q r) H hH d
    (2 * a^k * Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k) hstep
  have h0 : mu 0 = fun _ => nu0 := by funext j; simp [mu, hybridCoordinatePrior]
  have hd' : mu d = fun _ => nu1 := by
    funext j
    simp [mu, hybridCoordinatePrior, j.isLt]
  simpa only [H, h0, hd', productPrior] using
    (hbound.trans_eq (by ring))

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [sequential local privacy of the protocol](hyp:hQ), and [an admissible sample size, dimension, and privacy budget](hyp:hAllowed). [The RN gate supplies a canonical density certificate with the full product-prior L1 contraction bound at every seed](goal). -/
-- @node: density_product_matching_of_gate
lemma density_product_matching_of_gate (hRN : MeasurableKernelRadonNikodym)
    (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ) (hQ : SequentialClass Q eps)
    (hAllowed : Allowed n d eps) :
    ∃ p : (Fin d → ℝ) × Q.Seed × ProtocolTranscript Q → ℝ,
      DensityCertificate Q eps p ∧
      ∀ r, ∀ a ∈ Set.Ioc 0 (1 / 2 : ℝ), ∀ nu0 nu1 : Measure ℝ,
        AmplitudePrior a nu0 → AmplitudePrior a nu1 → ∀ k : ℕ,
        1 ≤ k → k ≤ n → MatchingMoments k nu0 nu1 →
        (∫ z, |(∫ theta, p (theta,r,z) ∂productPrior d nu0) -
          (∫ theta, p (theta,r,z) ∂productPrior d nu1)| ∂referenceLaw Q r) ≤
          2 * d * a^k * Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k := by
  obtain ⟨f, hf, hf0, hrow, hcert⟩ :=
    canonical_density_certificate_rows_of_gate hRN Q eps hQ hAllowed
  refine ⟨canonicalTranscriptDensity f, hcert, ?_⟩
  intro r a ha nu0 nu1 hnu0 hnu1 k hk hkn hmom
  exact canonical_density_product_matching_L1 Q eps (le_of_lt hAllowed.2.2.1)
    (by have := hAllowed.2.1; omega) f hf hf0 hrow hcert r a ha
      nu0 nu1 hnu0 hnu1 k hk hkn hmom

end CausalSmith.Stat.LdpOptvalueUniformFrontier

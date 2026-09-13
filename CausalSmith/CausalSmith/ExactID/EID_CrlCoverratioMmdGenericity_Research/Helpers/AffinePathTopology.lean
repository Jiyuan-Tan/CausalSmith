import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessPathRegularity
import Causalean.Mathlib.Topology.UniformConvergence.Affine
import Mathlib.Analysis.Calculus.TangentCone.Pi
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Topology of the affine witness path

This file records compact-uniform continuity of all six value and within-derivative coordinates of
the affine mechanism path, and hence continuity in the induced relative product `C²` topology.
-/

open Set Filter
open scoped Topology UniformConvergence

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- Restricting a differentiable function on the product cube to one coordinate turns its
within Fréchet derivative into evaluation on the corresponding coordinate basis vector.  Given [the stated inputs and conditions](hyp:hF,hv,hz), [the stated conclusion](goal) follows. -/
lemma derivWithin_coordinateSection_eq_fderivWithin_apply
    {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : DifferentiableOn ℝ F (latentCube n))
    {v : Fin n → ℝ} (hv : v ∈ latentCube n) (i : Fin n)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    derivWithin (fun y ↦ F (Function.update v i y)) (Set.Icc (0 : ℝ) 1) z =
      fderivWithin ℝ F (latentCube n) (Function.update v i z) (Pi.single i 1) := by
  have hmap : Set.MapsTo (Function.update v i) (Set.Icc (0 : ℝ) 1) (latentCube n) := by
    intro y hy k
    by_cases hki : k = i
    · subst k
      simpa using hy
    · simpa [Function.update, hki] using hv k
  have hcomp := (hF (Function.update v i z) (hmap hz)).hasFDerivWithinAt.comp z
    (hasDerivAt_update v i z).hasFDerivAt.hasFDerivWithinAt hmap
  simpa [Function.comp_def] using hcomp.hasDerivWithinAt.derivWithin
    ((uniqueDiffOn_Icc (by norm_num)).uniqueDiffWithinAt hz)

/-- Given [the selected directed edge](hyp:hji), the [observational-factor value coordinate of the
unrestricted affine path varies continuously in the compact-uniform topology](goal). -/
@[fun_prop] lemma continuous_affinePathExtension_p_values
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) (l : Fin n) :
    Continuous (fun t : ℝ => UniformOnFun.ofFun {latentCube n}
      ((affinePathExtension s θ hji t).p l)) := by
  apply Causalean.Mathlib.Topology.continuous_uniformOnFun_affine_of_compact
  · rw [latentCube]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  · exact ⟨0, fun _ _ => ⟨by norm_num, by norm_num⟩⟩
  · simpa only [smul_eq_mul] using (θ.property.positiveSmooth.2.2.1 l).continuousOn
  · exact ((embeddedSparseWitness_positive_normalized_smooth s hji).2.2.1 l).continuousOn

/-- Given [the selected directed edge](hyp:hji), the [intervention-factor value coordinate of the
unrestricted affine path varies continuously in the compact-uniform topology](goal). -/
@[fun_prop] lemma continuous_affinePathExtension_q_values
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) (l : Fin n) :
    Continuous (fun t : ℝ => UniformOnFun.ofFun {Set.Icc (0 : ℝ) 1}
      ((affinePathExtension s θ hji t).q l)) := by
  apply Causalean.Mathlib.Topology.continuous_uniformOnFun_affine_of_compact isCompact_Icc
    (nonempty_Icc.mpr (by norm_num))
  · simpa only [smul_eq_mul] using (θ.property.positiveSmooth.2.2.2.1 l).continuousOn
  · exact ((embeddedSparseWitness_positive_normalized_smooth s hji).2.2.2.1 l).continuousOn

/-- Given [the selected directed edge](hyp:hji), the [observational-factor first within-derivative
coordinate varies continuously along the unrestricted affine path](goal). -/
@[fun_prop] lemma continuous_affinePathExtension_p_fderivWithin
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) (l : Fin n) :
    Continuous (fun t : ℝ => UniformOnFun.ofFun {latentCube n}
      (fderivWithin ℝ ((affinePathExtension s θ hji t).p l) (latentCube n))) := by
  let hu : UniqueDiffOn ℝ (latentCube n) := by
    rw [latentCube]
    exact UniqueDiffOn.univ_pi fun _ => uniqueDiffOn_Icc (by norm_num)
  let hθ := θ.property.positiveSmooth.2.2.1 l
  let hstar := (embeddedSparseWitness_positive_normalized_smooth s hji).2.2.1 l
  apply Causalean.Mathlib.Topology.continuous_uniformOnFun_of_eq_affine_on_compact
    (K := latentCube n)
    (by rw [latentCube]; exact isCompact_univ_pi fun _ => isCompact_Icc)
    (show (latentCube n).Nonempty from
      ⟨0, fun _ _ => ⟨by norm_num, by norm_num⟩⟩)
    (hθ.continuousOn_fderivWithin hu (by norm_num))
    (hstar.continuousOn_fderivWithin hu (by norm_num))
  intro t x hx
  change fderivWithin ℝ
      (fun y => (1 - t) • θ.1.p l y + t • (embeddedSparseWitness s hji).p l y)
      (latentCube n) x = _
  rw [fderivWithin_fun_add (hu.uniqueDiffWithinAt hx)
      (((hθ.const_smul (1 - t)) x hx).differentiableWithinAt (by norm_num))
      (((hstar.const_smul t) x hx).differentiableWithinAt (by norm_num)),
    fderivWithin_fun_const_smul (hu.uniqueDiffWithinAt hx)
      ((hθ x hx).differentiableWithinAt (by norm_num)) (1 - t),
    fderivWithin_fun_const_smul (hu.uniqueDiffWithinAt hx)
      ((hstar x hx).differentiableWithinAt (by norm_num)) t]

/-- Given [the selected directed edge](hyp:hji), the [observational-factor second within-derivative
coordinate varies continuously along the unrestricted affine path](goal). -/
@[fun_prop] lemma continuous_affinePathExtension_p_iteratedFDerivWithin_two
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) (l : Fin n) :
    Continuous (fun t : ℝ => UniformOnFun.ofFun {latentCube n}
      (iteratedFDerivWithin ℝ 2 ((affinePathExtension s θ hji t).p l)
        (latentCube n))) := by
  let hu : UniqueDiffOn ℝ (latentCube n) := by
    rw [latentCube]
    exact UniqueDiffOn.univ_pi fun _ => uniqueDiffOn_Icc (by norm_num)
  let hθ := θ.property.positiveSmooth.2.2.1 l
  let hstar := (embeddedSparseWitness_positive_normalized_smooth s hji).2.2.1 l
  let hθ2 : ContDiffOn ℝ 2 (θ.1.p l) (latentCube n) :=
    hθ.of_le (by norm_num)
  let hstar2 : ContDiffOn ℝ 2 ((embeddedSparseWitness s hji).p l) (latentCube n) :=
    hstar.of_le (by norm_num)
  apply Causalean.Mathlib.Topology.continuous_uniformOnFun_of_eq_affine_on_compact
    (K := latentCube n)
    (by rw [latentCube]; exact isCompact_univ_pi fun _ => isCompact_Icc)
    (show (latentCube n).Nonempty from
      ⟨0, fun _ _ => ⟨by norm_num, by norm_num⟩⟩)
    (hθ.continuousOn_iteratedFDerivWithin (by norm_num) hu)
    (hstar.continuousOn_iteratedFDerivWithin (by norm_num) hu)
  intro t x hx
  change iteratedFDerivWithin ℝ 2
      (fun y => (1 - t) • θ.1.p l y + t • (embeddedSparseWitness s hji).p l y)
      (latentCube n) x = _
  have hscaleθ : iteratedFDerivWithin ℝ 2
      (fun y => (1 - t) • θ.1.p l y) (latentCube n) x =
      (1 - t) • iteratedFDerivWithin ℝ 2 (θ.1.p l) (latentCube n) x := by
    change iteratedFDerivWithin ℝ 2 ((1 - t) • θ.1.p l) (latentCube n) x = _
    exact iteratedFDerivWithin_const_smul_apply
      (hθ2 x hx) hu hx
  have hscaleStar : iteratedFDerivWithin ℝ 2
      (fun y => t • (embeddedSparseWitness s hji).p l y) (latentCube n) x =
      t • iteratedFDerivWithin ℝ 2 ((embeddedSparseWitness s hji).p l)
        (latentCube n) x := by
    change iteratedFDerivWithin ℝ 2
      (t • (embeddedSparseWitness s hji).p l) (latentCube n) x = _
    exact iteratedFDerivWithin_const_smul_apply
      (hstar2 x hx) hu hx
  rw [fun_iteratedFDerivWithin_add_apply
      ((hθ2.const_smul (1 - t)) x hx)
      ((hstar2.const_smul t) x hx) hu hx,
    hscaleθ, hscaleStar]

/-- Given [the selected directed edge](hyp:hji), the [intervention-factor first within-derivative
coordinate varies continuously along the unrestricted affine path](goal). -/
@[fun_prop] lemma continuous_affinePathExtension_q_fderivWithin
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) (l : Fin n) :
    Continuous (fun t : ℝ => UniformOnFun.ofFun {Set.Icc (0 : ℝ) 1}
      (fderivWithin ℝ ((affinePathExtension s θ hji t).q l) (Set.Icc (0 : ℝ) 1))) := by
  let K := Set.Icc (0 : ℝ) 1
  let hu : UniqueDiffOn ℝ K := uniqueDiffOn_Icc (by norm_num)
  let hθ := θ.property.positiveSmooth.2.2.2.1 l
  let hstar := (embeddedSparseWitness_positive_normalized_smooth s hji).2.2.2.1 l
  apply Causalean.Mathlib.Topology.continuous_uniformOnFun_of_eq_affine_on_compact isCompact_Icc
    (nonempty_Icc.mpr (by norm_num))
    (hθ.continuousOn_fderivWithin hu (by norm_num))
    (hstar.continuousOn_fderivWithin hu (by norm_num))
  intro t x hx
  change fderivWithin ℝ
      (fun y => (1 - t) • θ.1.q l y + t • (embeddedSparseWitness s hji).q l y) K x = _
  rw [fderivWithin_fun_add (hu.uniqueDiffWithinAt hx)
      (((hθ.const_smul (1 - t)) x hx).differentiableWithinAt (by norm_num))
      (((hstar.const_smul t) x hx).differentiableWithinAt (by norm_num)),
    fderivWithin_fun_const_smul (hu.uniqueDiffWithinAt hx)
      ((hθ x hx).differentiableWithinAt (by norm_num)) (1 - t),
    fderivWithin_fun_const_smul (hu.uniqueDiffWithinAt hx)
      ((hstar x hx).differentiableWithinAt (by norm_num)) t]

/-- Given [the selected directed edge](hyp:hji), the [intervention-factor second within-derivative
coordinate varies continuously along the unrestricted affine path](goal). -/
@[fun_prop] lemma continuous_affinePathExtension_q_iteratedFDerivWithin_two
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) (l : Fin n) :
    Continuous (fun t : ℝ => UniformOnFun.ofFun {Set.Icc (0 : ℝ) 1}
      (iteratedFDerivWithin ℝ 2 ((affinePathExtension s θ hji t).q l)
        (Set.Icc (0 : ℝ) 1))) := by
  let K := Set.Icc (0 : ℝ) 1
  let hu : UniqueDiffOn ℝ K := uniqueDiffOn_Icc (by norm_num)
  let hθ := θ.property.positiveSmooth.2.2.2.1 l
  let hstar := (embeddedSparseWitness_positive_normalized_smooth s hji).2.2.2.1 l
  let hθ2 : ContDiffOn ℝ 2 (θ.1.q l) K :=
    hθ.of_le (by norm_num)
  let hstar2 : ContDiffOn ℝ 2 ((embeddedSparseWitness s hji).q l) K :=
    hstar.of_le (by norm_num)
  apply Causalean.Mathlib.Topology.continuous_uniformOnFun_of_eq_affine_on_compact isCompact_Icc
    (nonempty_Icc.mpr (by norm_num))
    (hθ.continuousOn_iteratedFDerivWithin (by norm_num) hu)
    (hstar.continuousOn_iteratedFDerivWithin (by norm_num) hu)
  intro t x hx
  change iteratedFDerivWithin ℝ 2
      (fun y => (1 - t) • θ.1.q l y + t • (embeddedSparseWitness s hji).q l y) K x = _
  have hscaleθ : iteratedFDerivWithin ℝ 2
      (fun y => (1 - t) • θ.1.q l y) K x =
      (1 - t) • iteratedFDerivWithin ℝ 2 (θ.1.q l) K x := by
    change iteratedFDerivWithin ℝ 2 ((1 - t) • θ.1.q l) K x = _
    exact iteratedFDerivWithin_const_smul_apply
      (hθ2 x hx) hu hx
  have hscaleStar : iteratedFDerivWithin ℝ 2
      (fun y => t • (embeddedSparseWitness s hji).q l y) K x =
      t • iteratedFDerivWithin ℝ 2 ((embeddedSparseWitness s hji).q l) K x := by
    change iteratedFDerivWithin ℝ 2 (t • (embeddedSparseWitness s hji).q l) K x = _
    exact iteratedFDerivWithin_const_smul_apply
      (hstar2 x hx) hu hx
  rw [fun_iteratedFDerivWithin_add_apply
      ((hθ2.const_smul (1 - t)) x hx)
      ((hstar2.const_smul t) x hx) hu hx,
    hscaleθ, hscaleStar]

/-- Given [the selected directed edge](hyp:hji), the [unrestricted affine mechanism path is
continuous in the induced relative product C² topology](goal). -/
@[fun_prop] lemma continuous_affinePathExtension
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) :
    Continuous (fun t : ℝ => affinePathExtension s θ hji t) := by
  rw [continuous_induced_rng]
  unfold mechanismC2Coordinates
  fun_prop

/-- The unrestricted affine mechanism path tends to its initial stratum point at parameter zero.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma tendsto_affinePathExtension_zero
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) :
    Tendsto (fun t : ℝ => affinePathExtension s θ hji t) (𝓝 0) (𝓝 θ.1) := by
  have hzero : affinePathExtension s θ hji 0 = θ.1 := by
    rcases θ with ⟨⟨p, q, hlocal⟩, hprop⟩
    simp [affinePathExtension]
  have hc : Tendsto (fun t : ℝ => affinePathExtension s θ hji t) (𝓝 0)
      (𝓝 (affinePathExtension s θ hji 0)) :=
    (continuous_affinePathExtension θ hji).continuousAt
  rwa [hzero] at hc

/-- The observational factors of the affine path are uniformly close to their initial values for
all nodes and cube points when the parameter is sufficiently small.  Given [the stated inputs and conditions](hyp:hji,hε), [the stated conclusion](goal) follows. -/
lemma affinePathExtension_p_eventually_uniform_close
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ → ∀ l v, v ∈ latentCube n →
      |(affinePathExtension s θ hji t).p l v - θ.1.p l v| < ε := by
  let θstar := embeddedSparseWitness s hji
  let K : Set (Fin n × LatentState n) := Set.univ ×ˢ latentCube n
  have hK : IsCompact K := isCompact_univ.prod (by
    rw [latentCube]
    exact isCompact_univ_pi fun _ => isCompact_Icc)
  have hKne : K.Nonempty := ⟨(j, 0), ⟨Set.mem_univ _, fun _ _ => ⟨by norm_num, by norm_num⟩⟩⟩
  have hcont : ContinuousOn
      (fun z : Fin n × LatentState n => |θstar.p z.1 z.2 - θ.1.p z.1 z.2|) K := by
    rw [continuousOn_prod_of_discrete_left]
    intro l
    simpa only [K, Set.mem_prod, Set.mem_univ, true_and, Set.ofPred_mem_eq, θstar,
      Pi.sub_apply] using
      (((embeddedSparseWitness_positive_normalized_smooth s hji).2.2.1 l).continuousOn.sub
        (θ.property.positiveSmooth.2.2.1 l).continuousOn).abs
  rcases hK.exists_isMaxOn hKne hcont with ⟨z₀, hz₀, hzmax⟩
  let B := |θstar.p z₀.1 z₀.2 - θ.1.p z₀.1 z₀.2| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨ε / B, div_pos hε hB, ?_⟩
  intro t ht l v hv
  have hbound0 := hzmax (show (l, v) ∈ K from ⟨Set.mem_univ _, hv⟩)
  change |θstar.p l v - θ.1.p l v| ≤
    |θstar.p z₀.1 z₀.2 - θ.1.p z₀.1 z₀.2| at hbound0
  have hbound : |θstar.p l v - θ.1.p l v| < B := by dsimp [B]; linarith
  change |((1 - t) * θ.1.p l v + t * θstar.p l v) - θ.1.p l v| < ε
  rw [show ((1 - t) * θ.1.p l v + t * θstar.p l v) - θ.1.p l v =
      t * (θstar.p l v - θ.1.p l v) by ring, abs_mul]
  calc
    |t| * |θstar.p l v - θ.1.p l v| ≤ |t| * B :=
      mul_le_mul_of_nonneg_left hbound.le (abs_nonneg _)
    _ < (ε / B) * B := mul_lt_mul_of_pos_right ht hB
    _ = ε := div_mul_cancel₀ ε hB.ne'

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.ComponentNormalization

/-!
# Hellinger assembly over independent finite coordinate blocks

Finite spin coordinates may have different types in the labeled and auxiliary
channels. Regrouping their product weights proves affinity tensorization over
components, the finite-product step of MC32.
-/

public section

attribute [local instance] Classical.propDecidable

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Regroup a dependent finite product distribution by the owner of each coordinate.  Given [the specified input S](hyp:S), [the specified input owner](hyp:owner), [the specified input w](hyp:w), [the specified input G](hyp:G), [the finite dependent fiber weighted sum conclusion](goal) holds. -/
lemma finite_dependent_fiber_weighted_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    {S : ι → Type*} [∀ i, Fintype (S i)]
    (owner : ι → κ) (w : ∀ i, S i → ℝ)
    (G : ∀ c, (∀ z : {z // owner z = c}, S z.1) → ℝ) :
    (∑ sigma : ∀ i, S i, (∏ z, w z (sigma z)) *
      ∏ c, G c (fun z => sigma z.1)) =
    ∏ c, ∑ s : (∀ z : {z // owner z = c}, S z.1),
      (∏ z, w z.1 (s z)) * G c s := by
  classical
  let e : (∀ i, S i) ≃ (∀ c, ∀ z : {z // owner z = c}, S z.1) :=
    Equiv.piCongrFiberwise (fun _ => Equiv.refl _)
  calc
    _ = ∑ s : (∀ c, ∀ z : {z // owner z = c}, S z.1),
        ∏ c, (∏ z : {z // owner z = c}, w z.1 (s c z)) * G c (s c) := by
      apply Fintype.sum_equiv e
      intro sigma
      simp only [e, Equiv.piCongrFiberwise_apply, Equiv.refl_apply,
        Finset.prod_mul_distrib]
      rw [Fintype.prod_fiberwise owner (fun z => w z (sigma z))]
    _ = _ := (Fintype.prod_sum (fun c (s : ∀ z : {z // owner z = c}, S z.1) =>
      (∏ z, w z.1 (s z)) * G c s)).symm

/-- Expectations multiply for functions of disjoint coordinate blocks, including empty blocks.  Given [the specified input S](hyp:S), [the specified input owner](hyp:owner), [the specified input w](hyp:w), [the specified input hw](hyp:hw), [the specified input F](hyp:F), [the specified input hF](hyp:hF), [the finite dependent fiber expectation factorization conclusion](goal) holds. -/
lemma finite_dependent_fiber_expectation_factorization {ι κ : Type*}
    [Fintype ι] [Fintype κ] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (owner : ι → κ) (w : ∀ i, S i → ℝ) (hw : ∀ z, ∑ s, w z s = 1)
    (F : κ → (∀ i, S i) → ℝ)
    (hF : ∀ c sigma sigma', (∀ z, owner z = c → sigma z = sigma' z) →
      F c sigma = F c sigma') :
    (∑ sigma : ∀ i, S i, (∏ z, w z (sigma z)) * ∏ c, F c sigma) =
    ∏ c, ∑ sigma : ∀ i, S i, (∏ z, w z (sigma z)) * F c sigma := by
  classical
  let lift (c : κ) (s : ∀ z : {z // owner z = c}, S z.1) (z : ι) : S z :=
    if hz : owner z = c then s ⟨z, hz⟩ else Classical.choice (inferInstance : Nonempty (S z))
  let G (c : κ) (s : ∀ z : {z // owner z = c}, S z.1) : ℝ := F c (lift c s)
  have hG (c : κ) (sigma : ∀ i, S i) : F c sigma = G c (fun z => sigma z.1) := by
    apply hF
    intro z hz
    simp [lift, hz]
  have hmass (c : κ) : (∑ s : (∀ z : {z // owner z = c}, S z.1),
      ∏ z, w z.1 (s z)) = 1 := by
    rw [← Fintype.prod_sum]
    simp [hw]
  have hmarg (c : κ) : (∑ sigma : ∀ i, S i, (∏ z, w z (sigma z)) * F c sigma) =
      ∑ s : (∀ z : {z // owner z = c}, S z.1), (∏ z, w z.1 (s z)) * G c s := by
    have ht := finite_dependent_fiber_weighted_sum owner w
      (fun j s => if hj : j = c then G c (hj ▸ s) else 1)
    have hprod (sigma : ∀ i, S i) :
        (∏ j, if hj : j = c then G c (hj ▸ (fun z => sigma z.1)) else 1) = F c sigma := by
      simp [← hG]
    simp_rw [hprod] at ht
    rw [ht]
    have hsum (j : κ) :
        (∑ s : (∀ z : {z // owner z = j}, S z.1), (∏ z, w z.1 (s z)) *
          (if hj : j = c then G c (hj ▸ s) else 1)) =
        if hj : j = c then (∑ s : (∀ z : {z // owner z = c}, S z.1),
          (∏ z, w z.1 (s z)) * G c s) else 1 := by
      by_cases hj : j = c
      · subst j; simp
      · simp [hj, hmass]
    simp_rw [hsum]
    simp
  simp_rw [hG] at ⊢
  rw [finite_dependent_fiber_weighted_sum]
  apply Finset.prod_congr rfl
  intro c _
  exact (hmarg c).symm.trans (by simp_rw [hG])

/-- A finite product reference [with coordinate measures μ](hyp:μ) integrates block-dependent functions multiplicatively.  Given [the specified input S](hyp:S), [the specified input owner](hyp:owner), [the specified input F](hyp:F), [the specified input hF](hyp:hF), [the integral finite block product conclusion](goal) holds. -/
lemma integral_finite_block_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, MeasurableSingletonClass (S i)]
    (μ : ∀ i, Measure (S i)) [∀ i, IsProbabilityMeasure (μ i)]
    (owner : ι → κ) (F : κ → (∀ i, S i) → ℝ)
    (hF : ∀ c sigma sigma', (∀ z, owner z = c → sigma z = sigma' z) →
      F c sigma = F c sigma') :
    (∫ sigma, ∏ c, F c sigma ∂Measure.pi μ) =
      ∏ c, ∫ sigma, F c sigma ∂Measure.pi μ := by
  have hw (i : ι) : ∑ s, (μ i).real {s} = 1 := by
    simpa using (integral_fintype (μ := μ i) (f := fun _ => (1:ℝ)) Integrable.of_finite).symm
  simp_rw [integral_fintype (μ := Measure.pi μ) Integrable.of_finite,
    measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod, smul_eq_mul]
  exact finite_dependent_fiber_expectation_factorization owner
    (fun i s => (μ i).real {s}) hw F hF

/-- Affinity tensorizes across disjoint blocks of [a finite product reference with coordinate measures μ](hyp:μ).  Given [the specified input S](hyp:S), [the specified input owner](hyp:owner), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf0](hyp:hf0), [the specified input hg0](hyp:hg0), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the density affinity finite blocks conclusion](goal) holds. -/
lemma densityAffinity_finite_blocks {ι κ : Type*} [Fintype ι] [Fintype κ]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, MeasurableSingletonClass (S i)]
    (μ : ∀ i, Measure (S i)) [∀ i, IsProbabilityMeasure (μ i)]
    (owner : ι → κ) (f g : κ → (∀ i, S i) → ℝ)
    (hf0 : ∀ c s, 0 ≤ f c s) (hg0 : ∀ c s, 0 ≤ g c s)
    (hf : ∀ c s t, (∀ z, owner z = c → s z = t z) → f c s = f c t)
    (hg : ∀ c s t, (∀ z, owner z = c → s z = t z) → g c s = g c t) :
    Causalean.Stat.densityAffinity (Measure.pi μ)
      (fun s => ∏ c, f c s) (fun s => ∏ c, g c s) =
    ∏ c, Causalean.Stat.densityAffinity (Measure.pi μ) (f c) (g c) := by
  unfold Causalean.Stat.densityAffinity
  simp_rw [← Finset.prod_mul_distrib,
    Real.sqrt_prod _ (fun c _ => mul_nonneg (hf0 c _) (hg0 c _))]
  apply integral_finite_block_product μ owner
  intro c s t hst
  rw [hf c s t hst, hg c s t hst]

/-- Normalized component densities combine by Hellinger subadditivity on their
actual shared spin space [with coordinate measures μ](hyp:μ), provided they use disjoint coordinate blocks.  Given [the specified input S](hyp:S), [the specified input owner](hyp:owner), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf0](hyp:hf0), [the specified input hg0](hyp:hg0), [the specified input hf1](hyp:hf1), [the specified input hg1](hyp:hg1), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the density hellinger finite blocks le sum conclusion](goal) holds. -/
lemma density_hellinger_finite_blocks_le_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, MeasurableSingletonClass (S i)]
    (μ : ∀ i, Measure (S i)) [∀ i, IsProbabilityMeasure (μ i)]
    (owner : ι → κ) (f g : κ → (∀ i, S i) → ℝ)
    (hf0 : ∀ c s, 0 ≤ f c s) (hg0 : ∀ c s, 0 ≤ g c s)
    (hf1 : ∀ c, ∫ s, f c s ∂Measure.pi μ = 1)
    (hg1 : ∀ c, ∫ s, g c s ∂Measure.pi μ = 1)
    (hf : ∀ c s t, (∀ z, owner z = c → s z = t z) → f c s = f c t)
    (hg : ∀ c s t, (∀ z, owner z = c → s z = t z) → g c s = g c t) :
    Causalean.Stat.hellingerSqDensity (Measure.pi μ)
      (fun s => ∏ c, f c s) (fun s => ∏ c, g c s) ≤
    ∑ c, Causalean.Stat.hellingerSqDensity (Measure.pi μ) (f c) (g c) := by
  have hpf : (∫ s, ∏ c, f c s ∂Measure.pi μ) = 1 := by
    rw [integral_finite_block_product μ owner f hf]
    simp [hf1]
  have hpg : (∫ s, ∏ c, g c s ∂Measure.pi μ) = 1 := by
    rw [integral_finite_block_product μ owner g hg]
    simp [hg1]
  rw [Causalean.Stat.hellingerSqDensity_eq_two_mul_one_sub_affinity _ _ _
    Integrable.of_finite Integrable.of_finite
    (fun s => Finset.prod_nonneg (fun c _ => hf0 c s))
    (fun s => Finset.prod_nonneg (fun c _ => hg0 c s)) hpf hpg,
    densityAffinity_finite_blocks μ owner f g hf0 hg0 hf hg]
  simp_rw [Causalean.Stat.hellingerSqDensity_eq_two_mul_one_sub_affinity _ _ _
    Integrable.of_finite Integrable.of_finite (hf0 _) (hg0 _) (hf1 _) (hg1 _)]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  exact Causalean.Stat.one_sub_prod_le_sum _
    (fun c => (densityAffinity_mem_unit _ _ _ Integrable.of_finite Integrable.of_finite
      (hf0 c) (hg0 c) (hf1 c) (hg1 c)).1)
    (fun c => (densityAffinity_mem_unit _ _ _ Integrable.of_finite Integrable.of_finite
      (hf0 c) (hg0 c) (hf1 c) (hg1 c)).2)

/-- A selected component density depends only on its selected record spins.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input x](hyp:x), [the specified input V](hyp:V), [the specified input s](hyp:s), [the specified input t](hyp:t), [the specified input hl](hyp:hl), [the specified input ha](hyp:ha), [the component density spin congr conclusion](goal) holds. -/
lemma componentDensity_spin_congr {d n m : ℕ} (H : MarkedPriors d) (theta : Bool)
    (x : Fin (n+m) → Cov d) (V : Finset (Fin (n+m)))
    (s t : RecordSpins n m)
    (hl : ∀ i : Fin n, Fin.castAdd m i ∈ V → s.1 i = t.1 i)
    (ha : ∀ j : Fin m, Fin.natAdd n j ∈ V → s.2 j = t.2 j) :
    componentDensity H theta x V s = componentDensity H theta x V t := by
  unfold componentDensity
  apply Finset.sum_congr rfl
  intro sigma _
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  induction i using Fin.addCases with
  | left j => simp only [recordLikelihood, Fin.addCases_left, hl j hi]
  | right j => simp only [recordLikelihood, Fin.addCases_right, ha j hi]

/-- The marked conditional Hellinger discrepancy is at most the sum of the
component discrepancies (the tensorization part of MC32). No extra independence
assumption is needed: the fair reference spins are independent by construction.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input hd](hyp:hd), [the specified input hdh](hyp:hdh), [the specified input hh](hyp:hh), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the marked conditional hellinger le component sum conclusion](goal) holds. -/
lemma marked_conditional_hellinger_le_component_sum {d n m : ℕ}
    (h delta a b : ℝ) (hd : 0 < delta) (hdh : delta ≤ h) (hh : h ≤ 1/2)
    (x : Fin (n+m) → Cov d) (hx : ∀ i, x i ∈ cube d) :
    Causalean.Stat.hellingerSqDensity
      ((Measure.pi (fun _ : Fin n => fairObserved)).prod
        (Measure.pi (fun _ : Fin m => bern (1/2))))
      (mixedDensity (markedHandle d h delta a b) true x)
      (mixedDensity (markedHandle d h delta a b) false x) ≤
    ∑ c : (recordGraph h delta x).ConnectedComponent,
      Causalean.Stat.hellingerSqDensity
        ((Measure.pi (fun _ : Fin n => fairObserved)).prod
          (Measure.pi (fun _ : Fin m => bern (1/2))))
        (componentDensity (markedHandle d h delta a b) true x (componentVertices h delta x c))
        (componentDensity (markedHandle d h delta a b) false x (componentVertices h delta x c)) := by
  classical
  letI hBern := bern_probability (1/2) (by norm_num)
  letI hFair : IsProbabilityMeasure fairObserved := by unfold fairObserved; infer_instance
  let S : Fin n ⊕ Fin m → Type := Sum.elim (fun _ => Bool × Bool) (fun _ => Bool)
  letI : ∀ i, Fintype (S i) := fun i => by cases i <;> dsimp [S] <;> infer_instance
  letI : ∀ i, Nonempty (S i) := fun i => by cases i <;> dsimp [S] <;> infer_instance
  letI mS : ∀ i, MeasurableSpace (S i) := fun i => by cases i <;> dsimp [S] <;> infer_instance
  letI : ∀ i, MeasurableSingletonClass (S i) := fun i => by cases i <;> dsimp [S] <;> infer_instance
  let μ : ∀ i, Measure (S i) := Sum.rec (fun _ => fairObserved) (fun _ => bern (1/2))
  letI hProb : ∀ i, IsProbabilityMeasure (μ i) := fun i => by
    cases i with
    | inl j => exact hFair
    | inr j => exact hBern
  letI hSigma : ∀ i, SigmaFinite (μ i) := fun i => by
    cases i with
    | inl j => exact (inferInstance : SigmaFinite fairObserved)
    | inr j => exact (inferInstance : SigmaFinite (bern (1/2)))
  have hi (F : RecordSpins n m → ℝ) :
      (∫ s, F (fun i => s (.inl i), fun j => s (.inr j)) ∂Measure.pi μ) =
      ∫ s, F s ∂(Measure.pi (fun _ : Fin n => fairObserved)).prod
        (Measure.pi (fun _ : Fin m => bern (1/2))) :=
    (@measurePreserving_sumPiEquivProdPi (Fin n) (Fin m) _ _ S mS μ hSigma).integral_comp' F
  let H := markedHandle d h delta a b
  let comp := (recordGraph h delta x).connectedComponentMk
  let owner : Fin n ⊕ Fin m → (recordGraph h delta x).ConnectedComponent :=
    fun i => comp (i.elim (Fin.castAdd m) (Fin.natAdd n))
  let f : (recordGraph h delta x).ConnectedComponent → (∀ i, S i) → ℝ := fun c s => componentDensity H true x (componentVertices h delta x c) (fun i => s (.inl i), fun j => s (.inr j))
  let g : (recordGraph h delta x).ConnectedComponent → (∀ i, S i) → ℝ := fun c s => componentDensity H false x (componentVertices h delta x c) (fun i => s (.inl i), fun j => s (.inr j))
  have hdep (theta : Bool) (c : (recordGraph h delta x).ConnectedComponent)
      (s t : ∀ i, S i) (hst : ∀ z, owner z = c → s z = t z) :
      componentDensity H theta x (componentVertices h delta x c) (fun i => s (.inl i), fun j => s (.inr j)) =
      componentDensity H theta x (componentVertices h delta x c) (fun i => t (.inl i), fun j => t (.inr j)) := by
    apply componentDensity_spin_congr
    · intro i hi
      exact hst (.inl i) (Finset.mem_filter.mp hi).2
    · intro j hj
      exact hst (.inr j) (Finset.mem_filter.mp hj).2
  have hb := @density_hellinger_finite_blocks_le_sum (Fin n ⊕ Fin m)
    (recordGraph h delta x).ConnectedComponent _ _ S _ _ mS _ μ hProb owner f g
    (fun c s => componentDensity_nonneg H true (marked_prior_mass d h delta true).1 _ _ _)
    (fun c s => componentDensity_nonneg H false (marked_prior_mass d h delta false).1 _ _ _)
    (fun c => (hi _).trans (marked_componentDensity_integral_one h delta a b true x _))
    (fun c => (hi _).trans (marked_componentDensity_integral_one h delta a b false x _))
    (hdep true) (hdep false)
  have hfactor := marked_conditional_factorization d h delta a b hd hdh hh n m x hx
  have hlhs : Causalean.Stat.hellingerSqDensity (Measure.pi μ)
      (fun s => ∏ c, f c s) (fun s => ∏ c, g c s) =
      Causalean.Stat.hellingerSqDensity
        ((Measure.pi (fun _ : Fin n => fairObserved)).prod
          (Measure.pi (fun _ : Fin m => bern (1/2))))
        (mixedDensity H true x) (mixedDensity H false x) := by
    unfold Causalean.Stat.hellingerSqDensity
    have hfprod (s : ∀ i, S i) : (∏ c, f c s) =
        mixedDensity H true x (fun i => s (.inl i), fun j => s (.inr j)) :=
      (hfactor true _).symm
    have hgprod (s : ∀ i, S i) : (∏ c, g c s) =
        mixedDensity H false x (fun i => s (.inl i), fun j => s (.inr j)) :=
      (hfactor false _).symm
    calc
      _ = ∫ s, (Real.sqrt (mixedDensity H true x
          (fun i => s (.inl i), fun j => s (.inr j))) -
          Real.sqrt (mixedDensity H false x
          (fun i => s (.inl i), fun j => s (.inr j))))^2 ∂Measure.pi μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s =>
          congrArg₂ (fun u v : ℝ => (Real.sqrt u - Real.sqrt v)^2) (hfprod s) (hgprod s))
      _ = _ := hi (fun s => (Real.sqrt (mixedDensity H true x s) -
        Real.sqrt (mixedDensity H false x s))^2)
  have hrhs (c : (recordGraph h delta x).ConnectedComponent) :
      Causalean.Stat.hellingerSqDensity (Measure.pi μ) (f c) (g c) =
      Causalean.Stat.hellingerSqDensity
        ((Measure.pi (fun _ : Fin n => fairObserved)).prod
          (Measure.pi (fun _ : Fin m => bern (1/2))))
        (componentDensity H true x (componentVertices h delta x c))
        (componentDensity H false x (componentVertices h delta x c)) := by
    unfold Causalean.Stat.hellingerSqDensity
    exact hi (fun s => (Real.sqrt (componentDensity H true x (componentVertices h delta x c) s) -
      Real.sqrt (componentDensity H false x (componentVertices h delta x c) s))^2)
  rwa [hlhs, show (∑ c, Causalean.Stat.hellingerSqDensity (Measure.pi μ) (f c) (g c)) = _
    from Finset.sum_congr rfl (fun c _ => hrhs c)] at hb

/-- A component sum regrouped by size counts exactly the informative components.  Given [the specified input size](hyp:size), [the specified input info](hyp:info), [the specified input N](hyp:N), [the specified input hsize](hyp:hsize), [the specified input W](hyp:W), [the finite size weighted count conclusion](goal) holds. -/
lemma finite_size_weighted_count {ι : Type*} [Fintype ι]
    (size : ι → ℕ) (info : ι → Prop) [DecidablePred info] (N : ℕ) (hsize : ∀ i, size i ≤ N)
    (W : ℕ → ℝ) :
    (∑ i, if 2 ≤ size i ∧ info i then W (size i) else 0) =
    ∑ p ∈ Finset.Icc 2 N, W p *
      ((Finset.univ.filter (fun i => size i = p ∧ info i)).card : ℝ) := by
  classical
  have hexpand (p : ℕ) : W p *
      ((Finset.univ.filter (fun i => size i = p ∧ info i)).card : ℝ) =
      ∑ i, if size i = p ∧ info i then W p else 0 := by
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, mul_comm]
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : info i
  · by_cases hs : 2 ≤ size i
    · rw [if_pos ⟨hs, hi⟩]
      symm
      rw [Finset.sum_eq_single (size i)]
      · simp [hi]
      · intro p hp hne
        simp [Ne.symm hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_Icc.mpr ⟨hs, hsize i⟩))
    · rw [if_neg (fun h => hs h.1)]
      symm
      apply Finset.sum_eq_zero
      intro p hp
      have hne : size i ≠ p := by
        intro heq
        exact hs (heq.symm ▸ (Finset.mem_Icc.mp hp).1)
      simp [hne]
  · simp [hi]

/-- MC32 before integration over covariates: only components of size at least
two containing a label contribute, and they are grouped by their exact size.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the marked conditional hellinger count bound conclusion](goal) holds. -/
lemma marked_conditional_hellinger_count_bound (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < K ∧ ∀ h delta a b,
      0 < delta → delta ≤ h → h ≤ 1/2 → 0 < a → a ≤ c*delta^alpha →
      0 < b → b ≤ c*delta^beta → a*b ≤ c*h^gamma →
      ∀ n m (x : Fin (n+m) → Cov d), (∀ i, x i ∈ cube d) →
      Causalean.Stat.hellingerSqDensity
        ((Measure.pi (fun _ : Fin n => fairObserved)).prod
          (Measure.pi (fun _ : Fin m => bern (1/2))))
        (mixedDensity (markedHandle d h delta a b) true x)
        (mixedDensity (markedHandle d h delta a b) false x) ≤
      K*a^2*b^2 * ∑ p ∈ Finset.Icc 2 (n+m), (9/2:ℝ)^p*(p:ℝ)^4 *
        ((Finset.univ.filter (fun c : (recordGraph h delta x).ConnectedComponent =>
          (componentVertices h delta x c).card = p ∧
          ∃ i ∈ componentVertices h delta x c, i.val < n)).card : ℝ) := by
  classical
  obtain ⟨cH, K, hcH, hcH1, hK, hbound⟩ :=
    marked_component_hellinger_bound d alpha beta gamma L eps hdom
  obtain ⟨cU, hcU, hcU1, huninf⟩ :=
    uninformative_component_equality d alpha beta gamma L eps hdom
  let c := min cH cU
  have hc : 0 < c := lt_min hcH hcU
  refine ⟨c, K, hc, (min_le_left _ _).trans hcH1, hK, ?_⟩
  intro h delta a b hd hdh hh ha hac hb hbc hab n m x hx
  letI := bern_probability (1/2) (by norm_num)
  letI : IsProbabilityMeasure fairObserved := by unfold fairObserved; infer_instance
  let μ := (Measure.pi (fun _ : Fin n => fairObserved)).prod
    (Measure.pi (fun _ : Fin m => bern (1/2)))
  let H := markedHandle d h delta a b
  have hamp (c' : ℝ) (hcc : c ≤ c') :
      a ≤ c'*delta^alpha ∧ b ≤ c'*delta^beta ∧ a*b ≤ c'*h^gamma :=
    ⟨hac.trans (mul_le_mul_of_nonneg_right hcc (Real.rpow_pos_of_pos hd _).le),
      hbc.trans (mul_le_mul_of_nonneg_right hcc (Real.rpow_pos_of_pos hd _).le),
      hab.trans (mul_le_mul_of_nonneg_right hcc (Real.rpow_pos_of_pos (hd.trans_le hdh) _).le)⟩
  have hH := hamp cH (min_le_left _ _)
  have hU := hamp cU (min_le_right _ _)
  have hzero := huninf h delta a b hd hdh hh ha hU.1 hb hU.2.1 hU.2.2 n m x hx
  let size := fun c => (componentVertices h delta x c).card
  let info := fun c => ∃ i ∈ componentVertices h delta x c, i.val < n
  have hsize (c : (recordGraph h delta x).ConnectedComponent) : size c ≤ n+m := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have hcomp (c : (recordGraph h delta x).ConnectedComponent) :
      Causalean.Stat.hellingerSqDensity μ
        (componentDensity H true x (componentVertices h delta x c))
        (componentDensity H false x (componentVertices h delta x c)) ≤
      if 2 ≤ size c ∧ info c then K*a^2*b^2*(9/2:ℝ)^(size c)*(size c:ℝ)^4 else 0 := by
    split_ifs with hinf
    · have hbnd := hbound h delta a b hd hdh hh ha hH.1 hb hH.2.1 hH.2.2
        n m x hx (componentVertices h delta x c) μ inferInstance
      convert hbnd using 1 <;> ring
    · have heq : ∀ s, componentDensity H true x (componentVertices h delta x c) s =
          componentDensity H false x (componentVertices h delta x c) s := by
        by_cases hi : info c
        · have hs : ¬ 2 ≤ size c := fun hs => hinf ⟨hs, hi⟩
          have hn : (componentVertices h delta x c).Nonempty := by
            obtain ⟨i, hiV, _⟩ := hi
            exact ⟨i, hiV⟩
          have hs1 : size c = 1 := by have := Finset.card_pos.mpr hn; dsimp [size] at *; omega
          exact hzero c (Or.inr ⟨hs1, hi⟩)
        · apply hzero c
          left
          intro i hiV
          by_contra hni
          exact hi ⟨i, hiV, by omega⟩
      unfold Causalean.Stat.hellingerSqDensity
      simp only [heq, sub_self, zero_pow (by decide : 2 ≠ 0), integral_zero, le_refl]
  calc
    _ ≤ ∑ c, Causalean.Stat.hellingerSqDensity μ
        (componentDensity H true x (componentVertices h delta x c))
        (componentDensity H false x (componentVertices h delta x c)) :=
      marked_conditional_hellinger_le_component_sum h delta a b hd hdh hh x hx
    _ ≤ ∑ c, if 2 ≤ size c ∧ info c then
        K*a^2*b^2*(9/2:ℝ)^(size c)*(size c:ℝ)^4 else 0 :=
      Finset.sum_le_sum (fun c _ => hcomp c)
    _ = K*a^2*b^2 * ∑ p ∈ Finset.Icc 2 (n+m), (9/2:ℝ)^p*(p:ℝ)^4 *
        ((Finset.univ.filter (fun c => size c = p ∧ info c)).card : ℝ) := by
      calc
        _ = ∑ p ∈ Finset.Icc 2 (n+m),
            (K*a^2*b^2*(9/2:ℝ)^p*(p:ℝ)^4) *
              ((Finset.univ.filter (fun c => size c = p ∧ info c)).card : ℝ) :=
          by
            with_reducible exact (@finite_size_weighted_count (recordGraph h delta x).ConnectedComponent
              (inferInstance : Fintype (recordGraph h delta x).ConnectedComponent)
              size info (inferInstance : DecidablePred info) (n+m) hsize
              (fun p => K*a^2*b^2*(9/2:ℝ)^p*(p:ℝ)^4))
        _ = _ := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          ring

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

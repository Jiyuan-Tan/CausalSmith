module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Main
public import Mathlib.Probability.Distributions.Binomial

/-! Countable Poisson splitting and total-variation transport helpers. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory

/-- Total variation contracts under a common Markov kernel.  [the stated conclusion](goal). -/
theorem tvDist_bind_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (K : Kernel X Y) [IsMarkovKernel K] :
    Causalean.Stat.tvDist (K ∘ₘ mu) (K ∘ₘ nu) ≤
      Causalean.Stat.tvDist mu nu := by
  let _ : IsProbabilityMeasure (K ∘ₘ mu) := by infer_instance
  let _ : IsProbabilityMeasure (K ∘ₘ nu) := by infer_instance
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  have hreal (rho : Measure X) [IsProbabilityMeasure rho] :
      (K ∘ₘ rho).real A = ∫ x, (K x A).toReal ∂rho := by
    rw [measureReal_def, Measure.bind_apply hA K.aemeasurable,
      integral_toReal (K.measurable_coe hA).aemeasurable]
    filter_upwards with x
    exact measure_lt_top (K x) A
  rw [hreal mu, hreal nu]
  have hrange : ∀ x, (K x A).toReal ∈ Set.Icc (0 : Real) 1 := by
    intro x
    constructor
    · exact ENNReal.toReal_nonneg
    · have hle := ENNReal.toReal_mono (measure_ne_top (K x) _)
        (measure_mono (Set.subset_univ A))
      simpa using hle
  simpa only [zero_add, mul_one, Causalean.Stat.tvDist] using
    Causalean.Stat.tvDist_integral_range mu nu
      (fun x => (K x A).toReal) (K.measurable_coe hA).ennreal_toReal
      0 1 (by norm_num) (by simpa using hrange)

/-- Post-processing commutes with formation of a prior-predictive law.  [the stated conclusion](goal). -/
theorem kernel_comp_priorPredictive
    {Theta X Y : Type*} [MeasurableSpace Theta] [MeasurableSpace X]
    [MeasurableSpace Y] (pi : Measure Theta) (K : Kernel Theta X)
    (T : Kernel X Y) :
    T ∘ₘ Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive pi K =
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive pi (T ∘ₖ K) := by
  unfold Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
  exact Measure.comp_assoc

/-- Prior-predictive TV depends only on the pointwise difference of kernel masses.  [the stated conditions](hyp:hK0,hK1,hJ0,hJ1,hdiff) [the stated conclusion](goal). -/
theorem tvDist_priorPredictive_eq_of_fiber_sub_eq
    {Theta X : Type*} [MeasurableSpace Theta] [MeasurableSpace X]
    (pi : Measure Theta) [IsProbabilityMeasure pi]
    (K0 K1 J0 J1 : Kernel Theta X)
    (hK0 : ∀ theta, IsProbabilityMeasure (K0 theta))
    (hK1 : ∀ theta, IsProbabilityMeasure (K1 theta))
    (hJ0 : ∀ theta, IsProbabilityMeasure (J0 theta))
    (hJ1 : ∀ theta, IsProbabilityMeasure (J1 theta))
    (hdiff : ∀ theta A, MeasurableSet A →
      (K0 theta).real A - (K1 theta).real A =
        (J0 theta).real A - (J1 theta).real A) :
    Causalean.Stat.tvDist
        (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive pi K0)
        (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive pi K1) =
      Causalean.Stat.tvDist
        (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive pi J0)
        (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive pi J1) := by
  have hreal (K : Kernel Theta X)
      (hK : ∀ theta, IsProbabilityMeasure (K theta))
      (A : Set X) (hA : MeasurableSet A) :
      (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive pi K).real A =
        ∫ theta, (K theta).real A ∂pi := by
    change (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive pi K).real A =
      ∫ theta, (K theta A).toReal ∂pi
    rw [measureReal_def,
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_apply _ _ hA,
      integral_toReal (K.measurable_coe hA).aemeasurable]
    filter_upwards with theta
    let _ := hK theta
    exact measure_lt_top _ _
  have hint (K : Kernel Theta X)
      (hK : ∀ theta, IsProbabilityMeasure (K theta))
      (A : Set X) (hA : MeasurableSet A) :
      Integrable (fun theta => (K theta).real A) pi := by
    apply Integrable.of_bound (K.measurable_coe hA).ennreal_toReal.aestronglyMeasurable 1
    filter_upwards with theta
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    let _ := hK theta
    have hle := ENNReal.toReal_mono (measure_ne_top (K theta) _)
      (measure_mono (Set.subset_univ A))
    simpa using hle
  unfold Causalean.Stat.tvDist
  congr 1
  ext A
  rcases A with ⟨A, hA⟩
  simp only
  rw [hreal K0 hK0 A hA, hreal K1 hK1 A hA,
    hreal J0 hJ0 A hA, hreal J1 hJ1 A hA,
    ← integral_sub (hint K0 hK0 A hA) (hint K1 hK1 A hA),
    ← integral_sub (hint J0 hJ0 A hA) (hint J1 hJ1 A hA)]
  congr 2 with theta
  exact hdiff theta A hA
/-- [the stated conditions](hyp:n,j) defines [the specified object](goal). -/

def poissonSplitEmbed (n j : Nat) : Nat × Nat := (j, n - j)

/-- Given a total count, split it according to a binomial draw.  [the stated conditions](hyp:q,n) [the stated conclusion](goal). -/
noncomputable def poissonSplitMeasure (q : unitInterval) (n : Nat) :
    Measure (Nat × Nat) :=
  ∑ j ∈ Finset.range (n + 1),
    (binomial n q) {j} • Measure.dirac (poissonSplitEmbed n j)

private theorem poissonSplitMeasure_univ (q : unitInterval) (n : Nat) :
    poissonSplitMeasure q n Set.univ = 1 := by
  rw [poissonSplitMeasure, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [sum_measure_singleton]
  rw [← show (binomial n q) Set.univ = 1 by simp]
  apply measure_congr
  filter_upwards [ae_le_of_hasLaw_binomial
    (ProbabilityTheory.HasLaw.id (μ := binomial n q))] with j hj
  change j ≤ n at hj
  apply propext
  change j ∈ Finset.range (n + 1) ↔ j ∈ Set.univ
  simp only [Finset.mem_range, Set.mem_univ, iff_true]
  omega
/-- [the stated conditions](hyp:q,n) defines [the specified object](goal). -/

noncomputable instance poissonSplitMeasure_isProbabilityMeasure
    (q : unitInterval) (n : Nat) :
    IsProbabilityMeasure (poissonSplitMeasure q n) :=
  ⟨poissonSplitMeasure_univ q n⟩

/-- The binomial splitting law as a countable-state Markov kernel.  [the stated conditions](hyp:q) [the stated conclusion](goal). -/
noncomputable def poissonSplitKernel (q : unitInterval) :
    Kernel Nat (Nat × Nat) :=
  Kernel.ofFunOfCountable (poissonSplitMeasure q)
/-- [the stated conditions](hyp:q) defines [the specified object](goal). -/

noncomputable instance poissonSplitKernel_isMarkovKernel (q : unitInterval) :
    IsMarkovKernel (poissonSplitKernel q) where
  isProbabilityMeasure n := poissonSplitMeasure_isProbabilityMeasure q n

private theorem poissonSplitMeasure_singleton (q : unitInterval) (n k s : Nat) :
    poissonSplitMeasure q n {(k, s)} =
      if n = k + s then (binomial (k + s) q) {k} else 0 := by
  classical
  by_cases hn : n = k + s
  · subst n
    rw [if_pos rfl, poissonSplitMeasure, Measure.finsetSum_apply,
      Finset.sum_eq_single k]
    · simp [poissonSplitEmbed]
    · intro j hj hjk
      have hjle : j ≤ k + s := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hne : poissonSplitEmbed (k + s) j ≠ (k, s) := by
        intro heq
        have hjk : j = k := congrArg Prod.fst heq
        have hjs : k + s - j = s := congrArg Prod.snd heq
        omega
      simp [hne]
    · simp
  · rw [if_neg hn, poissonSplitMeasure, Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hne : poissonSplitEmbed n j ≠ (k, s) := by
      intro h
      simp only [poissonSplitEmbed, Prod.mk.injEq] at h
      omega
    simp [hne]

private theorem poisson_binomial_split
    (u v r : Real) (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : 0 ≤ r)
    (ht : 0 < u + v) (k s : Nat) :
    (poissonMeasure (Real.toNNReal ((u + v) * r))).real {k + s} *
        (binomial (k + s)
          (⟨u / (u + v), by
            constructor
            · positivity
            · rw [div_le_one ht]
              linarith⟩ : unitInterval)).real {k} =
      (poissonMeasure (Real.toNNReal (u * r))).real {k} *
        (poissonMeasure (Real.toNNReal (v * r))).real {s} := by
  rw [poissonMeasure_real_singleton, binomial_real_singleton,
    poissonMeasure_real_singleton, poissonMeasure_real_singleton]
  have hfacNat := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k s)
  rw [Nat.add_sub_cancel_left] at hfacNat
  have hfac :
      ((k + s).choose k : Real) * (k.factorial : Real) * (s.factorial : Real) =
        ((k + s).factorial : Real) := by
    exact_mod_cast hfacNat
  simp only [Nat.add_sub_cancel_left]
  rw [Real.coe_toNNReal _ (mul_nonneg (add_nonneg hu hv) hr),
    Real.coe_toNNReal _ (mul_nonneg hu hr),
    Real.coe_toNNReal _ (mul_nonneg hv hr)]
  rw [show (1 - u / (u + v) : Real) = v / (u + v) by
    field_simp
    ring]
  have hexp : Real.exp (-((u + v) * r)) =
      Real.exp (-(u * r)) * Real.exp (-(v * r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, pow_add, mul_pow, mul_pow, div_pow, div_pow]
  field_simp
  rw [← hfac]
  ring

private theorem prod_real_singleton
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (mu : Measure X) (nu : Measure Y) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (x : X) (y : Y) :
    (mu.prod nu).real {(x, y)} = mu.real {x} * nu.real {y} := by
  rw [measureReal_def, ← Set.singleton_prod_singleton, Measure.prod_prod,
    ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def]

/-- Splitting a Poisson count binomially produces two independent Poisson counts.  [the stated conditions](hyp:hu,hv,hr,ht) [the stated conclusion](goal). -/
theorem poissonSplitKernel_comp_poisson
    (u v r : Real) (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : 0 ≤ r)
    (ht : 0 < u + v) :
    poissonSplitKernel
        (⟨u / (u + v), by
          constructor
          · positivity
          · rw [div_le_one ht]
            linarith⟩ : unitInterval) ∘ₘ
        poissonMeasure (Real.toNNReal ((u + v) * r)) =
      (poissonMeasure (Real.toNNReal (u * r))).prod
        (poissonMeasure (Real.toNNReal (v * r))) := by
  let q : unitInterval :=
    ⟨u / (u + v), by
      constructor
      · positivity
      · rw [div_le_one ht]
        linarith⟩
  apply Measure.ext_of_measureReal_singleton
  rintro ⟨k, s⟩
  have hreal :
      (poissonSplitKernel q ∘ₘ
          poissonMeasure (Real.toNNReal ((u + v) * r))).real {(k, s)} =
        ∫ n, (poissonSplitMeasure q n).real {(k, s)}
          ∂poissonMeasure (Real.toNNReal ((u + v) * r)) := by
    rw [measureReal_def, Measure.bind_apply (measurableSet_singleton _) (by fun_prop),
      ← integral_toReal (by fun_prop)]
    · apply integral_congr_ae
      filter_upwards with n
      rfl
    · filter_upwards with n
      exact measure_lt_top _ _
  change (poissonSplitKernel q ∘ₘ
      poissonMeasure (Real.toNNReal ((u + v) * r))).real {(k, s)} = _
  rw [hreal, integral_countable (by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with n
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)).trans_eq
      (by simp))]
  simp only [smul_eq_mul]
  rw [show (fun n : Nat =>
      (poissonMeasure (Real.toNNReal ((u + v) * r))).real {n} *
        (poissonSplitMeasure q n).real {(k, s)}) = fun n =>
      if n = k + s then
        (poissonMeasure (Real.toNNReal ((u + v) * r))).real {n} *
          (binomial (k + s) q).real {k}
      else 0 by
    funext n
    simp only [measureReal_def]
    rw [poissonSplitMeasure_singleton]
    split_ifs <;> simp_all]
  rw [tsum_ite_eq (k + s), prod_real_singleton]
  exact poisson_binomial_split u v r hu hv hr ht k s

/-- Apply the same countable-state kernel independently in finitely many coordinates.  [the stated conditions](hyp:K) [the stated conclusion](goal). -/
noncomputable def coordinatewiseKernel
    {I X Y : Type*} [Fintype I] [MeasurableSpace X] [Countable (I → X)]
    [MeasurableSingletonClass (I → X)] [MeasurableSpace Y]
    (K : Kernel X Y) : Kernel (I → X) (I → Y) :=
  Kernel.ofFunOfCountable fun x => Measure.pi fun i => K (x i)

/-- Applying [a kernel](hyp:K) coordinatewise at [an input array](hyp:x) [equals the product measure of its coordinatewise applications](goal). -/
@[simp] theorem coordinatewiseKernel_apply
    {I X Y : Type*} [Fintype I] [MeasurableSpace X] [Countable (I → X)]
    [MeasurableSingletonClass (I → X)] [MeasurableSpace Y]
    (K : Kernel X Y) (x : I → X) :
    coordinatewiseKernel K x = Measure.pi fun i => K (x i) := rfl
/-- [the stated conditions](hyp:K) defines [the specified object](goal). -/

noncomputable instance coordinatewiseKernel_isMarkovKernel
    {I X Y : Type*} [Fintype I] [MeasurableSpace X] [Countable (I → X)]
    [MeasurableSingletonClass (I → X)] [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] :
    IsMarkovKernel (coordinatewiseKernel K : Kernel (I → X) (I → Y)) where
  isProbabilityMeasure x := by
    change IsProbabilityMeasure (Measure.pi fun i => K (x i))
    infer_instance

/-- A one-coordinate TV bound tensorizes across an i.i.d. finite product.  [the stated conditions](hyp:h) [the stated conclusion](goal). -/
theorem tvDist_pi_iid_le_bound
    {X : Type*} [MeasurableSpace X] (k : Nat) (mu nu : Measure X)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (delta : Real)
    (h : Causalean.Stat.tvDist mu nu ≤ delta) :
    Causalean.Stat.tvDist (Measure.pi fun _ : Fin k => mu)
        (Measure.pi fun _ : Fin k => nu) ≤ k * delta := by
  exact (Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_pi_iid_le k mu nu).trans
    (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg k))

/-- Split only the aggregate control coordinate of a marked-Poisson observation.  [the stated conditions](hyp:q) [the stated conclusion](goal). -/
noncomputable def markedControlSplitKernel (q : unitInterval) :
    Kernel
      Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.MarkedPoissonObservation
      ((Nat × Nat) × (Nat × (Nat × Nat))) :=
  Kernel.id ∥ₖ (Kernel.id ∥ₖ poissonSplitKernel q)
/-- [the stated conditions](hyp:q) defines [the specified object](goal). -/

noncomputable instance markedControlSplitKernel_isMarkovKernel (q : unitInterval) :
    IsMarkovKernel (markedControlSplitKernel q) := by
  unfold markedControlSplitKernel
  infer_instance

/-- The marked-Poisson law after control splitting, with all five raw rates exposed.  [the stated conditions](hyp:hu,hv,hcontrol,ht) [the stated conclusion](goal). -/
theorem markedControlSplitKernel_comp_markedPoissonLaw
    (eps a u v : Real) (h : Real → Real) (branch : Bool) (p : Real)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hcontrol :
      0 ≤ Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.controlMass
        eps a p)
    (ht : 0 < u + v) :
    markedControlSplitKernel
        (⟨u / (u + v), by
          constructor
          · positivity
          · rw [div_le_one ht]
            linarith⟩ : unitInterval) ∘ₘ
        Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.markedPoissonLaw
          eps a u v h branch p =
      ((poissonMeasure (Real.toNNReal
          (u * Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.treatedMass
            eps a p *
            (1 + Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.branchMark
              branch (h p)) / 2))).prod
        (poissonMeasure (Real.toNNReal
          (u * Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.treatedMass
            eps a p *
            (1 - Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.branchMark
              branch (h p)) / 2)))).prod
        ((poissonMeasure (Real.toNNReal
          (v * Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.treatedMass
            eps a p))).prod
          ((poissonMeasure (Real.toNNReal
            (u * Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.controlMass
              eps a p))).prod
            (poissonMeasure (Real.toNNReal
              (v * Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.controlMass
                eps a p))))) := by
  let q : unitInterval :=
    ⟨u / (u + v), by
      constructor
      · positivity
      · rw [div_le_one ht]
        linarith⟩
  change markedControlSplitKernel q ∘ₘ
      Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.markedPoissonLaw
        eps a u v h branch p = _
  unfold Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.markedPoissonLaw
  unfold markedControlSplitKernel
  rw [← Measure.prod_comp_right, ← Measure.prod_comp_right]
  dsimp [q]
  rw [poissonSplitKernel_comp_poisson u v
    (Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.controlMass
      eps a p) hu hv hcontrol ht]

/-- Pad an injectively indexed family and one distinguished coordinate by a fixed
value on all unused coordinates.  [the stated conditions](hyp:f,r,y0) [the stated conclusion](goal). -/
noncomputable def finitePadding
    {I J Y : Type*} [Fintype I] [DecidableEq J]
    (f : I → J) (r : J) (y0 : Y) : ((I → Y) × Y) → J → Y := fun zy j =>
  if hj : j = r then zy.2
  else if hi : ∃ i, j = f i then zy.1 (Classical.choose hi)
  else y0

/-- Coordinate laws corresponding to `finitePadding`.  [the stated conditions](hyp:f,r,mu,nu,y0) [the stated conclusion](goal). -/
noncomputable def finitePaddedMeasure
    {I J Y : Type*} [Fintype I] [DecidableEq J]
    [MeasurableSpace Y]
    (f : I → J) (r : J) (mu : I → Measure Y) (nu : Measure Y) (y0 : Y) :
    J → Measure Y := fun j =>
  if hj : j = r then nu
  else if hi : ∃ i, j = f i then mu (Classical.choose hi)
  else Measure.dirac y0

/-- Pad an injectively indexed finite product and one distinguished coordinate by a
fixed value on all unused coordinates.  [the stated conditions](hyp:hf,hr) [the stated conclusion](goal). -/
theorem pi_prod_map_finitePadding
    {I J Y : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (f : I → J) (r : J) (hf : Function.Injective f) (hr : ∀ i, r ≠ f i)
    (mu : I → Measure Y) (nu : Measure Y) (y0 : Y)
    [∀ i, IsProbabilityMeasure (mu i)] [IsProbabilityMeasure nu] :
    ((Measure.pi mu).prod nu).map (finitePadding f r y0) =
      Measure.pi (finitePaddedMeasure f r mu nu y0) := by
  classical
  let pad : ((I → Y) × Y) → J → Y := finitePadding f r y0
  have hchoose (i : I) (hi : ∃ i', f i = f i') : Classical.choose hi = i := by
    apply hf
    exact (Classical.choose_spec hi).symm
  have hpad_meas : Measurable pad := by
    refine measurable_pi_lambda _ fun j => ?_
    by_cases hj : j = r
    · simpa [pad, finitePadding, hj] using measurable_snd
    · by_cases hi : ∃ i, j = f i
      · simp only [pad, finitePadding, hj, hi, ↓reduceDIte]
        exact (measurable_pi_apply (Classical.choose hi)).comp measurable_fst
      · simp only [pad, finitePadding, hj, hi, ↓reduceDIte]
        exact measurable_const
  letI : ∀ j, SigmaFinite (finitePaddedMeasure f r mu nu y0 j) :=
    fun j => by
      unfold finitePaddedMeasure
      split
      · exact IsFiniteMeasure.toSigmaFinite nu
      · split
        · exact IsFiniteMeasure.toSigmaFinite (mu _)
        · exact IsFiniteMeasure.toSigmaFinite (Measure.dirac y0)
  symm
  refine Measure.pi_eq (μ := finitePaddedMeasure f r mu nu y0) fun s hs => ?_
  simp only [finitePaddedMeasure]
  rw [Measure.map_apply hpad_meas (MeasurableSet.pi Set.countable_univ fun j _ => hs j)]
  by_cases hbad : ∃ j, j ≠ r ∧ (∀ i, j ≠ f i) ∧ y0 ∉ s j
  · obtain ⟨j, hjr, hjf, hj0⟩ := hbad
    have hpre : pad ⁻¹' (Set.univ.pi s) = ∅ := by
      ext zy
      constructor
      · intro hz
        have := hz j (Set.mem_univ j)
        simp only [pad, finitePadding] at this
        rw [dif_neg hjr, dif_neg (not_exists.mpr hjf)] at this
        exact (hj0 this).elim
      · intro hz
        simpa using hz
    rw [hpre, measure_empty]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [dif_neg hjr, dif_neg (not_exists.mpr hjf), Measure.dirac_apply' y0 (hs j)]
    simp [hj0]
  · push_neg at hbad
    have hpre : pad ⁻¹' (Set.univ.pi s) =
        (Set.univ.pi fun i => s (f i)) ×ˢ s r := by
      ext zy
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_prod]
      constructor
      · intro hz
        constructor
        · intro i
          simpa [pad, finitePadding, (hr i).symm, hchoose i] using hz (f i)
        · simpa [pad, finitePadding] using hz r
      · rintro ⟨hzi, hzr⟩ j
        by_cases hjr : j = r
        · simpa [pad, finitePadding, hjr] using hzr
        · by_cases hjf : ∃ i, j = f i
          · have hj : j = f (Classical.choose hjf) := Classical.choose_spec hjf
            rw [show pad zy j = zy.1 (Classical.choose hjf) by
              simp only [pad, finitePadding, hjr, hjf, ↓reduceDIte]]
            rw [congrArg s hj]
            exact hzi (Classical.choose hjf)
          · simpa [pad, finitePadding, hjr, hjf] using hbad j hjr (not_exists.mp hjf)
    rw [hpre, Measure.prod_prod, Measure.pi_pi]
    have hcoord (i : I) :
        (if hj : f i = r then nu
          else if hi : ∃ i', f i = f i' then mu (Classical.choose hi)
          else Measure.dirac y0) (s (f i)) = mu i (s (f i)) := by
      simp [show f i ≠ r from (hr i).symm, hchoose i]
    have hunused (j : J) (hjr : j ≠ r) (hjf : ∀ i, j ≠ f i) :
        (if hj : j = r then nu
          else if hi : ∃ i, j = f i then mu (Classical.choose hi)
          else Measure.dirac y0) (s j) = 1 := by
      rw [dif_neg hjr, dif_neg (not_exists.mpr hjf), Measure.dirac_apply' y0 (hs j)]
      simp [hbad j hjr hjf]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ r)]
    simp only [if_pos]
    apply congrArg (fun z => z * nu (s r))
    symm
    calc
      ∏ j ∈ Finset.univ.erase r,
          (if hj : j = r then nu
            else if hi : ∃ i, j = f i then mu (Classical.choose hi)
            else Measure.dirac y0) (s j) =
          ∏ j ∈ Finset.univ.image f,
            (if hj : j = r then nu
              else if hi : ∃ i, j = f i then mu (Classical.choose hi)
              else Measure.dirac y0) (s j) := by
        apply (Finset.prod_subset ?_ ?_).symm
        · intro j hj
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj
          obtain ⟨i, rfl⟩ := hj
          exact Finset.mem_erase.mpr ⟨(hr i).symm, Finset.mem_univ _⟩
        · intro j hj jhimage
          rw [hunused j (Finset.mem_erase.mp hj).1]
          intro i hji
          apply jhimage
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hji.symm⟩
      _ = ∏ i, (if hj : f i = r then nu
              else if hi : ∃ i', f i = f i' then mu (Classical.choose hi)
              else Measure.dirac y0) (s (f i)) :=
        Finset.prod_image hf.injOn
      _ = ∏ i, mu i (s (f i)) :=
        Finset.prod_congr rfl fun i _ => hcoord i

/-- A binary product, written as a Boolean-indexed random function.  [the stated conclusion](goal). -/
theorem prod_map_boolArrow
    {Y : Type*} [MeasurableSpace Y] (muFalse muTrue : Measure Y)
    [IsProbabilityMeasure muFalse] [IsProbabilityMeasure muTrue] :
    (muFalse.prod muTrue).map (fun z arm => if arm then z.2 else z.1) =
      Measure.pi fun arm : Bool => if arm then muTrue else muFalse := by
  classical
  symm
  refine Measure.pi_eq (μ := fun arm : Bool => if arm then muTrue else muFalse)
    fun s hs => ?_
  have hfun : Measurable (fun (z : Y × Y) (arm : Bool) =>
      if arm then z.2 else z.1) := by
    refine measurable_pi_lambda _ fun arm => ?_
    cases arm <;> simp only [Bool.false_eq_true, if_false, if_true]
    · exact measurable_fst
    · exact measurable_snd
  rw [Measure.map_apply hfun
      (MeasurableSet.pi Set.countable_univ fun arm _ => hs arm)]
  have hpre : (fun z arm => if arm then z.2 else z.1) ⁻¹' Set.univ.pi s =
      s false ×ˢ s true := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_prod]
    constructor
    · intro hz
      exact ⟨by simpa using hz false, by simpa using hz true⟩
    · rintro ⟨hf, ht⟩ arm
      cases arm <;> assumption
  rw [hpre, Measure.prod_prod]
  simp [Fintype.prod_bool, mul_comm]

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

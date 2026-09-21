namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability

/-- Under [a probability design law](hyp:Q), [a Markov marking kernel](hyp:K), [a
measurable conditional mean](hyp:mD,hmD) satisfying [the kernel mean identity](hyp:hmean),
[unit-interval marks on almost every kernel fibre](hyp:hbound), and [a measurable complete-design
coefficient array](hyp:w,hw), [the weighted centered mark sum is conditionally sub-Gaussian
with variance proxy equal to one quarter of realized weight energy](goal). -/
theorem product_weighted_centered_attachKernel_hasSubgaussianMGF
    {N : Nat} {D : Type*} [MeasurableSpace D]
    (Q : Measure D) [IsProbabilityMeasure Q]
    (K : Kernel D Real) [IsMarkovKernel K]
    (mD : D -> Real) (hmD : Measurable mD)
    (hmean : ∀ᵐ d ∂Q, ∫ y, y ∂K d = mD d)
    (hbound : ∀ᵐ d ∂Q, ∀ᵐ y ∂K d, y ∈ Set.Icc (0 : Real) 1)
    (w : (Fin N -> D) -> Fin N -> Real) (hw : Measurable w) :
    ∀ᵐ d ∂Measure.pi (fun _ : Fin N => Q),
      HasSubgaussianMGF (weightedCenteredMarkSum mD w d)
        (Real.toNNReal (realizedWeightEnergy w d / 4))
        (Causalean.Stat.finProductKernel N K d) := by
  have hmeans :
      ∀ᵐ d ∂Measure.pi (fun _ : Fin N => Q),
        ∀ i, ∫ y, y ∂K (d i) = mD (d i) := by
    rw [ae_all_iff]
    intro i
    exact Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin N => Q) (i := i) |>.eventually hmean
  have hbounds :
      ∀ᵐ d ∂Measure.pi (fun _ : Fin N => Q),
        ∀ i, ∀ᵐ y ∂K (d i), y ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_all_iff]
    intro i
    exact Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin N => Q) (i := i) |>.eventually hbound
  filter_upwards [hmeans, hbounds] with d hdmean hdbound
  rw [Causalean.Stat.finProductKernel_apply]
  let mu : Measure (Fin N -> ℝ) := Measure.pi (fun i : Fin N => K (d i))
  let X : Fin N -> (Fin N -> ℝ) -> ℝ :=
    fun i y => w d i * (y i - mD (d i))
  let c : Fin N -> NNReal := fun i =>
    ⟨(w d i) ^ 2, sq_nonneg _⟩ * ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2)
  have hindep_eval : iIndepFun (fun i (y : Fin N -> ℝ) => y i) mu :=
    iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
  have hindep : iIndepFun X mu :=
    hindep_eval.comp (fun i y => w d i * (y - mD (d i)))
      (fun i => measurable_const.mul (measurable_id.sub measurable_const))
  have hsub : ∀ i, HasSubgaussianMGF (X i) (c i) mu := by
    intro i
    have hbase := hasSubgaussianMGF_of_mem_Icc
      (μ := K (d i)) (X := id) measurable_id.aemeasurable (hdbound i)
    have hcentered : HasSubgaussianMGF (fun y : ℝ => y - mD (d i))
        ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) (K (d i)) := by
      simpa [hdmean i] using hbase
    have hmap : Measure.map (fun y : Fin N -> ℝ => y i) mu = K (d i) := by
      simpa only [mu] using
        (measurePreserving_eval (fun j : Fin N => K (d j)) i).map_eq
    rw [← hmap] at hcentered
    have hbase' := HasSubgaussianMGF.of_map
      (μ := mu) (Y := fun y : Fin N -> ℝ => y i)
      (X := fun y : ℝ => y - mD (d i))
      (measurable_pi_apply i).aemeasurable hcentered
    change HasSubgaussianMGF (fun y : Fin N -> ℝ => y i - mD (d i))
      ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) mu at hbase'
    have hscaled := hbase'.const_mul (w d i)
    simpa only [X, c] using hscaled
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hindep
    (s := Finset.univ) (fun i _ => hsub i)
  have hc_sum : (↑(∑ i, c i) : ℝ) = realizedWeightEnergy w d / 4 := by
    rw [NNReal.coe_sum]
    simp only [c]
    norm_num [Real.norm_eq_abs]
    change (∑ i, (w d i) ^ 2 * (1 / 4)) =
      (∑ i, (w d i) ^ 2) / 4
    rw [← Finset.sum_mul]
    ring
  have henergy_nonneg : 0 <= realizedWeightEnergy w d := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg (w d i)
  have hc : (∑ i, c i) = Real.toNNReal (realizedWeightEnergy w d / 4) := by
    apply NNReal.eq
    rw [hc_sum, Real.coe_toNNReal _ (div_nonneg henergy_nonneg (by norm_num))]
  rw [hc] at hsum
  change HasSubgaussianMGF
    (fun y : Fin N -> Real => ∑ i, w d i * (y i - mD (d i)))
    (Real.toNNReal (realizedWeightEnergy w d / 4))
    (Measure.pi (fun i : Fin N => K (d i)))
  simpa only [mu, X] using hsum

/-- Under [a probability design law](hyp:Q), [a Markov marking kernel](hyp:K), [a
measurable conditional mean](hyp:mD,hmD) satisfying [the kernel mean identity](hyp:hmean),
[unit-interval marks on almost every kernel fibre](hyp:hbound), and [a measurable complete-design
coefficient array](hyp:w,hw), [the conditional weighted-sum exponential moment is bounded by
the Hoeffding proxy equal to one quarter of realized weight energy](goal). -/
theorem product_weighted_centered_attachKernel_conditional_mgf_le
    {N : Nat} {D : Type*} [MeasurableSpace D]
    (Q : Measure D) [IsProbabilityMeasure Q]
    (K : Kernel D Real) [IsMarkovKernel K]
    (mD : D -> Real) (hmD : Measurable mD)
    (hmean : ∀ᵐ d ∂Q, ∫ y, y ∂K d = mD d)
    (hbound : ∀ᵐ d ∂Q, ∀ᵐ y ∂K d, y ∈ Set.Icc (0 : Real) 1)
    (w : (Fin N -> D) -> Fin N -> Real) (hw : Measurable w) :
    ∀ᵐ d ∂Measure.pi (fun _ : Fin N => Q), ∀ s : Real,
      ∫ y, Real.exp (s * weightedCenteredMarkSum mD w d y)
          ∂Causalean.Stat.finProductKernel N K d <=
        Real.exp (s ^ 2 * realizedWeightEnergy w d / 8) := by
  filter_upwards [product_weighted_centered_attachKernel_hasSubgaussianMGF
    Q K mD hmD hmean hbound w hw] with d hd
  intro s
  have hmgf := hd.mgf_le s
  have henergy_nonneg : 0 <= realizedWeightEnergy w d := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg (w d i)
  rw [Real.coe_toNNReal _ (div_nonneg henergy_nonneg (by norm_num))] at hmgf
  simp only [mgf] at hmgf
  convert hmgf using 1
  congr 1
  ring

/-- Under [a probability observation law](hyp:P), [a measurable design map](hyp:design,hdesign),
[a measurable unit-interval outcome](hyp:Y,hY,hY_nonneg,hY_le_one), [a measurable regression](hyp:mD,hmD)
equal to [its conditional expectation given the design](hyp:hcond), and [a measurable complete-design
coefficient array](hyp:w,hw), [the full-design conditional weighted-sum exponential moment has
the Hoeffding bound with one-quarter realized weight energy](goal). -/
theorem product_weighted_centered_conditional_mgf_le
    {N : Nat} {Omega D : Type*} [MeasurableSpace Omega] [MeasurableSpace D]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (design : Omega -> D) (hdesign : Measurable design)
    (Y : Omega -> Real) (hY : Measurable Y)
    (hY_nonneg : ∀ᵐ omega ∂P, 0 <= Y omega)
    (hY_le_one : ∀ᵐ omega ∂P, Y omega <= 1)
    (mD : D -> Real) (hmD : Measurable mD)
    (hcond :
      P[Y | MeasurableSpace.comap design inferInstance] =ᵐ[P] mD ∘ design)
    (w : (Fin N -> D) -> Fin N -> Real) (hw : Measurable w) :
    ∀ᵐ d ∂Measure.pi (fun _ : Fin N => P.map design), ∀ s : Real,
      ∫ y, Real.exp (s * weightedCenteredMarkSum mD w d y)
          ∂Causalean.Stat.finProductKernel N (condDistrib Y design P) d <=
        Real.exp (s ^ 2 * realizedWeightEnergy w d / 8) := by
  have hY_mem : ∀ᵐ omega ∂P, Y omega ∈ Set.Icc (0 : ℝ) 1 :=
    hY_nonneg.and hY_le_one
  have hY_int : Integrable Y P :=
    Integrable.of_mem_Icc 0 1 hY.aemeasurable hY_mem
  have hmean_comp :
      (fun omega => ∫ y, y ∂condDistrib Y design P (design omega)) =ᵐ[P]
        mD ∘ design :=
    (condExp_ae_eq_integral_condDistrib' hdesign hY_int).symm.trans hcond
  have hmean :
      ∀ᵐ d ∂P.map design, ∫ y, y ∂condDistrib Y design P d = mD d := by
    rw [ae_map_iff hdesign.aemeasurable]
    · filter_upwards [hmean_comp] with x hx
      exact hx
    · exact measurableSet_eq_fun
        (((stronglyMeasurable_id.comp_measurable measurable_snd).integral_condDistrib
          (X := design) (Y := Y) (μ := P)).measurable)
        hmD
  have hpair :
      ∀ᵐ p ∂(P.map design ⊗ₘ condDistrib Y design P),
        p.2 ∈ Set.Icc (0 : ℝ) 1 := by
    rw [compProd_map_condDistrib hY.aemeasurable]
    rw [ae_map_iff (hdesign.prodMk hY).aemeasurable]
    · simpa using hY_mem
    · exact measurableSet_Icc.preimage measurable_snd
  have hrange :
      ∀ᵐ d ∂P.map design,
        ∀ᵐ y ∂condDistrib Y design P d, y ∈ Set.Icc (0 : ℝ) 1 :=
    Measure.ae_ae_of_ae_compProd hpair
  letI : IsProbabilityMeasure (P.map design) :=
    Measure.isProbabilityMeasure_map hdesign.aemeasurable
  exact product_weighted_centered_attachKernel_conditional_mgf_le
    (P.map design) (condDistrib Y design P) mD hmD hmean hrange w hw

end Causalean.Stat.Concentration

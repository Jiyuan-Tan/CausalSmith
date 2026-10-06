module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CombinedBias

/-! # Coordinate and spatial assembly of the exact Taylor polynomial

These identities connect the Fréchet Taylor remainder to the coordinate sums
used in the exact quadratic and cubic projection means.
-/

@[expose] public section

open MeasureTheory
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Expansion of a multilinear form on the diagonal in the estimator's basis.  Under [the displayed assumptions and inputs](hyp:q,T,h), [the stated conclusion holds](goal). -/
-- @node: density_multilinear_diagonal_expansion
lemma density_multilinear_diagonal_expansion {q : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin q => Fin 7 → ℝ) ℝ)
    (h : Fin 7 → ℝ) :
    T (fun _ => h) = ∑ idx : Fin q → Fin 7,
      (∏ j : Fin q, h (idx j)) * T (fun j => basis (idx j)) := by
  classical
  have hh : (∑ i : Fin 7, h i • basis i) = h := by
    ext j
    simp [basis, Finset.sum_apply]
  calc
    T (fun _ => h) = T (fun _ => ∑ i : Fin 7, h i • basis i) := by rw [hh]
    _ = ∑ idx : Fin q → Fin 7, T (fun j => h (idx j) • basis (idx j)) :=
      T.map_sum (fun _ i => h i • basis i)
    _ = _ := by simp_rw [T.map_smul_univ, smul_eq_mul]

/-- Reindexing a sum over a finite tuple by its first entry and its tail.  Under [the displayed assumptions and inputs](hyp:q,f), [the stated conclusion holds](goal). -/
-- @node: sum_density_tuple_cons
lemma sum_density_tuple_cons {q : ℕ} (f : (Fin (q + 1) → Fin 7) → ℝ) :
    (∑ idx, f idx) = ∑ i : Fin 7, ∑ idx : Fin q → Fin 7, f (Fin.cons i idx) := by
  classical
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (q + 1) => Fin 7))]
  exact Fintype.sum_prod_type _

/-- The first Fréchet Taylor term is the exact coordinate linear polynomial.  Under [the displayed assumptions and inputs](hyp:A,v,h), [the stated conclusion holds](goal). -/
-- @node: iteratedFDeriv_one_eq_coordinate_sum
lemma iteratedFDeriv_one_eq_coordinate_sum (A : Bool) (v h : Fin 7 → ℝ) :
    iteratedFDeriv ℝ 1 (Phi A) v ![h] =
      ∑ i : Fin 7, dPhi1 A v i * h i := by
  have hv : (![h] : Fin 1 → Fin 7 → ℝ) = fun _ => h := by ext j; fin_cases j; rfl
  rw [hv, density_multilinear_diagonal_expansion, sum_density_tuple_cons]
  simp [dPhi1, iteratedFDeriv_one_apply, mul_comm]

/-- The second Fréchet Taylor term is the exact ordered coordinate sum.  Under [the displayed assumptions and inputs](hyp:A,v,h), [the stated conclusion holds](goal). -/
-- @node: iteratedFDeriv_two_eq_coordinate_sum
lemma iteratedFDeriv_two_eq_coordinate_sum (A : Bool) (v h : Fin 7 → ℝ) :
    iteratedFDeriv ℝ 2 (Phi A) v ![h, h] =
      ∑ i : Fin 7, ∑ j : Fin 7, dPhi2 A v i j * h i * h j := by
  have hv : (![h, h] : Fin 2 → Fin 7 → ℝ) = fun _ => h := by
    ext j; fin_cases j <;> rfl
  rw [hv, density_multilinear_diagonal_expansion, sum_density_tuple_cons]
  simp_rw [sum_density_tuple_cons]
  simp only [dPhi2, Finset.univ_unique, Nat.reduceAdd, Fin.prod_univ_two,
    Fin.isValue, Fin.cons_zero, Fin.cons_one, Finset.sum_singleton, mul_comm, mul_left_comm, mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 3
  ext r; fin_cases r <;> rfl

/-- The third Fréchet Taylor term is the exact ordered coordinate sum.  Under [the displayed assumptions and inputs](hyp:A,v,h), [the stated conclusion holds](goal). -/
-- @node: iteratedFDeriv_three_eq_coordinate_sum
lemma iteratedFDeriv_three_eq_coordinate_sum (A : Bool) (v h : Fin 7 → ℝ) :
    iteratedFDeriv ℝ 3 (Phi A) v ![h, h, h] =
      ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
        dPhi3 A v i j k * h i * h j * h k := by
  have hv : (![h, h, h] : Fin 3 → Fin 7 → ℝ) = fun _ => h := by
    ext j; fin_cases j <;> rfl
  rw [hv, density_multilinear_diagonal_expansion, sum_density_tuple_cons]
  simp_rw [sum_density_tuple_cons]
  simp only [dPhi3, Finset.univ_unique, Nat.reduceAdd, Fin.prod_univ_three,
    Fin.isValue, Fin.cons_zero, Fin.cons_one, Finset.sum_singleton, mul_comm, mul_left_comm, mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  congr 4
  ext r; fin_cases r <;> rfl

/-- A function continuous in the spatial argument at each fixed pilot value
is integrable on the compact covariate region: the pilot has finitely many values.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,n,g,hg), [the stated conclusion holds](goal). -/
-- @node: integrableOn_spatial_pilot_composition
lemma integrableOn_spatial_pilot_composition (c_f C_f : ℝ) {n : ℕ}
    (ω : TwoSample n n) (g : (Fin 7 → ℝ) → ℝ → ℝ)
    (hg : ∀ v, ContinuousOn (g v) covariateSpace) :
    IntegrableOn (fun x => g (pilot c_f C_f ω x) x) covariateSpace := by
  have hK : 0 < pilotResolution n := by
    unfold pilotResolution dyadicResolution
    split_ifs <;> positivity
  rw [← iUnion_cell_eq_covariateSpace hK, integrableOn_finite_iUnion]
  intro l
  have hi : IntegrableOn (g (pilot c_f C_f ω (midpoint (pilotResolution n) l)))
      covariateSpace := (hg _).integrableOn_Icc
  apply (integrableOn_congr_fun (s := cell (pilotResolution n) l)
    (g := g (pilot c_f C_f ω (midpoint (pilotResolution n) l)))
    (by
      intro x hx
      exact congrArg (fun v => g v x)
        (pilot_eq_midpoint_of_refinement c_f C_f hK (dvd_refl _) ω l hx))
    (measurableSet_cell _ _)).2
  exact hi.mono_set (cell_subset_covariateSpace hK l)

/-- Every spatial coordinate Taylor monomial is integrable, without additional
regularity assumptions on the data or a pilot-dependent coefficient.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,q,hP,a,idx), [the stated conclusion holds](goal). -/
-- @node: integrableOn_spatial_pilot_monomial
lemma integrableOn_spatial_pilot_monomial (c_f C_f L : ℝ) (P : TransportLaw)
    (n q : ℕ) (hP : ModelClass c_f C_f L P n) (ω : TwoSample n n)
    (a : (Fin 7 → ℝ) → ℝ) (idx : Fin q → Fin 7) :
    IntegrableOn (fun x => a (pilot c_f C_f ω x) *
      ∏ j : Fin q, (markedDensityVector c_f C_f L P n hP x (idx j) -
        pilot c_f C_f ω x (idx j))) covariateSpace := by
  apply integrableOn_spatial_pilot_composition c_f C_f ω
    (fun v x => a v * ∏ j : Fin q,
      (markedDensityVector c_f C_f L P n hP x (idx j) - v (idx j)))
  intro v
  have hF (i : Fin 7) := markedDensityVector_continuousOn c_f C_f L P n hP i
  fun_prop

/-- If [a function satisfies the stated Hölder condition](hyp:hf), then [it is continuous on the covariate region](goal). -/
-- @node: holderOn_continuousOn_covariateSpace
@[fun_prop] lemma holderOn_continuousOn_covariateSpace {f : ℝ → ℝ} {L : ℝ}
    (hf : HolderOn f L) : ContinuousOn f covariateSpace := by
  have hmap : ContinuousOn (fun x : ℝ => ![x]) covariateSpace := by fun_prop
  have hmaps : Set.MapsTo (fun x : ℝ => ![x]) covariateSpace
      {v : Fin 1 → ℝ | v 0 ∈ covariateSpace} := by
    intro x hx
    simpa using hx
  simpa [Function.comp_def] using hf.2.1.continuousOn.comp hmap hmaps

/-- The exact spatial Taylor polynomial and remainder integrate to the
transported form. All ordered coordinate sums retain their factorial factors.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated conclusion holds](goal). -/
-- @node: spatialTaylorRemainder_eq_transport_sub_coordinate_terms
lemma spatialTaylorRemainder_eq_transport_sub_coordinate_terms
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) (ω : TwoSample n n) (A : Bool) :
    spatialTaylorRemainder c_f C_f L P n hP ω A = transportedForm P A -
      (pilotIntegral c_f C_f ω A +
        (∑ i : Fin 7, ∫ x in covariateSpace,
          dPhi1 A (pilot c_f C_f ω x) i *
            (markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i)) +
        (∑ i : Fin 7, ∑ j : Fin 7, ∫ x in covariateSpace,
          (dPhi2 A (pilot c_f C_f ω x) i j / 2) *
            (markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i) *
            (markedDensityVector c_f C_f L P n hP x j - pilot c_f C_f ω x j)) +
        (∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, ∫ x in covariateSpace,
          (dPhi3 A (pilot c_f C_f ω x) i j k / 6) *
            (markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i) *
            (markedDensityVector c_f C_f L P n hP x j - pilot c_f C_f ω x j) *
            (markedDensityVector c_f C_f L P n hP x k - pilot c_f C_f ω x k))) := by
  let F := markedDensityVector c_f C_f L P n hP
  let v := pilot c_f C_f ω
  let h := fun x => F x - v x
  let l := fun i x => dPhi1 A (v x) i * h x i
  let q := fun i j x => (dPhi2 A (v x) i j / 2) * h x i * h x j
  let c := fun i j k x => (dPhi3 A (v x) i j k / 6) * h x i * h x j * h x k
  have hl (i : Fin 7) : IntegrableOn (l i) covariateSpace := by
    simpa [l, h, v, F] using integrableOn_spatial_pilot_monomial
      c_f C_f L P n 1 hP ω (fun v => dPhi1 A v i) ![i]
  have hq (i j : Fin 7) : IntegrableOn (q i j) covariateSpace := by
    simpa [q, h, v, F, Fin.prod_univ_two, mul_assoc] using integrableOn_spatial_pilot_monomial
      c_f C_f L P n 2 hP ω (fun v => dPhi2 A v i j / 2) ![i, j]
  have hc (i j k : Fin 7) : IntegrableOn (c i j k) covariateSpace := by
    simpa [c, h, v, F, Fin.prod_univ_three, mul_assoc] using integrableOn_spatial_pilot_monomial
      c_f C_f L P n 3 hP ω (fun v => dPhi3 A v i j k / 6) ![i, j, k]
  have hp : IntegrableOn (fun x => Phi A (v x)) covariateSpace :=
    integrableOn_spatial_pilot_composition c_f C_f ω (fun v _ => Phi A v)
      (fun _ => continuousOn_const)
  have ht : IntegrableOn (fun x => Phi A (F x)) covariateSpace := by
    have hT := holderOn_continuousOn_covariateSpace hP.targetHolder
    have hm1 := holderOn_continuousOn_covariateSpace (hP.armHolder.1 A true)
    have hm0 := holderOn_continuousOn_covariateSpace (hP.armHolder.1 A false)
    have hi : IntegrableOn (fun x => P.fT x * armContrast P A x) covariateSpace :=
      (hT.mul (hm1.sub hm0)).integrableOn_Icc
    exact (integrableOn_congr_fun
      (fun x hx => Phi_markedDensityVector_eq_transport_integrand c_f C_f L P n hP A x hx)
      measurableSet_Icc).2 hi
  have hls := integrable_finsetSum Finset.univ (fun i _ => hl i)
  have hqs := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hq i j))
  have hcs := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ => hc i j k)))
  have heq : spatialTaylorRemainder c_f C_f L P n hP ω A =
      ∫ x in covariateSpace, Phi A (F x) -
        (Phi A (v x) + (∑ i, l i x) + (∑ i, ∑ j, q i j x) +
          (∑ i, ∑ j, ∑ k, c i j k x)) := by
    unfold spatialTaylorRemainder
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    dsimp only
    rw [iteratedFDeriv_one_eq_coordinate_sum, iteratedFDeriv_two_eq_coordinate_sum,
      iteratedFDeriv_three_eq_coordinate_sum]
    simp only [Finset.sum_div]
    simp only [l, q, c, h, v, F, Pi.sub_apply, div_mul_eq_mul_div]
  rw [heq]
  have hsub := integral_sub ht (((hp.add hls).add hqs).add hcs)
  have hadd3 := integral_add ((hp.add hls).add hqs) hcs
  have hadd2 := integral_add (hp.add hls) hqs
  have hadd1 := integral_add hp hls
  simp only [Pi.add_apply] at hsub hadd3 hadd2 hadd1
  rw [hsub, hadd3, hadd2, hadd1]
  rw [integral_finsetSum _ (fun i _ => hl i),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hq i j)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      integrable_finsetSum _ (fun k _ => hc i j k)))]
  simp_rw [integral_finsetSum _ (fun j _ => hq _ j),
    integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hc _ j k)),
    integral_finsetSum _ (fun k _ => hc _ _ k)]
  have ht' : (∫ x in covariateSpace, Phi A (F x)) = transportedForm P A := by
    rw [transportedForm_eq_integral_Phi_markedDensityVector c_f C_f L P n hP A]
    simp [F, covariateSpace, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc]
  have hp' : (∫ x in covariateSpace, Phi A (v x)) = pilotIntegral c_f C_f ω A := by
    simp [pilotIntegral, v, covariateSpace,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Icc_eq_integral_Ioc]
  rw [ht', hp']
  rfl

/-- The spatial linear Taylor term, the proposed conditional mean of the
held-out linear statistic in roadmap (10).  For [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated object is defined](goal). -/
-- @node: linearProjectionMean
noncomputable def linearProjectionMean (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) (ω : TwoSample n n) (A : Bool) : ℝ :=
  ∑ i : Fin 7, ∫ x in covariateSpace,
    dPhi1 A (pilot c_f C_f ω x) i *
      (markedDensityVector c_f C_f L P n hP x i - pilot c_f C_f ω x i)

/-- The projected mean of the exact cubic statistic. Identification with
conditional expectation still requires the held-out linear mean identity.  For [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated object is defined](goal). -/
-- @node: projectedEstimatorMean
noncomputable def projectedEstimatorMean (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) (ω : TwoSample n n) (A : Bool) : ℝ :=
  pilotIntegral c_f C_f ω A + linearProjectionMean c_f C_f L P n hP ω A +
    quadraticProjectionMean c_f C_f L P n hP ω A +
    cubicProjectionMean c_f C_f L P n hP ω A

/-- The exact projected mean has precisely the three spatial errors from
roadmap (14), with a common negative sign. No bias term is omitted.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated conclusion holds](goal). -/
-- @node: projectedEstimatorMean_sub_transport_eq_spatial_bias
lemma projectedEstimatorMean_sub_transport_eq_spatial_bias
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) (ω : TwoSample n n) (A : Bool) :
    projectedEstimatorMean c_f C_f L P n hP ω A - transportedForm P A =
      -(spatialTaylorRemainder c_f C_f L P n hP ω A +
        quadraticCellProjectionBias c_f C_f L P n (quadraticResolution n) hP ω A +
        spatialCubicProjectionBias c_f C_f L P n hP ω A) := by
  rw [spatialTaylorRemainder_eq_transport_sub_coordinate_terms,
    quadraticCellProjectionBias_eq_spatial_sub_projectionMean]
  unfold projectedEstimatorMean linearProjectionMean spatialCubicProjectionBias
  ring

/-- The exact projected mean's squared bias is the expression already
bounded by `combined_spatial_projection_bias_second_moment` in roadmap (14).  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated conclusion holds](goal). -/
-- @node: projectedEstimatorMean_squared_bias_integral_eq
lemma projectedEstimatorMean_squared_bias_integral_eq
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    (∫ ω, (projectedEstimatorMean c_f C_f L P n hP ω A - transportedForm P A) ^ 2
      ∂dataLaw P n n) =
    ∫ ω, (spatialTaylorRemainder c_f C_f L P n hP ω A +
      quadraticCellProjectionBias c_f C_f L P n (quadraticResolution n) hP ω A +
      spatialCubicProjectionBias c_f C_f L P n hP ω A) ^ 2 ∂dataLaw P n n := by
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [projectedEstimatorMean_sub_transport_eq_spatial_bias, neg_sq]

/-- Roadmap (14) holds for the exact projected estimator mean, with the
paper's explicit constant 3(BR+BQ+BC).  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: projectedEstimatorMean_squared_bias_sample_rate
lemma projectedEstimatorMean_squared_bias_sample_rate
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (A : Bool) :
    let H := 3 * (1 + C_f) * L
    let M := fourthDerivativeEnvelope c_f C_f
    let A2 := 2 * (1 + C_f + C_f ^ 2) * (5 : ℝ) ^ (1 / 5 : ℝ) +
      (2 : ℝ) ^ (5 / 4 : ℝ) * H ^ 2 * (5 : ℝ) ^ (1 / 5 : ℝ)
    let BR := (M / 24) ^ 2 * (7 : ℝ) ^ (8 : ℕ) * pilotEighthConstant C_f L
    let BQ := (7 : ℝ) ^ 4 * M ^ 2 * H ^ 4 * (2 : ℝ) ^ (1 / 2 : ℝ) *
      (5 : ℝ) ^ (2 / 3 : ℝ)
    let C1 := (M / 2) * (7 : ℝ) ^ 2 * H ^ 2
    let C2 := (M / 6) * (7 : ℝ) ^ 3 * H ^ 3
    let BC := 2 * (C1 ^ 2 * (7 : ℝ) ^ 2 * A2 * (2 : ℝ) ^ (1 / 2 : ℝ) *
      (5 : ℝ) ^ (1 / 2 : ℝ) + C2 ^ 2 * (2 : ℝ) ^ (3 / 4 : ℝ) *
      (5 : ℝ) ^ (3 / 4 : ℝ))
    (∫ ω, (projectedEstimatorMean c_f C_f L P n hP ω A - transportedForm P A) ^ 2
      ∂dataLaw P n n) ≤
      3 * (BR + BQ + BC) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  dsimp only
  rw [projectedEstimatorMean_squared_bias_integral_eq]
  exact combined_spatial_projection_bias_second_moment c_f C_f L P n hn hP A

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

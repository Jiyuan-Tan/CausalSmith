module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationMoments
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.TargetIdentification
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.TwoPoint

/-! # Oracle bandwidth and full-block information
The explicit constant-nuisance bump alternatives have a common auxiliary law.
Their labeled information tensorizes, and the oracle bandwidth cancels the
sample size in the resulting Hellinger bound.
-/

public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- The oracle bandwidth is positive, lies below one, and has the prescribed
bias and information scaling.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input gamma](hyp:gamma), [the specified input hg](hyp:hg), [the specified input hn](hyp:hn), [the oracle bandwidth identities conclusion](goal) holds. -/
lemma oracle_bandwidth_identities (d n : ℕ) (gamma : ℝ) (hg : 0 < gamma)
    (hn : 2 ≤ n) :
    let H := (n:ℝ)^(-(1/(2*gamma+d)))
    0 < H ∧ H ≤ 1 ∧ H^gamma = oracleRate d gamma n ∧
      (n:ℝ)*(oracleRate d gamma n)^2*H^d = 1 := by
  dsimp only
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hden : 0 < 2*gamma+(d:ℝ) := by positivity
  refine ⟨Real.rpow_pos_of_pos hn0 _,
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (one_div_nonneg.mpr hden.le)), ?_, ?_⟩
  · unfold oracleRate
    rw [← Real.rpow_mul hn0.le]
    congr 1
    ring
  · unfold oracleRate
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le,
      ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    conv_lhs => lhs; lhs; rw [← Real.rpow_one (n:ℝ)]
    rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
    have hexp : (1 + -(gamma/(2*gamma+d))*2) + -(1/(2*gamma+d))*(d:ℝ) = 0 := by
      field_simp
      <;> ring
    norm_num only [Nat.cast_ofNat] at ⊢
    rw [hexp, Real.rpow_zero]

/-- Both signs of the oracle bump produce exactly the same treatment records.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input b](hyp:b), [the specified input hb](hyp:hb), [the specified input hbs](hyp:hbs), [the oracle bump common auxiliary conclusion](goal) holds. -/
lemma oracle_bump_common_auxiliary (d : ℕ) (h b : ℝ)
    (hb : 0 ≤ b) (hbs : b ≤ 1/8) :
    xaLaw (oracleBumpPrimitive d h b false) = xaLaw (oracleBumpPrimitive d h b true) := by
  have he0 := (oracleBumpPrimitive_margins d h b false hb hbs).1
  have he1 := (oracleBumpPrimitive_margins d h b true hb hbs).1
  have hu (theta : Bool) : UniformDesign (oracleBumpPrimitive d h b theta) :=
    independentFullLaw_covariates d _ _ _ measurable_const measurable_const (by fun_prop)
  unfold xaLaw
  rw [(oracleBumpPrimitive d h b false).margin_e,
    (oracleBumpPrimitive d h b true).margin_e, hu false, hu true]
  congr 1

/-- A common auxiliary channel and randomizer contribute no information to a
pair of primitive laws; only the labeled-record product remains.  Given [the specified input d](hyp:d), [the specified input P](hyp:P), [the specified input Q](hyp:Q), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input haux](hyp:haux), [the oracle experiment hellinger le conclusion](goal) holds. -/
lemma oracle_experiment_hellinger_le {d : ℕ} (P Q : PrimitiveLaw d) (n m : ℕ)
    (haux : xaLaw P = xaLaw Q) :
    hellingerSq (experiment P n m) (experiment Q n m) ≤
      (n:ℝ)*hellingerSq (obsLaw P) (obsLaw Q) := by
  letI := obsLaw_probability P
  letI := obsLaw_probability Q
  letI := xaLaw_probability P
  letI := population_randomizer_probability
  unfold experiment
  rw [← haux, hellingerSq_prod_probability, hellingerSq_prod_probability]
  simpa using hellingerSq_pi_le_sum
    (fun _ : Fin n => obsLaw P) (fun _ : Fin n => obsLaw Q)

/-- The full randomized oracle bump experiment has the paper's fixed-size
information bound, uniformly in the auxiliary sample size.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input b](hyp:b), [the specified input hh](hyp:hh), [the specified input hh1](hyp:hh1), [the specified input hb](hyp:hb), [the specified input hbs](hyp:hbs), [the oracle bump block hellinger conclusion](goal) holds. -/
lemma oracle_bump_block_hellinger (d n m : ℕ) (h b : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hb : 0 ≤ b) (hbs : b ≤ 1/8) :
    hellingerSq (experiment (oracleBumpPrimitive d h b false) n m)
      (experiment (oracleBumpPrimitive d h b true) n m) ≤
      16*(n:ℝ)*b^2*h^d := by
  calc
    _ ≤ (n:ℝ)*hellingerSq (obsLaw (oracleBumpPrimitive d h b false))
        (obsLaw (oracleBumpPrimitive d h b true)) :=
      oracle_experiment_hellinger_le _ _ n m (oracle_bump_common_auxiliary d h b hb hbs)
    _ ≤ (n:ℝ)*(16*b^2*h^d) := mul_le_mul_of_nonneg_left
      (oracle_bump_hellinger_bound d h b hh hh1 hb hbs) (Nat.cast_nonneg n)
    _ = _ := by ring

/-- At the oracle bandwidth, the full-block information is bounded by sixteen
 times the squared public bump amplitude.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input gamma](hyp:gamma), [the specified input eta](hyp:eta), [the specified input hg](hyp:hg), [the specified input hn](hyp:hn), [the specified input heta](hyp:heta), [the specified input hetas](hyp:hetas), [the oracle bump information at rate conclusion](goal) holds. -/
lemma oracle_bump_information_at_rate (d n m : ℕ) (gamma eta : ℝ)
    (hg : 0 < gamma) (hn : 2 ≤ n) (heta : 0 ≤ eta) (hetas : eta ≤ 1/8) :
    let H := (n:ℝ)^(-(1/(2*gamma+d)))
    let b := eta*oracleRate d gamma n
    hellingerSq (experiment (oracleBumpPrimitive d H b false) n m)
      (experiment (oracleBumpPrimitive d H b true) n m) ≤ 16*eta^2 := by
  dsimp only
  obtain ⟨hH, hH1, hrate, hinfo⟩ := oracle_bandwidth_identities d n gamma hg hn
  have hr0 : 0 ≤ oracleRate d gamma n := by unfold oracleRate; positivity
  have hr1 : oracleRate d gamma n ≤ 1 := by
    rw [← hrate]
    exact Real.rpow_le_one hH.le hH1 hg.le
  have hb0 : 0 ≤ eta*oracleRate d gamma n := mul_nonneg heta hr0
  have hb1 : eta*oracleRate d gamma n ≤ 1/8 :=
    (mul_le_mul_of_nonneg_left hr1 heta).trans (by simpa using hetas)
  apply (oracle_bump_block_hellinger d n m _ _ hH hH1 hb0 hb1).trans_eq
  calc
    _ = 16*eta^2*((n:ℝ)*(oracleRate d gamma n)^2*
        ((n:ℝ)^(-(1/(2*gamma+d))))^d) := by ring
    _ = 16*eta^2 := by rw [hinfo, mul_one]

/-- A single public amplitude makes the explicit bump laws admissible for every
sample size and leaves the full experiment inside the testing budget.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the oracle bump testing family conclusion](goal) holds. -/
lemma oracle_bump_testing_family (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1/16 ∧ ∀ (n : ℕ), 2 ≤ n →
      let H := (n:ℝ)^(-(1/(2*gamma+d)))
      let bn := eta*oracleRate d gamma n
      (∀ theta, ∃ hP : PrimitiveClass alpha beta gamma L eps
          (oracleBumpPrimitive d H bn theta),
        ∀ x ∈ cube d, designatedPropensity _ hP x = 1/2 ∧
          designatedControl _ hP x = 1/2 ∧
          tau _ hP x = thetaSign theta*bn*macroBump H x) ∧
      (∀ m, hellingerSq (experiment (oracleBumpPrimitive d H bn false) n m)
        (experiment (oracleBumpPrimitive d H bn true) n m) ≤ 1/16) := by
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hL : 1/2 ≤ L := hdom.2.2.2.2.2.2.2.1.le
  have heps : 0 < eps := hdom.2.2.2.2.2.2.2.2.1
  have heps' : eps ≤ 1/2 := hdom.2.2.2.2.2.2.2.2.2.le
  obtain ⟨D, hD, hprofile⟩ := oracle_macro_holder d gamma hg
  let eta := (128*(D+1))⁻¹
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetaD : eta*(D+1) = 1/128 := by dsimp [eta]; field_simp
  have hetasmall : eta ≤ 1/8 := by nlinarith
  have hDeta : eta*D ≤ L := by nlinarith
  have hetatest : eta ≤ 1/16 := by nlinarith
  refine ⟨eta, heta, hetatest, ?_⟩
  intro n hn
  let H : ℝ := (n:ℝ)^(-(1/(2*gamma+d)))
  let bn : ℝ := eta*oracleRate d gamma n
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hden : 0 < 2*gamma+(d:ℝ) := by positivity
  have hH : 0 < H := Real.rpow_pos_of_pos hn0 _
  have hH1 : H ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (one_div_nonneg.mpr hden.le))
  have hrate : H^gamma = oracleRate d gamma n := by
    dsimp only [H, oracleRate]
    rw [← Real.rpow_mul hn0.le]
    congr 1
    ring
  have hbn : 0 < bn := by dsimp [bn, oracleRate]; positivity
  have hbsmall : bn ≤ 1/8 := by
    dsimp only [bn]
    rw [← hrate]
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_one hH.le hH1 hg.le) heta.le).trans
      (by simpa using hetasmall)
  have hsmooth : holderNorm (fun x : Cov d => bn*macroBump H x) gamma ≤ ENNReal.ofReal L := by
    have hs := holderNorm_const_mul_bound (macroBump (d:=d) H) gamma (D*H^(-gamma)) bn
      (by positivity) (hprofile H hH hH1)
    rw [abs_of_pos hbn] at hs
    have hid : bn*(D*H^(-gamma)) = eta*D := by
      dsimp only [bn]
      rw [← hrate]
      calc
        eta*H^gamma*(D*H^(-gamma)) = eta*D*(H^gamma*H^(-gamma)) := by ring
        _ = eta*D := by rw [← Real.rpow_add hH, add_neg_cancel, Real.rpow_zero, mul_one]
    rw [hid] at hs
    exact hs.trans (ENNReal.ofReal_le_ofReal hDeta)
  constructor
  · intro theta
    exact oracleBumpPrimitive_membership d alpha beta gamma L eps H bn
      hL heps heps' hbn.le hbsmall hsmooth theta
  · intro m
    apply (oracle_bump_information_at_rate d n m gamma eta hg hn heta.le hetasmall).trans
    have hsq : eta^2 ≤ (1/16:ℝ)^2 := pow_le_pow_left₀ heta.le hetatest 2
    nlinarith

/-- The target of an oracle bump is identified by its full experiment law.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input h](hyp:h), [the specified input b](hyp:b), [the specified input hn](hyp:hn), [the specified input hMembers](hyp:hMembers), [the specified input theta](hyp:theta), [the specified input theta'](hyp:theta'), [the specified input hE](hyp:hE), [the oracle bump target eq of experiment conclusion](goal) holds. -/
lemma oracle_bump_target_eq_of_experiment {d n m : ℕ} {alpha beta gamma L eps h b : ℝ}
    (hn : 0 < n)
    (hMembers : ∀ theta, PrimitiveClass alpha beta gamma L eps (oracleBumpPrimitive d h b theta))
    (theta theta' : Bool)
    (hE : experiment (oracleBumpPrimitive d h b theta) n m =
      experiment (oracleBumpPrimitive d h b theta') n m) :
    tau _ (hMembers theta) (x0 d) = tau _ (hMembers theta') (x0 d) := by
  have ho := congrArg (fun μ : Measure (Sample d n m) =>
    μ.map (fun w => w.1.1 (⟨0, hn⟩ : Fin n))) hE
  rw [experiment_map_labeled, experiment_map_labeled] at ho
  have hl := independent_fullLaw_eq_of_obsLaw _ _ _ _ _ _
    measurable_const measurable_const (by fun_prop)
    measurable_const measurable_const (by fun_prop) (hMembers theta) ho
  have hu := admissible_versions_unique _ _ (hMembers theta) (hMembers theta') hl
  exact (hu (x0 d) (by intro i; norm_num [x0, cube])).2.2.2

/-- The two oracle targets extend to a functional of the full-block law, as
required by the cited testing theorem.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input h](hyp:h), [the specified input b](hyp:b), [the specified input hn](hyp:hn), [the specified input hMembers](hyp:hMembers), [the oracle bump experiment target exists conclusion](goal) holds. -/
lemma oracle_bump_experiment_target_exists {d n m : ℕ} {alpha beta gamma L eps h b : ℝ}
    (hn : 0 < n)
    (hMembers : ∀ theta, PrimitiveClass alpha beta gamma L eps (oracleBumpPrimitive d h b theta)) :
    ∃ Ψ : Measure (Sample d n m) → ℝ, ∀ theta,
      Ψ (experiment (oracleBumpPrimitive d h b theta) n m) =
        tau _ (hMembers theta) (x0 d) := by
  exact exists_function_on_image
    (fun theta => experiment (oracleBumpPrimitive d h b theta) n m)
    (fun theta => tau _ (hMembers theta) (x0 d))
    (fun theta theta' hE => oracle_bump_target_eq_of_experiment hn hMembers theta theta' hE)

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

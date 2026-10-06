module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.RateAlgebra
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.T_MarkedComponentCertificate

/-!
# Scales for the nuisance-frontier converse

The prescribed bandwidth, cell side and nuisance amplitudes satisfy the
geometric, occupancy and information identities in the converse roadmap.
These identities retain both sample channels and both nuisance amplitudes.
-/

public section

noncomputable section
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Below the frontier cutoff, the sum of nuisance orders is below the effect order.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input hS](hyp:hS), [the nuisance order lt gamma conclusion](goal) holds. -/
lemma nuisance_order_lt_gamma (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps)
    (hS : alpha+beta < sCrit d gamma) : alpha+beta < gamma := by
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hA : 0 < 2*gamma+(d:ℝ) := by positivity
  apply hS.trans
  dsimp [sCrit]
  apply (div_lt_iff₀ hA).mpr
  nlinarith

/-- The two lower-bound scales are positive, nested and in the localization domain.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input hS](hyp:hS), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the specified input ch](hyp:ch), [the specified input cd](hyp:cd), [the specified input hch](hyp:hch), [the specified input hch'](hyp:hch'), [the specified input hcd](hyp:hcd), [the specified input hcd'](hyp:hcd'), [the nuisance scales admissible conclusion](goal) holds. -/
lemma nuisance_scales_admissible (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps)
    (hS : alpha+beta < sCrit d gamma) (n m : ℕ) (hn : 2 ≤ n)
    (ch cd : ℝ) (hch : 0 < ch) (hch' : ch ≤ 1/2)
    (hcd : 0 < cd) (hcd' : cd ≤ ch) :
    let h := ch*((n:ℝ)*((n:ℝ)+m))^(-(1/bigDelta d alpha beta gamma))
    let delta := cd*((n:ℝ)*((n:ℝ)+m))^(-(gamma/((alpha+beta)*bigDelta d alpha beta gamma)))
    0 < delta ∧ delta ≤ h ∧ h ≤ 1/2 := by
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hS0 : 0 < alpha+beta := add_pos hdom.2.1 hdom.2.2.2.1
  have hD : 0 < bigDelta d alpha beta gamma := by dsimp [bigDelta]; positivity
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hN1 : (1:ℝ) ≤ (n:ℝ)+m := hn1.trans (le_add_of_nonneg_right (Nat.cast_nonneg m))
  have hx1 : (1:ℝ) ≤ (n:ℝ)*((n:ℝ)+m) := by nlinarith
  have hx : 0 < (n:ℝ)*((n:ℝ)+m) := zero_lt_one.trans_le hx1
  have he : -(gamma/((alpha+beta)*bigDelta d alpha beta gamma)) ≤
      -(1/bigDelta d alpha beta gamma) := by
    apply neg_le_neg
    apply (div_le_div_iff₀ hD (mul_pos hS0 hD)).mpr
    have hs := (nuisance_order_lt_gamma d alpha beta gamma L eps hdom hS).le
    nlinarith
  refine ⟨mul_pos hcd (Real.rpow_pos_of_pos hx _), ?_, ?_⟩
  · exact mul_le_mul hcd' (Real.rpow_le_rpow_of_exponent_le hx1 he)
      (Real.rpow_pos_of_pos hx _).le hch.le
  · have hp : ((n:ℝ)*((n:ℝ)+m))^(-(1/bigDelta d alpha beta gamma)) ≤ 1 := by
      simpa using (Real.rpow_le_rpow_of_exponent_le hx1
        (show -(1/bigDelta d alpha beta gamma) ≤ 0 from neg_nonpos.mpr (by positivity)))
    calc
      _ ≤ ch*1 := mul_le_mul_of_nonneg_left hp hch.le
      _ ≤ 1/2 := by simpa using hch'

/-- The cell occupancy is the public constant times a power of the count-boundary ratio.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input n](hyp:n), [the specified input N](hyp:N), [the specified input cd](hyp:cd), [the specified input hn](hyp:hn), [the specified input hN](hyp:hN), [the specified input hcd](hyp:hcd), [the nuisance occupancy identity conclusion](goal) holds. -/
lemma nuisance_occupancy_identity (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (n N cd : ℝ)
    (hn : 0 < n) (hN : 0 < N) (hcd : 0 < cd) :
    N*(cd*(n*N)^(-(gamma/((alpha+beta)*bigDelta d alpha beta gamma))))^d =
      cd^d*(N/n^qStar d alpha beta gamma)^(1/(1+qStar d alpha beta gamma)) := by
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hS : 0 < alpha+beta := add_pos hdom.2.1 hdom.2.2.2.1
  have hA : 0 < 2*gamma+(d:ℝ) := by positivity
  have hq : 0 ≤ qStar d alpha beta gamma := by dsimp [qStar]; positivity
  have hq1 : 0 < 1+qStar d alpha beta gamma := by positivity
  have he : gamma*(d:ℝ)/((alpha+beta)*bigDelta d alpha beta gamma) =
      qStar d alpha beta gamma/(1+qStar d alpha beta gamma) := by
    rw [(rate_exponent_identities d alpha beta gamma L eps hdom).2]
    dsimp [qStar]
    field_simp
  apply Real.log_injOn_pos (by change (0:ℝ) < _; positivity) (by change (0:ℝ) < _; positivity)
  simp only [← Real.rpow_natCast]
  rw [Real.log_mul hN.ne' (by positivity), Real.log_rpow (by positivity),
    Real.log_mul hcd.ne' (by positivity), Real.log_rpow (mul_pos hn hN),
    Real.log_mul hn.ne' hN.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hcd, Real.log_rpow (by positivity),
    Real.log_div hN.ne' (by positivity), Real.log_rpow hn]
  have he' : (d:ℝ)*(-(gamma/((alpha+beta)*bigDelta d alpha beta gamma))) =
      -(qStar d alpha beta gamma/(1+qStar d alpha beta gamma)) := by
    rw [← he]; ring
  rw [mul_add, ← mul_assoc, he']
  field_simp
  ring

/-- In the sparse range the cell occupancy never exceeds the public cell constant.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input n](hyp:n), [the specified input N](hyp:N), [the specified input cd](hyp:cd), [the specified input hn](hyp:hn), [the specified input hN](hyp:hN), [the specified input hcd](hyp:hcd), [the specified input hboundary](hyp:hboundary), [the nuisance occupancy bound conclusion](goal) holds. -/
lemma nuisance_occupancy_bound (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (n N cd : ℝ)
    (hn : 0 < n) (hN : 0 < N) (hcd : 0 < cd)
    (hboundary : N ≤ n^qStar d alpha beta gamma) :
    N*(cd*(n*N)^(-(gamma/((alpha+beta)*bigDelta d alpha beta gamma))))^d ≤ cd^d := by
  rw [nuisance_occupancy_identity d alpha beta gamma L eps hdom n N cd hn hN hcd]
  have hq : 0 ≤ qStar d alpha beta gamma := by
    have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
    have hS : 0 < alpha+beta := add_pos hdom.2.1 hdom.2.2.2.1
    dsimp [qStar]; positivity
  have hr : N/n^qStar d alpha beta gamma ≤ 1 :=
    (div_le_one (Real.rpow_pos_of_pos hn _)).mpr hboundary
  have hp : (N/n^qStar d alpha beta gamma)^(1/(1+qStar d alpha beta gamma)) ≤ 1 := by
    simpa using Real.rpow_le_rpow (by positivity) hr
      (show 0 ≤ 1/(1+qStar d alpha beta gamma) by positivity)
  simpa using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ cd^d)

/-- The product of the two prescribed amplitudes has exactly the converse rate.  Given [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input D](hyp:D), [the specified input x](hyp:x), [the specified input cd](hyp:cd), [the specified input rho](hyp:rho), [the specified input hS](hyp:hS), [the specified input hD](hyp:hD), [the specified input hx](hyp:hx), [the specified input hcd](hyp:hcd), [the nuisance amplitude product conclusion](goal) holds. -/
lemma nuisance_amplitude_product (alpha beta gamma D x cd rho : ℝ)
    (hS : 0 < alpha+beta) (hD : 0 < D) (hx : 0 < x) (hcd : 0 < cd) :
    (rho*(cd*x^(-(gamma/((alpha+beta)*D))))^alpha)*
      (rho*(cd*x^(-(gamma/((alpha+beta)*D))))^beta) =
      rho^2*cd^(alpha+beta)*x^(-(gamma/D)) := by
  rw [mul_mul_mul_comm, ← pow_two, ← Real.rpow_add (by positivity),
    Real.mul_rpow hcd.le (Real.rpow_pos_of_pos hx _).le,
    ← Real.rpow_mul hx.le]
  have he : -(gamma/((alpha+beta)*D))*(alpha+beta) = -(gamma/D) := by field_simp
  rw [he]
  ring

/-- Both channels and both nuisance orders cancel in the information monomial.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input x](hyp:x), [the specified input ch](hyp:ch), [the specified input cd](hyp:cd), [the specified input hx](hyp:hx), [the specified input hch](hyp:hch), [the specified input hcd](hyp:hcd), [the nuisance information monomial conclusion](goal) holds. -/
lemma nuisance_information_monomial (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (x ch cd : ℝ)
    (hx : 0 < x) (hch : 0 < ch) (hcd : 0 < cd) :
    x*(ch*x^(-(1/bigDelta d alpha beta gamma)))^d*
      (cd*x^(-(gamma/((alpha+beta)*bigDelta d alpha beta gamma))))^((d:ℝ)+2*(alpha+beta)) =
      ch^d*cd^((d:ℝ)+2*(alpha+beta)) := by
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hS : 0 < alpha+beta := add_pos hdom.2.1 hdom.2.2.2.1
  have hD : 0 < bigDelta d alpha beta gamma := by dsimp [bigDelta]; positivity
  apply Real.log_injOn_pos (by change (0:ℝ) < _; positivity) (by change (0:ℝ) < _; positivity)
  simp only [← Real.rpow_natCast]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hx.ne' (by positivity),
    Real.log_rpow (by positivity), Real.log_mul hch.ne' (by positivity),
    Real.log_rpow hx, Real.log_rpow (by positivity),
    Real.log_mul hcd.ne' (by positivity), Real.log_rpow hx,
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hch, Real.log_rpow hcd]
  have he : 1+(d:ℝ)*(-(1/bigDelta d alpha beta gamma))+
      ((d:ℝ)+2*(alpha+beta))*(-(gamma/((alpha+beta)*bigDelta d alpha beta gamma))) = 0 := by
    dsimp [bigDelta]
    field_simp
    ring
  linear_combination (Real.log x)*he

/-- Raising the bandwidth to the effect order gives exactly its prescribed power.  Given [the specified input gamma](hyp:gamma), [the specified input D](hyp:D), [the specified input x](hyp:x), [the specified input ch](hyp:ch), [the specified input hx](hyp:hx), [the specified input hch](hyp:hch), [the nuisance bandwidth bias identity conclusion](goal) holds. -/
lemma nuisance_bandwidth_bias_identity (gamma D x ch : ℝ)
    (hx : 0 < x) (hch : 0 < ch) :
    (ch*x^(-(1/D)))^gamma = ch^gamma*x^(-(gamma/D)) := by
  rw [Real.mul_rpow hch.le (Real.rpow_pos_of_pos hx _).le, ← Real.rpow_mul hx.le]
  congr 2
  ring

/-- The actual rectangular information term equals the constant monomial after scaling.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input x](hyp:x), [the specified input ch](hyp:ch), [the specified input cd](hyp:cd), [the specified input rho](hyp:rho), [the specified input hx](hyp:hx), [the specified input hch](hyp:hch), [the specified input hcd](hyp:hcd), [the nuisance scaled information identity conclusion](goal) holds. -/
lemma nuisance_scaled_information_identity (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) (x ch cd rho : ℝ)
    (hx : 0 < x) (hch : 0 < ch) (hcd : 0 < cd) :
    let h := ch*x^(-(1/bigDelta d alpha beta gamma))
    let delta := cd*x^(-(gamma/((alpha+beta)*bigDelta d alpha beta gamma)))
    x*h^d*delta^d*(rho*delta^alpha)^2*(rho*delta^beta)^2 =
      rho^4*ch^d*cd^((d:ℝ)+2*(alpha+beta)) := by
  dsimp only
  let delta := cd*x^(-(gamma/((alpha+beta)*bigDelta d alpha beta gamma)))
  have hd : 0 < delta := by dsimp [delta]; positivity
  have he : delta^d*(rho*delta^alpha)^2*(rho*delta^beta)^2 =
      rho^4*delta^((d:ℝ)+2*(alpha+beta)) := by
    rw [Real.rpow_add hd, Real.rpow_natCast,
      show 2*(alpha+beta) = (alpha+beta)*2 by ring,
      Real.rpow_mul hd.le, Real.rpow_two, Real.rpow_add hd]
    ring
  calc
    _ = rho^4*(x*(ch*x^(-(1/bigDelta d alpha beta gamma)))^d*
        delta^((d:ℝ)+2*(alpha+beta))) := by
      calc
        _ = x*(ch*x^(-(1/bigDelta d alpha beta gamma)))^d*
            (delta^d*(rho*delta^alpha)^2*(rho*delta^beta)^2) := by ring
        _ = _ := by rw [he]; ring
    _ = _ := by rw [nuisance_information_monomial d alpha beta gamma L eps hdom x ch cd hx hch hcd]; ring

/-- A single choice of public constants gives admissible marked priors with the
converse-rate separation and small Hellinger distance throughout the sparse range.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input hS](hyp:hS), [the nuisance scaled marked priors conclusion](goal) holds. -/
lemma nuisance_scaled_marked_priors (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps)
    (hS : alpha+beta < sCrit d gamma) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ (n m : ℕ), 2 ≤ n →
      (n:ℝ)+m ≤ (n:ℝ)^qStar d alpha beta gamma →
      ∃ h delta a b : ℝ, 0 < delta ∧ delta ≤ h ∧ h ≤ 1/2 ∧ 0 < a ∧ 0 < b ∧
        a*b = kappa*((n:ℝ)*((n:ℝ)+m))^(-(gamma/bigDelta d alpha beta gamma)) ∧
        ∃ hMembers : ∀ theta sigma,
          PrimitiveClass alpha beta gamma L eps ((markedHandle d h delta a b).law theta sigma),
          (∀ sigma,
            tau ((markedHandle d h delta a b).law false sigma) (hMembers false sigma) (x0 d) = 2*a*b ∧
            tau ((markedHandle d h delta a b).law true sigma) (hMembers true sigma) (x0 d) = -2*a*b) ∧
          hellingerSq (markedMixture (markedHandle d h delta a b) true n m)
            (markedMixture (markedHandle d h delta a b) false n m) ≤ 1/16 := by
  obtain ⟨c, c0, C, hc, hc1, hc0, hC, hcert⟩ :=
    marked_component_certificate d alpha beta gamma L eps hdom
  have hg : 0 < gamma := lt_of_lt_of_le zero_lt_one hdom.2.2.2.2.2.1
  have hS0 : 0 < alpha+beta := add_pos hdom.2.1 hdom.2.2.2.1
  have hD : 0 < bigDelta d alpha beta gamma := by dsimp [bigDelta]; positivity
  let ch : ℝ := 1/4
  let cd : ℝ := min ch c0
  let rho : ℝ := min c (min 1 (min (c*ch^gamma) (1/(16*C))))
  have hch : 0 < ch := by norm_num [ch]
  have hch1 : ch ≤ 1 := by norm_num [ch]
  have hchhalf : ch ≤ 1/2 := by norm_num [ch]
  have hcd : 0 < cd := lt_min hch hc0
  have hcdch : cd ≤ ch := min_le_left _ _
  have hcd1 : cd ≤ 1 := hcdch.trans hch1
  have hcdc0 : cd ≤ c0 := min_le_right _ _
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrhoc : rho ≤ c := min_le_left _ _
  have hrho1 : rho ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrhob : rho ≤ c*ch^gamma :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrhoC : rho ≤ 1/(16*C) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hrho2 : rho^2 ≤ rho := by nlinarith
  have hrho4 : rho^4 ≤ rho := by
    rw [← Real.rpow_natCast rho 4]
    simpa using
      Real.rpow_le_rpow_of_exponent_ge hrho hrho1 (by norm_num : (1:ℝ) ≤ (4:ℝ))
  have hcdpow : cd^d ≤ c0 := by
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hdom.1
    have hp := Real.rpow_le_rpow_of_exponent_ge hcd hcd1 hd1
    have hp' : cd^d ≤ cd := by simpa only [Real.rpow_natCast, Real.rpow_one] using hp
    exact hp'.trans hcdc0
  have hcdS : cd^(alpha+beta) ≤ 1 := Real.rpow_le_one hcd.le hcd1 hS0.le
  have hchd : ch^d ≤ 1 := by exact_mod_cast (pow_le_one₀ hch.le hch1)
  have hcdinfo : cd^((d:ℝ)+2*(alpha+beta)) ≤ 1 :=
    Real.rpow_le_one hcd.le hcd1 (by positivity)
  have hconstant : C*(rho^4*ch^d*cd^((d:ℝ)+2*(alpha+beta))) ≤ 1/16 := by
    calc
      _ ≤ C*rho := by
        gcongr
        calc
          rho^4*ch^d*cd^((d:ℝ)+2*(alpha+beta)) ≤ rho^4*1*1 := by gcongr
          _ ≤ rho := by simpa using hrho4
      _ ≤ C*(1/(16*C)) := mul_le_mul_of_nonneg_left hrhoC hC.le
      _ = 1/16 := by field_simp
  refine ⟨rho^2*cd^(alpha+beta), by positivity, ?_⟩
  intro n m hn hboundary
  let x : ℝ := (n:ℝ)*((n:ℝ)+m)
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNpos : (0:ℝ) < (n:ℝ)+m := by positivity
  have hx : 0 < x := mul_pos hnpos hNpos
  let h := ch*x^(-(1/bigDelta d alpha beta gamma))
  let delta := cd*x^(-(gamma/((alpha+beta)*bigDelta d alpha beta gamma)))
  let a := rho*delta^alpha
  let b := rho*delta^beta
  have hs := nuisance_scales_admissible d alpha beta gamma L eps hdom hS n m hn ch cd hch hchhalf hcd hcdch
  have hd : 0 < delta := hs.1
  have ha : 0 < a := mul_pos hrho (Real.rpow_pos_of_pos hd _)
  have hb : 0 < b := mul_pos hrho (Real.rpow_pos_of_pos hd _)
  have hprod : a*b = rho^2*cd^(alpha+beta)*x^(-(gamma/bigDelta d alpha beta gamma)) :=
    nuisance_amplitude_product alpha beta gamma _ x cd rho hS0 hD hx hcd
  have hab : a*b ≤ c*h^gamma := by
    rw [hprod, nuisance_bandwidth_bias_identity gamma _ x ch hx hch]
    calc
      _ ≤ (rho*1)*x^(-(gamma/bigDelta d alpha beta gamma)) := by gcongr
      _ ≤ (c*ch^gamma)*x^(-(gamma/bigDelta d alpha beta gamma)) :=
        mul_le_mul_of_nonneg_right (by simpa using hrhob) (Real.rpow_pos_of_pos hx _).le
      _ = _ := by ring
  have hocc : ((n:ℝ)+m)*delta^d ≤ c0 :=
    (nuisance_occupancy_bound d alpha beta gamma L eps hdom (n:ℝ) ((n:ℝ)+m) cd hnpos hNpos hcd hboundary).trans hcdpow
  have hac : a ≤ c*delta^alpha := mul_le_mul_of_nonneg_right hrhoc (by positivity)
  have hbc : b ≤ c*delta^beta := mul_le_mul_of_nonneg_right hrhoc (by positivity)
  rcases hcert n m h delta a b hn hd hs.2.1 hs.2.2 ha hac hb hbc hab hocc with
    ⟨_, ⟨hMembers, hcontrast, _⟩, htarget, _, hhell, _⟩
  refine ⟨h, delta, a, b, hd, hs.2.1, hs.2.2, ha, hb, hprod, hMembers, ?_, ?_⟩
  · intro sigma
    constructor
    · rw [hcontrast false sigma _ (by intro i; norm_num [x0, cube]), htarget false]
      norm_num [thetaSign]
    · rw [hcontrast true sigma _ (by intro i; norm_num [x0, cube]), htarget true]
      norm_num [thetaSign]
  · apply hhell.trans
    rw [show C*(n:ℝ)*((n:ℝ)+m)*h^d*delta^d*a^2*b^2 =
      C*(x*h^d*delta^d*a^2*b^2) by dsimp [x]; ring]
    rw [nuisance_scaled_information_identity d alpha beta gamma L eps hdom x ch cd rho hx hch hcd]
    exact hconstant

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

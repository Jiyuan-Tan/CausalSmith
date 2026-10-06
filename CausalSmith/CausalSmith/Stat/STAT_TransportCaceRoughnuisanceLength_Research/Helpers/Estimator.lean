module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Four-block marked histogram score and affine inversion -/

@[expose] public section
set_option linter.style.longLine false

open MeasureTheory Set
open scoped BigOperators

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

-- @env: S3
variable (n : ℕ)
/-- [The block idx object](goal) is defined from [the supplied inputs](hyp:n,b). -/
def blockIdx (n : ℕ) (b : Fin 4) : Finset (Fin n) := -- @realizes \mathcal B_b^G(exact deterministic block)
  Finset.univ.filter (fun i => b.val * n / 4 ≤ i.val ∧
    i.val < (b.val + 1) * n / 4)
/-- [The block size object](goal) is defined from [the supplied inputs](hyp:n,b). -/
def blockSize (n : ℕ) (b : Fin 4) : ℕ :=
  (b.val + 1) * n / 4 - b.val * n / 4 -- @realizes m_b(exact block size)
/-- [The dyadic resolution object](goal) is defined from [the supplied inputs](hyp:n,power). -/

noncomputable def dyadicResolution (n : ℕ) (power : ℝ) : ℕ :=
  if n < threshold then 1 else
    2 ^ Nat.floor (power * (Real.log (blockSize n 0 : ℝ) / Real.log 2))
/-- [The pilot resolution object](goal) is defined from [the supplied inputs](hyp:n). -/
noncomputable def pilotResolution (n : ℕ) : ℕ :=
  dyadicResolution n (4 / 5) -- @realizes K_0(pilot resolution)
/-- [The quadratic resolution object](goal) is defined from [the supplied inputs](hyp:n). -/
noncomputable def quadraticResolution (n : ℕ) : ℕ :=
  dyadicResolution n (4 / 3) -- @realizes K_2(quadratic resolution)
/-- [The cubic resolution object](goal) is defined from [the supplied inputs](hyp:n). -/
noncomputable def cubicResolution (n : ℕ) : ℕ :=
  dyadicResolution n 1 -- @realizes K_3(cubic resolution)
/-- [The cell object](goal) is defined from [the supplied inputs](hyp:K). -/

noncomputable def cell (K : ℕ) (ℓ : Fin K) : Set ℝ := -- @realizes I_{\ell,K}(last cell closed at one)
  if ℓ.val + 1 = K then
    Icc ((ℓ.val : ℝ) / K) 1
  else Ico ((ℓ.val : ℝ) / K) (((ℓ.val : ℝ) + 1) / K)
/-- [The midpoint object](goal) is defined from [the supplied inputs](hyp:K). -/
noncomputable def midpoint (K : ℕ) (ℓ : Fin K) : ℝ :=
  ((ℓ.val : ℝ) + 1 / 2) / K
/-- [The source channel object](goal) is defined from [the supplied inputs](hyp:i). -/

def sourceChannel (i : Fin 7) : Bool := i.val ≠ 0
  -- @realizes g(i)(target at coordinate zero; source otherwise)
/-- [The channel x object](goal) is defined from [the supplied inputs](hyp:n,i,r). -/
def channelX {n : ℕ} (ω : TwoSample n n) (i : Fin 7) (r : Fin n) : ℝ :=
  if sourceChannel i then (ω.1 r).1 else ω.2 r
/-- [The channel mark object](goal) is defined from [the supplied inputs](hyp:n,i,r). -/
def channelMark {n : ℕ} (ω : TwoSample n n) (i : Fin 7) (r : Fin n) : ℝ :=
  if i.val = 0 then 1 else
  if i.val = 1 then boolReal (!(ω.1 r).2.1) else
  if i.val = 2 then boolReal (ω.1 r).2.1 else
  if i.val = 3 then boolReal (!(ω.1 r).2.1) *
    max 0 (min 1 (ω.1 r).2.2.2) else
  if i.val = 4 then boolReal (ω.1 r).2.1 *
    max 0 (min 1 (ω.1 r).2.2.2) else
  if i.val = 5 then boolReal (!(ω.1 r).2.1) * boolReal (ω.1 r).2.2.1 else
    boolReal (ω.1 r).2.1 * boolReal (ω.1 r).2.2.1
  -- @realizes W_i(bounded source or target mark)
/-- [The marked histogram object](goal) is defined from [the supplied inputs](hyp:n,i,K,b,x). -/

noncomputable def markedHistogram {n : ℕ} (ω : TwoSample n n)
    (i : Fin 7) (K : ℕ) (b : Fin 4) (x : ℝ) : ℝ := by
  classical
  exact if n < threshold then 0 else
    ∑ ℓ : Fin K, if x ∈ cell K ℓ then
      (K : ℝ) / blockSize n b *
        ∑ r ∈ blockIdx n b,
          channelMark ω i r * if channelX ω i r ∈ cell K ℓ then 1 else 0
      else 0
  -- @realizes H_{i,K}^{(b)}(normalized marked histogram)
/-- [The clip object](goal) is defined from [the supplied inputs](hyp:lo,hi,x). -/

def clip (lo hi x : ℝ) : ℝ := max lo (min hi x)
/-- [The clip channel object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,i,x). -/
noncomputable def clipChannel (c_f C_f : ℝ) (i : Fin 7) (x : ℝ) : ℝ :=
  if i.val = 0 then clip c_f C_f x else
  if i.val = 1 || i.val = 2 then clip (c_f / 4) (3 * C_f / 4) x else
    clip 0 (3 * C_f / 4) x
/-- [The pilot object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,n,x). -/

noncomputable def pilot (c_f C_f : ℝ) {n : ℕ}
    (ω : TwoSample n n) (x : ℝ) : Fin 7 → ℝ :=
  if n < threshold then ![1, 1 / 2, 1 / 2, 0, 0, 0, 0] else
    fun i => clipChannel c_f C_f i
      (markedHistogram ω i (pilotResolution n) 0 x)
  -- @realizes \widehat F(clipped pilot)
/-- [The residual object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,n,i,K,b,x). -/

noncomputable def residual (c_f C_f : ℝ) {n : ℕ}
    (ω : TwoSample n n) (i : Fin 7) (K : ℕ) (b : Fin 4) (x : ℝ) : ℝ :=
  markedHistogram ω i K b x - pilot c_f C_f ω x i
  -- @realizes R_{i,K}^{(b)}(independent-block residual)
/-- [The basis object](goal) is defined from [the supplied inputs](hyp:i). -/

def basis (i : Fin 7) : Fin 7 → ℝ := fun j => if j = i then 1 else 0
/-- [The d phi1 object](goal) is defined from [the supplied inputs](hyp:A,v,i). -/
noncomputable def dPhi1 (A : Bool) (v : Fin 7 → ℝ) (i : Fin 7) : ℝ :=
  fderiv ℝ (Phi A) v (basis i)
/-- [The d phi2 object](goal) is defined from [the supplied inputs](hyp:A,v,i,j). -/
noncomputable def dPhi2 (A : Bool) (v : Fin 7 → ℝ)
    (i j : Fin 7) : ℝ :=
  iteratedFDeriv ℝ 2 (Phi A) v ![basis i, basis j]
/-- [The d phi3 object](goal) is defined from [the supplied inputs](hyp:A,v,i,j,k). -/
noncomputable def dPhi3 (A : Bool) (v : Fin 7 → ℝ)
    (i j k : Fin 7) : ℝ :=
  iteratedFDeriv ℝ 3 (Phi A) v ![basis i, basis j, basis k]
/-- [The pilot integral object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,n,A). -/

noncomputable def pilotIntegral (c_f C_f : ℝ) {n : ℕ}
    (ω : TwoSample n n) (A : Bool) : ℝ :=
  ∫ x in (0 : ℝ)..1, Phi A (pilot c_f C_f ω x)
/-- [The linear term object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,n,A). -/

noncomputable def linearTerm (c_f C_f : ℝ) {n : ℕ}
    (ω : TwoSample n n) (A : Bool) : ℝ :=
  ∑ i : Fin 7, (
    ((1 / (blockSize n 1 : ℝ)) *
      ∑ r ∈ blockIdx n 1,
        channelMark ω i r *
          dPhi1 A (pilot c_f C_f ω (channelX ω i r)) i) -
    (∫ x in (0 : ℝ)..1,
      dPhi1 A (pilot c_f C_f ω x) i * pilot c_f C_f ω x i))
/-- [The quadratic term object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,n,A). -/

noncomputable def quadraticTerm (c_f C_f : ℝ) {n : ℕ}
    (ω : TwoSample n n) (A : Bool) : ℝ :=
  let K := quadraticResolution n
  (1 / (2 * (K : ℝ))) *
    ∑ i : Fin 7, ∑ j : Fin 7, ∑ ℓ : Fin K,
      dPhi2 A (pilot c_f C_f ω (midpoint K ℓ)) i j *
      residual c_f C_f ω i K 1 (midpoint K ℓ) *
      residual c_f C_f ω j K 2 (midpoint K ℓ)
/-- [The cubic term object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,n,A). -/

noncomputable def cubicTerm (c_f C_f : ℝ) {n : ℕ}
    (ω : TwoSample n n) (A : Bool) : ℝ :=
  let K := cubicResolution n
  (1 / (6 * (K : ℝ))) *
    ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7, ∑ ℓ : Fin K,
      dPhi3 A (pilot c_f C_f ω (midpoint K ℓ)) i j k *
      residual c_f C_f ω i K 1 (midpoint K ℓ) *
      residual c_f C_f ω j K 2 (midpoint K ℓ) *
      residual c_f C_f ω k K 3 (midpoint K ℓ)

-- @node: def:cubic-estimator
/-- [The cubic estimator object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,n,A). -/
noncomputable def cubicEstimator (c_f C_f : ℝ) {n : ℕ}
    (ω : TwoSample n n) (A : Bool) : ℝ :=
  if n < threshold then 0 else
    pilotIntegral c_f C_f ω A + linearTerm c_f C_f ω A +
      quadraticTerm c_f C_f ω A + cubicTerm c_f C_f ω A
  -- @realizes \widehat T_A(exact split cubic Taylor statistic)
/-- [The mse envelope object](goal) is defined from [the supplied inputs](hyp:c_f,C_f,L). -/

noncomputable def mseEnvelope (c_f C_f L : ℝ) : ℝ :=
  let d : ℝ := 7
  let U := 2 * (1 + C_f)
  let H := 3 * (1 + C_f) * L
  let V := 1 + C_f + C_f ^ 2
  let M := 48 * (1 + C_f) ^ 2 * (4 / c_f) ^ 5
  let A2 := 2 * V * 5 ^ ((1 : ℝ) / 5) +
    2 ^ ((5 : ℝ) / 4) * H ^ 2 * 5 ^ ((1 : ℝ) / 5)
  let A8 := 2 ^ (7 : ℕ) * (Nat.factorial 8 : ℝ) *
    (V ^ 4 * 5 ^ ((4 : ℝ) / 5) + V * 5 ^ ((7 : ℝ) / 5)) +
    2 ^ (8 : ℕ) * H ^ 8 * 5 ^ ((4 : ℝ) / 5)
  let BR := (M / 24) ^ 2 * d ^ 8 * A8
  let BQ := d ^ 4 * M ^ 2 * H ^ 4 *
    2 ^ ((1 : ℝ) / 2) * 5 ^ ((2 : ℝ) / 3)
  let C1 := (M / 2) * d ^ 2 * H ^ 2
  let C2 := (M / 6) * d ^ 3 * H ^ 3
  let BC := 2 * (C1 ^ 2 * d ^ 2 * A2 * 2 ^ ((1 : ℝ) / 2) *
    5 ^ ((1 : ℝ) / 2) + C2 ^ 2 * 2 ^ ((3 : ℝ) / 4) *
    5 ^ ((3 : ℝ) / 4))
  let B2 := d ^ 4 * (2 ^ (2 : ℕ) - 1) ^ 2 * M ^ 2 *
    (1 + U) ^ 4 * (1 + V) ^ 2
  let B3 := d ^ 6 * (2 ^ (3 : ℕ) - 1) ^ 2 * M ^ 2 *
    (1 + U) ^ 6 * (1 + V) ^ 3
  3 * (BR + BQ + BC) + 3 * (10 * d ^ 2 * M ^ 2 + 60 * B2 + 310 * B3)
  -- @realizes C_{\mathrm{mse}}(equation 21)
/-- [The score radius object](goal) is defined from [the supplied inputs](hyp:α,c_f,C_f,L,n). -/

noncomputable def scoreRadius (α c_f C_f L : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * mseEnvelope c_f C_f L / α) *
    (n : ℝ) ^ (-(1 / 3 : ℝ))
  -- @realizes r_n(calibrated score radius)
/-- [The score inversion object](goal) is defined from [the supplied inputs](hyp:α,c_f,C_f,L,n). -/

noncomputable def scoreInversion (α c_f C_f L : ℝ) {n : ℕ}
    (ω : TwoSample n n) : Set ℝ :=
  Causalean.Stat.affineInversionSet parameterSpace
    (cubicEstimator c_f C_f ω true) (cubicEstimator c_f C_f ω false)
    (2 * scoreRadius α c_f C_f L n)
  -- @realizes \mathcal A_n(affine score set)

-- @node: def:score-interval
/-- [The score interval object](goal) is defined from [the supplied inputs](hyp:α,c_f,C_f,L,n). -/
noncomputable def scoreInterval (α c_f C_f L : ℝ) {n : ℕ}
    (ω : TwoSample n n) : Set ℝ := by
  classical
  exact if n < threshold then parameterSpace else
    if (scoreInversion α c_f C_f L ω).Nonempty then
      scoreInversion α c_f C_f L ω else {0}
  -- @realizes I_n(honest score interval)

end CausalSmith.Stat.TransportCaceRoughnuisanceLength

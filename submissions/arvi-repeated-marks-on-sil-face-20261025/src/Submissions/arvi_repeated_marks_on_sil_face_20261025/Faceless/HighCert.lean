import Submissions.arvi_repeated_marks_on_sil_face_20261025.Faceless.Family
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Faceless.IPoly
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Finite.HighGate

/-!
# Uniform HIGH certificates for a piece of the faceless family

For a piece `P`, a width endpoint `b` (a polynomial in `y`: the crossing `s(y)` or the cap) and a
branch `k`, the cleared HIGH gate

  `6³ B₀³ · Dn · highGate (P.node y) (P.node (y - Dy)) (P.node (y - Dy)) 8 b ν p k`,

with `ν = q + u (3/4 - q)`, is a bicubic in `(u, p)` whose coefficients `CuP` are polynomials in `y`.
They are computed by polynomial arithmetic from the samples of `gateG` at `ν, p ∈ {0, 1, -1, 2}`
(`gateG` is affine in the amplifier `a` and in `F`). A bisection tree in `(u, p)` with positive
Bernstein coefficients on every leaf, each positive for `y ∈ [0, 1]`, proves the gate positive for
every `y`, `ν ∈ [q, 3/4]`, `p ∈ [0, 1/2]` (`Piece.high_pos_of_U`, `HighCoeffPos`).

This file has the formulas and the Bernstein transforms of the leaves, on integer polynomials and on
packed ones (`PP`). `Packed.lean` computes the coefficients in packed arithmetic, and `TreeZ.lean`
checks the trees.
-/

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite Poly

/-! ## `gateG` over polynomials -/

def dIP (p : ℚ) : Fin 2 → Poly := ![[1], [1 - p]]
def ePP (p : ℚ) (L : Poly) : Fin 3 → Poly := ![[1], [1], add L [-2*p]]
def gPP (L : Poly) : Fin 3 → Poly := ![[1], [1], L]
def gateMP (ν p : ℚ) (L : Poly) (k : Branch) : Poly :=
  add (smul (12*ν) (mul (dIP p k.1) (ePP p L k.2)))
    (smul (5 - 6*ν) (add (smul 2 (ePP p L k.2)) (mul (dIP p k.1) (gPP L k.2))))

/-! ## The cleared samples -/

/-- `Dn · gateG (Na/Dn) T S (NF/Dn) …`, cleared directly (`TD = T·Dn`, `SD = S·Dn`). -/
def gateGDnP (Dn Na NF TD SD : Poly) (fee K : ℚ) (B L : Poly) (hc ν p : ℚ) (k : Branch) : Poly :=
  let bI : Fin 2 → Poly := ![smul (2*p*K) SD, smul p NF]
  let hP : Fin 3 → Poly := ![smul (2*p) SD, smul (2*p*hc) NF, mul (smul (2*p) B) NF]
  let base := add (smul (15 - 6*ν) (sub Na (smul ν TD)))
    (add (smul ν (sub (smul 10 Dn) (smul 60 Na)))
      (add (smul ((15 - 6*ν)*(1 - 2*p)*ν) SD) (add (smul (-10*ν) NF) (smul (-fee*(15 - 6*ν)) Dn))))
  let N := add (smul 10 (mul NF (mul (dIP p k.1) (ePP p L k.2))))
    (smul (5 - 6*ν) (add (smul 2 (mul (ePP p L k.2) (bI k.1))) (mul (dIP p k.1) (hP k.2))))
  add (mul (gateMP ν p L k) base) (smul (ν*(15 - 6*ν)) N)

theorem eval_gateGDnP (Dn Na NF T S : Poly) (fee K : ℚ) (B L : Poly) (hc ν p : ℚ) (k : Branch)
    (y : ℚ) (hD : eval Dn y ≠ 0) :
    eval (gateGDnP Dn Na NF (mul T Dn) (mul S Dn) fee K B L hc ν p k) y =
      eval Dn y * gateG (eval Na y / eval Dn y) (eval T y) (eval S y) (eval NF y / eval Dn y)
        fee K (eval B y) (eval L y) hc ν p k := by
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [gateGDnP, gateMP, dIP, ePP, gPP, gateG, gateM, gateN, dI, eP, gP, bI, hP,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    field_simp <;> ring

namespace Piece
variable (P : Piece)

/-- `Dn · highGate` at the sample `(ν, p)`, as a polynomial in `y`. -/
def valP (b : Poly) (k : Branch) (ν p : ℚ) : Poly :=
  let T := add (P.tP b) b
  let S := sub b [2*feeE]
  let Na := P.NaP b
  let NF := sub (smul (1 - feeE) P.DnP) (smul 6 Na)
  trim (gateGDnP P.DnP Na NF (mul T P.DnP) (mul S P.DnP) feeF 8 P.B0p P.L0p capF ν p k)

theorem eval_valP (b : Poly) (k : Branch) (ν p y : ℚ) (hB : P.B (y - P.Dy) ≠ 0)
    (hL : P.L (y - P.Dy) ≠ 0) :
    eval (P.valP b k ν p) y =
      P.DnAt y * highGate (P.node y) (P.node (y - P.Dy)) (P.node (y - P.Dy)) 8 (eval b y) ν p k := by
  have hD : P.DnAt y ≠ 0 := by simp [DnAt, den, hB]
  have hD' : eval P.DnP y ≠ 0 := by simpa using hD
  simp only [valP, eval_trim]
  rw [eval_gateGDnP _ _ _ _ _ _ _ _ _ _ _ _ _ y hD']
  rw [highGate, sourceA_eq P y _ hB hL, sourceF_eq P y _ hB hL, sourceT_eq]
  simp only [eval_add, eval_sub, eval_smul, eval_tP, eval_NaP, eval_DnP, eval_B0p, eval_L0p,
    eval_nil, eval_cons, mul_zero, add_zero, node]
  congr 1
  congr 1
  field_simp
  ring

end Piece

/-! ## Interpolation, the `u` substitution and Bernstein coefficients over polynomials -/

def cubic4P (f : ℚ → Poly) : Fin 4 → Poly :=
  ![f 0, smul (1/6) (add (add (smul (-1) (f 2)) (smul 6 (f 1))) (add (smul (-3) (f 0)) (smul (-2) (f (-1))))),
    smul (1/2) (add (add (f 1) (f (-1))) (smul (-2) (f 0))),
    smul (1/6) (add (add (f 2) (smul (-3) (f 1))) (add (smul 3 (f 0)) (smul (-1) (f (-1)))))]

theorem eval_cubic4P (f : ℚ → Poly) (i : Fin 4) (y : ℚ) :
    eval (cubic4P f i) y = cubic4 (fun x => eval (f x) y) i := by
  fin_cases i <;> simp [cubic4P, cubic4] <;> ring

def bicubicP (f : ℚ → ℚ → Poly) (i j : Fin 4) : Poly :=
  cubic4P (fun x => cubic4P (fun z => f x z) j) i

theorem eval_bicubicP (f : ℚ → ℚ → Poly) (i j : Fin 4) (y : ℚ) :
    eval (bicubicP f i j) y = bicubic (fun x z => eval (f x z) y) i j := by
  simp only [bicubicP, bicubic, eval_cubic4P]

/-- `Σ_i C(i,a) c_{ij} α^{i-a} β^a D^{3-i}`: the `(u, p)` coefficients of `D³ Σ c_{ij} ν^i p^j`
with `ν = (α + u β)/D`. -/
def cuR {R : Type*} [CommRing R] (c : Fin 4 → Fin 4 → R) (α β D : R) (a j : Fin 4) : R :=
  ∑ i : Fin 4, ((i : ℕ).choose a : R) * c i j * α ^ ((i : ℕ) - a) * β ^ (a : ℕ) * D ^ (3 - (i : ℕ))

theorem cuR_eq (c : Fin 4 → Fin 4 → ℝ) (α β D u p : ℝ) (hD : D ≠ 0) :
    D ^ 3 * ∑ i : Fin 4, ∑ j : Fin 4, c i j * ((α + u * β) / D) ^ (i : ℕ) * p ^ (j : ℕ) =
      ∑ a : Fin 4, ∑ j : Fin 4, cuR c α β D a j * u ^ (a : ℕ) * p ^ (j : ℕ) := by
  simp only [cuR, Fin.sum_univ_four]
  simp [Nat.choose]
  field_simp
  ring

def powsP (α β D : Poly) (i a : ℕ) : Poly :=
  smul (i.choose a) (mul (pow α (i - a)) (mul (pow β a) (pow D (3 - i))))

/-- Only the terms `i ≥ a` (the others carry `choose i a = 0`). -/
def cuTerms (c : Fin 4 → Fin 4 → Poly) (α β D : Poly) (a j : Fin 4) : List Poly :=
  ((List.finRange 4).filter (fun i : Fin 4 => a.val ≤ i.val)).map
    (fun i => mul (c i j) (powsP α β D i a))

def sumP (l : List Poly) : Poly := l.foldr add []

def cuP (c : Fin 4 → Fin 4 → Poly) (α β D : Poly) (a j : Fin 4) : Poly :=
  trim (sumP (cuTerms c α β D a j))

theorem eval_cuP (c : Fin 4 → Fin 4 → Poly) (α β D : Poly) (a j : Fin 4) (y : ℚ) :
    eval (cuP c α β D a j) y =
      cuR (fun i j => eval (c i j) y) (eval α y) (eval β y) (eval D y) a j := by
  fin_cases a <;> fin_cases j <;>
    simp [cuP, cuTerms, sumP, List.finRange, powsP, cuR, Fin.sum_univ_four, Nat.choose,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring

/-! ## Bisection trees in `(u, p)` with breakpoint lists in `y` -/

/-! ## The uniform HIGH gate of a piece -/

theorem bicubic_smul (c : ℚ) (f : ℚ → ℚ → ℚ) (i j : Fin 4) :
    bicubic (fun x z => c * f x z) i j = c * bicubic f i j := by
  fin_cases i <;> fin_cases j <;> simp [bicubic, cubic4] <;> ring

theorem cuR_smul (k : ℚ) (c : Fin 4 → Fin 4 → ℚ) (α β D : ℚ) (a j : Fin 4) :
    cuR (fun i j => k * c i j) α β D a j = k * cuR c α β D a j := by
  simp only [cuR, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

theorem cuR_cast (c : Fin 4 → Fin 4 → ℚ) (α β D : ℚ) (a j : Fin 4) :
    ((cuR c α β D a j : ℚ) : ℝ) = cuR (fun i j => (c i j : ℝ)) (α:ℝ) (β:ℝ) (D:ℝ) a j := by
  simp [cuR]

namespace Piece
variable (P : Piece)

def alphaP : Poly := smul (1 - den) P.L0p
def betaP : Poly := sub (smul (9/2) P.B0p) P.alphaP
def sixB0P : Poly := smul 6 P.B0p

/-- The `(u, p)` coefficients of `(6 B₀)³ · Dn · highGate` at width endpoint `b`, branch `k`. -/
def highU (b : Poly) (k : Branch) (a j : Fin 4) : Poly :=
  cuP (bicubicP (fun ν p => P.valP b k ν p)) P.alphaP P.betaP P.sixB0P a j

theorem high_pos_of_U (b : Poly) (k : Branch) (y : ℚ)
    (hU0 : ∀ u p : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ p → p ≤ 1/2 →
      0 < ∑ i : Fin 4, ∑ j : Fin 4, ((eval (P.highU b k i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ))
    (hB : 0 < P.B (y - P.Dy)) (hL : 0 < P.L (y - P.Dy)) (hq : P.q y < 3/4)
    (ν p : ℝ) (hν : ν ∈ Set.Icc ((P.q y : ℚ) : ℝ) (3/4)) (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    0 < highGateReal (P.node y) (P.node (y - P.Dy)) (P.node (y - P.Dy)) 8
      ((eval b y : ℚ) : ℝ) ν p k := by
  set B0 := P.B (y - P.Dy) with hB0
  set L0 := P.L (y - P.Dy) with hL0
  set c : Fin 4 → Fin 4 → ℚ :=
    highCoeffs (P.node y) (P.node (y - P.Dy)) (P.node (y - P.Dy)) 8 (eval b y) k with hcdef
  set Dn := P.DnAt y with hDn
  have hDn0 : 0 < Dn := by simp only [hDn, Piece.DnAt, den]; positivity
  -- the samples: Dn · c = eval (bicubicP valP)
  have hsamp : ∀ i j, eval (bicubicP (fun ν p => P.valP b k ν p) i j) y = Dn * c i j := by
    intro i j
    rw [eval_bicubicP]
    simp only [eval_valP P b k _ _ y hB.ne' hL.ne', hcdef, highCoeffs]
    exact bicubic_smul _ _ i j
  -- the (u, p) coefficients
  have hU : ∀ a j, eval (P.highU b k a j) y =
      Dn * cuR c (eval P.alphaP y) (eval P.betaP y) (eval P.sixB0P y) a j := by
    intro a j
    rw [highU, eval_cuP]
    simp only [hsamp]
    exact cuR_smul Dn c _ _ _ a j
  have hα : eval P.alphaP y = (1 - den) * L0 := by
    simp only [alphaP, eval_smul, eval_L0p]; rfl
  have hβ : eval P.betaP y = 9/2 * B0 - (1 - den) * L0 := by
    simp only [betaP, alphaP, eval_sub, eval_smul, eval_L0p, eval_B0p]; rfl
  have hD : eval P.sixB0P y = 6 * B0 := by
    simp only [sixB0P, eval_smul, eval_B0p]; rfl
  have hqy : P.q y = (1 - den) * L0 / (6 * B0) := rfl
  -- the parametrization nu = q + u w
  have hw : (0:ℝ) < 3/4 - (P.q y : ℝ) := by
    have : ((P.q y : ℚ) : ℝ) < ((3/4 : ℚ) : ℝ) := Rat.cast_lt.mpr hq
    push_cast at this; linarith
  set u : ℝ := (ν - (P.q y : ℝ))/(3/4 - (P.q y : ℝ)) with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith [hν.1]) hw.le
  have hu1 : u ≤ 1 := (div_le_one hw).mpr (by linarith [hν.2])
  have hνu : ν = (((1 - den) * L0 : ℚ) + u * ((9/2 * B0 - (1 - den) * L0 : ℚ) : ℝ)) / ((6 * B0 : ℚ) : ℝ) := by
    have hB0r : (0:ℝ) < (B0 : ℝ) := by exact_mod_cast hB
    have hD0 : ((6 * B0 : ℚ) : ℝ) ≠ 0 := by push_cast; positivity
    have hβw : ((9/2 * B0 - (1 - den) * L0 : ℚ) : ℝ) = (3/4 - (P.q y : ℝ)) * ((6 * B0 : ℚ) : ℝ) := by
      rw [hqy]; push_cast; field_simp; ring
    have hαq : (((1 - den) * L0 : ℚ) : ℝ) = (P.q y : ℝ) * ((6 * B0 : ℚ) : ℝ) := by
      rw [hqy]; push_cast; field_simp
    have huw : u * (3/4 - (P.q y : ℝ)) = ν - (P.q y : ℝ) := by
      rw [hu]; exact div_mul_cancel₀ _ hw.ne'
    rw [hβw, hαq, eq_div_iff hD0]
    linear_combination (-(((6 * B0 : ℚ) : ℝ))) * huw
  -- positivity of the (u, p) bicubic
  have hpos := hU0 u p hu0 hu1 hp.1 hp.2
  simp only [hU] at hpos
  -- back to the gate
  rw [highGateReal_rat]
  have hB0r : (0:ℝ) < (B0 : ℝ) := by exact_mod_cast hB
  have hDnr : (0:ℝ) < (Dn : ℝ) := by exact_mod_cast hDn0
  have key : ((6 * B0 : ℚ) : ℝ) ^ 3 * ((Dn : ℚ) : ℝ) *
      ∑ i : Fin 4, ∑ j : Fin 4, ((c i j : ℚ) : ℝ) * ν ^ (i:ℕ) * p ^ (j:ℕ) =
      ∑ a : Fin 4, ∑ j : Fin 4, ((Dn * cuR c (eval P.alphaP y) (eval P.betaP y) (eval P.sixB0P y) a j : ℚ) : ℝ)
        * u ^ (a:ℕ) * p ^ (j:ℕ) := by
    rw [hα, hβ, hD, hνu]
    have h6 : ((6 * B0 : ℚ) : ℝ) ≠ 0 := by push_cast; positivity
    rw [mul_comm (((6 * B0 : ℚ) : ℝ) ^ 3) _, mul_assoc,
      cuR_eq (fun i j => ((c i j : ℚ) : ℝ)) _ _ _ u p h6, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
    push_cast [cuR_cast]
    ring
  have hfac : (0:ℝ) < ((6 * B0 : ℚ) : ℝ) ^ 3 * ((Dn : ℚ) : ℝ) := by push_cast; positivity
  have : 0 < ((6 * B0 : ℚ) : ℝ) ^ 3 * ((Dn : ℚ) : ℝ) *
      ∑ i : Fin 4, ∑ j : Fin 4, ((c i j : ℚ) : ℝ) * ν ^ (i:ℕ) * p ^ (j:ℕ) := by
    rw [key]; exact hpos
  exact pos_of_mul_pos_right this hfac.le

end Piece

/-! ## Integer leaves: Bernstein coefficients on dyadic boxes with integer arithmetic -/

namespace IPoly

open Faceless.Kronecker

/-- `2^{3m} · shift3 c (k/2^m) (1/2^m)`. -/
def ishift3A (c : Fin 4 → IPoly) (k A : ℤ) : Fin 4 → IPoly :=
  ![add (add (smul (A ^ 3) (c 0)) (smul (A ^ 2 * k) (c 1))) (add (smul (A * k ^ 2) (c 2)) (smul (k ^ 3) (c 3))),
    add (add (smul (A ^ 2) (c 1)) (smul (2 * A * k) (c 2))) (smul (3 * k ^ 2) (c 3)),
    add (smul A (c 2)) (smul (3 * k) (c 3)),
    c 3]

/-- `2^{3m} · shift3 c (k/2^m) (1/2^m)`. -/
def ishift3 (c : Fin 4 → IPoly) (k : ℤ) (m : ℕ) : Fin 4 → IPoly := ishift3A c k ((2 ^ m : ℕ) : ℤ)

/-- `3 · bern3`. -/
def ibern3 (e : Fin 4 → IPoly) : Fin 4 → IPoly :=
  ![smul 3 (e 0), add (smul 3 (e 0)) (e 1), add (add (smul 3 (e 0)) (smul 2 (e 1))) (e 2),
    smul 3 (add (add (e 0) (e 1)) (add (e 2) (e 3)))]

def ib33 (c : Fin 4 → Fin 4 → IPoly) (ka : ℤ) (m : ℕ) (kb : ℤ) (n : ℕ) (I J : Fin 4) : IPoly :=
  ibern3 (fun j => ibern3 (fun i => ishift3 (fun i' => ishift3 (c i') kb n j) ka m i) I) J

theorem eval_ishift3A (c : Fin 4 → IPoly) (k A : ℤ) (hA : A ≠ 0) (y : ℚ) (i : Fin 4) :
    eval (ishift3A c k A i) y =
      (A:ℚ) ^ 3 * shift3 (fun i => eval (c i) y) ((k:ℚ) / A) (1 / A) i := by
  have h : (A:ℚ) ≠ 0 := by exact_mod_cast hA
  fin_cases i <;> simp [ishift3A, shift3, IPoly.eval_add, IPoly.eval_smul, -mul_eq_mul_left_iff,
    -mul_eq_mul_right_iff] <;> field_simp <;> ring

theorem eval_ishift3 (c : Fin 4 → IPoly) (k : ℤ) (m : ℕ) (y : ℚ) (i : Fin 4) :
    eval (ishift3 c k m i) y =
      ((2:ℚ) ^ m) ^ 3 * shift3 (fun i => eval (c i) y) ((k:ℚ) / 2 ^ m) (1 / 2 ^ m) i := by
  rw [ishift3, eval_ishift3A _ _ _ (by positivity)]
  push_cast; rfl

theorem eval_ibern3 (e : Fin 4 → IPoly) (y : ℚ) (i : Fin 4) :
    eval (ibern3 e i) y = 3 * bern3 (fun i => eval (e i) y) i := by
  fin_cases i <;> simp [ibern3, bern3] <;> ring

theorem shift3_smul (κ : ℚ) (v : Fin 4 → ℚ) (a s : ℚ) (i : Fin 4) :
    shift3 (fun j => κ * v j) a s i = κ * shift3 v a s i := by
  fin_cases i <;> simp [shift3] <;> ring

theorem bern3_smul (κ : ℚ) (v : Fin 4 → ℚ) (i : Fin 4) :
    bern3 (fun j => κ * v j) i = κ * bern3 v i := by
  fin_cases i <;> simp [bern3] <;> ring

theorem eval_ib33 (c : Fin 4 → Fin 4 → IPoly) (ka : ℤ) (m : ℕ) (kb : ℤ) (n : ℕ) (y : ℚ)
    (I J : Fin 4) :
    eval (ib33 c ka m kb n I J) y = 9 * ((2:ℚ) ^ m) ^ 3 * ((2:ℚ) ^ n) ^ 3 *
      bern33 (fun i j => eval (c i j) y) ((ka:ℚ) / 2 ^ m) (1 / 2 ^ m) ((kb:ℚ) / 2 ^ n) (1 / 2 ^ n) I J := by
  simp only [ib33, bern33, eval_ibern3, eval_ishift3]
  rw [show (fun j => 3 * bern3 (fun i => ((2:ℚ) ^ m) ^ 3 * shift3 (fun i =>
      ((2:ℚ) ^ n) ^ 3 * shift3 (fun i_1 => eval (c i i_1) y) ((kb:ℚ) / 2 ^ n) (1 / 2 ^ n) j)
        ((ka:ℚ) / 2 ^ m) (1 / 2 ^ m) i) I) =
      fun j => (3 * ((2:ℚ) ^ m) ^ 3 * ((2:ℚ) ^ n) ^ 3) * bern3 (fun i => shift3 (fun i =>
        shift3 (fun i_1 => eval (c i i_1) y) ((kb:ℚ) / 2 ^ n) (1 / 2 ^ n) j)
          ((ka:ℚ) / 2 ^ m) (1 / 2 ^ m) i) I by
    funext j
    rw [show (fun i => ((2:ℚ) ^ m) ^ 3 * shift3 (fun i =>
        ((2:ℚ) ^ n) ^ 3 * shift3 (fun i_1 => eval (c i i_1) y) ((kb:ℚ) / 2 ^ n) (1 / 2 ^ n) j)
          ((ka:ℚ) / 2 ^ m) (1 / 2 ^ m) i) =
        fun i => (((2:ℚ) ^ m) ^ 3 * ((2:ℚ) ^ n) ^ 3) * shift3 (fun i =>
          shift3 (fun i_1 => eval (c i i_1) y) ((kb:ℚ) / 2 ^ n) (1 / 2 ^ n) j)
            ((ka:ℚ) / 2 ^ m) (1 / 2 ^ m) i by
      funext i; rw [shift3_smul]; ring]
    rw [bern3_smul]; ring]
  rw [bern3_smul]; ring

/-! ### Packed leaves

A polynomial `q = A − B` (`A, B` natural coefficient lists) is carried as the four numbers
`⟨A(X), B(X), A(1), B(1)⟩` (`Kronecker.pack`). The Bernstein transform of a leaf is a linear
combination with integer weights, so it acts on these numbers directly: one big-number operation
per term instead of one per coefficient. The coefficients are the base-`X` digits, exactly once
`A(1), B(1) < X` (`Kronecker.unpack_pack_of_one_lt`); `TreeZ.lean` reads them off directly. -/

structure PP where
  pos : ℕ
  neg : ℕ
  pos1 : ℕ
  neg1 : ℕ

namespace PP

def add (r s : PP) : PP := ⟨r.pos + s.pos, r.neg + s.neg, r.pos1 + s.pos1, r.neg1 + s.neg1⟩

def smul (w : ℤ) (r : PP) : PP :=
  if 0 ≤ w then ⟨w.toNat * r.pos, w.toNat * r.neg, w.toNat * r.pos1, w.toNat * r.neg1⟩
  else ⟨(-w).toNat * r.neg, (-w).toNat * r.pos, (-w).toNat * r.neg1, (-w).toNat * r.pos1⟩

/-- Pack both parts of `q` at base `X` and at `1`. -/
def pack (X : ℕ) (q : IPoly) : PP :=
  ⟨Kronecker.pack X (posPart q), Kronecker.pack X (negPart q), Kronecker.pack 1 (posPart q),
    Kronecker.pack 1 (negPart q)⟩

/-- `r` packs `q` at base `X`, with at most `L` coefficients. -/
def Rep (X L : ℕ) (r : PP) (q : IPoly) : Prop :=
  ∃ A B : List ℕ, A.length ≤ L ∧ B.length ≤ L ∧ r.pos = Kronecker.pack X A ∧
    r.neg = Kronecker.pack X B ∧ r.pos1 = Kronecker.pack 1 A ∧ r.neg1 = Kronecker.pack 1 B ∧
    ∀ y : ℚ, eval q y = evalQ A y - evalQ B y

theorem rep_pack (X L : ℕ) (q : IPoly) (hq : q.length ≤ L) : Rep X L (pack X q) q :=
  ⟨_, _, by simpa using hq, by simpa using hq, rfl, rfl, rfl, rfl, fun y => eval_eq_parts q y⟩

theorem rep_add {X L : ℕ} {r s : PP} {q q' : IPoly} (hr : Rep X L r q) (hs : Rep X L s q') :
    Rep X L (add r s) (IPoly.add q q') := by
  obtain ⟨A, B, hA, hB, h1, h2, h3, h4, h5⟩ := hr
  obtain ⟨A', B', hA', hB', h1', h2', h3', h4', h5'⟩ := hs
  refine ⟨addN A A', addN B B', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [length_addN]; omega
  · rw [length_addN]; omega
  · simp only [add, h1, h1', pack_addN]
  · simp only [add, h2, h2', pack_addN]
  · simp only [add, h3, h3', pack_addN]
  · simp only [add, h4, h4', pack_addN]
  · intro y; rw [IPoly.eval_add, h5, h5', evalQ_addN, evalQ_addN]; ring

theorem rep_smul {X L : ℕ} {r : PP} {q : IPoly} (w : ℤ) (hr : Rep X L r q) :
    Rep X L (smul w r) (IPoly.smul w q) := by
  obtain ⟨A, B, hA, hB, h1, h2, h3, h4, h5⟩ := hr
  by_cases hw : 0 ≤ w
  · have hc : ((w.toNat : ℕ) : ℚ) = (w : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hw
    refine ⟨smulN w.toNat A, smulN w.toNat B, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rwa [length_smulN]
    · rwa [length_smulN]
    · simp only [smul, hw, ite_true, h1, pack_smulN]
    · simp only [smul, hw, ite_true, h2, pack_smulN]
    · simp only [smul, hw, ite_true, h3, pack_smulN]
    · simp only [smul, hw, ite_true, h4, pack_smulN]
    · intro y; rw [IPoly.eval_smul, h5, evalQ_smulN, evalQ_smulN, hc]; ring
  · have hw' : 0 ≤ -w := by omega
    have hc : (((-w).toNat : ℕ) : ℚ) = -(w : ℚ) := by
      have := Int.toNat_of_nonneg hw'; push_cast at this ⊢; exact_mod_cast this
    refine ⟨smulN (-w).toNat B, smulN (-w).toNat A, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rwa [length_smulN]
    · rwa [length_smulN]
    · simp only [smul, hw, ite_false, h2, pack_smulN]
    · simp only [smul, hw, ite_false, h1, pack_smulN]
    · simp only [smul, hw, ite_false, h4, pack_smulN]
    · simp only [smul, hw, ite_false, h3, pack_smulN]
    · intro y; rw [IPoly.eval_smul, h5, evalQ_smulN, evalQ_smulN, hc]; ring

end PP

/-- `2^{3m} · shift3` on packed polynomials (as `ishift3A`). -/
def pshift3A (c : Fin 4 → PP) (k A : ℤ) : Fin 4 → PP :=
  ![PP.add (PP.add (PP.smul (A ^ 3) (c 0)) (PP.smul (A ^ 2 * k) (c 1)))
      (PP.add (PP.smul (A * k ^ 2) (c 2)) (PP.smul (k ^ 3) (c 3))),
    PP.add (PP.add (PP.smul (A ^ 2) (c 1)) (PP.smul (2 * A * k) (c 2))) (PP.smul (3 * k ^ 2) (c 3)),
    PP.add (PP.smul A (c 2)) (PP.smul (3 * k) (c 3)),
    c 3]

/-- `3 · bern3` on packed polynomials (as `ibern3`). -/
def pbern3 (e : Fin 4 → PP) : Fin 4 → PP :=
  ![PP.smul 3 (e 0), PP.add (PP.smul 3 (e 0)) (e 1),
    PP.add (PP.add (PP.smul 3 (e 0)) (PP.smul 2 (e 1))) (e 2),
    PP.smul 3 (PP.add (PP.add (e 0) (e 1)) (PP.add (e 2) (e 3)))]

def pb33 (c : Fin 4 → Fin 4 → PP) (ka : ℤ) (m : ℕ) (kb : ℤ) (n : ℕ) (I J : Fin 4) : PP :=
  pbern3 (fun j => pbern3 (fun i => pshift3A (fun i' => pshift3A (c i') kb ((2 ^ n : ℕ) : ℤ) j)
    ka ((2 ^ m : ℕ) : ℤ) i) I) J

theorem rep_pshift3A {X L : ℕ} {c' : Fin 4 → PP} {c : Fin 4 → IPoly} (k A : ℤ)
    (h : ∀ i, PP.Rep X L (c' i) (c i)) (i : Fin 4) :
    PP.Rep X L (pshift3A c' k A i) (ishift3A c k A i) := by
  fin_cases i
  · exact PP.rep_add (PP.rep_add (PP.rep_smul _ (h 0)) (PP.rep_smul _ (h 1)))
      (PP.rep_add (PP.rep_smul _ (h 2)) (PP.rep_smul _ (h 3)))
  · exact PP.rep_add (PP.rep_add (PP.rep_smul _ (h 1)) (PP.rep_smul _ (h 2))) (PP.rep_smul _ (h 3))
  · exact PP.rep_add (PP.rep_smul _ (h 2)) (PP.rep_smul _ (h 3))
  · exact h 3

theorem rep_pbern3 {X L : ℕ} {e' : Fin 4 → PP} {e : Fin 4 → IPoly}
    (h : ∀ i, PP.Rep X L (e' i) (e i)) (i : Fin 4) : PP.Rep X L (pbern3 e' i) (ibern3 e i) := by
  fin_cases i
  · exact PP.rep_smul 3 (h 0)
  · exact PP.rep_add (PP.rep_smul 3 (h 0)) (h 1)
  · exact PP.rep_add (PP.rep_add (PP.rep_smul 3 (h 0)) (PP.rep_smul 2 (h 1))) (h 2)
  · exact PP.rep_smul 3 (PP.rep_add (PP.rep_add (h 0) (h 1)) (PP.rep_add (h 2) (h 3)))

theorem rep_pb33 {X L : ℕ} {c' : Fin 4 → Fin 4 → PP} {c : Fin 4 → Fin 4 → IPoly}
    (h : ∀ i j, PP.Rep X L (c' i j) (c i j)) (ka : ℤ) (m : ℕ) (kb : ℤ) (n : ℕ) (I J : Fin 4) :
    PP.Rep X L (pb33 c' ka m kb n I J) (ib33 c ka m kb n I J) :=
  rep_pbern3 (fun j => rep_pbern3 (fun i => rep_pshift3A _ _
    (fun i' => rep_pshift3A _ _ (fun j' => h i' j') j) i) I) J

/-- The largest length over a coefficient array. -/
def maxLen16 (c : Fin 4 → Fin 4 → IPoly) : ℕ :=
  (List.finRange 4).foldr (fun i acc => (List.finRange 4).foldr
    (fun j acc' => max (c i j).length acc') acc) 0

theorem le_foldr_max {α : Type*} (f : α → ℕ) (l : List α) (a : ℕ) {x : α} (hx : x ∈ l) :
    f x ≤ l.foldr (fun z acc => max (f z) acc) a := by
  induction l with
  | nil => simp at hx
  | cons z l ih =>
    simp only [List.mem_cons] at hx
    simp only [List.foldr_cons]
    rcases hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih hx) (le_max_right _ _)

theorem le_foldr_max_init {α : Type*} (f : α → ℕ) (l : List α) (a : ℕ) :
    a ≤ l.foldr (fun z acc => max (f z) acc) a := by
  induction l with
  | nil => simp
  | cons z l ih => simp only [List.foldr_cons]; exact le_trans ih (le_max_right _ _)

theorem length_le_maxLen16 (c : Fin 4 → Fin 4 → IPoly) (i j : Fin 4) :
    (c i j).length ≤ maxLen16 c := by
  unfold maxLen16
  have key : ∀ l : List (Fin 4), i ∈ l → (c i j).length ≤
      l.foldr (fun i acc => (List.finRange 4).foldr (fun j acc' => max (c i j).length acc') acc) 0 := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons z l ih =>
      simp only [List.foldr_cons]
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact le_foldr_max (fun j => (c i j).length) _ _ (List.mem_finRange j)
      · exact le_trans (ih hl) (le_foldr_max_init (fun j => (c z j).length) _ _)
  exact key _ (List.mem_finRange i)

inductive UTreeI where
  | leaf : List (List (ℕ × ℕ)) → UTreeI
  | u : UTreeI → UTreeI → UTreeI
  | p : UTreeI → UTreeI → UTreeI
  deriving Repr

end IPoly

/-- The bicubic in `(u, p)` with coefficients `c i j (y)` is positive on the certified box for every
`y ∈ [0, 1]` (what every HIGH certificate proves). -/
def HighCoeffPos (c : Fin 4 → Fin 4 → Poly) : Prop :=
  ∀ y : ℚ, 0 ≤ y → y ≤ 1 → ∀ u p : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ p → p ≤ 1/2 →
    0 < ∑ i : Fin 4, ∑ j : Fin 4, ((eval (c i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ)

namespace Piece
variable (P : Piece)

end Piece

end QRH.RepeatedMarks.Faceless

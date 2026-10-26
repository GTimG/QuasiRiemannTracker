import Submissions.arvi_repeated_marks_20261024.Faceless.Family
import Submissions.arvi_repeated_marks_20261024.Faceless.IPoly
import Submissions.arvi_repeated_marks_20261024.Finite.HighGate

/-!
# Uniform HIGH certificates for a piece of the faceless family

For a piece `P`, a width endpoint `b` (a polynomial in `y`: the crossing `s(y)` or the cap) and a
branch `k`, the cleared HIGH gate

  `6³ B₀³ · Dn · highGate (P.node y) (P.node (y - Dy)) (P.node (y - Dy)) 8 b ν p k`,

with `ν = q + u (3/4 - q)`, is a bicubic in `(u, p)` whose coefficients `CuP` are polynomials in `y`.
They are computed by polynomial arithmetic from the samples of `gateG` at `ν, p ∈ {0, 1, -1, 2}`
(`gateG` is affine in the amplifier `a` and in `F`). A bisection tree in `(u, p)` with positive
Bernstein coefficients on every leaf, each certified on `y ∈ [0, 1]` by `Poly.posOn`, proves the gate
positive for every `y`, `ν ∈ [q, 3/4]`, `p ∈ [0, 1/2]`.
-/

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite Poly

/-! ## `gateG` over polynomials -/

def dIP (p : ℚ) : Fin 2 → Poly := ![[1], [1 - p]]
def ePP (p : ℚ) (L : Poly) : Fin 3 → Poly := ![[1], [1], add L [-2*p]]
def gPP (L : Poly) : Fin 3 → Poly := ![[1], [1], L]
def bIP (p K : ℚ) (S F : Poly) : Fin 2 → Poly := ![smul (2*p*K) S, smul p F]
def hPP (p hc : ℚ) (B S F : Poly) : Fin 3 → Poly :=
  ![smul (2*p) S, smul (2*p*hc) F, mul (smul (2*p) B) F]

def gateMP (ν p : ℚ) (L : Poly) (k : Branch) : Poly :=
  add (smul (12*ν) (mul (dIP p k.1) (ePP p L k.2)))
    (smul (5 - 6*ν) (add (smul 2 (ePP p L k.2)) (mul (dIP p k.1) (gPP L k.2))))

def gateNP (ν p K hc : ℚ) (B L S F : Poly) (k : Branch) : Poly :=
  add (smul 10 (mul F (mul (dIP p k.1) (ePP p L k.2))))
    (smul (5 - 6*ν) (add (smul 2 (mul (ePP p L k.2) (bIP p K S F k.1)))
      (mul (dIP p k.1) (hPP p hc B S F k.2))))

def gateGP (a T S F : Poly) (fee K : ℚ) (B L : Poly) (hc ν p : ℚ) (k : Branch) : Poly :=
  add (mul (gateMP ν p L k)
      (add (add (smul (15 - 6*ν) (sub a (smul ν T))) (smul ν (sub [10] (smul 60 a))))
        (add (smul ((15 - 6*ν)*(1 - 2*p)*ν) S) (add (smul (-10*ν) F) [-fee*(15 - 6*ν)]))))
    (smul (ν*(15 - 6*ν)) (gateNP ν p K hc B L S F k))

theorem eval_gateGP (a T S F : Poly) (fee K : ℚ) (B L : Poly) (hc ν p : ℚ) (k : Branch) (y : ℚ) :
    eval (gateGP a T S F fee K B L hc ν p k) y =
      gateG (eval a y) (eval T y) (eval S y) (eval F y) fee K (eval B y) (eval L y) hc ν p k := by
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [gateGP, gateMP, gateNP, dIP, ePP, gPP, bIP, hPP, gateG, gateM, gateN, dI, eP, gP, bI, hP,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring

/-- `gateG` is affine in the amplifier `a` and in `F`. -/
theorem gateG_affine (a T S F fee K B L hc ν p : ℚ) (k : Branch) :
    gateG a T S F fee K B L hc ν p k = gateG 0 T S 0 fee K B L hc ν p k
      + (gateG 1 T S 0 fee K B L hc ν p k - gateG 0 T S 0 fee K B L hc ν p k) * a
      + (gateG 0 T S 1 fee K B L hc ν p k - gateG 0 T S 0 fee K B L hc ν p k) * F := by
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [gateG, gateM, gateN, dI, eP, gP, bI, hP] <;> ring

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

def shift3P (c : Fin 4 → Poly) (a s : ℚ) : Fin 4 → Poly :=
  ![add (add (c 0) (smul a (c 1))) (add (smul (a^2) (c 2)) (smul (a^3) (c 3))),
    smul s (add (add (c 1) (smul (2*a) (c 2))) (smul (3*a^2) (c 3))),
    smul (s^2) (add (c 2) (smul (3*a) (c 3))),
    smul (s^3) (c 3)]

def bern3P (e : Fin 4 → Poly) : Fin 4 → Poly :=
  ![e 0, add (e 0) (smul (1/3) (e 1)), add (add (e 0) (smul (2/3) (e 1))) (smul (1/3) (e 2)),
    add (add (e 0) (e 1)) (add (e 2) (e 3))]

def bern33P (c : Fin 4 → Fin 4 → Poly) (a s b t : ℚ) (I J : Fin 4) : Poly :=
  bern3P (fun j => bern3P (fun i => shift3P (fun i' => shift3P (c i') b t j) a s i) I) J

theorem eval_shift3P (c : Fin 4 → Poly) (a s y : ℚ) (i : Fin 4) :
    eval (shift3P c a s i) y = shift3 (fun i => eval (c i) y) a s i := by
  fin_cases i <;> simp [shift3P, shift3, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

theorem eval_bern3P (e : Fin 4 → Poly) (y : ℚ) (i : Fin 4) :
    eval (bern3P e i) y = bern3 (fun i => eval (e i) y) i := by
  fin_cases i <;> simp [bern3P, bern3, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

theorem eval_bern33P (c : Fin 4 → Fin 4 → Poly) (a s b t y : ℚ) (I J : Fin 4) :
    eval (bern33P c a s b t I J) y = bern33 (fun i j => eval (c i j) y) a s b t I J := by
  simp only [bern33P, bern33, eval_bern3P, eval_shift3P]

/-! ## Bisection trees in `(u, p)` with breakpoint lists in `y` -/

inductive UTree where
  | leaf : List (List ℚ) → UTree
  | u : UTree → UTree → UTree
  | p : UTree → UTree → UTree
  deriving Repr

/-- Every Bernstein coefficient of the leaf box is positive on `y ∈ [0, 1]`; the breakpoint list
of coefficient `(I, J)` is entry `4 I + J`. -/
def leafCheck (c : Fin 4 → Fin 4 → Poly) (a s b t : ℚ) (br : List (List ℚ)) : Bool :=
  (List.finRange 4).all fun I => (List.finRange 4).all fun J =>
    let bs := br.getD (4 * I.val + J.val) []
    !bs.isEmpty && decide (1 ≤ lastPt 0 bs) && posOn (bern33P c a s b t I J) 0 bs

def uCheck (c : Fin 4 → Fin 4 → Poly) : UTree → ℚ → ℚ → ℚ → ℚ → Bool
  | .leaf br, a, s, b, t => leafCheck c a s b t br
  | .u l r, a, s, b, t => uCheck c l a (s/2) b t && uCheck c r (a + s/2) (s/2) b t
  | .p l r, a, s, b, t => uCheck c l a s b (t/2) && uCheck c r a s (b + t/2) (t/2)

theorem leafCheck_sound (c : Fin 4 → Fin 4 → Poly) (a s b t : ℚ) (br : List (List ℚ))
    (hc : leafCheck c a s b t br = true) (y : ℚ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (I J : Fin 4) :
    0 < bern33 (fun i j => eval (c i j) y) a s b t I J := by
  simp only [leafCheck, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨⟨hne, hlast⟩, hpos⟩ := hc I J
  rw [← eval_bern33P]
  refine posOn_sound _ 0 _ hpos y hy0 (hy1.trans hlast) ?_
  intro h; rw [h] at hne; simp at hne

theorem uCheck_sound (c : Fin 4 → Fin 4 → Poly) (T : UTree) :
    ∀ (a s b t : ℚ), 0 < s → 0 < t → uCheck c T a s b t = true →
      ∀ y : ℚ, 0 ≤ y → y ≤ 1 → ∀ u p : ℝ, (a:ℝ) ≤ u → u ≤ (a:ℝ) + s → (b:ℝ) ≤ p → p ≤ (b:ℝ) + t →
        0 < ∑ i : Fin 4, ∑ j : Fin 4, ((eval (c i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ) := by
  induction T with
  | leaf br =>
    intro a s b t hs ht hc y hy0 hy1 u p hu0 hu1 hp0 hp1
    apply bicubic_pos (fun i j => ((eval (c i j) y : ℚ) : ℝ)) (a := (a:ℝ)) (s := (s:ℝ)) (b := (b:ℝ))
      (t := (t:ℝ)) (by exact_mod_cast hs) (by exact_mod_cast ht) hu0 hu1 hp0 hp1
    intro I J
    rw [← bern33_cast]
    exact_mod_cast leafCheck_sound c a s b t br hc y hy0 hy1 I J
  | u l r ihl ihr =>
    intro a s b t hs ht hc y hy0 hy1 u p hu0 hu1 hp0 hp1
    simp only [uCheck, Bool.and_eq_true] at hc
    rcases le_total u ((a:ℝ) + (s:ℝ)/2) with hu | hu
    · exact ihl a (s/2) b t (by linarith) ht hc.1 y hy0 hy1 u p hu0 (by push_cast; linarith) hp0 hp1
    · exact ihr (a + s/2) (s/2) b t (by linarith) ht hc.2 y hy0 hy1 u p (by push_cast; linarith)
        (by push_cast; linarith) hp0 hp1
  | p l r ihl ihr =>
    intro a s b t hs ht hc y hy0 hy1 u p hu0 hu1 hp0 hp1
    simp only [uCheck, Bool.and_eq_true] at hc
    rcases le_total p ((b:ℝ) + (t:ℝ)/2) with hp | hp
    · exact ihl a s b (t/2) hs (by linarith) hc.1 y hy0 hy1 u p hu0 hu1 hp0 (by push_cast; linarith)
    · exact ihr a s (b + t/2) (t/2) hs (by linarith) hc.2 y hy0 hy1 u p hu0 hu1 (by push_cast; linarith)
        (by push_cast; linarith)

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

theorem high_pos_of_cert (b : Poly) (k : Branch) (T : UTree)
    (hc : uCheck (P.highU b k) T 0 1 0 (1/2) = true)
    (y : ℚ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hB : 0 < P.B (y - P.Dy)) (hL : 0 < P.L (y - P.Dy)) (hq : P.q y < 3/4)
    (ν p : ℝ) (hν : ν ∈ Set.Icc ((P.q y : ℚ) : ℝ) (3/4)) (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    0 < highGateReal (P.node y) (P.node (y - P.Dy)) (P.node (y - P.Dy)) 8
      ((eval b y : ℚ) : ℝ) ν p k :=
  P.high_pos_of_U b k y (fun u p hu0 hu1 hp0 hp1 => uCheck_sound (P.highU b k) T 0 1 0 (1/2) one_pos
    (by norm_num) hc y hy0 hy1 u p (by simpa using hu0) (by simpa using hu1) (by simpa using hp0)
    (by simpa using hp1)) hB hL hq ν p hν hp

end Piece

/-! ## Integer leaves: Bernstein coefficients on dyadic boxes with integer arithmetic -/

namespace IPoly

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

/-- Every Bernstein coefficient of the dyadic leaf box is positive on `y ∈ [0, 1]`. -/
def leafCheckI (c : Fin 4 → Fin 4 → IPoly) (ka m kb n : ℕ) (br : List (List (ℕ × ℕ))) : Bool :=
  (List.finRange 4).all fun I => (List.finRange 4).all fun J =>
    let l := br.getD (4 * I.val + J.val) []
    !l.isEmpty && posOn (ib33 c ka m kb n I J) 0 0 l

inductive UTreeI where
  | leaf : List (List (ℕ × ℕ)) → UTreeI
  | u : UTreeI → UTreeI → UTreeI
  | p : UTreeI → UTreeI → UTreeI
  deriving Repr

/-- The box `u ∈ [ka/2^m, (ka+1)/2^m]`, `p ∈ [kb/2^n, (kb+1)/2^n]`. -/
def uCheckI (c : Fin 4 → Fin 4 → IPoly) : UTreeI → ℕ → ℕ → ℕ → ℕ → Bool
  | .leaf br, ka, m, kb, n => leafCheckI c ka m kb n br
  | .u l r, ka, m, kb, n => uCheckI c l (2*ka) (m+1) kb n && uCheckI c r (2*ka+1) (m+1) kb n
  | .p l r, ka, m, kb, n => uCheckI c l ka m (2*kb) (n+1) && uCheckI c r ka m (2*kb+1) (n+1)

theorem leafCheckI_sound (c : Fin 4 → Fin 4 → IPoly) (ka m kb n : ℕ) (br : List (List (ℕ × ℕ)))
    (hc : leafCheckI c ka m kb n br = true) (y : ℚ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (I J : Fin 4) :
    0 < bern33 (fun i j => eval (c i j) y) ((ka:ℚ) / 2 ^ m) (1 / 2 ^ m) ((kb:ℚ) / 2 ^ n)
      (1 / 2 ^ n) I J := by
  simp only [leafCheckI, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.not_eq_true'] at hc
  obtain ⟨hne, hpos⟩ := hc I J
  have h := posOn_sound _ 0 0 _ hpos y (by simpa using hy0) hy1
    (by intro h; rw [h] at hne; simp at hne)
  rw [eval_ib33] at h
  have hk : (0:ℚ) < 9 * ((2:ℚ) ^ m) ^ 3 * ((2:ℚ) ^ n) ^ 3 := by positivity
  exact pos_of_mul_pos_right h hk.le

theorem uCheckI_sound (c : Fin 4 → Fin 4 → IPoly) (T : UTreeI) :
    ∀ (ka m kb n : ℕ), uCheckI c T ka m kb n = true →
      ∀ y : ℚ, 0 ≤ y → y ≤ 1 → ∀ u p : ℝ, (ka:ℝ) / 2 ^ m ≤ u → u ≤ ((ka:ℝ) + 1) / 2 ^ m →
        (kb:ℝ) / 2 ^ n ≤ p → p ≤ ((kb:ℝ) + 1) / 2 ^ n →
        0 < ∑ i : Fin 4, ∑ j : Fin 4, ((eval (c i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ) := by
  induction T with
  | leaf br =>
    intro ka m kb n hc y hy0 hy1 u p hu0 hu1 hp0 hp1
    have hs : (0:ℝ) < 1 / 2 ^ m := by positivity
    have ht : (0:ℝ) < 1 / 2 ^ n := by positivity
    apply bicubic_pos (fun i j => ((eval (c i j) y : ℚ) : ℝ)) (a := (ka:ℝ) / 2 ^ m) (s := 1 / 2 ^ m)
      (b := (kb:ℝ) / 2 ^ n) (t := 1 / 2 ^ n) hs ht hu0 (by rw [← add_div]; exact hu1) hp0
      (by rw [← add_div]; exact hp1)
    intro I J
    have h := leafCheckI_sound c ka m kb n br hc y hy0 hy1 I J
    have hcast := bern33_cast (fun i j => eval (c i j) y) ((ka:ℚ) / 2 ^ m) (1 / 2 ^ m)
      ((kb:ℚ) / 2 ^ n) (1 / 2 ^ n) I J
    push_cast at hcast
    rw [← hcast]
    exact_mod_cast h
  | u l r ihl ihr =>
    intro ka m kb n hc y hy0 hy1 u p hu0 hu1 hp0 hp1
    simp only [uCheckI, Bool.and_eq_true] at hc
    have h2 : (0:ℝ) < 2 ^ m := by positivity
    rcases le_total u ((((2 * ka : ℕ) : ℝ) + 1) / 2 ^ (m + 1)) with hu | hu
    · refine ihl (2*ka) (m+1) kb n hc.1 y hy0 hy1 u p ?_ hu hp0 hp1
      rw [pow_succ]; push_cast
      calc (2 * (ka:ℝ)) / (2 ^ m * 2) = (ka:ℝ) / 2 ^ m := by field_simp
        _ ≤ u := hu0
    · refine ihr (2*ka+1) (m+1) kb n hc.2 y hy0 hy1 u p ?_ ?_ hp0 hp1
      · push_cast at hu ⊢; exact hu
      · rw [pow_succ]; push_cast
        calc u ≤ ((ka:ℝ) + 1) / 2 ^ m := hu1
          _ = (2 * (ka:ℝ) + 1 + 1) / (2 ^ m * 2) := by field_simp; ring
  | p l r ihl ihr =>
    intro ka m kb n hc y hy0 hy1 u p hu0 hu1 hp0 hp1
    simp only [uCheckI, Bool.and_eq_true] at hc
    have h2 : (0:ℝ) < 2 ^ n := by positivity
    rcases le_total p ((((2 * kb : ℕ) : ℝ) + 1) / 2 ^ (n + 1)) with hp | hp
    · refine ihl ka m (2*kb) (n+1) hc.1 y hy0 hy1 u p hu0 hu1 ?_ hp
      rw [pow_succ]; push_cast
      calc (2 * (kb:ℝ)) / (2 ^ n * 2) = (kb:ℝ) / 2 ^ n := by field_simp
        _ ≤ p := hp0
    · refine ihr ka m (2*kb+1) (n+1) hc.2 y hy0 hy1 u p hu0 hu1 ?_ ?_
      · push_cast at hp ⊢; exact hp
      · rw [pow_succ]; push_cast
        calc p ≤ ((kb:ℝ) + 1) / 2 ^ n := hp1
          _ = (2 * (kb:ℝ) + 1 + 1) / (2 ^ n * 2) := by field_simp; ring

end IPoly

/-- The common denominator of a coefficient array. -/
def lcmDen16 (c : Fin 4 → Fin 4 → Poly) : ℕ :=
  (List.finRange 4).foldr (fun i acc => (List.finRange 4).foldr
    (fun j acc' => Nat.lcm (IPoly.lcmDen (c i j)) acc') acc) 1

def intOK16 (c : Fin 4 → Fin 4 → Poly) (D : ℕ) : Bool :=
  (List.finRange 4).all fun i => (List.finRange 4).all fun j => IPoly.isIntMul (c i j) D

/-- The integer certificate of a coefficient array. -/
def certI (c : Fin 4 → Fin 4 → Poly) (T : IPoly.UTreeI) : Bool :=
  let D := lcmDen16 c
  decide (0 < D) && intOK16 c D && IPoly.uCheckI (fun i j => IPoly.ofPoly (c i j) D) T 0 0 0 1

theorem certI_sound (c : Fin 4 → Fin 4 → Poly) (T : IPoly.UTreeI) (hc : certI c T = true)
    (y : ℚ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (u p : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1/2) :
    0 < ∑ i : Fin 4, ∑ j : Fin 4, ((eval (c i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ) := by
  simp only [certI, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hD, hint⟩, hu⟩ := hc
  have h := IPoly.uCheckI_sound _ T 0 0 0 1 hu y hy0 hy1 u p (by simpa using hu0)
    (by simpa using hu1) (by simpa using hp0) (by norm_num; linarith)
  simp only [intOK16, List.all_eq_true, List.mem_finRange, true_implies] at hint
  have hD' : (0:ℝ) < (lcmDen16 c : ℝ) := by exact_mod_cast hD
  have heq : ∀ i j, ((IPoly.eval (IPoly.ofPoly (c i j) (lcmDen16 c)) y : ℚ) : ℝ) =
      (lcmDen16 c : ℝ) * ((eval (c i j) y : ℚ) : ℝ) := by
    intro i j; rw [IPoly.eval_ofPoly _ _ (hint i j)]; push_cast; ring
  simp only [heq] at h
  have : ∑ i : Fin 4, ∑ j : Fin 4, (lcmDen16 c : ℝ) * ((eval (c i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ)
      = (lcmDen16 c : ℝ) * ∑ i : Fin 4, ∑ j : Fin 4, ((eval (c i j) y : ℚ) : ℝ) * u ^ (i:ℕ) * p ^ (j:ℕ) := by
    simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [this] at h
  exact pos_of_mul_pos_right h hD'.le

namespace Piece
variable (P : Piece)

/-- The uniform HIGH gate of a piece from an integer certificate. -/
theorem high_pos_of_certI (b : Poly) (k : Branch) (T : IPoly.UTreeI)
    (hc : certI (P.highU b k) T = true)
    (y : ℚ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hB : 0 < P.B (y - P.Dy)) (hL : 0 < P.L (y - P.Dy)) (hq : P.q y < 3/4)
    (ν p : ℝ) (hν : ν ∈ Set.Icc ((P.q y : ℚ) : ℝ) (3/4)) (hp : p ∈ Set.Icc (0:ℝ) (1/2)) :
    0 < highGateReal (P.node y) (P.node (y - P.Dy)) (P.node (y - P.Dy)) 8
      ((eval b y : ℚ) : ℝ) ν p k :=
  P.high_pos_of_U b k y (fun u p hu0 hu1 hp0 hp1 => certI_sound _ T hc y hy0 hy1 u p hu0 hu1 hp0 hp1)
    hB hL hq ν p hν hp

end Piece

end QRH.RepeatedMarks.Faceless

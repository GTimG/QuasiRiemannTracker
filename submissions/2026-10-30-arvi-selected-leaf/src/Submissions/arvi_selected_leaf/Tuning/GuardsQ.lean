import Submissions.arvi_selected_leaf.Tuning.Poly2

/-!
# The admission guards and row margins of the return as computable polynomials

`BranchQ` is the rational data of one count branch: a face `(B, Λ, cap)` and whether the plain curve is
read on its capped piece. `BranchQ.guard b j` is the `j`-th guard of `Formulas.lean`'s `admissionGuard`
as a polynomial in `(δ, p)`, built from the same pieces (`D, A, C0, Z, U, J, N, T, RN, MN, DJ` and the
`p`-derivatives). The return's global constants (`m_minus = 3/10`, `s_minus = 27/1000`,
`naturalK = 9/2`, the buffer `1/10^7`) enter as the rational literals of `Constants.lean`.
-/

set_option autoImplicit false

namespace QRH.ArviReturnTuning

open Q2

/-- The buffer `1/10000000` of `Formulas.lean`. -/
def etaQ : ℚ := 1 / 10000000
def mMinusQ : ℚ := 3 / 10
def sMinusQ : ℚ := 27 / 1000
def naturalKQ : ℚ := 9 / 2
def naturalMQ : ℚ := (1 - naturalKQ * sMinusQ) / 2

/-- Rational data of a (non-old) count branch. -/
structure BranchQ where
  B : ℚ
  L : ℚ
  cap : ℚ
  capped : Bool

namespace BranchQ
variable (b : BranchQ)

def Zc : ℚ := b.cap - etaQ
def Vq : Q2 := sub (C (5 / 6)) X
def Dq : Q2 := if b.capped then sub (C 3) Y else sub (sub (C 3) Y) (smul (4 / b.L) Y)
def Aq : Q2 := if b.capped then C 2 else sub (C 2) (smul (4 / b.L) Y)
def C0q : Q2 := if b.capped then sub (C 1) (smul (2 * b.Zc) Y) else sub (C 1) (smul (2 * b.B / b.L) Y)
def Zq : Q2 := if b.capped then smul (2 * b.Zc) Y else smul (2 * b.B / b.L) Y
def Uq : Q2 := mul (sub (C 1) Y) b.C0q
def Jq : Q2 := add (mul Vq b.Dq) (mul (mul X (sub (C 1) Y)) b.Aq)
def Nq : Q2 := add (mul (sub (C 1) X) b.Jq) (mul (mul Vq X) b.Uq)
def Tq : Q2 := add b.Jq (mul X b.Uq)
def RNq : Q2 := add (mul b.Aq b.Tq) (mul (sub b.Zq Y) b.Jq)
def MNq : Q2 := sub (mul b.Dq b.Tq) b.RNq
def DJq : Q2 := mul b.Dq b.Jq
def dD : ℚ := if b.capped then -1 else -1 - 4 / b.L
def dA : ℚ := if b.capped then 0 else -4 / b.L
def dC : ℚ := if b.capped then -2 * b.Zc else -2 * b.B / b.L
def dUq : Q2 := add (smul (-1) b.C0q) (smul b.dC (sub (C 1) Y))
def dJq : Q2 := add (smul b.dD Vq) (mul X (add (smul (-1) b.Aq) (smul b.dA (sub (C 1) Y))))
def lowerM : ℚ :=
  if b.capped then mMinusQ + etaQ else max (mMinusQ + etaQ) ((b.B - b.L * (b.cap - etaQ)) / 2 + etaQ)
def upperM : ℚ :=
  if b.capped then min (min (11 / 25 - etaQ) (naturalMQ - etaQ)) ((b.B - b.L * b.Zc) / 2 - etaQ)
  else min (min (11 / 25 - etaQ) (naturalMQ - etaQ)) ((b.B - b.L * (sMinusQ + etaQ)) / 2 - etaQ)

/-- The fifteen guards of `admissionGuard` (`Formulas.lean`), in its order. -/
def guard : Fin 15 → Q2 :=
  ![b.Dq, b.Aq, b.C0q, b.Jq, sub b.Tq b.Jq, sub (smul (12499 / 10000) b.Jq) b.Tq,
    sub b.RNq (smul (23 / 37) b.DJq), sub b.DJq b.RNq,
    sub b.MNq (smul b.lowerM b.DJq), sub (smul b.upperM b.DJq) b.MNq,
    sub b.Nq (mul (sub (sub (C 1) (smul (2 * naturalMQ) X)) (smul (2 * sMinusQ) (mul X Y))) b.Jq),
    sub (mul b.Uq b.dJq) (mul b.dUq b.Jq),
    C (11 / 25 - naturalMQ - etaQ),
    C (b.B - 2 * naturalMQ - b.L * (sMinusQ + etaQ) - 2 * etaQ),
    if b.capped then smul (b.Zc - sMinusQ - etaQ) b.DJq else C 1]

end BranchQ

/-- All fifteen guards are positive on the window `[dlo, dhi] × [plo, 1/2]` (subdivision depth `k`). -/
def windowCheck (b : BranchQ) (k : ℕ) (dlo dhi plo : ℚ) : Bool :=
  (List.finRange 15).all fun j => posBox (b.guard j) k dlo dhi plo (1 / 2)

end QRH.ArviReturnTuning

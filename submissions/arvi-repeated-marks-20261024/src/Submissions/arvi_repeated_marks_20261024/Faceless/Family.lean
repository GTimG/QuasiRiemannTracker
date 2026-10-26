import Submissions.arvi_repeated_marks_20261024.Faceless.Poly
import Submissions.arvi_repeated_marks_20261024.Finite.SourceValid2

/-!
# The faceless source family

The source graph is replaced by one explicit family of faces. On a piece `s = σ + H y`, `y ∈ [0,1]`,
the envelope is a polynomial `E(y)` (a cubic tracking the closed-form switching flow of
`research/chain-ode`). The face at `y` is the secant of `E` over one step `Dy`:

  `L(y) = (E(y) - E(y + Dy))/(H Dy)`,  `B(y) = E(y) + s(y) L(y)`,

so consecutive faces cross exactly at `s(y)`. The threshold is the LOW limit of the previous face
with the fixed LOW denominator `den`: `q(y) = (1 - den) L(y - Dy)/(6 B(y - Dy))`. Every gate of the
step from the face at `y - Dy` to the face at `y` is then a rational function of `y` whose
denominator is a power of `B(y - Dy)`; this file proves the algebraic identities.
-/

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless
open Record1252270103Finite Poly

/-- The LOW denominator of every step. -/
def den : ℚ := 1/2^15
/-- The common cap of every face. -/
def capF : ℚ := 549989/10000000
/-- The fine fee tuple of `NFAccounting` (`Or.inr`). -/
def feeE : ℚ := 1/10^17
def feeR : ℚ := 1/10^12
def feeF : ℚ := 1/10^10

/-- One piece of the family: `s = sig + H y` and the envelope polynomial `Ey` in `y`, step `Dy`. -/
structure Piece where
  sig : ℚ
  H : ℚ
  Dy : ℚ
  Ey : Poly

namespace Piece
variable (P : Piece)

def E (y : ℚ) : ℚ := eval P.Ey y
def s (y : ℚ) : ℚ := P.sig + P.H * y
def L (y : ℚ) : ℚ := (P.E y - P.E (y + P.Dy)) / (P.H * P.Dy)
def B (y : ℚ) : ℚ := P.E y + P.s y * P.L y
def q (y : ℚ) : ℚ := (1 - den) * P.L (y - P.Dy) / (6 * P.B (y - P.Dy))

/-- The face at `y`. -/
def node (y : ℚ) : Source := ⟨P.B y, P.L y, capF, P.q y, feeE, feeR, feeF⟩

/-! ### The same quantities as polynomials in `y` -/

def sp : Poly := [P.sig, P.H]
def Lp : Poly := smul (1 / (P.H * P.Dy)) (sub P.Ey (shift P.Ey P.Dy))
def Bp : Poly := add P.Ey (mul P.sp P.Lp)
def B0p : Poly := shift P.Bp (-P.Dy)
def L0p : Poly := shift P.Lp (-P.Dy)

@[simp] theorem eval_sp (y : ℚ) : eval P.sp y = P.s y := by simp [sp, s]; ring

@[simp] theorem eval_Lp (y : ℚ) : eval P.Lp y = P.L y := by
  simp [Lp, L, E]; rw [add_comm P.Dy y]; ring

@[simp] theorem eval_Bp (y : ℚ) : eval P.Bp y = P.B y := by simp [Bp, B, E]

@[simp] theorem eval_B0p (y : ℚ) : eval P.B0p y = P.B (y - P.Dy) := by
  simp [B0p]; ring_nf

@[simp] theorem eval_L0p (y : ℚ) : eval P.L0p y = P.L (y - P.Dy) := by
  simp [L0p]; ring_nf

/-! ### Identities of the step from `y - Dy` to `y` -/

/-- Consecutive faces cross exactly at `s(y)`. -/
theorem crossing_eq (y : ℚ) (hH : P.H * P.Dy ≠ 0) (hL : P.L (y - P.Dy) ≠ P.L y) :
    crossing (P.node y) (P.node (y - P.Dy)) = P.s y := by
  have hH1 : P.H ≠ 0 := left_ne_zero_of_mul hH
  have hD1 : P.Dy ≠ 0 := right_ne_zero_of_mul hH
  have key : P.B (y - P.Dy) - P.B y = P.s y * (P.L (y - P.Dy) - P.L y) := by
    simp only [B, L, s, sub_add_cancel]
    field_simp
    ring
  have hL' : P.L (y - P.Dy) - P.L y ≠ 0 := sub_ne_zero.mpr hL
  simp only [crossing, node]
  rw [key]; field_simp

/-- The LOW denominator of the step is `den`. -/
theorem sourceDen_eq (y : ℚ) (hB : P.B (y - P.Dy) ≠ 0) (hL : P.L (y - P.Dy) ≠ 0) :
    sourceDen (P.node y) (P.node (y - P.Dy)) = den := by
  simp only [sourceDen, node, q]
  field_simp
  ring

/-- `t = B - L (b - e)`. -/
def tAt (y b : ℚ) : ℚ := P.B y - P.L y * (b - feeE)
/-- The numerator of the amplifier: `a = Na/(6 den B₀)`. -/
def NaAt (y b : ℚ) : ℚ :=
  (1 - den) * (P.L (y - P.Dy) * b + P.tAt y b - P.B (y - P.Dy)) + 6 * feeR * P.B (y - P.Dy)
/-- The common denominator `6 den B₀`. -/
def DnAt (y : ℚ) : ℚ := 6 * den * P.B (y - P.Dy)

theorem sourceT_eq (y b : ℚ) : sourceT (P.node y) b = P.tAt y b := by
  simp [sourceT, node, tAt]

theorem sourceA_eq (y b : ℚ) (hB : P.B (y - P.Dy) ≠ 0) (hL : P.L (y - P.Dy) ≠ 0) :
    sourceA (P.node y) (P.node (y - P.Dy)) b = P.NaAt y b / P.DnAt y := by
  rw [sourceA, sourceDen_eq P y hB hL]
  simp only [node, q, NaAt, DnAt, tAt, sourceT]
  field_simp
  ring

theorem sourceF_eq (y b : ℚ) (hB : P.B (y - P.Dy) ≠ 0) (hL : P.L (y - P.Dy) ≠ 0) :
    sourceF (P.node y) (P.node (y - P.Dy)) b = 1 - 6 * (P.NaAt y b / P.DnAt y) := by
  rw [sourceF, sourceA_eq P y b hB hL]

/-! ### Polynomial versions -/

def tP (b : Poly) : Poly := sub P.Bp (mul P.Lp (sub b [feeE]))
def NaP (b : Poly) : Poly :=
  add (smul (1 - den) (add (mul P.L0p b) (sub (P.tP b) P.B0p))) (smul (6 * feeR) P.B0p)
def DnP : Poly := smul (6 * den) P.B0p

@[simp] theorem eval_tP (b : Poly) (y : ℚ) : eval (P.tP b) y = P.tAt y (eval b y) := by
  simp [tP, tAt]

@[simp] theorem eval_NaP (b : Poly) (y : ℚ) : eval (P.NaP b) y = P.NaAt y (eval b y) := by
  simp only [NaP, NaAt, eval_add, eval_smul, eval_mul, eval_sub, eval_tP, eval_B0p, eval_L0p]
  ring

@[simp] theorem eval_DnP (y : ℚ) : eval P.DnP y = P.DnAt y := by simp [DnP, DnAt]

end Piece

end QRH.RepeatedMarks.Faceless

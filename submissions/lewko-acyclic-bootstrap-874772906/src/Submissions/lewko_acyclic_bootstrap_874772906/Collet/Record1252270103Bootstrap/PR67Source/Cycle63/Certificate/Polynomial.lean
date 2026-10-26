import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Computable polynomials in several variables with rational coefficients, evaluated at real points.
Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.Certificate

/-- A point with its first coordinate dropped. -/
def tailPt (x : ℕ → ℝ) : ℕ → ℝ := fun i => x (i + 1)

/-- The box `Π [lo_i, hi_i]` as a condition on the first coordinates of a point. -/
def InBox : List (ℚ × ℚ) → (ℕ → ℝ) → Prop
  | [], _ => True
  | I :: box, x => (I.1 : ℝ) ≤ x 0 ∧ x 0 ≤ (I.2 : ℝ) ∧ InBox box (tailPt x)

/-- Coefficient arithmetic for computable polynomials: the operations, a zero test, a positivity test
on a box, and an evaluation at real points that respects the operations. -/
structure Coeffs (R : Type) where
  /-- Number of variables. -/
  nvars : ℕ
  add : R → R → R
  mul : R → R → R
  smul : ℚ → R → R
  ofRat : ℚ → R
  var : ℕ → R
  isZero : R → Bool
  /-- A sufficient test for equality. -/
  beq : R → R → Bool
  /-- A sufficient test for positivity on a box. -/
  posOn : R → List (ℚ × ℚ) → Bool
  eval : R → (ℕ → ℝ) → ℝ
  eval_add : ∀ a b x, eval (add a b) x = eval a x + eval b x
  eval_mul : ∀ a b x, eval (mul a b) x = eval a x * eval b x
  eval_smul : ∀ c a x, eval (smul c a) x = (c : ℝ) * eval a x
  eval_ofRat : ∀ c x, eval (ofRat c) x = (c : ℝ)
  eval_var : ∀ i, i < nvars → ∀ x, eval (var i) x = x i
  isZero_sound : ∀ a, isZero a = true → ∀ x, eval a x = 0
  beq_sound : ∀ a b, beq a b = true → ∀ x, eval a x = eval b x
  posOn_sound : ∀ a box, posOn a box = true → ∀ x, InBox box x → 0 < eval a x

/-- Rational constants: polynomials in no variables. -/
def ratCoeffs : Coeffs ℚ where
  nvars := 0
  add := (· + ·)
  mul := (· * ·)
  smul := fun c a => c * a
  ofRat := id
  var := fun _ => 0
  isZero := fun a => decide (a = 0)
  beq := fun a b => decide (a = b)
  posOn := fun a _ => decide (0 < a)
  eval := fun a _ => (a : ℝ)
  eval_add := by intro a b x; push_cast; ring
  eval_mul := by intro a b x; push_cast; ring
  eval_smul := by intro c a x; push_cast; ring
  eval_ofRat := by intro c x; rfl
  eval_var := by intro i hi; omega
  isZero_sound := by
    intro a ha x
    have : a = 0 := of_decide_eq_true ha
    simp [this]
  beq_sound := by
    intro a b h x
    have : a = b := of_decide_eq_true h
    rw [this]
  posOn_sound := by
    intro a box ha x _
    have : 0 < a := of_decide_eq_true ha
    exact_mod_cast this

section Operations

variable {R : Type} (C : Coeffs R)

/-- Sum of coefficient lists (lowest degree first). -/
def padd : List R → List R → List R
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => C.add a b :: padd p q

/-- Product of a coefficient list with a coefficient. -/
def pmulc (a : R) (q : List R) : List R := q.map (C.mul a)

/-- Product of a coefficient list with a rational number. -/
def psmul (c : ℚ) (q : List R) : List R := q.map (C.smul c)

/-- Product of coefficient lists. -/
def pmul : List R → List R → List R
  | [], _ => []
  | a :: p, q => padd C (pmulc C a q) (C.ofRat 0 :: pmul p q)

/-- Value at `x` of the polynomial in `x 0` whose coefficients are evaluated at the remaining
coordinates. -/
def peval : List R → (ℕ → ℝ) → ℝ
  | [], _ => 0
  | a :: p, x => C.eval a (tailPt x) + x 0 * peval p x

theorem peval_nil (x : ℕ → ℝ) : peval C [] x = 0 := rfl

theorem peval_cons (a : R) (p : List R) (x : ℕ → ℝ) :
    peval C (a :: p) x = C.eval a (tailPt x) + x 0 * peval C p x := rfl

theorem peval_padd : ∀ (p q : List R) (x : ℕ → ℝ),
    peval C (padd C p q) x = peval C p x + peval C q x
  | [], q, x => by simp [padd, peval]
  | a :: p, [], x => by simp [padd, peval]
  | a :: p, b :: q, x => by
    simp only [padd, peval_cons, C.eval_add, peval_padd p q x]
    ring

theorem peval_pmulc (a : R) : ∀ (q : List R) (x : ℕ → ℝ),
    peval C (pmulc C a q) x = C.eval a (tailPt x) * peval C q x
  | [], x => by simp [pmulc, peval]
  | b :: q, x => by
    have ih := peval_pmulc a q x
    simp only [pmulc, List.map_cons, peval_cons, C.eval_mul] at ih ⊢
    rw [ih]
    ring

theorem peval_psmul (c : ℚ) : ∀ (q : List R) (x : ℕ → ℝ),
    peval C (psmul C c q) x = (c : ℝ) * peval C q x
  | [], x => by simp [psmul, peval]
  | b :: q, x => by
    have ih := peval_psmul c q x
    simp only [psmul, List.map_cons, peval_cons, C.eval_smul] at ih ⊢
    rw [ih]
    ring

theorem peval_pmul : ∀ (p q : List R) (x : ℕ → ℝ),
    peval C (pmul C p q) x = peval C p x * peval C q x
  | [], q, x => by simp [pmul, peval]
  | a :: p, q, x => by
    simp only [pmul, peval_padd, peval_pmulc, peval_cons, C.eval_ofRat, peval_pmul p q x]
    push_cast
    ring

theorem peval_zero_of_all_isZero : ∀ (p : List R), p.all C.isZero = true → ∀ x, peval C p x = 0
  | [], _, x => rfl
  | a :: p, h, x => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [peval_cons, C.isZero_sound a h.1, peval_zero_of_all_isZero p h.2 x]
    ring

/-- Entrywise equality test of coefficient lists of the same length. -/
def pbeq : List R → List R → Bool
  | [], [] => true
  | a :: p, b :: q => C.beq a b && pbeq p q
  | _, _ => false

theorem pbeq_sound : ∀ (p q : List R), pbeq C p q = true → ∀ x, peval C p x = peval C q x
  | [], [], _, _ => rfl
  | a :: p, b :: q, h, x => by
    simp only [pbeq, Bool.and_eq_true] at h
    rw [peval_cons, peval_cons, C.beq_sound a b h.1, pbeq_sound p q h.2 x]
  | [], _ :: _, h, _ => by simp [pbeq] at h
  | _ :: _, [], h, _ => by simp [pbeq] at h

end Operations

end Cycle63.Certificate

end Record1252270103Bootstrap.PR67

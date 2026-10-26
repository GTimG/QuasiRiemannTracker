import Mathlib.Tactic

/-!
# Computable polynomials over `ℚ` for uniform certificates

A polynomial is its coefficient list, lowest degree first. Every operation is computable, so a
certificate about a whole family of rational parameters is checked by `decide +kernel`, and `eval`
commutes with every operation.

Positivity on an interval uses a first-order Taylor test (`tm1`): on `[a, a + h]` write
`p (a + t) = c₀ + c₁ t + t² r(t)`; if `h² Σ_{k} |r_k| h^k < min c₀ (c₀ + c₁ h)` then `p > 0` there.
-/

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless

abbrev Poly := List ℚ

namespace Poly

def eval : Poly → ℚ → ℚ
  | [], _ => 0
  | c :: cs, x => c + x * eval cs x

def add : Poly → Poly → Poly
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

def smul (c : ℚ) (p : Poly) : Poly := p.map (c * ·)

def mul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => add (smul a q) (0 :: mul p q)

def sub (p q : Poly) : Poly := add p (smul (-1) q)

def pow (p : Poly) : ℕ → Poly
  | 0 => [1]
  | n + 1 => mul p (pow p n)

/-- Drop trailing zero coefficients. -/
def trim : Poly → Poly
  | [] => []
  | c :: cs => if (trim cs).isEmpty && c == 0 then [] else c :: trim cs

/-- The coefficients of `t ↦ p (a + t)`. -/
def shift (p : Poly) (a : ℚ) : Poly := p.foldr (fun c acc => add [c] (mul [a, 1] acc)) []

@[simp] theorem eval_nil (x : ℚ) : eval [] x = 0 := rfl
@[simp] theorem eval_cons (c : ℚ) (cs : Poly) (x : ℚ) : eval (c :: cs) x = c + x * eval cs x := rfl

@[simp] theorem eval_add (p q : Poly) (x : ℚ) : eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih]; ring

@[simp] theorem eval_smul (c : ℚ) (p : Poly) (x : ℚ) : eval (smul c p) x = c * eval p x := by
  induction p with
  | nil => simp [smul]
  | cons a p ih =>
    simp only [smul, List.map_cons, eval_cons] at ih ⊢
    rw [ih]; ring

@[simp] theorem eval_mul (p q : Poly) (x : ℚ) : eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih => simp [mul, ih]; ring

@[simp] theorem eval_sub (p q : Poly) (x : ℚ) : eval (sub p q) x = eval p x - eval q x := by
  simp [sub]; ring

@[simp] theorem eval_pow (p : Poly) (n : ℕ) (x : ℚ) : eval (pow p n) x = eval p x ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow, ih]; ring

@[simp] theorem eval_trim (p : Poly) (x : ℚ) : eval (trim p) x = eval p x := by
  induction p with
  | nil => simp [trim]
  | cons c cs ih =>
    simp only [trim]
    split_ifs with h
    · simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
      obtain ⟨h1, h2⟩ := h
      rw [eval_cons, ← ih, h1, h2]; simp
    · rw [eval_cons, eval_cons, ih]

@[simp] theorem eval_shift (p : Poly) (a t : ℚ) : eval (shift p a) t = eval p (a + t) := by
  induction p with
  | nil => simp [shift]
  | cons c p ih =>
    have : shift (c :: p) a = add [c] (mul [a, 1] (shift p a)) := rfl
    rw [this, eval_add, eval_mul, ih]
    simp

/-! ## The first-order Taylor test -/

end Poly

end QRH.RepeatedMarks.Faceless

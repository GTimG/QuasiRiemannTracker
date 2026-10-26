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

def C (c : ℚ) : Poly := [c]

def X : Poly := [0, 1]

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

@[simp] theorem eval_C (c x : ℚ) : eval (C c) x = c := by simp [C]

@[simp] theorem eval_X (x : ℚ) : eval X x = x := by simp [X]

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

/-- `Σ_k |c_k| h^k`. -/
def absSum : Poly → ℚ → ℚ
  | [], _ => 0
  | c :: cs, h => |c| + h * absSum cs h

theorem absSum_nonneg (p : Poly) {h : ℚ} (hh : 0 ≤ h) : 0 ≤ absSum p h := by
  induction p with
  | nil => simp [absSum]
  | cons c p ih => simp only [absSum]; positivity

theorem abs_eval_le (p : Poly) {h t : ℚ} (ht0 : 0 ≤ t) (hth : t ≤ h) :
    |eval p t| ≤ absSum p h := by
  induction p with
  | nil => simp [absSum]
  | cons c p ih =>
    simp only [eval_cons, absSum]
    have h0 : 0 ≤ h := ht0.trans hth
    have hs := absSum_nonneg p h0
    calc |c + t * eval p t| ≤ |c| + |t * eval p t| := abs_add_le _ _
      _ = |c| + t * |eval p t| := by rw [abs_mul, abs_of_nonneg ht0]
      _ ≤ |c| + h * absSum p h := by
          have := mul_le_mul hth ih (abs_nonneg _) h0
          linarith

/-- First-order Taylor test of `p > 0` on `[a, a + h]`. -/
def tm1 (p : Poly) (a h : ℚ) : Bool :=
  match shift p a with
  | [] => false
  | [c₀] => decide (0 < c₀)
  | c₀ :: c₁ :: cs => decide (h ^ 2 * absSum cs h < min c₀ (c₀ + c₁ * h))

theorem tm1_sound (p : Poly) (a h : ℚ) (hc : tm1 p a h = true) :
    ∀ x : ℚ, a ≤ x → x ≤ a + h → 0 < eval p x := by
  intro x hx0 hx1
  have ht0 : 0 ≤ x - a := by linarith
  have hth : x - a ≤ h := by linarith
  have hx : eval p x = eval (shift p a) (x - a) := by rw [eval_shift]; ring_nf
  rw [hx]
  unfold tm1 at hc
  generalize shift p a = c at hc ⊢
  match c, hc with
  | [c₀], hc =>
    simp only [decide_eq_true_eq] at hc
    simpa using hc
  | c₀ :: c₁ :: cs, hc =>
    simp only [decide_eq_true_eq] at hc
    have hb := abs_eval_le cs ht0 hth
    have hlin : min c₀ (c₀ + c₁ * h) ≤ c₀ + c₁ * (x - a) := by
      rcases le_total 0 c₁ with h1 | h1
      · exact (min_le_left _ _).trans (by nlinarith)
      · exact (min_le_right _ _).trans (by nlinarith)
    have hsq : (x - a) ^ 2 * |eval cs (x - a)| ≤ h ^ 2 * absSum cs h := by
      apply mul_le_mul (pow_le_pow_left₀ ht0 hth 2) hb (abs_nonneg _) (by positivity)
    have hlow : -((x - a) ^ 2 * |eval cs (x - a)|) ≤ (x - a) ^ 2 * eval cs (x - a) := by
      have := neg_abs_le (eval cs (x - a))
      nlinarith [sq_nonneg (x - a)]
    simp only [eval_cons]
    nlinarith

/-- `p > 0` on `[a, b]`, checked on the consecutive intervals of the breakpoint list `a :: bs`. -/
def posOn (p : Poly) : ℚ → List ℚ → Bool
  | _, [] => true
  | a, b :: bs => decide (a ≤ b) && tm1 p a (b - a) && posOn p b bs

/-- The right end of a breakpoint list. -/
def lastPt : ℚ → List ℚ → ℚ
  | a, [] => a
  | _, b :: bs => lastPt b bs

theorem posOn_sound (p : Poly) : ∀ (a : ℚ) (bs : List ℚ), posOn p a bs = true →
    ∀ x : ℚ, a ≤ x → x ≤ lastPt a bs → bs ≠ [] → 0 < eval p x := by
  intro a bs
  induction bs generalizing a with
  | nil => intro _ x _ _ h; exact absurd rfl h
  | cons b bs ih =>
    intro hc x hx0 hx1 _
    simp only [posOn, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hab, htm⟩, hrest⟩ := hc
    rcases le_total x b with hxb | hxb
    · exact tm1_sound p a (b - a) htm x hx0 (by linarith)
    · cases bs with
      | nil =>
        have : x = b := le_antisymm (by simpa [lastPt] using hx1) hxb
        exact tm1_sound p a (b - a) htm x hx0 (by linarith)
      | cons c cs =>
        exact ih b hrest x hxb (by simpa [lastPt] using hx1) (by simp)

end Poly

end QRH.RepeatedMarks.Faceless

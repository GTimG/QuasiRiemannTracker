/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.PositiveGap.Return.Tuning.CoverQ

/-!
# A discriminant certificate at the contact

Bisection near a quadratic minimum needs depth proportional to the logarithm of the inverse
margin. The top-edge row of the count face has degree two in `δ`, so that minimum can be certified
exactly. Dividing the row by `p - 1/2` gives `P(δ, p) = R(δ) + (p - 1/2) Q(δ, p)`. A negative
discriminant makes `R` positive for every real `δ`, and one Bernstein check gives `Q < 0` on the
box, so `P > 0` for `p ≤ 1/2`. The number of operations does not depend on the margin.
-/

set_option autoImplicit false

namespace QRH.PositiveGap.ReturnTuning

open QRH.PositiveGap.Return QRH.ArviReturnTuning

/-- Horner evaluation at a rational point. -/
def evalQ : Q1 → ℚ → ℚ
  | [], _ => 0
  | c :: cs, a => c + a * evalQ cs a

/-- The quotient of `r(p) - r(a)` by `p - a`. -/
def divQ : Q1 → ℚ → Q1
  | [], _ => []
  | _ :: cs, a => Q1.add cs (Q1.smul a (divQ cs a))

theorem ev_divQ (r : Q1) (a : ℚ) (p : ℝ) :
    Q1.ev r p = (evalQ r a : ℝ) + (p - a) * Q1.ev (divQ r a) p := by
  induction r with
  | nil => simp [evalQ, divQ]
  | cons c cs ih =>
    simp only [Q1.ev_cons, evalQ, divQ, Q1.ev_add, Q1.ev_smul]
    push_cast
    rw [ih]
    ring

/-- The row of each power of `δ`, evaluated at `p = a`. -/
def headsQ (P : Q2) (a : ℚ) : Q1 := P.map (evalQ · a)

/-- The quotient of each row by `p - a`. -/
def quotQ (P : Q2) (a : ℚ) : Q2 := P.map (divQ · a)

theorem ev_split (P : Q2) (a : ℚ) (d p : ℝ) :
    Q2.ev P d p = Q1.ev (headsQ P a) d + (p - a) * Q2.ev (quotQ P a) d p := by
  induction P with
  | nil => simp [headsQ, quotQ]
  | cons r P ih =>
    simp only [headsQ, quotQ, List.map_cons, Q2.ev_cons, Q1.ev_cons] at ih ⊢
    rw [ev_divQ r a p, ih]
    ring

/-- A quadratic with positive leading coefficient and negative discriminant. -/
def quadPos : Q1 → Bool
  | a₀ :: a₁ :: a₂ :: rest =>
    decide (0 < a₂) && decide (a₁ * a₁ < 4 * a₀ * a₂) && Q1.isZero rest
  | _ => false

theorem quadPos_sound (R : Q1) (h : quadPos R = true) (d : ℝ) : 0 < Q1.ev R d := by
  match R, h with
  | a₀ :: a₁ :: a₂ :: rest, h =>
    simp only [quadPos, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h2, hd⟩, hz⟩ := h
    have h2' : (0 : ℝ) < a₂ := by exact_mod_cast h2
    have hd' : (a₁ : ℝ) * a₁ < 4 * a₀ * a₂ := by exact_mod_cast hd
    simp only [Q1.ev_cons, Q1.ev_of_isZero rest hz, mul_zero, add_zero]
    have key : 0 < (4 * (a₂ : ℝ)) * ((a₀ : ℝ) + d * ((a₁ : ℝ) + d * a₂)) := by
      nlinarith [sq_nonneg (2 * (a₂ : ℝ) * d + a₁)]
    exact (pos_iff_pos_of_mul_pos key).mp (by positivity)
  | [], h => simp [quadPos] at h
  | [_], h => simp [quadPos] at h
  | [_, _], h => simp [quadPos] at h

/-- The contact check of `P` on `[a, b] × [c, 1/2]`. -/
def contactOK (P : Q2) (a b c : ℚ) : Bool :=
  quadPos (headsQ P (1 / 2)) && bernCheck (Q2.smul (-1) (quotQ P (1 / 2))) a b c (1 / 2)

theorem contactOK_sound (P : Q2) (a b c : ℚ) (h : contactOK P a b c = true) {d p : ℝ}
    (hd0 : (a : ℝ) ≤ d) (hd1 : d ≤ b) (hp0 : (c : ℝ) ≤ p) (hp1 : p ≤ 1 / 2) : 0 < Q2.ev P d p := by
  simp only [contactOK, Bool.and_eq_true] at h
  have hR := quadPos_sound _ h.1 d
  have hQ := bernCheck_sound _ a b c (1 / 2) h.2 hd0 hd1 hp0 (by simpa using hp1)
  rw [Q2.ev_smul] at hQ
  rw [ev_split P (1 / 2) d p]
  push_cast at hQ ⊢
  have hw : 0 ≤ ((1 : ℝ) / 2 - p) * (-(Q2.ev (quotQ P (1 / 2)) d p)) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- A box of one window whose row passes the contact check satisfies the edge inequality. -/
theorem contact_row (e : Edge) (ws : List WinQ) (env : ℝ → ℝ → ℝ)
    (hwin : ∀ w ∈ ws, w.branch ≠ .old → ∀ δ p, δ ∈ Set.Icc (w.dlo : ℝ) w.dhi →
      p ∈ Set.Icc (w.plo : ℝ) (1 / 2) → env δ p ≤ countN w.branch δ p / countJ w.branch δ p)
    (w : WinQ) (hw : w ∈ ws) (hb : w.branch ≠ .old) (a b c : ℚ) (ha : w.dlo ≤ a) (hbd : b ≤ w.dhi)
    (hc : w.plo ≤ c) (h : contactOK (rowBrQ e (toQ w.branch)) a b c = true) {δ p : ℝ}
    (hd0 : (a : ℝ) ≤ δ) (hd1 : δ ≤ b) (hp0 : (c : ℝ) ≤ p) (hδ : δ ∈ Set.Icc (0 : ℝ) (3 / 4))
    (hp : p ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    Ebase (edgeD e) (edgeC e) δ p + 3 / 4 * edgeD e * env δ p < theta - reserve := by
  have hF : 0 < rowMargin e w.branch δ p := by
    rw [← ev_rowBrQ δ p e w.branch hb]
    exact contactOK_sound _ a b c h hd0 hd1 hp0 hp.2
  have ha' : (w.dlo : ℝ) ≤ a := by exact_mod_cast ha
  have hbd' : (b : ℝ) ≤ w.dhi := by exact_mod_cast hbd
  have hc' : (w.plo : ℝ) ≤ c := by exact_mod_cast hc
  exact exponent_lt_of_margin (countJ_pos w.branch hδ hp) hF
    (hwin w hw hb δ p ⟨ha'.trans hd0, hd1.trans hbd'⟩ ⟨hc'.trans hp0, hp.2⟩)

end QRH.PositiveGap.ReturnTuning

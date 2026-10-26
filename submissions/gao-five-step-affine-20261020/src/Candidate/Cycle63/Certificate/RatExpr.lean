/- Rational functions as expression trees, their numerator and denominator polynomials, and a
positivity test on boxes that the kernel evaluates. Released under Apache 2.0. -/
import Candidate.Cycle63.Certificate.Bernstein
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace Cycle63.Certificate

/-- Expressions built from rational constants, variables and the field operations. -/
inductive RatExpr where
  | const : ℚ → RatExpr
  | var : ℕ → RatExpr
  | add : RatExpr → RatExpr → RatExpr
  | sub : RatExpr → RatExpr → RatExpr
  | mul : RatExpr → RatExpr → RatExpr
  | div : RatExpr → RatExpr → RatExpr
  | neg : RatExpr → RatExpr
  | pow : RatExpr → ℕ → RatExpr

namespace RatExpr

/-- The real value at the point `x` (division by zero is zero, as in `ℝ`). -/
noncomputable def denote : RatExpr → (ℕ → ℝ) → ℝ
  | const c, _ => (c : ℝ)
  | var i, x => x i
  | add a b, x => denote a x + denote b x
  | sub a b, x => denote a x - denote b x
  | mul a b, x => denote a x * denote b x
  | div a b, x => denote a x / denote b x
  | neg a, x => -denote a x
  | pow a n, x => denote a x ^ n

/-- Every variable index is below `k`. -/
def varsLt (k : ℕ) : RatExpr → Bool
  | const _ => true
  | var i => decide (i < k)
  | add a b => varsLt k a && varsLt k b
  | sub a b => varsLt k a && varsLt k b
  | mul a b => varsLt k a && varsLt k b
  | div a b => varsLt k a && varsLt k b
  | neg a => varsLt k a
  | pow a _ => varsLt k a

section Fractions

variable {R : Type} (C : Coeffs R)

/-- `r ^ n` in the coefficient arithmetic. -/
def cpow (r : R) : ℕ → R
  | 0 => C.ofRat 1
  | n + 1 => C.mul r (cpow r n)

theorem eval_cpow (r : R) (x : ℕ → ℝ) : ∀ n : ℕ, C.eval (cpow C r n) x = C.eval r x ^ n
  | 0 => by simp [cpow, C.eval_ofRat]
  | n + 1 => by rw [cpow, C.eval_mul, eval_cpow r x n, pow_succ]; ring

/-- A fraction: numerator, denominator, and the denominators of divisors, which must not vanish. -/
structure Frac (R : Type) where
  num : R
  den : R
  sides : List R

/-- Sum of fractions (a common denominator is kept). -/
def fracAdd (p q : Frac R) : Frac R :=
  bif C.beq p.den q.den then ⟨C.add p.num q.num, p.den, p.sides ++ q.sides⟩
  else ⟨C.add (C.mul p.num q.den) (C.mul q.num p.den), C.mul p.den q.den, p.sides ++ q.sides⟩

/-- Difference of fractions. -/
def fracSub (p q : Frac R) : Frac R :=
  bif C.beq p.den q.den then ⟨C.add p.num (C.smul (-1) q.num), p.den, p.sides ++ q.sides⟩
  else ⟨C.add (C.mul p.num q.den) (C.smul (-1) (C.mul q.num p.den)), C.mul p.den q.den,
    p.sides ++ q.sides⟩

/-- Product of fractions. -/
def fracMul (p q : Frac R) : Frac R := ⟨C.mul p.num q.num, C.mul p.den q.den, p.sides ++ q.sides⟩

/-- Quotient of fractions; the divisor's denominator becomes a side condition. -/
def fracDiv (p q : Frac R) : Frac R :=
  bif C.beq p.den q.den then ⟨p.num, q.num, q.den :: (p.sides ++ q.sides)⟩
  else ⟨C.mul p.num q.den, C.mul p.den q.num, q.den :: (p.sides ++ q.sides)⟩

/-- Numerator, denominator and side conditions of an expression. -/
def toFrac : RatExpr → Frac R
  | const c => ⟨C.ofRat c, C.ofRat 1, []⟩
  | var i => ⟨C.var i, C.ofRat 1, []⟩
  | add a b => fracAdd C (toFrac a) (toFrac b)
  | sub a b => fracSub C (toFrac a) (toFrac b)
  | mul a b => fracMul C (toFrac a) (toFrac b)
  | div a b => fracDiv C (toFrac a) (toFrac b)
  | neg a => ⟨C.smul (-1) (toFrac a).num, (toFrac a).den, (toFrac a).sides⟩
  | pow a n => ⟨cpow C (toFrac a).num n, cpow C (toFrac a).den n, (toFrac a).sides⟩

theorem toFrac_sound : ∀ (e : RatExpr) (x : ℕ → ℝ), e.varsLt C.nvars = true →
    (∀ s ∈ (e.toFrac C).sides, C.eval s x ≠ 0) → C.eval (e.toFrac C).den x ≠ 0 →
      e.denote x = C.eval (e.toFrac C).num x / C.eval (e.toFrac C).den x
  | const c, x, _, _, _ => by simp [denote, toFrac, C.eval_ofRat]
  | var i, x, hv, _, _ => by
    simp only [varsLt, decide_eq_true_eq] at hv
    simp [denote, toFrac, C.eval_ofRat, C.eval_var i hv]
  | add a b, x, hv, hs, hd => by
    simp only [varsLt, Bool.and_eq_true] at hv
    have hsa : ∀ s ∈ (a.toFrac C).sides, C.eval s x ≠ 0 := fun s h' => hs s (by
      simp only [toFrac, fracAdd]; cases C.beq (a.toFrac C).den (b.toFrac C).den <;>
        simp [h'])
    have hsb : ∀ s ∈ (b.toFrac C).sides, C.eval s x ≠ 0 := fun s h' => hs s (by
      simp only [toFrac, fracAdd]; cases C.beq (a.toFrac C).den (b.toFrac C).den <;>
        simp [h'])
    simp only [toFrac, fracAdd] at hd ⊢
    rw [denote]
    cases hb : C.beq (a.toFrac C).den (b.toFrac C).den
    · simp only [hb, Bool.cond_false, C.eval_mul, C.eval_add] at hd ⊢
      have ha : C.eval (a.toFrac C).den x ≠ 0 := left_ne_zero_of_mul hd
      have hb' : C.eval (b.toFrac C).den x ≠ 0 := right_ne_zero_of_mul hd
      rw [toFrac_sound a x hv.1 hsa ha, toFrac_sound b x hv.2 hsb hb']
      field_simp
    · simp only [hb, Bool.cond_true, C.eval_add] at hd ⊢
      have he := C.beq_sound _ _ hb x
      have hb' : C.eval (b.toFrac C).den x ≠ 0 := by rw [← he]; exact hd
      rw [toFrac_sound a x hv.1 hsa hd, toFrac_sound b x hv.2 hsb hb', ← he]
      field_simp
  | sub a b, x, hv, hs, hd => by
    simp only [varsLt, Bool.and_eq_true] at hv
    have hsa : ∀ s ∈ (a.toFrac C).sides, C.eval s x ≠ 0 := fun s h' => hs s (by
      simp only [toFrac, fracSub]; cases C.beq (a.toFrac C).den (b.toFrac C).den <;>
        simp [h'])
    have hsb : ∀ s ∈ (b.toFrac C).sides, C.eval s x ≠ 0 := fun s h' => hs s (by
      simp only [toFrac, fracSub]; cases C.beq (a.toFrac C).den (b.toFrac C).den <;>
        simp [h'])
    simp only [toFrac, fracSub] at hd ⊢
    rw [denote]
    cases hb : C.beq (a.toFrac C).den (b.toFrac C).den
    · simp only [hb, Bool.cond_false, C.eval_mul, C.eval_add, C.eval_smul] at hd ⊢
      have ha : C.eval (a.toFrac C).den x ≠ 0 := left_ne_zero_of_mul hd
      have hb' : C.eval (b.toFrac C).den x ≠ 0 := right_ne_zero_of_mul hd
      rw [toFrac_sound a x hv.1 hsa ha, toFrac_sound b x hv.2 hsb hb']
      field_simp
      push_cast
      ring
    · simp only [hb, Bool.cond_true, C.eval_add, C.eval_smul] at hd ⊢
      have he := C.beq_sound _ _ hb x
      have hb' : C.eval (b.toFrac C).den x ≠ 0 := by rw [← he]; exact hd
      rw [toFrac_sound a x hv.1 hsa hd, toFrac_sound b x hv.2 hsb hb', ← he]
      field_simp
      push_cast
      ring
  | mul a b, x, hv, hs, hd => by
    simp only [varsLt, Bool.and_eq_true] at hv
    simp only [toFrac, fracMul, C.eval_mul, List.mem_append] at hd hs ⊢
    have ha : C.eval (a.toFrac C).den x ≠ 0 := left_ne_zero_of_mul hd
    have hb : C.eval (b.toFrac C).den x ≠ 0 := right_ne_zero_of_mul hd
    rw [denote, toFrac_sound a x hv.1 (fun s h' => hs s (Or.inl h')) ha,
      toFrac_sound b x hv.2 (fun s h' => hs s (Or.inr h')) hb]
    field_simp
  | div a b, x, hv, hs, hd => by
    simp only [varsLt, Bool.and_eq_true] at hv
    have hsa : ∀ s ∈ (a.toFrac C).sides, C.eval s x ≠ 0 := fun s h' => hs s (by
      simp only [toFrac, fracDiv]; cases C.beq (a.toFrac C).den (b.toFrac C).den <;>
        simp [h'])
    have hsb : ∀ s ∈ (b.toFrac C).sides, C.eval s x ≠ 0 := fun s h' => hs s (by
      simp only [toFrac, fracDiv]; cases C.beq (a.toFrac C).den (b.toFrac C).den <;>
        simp [h'])
    have hbd : C.eval (b.toFrac C).den x ≠ 0 := hs _ (by
      simp only [toFrac, fracDiv]; cases C.beq (a.toFrac C).den (b.toFrac C).den <;> simp)
    simp only [toFrac, fracDiv] at hd ⊢
    rw [denote]
    cases hb : C.beq (a.toFrac C).den (b.toFrac C).den
    · simp only [hb, Bool.cond_false, C.eval_mul] at hd ⊢
      have ha : C.eval (a.toFrac C).den x ≠ 0 := left_ne_zero_of_mul hd
      have hbn : C.eval (b.toFrac C).num x ≠ 0 := right_ne_zero_of_mul hd
      rw [toFrac_sound a x hv.1 hsa ha, toFrac_sound b x hv.2 hsb hbd]
      field_simp
    · simp only [hb, Bool.cond_true] at hd ⊢
      have he := C.beq_sound _ _ hb x
      have ha : C.eval (a.toFrac C).den x ≠ 0 := by rw [he]; exact hbd
      rw [toFrac_sound a x hv.1 hsa ha, toFrac_sound b x hv.2 hsb hbd, he]
      field_simp
  | neg a, x, hv, hs, hd => by
    simp only [varsLt] at hv
    simp only [toFrac, C.eval_smul] at hd hs ⊢
    rw [denote, toFrac_sound a x hv hs hd]
    push_cast
    ring
  | pow a n, x, hv, hs, hd => by
    simp only [varsLt] at hv
    simp only [toFrac, eval_cpow] at hd hs ⊢
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [denote]
    · have ha : C.eval (a.toFrac C).den x ≠ 0 := by
        intro h0; apply hd; rw [h0, zero_pow hn.ne']
      rw [denote, toFrac_sound a x hv hs ha, div_pow]

/-- A strict sign test on a box. -/
def signOn (r : R) (box : List (ℚ × ℚ)) (d : ℕ) : Bool :=
  posOnSplit C r box d || posOnSplit C (C.smul (-1) r) box d

theorem signOn_sound (r : R) (box : List (ℚ × ℚ)) (d : ℕ) (h : signOn C r box d = true)
    (x : ℕ → ℝ) (hx : InBox box x) : C.eval r x ≠ 0 := by
  simp only [signOn, Bool.or_eq_true] at h
  rcases h with h | h
  · exact (posOnSplit_sound C r box d h x hx).ne'
  · have := posOnSplit_sound C _ box d h x hx
    rw [C.eval_smul] at this
    push_cast at this
    linarith

/-- The side conditions that need a sign test: constant `1` and repeated entries are dropped. -/
def distinctSides : List R → List R
  | [] => []
  | s :: l =>
    bif C.beq s (C.ofRat 1) || (distinctSides l).any (C.beq s) then distinctSides l
    else s :: distinctSides l

/-- Every dropped side condition is the constant `1` or equal to a kept one. -/
theorem distinctSides_cover (x : ℕ → ℝ) : ∀ (l : List R) (s : R), s ∈ l →
    C.eval s x = 1 ∨ ∃ s' ∈ distinctSides C l, C.eval s x = C.eval s' x
  | [], s, hs => absurd hs List.not_mem_nil
  | t :: l, s, hs => by
    rcases List.mem_cons.mp hs with rfl | hs
    · cases hb : C.beq s (C.ofRat 1)
      · cases ha : (distinctSides C l).any (C.beq s)
        · right
          exact ⟨s, by simp [distinctSides, hb, ha], rfl⟩
        · obtain ⟨s', hs', hbeq⟩ := List.any_eq_true.mp ha
          right
          exact ⟨s', by simp [distinctSides, hb, ha, hs'], C.beq_sound _ _ hbeq x⟩
      · left
        rw [C.beq_sound _ _ hb x, C.eval_ofRat]
        simp
    · rcases distinctSides_cover x l s hs with h | ⟨s', hs', heq⟩
      · exact Or.inl h
      · right
        refine ⟨s', ?_, heq⟩
        simp only [distinctSides]
        cases C.beq t (C.ofRat 1) || (distinctSides C l).any (C.beq t) <;> simp [hs']

/-- Positivity test of a fraction on a box: the distinct side conditions have strict signs, and
numerator and denominator have the same strict sign. -/
def fracPos (f : Frac R) (box : List (ℚ × ℚ)) (d : ℕ) : Bool :=
  (distinctSides C f.sides).all (fun s => signOn C s box d) &&
    ((posOnSplit C f.num box d && posOnSplit C f.den box d) ||
      (posOnSplit C (C.smul (-1) f.num) box d && posOnSplit C (C.smul (-1) f.den) box d))

end Fractions

/-- Positivity test of an expression on a box, with bisection down to depth `d`. -/
def ratPos {R : Type} (C : Coeffs R) (e : RatExpr) (box : List (ℚ × ℚ)) (d : ℕ) : Bool :=
  e.varsLt C.nvars && fracPos C (e.toFrac C) box d

theorem ratPos_sound {R : Type} (C : Coeffs R) (e : RatExpr) (box : List (ℚ × ℚ)) (d : ℕ)
    (h : ratPos C e box d = true) (x : ℕ → ℝ) (hx : InBox box x) : 0 < e.denote x := by
  simp only [ratPos, fracPos, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at h
  obtain ⟨hv, hs, h⟩ := h
  have hs' : ∀ s ∈ (e.toFrac C).sides, C.eval s x ≠ 0 := by
    intro s h'
    rcases distinctSides_cover C x _ s h' with h1 | ⟨s', hs'', heq⟩
    · rw [h1]; exact one_ne_zero
    · rw [heq]; exact signOn_sound C s' box d (hs s' hs'') x hx
  rcases h with ⟨hn, hd⟩ | ⟨hn, hd⟩
  · have hN := posOnSplit_sound C _ box d hn x hx
    have hD := posOnSplit_sound C _ box d hd x hx
    rw [toFrac_sound C e x hv hs' hD.ne']
    exact div_pos hN hD
  · have hN := posOnSplit_sound C _ box d hn x hx
    have hD := posOnSplit_sound C _ box d hd x hx
    rw [C.eval_smul] at hN hD
    push_cast at hN hD
    have hD' : C.eval (e.toFrac C).den x < 0 := by linarith
    rw [toFrac_sound C e x hv hs' hD'.ne]
    exact div_pos_of_neg_of_neg (by linarith) hD'

/-- Every expression of the list is nonnegative at `x`. -/
def AllNonneg : List RatExpr → (ℕ → ℝ) → Prop
  | [], _ => True
  | c :: cs, x => 0 ≤ c.denote x ∧ AllNonneg cs x

/-- The test of one sub-box: the expression is positive on it, or some constraint is negative on
it. -/
def ratPosOrRefuted {R : Type} (C : Coeffs R) (cs : List RatExpr) (e : RatExpr)
    (box : List (ℚ × ℚ)) (d : ℕ) : Bool :=
  ratPos C e box d || cs.any (fun c => ratPos C c.neg box d)

/-- Positivity of an expression on the part of a box where the constraints are nonnegative: the
box is bisected along its widest side up to depth `n`, and each sub-box passes `ratPosOrRefuted`
with polynomial bisection up to depth `d`. -/
def ratPosOn {R : Type} (C : Coeffs R) (cs : List RatExpr) (e : RatExpr) :
    List (ℚ × ℚ) → ℕ → ℕ → Bool
  | box, d, 0 => ratPosOrRefuted C cs e box d
  | box, d, n + 1 => ratPosOrRefuted C cs e box d ||
      (ratPosOn C cs e (splitBox box (widestIndex box)).1 d n &&
        ratPosOn C cs e (splitBox box (widestIndex box)).2 d n)

theorem allNonneg_of_mem {cs : List RatExpr} {x : ℕ → ℝ} (h : AllNonneg cs x) :
    ∀ c ∈ cs, 0 ≤ c.denote x := by
  induction cs with
  | nil => intro c hc; simp at hc
  | cons c cs ih =>
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact h.1
    · exact ih h.2 c' hc'

theorem ratPosOrRefuted_sound {R : Type} (C : Coeffs R) (cs : List RatExpr) (e : RatExpr)
    (box : List (ℚ × ℚ)) (d : ℕ) (h : ratPosOrRefuted C cs e box d = true) (x : ℕ → ℝ)
    (hx : InBox box x) (hc : AllNonneg cs x) : 0 < e.denote x := by
  simp only [ratPosOrRefuted, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨c, hcm, h⟩
  · exact ratPos_sound C e box d h x hx
  · have hneg := ratPos_sound C c.neg box d h x hx
    have hnn := allNonneg_of_mem hc c hcm
    simp only [denote] at hneg
    linarith

theorem ratPosOn_sound {R : Type} (C : Coeffs R) (cs : List RatExpr) (e : RatExpr) (d : ℕ) :
    ∀ (n : ℕ) (box : List (ℚ × ℚ)), ratPosOn C cs e box d n = true →
      ∀ x, InBox box x → AllNonneg cs x → 0 < e.denote x
  | 0, box, h, x, hx, hc => ratPosOrRefuted_sound C cs e box d h x hx hc
  | n + 1, box, h, x, hx, hc => by
    simp only [ratPosOn, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact ratPosOrRefuted_sound C cs e box d h x hx hc
    · rcases inBox_splitBox box (widestIndex box) x hx with hx' | hx'
      · exact ratPosOn_sound C cs e d n _ h1 x hx' hc
      · exact ratPosOn_sound C cs e d n _ h2 x hx' hc

/-- The point whose coordinates are the entries of a list (and `0` beyond it). -/
def ptOfList (vs : List ℝ) : ℕ → ℝ := fun i => vs.getD i 0

/-- The form used by the `rat_pos` tactic. -/
theorem lt_of_ratPos {R : Type} (C : Coeffs R) (e : RatExpr) (box : List (ℚ × ℚ)) (d : ℕ)
    (h : ratPos C e box d = true) (x : ℕ → ℝ) (hx : InBox box x) {a b : ℝ}
    (he : e.denote x = b - a) : a < b := by
  have := ratPos_sound C e box d h x hx
  linarith

/-- The form used by the `rat_pos` tactic with constraint hypotheses. -/
theorem lt_of_ratPosOn {R : Type} (C : Coeffs R) (cs : List RatExpr) (e : RatExpr)
    (box : List (ℚ × ℚ)) (d n : ℕ) (h : ratPosOn C cs e box d n = true) (x : ℕ → ℝ)
    (hx : InBox box x) (hc : AllNonneg cs x) {a b : ℝ} (he : e.denote x = b - a) : a < b := by
  have := ratPosOn_sound C cs e d n box h x hx hc
  linarith

end RatExpr

end Cycle63.Certificate

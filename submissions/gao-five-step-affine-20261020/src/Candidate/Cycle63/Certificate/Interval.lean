/- Rational enclosures of real expressions built from numerals, rational constants, variables with
known enclosures, the field operations, natural powers, square roots, `min` and `max`, by interval
arithmetic with outward rounding to dyadic rationals, evaluated by the kernel.
Released under Apache 2.0. -/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

set_option autoImplicit false

namespace Cycle63.Certificate

/-- Real expressions: natural numerals, rational constants, variables, the field operations,
natural powers, square roots, `min` and `max`. -/
inductive CExpr where
  | nat : ℕ → CExpr
  | rat : ℚ → CExpr
  | var : ℕ → CExpr
  | add : CExpr → CExpr → CExpr
  | sub : CExpr → CExpr → CExpr
  | mul : CExpr → CExpr → CExpr
  | div : CExpr → CExpr → CExpr
  | neg : CExpr → CExpr
  | pow : CExpr → ℕ → CExpr
  | sqrt : CExpr → CExpr
  | min : CExpr → CExpr → CExpr
  | max : CExpr → CExpr → CExpr

namespace CExpr

/-- The real value at the point `x` (division by zero is zero, as in `ℝ`). -/
noncomputable def denote (x : ℕ → ℝ) : CExpr → ℝ
  | nat n => (n : ℝ)
  | rat q => (q : ℝ)
  | var i => x i
  | add a b => denote x a + denote x b
  | sub a b => denote x a - denote x b
  | mul a b => denote x a * denote x b
  | div a b => denote x a / denote x b
  | neg a => -denote x a
  | pow a n => denote x a ^ n
  | sqrt a => Real.sqrt (denote x a)
  | min a b => Min.min (denote x a) (denote x b)
  | max a b => Max.max (denote x a) (denote x b)

end CExpr

/-- The closed interval `[lo, hi]` with rational ends. -/
structure QInterval where
  lo : ℚ
  hi : ℚ

namespace QInterval

/-- The interval contains the real number `x`. -/
def Mem (I : QInterval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- The one-point interval. -/
def point (q : ℚ) : QInterval := ⟨q, q⟩

/-- Interval sum. -/
def add (I J : QInterval) : QInterval := ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- Interval difference. -/
def sub (I J : QInterval) : QInterval := ⟨I.lo - J.hi, I.hi - J.lo⟩

/-- Interval negation. -/
def neg (I : QInterval) : QInterval := ⟨-I.hi, -I.lo⟩

/-- Interval product: the smallest and largest of the four corner products. -/
def mul (I J : QInterval) : QInterval :=
  ⟨Min.min (Min.min (I.lo * J.lo) (I.lo * J.hi)) (Min.min (I.hi * J.lo) (I.hi * J.hi)),
   Max.max (Max.max (I.lo * J.lo) (I.lo * J.hi)) (Max.max (I.hi * J.lo) (I.hi * J.hi))⟩

/-- The reciprocal interval, when the interval does not contain zero. -/
def inv? (I : QInterval) : Option QInterval :=
  if 0 < I.lo ∨ I.hi < 0 then some ⟨1 / I.hi, 1 / I.lo⟩ else none

/-- Interval power, by repeated products. -/
def pow (I : QInterval) : ℕ → QInterval
  | 0 => point 1
  | n + 1 => mul I (pow I n)

/-- Interval minimum. -/
def min (I J : QInterval) : QInterval := ⟨Min.min I.lo J.lo, Min.min I.hi J.hi⟩

/-- Interval maximum. -/
def max (I J : QInterval) : QInterval := ⟨Max.max I.lo J.lo, Max.max I.hi J.hi⟩

/-- `x` rounded down to a multiple of `1/2^p`. -/
def roundDown (p : ℕ) (x : ℚ) : ℚ := ((⌊x * 2 ^ p⌋ : ℤ) : ℚ) / 2 ^ p

/-- `x` rounded up to a multiple of `1/2^p`. -/
def roundUp (p : ℕ) (x : ℚ) : ℚ := ((⌈x * 2 ^ p⌉ : ℤ) : ℚ) / 2 ^ p

/-- The interval rounded outward to multiples of `1/2^p`. -/
def round (p : ℕ) (I : QInterval) : QInterval := ⟨roundDown p I.lo, roundUp p I.hi⟩

/-- Bisection for `√x`: from `0 ≤ lo`, `lo² ≤ x ≤ hi²` and `0 ≤ hi`, `n` halvings of `[lo, hi]`. -/
def sqrtBisect (x : ℚ) : ℕ → ℚ → ℚ → ℚ × ℚ
  | 0, lo, hi => (lo, hi)
  | n + 1, lo, hi =>
    if (lo + hi) / 2 * ((lo + hi) / 2) ≤ x then sqrtBisect x n ((lo + hi) / 2) hi
    else sqrtBisect x n lo ((lo + hi) / 2)

/-- A lower bound of `√x`, by `n` bisection steps. -/
def sqrtLower (n : ℕ) (x : ℚ) : ℚ := if x ≤ 0 then 0 else (sqrtBisect x n 0 (Max.max x 1)).1

/-- An upper bound of `√x`, by `n` bisection steps. -/
def sqrtUpper (n : ℕ) (x : ℚ) : ℚ := if x ≤ 0 then 0 else (sqrtBisect x n 0 (Max.max x 1)).2

/-- Interval square root, the ends bisected `n` times. -/
def sqrt (n : ℕ) (I : QInterval) : QInterval := ⟨sqrtLower n I.lo, sqrtUpper n I.hi⟩

theorem roundDown_le (p : ℕ) (x : ℚ) : roundDown p x ≤ x := by
  unfold roundDown
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

theorem le_roundUp (p : ℕ) (x : ℚ) : x ≤ roundUp p x := by
  unfold roundUp
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

theorem mem_point (q : ℚ) : (point q).Mem q := ⟨le_rfl, le_rfl⟩

theorem mem_round (p : ℕ) {I : QInterval} {x : ℝ} (h : I.Mem x) : (I.round p).Mem x :=
  ⟨le_trans (by exact_mod_cast roundDown_le p I.lo) h.1,
   le_trans h.2 (by exact_mod_cast le_roundUp p I.hi)⟩

theorem mem_add {I J : QInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.add J).Mem (x + y) := by
  unfold Mem add at *
  push_cast
  exact ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩

theorem mem_sub {I J : QInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.sub J).Mem (x - y) := by
  unfold Mem sub at *
  push_cast
  exact ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩

theorem mem_neg {I : QInterval} {x : ℝ} (hx : I.Mem x) : I.neg.Mem (-x) := by
  unfold Mem neg at *
  push_cast
  exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- A product `x y` with `x ∈ [a, b]` lies between `a y` and `b y`. -/
theorem between_mul_left {a b x : ℝ} (y : ℝ) (hx : a ≤ x ∧ x ≤ b) :
    Min.min (a * y) (b * y) ≤ x * y ∧ x * y ≤ Max.max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hy),
      (mul_le_mul_of_nonneg_right hx.2 hy).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hy),
      (mul_le_mul_of_nonpos_right hx.1 hy).trans (le_max_left _ _)⟩

theorem mem_mul {I J : QInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.mul J).Mem (x * y) := by
  unfold Mem mul at *
  push_cast
  obtain ⟨h1, h2⟩ := between_mul_left y hx
  have hlo := between_mul_left (I.lo : ℝ) hy
  have hhi := between_mul_left (I.hi : ℝ) hy
  simp only [mul_comm _ (I.lo : ℝ), mul_comm _ (I.hi : ℝ)] at hlo hhi
  constructor
  · refine le_trans ?_ h1
    exact le_min ((min_le_left _ _).trans hlo.1) ((min_le_right _ _).trans hhi.1)
  · refine h2.trans ?_
    exact max_le (hlo.2.trans (le_max_left _ _)) (hhi.2.trans (le_max_right _ _))

theorem mem_inv {I K : QInterval} {x : ℝ} (hx : I.Mem x) (h : I.inv? = some K) : K.Mem x⁻¹ := by
  unfold inv? at h
  split_ifs at h with hs
  cases h
  unfold Mem at *
  push_cast
  rw [← one_div]
  rcases hs with hpos | hneg
  · have hlo : (0:ℝ) < I.lo := by exact_mod_cast hpos
    have hxpos : 0 < x := lt_of_lt_of_le hlo hx.1
    exact ⟨one_div_le_one_div_of_le hxpos hx.2, one_div_le_one_div_of_le hlo hx.1⟩
  · have hhi : (I.hi:ℝ) < 0 := by exact_mod_cast hneg
    have hxneg : x < 0 := lt_of_le_of_lt hx.2 hhi
    exact ⟨one_div_le_one_div_of_neg_of_le hhi hx.2, one_div_le_one_div_of_neg_of_le hxneg hx.1⟩

theorem mem_pow {I : QInterval} {x : ℝ} (hx : I.Mem x) : ∀ n : ℕ, (I.pow n).Mem (x ^ n)
  | 0 => by simpa [pow] using mem_point 1
  | n + 1 => by rw [pow_succ']; exact mem_mul hx (mem_pow hx n)

theorem mem_min {I J : QInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.min J).Mem (Min.min x y) := by
  unfold Mem min at *
  push_cast
  exact ⟨min_le_min hx.1 hy.1, min_le_min hx.2 hy.2⟩

theorem mem_max {I J : QInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.max J).Mem (Max.max x y) := by
  unfold Mem max at *
  push_cast
  exact ⟨max_le_max hx.1 hy.1, max_le_max hx.2 hy.2⟩

theorem sqrtBisect_spec (x : ℚ) : ∀ (n : ℕ) (lo hi : ℚ), 0 ≤ lo → lo * lo ≤ x → x ≤ hi * hi →
    0 ≤ hi → 0 ≤ (sqrtBisect x n lo hi).1 ∧
      (sqrtBisect x n lo hi).1 * (sqrtBisect x n lo hi).1 ≤ x ∧
      x ≤ (sqrtBisect x n lo hi).2 * (sqrtBisect x n lo hi).2 ∧ 0 ≤ (sqrtBisect x n lo hi).2
  | 0, _, _, h0, h1, h2, h3 => ⟨h0, h1, h2, h3⟩
  | n + 1, lo, hi, h0, h1, h2, h3 => by
    have hm : 0 ≤ (lo + hi) / 2 := by linarith
    simp only [sqrtBisect]
    split_ifs with hc
    · exact sqrtBisect_spec x n _ _ hm hc h2 h3
    · exact sqrtBisect_spec x n _ _ h0 h1 (le_of_lt (not_le.mp hc)) hm

theorem sqrtLower_le (n : ℕ) (x : ℚ) : (sqrtLower n x : ℝ) ≤ Real.sqrt x := by
  unfold sqrtLower
  split_ifs with hx
  · simp [Real.sqrt_nonneg]
  · have hx' : 0 < x := lt_of_not_ge hx
    obtain ⟨h0, h1, -, -⟩ := sqrtBisect_spec x n 0 (Max.max x 1) le_rfl (by simpa using hx'.le)
      (by rcases le_total x 1 with h | h
          · rw [max_eq_right h]; nlinarith
          · rw [max_eq_left h]; nlinarith) (by positivity)
    apply Real.le_sqrt_of_sq_le
    rw [sq]
    exact_mod_cast h1

theorem le_sqrtUpper (n : ℕ) (x : ℚ) : Real.sqrt x ≤ sqrtUpper n x := by
  unfold sqrtUpper
  split_ifs with hx
  · have hx0 : ((x : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hx
    rw [Real.sqrt_eq_zero'.mpr hx0]
    simp
  · have hx' : 0 < x := lt_of_not_ge hx
    obtain ⟨-, -, h2, h3⟩ := sqrtBisect_spec x n 0 (Max.max x 1) le_rfl (by simpa using hx'.le)
      (by rcases le_total x 1 with h | h
          · rw [max_eq_right h]; nlinarith
          · rw [max_eq_left h]; nlinarith) (by positivity)
    rw [Real.sqrt_le_left (by exact_mod_cast h3)]
    rw [sq]
    exact_mod_cast h2

theorem mem_sqrt (n : ℕ) {I : QInterval} {x : ℝ} (hx : I.Mem x) : (I.sqrt n).Mem (Real.sqrt x) :=
  ⟨(sqrtLower_le n I.lo).trans (Real.sqrt_le_sqrt hx.1),
   (Real.sqrt_le_sqrt hx.2).trans (le_sqrtUpper n I.hi)⟩

end QInterval

namespace CExpr

open QInterval in
/-- An enclosure of the value when the variable `i` lies in the `i`-th interval of `box`: every
intermediate interval is rounded outward to multiples of `1/2^p`, and square roots are bisected
`p` times; `none` when a variable has no interval or a divisor's enclosure contains zero. -/
def enclose (p : ℕ) (box : List QInterval) : CExpr → Option QInterval
  | nat n => some (point n)
  | rat q => some (point q)
  | var i => box[i]?
  | add a b =>
    match enclose p box a, enclose p box b with
    | some I, some J => some ((I.add J).round p)
    | _, _ => none
  | sub a b =>
    match enclose p box a, enclose p box b with
    | some I, some J => some ((I.sub J).round p)
    | _, _ => none
  | mul a b =>
    match enclose p box a, enclose p box b with
    | some I, some J => some ((I.mul J).round p)
    | _, _ => none
  | div a b =>
    match enclose p box a, enclose p box b with
    | some I, some J =>
      match J.inv? with
      | some K => some ((I.mul K).round p)
      | none => none
    | _, _ => none
  | neg a =>
    match enclose p box a with
    | some I => some I.neg
    | none => none
  | pow a n =>
    match enclose p box a with
    | some I => some ((I.pow n).round p)
    | none => none
  | sqrt a =>
    match enclose p box a with
    | some I => some ((I.sqrt p).round p)
    | none => none
  | min a b =>
    match enclose p box a, enclose p box b with
    | some I, some J => some (I.min J)
    | _, _ => none
  | max a b =>
    match enclose p box a, enclose p box b with
    | some I, some J => some (I.max J)
    | _, _ => none

/-- Every variable lies in its interval of `box`. -/
def InBoxes (box : List QInterval) (x : ℕ → ℝ) : Prop := ∀ i (I : QInterval), box[i]? = some I → I.Mem (x i)

open QInterval in
theorem enclose_sound (p : ℕ) (box : List QInterval) (x : ℕ → ℝ) (hx : InBoxes box x) :
    ∀ (e : CExpr) (I : QInterval), e.enclose p box = some I → I.Mem (e.denote x)
  | nat n, I, h => by
    simp only [enclose, Option.some.injEq] at h
    subst h
    simpa [denote] using mem_point (n : ℚ)
  | rat q, I, h => by
    simp only [enclose, Option.some.injEq] at h
    subst h
    exact mem_point q
  | var i, I, h => by
    simp only [enclose] at h
    exact hx i I h
  | add a b, I, h => by
    cases ha : enclose p box a <;> cases hb : enclose p box b <;> simp only [enclose, ha, hb, reduceCtorEq,
      Option.some.injEq] at h
    subst h
    exact mem_round p (mem_add (enclose_sound p box x hx a _ ha) (enclose_sound p box x hx b _ hb))
  | sub a b, I, h => by
    cases ha : enclose p box a <;> cases hb : enclose p box b <;> simp only [enclose, ha, hb, reduceCtorEq,
      Option.some.injEq] at h
    subst h
    exact mem_round p (mem_sub (enclose_sound p box x hx a _ ha) (enclose_sound p box x hx b _ hb))
  | mul a b, I, h => by
    cases ha : enclose p box a <;> cases hb : enclose p box b <;> simp only [enclose, ha, hb, reduceCtorEq,
      Option.some.injEq] at h
    subst h
    exact mem_round p (mem_mul (enclose_sound p box x hx a _ ha) (enclose_sound p box x hx b _ hb))
  | div a b, I, h => by
    cases ha : enclose p box a <;> cases hb : enclose p box b <;> simp only [enclose, ha, hb, reduceCtorEq]
      at h
    rename_i J K
    cases hk : K.inv? <;> simp only [hk, reduceCtorEq, Option.some.injEq] at h
    subst h
    rw [denote, div_eq_mul_inv]
    exact mem_round p (mem_mul (enclose_sound p box x hx a _ ha) (mem_inv (enclose_sound p box x hx b _ hb) hk))
  | neg a, I, h => by
    cases ha : enclose p box a <;> simp only [enclose, ha, reduceCtorEq, Option.some.injEq] at h
    subst h
    exact mem_neg (enclose_sound p box x hx a _ ha)
  | pow a n, I, h => by
    cases ha : enclose p box a <;> simp only [enclose, ha, reduceCtorEq, Option.some.injEq] at h
    subst h
    exact mem_round p (mem_pow (enclose_sound p box x hx a _ ha) n)
  | sqrt a, I, h => by
    cases ha : enclose p box a <;> simp only [enclose, ha, reduceCtorEq, Option.some.injEq] at h
    subst h
    exact mem_round p (mem_sqrt p (enclose_sound p box x hx a _ ha))
  | min a b, I, h => by
    cases ha : enclose p box a <;> cases hb : enclose p box b <;> simp only [enclose, ha, hb, reduceCtorEq,
      Option.some.injEq] at h
    subst h
    exact mem_min (enclose_sound p box x hx a _ ha) (enclose_sound p box x hx b _ hb)
  | max a b, I, h => by
    cases ha : enclose p box a <;> cases hb : enclose p box b <;> simp only [enclose, ha, hb, reduceCtorEq,
      Option.some.injEq] at h
    subst h
    exact mem_max (enclose_sound p box x hx a _ ha) (enclose_sound p box x hx b _ hb)

/-- The enclosure at precision `p` over `box` exists and lies in `[lo, hi]`. -/
def within (p : ℕ) (box : List QInterval) (e : CExpr) (lo hi : ℚ) : Bool :=
  match e.enclose p box with
  | some I => decide (lo ≤ I.lo) && decide (I.hi ≤ hi)
  | none => false

theorem bounds_of_within (p : ℕ) (box : List QInterval) (e : CExpr) (lo hi : ℚ)
    (h : e.within p box lo hi = true) (x : ℕ → ℝ) (hx : InBoxes box x) :
    (lo : ℝ) ≤ e.denote x ∧ e.denote x ≤ hi := by
  unfold within at h
  cases he : e.enclose p box with
  | none => simp [he] at h
  | some I =>
    simp only [he, Bool.and_eq_true, decide_eq_true_eq] at h
    have hm := enclose_sound p box x hx e I he
    exact ⟨le_trans (by exact_mod_cast h.1) hm.1, le_trans hm.2 (by exact_mod_cast h.2)⟩

/-- The point whose `i`-th coordinate is the `i`-th entry of the list. -/
def ptOfList (vs : List ℝ) : ℕ → ℝ := fun i => vs.getD i 0

theorem inBoxes_nil (x : ℕ → ℝ) : InBoxes [] x := fun i I h => by simp at h

/-- The box condition for a point given as a list, one interval and one value at a time. -/
theorem inBoxes_cons {I : QInterval} {box : List QInterval} {v : ℝ} {vs : List ℝ}
    (hv : (I.lo : ℝ) ≤ v ∧ v ≤ I.hi) (hvs : InBoxes box (ptOfList vs)) :
    InBoxes (I :: box) (ptOfList (v :: vs)) := by
  intro i J hJ
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hJ
    subst hJ
    exact hv
  | succ k =>
    simp only [List.getElem?_cons_succ] at hJ
    have := hvs k J hJ
    simpa [ptOfList] using this

end CExpr

end Cycle63.Certificate

/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Mathlib.Tactic

/-!
# Sound rational interval evaluation

The endpoints are computed in `ℚ`; containment concerns the actual real value.
Multiplication uses all four corners. Division has an explicit positive lower
endpoint hypothesis, which suffices for every interval division in the recovered
contact certificate. No machine arithmetic is trusted by these lemmas.
-/

set_option autoImplicit false
namespace QRH.RationalInterval

/-- A pair of rational endpoints; soundness theorems require containment. -/
structure Interval where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

/-- Membership of a real number in a closed rational interval. -/
def Contains (a : Interval) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)

/-- The degenerate interval consisting of one rational number. -/
def point (q : ℚ) : Interval := ⟨q, q⟩
/-- Directed interval addition. -/
def add (a b : Interval) : Interval := ⟨a.lo+b.lo, a.hi+b.hi⟩
/-- Directed interval negation. -/
def neg (a : Interval) : Interval := ⟨-a.hi, -a.lo⟩
/-- Directed interval subtraction. -/
def sub (a b : Interval) : Interval := add a (neg b)
/-- Four-corner interval multiplication, including intervals crossing zero. -/
def mul (a b : Interval) : Interval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩
/-- Reciprocal endpoints; soundness requires a positive denominator interval. -/
def inv (a : Interval) : Interval := ⟨1/a.hi, 1/a.lo⟩
/-- Directed interval division. -/
def div (a b : Interval) : Interval := mul a (inv b)
/-- Repeated interval multiplication, matching the supplied Python certificate. -/
def pow (a : Interval) : ℕ → Interval
  | 0 => point 1
  | n+1 => mul (pow a n) a

/-- A rational point interval contains its real coercion. -/
theorem point_sound (q : ℚ) : Contains (point q) (q : ℝ) := ⟨le_rfl, le_rfl⟩

/-- Directed addition encloses the sum of any two enclosed real values. -/
theorem add_sound {a b : Interval} {x y : ℝ}
    (hx : Contains a x) (hy : Contains b y) : Contains (add a b) (x+y) := by
  simpa [Contains, add] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

/-- Reversing and negating endpoints encloses the negative real value. -/
theorem neg_sound {a : Interval} {x : ℝ} (hx : Contains a x) :
    Contains (neg a) (-x) := by
  simpa [Contains, neg] using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

/-- Directed subtraction encloses the difference. -/
theorem sub_sound {a b : Interval} {x y : ℝ}
    (hx : Contains a x) (hy : Contains b y) : Contains (sub a b) (x-y) := by
  simpa [sub, sub_eq_add_neg] using add_sound hx (neg_sound hy)

/-- Multiplication by a fixed real number lies between its two endpoint values. -/
theorem mul_between {a b x : ℝ} (hx : a ≤ x ∧ x ≤ b) (y : ℝ) :
    min (a*y) (b*y) ≤ x*y ∧ x*y ≤ max (a*y) (b*y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hy),
      (mul_le_mul_of_nonneg_right hx.2 hy).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hy),
      (mul_le_mul_of_nonpos_right hx.1 hy).trans (le_max_left _ _)⟩

/-- All four corner products enclose the product throughout a real rectangle. -/
theorem mul_sound {a b : Interval} {x y : ℝ}
    (hx : Contains a x) (hy : Contains b y) : Contains (mul a b) (x*y) := by
  have hxy := mul_between hx y
  have ha : min ((a.lo : ℝ)*b.lo) ((a.lo : ℝ)*b.hi) ≤ (a.lo : ℝ)*y ∧
      (a.lo : ℝ)*y ≤ max ((a.lo : ℝ)*b.lo) ((a.lo : ℝ)*b.hi) := by
    simpa only [mul_comm] using mul_between hy (a.lo : ℝ)
  have hb : min ((a.hi : ℝ)*b.lo) ((a.hi : ℝ)*b.hi) ≤ (a.hi : ℝ)*y ∧
      (a.hi : ℝ)*y ≤ max ((a.hi : ℝ)*b.lo) ((a.hi : ℝ)*b.hi) := by
    simpa only [mul_comm] using mul_between hy (a.hi : ℝ)
  constructor
  · simp only [mul, Rat.cast_min, Rat.cast_mul]
    exact (min_le_min ha.1 hb.1).trans hxy.1
  · simp only [mul, Rat.cast_max, Rat.cast_mul]
    exact hxy.2.trans (max_le_max ha.2 hb.2)

/-- The reciprocal is enclosed whenever the lower endpoint is positive. -/
theorem inv_sound {a : Interval} {x : ℝ} (hx : Contains a x) (ha : 0 < a.lo) :
    Contains (inv a) (1/x) := by
  have hlo : (0 : ℝ) < (a.lo : ℝ) := by exact_mod_cast ha
  have hpos : 0 < x := hlo.trans_le hx.1
  simpa [Contains, inv] using And.intro
    (one_div_le_one_div_of_le hpos hx.2) (one_div_le_one_div_of_le hlo hx.1)

/-- Positive-denominator interval division encloses real division. -/
theorem div_sound {a b : Interval} {x y : ℝ}
    (hx : Contains a x) (hy : Contains b y) (hb : 0 < b.lo) :
    Contains (div a b) (x/y) := by
  simpa [div, div_eq_mul_inv] using mul_sound hx (inv_sound hy hb)

/-- Repeated interval multiplication encloses every natural power. -/
theorem pow_sound {a : Interval} {x : ℝ} (hx : Contains a x) (n : ℕ) :
    Contains (pow a n) (x^n) := by
  induction n with
  | zero => simpa [pow] using point_sound 1
  | succ n ih => simpa [pow, pow_succ] using mul_sound ih hx

/-- An exact expression in one real variable, used for replayable certificates. -/
inductive Expr where
  | var
  | lit (q : ℚ)
  | sum (a b : Expr)
  | difference (a b : Expr)
  | product (a b : Expr)
  | quotient (a b : Expr)
  | power (a : Expr) (n : ℕ)
  deriving Repr

instance : Add Expr := ⟨Expr.sum⟩
instance : Sub Expr := ⟨Expr.difference⟩
instance : Mul Expr := ⟨Expr.product⟩
instance : Div Expr := ⟨Expr.quotient⟩
instance : Pow Expr ℕ := ⟨Expr.power⟩
instance (n : ℕ) : OfNat Expr n := ⟨Expr.lit n⟩

/-- Interpret the expression over the real numbers. -/
noncomputable def value (x : ℝ) : Expr → ℝ
  | .var => x
  | .lit q => q
  | .sum a b => value x a + value x b
  | .difference a b => value x a - value x b
  | .product a b => value x a * value x b
  | .quotient a b => value x a / value x b
  | .power a n => value x a ^ n

/-- Real evaluation commutes with an expression sum. -/
@[simp] theorem value_add (x : ℝ) (a b : Expr) :
    value x (a+b) = value x a + value x b := rfl
/-- Real evaluation commutes with an expression difference. -/
@[simp] theorem value_sub (x : ℝ) (a b : Expr) :
    value x (a-b) = value x a - value x b := rfl
/-- Real evaluation commutes with an expression product. -/
@[simp] theorem value_mul (x : ℝ) (a b : Expr) :
    value x (a*b) = value x a * value x b := rfl
/-- Real evaluation commutes with an expression quotient. -/
@[simp] theorem value_div (x : ℝ) (a b : Expr) :
    value x (a/b) = value x a / value x b := rfl
/-- Real evaluation commutes with a natural power. -/
@[simp] theorem value_pow (x : ℝ) (a : Expr) (n : ℕ) :
    value x (a^n) = value x a ^ n := rfl
/-- Expression numerals denote the same real numerals. -/
@[simp] theorem value_nat (x : ℝ) (n : ℕ) : value x (OfNat.ofNat n : Expr) = (n : ℝ) := by
  change ((n : ℚ) : ℝ) = (n : ℝ)
  exact Rat.cast_natCast n

/-- Compute the rational enclosure using the same expression tree. -/
def enclose (i : Interval) : Expr → Interval
  | .var => i
  | .lit q => point q
  | .sum a b => add (enclose i a) (enclose i b)
  | .difference a b => sub (enclose i a) (enclose i b)
  | .product a b => mul (enclose i a) (enclose i b)
  | .quotient a b => div (enclose i a) (enclose i b)
  | .power a n => pow (enclose i a) n

/-- Check every division denominator before using the computed enclosure. -/
def safe (i : Interval) : Expr → Bool
  | .var | .lit _ => true
  | .sum a b | .difference a b | .product a b => safe i a && safe i b
  | .quotient a b => (safe i a && safe i b) && decide (0 < (enclose i b).lo)
  | .power a _ => safe i a

/-- Kernel-checked denominator guards make the full interval evaluation sound. -/
theorem expression_sound (i : Interval) (e : Expr) {x : ℝ}
    (hx : Contains i x) (h : safe i e = true) : Contains (enclose i e) (value x e) := by
  induction e with
  | var => exact hx
  | lit q => exact point_sound q
  | sum a b ha hb =>
    have hs := Bool.and_eq_true_iff.mp h
    exact add_sound (ha hs.1) (hb hs.2)
  | difference a b ha hb =>
    have hs := Bool.and_eq_true_iff.mp h
    exact sub_sound (ha hs.1) (hb hs.2)
  | product a b ha hb =>
    have hs := Bool.and_eq_true_iff.mp h
    exact mul_sound (ha hs.1) (hb hs.2)
  | quotient a b ha hb =>
    have hs := Bool.and_eq_true_iff.mp h
    have ht := Bool.and_eq_true_iff.mp hs.1
    exact div_sound (ha ht.1) (hb ht.2) (of_decide_eq_true hs.2)
  | power a n ha => exact pow_sound (ha h) n

end QRH.RationalInterval

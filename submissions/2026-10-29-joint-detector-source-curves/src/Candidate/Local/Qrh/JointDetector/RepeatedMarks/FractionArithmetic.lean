/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Qrh.JointDetector.RepeatedMarks.FractionArithmetic
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Computable unreduced fractions. No operation computes a gcd. -/
structure Fraction where
  num : ℤ
  den : ℕ
  den_pos : 0<den

def Fraction.ofInt (n : ℤ) : Fraction := ⟨n,1,by decide⟩
instance (n : ℕ) : OfNat Fraction n := ⟨Fraction.ofInt n⟩
instance : Coe ℤ Fraction := ⟨Fraction.ofInt⟩

def Fraction.add (a b : Fraction) : Fraction :=
  if a.den=b.den then ⟨a.num+b.num,a.den,a.den_pos⟩ else
    ⟨a.num*(b.den:ℤ)+b.num*(a.den:ℤ),a.den*b.den,Nat.mul_pos a.den_pos b.den_pos⟩
def Fraction.neg (a : Fraction) : Fraction := ⟨-a.num,a.den,a.den_pos⟩
def Fraction.sub (a b : Fraction) : Fraction := a.add b.neg
def Fraction.mul (a b : Fraction) : Fraction :=
  ⟨a.num*b.num,a.den*b.den,Nat.mul_pos a.den_pos b.den_pos⟩
def Fraction.inv (a : Fraction) : Fraction :=
  if h : a.num=0 then 0 else
    ⟨(a.den:ℤ)*a.num.sign,a.num.natAbs,Int.natAbs_pos.mpr h⟩
def Fraction.div (a b : Fraction) : Fraction := a.mul b.inv

def Fraction.pow (a : Fraction) : ℕ→Fraction
  | 0 => 1
  | n+1 => (a.pow n).mul a

instance : Add Fraction := ⟨Fraction.add⟩
instance : Neg Fraction := ⟨Fraction.neg⟩
instance : Sub Fraction := ⟨Fraction.sub⟩
instance : Mul Fraction := ⟨Fraction.mul⟩
instance : Inv Fraction := ⟨Fraction.inv⟩
instance : Div Fraction := ⟨Fraction.div⟩
instance : Pow Fraction ℕ := ⟨Fraction.pow⟩

/-- Evaluation is polymorphic; its laws need only a characteristic-zero field. -/
def Fraction.eval {K : Type*} [Field K] [CharZero K] (a : Fraction) : K :=
  (a.num:K)/(a.den:K)
def Fraction.evalQ (a : Fraction) : ℚ := a.eval
noncomputable def Fraction.evalR (a : Fraction) : ℝ := a.eval

theorem Fraction.den_cast_ne_zero {K : Type*} [Field K] [CharZero K] (a : Fraction) :
    (a.den:K)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt a.den_pos)

@[simp] theorem Fraction.eval_ofInt {K : Type*} [Field K] [CharZero K] (n : ℤ) :
    (Fraction.ofInt n).eval=(n:K) := by simp [eval,ofInt]
@[simp] theorem Fraction.eval_nat {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    (OfNat.ofNat n : Fraction).eval=(n:K) := by
  change (Fraction.ofInt (n:ℤ)).eval=(n:K)
  rw [eval_ofInt]
  simp
@[simp] theorem Fraction.eval_ofNat {K : Type*} [Field K] [CharZero K]
    (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Fraction).eval=(ofNat(n) : K) := by
  rw [eval_nat]
  rfl
@[simp] theorem Fraction.eval_zero {K : Type*} [Field K] [CharZero K] :
    (0:Fraction).eval=(0:K) := by
  change (Fraction.ofInt 0).eval=(0:K)
  rw [eval_ofInt]
  simp
@[simp] theorem Fraction.eval_one {K : Type*} [Field K] [CharZero K] :
    (1:Fraction).eval=(1:K) := by
  change (Fraction.ofInt 1).eval=(1:K)
  rw [eval_ofInt]
  simp

@[simp] theorem Fraction.eval_add {K : Type*} [Field K] [CharZero K] (a b : Fraction) :
    (a+b).eval=(a.eval+b.eval:K) := by
  change (a.add b).eval=_
  by_cases h : a.den=b.den
  · simp only [add,if_pos h,eval,Int.cast_add]
    rw [h,add_div]
  · simp only [add,if_neg h,eval,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_mul]
    field_simp [a.den_cast_ne_zero,b.den_cast_ne_zero]
    <;> ring

@[simp] theorem Fraction.eval_neg {K : Type*} [Field K] [CharZero K] (a : Fraction) :
    (-a).eval=-(a.eval:K) := by
  change ((-a.num:ℤ):K)/(a.den:K)=-a.eval
  simp only [eval,Int.cast_neg,neg_div]
@[simp] theorem Fraction.eval_sub {K : Type*} [Field K] [CharZero K] (a b : Fraction) :
    (a-b).eval=(a.eval-b.eval:K) := by
  change (a+(-b)).eval=_
  rw [eval_add,eval_neg,sub_eq_add_neg]
@[simp] theorem Fraction.eval_mul {K : Type*} [Field K] [CharZero K] (a b : Fraction) :
    (a*b).eval=(a.eval*b.eval:K) := by
  change ((a.num*b.num:ℤ):K)/(a.den*b.den:ℕ)=_
  push_cast
  simp only [eval]
  ring
@[simp] theorem Fraction.eval_inv {K : Type*} [Field K] [CharZero K] (a : Fraction) :
    (a⁻¹).eval=(a.eval:K)⁻¹ := by
  change (a.inv).eval=(a.eval:K)⁻¹
  by_cases h : a.num=0
  · simp only [inv,dif_pos h,eval_zero]
    simp [eval,h]
  · have hn : (a.num:K)≠0 := Int.cast_ne_zero.mpr h
    have habs : (a.num.natAbs:K)≠0 := Nat.cast_ne_zero.mpr (Int.natAbs_ne_zero.mpr h)
    have hs : (a.num.sign:K)*(a.num:K)=(a.num.natAbs:K) := by
      have hsInt : a.num.sign*a.num=(a.num.natAbs:ℤ) := Int.sign_mul_self_eq_natAbs a.num
      simpa only [Int.cast_mul,Int.cast_natCast] using
        congrArg (fun z : ℤ=>(z:K)) hsInt
    simp only [inv,dif_neg h,eval,Int.cast_mul,Int.cast_natCast,inv_div]
    field_simp [hn,habs]
    linear_combination (a.den:K)*hs
@[simp] theorem Fraction.eval_div {K : Type*} [Field K] [CharZero K] (a b : Fraction) :
    (a/b).eval=(a.eval/b.eval:K) := by
  change (a*b⁻¹).eval=_
  rw [eval_mul,eval_inv,div_eq_mul_inv]
@[simp] theorem Fraction.eval_pow {K : Type*} [Field K] [CharZero K] (a : Fraction) (n : ℕ) :
    (a^n).eval=(a.eval:K)^n := by
  induction n with
  | zero =>
    change (Fraction.pow a 0).eval=(a.eval:K)^0
    rw [Fraction.pow,pow_zero]
    exact eval_one (K:=K)
  | succ n ih =>
    change ((a^n)*a).eval=_
    rw [eval_mul,ih,pow_succ]

/-- Casting the rational interpretation agrees with direct real evaluation. -/
@[simp] theorem Fraction.cast_evalQ (a : Fraction) : (a.evalQ:ℝ)=a.evalR := by
  simp [evalQ,evalR,eval]

/-- The certificate decision checks only the numerator. -/
def Fraction.nonneg (a : Fraction) : Bool := decide (0≤a.num)
@[simp] theorem Fraction.nonneg_eq_true (a : Fraction) : a.nonneg=true ↔ 0≤a.num := by
  simp [nonneg]
theorem Fraction.evalR_nonneg_of_num (a : Fraction) (h : 0≤a.num) : 0≤a.evalR := by
  apply div_nonneg (by exact_mod_cast h) (Nat.cast_nonneg a.den)
theorem Fraction.evalR_nonneg_of_check (a : Fraction) (h : a.nonneg=true) : 0≤a.evalR :=
  a.evalR_nonneg_of_num (a.nonneg_eq_true.mp h)
theorem Fraction.evalR_pos_of_num (a : Fraction) (h : 0<a.num) : 0<a.evalR := by
  exact div_pos (by exact_mod_cast h) (by exact_mod_cast a.den_pos)

end Qrh.JointDetector.RepeatedMarks.FractionArithmetic

#print axioms Qrh.JointDetector.RepeatedMarks.FractionArithmetic.Fraction.eval_inv
#print axioms Qrh.JointDetector.RepeatedMarks.FractionArithmetic.Fraction.evalR_nonneg_of_check

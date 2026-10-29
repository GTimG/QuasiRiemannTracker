/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FractionArithmetic
namespace Qrh.JointDetector.RepeatedMarks.FractionArithmetic

/-- Compact input constructor; a zero denominator has the field value zero. -/
def uf (n : ℤ) (d : ℕ) : Fraction :=
 if h : 0<d then ⟨n,d,h⟩ else 0

@[simp] theorem Fraction.eval_mk {K : Type*} [Field K] [CharZero K]
 (n : ℤ) (d : ℕ) (h : 0<d) : (Fraction.mk n d h).eval=(n:K)/(d:K) := rfl

@[simp] theorem eval_uf {K : Type*} [Field K] [CharZero K] (n : ℤ) (d : ℕ) :
 (uf n d).eval=(n:K)/(d:K) := by
 unfold uf
 split_ifs with h
 · rfl
 · have hd : d=0 := Nat.eq_zero_of_not_pos h
   simp [hd]

end Qrh.JointDetector.RepeatedMarks.FractionArithmetic

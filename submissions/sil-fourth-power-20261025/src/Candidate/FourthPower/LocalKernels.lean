/- Copyright (c) 2026 Sil. Apache-2.0.
Local fifth-free restoration algebra. Global mass bounds are separate obligations. -/
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace Candidate.FourthPower.LocalKernels

def truncated {R : Type*} [CommRing R] (x y : R) : R :=
  1 + x + y + x^2 + x*y + y^2 +
  x^3 + x^2*y + x*y^2 + y^3 +
  x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4

def base {R : Type*} [CommRing R] (x y : R) : R := (1-x)*(1-y)
def ordinary {R : Type*} [CommRing R] (x y : R) : R :=
  base x y * truncated x y

theorem ordinary_expansion {R : Type*} [CommRing R] (x y : R) :
    ordinary x y =
      1 - (x^5+x^4*y+x^3*y^2+x^2*y^3+x*y^4+y^5) +
        (x^5*y+x^4*y^2+x^3*y^3+x^2*y^4+x*y^5) := by
  dsimp [ordinary, base, truncated]
  ring

/-- Forward marked coefficient with unrestricted residual series F. -/
theorem forward_marked {K : Type*} [Field K] (B H : K) (hB : B ≠ 0) :
    H * B⁻¹ + (B-H) * B⁻¹ = 1 := by
  field_simp
  <;> ring

/-- The inverse kernel-extraction term keeps the restricted residual T. -/
theorem inverse_marked {K : Type*} [Field K] (B T : K)
    (hB : B ≠ 0) (hT : T ≠ 0) :
    (B*T)⁻¹ + (B*T-B)*(B*T)⁻¹^2*T = B⁻¹ := by
  field_simp
  <;> ring

theorem inverse_ordinary {K : Type*} [Field K] (B T : K)
    (hB : B ≠ 0) (hT : T ≠ 0) :
    (B*T)⁻¹*T = B⁻¹ := by
  field_simp

/-- Multiplication of square-zero marked coefficients, written as a pair. -/
def markedMul {R : Type*} [CommRing R] (a b : R × R) : R × R :=
  (a.1*b.1, a.1*b.2+a.2*b.1)

theorem forward_operator {K : Type*} [Field K] (B T : K) (hB : B ≠ 0) :
    markedMul (B*T, B-B*T) (B⁻¹, B⁻¹) = (T, 1) := by
  apply Prod.ext
  · dsimp [markedMul]
    field_simp
  · exact forward_marked B (B*T) hB

theorem inverse_operator {K : Type*} [Field K] (B T : K)
    (hB : B ≠ 0) (hT : T ≠ 0) :
    markedMul ((B*T)⁻¹, (B*T-B)*(B*T)⁻¹^2) (T, 1) = (B⁻¹, B⁻¹) := by
  apply Prod.ext
  · exact inverse_ordinary B T hB hT
  · simpa only [markedMul, mul_one] using inverse_marked B T hB hT

end Candidate.FourthPower.LocalKernels

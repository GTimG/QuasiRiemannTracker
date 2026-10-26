/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The total-product squarefree projector used in the ordinary two-ideal source.
The identities retain character zeros; no character value is divided out. -/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103TwoIdeal
noncomputable section

variable {M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M] [DecompositionMonoid M]

def squarefreeIndicator (x : M) : ℂ := by
  classical
  exact if Squarefree x then 1 else 0

def coprimalityIndicator (x y : M) : ℂ := by
  classical
  exact if IsRelPrime x y then 1 else 0

theorem squarefreeIndicator_mul (x y : M) :
    squarefreeIndicator (x*y) = squarefreeIndicator x * squarefreeIndicator y *
      coprimalityIndicator x y := by
  classical
  by_cases hxy : IsRelPrime x y <;> by_cases hx : Squarefree x <;>
    by_cases hy : Squarefree y <;>
    simp [squarefreeIndicator, coprimalityIndicator, squarefree_mul_iff, hxy, hx, hy]

/-- The complete common puncture is retained as a coprimality mask. -/
theorem squarefree_extraction (A B a b : M) :
    squarefreeIndicator (A*B*a*b) =
      squarefreeIndicator (A*B) * squarefreeIndicator (a*b) *
        coprimalityIndicator (A*B) (a*b) := by
  simpa only [mul_assoc] using squarefreeIndicator_mul (A*B) (a*b)

theorem nonsquarefree_extracted_zero (A B a b : M) (h : ¬Squarefree (A*B)) :
    squarefreeIndicator (A*B*a*b) = 0 := by
  rw [squarefree_extraction A B a b]
  simp [squarefreeIndicator, h]

/-- Multiplicative character zeros survive extraction literally. -/
theorem squarefree_character_extraction (ψ : M →*₀ ℂ) (A B a b : M) :
    squarefreeIndicator (A*B*a*b) * ψ (A*B*a*b) =
      (squarefreeIndicator (A*B) * ψ (A*B)) *
        (squarefreeIndicator (a*b) * coprimalityIndicator (A*B) (a*b) * ψ (a*b)) := by
  rw [squarefree_extraction A B a b]
  simp only [map_mul]
  ring

/-- The same extracted projector applies to both rectangles before taking
their difference; no independent coefficient or puncture is introduced. -/
theorem squarefree_centered_extraction (A B a b : M) (u v : ℂ) :
    squarefreeIndicator (A*B*a*b) * (u-v) =
      squarefreeIndicator (A*B) *
        (squarefreeIndicator (a*b) * coprimalityIndicator (A*B) (a*b) * (u-v)) := by
  rw [squarefree_extraction A B a b]
  ring

/-- A separated amplifier prime cannot occur twice in a restricted column. -/
theorem no_prime_square_dvd_column {p S I J : M} (hp : Prime p)
    (hIJ : Squarefree (I*J)) (hS : ¬p ∣ S) : ¬p^2 ∣ S*I*J := by
  intro h
  have h' : p^2 ∣ I*J :=
    hp.pow_dvd_of_dvd_mul_left 2 hS (by simpa only [mul_assoc] using h)
  exact hp.not_isUnit (hIJ p (by simpa only [pow_two] using h'))

theorem no_prime_square_dvd_column_of_coprime {p S I J : M} (hp : Prime p)
    (hIJ : Squarefree (I*J)) (hSP : IsRelPrime S p) : ¬p^2 ∣ S*I*J := by
  apply no_prime_square_dvd_column hp hIJ
  intro h
  exact hp.not_isUnit (hSP h (dvd_refl p))

/-- Extraction by any genuine divisor preserves the same exclusion. -/
theorem prime_square_exclusion_of_dvd {p A column : M}
    (h : ¬p^2 ∣ column) (hA : A ∣ column) : ¬p^2 ∣ A :=
  fun hbad => h (hbad.trans hA)

/-- The marked and ordinary squarefree products give complete valuation at
most two; no third local occurrence is available. -/
theorem no_prime_cube_dvd_two_squarefree {p x y : M} (hp : Prime p)
    (hx : Squarefree x) (hy : Squarefree y) : ¬p^3 ∣ x*y := by
  intro h
  have h' : p^2 ∣ y :=
    hx.pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right hp h
  exact hp.not_isUnit (hy p (by simpa only [pow_two] using h'))

end
end QRH.Record1252270103TwoIdeal

#print axioms QRH.Record1252270103TwoIdeal.squarefree_extraction
#print axioms QRH.Record1252270103TwoIdeal.squarefree_character_extraction
#print axioms QRH.Record1252270103TwoIdeal.squarefree_centered_extraction
#print axioms QRH.Record1252270103TwoIdeal.no_prime_square_dvd_column
#print axioms QRH.Record1252270103TwoIdeal.prime_square_exclusion_of_dvd
#print axioms QRH.Record1252270103TwoIdeal.no_prime_cube_dvd_two_squarefree

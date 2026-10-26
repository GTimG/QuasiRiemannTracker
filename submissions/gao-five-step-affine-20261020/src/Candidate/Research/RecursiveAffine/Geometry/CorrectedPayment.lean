import Candidate.Research.RecursiveAffine.Geometry.PhysicalCoordinates

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153Geometry
noncomputable section
open scoped BigOperators
namespace CorrectedPayment

/-- The actual native common credit is charged once. Common reduction is
not assigned the larger residual-F credit a second time. -/
def h (q : ℝ) : ℝ := max (3/19) (4*Coordinates.rho q-5/4)

def paid1 (x : Fin 14 → ℝ) : ℝ :=
  Coordinates.joint1 x - h Coordinates.q1 * Coordinates.historicalReduction1 x +
    ((1-Coordinates.rho Coordinates.q1)-h Coordinates.q1) * Coordinates.historicalMissing1 x

def paid2 (x : Fin 14 → ℝ) : ℝ :=
  Coordinates.joint2 x - h Coordinates.q2 * Coordinates.historicalReduction2 x +
    ((1-Coordinates.rho Coordinates.q2)-h Coordinates.q2) * Coordinates.historicalMissing2 x

def paid3 (x : Fin 14 → ℝ) : ℝ :=
  Coordinates.joint3 x - h Coordinates.q3 * Coordinates.historicalReduction3 x +
    ((1-Coordinates.rho Coordinates.q3)-h Coordinates.q3) * Coordinates.historicalMissing3 x

def paid4 (x : Fin 14 → ℝ) : ℝ :=
  Coordinates.joint4 x - h Coordinates.q4 * Coordinates.historicalReduction4 x +
    ((1-Coordinates.rho Coordinates.q4)-h Coordinates.q4) * Coordinates.historicalMissing4 x

/-- Direct corrected junction certificates have stronger margins and smaller
multiplier mass than the general 62-gate geometry bundle. -/
theorem uniform_robust_lower {k : ℕ} (C : Certificate 14 k)
    (hmargin : (1249/10000000000 : ℚ) < C.margin)
    (hmass : (∑ j, C.weights j) < 349)
    (x : Fin 14 → ℝ) (E : ℝ) (hE : E ≤ 1/1000000000000000)
    (hc : ∀ j, -E ≤ eval (C.rows j) x) :
    (124899651/1000000000000000 : ℝ) < eval C.objective x := by
  have hm : (1249/10000000000 : ℝ) < (C.margin : ℝ) := by
    have hcast := Rat.cast_lt (K:=ℝ).mpr hmargin
    norm_num at hcast
    exact hcast
  have hw : (∑ j, (C.weights j : ℝ)) ≤ 349 := by
    exact_mod_cast hmass.le
  have hw0 : 0 ≤ ∑ j, (C.weights j : ℝ) := by
    apply Finset.sum_nonneg
    intro j _
    exact_mod_cast C.weights_nonneg j
  have he : E*(∑ j, (C.weights j : ℝ)) ≤ (1/1000000000000000 : ℝ)*349 :=
    (mul_le_mul_of_nonneg_right hE hw0).trans
      (mul_le_mul_of_nonneg_left hw (by norm_num))
  have hb := C.bound_of_constraint_error x E hc
  linarith only [hm, he, hb]

end CorrectedPayment
end
end OAI.SevenEighths.Cycle153Geometry

#print axioms OAI.SevenEighths.Cycle153Geometry.CorrectedPayment.uniform_robust_lower

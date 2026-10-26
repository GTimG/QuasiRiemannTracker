import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryScalarCompensation
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryHighSelected
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily Cycle63Moment

/-- Shift the actual side normalization inside the coefficient coordinate.
The varying side exponent then cancels before joint density is applied. -/
def compensatedHighCoordinates (x : Fin 4→ℝ)(side : ℝ) : Fin 4→ℝ :=
  childHighCoordinates x (-side)

lemma compensated_high_exponent (δ side : ℝ)(x : Fin 4→ℝ) :
    highExponentValue δ (compensatedHighCoordinates x side)=
      highExponentValue δ x-side := by
  simp only [compensatedHighCoordinates,child_high_exponent_value,sub_eq_add_neg]

lemma compensated_high_coordinate_box (x : Fin 4→ℝ)(side B S : ℝ)
    (hx : ∀j,-B≤x j ∧ x j≤B)(hs : |side|≤S) :
    ∀j,-(B+S)≤ compensatedHighCoordinates x side j ∧
      compensatedHighCoordinates x side j≤B+S := by
  intro j
  have hh := child_high_coordinate_box x B (-side) hx j
  simp only [abs_neg] at hh
  dsimp only [compensatedHighCoordinates]
  exact ⟨by linarith [hh.1],by linarith [hh.2]⟩

/-- Multiply by the literal first allocation mass without pulling out a
maximum over labels. Only the fixed compensated factor is external. -/
lemma compensated_high_coefficient (Z mass coeff factor loss side : ℝ)
    (x : Fin 4→ℝ)(hZ : 0<Z)(hm : 0≤ mass)
    (hmass : mass≤factor*Z^loss/Z^side)(hcoeff : coeff≤Z^(x 0)) :
    mass*coeff≤(factor*Z^loss)*Z^((compensatedHighCoordinates x side) 0) := by
  have hh := mul_le_mul_of_nonneg_left hcoeff hm
  apply hh.trans
  apply (mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg hZ.le _)).trans_eq
  simp only [compensatedHighCoordinates,childHighCoordinates,ite_true]
  rw [show x 0+-side=x 0-side by ring,Real.rpow_sub hZ]
  ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67

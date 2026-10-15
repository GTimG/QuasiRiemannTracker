import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.SlotHeight
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskExpansion

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62MarkedPlain
noncomputable section
open scoped Classical BigOperators
open HeckeFamily HeckePrimeAnnular
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
local notation "O" => HeckeFamily.O

theorem naturalSlot_phase (χ : Character) (pool : Finset (Ideal O))
    (β γ : Ideal O→ℂ) (phase : ℂ) (P : ℝ)
    (hcoeff : ∀I∈pool,β I=phase*γ I) :
    naturalSlot χ pool β P=phase*naturalSlot χ pool γ P := by
  unfold naturalSlot
  calc
    _=(Real.sqrt P:ℂ)⁻¹*(phase*∑I∈pool,idealCoeff χ I*γ I) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      rw [hcoeff I hI]
      ring
    _=_:=by ring

/-- The unnormalised physical height differs from the normalized annular
height only by a common factor of absolute value one. -/
theorem naturalSlot_height_norm (χ : Character) (pool : Finset (Ideal O))
    (ν : Ideal O→ℂ) (W : ℝ→ℂ) (P σ v t : ℝ) (hP : 0<P)
    (hpool : ∀I∈pool,I≠0) :
    ‖naturalSlot χ pool (heightCoefficient (fun I=>ν I*annularWeight W P σ v I) t) P‖=
      ‖naturalSlot χ pool (fun I=>ν I*annularWeight W P σ (t+v) I) P‖ := by
  rw [naturalSlot_phase χ pool _ _ ((P:ℂ)^(Complex.I*t)) P
    (fun I hI=>CenteredMomentEnergySlotHeight.height_coefficient ν W P σ v t hP I (hpool I hI))]
  rw [norm_mul]
  have hp : ‖(P:ℂ)^(Complex.I*t)‖=1 := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hP (Complex.I*t)
  rw [hp,one_mul]

end
end OAI.SevenEighths.Cycle62MarkedPlain
#print axioms OAI.SevenEighths.Cycle62MarkedPlain.naturalSlot_height_norm

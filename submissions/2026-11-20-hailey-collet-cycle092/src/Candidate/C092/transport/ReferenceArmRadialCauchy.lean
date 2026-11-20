/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Same-row Cauchy with independent genuine radial fourth prices. -/
import Candidate.C092.transport.ReferenceShortP3Finite
set_option autoImplicit false
namespace QRH.Cycle092.ReferenceArmRadial
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.ReferenceShortP3

theorem independent_radius_cauchy {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (rows : Finset FreeRow) (eta1 eta2 : Character) (W1 W2 : ℝ→ℂ)
    (t1 t2 X1 X2 : ℝ) (mark : Slot→FreeRow→ℂ)
    {U r1 r2 A B C x y : ℝ} (hU : 0< U) (hA : 0≤ A) (hB : 0≤ B)
    (hC1 : 1≤ C) (hAC : A≤ C) (hBC : B≤ C) (hx : 0≤ x) (hy : 0≤ y)
    (hshort : (∑u∈rows,(‖original eta1 (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
      1 u.val W1 t1 X1‖^2*∏i,‖mark i u‖^2)^2) ≤ A*x^4*U^r1)
    (hlong : (∑u∈rows,‖original eta2 (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
      1 u.val W2 t2 X2‖^4) ≤ B*y^4*U^r2) :
    finiteEnergy rows eta1 eta2 W1 W2 t1 t2 X1 X2 mark ≤
      C^2*(x*y)^2*U^((r1+r2)/2) := by
  have hp (r : ℝ) : (U^(r/2))^2=U^r := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
    congr 1
    ring
  have hC0 : 0≤ C := zero_le_one.trans hC1
  have hCC : C≤ C^2 := by nlinarith
  have hs : (∑u∈rows,(‖original eta1 (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
      1 u.val W1 t1 X1‖^2*∏i,‖mark i u‖^2)^2) ≤ (C*x^2*U^(r1/2))^2 := by
    apply hshort.trans
    calc
      _ ≤ C^2*x^4*U^r1 := by gcongr; exact hAC.trans hCC
      _ = _ := by simp only [mul_pow,hp];ring
  have hl : (∑u∈rows,‖original eta2 (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
      1 u.val W2 t2 X2‖^4) ≤ (C*y^2*U^(r2/2))^2 := by
    apply hlong.trans
    calc
      _ ≤ C^2*y^4*U^r2 := by gcongr; exact hBC.trans hCC
      _ = _ := by simp only [mul_pow,hp];ring
  have he := finite_reference_of_fourths Finset.univ rows eta1 eta2 W1 W2 t1 t2 X1 X2 mark
    (by positivity : 0≤ C*x^2*U^(r1/2)) (by positivity : 0≤ C*y^2*U^(r2/2))
    hs hl
  change finiteEnergy rows eta1 eta2 W1 W2 t1 t2 X1 X2 mark ≤ _ at he
  apply he.trans_eq
  rw [show (r1+r2)/2=r1/2+r2/2 by ring,Real.rpow_add hU]
  ring

end
end QRH.Cycle092.ReferenceArmRadial
#print axioms QRH.Cycle092.ReferenceArmRadial.independent_radius_cauchy

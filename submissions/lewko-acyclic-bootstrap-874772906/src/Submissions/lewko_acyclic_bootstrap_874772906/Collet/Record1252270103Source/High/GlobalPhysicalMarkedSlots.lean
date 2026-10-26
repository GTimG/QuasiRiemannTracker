/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual frozen marked factor is removed only through its existing puncture.
The live squarefree projector remains the literal collision tuple polynomial. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Second.RestoredNewtonPositive
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.CorrectedRowsForward

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open Record1252270103Second Record1252270103Source
open CenteredMomentSecondHeightFamily CenteredMomentSourceRectangleMask
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

/-- No nonzero row-character division occurs: the zero branch vanishes before
using the puncture to split the frozen squarefree factor. -/
theorem marked_frozen_row_factor (K R M : Ideal O) (hKR : K∣R)
    (τ : Character) (t : ℝ) (z : O) :
    QRH.Record1252270103TwoIdeal.squarefreeIndicator (K*M)*
        rowWeight τ (fixedBadMask*idealGenerator R) 1 z t M=
      QRH.Record1252270103TwoIdeal.squarefreeIndicator K*
        QRH.Record1252270103TwoIdeal.squarefreeIndicator M*
          rowWeight τ (fixedBadMask*idealGenerator R) 1 z t M := by
  by_cases hz : rowWeight τ (fixedBadMask*idealGenerator R) 1 z t M=0
  · simp only [hz,mul_zero]
  have hc : IsCoprime M R := by
    by_contra hn
    apply hz
    rw [←rowWeight_ideal_mask τ fixedBadMask 1 z t (dvd_mul_right _ _) (dvd_mul_left _ _)]
    simp only [hn,ite_false,zero_mul]
  have hcop : IsCoprime K M := (hc.of_isCoprime_of_dvd_right hKR).symm
  rw [Record1252270103Source.Collision.squarefreeIndicator_mul_of_coprime K M hcop]

theorem marked_newton_slots_collision (s : Input ι) (K R : Ideal O) (hKR : K∣R)
    (τ : Character) (t : ℝ) (z : O) :
    markedNewtonSlots s K R τ t z=
      QRH.Record1252270103TwoIdeal.squarefreeIndicator K*
        QRH.Record1252270103Source.Collision.normalizedMarkedTupleRow τ
          (fixedBadMask*idealGenerator R) 1 z t s.slots (restoredSlotCoeff s) s.P := by
  have hs : (Real.sqrt (∏i,s.P i):ℂ)⁻¹=∏i,(Real.sqrt (s.P i):ℂ)⁻¹ := by
    rw [Real.sqrt_prod Finset.univ (fun i _=>(s.P_pos i).le)]
    simp only [Complex.ofReal_prod,Finset.prod_inv_distrib]
  unfold markedNewtonSlots QRH.Record1252270103Source.Collision.normalizedMarkedTupleRow
  rw [hs,mul_left_comm _ (∏i,(Real.sqrt (s.P i):ℂ)⁻¹)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hh := marked_frozen_row_factor K R (∏i,(v i:Ideal O)) hKR τ t z
  calc
    _=(QRH.Record1252270103TwoIdeal.squarefreeIndicator (K*∏i,(v i:Ideal O))*
        rowWeight τ (fixedBadMask*idealGenerator R) 1 z t (∏i,(v i:Ideal O)))*
          (∏i,restoredSlotCoeff s i (v i)) := by ring
    _=_ := by rw [hh];ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.marked_frozen_row_factor
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.marked_newton_slots_collision

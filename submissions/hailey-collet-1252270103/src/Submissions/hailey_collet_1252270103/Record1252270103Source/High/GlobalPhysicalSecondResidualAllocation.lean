/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The full residual pool is retained inside each actual second allocation.
There is no residual-cardinality estimate and no row-divisibility shortcut. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSecondChildRows
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.JointForcedSelection
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile
open Record1252270103Source Record1252270103Second Collision
open Admission.JointForced
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem marked_plain_full_residual_allocation (s : Input ι)
    (A₁ A₂ D K C R seed : Ideal O) (F : Ideal O→ℂ)
    (hC : Supported C) (hseed : seed∣C)
    (Ls : Finset (Ideal O)) (τ : Character) (t : ℝ) (z : O) :
    (∑L∈Ls,‖modifiedPlainColumn s (markedSourceModifier A₁ A₂ D K F)
      C hC R seed L τ t z‖^2)≤
      ((actualAllocations s.pools C).card:ℝ)*∑B:actualAllocations s.pools C,
        ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
          ((volume (child s C R B τ t)/volume s)*
            ∑L∈Ls,‖normalizedRow (child s C R B τ t)
              (markedSourceModifier (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1))
                (D*C) (K*markedProduct B.val) F) (R*C) L τ t z‖^2) := by
  calc
    _≤∑L∈Ls,((actualAllocations s.pools C).card:ℝ)*∑B:actualAllocations s.pools C,
        ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
          ((volume (child s C R B τ t)/volume s)*
            ‖normalizedRow (child s C R B τ t)
              (markedSourceModifier (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1))
                (D*C) (K*markedProduct B.val) F) (R*C) L τ t z‖^2) := by
      apply Finset.sum_le_sum
      intro L hL
      exact marked_plain_allocation_rows s A₁ A₂ D K C R seed L F hC hseed τ t z
    _=_ := by
      rw [←Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro B hB
      rw [←Finset.mul_sum,←Finset.mul_sum]

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.marked_plain_full_residual_allocation

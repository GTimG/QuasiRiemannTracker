import Candidate.Cycle63.Moment.PrimaryMaskTransport
import Candidate.Cycle63.Moment.CanonicalFirstNorm

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open ActualEisensteinCubic CenteredMomentCanonicalFirst CenteredMomentFirstColumns
open CenteredMomentChildRows CenteredMomentNaturalRowSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCommonSupport RayFourExpansion
local notation "O" => HeckeFamily.O

theorem first_signed_prime_dvd_conductor (C D : Ideal O) (hC : Supported C)
    (P : ActiveIndex C D) : firstSignedPrime C D P ∣ activeConductor C D := by
  obtain ⟨u,hu⟩ := actual_first_conductor_unit C D hC
  rw [hu]
  exact dvd_mul_of_dvd_right
    (Finset.dvd_prod_of_mem (firstSignedPrime C D) (Finset.mem_univ P)) _

end
end OAI.SevenEighths.Cycle63Moment

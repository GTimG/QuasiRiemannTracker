/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.AuxiliaryZeroPayment
import Candidate.Uneven.AuxiliaryZeroScalar

set_option autoImplicit false
namespace OAI.SevenEighths.AuxiliaryReconstruction
noncomputable section
open Cycle63InitialMass CenteredMomentSectorLocalization

/-- The auxiliary zero reserve is 3/50. Its sharper amplifier upper bound
leaves the same final 1/20 saving after the scheduled losses. -/
theorem auxiliary_geometry_zero_exponent_saving
    (Z M A a ξ reserve padding ε εmass B count b : ℝ)
    (hM : 0 ≤ M)
    (hb : Sil.Uneven.AuxiliarySource.widthLo ≤ b ∧ b ≤ Sil.Uneven.AuxiliarySource.widthHi)
    (ha : a ≤ M*Sil.Uneven.AuxiliarySource.amp b)
    (hloss : frequencyLoss Z 32 ξ+reserve+ε*(A+padding)+B*εmass+3*count ≤ M/380) :
    zeroPaymentExponent Z M A a ξ reserve padding ε εmass B+3*count ≤ -M/20 := by
  have hamp := mul_le_mul_of_nonneg_left (auxiliary_amplifier_upper hb) hM
  unfold zeroPaymentExponent
  linarith only [hM,hamp,ha,hloss]

end
end OAI.SevenEighths.AuxiliaryReconstruction

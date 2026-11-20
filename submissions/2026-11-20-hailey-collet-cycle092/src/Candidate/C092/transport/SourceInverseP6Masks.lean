/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The unit puncture in the actual regular state preserves the original slots,
including their complex phases, without an extra mask-opening hypothesis. -/
import Candidate.C092.transport.SourceInverseP6Attaining

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentSecondHeightFamily CenteredMomentEnergyState
open ConcretePrimeRowBridge ProbeHighRowFamily HeckeInverseAmplification
local notation "O" => HeckeFamily.O

theorem unit_mask_slot (η : Character) (u : FreeRow) (pool : Finset (Ideal O))
    (β : Ideal O→ℂ) (t P : ℝ) :
    normalizedSlot η (fixedBadMask*idealGenerator 1) 1 u.val pool β t P =
      normalizedSlot η fixedBadMask 1 u.val pool β t P := by
  simp only [normalizedSlot,CenteredMomentHeckeSlots.rowSlot,one_mul,
    natural_unit_mask_coefficient (naturalRow η u.val u.property.1)]

theorem regular_state_slot {Z B bΦ : ℝ} (s : NaturalState Z B bΦ)
    (η : Character) (hη : s.character=η) (hp : s.puncture=1)
    (u : FreeRow) (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (t P : ℝ) :
    normalizedSlot s.character s.mask 1 u.val pool β t P =
      normalizedSlot η fixedBadMask 1 u.val pool β t P := by
  rw [hη,NaturalState.mask,hp]
  exact unit_mask_slot η u pool β t P

#print axioms regular_state_slot
end
end QRH.Cycle092.SourceInverseP6

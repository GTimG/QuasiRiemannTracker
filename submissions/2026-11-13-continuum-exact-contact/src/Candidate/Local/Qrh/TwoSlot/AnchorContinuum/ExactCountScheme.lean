/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The exact tangent's count scheme, reusing the admitted native windows. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ExactCountWindow
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.CountScheme

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum.Contact
noncomputable section
open Qrh.TwoSlot.AnchorZeroLoss

@[instance_reducible] def exactScheme : Affine.Return.ImprovedCountScheme exactLine where
  toCountScheme := RationalReturn.scheme.toCountScheme
  toCapacityBounds := exact_capacity
  improved := [Affine.Return.ExactWindow.window]
  improved_face := by
    intro w hw
    simp only [List.mem_singleton] at hw
    subst w
    have hs := RationalReturn.scheme.improved_face
      (w := Affine.Return.ContinuumQ.window)
      (show Affine.Return.ContinuumQ.window ∈ RationalReturn.scheme.improved from by
        change Affine.Return.ContinuumQ.window ∈ [Affine.Return.ContinuumQ.window]
        exact List.mem_singleton_self _)
    exact hs

end
end Qrh.TwoSlot.AnchorContinuum.Contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.exactScheme

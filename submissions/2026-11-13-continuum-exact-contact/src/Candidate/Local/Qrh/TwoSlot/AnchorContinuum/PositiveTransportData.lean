/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Actual baseline data at an arbitrary positive conductor extension. The full
transport parameters and early common meshes are supplied by the existing
constructor, with a smaller requested budget. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.Transport.TransportParameters

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open OAI.SevenEighths
variable [Geometry.Parameters]
variable [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds]

/-- Choose the genuine finite slot partition, detector data, contour and phase
parameters before the arithmetic data, fitting any positive extension. All
existing transport constraints are retained as well. -/
theorem exists_data_with_extension {κ budget Δ : ℝ}
    (hk : (7/10:ℝ) ≤ κ) (hkhi : κ ≤ (3/4:ℝ))
    (hb : 0 < budget) (hΔ : 0 < Δ) (extraMesh : ℝ → ℝ)
    (hExtra : ∀ t : ℝ, 0 < t → 0 < extraMesh t) :
    ∃ D : BaselineData, D.momentKappa = κ ∧ 159*D.ε+609*D.t ≤ budget ∧
      D.t ≤ Δ/4 ∧ Δ/2+2*D.t ≤ Δ ∧
      Geometry.h+Δ/2+2*D.t ≤ Geometry.h+Δ ∧
      (∀ j, D.length j ≤ Cycle25.sourceMesh D.t/200) ∧
      (∀ j, D.length j ≤ commonMesh D.t/200) ∧
      (∀ j, D.length j ≤ extraMesh D.t/200) ∧
      Nonempty (TransportParameters D) := by
  have hsmall : 0 < min budget Δ := lt_min hb hΔ
  obtain ⟨D,hκ,hbudget,hfine,hcommon,hextra,hP⟩ :=
    exists_compatible_data_with_mesh hk hkhi hsmall extraMesh hExtra
  have hbound : 159*D.ε+609*D.t ≤ budget := hbudget.trans (min_le_left _ _)
  have hboundΔ : 159*D.ε+609*D.t ≤ Δ := hbudget.trans (min_le_right _ _)
  have ht : D.t ≤ Δ/4 := by linarith [D.epsilon_pos,D.t_pos]
  refine ⟨D,hκ,hbound,ht,?_,?_,hfine,hcommon,hextra,hP⟩ <;> linarith

/-- The same construction may spend only a prescribed fraction of a positive
row fee. This keeps the count-loss reserve and extension choice synchronized. -/
theorem exists_data_with_fee_and_extension {κ budget Δ fee : ℝ}
    (hk : (7/10:ℝ) ≤ κ) (hkhi : κ ≤ (3/4:ℝ))
    (hb : 0 < budget) (hΔ : 0 < Δ) (hfee : 0 < fee)
    (extraMesh : ℝ → ℝ) (hExtra : ∀ t : ℝ, 0 < t → 0 < extraMesh t) :
    ∃ D : BaselineData, D.momentKappa = κ ∧
      159*D.ε+609*D.t ≤ budget ∧ 159*D.ε+609*D.t ≤ fee/4 ∧
      D.t ≤ Δ/4 ∧ Δ/2+2*D.t ≤ Δ ∧
      (∀ j, D.length j ≤ Cycle25.sourceMesh D.t/200) ∧
      (∀ j, D.length j ≤ commonMesh D.t/200) ∧
      (∀ j, D.length j ≤ extraMesh D.t/200) ∧
      Nonempty (TransportParameters D) := by
  have hsmall : 0 < min budget (fee/4) := lt_min hb (by positivity)
  obtain ⟨D,hκ,hbudget,ht,hpad,_,hfine,hcommon,hextra,hP⟩ :=
    exists_data_with_extension hk hkhi hsmall hΔ extraMesh hExtra
  exact ⟨D,hκ,hbudget.trans (min_le_left _ _),hbudget.trans (min_le_right _ _),
    ht,hpad,hfine,hcommon,hextra,hP⟩

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.exists_data_with_extension
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.exists_data_with_fee_and_extension

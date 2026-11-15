/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The actual chosen physical source, detector and count data can be fixed at
arbitrary positive extension and fee budgets, on one early common mesh. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveTransportData
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.Chosen

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open OAI.SevenEighths
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds]
variable [scheme : Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

/-- The physical source, full prime/slot data and count parameters are actual
objects from the inherited analytic constructors. No PhysicalSchedule instance
or fixed fee is needed to choose them. -/
theorem exists_chosen_with_costs
    (hgap : Geometry.theta < HeckeZeroSupremum.beta)
    (hcap : 2*HeckeZeroSupremum.beta-1 ≤ scheme.naturalκ)
    {Δ fee : ℝ} (hΔ : 0 < Δ) (hfee : 0 < fee)
    (mesh : ℝ → ℝ) (hmesh : ∀ t : ℝ, 0 < t → 0 < mesh t) :
    ∃ A : ChosenData, A.sourceMesh = mesh A.D.t ∧
      A.D.t ≤ Δ/4 ∧ Δ/2+2*A.D.t ≤ Δ ∧
      159*A.D.ε+609*A.D.t ≤ fee/4 := by
  have hk : (7/10:ℝ) ≤ 2*HeckeZeroSupremum.beta-1 := by
    linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds.theta_bounds.1]
  have hkhi : 2*HeckeZeroSupremum.beta-1 ≤ (3/4:ℝ) :=
    hcap.trans scheme.natural_hi
  obtain ⟨D,hκ,hbudget,hfeeBudget,ht,hpad,hfine,_hcommon,hextra,⟨P⟩⟩ :=
    exists_data_with_fee_and_extension hk hkhi
      (show 0 < (HeckeZeroSupremum.beta-Geometry.theta)/10000 by positivity)
      hΔ hfee mesh hmesh
  obtain ⟨F⟩ := QRH.Record1252270103Return.GenericPhysical.exists_baseline_source D
  let SF := baselineSource D F
  obtain ⟨co,κo,Ko,ca,κa,Ka,hco,hco1,hκo,hKo,hca,hca1,hκa,hKa,hcount⟩ :=
    Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCount.fixed_amplitude_selected_envelope_count
      SF.modulus ⊤ le_top SF.S SF.w SF.smooth SF.compact SF.positive_support
      (fun y => (SF.bounded y).1) SF.nonzero 1 2 1
      (by norm_num) (by norm_num) (by norm_num) SF.support
      (fun y => (SF.bounded y).2) D.t D.t_pos
  let counts : CountParameters SF.modulus ⊤ D.t :=
    ⟨co,κo,Ko,ca,κa,Ka,hco,hco1,hκo,hKo,hca,hca1,hκa,hKa,hcount⟩
  exact ⟨⟨D,hκ,hκ.symm ▸ hcap,hbudget,hfine,mesh D.t,hmesh D.t D.t_pos,
    hextra,P,F,counts⟩,rfl,ht,hpad,hfeeBudget⟩

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.exists_chosen_with_costs

/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Use the actual stationary cutoff from the checked contact argument and the
paper's exact shift. No arbitrary conductor or isolated point is chosen. -/
import Candidate.C092.transport.FinalCycle092Endpoint
import Candidate.C092.transport.MixedTicketTailsContact
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorContinuum.ParameterPrecision
set_option autoImplicit false
noncomputable section
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103Return
namespace QRH.Cycle092.Final

def conductorQ : ℝ := Qrh.TwoSlot.AnchorContinuum.Contact.stationaryCutoff+22595743/10000000000

theorem conductorQ_bounds : Cycle090.hLower ≤ conductorQ ∧ conductorQ ≤ Cycle090.hUpper := by
  have hc:=Qrh.TwoSlot.AnchorContinuum.Contact.Precision.cutoff_bounds
  exact ActualGeometry.shifted_contact_mem hc.1.le (by linarith only [hc.2])

theorem target_at_true_contact
    (h : letI : Geometry.Parameters := ActualGeometry.parameters conductorQ conductorQ_bounds.1 conductorQ_bounds.2
      letI : ActualGeometry.WidenedCoreBounds := ActualGeometry.widenedBounds conductorQ conductorQ_bounds.1 conductorQ_bounds.2
      MixedUpperEstimate Qrh.TwoSlot.AnchorContinuum.Contact.theta) :
    HeckeZeroSupremum.beta ≤ Cycle090.theta ∧
    (∀ (η:Character) (s:ℂ),Cycle090.theta<s.re → (s≠1 ∨ η.residue≠1) → LFunction η s≠0) ∧
      Cycle090.OrdinaryTarget :=
  canonical_targets_of_mixed conductorQ conductorQ_bounds.1 conductorQ_bounds.2 _ MixedTicketTails.actual_contact_root h

#print axioms conductorQ_bounds
#print axioms target_at_true_contact
end QRH.Cycle092.Final

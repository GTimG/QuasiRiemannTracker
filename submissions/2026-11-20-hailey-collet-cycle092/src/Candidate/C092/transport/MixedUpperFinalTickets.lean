/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Select a literal original mixed ticket from the actual full phase point. -/
import Candidate.C092.transport.ActualMixedPriceEndpoint
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open scoped Classical
open QRH.Cycle092.TopData

def originalPhaseTicket (δ p : ℝ) : Row :=
  if h : ∃r∈rows,r.box.Contains (δ,p) then Classical.choose h
  else ⟨0,⟨0,0,0,0⟩,0⟩

/-- Ticket selection uses the full original phase mean. Its proof is fixed
before the conductor split and every response or error-prime mask. -/
theorem original_phase_ticket {h contact d δ p : ℝ}
    (hpaid : ActualMixedPrice.MixedPaid h contact d (δ,p)) :
    originalPhaseTicket δ p∈rows ∧ (originalPhaseTicket δ p).box.Contains (δ,p) := by
  obtain ⟨r,hr,hp,_⟩:=hpaid
  have he : ∃r∈rows,r.box.Contains (δ,p):=⟨r,hr,hp⟩
  simp only [originalPhaseTicket,dif_pos he]
  exact Classical.choose_spec he

#print axioms original_phase_ticket
end
end QRH.Cycle092.MixedUpperFinal

/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Continuous scalar coverage of a finite anchor stage. This is an adapter
for the physical source step, not an endpoint or an analytic supplier. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.OrdinaryStage
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.CertificateCheck

set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorContinuum
open Qrh.TwoSlot.AnchorExtension.ChainData

/-- The three ordinary/reference gates hold throughout the stage once
they hold at both ends. The mesh and number of stages play no role. -/
theorem ordinary_gates_between {R z k a b r : ℝ} (hab : a < b)
    (hlo : a ≤ r) (hhi : r ≤ b)
    (h2a : 0 < 137/1000-fS R z k a) (h2b : 0 < 137/1000-fS R z k b)
    (h4a : 0 < 9/10-a-fS R z k a-4*fu R a)
    (h4b : 0 < 9/10-b-fS R z k b-4*fu R b)
    (h6a : 0 < 5/6+21/250-a-fS R z k a-3*fu R a-1/100)
    (h6b : 0 < 5/6+21/250-b-fS R z k b-3*fu R b-1/100) :
    0 < 137/1000-fS R z k r ∧
    0 < 9/10-r-fS R z k r-4*fu R r ∧
    0 < 5/6+21/250-r-fS R z k r-3*fu R r-1/100 := by
  refine ⟨?_,?_,?_⟩
  · exact Qrh.MarkedAnchor.Price.pos_affine
      (f := fun x => 137/1000-fS R z k x)
      (fun x => by simp only [fS,fY,fu]; ring) hab hlo hhi h2a h2b
  · exact Qrh.MarkedAnchor.Price.pos_affine
      (f := fun x => 9/10-x-fS R z k x-4*fu R x)
      (fun x => by simp only [fS,fY,fu]; ring) hab hlo hhi h4a h4b
  · exact Qrh.MarkedAnchor.Price.pos_affine
      (f := fun x => 5/6+21/250-x-fS R z k x-3*fu R x-1/100)
      (fun x => by simp only [fS,fY,fu]; ring) hab hlo hhi h6a h6b

/-- Affine source-output minorants also extend across the complete stage. -/
theorem source_minorant_between {R z k a0 a1 pad a b r : ℝ}
    (hab : a < b) (hlo : a ≤ r) (hhi : r ≤ b)
    (ha : a0-a1*a+pad < fY R z k a)
    (hb : a0-a1*b+pad < fY R z k b) :
    a0-a1*r+pad < fY R z k r := by
  have h := Qrh.MarkedAnchor.Price.pos_affine
    (f := fun x => fY R z k x-(a0-a1*x+pad))
    (fun x => by simp only [fY,fu]; ring) hab hlo hhi
    (by linarith) (by linarith)
  linarith

end Qrh.TwoSlot.AnchorContinuum
#print axioms Qrh.TwoSlot.AnchorContinuum.ordinary_gates_between
#print axioms Qrh.TwoSlot.AnchorContinuum.source_minorant_between

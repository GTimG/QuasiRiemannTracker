/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedMiddleReturnDecomposition
set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open Cycle25.Numerator Cycle25.Weighted.Numerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.SelectedNonfloor

/-- Return the exact native energy subtype sum to the original free rows. -/
theorem common_sum (rows common : Finset FreeRow) (hsub : common⊆rows) (f : FreeRow→ℝ) :
    (∑u∈commonIndices rows common,f u.val)=∑u∈common,f u := by
  classical
  apply Finset.sum_bij (fun u _=>u.val)
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · intro u hu v hv he
    exact Subtype.ext he
  · intro u hu
    exact ⟨⟨u,hsub hu⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩,rfl⟩
  · intro u hu
    rfl

variable [Geometry.Parameters]
/-- Every complete tuple box is summed on the SAME original finite rows,
with the complementary main product intact. No coefficient tail is hidden
in the outer finite multiplicity. -/
theorem original_boxes_norm (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (rows : Finset FreeRow)
    (Z : ℝ) (x z : ℂ)
    (data : ∀u : rows,PhysicalReflectionData F.S F.exclusions.prime u.val)
    (Y U xi : ℝ) (n : ℕ) (hY : 0<Y)
    (hrow : ∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hmargin : 1+4*D.e≤x.re+1/2) (main : FreeRow→ℂ) :
    (∑u : rows,‖errorPacket D F J η u.val Z x z Y*main u.val‖)≤
      ∑j∈Finset.range (n+1),∑u : rows,
        ‖originalBoxPacket D F J η u.val Z x z (data u) Y U xi n j*main u.val‖ := by
  calc
    _ ≤ ∑u : rows,∑j∈Finset.range (n+1),
      ‖originalBoxPacket D F J η u.val Z x z (data u) Y U xi n j*main u.val‖ := by
      apply Finset.sum_le_sum
      intro u _
      rw [original_packet_boxes D F J η u.val Z x z (data u) Y U xi n hY
        (hrow u.val u.property) hx hz hmargin,Finset.sum_mul]
      exact norm_sum_le _ _
    _ = _ := Finset.sum_comm

#print axioms common_sum
#print axioms original_boxes_norm
end
end QRH.Cycle092.MixedMiddleReturn

/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsLargeActual
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open ProbePhysical HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor
open QRH.Cycle092.PacketJoin
open Cycle25.Weighted.Numerator
namespace QRH.Cycle092.MixedTicketTails
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]
lemma large_class_mask_empty (D : BaselineData) (F : BaselineSourceData D) (J : Finset (Fin D.N))
    (rows : Finset FreeRow) (data : ∀u:rows,PhysicalReflectionData F.S F.exclusions.prime u.val)
    (η : Character) (Z d a : ℝ) (x z : ℂ) (Y vcut : ℝ)
    (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
    (hZ : 0<Z) (hd : 0<d)
    (hempty : MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin=∅) :
    largeClassMaskNorm D F J rows data η Z d a x z Y vcut bin=0 := by
  have heq := amplitudeCell_eq_original D F Z d a hZ hd rows z bin
  rw [heq] at hempty
  unfold largeClassMaskNorm
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro u hu
  exact False.elim ((Finset.not_nonempty_iff_eq_empty.mpr hempty) ⟨u.val,u.property⟩)
end QRH.Cycle092.MixedTicketTails
#print axioms QRH.Cycle092.MixedTicketTails.large_class_mask_empty

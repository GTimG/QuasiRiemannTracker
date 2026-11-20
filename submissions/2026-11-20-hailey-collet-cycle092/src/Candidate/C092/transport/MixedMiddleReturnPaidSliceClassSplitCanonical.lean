/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Canonical true reflection data and exact original small/large coefficient join. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceClassSource
import Candidate.C092.transport.MixedTicketTailsLargeActual
import Candidate.C092.transport.MixedUpperFinalSplit
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open ProbeRowRadicalConductor HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open Cycle25.Numerator Cycle25.Weighted.Numerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MediumWitness QRH.Cycle092.MixedTicketTails
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Genuine reflection is constructed only on the original nonprincipal rows. -/
def classCanonicalData (D : BaselineData) (F : BaselineSourceData D) (rows : Finset FreeRow)
    (hn : ∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) :
    ∀u : rows,PhysicalReflectionData F.S F.exclusions.prime u.val :=
  fun u=>Classical.choice (physical_reflection_data_exists F.S F.exclusions.prime u.val (hn u.val u.property))

def classCanonicalLarge (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (Z : ℝ) (x z : ℂ)
    (Y U : ℝ) (r : TopData.Row) (u : FreeRow) : ℂ :=
  if hn : (rowCharacter F.S F.exclusions.prime u).residue≠1 then
    largeLabelPolynomialPacket F.S F.exclusions η u
      (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
      (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W Y
      (Classical.choice (physical_reflection_data_exists F.S F.exclusions.prime u hn)).combinedConductor
      (fixedConductorConstant F.S) U (originalVcut r) else 0

/-- The SAME actual original packet splits at the strict OLD small cutoff.
No phase class, prime mask, coefficient index or main factor changes. -/
theorem class_coefficient_split (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (u : FreeRow) (Z a : ℝ) (x z : ℂ)
    (Y U : ℝ) (r : TopData.Row)
    (hn : (rowCharacter F.S F.exclusions.prime u).residue≠1)
    (ha : 51/100 ≤ a) (hx : x.re=a+16*D.e) (hz : z.re=17/50) (hY : 0<Y) :
    errorPacket D F J η u Z x z Y=
      classCanonicalSmall D F J η Z x z Y U r u+classCanonicalLarge D F J η Z x z Y U r u := by
  rw [classCanonicalSmall,classCanonicalLarge,dif_pos hn,dif_pos hn]
  exact actual_original_coefficient_split D F J η u
    (Classical.choice (physical_reflection_data_exists F.S F.exclusions.prime u hn)) Z a x z Y U
    (originalVcut r) hn ha hx hz hY

/-- The original largeClassMaskNorm uses the identical canonical reflection
on the original rows. Its physical phase slice equals the literal cell. -/
theorem class_large_original (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (rows : Finset FreeRow)
    (hn : ∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)
    (Z d a : ℝ) (x z : ℂ) (Y : ℝ) (r : TopData.Row) (hZ : 0<Z) (hd : 0<d)
    (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t) :
    mainFront D J Z*(∑u∈amplitudeCell D F Z d a rows (fun _=>z) bin,
      ‖classCanonicalLarge D F J η Z x z Y (Z^d) r u*mainProduct D F J u Z z‖)=
    largeClassMaskNorm D F J rows (classCanonicalData D F rows hn) η Z d a x z Y (originalVcut r) bin := by
  unfold largeClassMaskNorm
  dsimp only
  conv_lhs => rw [PacketJoin.amplitudeCell_eq_original D F Z d a hZ hd rows z bin]
  rw [←Finset.sum_coe_sort]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  rw [classCanonicalLarge,dif_pos (hn u.val (Finset.filter_subset _ _ u.property))]
  rfl

#print axioms class_coefficient_split
#print axioms class_large_original
end
end QRH.Cycle092.MixedMiddleReturn

/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact full original packet join: untouched exits, true remaining small class,
and one original large packet over the full phase cell for each error mask. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceClassSplitCanonical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly
open QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MediumWitness QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount QRH.Cycle092.MixedUpperFinal
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]
variable {D : BaselineData} {F : BaselineSourceData D} {η : Character}
variable {Z d a : ℝ} {rows : Finset FreeRow} {z : ℂ}
variable {bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t}
variable {t₀ γ τ : ℝ} {i : ℕ}

/-- All original masks are joined on the SAME genuine physical source bank.
Only remaining classes use small+large; exit classes keep their full packet.
The original largeClassMaskNorm is paid ONCE on the complete original cell.
This is exact algebra with no analytic moment/count/price premise. -/
theorem actual_packet_class_split (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (cap : ℝ) (hcap : 0<cap) (hfine : ∀s,D.length s ≤ cap/200)
    (middle : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d))→Prop)
    (hn : ∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)
    (hZ : 0<Z) (ha : 51/100 ≤ a) (x : ℂ) (hx : x.re=a+16*D.e) (hz : z.re=17/50)
    (Y : ℝ) (hY : 0<Y) (r : TopData.Row) :
    packetNorm D F (amplitudeCell D F Z d a rows (fun _=>z) bin) η Z x z Y ≤
      (∑σ∈Finset.univ.filter (fun σ=>¬middle σ),
        packetNorm D F ((B.layoutCap P hd hdhi cap hcap hfine).common σ) η Z x z Y)+
      (∑σ∈Finset.univ.filter middle,∑J∈Finset.univ.powerset,
        classSmallNorm D F J η Z x z Y (Z^d) r ((B.layoutCap P hd hdhi cap hcap hfine).common σ))+
      (∑J∈Finset.univ.powerset,
        largeClassMaskNorm D F J rows (classCanonicalData D F rows hn) η Z d a x z Y (originalVcut r) bin) := by
  classical
  let L:=B.layoutCap P hd hdhi cap hcap hfine
  let Exit:=Finset.univ.filter (fun σ=>¬middle σ)
  let Mid:=Finset.univ.filter middle
  let Cell:=amplitudeCell D F Z d a rows (fun _=>z) bin
  have hmask (J : Finset (Fin D.N)) :
      mainFront D J Z*(∑u∈Cell,‖errorPacket D F J η u Z x z Y*mainProduct D F J u Z z‖) ≤
      (∑σ∈Exit,mainFront D J Z*(∑u∈L.common σ,‖errorPacket D F J η u Z x z Y*mainProduct D F J u Z z‖))+
      (∑σ∈Mid,classSmallNorm D F J η Z x z Y (Z^d) r (L.common σ))+
      largeClassMaskNorm D F J rows (classCanonicalData D F rows hn) η Z d a x z Y (originalVcut r) bin := by
    have hs:=B.norm_split P hd hdhi middle
      (fun u=>errorPacket D F J η u Z x z Y*mainProduct D F J u Z z)
      (fun u=>classCanonicalSmall D F J η Z x z Y (Z^d) r u*mainProduct D F J u Z z)
      (fun u=>classCanonicalLarge D F J η Z x z Y (Z^d) r u*mainProduct D F J u Z z)
      (fun u hu=>by rw [class_coefficient_split D F J η u Z a x z Y (Z^d) r
        (hn u (Finset.mem_filter.mp hu).1) ha hx hz hY,add_mul])
    apply (mul_le_mul_of_nonneg_left hs (show 0 ≤ mainFront D J Z by unfold mainFront;positivity)).trans_eq
    rw [mul_add,mul_add,Finset.mul_sum,Finset.mul_sum]
    rw [class_large_original D F J η rows hn Z d a x z Y r hZ (by linarith) bin]
    rfl
  unfold packetNorm
  calc
    _ ≤ ∑J∈Finset.univ.powerset,
      ((∑σ∈Exit,mainFront D J Z*(∑u∈L.common σ,‖errorPacket D F J η u Z x z Y*mainProduct D F J u Z z‖))+
      (∑σ∈Mid,classSmallNorm D F J η Z x z Y (Z^d) r (L.common σ))+
      largeClassMaskNorm D F J rows (classCanonicalData D F rows hn) η Z d a x z Y (originalVcut r) bin) :=
      Finset.sum_le_sum (fun J _=>hmask J)
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
      congr 2
      · exact Finset.sum_comm
      · exact Finset.sum_comm

#print axioms actual_packet_class_split
end
end QRH.Cycle092.MixedMiddleReturn

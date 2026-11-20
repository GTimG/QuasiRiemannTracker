/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite phase join on one fixed true bank family, including all empty cells. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSlicePhaseBanks
import Candidate.C092.transport.MixedMiddleReturnPaidSliceClassSplit
import Candidate.C092.transport.MixedUpperFinalExitPhaseSumData
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MediumWitness
open QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount QRH.Cycle092.PacketJoinE49
open QRH.Cycle092.MixedUpperFinal QRH.Cycle092.MixedTicketTails QRH.Cycle090
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Actual remaining descriptor/all-mask norm. Both empty original phases
and bins outside the supplied fixed family contribute exactly zero. -/
def phaseMiddleNorm (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z : ℝ) (P : TransportParameters D) (d a : ℝ) (rows : Finset FreeRow) (z : ℂ) (τ : ℝ) (i : ℕ)
    (hd : (1/2:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (bins : Finset (BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t))
    (data : ∀bin∈bins,∀hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty,
      ExitPhaseData D F η Z P d a rows z bin τ i)
    (cap : ℝ) (hcap : 0<cap) (hfCap : ∀s,D.length s ≤ cap/200)
    (x : ℂ) (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t) : ℝ :=
  if hb : bin∈bins then
    if hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty then
      ∑σ∈Finset.univ.filter (data bin hb hne).remaining,∑J∈Finset.univ.powerset,
        classSmallNorm D F J η Z x z (Z^Geometry.y) (Z^d) (data bin hb hne).r
          (((data bin hb hne).bank.layoutCap P (by linarith) hdhi cap hcap hfCap).common σ)
    else 0
  else 0

/-- Original complete phase packets join into counted exits, genuine middle
small packets and the original large packet paid once per original mask.
The same fixed data.bank appears in every part; no analytic bound is assumed. -/
theorem actual_phase_packet_split (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z : ℝ) (P : TransportParameters D) (d a : ℝ) (rows : Finset FreeRow) (z : ℂ) (τ : ℝ) (i : ℕ)
    (hd : (1/2:ℝ) ≤ d) (hdhi : d ≤ 7/8)
    (bins : Finset (BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t))
    (data : ∀bin∈bins,∀hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty,
      ExitPhaseData D F η Z P d a rows z bin τ i)
    (ticket : ∀bin hb hne,(data bin hb hne).r=paidPhaseTicket D d a bin)
    (cap : ℝ) (hcap : 0<cap) (hfCap : ∀s,D.length s ≤ cap/200)
    (hn : ∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)
    (hZ : 0<Z) (ha : 51/100 ≤ a) (x : ℂ) (hx : x.re=a+16*D.e) (hz : z.re=17/50) :
    (∑bin∈bins,packetNorm D F (amplitudeCell D F Z d a rows (fun _=>z) bin) η Z x z (Z^Geometry.y)) ≤
      (∑bin∈bins,∑σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)),
        phaseExitClassNorm D F η Z P d a rows z τ i hd bins data x σ bin)+
      (∑bin∈bins,phaseMiddleNorm D F η Z P d a rows z τ i hd hdhi bins data cap hcap hfCap x bin)+
      (∑bin∈bins,∑J∈Finset.univ.powerset,
        largeClassMaskNorm D F J rows (classCanonicalData D F rows hn) η Z d a x z
          (Z^Geometry.y) (originalVcut (paidPhaseTicket D d a bin)) bin) := by
  classical
  have hbin (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t) (hb : bin∈bins) :
      packetNorm D F (amplitudeCell D F Z d a rows (fun _=>z) bin) η Z x z (Z^Geometry.y) ≤
      (∑σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)),
        phaseExitClassNorm D F η Z P d a rows z τ i hd bins data x σ bin)+
      phaseMiddleNorm D F η Z P d a rows z τ i hd hdhi bins data cap hcap hfCap x bin+
      (∑J∈Finset.univ.powerset,
        largeClassMaskNorm D F J rows (classCanonicalData D F rows hn) η Z d a x z
          (Z^Geometry.y) (originalVcut (paidPhaseTicket D d a bin)) bin) := by
    by_cases hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty
    · let A:=data bin hb hne
      have he:=phaseExitClassNorm_sum_eq D F η Z P d a rows z τ i hd hdhi bins data x bin hb hne
      have hecap : (∑σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)),
          phaseExitClassNorm D F η Z P d a rows z τ i hd bins data x σ bin)=
          ∑σ∈Finset.univ.filter (fun σ=>¬A.remaining σ),
            packetNorm D F ((A.bank.layoutCap P (by linarith) hdhi cap hcap hfCap).common σ) η Z x z (Z^Geometry.y) := by
        simpa only [CellBank.layoutCap_common] using he
      have hm : phaseMiddleNorm D F η Z P d a rows z τ i hd hdhi bins data cap hcap hfCap x bin=
          ∑σ∈Finset.univ.filter A.remaining,∑J∈Finset.univ.powerset,
            classSmallNorm D F J η Z x z (Z^Geometry.y) (Z^d) A.r
              ((A.bank.layoutCap P (by linarith) hdhi cap hcap hfCap).common σ) := by
        dsimp only [phaseMiddleNorm]
        rw [dif_pos hb,dif_pos hne]
      have hs:=actual_packet_class_split A.bank P (by linarith) hdhi cap hcap hfCap A.remaining
        hn hZ ha x hx hz (Z^Geometry.y) (by positivity) A.r
      have hl : (∑J∈Finset.univ.powerset,
          largeClassMaskNorm D F J rows (classCanonicalData D F rows hn) η Z d a x z
            (Z^Geometry.y) (originalVcut A.r) bin)=
          ∑J∈Finset.univ.powerset,
          largeClassMaskNorm D F J rows (classCanonicalData D F rows hn) η Z d a x z
            (Z^Geometry.y) (originalVcut (paidPhaseTicket D d a bin)) bin := by
        apply Finset.sum_congr rfl
        intro J hJ
        rw [show A.r=paidPhaseTicket D d a bin from ticket bin hb hne]
      have hem := congrArg₂ (fun e m : ℝ=>e+m) hecap.symm hm.symm
      exact hs.trans_eq (congrArg₂ (fun em l : ℝ=>em+l) hem hl)
    · have hempty:=Finset.not_nonempty_iff_eq_empty.mp hne
      have hlarge : 0 ≤ ∑J∈Finset.univ.powerset,
          largeClassMaskNorm D F J rows (classCanonicalData D F rows hn) η Z d a x z
            (Z^Geometry.y) (originalVcut (paidPhaseTicket D d a bin)) bin := by
        apply Finset.sum_nonneg
        intro J hJ
        unfold largeClassMaskNorm
        exact mul_nonneg (by unfold mainFront;positivity) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))
      have hzero : packetNorm D F (amplitudeCell D F Z d a rows (fun _=>z) bin) η Z x z (Z^Geometry.y)=0 := by
        rw [hempty]
        simp only [packetNorm,Finset.sum_empty,mul_zero,Finset.sum_const_zero]
      rw [hzero]
      simp only [phaseMiddleNorm,dif_pos hb,dif_neg hne,phaseExitClassNorm,phaseExitKeep,
        ite_false,Finset.sum_const_zero,zero_add]
      exact hlarge
  calc
    _ ≤ ∑bin∈bins,((∑σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)),
        phaseExitClassNorm D F η Z P d a rows z τ i hd bins data x σ bin)+
      phaseMiddleNorm D F η Z P d a rows z τ i hd hdhi bins data cap hcap hfCap x bin+
      (∑J∈Finset.univ.powerset,
        largeClassMaskNorm D F J rows (classCanonicalData D F rows hn) η Z d a x z
          (Z^Geometry.y) (originalVcut (paidPhaseTicket D d a bin)) bin)) := Finset.sum_le_sum hbin
    _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_add_distrib]

#print axioms actual_phase_packet_split
end
end QRH.Cycle092.MixedMiddleReturn

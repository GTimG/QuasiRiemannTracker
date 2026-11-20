/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine source counts on every frozen bank class outside the middle branch. -/
import Candidate.C092.transport.MixedUpperFinalExitPhaseData
import Candidate.C092.transport.MixedUpperFinalExits
import Candidate.C092.transport.MixedOutsideActualFourthLog
set_option autoImplicit false
set_option allowUnsafeReducibility true
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
attribute [local reducible] QRH.Record1252270103Return.GenericPhysical.BaselineData.toMomentData
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MediumWitness QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount
open QRH.Cycle092.PacketJoin HeckeDetectorRawFiber
open QRH.Cycle092.PacketJoinE49 QRH.Cycle090 QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]


/-- Native counted exits on the SAME actual selected banks, including every
original mask and phase prefactor. Only geometric source/ticket metadata and
the explicit early fee reserve are inputs; no count or price is assumed. -/
theorem actual_selected_exit_phase_sum
    (h : ℝ) (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    (hgeometry : (inferInstance : Geometry.Parameters)=ActualGeometry.parameters h hh hh')
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκ : 2*HeckeZeroSupremum.beta-1 ≤ (3/4:ℝ))
    (affineError : ℝ) (haff : 0 < affineError) (logLoss : ℝ) (hlogLoss : 0 < logLoss) :
    ∃mc : ℝ→ℝ,(∀t,0<t → 0 < mc t) ∧ ∃mp : ℝ,0 < mp ∧
    ∀(D : BaselineData)(F : BaselineSourceData D),
      (∀s,D.length s ≤ mc D.t/200) →
      (∀s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
      (∀s,D.length s ≤ mp/200) →
      (∀s,D.length s ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)/200) →
      2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa →
    ∀η : Character,∃m : ℕ,∃C0 : ℝ,0 < C0 ∧
    ∀(P : TransportParameters D)(padding τ : ℝ),0 < τ →
      4*τ < (1/200:ℝ)*D.cost → padding+2*D.t ≤ 1/10000000000 → ∀n : ℕ,
    ∀ᶠZ : ℝ in atTop,1 < Z ∧ ∀idx grid : FreeRow→ℕ,
    selected D F padding τ n η Z idx grid →
    ∀k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀i∈Finset.range (n+1),∀j : ℕ,
      (cellRows D F padding Z idx grid k i j).Nonempty →
    let d := sourceDyadConductor Z D.t k
    let a : ℝ := 51/100+D.e*j
    let rows := cellRows D F padding Z idx grid k i j
    ∀hd : (1/2:ℝ) ≤ d,∀(x z : ℂ),x.re=a+16*D.e → z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ →
    ∀bins : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t),
    ∀data : ∀bin∈bins,∀hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty,
      ExitPhaseData D F η Z P d a rows z bin τ i,
    ∀σ : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t →
      Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)),
    (∀bin hb hne,¬(data bin hb hne).remaining (σ bin)) →
    ∀fee : ℝ,
      d*(3*(countLoss D.ε P.mesh D.t+logLoss)/4+nativeMoment D affineError/4+nativeMass D a d)+fee+rowPad ≤
        1/2000000000000 →
    (∑bin∈bins,SelectedNonfloor.packetNorm D F
      (phaseExitCommon D F η Z P d a rows z τ i hd bins data σ bin) η Z x z (Z^Geometry.y)) ≤
      C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^d)^(SelectedNonfloor.finalPower a d sourceCost fee (theta-1/2000000000000)) := by
  obtain ⟨mc,hmc,hcounts⟩ := actual_bank_exit_counts h hh hh' hgeometry hβ hκ logLoss
  obtain ⟨mp,hmp,hpacket⟩ := actual_common_phase_sum_log_bound hβ affineError haff logLoss hlogLoss
  refine ⟨mc,hmc,mp,hmp,?_⟩
  intro D F hfCount hfSource hfPacket hfCommon hkβ η
  obtain ⟨Cc,hCc,Jc,hcounts⟩ := hcounts D F hfCount hfSource D.epsilon_count_small (by linarith [D.t_small])
    D.momentKappa D.momentKappa_lo D.momentKappa_hi hkβ η
  obtain ⟨m,C0,hC0,hpacket⟩ := hpacket D F hfPacket hfCommon hfSource hkβ Cc Jc
  refine ⟨m,C0,hC0,?_⟩
  intro P padding τ hτ hheight hpad n
  filter_upwards [hcounts,hpacket P padding τ hτ hheight hpad n η,
    actual_cell_native_data D F P padding τ hτ hheight hpad n η] with Z hc hp hg
  refine ⟨hp.1,?_⟩
  intro idx grid hs k hk i hi j hn
  dsimp only
  intro hd x z hx hz him bins data σ hnot fee hbudget
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  let rows := cellRows D F padding Z idx grid k i j
  let common := phaseExitCommon D F η Z P d a rows z τ i hd bins data σ
  obtain ⟨hdhi,ha,hahi,hrows,hphase⟩ := hg.2 idx grid hs k hk i hi j hn
  change d ≤ 7/8 at hdhi
  change 51/100 < a at ha
  change a ≤ 7/8 at hahi
  have hsub : ∀bin∈bins,common bin ⊆ amplitudeCell D F Z d a rows (fun _=>z) bin := by
    intro bin hb
    by_cases hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty
    · change phaseExitCommon D F η Z P d a rows z τ i hd bins data σ bin ⊆ _
      simp only [phaseExitCommon,dif_pos hb,dif_pos hne,dif_pos hdhi]
      let B := (data bin hb hne).bank
      by_cases hcommon : ((B.layout P (by linarith) hdhi).common (σ bin)).Nonempty
      · exact ((B.layout P (by linarith) hdhi).common_subset (σ bin) hcommon (0:Offset)).trans
          (B.native_rows_subset P (by linarith) hdhi (σ bin) hcommon (0:Offset))
      · rw [Finset.not_nonempty_iff_eq_empty.mp hcommon]
        exact Finset.empty_subset _
    · simp only [common,phaseExitCommon,dif_pos hb,dif_neg hne,Finset.empty_subset]
  apply hp.2 idx grid hs k hk i hi j hn hd x z hx hz him bins common hsub fee (theta-1/2000000000000)
  intro bin hb hneCommon
  have hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty := hneCommon.mono (hsub bin hb)
  let A := data bin hb hne
  let I := A.toInput hd hdhi ha hahi (fun u hu=>(hrows u hu).1) hz him
  have heq : I.layout.common (σ bin)=common bin := by
    simp only [common,phaseExitCommon,dif_pos hb,dif_pos hne,dif_pos hdhi]
    rfl
  have hnotI : ¬I.remaining (σ bin) := hnot bin hb hne
  have hbI : I.d*(3*(countLoss D.ε I.P.mesh D.t+logLoss)/4+nativeMoment D affineError/4+nativeMass D I.a I.d)+fee+rowPad ≤
      1/2000000000000 := hbudget
  obtain ⟨R,hcard,hprice⟩ := hc.2 I (nativeMoment D affineError) (nativeMass D a d) fee hbI (σ bin)
    (heq.symm ▸ hneCommon) hnotI
  refine ⟨R,?_,hprice⟩
  rw [heq] at hcard
  change ((common bin).card:ℝ) ≤ outsideCountEnvelope Cc Jc Z d τ i*(dyadicLength (Z^d):ℝ)^2*(Z^d)^R at hcard
  exact hcard

#print axioms actual_selected_exit_phase_sum
end
end QRH.Cycle092.MixedUpperFinal

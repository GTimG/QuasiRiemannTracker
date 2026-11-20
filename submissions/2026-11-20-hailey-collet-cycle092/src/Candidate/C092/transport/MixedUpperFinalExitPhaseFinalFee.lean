/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine source counts on every frozen bank class outside the middle branch. -/
import Candidate.C092.transport.MixedUpperFinalExitPhaseActual
import Candidate.C092.transport.MixedUpperFinalReserve
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


theorem actual_selected_exit_phase_sum_final_fee
    (h : ℝ) (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    (hgeometry : (inferInstance : Geometry.Parameters)=ActualGeometry.parameters h hh hh')
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκ : 2*HeckeZeroSupremum.beta-1 ≤ (3/4:ℝ))
    (affineError : ℝ) (haff : 0 < affineError) (loss logLoss : ℝ)
    (hloss : 0 < loss) (hlogLoss : 0 < logLoss) (hle : logLoss ≤ loss) :
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
    159*D.ε+12*D.t+P.mesh+16*D.e+2*P.eps+affineError/4+loss+2*rowPad ≤
      1/100000000000000 →
    (∑bin∈bins,SelectedNonfloor.packetNorm D F
      (phaseExitCommon D F η Z P d a rows z τ i hd bins data σ bin) η Z x z (Z^Geometry.y)) ≤
      C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^d)^(SelectedNonfloor.finalPower a d sourceCost (16*D.e+2*P.eps*d+17*D.t/25) (theta-1/2000000000000)) := by
  obtain ⟨mc,hmc,mp,hmp,hpacket⟩ := actual_selected_exit_phase_sum h hh hh' hgeometry hβ hκ affineError haff logLoss hlogLoss
  refine ⟨mc,hmc,mp,hmp,?_⟩
  intro D F hfCount hfSource hfPacket hfCommon hkβ η
  obtain ⟨m,C0,hC0,hpacket⟩ := hpacket D F hfCount hfSource hfPacket hfCommon hkβ η
  refine ⟨m,C0,hC0,?_⟩
  intro P padding τ hτ hheight hpad n
  filter_upwards [hpacket P padding τ hτ hheight hpad n,
    actual_cell_native_data D F P padding τ hτ hheight hpad n η] with Z hp hg
  refine ⟨hp.1,?_⟩
  intro idx grid hs k hk i hi j hn
  dsimp only
  intro hd x z hx hz him bins data σ hnot hreserve
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  obtain ⟨hdhi,ha,hahi,hrows,hphase⟩ := hg.2 idx grid hs k hk i hi j hn
  change d ≤ 7/8 at hdhi
  change 51/100 < a at ha
  change a ≤ 7/8 at hahi
  have hb := actual_exit_fee_paid D P a d affineError loss logLoss (by dsimp [d];linarith)
    (by linarith) (by linarith) hahi haff.le hloss.le hle hlogLoss.le hreserve
  exact hp.2 idx grid hs k hk i hi j hn hd x z hx hz him bins data σ hnot
    (16*D.e+2*P.eps*d+17*D.t/25) hb

#print axioms actual_selected_exit_phase_sum_final_fee
end
end QRH.Cycle092.MixedUpperFinal

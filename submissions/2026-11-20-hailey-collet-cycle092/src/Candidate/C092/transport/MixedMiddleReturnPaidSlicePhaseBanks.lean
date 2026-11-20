/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual selected-cell phase bank factory at the literal original mixed ticket.
One genuine bank per nonempty big phase is fixed for every later consumer. -/
import Candidate.C092.transport.MixedUpperFinalActualBanks
import Candidate.C092.transport.MixedUpperFinalTickets
import Candidate.C092.transport.MixedUpperFinalExitPhaseData
set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MediumWitness
open QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount QRH.Cycle092.PacketJoinE49
open QRH.Cycle092.MixedUpperFinal QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.MixedTicketTails
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- The ticket is selected by the FULL original amplitude phase mean,
before any response descriptor or original prime/error mask. -/
def paidPhaseTicket (D : BaselineData) (d a : ℝ)
    (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t) : Row :=
  originalPhaseTicket (2*a-1)
    (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))

/-- Only the original conductor guard partitions the original finite bins.
No response, count estimate, error mask or witness choice enters this split. -/
def paidPhaseBigBins (D : BaselineData) (d a : ℝ)
    (bins : Finset (BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)) :=
  bins.filter (fun bin=>originalDlow (paidPhaseTicket D d a bin) ≤ d)

/-- Actual selected rows construct the entire phase metadata family. The
source cap/fine proof is fixed before the later transport. Every future split,
small price and exit price uses the SAME chosen actual CellBank in this family.
There is no Layout, source, count, moment or amplitude estimate premise. -/
theorem actual_selected_phase_banks (D : BaselineData) (F : BaselineSourceData D)
    (cap : ℝ) (hcap : 0<cap) (hfCap : ∀s,D.length s ≤ cap/200)
    (hcollar : D.ε ≤ 3*witnessCollar)
    (P : TransportParameters D) (padding τ : ℝ) (hτ : 0<τ)
    (hheight : 4*τ<(1/200:ℝ)*D.cost) (hpad : padding+2*D.t ≤ 1/10000000000)
    (n : ℕ) (η : Character) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀idx grid : FreeRow→ℕ,
    selected D F padding τ n η Z idx grid →
    ∀k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀i∈Finset.range (n+1),∀j0 : ℕ,
    (cellRows D F padding Z idx grid k i j0).Nonempty →
    let d:=sourceDyadConductor Z D.t k
    let a:ℝ:=51/100+D.e*j0
    let rows:=cellRows D F padding Z idx grid k i j0
    (1/2:ℝ) ≤ d → d ≤ Geometry.h+rowPad →
    ∀z : ℂ,z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ →
    ∀ (contact : ℝ) (bins : Finset (BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)),
    (∀bin∈bins,(amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty →
      ActualMixedPrice.MixedPaid Geometry.h contact d
        (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))) →
    ∃data : ∀bin∈paidPhaseBigBins D d a bins,
      ∀hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty,
        ExitPhaseData D F η Z P d a rows z bin τ i,
    ∀bin hb hne,
      (data bin hb hne).r=paidPhaseTicket D d a bin ∧
      (data bin hb hne).cap=cap ∧
      (data bin hb hne).t₀=Return.cutoffI (2*a-1)
        (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) ∧
      (data bin hb hne).γ=(Mixed.rowGamma (paidPhaseTicket D d a bin).box (paidPhaseTicket D d a bin).B:ℝ) := by
  classical
  filter_upwards [actual_selected_mixed_banks D F P padding τ hτ hheight hpad n η] with Z hB
  refine ⟨hB.1,?_⟩
  intro idx grid hsel k hk i hi j0 hneCell
  dsimp only
  intro hd hdmax z hz him contact bins hpaid
  let d:=sourceDyadConductor Z D.t k
  let a:ℝ:=51/100+D.e*j0
  let rows:=cellRows D F padding Z idx grid k i j0
  have banks:=(hB.2 idx grid hsel k hk i hi j0 hneCell).2.2.2.2.2
  let data : ∀bin∈paidPhaseBigBins D d a bins,
      ∀hne : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty,
        ExitPhaseData D F η Z P d a rows z bin τ i := fun bin hb hne=>
    let hb0 : bin∈bins := (Finset.mem_filter.mp hb).1
    let hold : originalDlow (paidPhaseTicket D d a bin) ≤ d := (Finset.mem_filter.mp hb).2
    let ht := original_phase_ticket (hpaid bin hb0 hne)
    let B := Classical.choice (banks z hz him bin hne (paidPhaseTicket D d a bin) ht.1 ht.2)
    ExitPhaseData.ofCellBank (P:=P) (paidPhaseTicket D d a bin) ht.1 ht.2 B cap hcap hfCap hcollar hold hdmax
  refine ⟨data,?_⟩
  intro bin hb hne
  exact ⟨rfl,rfl,rfl,rfl⟩

#print axioms actual_selected_phase_banks
end
end QRH.Cycle092.MixedMiddleReturn

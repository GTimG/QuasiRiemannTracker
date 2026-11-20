/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original mixed ticket fixes a real same-zero response bank on each cell. -/
import Candidate.C092.transport.MixedUpperFinalAdmission
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MediumWitness
open QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount QRH.Cycle092.PacketJoinE49
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- The actual full phase mean and original mixed row choose the endpoints.
No layout, source response, zero or analytic estimate is an input. -/
theorem actual_selected_mixed_banks (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding τ : ℝ) (hτ : 0<τ)
    (hheight : 4*τ<(1/200:ℝ)*D.cost) (hpad : padding+2*D.t ≤ 1/10000000000)
    (n : ℕ) (η : Character) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀idx grid : FreeRow→ℕ,
    selected D F padding τ n η Z idx grid →
    ∀k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀i∈Finset.range (n+1),∀j : ℕ,
    (cellRows D F padding Z idx grid k i j).Nonempty →
    let d:=sourceDyadConductor Z D.t k
    let a:ℝ:=51/100+D.e*j
    let rows:=cellRows D F padding Z idx grid k i j
    (1/100:ℝ) ≤ d ∧ d ≤ 7/8 ∧ 51/100<a ∧ a ≤ 7/8 ∧
    (∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u) ∧
    ∀z : ℂ,z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ →
    ∀bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
    (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty →
    ∀r : TopData.Row,r∈TopData.rows →
    r.box.Contains (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) →
      Nonempty (CellBank D F η Z d a rows z bin
        (Return.cutoffI (2*a-1) (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)))
        (Mixed.rowGamma r.box r.B) τ i) := by
  filter_upwards [actual_selected_cell_banks D F P padding τ hτ hheight hpad n η] with Z h
  refine ⟨h.1,?_⟩
  intro idx grid hs k hk i hi j hne
  dsimp only
  obtain ⟨hd,hdhi,ha,hahi,hlow,hbanks⟩:=h.2 idx grid hs k hk i hi j hne
  refine ⟨hd,hdhi,ha,hahi,hlow,?_⟩
  intro z hz him bin hnebin r hr hp
  have hb:=original_bank_admission hr hp
  exact hbanks z hz him bin hnebin _ _ hb.2.1 hb.2.2.2.1 hb.2.2.2.2.1

#print axioms actual_selected_mixed_banks
end
end QRH.Cycle092.MixedUpperFinal

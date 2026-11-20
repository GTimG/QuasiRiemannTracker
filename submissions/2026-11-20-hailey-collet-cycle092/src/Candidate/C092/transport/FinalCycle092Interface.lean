/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The residual input is only the authentic mixed upper phase sum. -/
import Candidate.C092.transport.NaturalPacketLowEstablished
import Candidate.C092.transport.PacketJoinUpperCover
import Candidate.C092.transport.SelectedActualData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeDetectorWitnessRows HeckeDetectorBatch
open ProbePhysical HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor
open QRH.Cycle092.Direct QRH.Cycle092.DirectCount QRH.Coverage QRH.Cycle092.PacketJoin
namespace QRH.Cycle092.Final
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

def reserve : ℝ := 1/10000000000000

/-- No packet premise is imposed below conductor 19/25 or on any proved upper
sector. The bins here retain their original full-row class mean, original
amplitude rows, all physical masks and both contour coordinates. The common
mesh and finite polynomial degree precede the physical height and scale. -/
def MixedUpperEstimate (contact : ℝ) : Prop :=
  Geometry.theta < HeckeZeroSupremum.beta →
  ∀ (affineError loss : ℝ),0<affineError → 0<loss →
  ∃ mc : ℝ→ℝ,(∀ t,0<t → 0 < mc t) ∧ ∃ mp : ℝ,0 < mp ∧
  ∀ (D : BaselineData) (F : BaselineSourceData D),
  (∀ s,D.length s ≤ mc D.t/200) → (∀ s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
  (∀ s,D.length s ≤ mp/200) → (∀ s,D.length s ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)/200) →
  2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa →
  ∀ η : Character,∃ m : ℕ,∃ C0 : ℝ,0<C0 ∧
  ∀ (P : TransportParameters D) (padding τ : ℝ),0<τ →
  4*τ<(1/200:ℝ)*D.cost → padding+2*D.t ≤ 1/10000000000 → ∀ n : ℕ,
  ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀ idx grid : FreeRow→ℕ,
  selected D F padding τ n η Z idx grid →
  ∀ k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀ i∈Finset.range (n+1),∀ j : ℕ,
  (cellRows D F padding Z idx grid k i j).Nonempty →
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  let rows := cellRows D F padding Z idx grid k i j
  (19/25:ℝ)<d → d ≤ Geometry.h+Cycle090.rowPad → ∀ (x z : ℂ),
  x.re=a+16*D.e → z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ →
  ∀ bins : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t),
  (∀ bin∈bins,(MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty →
    ¬upperSectorAdmission (2*a-1)
      (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) ∧
    ActualMixedPrice.MixedPaid Geometry.h contact d
      (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))) →
  159*D.ε+12*D.t+P.mesh+16*D.e+2*P.eps+affineError/4+loss+2*Cycle090.rowPad ≤ 1/100000000000000 →
  (∑ bin∈bins,packetNorm D F (MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin)
    η Z x z (Z^Geometry.y)) ≤
    C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
      (Z^d)^(finalPower a d Cycle090.sourceCost (16*D.e+2*P.eps*d+17*D.t/25)
        (Cycle090.theta-reserve))

end QRH.Cycle092.Final

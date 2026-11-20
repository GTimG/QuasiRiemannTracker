/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Natural packets with the finite prefactors paid from an early power reserve. -/
import Candidate.C092.transport.NaturalPacketLowCells
import Candidate.C092.transport.IncumbentMoment
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeDetectorWitnessRows HeckeDetectorBatch
open ProbePhysical HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor
open QRH.Cycle092.Direct QRH.Cycle092.DirectCount QRH.Coverage
open QRH.Cycle092.PacketJoin
open Cycle25.Weighted.FullWContour
namespace QRH.Cycle092.NaturalPacketLow
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

theorem actual_natural_lower_whole_final_fee_established (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (loss : ℝ) (hloss : 0<loss) :
    ∃ mc : ℝ→ℝ,(∀ t,0<t → 0 < mc t) ∧
    ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀ s,D.length s ≤  mc D.t/200) → (∀ s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
    ∀ η : Character,∃ m : ℕ,∃ C0 : ℝ,0 < C0 ∧
    ∀ (P : TransportParameters D) (padding τ : ℝ),0<τ →
    4*τ<(1/200:ℝ)*D.cost → padding+2*D.t ≤ 1/10000000000 → ∀ n : ℕ,
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀ idx grid : FreeRow→ℕ,
    selected D F padding τ n η Z idx grid →
    ∀ k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀ i∈Finset.range (n+1),∀ j : ℕ,
    (cellRows D F padding Z idx grid k i j).Nonempty →
    let d := sourceDyadConductor Z D.t k
    let a : ℝ := 51/100+D.e*j
    let rows := cellRows D F padding Z idx grid k i j
    d ≤ 19/25 → ∀ (x z : ℂ),x.re=a+16*D.e → z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ →
    Cycle090.hLower ≤ Geometry.h → Geometry.h ≤ Cycle090.hUpper →
    Geometry.ell=Physical.ell → ∀ eps : ℝ,0  ≤  eps → 0  ≤  P.mesh →
    159*D.ε+12*D.t+P.mesh+16*D.e+2*eps+loss  ≤  1/5000000 →
    packetNorm D F rows η Z x z (Z^Geometry.y) ≤
      C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^d)^(finalPower a d Cycle090.sourceCost (16*D.e+2*eps*d+17*D.t/25) (Cycle090.theta-1/5000000)) := by
  exact actual_natural_lower_whole_final_fee hβ QRH.Cycle092.Incumbent.established_moment loss hloss

theorem actual_natural_lower_final_power_cells_established (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (loss : ℝ) (hloss : 0<loss) :
    ∃ mc : ℝ→ℝ,(∀ t,0<t → 0 < mc t) ∧
    ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀ s,D.length s ≤  mc D.t/200) → (∀ s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
    ∀ η : Character,∃ m : ℕ,∃ C0 : ℝ,0 < C0 ∧
    ∀ (P : TransportParameters D) (padding τ : ℝ),0<τ →
    4*τ<(1/200:ℝ)*D.cost → padding+2*D.t ≤ 1/10000000000 → ∀ n : ℕ,
    ∀ (saving allowance eps : ℝ),Cycle090.hLower ≤ Geometry.h → Geometry.h ≤ Cycle090.hUpper →
    Geometry.ell=Physical.ell → 0 ≤ eps → 0 ≤ P.mesh →
    159*D.ε+12*D.t+P.mesh+16*D.e+2*eps+loss ≤ 1/5000000 →
    Cycle090.theta-1/5000000 ≤ HeckeZeroSupremum.beta-saving-3*allowance →
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀ idx grid : FreeRow→ℕ,
    selected D F padding τ n η Z idx grid →
    ∀ k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀ i∈Finset.range (n+1),
    ∀ j∈Finset.range (⌊(49/100:ℝ)/D.e⌋₊+1),
    (cellRows D F padding Z idx grid k i j).Nonempty →
    let d := sourceDyadConductor Z D.t k
    let a : ℝ := 51/100+D.e*j
    d ≤ 19/25 → ∀ q∈szRectangle ((3*i+1:ℕ)*Z^τ),
      packetNorm D F (cellRows D F padding Z idx grid k i j) η Z
        ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I) (Z^Geometry.y) ≤
      C0*(3+(3*i+1:ℕ)*Z^τ)^(m:ℝ)*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^d)^(finalPower a d Cycle090.sourceCost (16*D.e+2*eps*d+17*D.t/25)
          (HeckeZeroSupremum.beta-saving-3*allowance)) := by
  simpa only [Real.rpow_natCast] using
    actual_natural_lower_final_power_cells hβ QRH.Cycle092.Incumbent.established_moment loss hloss

end QRH.Cycle092.NaturalPacketLow
#print axioms QRH.Cycle092.NaturalPacketLow.actual_natural_lower_whole_final_fee_established
#print axioms QRH.Cycle092.NaturalPacketLow.actual_natural_lower_final_power_cells_established

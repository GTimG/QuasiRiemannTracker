/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Entire original error packets on actual selected native-direct cell slices. -/
import Candidate.C092.transport.MixedOutsideActualFourthMask
import Candidate.C092.transport.PacketJoinActual
import Candidate.C092.transport.PacketJoinEnvelope

import Candidate.C092.transport.PacketFinalPower
import Candidate.C092.transport.Direct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths
open ProbePhysical HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorBatch
open HeckeDetectorWitnessRows HeckeDetectorRawFiber
open Cycle25.Weighted.Numerator Cycle25.Numerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor
open QRH.Cycle092.Direct QRH.Cycle092.DirectCount
namespace QRH.Cycle092.PacketJoin
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- All original masks on an arbitrary actual common subfamily, using its
own count exponent R and the caller's proved scalar admission price. -/
theorem actual_common_packet_final_power (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (affineError : ℝ) (haff : 0 < affineError) :
    ∃ mp : ℝ,0 < mp ∧ ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀ s,D.length s ≤ mp/200) →
    (∀ s,D.length s ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)/200) →
    (∀ s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
    2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa →
    ∃ degree : Finset (Fin D.N)→ℕ,∃ C : Finset (Fin D.N)→ℝ,(∀ J,0 < C J) ∧
    ∀ (P : TransportParameters D) (padding τ : ℝ),0 < τ →
    4*τ < (1/200:ℝ)*D.cost → padding+2*D.t ≤ 1/10000000000 →
    ∀ (n : ℕ) (η : Character),∀ᶠ Z : ℝ in atTop,1 < Z ∧
    ∀ idx grid : FreeRow→ℕ,selected D F padding τ n η Z idx grid →
    ∀ k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀ i∈Finset.range (n+1),∀ j : ℕ,
    (cellRows D F padding Z idx grid k i j).Nonempty →
    let d := sourceDyadConductor Z D.t k
    let a : ℝ := 51/100+D.e*j
    let rows := cellRows D F padding Z idx grid k i j
    (1/2:ℝ) ≤ d → ∀ (x z : ℂ),x.re=a+16*D.e → z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ →
    ∀ bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
    ∀ common : Finset FreeRow,
    common ⊆ MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin → common.Nonempty →
    ∀ R Ccount fee target : ℝ,1 ≤ Ccount → (common.card:ℝ) ≤ Ccount*(Z^d)^R →
    rowPrice (2*a-1)
      (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))
      R d Cycle090.sourceCost+d*(nativeMoment D affineError/4+nativeMass D a d)+fee ≤ target →
    packetNorm D F common η Z x z (Z^Geometry.y) ≤
      (∑ J∈Finset.univ.powerset,outsideMaskWeight D J Ccount (C J) (degree J) Z d τ i)*
        (Z^d)^(finalPower a d Cycle090.sourceCost fee target) := by
  obtain ⟨mp,hmp,hpacket⟩ := actual_common_mask_bound hβ affineError haff
  refine ⟨mp,hmp,?_⟩
  intro D F hfPacket hfCommon hfSource hkβ
  choose degree C hC hpacket using hpacket D F hfPacket hfCommon hfSource hkβ
  refine ⟨degree,C,hC,?_⟩
  intro P padding τ hτ hheight hpad n η
  have hpAll := Filter.eventually_all.mpr (fun J=>hpacket J P padding τ hτ hheight hpad n η)
  filter_upwards [hpAll] with Z hp
  refine ⟨(hp ∅).1,?_⟩
  intro idx grid hs k hk i hi j hn
  dsimp only
  intro hd x z hx hz him bin common hsub hne R Ccount fee target hCc hcard hprice
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  let W := fun J=>outsideMaskWeight D J Ccount (C J) (degree J) Z d τ i
  have hd0 : 0 < d := by dsimp [d];linarith
  have hZ0 : 0 < Z := zero_lt_one.trans (hp ∅).1
  have hCc0 : 0 < Ccount := zero_lt_one.trans_le hCc
  have hW (J : Finset (Fin D.N)) : 0 ≤ W J := by
    have hCJ := hC J
    have hH : 0 ≤ nativeHeight Z d τ i := by unfold nativeHeight;positivity
    dsimp [W,outsideMaskWeight,mainFront]
    positivity
  apply packet_of_partition_prices D F common η Z x z (Z^Geometry.y)
    (fun _=>({()} : Finset Unit)) (fun _ _=>()) (by intros;simp)
    a d Cycle090.sourceCost fee target (∑ J∈Finset.univ.powerset,W J)
    (hp ∅).1.le hd0 (fun J _=>W J) (fun J _ _ _=>hW J) (by simp)
  intro J hJ b hb hneSlice
  cases b
  refine ⟨_,R,nativeMoment D affineError,nativeMass D a d,hprice,?_⟩
  have hm := (hp J).2 idx grid hs k hk i hi j hn hd x z hx hz him bin common hsub hne R Ccount hCc hcard
  simpa only [Finset.filter_true,eq_self] using hm
end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.actual_common_packet_final_power

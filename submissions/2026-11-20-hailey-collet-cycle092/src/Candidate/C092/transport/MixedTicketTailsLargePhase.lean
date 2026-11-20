/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native packets with the finite prefactors paid from an early power reserve. -/
import Candidate.C092.transport.PacketJoinEnvelope
import Candidate.C092.transport.MixedTicketTailsLargeEmpty
import Candidate.C092.transport.MixedTicketTailsLargePaid
import Candidate.C092.transport.PacketJoinPhaseSum
import Candidate.C092.transport.MixedTicketTailsRawPrice
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
open QRH.Cycle092.PacketJoin QRH.Cycle092.TopData QRH.Cycle092.RawTicket
open Cycle25.Weighted.Numerator
namespace QRH.Cycle092.MixedTicketTails
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]


/- Collect all physically nonempty phase cells with their original tickets. -/
theorem actual_original_large_phase_sum_absorbed (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (affineError : ℝ) (haff : 0<affineError) (loss : ℝ) (hloss : 0 < loss) :
    ∃ mc : ℝ→ℝ,(∀ t,0<t → 0 < mc t) ∧ ∃ mp : ℝ,0 < mp ∧
    ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀ s,D.length s≤ mc D.t/200) → (∀ s,D.length s≤Cycle25.sourceMesh D.t/200) →
    (∀ s,D.length s≤ mp/200) → (∀ s,D.length s≤Cycle25.Energy.commonMesh 2 0 1 (D.t/4)/200) →
    2*HeckeZeroSupremum.beta-1≤D.momentKappa →
    ∀ η : Character,∃ m : ℕ,∃ C0 : ℝ,0 < C0 ∧
    ∀ (P : TransportParameters D) (padding τ : ℝ),0<τ →
    4*τ<(1/200:ℝ)*D.cost → padding+2*D.t≤1/10000000000 → ∀ n : ℕ,
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀ idx grid : FreeRow→ℕ,
    selected D F padding τ n η Z idx grid →
    ∀ k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀ i∈Finset.range (n+1),∀ j : ℕ,
    (cellRows D F padding Z idx grid k i j).Nonempty →
    let d := sourceDyadConductor Z D.t k
    let a : ℝ := 51/100+D.e*j
    let rows := cellRows D F padding Z idx grid k i j
    (1/2:ℝ)≤d → d≤Geometry.h+Cycle090.rowPad → ∀ (x z : ℂ),x.re=a+16*D.e → z.re=17/50 → |z.im|≤(3*i+1:ℕ)*Z^τ →
    ∀ (data : ∀u:rows,PhysicalReflectionData F.S F.exclusions.prime u.val),
    ∀ bins : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t),
    ∀ ticket : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t → Row,
    (∀ bin∈bins,(MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty →
      ticket bin∈TopData.rows ∧ (ticket bin).box.Contains (2*a-1,
        classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) ∧
      originalDlow (ticket bin)≤d) → Cycle090.hLower≤Geometry.h → Geometry.h≤Cycle090.hUpper →
    Geometry.ell=Physical.ell → ∀ fee : ℝ,
    d*(3*(159*D.ε+8*D.t+P.mesh)/4+nativeMoment D affineError/4+nativeMass D a d)+
      fee+d*loss+2*Cycle090.rowPad≤7*oldFee →
    (∑ bin∈bins,∑ J∈Finset.univ.powerset,
      largeClassMaskNorm D F J rows data η Z d a x z (Z^Geometry.y) (originalVcut (ticket bin)) bin) ≤
      C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^d)^(finalPower a d Cycle090.sourceCost fee (Cycle090.theta-oldFee)) := by
  obtain ⟨mc,hmc,mp,hmp,hpacket⟩ := actual_original_large_slice_absorbed hβ affineError haff loss hloss
  refine ⟨mc,hmc,mp,hmp,?_⟩
  intro D F hfCount hfSource hfPacket hfCommon hkβ η
  obtain ⟨m,C0,hC0,hpacket⟩ := hpacket D F hfCount hfSource hfPacket hfCommon hkβ η
  refine ⟨m,C0,hC0,?_⟩
  intro P padding τ hτ hheight hpad n
  filter_upwards [hpacket P padding τ hτ hheight hpad n] with Z hp
  refine ⟨hp.1,?_⟩
  intro idx grid hs k hk i hi j hn
  dsimp only
  intro hd hdh x z hx hz him data bins ticket hbins hh hh' hell fee hbudget
  have hZ0 : 0 < Z := zero_lt_one.trans hp.1
  have hd0 : 0 < sourceDyadConductor Z D.t k := by linarith
  apply sum_of_card_payment bins _ _ (by positivity)
  intro bin hb
  by_cases hne : (MediumWitness.amplitudeCell D F Z (sourceDyadConductor Z D.t k)
      (51/100+D.e*j) (cellRows D F padding Z idx grid k i j) (fun _=>z) bin).Nonempty
  · obtain ⟨hr,hbox,hdlo⟩ := hbins bin hb hne
    exact hp.2 idx grid hs k hk i hi j hn hd hdh x z hx hz him data bin hne
      (ticket bin) hr hbox hdlo hh hh' hell fee hbudget
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    have hz0 (J : Finset (Fin D.N)) := large_class_mask_empty D F J _ data η Z
      (sourceDyadConductor Z D.t k) (51/100+D.e*j) x z (Z^Geometry.y)
      (originalVcut (ticket bin)) bin hZ0 hd0 hempty
    simp only [hz0,Finset.sum_const_zero,mul_zero]
    positivity
end QRH.Cycle092.MixedTicketTails
#print axioms QRH.Cycle092.MixedTicketTails.actual_original_large_phase_sum_absorbed

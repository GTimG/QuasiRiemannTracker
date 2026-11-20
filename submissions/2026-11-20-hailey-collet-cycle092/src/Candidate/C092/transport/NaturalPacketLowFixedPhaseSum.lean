/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Natural packets with the finite prefactors paid from an early power reserve. -/
import Candidate.C092.transport.NaturalPacketLowFixedAbsorbed
import Candidate.C092.transport.PacketJoinPhaseSum
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
namespace QRH.Cycle092.NaturalPacketLow
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- All natural amplitude slices may be collected. Numerical admission uses
public certificates, while counts, moments, dictionaries and finite payments
are supplied by the original source theorem. -/
theorem actual_natural_fixed_phase_sum_absorbed (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hkβ : 2*HeckeZeroSupremum.beta-1≤kap) (loss : ℝ) (hloss : 0<loss) :
    ∃ mc : ℝ→ℝ,(∀ t,0<t → 0 < mc t) ∧
    ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀ s,D.length s≤ mc D.t/200) → (∀ s,D.length s≤Cycle25.sourceMesh D.t/200) →
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
    d≤19/25 → ∀ (x z : ℂ),x.re=a+16*D.e → z.re=17/50 → |z.im|≤(3*i+1:ℕ)*Z^τ →
    ∀ bins : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t),
    (∀ bin∈bins,
      (MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty →
      ∃ cS cA : DirectCertificate,cS∈directCertificates ∧ cA∈directCertificates ∧
        cS.route=.fixedS ∧ cA.route=.fixedA ∧ cS.edge=1 ∧ cA.edge=1 ∧
        cS.box.Contains (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t
          (fun s=>D.length s/d) bin/(2*a-1)) ∧
        cA.box.Contains (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t
          (fun s=>D.length s/d) bin/(2*a-1))) → Cycle090.hLower≤Geometry.h → Geometry.h≤Cycle090.hUpper →
    Geometry.ell=Physical.ell → ∀ fee : ℝ,
    d*(3*(159*D.ε+8*D.t+P.mesh)/4+(2*D.t)/4+nativeMass D a d)+fee+d*loss≤1/5000000 →
    (∑ bin∈bins,packetNorm D F (MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin)
      η Z x z (Z^Geometry.y)) ≤
      C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^d)^(finalPower a d Cycle090.sourceCost fee (Cycle090.theta-1/5000000)) := by
  obtain ⟨mc,hmc,hpacket⟩ := actual_natural_fixed_slice_absorbed hβ hkβ loss hloss
  refine ⟨mc,hmc,?_⟩
  intro D F hfCount hfSource η
  obtain ⟨m,C0,hC0,hpacket⟩ := hpacket D F hfCount hfSource η
  refine ⟨m,C0,hC0,?_⟩
  intro P padding τ hτ hheight hpad n
  filter_upwards [hpacket P padding τ hτ hheight hpad n] with Z hp
  refine ⟨hp.1,?_⟩
  intro idx grid hs k hk i hi j hn
  dsimp only
  intro hdtop x z hx hz him bins hbins hh hh' hell fee hbudget
  have hZ0 : 0 < Z := zero_lt_one.trans hp.1
  apply sum_of_card_payment bins _ _ (by positivity)
  intro bin hb
  by_cases hne : (MediumWitness.amplitudeCell D F Z (sourceDyadConductor Z D.t k)
      (51/100+D.e*j) (cellRows D F padding Z idx grid k i j) (fun _=>z) bin).Nonempty
  · obtain ⟨cS,cA,hS,hA,hrS,hrA,heS,heA,hbS,hbA⟩ := hbins bin hb hne
    exact hp.2 idx grid hs k hk i hi j hn hdtop x z hx hz him bin hne cS cA hS hA hrS hrA heS heA hbS hbA hh hh' hell fee hbudget
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [packetNorm,Finset.sum_empty,mul_zero,Finset.sum_const_zero]
    positivity

end QRH.Cycle092.NaturalPacketLow
#print axioms QRH.Cycle092.NaturalPacketLow.actual_natural_fixed_phase_sum_absorbed

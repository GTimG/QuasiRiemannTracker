/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native packets with the finite prefactors paid from an early power reserve. -/
import Candidate.C092.transport.PacketJoinEnvelope
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
namespace QRH.Cycle092.PacketJoin
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- The entire phase alphabet is prepaid. Thus this bound can be summed over
any set of native phase slices without changing the constant or height degree.
The positive logarithm loss is fixed before the BaselineData and paid by d*loss. -/
theorem actual_native_slice_absorbed (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
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
    (1/2:ℝ)≤d → d≤Geometry.h → ∀ (x z : ℂ),x.re=a+16*D.e → z.re=17/50 → |z.im|≤(3*i+1:ℕ)*Z^τ →
    ∀ bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
    let slice := MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin
    let p := classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)
    slice.Nonempty → ∀ c : DirectCertificate,c∈directCertificates → c.route=.native → c.edge=3 →
    c.box.Contains (2*a-1,p) → Cycle090.hLower≤Geometry.h → Geometry.h≤Cycle090.hUpper →
    Geometry.ell=Physical.ell → ∀ fee : ℝ,
    d*(3*(159*D.ε+8*D.t+P.mesh)/4+nativeMoment D affineError/4+nativeMass D a d)+fee+d*loss≤1/5000000 →
    (Nat.card (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t):ℝ)*
      packetNorm D F slice η Z x z (Z^Geometry.y) ≤
      C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^d)^(finalPower a d Cycle090.sourceCost fee (Cycle090.theta-1/5000000)) := by
  obtain ⟨mc,hmc,mp,hmp,hpacket⟩ := actual_native_slice_final_power hβ affineError haff
  refine ⟨mc,hmc,mp,hmp,?_⟩
  intro D F hfCount hfSource hfPacket hfCommon hkβ
  obtain ⟨K,hK,hpacket⟩ := hpacket D F hfCount hfSource hfPacket hfCommon hkβ
  intro η
  obtain ⟨Jc,Cc,hCc,degree,C,hC,hpacket⟩ := hpacket η
  obtain ⟨m,C0,hC0,henv⟩ := native_prefactors_absorbed D F K Cc Jc hCc degree C hC loss hloss
  refine ⟨m,C0,hC0,?_⟩
  intro P padding τ hτ hheight hpad n
  filter_upwards [hpacket P padding τ hτ hheight hpad n,henv,
    actual_cell_native_data D F P padding τ hτ hheight hpad n η] with Z hp he hc
  refine ⟨hp.1,?_⟩
  intro idx grid hs k hk i hi j hn
  dsimp only
  intro hd hdh x z hx hz him bin hne c hcCert hr hedge hpbox hh hh' hell fee hbudget
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  have hZ0 : 0 < Z := zero_lt_one.trans hp.1
  have hd0 : 0 < d := by dsimp [d];linarith
  obtain ⟨hdhi,ha,ha',hrest⟩ := hc.2 idx grid hs k hk i hi j hn
  change a ≤ 7/8 at ha'
  have hdhi' : d ≤ 7/8 := hdhi
  have hb := hp.2 idx grid hs k hk i hi j hn hd hdh x z hx hz him bin hne c hcCert hr hedge hpbox hh hh' hell
    (fee+d*loss) (by linarith)
  have he' := he.2 d a τ hd hdhi' ha' hτ.le i
  let bc : ℝ := Nat.card (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t)
  have hbc : 0 ≤ bc := by dsimp [bc];positivity
  have heq : loss+finalPower a d Cycle090.sourceCost (fee+d*loss) (Cycle090.theta-1/5000000) =
      finalPower a d Cycle090.sourceCost fee (Cycle090.theta-1/5000000) := by
    unfold finalPower
    field_simp
    <;> ring
  calc
    _ ≤ bc*((∑ J∈Finset.univ.powerset,actualMaskWeight D F J K Cc (C J) Jc (degree J) Z d a τ i)*
      (Z^d)^(finalPower a d Cycle090.sourceCost (fee+d*loss) (Cycle090.theta-1/5000000))) :=
      mul_le_mul_of_nonneg_left hb hbc
    _ = (bc*(∑ J∈Finset.univ.powerset,actualMaskWeight D F J K Cc (C J) Jc (degree J) Z d a τ i))*
      (Z^d)^(finalPower a d Cycle090.sourceCost (fee+d*loss) (Cycle090.theta-1/5000000)) := by ring
    _ ≤ (C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*(Z^d)^loss)*
      (Z^d)^(finalPower a d Cycle090.sourceCost (fee+d*loss) (Cycle090.theta-1/5000000)) :=
      mul_le_mul_of_nonneg_right he' (Real.rpow_nonneg (Real.rpow_nonneg hZ0.le _) _)
    _ = _ := by rw [mul_assoc,←Real.rpow_add (Real.rpow_pos_of_pos hZ0 _),heq]

end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.actual_native_slice_absorbed

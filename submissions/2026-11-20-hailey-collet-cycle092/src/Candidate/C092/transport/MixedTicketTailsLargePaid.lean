/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native packets with the finite prefactors paid from an early power reserve. -/
import Candidate.C092.transport.PacketJoinEnvelope
import Candidate.C092.transport.MixedTicketTailsLargeActual
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


/-- Complete large-coefficient-dilation numerator packet, all masks and the
entire original phase alphabet prepaid. The only scalar budget is the explicit
early allocation of source/count/logarithm fees; the literal original ticket
pays the actual physical row price. -/
theorem actual_original_large_slice_absorbed (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
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
    ∀ bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
    let slice := MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin
    let p := classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)
    slice.Nonempty → ∀ r : Row,r∈TopData.rows → r.box.Contains (2*a-1,p) →
    originalDlow r≤d → Cycle090.hLower≤Geometry.h → Geometry.h≤Cycle090.hUpper →
    Geometry.ell=Physical.ell → ∀ fee : ℝ,
    d*(3*(159*D.ε+8*D.t+P.mesh)/4+nativeMoment D affineError/4+nativeMass D a d)+
      fee+d*loss+2*Cycle090.rowPad≤7*oldFee →
    (Nat.card (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t):ℝ)*
      (∑ J∈Finset.univ.powerset,largeClassMaskNorm D F J rows data η Z d a x z (Z^Geometry.y) (originalVcut r) bin) ≤
      C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^d)^(finalPower a d Cycle090.sourceCost fee (Cycle090.theta-oldFee)) := by
  obtain ⟨mc,hmc,mp,hmp,hpacket⟩ := actual_large_e49_mask_bound hβ affineError haff
  refine ⟨mc,hmc,mp,hmp,?_⟩
  intro D F hfCount hfSource hfPacket hfCommon hkβ
  obtain ⟨K,hK,hpacket⟩ := hpacket D F hfCount hfSource hfPacket hfCommon hkβ
  intro η
  obtain ⟨Jc,Cc,hCc,hpacket⟩ := hpacket η
  choose degree C hC hpacket using hpacket
  obtain ⟨m,C0,hC0,henv⟩ := native_prefactors_absorbed D F K Cc Jc hCc degree C hC loss hloss
  refine ⟨m,C0,hC0,?_⟩
  intro P padding τ hτ hheight hpad n
  have hpAll := Filter.eventually_all.mpr (fun J=>hpacket J P padding τ hτ hheight hpad n)
  filter_upwards [hpAll,henv,actual_cell_e49_data D F P padding τ hτ hheight hpad n η] with Z hp he hc
  refine ⟨(hp ∅).1,?_⟩
  intro idx grid hs k hk i hi j hn
  dsimp only
  intro hd hdh x z hx hz him data bin hne r hr hpbox hdlo hh hh' hell fee hbudget
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  let rows := cellRows D F padding Z idx grid k i j
  let p := classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)
  have hZ := (hp ∅).1
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hd0 : 0 < d := by dsimp [d];linarith
  obtain ⟨hdhi,ha,ha',hrest⟩ := hc.2 idx grid hs k hk i hi j hn
  change a ≤ 7/8 at ha'
  have hbounds := original_point_bounds hr hpbox
  have hguard := original_e49_available hr hpbox
  have hprice := original_large_price_paid hr hpbox hh hh' hell hdlo hdh
  change rowPrice (2*a-1) p (PacketJoinE49.Return.valueI (2*a-1) p) d Cycle090.sourceCost-
    d*(2*a-1)*originalVcut r/4 < Cycle090.theta-8*oldFee+2*Cycle090.rowPad at hprice
  change d*(3*(159*D.ε+8*D.t+P.mesh)/4+nativeMoment D affineError/4+nativeMass D a d)+
    fee+d*loss+2*Cycle090.rowPad≤7*oldFee at hbudget
  have hcount : rowPrice (2*a-1) p (e49R D P (2*a-1) p) d Cycle090.sourceCost =
      rowPrice (2*a-1) p (PacketJoinE49.Return.valueI (2*a-1) p) d Cycle090.sourceCost+
        3*d*(159*D.ε+8*D.t+P.mesh)/4 := by unfold rowPrice e49R;ring
  have hgain : 0 ≤ d*(2*a-1)*D.t/4 := by
    exact div_nonneg (mul_nonneg (mul_nonneg hd0.le hbounds.1) D.t_pos.le) (by norm_num)
  have hpaid : rowPrice (2*a-1) p (e49R D P (2*a-1) p) d Cycle090.sourceCost+
      d*(nativeMoment D affineError/4+(nativeMass D a d-(2*a-1)*(originalVcut r+D.t)/4))+
        (fee+d*loss) ≤ Cycle090.theta-oldFee := by
    rw [hcount]
    nlinarith only [hprice,hbudget,hgain]
  have hpow := (power_le_final_iff a p (e49R D P (2*a-1) p) d Cycle090.sourceCost
    (nativeMoment D affineError) (nativeMass D a d-(2*a-1)*(originalVcut r+D.t)/4)
    (fee+d*loss) (Cycle090.theta-oldFee) hd0).mpr hpaid
  have hpow' : packetPower a p (e49R D P (2*a-1) p) d Cycle090.sourceCost
      (nativeMoment D affineError) (nativeMass D a d)-(2*a-1)*(originalVcut r+D.t)/4 ≤
        finalPower a d Cycle090.sourceCost (fee+d*loss) (Cycle090.theta-oldFee) := by
    convert hpow using 1 <;> unfold packetPower <;> ring
  let W := fun J=>actualMaskWeight D F J K Cc (C J) Jc (degree J) Z d a τ i
  have hW (J : Finset (Fin D.N)) : 0≤W J := by
    have hCJ := hC J
    have hCP : 0≤nativeCountPrefactor D F K Cc Jc Z d a τ i := zero_le_one.trans (le_max_left _ _)
    have hH : 0≤nativeHeight Z d τ i := by unfold nativeHeight;positivity
    dsimp only [W,actualMaskWeight]
    unfold mainFront
    positivity
  have hmask (J : Finset (Fin D.N)) : largeClassMaskNorm D F J rows data η Z d a x z (Z^Geometry.y) (originalVcut r) bin ≤
      W J*(Z^d)^(finalPower a d Cycle090.sourceCost (fee+d*loss) (Cycle090.theta-oldFee)) := by
    have hm := (hp J).2 idx grid hs k hk i hi j hn hd x z hx hz him data (originalVcut r) bin hne hguard
    exact hm.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (Real.one_le_rpow hZ.le hd0.le) hpow') (hW J))
  have hsum := Finset.sum_le_sum (fun J (_ : J∈Finset.univ.powerset)=>hmask J)
  rw [←Finset.sum_mul] at hsum
  have he' := he.2 d a τ hd hdhi ha' hτ.le i
  let bc : ℝ := Nat.card (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t)
  have hbc : 0 ≤ bc := by dsimp [bc];positivity
  have heq : loss+finalPower a d Cycle090.sourceCost (fee+d*loss) (Cycle090.theta-oldFee) =
      finalPower a d Cycle090.sourceCost fee (Cycle090.theta-oldFee) := by
    unfold finalPower
    field_simp
    <;> ring
  calc
    _ ≤ bc*((∑ J∈Finset.univ.powerset,W J)*
      (Z^d)^(finalPower a d Cycle090.sourceCost (fee+d*loss) (Cycle090.theta-oldFee))) :=
      mul_le_mul_of_nonneg_left hsum hbc
    _ = (bc*(∑ J∈Finset.univ.powerset,W J))*
      (Z^d)^(finalPower a d Cycle090.sourceCost (fee+d*loss) (Cycle090.theta-oldFee)) := by ring
    _ ≤ (C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*(Z^d)^loss)*
      (Z^d)^(finalPower a d Cycle090.sourceCost (fee+d*loss) (Cycle090.theta-oldFee)) :=
      mul_le_mul_of_nonneg_right he' (Real.rpow_nonneg (Real.rpow_nonneg hZ0.le _) _)
    _ = _ := by rw [mul_assoc,←Real.rpow_add (Real.rpow_pos_of_pos hZ0 _),heq]
end QRH.Cycle092.MixedTicketTails
#print axioms QRH.Cycle092.MixedTicketTails.actual_original_large_slice_absorbed

/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native packets with the finite prefactors paid from an early power reserve. -/
import Candidate.C092.transport.PacketJoinEnvelope
import Candidate.C092.transport.PacketJoinE49FinalFee
import Candidate.C092.transport.PacketJoinE49Actual
import Candidate.C092.transport.MixedOutsidePaidConductor
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


/-- The full original selected phase packet below each literal ticket's
original conductor cutoff. No bank descriptor or reduced row subfamily is used. -/
theorem actual_original_small_phase_sum_final_fee (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (affineError : ℝ) (haff : 0 < affineError) (loss : ℝ) (hloss : 0 < loss) :
    ∃ mc : ℝ→ℝ,(∀ t,0 < t → 0 < mc t) ∧ ∃ mp : ℝ,0 < mp ∧
    ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀ s,D.length s ≤ mc D.t/200) → (∀ s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
    (∀ s,D.length s ≤ mp/200) → (∀ s,D.length s ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)/200) →
    2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa →
    ∀ η : Character,∃ m : ℕ,∃ C0 : ℝ,0 < C0 ∧
    ∀ (P : TransportParameters D) (padding τ : ℝ),0 < τ →
    4*τ < (1/200:ℝ)*D.cost → padding+2*D.t ≤ 1/10000000000 → ∀ n : ℕ,
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧ ∀ idx grid : FreeRow→ℕ,
    selected D F padding τ n η Z idx grid →
    ∀ k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀ i∈Finset.range (n+1),∀ j : ℕ,
    (cellRows D F padding Z idx grid k i j).Nonempty →
    let d := sourceDyadConductor Z D.t k
    let a : ℝ := 51/100+D.e*j
    let rows := cellRows D F padding Z idx grid k i j
    (1/2:ℝ) ≤ d → ∀ (x z : ℂ),x.re=a+16*D.e → z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ →
    ∀ bins : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t),
    ∀ ticket : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t → Row,
    (∀ bin∈bins,(MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty →
      ticket bin∈TopData.rows ∧ (ticket bin).box.Contains (2*a-1,
        classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) ∧
      d ≤ originalDlow (ticket bin)) → Cycle090.hLower ≤ Geometry.h → Geometry.h ≤ Cycle090.hUpper →
    Geometry.ell=Physical.ell → ∀ eps : ℝ,0 ≤ eps → 0 ≤ P.mesh →
    159*D.ε+12*D.t+P.mesh+16*D.e+2*eps+affineError/4+loss ≤ 1/100000000000000 →
    (∑ bin∈bins,packetNorm D F (MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin)
      η Z x z (Z^Geometry.y)) ≤
      C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^d)^(finalPower a d Cycle090.sourceCost (16*D.e+2*eps*d+17*D.t/25) (Cycle090.theta-oldFee)) := by
  obtain ⟨mc,hmc,mp,hmp,hpacket⟩ := actual_e49_mask_bound hβ affineError haff
  refine ⟨mc,hmc,mp,hmp,?_⟩
  intro D F hfCount hfSource hfPacket hfCommon hkβ η
  obtain ⟨K,hK,hpacket⟩ := hpacket D F hfCount hfSource hfPacket hfCommon hkβ
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
  intro hd x z hx hz him bins ticket hbins hh hh' hell eps heps hm hreserve
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  let rows := cellRows D F padding Z idx grid k i j
  let fee := 16*D.e+2*eps*d+17*D.t/25
  have hZ := (hp ∅).1
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hd0 : 0 < d := by dsimp [d];linarith
  obtain ⟨hdhi,ha,hahi,hrow,hrest⟩ := hc.2 idx grid hs k hk i hi j hn
  change a ≤ 7/8 at hahi
  change 51/100 < a at ha
  have hb := e49_early_budget D P a d eps affineError loss hd0 (by linarith) (by linarith) hahi
    heps haff.le hloss.le hm (hreserve.trans (by norm_num))
  have hbudget : d*(3*(159*D.ε+8*D.t+P.mesh)/4+nativeMoment D affineError/4+nativeMass D a d)+
      (fee+d*loss) ≤ 7*oldFee := by
    dsimp only [fee]
    have ho : (1/250000000:ℝ) ≤ 7*oldFee := by norm_num [oldFee]
    linarith only [hb,ho]
  have he' := he.2 d a τ hd hdhi hahi hτ.le i
  let bc : ℝ := Nat.card (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t)
  have hbc : 0 ≤ bc := by dsimp [bc];positivity
  let W := fun J=>actualMaskWeight D F J K Cc (C J) Jc (degree J) Z d a τ i
  have hW (J : Finset (Fin D.N)) : 0 ≤ W J := by
    have hCJ := hC J
    have hCP : 0 ≤ nativeCountPrefactor D F K Cc Jc Z d a τ i := zero_le_one.trans (le_max_left _ _)
    have hH : 0 ≤ nativeHeight Z d τ i := by unfold nativeHeight;positivity
    dsimp only [W,actualMaskWeight]
    unfold mainFront
    positivity
  apply sum_of_card_payment bins _ _ (by positivity)
  intro bin hbin
  by_cases hne : (MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty
  · obtain ⟨hr,hbox,hdlo⟩ := hbins bin hbin hne
    have hav := original_e49_available hr hbox
    have hprice := MixedOutsidePaid.original_small_conductor_price_errors_paid hr hbox hh hh' hell hd0 hdlo hbudget
    let p := classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)
    have hprice' : rowPrice (2*a-1) p (e49R D P (2*a-1) p) d Cycle090.sourceCost+
        d*(nativeMoment D affineError/4+nativeMass D a d)+(fee+d*loss) ≤ Cycle090.theta-oldFee := by
      simpa only [p,e49R,add_assoc] using hprice
    have hpacketbin := packet_of_partition_prices D F (MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin)
      η Z x z (Z^Geometry.y) (fun _=>({()} : Finset Unit)) (fun _ _=>()) (by intros;simp)
      a d Cycle090.sourceCost (fee+d*loss) (Cycle090.theta-oldFee)
      (∑ J∈Finset.univ.powerset,W J) hZ.le hd0 (fun J _=>W J)
      (fun J _ _ _=>hW J) (by simp)
      (by
        intro J hJ b hb hneSlice
        cases b
        refine ⟨_,e49R D P (2*a-1) _,nativeMoment D affineError,nativeMass D a d,hprice',?_⟩
        have hb := (hp J).2 idx grid hs k hk i hi j hn hd x z hx hz him bin hne hav
        simpa only [Finset.filter_true,eq_self] using hb)
    have hpow : loss+finalPower a d Cycle090.sourceCost (fee+d*loss) (Cycle090.theta-oldFee) =
        finalPower a d Cycle090.sourceCost fee (Cycle090.theta-oldFee) := by
      unfold finalPower
      field_simp
      <;> ring
    calc
      _ ≤ bc*((∑ J∈Finset.univ.powerset,W J)*
          (Z^d)^(finalPower a d Cycle090.sourceCost (fee+d*loss) (Cycle090.theta-oldFee))) :=
        mul_le_mul_of_nonneg_left hpacketbin hbc
      _ = (bc*(∑ J∈Finset.univ.powerset,W J))*
          (Z^d)^(finalPower a d Cycle090.sourceCost (fee+d*loss) (Cycle090.theta-oldFee)) := by ring
      _ ≤ (C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*(Z^d)^loss)*
          (Z^d)^(finalPower a d Cycle090.sourceCost (fee+d*loss) (Cycle090.theta-oldFee)) :=
        mul_le_mul_of_nonneg_right he' (by positivity)
      _ = _ := by rw [mul_assoc,←Real.rpow_add (Real.rpow_pos_of_pos hZ0 _),hpow]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [packetNorm,Finset.sum_empty,mul_zero,Finset.sum_const_zero]
    positivity
end QRH.Cycle092.MixedTicketTails
#print axioms QRH.Cycle092.MixedTicketTails.actual_original_small_phase_sum_final_fee

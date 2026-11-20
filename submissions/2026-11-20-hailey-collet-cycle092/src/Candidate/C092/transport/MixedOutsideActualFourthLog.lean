/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Entire original error packets on actual selected native-direct cell slices. -/
import Candidate.C092.transport.MixedOutsideActualFourthPhase
import Candidate.C092.transport.PacketJoinPhaseSum
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

theorem actual_common_phase_sum_log_bound (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (affineError : ℝ) (haff : 0 < affineError) (countLoss : ℝ) (hcountLoss : 0 < countLoss) :
    ∃ mp : ℝ,0 < mp ∧ ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀ s,D.length s ≤ mp/200) →
    (∀ s,D.length s ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)/200) →
    (∀ s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
    2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa →
    ∀ (Cc : ℝ) (Jc : ℕ),∃ m : ℕ,∃ C0 : ℝ,0 < C0 ∧
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
    ∀ (bins : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t))
      (common : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t→Finset FreeRow),
    (∀ bin∈bins,common bin ⊆ MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin) →
    ∀ fee target : ℝ,
    (∀ bin∈bins,(common bin).Nonempty → ∃ R : ℝ,
      ((common bin).card:ℝ) ≤ outsideCountEnvelope Cc Jc Z d τ i*(dyadicLength (Z^d):ℝ)^2*(Z^d)^R ∧
      rowPrice (2*a-1)
        (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))
        (R+countLoss) d Cycle090.sourceCost+d*(nativeMoment D affineError/4+nativeMass D a d)+fee ≤ target) →
    (∑ bin∈bins,packetNorm D F (common bin) η Z x z (Z^Geometry.y)) ≤
      C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^d)^(finalPower a d Cycle090.sourceCost fee target) := by
  obtain ⟨mp,hmp,hpacket⟩ := actual_common_phase_sum_bound hβ affineError haff
  obtain ⟨L,hL,hlog⟩ := dyadic_cost_uniform countLoss hcountLoss
  refine ⟨mp,hmp,?_⟩
  intro D F hfPacket hfCommon hfSource hkβ Cc Jc
  let Cc' : ℝ := max 1 Cc*max 1 L
  have hCc' : 1 ≤ Cc' := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
  obtain ⟨m,C0,hC0,hpacket⟩ := hpacket D F hfPacket hfCommon hfSource hkβ Cc' Jc
  refine ⟨m,C0,hC0,?_⟩
  intro P padding τ hτ hheight hpad n η
  filter_upwards [hpacket P padding τ hτ hheight hpad n η,hlog] with Z hp hl
  refine ⟨hp.1,?_⟩
  intro idx grid hs k hk i hi j hn
  dsimp only
  intro hd x z hx hz him bins common hsub fee target hprices
  let d := sourceDyadConductor Z D.t k
  have hZ0 : 0 < Z := zero_lt_one.trans hp.1
  have hU0 : 0 < Z^d := Real.rpow_pos_of_pos hZ0 _
  apply hp.2 idx grid hs k hk i hi j hn hd x z hx hz him bins common hsub fee target
  intro bin hb hne
  obtain ⟨R,hcard,hprice⟩ := hprices bin hb hne
  refine ⟨R+countLoss,?_,hprice⟩
  have hLmax : L ≤ max 1 L := le_max_right _ _
  have hEnv : outsideCountEnvelope Cc Jc Z d τ i*L ≤ outsideCountEnvelope Cc' Jc Z d τ i := by
    unfold outsideCountEnvelope
    rw [max_eq_right hCc']
    have hH : 0 ≤ (1+nativeHeight Z d τ i)^Jc := by
      have hHH : 0 ≤ nativeHeight Z d τ i := by unfold nativeHeight;positivity
      positivity
    calc
      _ = max 1 Cc*L*(1+nativeHeight Z d τ i)^Jc := by ring
      _ ≤ max 1 Cc*max 1 L*(1+nativeHeight Z d τ i)^Jc :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLmax (zero_le_one.trans (le_max_left _ _))) hH
  have hEnv0 : 0 ≤ outsideCountEnvelope Cc Jc Z d τ i :=
    zero_le_one.trans (outside_count_envelope_one _ _ _ _ _ _ hZ0.le)
  calc
    _ ≤ outsideCountEnvelope Cc Jc Z d τ i*(dyadicLength (Z^d):ℝ)^2*(Z^d)^R := hcard
    _ ≤ outsideCountEnvelope Cc Jc Z d τ i*(L*(Z^d)^countLoss)*(Z^d)^R :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hl.2 d hd) hEnv0) (Real.rpow_nonneg hU0.le _)
    _ = (outsideCountEnvelope Cc Jc Z d τ i*L)*((Z^d)^countLoss*(Z^d)^R) := by ring
    _ ≤ outsideCountEnvelope Cc' Jc Z d τ i*((Z^d)^countLoss*(Z^d)^R) :=
      mul_le_mul_of_nonneg_right hEnv (by positivity)
    _ = _ := by rw [←Real.rpow_add hU0,add_comm countLoss R]
end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.actual_common_phase_sum_log_bound

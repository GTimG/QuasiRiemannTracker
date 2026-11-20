/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Natural packets with the finite prefactors paid from an early power reserve. -/
import Candidate.C092.transport.NaturalPacketLowWhole
import Candidate.C092.transport.PacketFinalCells
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

/-- Natural phase slices with the exact two integration fees and one reserve
chosen ahead of the live scale. All finite costs are already in C0. -/
theorem actual_natural_lower_final_power_cells (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hkβ : 2*HeckeZeroSupremum.beta-1 ≤ kap) (loss : ℝ) (hloss : 0<loss) :
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
      C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^d)^(finalPower a d Cycle090.sourceCost (16*D.e+2*eps*d+17*D.t/25)
          (HeckeZeroSupremum.beta-saving-3*allowance)) := by
  obtain ⟨mc,hmc,hpacket⟩ := actual_natural_lower_whole_final_fee hβ hkβ loss hloss
  refine ⟨mc,hmc,?_⟩
  intro D F hfCount hfSource η
  obtain ⟨m,C0,hC0,hpacket⟩ := hpacket D F hfCount hfSource η
  refine ⟨m,C0,hC0,?_⟩
  intro P padding τ hτ hheight hpad n saving allowance eps hh hh' hell heps hm hreserve htarget
  filter_upwards [hpacket P padding τ hτ hheight hpad n,actual_cell_conductor D F padding] with Z hp hc
  refine ⟨hp.1,?_⟩
  intro idx grid hsel k hk i hi j hj hn
  dsimp only
  intro hdtop q hq
  have hdlo := (hc idx grid k hk i j hn).1
  have hd0 : 0<sourceDyadConductor Z D.t k := by change (1/100:ℝ) ≤ sourceDyadConductor Z D.t k at hdlo;linarith
  have hraw := hp.2 idx grid hsel k hk i hi j hn hdtop
    (((((51/100+D.e*j)+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)
    (by simp) (by simp) (by simpa using hq.2) hh hh' hell eps heps hm hreserve
  have hZ0 : 0<Z := zero_lt_one.trans hp.1
  apply hraw.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (Real.one_le_rpow hp.1.le hd0.le)
  unfold finalPower
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ hd0.le
  linarith only [htarget]

end QRH.Cycle092.NaturalPacketLow
#print axioms QRH.Cycle092.NaturalPacketLow.actual_natural_lower_final_power_cells

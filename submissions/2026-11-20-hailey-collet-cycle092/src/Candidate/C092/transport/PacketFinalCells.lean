/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Use one final exponent after every row subclass is priced.
The fixed height degree is chosen before the one physical height exponent. -/
import Candidate.C092.transport.PacketFinalPower

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Classical BigOperators
open Filter
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open Cycle25.Numerator Cycle25.Weighted.FullWContour
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.ProbeAssembly
namespace QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

def FinalPowerCells (D : BaselineData) (F : BaselineSourceData D)
    (padding tau saving allowance eps degree source : ℝ) (n : ℕ) (η : Character) : Prop :=
  ∃ C0 : ℝ, 0 < C0 ∧ ∀ᶠ Z : ℝ in atTop, ∀ idx grid : FreeRow → ℕ,
    selected D F padding tau n η Z idx grid →
    ∀ k ∈ smallDyadicIndices (Z^(Geometry.h+padding)), ∀ i ∈ Finset.range (n+1),
    ∀ j ∈ Finset.range (⌊(49/100:ℝ)/D.e⌋₊+1),
    (cellRows D F padding Z idx grid k i j).Nonempty →
    let d := sourceDyadConductor Z D.t k
    let a : ℝ := 51/100+D.e*j
      ∀ q ∈ szRectangle ((3*i+1:ℕ)*Z^tau),
        packetNorm D F (cellRows D F padding Z idx grid k i j) η Z
          ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I) (Z^Geometry.y) ≤
          C0*(3+((3*i+1:ℕ):ℝ)*Z^tau)^degree*(Z^Geometry.y)^(-(1/2:ℝ))*
            Z^(-4*Geometry.ell/25)*(Z^d)^(finalPower a d source (16*D.e+2*eps*d+17*D.t/25) (HeckeZeroSupremum.beta-saving-3*allowance))


/-- The earlier integral theorem only reads the scalar exponent. Here the tuple
(0,0,0,E−1/4) is an algebraic parameterization of that scalar; all actual
row counts and moments have already been charged inside each partition. -/
theorem pointwise_of_final (D : BaselineData) (F : BaselineSourceData D)
    (padding tau saving allowance eps degree source : ℝ) (n : ℕ) (η : Character)
    (hpadding : 0 < padding) (hpad : padding+2*D.t ≤ 1/10000000000)
    (hfinal : FinalPowerCells D F padding tau saving allowance eps degree source n η) :
    PointwisePacketCells D F padding tau saving allowance eps degree source n η := by
  obtain ⟨C,hC,hcell⟩ := hfinal
  refine ⟨C,hC,?_⟩
  filter_upwards [hcell, actual_cell_geometry D F padding hpadding hpad] with Z hc hg
  intro idx grid hsel k hk i hi j hj hn
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  let fee := 16*D.e+2*eps*d+17*D.t/25
  let target := HeckeZeroSupremum.beta-saving-3*allowance
  let E := finalPower a d source fee target
  have hd : 0 < d := (hg tau n η idx grid hsel k hk i j hn).1
  have hid : packetPower a 0 0 d source 0 (E-1/4) = E := by unfold packetPower; ring
  refine ⟨0,0,0,E-1/4,?_,?_⟩
  · have hp := (power_le_final_iff a 0 0 d source 0 (E-1/4) fee target hd).mp (le_of_eq hid)
    change rowPrice (2*a-1) 0 0 d source+16*D.e+2*eps*d+d*(0/4+(E-1/4))+17*D.t/25 ≤ target
    dsimp only [fee] at hp
    linarith only [hp]
  · intro q hq
    have hid' : packetPower (51/100+D.e*j) 0 0 (sourceDyadConductor Z D.t k) source 0 (E-1/4) = E := hid
    rw [hid']
    exact hc idx grid hsel k hk i hi j hj hn q hq

#print axioms pointwise_of_final
end QRH.Cycle092.SelectedNonfloor

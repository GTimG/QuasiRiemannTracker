/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Pointwise original packet/source/count cells to the entire finite numerator.
The fixed height degree is chosen before the one physical height exponent. -/
import Candidate.C092.transport.SelectedNonfloorGeometry

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

/-- The residual genuine source/count input is POINTWISE on every actual cell,
with its complete physical error packet. There is no normalizer, integral,
probe, or energy premise. Packet summation follows from the P15 coefficient
mass and original polynomial fourths/counts/amplitudes in `Packet`.
The common finite height degree is fixed before tau and every later n. -/
def PointwisePacketCells (D : BaselineData) (F : BaselineSourceData D)
    (padding tau saving allowance eps degree source : ℝ) (n : ℕ) (η : Character) : Prop :=
  ∃ C0 : ℝ, 0 < C0 ∧ ∀ᶠ Z : ℝ in atTop, ∀ idx grid : FreeRow → ℕ,
    selected D F padding tau n η Z idx grid →
    ∀ k ∈ smallDyadicIndices (Z^(Geometry.h+padding)), ∀ i ∈ Finset.range (n+1),
    ∀ j ∈ Finset.range (⌊(49/100:ℝ)/D.e⌋₊+1),
    (cellRows D F padding Z idx grid k i j).Nonempty →
    let d := sourceDyadConductor Z D.t k
    let a : ℝ := 51/100+D.e*j
    ∃ p R momentLoss massLoss : ℝ,
      rowPrice (2*a-1) p R d source+16*D.e+2*eps*d+
        d*(momentLoss/4+massLoss)+17*D.t/25 ≤ HeckeZeroSupremum.beta-saving-3*allowance ∧
      ∀ q ∈ szRectangle ((3*i+1:ℕ)*Z^tau),
        packetNorm D F (cellRows D F padding Z idx grid k i j) η Z
          ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I) (Z^Geometry.y) ≤
          C0*(3+((3*i+1:ℕ):ℝ)*Z^tau)^degree*(Z^Geometry.y)^(-(1/2:ℝ))*
            Z^(-4*Geometry.ell/25)*(Z^d)^(packetPower a p R d source momentLoss massLoss)

/-- Entire independent contour integrations, literal normalizer and common
height loss from the genuine pointwise packet cells. -/
theorem cell_bound_of_pointwise_packets (D : BaselineData) (F : BaselineSourceData D)
    (padding tau saving allowance eps degree source : ℝ)
    (hpadding : 0 < padding) (hpad : padding+2*D.t ≤ 1/10000000000)
    (htau : 0 < tau) (hallowance : 0 < allowance) (heps : 0 < eps) (hdegree : 0 ≤ degree)
    (hheight : 2*tau*(1+degree+2*eps) ≤ allowance) (n : ℕ) (η : Character)
    (hinput : PointwisePacketCells D F padding tau saving allowance eps degree source n η) :
    CellBound D F padding tau saving allowance n η := by
  obtain ⟨C0, hC0, hb⟩ := hinput
  obtain ⟨C, hC, hf⟩ := finite_fullW_of_original_packet_price D F eps heps
  obtain ⟨Cn, hCn, hn⟩ := SelectedActual.actual_normalizer_inverse D F allowance hallowance
  have hm := HeckeLogarithmicInput.modulus_norm_ge_one η
  refine ⟨C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Cn, by positivity, ?_⟩
  filter_upwards [hb, hf η, hn, actual_cell_geometry D F padding hpadding hpad,
    SelectedFloorEstimate.source_height_absorption (degree+2*eps) allowance tau n
      (by linarith) hallowance htau (by linarith only [hheight]),
    (tendsto_rpow_atTop htau).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hb hf hn hg hh hT hZ
  intro idx grid hs k hk i hi j hj hne
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  let rows := cellRows D F padding Z idx grid k i j
  have geom := hg tau n η idx grid hs k hk i j hne
  obtain ⟨p, R, momentLoss, massLoss, hprice, hpkt⟩ := hb idx grid hs k hk i hi j hj hne
  let H : ℝ := (3*i+1:ℕ)*Z^tau
  have hZp := zero_lt_one.trans hZ
  have hH : 0 < 3+H := by dsimp [H]; positivity
  have hCf : 0 ≤ C0*(3+H)^degree := by positivity
  have hbraw := hf rows tau d a p R source momentLoss massLoss (C0*(3+H)^degree) i
    hT geom.2.1 geom.2.2.1 geom.1.ne' hCf geom.2.2.2.1 geom.2.2.2.2 hpkt
  have hrowsvalue : ‖cellValue D F padding tau η Z idx grid k i j‖ ≤
      C*(C0*(3+H)^degree)*(η.modulus.absNorm:ℝ)^(2*eps)*(3+H)^(2*eps)*
        Z^(Geometry.signalShift+rowPrice (2*a-1) p R d source+
          16*D.e+2*eps*d+d*(momentLoss/4+massLoss)+17*D.t/25) := by
    exact hbraw
  have hheightZ : (3+H)^(degree+2*eps) ≤ Z^allowance :=
    hh i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hshift : Geometry.signalShift = ProbeAssembly.shift := by
    dsimp [Geometry.signalShift, ProbeAssembly.shift,
      Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.signalShift,
      Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Assembly.signalShift]
    change -(4+Geometry.y-Geometry.x)/6 = -(5/6-Geometry.x/3-Geometry.ell/6)
    linarith [Geometry.x_add_y]
  have hexp : Geometry.signalShift+rowPrice (2*a-1) p R d source+
      16*D.e+2*eps*d+d*(momentLoss/4+massLoss)+17*D.t/25 ≤
      HeckeZeroSupremum.beta+ProbeAssembly.shift-saving-3*allowance := by
    rw [hshift]
    linarith only [hprice]
  have hraw : ‖cellValue D F padding tau η Z idx grid k i j‖ ≤
      (C*C0*(η.modulus.absNorm:ℝ)^(2*eps))*Z^allowance*
        Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving-3*allowance) := by
    apply hrowsvalue.trans
    calc
      _ = (C*C0*(η.modulus.absNorm:ℝ)^(2*eps))*((3+H)^(degree+2*eps))*
          Z^(Geometry.signalShift+rowPrice (2*a-1) p R d source+
            16*D.e+2*eps*d+d*(momentLoss/4+massLoss)+17*D.t/25) := by
        rw [Real.rpow_add hH]; ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hheightZ (by positivity))
        (Real.rpow_le_rpow_of_exponent_le hZ.le hexp) (by positivity) (by positivity)
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ ((C*C0*(η.modulus.absNorm:ℝ)^(2*eps))*Z^allowance*
        Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving-3*allowance))*(Cn*Z^allowance) :=
      mul_le_mul hraw hn.2 (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [show HeckeZeroSupremum.beta+ProbeAssembly.shift-saving-allowance =
        allowance+(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving-3*allowance)+allowance by ring]
      simp_rw [Real.rpow_add hZp]
      ring

/-- Literal finite nonfloor numerator from the finer genuine pointwise packet
source/count cells. The same tau works for every label/grid at this n. -/
theorem finite_numerator_of_pointwise_packets (D : BaselineData) (F : BaselineSourceData D)
    (padding tau saving allowance eps degree source : ℝ)
    (hpadding : 0 < padding) (hpad : padding+2*D.t ≤ 1/10000000000)
    (htau : 0 < tau) (hsaving : saving ≤ 1) (hallowance : 0 < allowance)
    (heps : 0 < eps) (hdegree : 0 ≤ degree)
    (hheight : 2*tau*(1+degree+2*eps) ≤ allowance)
    (hupper : Geometry.h+padding ≤ 1)
    (hpadSmall : padding ≤ QRH.Cycle092.SelectedActualKernel.TransportKernel.Transport.Transport.rowExtension)
    (hbeta : Geometry.theta ≤ HeckeZeroSupremum.beta) (n : ℕ) (η : Character)
    (hinput : PointwisePacketCells D F padding tau saving allowance eps degree source n η) :
    FiniteNumeratorBound D F padding tau saving n η :=
  finite_numerator_of_cells D F padding tau saving allowance htau hsaving hallowance hupper
    hpadSmall hbeta n η
    (cell_bound_of_pointwise_packets D F padding tau saving allowance eps degree source
      hpadding hpad htau hallowance heps hdegree hheight n η hinput)

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.cell_bound_of_pointwise_packets
#print axioms QRH.Cycle092.SelectedNonfloor.finite_numerator_of_pointwise_packets

/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Pointwise full-packet bounds to literal finite physical integrals, with the
exact physical price and all displayed exponent losses. -/
import Candidate.C092.transport.SelectedNonfloorPrice

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open HeckeDetectorPhysicalSelection
open OAI.SevenEighths.BoundaryDensitySplitReturn.TransportHighTransport
open Cycle25.Weighted.Numerator Cycle25.Numerator Cycle25.Weighted.FullWContour
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
namespace QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters]

/-- Genuine packet power in the source's own conductor units. All masks and
all original coefficient tuples must satisfy the packet bound at this power. -/
def packetPower (a p R D source momentLoss massLoss : ℝ) : ℝ :=
  (2*a-1)*p*(Geometry.ell/D-Physical.Selection.zeroCapacity Geometry.y source D/2)+
    (3*R+1+momentLoss)/4+massLoss

/-- Every original main/error packet is integrated against the true reciprocal
scalar. The output exponent is the literal physical price, with every listed
loss still visible. Finer source/count/amplitude conditions enter only through
the actual pointwise packet estimate; no physical integral is postulated. -/
theorem finite_fullW_of_original_packet_price
    (D : BaselineData) (F : BaselineSourceData D) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ (rows : Finset FreeRow) (tau d a p R source momentLoss massLoss C0 : ℝ) (i : ℕ),
      2 < Z^tau → 51/100 ≤ a → a ≤ 7/8 → d ≠ 0 → 0 ≤ C0 →
      (∀ u ∈ rows, u.val ≠ 1 ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
        Z^(d-2*D.t) ≤ rowNorm u ∧ rowNorm u ≤ Z^d) →
      (∀ u ∈ rows, detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^tau) < a+2*D.e) →
      (∀ q ∈ szRectangle ((3*i+1:ℕ)*Z^tau), packetNorm D F rows η Z
        ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I) (Z^Geometry.y) ≤
        C0*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-4*Geometry.ell/25)*
          (Z^d)^(packetPower a p R d source momentLoss massLoss)) →
      ‖finiteCentralFullWRows F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
        (fun j => source_prime_pool_outside F Z j) (fun _ => F.W)
        (fun j => Z^(D.length j)) F.W F.W (Z^Geometry.x) (Z^Geometry.y) Z D.e
        (fun _ => a) (fun _ => (3*i+1:ℕ)*Z^tau)‖ ≤
      C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+((3*i+1:ℕ):ℝ)*Z^tau)^(2*eps)*
        Z^(Geometry.signalShift+rowPrice (2*a-1) p R d source+
          16*D.e+2*eps*d+d*(momentLoss/4+massLoss)+17*D.t/25) := by
  obtain ⟨C, hC, hf⟩ := finite_fullW_of_packet_norm D F eps heps
  refine ⟨C, hC, ?_⟩
  intro η
  filter_upwards [hf η, eventually_gt_atTop (1:ℝ)] with Z hf hZ
  intro rows tau d a p R source momentLoss massLoss C0 i hT ha hatop hd hC0 hr hb hpacket
  have hZp := zero_lt_one.trans hZ
  let E := packetPower a p R d source momentLoss massLoss
  let M := C0*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-4*Geometry.ell/25)*(Z^d)^E
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hh := hf rows tau d a M i hT ha hatop hM hr hb hpacket
  have hcollapse :
      (Z^Geometry.x)^(4/25:ℝ)*Z^(a+16*D.e-33/50)*
        ((Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*D.t))*
        ((Z^Geometry.y)^(-(1/2:ℝ))*Z^(-4*Geometry.ell/25)*(Z^d)^E) =
      Z^(rawExponent a p R d source D.e D.t eps momentLoss massLoss) := by
    simp_rw [←Real.rpow_mul hZp.le]
    have he : rawExponent a p R d source D.e D.t eps momentLoss massLoss =
        Geometry.x*(4/25)+(a+16*D.e-33/50)+
        (d*(2*eps)+d*(-(17/50))+(17/25)*D.t)+
        (Geometry.y*(-(1/2))+(-4*Geometry.ell/25)+d*E) := by
      dsimp [rawExponent, E, packetPower]
      ring
    rw [he]
    simp_rw [Real.rpow_add hZp]
  calc
    _ ≤ _ := hh
    _ = C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+((3*i+1:ℕ):ℝ)*Z^tau)^(2*eps)*
        Z^(rawExponent a p R d source D.e D.t eps momentLoss massLoss) := by
      dsimp only [M]
      rw [←hcollapse]
      ring
    _ = _ := by rw [raw_exponent_eq_price _ _ _ _ _ _ _ _ _ _ hd]

/-- An actual common-row count deficit pays its exact 3/4 exponent once. -/
theorem row_price_count_deficit (delta p R G d source : ℝ) :
    rowPrice delta p (R-G) d source = rowPrice delta p R d source-3*d*G/4 := by
  unfold rowPrice
  ring

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.finite_fullW_of_original_packet_price
#print axioms QRH.Cycle092.SelectedNonfloor.row_price_count_deficit

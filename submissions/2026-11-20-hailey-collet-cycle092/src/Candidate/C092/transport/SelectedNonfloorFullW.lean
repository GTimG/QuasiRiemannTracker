/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Complete original physical packet to the finite retained contour integral.
The source scalar, FullW kernel and exact reconstruction retain their original
OpenAI/Collet/Levy/Gao/Bebel credits through the imports. -/
import Candidate.C092.transport.SelectedNonfloorScalar

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

/-- Every error mask and its complementary main primes, including the exact
physical `Yp^(-4/25)` fronts, remain inside this positive packet sum. -/
def packetNorm (D : BaselineData) (F : BaselineSourceData D) (rows : Finset FreeRow)
    (η : Character) (Z : ℝ) (x z : ℂ) (Y : ℝ) : ℝ :=
  ∑ J ∈ Finset.univ.powerset, mainFront D J Z*
    (∑ u ∈ rows, ‖errorPacket D F J η u Z x z Y * mainProduct D F J u Z z‖)

/-- The authentic FullW norm theorem performs both remaining integrations.
The packet input is pointwise on the original independent outer rectangle. -/
theorem finite_fullW_of_pointwise (D : BaselineData) (F : BaselineSourceData D) :
    ∃ Cw : ℝ, 0 < Cw ∧ ∀ (η : Character) (rows : Finset FreeRow)
      (Z a B H A : ℝ) (i : ℕ),
      0 < Z → 51/100 ≤ a → a ≤ 7/8 → 2 < B → H ≤ (3*i+2:ℕ)*B → 0 ≤ A →
      (∀ u ∈ rows, u.val ≠ 1) →
      (∀ u ∈ rows, detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*B) < a+2*D.e) →
      (∀ q ∈ szRectangle H,
        ‖integratedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
          (fun j => source_prime_pool_outside F Z j) (fun _ => F.W)
          (fun j => Z^(D.length j)) F.W (Z^Geometry.y)
          ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖ ≤ A) →
      ‖finiteCentralFullWRows F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
        (fun j => source_prime_pool_outside F Z j) (fun _ => F.W)
        (fun j => Z^(D.length j)) F.W F.W (Z^Geometry.x) (Z^Geometry.y) Z D.e
        (fun _ => a) (fun _ => H)‖ ≤
        Cw*(Z^Geometry.x)^(4/25:ℝ)*Z^(a+16*D.e-33/50)*A := by
  obtain ⟨Cw, hCw, hw⟩ := finiteFullW_uniform_norm_bound F.W 1 2 (by norm_num) F.complex_support
  refine ⟨Cw, hCw, ?_⟩
  intro η rows Z a B H A i hZ ha hatop hB hHi hA hone hnext hraw
  have hh := hw D.e a B H i D.e_pos D.e_small ha (by linarith [D.e_small]) hB hHi
    F.S F.exclusions F.maximal F.first η rows hone (sourcePrimePool F Z)
    (fun j => source_prime_pool_outside F Z j) (rayCubeFamily F.modulus ⊤ le_top) hnext
    (fun _ => F.W) (fun j => Z^(D.length j)) F.W 1 2 (by norm_num) F.complex_support
    (Z^Geometry.x) (Z^Geometry.y) Z A (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) hZ hA hraw
  convert hh using 1 <;> ring_nf

/-- Full original packet estimate, including its physical reciprocal, now
bounds the actual finite FullW row sum. No integral or probe estimate is an
input; the only analytic input left is the finer genuine packet row bound. -/
theorem finite_fullW_of_packet_norm (D : BaselineData) (F : BaselineSourceData D)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ (rows : Finset FreeRow) (tau d a M : ℝ) (i : ℕ),
      2 < Z^tau → 51/100 ≤ a → a ≤ 7/8 → 0 ≤ M →
      (∀ u ∈ rows, u.val ≠ 1 ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
        Z^(d-2*D.t) ≤ rowNorm u ∧ rowNorm u ≤ Z^d) →
      (∀ u ∈ rows, detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^tau) < a+2*D.e) →
      (∀ q ∈ szRectangle ((3*i+1:ℕ)*Z^tau), packetNorm D F rows η Z
        ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I) (Z^Geometry.y) ≤ M) →
      ‖finiteCentralFullWRows F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
        (fun j => source_prime_pool_outside F Z j) (fun _ => F.W)
        (fun j => Z^(D.length j)) F.W F.W (Z^Geometry.x) (Z^Geometry.y) Z D.e
        (fun _ => a) (fun _ => (3*i+1:ℕ)*Z^tau)‖ ≤
      C*(Z^Geometry.x)^(4/25:ℝ)*Z^(a+16*D.e-33/50)*
        ((η.modulus.absNorm:ℝ)^(2*eps)*(3+((3*i+1:ℕ):ℝ)*Z^tau)^(2*eps)*
          (Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*D.t))*M := by
  obtain ⟨Cw, hCw, hw⟩ := finite_fullW_of_pointwise D F
  obtain ⟨Cs, hCs, hs⟩ := actual_scalar_packet_bound D F eps heps
  refine ⟨Cw*((2*Real.pi)*Cs), by positivity, ?_⟩
  intro η
  filter_upwards [hs η, eventually_gt_atTop (1:ℝ)] with Z hs hZ
  intro rows tau d a M i hT ha hatop hM hr hb hpacket
  have hZp := zero_lt_one.trans hZ
  let A := (2*Real.pi)*(Cs*(η.modulus.absNorm:ℝ)^(2*eps)*
    (3+((3*i+1:ℕ):ℝ)*Z^tau)^(2*eps)*(Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*D.t))*M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hh := hw η rows Z a (Z^tau) ((3*i+1:ℕ)*Z^tau) A i hZp ha hatop hT
    (by push_cast; have hp := Real.rpow_nonneg hZp.le tau; nlinarith) hA
    (fun u hu => (hr u hu).1) hb ?_
  · exact hh.trans_eq (by dsimp only [A]; ring)
  · intro q hq
    have hp := hs rows tau d a i hT ha hatop hr hb q hq
      (fun J => ∑ u ∈ rows, ‖errorPacket D F J η u Z
        ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I) (Z^Geometry.y)*
        mainProduct D F J u Z ((17/50:ℂ)+q.2*Complex.I)‖)
      (fun _ => le_rfl)
    exact hp.trans (mul_le_mul_of_nonneg_left (hpacket q hq) (by positivity))

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.finite_fullW_of_pointwise
#print axioms QRH.Cycle092.SelectedNonfloor.finite_fullW_of_packet_norm

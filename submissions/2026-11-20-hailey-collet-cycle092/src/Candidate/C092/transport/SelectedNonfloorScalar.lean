/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original physical reciprocal scalar is applied after full w-inversion and
before packet subdivision. Original source credits remain in the imports. -/
import Candidate.C092.transport.SelectedNonfloorMass

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

/-- True denominator reciprocal, full masks and complementary prime factors on
the original two independent outer contour heights. The independent w variable
has been inverted by exact reconstruction; no detector denominator is used. -/
theorem actual_scalar_packet_bound (D : BaselineData) (F : BaselineSourceData D)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ (rows : Finset FreeRow) (tau d a : ℝ) (i : ℕ),
      2 < Z^tau → 51/100 ≤ a → a ≤ 7/8 →
      (∀ u ∈ rows, u.val ≠ 1 ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
        Z^(d-2*D.t) ≤ rowNorm u ∧ rowNorm u ≤ Z^d) →
      (∀ u ∈ rows, detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^tau) < a+2*D.e) →
      ∀ q ∈ szRectangle ((3*i+1:ℕ)*Z^tau), ∀ B : Finset (Fin D.N) → ℝ,
      (∀ J, (∑ u ∈ rows, ‖errorPacket D F J η u Z
        ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I) (Z^Geometry.y) *
        mainProduct D F J u Z ((17/50:ℂ)+q.2*Complex.I)‖) ≤ B J) →
      ‖integratedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
        (fun j => source_prime_pool_outside F Z j) (fun _ => F.W)
        (fun j => Z^(D.length j)) F.W (Z^Geometry.y)
        ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖ ≤
      (2*Real.pi)*
        (Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+((3*i+1:ℕ):ℝ)*Z^tau)^(2*eps)*
          (Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*D.t))*
        (∑ J ∈ Finset.univ.powerset, mainFront D J Z*B J) := by
  obtain ⟨Cs, hCs, hscalar⟩ := DirectEnergy.Source.source_scalar_on_rows D F eps heps
  refine ⟨Cs, hCs, ?_⟩
  intro η
  filter_upwards [source_prime_reconstruction_geometry F η, eventually_gt_atTop (1:ℝ)] with Z hg hZ
  intro rows tau d a i hT ha hatop hr hb q hq B hpacket
  have hZp := zero_lt_one.trans hZ
  have he := D.e_pos
  have hrow (u : FreeRow) (hu : u ∈ rows) :
      (rowCharacter F.S F.exclusions.prime u).residue ≠ 1 :=
    calibrated_row_nonprincipal F.S F.exclusions.prime F.maximal F.exclusions.bad u
      (hr u hu).1 (hr u hu).2.1
  apply integrated_bound D F rows η Z hZp
    ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I) (Z^Geometry.y)
    _ B (Real.rpow_pos_of_pos hZp _) hrow hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2
    (by simp; linarith) (by norm_num) (by simp; linarith) (by positivity)
    (hscalar η rows Z tau d a i hZp hT ha hatop
      (fun u hu => (hr u hu).2.2.1) (fun u hu => (hr u hu).2.2.2) hb q hq) hpacket

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.actual_scalar_packet_bound

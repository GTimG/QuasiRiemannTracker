/- Variable-cost adaptation by Joseph Bebel (2026). All preceding attribution retained. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Chosen-source transport with the proved averaged floor replacing the legacy
pointwise floor. Original transport estimates are reused without alteration. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveFloorSelection
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.Transport.FinalFixedHigh
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.Transport.Transport.NormalizedTransportSaving
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators Topology ContDiff
open Filter Asymptotics
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
open Qrh.TwoSlot.AnchorZeroLoss
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
open OAI OAI.SevenEighths ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open HeckeDetectorPhysicalSelection Cycle25.Numerator Cycle25.Weighted.FullWContour
open BoundaryDensitySplitReturn.TransportHighTransport
variable [Geometry.Parameters] [BoundsCore]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]
variable [S : Schedule (line := line)]

def chosenCube (A : BufferedData (line := line)) (η : Character) (Z tau : ℝ)
    (rows : Finset FreeRow) (alpha : FreeRow → ℝ) (idx : FreeRow → ℕ) : ℂ :=
  finiteCentralCubeRows A.F.S A.F.exclusions A.F.maximal η rows
    (sourcePrimePool A.F Z) (fun j => source_prime_pool_outside A.F Z j)
    (fun _ => A.F.W) (fun j => Z^(A.D.length j)) A.F.W A.F.W
    (Z^x) (Z^y) Z A.D.e alpha (fun u => (3*idx u+1:ℕ)*Z^tau)

/-- The averaged-floor supplier removes the actual floor from the full
normalized transport, with all masks and both original row subsets retained. -/
theorem chosen_floor_removal (hgap : theta<HeckeZeroSupremum.beta) (A : BufferedData (line := line)) :
    ∃ J : ℝ, 0≤J ∧ ∀ tau : ℝ, HeightAdmissible A.D A.P J tau →
    ∀ n : ℕ, ∃ C : ℝ, 0<C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
    ∀ idx grid : FreeRow → ℕ,
    ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
      η rowPadding A.D.e tau n Z idx grid →
    ∀ V signal : ℂ, ∀ B E : ℝ,
    Geometry.signal theta-1/4000≤E →
    ‖V-signal-chosenCube A η Z tau
      (rowBand (Z^(1/100:ℝ)) (Z^(h+rowPadding)))
      (fun u=>51/100+A.D.e*grid u) idx/floorNormalizer A Z‖≤B*Z^E →
    ‖V-signal-finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal
      A.D.length 1 2 rowPadding A.D.e tau (fun _=>A.F.w) A.F.W A.F.W η Z idx grid/
      floorNormalizer A Z‖ ≤
      (B+C*(η.modulus.absNorm:ℝ)^(2+2*A.P.eps))*Z^E := by
  obtain ⟨J,hJ,hf⟩ := actual_selected_floor hgap A
  refine ⟨J,hJ,?_⟩
  intro tau ht n
  obtain ⟨C,hC,hf⟩ := hf tau ht n
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hf η,eventually_ge_atTop (1:ℝ)] with Z hf hZ
  intro idx grid hs V signal B E hE herr
  have hN := (hf idx grid hs).1
  have hfloor := (hf idx grid hs).2
  have hsplit := finiteCentralCubeRows_supported_split A.F.S A.F.exclusions A.F.maximal η
    (rowBand (Z^(1/100:ℝ)) (Z^(h+rowPadding)))
    (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
    (fun _=>A.F.W) (fun j=>Z^(A.D.length j)) A.F.W A.F.W
    (Z^x) (Z^y) Z A.D.e grid (fun u=>(3*idx u+1:ℕ)*Z^tau)
  change ‖V-signal-chosenCube A η Z tau _ _ idx/floorNormalizer A Z‖≤_ at herr
  unfold chosenCube at herr
  rw [hsplit] at herr
  have hW : (fun (_ : Fin A.D.N) y => (A.F.w y:ℂ)) = (fun _=>⇑A.F.W) := by
    funext j y
    exact (A.F.complex_eq y).symm
  unfold finiteNonfloorNumerator
  rw [hW]
  have hV : V*floorNormalizer A Z/floorNormalizer A Z=V :=
    mul_div_cancel_right₀ V hN
  have hh := normalized_nonfloor_error (V*floorNormalizer A Z) signal _ _
    (floorNormalizer A Z) _ _ (by simpa only [hV,chosenFloorRows] using herr) hfloor
  rw [hV] at hh
  apply hh.trans
  calc
    _ ≤ B*Z^E+(C*(η.modulus.absNorm:ℝ)^(2+2*A.P.eps))*Z^E := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ hE)
        (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
    _ = _ := by ring

end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.chosen_floor_removal

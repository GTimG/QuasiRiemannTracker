/- Variable-cost adaptation by Joseph Bebel (2026). All preceding attribution retained. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The averaged floor supplier on the rows selected by the actual transport. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveFloorError
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.Transport.Transport.HighApproximation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralSupportedSplit
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators Topology ContDiff
open Filter
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

def chosenFloorRows (A : BufferedData (line := line)) (Z : ℝ) (grid : FreeRow → ℕ) : Finset FreeRow :=
  supportedFloorRows A.F.S A.F.maximal
    (rowBand (Z^(1/100:ℝ)) (Z^(h+rowPadding))) grid

/-- Actual buffered selection supplies every row/nonprincipality/height event
needed by the new complete cube floor bound. -/
theorem actual_selected_floor (hgap : theta < HeckeZeroSupremum.beta) (A : BufferedData (line := line)) :
    ∃ J : ℝ, 0≤J ∧ ∀ tau : ℝ, HeightAdmissible A.D A.P J tau →
    ∀ n : ℕ, ∃ C : ℝ, 0<C ∧ ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
    ∀ idx grid : FreeRow → ℕ,
    ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
      η rowPadding A.D.e tau n Z idx grid →
    floorNormalizer A Z≠0 ∧
    ‖finiteCentralCubeRows A.F.S A.F.exclusions A.F.maximal η (chosenFloorRows A Z grid)
      (sourcePrimePool A.F Z) (fun j => source_prime_pool_outside A.F Z j)
      (fun _ => A.F.W) (fun j => Z^(A.D.length j)) A.F.W A.F.W
      (Z^x) (Z^y) Z A.D.e (fun _ => 51/100) (fun u => (3*idx u+1:ℕ)*Z^tau)/
      floorNormalizer A Z‖ ≤ C*(η.modulus.absNorm:ℝ)^(2+2*A.P.eps)*
        Z^(Geometry.signal theta-1/4000) := by
  obtain ⟨J,hJ,hf⟩ := actual_averaged_floor_cube_rows hgap A
  refine ⟨J,hJ,?_⟩
  intro tau ht n
  obtain ⟨C,hC,hf⟩ := hf tau ht n
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hf η,eventually_ge_atTop (1:ℝ)] with Z hf hZ
  intro idx grid hs
  let rows := chosenFloorRows A Z grid
  have hm (u : FreeRow) (hu : u∈rows) :
      u∈rowBand (Z^(1/100:ℝ)) (Z^(h+rowPadding)) ∧
      (calibrationForSet A.F.S A.F.maximal).residueMonoid u.val≠0 ∧ grid u=0 :=
    (mem_supportedFloorRows A.F.S A.F.maximal _ grid u).mp hu
  apply hf rows idx
  · intro u hu
    have hr := mem_rowBand.mp (hm u hu).1
    exact ⟨hr.1,hr.2.1,(hm u hu).2.1,hr.2.2.le⟩
  · intro u hu
    exact calibrated_row_nonprincipal A.F.S A.F.exclusions.prime A.F.maximal A.F.exclusions.bad
      u (mem_rowBand.mp (hm u hu).1).1 (hm u hu).2.1
  · intro u hu
    exact (hs.1 u).2.1
  · intro u hu
    have hb := (hs.2.1 u).2.2.2.2.1
    simpa only [(hm u hu).2.2,Nat.cast_zero,mul_zero,add_zero] using hb

end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.actual_selected_floor

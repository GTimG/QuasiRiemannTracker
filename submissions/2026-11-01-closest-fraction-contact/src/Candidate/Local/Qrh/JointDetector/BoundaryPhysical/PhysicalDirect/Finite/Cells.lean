/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed positive row fee and conductor extension 1/10^22.
The support padding is half the extension; the later budget is reduced accordingly.
Inherited notices and source attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed HIGH row fee 1/10^12, source reserve half that fee.
Contour extension 1/10^10 and support padding 5/10^11 are unchanged.
Inherited notices and preceding adapter attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-22.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module PhysicalDirect.Finite.Cells (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.Finite.Partition
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.Chosen
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Transport.FinalFixedHigh
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Schedule
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.GenericScalar

set_option autoImplicit false
namespace Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.FiniteNumerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
noncomputable section
set_option maxHeartbeats 200000
variable [QRH.Record1252270103Return.Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN]
variable [scheme : QRH.Record1252270103Return.CountScheme] [Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.PhysicalSchedule]
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic QRH.Record1252270103Return.GenericPhysical OAI OAI.SevenEighths
open scoped Classical BigOperators
open QRH.Record1252270103Return.GenericPhysical (baselineSource)
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly OAI.SevenEighths.BoundaryDensitySplitReturn.TransportHighTransport
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

instance fixedProduct (D : BaselineData) (F : BaselineSourceData D) : NeZero (∏P∈F.S,P) :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

def primePool (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) (j : Fin D.N) :=
  pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Z^(D.length j))

theorem poolOutside (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) :
    ∀j P,P∈primePool D F Z j→P.val∉F.S :=
  fun j P hP=>(mem_pool _ F.S 1 2 (Z^(D.length j)) P).mp hP |>.2.2.2

def normalizer (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) : ℂ :=
  actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=>F.w) F.W F.W Z

def fullW (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z : ℝ) (R : Finset FreeRow) (a H : FreeRow→ℝ) : ℂ :=
  Cycle25.Weighted.FullWContour.finiteCentralFullWRows F.S F.exclusions F.maximal η R
    (primePool D F Z) (poolOutside D F Z) (fun _ y=>(F.w y:ℂ)) (fun j=>Z^(D.length j))
    F.W F.W (Z^Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.x) (Z^Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.y) Z D.e a H

def selectedRows (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) (grid : FreeRow→ℕ) :=
  supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^(Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.h+rowPadding))) grid

def cellRows (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ)
    (idx grid : FreeRow→ℕ) (k i j : ℕ) :=
  cubeBinRows (selectedRows D F Z grid∩dyadicRows 1 k) idx grid i j

def cellTarget : ℝ :=
  HeckeZeroSupremum.beta+Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.signalShift-Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Scalar.sourceReserve-
    (HeckeZeroSupremum.beta-Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.theta)/2

structure CellFacts (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z τ : ℝ) (R : Finset FreeRow) (d a : ℝ) (i : ℕ) : Prop where
  d_lower : (1/200:ℝ)≤ d
  d_upper : d≤ Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.dp
  a_lower : (51/100:ℝ)< a
  a_upper : a≤7/8
  source_rows : ∀u∈R,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
    (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-D.t)
  moment_rows : ∀u∈R,(Z^d)^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ Z^d
  frequency_lower : ∀u∈R,Z^(d-2*D.t)≤ rowNorm u
  natural_nonprincipal : ∀u∈R,∀θ,(rayCubeFamily F.modulus ⊤ le_top u θ).residue≠1
  next_maximum : ∀u∈R,detectorMaximum
    (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
    (3*(i+1:ℕ)*Z^τ)< a+2*D.e
  current_maximum : ∀u∈R,a≤ detectorMaximum
    (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
    ((3*i:ℕ)*Z^τ)

theorem selected_rows_facts (D : BaselineData) (F : BaselineSourceData D)
    (Z : ℝ) (grid : FreeRow→ℕ) :
    ∀u∈selectedRows D F Z grid,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧
      rowNorm u≤ Z^(Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.h+rowPadding) := by
  intro u hu
  rcases (mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu with ⟨hb,hcal,_⟩
  rcases mem_rowBand.mp hb with ⟨hne,hlo,hhi⟩
  exact ⟨hne,hlo,hcal,hhi.le⟩
end
end Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.FiniteNumerator

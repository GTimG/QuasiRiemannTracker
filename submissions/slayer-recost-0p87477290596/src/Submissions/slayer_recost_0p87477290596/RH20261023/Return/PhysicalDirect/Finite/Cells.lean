/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.PhysicalDirect.Finite.Partition
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.PhysicalDirect.Chosen
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.Transport.FinalFixedHigh
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.Schedule
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.GenericScalar

set_option autoImplicit false
namespace QRH.RH20261023Return.GenericPhysical.PhysicalDirect.FiniteNumerator
noncomputable section
set_option maxHeartbeats 200000
variable [QRH.RH20261023Return.Geometry.Parameters] [QRH.RH20261023Return.Geometry.Bounds]
variable [scheme : QRH.RH20261023Return.CountScheme] [QRH.RH20261023Return.GenericArithmetic.PhysicalSchedule]
open QRH.RH20261023Return.GenericArithmetic QRH.RH20261023Return.GenericPhysical OAI OAI.SevenEighths
open scoped Classical BigOperators
open QRH.RH20261023Return.GenericPhysical (baselineSource)
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open QRH.RH20261023Return.GenericPhysical.PhysicalDirect QRH.RH20261023Return.GenericPhysical.FinalAssembly RH20261023Return.TransportHighTransport
open QRH.RH20261023Return.GenericPhysical.Assembly
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
    F.W F.W (Z^QRH.RH20261023Return.GenericArithmetic.x) (Z^QRH.RH20261023Return.GenericArithmetic.y) Z D.e a H

def selectedRows (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) (grid : FreeRow→ℕ) :=
  supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^(QRH.RH20261023Return.GenericArithmetic.h+rowPadding))) grid

def cellRows (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ)
    (idx grid : FreeRow→ℕ) (k i j : ℕ) :=
  cubeBinRows (selectedRows D F Z grid∩dyadicRows 1 k) idx grid i j

def cellTarget : ℝ :=
  HeckeZeroSupremum.beta+QRH.RH20261023Return.GenericPhysical.Assembly.signalShift-QRH.RH20261023Return.GenericPhysical.Scalar.sourceReserve-
    (HeckeZeroSupremum.beta-QRH.RH20261023Return.GenericArithmetic.theta)/2

structure CellFacts (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z τ : ℝ) (R : Finset FreeRow) (d a : ℝ) (i : ℕ) : Prop where
  d_lower : (1/200:ℝ)≤ d
  d_upper : d≤ QRH.RH20261023Return.GenericArithmetic.dp
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
      rowNorm u≤ Z^(QRH.RH20261023Return.GenericArithmetic.h+rowPadding) := by
  intro u hu
  rcases (mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu with ⟨hb,hcal,_⟩
  rcases mem_rowBand.mp hb with ⟨hne,hlo,hhi⟩
  exact ⟨hne,hlo,hcal,hhi.le⟩
end
end QRH.RH20261023Return.GenericPhysical.PhysicalDirect.FiniteNumerator

#print axioms QRH.RH20261023Return.GenericPhysical.PhysicalDirect.FiniteNumerator.poolOutside
#print axioms QRH.RH20261023Return.GenericPhysical.PhysicalDirect.FiniteNumerator.selected_rows_facts

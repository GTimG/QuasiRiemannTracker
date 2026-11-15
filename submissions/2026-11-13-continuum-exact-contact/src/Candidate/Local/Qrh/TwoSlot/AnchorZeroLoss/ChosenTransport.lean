/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Actual chosen-source probe transport using the proved averaged floor. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.FloorTransport
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators Topology ContDiff
open Filter Asymptotics
namespace Qrh.TwoSlot.AnchorZeroLoss
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.FinalAssembly
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
open OAI OAI.SevenEighths ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open HeckeDetectorPhysicalSelection Cycle25.Numerator Cycle25.Weighted.FullWContour
open BoundaryDensitySplitReturn.TransportHighTransport
open BoundaryDensitySplitReturn.TransportHighRowFamily
open ProbeMellinBoundary CompletedGauss PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
variable [Geometry.Parameters] [BoundsCore]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]
variable [Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.PhysicalSchedule]

/-- The complete physical transport, now with the actual averaged floor.
The source/height order and selection facts are unchanged. -/
theorem actual_chosen_nonfloor_transport (hgap : theta<HeckeZeroSupremum.beta) (A : ChosenData) :
    ∃ J : ℝ, 0≤J ∧ ∀ tau : ℝ, HeightAdmissible A.D A.P J tau →
    ∃ n : ℕ, 0<n ∧ ∀ η : Character, ∃ C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in atTop,
    floorNormalizer A Z≠0 ∧ ∃ idx grid : FreeRow → ℕ,
    ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
      η rowPadding A.D.e tau n Z idx grid ∧
    ‖sourceProbe A.D A.F η Z-HeckeSignal.signal
        (η.excludePrimes A.F.S A.F.exclusions.prime) (sourceCorrection η A.F.S)
        Assembly.signalShift Z-
      finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal
        A.D.length 1 2 rowPadding A.D.e tau (fun _=>A.F.w) A.F.W A.F.W η Z idx grid/
        floorNormalizer A Z‖ ≤
      C*Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma) := by
  obtain ⟨J,hJ,hfloor⟩ := chosen_floor_removal hgap A
  refine ⟨J,hJ,?_⟩
  intro tau hheight
  have hlarge : A.P.sigma+A.P.nu≤1+Assembly.signal theta := by
    have hn := A.P.nu_eq
    have hs := A.P.sigma_small
    have ht := A.D.t_small
    have hsig : (1/10:ℝ)<Assembly.signal theta := by
      have hb := Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Assembly.signal_at_boundary
      have hx : 1672/10000<Geometry.x := BoundsCore.ell_interval.1.trans Geometry.ell_lt_x
      have hy : 458/1000<Geometry.y := BoundsCore.ly_coarse.1
      change Assembly.signal theta=Geometry.x/2+(Geometry.y-Geometry.x)/12 at hb
      linarith
    linarith
  have hbeta : HeckeZeroSupremum.beta≤(7/8:ℝ) :=
    HeckeCommonProbe.beta_le_seven_eighths
      (ProbeFinalAssembly.common_probe_of_chosen_moments
        (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
          ProbeFinalAssemblyUnconditional.detector_certified_bands))
  obtain ⟨n,hn,htransport⟩ := BoundaryDensitySplitReturn.TransportHighRowFamily.actual_normalized_probe_transport_saving
    A.F.modulus ⊤ le_top A.D.N A.D.e (1/100) 1 2 1 rowPadding 1 tau A.P.ellMin A.P.nu
    A.D.e_pos A.D.e_small (by norm_num) (by norm_num)
    (by norm_num [rowPadding]) (by norm_num [rowPadding]) hheight.1
    (by norm_num) (by norm_num) (by norm_num) A.P.ellMin_pos A.P.nu_pos
    hgap.le hbeta A.F.S A.F.exclusions A.F.maximal A.F.first
    A.D.length A.P.slots_min A.D.slots_injective A.D.slots_sum
    (fun _=>A.F.w) (fun _=>A.F.smooth) (fun _=>A.F.compact) (fun _=>A.F.support)
    (fun _=>A.F.bounded) (fun _=>A.F.nonzero)
    A.F.W A.F.W 1 2 1 2 (by norm_num) (by norm_num)
    A.F.complex_support A.F.complex_support A.F.real A.F.real A.F.nonnegative A.F.nonnegative
    A.F.complex_nonzero A.F.complex_nonzero A.P.sigma A.P.sigma_pos
    A.P.geometric_budget A.P.principal_budget A.P.window_budget hlarge
  obtain ⟨Cf,hCf,hfloor⟩ := hfloor tau hheight n
  refine ⟨n,hn,?_⟩
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  refine ⟨Ct+Cf*(η.modulus.absNorm:ℝ)^(2+2*A.P.eps),by positivity,?_⟩
  filter_upwards [htransport,hfloor η] with Z ht hf
  dsimp only at ht
  obtain ⟨hN,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  have hsel : ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
      η rowPadding A.D.e tau n Z idx grid := ⟨hlabels,hbins,hray⟩
  change floorNormalizer A Z≠0 at hN
  refine ⟨hN,idx,grid,hsel,?_⟩
  have hE : Geometry.signal theta-1/4000≤HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma := by
    have hs := A.P.sigma_small
    have ht := A.D.t_small
    change theta+Geometry.signalShift-1/4000≤HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma
    have heq : Geometry.signalShift=Assembly.signalShift := by
      change -(4+Geometry.y-Geometry.x)/6=-(5/6-Geometry.x/3-Geometry.ell/6)
      linarith [Geometry.x_add_y]
    rw [heq]
    linarith
  apply hf idx grid hsel (sourceProbe A.D A.F η Z)
    (HeckeSignal.signal (η.excludePrimes A.F.S A.F.exclusions.prime)
      (sourceCorrection η A.F.S) Assembly.signalShift Z) Ct
    (HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma) hE
  have hshift : Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Assembly.signalShift =
      Assembly.signalShift := by rfl
  have hexp : HeckeZeroSupremum.beta-
      (4+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Transport.b)/6-A.P.sigma =
      HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma := by
    rw [←hshift,←Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Transport.signalShift_eq]
    ring
  rw [hexp] at herror
  simp only [sourceProbe,Record1252270103Low.normalizedProbe,
    BoundaryDensitySplitTransportLow.normalizedProbe,chosenCube,floorNormalizer,
    actualNormalizer,sourcePrimePool,hshift,
    Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Transport.signalShift_eq,
    Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h,
    Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.x,
    Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.y,
    Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell,
    ←A.F.complex_eq] at herror ⊢
  convert herror using 1 <;> rfl

end Qrh.TwoSlot.AnchorZeroLoss
#print axioms Qrh.TwoSlot.AnchorZeroLoss.actual_chosen_nonfloor_transport

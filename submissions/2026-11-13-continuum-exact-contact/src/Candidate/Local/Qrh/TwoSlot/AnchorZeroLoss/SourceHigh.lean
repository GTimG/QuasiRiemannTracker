/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
High probe closure under coarse geometry using the actual averaged-floor
transport and a separately supplied honest finite nonfloor numerator bound. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.ChosenTransport
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
open BoundaryDensitySplitReturn.TransportHighTransport PrincipalSignalComparison
variable [Geometry.Parameters] [BoundsCore]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]
variable [Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic.PhysicalSchedule]

/-- The complete high probe estimate has no old pointwise floor premise.
The finite nonfloor numerator remains its explicit analytic prerequisite. -/
theorem actual_sourceProbe_high_of_finite (hgap : theta<HeckeZeroSupremum.beta) (A : ChosenData) :
    ∃ J : ℝ, 0≤J ∧ ∀ tau : ℝ, HeightAdmissible A.D A.P J tau →
    ∀ η : Character, FixedFiniteNumeratorInputAt A.D A.F A.P tau η →
    (fun Z=>sourceProbe A.D A.F η Z-HeckeSignal.signal
      (η.excludePrimes A.F.S A.F.exclusions.prime) (sourceCorrection η A.F.S)
      Assembly.signalShift Z) =O[atTop]
      (fun Z : ℝ=>Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma)) := by
  obtain ⟨J,hJ,ht⟩ := actual_chosen_nonfloor_transport hgap A
  refine ⟨J,hJ,?_⟩
  intro tau hh η hfinite
  obtain ⟨n,hn,ht⟩ := ht tau hh
  obtain ⟨Ct,hCt,ht⟩ := ht η
  obtain ⟨Cf,hCf,hf⟩ := hfinite n hn
  apply BoundaryDensitySplitTransportLow.isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+Cf,by positivity,?_⟩
  filter_upwards [ht,hf,eventually_gt_atTop (0:ℝ)] with Z ht hf hZ
  obtain ⟨hN,idx,grid,hsel,herror⟩ := ht
  have hraw := hf idx grid hsel
  let N := floorNormalizer A Z
  let V := finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal
    A.D.length 1 2 rowPadding A.D.e tau (fun _=>A.F.w) A.F.W A.F.W η Z idx grid
  let R := sourceProbe A.D A.F η Z-HeckeSignal.signal
    (η.excludePrimes A.F.S A.F.exclusions.prime) (sourceCorrection η A.F.S)
    Assembly.signalShift Z
  let E := Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma)
  have herr : ‖R-V/N‖≤Ct*E := herror
  have hnum : ‖V/N‖≤Cf*E := by
    rw [norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hN)).mpr
    simp only [V,N,E,floorNormalizer,mul_assoc,mul_comm,mul_left_comm] at hraw ⊢
    convert hraw using 1 <;> rfl
  calc
    ‖R‖ = ‖(R-V/N)+V/N‖ := by rw [sub_add_cancel]
    _ ≤ ‖R-V/N‖+‖V/N‖ := norm_add_le _ _
    _ ≤ Ct*E+Cf*E := add_le_add herr hnum
    _ = (Ct+Cf)*E := by ring

end Qrh.TwoSlot.AnchorZeroLoss
#print axioms Qrh.TwoSlot.AnchorZeroLoss.actual_sourceProbe_high_of_finite

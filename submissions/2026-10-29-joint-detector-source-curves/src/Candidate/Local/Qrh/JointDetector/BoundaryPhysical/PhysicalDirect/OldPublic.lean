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
/- Repeated marks: fork of Collet's generic return module PhysicalDirect.OldPublic (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Actual old-band physical reconstruction on new geometry, adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Schedule
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.OldActive
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.Data
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open Filter
namespace Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.OldFourth
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic OAI OAI.SevenEighths
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open QRH.Record12518109Count
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic QRH.Record12518109Count
open ProbeRowRadicalConductor
open Cycle25.Numerator Cycle25.Weighted.Numerator

/- Geometry-independent original/reflected physical reconstruction APIs. -/
export Cycle25.Weighted.Numerator.PhysicalMoment (certified_original_numerator_fourth)
export OAI.SevenEighths.Cycle25WeightedNumeratorPhysical
  (certified_actual_retained_fourth certified_retained_fixed_profile)

/-- Actual old-band source moment on new lengths and geometry; no affine premise. -/
theorem baseline_old_active_box_fourth (D : BaselineData) (F : BaselineSourceData D)
    (hb : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤ D.momentKappa)
    (G:𝓢(ℝ,ℂ)) (loss boxWidth annulusSlack b:ℝ)
    (hloss:0 < loss) (hbox:0 < boxWidth) (hann:0 < annulusSlack) (hbcut:0 < b)
    (hsmall:2*boxWidth+annulusSlack ≤ 1/2) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀data:∀i:rows,PhysicalReflectionData F.S F.exclusions.prime i.val,
      ∀N:rows→ℝ,(∀i,0 < N i) → ∀d:ℝ,d0 ≤ d → d ≤ dm →
      ∀j∈Finset.range (coefficientBoxCount100 boxWidth+1),
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0 < width i) →
      (∀i,width i ≤ Cycle25.sourceMesh D.t) →
      (∀i,(z i).re=17/50) → 0 ≤ height → (∀i,|(z i).im| ≤ height) →
      (∑i,width i) ≤ capOld D.momentKappa d ((j:ℝ)*boxWidth+boxWidth+annulusSlack) →
      (∀i:rows,‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(width s)) (z s)‖ ≤ U) →
      let Y := U^(y/d)
      let Lc (i:rows) := (data i).combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm i.val)
      (∑i:rows,‖if N i ≤ b*Y ∧
          dilationBox U boxWidth (coefficientBoxCount100 boxWidth) (max 1 (Lc i*N i))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0
        else 0‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤ C*(1+height)^degree*U^(1+D.t+loss) := by
  exact old_active_box_fourth F D.momentKappa D.momentKappa_lo D.momentKappa_hi hκβ hb
    G loss boxWidth annulusSlack b hloss hbox hann hbcut hsmall

end Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.OldFourth

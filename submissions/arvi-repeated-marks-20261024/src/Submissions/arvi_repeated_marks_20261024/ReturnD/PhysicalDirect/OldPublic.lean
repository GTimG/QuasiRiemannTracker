/- Repeated marks: fork of Collet's generic return module PhysicalDirect.OldPublic (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Actual old-band physical reconstruction on new geometry, adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
import Submissions.arvi_repeated_marks_20261024.ReturnD.Schedule
import Submissions.arvi_repeated_marks_20261024.ReturnD.PhysicalDirect.OldActive
import Submissions.arvi_repeated_marks_20261024.ReturnD.PhysicalDirect.Data
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open Filter
namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.OldFourth
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Geometry.BoundsR] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.RepeatedMarks.Return.GenericArithmetic OAI OAI.SevenEighths
open QRH.RepeatedMarks.Return.GenericArithmetic
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open QRH.Record12518109Count
open QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect QRH.RepeatedMarks.Return.GenericArithmetic QRH.Record12518109Count
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

end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.OldFourth


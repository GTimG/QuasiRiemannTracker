import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.LowEnergyExtension.FinalAssemblySource
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedSourceData
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.CubicLowSourceGeometry
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedSourceNormalization

/- UNVERIFIED low-growth statements for the concrete retuned physical probe. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.Parameters
noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeFinalAssembly
open LowExtension PrincipalExtension

def RetunedSourceData.probe {Δ L margin mesh : ℝ} {D : RetunedHighData Δ L margin mesh}
    (F : RetunedSourceData D) (ξ υ : ℝ) (η : Character) : ℝ→ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  normalizedProbe_retuned ξ υ L F.modulus ⊤ F.S F.maximal D.ell 1 2 (fun _=>F.w) F.W F.W η

theorem RetunedSourceData.probe_low {Δ L margin mesh : ℝ} {D : RetunedHighData Δ L margin mesh}
    (F : RetunedSourceData D) (ξ υ : ℝ) (hL : 0≤L) (hL1 : L≤1/5)
    (hscale : ξ+υ=1-L) (hgap : 0<υ-ξ) (hmargin : 0<2*ξ-υ-L) (hυ : υ≤1)
    (loss : ℝ) (hloss : 0<loss) (η : Character) :
    F.probe ξ υ η=O[atTop](fun Z : ℝ=>Z^((5*ξ+υ)/12+loss)) := by
  exact normalizedProbe_low_retuned ξ υ L hL hL1 hscale hgap hmargin hυ
    F.modulus ⊤ le_top F.S F.exclusions F.maximal 1 2 1 loss
    (by norm_num) (by norm_num) hloss D.ell (fun j=>(D.slots_bounds j).1)
    D.slots_injective D.slots_sum (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact)
    (fun _=>F.support) (fun _=>F.bounded) (fun _=>F.nonzero) F.W F.W 1 2 1 2
    (by norm_num) (by norm_num) F.complex_support F.complex_support F.real F.real
    F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero η

theorem RetunedSourceData.rational_probe_low {Δ margin mesh : ℝ}
    {D : RetunedHighData Δ ellRat margin mesh} (F : RetunedSourceData D)
    (loss : ℝ) (hloss : 0<loss) (η : Character) :
    F.probe lxRat lyRat η=O[atTop]
      (fun Z : ℝ=>Z^(sigmaRat+sourceShift lxRat ellRat+loss)) := by
  have hb := F.probe_low lxRat lyRat (by norm_num [ellRat]) (by norm_num [ellRat])
    (by dsimp only [lxRat,lyRat];ring) rational_gram_geometry.1 rational_gram_geometry.2.1
    (by norm_num [lyRat,ellRat,bRat]) loss hloss η
  simpa only [rational_gram_geometry.2.2,rational_source_shift] using hb

theorem RetunedSourceData.cubic_probe_low {Δ margin mesh : ℝ}
    {D : RetunedHighData Δ (ellOptimal deltaRoot) margin mesh} (F : RetunedSourceData D)
    (loss : ℝ) (hloss : 0<loss) (η : Character) :
    F.probe (cubicLX deltaRoot) (lyOptimal deltaRoot) η=O[atTop]
      (fun Z : ℝ=>Z^(sigmaRoot+sourceShift (cubicLX deltaRoot) (ellOptimal deltaRoot)+loss)) := by
  obtain ⟨hL,hL1,hscale,hgap,hmargin,hυ⟩ := cubic_source_geometry
  have hb := F.probe_low (cubicLX deltaRoot) (lyOptimal deltaRoot)
    hL.le hL1 hscale hgap hmargin hυ loss hloss η
  have hshift : sourceShift (cubicLX deltaRoot) (ellOptimal deltaRoot)=
      -2/3-bOptimal deltaRoot/6 := by
    exact balanced_source_shift (ellOptimal deltaRoot) (bOptimal deltaRoot)
  simpa only [cubic_gram_exponent,hshift] using hb

#print axioms RetunedSourceData.probe_low
#print axioms RetunedSourceData.rational_probe_low
#print axioms RetunedSourceData.cubic_probe_low
end
end BelowSevenEighthsTight.Parameters

import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonSectorWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ExceptionalIndexedWindow
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn
open CenteredMomentCommonPairedSource CenteredMomentCommonHeightEnvelope
open CenteredMomentPlainWindowEnergy CenteredMomentExceptionalWindowPair
open CenteredMomentHeckeColumnWindow CenteredMomentSmooth FourierBridge
open CenteredMomentSourceRow
local notation "O" => HeckeFamily.O
local instance jointWindowDecidableEq {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem actual_window_column_integral (s : Input ι) (C : Ideal O) (hC : Supported C)
    (R seed L : Ideal O) (η : Character) (t θ X : ℝ) (hX : 0 < X)
    (V : ℝ → ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V) (z : O) :
    windowColumn s C hC R seed L η t θ X V z =
      ∫ u : ℝ, columnDensity V hc hs u*logPhase (θ-u) (Real.log X)*
        normalizedColumn (withHeight s η (t+2*Real.pi*(u-θ))) C hC R seed L z := by
  have hh := plain_column_integral Finset.univ
    (sourceGenerator (columns s C hC)) (sourceGenerator_supported _)
    (coefficient s C hC R seed L) η t θ X hX V hc hs z
  simpa only [sourceGenerator_span, windowColumn, coefficient_polynomial] using hh

omit [DecidableEq ι] in
theorem actual_window_column_integrable (s : Input ι) (C : Ideal O) (hC : Supported C)
    (R seed L : Ideal O) (η : Character) (t θ X : ℝ) (hX : 0 < X)
    (V : ℝ → ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun u : ℝ => columnDensity V hc hs u*logPhase (θ-u) (Real.log X)*
      normalizedColumn (withHeight s η (t+2*Real.pi*(u-θ))) C hC R seed L z) := by
  have hh := plain_column_integrable Finset.univ
    (sourceGenerator (columns s C hC)) (sourceGenerator_supported _)
    (coefficient s C hC R seed L) η t θ X hX V hc hs z
  simpa only [sourceGenerator_span, coefficient_polynomial] using hh

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67

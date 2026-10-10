import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorBudget
import QRH.PrimeRows.DynamicNonfloorCount
/-! Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The changed count and capacity bounds are provided by the checked dynamic analytic branches. -/

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.QRHProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst QRHDetectorRowCount QRHAdaptiveCutoff
open ProbeHighRowFamily

section
variable (M : Ideal O)
include M





end

def adaptiveRowExponent (δ q Δ ε εm slotMesh ν : ℝ) : ℝ :=
  if δ≤5/6 then QRH.adaptiveCount δ (q/δ)+(30/169)*Δ+159*ε+εm+slotMesh+7*ν
  else 1-δ+78*ε+εm



end SevenEighths.QRHProbeHighRowFamily

end

end OAI

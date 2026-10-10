import QRH.Energy.UniformMoment
import QRH.Detector.DetectorPlainMarkedFineField

/-! Discharges the actual detector energy input using the extended analytic theorem.
No analytic estimate is a premise of dynamic_source_input. The remaining HighData
argument is the upstream slot-data presentation, whose fixed total is 1/6. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace SevenEighths.QRHDynamicMomentInput
open HeckeFamily ProbeFinalAssembly CenteredMomentEnergyBands
open CenteredMomentEnergyWidthRanges CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorPlainSlotProfile CenteredMomentNaturalFixedRaySource
open ProbeDetectorPlainMarkedFineField QRHPlainMoment
open CenteredMomentDetectorEnergyInitialState

def dynamicMesh (t : ℝ) : ℝ := fineMesh 2 0 1 1 (t/4)

lemma dynamicMesh_pos (t : ℝ) (ht : 0 < t) : 0 < dynamicMesh t :=
  fineMesh_pos 2 0 1 1 (t/4) (by norm_num) (by norm_num) (by norm_num) (by positivity)



open HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles ProbeHighRowFamily
open CenteredMomentDetectorDictionary



end SevenEighths.QRHDynamicMomentInput
end
end OAI
